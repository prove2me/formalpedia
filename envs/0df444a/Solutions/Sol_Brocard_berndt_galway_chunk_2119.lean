-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2119
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:41:53.520703+00:00
-- url     : https://prove2.me/submissions/ade7b72b-d86a-4066-b063-01d0427afb43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 380935251 ≤ n < 381115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 380936501 1250 380935251 380935253
    0x41202010e15060a1202031b120106060c170a020601150507020607030f030f0b2202120103080d110906070809010306030b01090207150212040b04050c09250c020a0506090d 75
    0x420030328080c0703440405070100d0b420300c00c0030300b40b16000030002e005102c07009410392004d500083d1590102101c407042051100202c108603581d40480c545c94908090080000603034480d80507003020414002541d00080c4c801e6003101101005048540c00c0e10b60b94040e101503804d0800c0b10003101c400c07001c180304102c814402038005032112001880381074001d40f07524901c6002c082000b815182ca190408074035900b0080c110040d5203403008007503e92507180c0030300041d0310020088c1b074000f8010401508190000040000181314180000b0128030f8103401e030520203604004a014690700c51150055082041042034602048070340c005480340c03031014900401c040703599440340c00e20100c003a00040e090310f03800030b5440304100c030500204010351500d41080d400c0c200c0540b8820300c5c04000a1020300410168800502045400c0c08404901c050080402407941404002144410090031071041000380c20804654982d000700e1414a500d54002c0c42d00c400141042c0600c030054100981150300001c031803400c64 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 380937751 1250 380936501 380936503
    0x9030405060f090913030f030c0c0c0f051306030c0501080c2b0b1e0f180f070f1704021e0409050a02190f0e0c040b030403020c03011b08041202010e 65
    0x2090951100d52001c0e03c50314484104044018050326581c502d40c1c15103080b40000750404002c410b0301006060018040031000005d0f280d01015043c018283d881480010034100180c000c448192101922a8a103031030301d001003002120500d0101801b13402072100e04021130b40c444d140c0c6aa001ca00c0e418400c0c00c1c10701421411281c1101009950342900c1c11014020008450380300d01110520708840d0b24502c51181c0c201408101521010140103a1001010407815120a080340708000f9488e600803425140520181c2404175040e03803d000040c0034907560200c0d0703611402d80d031803103180381440c10000c03074541c5c3d03007040580004100784c000841c00600301250591b03224400d84c040c09001c0e00141840c5101071040240c800b80d00310140701198a5200d041c40890980f600341e13020703283c21030308900301d81d200c02c0921403150140c0da0003501146000410842015400309510b004160b05074020300c00b8611450002d4021012138904100080000b800940440c6c800007910202d1411400000740c4056000750312 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 380939001 1250 380937751 380937757
    0x2010302070503130e0714090405041b0303020102040e01150519030b271b03040615050a09020d05010f0b0d0b12030406050403030206280e16090c0908030a08040b0903040506 76
    0x4002c2d503440300b50007003103001c0300c5c0064281c0c81800c0c0d00d005100e0304448904041180501c018590266946400007020408022101d10402058940c0040c509941e440c0080c081d41c0036000b103084032608400009042c51100111130a044a640c8803d03080030780145440d072010180e0500c83d01010b84a0707003a41b0076038940c0c820300410740324684205540301240d0400891a5900a02200884044441543c0c06480c16000b500d4015074846c40104a11050030400064000c0a070080e0340d1205802c100010070b501194010200860181c1c414005030380e07aa5105154042c1c1c40c40b404059200070041400500078940c00f621403030200410849030031345040011740c9150015049540401c00025080c0140740d0100441980b000303803194401c42c1003a09402440c2c01141c9540c902408586131b00c0f0180301d082c0280564562421501c4601d401e0681d40d04c5804048c0800c0c28520f000300d00d00d4103000c191100003000300d03081500300d91a41603040d180c9683d81d005144004110900b0360109103c0810705075911001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 380940251 1250 380939001 380939017
    0x120504020d15060603050c0c070605070c08010c0804031205040206182d03100e0c0402030a180312181709030a0b1003060b010c0b0a2c0102180603041e02010302070503 73
    0x70f4043c10000007074110745018140c1c02030901e0510000d50084800500003065a81c03a20789640c407960b0504e0100502c65447d00210401c1d42042d140036445a440091603124902035078800d048540346200d000100d0310b090350003035005802004001c2c0c814a481d003a503600c420002c2d2151440c0c40b8000070850031051154080240a51466400d4070b49280401047d02c4041340860104900d80c0901003032642c035002862101d00650700840000d103010029030007103010001001915098400b2450003c2280300311840040c1d01e5480c0c040340001c0c610503102c4100e54a503110058035030346070b103040841c180d0340c03c00502c00368944103c2440500051151139194018010b8481d4603071464210319040301500c0040c4822410031072445102d8020803c2150283d40010041c40c000612150b5240744101000d400d40f070100d1a6000b05c1301d02403c10805600500708904100030310300c140310748002088035174442501c0c05400e002d4400c0036030104400c1803080d47c080c03c0c8141001894095a035440c241503400c1881 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 380941501 1250 380940251 380940293
    0x20a060e0a03080c0a09030210090801150305060106020d120e160311040b04050c030a050a0b0d051005100f0608130f08031801110d111b06190c120504020d 68
    0x80d02001c164000d03500d1500320134405030b11400c0c500c010724000e00c8100c0c0c92001070b01c20824040c0204801e40120218805451140001c0c00306038800120540d59060301c0c80211058813070400000740482c03000c00c261140d5801541c942503948040910400600342d10f2251002a005100084090a81700c4020a005510038022441400c0a82c4200b0085682045505015a0411082011b210701c0c1c030302240d5002110210004054460b00410001400c0c054055038021240e40410014410002032090008480050610555035403a6400d205000607204804402c02581c000740328243c083d1f070035558869110881c80142d16056240d401c68043c1400055411440c00414840f00c2c1007110351520000329104020701501507000100f181074840c5501e0380320b115541d03114030110100c0e00000c41d592010303004141070421886c0e0380c2e495200d40c0e0a407030026040c1031030022000b0b20b59003806114044000c54035007030040307150101040d015100040c402c90744000003a807500c00054003071441c0320850f08450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 380942751 1250 380941501 380941513
    0x50706020d0606120c03050f01170c03060a15120c03030507141b1002062202040615091d06030604030f180320010c211701060c0b0c07050d050a020a060e 67
    0x809180c00c507401910100c0806d800c0c81d04001d481e241440d00181140e074400074000c1c1514202e02e4041c280100d0348555681400b60100f4000000f0a642002c10540c042d11541201c0d1903131002511241d01604e10018102c0b4180e10302000428010005481d2480c05070158043c1d041d00810402e04045550409080420843e2070328015814500940d0200c954540002d202505181c0014440002041504280c203140c0400c030f0740031501d6542220008004195031903c510b40070140182020800d030150024a400302c406042c4d413251117030102405800043c3c00b0306900d0322107807011641100710a81144c00c0c40401900491032524030707281440107500981c844142410031032941450310418502071810000750166020104a288030072800680c13500c0c49903031900740b01e000f099507916217010901d10105120400040c2039904510100c01076072007800c010415541d0b484140700d003030180c010041c0803a8008559601007030b00a0004041d40f20460040300c0c200c0406d980d606043c0d45059407120103a80040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 380944001 1250 380942751 380942777
    0xf0f1202101109010e04150503031206041803080c0d060308030a0f05010602031305100e060c01020406030b1e010305221406070f08070507020f06070b0708160f050706020d0606 77
    0x501c00d001041e107601035480d02c3c100219000034940010911458403940d51a80300b84090307410b1200701d00c01410050240ca481e807803110100d00e0400412034803540140c1c00d110203c190550070040700d2142c1a03041c1c84a80c00d035100c2300c000300030640040c044d41e403080340c2d600310100200e040007028600c120558100402d502a111102c00e0503940180c0c03000d010f41d4400c0c411090081503030600c5001b502e20a58035664030002001c021101c0b00f6414541d02d801840004401f01c04034010740080c019030380640c4043c041d480c011400c3c00343c0000c0001507016041021181546658401d402158100056010307400070280904003000d400141802d044a80f00c001030300d0306040d01018080240d00c104181010071000404020103400c4020082940d0108280014810210356418412200c440c42c00740c6030589810041c501103400c40c8003621000c0100c0c0f0f42900040420142d42001c1d0601d840c1543c51003440143c0a00c2503880b50004603088404540070321800c017207844e013849400700501c0980d0b00c404007886c0c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 380945251 1250 380944001 380944033
    0x20112051050010507060b190602010e0c010e040903090503030a0f020c06031e090a05120d0f06441507020312180a1b140a0e040f0f1202 60
    0x310301400714104021091802c030800c003003071150014030001e0804683d41d040d246002001050464041c903402034101140011000611111009607102d40e0000c10070000040c2c071042e9140c45590555000450002c465030302030500c0d0300814001c3d4132a007400324840e5100e4002a007590040c16a40c00014102c102201c0c00d142c0c10070290813100b1040d41d00d9071450030154407445006145010f0700030a500071101141500f036003084110040d980100a807013040c039aa0b41d031200c0740d6000c1e10b140702030b8506000401384d08500d0ba00c08c40c0104c03a1552102a5030070115240c0c86915070300c0171900400c42039402001c0394503907485403c01c003800d81c0c1c090140c45043ca00c94081700e0b960601400c410115407080c01003014002030601c04541200f1008001e4400c0709490035810b20307000810314014a010040c2c0e02d1350300d4800d1034401200c01d5500c1c014116208032210803e110342241c0c84d1007003410f0042240d0101d40031480d100500110680110805911110390762101d01c83c001100c030514005902400900803541c0c3c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 380946501 1250 380945251 380945339
    0xf0b0f060f0a030f0201201204060906020318150d02030a020403050114040b04200607050d02060115140307140315030d03020306031e0f011404110a030201120510 71
    0x79044840b400c801c1e08540750002c03000d00c0d50400038140007001c04000810046034910319000041001180d82900085505a00940040c0b04001c080b9844130408280c1c5400070081d2840c8240c0c04655809000d08002000040c0f0000900c1030440141000140390b04400c500040d407242003000000359603685140341690071682064091aa0283c0040500c0000356502402c03540082e0020851b40e8007100c4025080500405249080c1d0300c0100044c80c0c10070061f0114038081001d4039038003600c8460f81d0344c0c248029007119600e0f4460000355501c003003c0c098540400135503040605840e080e100b00da0034820118056001340c0340e0210707100e2080303444a124601040f0400750300d451441c0c1503046003400804696501801213881400303285441203401808410020808410000c0000307022500880c004603002502c1540c00380c804c07110b00822100a414110f1088003107903810b075a8481c58041c00705241c2c00805010f410581c2d1408801d0300040c0160480750161810f90030b00c041010000300381010a00f19003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 380947751 1250 380946501 380946529
    0x305031b0d080a0c090b0711030d0806030a030516050a081c140112210f080901020a080c0f0f07060c11010c0207120f050609030c21070f0f0b0f06 64
    0x2a0040072000c101980c4124a503410108000010401d400000c0050f11810050b8018001c01c1c1c0c000300c1c6240602009131028520550141c0c00e89940c50200681141c1e0b0402c103c0b111038041d4809585000041c1c4100c0042c40307840fa801e80200555200d607074409050081c0c0c400c058440003000300d101101d00011860400f0450b1102030100001d0443c004071488070345051003050341041c0c4010b029424401102c0d01e0849142c4a0381d0100604888140c010306104040001d00780003942d084c0000d41f03003250500c200c1d14241520340790366804d640d4501e60344040303502103030740c1c1c0000a405001c242c0300c591b2050b010f8903070f0f43c2c031520000c50030b1200071100810041c0084c0480240fa81807180a818003500030625800307032407040085c0c00c0f1410380b50030440401c2c904803c004120740704800c1006105500400645407040514041e00e4001035250b03e440246441c01d124100014030070001840003c120b18041100188100940d02841000c1e844200740200100e403003504222044082102034601595072203100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 380949001 1250 380947751 380947753
    0xa020f010e07061218060c020d17010909020102100c05031b070b0a0b0f18060102120304050606060703090e1008010c051303080c160602030c0c0f010804061508070305031b 75
    0x200360014520750301d080d188980000d01101c0140109010a130fa0400d5441041d00e8a00c03410b4540740e490844024400a03041200501420100b542d1103881640c440c0d41000d1038030540c80300c507401c2188038001407121020880c1903206680200b9041d2314580501050105a9102c2070303101d1401c40d003808520b081d0078401d9046010100f0119000890410449401200141d8001003210803000803513103900002c21a41e83c409408003490070300e030403c45c1030240315000aa0075190344600030810410300f80400c0c0d90040098000303800082c0725040100c05003031158002c0ca44071a84070742d40c0506d60440c6a00381c4600f206480c1307003c000d2118035030074000c40c88031146520340640350980c1036101c0ea015000c00d0000820807000001c3e00404244100000c4103548101c05003921401c0d50f940000c0c0d5654820a00e9500740d000d00f402c94001e44c83c010f052a1282901a100c0c3d0354540d5131556458001c0400701011400d0b40c91010000c501d681040100c04095072003100250b40d0752046444405040b100c0003503803121 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 380950251 1250 380949001 380949011
    0x3270303090c0a03021e030c040f020904140405030304061109060c011401050604060219060212070c0605061c030e0117091f150b45010e03120a030b060f0a020f01 71
    0x141c0f10100301494400610301c601b241d03d030851000a05200c1e040070001d07401420118090300d141c08660041c030180300100d80820800006030301c141c04460342101c002d4601c1c1c10a10008000ca00d1a421080203661002031076498081200001003040d001440382c03048580d903803c0d1421307010a0401400e409018100c8000f0b0070a443c0040095854400740490b0039113803281c080790400c0103480d80503103a8802c0d01e40f90080300307031801210052004d83d404200751030399414900451a9401c0c04c4049040c100b085055041d03200810b5241650700660803410340e410412002c0e00346060b614201c04882c043c10403403000e8042e69074010240710b01c4800c494154240c007841c2c03a01094007610140301150413a035010000644551901c1d0814501c220a91300101c9801003040c1d8941112082960402e29114403030010345a20445000449800c0c012420b50b03509a484444c401d82810101c2001d0500d41500d86008102c0120700e2002c90025040450342510b0001e0125012a60369010321030700d208544400c000b001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 380951501 1250 380950251 380950253
    0x20a030804030303180c0611030c0106030501140106110309040515090a02270f0108130605090102030601120218120703020301020f090108090d0912110d12140406120203270303090c0a03 81
    0x81d106c4000c0c451401030204840c0381328400f00c4244142c070202a1450000c200003a070382d08046001c0d02c14410901c00b850184000468441c0c0901d10000d80c0da03020308025070400360840305000042070301400c02040340446031031490403039441220441c413900f00b0110250300c0d660361220f04c80c580300e14070071354401e00c0803403810440550f150f002980001c0d100034600702c02151100d076000c0c40e8441c0d9601000e010913080c03004000c0750703e00c1500118000d042c01c0e658401110358a06032070b002c9000c5d60a540c801c84181c9048030f0302c02d02d80b100e40c910140940b60705442a169907940001d08a0307202b03090400340640081010682c542e046075100b0b5004440700042c0c030b81c507403030100001c5c00d41e0b69a0107050b00001000c1c1481c0e050003000e1580c0341002a018110181d13054032818020404c00401c40d0001c001107144000c01c010041d01c00a0703408461a5071a408000496401104082d40000f0140d04c403102c08121030307e6150140f01c0c9002c2140e00310740d0245035a400c00380b1301a0308104500d06603d01646444400300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 380952751 1250 380951501 380951513
    0x2010e180a020f0c0312040b0601030203010b121807140f1807030504060212070e040e16030f02030c0a030c1703030103380c25020102210403020a03080403030318 71
    0xc0e44108003003801079607a4440420f4182d00c4c010940c040901d44070120b10340f020003900c42c000c14000d074003e444001d2a5556480110240d2100340100c24040605000c01d60020a070156030540052208040555100d030f4082558940304455002c0d0b010348480140300711007414007600c0c05240707070740948600a071314501e0390f0a1100c00c80c020b803500041582d00c40028041c0801c640c1a0350a8142440940c01141080704000b05003a04403013100b48074502c0c28240520101000032404607984281c14188042c84c42c46d1107040c0340720380e900802d90705030041f0104242e80d5502e203a2000003643c41040c0c1101c080c2d042100c1002030803400aa0741c85280d008000610218052005024000020440500c13542c11401048030118400c004064446c0400d9008d0280519002e009081011860140b541d06c030f00034840e4411540044d083c0190160b0005c48406600074402000001c1c51000304030a0740c6010750303d5010a882030042d0344140ca600c60045428020180e06014072244494640041a01c0800c951281 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 380954001 1250 380952751 380952799
    0x2030d0f06052404051c0506250f0302071502030121030e0f1f0f0e0307050916110f0a0b01080313210602030c180316060518061602010e 60
    0x1010703c0b850918925480030702650485001c0e041c0541907040707000b0325006003400500b0b4540c00316920300078100094a84201d07040c4c1002006045d2090380740d5601168400d48024110584d2841050f400b0450758000c10344402007014078000154005a403585410f907410034041418510140d0913014110072400b091303000b42030305141c0c80101d50084070b2064580029014040c40c0d04440c0304003804050450f591500034083c090a2030140c1ca40104a9115004050315401c542c01030b958082e0014011410a20701803848080d6001503090815203900411440c500d4400000a0241a648034001010030000d40d01101707030040160384029070405007080004c0d220200d19000e15500d0181400081e01c40650101c4a00e20942c2c10000455072410841940640f03a4480318080305580200f040801c0c180c140003034644030400f9020070001c501030400b0340885c0e2991140b05013a00081b0710301025006036841d00c00815105000c01c00d008171001161002500d00301078202c0f0684504501011004611010410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 380955251 1250 380954001 380954029
    0x7090803120604020409140a06090c0801090b060717090a0f05010c030e040b100507050d0503091507030b09090115090b101b0b010e09060609060622051002030d0f0605 73
    0x1400740a560305400300b0001e009a83c0720442d86400c1c8002c0b00b2082ca1035000c81c900404640c3c80a200b5180c41d08090b1054030488400d610000f000c4400400c180400707a031020120580003008249000640d0716000740441180b0005141c02000065039200e42c50000e0394140180f4003800c09a1800786450006001c113017001c18090140102540620026900c0758071844006c2d000a00200712603040e000d00034000c0e006107108503140c0c4201b001150400f4000c805507440f4201070350042107042d1010000f592580d1018050300145521814501c2071962100c0400d40309040341d5000058201d080100c203104001c2541c489411903140c003140c1d05e19030f103400b682101114202d091611904400203075692540304045409816031207400000b0401d0458600c04900801150044800589600f40bc1214040043d202070354884001c0107644112840543d880a00f00b0b04021104603240d6206d021903134103000ac04080006030030001c1d4190b82010315104500d25140360f040100411810030012030926031007610 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 380956501 1250 380955251 380955277
    0x9230408030406110c070501111504020d0606080601060e010f080603120c12130e220f0303021b1e0c130203060607060f09060c17040602090d0203011a0907090803 71
    0x2d000d20007960440c440400030700315005d83e0744c0b6030103c00a40f50410746c018030780003581c00b00e8849850b982c00180c0c422842207000501c1c1258956608110400703048030411901c0c0f80d200c203030005460200340003d9008107065258601041d042e4000100342d8110b00b4244c000380300c041401d0040980780050728400600d40c050f24980c0d282c85d01001d2510340b01c080c25820141b00300003d00c1000e8a952030f61458119043c040c14448191210303881044401003c01d6560054071030454880c01081985500c0c1214900a0900616008a400140e071680d4040003039011540e01c4000c001030b01d9541101c242c0010200e42c0041c00b02070800d10000b42e4048200c060701c84100e500030001c26038542d00c54003250341c519030001040008094030344040d4050403440c04240c031002c1c41d1548051101d40500c03036520440342c0c40ba08103c495540c0b5a9400001c1d0400840d45800c2040031880b840141c03024032034600b101905070118600c82d40c1640400c07800802c000d01c071000b00708400d0004c0000c1e030381c00803d481058140ac0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 380957751 1250 380956501 380956507
    0x150309150a0207170706060806360102030414060721020a090503070e0106090f0303020c0d0c05060c1605060f07060c141209060a0605030c0409140102040b0409230408 73
    0x3100c071001038022080b01802d5402c07a02d0720030700349204580041043d244961b0302442826902e4801917183d00045446088000707491207402c284800759501c101c0350030600301c5400100181e000d60f450881c0c00c01c407030440e9501007011200e030070034000704440b5178070100610b0598520701c013181801d07450b140c200c0382600c000380d00801c511740864043d038000b20103440301404a0394038580d00d1000c204081c20078820440800e50b0348101107070303405015001d070056075015002003e0000f0034500303116000300000010741da551078115001ca55661010000d15054240d04014a004000c0d0140d1f0070324000c0d0f035400103220b03c8080140803507185c81c100907680903030380144001800c400188419243c005071044a2010321600042e50b1000078801c44007203009a102e501216400c2d0740e4420441d084403014020b2079810781c803001d012500e070326242d08644a002d00c61751400740b00010130704129003603030082e0b004106412004281803015103120700c60096000740402c0c42140000541290058805003c1c4c000740c0f90f41000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 380959001 1250 380957751 380957761
    0xb09150603060607121d04180f060615020c01081e1b22060f08040203031b030c031206091e0112080c07061808010e060609060a09060803030615030915 66
    0x40400d9032005a00b2485c00c1501040407035000303160012003880503440c81411500c00d0090f050074842d040d1241d8244011800c80380381038079000282c00c0f901d102140e601d078891030082050150001150900075440d0010300f09001c502001400c8072900030b280094030f0401c1031450312580640b410103a003100a614040300700000e640c003940503a1160010f18003902180c915502d0b56403519414132012510695039102c04085895411540b84c4421364019515502c103001d030840440e8940c00c080c80007040042280d02c2c0c0344014040c0b070306640003402c0e04440d0010440c100b11003814015215940843c1004002c2c040e0180701000c00480801809195049480c401d1001c081242580c12210004056801c0b034110580e00e60000b00042c8107003207403114158800400144151050040c03000030910207028010070364421082c0040e8203002016160701c01d4904100082c020381c2441607102400191000e5581ca15001c4180000340c0c80c1c01004d44041c1d001001000700c034610100d161020003502109401c155118 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 380960251 1250 380959001 380959009
    0x11090307050d03050d11130902090108070e18040f03020705060705031603030b040f0905010f090c051504050d11030111120a0902060d0f02040302120102120c090d240b0915060306 78
    0x5d1600140101480d080030801081c0140e4090310b2942401e03c144403803940c07109149800d0f8011440d580c2e0105442c40302295240b4014a882d8007407000107400c403101a464034900e000c1070306003038405a900f039840010b41400c0c940e06002d04000341c00c0580d070051070b00d04150354160742c900ca50800b00404d0070345030b511201090300ca50408060380000034400e00c00581c0c9120104014007088600301c0d03135507207408800c010b48031640c080c1d101d0154000521b0f2001038901800e001d00410980000344c10f04030200408a031b1a501e000218083d40d000d40041d014101400090608441300720980c034031a02014000b00c83c0c09103440701026131010302040d0104a02c4a5880461124080c00b00c2d100c601c2400c200f031512040040f50b002e001241d00840b40c800d0b00c0540c42a03168200e11803618071140b0300e01030000054080d402c0000900c81658041c0103940406059145d802002100017400c10101c03150300c502c51b45000d424044c0310300780d1200310350b070400d0b60605c503024241038412000064000e54021000600c5d0350f88e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 380961501 1250 380960251 380960257
    0x6130b120a05061012152c1b090d05010c020a050c060304080a12060305071415090609010c050c18190c02061603091a040c0b030105030a0b04060f0e060a11090307050d0305 75
    0x4022052182599202c00c802c3d8964100b8100416506042c7c0200b5030300d145601004502400308030300c0c004490b00000c030746440c140d40042c41c143d0704401c0d65040c2d400000c00910400f50381d03484503409044d10125910308a8204540120140d1160303205001f07000200b080300c01160048a40c034280200050303501030080d400392040e81d101404a005a08001070540e040c2162105100b4049801c00980500c8465903a124081c1640c1d60350401c40c1404011a40d500a1458601c2c1f140a1412155001501c40006507010340c42c0182c080303414948401c1c00fa105403203890076040da207038410301130003030b03a440c1c0c2c0c0000e5542c00700512040c0d1081104040300e036a81d00070381c0007044082d0041802981c06426400c00203450b84280c804541a2441c91400244000c10704103030390581318010090406030b11030f611500343c0084060400d64040e035542c03d907410381c0192840307440d15a074425070107001c4928252184030308450315051403a007114820400d00710169408110042910002c030740031140e0f9100d904045913540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 380962751 1250 380961501 380961521
    0x3150105032a0a0e0924061b0c010f03090203250f03120809070b0a080c0c1e1009170c070b0301120c12030f080606130b120a05061012 59
    0x1030b10070050301e04000440d100030070002d000c9844200074121241d0900000000444180c0d00034a0b0140752610b0344815413490030002d90b00244074500701a820803140c00301074021840080c5960000740c440f00d165030000b54110352001e20b401e0811050781c180d00480c0c0c1b40d414445d40308001c05414801d840c00c04841c0c403014006011084601d810381c80d1240f0701031800600341c00c100004074010710000b800b460b40028250003501e004200342420944154410364018001400d0907810f40301c10301802e0f00202d03040201c4107804049044201c40404089011400c01f6071030340040c0801c90420680c0c0c4c0224040c048401460010070a55582d103080c012030345401e003500c0e50480b004034a0000000100c41d0301112444254034064068102c0b9903655140c0c0d150059100038000340130034115030316951324601422080e80d0185025028a01d41000081080d074401d10700e40100041c0c28012540ca40b44500382c124603503000080c0441002142061340006010901601038003080006000891083c000c003038201105407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 380964001 1250 380962751 380962801
    0x1614030f1602031b03030d020a03020d1803030f020310031e1e031202030708152b11030c03032a010c0e1008010e0106120e0604081e0315010503 63
    0x1410040044030744003005a109078480d21030000994828024040c0709542c2e401c0040045181800100d10030001e034205d01c020310b041c16400d000c2c40907848170b07600624514820840c0c1800078000c04e4a40501209c03905500300803250310500401c8424442035140c0d50550350440280b450150710510040298001000c005080700c48500302c91460454880c07940040501c00d0b01c42e54040c0c80080d0000040740411104030001400c00d4000c500076510122401d211440085d1020617401c0e02e58411000740411498400c0c43e13001209040801c1c00079074515810700404c105d026010380c1c40c0400001e13549010301d03424880d04940c00c1c40c0216510580d01d856498550a4400a000c00c03001200003428680c80840365a00074918012950071148c406c1a0b60b81c1a601e00c82c0300304540364282501210b41d038403401c80b000b6800e59292007107a20710504001e0301d40716503c903240d5155135450f420703000c60344401440301107000c5484c01d0040c000c3d58500c0281c8400a01000e01e400340e201d50355803180022241d0360f100c81c031102d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 380965251 1250 380964001 380964007
    0x50a0b0a09020c0705060706020a020d080c120915010e06040b010216090c09030506100317310305060c03160c030e090408161110020c1c050c06040621021614030f 71
    0x800031227030060618500d0395000e03112070300030a0300192020b03902101e60a0003880104001b00101408294454101c1442c17400c03034000b003900c48009010300714207801800300404020100886032070300380241e91220313000784040c02402c00208421001701c4980d0140d801e040f0744072003801844e5485408894015500007003115440d0407c240071a018040e00c1c002940c4020310000900303110b15100e0300301c440b1040310200e90074a180030400d40201032106c8031018001d401c8412000400703d41c0c02c2040038005c0c1070006006503139090a801015000c018101444107010100012202081d0011828512644192404000d039903503441c007072710b6070710403400244408200074400c2401c0c81091400e403890601e040d107603815418042e0340203a1390b400224079025400702c2400d1204a0404030132960100701440340e021541600c04d0700000034060707081034000c00c000134803030160100078000c06a0190420001c503481140307010b40100e20148680c41508003d0010300c515075146204800801c2280c901c411034441c0161 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 380966501 1250 380965251 380965253
    0x30b060d02070314090609040c030e100b1309120e011709010504061a060a0c0602041d0f010b0a090308130b130e0f011d0a0e03031306050a0b0a09020c07050607 70
    0x402904594402e400003113080c034440001d004d000003160f40da0310b80203002e641440c010780c1c200000707011004417000415072602c070749902007842044603151200c1607070004243c201801080c0102121031358081c50010f0b080100c2c07000400c0600303104030960000e0380780894840c2d5008005840745910150a200004041420043c00360010f61000e80200e10606080c8260042101c8203590240b51022171130f803004081100c15041e83c050741100c54407030303c186000750505035210300201c01c04800c9040b002000721182c003084405c4442a95882c0944101c3c0801401d00d03840000c000d2401c200380c04024030841c00051405141358906101200404030b0408081d41c90391910200c2d41c1007482c9100b000100d22407100410b00b00040a007000c1e0503203c919143d01c59108414040c4805174a01a10900640d503507000141084881407000b18407550707030240e8201c90600680351240031100000e10500031140790101c014450350b40c6644c070b041262091103002d40c031241110401070600d1a560700c00341c0c0c0800001b520074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 380967751 1250 380966501 380966527
    0x4021c05121903050601210b0f1002030a080901050f04170c0f010209030708071d180d18050108040b07080a02120a0c02120f070609060b0301021303050105060a24030b06 74
    0x588181d9594084c0055200d0600640b4502c1c52045c40502d43c40019000322910b43d0107a001d070f01100401400b610f07440c941100482d507107501d8030b01e04100580002560034a403e40004003e03030400c00e003034004c201d10700d46082d11020b1294007520040c10700c100ca5840d140300c0040328080c1c40254410304c05075000007400d22030160003548980e01032406030080400c0000d1002e00890544111603980d4188840c2a420104440e48040010084081044140b1101d42e07000c10030094050132103a02d480303444801441a620100d43c0d580303503100c00d040080c15000c0000150030220503640000807414048103544401140c580607004c0c42d41500c040c0301c0d07070004001001d9216040440c0d0303480185c080d500703540c42100c03a4450703038452000101821351041040b070002070025404866000e00400c000035018140c00002820b81c0d0260046512a040c01603080c801e104080c450705800c1042100d0b842d1501e460441503620010b216500320701480174112001d1503083c080e401203000f00c800100f402e03564142c218102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 380969001 1250 380967751 380967787
    0x4090f050f0a050d03020c03040b070302150702010203070305010e01031a0402041d060f070504080a11010306270c022116020306010e0411010801030f1b030b0108030711060304021c0512 81
    0x1650140704802e044c1d91818000e20032240c2001c00080918034041c00c03c09440d26640c41084100c00f148141154115200035400f0514000e02c415800581ea030f0610070401400d40d0010381210340c01d00d00c10030040000540d001c0f2540700302e00500c05a003200b0355490002800611443c0c02c0f481c00110301078455813114102040817403291091240a00058480350002c8426020b1b40c05988820361000c03401d400446e015141031003e03400149004100c071501d40c100183d0860281c05207041044c41d000f400700c0c003040da60084604003e020710052084148200304409a60301c502051842400d00041002451424540d100c810a801804850301541d603181450341c5001c0803902a900c00c503040340ca9903582d40c0b01c0c40326181202e030001881113107550551512030b100485c110110381002d90380040000011040c1d00b5290003404484c01942e2540342c60309250181200c208181c912a190800c04c000041c2d0716601c00725a1194a41c3c0801100400d0b490054076082522205030400031002c600039412030092903034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 380970251 1250 380969001 380969003
    0x1b0c0f062409140105090c0708070602040e06041404082712030304050d0206090604201e040c030204050d060e070915090b01050909190216050105010806060a030f0204090f050f0a 78
    0x400407003142c0c0f03032035500315803080c05015401010000459080c10080018003011303030190020501d040e04d0740d61000100e03403165101d00c0c030b5035403080104402460144205480c7c0291204a10414600765849030345510030b203000b40c021905040c51000c14195070801c19040410054074020300a03000181c101d5894004903000c03200ca01c515038008802c50303c0820942c1c02034403d00c00400707641c0c840ea0f031081c0285c8680c3d10600402c0c0c06210f0101c82660701d445c18510b01000c035442e0b0103100c5c5003120500c020b07969110300c01814103004000c00c201c291103c0c03000131180741d04001c0004805860341411410301c0d4081e03110200f0641455118a002c04003809000c08440c50100d0404c804c6100038010344040c0194420580e201000c0c03000510300717407452056074074040104000103141c40c80c200b416090030036810720141c1d2203070340d00e20043c85178201c100071107904058202c841c81ca00328039544d030f40748864000d02e500034003d6171142c280b402000014180b40303900b154010b0545101030700c07004419070340f1103d8003c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 380971501 1250 380970251 380970269
    0x190908070605100f150c05011418032704090f0812070c080a030c03181a01050102010b060406050702030102070c080a021e240d05040c06031b0c0f0624 66
    0xc0071032143e2201d50ba01004032000c14440d03410041c6450b0600000b0304550000f401480000f02d000c000190007889000c64000702185072500c58144041d00c5e00c140c207403c1107040038540c410454144403000900410100540000d44035050f00b80b80e602290181c91000340042842203070880c42c40400c200100a0000201c051070440311980e22101e049406507800b40c0003400802c41045480304081c82034010301c00790000c90502203502088242514008e403888101555a4050310400000b0480713443c00b110b00509091000340724a0b04086c0000703070244200c0c4a42d1052250001c1c0036011034800b901550760b440d0b000b1456040d01c65a5964580e129404460106e2051815680700d540003c004640099801000341100d0740501810404a80c0040200301080450005204103014170441c0e00915204034031400c5c0118107546003c1e00902512210583c5110301c2c41401403104103142c0c400031b02008250440401c400b0503141d810402e00400003030b03100c01c030015540c1840014820303841048000311b0380d00714 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 380972751 1250 380971501 380971511
    0x30a0813080c090601090501050706380909060c220b21010f051311030411031204030201142a0c1c02090109021c1b0e04020a14031909080706 62
    0x40010f1020122080c07408202c061209102c5540f040c80034080c440c0c442d08000030101e0800d40c100f1584284203c11500c00401c900d80824004600300307481003180ca007a10020324034207010300c9843d1285c0009200c0b030000c000108110041c9a00c1c62007030b01000300368004900f140f80d12030a2044040c1d00c1181460f00d50007200401c40e4403e004030010303504030b0307050280032840c0500f0601006400c0c90350181d40c4000588901d0180d0130425940001c5000d20721940700074801200603014981800c3c0c00b800c550b40070031001d100400c0540d0308094400c480d841088240c9135118000c1d884423401c0c3c0b818103200342c1c00600021012803102c03c002100112900c2c01c0f54071440303a041c0807811500b01218602c0094000503802c004005801045d00980b40c1c070096213020115a50740328540604403424081c1040056864600c5c4c4402141c002088180400e800ea400350318100d1030300781c040c140c2242e410101c100c0200010000d5004000b4501240710103e0480003400241200e041040c120b40041d2f138156020380c609 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 380974001 1250 380972751 380972773
    0x301120812130308090c010c1214032d31050a0b04110301020a0c150b130f110a020d080408040801060303030608061302010c0f021809010e0c030304140906030a081308 73
    0x61b202d80141c2c050751520071442c1c040d640c0d01a008000c0c03650801740090724a00d17030040c440c81c001961086c02a040c1450380c1144420321082a03100310310703545c1c400c1c16114050089a6400317218444058400c2c141594211404c541403101c5c01c910003e01600038003a8901c2002081285c1108034020f50040110200c001c581504043c203c0c42400c0441000c140722088078000038101c50ba0114803070100003800038140a9070fa0204010038415051480d0590342c50b904950304144a1041d100e07024a43c3c41c02d24141840d10101a40c1c6130300301e403450028050307041e00180400c10100101d4029101500c000c4c45000e95034600a001b405081c05250841d01400000940700e80d03002503000c094039016075541c40610741d942c80d806040001c4400c16038008410a080c0889600351841440c0151030318030001a04414072a43c65041c80400c800b0700780300741c00070401000304103101821544409021034100c02c154482400283c80c190f01403d0003800d107103010500b10600076245511404549002c2c6c01c8e95041281 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 380975251 1250 380974001 380974003
    0x7020901140102101e110c0724020303010302060304020409060e0d09060212070201020601170109050a030504140409020303030a0e1f200c10020315121e12030112081213030809 77
    0x1118111100d4441740007074900c0c030f00281d60004201303c4001c0780d03a246405100f87c0818200421604440c038007030503400b80700f5600ea030707a80003082000380c3c10700c007550071541107030700055141c1700c0517101a11881c1c4902400d41401280d0740704840d01400d210445440398034803a00600461440d10600015000b001d01d14418480460200c80141c1d605a001e031071aa800d28407024048000518040081d41d81c0b07150b031000003002082900340e01402a110992181d2521180640a00704151614069400d12030b000d40140c900000b92070300310280280114291485824040c07030110001030610b4400c4034401b000c1e4200d61a03502c2200846111303a0f903070f418141c11001c284c2061146607400409940100a001c10020301079000c4d40d004618401c009101c1e03a102400103820540d60072020045410007003901030200e28141d0311031803c0300880003038019180766040074021030105100c2d40100a42c2e80080500300702440c000c030742086c2c182850071981c6051044940d040c8248894045012640d580045401140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 380976501 1250 380975251 380975261
    0x411030f0c0622031401061412120307120510050a1502030a1b050609060f130309050f0406180902090a021602131104060302250503030109110702090114010210 70
    0x340c042e080c5032034829400000c0b426100940342c5842d20081c49500071001806000002903142050000410841d0030121040d40d500c4480c0103482c0b03d11419200d0000002d0f0100d0800d0030320519505640d1240c1c0c0f601d10070765964541400901415242c8010402030000a6181d0340c16640700303075105200541c5034842181022080d054000c0903a00c14841e514109114908000d00d03220700d442480c29040f15641c0f1203281800c15150760702540c1050f4100300101000c1d9120a9000c82d07003914415140e03c840e00c0143c0300c54420f004281c004c0f00e40c40e6081080d9129078000074014005040e0814401342d00310b00b490000c0900c07140072031091041d4004520922218003e807001140c1c00d1140400c4200180d080080c1818070b08405802c454450000c00c4101511a01408c011301c0662400340c0d58091500c100382090141ca40076940c0400c001540b28017060001003a42d054801460b8009001d642c41c51800003c0c0c0609a0002d5201c6502030001c0b980f5044d0550f82d560400083c0c00702d41c94102c0d20700d40401a54 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 380977751 1250 380976501 380976523
    0x6060801050906040b0c130b03042a0b070303150b0403030f0206060105090a050d020310020417060f0c040501112505190602030d09020d06050c0a08070305012306120411030f 76
    0x1101078004242c649101c5001004205c0c2c2c000c1d0030030007080e23658030071903802e4104913026141640a40780d2101c00d010080441c0c11340300c00b4400134403620b40c00c044800c0c0b610300071514042d0403d070341e4100c54965003085401d01c0300038017440000c5079203c699a02c0d00401d507503400140e04005005680c00708845501440540308103540c010014554541050148180001e10b01403d0b40d0501c280381041074260b0700f910060001c0c040300c120200c0b004174148406850302c41c000e4202080c409100301004842e441c404203440c2600d409203000303200c60141501151400030201c080e07011419246280320380b4959954036040845405640c110792000200c0c0419000c41e509208017005a00304121006803c04a9072112080780d100600326404041c258030341030b0840300704458417140380e00f001a0540b420360300a04103503444441c601e805c0c8000e44c1000090903800340991410743c4004821004141c1a42e1a036064510341000784031351032003600d010308181100140419442d8024040d10030900c00c245000b0812030800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 380979001 1250 380977751 380977763
    0xb03060112090510051008150903070308102412152c0c070611032a07050f0a1103010b180a0b060406050c07060305090a06090512070606080105090604 66
    0x103500c01d90844040e042c1d1030b108452a010721000c154050005200d400d005005080c4454420350400b6200c62800c810345004140d004000410000c0590001085a4010713900d807400c10300715282c00c0100351024109400c6a14501e918082c81400c0814803510a0302c41c0303010381c3c1e8203c58041c80744860300c21500c10003900004004050420703c6512003600060a10145540520724100304049035180c05403000d5030f520300500f60018414081c85180d002e80050704031006121842c6061500b85442e5080900040d44c034102a14540d0340101c605c55015034a400d5002816110380b03030040d03032910791514010a001c8a40402504516000d030905108050714213001400840311001d01c01900079000000821084015841c0c5a030032010f5251100944002c0500f80c54558841c000310b0300071410401c0c81e800500405151608100c00342500003001a51550040000548090542005030401184c0e5114921b612070010307111003002443d61040f4115100030000300107644401628944400040d1005848 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 380980251 1250 380979001 380979017
    0x10b0a032003120f040f090209060d0509030f2101170d030213050411120a0506010509040f06033e010507150b040603060e0f010e031602010e180403090b030601 70
    0x3402225801d10809039074000d04507a50b0126254142269a01000107003a0722000030408000803070740b45c81188003030210400c1c10350078161100d0100741c103801903124040249880f0000308114400030b00840d0003180714410010756030181104000004a605000d5140c0500c050000140d4030b403030845441c40c0c615144028040c22020488120040e4020341c22400207590700306400101640d40784142c0e00400c001d0350085840d01541109030582074801440e21001c0e50908040120380c1e0fa01c13008603110701604680003c0c541656040c130100504003504020a0b203010001032290990b0082e03100015031a0008504130391a400c403c0301d9600d01c40d03050140b4081042032043d072000411544039204210100d41d80058040c4109001409441440c0c0c4291080e0b952500d083c40001402d00c010390340203400b180244041810102c3c11541c038847e8418942c240e03c00c6003d610116807255600c90b03054100200702e01c8c5007008074944a07541290942c3d084000c10542040001c480100d84152445000305071034041e1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 380981501 1250 380980251 380980283
    0xf030a1e0905060708160e01020705090f0106020d020d050403020402030a02090a0f15260603030c0102040905041a0f0a02091210140f01030803040303020d0e03071101081b0403020409020a080d030509010b0a03 91
    0x505034104079029040d4080c00ad0085541c4d2a241021441065124121500c1d945003400103801c0048001e45a0110b400c04002e0031003054000301100c1c04c41e903040e1401660790381d580607044000d00641c3d0209500c80340307600000424070050401c0b00d0a40300140303200380c80c44040c05400d442c0c41c1049032034410055002c190300d1012200c0b10880c80c0d80040060b040e245480114a01c0e1800c82c2d1213600984040e030f680b00180300c184082c0017281095820ba030003c1c0c082d07504100814148444005041010094000a150166807a904480844140c444007160041c0c000c0c148810301400f2030381c81c00d00c01441c80340c7c0000e58821813950000d0403241c10000039455522540c4084000e540b20b070010b1004c0a44421782c2801e940d0040000704500b03401038140b880e8a13150712000500d0311001030280072035400f400302c0e00307911903841504a500722541100e00040348501840401c20840090340064181d02444191208182d05034200b580b040d1007000c0200031860841040240d103000c1030002401d107c0000c40c940f5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 380982751 1250 380981501 380981507
    0x206060117010504180c240c1110020f030c03040311061204120203040f0810112505010b0414041b0b030f09070b03090106030606080609030f030a1e090506070816 71
    0xd03048601307030340c103035580c040361038030741e11007191f640010465410010700020381d00341c0e03c41225400d8140c1c58014041c40c40d68803441051403102020600c1401c0d5407803002c0144d8002c12049000c00c602c1016203840302c040321011603c2c1d8000d1311041c0c503480c060000d0070005103000811902c68000d940040038051f2226280d40c0080c0c06607000d0740e015480100310102e070040440c048500100003c0c4020309103504e030590341c0340545855020421a68009101030702502c44031103096118284080e190702c010003000d007440c034013404811000f035800c18a88a184240c12030309402140c819401103400c1e00c01c0e296150507448900f0b4080c403845074420b80601c0891800d43c80155111f40103030b400f008603a1750700c1d142c0030440d541d5802030b11400d106039554030040040220500424005040e02005080c1034600540003076240d01c2001c02840510b080040010380e844155888142070150742c040403180d50030700003010001445410380941e0940b08900001d0503451199403400e1280d014200301100d540b420307020603 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 380984001 1250 380982751 380982761
    0x4030f030e040914011d19080d020a0c03021b030309041805060a0b24040504020a0909020f040906050409020a0504020306210c040606021501031b150804030206060117010504 76
    0x11401c0052881c02892140d9a0340900c940300c030300429441c407201030380748501c40c219071031401440d50408040a400a601030081072040e10b044c04442c068a1554091501e002c40d44554142d070710700180f011600582c40399120501c0030842e4807940840c0c41a09582810306050b0480c448040e5140d07204008031140c070b0405412001e030407503000c4200c0c1c500480c103550716801c1280898400c003080e40d641080040d145410300840c0e8a03841c000000400344e04440c01c000599201302c0c0159070156800040000b241885004080e00a1212040071074a030a02d40340f848649500a00c0741d0410103041075404071311403915100e664441175006200220f5145032106000213034100624007a4402c12285080c6a10b4403001841021400000c02900e168010304c4200030842e0304981000045502014104401014001800e4192a0011010107000030000c100041c801d860b0b40242203054003200101a03445d412904040c00f840c031980903500c581d52680011114900040e00454040750782c9001007107142025400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 380985251 1250 380984001 380984003
    0x90405060115020f0304140609040f09200105070f0302160303020c0109060e0f0d0204180309032d03052d1308030901120f09060207051609090209010519080d09080c0604080304030f 79
    0x8070f08010040000608a2f0921456911840d4070f40c6891404c0003210b0002006841202e1039100402c0880ca0009100d03014110004000d480c0301405041858000c10002040f2039110702c2009060b9201e20700291101c001c0103021340400d14030031020400078041d401480d80440043d1403000c0700c0c41e100c0c0c2002a040c45400050b41c010f5610780340c1c46228050110f540881c00d009403204d803032452841c5889000c01d0200e54035009194540d6000d02500003008000340c4100d034151034056156210005134803132011701c00c0f0120000944061498000254410140111140c80241c11806540e1a000251a0700c00c03100c216001078040307200c1000c452280d030301c05034100d010700d02d001402600664a4004903440b05009071790a50015484034280b14801402c10040c00010400344481c03420399001c61641903040c0a00c61240d100f111039501c0303046420908070020004842110200c00c441c10000d0300008c21402034500c10f01802e0448a61420103d0850742221458070086107010b1a40d1550800c0c00800d80b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 380986501 1250 380985251 380985259
    0x2010c061104060c020a05060406140d060b180f0a050a12150c020c130c0c081c050a0b0109080601080303151201111c05061305060f090405060115020f030414 69
    0x7081c0045104000c001d00058540f40d121001d1840341801005105801c0354019882080c04000a100182d88491079004001c0003120281c2c50305503008410028005541044040b00b50201d0754058201019580f64000c05080d0340e50a0316200350000d2180007003c60007269040340da0103004100e11070484600056041c06441c00b40c000c00c180e24003500544001e041c0f1040160300195448466140001030606801ea44650410403a2900300f030103812101c0c42800030b0000c1c03d02141034505185400240031507800d000c5070400c4a4900494801c00410841c45180c1c005000a14085156200050b40e01c1c1a03c2da50f1000b0340c00c41c2c1d1503201050b00307000214040c0b9002040341310035042040c001d00840117880080b10580e03803100600b6071810611419140e02400300e07030034038040c02081d807204800081400d20031030000c2081e82c0d5074800301d1104650347d207005400290400420003845400b2402c075040e20750303030440400d0780e030ba0b00c10301203917910416040ea000c0b0750010482080780600041490b245400c01038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 380987751 1250 380986501 380986511
    0x82b030e0f030301170f1c09030b1e0705040308090402030a090206120108120702060a0f021e030c0607140a030506191d010906080a031206050409033902010c06 70
    0x1203031603060409000381109142d101200501040b43c0c0080c0070008402c003c4010416664040202691a8030200e200e24895288104448407140b28514a81c085e540048008026040c2104080e504070b44038010140340c2807000000c1107015100303800300c0341120741001b46e0314100081c010410009600103020504400e41c2c8004500c0141ca840d0040c0211140c41d11040161390301d400c14140c10508880e0018840076010070107100142d54110950751006020710b041071400c0c030046026481d004440044c24443c3d2007a400e1740d807003110700000030000b016010f010b85646072115031003601c42001040c1e054921480611503007130034900c00e90250340c1c404401046420b80e00d40301c40f0072285402c140d81250030b0508840d4500540000c00c2c544c1e003030040500301e5082200c0f07403405140381c0d15101100402030411801004440b195903240d0400000ba0200401c10801489507142c0031308010138008401c0710300f1004808020003103c14045803e0900310301101d100051031107900440740c031300314a942280d04d5940c80c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 380989001 1250 380987751 380987771
    0x20c03031e090d050318191517090102042c010b0a03022b0b010e0a1a0f0f0a12060f050906061204291635010e01082b03 53
    0x118024400c58010409565a402c0072011301b641e00c240c083c80d907401803400140900d036001600250808a0b085010350382d0460610140440d68400701800c00580084610240300c2c864406600400032100354170100021110a68480000010300c881c0c00042d180c4070300010050030982000500d946100b51400503c0d01e400d03403280c1c500c2c090500301303544541c0351514100041c2280c01c2c424a030426a00342801182500070000245042d032460242154044000000d0100402c80b00140c9400013081c90255881d22101c0100300680d812075503181000887e55281160800568404c0c4001e07191018028202c0c0c90a140c144509801d014200b282c112400b00001210107284503034260045204a08410145c00b01c1146068600701c1c0c40201b4100005000911071845045c0c9040c0d80544240e0410418030302c421100c006004140000600e01c90b030060070345a002e40f40d01d01800b41620200380050444e0707601d131645180e0b9200310443c0a0329085601000c401c145512007403400c01e81071540740c00315900041d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 380990251 1250 380989001 380989009
    0x30309040c0c081813050402030c010f17010902121014040207020607060e0a061121090703020d050c090a09050c01080a1e0506090f070906050c031e031501020c03031e09 74
    0x1000e50130690304c0801c85070780f06440c545444605902403c201c1c062260341041d4000980311a820306201e41032290420a1415682c02030002900c1000030b803600b640c00e0342c1d4818400b40070394070805d0503c810741e10041c002001040f1071400e039004d881d2801c0d69000985543d009100013544402810b2b03074401e03c140842c00c0007918500400341d00b030b58200058226a801840c1034002e80d96004101c1007c100c090294036080a0032024200302c101c4001980780300d54a40039609801d0102c03d410194000039462000707800d01c94001142d5144c01d0003900d4003101940c6108560048500c60b0100400c00e4200b0b036450016584500c0c1401d8104010030707400074486130078481511098071a10003102015441d18100405450004581544401c480e00303050303a540f42880c4024103101c110f00a04051000219032203c01960403c1502d100e00300040d92034500c040c030701c0501d0031103810444550720120014048241b01d94400b10300094108005030040d4140f051b03074241070851011074440b984101106201d038074030f00e0307603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 380991501 1250 380990251 380990257
    0x50103080d050901020406120b0d050f16120305040b03090708010e0d0206130b040314071209030221030a032a050909100506040314160b1c0b030309040c0c08 69
    0x8421031100c0d41d5003104201c8201a208001c00001d8164810b2004200d1943c0020010034851940c0c90b00042150002000880c52484081c000d0705501c00c4071251103103000000340c0d040700c00441200c10100250742e60050303401001080c90050001d80c0c148004c1000c8100d81d0099034024003280155200c050321216a035003140c05520f01052076034044042d84200316014090399402090011013414000c21648900840120142000b000c00c4003410002203202d9808054541055020f4200e2941090f455030080c81408103000a07803041201002c241036070542e0343c04143c0109116000740d800d01e008174000360001c1484810311aa0500361040706043c4803041c60304d102c168002900d881e0f403280b03505024003211040007046a41c5580d100c82081c88259541c405803401c0701c2d408107169402442d14041e1909292081a4440e00e002d00c15201146c10a0020003030710300050060342c0da210f1500c4e240340c0c030015100c0c200c0d100394040c0c00030440e540a500700f80d00710f40b111060070300340504003034040e03554169039074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 380992751 1250 380991501 380991503
    0xf0f030a120305010f0b040b193b0306130605090705120d02060612100207030c1e0b0a0b0a0e1008070b0306010306051012150b0a02030729040305071104050103 70
    0xc1c1d620001400f24845d10301c2e451000d4000c2c80000c9080c20f0410310781120038030403088060780c04501e88001d9010a0b02c94003141038501c400e1607001007100b00d030320190761000440d0350081e580000042d1041c2030318100007030b40c3d92185da040c1c0003001c032256054540000410b00900602c3d80c90081c29030105968075101c407a20284000070b002810701011000c402810480301802640c03040150050300300c90744800084158058002c0000103940d46400d2906950001c12650000c042034071703482e03160600d0501c2107001480e140c02000092851355440c1036003400c60740e101c4985030b44140a84018083c4404e03017001950b000e81403c468003c076545800e0000c0c84c00d903841e0310803c1007042c00010040d0030b50b810301480000380010341e040246074400c410b0180000f00700180181d041ea54401c10358405074106241c10340140007212a0650340c0400e400000c0d183c0d44010010394103489122208031507500c2c3d0f5800780c00445110901d02c45944c07103a680c11105a0f114140503992020f00c0c01d1080034503078540c03055078021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 380994001 1250 380992751 380992757
    0x9020f03040c15141606061410080132091f0f0617061302030a06030233070c150c06140f07031503050a0c0f080304050f0f030a12 57
    0x80c0340a00e0b04042200300d5400c99980401108014000690044a01400200c0e031181c40e581315988800c1104209640d80302c041c1040f410071400164280741212020320081c01039039102d203510000344040d1041d05080c451041500c05028441a05c0b4250b40d844490076081024056030900c900400034000700d0040d50750310660000b20401c11411400c500c1071400608001043c920480c0c40c10502801c074542007001d840780480b500c000105a90365090b141900b02d501204110b4482c141801010700800c507601040707004c0e024501d41d0500c010364a07002c1103210b01c1c0c0144543c0440c0d40030f5021070510b41107a4401c440c0c042440c480856500400440c03c1d400c150030781e035070311580551303802d02105035090000c1c0f117148811007000b0700a24084a80946a01020506002c90b10100300c001c02d0011507215400a0505e025200d49001000102041c444c1202e2400201c3c1107560780f520700a60b2a40709502c0348650141000d84003603c2424503004c040c1c3e8a01c40103050b221046d0303094540f64040030841c1400c02c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 380995251 1250 380994001 380994007
    0x1205070b07060510120b01060305040510060305030306032103070c301418060c03040f1223060a0b0607061a091303020a060e01020418060303020d0e0d060e01020409020f 74
    0x8400c01d04c68544018040d190f080300112025494507507074420107000d03201c03c06031110002400e1000c1081110250b00603c2c00030043c00342e90f030030b151380c5070342064803024031034080d8001e01101d051034804003100c120340401000f440c640300c240003a101c0f007603641022070b400b10f4142410f10031007590781d502c4001078000d0302201801e60200c0c600202801000fa143e031211041c00e001255449920b1403400078600d5007a10001e6640d5158010b183c0707180250b80c00b21041340d410b181e02183d9110031032a039110b4580700d5034045181603104c8085d1680008050070380001540a040084c0070310040e50401c01d040c800262030189007500d1a290141036031900c0c038078500c3c6a4000800700c10541001d11038103601013068100592811000d0360004c1d2100c590803806041551200718184503040c0c00e504490040850341030b803291206111a0303001c041c0c00b0a10054015014540d0391011181c01111a80d100480080c00880c1214440c0d9031040141018180d55080350360038480410280054402425031404415005403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 380996501 1250 380995251 380995261
    0x1020123040303050a020c1b0112020a0320030f0703093e0f030a0609141603030305090c0a03080a140414030c041b1d0303030c040905070201090503041205070b070605 73
    0x1a81c001400e15582e603407040056244000011400011007030640c0c490306404d01c40d541c0102d800c071000562b28002e00c0d10000700c10142903056031001134002c0803201c403680708000071070034004680801c540c03459041c0e6031540000c035000c1c400d81c05141c81c40d00c81c01d082c4042c0b1313040340450141840040400e41d10341940d0300600e0040310f0380c01d2276000086004c4545011440040000c2619240d0041c070041c00541c07203592042c20045c215041920041c103110455440c614125607140c1080e00900c01900420b15100c0843d03001e0340003080101c3e10001c06400b41800c0c5107907603548c1f030703541c0e12640c0001d0400c480780d0070046020010000920081800c10098100d281200301014101920280c0d040e10962506030106d41e41100380300000310442d018140042610050450342c03a098400000003641400008204000440e2840c050010f6404650b41000240e40d8500180e0880314a04405000c40c0d0040c4010005400703400804208944280251380c0c115580d04242c0d40c2c1c5810240c0c040ba11161600c0401c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 380997751 1250 380996501 380996507
    0x11152b05010609140d21090e0906160e0109150507050d27140d020a03060204230907020a02091005040504050c12070b04050603150d0b01060912031706010201230403 72
    0x625054011a0f0500005101c3d0303403540b80154032804002c42c81c9085110f60070301b450040f43d0803401440142181105850034011003900ca0a04540c100d010742c020341e002944040c03064121007112075041e114507841a04110a800414040c4450716007009410092000010170a0001820302a0540c64901489080c841207400d07025208a9401e1600c0701c0c000308002828918200040c5488140d40f4000d13607048900115403040c4003608041d04183c000034000480e800204400131080c958060711041e10a0100108002c0c440c060b603c0b04c00580c001145540945003d00d5a01e404c01d0316504000c4105076a040410191401103c2c142c615030404400034000b03081502c00c0440681042c0c5c050301c07102d41040d0781303081e00740164040d00d802090301000017043c03050400601512108010800c5224840f103107022100e00070240106c03400660070700c10000314010100552211981c0c992640c01c40550380c015418204000108801d046640b1800380407840c4034000c070350000703800c41c694500c641c529040c2405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 380999001 1250 380997751 380997779
    0x19090b060f011d10020712030504060905090114041109031906061a03010303030905030d060e0a060b0309030a032415030c1806180302150711152b05010609 68
    0x40360510483c0e580c44111243d06071541c40603034070112520b070807101e001321040740740c40c0c96504010320b014450030f480e80915401c000038008030b41241c2c0e50496102c0d26032040c0000302c002803041800b1461140d40c2284985000e07006080e41218182e0024103102031070000a20700a007522404000c8800c142e002c10910689028a8000e801886c03030404006006149508092005200140415548400034410410107004490540721020814010b0b01d440391018000c8e61010389009451516003080016540f4280003038901c6000759201660621110f944150007030040000d45607e0400b410205003603000c1c8407030002000e040300c54914118203041410140c2291421664031052002c0c818041c000d030032040e801c0c0c000ba0f44191901e102484811908a008250f05400c000e500c00c50b1031461041503060715010b842440d004040801665101d0030900112115040019041c007104214403016a081c419030394400390740240300303810440ae0401100d412104207070403000000744802002c108601d0404e00f4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 381000251 1250 380999001 380999029
    0x1020a0504060e0901060c030819060f060e01020a021e0d05060c0c060a06120201030923010b0112051b07020d0b0c091f0f12020417010b0102121804020319090b06 71
    0xd800782d1541400c4000d0180003490400808215140c40050088010304042500841d0310f44030038800b0f2a00c40c4c00300e9410051370700401d40082c8504000f21025840024003007500c54001d0512080300e50b82a2140d510050f000c11020341210510b4101400a1800c001c01d40c1305940c184000c2c0c4e00c074100c44500d9420321002510402c3c191742051401c0c0034120b1000f500c100d1740ca42c2401c1c005107000003480d004600c581c012110070b05003c80c0f0f00504424507011b4010500c800000d981c1d0350b080382c4042c003038074040382c1d0140d5100c0c440761440c3d061102c44c8a000740044c0300281c00100385142e03541181d4ad1b00340700000d0071194500c1060b40031510610600f0714828804806446001d403001d2011083d8000b0180d554850607a0200301440840f049004900d6044030003034046500400b51310348000030030134080c221191041e0700504c544005c00e000c1c16894400c1e10702c001e502084000284072a1010040a508050a0001d04c44011014014802080d00c1034100051180394545124a483d0042205c1000f41c00300c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 381001501 1250 381000251 381000259
    0x3210b0904050106030c08211b15070f0f0210180b010605040e070c05060708060f06070309080706020c0d03050904180501090b0106050319090f0506090f0714010503012601020a0504060e 81
    0x743d8401b46038054221400304280d401490300c843c9020b0000c000c1d02400740c41275016000c2c10390b800c0040010045498803c6425031205040301d00202402c5070540c01080305040180c03c031900402d0751102c2500011802111002043d5202c0c1c2c0c00c2d00c030500301c0c98007030340508081040000c0400000f0b885000344d84c0d000c003590400d00c0030591551500341d00e03820f004100f00100410700d4005a42c0c3d0703031948181c030b0059a02030060f50322a82e0310b11700500751300114084e40b816480b410300c00049039440021100700384040030b0b00b20403116105980546082d00000c902551140d107501c0480c40c1541074140003e01a40034800218141100742810184120180c12410030081c0c20001c0050039004e66114000394441c03458001598409030400c81e1010408000080244c0108020702401da180015007050165940c4140c81d05031b503440d050000b5861300c2010316804203809000402004401450240c00e200c1080580300914503c40c0c451802ca030301001030a00030800201e000e0180640c4004081e40c480e0040d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 381002751 1250 381001501 381001513
    0x30f05070b0a0906170f0601111501140f030d0504030308040510020d06050f090403080126060708060102060f06090a0527010e0705010809030d0203060303070c030c050111030703210b0904050106030c08 88
    0x406c2422600000305030714144030300840801b0f09290100084028080554050042942c40381c00d0030102d40032210643d407050320005402d024615001c80c0300800d02080751a001d142c02d1840d03034280da040f003005005862600944980702d102d280180001d000d80c4828041c0050a142400c080015540303190401c54000c8a4840c10400040e402030400d07810340b0303e00c0301903c0250701c200303e49680d00c000005a0750203c1c040d80040c408440d42100c0a14009c0c1d40076000e079070342551004541091041d04030f4100e64400e0210000c901008100d5001d26003140342a00c681a0700000d4001415103400c42040030781c103503035481c03180a100c4102070001700046c007000d10304806c00d8144000280c2c1d0307034003072400d88000c025030000210340a55000c208680c059544001400300c855a00d08040c505100140f15040c0410420860421340c0b40c4d012007141d1550350b1540310140d80c3c014191001541a00800841d001641d07980e40144607a503992050900c594400c2c00007142040c214070700f4000e040402d0303000349102e40c844 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 381004001 1250 381002751 381002761
    0x4031202120723040f0801050c03070f050d061d0106030507111c05040e0c030405010f020319050403020c0612010503010b030a02061206010903020a1403060c0310030f05070b0a090617 80
    0x6107015034100310145000f4007000c06041c6201042c6036801c0c50248031180008001503c80d103d807031004201c802c200001c20484c2d50755140012039110888415000407072035500d801035540540c2c007400380c0511071000051030640302c2c0d0b4801401458200c00c60000c030281c0c070040119a51500445601891070314098010440c01c5a881e6950340e82d091000070407111301c0e25501071503841101071702c00070540d41074034080303e041c6002c000080b80d0040ea810ba40315401c20310081d4141d580d600840e4007031810032103080c811248400d0000000d24001d40110218020400185016507840010702406d1000710410140c5500d03140c105800c480310180e4507400ba801a2005102595594081d10340714038448012072000d54802c07004881c0400d44e070f04003d5200c111a0b8011500e4a084240b020402806400700e0b0700035241c000c12440e00b03010460354140c00140034a42400060381996401c940d8612490480d90103a4841504108030307008246c8400000c0c41d415010024194000c181d03c12212103168070440c0d038100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 381005251 1250 381004001 381004027
    0xb2521031e020711190905130807020609010306091a01021c020703140a0501090305030a0b0a0b0301050d080f04060f09150e06070201020a06060b1b15040b1e0c0304031202 75
    0x501c1e100c40d032003941d02060900500401d0703d4040100b1400a0860200c0c141c03115184124070710501607003960740e02d0540010210108400303c0f20803107401580e4a41000000d42c2002005d5208034400c0381090b4890b0000510482035001e900e144124040d5006840503044000a21707140030030483c242036403280c2179a1121540c000c1401c070143c0360450b4420107800d1030146840d00c0c003024004000d02070341c60201c10400741544000551700034200a0000e002c900419420428412201c0c003a00ca0702030300400c01000b0b1441c0034200d03245000d115a54007800c00c1015584107503c2c0d0020340c02080860034402c0300c481480e9000c3e080b4000741c11826807004a00d05000700041020303407400503c1d80100000600403065a008000c100c0c03d860340b20703d091040d1038a0b80710070b50560b0401044141d0b8050b00c1c90b01842c80c04000700d025110b0454400d4040d100c2d98642c0c660903541e404c064144440c13103502c3c5160b848401d9803030410318401d00c1c20050540c3e4030308191500030618501400b90000c81c0b441480200140c0903 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 381006501 1250 381005251 381005291
    0x605040809190b0a0c031e0201141305120a020109021804140f03070227151e1e06070b040309061b110f011412160f02070b252103 57
    0x9503e24001108002c10300d01031f108140300401c8814140501c4400c540c40b19030542196440e2101c1510101040c0c840361400840a0210480100550407690a48169411030000350400d09804d20010440c000c403038010415250700441c800b03002ea040f0104002c14814600751a2456003a554002c01d664000b04000c01c1d12800344c9280280300301c640c412016100103008038110180005d103122240d19042000320000c039440951071590250000c118401e000c00c800705141300380030202401e080b101203040d00348008800c104925140c1e0244050000a007c80d400380201c602c12131080e11b074075650906042c0c000e41600210b9107490728405c80e8411034000110b00c4080e44007035200540d80101c103890500010b807040c20360840940b8000c1000700f1011070070468002c00600846074101040c6510b0340400c0700302d559050020321800543e0106608000585424008100e1121107800751200c0301708920001d200c3c0d213110101038502c004124a403162221301c10001d01c01e10525402c040000a21900703104240d40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 381007751 1250 381006501 381006517
    0x30301061b020609061218121e2209060e19050411030f1b030106030b16120f0504150b010e040902030c031203160201020306130207020d0605040809190b 67
    0x3034110341e82070086480322016180f808600070092502d5400300c030040f4602890803034100500b000d0060001c2d040e608045101c01032508103403030892501d140900b00041c170900021012483d00c1c0101314001c0b040b0289001424070000f0060750150980c80d001713500c03003034641c0358100c01c0100000c0340030311095401080746501c40c0021000045101c3d030300e500300060a4a6018400c5c1c0d0540540041145808000b14088402040c4040c401c0400b0800c601458203e80160200900b03007004400441c01c0800784a122052790a00e6251a011030a130851100041d60503030075407018a03030345400034030041140c1070707000c070303200d40940c4d80d0400007100030301c0c0000c0032064100410341c0201d50318462a429910148614464414082d0840352103200709454000700d80e10441380141d0f00809032403005101172040c02203d002c0d2000504100c00e2009402508000b503200400c100d82c443c0621100c400042d18900680f4400c50050051a445000113428031120340303941ca501d03240c2e68880c44d03c14440d080c406c005651031070b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 381009001 1250 381007751 381007787
    0x80705040e030702040f06060210180318030f030305061c030c020603070504080f06062701031122060906050a0303080f0a1404140d09050d030c2102010f0e03030106 72
    0xa103142401e0341c0d042d03114002c070180d00142401e4914286c4001e03604003800300d41e030307581c05c40301c2501140388420111803404c0e0030300c0e0200301d0390b800410110744245805035100401070340841c0142da41e541c13550b100101213030b4200c002c41e40f54400c21266140501c80030030052640307180d1540c02011540d00074400030710b150000784100804004611854850015100601520011168101c640c5041181d1b03d0f28222540f6215000c5404d10304081c1c0c260041c0b03104442011001c0180d030b80d0950383c038181158a070541e55074100c0030711010b90030040650b00c0d41c4c203030050700392200080c840d003015108010340790a070304554062601c0c41000c05c00031b90b0240d1426409085900b00300c030280c88007082100a004c070700345118903400440d0140003d01941744400421344211404a501c00030422500740d4203a00540b1038258450091160400801c1c042c0c451030b00c929124554074802d41100c40d40b181c400d800303085c500c2c0c0010b07903545582040d4030a440c07003140384020b0307500011030943d80b40c03c10041480760010850021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 381010251 1250 381009001 381009011
    0x30906040b0a020c07060504050a050a050d030c0f02090115020705120d0509030a06050726070906210e031b030412080a0c06020703030906051308180f061911060108070504 75
    0xc00b44541d030640300906000790030b8510407135036004018003940150150324411440c9080c0000c00d860321784803180488202600d030741c2064000d618180c801c00602282074942c5001e5558007030041e07076800c108034081c0410100480701000c500700b0082c80d0140c10303042a80102d41c90340d08002403401c00518200c000e202440c0950740c0e5400240464106440c0c5800105154101403d00c030800390415820711214205200c1c0ea0b84064002c01c1c8444040010380301000880c00c89481403102c944100c0a110b810400071182c00c00030640a0360340d00894191500d084480d400214500d00c1040a51888412400e4454019802c007030034986040001c40c41003400610240340010b11070348490103050400600c58204004540340d410a08000d00078144d00c00c000c803202e51a203800542d068440041a0301a00d8201520b1400d00300d0120303090404402437411140c0c800031031a0325440698034030000f40001050907e118031076400b0000c006c0e1081500c1945c05000750442c0c401400889400200b00b801c5881c1280d01040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 381011501 1250 381010251 381010261
    0x509010c0c32010e060615040303080114060c1c14040e0117160816080307030c030806030a0c0b09090f040506040f060e0d0f09052b061e090204050705030906040b 71
    0x80805102d842d10314075400e0203481501e00b40045517892003030900351a100c0781110a0819020300d44910f0000902040d01079005205074200d980500d550108040c040b10302c0d1240d010034042c9040d480703040b02e070780d0301032064180c030705c0310380d0120103d0040008585605c1c242410824401d601410501410403170800384410b4101d4800200a16180c050f10340480c5641c0e142c613410f104c0c7e1504040842c02c101c03c0d80f5a080040c141000208132080d1a4140d85e07103804104a030b0380c08403000303e40a0300c0594540701c1d1280007400714200141000041c0010600d1a66900c5038a05001c50028000c0540c03200703500034402c02c030100d90040346441c0e10903800b00b1000d0720445a4a0050000d2403ea0000d400d10b2041ccc5000e00d000d02e400240b14412005552645245581c1e28010401440d10744940720207400b00c01c46401d02d185070200c4251940c07a11802d00401c41c81803140400000080d02403915181c0d90301d445144003941003034400d00b40c01600c685021465840c2211407107a40b90b1016000804000c12640012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 381012751 1250 381011501 381011573
    0x10e04060e0c18061303020307061d0f061b07090e0f030f03060307150503090105090f0a0201180e2401020601030f1b0b03010906030b01093806030a0509010c0c 70
    0x3c044100010003c90b00c40c0e400c561040b0b440d0016010485c00b034460044003203007071030145504004c01e00c111046510f820303800c08103001c0c1c4070056202080d0448002d0048101c0b51002c0e40c076001c440c0c5440001007030f000e032070f00410000303603607003176005898a4000d0000c1404100000c0300b00d41001040c5004250340b40c0351140441d24011803039004084030240440741040844d0300c54001c4d0b000d0031070b20000780120749601c2a004d40b101000e4031158034581c00ba11100005501410a24014008a0b80d41c207244603a80c1400355401d03001103030088510681183c9c440c0702d048800180003119103081c03000305919815640c034196a02c100e030740701400c402c051426800c0b01240588804019040309003055442e560743b4076411010303050500084401d5800c0c800081105e4196100d0002c0704607403034078205103551009100840749144606a43ca81f003052985140103602c41038015805031000403c002124034010f00b4040c03c40790410909800c0003004045040800c405081219904c1040c1320804512002100a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 381014001 1250 381012751 381012787
    0x1061d0f0414031209010b090114010c0302010f1a120f06011802160302010b101407080c1c0f03050f102c0f010f05030313090b0105070818010e04060e0c 67
    0x3042d49200005046403103080b07001105001c0c0d040c80e4024080350f0001820010030003030074000c0c0740c180801440c1140709580b2800642e101c2d81e02034000040ca213100340020209444035040211090300071007244541600700010f5038441c0c14120406807284d880c1203910140c0ba01c0040c450228140d0404080c44c903003400a50444d198181e6a4078210035070b5115140180c040c040c0b400900d80308901c2c488035224050701402002c5c0f58032800e0312000d031606100d5034400ca000d0700321415184151107401d014400100e4100401140d201c00c0ea180c03000b03080041ca00042c10b490f8003d189030401c0007110180300390342c1078004405095445080000d0384002c1800117656100c0e01001c894140d12611038107001d40c01c48111200c5058540c00810000000e07150414142d6030b1056400e0b12691045802c1c1c104010710315a44607005900051501900c0c00f413550301c441d0010f40205081c140c10a00e86c2140412079038001138100500ca00c15241440181d241c51030013070440c1c400819502001000048550041840b8480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 381015251 1250 381014001 381014033
    0x1030b0f060117090c040e0102180d030201090f110301050114061e0903120306100e1008100e0403180906361103010f0b030402060d0e0a1202010c0201061d0f04 70
    0x4003141451328120300b40e50764540c24030140c0200d00d0800f515140c000c0600803200443c204500d040745415000c002d101100442c8281901107540c4c403080d03040010350103078104003242e009517074a41075070000d00101030845106910000000001c407241011907124003041e114150904c1c9400801e00d02c0c03040e08020103201d0000300e1035143c0240b030010f02d045000c0304091030280301c0960ba180418810510140c4084500d4000340394842901210800603601c035100383c50f440b2850300410595a03584025900c40c14405a404501203140b08651161401040354075074000d090154080c00290719202040d190110041641100780c501c41d0b65004680c40b480c8148858a00103000403c001c02d26072030311102c2d581080c052008181d440c0c02c80060003208840a1707074041d035001483d0620700804481c00348014103903044a09464012a052440401d900303501c0081c56004030340001c10a080030304002401c440079a04402700d8544203540c0380a0318003002d00780c180d200304024000c2c40719403103600382450b2001c00406 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 381016501 1250 381015251 381015287
    0x1603020a0303112d070f050f09090a060912030b01091a0f0c060a020a1101020703050f09030c04050a05071404150f02030c0a0c0510031b03021804061403060f01030b0f0601 75
    0x10810340d42d9107212a1400130f1400102510700c4180c40701100c900c02c0743c003440f44982c0450252600520f81c540039001c2600b050400c011581e00c200c0c190383c1d00003952140e12003551800701f0680c60310442501400388440408091034018055401c000a04600144480d044062014086441840c1910440c2216001ca01740400c03204a440d10b03a2003480650300c0103000100044412030300d0060ac83e03050003644e03c95645916141d042000b41c20030800c04c0d0700414540e1b03a00d0303c550002002c80792168452140261001000452140341080c0c0281940d01090301045408100700820428103005606001d0402413525000b4100b0400305412842c601030005100039031f004140d030910802c40382c0c6190504980054481c08500d0f410350605400316503c0c500b800b5003c0e000c030010101c1d098802d60043c00440040b0740c10355211a200300128085414503045009252841e100002c0d0628040043c19070100d964201c0c84547e604556800481c40400380c410f5903544c46000c045011a80035443c02075400b00d07211 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 381017751 1250 381016501 381016543
    0x31b12050c1e0601030c0f0b03070c21030b040b0604080c0405060307031202010e0c01081603050402041d150c1c09050a1713050102070605071104110a050a021603020a030311 76
    0x201030ba4441900b07200c202e52035502210001999480c0303a20010880c1c9140d0703215411076a032002d0503100c0f008400b00841c1d030b03088201c908000152040720680684852680c0005811000b4014041101c0c0700305406031080105100800c031140000803203070316004043c0c9000c24552100004249028042d4000400040c01c0464110700142e056000340145c2030304400b1142180019030055031080f000740ca03648048040b40b8002c00545011790090380d0040c0c8064400100356003070005903c003a40100010100d203410080764440343c0300c1c178041c441b40c00203218242c0520303040468905903480048000c180d00110b0701d40c40d40405202e0b0900c10042591f03040aa400b0507150351000909a40e03000300c1c1d0308c003200540524081090351001450030705940c0325880e9141f608610b91078440300a0f01c00c81c50b082d485900c81c0301c61260b0703080e40005040500d440703071115512541035141c040c1c01e110602f08041150107040d0420409a502c0e20f40c0f4004698040c00d0203000000c10a142c0c3c0d0511000c0c00c1640071203510340d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 381019001 1250 381017751 381017803
    0xa0305030c0705040501050f120f060c0909150f090415020a03020c1b01022802180415050f130602070218090d090803030f060a09140103031b12050c 65
    0x84024001055030700180da00980d11002008121034081c0506504201c1c0741c0b030b00c200e0318104404400034104940c401c070b8200c64490110a8500f21040317550301d0704094003180c10651400c1202c100c90b08202d0b1001032030100b90200020601c201101e6103014030803050704d4042002d100c515400c3c0d49001201000a5554442c42600500a544485e00c2020248101248800e004520380030501c14450160301400c1c0322000b4100341000c40030701c0151203e140300c800450900595030050002c0c580140540d00c00c80320718150401803880c040008180714898140405c00440614620f030f0f90b0350224045000c00075100890410300300030f014002009401485918030f40070844810101c040c469007940d0b0407241c1e502c4a40c0800c840074082845007000b247c2c02480407031030f0400c0d008240e990128002c0c050300d010982c1c544110007a034400813090415003610070010f106040e80810001020200b900449105012070764842c8000440c0098950800001042d103951266052001451241855034244407010344 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 381020251 1250 381019001 381019003
    0xc110a0807031824050c0c040f0e030d0c0e090c0403060c05041e05040501091503140c0d0c05150906030a0902150c060f070f02060106210f020a091403030d090f020a0305 74
    0x55045242181400c8400c00f1310051007902255540d8074010040d040f0603a0101c1400b02421303000440c01ca01c5511801c0204400c0c4d01040a88106200f11001181c5207941c05000340602c080da009a0703001d0000e910420144195001c00c40c1d04507070b4131020004400c04260411202d900890b00407090070466104016001e0340b00302000c10540384221000c200c1a41d0b5140fa240850b00c80c1d07034110740c119900603001c2020070120358001100c80f103084243d680401080e80021140c400003002200c20340b00001d41400726041101c00078031107e0f0309140d40c1e031400c403000c80000c0030790000401d85d5281c9601c440b4a034086407203206000d20001440c081242d180c0b0302c44e19040352075030300c200e9007058001c243d6030008004a00c9000d20642c0a000c58018100c1a424210100c0f0704141c80c100010f400c298003e64401850701522031907c012041e810016240d0081e400014081800c50b40001440c01801c1c800255a6402004484180e401c8850004200c103003450016a01c2e204040041d6200d1030500f000400d004c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 381021501 1250 381020251 381020279
    0x30904050109140f06010c08130b0a110d0207120605070908010e101a060316020a0b040f2303030a020d1107050a0b0a05090a030509010203070c030804090c110a08070318 74
    0x50030090000d540e0350b450780300701ea06042110201d00245481c100e6802040a0000801040451445408028ae19980c01008a510081903080002c20080154020350340510070b050b03001a0300e101408400d80b90058072201e2035414840600101d50701c1020420045c0030321542c0f4002c0505900034411100e01040450312031500c0c40e65130000900349100071741c81002da1414a2400c407801054903003075884007902400e00c0c40301d108410301984034040700f0001140d98240c610303100301d00ca0941c0242906551400300c5600301303a51061a105160440040d104003008020740c4d6202c80300c0c104c0140c607221040c0c0c07541c010b000781d041521200b0000007100d1061000202e0341000c07080c0a6245203241c2d407940b40c0420100d0710b04403400c40c040d422207000c81e4000380c030850041a00c0130051044a040801c15101c0c1300c900c084a600c11140d00a0010b01000003010310b02070410000840c0c2010b0070001840049140c80f0608110001c2a080c0001216410903000b10703910300c41203001542003240e19480f46a200201c013 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 381022751 1250 381021501 381021521
    0x50d1b0807020d0305011206020f1308030913022d1b060105041d1f090b0703090302010e070806010b030402010306031709030115060e09250815030d081305030904050109 74
    0x40503022103c222940640580e9049540450050407080020f840d0388000b5000500229039440c401c01c9451085002c0d002884090031180c0c000d1942d4400c1c0c0c0c0200300103038a52030a2002801d005012485043e43c000e2041181a01c8a4008443c00c9a007610821107d1088220307400c3ca00822098a0081c42c0000400b541a80c5042d1003c0201074801110984040744c28595203000e80d1160541c03150048004103859403d000901001c04c000e422552102c66014040f50504000b0781c0e215507910604d41d090150007101e41d14080603220190400d104203858100c1400b9410b800c0100102090459210f07a101c84004d681046810440200542140110340e2103d20114441e608001c0d450006903482c11000d011601c9544641c1c882c1c0c82c41000307122400724002d0251000410300284498034a00e040d0070454041f0130356694514900d8024850b4000c0a43e00d03101a0190340685c5002541d40d40059505811003a1507140c0c081d001c00d2131502034514031031142401e400a081000000e03804a0300e41001400d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 381024001 1250 381022751 381022753
    0xa050c0609071214072304060b16031d060301030507060e031212040219090b04050f0103030207060c0c12080306100f050405011206030605070e13091101050d1b080702 73
    0x207a1181c446160340c5011500030b4a040c0c40c0c008405500050184244a500c81100001d80c0e5081c1d0399465000207216860022616215104036055124500741c4100c601030101c2402080c10a07464440c6a0443c5c807140302c0040600000b03e912190040070800c0320514481c0052650355650307100d20380b10b070b00c0700042c2c410200400c16084200c1580e1401180d10100014890021402c010000d03002c003030720080c05082131342c0056505e500a0340c50007480680d10702420310b030b00011602d5280c4c0c000b44030440e031006100c07100305041e9034014000607038045000c0080319001c2c90a41103e18450030410150344c410f42c080c0c542c1c03515040100c0108010706001e107203d4101101d59020b025508003007034032030381c6512000500241c0100b205200940c0238040c06c00003444100000030300580c584c2d13526012143c00341c070100042201017060303031007510f01102d00301e04c03030219200b0502c255000c6a4aa2100403205980e4034140074000c64800c3e4440e5a0fa07100507819282800c40c400315015002d00940140c270141c4200d001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 381025251 1250 381024001 381024013
    0x9050717010507020303060d0305090d0c0609061704030f17091b100e120717010608010b01050705030904230712050702071206050901020903100c020d031a090a0b04020a050c 76
    0x4180180300702ca1280c441ca402940c40d580d50402045000c14081d002202802428030980e01303162100070318440b155101e5020745100038140700b4080c3c00c1180581c00701040142010700d9003050340504410a4020341d02d800c0101c40c0e000c43e00426541c0c10b000444914221032540100009450000740c200d000781840068840f0815514042c414181880440c1c5070100d80a81d000c1704060030034505044000c2100401e4913511900c0f0f400b176021a01c900c0c12541e9440c3c0d1550b0050200c0a800e101f905c5040c40c090802528201165031055128003402080c584076540c4c5190140180303a0b10401d941094000b6002c036215442c0081c8044c0022501259081c00703240381a0001e01d40500000382d907020754032021252000e0507141d0b951400078140c01171140d451550240b046000301d4a080002c51700283d00f0b40c90221301c22a201500a00d00552201c02d9410942840c690412400c080821f1100a2100340c480c20003c0d40e500c15080058100b581d80242c2080c0f001590082d2240e1003005400144848019129 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 381026501 1250 381025251 381025289
    0x10303020c03030a0903061a101e032901020111040915060305011805041704080303040b0604020906070b09030d0c020708010c030b01050f0a02121c0609060614030a06030c0e090d1d10050904090507 86
    0x204540030868030300004ce00100d00d241a0f011140d903e83c1b40d0318030520001c200e03400803000e041e8842c0c00903401100301d180c8508054002840d2001f42c00040c1c9428074040045609d864065500c0c160a010128500da94510110303090284252907803d026186086a540c0d403507880f0025a030740e603c210340c2600c40404844c081000b6103024022a5038441004101c1414030a840d10381101200000e420b05006120401c541680d8810a00074440e4441c002c0e0041d01d9003a103402003803030a4804001600742018507002034440c2e2607801205840e01320048441007030303c5131441c941c1640f03485070842c4964949180407400110f00900c5110918444074810418030015540704032080542350b00d406203501180c0783c0918810101100c002455000201e60800b0900d40c2d92030b207030301c59049507030741004810001400800003000002c221310086504c0300c5c0f4000c42c60901500310416103c4140c13400b40c5c0705050759400310382c6940c40f40c402e0390f0a142c3c6c01031042006012a2400941c2d0303072980d100c0c1c00c06050324054020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 381027751 1250 381026501 381026507
    0xb04061d01051e2b0e01090b2701050703060501020607020c01020a030806040f05090c041103010302090a32040c050d0c0504050703062103031808030a021b0a0b010303020c03030a0903061a101e 84
    0x182601d0f600801581c100e031100d03818030751000460412110270400380510a5481c0c0c03002d0181500411058500003009070400000a0500d04001c0c445415544003846002d560f9074001000e01c2e2554251420b601c29840340740c0050081c0070326001389038041d401d01b024405109004136036a4228a0b045070100712030b05980100032601c3c0030900c0080d612006001c0050702c0c141c450303002880c0119000100c24460101002181c100000c0314407160140428071041004104200d51000080c1c98101c40c440e04141031036480740c840134213038001c40d0b000d15110300100301400d003c1e8122a0282c102c0c0d40342141c0c000900d440345c1c1c0d21210080015400070303081100910f0100c03281c0050117691500400250b1660b07681003041c6000e0f5101109000800c44c0792000c1d8a0060418480456000d1259400440715491030500034502007402c2d40142c801d8200b08188269150410f1144007229440b810118406503c1503155400c120307038190306508691040300c902991540a034148a0406008481d8000d00e01045011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 381029001 1250 381027751 381027761
    0x310c15090305070504020304080403080c100f05090c040f1d0a020a0b0c07090b0105040f0b0315030d020a2607080406022806180602040b04061d01051e2b0e01 69
    0x508243c104101c18069400c140d0003d50380140105150340c6000e82d6a60360300090b0340b007800f400e006030b08820743e000c03011215409185016101d00c1c81c1071143d810110301554441e10101003051007143c1d04c01000c039020490350012900c85544202c0790000504900c1560384030400301d13030b0492140900d0303080811591032030400e940b08004040000d2208504000c144002801640c4001d8103103c002c2c0b0001881c002204503190182481036030294a9080401c200c0350261003024400e48030303810401a90b07003000d90001e41203541d15007002d10f400042d00c240084540d4000e40c07a1207944040310004601c810b2140c3c0c01300900803580c0319402c4403001c400801402c0406141300003d620000e0070100fa40010031110b402003042850300200200342684650340c0d490480e8425400030312303003130740c086420440725401c140d40c0c4001c02c50004803030400800400008103280302d006031124940940341c00c1001701071155030641b441c01ca81007444018400080c08102a00b000d004403000d04035051003003441100c0f00c103001e1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 381030251 1250 381029001 381029003
    0xc060e0d020d12020f0d02090f01020c0f061b0102040909021002010608060f070302090405100f0b040b0405100203070503070b010f08030901480524310c150903 70
    0x60500302d00040c0045444080c1c411103540c900d03400740b210b04803080e8803074018104000701c00350042c0d944030004288118802180c06860542d0400484940e003a120b80c000c00c0e01c40b040440f00207035150b16031112400c012032120b100d94255840440e0204401925078030602d8041d00031203110340d00c800025400c9003644d90074041e1a246401c00d20104400003240401d50760403819138240075003826403400100d4210381046500000c181d030803500030409076101444407c05404d07400c0c0c01529040c101141107020388114850a4054540b11914520b80e6209100b0703103440662000641e551001c00341040381c890b02c020b010320a031181480c100091209000000c44210000603110114050032001c140807100c40032020f508020b41c40705141651b036070040340c00060144200301c6d020042070340c0350428602d0015005800642146444004500102d0f051201c90313000d00b94619445c9041d080544101101d280c80c892481326449002d031500410108148034000d40d5103050b00c40c03240b0300078500103d904200c1c901c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 381031501 1250 381030251 381030253
    0x12101505011103190c020d1b0e090c06070809040b060f090a0b07031e020f070b030406050112150e0307080409050f0604051509060312070c060e060a080a05040f0c060c060e0d02 77
    0x100c0282c139140186001900d5a000910b651031804180d22402103d5038522410715480c00b10a00c140b01c24000f5011040d00100c400d070040c6100e031310800210b139040c45030030800380411401181c1901d207a80c0d60340086c0340320300e0060021602c07046048204903407500403000c15486405503403404078514034007105031030503039415a071004421404645107948401c5104000e0003180150038151041d90002c00c000340c020840081c18580d40c1c64181048801c80d001030b000080c9541000350248003103a080b840c0381e415131170403042c0080e298800382c288502e14800c1603070080c2070300000300c2c000036120800d030b015920400140142c011180c1c0c4800401040303d8048950301c4d40e003100703101c40e000b49042034030f40154880005401c07541616500ca00050542e0000c1e8002c80e4212440c42c402c0c000d1076840813681075242026594503051002034003010b0b040800c02481c8200e429a41c0001801f440a1241d07a401d040c0d030016000a040c40e19024002c00b101c40741d01c0160342c09070600c1c41843c906e150000d4442400141f40d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 381032751 1250 381031501 381031537
    0x120f1c1107081e16110405251101050106050405040b0102060f0a09050a17041d191113060302040801060608090706080612030a0903020901080604050c12101505011103 73
    0xda50b040d031640151034081c454000d01c0140c2d221521401008188000c40c8400031a4091040e2820702a0610005030b810b000c0d074140001c1c0500003201419034040c4244505800040205a10088641810015030007c1342c2d8201400024001e42000c028000e072401a141070143c1d20614006903590001581c0c0955608410b01c0040c05034141603101020030386c0b0070004d440c42078000c2d85500204013021208120898000981001041404800da1400c0342e0740301840e4000f440c00b0170941c030502c8800310300e552070b154541c1034110417100c00c04c0807600840c00d600040d02c5203d80390000100290018064210158600300703022034210b000d807191504c1484040020a0703c135081020480c0c2611003d40084d82250065601181c1c0c2d032130500150045018590700c0c6044c040c40c40c010000c040c04180e00079400d0380c11003800e12000c9070002c650310424030403d0305c0c2c40c451201c240f0780051604681c411011403c618100c11440700c0d00c840c040d140101da400b43d031040c089030340b072810507904c82c4100703440c07041400c4020f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 381034001 1250 381032751 381032753
    0xf09021345051e0106140403051e16080309040b210601080f1207080c07030f0b062407470606091c02010c02060d0c031506020703020111120f1c1107 65
    0x5906c09407401048449034504265990b03495918005904807051a65840c2c1030008006000400a1075900321103040034015451500500359100d10a14003507600a40e01d40d002c2007201d40b10411181001c3e1003d401c1c41d0800c0d0445860b80352682c00070f00584549001e8000c05503405140040c451300e05085a201140c9001810b581d0303241d6a92010302a40440e0080500000102d04c08558201c0c19034001d01c4283e800c0d107800801c01030003441c03101c010020a80310101144075101e05505079a403180c1d02c110b454800c0070101c0401480c0500584443ca004c142d0442a504991000300c00f4940c500d0f10046141344075120303402042114000c2c1c00c607980c1c000700f40860201242d94181c20000c0414018100078005003000d801040382e5621482e0102c23a4540c0345d4109502050345842041380d2480d40c00ba00f20201414118003e413141281d2002a042010f03c4c2c50803c01c00c1001c0c0704040f64000d0300e050f0240c0c0c0307903000c0000d00a990040c40040d42c00da14458a600c9000003503002c0c5070300500307a660400b03103801e940e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 381035251 1250 381034001 381034007
    0x110c030d0521040c03060c180b0304060b031f0b150a141c140604200c0f070306060e090304030c15050c0d05040f09021345051e0106 58
    0x2c08848500d201c603152a44252000c51441d94020b034000c1410080540c1142046401c0d500c4202c80b0008004a60243d410806104140305055414034005141e0300d48550a043c4080d1040e50045545030040c23003603004038048846034844009100580600000b000e260404c16007011501031860104000c100086c500d40c803038030030180100c26011030241011031b101d19605c901820b2100c20804995940f59503000a12404401a4446011601803181d964511043c0000400380800e01c2c07003001c00464001030040e0240908111005038104a881107076a17030030b202c400750405204600040b0380c0c030f6000c515290310110417201900d4110f2a4062450f14040340c04d41c40c048a032154001b0070009009c03036003142d4004d005064201c0b6056039031320340b131b1414408890b030106420390102000d44d10400c16402070300750030140c4d04111401604540000e40420705410b044981108006c904440d0040d420401c00015038802241100e40c41c004204640c0d0f0030751042100400c03c1052200e4001031001040404c2c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 381036501 1250 381035251 381035257
    0x90b06030c07171c060e04022b02040e0c1c03090515070203061005040c050405030a2003150411060427021911010c03020a090918150c110c030d05 64
    0x112524401140340383c2401110056000b12407014089014003108440c0101c0d6802904007a1207005000300c0242000d60005072417003618040316038000c070a00001d000741c842e050300d40210203401030000c0c4001d00c0038041031a203800d2601940c9129180d0390080709201c40ca184c429544803541620350790360103402c0604000781c40d09028030003110781c001000000016281480700b03e00500b06d40c50604029420b08c41084261080c410300502040750a0100b00043d0380c1c00034a110340e154219120300e00030f500442418142c2d10101c0d05140d010300c41c410b491201031800e903998a02c5135026010305064040311404100140c0300300c0c0f01d07a100f0310f40c040c1d0004001d03261246c0c50415003172071903900510704510212100010a8041c005c1d0700460034800000202036020b006507009046503280840c50f080344200040c1030302007070b40a0829042d645001014042d13211407848031010341c00028900a0701c0d0800040310140400000903400120011036002c2c1c1d040c40080c0360703d0350310310081c041d100d224400c0c0001c6446030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 381037751 1250 381036501 381036503
    0x105130f1e03050304020a06050307022a0a030f05060708130204020d0f0606091a0408210d090b041a0c0f070201020a060501030f050d1b0809040e0d0504080106090b06030c07 76
    0x44010001d601c1e82554400d1400d91107a214152030b8a8180100708182c0310542c1f161003885420010003032a00e034082007403c585051800085820008003400406c0185410100e40c4c02c80b030b407a2404000d001441d0700011142e40308404075000707941d960b031046454010564035480280e144059203c0149495006800041c0c1010400211040c08a0250041e038549600c031502090000074180545480c0303172100e1516000040c05146458901506580d03a54075440141240800855150501070101c2c0101c0380b800c00c104800b44901142c600b0407019030030b07080e1000ca510030240c5c006603008403c1c41c0c002da44204406d8001a04100011601001c90751180c00200d0440c0034023910840012624402e050195009100a1404d070419241c040c0c900007400c0d4181007070003030310103152941c01c0440c0090f83c00030360300030150707900d40d24201d01080c09044401d4005c0700ca4098075001c6541168000042c0c4110781180000344012542c0707030400c008580082c6030382504020100000750000303240500400c101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 381039001 1250 381037751 381037763
    0x140106050f0a0c05150a0b030c0103050c160203030c010c030b0f040b0321121602010b030f0a020d032606040f020408070b130e090606211f1121090105130f 68
    0x4142580d082c3d80c030001d000c6540050455454645030701a048c10001e002c4640c00070300b41041281840f003003401c0c59000c2c1c9418851888040200c5201b1901c05001361074074000010020b1048014181001d000350803008402d90141d2245000204285400d010f811802503002e0003401115094842d108400980c54210610108040100d040c2c501955001d01d4420071902d40014003030060000001d0966502800f4a4131a6101e103507118502003010520504980d812501a80c0701a118601030310006841c00581e42d050544213039006044502044a03481203004680800a617189a02c80724200d010301c0c051012540c0c0110f00038031001030400001d00004441155840e8040d43d00c94510305103d000300ca07801025000a0140405801d064a022042c0ca05603046986038039480003105698a01031641000401d50350700c03120100b54902e40c0141c007002d0850014039a1040070800b18039050400600c07800c051181c0d5030001c0c20700013040c40f90a0080c9000e420410301c00c2c0548d1110b16200010604c01e940d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 381040251 1250 381039001 381039013
    0x81602011104081609050421020a0b070c0219080316080405030607020d0e0d02060f0a0e120a0b0c030912070821040b0a060e1305120c01140106050f0a0c05 68
    0x1401c035003030060002440000b004041203100b80448403070b81941da074413200109003414107200000f0100910002c031076584403c0300081c404d0b01d0b07101724941101d902001d810050307400203004000b50b001c502e1710b00031030090b20300710005c0200018204600d0890f109002246e0020b211071584d01154071001c60103107000c2c5210074203045c0c031000042e06114051300c0200141c0c2c40b19456501854021459022142d0101e5500f0070840d01030b00414002d22800c0741d00c8401203800104010041d0084038066801200a420800583e0090b0740700d503581c1120380c6090303400c00d80c0350700010352014044084910620300300c000360900302080503140d0115001604c040740d240c01c2c14040e41c1d164034034440001c0c90066803070b41140102e0405080280b42c50201800c850001400c0c504180a0f041c5240344042c2c206491110000140d100c2d07003020b5081c40140c4030040c9540e000040c00c4140d04005401c5038040e108911742d0400c240e640c914080e5000e00c20a9902148140c0902640034158018031303443c02494010383c10303618 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 381041501 1250 381040251 381040271
    0xa031b0f021302031b04050d0809041d1e01051302060c070801360c0b0904020f03040f0201020c1e060a0908010507091e030201090b090103110307020601030204050c0a08160201 77
    0x1c0a810b218021040741e0390101c20001d640040c0791030202d52184e10f04645140c1824500480c0c3e14440c00e100203000e04100240980d11a1101c0e8070103000c000e00d800c01c82e03200c500300044003a00c86c1c1c041c060441d20341101c1c98000c0d10019061003403038042c2c018848100b850703119983c203000098100c568440a94028001c0c00103101c0c2080c0500920813210354602c0c055100400b40c104004c4040001d2901403416455042c00018140d04e021800d99400400701d03034540d840040010064440c00c0c0c45442020804000e00040011010546200340c4c400d800350340c241e0280c0c03001d02004280c80d44032141216841c1040c0780aa0521200410501d48649801c2a41903207420545096030710946045c0001244c0f694200100d800300d1a0313030303000d071101d4040320808645580c000032700c0205180904e540610700021b01e0040340c1e019501190080d42001c101d81d440b0320701503001030744950b400d1000740d01031404e0100003000003c450080300c45641d42c0783c84400868491000029030b502e0b40b810084203640da5110086 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 381042751 1250 381041501 381041509
    0x70209010e0910060b1804060902182b0f030c0f1a071823191823070908120a09051f21020712020f0a031b0f02 49
    0x340a0054441140c0d01c50400c01d401e10301c0d10401844030a074180c42e0001c1070069044100c00c40741034141c129801202041c0e481c1c0040c000b409150311811043d031002074400207000141031170302e112041c2114214440101071800c00405820110032000010022240398001400419441d03000fa009180185c00c0c8001c0e0b41d41d204007400440c0c016070750715070b41d5400401e0345050300a6003507001c1c401d40303026410701440c1920b00210801a010f0410030300125a0340507480e507480e00100f035100100800682ca10105d2001c05000d82002c0c0c040c54600a2401401180301c405500038241c24088055042c50201a82188a074001c1b80207041c241c1003110403100007030307401e104000f4101804005200c5507610340f50340001074400d0840d0380c8224080c201d02c1320035a01d54603003815030b54010112401d05c0e03030201e203098181f52940e004020700204001d2001c1245414068001c00e484070f010348075001c4450040c0061049503072605801c078001d002500f0b980b002040c06500c800800d44445c4101280c00c9941c01c1d541c001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 381044001 1250 381042751 381042769
    0x801050d03090e0709050913440a02071208030c1b070303020c010e0d0803310303090c0e10180e030c0604030f0f17060616060f050c131a0702 62
    0xc40c0004030024010304c6240b80081d60150000303c0a81d146081040c0f955071803036030049d00c100c102130748120402441e0f450001c828204081c40414000a00c03844110b690303403c540e810802881005215945011a01e40c1600005490841e0045001800c0d551500b03075049031a8081d20300a001c8100300010002111000c2058801652207a0040d1005030381020005000504e0001d009105408000c004000305490038101c0381c01210300c0c10310002c10010007903480524000807601c240248900840790041c0b55050b40041300d50344c800c61009544a80d9100c0c41035000c40180c0b500740010402c1807040140d06c800361001501aa0041c1c1c012486001e401580c0d4115008100c0c0200c042d0407190030001010790040700a98800308c030341030540e07810461f144024174207104d01d0040c9034500e08042c04580710b43e40d8482542c06110b98864112400c00c0e01d880e081c00030380482d02c07191806a0604001c10b44841884082c1c0d01512100034644c80360354503104148400d10141d8881507007664040151a002d030f02d0308909 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 381045251 1250 381044001 381044011
    0x1608151e090d030b030703030e1e0d0b010f0b0901050306040b12010603031809020307051b15071e0801080a02060d140c2d040311120d020c120a030801050d03090e 71
    0x1804112038000000343c162071a56400d80d01c240c20001e0700780700081e04a480c61280810982d07015040f590b080b0209401c4001031941560302840c00c5070307a01d0400c506078450790b0513241481001c0c0291541ea80600c140d6000d504040703030100700c00344001020785c109580000107299004001020842c001d9225a003143c080f81c105600066503c04100c500d04000c00b0301000a00014508600d9440c1446006185020f24442d28948a0219060421516042089800701d807486d034120b40309411f0414020f0070712500d1800150b035006100441c18141409040380a049608100260101e01e40903400c0040301d5105182420072203640e01402c144040003c4a003034414960038840c25614802d044e140c180380c0d40446040c18585042c0f0f0382008000135040199803c495100500248510494000450760300400000c1e0200c0e03c1200e2000b009640d0000d04285c0311030043e00c1d5410000060b881c2c1b01d864180c880c002a010550000040080c3d08000d5101c2185a020340b0b845416291185e41006218038282d503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 381046501 1250 381045251 381045253
    0x120803040c0315020702120703030503010317090a06050d0c0801150315081c12061404050402122a010809030711060f0d090210081501050f0c0303010e01081608151e09 73
    0x1417440110b05140c07505d205100c03019030040a40d145141c1c3c000300325100500000380b504148041204818005000b030b104030394401807801d002c5540341c94008065401000c1004030081c1400c03003d074203580c01900d07014182da070a09030035001c541000782e0603805418414400004508049800202407a085c080c042d1421401603284410813200e6000800b8804014454081946800020001100700c04070000600c442542d0100d0503980b1800010a401086001c1800d14046c4941841403200064090354031866102d40e0b201c1200d00039001144c4401c0c0440302040294410000000441c0d1400d0340089602c000402c03180c80c004c400300c051029508103001510165480340301c440110318101d04004c1024400f8500750b611403801000c8501c1500924550350f050040005800c24201d0a4030100e4200210300300c1241c0d9039503999a2181c0c0d0400c400d00c05c5407068041c005400c1a0762510301200d904646c2e03004002e0904004c40b080c242090400500011a8650900300401442249078425885040d9002c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 381047751 1250 381046501 381046507
    0x41103100e0609210a1808010f06080d1b02090a0e0d02070f2102010c03022a0f040908040e130c170f160e10050301050f011502030301120803040c031502 67
    0x10070300313444d240c91001c48000e001d62856480c0115603212007030312841c0075149032100020140b004103068690f01508030f00304a5090030b012801d81c490b0b58010070203c405034411100502c0e28001c04a944c1218514041c41200007081c01e4409454001c115603041026078000107542048440d41520f1702410030048800340e000103004110749080b0640d80c0005080340710b2045a000b011165460214000c0a40241804841c110030001e16100704150040d08200c10a0301c0079104841c0145452140080b4440d40310303d0107051540001d041500810600c0ea0b0b02045a50401c0d0904498030080c44000b03001540140f0154110780c0420301446d103210041ca42a80094078401584c1815400c1c08900707108008a68002c01003010340f11119101c2c141114080501c0c484203031100425080f408809901c90350341136007450f041c4501400c561580724100c4210401000e11210756003c1070741c5a00091091134040303c00c0f10003210203d84100c004682c07152140308010041910f81d41c80c03850a00e07840c84036501c6140c0c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 381049001 1250 381047751 381047761
    0x30f020c0f0f01051c020301060201090204060807061e020f030a03090303050f060108011e15020c0a06140f031f03110114030129132304090b041103100e06 68
    0x521010180480a0700c020344080c001102060342020001c00310ba04112000484079001c2c80311042c40310041c0a4400199a00e5a43e41c800130b01900000c007042c0e1196280010000d004100041c446048800e240c540604441c80d0b0407408200080074542d0b8419030003003075800185200c0a00080c82c8000054400098002031420010201d480c028820340040c1c8517182803040c40c1c1e8020780800e0444402c2c2d030190a00000710140c07072099000315401600f1000c0c031114112121500801c940140060584100700703071968800701124041030300140001b8441082014540081b1108000c40c0e00030f00c0740503420074000c00d4644070029109144d1080d142000a1094078245690081501d0984458100c110f401d41d4107000720816015816081c0442400104030010031070310441c800e4840f10380850425440c41680c503900310300804401407846482c0c2c1500c55040080740b406100d000c0386550803c040d01050b64079035840040c00b07801c044410340e06205082c0e0b441002417960241000c0548040b010f04202e042c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 381050251 1250 381049001 381049003
    0x61521091b06172a07050303072c011214160e030f0606040b0a05091501030501230d06020f0c01091106090d0305090105070804060c020f060a05070b0a020409020403030f02 75
    0x1250b0000e108100700c15800341548540740c510b0075008802681614a81c1c1e0443c4601c03c500250b0b400c444a03006000300740d24050181c08006140f04075030035100e8403802c071900c00783c6c01c0d000303100415042c074445801c50801038154401c6006050f82690201c00040900d000c0d1243d8900c00c200710707041781061841403500b00d03a2550140c2c0786444004241d004040e1060500c5403103445d904020051801565540c0380c20001d559100143c1c0024040507007400b20b207003062160070103d0300c04001884d0109040000000d0500d55080490010900341c1054041c800f00a20412046004100e400c0c0d5107150240070342080719506034018050322214000004108032940350115100c45881403980c4100800c1c00400e034a521076070310110402e54180ba24950719040400180c178a8020f0030000780036a0000320340407800ca43c11400d00d50884d070084801035028100700d030170420b031481003800000000303c0c18050000080c1c155803103248c0040d0b04505c00340c109501c0e441c1d04001c03038010740d0007580040d503003a00c044040d0350 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 381051501 1250 381050251 381050303
    0xe0a111503040f051204080c13180213110a180807030f030509030a0602040803092419020a0501140601110d0e0f010201140a050403080108070b03011814010f090f06152109 75
    0x41290003e00248115880b42c04100cac0c61400040c1c05070050207030801250f80b07682d0101e01010003404449407540e10340e440003040c880030703140400032138901541c021901460014a19040302e038400701c2c0807080100342e90200c3e10793d00400ba0703241d0035124a40102c00000c403980094005450103400864580f2107007410400780c403951000d1403084c14600c404c1c81d01001c075814112804071010806090030010742c0c540403860103001d22000380095103000d94040c41c1c4a04100f0060045000b66150f00741c20004804070b5071110300c00320303410b4041036007402840e0550528040c142001c2c181400009038400c80c0c06d40c44c1d40d640b0021220b5001c00b590700c104000415802c5040103014014160007403c5260408245540500c0103000701506a42d912079061600f4445400064100c1c0c044960702c111540e480e0303558440c2c1c0100e07004800b002d6060100050044125200d020304540e000224100610be801c11f054034014074020100848003201008a68107640e207000c0c4074145846101a80c84c040030032019100c9050b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 381052751 1250 381051501 381051529
    0x30c0d0b030f0609250905040c1208070b0606090307030320060907060306080312010e13050d021e0307031d01090f060c02010f03092003100e0a111503040f051204080c 73
    0x1c0003a481c05080482050305c2c203800e4520f40f0701c3c0020642c4a6007004a510512548401000381100e040c0c1420005003101038160140f01c1c00c1e185000341c40310340800000d4010042a240c159000d8142040401d20404600400508103201c0b40b0600d141060401c1c10644125041d882c6544030850800559606200c0c80005020207005541461035500322211400300602c00c4200c5010420040381a1255603400c50702c41c80e6001045409204a6140c00307911004101030307000302c040c40400c450060b510084210b03945107603d40e440c054080c41d030b20100006020b842018604002c00c140e004549002c0305010030018011a0702e81001c0e01480748001040441c0c41c031a4001007504140c0d101000445183c0340568020000740000e04030340345900400d08e840d1021110b4040b460510081c0d18a25002140b1100082d025101444140f42e02c10140301580c1011101d00f603c2110400c001004503010f032001807a0a80700d0703000d9403005508217080450740c0d0442d400c08103294200b4030240c00d139442c0011382080c1403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 381054001 1250 381052751 381052783
    0x403020307080604051e01110a08060108010509011a0d09060203130b0702030a0f321803010207051c02012408060708010b030c090f1009030506010609050303030c0d0b030f0609 77
    0x240c130f01595101c1d10fa000203000215a801503044050340c0c441c0a402045200700b000003107075211b8070200c13070040542c1001c0d0350040c0030580306030011030641001d04540381a40c0d0710000016001c824442e031382d8280d6002c802e8001049030f860100070000303400380c0021030050242401c2820007601c03905029140250140980d030a41d8000c00c0b4240c00d04d82c2110a003114083d441c00c180c03446c01c0c02d95101c003440c0c4410420b880149100d60107803411012110340a030644a60340f07400c4842d01c9140030b007414200c0c410b40e41c014100380e0154400ca07500c0341d2011480c0300031001a10010402140c85c1e219803910800001042422100580c018400c5402c1000116404141c900e040e483c5545041d00a5110b88030140c0401131080d40043e40c0803840c0c440014481b000368000e04940d0407c07c0403e402402c03906580011580b60086200010300b8038801d8028500341c40c0010082c525549410306540103e901c010507c0b04496168400c680b43e655040c0511032003007d5100c042d0a0341e1400740400341c14828050300b1880c0c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 381055251 1250 381054001 381054013
    0xb07080f060102060103241103090d09080c0f0a0e04030309030e030c0907080711100b0a05060705030406030504060e1e100c0c0f060b060706021c09020d020d03030209060f040302030708 81
    0x210b83c0e800160b06044940040d085134428080310a005605000d07500e1003008542007122040107a2114401144211101000c3d210b406016441c229090306d02032242c030445502c0001410355616015a6000350701e13400801d000301b0349540b00d1203105019012101078020994400004d400e16801102c8080c10000c200d01074100761100600007800010064442da003040030302000201d80901070408030388600c56174000c41d00300207802c0941a01400400d0303802400740402540020325801c043c016240701e01d0340700340654100790a09070110700800b0f00800640f0b9454540607000c1c0ca01c41e06014004440715030140812003603402d118001d10380594a00200380080c50100500c000d643d200c00304840326903009081c40307541c4105080c8103028103000c050960380a04009044010014194001d041da5403442d140d42444d62040305241080355410040a90030180e002900d000603c0c109001d81865031082c240141032041060101c4c12a03005a071064121100000d403e0007549802c2080c24001e0007000000c3c41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 381056501 1250 381055251 381055261
    0xd031d04020301181d0a0507081c17041b03030e01031a0f01030b0310060605120c0901120c142b0b0105091201060b07080d0e011a060f070f0b07080f 65
    0x22010452444042c40030b17652204469004080c56000a04070300d40303811111882c8450401c103440b440c2a200d550700358401c58034004140e040c0d164040d901d0100342e80760165004141d100c0c5c2120924000c00c202c03a102c6a4804074843d882c4400f80640245000342e03074203050744040d84000340441d0b8000d614960302198052080420341e44a00b03000202c26020701c0c0100d109455000401d251121084042c81c1c03103400d140000c41d4803507005010380144508440180e0154403030208200c4070f8401d040f6002e000807c0c0701503804101d8115000123803408a20320307080f180ca01402c010903445410502c1c1102e08091242c03001c41082842d10400322a103803c001c802c112100003900007820034810001c0e03550162244c2004015181402c0d03110000400d26000344a070ba0346460f00c6c1640c3e40d17504c40044080d006140002198241005110304042003924000c000210003070f4508014064110021044241c4010030400000402c101241c0510740e01c110041445e41c2800fa40241c20b0843c020010402c07000c81d0f138100b00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 381057751 1250 381056501 381056519
    0x10b03070e1b04050a08010519050405060112050a0c18060503010204081b0307081b01080a0b0d0204021e04091a0d1109040c0915080120040b0a020c0d031d04020301 72
    0x1504465124603810b510020b40500d101180a564800c541c8812038131000611300b035041d04658424a00c0000001d204214515004122241654040c103c0d44c801e800500050845290b40384240e40120308840b41d841107940c0700300c48135009402c10000d00e50142a48a0800818050b1001500d0110025070501d0305050944e0b40d25025480210746103030841d000303044181c805200c150052b140c00300686800139900400d603040504e14032a0715002820140008003100142e22490212103c000c00004028443d07408020294000c00c0814841101107071018200071034540c0103000400c0d10007008120b103038003050441c802086030800540200c03107480420700007449442c0d6201101104890094103a11181842172513100e664010684003032074203100760f03540a082c03803c3c4800c40d00c4520007401800f140c07010744280010074800385c0c00740840070f00084c0440101c00000c3c15005409104590301c0f02c03642d0300080c0c555061003000390080740020040035940600c4944c5042c0c58403080c0c13001c0d461549004045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 381059001 1250 381057751 381057779
    0x90708060f04140d03020715060b340c0305070b120c0c030409050a0209030706020118030c020d020607080403061406150a090b0319060e09030318070e0a05060102010b0307 75
    0xd40e144a000c040002c0810290341619040082c0740e0b82201e19060b4082c80241c000c4d0f0014905445050102c1460864200c0c1030081030196446141c07020b05000d60030011040c403400f903190408404841c240103e5001c2c0020741a40d01e494011210000924514200030f4140040e940051074001420090104030b08290203542d40c200810101c01d507904c040352110341e411270207103401520b41242090180300c190340030f5401030000000c00b1820f4803025561400281e0803100c2030510140120060881000400d0249054001c00b1f80042c10080301d1501d00d50004525a018050440e0b2000003c0307014024448288a6010391044480080030b40d420800000b074140c032810109801582c8001981413100380c4915191001803014003800e54a80c104480700c104921480e1101c5901c42e440d02d1000145000310076207150050400202461031a1242260081104844000c0b480d451144041c0024401c00c644186803117900308030800240350a00310300080c00d407144000c001d44a64042c40d0705001200c0d0700700d05 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 381060251 1250 381059001 381059011
    0x60813170a02030c07260114010603020c010615032717030414120c010b0901030c0504270807020f0111070b0901111504020a0b03150f01030207080c0a020909070806 72
    0xa0300d4880714903800803865482111341c03c0e405070080320f83c001050203c207401e210144203030766003000105900040d05800c0350b842445042d98039829500400045029500420805403044000702c0c0544c1c40b030741034005281d2501c02000c0040e554100c41000070340070304c111940140c0802900c011152250301c2c0c245c3c523104800702d840e031001c800001040410402551410020700c1b081e0070f0310061a9501034640aa400180c000282c40d42001440d0304d035840c0010089044e40d5100007504402418101800004e000b0943c181e5910310096024051503810b00740300b003500510a002e410346c2e03005588144030b8058102078106043c403541d180074400651b000b00b403100681d40c68005250b1901176102c0100c07070080c48034400e4443c034040c0e0f50702c0740b0b6540151003019105a0003510303002c40499445001001d1741c40100c81c03030740003120941c0c0786805504e048410010f00400503d009410080719850300d420310f80c4862020302c1554000c101e80f600f1800c000f90081c0d444000070010f8404d4614002c460380c1c072800b000701 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 381061501 1250 381060251 381060293
    0xc07030905060a09030203061f060f120f0b1804060b04060501020606010f020106120803011502190809130509030306040b09090c01031508010e06011a0702060901081b13060813 77
    0x500307038503020701c1002c4d101d0003150010111240c0741004802c500742520100c071103010740e540e0410081000b80c0100c0b82e0348090350b0b2a95808011910880c0801c00a150750202c41015940302d03604405150360b0402e80c84c0040e14510403034a9a03003801e10b005011100e0140d5043d00507030030150100203507070700400d88940c07102084c00c0014815060400807401050b454006d1112407111000003c140a01c1202070340c1659000f1822004a5190380002e0b81e985078103c003001d10075440110a20001100d82014248032500502503030b103600507900641c01030340c0c0c040342c038007160f903002000f080728500d031034003a84440030010f560030482030400044ca55152014601c006050684954560300000000311168004200c0c5070020031441c501c0340d43d019101c402c02c0c410511403d5000f40314508030506901101e82240c1e000300b44510704040d10006482800c401008582c8110040100128004500707000f8080038400c108007030409400d00b20064008417020f0100c1411102544085d40040c1401000343c03c0240085 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 381062751 1250 381061501 381061507
    0x3010c0507020105070f02100c2607240c030e16050a090917070b0105090106050f030a050901020712020d02070f030203030d050613060602010b1305090607030b04090f050607080c0703090506 83
    0x410064807440b0b41c60402500318581001d54891150310807a0a003015102b00600c012032030b0f0265a510b0b04a141050180000404100d031800052545030064500404040d40b01c07a04030000e00c490b800c40782c60408003400b2135103800441d0034140c8140240c5036400302e0a035030046454103110124101b80a2401400c100c0703aa104e204d101400203a140c0b100c000e00e54001304a503644401e1421468017082841a00c0c001d043c2c910000c141580950240d800410070030000c1070466940d2044d06c80540f4007e0010ad506543c01c110810100f06030480000401d01d0a4004011500780024024a8071585500c481003240ca81038045c4010f940100444154211205001c541515aa80025003080d080502c40c46400c1c504400080c807550103401400c10050212100d50820040000200a4440881e240c1c072103034103c8030000718a10b0080d4011740c3c2640026200180c61402560f50b07408107450420140c070039034043d604111907150b00103c41d56204102203640c500b4444140c1d0080e182007564010380744260008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 381064001 1250 381062751 381062753
    0x50c0703030e01090b07060204050a0e040b041b08030703031e0606021b040605060409050601020c10050304170d060609091b0f0507031b080315190e090f01240503010c050702010507 79
    0x1345905800f404030510000d9860140c3e19151000390710034844c060041004010000780410b0a20346030f0b2141c0d0f04141198010307551030340d4103030b8070003c921100c0c48038004851020415004c01c2020740003d0b446910009490b04910301320b030380c00046028480c2011414010107000556003c100090700000d000c506003402c40c2a100090301920940c2c10258000201180005800c10351303401650140c0d10a8082d0b90036614480140481c1d07524541442e03010070381c104042400501c03114407940800d940d071216242041c000b0118142a541c0581c01180004c2c01e94505004040303007882401d600041200725901e084800d824041c241c54a10001c0740c044c401701107002c100381030080300b2131226444441c210303804a1502d03107400341203908243c50b015107001001041c5001070070801d040721150085200d0b070346c03181e03441c04046510305a4000e2070709626000d41003c0f00002d0300240070786202440d0705c01c40400705405a0207803002c0111a42c2c03210f031080c0e0400c200440d1040d0040c045a00494080c030300644d0360416 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 381065251 1250 381064001 381064007
    0x21005090c0d0c0e0703020703050f0702030703140109050f06010302030715180603020406030b0a08100f0e01141b030c030703090201270603060f0e0a0c181d07050c0703030e01 77
    0x300e0300d201c5812607440b0049808100002104109680180301140f12030348942004908a0103501401404148204000d00e010107166000c0d01040d44001d003280c0d03c90b6100d5560a00a8180c200340c5200c9079102c05180342005030034040742c0c50300710800f03004000940c03642d000242d840f0b14a1085486041c040c00e01c4068440c42011020080130181109100b501d60381c0c003004000354040e200d00c0300041e1a0011040991601d0040d078001c9404950040c00c281080368420f800900340b0300c1030701005540e40c0241c0c103c0d400007802201402c1c02c0607c05c242c0585020b8414860844880c28100d036640002c10403c401750602109030b0744c1206c60380c500014075400700e100684190310016175000203a640d10071015500c03003201d9002003d4070903581d07050040580e5001a8060015a4010b8000340046080081c01111140d07000d105c040e09a40344ca0b18101c03981c10000b401c03165103074200c90402d6991850f101142040c540f0a00e4204540d880c1c03492508038504605a11110305c0d010090070425015440b101980c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 381066501 1250 381065251 381065263
    0x10170a0203091e2404030e0108070201020d0905030d0b120312280b040e07050604090f0605132702010804030f02010f0e03090a0905310b0a0203040c050405010602100509 74
    0x7842480e800400503003005650742d60150142c00300b100701e015419900311031942c000050207140c2c1b540344c01c04629401d40054490010080c95401159401d000c290307402a054001e60310024052009180c0c0d450f02c1d03001e40019542c2e21030015014816a103083c156540c0c000040b0345004064400c0c1c00126241d140a842c064240000d4500c0248d01800d2000c1c50030906034040c0c23030a16000c417000c0011080c084d210031384581540c07180c00e83c009020311040043d88040d0300034001e01c4010500010341d442d280c100203401340300d90780481440c1c0c40e9100b1400c070003c0c1030780a503071400d0441d040005d1803c0300c00c0da0000b800c07020001c1000342005041004881580d00035001020f00160301c01c010b00c011310092503400d0b0f4a80102102c6032240a131700310300185800072441001d015944420800da01d1003030000c0c8c2940100d0b00d00c2480301c611141012100007040407031600368001d80b42041301581e00e050600f8221030035401034001501c00d0745000010003481e500000d104040d03d561090109403682c03886443c1e4181f030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 381067751 1250 381066501 381066523
    0x412020309060a08153708030712020606010305040b0c0d0f05070f08100602030307050a09030c090c080618070c02010e03060412020d021b0f13060308040510170a020309 74
    0x102010420300c035015000f085151044d1000680e180603d1280000c02040d200525002090003140081202c126681c20606d100c002e10041e241410040d034440d212451a40030080a84021952000700407840d941801000c3d0031200c2480c040c4428149605c440c2e0110350b01504165902d88006024800483d0a8000e85081c0c0e103510010845882c10000103403540030110302e40300c00951484009050b07010719041150940c1d58a034005d40c03d651f1803680a90b80341d40300d505c805041c84840b003400000219045131a601400300b12201003860b02409201900b99007014080d180b040b8525110344003000c0c9c040f040c03643d003c01e5902d420260007800b4001614114141894030790103025039804c1105004105085440b03522070341e400c80790021070001f03080782c683d1100c41c010b80c82c0c9504d03c24500a00d1500c001900710354200100050708407451100ca44007144d03000c1d40111046000030508110390300d4140010b855410007810711446043c0414500307000074030000c00c0f0000555010020a5403501e00300b002c10711034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 381069001 1250 381067751 381067759
    0x60e04022d030a060e10030f0804080706020309040c0e030a02090601090302090c090315100b0f0c151506090310050a090206070b1006030b180c090d1a090102120412020309 75
    0xc5900e080028010ba00840d05401c4183c105107000a0b810b54199082e8407440c080c118120b14242140d0b2941035103d0800420713907260748140400b0415510901c001c800600c841d80085513260304800501c000d48074641d030302e6010301404108a40c100e44001c070710409616070454601040b030351000c3c0140d45801d241d4002940000548040014850b150b0005040c1c020b0100c04950000403801a024000482112019003102c0c10940411808144c00080c0c05418000c882c0581020250840d05190021440103081858602d00601c038a000c5503001402244c841139880b20b00c0c1c6856440400d1340d44003202001800385590304000f9130340f1005a808001060703402044183d03601007500b01116540401d490000000c2046c44000a1440c064400d205c400080502064203d0364010343d0110340a4000300040744240c170411044c051a03641014240034184980c1e0302d4559030004240701500103d008148c096268410402e403452403423403510840c0c2c420b40c0800408010400290200d08500a500006400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 381070251 1250 381069001 381069067
    0x10f0e060d0207150b060403050703030c030512041208250809010908040b04060e040c080f0907210b09030a20011103010617090a020f01051308030415020610060e0402 73
    0x300036111090f4808121310346000e01140150104100c40341c0306a00c402407080d48001810400a070040901c60000c5d8041c4c01d00905002d1007540c5900861030891b4111420345441c001501d00c65048108590804801c1403a4004410500d50079003424803907400c80c1040c071501000107610003500b50071842040764012035081e2981d07501c804480d0240c206004082c00b01d401c1b0103250205003468841c04024140b240d0350540991242c0c0404003450901074207603201c0e401103890200725007480c602d449006003a0600f0400340b807142c5041164140a0113014082c3d1754104000442800d03500514860b04050205810165104c201c04400e005040c11404035500c0c6c20080000903034560403017115041c061400c0207440503582d070030003007a8070f41d100c11400030343c44168605003558a500ca100580040105a0b602d44561a1900704441c80c58101d5030005500928a2a6491621b81c0c14008076030440b6a0302e814000050505030701404420213180d14900403503010403e81060041070070f0091405144400700300c0303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 381071501 1250 381070251 381070253
    0x14010515010c020609041103060a060c080d1d0708031905160b0c120c0301090c1e0806120604051e120a0f090e04050f070b0a05040306051e070302180108010302010f0e060d0207 77
    0x1f00ea0011a1018440c0076072000005103e4081c0c26100744080c4c2c003d00c001c1c501012003078024002e1910481c200c040c00e20040020400100402c611006400381c40020f40d06c0300d461036015941c00103084000e00802030300b8000011107183c0a9610303243e165200395296416030300c140d42d605c840c0c011204c044e03c040041e1414032103800d854800a40c10380d20800b0f01405004c003514400e40700e10302c0744d02041d413200018086140d0f6407845416183d4000c80018602c02540c0190030f6158509030082ea42038401e0b0304003480c0002201c103821182c45002d050103029203400c0a444000e244140164003448040c40075000d9140b00b0a403150710100007404181c03000312414246420001e61312980c805d800d01092045420100c3d072041241c00b5942c9512059031414503080c203640d5504058030011305242038155000d000d805c51030b01204040d61203620207680051316809504a441c0c10002a07098207418050f040c001400940d07440783c3d00041c1802c2c2418002a00900940072070410b21422089484203840800c4d860 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 381072751 1250 381071501 381071531
    0x50607230a05031b070501031e0b0a051521060d03080405010f06030b0f011a04050645010306050d12110d1107150f0c05030d060f0314010515010c02060904 68
    0x840390310720030105c41c0242d0300ca1005404448600e07100c150558100546125851425041071448000103403d01c00d11550f5900403459650105d1030845021101281c1000a84a113925400e03004848041e951041d09110740456008603105402408000f0501c000030240142504194000036100d0401c001641e0303642080f040b0207400b0344004100412a50002458064075101c80844c4004d440c0201d1600d45448104000b42e4000c20700340d401001d0f6001800000300c00601d55072125003c03034841c4803941800400036407240341c414075600e040c98501801449641c852850002070140d2002500d10442c0d15031ba4241d90007030075280c2c44407051044200c03110b40d90b54417144000c940d160300002c8641c210340720510b500030b400f101e0046ca00003810500c5801e2426104040100f0481d0007803007603900c0c010086a0100a45100d90001c0c112801d40302420010840c4081602401d507010a000f0441030505070f10700d200000181d0129410410050940d8007950b07201c0c012a50070400090007000300913440300c1d900d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 381074001 1250 381072751 381072787
    0x70603020406082a070212030301060201060f0e0403080604020304150504110406050d0f0210140f12070c1a090c0d050d030b03070305060f190c1701050607230a0503 72
    0x24005410b0320003043c0c0055000300c2665400c0c84010081c80c13610020b031540c80c840c4d0001017003a079104e441000c128410780e0003880110701a11141e8000b04040e800d00000b6450500c007944010500d0503240c0801000c60740c000c01907030b0010011100541c0c0c9032180d04201c001c62400a0012121a01d04001d200c10010341da0038111020100303580911200742d54100b0401d00c4d00c1108006003040015000c0b00700145469030845203d18514100414488100c005041c11340d00100305411010500045500040702c03510480f030b610003028504401c2041e0f2036a2141c198061409008030001d06001c0400d007942420302c40e0716000030010301171000600e410b0415540d211600151500800c0c030381261008141030200303031501a03c2d0440000c064a845800703501c10451002003031090102c1c810000601d01032401c2c05030505156070b0f40d079112080d40c000074240c0b88051040c2e000512801b81084a40000345105102c0e085d604d51810709486844848a1703441d0600168a2000b4514040040c400c001160b8000381 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 381075251 1250 381074001 381074009
    0xc0e0306070c060f0605030606100207080a08090915030c0d030e1309120504032003070312020322180f09021c030f08070503010e041406190b03160b030403110706030204 74
    0x100b071080544c45111003084076214002e858064004000251080c20110702240c400c81151048400716aa62411241405100f80040f6003904000424080510380105081d070464034a0a850001800c048000b81d80c8014000907507011300c1d42c01d0000b409148c00351a403a24212001f0f05091003000c0708041000c01401c804004555424040c059600210310940542d4140c030b50080e49081d82035451700d204d8140c0301d900c0312120350500ca60607021000903080c0c0c1c0310000d0152140c00450300d0b10f101c0c402405040c0000d80c002c0e1000340c1c0b00c0b5000c1002c45c201100f0181c00c031603500400141800c0300100310f0082c0c114100c01039003001001c80c80d0088c400c4009105070a007402a07071586c45158021800300c54405059404000140043c0018004003811101c81c50308240b14102c80d881c0449100f4500f0700f032075000c1350f51128240801e062010140b8450060907211a000c40c00303044000d902c06029802c07080c450003007800c81c0b000480081c08040c01040440760b0050020200e40550b5030311100207000c0d50140c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 381076501 1250 381075251 381075263
    0x132004080712050304182903100e06060d080d020c03040e01060518122b0f14040b09030a05010603110f0607050727060909140d120c0e0306070c 63
    0xc00100020001c40042c0c140b41d002d00035500e01894a01c810140320641540b15a490359a81340e010b2202400c52213401c12240e80e019040241001c01c005c040c02c00100c4210400d0850a144221035880408601c05a00c150b0454002122216a0070140301d5805180b01500319107100042c05080a840000940101c40c440b0200d40c5141e030b20345804640900469043d0484d090b10788130703441511b00d4038288003c0d0380000c0c00d08641480d02c031902c0741350b201200e03a0207801928000c483c0018240b50700c24410340f040c00301da00301891503403604118958113105138410103402e040e000c580d65410765001e024080506402900901c244c0780c0300c1c02d0403008908842e260910a05d0102c0c03062080341040d0084d02c10164200c0041c000f01403806a208103003158500344540142c60b1070032201c01045443c03180f40c01800d81c03003800250901ca20300e03151004180302c25900c01203034042002c401009a20108080d680f010030701001c10903805100c810348102040c1d801b215031500a1000700025180d00001825036503000315 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 381077751 1250 381076501 381076513
    0x12050106080f030d0902060d1a03070801020a0203090f12070807080106120f0b090c04151802030c030112030e0d1a060a080307030c0809040c05041802030f040213200408 74
    0x140c10305076151610015002d40350414403a04516241c40c3d40b01013510b50020b0b103c140380c4101052a1b404840140100c144200174410420f86182400c11100b03000d042028003c61801400c460060340e240500201a072080050f1846200140c9440382d0b8040609141d00031580d220391200c0c462521070400707009405840d0b1034603100080b4800d800074900d0619400c045901d950034011b489469104200404d114003922682c0f20600755078803075108a0129010456120315007506100341c00c00e40150389001c0f1000b59005000344200c41c070300d4100726070444021035180c200040041c501074526809084806503c015020042414030580460110b202842c21a80c00901c0d40c6d14000c002100c20140580c6429074412b0140c00d00090051050442c0e80c9e0080410a0501064400090030764105d00d07900e10010f400400e0402c1107406000c1c42c5130401803d52015800c0d03180c50506500303601801000079105015071601a0064101a444582c1c40c0cd010000601d1038072030307428000700e203500ca0b00c03a002c0f01e4030510b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 381079001 1250 381077751 381077759
    0x5030f18030703030e040509011d0a0506010b0a0e06070501060305150402011e050406030b0a0b13030506011403031206010509040e060613020f03012d03030314011415030c040f12050106 81
    0x101d020b0003642d9058a50321000c0d4140300921000b0800248640b005640c4c410300b03880c1c0c404002c0b0010382b80001500003008807820300d140c030609082e0180d03c0303003810341781c1401110070442e004000b03040c82700820307280d160300c0703a1090a240703024051692024000703000311213000c8050060524020b104a00070b8842280580e01d81110300e8002c460100c09070001041804140100f42c40b17500219052840101422a0207456101290541d1300a070659000c0044221041040050a0004500501c521174518882d04541d81c003003520791041d2020703030503444109800a1000d138003901c00e90b0400b40002c1c10820007500680e1207140e0b1004151122482144025100130040d5018003c0711540d2081c2540355003140d113000050f184890807401051000179940d80c10b903c040010303e003294000d600039900880c5800201c240c901c000e990603046943c0c0540588142c030426103a00c01c032490b8a0854688181e540c1c0e44a502004448c05182c0002c0a0504080300000c0c0500e030102070910014002d0b0000c000882d59 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 381080251 1250 381079001 381079003
    0xe031225080411040203090a1703010807080307030905040c091d0708090109031205101502060f06120606100905030f0708060a0c14031009050c07060e01020f07170705030f1803 77
    0x1124000d05025a8110344103541c2011780142da001284902101d404c40950390b02c1c02440565441c00c60000007000c00100304058040214000602d047c00c00b6526210450f10020050b10590140c9401951680b10416050340310300082c000070800040b500c0491001c01c400441965416513408002031019804a0300c034907010704c1140425541610b0300c0d40550070a48001d03001e480c005291164060240800007100391440144d40005c4045a020317040c00d2074030851069440380003900050152800003100141d843e80068080e0b0081c1c1d0840b19451400007600040313460b2005c030703007207c1e0300350044a070b20003102c13030000520a0a58045a0903510a41e0320003100d5030032500d1420614000401c2c0002080c00b401d440030003183c02411800c54121507549501d540015aa001d942c03c00340340c04c000520405000703080c4a9610070070550301c0254508440c07a1034008050040c0040944103844040b50800102501011104450340c040c09403030311480c1000c0502000d810500008036620510002034040b450 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 381081501 1250 381080251 381080267
    0xa08070504060c0b1506031801060b0313080d0603080d0905010518121803030a0915080907090209030109060e061e010b030403030f09021801260d030e031225 69
    0x1401c1c1d60f034407429001510350040010010b0207210707400c501e0080c1180300d61641001548990b141f07902d025a80103501e10b0300c0303084030080c0e4016550150107109000740e1f0142410300980c441c0d00444e5041e110b040d00070392000100a642d000500094000031419250442900000d490724000d0000b04441e590b10510070f13010095224800b421500502600c50040040001402c00f450000203d04089802e134000f0928546c01107120201142c5454010840c041d00d503400300701c1d0300c0c045107006d081e00c0c280540400d644d09428080d914040340c0203e500740050b1401d41c49180059000001884904409902d003503c4080559218100040900c0c07400b9a40104801ca80d040301c66801701e0174070390364854800714001c0c41d0741001000040d448503000c0e0b0250fa14003070908444140352540c0007055240844119035050203955848100200d95440b1001c20400b1504024825042c01c0100d04104020000c5040d442803000400c103070032020050040c009080e454086072042c00c1c0c104424020845407003914104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 381082751 1250 381081501 381081509
    0xb1609030c030219030605040f020a05100e01110a02060310060e030d050a0e040908030906070e03070e0103081308030301061d0103051302130b04020a020a05010605010905090a0905070f0602030a08070504 89
    0x201200200b0040c10310141110300310988018900d1302d19141c0c4d84800584406480c166904580144040c00703500d08030112000074041180e01266440c0320140c0641089422500d1905001c401c009694890b4014071850b040076500412050366840c20045004264900340034150006400c0b0703403d0300103400c00181c0390703070807041c9915080d003414110780d17085543c0e0b4140c41e5180c0c5c000b600c8100b46070000f030506020710300401e6031034064003041c81c0c100303001012001547c01e594483c0d440031004100401c803090210781941d0b0000c1e01159a032411400e101504141580408110710000000099807940800c22021162800040b9683c01c0d0101c0011800e940b400d881070248034000c84803ca00520b004243c203001d150300e06401241042c4001c3c0050102e03080f00d404180542c000b5840e02e41045001e22030032000d8070003424041859414032000c1003014400421610100369107003620401d0003000c01600005000b00c203801000316496440082d00c036048140d103c0c012a04280c00700d180b00b40102e00752015a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 381084001 1250 381082751 381082763
    0x5031014060319140a20030114010b07030804020339241e030705072901051005040909080d0c0f080615040503011401170703030503310b160903 63
    0x4074019132101d4810b4003400410314220f01c079020b00030300090050369105040700c10043c000000007035250300f031600759945986c5d102081080343e4018419860f89105a40b59181c1510b00f0b100c0ba07607030707030301c0070900e049042c0480000c00c102c0034045964800c0c0346207041c40368060b84002811b00b0f0822600340600300003003a580404040000e00f10f81104a82003019100c040450116100f001c202d5200d84003e03503000341c9818000610010b6084240b0001141403001c44544803000d03403d00c4000503082c046000c0c1070144500c5603403240b985411701b0344120305441c05440c10020030072400942d03280001c099400340444036400c508000511901900aa05100d4407007041e443e0b9581d25078a07081004240000200844400f560074000469951424400c520303108038100144403155051070240c1c0403803100c5c0b004415196104100900000340d01c00240c9170018074000c103003800d00703400e80c2ca1180f190043c1c001c9c80391040508581d1006001ca488501800b801070351124000c1300510903030480310030b0b80601001e844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 381085251 1250 381084001 381084043
    0x61d040605041820060904110d1b021209090406090201090807061716080103030f14040b03041b0b0d02180301050a0504060c090305070b2206020a02040b0d1e020a050310140603 77
    0x20609103600500c1a00345100035a52274a100e8541c480100c8000c64034414501a0703048015804c0c64041119080b1030748071050080c10403034100002603006078018802042c45444512003011640940c0c440c1025143d5141507a40e1292900e000a00d60a444d15443d0300c01010b080c01b14544400301200342d64141740595404000b130703007980c80a0340c90ba10281101c0c000c11000081544c1e16078a0703800600090100c0c0f0003050760724100303800c214080d0008000c124a0300c030070640007004924010003c03124440d24030361016890b01c03403c01b200e2091f01004104aa05035088c201001680e000b1607001c18880c40c41240304010b55080800c0c101d92951035400014016440391406005e1070728020041e01507181212840d804240d0000040010b040b841e900c00009a804a05102d00310701d041d000c0c42200b020103070340804c00c61400303480c2c280e0201a202c283c0f49140407810003107019500c9842488000d4200030381110601c030720306500c42c1c000701350320109146907040020100d00103140201c0c00c6030303007048512000d0750 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 381086501 1250 381085251 381085267
    0xb0301030803062404090b030616121802060415110111161b0e100e15040914070b07060f0501030f03050c2103040b070801061d04060504182006 63
    0x42c500b4111140d100d9040345044e918004511303000000d0001c1c00c900940071641d581d140c2c09052600001038002d0803070158011022000f10390003203001aa5012114020600d0618005c84450001a101000e504480001070200b0300300008071404050210ba541d4201c4075110310b0090900300e80c0712241c038910400003045600d9059030f2100100ea0503502509060204030f403141000205100706520007081204c1600410130f0710305400106000411007070140943c60320740316100c54001da0030701c59810720440e6600d0008080c005a982034411201800c002c41d903a0319100d050001013900412004c80e81c40b410003a402e9030004003809010b04036684501081c4805a65130341c207807003940000320380d540c142c896400782e020718801507407071207020050406886a03039007040d041000080c1d80c01013403170040c00042c20040000703507409007036901d04c031441003000344080700300c400014090101e030f500c5143d01038103009804034440101210a0011449090003425032480c80344c5500044040d00340040d8024403d02c4442 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 381087751 1250 381086501 381086509
    0xb190b030a0b010909060602010606110f0a0f050f060703060510030b06070206070f06020a18080d0c03050f0d02040b040e060a0612020703110a050c0307063905030705010203100b030103080306 84
    0x71810b10305040141443c0e890714180c0d8104c52841c2d22110040c1c0d1241010048283c02c074001a030800480005030680c0318101958668909903030b84000c069401d4001150203001c801e01034000c003014503a00390f03012410700e003a0040c040c1a280c01500d105058080f080e1190324040d100c0da41907404050700c083d00703103035040c5c0030071202d9008264140c038800e1240301d078940012803e1004000414168440704410300c9105903060710000213402c80650b80d84168011500c41da04000402010b070f034188bc01a9a8007015112040c0c203000703102801c0310b01d90020401041d602e0380318000c3c1094070060300c1401030980d0f9003000c10902d03482d207102d003401007900e44502d4152170f003503a00103001490203800c243c0501d019407050146806500141914250000f101c0301c80c2500d024000704000307014510700208040703007240c45920b8a0080c0642c41041040074140203401e81d041d0805944a150400c040c0c80d110800350800501270341c0111036100307844125800200702e050781f0109890580c0c1e0404911411a13031688280 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 381089001 1250 381087751 381087761
    0x15060a021f0e030715060b0702030309300a050d02161202040908070b0f01090c050f030402180c03090606010201021c0507140f0a08150d02010c1b090b190b030a 70
    0x26450258682041480044040000300340462155000c644003005445d402c60445049410008907600100502c402680c0c1c000f080c3da00b0100704441c0e10110181100d00b01d25244010038070115000c2802013241140c90001c82d000c180180075000740d45c0a1280440300b00d0712a000d000c0c10400d0b00a9803401841a8580314802403e034520142000445c0444d9444128958001e00402ca91204402c0308108018001c080a5801094890030620071240c0c4400c1c041c5c03483c00350306e060034806800440058159518040002e0106003d4242e010b00750400080650460b48100c1d401202c83c82000041103465205108a458282c1d5034030a501c445114607083e440a4000901108100014241d98101c04000c40c001421544164000260b580c1c48140014003503440003803895452410390002000a921070303803241c54103181d091815000224a5240050b20140001881215101c0105010646881540c461003065000710744c50010180300f000b4045410189004000e140c82c1c081c4045900e02e42e454001c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 381090251 1250 381089001 381089053
    0x6020604031112030a0204170a0308070513050d0506090601060215190f0c1d1e0402030c0d0c0c0c12052116050102040302040c2c060706050a0515060a02 67
    0x241c81c3d8052454907003800c0340c3c201355080e10040b940001c04104504608882010070750309440600074180040c1c0300604090401010481070080c0020402c01c110794109030040a00350040c62400450720310f04043c2d070f031001d00301c8009103136209031000403c0060000a10480307048122407405110b5640d0910341c8043d00d400d00d0309c4112251101e8050f400228140140c0c09408082d0b51003120900b0380409900c0403415400010303000c0d0a40a01d0703448001c200201c2102d050400759400340c1d90342c4400d141c408051184159141c00f40c0d01d421400c0c0302103503015440e405c416018a807107034001c0e5240e03a071003072221001c118003c0c129030040d803084540d02c003c4001c0c940c08103140c0000904040240e0300c81040700001000403150f0303940c005024411860140f180141000d0646804402034081c2d40104080300c13106490600309061340040c01000c0d5035003500301d4003442e038400310070300c42030814180d010042d00040e10b41201d5480c100303441d070380141044000e030303a41c42003242c0c000d200c08910f030351400600b1800650 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 381091501 1250 381090251 381090253
    0x6030b01050d14070201060918060b120d180b190c140a05030304120c0201050a03020306030109140307150b0f091909200f01090303080a0912020a1104020301060206040311 75
    0x142c106024188940c2603007111030340c0f10100f1441c0c0311a0080c00c4030340c590802948145040802c0300948000c900d8240516030141d00000d43c220600c0004424040c02555001d40d44210900307044520350107c02404400c86028001070855110180c1030307042d00074001c885041401c3e0504001c2280c0c0305481c47e202c410b014040c2d070700c1c903c840d0714181e0781003030040341080d03501ea4000000e000802100400507085806c1c40c0c41c02185000c42d50340003e001d48a004004003c140d00403000c695280d40a46c81001c0d44c50307106410820440010034099200e03000040c05440407448032601842041c40340c01081e548600c02444080c61900b41c1c1c042291140c8054080f0324680c010301320140002e001c500c2851291340c0581241311425071a07085c4048550f1120703075080d00a00c10082480c0351039030003020000c25aa418141905544c0d2007100c4400108800000681a03880c1c1150000c034294001c1070150ba002c3c0280542b500540c0da0303000388000d0384428801c400059001134000f41c0481d00c42c1c10030400a140c803078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 381092751 1250 381091501 381091507
    0x60e071401261f05030c0a050d0c050d030c02040c18090c020f0307050f1209060301031401020c07060f0e0f030601090209120a0321090c0b0307020316060c08090601080706030b0105 79
    0x2c0445140240031586034103c40303100c1d141d801c8035519601428008240031002000319104c2c6001003400400c0d0b40c480c0341d000703000524a002c104241d000c2188003a19000d000307040c0880403401c008101728113480081c2d0142d8501300e05c25241920070852002d40030641c0c8101040185400a00c00007040c040803040c0440c02001c185480074182400108180d5000d42c2c0201203d480d0703104014104101e409202002c2c030ba003000341480e1a1251310a0300d04403038200207640d8040400e03c2d40a40a40f003141d200d0301e514010108041151600700300154042d0303000307030b40d0340042c03034001d100b8081c0070308803480d07100c0d85a846000104454602074009107007011016201d030341c0d0401841d6104d803501010b0441100460408001c5841d400c66101d807450700aa400c80080c00b0340c81315900d8402e20502240240d40161200100068502e07000b00211002c0e0348007070713499100445850800800510b40c0301e031110005000b44010548800000071694141c5003c5d0014001d0189010426030080005030305141c1400428 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 381094001 1250 381092751 381092807
    0x204081002030f0121030503071e020607110a081603020c06190f080c07020f01140403080c070f0b040e0703060f0e060f062a0a0503040b07060e071401 66
    0x38040420380390361011015869003400d1541c01100c42058000d401640c2a9003542c1c04000f0344040d00e4202690181003d40ea07940300c0c91400c9800c003c003104180b50440040e800009416400a94036205482998600d92030099821400352201104034000d0310000d03050210001c0c40811481c0e200a0510a00403250700c0001c03c4085010394105c50b651890800700c00402c200701c00c4d00200701c41c1240c000741c42c002105241c03544110442d400b81100283c00f9444104941241c0d900500c1e00c64191065228403e44541d41c82c58409001e5201681404441c004c480c000a1030b04003201c100015600140031850409080c43c40c000701e060300c010941001c040c0c8404002401d110f00000250140800703090342056864410240554100c0404800340501c804200c0d110051000c1c000045844203146102407464880700181860014a42c602818078000018002900c80c00180180b4205100f14414812216440b00301c035100c14181c80303450501e400d0010000100d41c887c214105140c05100c0d0005030340303110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 381095251 1250 381094001 381094003
    0x307031b0905160801082a031e0102040f0510050418020d0c0503060103140c0306010e030a020a14030f21070816060c091a190c05060c040e09010c080415020408 70
    0x419541c211800103c140b0741103180c1e520109480c058603118008001c8004010810700180d031a0440303a92074440e1290b10401e0603a41484803020b00503040741c1250031480310051040c001d600c24420040b03071031542a000504c40c01c1100529002008513210641400c0c50a007800b1924112230105407003040d800c0000c4012151103105110039a51b840d5030307254a914141002400311142c1318000004411090100f1101e030f00408104e0380e12510a10784080f07408504800f01b8a4250300c0400254032900c04103000c90030b18080900411510170407402c03580464600d242d11b81d224030030001206040c0b02c1011a00038102240d03001001d2285c400d00526107400b880051449106807001d404580302511003030030b000c419600c400040041c1c070300000d86041015481640c4001485550f084e8950548104102c3c50803501034290b100d0451b4201003512540d142034130b6142d4840d8003a008800040100c0b001003140d42d00c051090a00b544041d844070341c2e9545841d258071720844c90f2500003003c0c698082201262142c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 381096501 1250 381095251 381095261
    0x106080c09071b0b01030605070809100b011202030c120106050304050312071b0c05090105030115030b1b04060e100908062716030212010c050403030c02061608070b010503010b0307031b09 82
    0x20003191042045d5041d442c2c00340c00c1da9005008003041120800c10b0014411020596006085c80c010001a90070030180042e103001081d44081c00300d0504c04010000d41585176002480c1025034408c240c3c4c8076a0301d550b420ba80320700040c7d038050204d03801800420b50714025070407016040082070400c002400c0f4180c0b032110b14000d203410111803c1c241003000b000f081c1020000540584401c400a1003d031401c06c035440103214151001404c40e0a46a0100300b808a1600400c1c0c0c40e5642c410310250741c0e60f01d980002d4102c4110307800a6002d514845000520a813180360f900056407121400350020352a00c245072104502c000e0f0030010391030700a07156514065030402c4041030480c6d00c84400c4a0151650041184440c1540d40084090341442030424500c1d901504032001e1382d80c0340c20580039145480c000f0030795138021000d804445035684001c030b409000566016041c118811501c220341a80c0300c41c145130036038035070000540d05544030700024000204131007e03102d00d9a01d0b0b291180d1040c0c0d507907404201690 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 381097751 1250 381096501 381096503
    0x414030a060c03151a0703050f16031d011d061e04140a09091a07020a020310050609090c01140702062206140a020303070311090d0b15030106080c09071b 67
    0x4d664401c4120000703000000040200040340c141c00a002410703074031540170711501200908000300041c0010002440a0650f4000d60300411000044182da1034040d000400121180740c811202d401c07440c405600c162100a0b05048460340203000340c43c42d00600c1401e410581d6034080300001028141c00d141e9060001e04002d00000b075840e100d83c0440d000b40400c1d007003a90410052141000c80700c10200364415032440b4006000120a080b542c0c50751412420300712903400c002e500d0b010f29990b0b4000070809812241c083c080803201e84080d5100c040d8281c0d51081c8070707003815000c215174400300034100110720040d244940c0080d00d05440d0a200f00c01d41441c40d07088540030f0300c0c85212880d0a0110341ea0050141c00070610f0301c01403502d8800803c030040c0d52800010004001c250300d48243c80074900c10b42003650240c45000e40741102540003490310000381601150914140c0090b03404100c8a85014004d03181103403202d5002c0c0100c0c0900000740219008010700100034041041510100c107030454140c01c02039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 381099001 1250 381097751 381097757
    0x81e04080406121116020612161103090a03020103110d050109021e0a2a060c021b032d0a0209040302061f03051f11040803120109020f0414030a060c 65
    0x582c10b00b1005450b1400104443c20150314080c8503d0752105400f00f280d02e40985070740504035500e60340c400203981e0700c50424982030b20088031003888107100315554812103500468585d081d2541c4c80b500d5059590007031003c850380c0940d1800c1c0c03c04c00355010382d200700c0c000b05010805618154050804600340e03082a80003000d6207034005a14a105140c4000400c1d91209040345c00b4503008450100822624200400c600b175011a06901d0402a0345151090710040e4890301c140546000350102944030410b0300d9141ca000e4215000111851078041820080612000400074003c8401f480381c40c21400074801a944a02c140101c1c0d0b405a5591074500780700714402d90080c02d0f81c0c9072045900c82c203482e034000680d86c0c840d0909410300000380c0200d070300f0541e844140c50310458010b200c6031140140009a4016108600004021500c3d0707802000608908841d03450a55890b40da404d20f1000700d12139501700c006440c000340801d10880d030700705814080c19040103044409140da261039034800c0b24030b490700681c04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 381100251 1250 381099001 381099007
    0xc21050c0d0c0215060f0303030c0a05300603030a0f110307060219120501050901030605070c0215070303060b03060a121403040b09040c0215070302070f0f0605010e090a0201020d081e0408 82
    0x44034500240c04d81e1122050311041c02e5500040c010907524080580190448c94022465035111171103241a03070104003911040d46840103241e00c6500002c00005040f20740c10011030001129801c000003210051240ca54a20060300c01e4504225071917181c0c603c95540c540010880c14000c5103040c005841d44050030402d00e1f050410041c070250882c1c00c1440c004102070b0414004000030350ba0188454110b23600800301060b80d6981c24400c840110146c0c0000358040c049000c1000c009501d0805483c02c030744607850401c03034540c0b100c0c40000180000c44d0750303660088aa15050280c61680c2030301741c14041c07107010741c0e00100011409840c01c540081d0004c0c0d14000f00814140b40c1c520b0140101d0490318210b00203000b03404075a0951500900005110200b80364002403041d081012102d403260120750002144020103042e4500340025003801e10a002e105040070010650401000c5100ca02030b80e8142c00030039004080180986017600020030000c1c0c0401c0040c0c0069424100b2409203120741e101c0c0b010195 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 381101501 1250 381100251 381100273
    0x515011403060709030f0320010c0503060f09010323030c0102180f06190509120a0501240e0105190b0a0c0201020f010c090e04020f0d0b04060c21050c0d0c02 69
    0x7180c404000d050004004c0c0060302040850510310066507181d4262810560b0001c1c0c00949919065036440480b146621b08403d140c1965800340c0034602030f0408460b00e02510441400b008440c030400c0c080640680c03000d980c0c65080300e100629915030001154240ca040c8004050300c10708a03044800c0c01c500a00702c02e0210034641c030b00894400b02c50a421070b074541c103040a2900c030004120040002c00700f170180014a2105681c0d41c00d00c20300980c2c0d0b4050840322100502c0c90700074043c0000c5044c0c80c201d214070109000c0c1c4081d001c000f150654600040c416100e0786401d08000c0001e041000301400e803031408601050b80c0b50391200600140000d6110002843c10b0382c40024503100c050042c030300c1564500304440c19125409501082103a40300000150720741c94900028990302000d09150b5070140350180703840100032480c1c640a2089004900030040102ca043c0107403221580807007102c402d0b01d902e8200c20340d9014150310282d040808043c0d11410800a00810b000b103a190751401c40c05070b800a00f10013 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 381102751 1250 381101501 381101503
    0x2280c021003020f0d0c0306050301150e06030d0f0804060f0e0c01021b03070311120109030909150e060105160203070b0409050603011112070c0b0a020a02010b0405160c0515011403 79
    0x2000303000300b460110319014002803124030901a10400c5620316803503640c4859214400c5d000078006d800300900801101d000010818030780042c51280080c100e800400143c0c07249804900d40d100000603840d070610442181c2c408a50401d4010030031100241d94004d4816490001c0c03041c040c038603041c500200f16454131a400645014811181d500a010032940c1d640c090b0389001c2220411a5845246110804c07c108001042c8010795554030501e07620302007490040c5a44101321108442c2c40003410801e02c494121010400441800340824050800d000308107d9403103039000301280e0035000182e1000141c5540000d080402641c80000840310100c1c1c10b01c00d41c00b140c81825082101100204561094044040e24a01510304061800505180060340541c01034008401d0300b640310011603094541028050029040340c65428015032804c480e0120b06c0c03c05100d0540180b191740d8003d040410702d110100c4044911142c1103030103004020003402483c00d2094101d0107095050101031011005000345 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 381104001 1250 381102751 381102769
    0x9020f0301050f04051b0a031b0507030f030504030206180a020a030501020d0e0f0a0303090c090204061206050613051005070807120212030c0d020a1103070f02010801141302280c02 79
    0x83c0e1060b0700d400305021103080140c07500e03070740c0c00d80014138940c4421003500700303800911a00c000304d940d5611988506051a910000920070036110703071246000075592050440032204c0440340100580d1014010614292044100740070301814142180c55540045e80414080070440d80200c8450f900400c2e02e10710818076005142c00c040300d5400805002c540031a6040c0e45440009000e000c0c10f944002c40c009210002c40c40d58084c00d14190300b9581e03a690740d04005c04800305070140c0c03203c503031070600081240c0c58187c0444480c4d54100c1c815841c8181080200405400c015045e0000e0100c20007483d40050010b102401101740540201034883c0206100a030800400c030007441a08002001000013865850f429940d10304641a4010303140c054083d402d8942108012141a603480003244990401c91196040100d0b1807003079840f50450b990721040031030f144070040c10003548480403110041d1b50204980c060403454082c182c5022024002985010404503080801c4001a684546050035402c0036000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 381105251 1250 381104001 381104029
    0xe09060a09093e0415241d1f02010204150302040e01050312030a09060612080705010b1906050d06170d021212041202150108030901020111040f12030909020f030105 72
    0x70240d0341e03a049106050000690300c000d521443d903840170030f00d600d0203504c00c1401500c030384d16038460150098161304d40900c6100c0740d0742d0001041a180c8401c5044402038008003400d024041c00c520401d180024403c8a4180b90f000e1700719035081c40001001501c5105d1130300000d400f5203005994a042400c42d40380214141c024138081e6000c68043c07800a0078100481c1d500003100300f0300099144035881c00d01b0280070740750700c0401c080f00304c00008030034044a07400078010180301e14001c202030428001440160f003013103601c500c0c407005c03501c004200f550700910040403519a211000030b040d98407800e10181c19500003c1c3c262060f8400100c04d00c0d05030301080b590b03201000d103150039400c212100c200700403c0100100000c00402e404c0441c0071901e0b008000a9282c3c0c01116040007143d0f8442c0041962500451801e40c015030a0084444081000c1e104039001d07285149010b04039070303041810b802407050040204400b000040000044c841515101500c1a610408102d036925403600c01003203074211441ca0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 381106501 1250 381105251 381105323
    0x1031b0918110319020c0a030e010815030718020d090f0c0b04120f06140405030d0b0a030b0a05060d0c09060501120b131e0f0603120f0e09060a0909 65
    0x903121031402c060507a0b500080450085056488040007139020f409030581c1c9100c1c51044421200800d0340250807068400c03802e03640c19450360744044202c00105031440e9207a81540000700103001244919031400c000202c010b4000d454242040e4541c0100c42d801502618007960101d01e0b00c00b00600480094010001440007505190605c207140c01e10140690000b800d10341503e0b00340d4100490f58000000c000303c0d950107a81076241034200366449078482d032941c455a516200c840c10381da14080c044c14007629002084003001c0d650325050300000b400003801c1140c0c800805940c0a0014541101003000b609241c0c1d00030640d2483c1400140048080024043e80c80d07003840f00d114050303152500400400e1950000c003280803111030002c002c004240352582d110844c108041000420203a41001044900c204080300c440c01a084080380c00400c11044440000c00d40c9000098514004840c01c0c4c0040c0002c0131102c805507200d8000048410440003115222050480b5410500e02e072a00c000c006000a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 381107751 1250 381106501 381106511
    0xb070b10062f060a051902040315021815040806060f130b013c0c03080a0b030709021c0e03391e01230408030601031b0918 54
    0x400040c04003090090020400e000b4502c60940700040d080c450040010200c090b07461900745900302d18080c1404690540311422004200c600d8002280b00b00c07004c07260401d00c0b49240070540c07000d95020303510084051a02014041c1106015540c044180f42002c1291046590b06d529100c0c0341403c0003001000c10744900c445110b40300080e00c07289030704030200720708803c0020780030021801030701e0785072144020903110307501d428820b071701405400c00e000402c003d0342c0704208410440c820122030b0a0905800180000c0c074610110f5030184032604440075424000302a00c40e1107880b0400102240c00034842c0400c400e03140c0500030b080707841171300c110070300003110201540c50002c0c20007010f14a030318120b40c1e0408010303440e03240c050401400485c1c0d110290140082d264040e141280340442c0213001c1c0c13421892035103881704210524004104a060003444010502c00b0751381c0d2512040b0280e0402800f03c1e062684544043c0c1000d0b003011055010b152507600c99901090412040141c9000903803c012080341c508 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 381109001 1250 381107751 381107759
    0x21218120d0e1c021005100b120a0f020a0e19080d110f010c0302070b15030a06020c030706050f09070b07050304050415030501060b03061503130803060117010b070b10 73
    0x5030840d210003910800200700b07400b0a40c001898200d00c55030100035420414030000c0681d50205100808100c819800d00243d15904005590b2410300e102e01c5200c10400c00100a145182c0d8a44941c80321100c40e00085026401c0c0d21041070b6070107198204009000942c40c5c00183c50011020415041070b2074480d0025410b01a5071540c07508000d091b8401d0184425010314009030411140907981000c0c0020b021500e59500b01501039004072004a4901105400048140581e068200c1d81224000d0003403201d074111340c40e580300039442419080190f00041000d100030500601030b00740500d214101400f410b1400c80045400e085903500541d488104c200705003404603100200f80c4042d50012100002d425405448136433144040350b000402075420320400149002c20711026520901003900c0843d02c071049190301400300e110171255074101d0f06a00e16114049400300c000307182d00c00c6060500340a010050b51200d08992800d80c840c1c3c43c60a0002251005c200c183c003009500164003a502440700c6042c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 381110251 1250 381109001 381109033
    0x22240b2715030115180b0616081312050d110f0a0210090e0a02040806010906080307150b04060803030105030c010804030c031b062c030f09091801021218 67
    0x4040d00036100d05015031112407140d0380c29400340c480096811010b8008a50f5554a21010349028003888126460842e0320095410aa404c50b602e144000104c0760b01400d03155141c0c2c1a60300060401c0c0840078407881c0100307130b8142003005000d01c02e005000034014070701412002490707004141d0000d909a0456075158417902c800190f1038280344e81c111070800c0c1e03030500e21714115131000c250b6211451681800007841948401d0b54001d0054621480c140c1b0791680c0c03a02844000ea56180c4541d151301e9204010300804520007009054800c0d070400340205442c00300c1d80000d416203202cae4000a102ea08004010010340c80c0402900315460020700b0800810b14140e18050144040c0402c05400c0c44280c48141050002403942c0c14600e50b8448020820810b808803150000c2c12000c0701c040e0303829007001a26030010000016140740f0000700d8265880c020420003440b0340c401c03000d8644007e03c1a9507088042040302030029100030190407412000c10b01e05030007005080b0021074030302055908840750b21100707094 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 381111501 1250 381110251 381110329
    0xc1206470705010f0c051e030c070b060a0504020f0d0f061a03040f081206240f1308101e0b010905010509010c05060f070f030522240b 59
    0x34000d216920350240382040c6000d0000461041070741340c9050b156890700b540080140c207034003881d050040079440c0400000300a0348001c0d10014580c1c031051100c1d000090801e240f45a0100c00a80714008096465003c1400d9130000f90080c070380d10001060541d041c4001d4410111441441903041c0200da1920000300d14802e8a0303410302520080c0040003800380505064000e00550388040d0541c1d940d1100b08000d12000b00c2689c0b824450111074021301001802c41083d141e043c0a5465000d02d0100824251540c40d44042d192105a80c0390100c0010040024044074202041008010402203d000d4011070b51211000c2c0080000e0310f003580203040399034044070f0441540c3e03003030074496074883c022001680c1c4500c0b9880000d0480c45003c0820be800c000303900c2c440d40134000e00e84654616000200c2c00390b080e20422100350300b15004002d111400b540c0301140c0083c1441c01885103000702c0100c600310100d60113030386140c034074250388a82d240425802d00c9080407c51820300c0001d030010000d05c649c03044801c0c07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 381112751 1250 381111501 381111629
    0x4050604060c080f070807030e0102010203091c091d070e060406021207080706022701020c010c08030a09140c0a050108010e060915031e07120804090c1206 68
    0xc0e42e03003026020044001c0848000c0c0b084002100d03210040c030700d000304055000000490000f4041603644405500500035a80600700c1c440142c0f40041c51190a14071013510260f14504000c00c01d080010403d032102c4440c0003825043c0c041403010316002d078000c0e00c035021a008030703030007808204810808140c0c0802d124036060040751459039940300c6414400746501600e5400303449180300140c5040c4102c501d02066281c00c64641c08035422001000059031034014000718280411044409400040c1c403940007103500c0301d440e071b0b030004001d1007907282d00d8110b8600308000c1c401d82e8049070941072286001c030351901c0101801d10707040380f456040207461604168050722050060400e4000300300d0341c0450341034401c4840d0000d03040300da542c0c1d0890b055031525040448000f206009407003000c6000311144180d084000e070002003e82c6410302e4910004001c282401240d0708120114907405d00300303512030044c00b009003480700d0f4203c240400c09860300c004e0304400b03140c106112941c2c510b1030340e50803042e51100131031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 381114001 1250 381112751 381112757
    0x1a010906050d05151c0501060e0108030901050f0c0d0215010e190f060b13030308090a0c061202040306050114130e1c03020d0207031e020a0b0402060901031503050601060e060405060406 81
    0x80d03c600f20b8038954113050020441d8080c0d8180c40d030f401c0c1501031140070240d01e030041000380425640c824046200040a000b05c1142e60410000042554002c03001400340f4046c1c0034030300f448c0c816525651800c0289025483d00141c00108506402c1d446001c4c5040c054600c1200d80c0d2124140150100807180c55a95503120094451424a400420590042000b01802006a83e840c1d84103291162600c91600007140880d030088049106103400041c691203195100e442d600d11903003001c6040d110450091815204642c00f00408400901076014140c002d03c50740129000c03d0304801c0c100440303036058140d000c000b6450012244260703640081d03c10701c4c0101e0207910f001940740a80c81103000c0e00c07030820441541030001812208041e4030400c1111381900c42c500319400390410311f2040f41c4071080250045c22044943c4040b401625143c0b00a10450354141030001d21789186e0a000003a1800c1c60388140c03040d4000c10010440c0d690000c80440054004543d81440c05041100007045030169019803410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 381115107 1106 381114001 381114011
    0x9060606020d020c0a0302210a1101031a011d060c01060b030601030b0105120c160f050a020f0a03020303030a05040c0506070f0c0902030705031501030b040f1a010906050d 75
    0x444402050380c000549140c0821098040002300d9824501441041e20a00c903030402500c5403452140c1415500c640444001401302d45540c031a0076900058080b181840380c0c0e218000c0607a540003a190107800c0f2904001059241c0501001d246007903284c52008a00c40b04c40c1c1000d0342c4502026a42840100d8969004460070b02030381c0348000c5a1b0442901241030b41c55408060003052001504403c1a001551140b00804504450580301e42d0480b10141003503042142005800c0742003515844859480c580c04030f1307664840100303907002d00f81c0d5030030200d03007002144807903040102001040c240d110806418400e032800303000c0d001250300e00b0b0b00d100006501400d0340242c03442141580c40d428110340c1d5540307000480200d800c6d0903c1c101507482e03191044940e0785120700402407101003400580480c014400c109440d5080c1140b506100700d8000c01c000d099800411609c60b41c00c0b2000203d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 380935251 381115107 := by
  have h0 := BRFrame.cov_init 380935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 380935251 ≤ n) (h2 : n < 381115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
