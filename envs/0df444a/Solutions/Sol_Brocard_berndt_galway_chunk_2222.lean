-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2222
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:02:47.086934+00:00
-- url     : https://prove2.me/submissions/b64bfd00-2ada-4325-a9b5-a1acd4768c63

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 399460431 ≤ n < 399640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 399461681 1250 399460431 399460459
    0xe090603030a180302100e031524042c0f0a0308071b020909010c020d02030c10020a05040918030306060f1215080a0803150303040b030f1503030d140a0b0d02 69
    0x116400400458000e0301b481c64113000d0040045c00f1243c482c03215402845190303642e0b0990f8540b420030a1045807003901c0d00e00309002414400304450300ca18500c542c4192030f14125820b0014079840348810300304412480c0054040d550569082400181d1132000a4000c14942001709402c208038540c00f40706890310080311030064602040d5807c00c51006504285007008001990074154001c0c01d1920315038089408002c0c0300c01c0304a070f5030300c14040003803420b4001c450714019003036041d005400603c18505240e400e00792244940c0007224007844100305001c8130441c89805040d01489101d002d031000c0c1c603190040780d0018601600c000100905425a1652030440b040d040000ea0101005010000282d400d0201c9900700030340d440d0000c0e00c02940664401076441481d150000445044410f0321842c9419903031120300802c0d040f80010302520b00c030800e40203c407207035a034244010600c004500c0000180400c00c00307813007441c00030700170902c8000c9840c1509200350795440f8000c401d441d0ba07044803403489100c21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 399462931 1250 399461681 399461717
    0x120614100c05030a030b060408060403030c090f03150207080c030c011509111b010b061809070c170903100c0f0f03061a0903030f1201170a0b07050306041118010e090603030a 76
    0x3031389c3c0c00b10000c1d0084000303102c100740c4d00d81c0205c1c082c41c5840e900d9540c9592140b00113400c40c03c4500c402481264101c10410141c440f0340c01400d0800e0250306c255080802c0f454100d070031913201641c041a16551422800c02c211607915200000d44040c0348204000400f200080d242d070711030185505c46007446c0c05014131084c242504000c2107884068691501c521002c51700300c0c5d20602041449116090340000a03080c140b0039402c41c113015130880500d094130003000025242a034000e4102641500038807210b041c4038501c03030264142280301035560240008882c2802000350000606030b40406041c0302c0300f0800700f1241d0840410305a012040c1581d0303840d80c4400249544503201c100076141c03401090109048281740035981c1203441a4110f074580c2101501850b07200c03007410000500c007000b80e10114406920400165500510190000403d080850700b08038440d0441c0000d45491420024071100550344013800d42d2016105940d62900c500305900042c0d02c038003070309601100300000c28602c482c140700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 399464181 1250 399462931 399462937
    0x109050111030c120c0d0f0c030e03011e09060516140a020106050a150206060406080304181427060405030a08070507020406090e07050109080607140415120513051507120614100c05030a030b06 84
    0x410314444c616401030482c3c370b00c000c2c0078450790546846203000c1c000742e211200a82051141c3e41c00c2e640d800741d040e02c1c64181c00800d41003161050110b650381c02001c00c0325124286250040e10b035102d446000518088002480c102004040c240994200201000500710000507103054a03a4004a800d010500c20b1044e4011f24012154110101c2c1600c148449030b0940c02c0c0708086030481c1c0308000c2c0b2080005280300e5480301d066070018240c0d801040b071016043d115582c00c0750070070814982203107041d406400160030355900d038003d20800742e643c41d10641d80307140800c0208001c2a080c01c2c082c0c41c1c00e01c1c00491544561300202010180b2484401c00c4400d0a2440200ca0103801000c48058580d0b404440041961f03d6140403913400c10f25003804030310615020400018000d600c18002e1403003802d105400c2340d030100d01030881d405022801d415a4035001c00f901511000e40208034010401e4910007080100c03000e20710401e03205000079092070350003044010049a030700c0c049506010403215141e20102e07a880c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 399465431 1250 399464181 399464201
    0x1104020d11030c040501230d09060204030803090105010e070903030903080915071103011a06190e030d08061008040c14010c0c03080a0e030c0109050111030c120c0d0f0c030e0301 78
    0x58001082241402085004e0000c2e02c500307a892211a040c820801c404102c0c5961040401d92801d111021021100e90083e401440c40b4500260a02d644ca5646141a40041c0c600741c3d4140d4440c2c2c0140101d40c81d401700d00f5880070722490100b04580c84c4d40c0f0098068400d0b40005440c0c0b40d00010b40306225220410190301c500300303250751969500001c0c14aa108106a0b612041c420750a101c004000604894152100700380010222460440131325491403c80c060380d010711043c03100c030303c1010000340d80078007030414411129104c1c008e06140060400004104030a0540d0a0041c00f000380008501c52620844c00e848000071041074030b403205401079443d1000e00100402d480b2005201208102e50320000c1c1c00c0040301912403500203034601d410580c0350980c24400e41d00003507940c1010400c540c46403000c442030910310000d40340740141a429041c14110b51815450301850300050110010400300131140c1d1042207450031114100340301800928681c00b0b20400b40030010784411051140c2da080d84086115 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 399466681 1250 399465431 399465461
    0x30703050a031d0402030709050105070c09050a090320060105010c08070f081b1b0f040906020a050a080702010e0c01140c0616020f01271505040b0604181104020d 71
    0x31036240307002070040b00d8080900141c103c5409032030b0030600b094000c0c3c900800254031403090b4141000c00448141d009400d0a81d41c0c0345401c00d0010792030160f8452680101e08040000c12000000d041c0945140c10780c0c080c41900400321031039546181d1021601c00e06581c0e09107009071000e0040c2c18101d0707880c080c0c80c0c0c0c040c1c02d86c08140c50b40e0041206050040484011380e8440314000c280807029180c07252455206071040b60800b010303008191505403080c03031400600400014544141e51940741c100d810200f90640425000603480c032009400c00d00c081d13071081c042d10081c8007048a00c1c3c412a21091581040340c1802122038200d00c500d8103000654a00c4082e0104652492506001ea40e403d08074010040c40035018450509190341e106005003010b43d1550205000345903500c900340d2150b01600380c401c3d00d0004012682e00f200d1171407070107002c0c000c5001d040c4420700340c00c103501000102e4542d2034a41010b01c4a0794075440c001180a482c40f40080b4003241c0060f00c500c5813a2000015012051310807a007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 399467931 1250 399466681 399466693
    0x70203120c0301063e010f0e150f0108120702130216140d05041401020118080d0b0418030e03071e0e0a18110303040e0112050111032403070305 63
    0x180900440a14103e45842d6109402c0a5008042c56603c100b136112000c4841400755203144900c440104942d05c1050500c00041e070000d0800034201201c8400b1341c003c10036017000c002c0d40000c0c0c5a0582080e000307074080e803076601075500d050303195a5107640c2d0b25180541c040005c18030006540d200620780e420000181320039075403881c83c0c0d101c10420070044102200e410f4404407405240190008d80c90103c0300040d200c180c83d243c2031032034420b02d0520110140b811992141c0340a120320f04406e0303c1a80310b45c0b00d80d004503281c00a803501401550000703550580218030b49143c03401da1120001402024903058100001d030381203440c0c0403906156954004c0303492a10900e074581a600e80340071002d822130b0f0101d08110410f444480f08003080d02d010001c419501007c0001c18000300d00c10f03500500078030200400f249c0c80c03d42d4402c1c801c01038030300c00d03840b5103401030549a5007810f1140a02a2a061040e501511403941c40c000001c15601d402044c03a204c9500005400f58226440030072030705020750b802034100c1e10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 399469181 1250 399467931 399467941
    0x2101a1c02040614062506152103050301120f0c060e03010f0501030b0106050d020c2d0705060f070c080a060e0f010e030415051b0c0103060b03040b0f07020312 70
    0xc0d29210101280228a40070300002c0c40512070341d210706031100041c05589400c1400c0144046000007015400141203170003046000101c1520403c904180700d64031003018a4500807841c0e084601000078400000144a41c7c0000a81d0220031031303044d62441d41d6490503140040c1403000381080b020320010310708003900901064468011208040440c0120001d0240f038040301c90a0050f0f070350a100047c08881440014003105002e42c000d80400743c2100001400d22140000703c6103050881c0e41441106414400c86c401d44e0344c91401d258400081000c0100005490300000c40d0084c418020014001038010540400700306080112031f0007401081d00315103c0003a40e08218000f085201000403281c800c2c0904e41441c810180180c1d4910032910014504203440e0030350110041c03069130b4552003049801c02c903854500205485002000c42c07024000c0801080c1c1c4000501201d046030401c9121070342c02d10070070000079070b580003a682c000b500f0b84507900c0607220b0803030a03441d602422190107040704c06542080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 399470431 1250 399469181 399469219
    0x9040b07030b18062e050322030c0c0603051b0307031509020a0e1c020402070f051e0609030f0403061d1209091006050703110f100509011b02101a 64
    0x241c040e40e001c80700100c089603055070101440301c00784020040611003211205d4441d000710702555008181502001001d20075020701401d03a00b001c0c1e0100c0124581c80b028109200a600b61407020b13000c01d0408000f03c0c01c3c41140c02c0300c01c82181e41a00d02c00d0f000000000c250a03c290001d00211a405503500c05450f1542e44500103500301000500000d1f032040c0301d0b103049107496098a41205224182da800d1194140c00f40006540300c0351040e501e102d26445c201c00010003c228030308050442004500d5030340c54072203142d0706141c0090940c0055038001d000607240c410352403081b142240e5006100040140418441d86030000c0d5440300c0e5400c0f40684540c155007024494000d02c0401001c81c3e040c14a5640d4903000305500246000b004000f6400703010f02e10009000d048011410340e8050308444d614450b05464524003d402452001d60a4480c800c0c00341004003405151002c2071904903210035220040d500075950403035010825915034441000102c83d01d0b202070310400e00d03a000780601c0072201c0302071094 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 399471681 1250 399470431 399470479
    0xf19051003050105190513020d06050604060c03030506090717100906180c020105010f03030e030106030b0117160305060619090504210927110304050c01020d0e09040b07030b 76
    0x240202007841c0907000043c045c200f050f0549800030a49441c5a41040d1684029000784070b0810400d030f0b0303440000c903496a542c2c0c007400003043c140c0d8030030071a4041c0c5d2600500340c44010304918011480c000c244a8025080111549403400e685020600b5944075440e1030030708851984002640c80c40e0000100b4162034070038240c4100492820144145c0103c18000c03400c03600c00341f25040c0e61600c0700d0401d000003441000001900c130320080000c0780301516512203c070302c0c44007a441805407140c90840c01c50b541d88140a03408a41c03101b0030002c02071514645903507803100310041195108400b54000c11040000649455016085204080102e07180a1811000006149a411220030800807845900520448540068880941d41c03043c00309100c00b8240044419140d0303d40d01151110600d001120040001d188a14041c40041404011400029003045080c40140003000008007814200d5107511401540141d40402c80180c990341c0c85100310300414030b6172605c991103810081201e10107140c220f20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 399472931 1250 399471681 399471689
    0x50303130f1b030308070203040806011701021308030d1a0a0303030203180d09050a15020a140a02030a08210108030901200d020127021503100e09010203090118020f190510030501 78
    0x248142c03a8076201c4040c2d075a80279502c5504000c0d0310210041c00080301c400c2070a000f07591400d00150030300401600d01ca04010050300120107076840410800c014800c940124401e03d41105519242510b5680100d007594140d400042c0903d50008080381000201c043d00180003138a8100b60382003d8503581d002801603040e07100d01ba20030f1200d02c8001c140c00303481c1040040284120340003010110010360b60004100c542c001c0e2402c56015000095026031410b01c0580074080c458055180d03540d001105c81e80d001c0e525101c0c00b03822030041c41700600c03220307800000301c079000c07403007402e00c041e803074400e20f410740d108041c00981040903002d50700b4003d0b011501504403114440c07103c1c0805840000160380c07003000c0000007001070360203e03c07070384220000c0791510b00454010000c0c9100e2200542c8400010303400c28016601c4c0e071800e039400400c0045100080c4034100b035029802e44510b4047c0416000114040c0c0d41202c180c2c820446c9070b000c19402004440340c04000c1c0300240a0380041d60100002800520003441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 399474181 1250 399472931 399472937
    0x2120327040b01020a0f03140d05060a14030607081f0303050a09060809190533130b01180f05090f0c060702060a0f05040f03080c0d0c050303130f1b0303 67
    0xd019401490280500b6a40100c107078010400d680c221b071518080d8803007a8100b81c0601c2049070150031070003124002410707409107203d004a01400c10009103e200f0700654004000d240c0c03861448a4165404280c1e903403c5500c1d842c12000c240c0b10702e4500a1f924400300306a003802450440700004058100780600305840702611071600b901c2d42c0c0c6600382c039014021641440a6000381a10300b0250040f5030408031403500680c00c6614008000c44e01c00101048984082408a003030119000c0c90821040115401408445c91220642d07155459400c1420306004599840b0714130050007100010035805610a101ca0305010701c8142890301c0c0c07580d03d946100c500d800f624000d07490460024100070003121151640982414641843c100c402c03102043d40e0403032107007002002c1000180c0d400c401a90316001d58040c0b040c0d2640d5012803003105280c18940150201800020710038040824404025070780e2010b0001c044024141103882c0c41c0d111401d4540c03004000003410204d00c1c0f45103003500d0440096a20a072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 399475431 1250 399474181 399474247
    0x30a1b030b090f100b0a0e100509030d020f071512290109080d0c03180807091a0a150e090108030a09050306160c02130203071107050402040509060d021203 68
    0x1d410300c03c00d150700326070010b0321400c400c00410103100e0020061101104900d0020045864a0001490005080d606600080c000710f410640341c5028483c5512000060000341810503103400d4003506c6610b01d10501c2428250800c5002c1c0080c020305024400c05401d04041040380e2100c00007036809100340f01c90030401100c058200000d94081c2221100b80c1d0414002464141124a0101c40c1005869401c4042110050811440281c81c441c010041c000e80b00241526a0414903854100e400c4204204c6c0700c00c1000b00f1402994541c1c440007c01c1d50403126062229070002c00003992a03d10141165400c4070400e0000181c4510210261036140142e60310355650b00c1d41c1e0001c050b038035002540c01ca030315a01940410904c0303030b0080c42c2e415012840034145500000000c001c0310100d80040310000e0200d145400e07207590201041c40600d000d00011903085041c14108408260780d180014412405610760080c2081550748000400007282d030031600b00c0b039680110821039400b6110380080c40400c1c00300c030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 399476681 1250 399475431 399475441
    0x9050d0c0c150905150717030f07030506060a08100b041202030d020705060d181a1008060c0d020c0a05070b0d05060105030411090717011e09050f0705030a1b030b09 72
    0x5940c180b8026076103645440609051500b0052040000c0b4425241d5001c100300038000a0f4060b41c80700401c0012000c01d50722442d0003207c100030400d0040101c82058641002c101040c0d980c10151400c03104c0c940b45c880116592101031140b4902180c0010009850100d00040d80c4240e01015452031403098083c2d60704c107800d1140583e42c40d0715600500d98007a00034030a40182c0100ca070711890015041c4d030325582580041d600c072040200c7d00308800c2c210070a5001d041001c0c04503141e05c2d4000801003000100920300e4000540d04035401400c50103c09190001448140404c040200e08507241e00079081d10641d0765130302c0d214441036001d4007011480d90306100000d0b100b98040e800f601d20031038002d031044001100703040c20881c0c0710030000c120074103203c200c441c2034000800500c0098040d00110048265562240e0350904012800303501803910030781818200030003e4107907050640c04c04807a0911540383c1e101e05500f07001030040c800c9040070007101035062501890345500214020b00e07056441c1051a212 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 399477931 1250 399476681 399476699
    0x11b030f140403050c07030210050705010506030c151608030108060f010e060f010309030521070905030309030307060b0a121505070c0b040b0c1e0301030605090703030e0d0609050d0c0c 81
    0x419032002a078005803000a004a4043e0004000c08061001601c0a15440b030340000d00010792117090500091012036a071041041c00d110707603904544110000c0c07a040801c10009045080848159030501c1d50211f40a11036503020345901c4c0d211a481816143c0b81c2d0384a200b5190f41d4941121319100d40443d500c0002820104440700a00841000c0e00f100c048081c03190042d40034220081d411410441e040100048070754086121070103005140c5000d40c8a400e01c8400101107441a0308040d209030400c0094441b1680c00004650040d603101c1c80100e841c4c1c103a4000101d2141003540b00300301c480c1c103201d40c1008001005886060408010b041000030b0b032501c901c112a0740f200400b004000f4420742c0041000700352800200e580c0a00c1c11030299280440c441300d000081107004201a44944c00840180700f0801640684e80c2c3c4000c6000090118a00d5a2002010081c520304a07a014802d40c0d0490320034005c243d08094141c0350044111211262990002001440d8000c000e65030042d80080101d8481d007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 399479181 1250 399477931 399477941
    0x30a150e0712030e06130e16030e0c09060906010e180703140412110c061303021806130e0118120f05040f0519080106121415011701060503011b030f 65
    0x1406985404107900701c4030601c031385da6010400d01002e28001000000c1c502030810002d91042d10440504242001c1700c80c03028080c0d815425000c0c0a40d0884c2e03a0062041c2c0307410b0462507100008449070b07000c0703854980050360302c40800744c0001d03044038440e07405540c0c0e1070f641a9528000c0d40266010454080c1c1c20a2013125903074143c40062903828290343ca0300c095441091801000d22000c4280c3e44288104000901180d008040c0c468500c14003101c10000d510388003c0d005280740305522031a90500e80500000d01e000034280b07046070813664400507070146620075480302c3c2c0900714509240b1025840b505210358443d811007035040000d090004140161403103203081d6011145801000302007141000100600c0b100808201c001d0403580e2180069000e0090148800901a81d0f40d040b0b502e1010f418500c08030040341a030790800380d009111216600c461113401c0c60449510b5400a00d2480d445003000c4d024001c290301c8154907600340382c2c0414200c203410440540f0f0712502e0f281003103600341e010040402d0b65 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 399480431 1250 399479181 399479183
    0xc153305040207030e0904060605060406110106090c05250209102d1712040e01180908030402040216151b020118030806210a1502030f070e030a150e0712 67
    0x541740c00002821410850001a0421310404001c5001500c0703030003181c8103070442e9202c0320000c1d00856135603e14803428030940003c3e0003d54014000500060303006411807048100c014004502c080c89508031600d00030b5680d00003580101410035909011b0404804181d05005403501080e100c45525040258080615403039040d40007942c1c203249c84c00054640c1400500e44901d11070141d402e0b030308100f12112000340041c0c00c05440703154240d41811075105600c2a0080e2400180d403400c1c0110012400c60400d80340d00560440d009a075885064903400001e05040000514003407404c10b030604c076035120790403031114040c051130700403613524400e030040b804d80b1034040301c0028404103451044080307881081541d5100001400700080104c40c1c10315868201e91a6007030820325003040300d840d4100107640d41490401600da903c20350860601051000c43c160000e8000000d0080400301c1440c1074405022000085800c5010284110004441d800180109010701401c0c2e00503c20003003180324051071000d14007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 399481681 1250 399480431 399480437
    0xa0302580308041e02030312040515010e042402070c05031209091b090901090501030c12031205041e0b0f010801090804120c091a0a060509010c15330504020703 70
    0x503441c3d54880c0890510044440b00c1540310300715040c4056201000244200720307410300307030000380e103400d08049080810181d03e40c81c0b60056500100b055040082503907405c260170125400005904500d10748602440801c080001e85c0007103803031414800030340d680741d08071038040e010368148400d21464844c1034401e440d243d40c4d0201c207907404a1420300b00d03600c441040c0700055450f0381c904001d0200041050000340d22003122284c8402c010310030030180115240c001c01034648004401441542d018298450f0048003c1c1d04d03507920400101445207121130160808420700c4414209136050030f01a841c0e07403040b1110040d0105103400010740d00303070503c40d6480b02908911418202400c140a11841032119201a111484204008110b05240b4421044807074041c1010a01e140030980500540700b003d80e0000042c8607041c4101c005036604186c0d01882c256000101d904209a03030344103600140190461006100c03900307a90000c49524a0030401b440032000c10040c1e400725038940401040c0d120382c0c3c0c8001c0c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 399482931 1250 399481681 399481697
    0x8150114160602040317130e0c04140307030204110a090f08030306060307030e0d030209011806090b0f04030804151205091f0b0d060f06060e0a03025803 67
    0x841c02540100c940740c5200c0c0c940540b6080d52500c4170b00c0b840708041403070b520354540060350301d080281080420009000c9000744d030710b40340742c511340d800c4980c01140303e105944c4c2070020f4070300d8403130780c0034420301c409036500804c10044640304549103e21600840c6000e0049201c105000c241400b9154207602180c0c1c0010003585580d4962090280d1b43d003002d0040d00a061701c0d12800307807420b81c00703010340b01a9000d40daa005840784108000100300c1010940c209045181248050010b1360744a8034003801d44280a0189965420300c800f0000a4030807540040e05494002c540482c0038400c0d8006105502c0490b034444000c1085140200c007282d1302590404e0540e4070180c0d0060207820101d0308501080c400000c0014070112100103d400070302e80d940e080314100d61311000142c490300644186000b0b040503203010b0700e440c1804404200d01a90a000103845410203004018103800380a0107026091500744421038080b070913000313529454810944901007118009894030203d05109003400e1283d425503a5161 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 399484181 1250 399482931 399482947
    0x140d0c0b070e010c051218040b150a0e0a0905100b04080d0e0d050f250315150f060503090607050f03070e06040f0303080108060106020c031c1e08150114 67
    0x2805800890b031641800710f08845400421400d001d9200d10792080400c1680e1112400791039034100080c849128032591420801b224241c032144000340c402c464405000d69902074a00042d10340c44001c0c06c0c01070744682d21150105060304503400882c02020020f1101083e583c48281c00341d4203006a0042210b075501150f1013440382c522800c898000c1290103000c6101450180e20b0380c9040c40201660a41f0345d07401041c0c1c45d01761201c05801d000c0c1010340088a40019800c65884640d141c28401d208205152500c0e403041c030300200e0b99849802040340c10700300030440350b940c3c40261a41e0011200c4c42c8540c001c100005500c18018002c4a0100c180b84038900e1665075800002d403018010180c216400203001d02010611f0404041500c010710f010b0303240d94a0ba5803501c00340c14500901604510115040101c040d2000c4d02d000401d51464000078280075180404004200d960088145070500c00300b800003070407100e4903000300840c3d0084080c3e07003010320503444050041d5216103000e00c0070715080a04010240e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 399485431 1250 399484181 399484187
    0xa0f1a030405060a1505060301240f0e2103030f0103050f01060f030b09010e070b1b01020a0212160b0a05062d0d08090a0603060501120603080708030c0c0a140d0c0b07 73
    0x1c00c141000c540001d18003500d40007c40d142e0381003600500d42c01c00c20481c125680f405203141380070342a0031030301d41003101c0000b10034002c213040e480380d645030700030507403c0b00c612100113210703142c41c0154034000100c0340c0700d00d040c0f00c000e85500001e10080e101c9003e480c4d04c0582e20782042c01200140c91240303003600c04580c55543c8519074481d00809541e800c1d581d9181c8201040c00030300100009041010304903440e036568400200e440001c3e82640714180c0c0c81007004002054010136210b00fa0011503d030340d62614101180e07031032102d90301d11000f400905020100312407480385030311080c059a0706071050401c404a804042459585c984650f1529010b1846a8000c42ca41a440c90344103030f21540c00f41d410884100301242078030240f070b0090004261030350014892568040006201d01c2c541d87c00921913945180c4030300a0318410702c5800b403e02c043c000300260106004604444003502548202c5442c88100e040001c0c10b440c40242c3c6022902802c3790201c80a031040940080340d40c0c210145042540b1400c03000c3d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 399486681 1250 399485431 399485441
    0x6090e0f090102190305151207060f1b030801090609020a0e30030903012009100e1008180304030b0f0405070e010611060105100c0308060f0a0f1a030405060a 69
    0x45040780d03400300550740030420300c0d5424046280aa80300401c99003444150104002889003040d40245840100c08285010005096040710321504160702880c0c01214201c0e4105040036891241160000c102010103501415640c103e500c1c0c984100070700e540380d0341750360280d105a00341139001444114a1040302e18113a402880b40180101e007500004811900d80c280070842900007424a410100350030116060178001c01d0702d1703a83e82200d03146103d01d0310102c41c65a8000c0ca414180215901c0b80010070141c05011041ca0303030f090060074940c40780604a8001d1207554100c80032880a01c100219505225000040d6802c3c5d940c4013411800c5940c80301848603c1c22002041641d0078840c28400041d105109107059029201d50f546002412840c80c00c01c5240440603809103015007003010145811f5580481c003494801d9040c60305a4051300ea4500081030000210009540f000e942c2100207064032030910303200b0480c0c001070491114610901c42c8a540380c041154098081d811140c009004151603603c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 399487931 1250 399486681 399486691
    0x51c0b0709080d020303010e0f13080a0302072109151706040f1b08070804110120010606051206030102162414010305061b0d0b0a09020c1606090e0f 65
    0x440088181e07101000c51030891044054801368100000600c0041410f072174903540004070714101c1c00d250401c08049a410301d081c200c0079051240224548100da8800d80441e00302079003010740e0f40e103085a152207038880e40d18008858000f0400070480028001c0e80086c8141c0c4040a94490284139100c140750125030800c014500c580c0182c1c1c559450440d0f01c1c1a11400007038004200b11410360300c00124000c0c2c4100e0001d0114001d2080000402c0005002c00302ca425031010f0078a854024101461070980504203a200c1c0c48100394280403010031015131142c0500b19882d0080c0d00d58007961904d030245401c034031903c00c1c86204000c14030b8001011543c002c016001d0b460b00101d0702c84602c4030156040e130440316488042c0c4e503244825801042030100400050340c0281200d1244040c4207a04211425684903102c030107140039480c2d1201130030642d00c20701c0d120000c0c580301405640c0c5401a000ca1511441c602410752401c1400c2d640215090b0705c190f01c0c805c00d82d030000b000c40c0d42c07d0312400d1090800d0003000300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 399489181 1250 399487931 399487937
    0x90316080408010608010507081e010513021e031605120105010e0a0e150a06020c090a0c0212070602040611070b07110d0f0501090201020c041a040c020f0601030308060a051c0b07 78
    0x1a040c0b42c248211801466820000581401d00520052807404044c041506805199101d5403609044804150458404560641140c0381d4424944064025214028000001045185a5a40440011481400c4204074a240c03404004415075a600402030885814030311000140095402480340580c9000010040c514003965103a480e020f1305801c4410079814110410090061308140003001d000d0402d0f8009010030400c3c807408501948001800303d1140c3e0f898145000c282402402204100c031400b900544d510043e0307041100107544184500700004951001e22441d0810200b100c07810350380c0c03406004e850100c40c0d485011003a01442c3c1d025078040c80c00861207001400c01f445151a15100380f00100e601545030001a040542031284a40602c0c18061001500340044485c0c89076010226000030b10129006000c0785022118003051090744100700c004020f05801c818100e10511040300d440d8005501c5405100c0c0840a404807041850001c2d1500c00002d46040c2c41c3e1035101300c2c0c0e85 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 399490431 1250 399489181 399489187
    0x10e070b16050f0d020d1106061908030a170601110717030d020703020d02060c210406140c180d08030f06010c02040c0c060b15042913050f01020609031608 68
    0x80c03105424091112800f040d0396002881d40c100326501881901213005e41c03410304440284411002d16254035005101c94480c0841550000002501c5030400300070b0304038501241d485800096001c0e04003c4421140901c0030b50f0b13040050340c0c82d03100701d10303180e1101242c50180058914110400b800c4080c1e58502110a005c18421002c0c0e540c19880680780c024001c0d4000c06110809032006800c20a006e0300c0c0540544041100583e480890f0060b61030f050050441d07960966564109440100290320140d198090341720140111440560302410384280c0040c024500c00c203040082200d604840c1074010000303201271000070031020501111540c0800d040c18190008021680014100c600c03540c000408a0411a101d01c10b01446100307a01000209607011319030350440950240d0280a54442c00380300d0490405801401d04980c94803440c0d503140020a035407554058076200c0010400b500030f00d03000364000c0440a50035803000030094018440c3c240a1440d0140c92089802c42d21101001540c5d110f03820 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 399491681 1250 399490431 399490433
    0x51201020702090720010b0f06090102030d020f07170a0c021201180501060f08120702040b0a0315050106030e0319141e041410020d05030a0902090403030b01030b03010e070b16 77
    0xf0071040307100d64115130f80c40408444480f101c0415484414000683e689490090007058950345c140302500c01e8100c99490316054401c004070700e548648244c220034180082100900c0601d094054440c0c0d40c0718860581030000070007108012806500e28180000b0345002c00000982803500c0900c000d642d26100201e406042210856400081e140080b2010f0303540760350401c500d1203a40e5040000e007011501600508900d0300c12203905002e002c5010b07108a41d03c040620048d641d0140903c01941c1c410b81a000440da10031580006003000d02c00c0001090810003450525000441211104200d07003800d00822601103c1c100c510101005021150360310030420035845000380d13612410f18042c1c0c005101d6a8900b0b021440c4540c02418a00501500407130024001c02500842c08000c0181d40e403600b952290385d01514a00039000c84074002c2d401100c00d005200600d035151304900c94125080e00e051000040c12402d00d1700303d0b00c0768030310440369030003040c0309105030001c0100800043d003440d0b041205000c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 399492931 1250 399491681 399491689
    0x1e0411041b0816050909070504080f0a0201030b06121f0b220e0402011d06040b0a020a0c1a070f11120a030906020303011508040303062403060816051201020702 70
    0x2246034941e403940500800344640c000d000d2540280707203c5480000048001e4054158050401e91070f1040c4200000104150b102e1030580d40207001c4d2008031502d030448401003a88440000800743c2c00a070800000c2c1c0f2070390822030110355001039250080c0c1e50540e1824100742c0c030222040400c518042070706100084840c131143c041c4c40301c0703006441c00041e40504e84003440c0355410f1700d600044814200300104000f5030f8209207000340c48090390010844107600c0b40e00094071071207182c10a200003440824490300d9650b0001d195008507201e2800381d05503d071122603400c06280ca5200c1c02e01c682c802008600c00140300031190102852051000d5000d0700801d40021f6003c1c140090700000d00e51081003550306050748013051000400b60740c0082c41c40c5504001300c800040d00ba540d258001d1284400106007018860391094000b004101c2016401c404400c0d90300401c02c650794041c200003410039001040000000c1050301c0c0300301d411038003c040d03589007200b44001e00c1e0000d451496555401e101c07410160711 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 399494181 1250 399492931 399492941
    0x5070809150a090f080c030309090a11040609140301063206040b070b0c030f01210f03030204090e0c100e0a08010903020a0b090607020703081c02040e0405151e041104 73
    0x2c0e0303500c51180fa9070500c0380580c08100a0741c800d182d260300100c0c2900c0c0f40d85021007150a20b14050712003a2171503403865400006043d80036140000844000b40004245038030055030350540c0c18158108039030400c0c40b0100341c260b0340f1900a01c0c80000140c01668091100710764032903605852814148542121080000e003076400076488400c8045002508404200c2001c0b8980e0744260440019819420b00740c16024040b4414002c0c0c0c142c00c8442200c40302c42c10783c500e44880c28254407080c07c01000c0031038980140603400a200e040d180505240d00040001000324584c0d40d07040d0043c04030038042c0b840741c13000c50761418a594510b800c901002c00200c0d0003d420300a144600340660000e04046200c0e181c6200c643e840109103011640020302031089040c2c0c04195181101e40200145c0d807a4004052010311240b0907005146140f44005000a02c0c00301440d0498421400b038400e4821900660300c0c4240c0f943c40443d60083c0c100c07440888207056440700c1d02081c0c0c000f4015024181c110383c034500413070102d035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 399495431 1250 399494181 399494197
    0x71b060315080d1710121209061d090c0f0a09090b0102030408150c0f040f061704200f030a0c1e1d0a0f0f0b0f040e0d1b0203010c0c03140301060507080915 68
    0x10071007440c50380b469800002c8c41c40180254030f0020864115000109a51035203092207502c1010844081452011030905440c21102c05c07180ca0380d616000064040c082a03482e01c00d004805081c108402c0c40b543c0040141c80c02c80b2000400f40007016070324030002d0402d60005210240e00d09003030000e0304400540d500500080c04403d02403120060810380f024110740d80e030002050b0f588214800300300005444c481500b00c520254024090051240c400048401922000380794040c49200104c2052250a501c01000c03129688803204100302e422040041d81d041c680640c0301c44243c11b2208420007240341111580c0004e8410700040c190741821088004d4070b2a681e420300e0341644500500e822860144c1c17403418450011a400c000303c0260308061603d6413911840b0348184411140d040250300c4c3c46035042c40c0b02c1035009008004044540070040d0544000a009400194000b44180c002d02d85401c1107034107995a0752500c0b414400d45984201440d8442c5a801c0d0b000381a5501c0c0881c0d400010014140c04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 399496681 1250 399495431 399495443
    0x8070e10080309100302030a0603080c0a02120c030d180e190b030c030607030b060c060109020301060f02010209092d0705090102190209010506071b060315080d171012 73
    0x15090412106210220341d03040300031141c01c00c0080c0e40d1690b0b1183c480011210301401c025803a40d503526500e40041c5090fa0014010450008000708803600200b0550b8540f4030844884913482c00080c90a56a00b55103d00b0350b4060f0300031860240d0850103507054420425101e846910f60304d4440c05c940319085030540c3c0c4e1036801e00e07019900f0b9292009902a80e04020300c10b07002003542d41e5052000a40d5100c0142c0144d0500d0f80c3c444030030f2141d444010403a4a400045800c4516a5940c1c220002c002c0d030007403181e4000245000200700702c461040c021074141d442c0080400056072a07040c144034403a42090b03040c108580c1018a508401d2031034030f003880e03c26651500d400b0303110220000003a0505480400b40b4031a984500c00220042e0f80e183c44603810340785d0554240d5251030091600c0680c0b98140580300d20300000006c2c0008600d541908429101c0c0e164240c1e00388129a501c09003569040b040312482c001ca1812a194680107040100d415888480120981440c542e0303981084107540c5490025249 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 399497931 1250 399496681 399496709
    0x60e0f010e10081b01030c020c01200109080f220806010608070c060906151707170106080304080c041109090402280b19020d09060c0c0306020301090207050705040618050a060807 78
    0x1303507070075204980e401c2d9401d0000d016102e071300d000020800c400101010380715031480350841e45201403d500098145602241c2c840c0d071680c2501d00b117503c030b40240b50440c02e41c120740c07905440d400c0c041c0600e000c1158005402403000d41d00b411001e840c800c0c8020414400c20440503070100100c0d06901442c3c2c105d500802c0c1c00100303000f0112409840c103989401940c0c2107400c3c034038950000440007038540b088400d00105403209100b903094640c054140ca510100b02403102180200d0103600c045201807170568102c8040142140080c2c00400d0f500a4040b4142c4c400301510000300541055040d0001c05840076561300340410240b0034401e10704015030041d03403418001080c0d852841e0359001c0d8403003841001d40005c08038651a4000100f8150303a0f4000c910800140341000c0d0100040e014086014643c0704500390b40706c1d84c503840c1210094100220598a0344625000082c403410310303218210a8400b880200520500d01d901044060b202c01b52105a421784d95102c0043c001d10240b02c08e00280c807080e022490 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 399499181 1250 399497931 399497983
    0x30703020d1a150a0c0b06030703050601060f081303090303050717030a09111212072d060c0822230309031b06120406200409060e0f010e1008 62
    0xa42c0101516034000c1ca1030100411141c158010031417800300d039030120704c0888035550600402d081c2191944000c1c014841da00000c500340d5006600748200070656514400180e840d60350003508410f01d40c60140c0490301490090002c0382c070480061240c5400752070540880708095481d020030f940100c460341c071140d543c1c001c00410060344000e504101c0d003088034002000c94212000c1615102c030307003d4103909181c0010341d42042240030101e40780390401c0c445804100c084100445001c1f42c1c0d4003032040301d01c18078084000704a2402010564010010364003904031503010f00c2002410003081c01010b5a00a000720000402a980043c81c62a2a0102c8000d1515504030300c06241c0351003103040d8402241f1100710f43d10101d42d212542540c000e24040ca4001040b511075003009001041d00941001c280207060700c11000c5000004000c204480d2590400c2240d660748440d107105520b0141c8000c081c60517244010031800071303c500c0c00c58002c10300c4154140019600d11455180c9028034002c966010b0800030155 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 399500431 1250 399499181 399499189
    0xa0f0308190e0303131518030e0904030806100507060509160b030103030509040203151801051002010e07140402090303031e010f05030c011206050d0302030c07080102040812030703020d1a 82
    0x5248000070906200c0141407807100c41d00d90000406000044130040054020f001c041c1c68291402c0b15004010411a0415007100214404840040e4049034041c0c00d0003500d27007007454103580708681598030a100b40d114081004140c40000541030f042080500405010a030f0740c1c032804d0b001e0703621200103090540400d1249000717900d0706d60054481440500041010035000b0040b01c15400c421240181d80b5920800c40e43c403924400039010b500728210030340103201c1022014805041c0c8804450410b129400001c00301e00b0307568110741c103441e1a040b0b10f800b008407070803070b0038062034500c40148054186007546001ca4910740048590000b094008052490102039805680d80580f08906c80301c8115030422002c00e668620384040b942c1040510503034140462440da00007406400c0040c92025421072034100256a41c010072074120040c0a420030010b5409414422101205c45440150020000d84000840560401400c607014140c00700308c0c03a81d01002c83d00c00d0280e101100001b81c0c00c0e001c00d120600c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 399501681 1250 399500431 399500461
    0x10090f050303070c030809010903120215160f05090619020604030f0e0f0918030a050702031b09060d080c061008011505010e04020a0e0d0633060f020a0f0308 69
    0x5180682c0040150b9004505a00c070460103680e045240344c1c1e1b80d0410140121040480e9601c0608088001e0006d0040503501040d100c0c0f42401c840f0b4114050b807140361a5a40702941da00924000c076145a0322080c0c4103000d50701524410354000d002a0904507050004000ca24400180500607081507042004050f0071000380c10340040140f825182940c900c6020500c090005100341c4d11500d003000c0003c440328015000380040c4018034043c4da0715580d90381c00140c459081100201d01c68002c0c400c0040340445498280c0c10714001c014030620580d02c0d400b00f0b01121103030240081d564072030100030090f17100104010050044c0b10b208401da99161611680034215951148904116100f000c0b0410943c0e90041180c506144100c034010307554071403040140e0f01c00440d45800740d0011803045150341400116488440002111900c00c1c400e4117000e0b014214011000c8402032180c02c451206004031441011a05130b4a04076004031081401d0a441d43c08c00001ca1040440000b201c41c0208211054003c0301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 399502931 1250 399501681 399501689
    0x6080d0c050309010e04021b010f230f040804030b010f030c0b1305270f0426070303090c08190309050123090d020a030503030a05011517060105040510090f 68
    0x2010054140d07a4940c1c80344155298241013090910f04410350b80d40e1a8110784c1d00a1040340500d6007901302156a50280507002c646480301707494002420886910b80f44403046248030302c0f0701c0041d9544c5d00011800c40d100043c10580705032006100200c0040c8000d4405400f030f10a42c2c031003101c01c03490f5207400207429185410840300107030107000c000c094007841841c90041e03840486040d0f0203103ca025001400b1805000590076040f801b42c00d000c0301550445181703000d28003443d045000d140044054600c9111036066001540c5801c10020b00482d2080e40315030341ca04c0c410007000074110741d02c580051902582110501031070103400c00550402d608070b41d0900042100f0700740b041c030b414025600410202c551500e440d181050000b1032031038540d5824820000d103070340240340c42c140340c1d141e05100d42d0780e80007201e03420b178200c3c0b41c41c0000c01e071500e00300382c2085580e00c545d64402d124a40c82084118192016140605000c8248804240c95880c00d100c410788800c00d50340c00f4003440c40d01c01342d601013001540c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 399504181 1250 399502931 399502937
    0x90e07030b0915121510050103020403050303010306090f0c0e0a0b09060f060711090c0a030c030504110409230321010803030c0f0f0d0204080d030510090b0d080c0106080d 75
    0x10700c03592152510204194811003580d00150364140c140d010030001250503141400500038040c401c000d10710b206000740d000703036190608500c40e55102c6c401502203100d14000540103034420710040000035a160085800c9501c90500e1090003005541c4820380c00205800100c0107410501c100045094036100b0324040c03e404540c0900103080c1540443c00c07000302c10300c440e80501000101907041c416008407003417202d400686015901c0ca00a07c0b401c40c1a040b50340508006420031030280b801c04c1c400d0140303d00494110030202045012403003040700621456a0481e0f2024413007400c03d001494000c12980fa207868038029640c0c4003500c50302401500e20014086c2d03a0000c1d0a4010b0008a00c00410303039500c0705240c018103949030803940042d06a40a600c0703d0703411950001a04621140454000d402141c02600842d41d0f01e001c0c0c20300c141d054460403103030030851403038140702000303604e00355080718140d50800b41104011a12980701c4c1e151590040e480b04a041e07460718420400035004004042c03500c1c050785 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 399505431 1250 399504181 399504191
    0x60509060606030705070305040f1e090e070b0721050c010e03040b180a0e0c07030f032003071b0b100806040b0f070e1201060e1513051503070303090e0703 68
    0x31000584600001d41301104103c008511042054021811580549110403d00c0c121076a904440c00412070051000300740c541000030f002131a04500c0c06980d8100002401600100d03040000301450350b00314640c159010004608008051200760f00d55161130011030b036696503a040c0030380078142035549800d038803c9251700412040001503064415038158425140821060000c0000000c1e0041140d030481c04201491070305010301903030404000e141003031194440384030b0112441b600343c04440c62503036403d846100212503a02d4005011005550191290401000c5500030b14007421848065000883d541c409600601007490600703400c2da401021a80c0082c101c0385495551902881d4000d040c0c241c04881410120b401c0600500e500c0c1e81103000070b0440380f000c2e000f40349514042c0c141403166070710a80403c0081001001789c11012031210318091300c1a040c91105d04444001020002c0212a6541c0b100c4500055540d052001b080298003954402044c00e08080e6105030402011b044a01032507e48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 399506681 1250 399505431 399505441
    0x1b050903030417010207080d09020a0e0606092101090303060906151b0f140a020a050108100b0f0403080a08010801060902130311030c04020a0309050f060906160e04110706050906 78
    0x440d400d803603c62020308203030490300d818203002e40581d60f40141000070225a183c11013015501a40300c4600803035035071020725504c0c1c1c60710441007416278140d0340140d0100316241c264200354425221201d8164a640201890b6000a600b11004a20101d00181d1205070411141e201d49c001c080c050580e00346036021024000e5005040511910724201842451a24200500104024190f203040c1c022410710706c04c4150501090b220041c4070401c0f03100741440e0b9804681548507800c0140300309200c1c1c0710090018200980700441d604404045001c3c400c0811004c0005407800d400307060080202d03100c000b01c0c0e504220120382924a1078104412052060000300c2c00d262a036502c950032290010190042c420049010a04150321f4034900c43e04240000755106115916a20030301c4105e02a400b030b581c09070501010b40351181019100740d01c1542c0014045148a082c05c1c101c0c41e940704150524403000400c900c049000c0c1c9650140b00002c03c0e202050490502003a8040c40d035020030308101808840c549 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 399507931 1250 399506681 399506683
    0x60510030c1a0313030c05030a0503090d0206090d0e030703080a020303040c080609120f0d1b0201140903032707031a090d0c060b13020c0109120f02070b0a120c031b050903 75
    0x5004400d8402c04d181d044080c140158840c0c3c550300c0d04003055964072888420060071541c01540c1030002031144c8882e4480d03040c404214280210035070f2000e050120b40c9550120b03a4540b0454034190306014400340040000c0000c2c2c02041c050003190013440e141d14013814084880d61083c0d10900309a00501c1c01c102c0042c8bc04910907020210480f04181c4410045000503168000d00c2d8100d01000e1506030220178100c2588909210401e03a903009001138205490b144000038410344101849a02c240082040b52a0f200704500d0560702018140722400080c4085600c0d09210f84e000b59400c000c020f410b502c0a03000d00174045d52100f04c00000701520716449000401212102c08060000c0c0d58800c03e00740c0c0c03a0f944d00044800d81046580c103540700c6070b101c0e464034006c0072107500032200b052a50324000d55281c01903494084586194003d0208540380561964540c0d0100103a44100705d0700b4403c0c25801d150300d21865050804c25540040c4180b0881901e44044810b80510000d101c018010121350b0b5074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 399509181 1250 399507931 399507937
    0x1020304060c110f0c0d141e070f050f0f01050903031c05060a0b0a210c020114070e06041202040f02070f14010e030409110409060602150604060302010f1b060510030c1a 74
    0x7105640d29400940745040c4059200401c182400c81f5024001507501003024040d0042c00144500064841c6244c0c1e412126000091700c1c41100c0d00040a40424800c1d031510152100310380406041840c50003110034002410360b031201d00700c01546001e21600da501e6606074800c0540c422803d441d510310b03079400c0c0f0801380220b01990342e900c4100144002c000403030b0f5602e1502e070410089184801d00c00c02e102a0b20203070290080301e41c1609081e100302c0c005400b40b4410070a401900901420140c40d090901c0e81ca900d10071000341041c0d82180c1ca9650720500140f261004001140c056203468500f03c07058034000305140207000300d00e26642e062840851121902000b21401c44110200004039480c10f1881d1503051f0003150301c03038642a03191450000c1c10700c1e0041001b0101104000364907440d030340c64008000860380307a400084d00084062600b8001107018000c5464049004907401c010b59840d95100d0042d0f4a040b10070041b140d0441c8410020069070355010b07070160078501008036914030000030051082c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 399510431 1250 399509181 399509203
    0x50622050319060c02010b060d0204081006121205070b0f090d030e07120311011a091008062410120b0d05060c030601090801020d0c0e030f1b0a050301020304060c110f 73
    0x3956a4146004d540c000d610030404100c01405003500c0d000d80c44402e00080d0054070982d4100d004443c0c400200014601c240000e480c5086503900342000561210388504483c07000b40d800f0b0102c02c0108001286845181a00c540d01e0341c1810b198620301a2103550402c062000541c0c140340c01e1220803500300101080c103100343d4011440c0d02c08041640e05044503400108040c80405520b032407025506690340781903032052080c050303030140300684540900d030300702c5070700c2d44aa40c207030307802c41d0b4003080b01040c514007240d6010800305245210b0032682000104400000c644840206a907042100041034540c020744014800448070804032038895181c568075200010540703800c004001001030016806000c012002d030030b101d03000b1922800480c075440020700c115580c40c1c2c08104041410b01492400003140000c400b00940940400a2080711403048002d0380c80802d580116410000326141d2005d1000c0c512940c0036090101d043c4104013405448141d07640c82d00d9805070800c0822408040d070001e4148180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 399511681 1250 399510431 399510443
    0x5040c091802090907050306070c0807060507050f0a08010501021006081207031106010305210301060e040b01050c01020c061806400b0403030c0806031e0304050622050319 75
    0x5000e401c070100501c800001e600203100c100740181581d0008440083d1007082e411174083d51105281030700c498100940080010404001c4400000d00c80e0f00081c2d0881d619040c07250a120801d01540d805800c00291540050000c4004201c6907a041100304010000e1007170822003141070200c440c0c4c9541003455005040c100000701c120400d4811070740b5610380ba00c600c0968210b540c43c0d103095a12004507180b4a004031780c0301d02c000d203180011542181d048503060b4840e0403e90700c0400c217010280c40340016143c103000c030500041080000c01c0c002480003d02000140103035151010400c5100c0d960b10201400e40c1c3e00090410213100111241409802e064511003000401151100d110804001d42c441c6a24100c2c1c1044408001d003041640b4010380c403d444c284918501a0400c60380e0042c22119158142c0c00b100d240b11246120a021200001c184410340749015101c101003405e9030f019000082280281030b9150081d40302c2d00a082c0c020301403c41c080c103c200c00319000b20307030214103400001c0d01c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 399512931 1250 399511681 399511691
    0x609080c09090c040e07030b061827120a020601090225060e070308092106130203031b03090310020a021f0b0907031a010201090b011502190501020702100305040c09 72
    0xc400b504106000e51060010428003811008004107034840c8400c5c8411103010405c500410800e00d0420041c0d80744144410842200f83c1d07554200d501155204080e1102218441020001c0c403d0300741710054a010050070000d0351010009030082c6070240c140d01c884caa02d031050011808881c00e1f6259010030b03034049940030f050381a003801c20000505040b226103880788074840c000070070003540401800c03c1580403590550004c1504d0004800300350110040383d000d8010a0000b698a00200d00c0c03111150b0020b0200c90400301ca0443d0501201c410fa0004605c60748080baa6440c203203401c000703050341c54084940950411008030006507550301c085a5080c590a594003400f20b407000e4913480034032881002003e0003081e080100340900240550b4043c00c0145910020059030b40d401401000007080d84405954030381c0e072800d006110003440b583c20100460040d0482a0f0300c18051403d0a03800c0f078054030005949020300e01c1000001d20003091000241401c010402021610307110320384085032448480412 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 399514181 1250 399512931 399512941
    0x903020310110c150703060509040f1203021308070f081c080601030209060a0810050409080d020f070b280605030d0309050c030a03090510020c100f09180c0305010609080c09 76
    0x240c900400010b80002e22891345201d580210841245000382d041c0c3d20200f10858945d400e00c5104003080710050410172801100c0c20000b950346004015043d41890014200500b0050b1742480e080241e000048660115005000c1c03448980c0000c4018450305008103240e00190195040003840d520a110601040900050050740250100e4029070b2000380301c595211244440905a01e40c240c9108a4034540c10b4004149420f2501c11101c8603508048554100204556444003a510103040e1100c000810f020744d800080d0031601c140d001c1c03600c1c1c10320441445c0c031644e4000c070340340d40c0c000b8100c917002d0400c00100140c0d200850754011880a070310780402e09031010b040c0189800882c00102d0b8061007420f10752020305030b000e490071040d0b0300c0450715540c0d03003522400301701d0742c41d41074000c410340c00602d91b03d5070880c81d4007030914640b040180f07090a05078a0341d1800394821602d60030807001212a03c5851910100f07a2520800d4050915400e01e1009541400348465640705001e5500340104235801c0410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 399515431 1250 399514181 399514211
    0xd02122203030b031501061116081b06070605010b0c06070c0f32010f110406020303070507051f020304060b010906140f0c010e010606020d08190207110d0c06020d0903020310 76
    0x1c007266204100c040195030354680080000c151072201280a01270503140c1c0107040f140015a07011507080340028007818041240121a20007e8514103900540c100300900c006406801118000c14440b40f0b0382e912011510304040c10400c004101000b0000b40101400008111166072810241c00141d07100c4241e00038000a421080380e40345004007004907000c0c0c002d0a100541200001d107401c0e400138414942440d0455085000310b000d40c1c03000d6002440080c04041c4100094218103004000701c0d6101c000c0c0c0c103907608480e4803c6170781e0400c440c0c001042009001190140300300c94003003841d2905c222484d20600600b049115030750400390b600006008500301c02e040098070300801c2002c0c02008100300704100c0314000c14641c4241c0b0094010102011085802104602d1141140500144001c1c05140c2001d0003907210f54001c8519a01d1440c3d06c40203915801485104036129000d0003404030308000000e4507041094558408000b10340c038040c401600d000c80c50a0201d440c42e60f02280080b6012844 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 399516681 1250 399515431 399515443
    0xa1407020904060c021510050420070b180a0f15140108030706060b04060903030c141005060910081e15040602030708070302030103051b0a0b0d02122203030b03 70
    0x6507004030064140414010103500c0b94044e25400d800b1100c0c03111107003041140511302182d0300700c00000403610801c8207003015044448030380c041407810319051500c040c1202d440d800030041a0748010010080101c040412202003640b00c0c01e41c4020032645000350b681c0c0007100041c032001070004220030324107402c805180d0460944200c6044000c2d2003507031244002c5070380780c00c000410345400c0d0500b81300040400c0f0450481d007e440c0b1642c5c80b010350300e0854405942c444000001100d42403041801080f01c064184002c50107120076000215190030324008016031480302400c502d405402c5584204181000081d014007807900000400020700e0303130320151a007031a0040300594481003181d000c01040008550065100b991951503840c080e4603001d404600328082400006c18030351050305440107250b0000a0041488030003005182255120000403040b50020700d891201c058011580082d40c2030a42c3c2d050303a0213100003007030707569500c1220000d105a1040768005810301d45d48804000c4261024404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 399517931 1250 399516681 399516683
    0x8061303030b0a1403010b0103061217120114010906050309030406260c250201052a030a03020409060e04080f070c0305030711030d0206090601180e070305062403030a1407 75
    0x110038401e40e0b5413440009540915604030f4400c0d441c16103001019070113441020182c8602c2c1131140c0b4264101d0717a411944200c0f2000058000c0030a1150320015480000e416000c1d00d5031101128003d00140005012810190042010310006100b000680d02000080c3c40c00c548103403078159440d0210b00040c070305000d60102e0baa50900e10600401c407061322030300010302c210444840794070740b498110b400d503128049803804000e0006000b00701c5002065440203000d11098000280c4488041d03515000c00d1840d8050a042004250081001c218895041c46406e0003460064603080a510302680c42140902c546410319681160200310f44040c8a00b8010b11000345502000b140e50b24034a03824140c00100780c0790b1001d403013440b80e110210543c40c0b0100e4000d001d1500d903002094a81d08003105500102d07503103690500340c0355035400c0b0001d000e0010054a001140100c0280925043c001d07681e01e0940140a03400b00d031180c1c501e0320320b0704a0b10b0000032141c2860540c540f00007100025601216184503000c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 399519181 1250 399517931 399517939
    0x606064104050a08160902070305090f0112060f060f0809061303020a0602160b011212031808030414010c11031c0609021c061203120506150423040608061303030b 71
    0x100204c1c6440d40020034050346143c41106415195840c01400168840c0c55402000151700303001000460401d5006030104820504181801080d200d03020740407504142d22110450304071580800032a50004c1a9840e071038440e16203242c01d0f01d448002603995404c040c00102c90305480701f403160280f51017800078641403170b88940700b99501c2480c12a1180c101c06102e00a80b240a01c00740000b81f524020302005c8446980b0075480502d100303101e0000e9004082034402030051620b0316041a0025110400440c4503521500300c8003282080d0111042c21140c1804000040c011211000640300b40b0000540d0f030802d545800000307440c08042e01110150030164020f010703142c000300d02c4003403590402a500240b1070510104021319691012914014406049d020300411180b69110141410030340220343c2c4810040d000c980345402c400c620b82087d42c05a40728442c4109108806800340000c40242c1014980c1220306001c1c4909040e80c050320b4901c0944a030580000184c4800101802034200c2561004018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 399520431 1250 399519181 399519199
    0xa1b0c170703110105181e211005010602100504060b060408030703170114090a0902030a050706030e070302060a050901031e0b0103051e04030c150603060606410405 72
    0xd880c0d07910a4940811505002c25150502055102d00182c8054201843d410300340004000c06200c6003107448003262100d41c80e4104101d10a40700c5400a10741054041010039191800510050a01c1c103404d81d02007a2070b090100400c050f5500190043d644031451500103400d403501d1600f070005200c0e600c6c0080e0058004140003a030424080003409500c5c0c00307a22284c0c450544121043d480000034080c040e8460300d03624039021103081100c4816408901080002102000d03034001a250480141e01151664007010b070600c00b080e032500800c01c204600308010300843e815680051014050b1b13080030400c00002051303e00301684a50001b0400ca10700b09503114141070014250005048100b101c240031a080c000403a0f500317602c001791599103907540d2984c1543c0362207a03601150502c405c0380041c0e54010a0151a449040035840b03058000c511412001801915003100a451b1070428030301e100c041e0062804d047c10280310a610714644c035408181c18028040e158000c24180d0180f40c000503000a051 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 399521681 1250 399520431 399520469
    0x280f0507090501120b09130c080613051005010302030a020d051e030a030c02060907090213030804090c030c02010b09010e1b0705010b010e1504140406181d01020a1b0c 73
    0x9030650003525001c1c0d82d48000c2d4140d07240420155a04d941120b44c200c501b02000902070807061051210252140307124450039607403954000c0c941801980c01c0b0381c2450801c81c08004100c005c02c4246400540000140419031554001075250b402c0c41e034011340034036652200303071302084014044c0c81809440507010155032820358401c1583c0b500142a0303075001c01e14000200880e903000107946446880ca4000420001e0b041040301c1d0041e403c0300b1785400380d05180901c00300010782c150001e4005490f0140001a0300403404000a085c1c400d10380302c0e24191791410b019201c90f0f844500000d07042d00c1110b0791407030b00341e203408415041c0114031643e034100207280424184104607046d0024070b43c01e40241d841e03411070503d82e02008044400202e801c4c0c034418081104002c0341c0019420f2041101d0b009000049860341ca280e980c40301001e42c00303900d5040f5a100444110a0702c128492150b5110302c1008501b0000d04020290010030700c04203001000381002c4c1f80008000a03d0813a4016041402105d842c012030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 399522931 1250 399521681 399521687
    0x5090910050418021e092a070f110a140909120a0513080d020604060b01030b0409060213060e13050406090503070c210809100207050307140103050c03280f0507 70
    0x2001404a11400c0070740041c01485d030b81d9806801c20300b800205000d0890301c600c451510810a2003140a070a1601c10440c40e995500030750182c007130306004901c28944035181b4503212b4020300c00080c0300c2e441884c04ca07809000b508040d407070200c0a03600688001e05540c035188120362a00c0e00c1c17100010214400021010f02050b440f00c041d160306110040480b24190b00c0758802030f1180810f042003401644401d001030040b0f07a4079000011580e0040c107001034240340c11000300d0180c40e508603083d1907260300080c01d06c06400c6408540401048545003800344002c3d110001039540b1003608159026540ba5000f00d010300c401c9505c540b200f00da0183c1160350312035003450020f401c040c1d0b07445205c040c1c0040b500c0080515500f080540c56042c0d102d08480c1c98440e0b442c0400444000304c1031400c0851003800d02c0030900d40c0f03042121030301800c3d1800c08186200746200004040d00c000500c20215175101f0b200f481120110b540b0710041c2d04c5600055132a0b10302096244800405010100701000c90400e014807100d44d030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 399524181 1250 399522931 399522971
    0xb1b0a0606090e16063603061d0c06040b0703020309091303110303090304030303050411041d0f0f0d030504080f0f12130f1202030c010e0606030f0d050909100504 71
    0x248040a41d64618a40d4004c0d0260108034410680419103014036802c4000200c209014989401d071480755003034440281c0b02c0d00c0e81501e84c10842d5503658500f03041c80a5005610a0b0543c0700084000340710801020010603058080e500c500c00781114085440320800d0300900c01d8400010001c8d0050f02035180c0030444105c18104a81c094000c2039452000380310603072004c41160701c01e5850b240110b181a10799a4110001e0500034001c1d110303c891080b2007001540ca40c020340c1d1304042660032086820000300c0005040071440c94104407903034081001882281000f1550506424842c140081c5640e194100114184910607271070940c4040090410a007050203009000301c40201540304141d60780d90407256940c81c030303800d4002d13060200c071203075040006032070b0000c46140300194130649060103141c8140f1800e4845c1d540031450650001c500700b04540c2010040195030840040c000d1841907241030b0081d16921810902c030b4050b841c490f0000e00004486070074240280310141c02001000ba4014031680380c40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 399525431 1250 399524181 399524201
    0xe0d06140610050403020f1201050406090212030c120307270f090b09040f03140705060624041e0302100507113f1e06070201060b1b0a060609 62
    0x4141440420180d09040c207640c2503442e03641e2550340c54a825a002c001e810312203030b001340e5401183d0541c080d240c100e0038003846010300d10441003c119000280b040186100c0100b0b00a84c0c039900034001001032580020700711020400841c059540d03038549250071200c3e03000e803201310328450f01e2200d260710a182408100c201120550341c01402c00700d45822000094618556401e03900c10f82e03030f0740400d01080b258060450003900c02c0c02c000c4400a070324102c1c44104d802c018015540d80c1c0004007081100c0c20700e001801400c540440381c002000c0c0e400c8085801d103018501800148400258201c24015950003001002c0e6400a0000c03034020004500146141c0c40034004569036a214460804282000744240d182607110f080c1150306d00c14031002000302120000c2c181c0b074841014070392583d0501130601103500c008601e0001b41140000c01c3d040589071000c007420b000c0440e13161007030400c021001c4c0c1059030101c2440f20b000602d003600c02c800491410b00950303009407a5034901400003603400c10590003141c080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 399526681 1250 399525431 399525461
    0x1060201050c1317150a020a02100213030b090a0204050408091c030203091003060b0708041d040f08030712060602010614010512070c0c0b030a0c030f1b08070e0d06 72
    0x1d59181c0c40c40340000d0061110341d10075070050140902c4040c4100060328042411407088903d032031641d241e4400c40e000300713480541c04641d0000d83d09507400c1c0e0502c022003054145400941c0341440c10203507a0a40d1580c1e10015001900000c0803400c3d40405009030309407550000c0c018002401e00e401c00034401d600c4411058413455030003020050407060560004000ca1f015005541850502c0c014000745400c140b05107010540c4e02c203004140c202c0d42030003078a20030b8000c1e0701c09611242405c4038a00407030b0700766022041050070541040300090402e10281c807899800320100e504d9440341c0005071041d6109501c2a48550305140004c50455170550048045900e07004401d821406000e00555603841810b100074000c1c01c034200003960240c01010002203c0c1e00c45e09422140e03d41e112810309681e002651640c00b80b035102c240482c135481d41401000600011001c041091800e07141c7c0300d51842203089504003d01c09240c002076001c50094092425500c0058001c00c0b003001d141c43c10100501380c4c4100302000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 399527931 1250 399526681 399526691
    0x705030a0c0e0d231905010b010512011a0705030a0c0201020606042702030a08070303020a0801050a0602030a12200409060f05030d050c0c180603010e0105160e030a0507080601060201 80
    0x4414800c030004140c0400c05001000f6001c1c1c1510b40070303410641840468440ba90203481d41089400401c952081c49005030103002d2000241d1901d5805c0d10031400c0b400d4104501401400d600c0300766940c0881c11101c0c4001c0088070032040c00c4201e0114001c01c2c00182082c00041017a6035801d81080080f00882d10036400c1c2c61040d644c440402c000c5800ba44440c3c14904610400a0048480300e642ca29555000178101e9400d00d105039621701e01e82c1e04c100d1003140002d4000c80c01160b050340200c442805020101d503072403051030030604025900e0241500c2c2100300110022103c410041ca580108010310001d012a00c00c20034021002805520600c184000d140c030340440041d207000f26050800903600001d01030020803480d010112200c3d084a454044180140c011030041030f40c41d240211210342101400c2d28841c40d01c0010182100d08041c11100f0703c1c0d060004004e107040d40d0401030b410001303e90401411030101c0401203841c100c502440200244a06000400c820400090031412110150300a1007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 399529181 1250 399527931 399527951
    0x2070c0e0c03090f0d090e040c150f02010f02041a031009020d090201020f0c1507061b0804061401030b0c070501090b0a02030402100e010807030f1418010b0402040f03021012050705030a 81
    0x1d60b802d0100842c000096510005004401f42c000000350014040c41200003880e0301c031190f900c0e5948002122802044c4e40d030031107a40c101e4086c01001c6203510104811402c1c203280034010404100304195030b581c030600020010b104002c0090f2040c005d0480d0442c119220707035512075950014409900140d016204076001c0303070301042000a1031110710001504003080c8a01140341e003000e40d00044011544980c650794041d00184003001440303903600055a4858190a250511004950040340840d082171000700043c404504428007c98004840f8a15103039280814100742d0f0043c0040d80c00204600545424808189070540141d80907500071140d6815494a0035800d8078104e44050010f40420f894500084001e0700980c4540800850b1441c0070070401c1c401515600c0801040f54101410329016a2150141e0400d1090300101c100540d42185403038246215510b003006c55101c000c0c810102d401841440702e00c02e01164034160883c100a02980c108010041c080b508202c55040015240c185d810f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 399530431 1250 399529181 399529183
    0x181606080105031614100c051006030b07031b08062814090712050408070f030206010e071d15071b1805061c05070b0d02131a0a0302070c0e0c03090f 65
    0x79049405c1103c001c4060b101c01800c0c4202ca082d8040b1800a0060721406040401c406001e00c5031805c1c0d140c00300003002402c503c0d20b0b41d84d4210150540d42018600300b0409400e8080031281c0410300c03d1400c0c110b54a6940e01c0003c0c42105503002001e1440d0120b03c003c0800915440d0044162642c03c10b000c16024000c000f07022038440121801000243e0034840e00c1e00d15441a4081d0340c00c14000c0c503805291400c6910740b0780d040d0508100c00c50041e8415130040165a99a4201540100303c91820600030b203840c0036020142c000341c10b0b00500c5070310810b43d80404100700004885081d03900140c0c8002c0440d82484a0b040c900c41e81c820800300000c034410082d0f483d4014825244603000007445005419a40800e141c00c074011000d00700c0302c901c0345490210301012154050119619862005a503406c00c0c0f48a402c95146994444541451074400b14140c41406800740c0d0012000c1d8038005848024906007120840042d90150004040322410b10850708c0c400b500440c07107030084004441c1921034401d811 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 399531681 1250 399530431 399530473
    0x1060c02030d0309060605120d0e0306011a13090e0a05010c050a0914040e030412110405070c15060f030c05040513020a0b2b02190203030105030618160608010503 71
    0x354541c2040c2c0c402c0c1c011a0083c0e01114200303009810000301d407a00c035004242000c0c0341010741c0081d540300210011070345a001f098450001f40540190100b940341610b10b481355a0341c24071403c0c1024010903808041d03400a10140010001341009200c6a41100900ca8480c40010b40581d0746509000b11404114050030403620b205200d80d5030041498900724a060714003134408000c541c0242c0320100f007244d211040002c2c0019041c445820806c1d0205864a00c2d40031103094600c5000310304120401040f640c1010235200d0840e0002120f00f407142d03510804100418450b00050390301070b804400417051040b130000b1282910f00c00c2d0b808000d66202c04841203203140061400030b600514940051011a09500240284440d0b056403044441c201400c407a8202d01d070550310042d01903011030b1840004290306004030f00b9407214000b40d40345506201c0070a40b034a40c01421030265418151980d03034040c4080003403c050030031340505042a00e03140c5400911640c4207100781ca103c0c0c800c5018040240f80c9030380c0c2d9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 399532931 1250 399531681 399531683
    0x3010303050a030b03160e01060908151303020a12051903290604050603010e040507050108040b06040218030307052506020c1c080408061b092103090a06110601060c 72
    0x40074101640210110042c010b0024905c3d014011005c595030390042210008004e040c04050080c030560401c50011700035000c40d400070030103502c03641002050b00652409141c102c1210101e0400da031009080580c544894840c00400d00314800c0032124206038808081d00604002e0680c0101308c90740d000b012030a6900c0d002144100480c450207403150005000c011011100014100c282090b54610001e451608241d2204400340000301c10401005011300c00c030b402621017420b0440c0c40d818140c9504102c1040280641d0140d640040c5580340d04c0d12401d80030007041801800c4a40c6d03008103261003a1600320311040c01230014030f5503002100c1d1100245082d01a109035a0090400060100030002400c4000b504035140306a13400d00b22000c00d0524004001608003032000f06102d007004a00304229606500f40c8400006043c0f12401055990088a0030000f0b00c803451016241e211701c01490541c4203a12070250b0118800c90002030307254101402209280c1d55606555183e80d0302d030420b45101c0ca034000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 399534181 1250 399532931 399532937
    0x120102030f060901150c03140f09130203042a0f090e0715020a020103020f09040606050703020f0c01140c101503021e010c030513080a06091e0b060402070206070602040905041703010303 81
    0x1490303002c5501c100502c81b007240c02403030241101c2500381078100080e0b002c04040b4154030750000c2e4075011410000c2d0403224840d900305c0308502c0d52a203610b0300400703440302c04061040841034200e01c110b40a802030061000e400000d03808400b482c0d0300c401010003080702244d290403501038001c00013001900c006c0d20b9020307030545801034510380c00c2d1540118005e522001c10040700f0603052117210b2054507141324a0b0080c1c00c95440c0c03a60b455005040203450b003e940202d02c0328540c00307010110000d03644a4034108203100c3d202c885686803901c01c5030b56424041d030b60804220f02850560452540000420366408480c029581c0b4988400007600004154501c81c02c09408104003400e00d8002a00c46c0000b0901c503d450a00b0b14010380e125111141481c500300b03404c0e035072280c0312480c803800e01002041c01e01c2c00500590054a619449941e8085050070007441284100c1d80440e0031820340d2200b100320351003190320103c119070340c075256411f0100410b81924190342c40f00a050403036510a0045007103038107803074140e2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 399535431 1250 399534181 399534209
    0xb0316120c081501020703141608030c07170c0d03030f0e0102090f0f15040f0e07080907030803090304030f0b15010203160f02010905030a150f1503150b120102030f060901 75
    0x1200102081010003c190452040c400b00001040c400303555041024a6140030381482d00c03d036505400c400c00c6e543c00c0211940c000b00094502d003040080c1550498000c040480125034851902d10f00b0101219012500204041d02003003c2603855403007603812003400d07001004000a1401c1d034908078005e14502d660022501c026804c1280303841048004201801803d580d015070303600700002e0290700079511a103030000075044240040800d5209280d80040780e0b03d4180e0f02481c1518600341d840e40c0520014001e4140040414000b00041c82214091030704110700d0b804030140d500c0c00d21040d1004840c0c0780e40950341d40240b04032541c800b100f20345524035414803014180c1d4a540302c10f0f600ea20049012810b010400c2c90000d00307030710300307000031003242d40516102d071080c0c01d51350342c60800d40d50f4039000703aa0168540884461101245c8034a941030b2500038040d46880c80b881181040100081401c05a2201825403240d101e0403054000f50700c11301c00c040070440c080c1c66040611003041428050030701164040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 399536681 1250 399535431 399535441
    0x5090d260a050a06080a060e01050703141609090c17070309020135040602120c090307031e020a083a030203041a130506010b031e070302040b0316120c08 67
    0x19411850f044500c1c4200003900c80d980ba49424603040b0020b41c101c0d60039840361400d03d0002002c1c032409078401d0031418140165414003c0c138800805000740400c1104485822130b04619200e07180800c003400d151407003002904c005100242c09a00350194031054030621400041c0110301c6406000c841c90380c1a141c1c08075150115298510508a0a001c1c030b0040c2454010181c0c4000c0411030540980c0c010900107956100d60004d814040c01d0040100407810030422400131f00303413030010ba03507001c40b034000b0113012011a11074161000354054010103507101042d54004584041e01103000121000c00400c40900340c07100c00d0900c412006009012800e0000c42034174010110f0207600255270180c803400605258004040e0501c00c0d001d0240c030309650503603d0314407190400070200005409400c110001a045142c90f10010100c07018001031580002c9214001c500340d00d02940580c1d01402c5130340b80b095264584080340b180d1b00414041080700150400011079081b880500c00c80044e500b0300d9030755049607641c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 399537931 1250 399536681 399536701
    0x10e1207020d05390901081b041104030812090c100804050c04090b0910090507050111151510050702090a021c06030b0a0e030a09141305090d26 63
    0xb800350281c03510701400350004000000c0c40c4450f0001620f1803244604400f003101350400d04884100254050402c0e0f600500c11014000f554000440d805e9009000d1900004041405803200c2d080380f00c041100410701004100b10070018001d05c0e01807001060680d03407070200710b6035122402001c4542145602000c529868441c1c0e5010350310034011411140005c42c440c001c81c003110305015041e18104800b0040c0714040758140030307560f595911604248004d208035181c1a0301d624180c070987d4103002060660b01451041401140c032061030840804035a890041d04c090f010114030b81c00b9510400c101d050001490b402a03081d11092a00030700407a07410b03550b000c14a0000e40c0711008201400c1002012280162207602860014500c9800c1c101c80a040503031000055604501e0340c14026003051142296082d400000c2208a9840d4000b4200c6510620042511001050085081c0c54100700070441c0324180050010708001c110340d2007054069054401d00300000168000800c2c41301c80c24086640920f0b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 399539181 1250 399537931 399537949
    0x2071203051809040606030b092a0a0b0a0c110909060414030c01110705010c051e0a030920130509070608090c03030a09240804020103050a0905060c04030203010e120702 74
    0x208640e100800b07140070009020030000315800c8a9981d01e5406c148200541c0c03400e480e4010446034001c0a1041e1081074601c0e00c59030301da180c29141c2c001c0c008000d0700ca90f034268030303003008180314011507075100c0e1900340040c08907032011415140401040c44845442c20a410041d11a07010074015100589899030340b00c82242c1c5025030f00459110601401d8000c603001c5c800d092961600a031030a580c0e070001d01c0d0541c2540e081c58036850074064140010408069641d580c101003207003e548041e42e0300c01e6041d0540003060384180c0940400e0700d1600c1c03240d04640e01c8042d60724840d4111201c000f98120040c0350f000342d64088400301c0090704910010080b0078000c3d01096000400d080564260b03d000f04007107880c40d00603252402c009120f0b55010080d4110f00483e42c00510302c1c5066513134005001c2c8402600d607010103400281011b5980307000030b0f03043c0c50546c00007141d01d500c0400e407412428606410010341d0070900042c2d11a510b80701c1200581da00020748455181c03c005800c41c1132203115020030644c22 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 399540431 1250 399539181 399539197
    0x607020603100b0a0f08010f03020f010c15050a06180b0f121009050304050108070302041d070c0f05010b01021501050a031220070f0801051e1b1204020f010207120305 73
    0xe12028010843c42d5240c00034107001d00e4203940d10010091500001803c1c0074041c2e001d84c2134204100b505001603240c02e40b070300151a00a0806044000103440c0098480312400011030369149031005005007825190031080403142c2040080442440382c03070000003201e00b40c003000d540c812a030140004460a0007410701605c68011000d6441d09884d4034005025500400400c403416000020140b00940e00400200c1d007140c2586011070410703040c025002c003510016500b46042120801c0007034030b80c51280d52030010042d884003802411000528002d80600349105002d07025024580d03e4402c410404410b0320f04842c4002d0412150301e02d1a140c90058001d90840c04041003540d104103200c503003201480d403041c8030b4000010042145050070042000303450f500480c80990401c000c0c0411040c100354001141200c080c20b00b4030603203490310102d14442480514940e49030001c20010f9000c1e03007041e030952103a802503545810f4145840700498a8103e1406500d40242c80b03958610b0100384200081c020366 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 399541681 1250 399540431 399540451
    0x90b041d0a0203071709012c0601080f0304060e0a0816060207050d02150c0114010602060f0a0203151e0d030c0c0e040b040303020c0c0a121203060602031e07020405010b030a1a0607020603 82
    0x2c08c0e45509240c51880e01d182c4044c0f51140c590380440f448040001c03600400114001e400701c0924546840c2e16171086100311800c2114500c0304414a039030f6040404020034180d022102c801c008059160401800c6d0b10400300580140100095941442150403804684c010710022a2603040301c211240c6400119207200203650340c041203075840d500d100c80d540c060103058008028925005c0c0d001200e99030300800751f840d064018401e11000c0413001210460703030142121402c0c0584007a00c1d503002544803034110030307601480310045c040a05400081504840340a103000000e1107895030300e81502d40c402520300401780340c0302d4000100031900c40e5001e02190908401540d100100d1480000d80340c0c41150812112881740b42d6060040000d034040141504030941030901c00c09260a0006c3d482e400384140d1452059111800038a18645e408103c0e0700150f4001d00c01c2056584415003103a85400485500f4019407801041000d0202c0b614250300c10300301c0007082d007468040d0f16400d10a194101405500c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 399542931 1250 399541681 399541691
    0x306010f05163f080a230a0213080d0516060605040f020a1101050609070f0c05030307030c020d1d0f06190e010e0a0806010b0a090b041d0a020307170901 67
    0x79191005a540411040c41454590364549402100c2c1c200b0a1101c040c4140a50f001c041546030440942c903030100600b800041c65150140364848407504e40085c10010590000800400140940c0503064110351000700080181d21900b40710f581c1d40e0702608143c0801c038248121200c10f6040c8d010309000500c20400401c00c00d60790700108042c0d61070403032100f60158010400141641d4071000103401400301100a1009040040210f0340142c0080e10940800c8440c6600d00c04590140c00183ca40030790100c2200e035240f90400380100148969a0300c54018054000c800305001e11940861010311456070069400100c00c0081102c583d59071601650054070501545408a99805c5126061491030319590014007525000404011041d04030b10311800c1e4041d0300f8051801c00080c83c0c1e05544101c2d0070380d40d680c002ca10080d94080b580d988200c00d52040020b0104030b114064200003071445081016003140e4403092901801d0b40400c9420000180300441c6038428000c4000c25950441102800025 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 399544181 1250 399542931 399542933
    0x8030c0d020c0c01030c0318060c0c080c010b0a0501090311010309140a0614010b070b0a0c0e030f0705010f0801050904020f040b06040308090a0506040b0f18061c0c050306010f0516 79
    0x1d81e0002811486240c0004070310862958050160500304070036483c040050712548512540501d6008501410141c0c1d200242e0f00400c1c040e191200c89290007d2206807901c480e2500e281c0a0003010749410300a2030001d1001038954040d2032030a081d00d40c414a10001c00b107409004600034010044292004809560b000b0011402840f84450060003203030b010a0300142c8001007000542c0681c480c0100c20710411000b070124801000064011450540116050008010032074200e84078802d266854003030b1110300160301c900003800004030b840a89444480e21008001690410030922645401c240b20100050061400c050002c001140c01080020b0412051001c240b00d50090b400c1240e02450028000505141040d400d0005000c01c541152070035003030100d29019405990110b540a0401042003604d211110201c501c44030705c054240340c0c031034010300c000000780d9850503983d403800c501d44040e44400d5440340d422203110310010b850710101480380001c11103059104110440c02d280310220840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 399545431 1250 399544181 399544207
    0xc050406030c051b2127060909010e070215101806080106080d0201180c051c0602190e030c0a2711070c09091703090f010e0304150809030708030c 64
    0x9030f0803400030001700304022074803081020001240000740e030811403d22800c0d4120340c10144e0504182620300f846c955034000386010a0442c060251802c0c0c0c45007201e000401c3e6a4440c0e60414402c011aa00712402c408695401c0f02c2d4480069400030500001914184a100c4046040c1e40072000881e80001c0c0e0f1030b40d103d440742c3c00c4511fa90092805a0003250703205141a90901880c0c3d079485c412281c82070110540d0781c07081450003e0344107460003803083c0c05c2d04214150403041480c00680d0460030666495108061410819050340c15202c08103010224042c2d0320300b03001605800c0000003501400f040d03800e010700b01d8a0b0840000d0300c3c0e21104042c0c00c0030381780d01d00d95000382171072600442c8409032030300760304d180000146009801c1158100c3c40c00c5582c3c8042580a550100c202690004055a81c1ca501400038244034035504261a19820410307041d4403071800100510494007040e1418028000d082001c950540040e2403040d80340e4810700c982004502c1c980002d46d000b10001d1841850580440141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 399546681 1250 399545431 399545467
    0xe180706021b0102150f040c031a040c080303060108070513030501090b060405180c040906090b071805060c0a0b090106030f080c101e0906200702030f010c050406030c05 74
    0x90040e04282c0c0c65031503005941880c2207402100f40081d060310241c800c0c178140c0903040200680c40109000e8042800c0c010010300c0b0304041e641012104100840c011803e8101c0c0703c082c7c2e0101d8806c400d83c1c0001582c0400071081ea401864141d440f0070760380c1c44024040300d0907049010303038000b01c000308900000016407d02c02c040340103128417011502494004100812602d0091030541c5ca070b28200e4044100b03010115421040407411074001848000f0742c18100000c00103640020100d2141c10180b001660700040d44a142d228080300142003203454800f8448203011304c1c104035001e90b0151403039100150001da0441c1d444034410000252055407a00d0b100004100d640e000c1c1c4410400149000301018180b0451a4020081c00c0621407043da280e5140c03490501226004103941e681e10031102045a950407004048000740801241d24000c2806080d407540b1085007240f081c0308046011701580410f01551400d002640c86580c10b15180c003006902410303041c61000b0400c0004c0184401081814401d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 399547931 1250 399546681 399546689
    0xa15080c040e16210b040b0d05060f0c04031202010506040605030712081c1805100b060a0c030e120f061003031b06021909092f0a020a0f2f0306010e1807 67
    0x4c0801c1da21511030500080b0f500300c0360f145004005038004a80440c9000512940041440001031100d54070420002c0560060381c0000b130040401141000070705905402c030303900649044408100c1140d4503c00c040d528039492042c480c0c007140711099200415112005040f4010000744038082c10200e01c2d0800003100c0d14a80414503a400740721108084c000100240305241d650344d52300b08039003000c0c04000f07942c90003400c1640040101c4000c0001c20548103010f010840ccd94042d00c44006996410300f600d07141c05402c1e520f080b0038411a00001d096090385000d1101316500350316440c0c0b12048525000c040d2281e81c406c1510740d55001c000c02410100d0f100c610110001c0595a100282410880344c10180c610302030000c41c8900902c0d4588158010501c80088100000508203035034010f040c105909014074440040d2500d00c10b03d525000740965041c0e00c15001c0e00003600309220719800050943c1c80d800800f145605503011400510207802d82071011600303c088d07203170b124a00c05024905a894421181c01c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 399549181 1250 399547931 399547997
    0x30f180501021b01020c070b0304061515230a03110f0310030c0603020703020d080a20070b010b072d061b0912200a050a15080c040e16 59
    0x40c54243c12603e0490303641d030040000d402940791201021406503a1710042c05800809080003012404102050740901c0c0c2c10494052584005650b0300c40c1050b11003031f040c1500c0089809541c5407030840841540e4030a52442d05d00585003401d101c1e0070128001d00d1442c03440c0000007001c0095820480c5101d0256104441c0c186d43c410b001410361030003907a000c599a000318285401401554006500816958520803503071a0800e03556484403003e001600c0c0600f1000615a035100c50340066584150007006040d0203a00622901d0340d0340c22903c051440380d50405881000301b0451200380c07032a0090380c0d061042000740c100304100650344811003168030b220101145070440d0280720318110f4218004400505c05100c179450031021355207500144000c071504540b0f8410030b660000c00255100c568800240002510980c060384d03c40445e07c800580c00d80190000c0703007102c4c3c005200c0c00521800c0700d0903600151039402240d114481a0902d8015440d0400c050006040c91156004450104899801d070411 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 399550431 1250 399549181 399549187
    0x5040806043c05010c0503370207200109050303121e1501020708030405210f0a05070e1f09020c100f0c1b0206070b150301020703030c110f070501030f18050102 70
    0x498181e08440a100c41901440014010030126070703201081c00e542a105800c00c0410340d1810201d6810710260b1a20720107a15200ac90310600340400d030705036007e16880c02c20107104410310b808010b40b540c1200d4803d02d540355004005111112814068054008084940c42400100400003942c00d5003000c90706407640c0b0035070500340c25256134100155001020500c002d07502d018140004950019101c951401c140704203201410501075041049880303501c040030540e0403500f418540280c4890700b62044080242010002c1143c01100300301003181e60446501d0030380500c0c5040c80d0000650010113148940e40920f9207a4180e56005000d100381d15030901c41c0000b400c1e6254003003d000c0c100d0303b0358080c490045202e01c0c000162260003c807044c0c150072440400f50b540c1c4803443c00302e030280c1c0b858041ea015400070420740205070701604000c580c0042ca846d03504500000f02c601c680c1d81c0782101c6c5103000701e60065404020b40d50080e800059041ca40c00004180850000d6070318008016852080301c1d569400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 399551681 1250 399550431 399550433
    0x10204050d0b0a0f11250506070801030209070206070503041e020a030303020d0e0a0c0b300414060610140c030417010b010f12150305011509050705040806043c 70
    0x920413031104a41a2a0400c000b031001501e000307030350094414590000144c8403640c0148054080c0341c02e4810f0f40704046503030300d28103110003e085039000c2c4001c90245080d40e000c10941c0380041101480362201e07070784003070450780e840d1101802420080d81080a0520703c05c54000580c8032500340f50042c6000f80c0300503a0f82d900d1000000d0484520903010740080d0407100d102000191a070301000c0403909070400558490502c2c0000f0b0781141a142c00000c15112020040d1992506805816102d02d00522104100ca07613070421403604e82000f102e429600c0078500c6452503801d4020501144541e85005071107040005540c210361031503120307400c8140d090010344151345505400f40501a814502031800740301d40c030340f80c01c0050941c0110310500802c2d10b1706c42d21807881c4149101c05640081d0340003802400080442c0540d40c00c00501400340c1081c107410400010300300c034059000c850485003080c1c0104182e0b50b41d0344902c0c11080d101085070300c2c171101c1c540c810001c2020031100c0d140382d03400c1018018110255 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 399552931 1250 399551681 399551701
    0x804060209030a0b062b06051017010f050133091206140705070206030103081608070602210114040902060c01020307090f06020d0e1e0603090307032c0d05010204050d0b 74
    0x110785070007101c820b8281c5100e0700c0e19840701c105254240d10041c04074540c0c40d440100c1301c1d000024ac1001075090381450712040c171058150460341d0125503403801004a41d803150038034006002070000d0340740301e681c0e01d030041408403580404409041607a890144032b403a171645900d102421200009964164964848802c00d0f007070b94148641145482c2491450f200d0142e000c200180014032001c0d000c0e03100405c80880b407407110301290407140e91001f10591b0744d0070f00d8680031009411a003100fa141c04022109054001002040603041c2d494042c0042c20080140c01040054a543c800c00c9800ca0801d02070001e04003000d0001d0b40c0107800c60348031007180340c2c00c001401c44c0d021400d0b0b020508561102111810040d0083d0085440840070f4910916840500c0113210a0316080004143c010310000308001c05500044098040c00c0d201c0d80e20304c1010022581182c0051039000721140d00040c0e446042d481c203150250b8a0a06540b0030000907042554460020f5883c4030421020340d8a40b001400308604115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 399554181 1250 399552931 399552949
    0x1060302042d050103020108060105070c0e0408031806060109120804171c02010c080a0504031106040c05040c09052b06050103050105040b060d0c03030f022d010e15070804060209030a0b06 82
    0x890346404203c02e6146800080000101501d410306000c00020710307105114480b090003001e0903400440e0000c0381030134034002019034070803101c0111b4120603001c4060200c0012030003074000c0c4c805a450380034050801c0310035150410b4022007100c40742030400000a2420b043d00e82980d43c005500c0240150150120301180b018000032031803000c691401c0c2000492035009000c8a4003c21032420010302990f039441e0030f6464440b007140d00c80480c82902c0400c0f00b0003d17550321050507503500f43da06114040c01c1d00303c00d5800042902400f0381c02200b42500e02c250050411410240641a42281c4026861b580301c010032200281c0080d94241d440303404100c280a5102c0703c05400240c02e8074040b80504c1d05454115003510320b8040201080042c030303032032106a4400c00007095454070700001d6078400d810745910840369125050400f5115400e0000d840224440800c60a0442c065001e800081c0d0785c44003400c694100c07004104031006030b405d100000c42504c0030421440c0b0984102c201c21010b007040750401103402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 399555431 1250 399554181 399554261
    0x50c120a06030b01050a1a0f1b0a02040b0319120216090204030605060604030503090111010209060a030e060c0a0f0e150a020a03080603120a030e01090b0c190e09011203020106030204 80
    0x1103d01d031040101c43c287d01807008020302c010a046842e8403410109102620408810042c090b007150081000e2005c00b144003130f01c1c0c41c0300312030802900c0f04103014143c503030107070b00d401008084c09020500c02207400469021004829071041d10100090340140c46000322081d004130340340719404a82401088401d2260640102d01110014141495980c0321640ca100305400c00f410004500107404041509405583c03885d080104516103070206a070006009001c03182c0800194400d4501140380c0a503480200c400d401c2d590b076103e200103440c13034400307032a074003200c07802d140c0c200b441804500f07041d102c0c42c000742800d0015580a45548000390800400b64500a409580702b43c0201c42803104400e480c00c04c55407240014103011403904000007034280109582c00c0050070b180f5014080105a14001000744640d04007a00e81c200c0111400c2402c446000924034401d4101403070f44018402d0030401c04820b0000e510038800403841c26201d502144c00d40d01c00c5141103021034000d082041009440030b602100301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 399556681 1250 399555431 399555439
    0x1b06020d091a190b130c0314090a290f1302030a030f0e040c050a031503050703050717030a081305030c100b1008100303140412051507081009050c120a06030b0105 71
    0x10701358500010500712169800c20003a66440c0c030541d1005000341c00c410a004824071030410b0b9850902000364544c02d240008844000c081685041342c0c41101c0c101c1070340b07403e0400d28818969034020b0300c0b4000c010054051043c0210000581006a508000b1f140125109a4800d8007600e64208040d19107645513102c1071041d0b0405000c0d03541580e000068501d1114a0318010401d6400070551800c000c0080d000640680510719022050120014242d002c8810390f4001c03503010b1188440540d249e00501350341e603000035502170100d00d03032100001c11011024000c90540c0e2820141700c3e50145840380740c070b0000f8a000c0c1ca0ba06070000c01d21300207003104000c080c0d034102a0080c0c40c0c0b071050b654440c44c0c0d9000040520105100c0c85071400044810782c1d01a204145012203c540c0d00d0600796a2115208a10340c010b0f1130703100004403054400e0400354098880420041c84031402e10390008060700c0020000b014440090180c058400f4480c2030b40f50051100b5000015101c0c1141080100c01505802c40c50003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 399557931 1250 399556681 399556691
    0x2030403020a120f020a060203150607110102240115030b091e0a150e0c04171b060403021c060b03010614040518210405090a15061b06020d091a19 64
    0x542c5e801041ca0301c203065121a005036640d0f038101042c03418990949290b40c02250100d42e50b01002003031041000b13018000d80844030f507100030382001c88000da000381c508100090b01c0001000484c80c02488a0b4001e040f508003c218140b03400e020a824440c21540c05961081250341102111602154260031140c120ba00f8860040e013400080c3c2410041e02c074242c034114080c030000300074400d124159009800107601070b502c0c1d44101119117541e0802001c4a1684001c8030441816a1500e0070488084a50140c403a2074480d00c0c54112410041314840182e5149454100f080c00c035136403c2c45104040e119460b0383c14610001e0a050000311a00200a1941103c000c109204030385400030f160200d100005070920f44068019112001c14040c642c0b015400c080b00e42e0a004400d14140c0006804021924522020355aa25000c0b201c040c481d82c440c2c80e58a0900d001f010124103a500144940d100146021901080799aa803500c0804402d0000f141050f0040030b0200e002440c1118080c0c44445040c1404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 399559181 1250 399557931 399557957
    0x50d08061e010c11060f1201051903060506040b030709090312020414270a050a0b0f01140903031e090a06090605031924050a062f03070602030403020a12 67
    0x70210015a280c14000901841410005204c0c00c1861a500142125440e0b0030942170081441c0c2001c1000c0b10300c81d2005001040c90300b0302c06920b030a0071403507007540c1c40078502c1d503100d0b04010003001c0c01c5903401c2511f03030603400c00303d0710208099002007842070400680070301d050600030700000c00c10325030800d064010082000000c02e10410580c030884221201e107469603d0b40070100c840080c28141c0c040f407003109010488410b0990380154860b481001c0180194000e18007000464151011104d020501994141410071a514042c00c880080a030441c0d160540e2142c1c40059086400109186180000f5075202c1c5810680760081c010a5203045c80d984240c18040042d0090100602c0411030410880e02148840902d402c1301c504000260000c0b00c901e58030150840404003140aa640a20303c070400c0051031318840c6400f902164003501c0c418030303079000c0d1444041540c8200268019544414420070010600920045000702d20a80003018605203500d40340905003a480300c49001e015000c0711803a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 399560431 1250 399559181 399559219
    0x110f060712030b060d05010e0709080105070206010905100315060906080a0b0a091a100e07090f15020c03030a09090b06090306040b07020f070e01080f07121b12050d0806 74
    0x14841810900b004604990742c0760102d40903000712410500998200000000c28002d989002401007040b40d44d4510020745030b0301d0850903503805440c410700592003800100245c44a0303611550f00b0400414030021030355565140c454a00180e1f20140461340d2b5500e00030012020f0384d07c9000f008100820141501d04a1929090f0324114014440e00c0f1841e02c0343d030071408000300715029000c640d2220740c1032511401d2481d40c2141510040c0140031403502c03100c0100f0700722401000032a00303d60296980d001d2450600110304044201d01d00810154416031501001d6580c060000d448505143e60f0f982543d03c2c031b414012400c1d981464081d60040d501000350758482c2d10042b404650154100343e07480d003191120201240382900642c0700b03120500407a900490360000301c81c4502e0481d0780302c400f1a41c00016101d8641d8a41e0b05900ca20b01282c060420300c000014020706072088100140320185404036510b514a5494840b0000304490325040307046045845030f040402290400815520508580c440c41080c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 399561681 1250 399560431 399560453
    0x909030903030c06020906030118150f0605090d050f0d021c09060e0a1814011a0306150c01020403081b12030a020d06051504030309120201022a03010603110f0607 71
    0x181c1009182003003c3c0a002c5140c040350b050180180441ea900d42c0d40d40c4086643c100c01b200750040d8241007401e0f0003444510703c0c1c0c180c03091f10400111001014a0b108003507030268403000a05420103642001040491030070b000000f04e81c22550041d0040c2e1140000c02800c007070741d400d80b030602018022880000d841c0d2002d9144107a664508003c0350442305240003c9905a2039803103400341d01e400c0004801124165006001543c8d2882010310b11070b600c0f108621407590b034010010401d06024000143d1034948031911b502204075107800203150260350996a42642d01540090300d0f407690000b12480c2e1034407003100d0801e41103a0340001d0603c810460b000020940700191100c41c03225004128500101c10780e0340100001c10004240420210b456003101e001da4002e8441a80450111500090744070355040c44900249e078160301070138148500d0406104031105240e4440c024400890041040e038409204480155000e050350ba18414004020041d80c0c902e032925643c01140207020040024081c0099 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 399562931 1250 399561681 399561683
    0x70c0b0c04030c14010513060e15070f020f060c0d170c03060a0314010204080709060504200a031805150114040e030706050a090803010e0105030c010e0609090c041701020c070909030903 81
    0x10504c00c0c032141400407034060041813076140013410300980000e581c80e0840c00a001c0c45e5001d0b0342c440051648040703200e05901641380061b0089000c408024010b00d4955035210700e080e80140340b681442c00303004c283e501d4047c001c005a0301003460b01500c04041807106c00f903243d0001c01140b41c2c0b85140b500e40003185641120b03100051054204c0031100c183c150003901a5000303003c0140c01c54410640e50070208024050391312419000e0362a1100824506480300781680f520390b4442d0226203880e070511021001040e000d00303006c011080c0c40c0c040e400041da09018002d186152094650800c1d414072000c11540303d104190035120350b15104c05080d06140102c01d851900d9000000001d040c0c0c0c0d55403000021340708044008080000000020a2060f40003025a0590380c05808441d00d0b0132211005450500c1700240183c0d20100c1804401c10900d0011140f48d8410741074101d10b424142e59880103039140c0c109001480490350003007505e5410020800c81e807070050a500303c0500503818079031400380c4500a40c0c04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 399564181 1250 399562931 399562949
    0xd120c0c140708010e0307060c02030403051902030a0803070201021305030f151005060c070609080304050f0415091e1a181f0e0402180c030c0a0e0603070c0b0c04030c 73
    0x5050700c008003081c4039600042c000000240220510710303510742d03207d070321014048031003c0c9001800c6101602c00004c2c0d40a50340d00c54010310803039404100080304103054a200326414800c00c0c41840002c2e1400002d10700035501a0000342e10ba9850305084018620a40c02c0a4040c0c1d000740c58001094000048203000c0b541c0e000c1d0006255207410744443e200340d203e900032540003280000d80c00d0f456000020400f007240c100e0350f07a06480340c0e12002a60b459114a119065000301c5030b000b0300d8094500b95111356000300d82c6124904000daa00c05031042a10700100c51003040383d0003206070210325100d5000d528485d813660075139502c1e80c82d40c0380c0000314540c1d1101000c4840d040c140000400c20303009100201701902642c09041920740c0da40404a0010b1001c03078080b405462800d40d25022052041412805243d603001003e003190342d05803140d5081d40200c40300804000d265007e121054403034600840c0100d10940c2c5014102845081c4894094005003543d45403c42c20003003040402c40c001d0416051701c903003034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 399565431 1250 399564181 399564203
    0xd0b071116060e2107030b0108010506030601030201120f09060b0f12030a05220306050709171e010906090807050601061422080d0815030c0a05060a1803050d120c0c 72
    0x20229001920341000340302440d2050030b04d064180c0c0006012001c6a00c60410384140b6070b2248255401d030380c400d880e401d415500c0039005000543c010000840c14214101c4001500c3d161285c400041c0c0b00e0901042da02907581d0140e0728418100810814802c55003075461a8499503002610350360fa11518040c01c04001c804140d2460000b0742c14265a180901307000b000c035030140c417810510004e01c0140c0e41c20300422070700c90000480b540a501560440300c022005019000e80e02840340b10b0482101c0701d914165542c42900fa00003030494851210003901401034152901981d2621900e400d006030002e0052000848407481e8a02d01601107442c103015a005c0c51440c020f4040407041240d809811400d4907004503800f1240095014401e031b032144d003c02031a00250018202407548810350011740b1900070004200511441c00c000000b009252250b14081ea202c500e080001c400301c4e0036541044038039802443c40e000082da8072440f44a02494030358000c2043c0c08100398050850038180d100100062085 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 399566681 1250 399565431 399565457
    0x9050c030d0918020906040b0c07140d030305040318170f070f150c020d03260606071103070801060e07030605011701050405271f02180910050d0b07111606 68
    0x1c0e0140d90f2017040140000d40c981e5114412461107030444240c0041600c0741d000700280c02c41c4150f8511108103400790203803940d203032507031812400362800030001e41c284405002c01201c640381d6031104e40000c21100c4a540421344110001c2410b007031002450b00d6040e4011102801015001540ca0f01211568a05250341d20300040c000c2d1440c0d8600d00e80a544034000403519400d00d40c204d09890341e00c0140696100d8549801541e03031001e00025503c0a810887c01d00500d00041d02c42a8043e152407002400c40d49550b9642030741c0d40c25501b26800c40485502c5100600950a030540a420090070742406d08040090007841447c501110504c942d620498460740441c1100d80032a0030320a40c4030180c02000348404043d15085d540e540d584e915181907060f9074804843e00c080c17030320a41c1c040e08000020f00090030070341010811840c0025011420028640c44001080c4e900c12075400e081504c940030b40c070380c203181c075000c040c103503007010004101c9540108450340fa610b0007203011401516644d08082d0000194 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 399567931 1250 399566681 399566729
    0x10f181a0d06150f031407080c010f09050d2a050607030c150609020c070e04020603040605060102070e0a05011a130506030a020408010203091005070912031b050d0309050c030d09 78
    0x40f080107542c1c03425404207030310302128002c2003543c1c0034004040c80758403240340065407400f161248403000c2d00044041107503588910701c00c0401403418900700d01c0032500c440000380d000c43c11090486908188440480381103596203442c40310401310300032000b002c42c03402e0041030780d034400d02400404110300414220104104150203074a140700c6001d0810415071502c07400070095101d0300c40101071f07100d082400903954440808071881540e02500580c150b86656075500d001c0c00d006070082d81540a1038101044103580b0040c1c1510847c5c41c42e8000c1259450103c0e055104205404032104031501000541150140c07016148220340c1c0c103031010340c1e8940d200100f0034000c0c01250046505940000103000002c1d00014608141c00c00072441082581c0340c4c20400c0e1030b80d0040e84101d414810501294a0219000c1d100d024402070b21503405401c88845036507141d00303101540034801c000c01d980e81e264005102c402c021001820800b5001000c0c000320900d00a800c004e8139100c1d89542c151340700e030807500d03c0b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 399569181 1250 399567931 399567941
    0x16060c0c0b03100501020c10120b010c12020303041208070c030f020106090212090705190b0a031401150f02011a0603100b0a020d08060406031109060406030b010f181a0d06 75
    0x816001041e890341461a0542c084480504c0b40780d00501c00c070000188a40340a40420142c80c0d0141c440c0e19082a1500000303024201c44c10b4070038140462101a40003041100ca0056114040c41c1d018580d00d01d89403400b04000c141184200041203c61002c018000381c20600c0c000080d50035080c0303d01141e2074008103d000d00050307000140c10500128840380109100c148140c001c18440003502c4103162030360280403518000b1501400c00a08944040180f0350b074080c0140b0104c81607140100d1090100001814281c0702a8006201d081c407000880360140e078004079034010010a0f2000340f04071101c001c40100e1781c5442e07820861041e5000008505440c102400c0b16008014501c5800c0d1203043c405130203501d51000a01500c0492400000034040f031030180b04003c262680401117901c094070020070b012680400518491704669604400f1001c200d807115414020081102c40b01c01060030010300f0450391154180299507603090810340603009a4044c182d1307039525800d6420886100d901c0c10801e02400c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 399570431 1250 399569181 399569189
    0x30414030c1b0301050705040308031e15040c0c0201020c21011a0a060f021f1805060601031505090106050f0f040605070303110c12030c04090e0303040204050916060c0c 74
    0x1110008030007120200c041140c01603000c0c22140050380414035001d0500381c520884501000400421080c0b00241883c0c01541d00280b07014080003c01c00d0300b94481100a0b02a40c0c85140d684130303900021801d10f01401940354841072803030705c4c107014401940040d648026031454284110100d81c1c1940c1c400c141001d01441507002d41c1d0084c80000103801c0e03400c8502484190042c081d0799402070125845004500a00c02019154028034004401c0d59400120307100012650000940307a4400080d407000b510b8008041a004078080c004c2070a18100141c1152000c1203500b452085c0420700300202e6072810b041904607503150030000d03550031500111140b40c0c03103a070b5011501c610010601045030740c1d208018040e603a1281e18108242c1d40c1400030f51b0034501541c107210034994031920316075482800d460003a5401001110000782810348800801c81a04d90f821040b00c4542c4c40031080000313524082c000c054000c1110b10152200d80c04803001655221454040d040520503103e0f0300303004001c0d02d412048010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 399571681 1250 399570431 399570433
    0x8011406060d0e06040c05030d111f0b04151809110402030903090a030506040b13050c0f0a0b0a1d04020c0d080c070605130201021b0a1a1e07060509060714030414 71
    0x1c5d00d0b00d460300240154003070007070034000c1c4104045820058000e040325240140d21400500108488c2b041c140307100003098030110766075901c40507400540e40b9140141152102c1c1c0114540c411800c1c550809032145c100003507241c0c0c981c00c000d1500c02091891104411000e400e84000da038135079a0184042c914130031075084076041201000008140500401c9160003540702c3d000c2c2e11019110a0003881041c1e110030401f8000f60840c80303000341203107401c0c00030345281c40e40640703002d5240795240358428150f00140f1159010030414160903500010315003980c03601c08005c8030114180052544039075964054507640c0c0092140c8000032904544580c0192503000b17505c00700034401842d01c41c007100035144019400300c0c05485818913020011040c04042e4001010242030000d0b4280303010b00250310041500a0020b850b9020401800c040012414503003180c101844070070b580da20945004000c8407070040c44a040c0303421a9060000569010b60384514200d280c030003071602c3c0e80300c6040c010032031500b0100340b10407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 399572931 1250 399571681 399571693
    0x1a0c07060908120c04030b0906070905041a1f090801020a02031e16030518030639030a05010302130501290d1b021b0a03020904140318040608011406060d0e 68
    0x403003007500117209580c030403200c0d00d40c15260b9042e020744e0f50030103440c3c00020500c4400f051142e800d07e41d000384280075400709201d0710014004045000991414002c07813001100350000703603086400124140080c46110021450310800c010001c2d280c1c0141c259950b41c03a0341a90410301e00d82c1d400780907900c0c000701441c8a21a14002407402074070301da210404e00c00900c8443d9803e50703d24640450480e00c9280c4445212071a110940a410103440c202c1c0f280c84a104400f103450680d203d2084082c42c0301d00045030001405504500411032403c00b0cd05d4000c0740c1c1d80c10300e4014009500b8150003908030030005640d845620903031200b5040c260240d618000c07104c604c1c09a00309400074103a2445403070005a502038450002c0c080100420301c00d20040050341040ca4020208010b04185180d564000d00a64070702d102244800b12450840d80722000758010305400c1801007240c0d25061081200500c046c0c2c008115144c1a0140e00c100444014403c81c0308810200f04902c0c01c0c604c64102030280c2e5078180c00e03948 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 399574181 1250 399572931 399572941
    0x1050325030816030f050306100305072d110a030e060703050c01092a03240b030a030e0102070b04050306071d102304030f060209010318060203041a0c0706090812 71
    0x9200114100540011752000c007102003541c059000c40b80160006000b10035903c002110036009404c018000c0004c01c91000f0810301002e6448201d005060b541261003c1d10f800300400080c80d0782d09550b4080c600e42c000d580060002a040515405810000e07621f0756180c80c11400e095850303010300c0801c0c00c1d0b42d50811103100b081005058070406840e019001602811201b40b0090081e192035010042101d000c101c1070301280c0d02c005500805411102d81c0220303001340c4000c04a414145069402c40c00314455085980440d0f80611280d805010f05240311803c151806002a58844002c0c0c05501840400a02c03880b01d00220102240002400b42100501e20304041008204034105922454148243e00e8043d0b000381041c8112002c403034121580040800f403e072561402513220b9000541410f507a41440f104081a800c10200d02d2800f4401c010b8882ca8075041492074a58000f44020302244003204100051403014141c0c0c07080d40e0401c60000d1448060300d40f1064600c55059183c48003442007042207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 399575431 1250 399574181 399574207
    0x5061806010915030c1e0507021903060608030a0e0619080712021804060b07030e190503061603230a0e010e010e0f0d050a08040605060f04050901050603070e010503250308 75
    0x5c03c650080b0758403118001480b1a9448814810344050b40004004104134809850a484002508441194545146035580d40c4103c200c41c802d40c0410381641000c521039402a401604900340b9004c10f9507a18a00701c0d000f6144c0100c0e0050038502014004400d01040d40310b4402c000100c601500b1920455590714083c05a0000c00c20360340e0300b50703c11801d201011030380283c403c0070f0b01c5407a589900e803042c208203007104100342100b105136101c040b1034a4640000396580c040110038003649118001d0340754645e1040c4000c082c0c13485032001000360031004d4030b49801e00794005070056101100f1000001c038010f10941440c050842c1c0c2800c10301940c03c003400c0304040300000c1a0011140104400c031038044044c0c2c4400e81e400c0c05007501050108040d000064082034058000940c41940140b00d483c1d0032040b1070024080720710540704032150b40e56031010001c190a0400031100074040180e000304881d80b410300080d64964508101048007885000b45160780c0003980e0130343e005954440e442c00d480345031100d458 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 399576681 1250 399575431 399575441
    0x9080720030f01020c0303060405090307151a0306130605090307020409080909280b1210090b07020a0203030306040b01020a050d0216050f03033108100507030506180601091503 77
    0x2161003802400750049250b401403084801d81c103a0200a50f04540d034000c1044000e040061071224240820401100010115003003181c043d1011280001c554108075111502500340840041c0240c0c805814418030f00c000f11400175415910000c0414959904814213096000d030500094000f03060000c2d0900b041360000260241c200b09440100792136440e1803116400c003400141c088851030110f5240d150407003154011a1b0003500142140c400f08a800d1111494104050450065259a800c0300c0b020400400d40c0d0b160810014802018422480c0c0c0010b5241d11015100c1449140d6813003401d042e590007801240740396508102940d20001030880081e481d4600e00500b01d0851081b04404a06c074171f443c0e640b0403000c000160086040ca50500c0229020b207102121080c1d0603980900400070f40340c01d0f01e0303e920240441d18060814034040b1341c115801c0c1c0382d014190302c0a15007860100300301074a43c4603440190703184099228241c0e4690034016980071203160441c02005200c1d08521141a0b016004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 399577931 1250 399576681 399576743
    0x2030301090b061314060403080406030e070509061c0203070b070b0f0f0432120706061406091005120a050f060d030f0e12030403050708070f050f0103090807 69
    0x14401c000ea01070070814144104d0700c42513410600c1d2031050009042c2d081d586030146030041c18043c6071a489840b0f00d95150410341c00580029160881c0c208030075010f020000040606981c108243c1c00c0400c000b4400b11700c000800f62110241400d0b00c2d044d9a801c124020083c0210700540f50b81c2e5001d81410103140740304650302d2074128040000720b4990b0040e085d10341d1045400c403074205503908a4100241e00c070350303181400071003071845070072030b01168001402030000106c0001700190341c8007036500e003080039a80030303038000304a00c10a111000200d480d000200c0b4082c00d4201c0c1e4810300b1044a42d0141c40038014803e000e900c01054400308082d031110b5911142c0a91600d11440503182c0d0f0301400c221000c0701e03452000340021003104445c0b40c228041e001e94a00c2a07002810003180c44180031907180345402a40c030a451607072215000b0010002e044c0240030181801402c0005c2050030900880c5440c52280c15440c10503a84541800c18081450283c944d1103500840055a0204140e80f180b201c4000c400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 399579181 1250 399577931 399577949
    0x4060306061a0403050613050c040608061008060c0702040c2109063b0a0209090303040c0509041101080a0f050405061816091808030709060311041805040c1502030301 73
    0x240100111001000b0380e0200d9a0000041c01c40ea07892200b001f0755000c8000c8100d0ba40d1103244980b80c0c02c0d544902804025140301c000030603452411700e20111107003140d1b90201c1d101d5002101071080c1000c051341241e80c0260103442c045031440d039129048400d50310140d1004d440032400c5840901c1030a080d00100c12060040c41d06001081c194902440f00d0b10b1040710400c0e0b880c800207103c00200c80740030307c10720040e0084020b440210700d20341c001c24444001202d0a01c401c0d04000104801c02a403852001c010700001d546c00d6078145010341d10340304092420031900341482041000200e180241e90072202c41c440200600b48480d003401d290596580d01b040d1a0040380b04c0c1040700f0310102c0b850008070355078201c49030040c8801c0180340400541c0103000324906890140c3c04405032101048040004600400c2103507134842d075251a080000b0201d58910060f020842c00400040010029003003a0040040312848005225111864840c1c0034040ea54000714003840d201218140060700800a035040320312280c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 399580431 1250 399579181 399579209
    0x90103200702010305060402090a1d160c0b0c040512010f11030c090909030f0a050a030b0105120133020102090a1d0708070210021201080c0909030f07060b0406030606 73
    0x3880602400c0524855803036001414414900075601c2078004603001704018000615280c1c1400200c0d000c0e03c481d0300102a82c0d8000c050f1a0160514012a9a8050a101400d40e0604080c010081a10390340f4071004d468210f0b44404140f000e001c0c042210000c0000403c03074030203583d140160601034802030001c07820032468840c1e01c8070901d075840102c03407156039407803401c501c0d109103101003099803000035141030268030040c00106403c50280c030091000408035120345441e03030421748000381541c231020181410041c00f40054010307092449801d0341900c4160f030030b88041b5131441480c20302c10a80c011a8600c2141d0080b4031403511034042d4000c050b1001300340c3e14400d420381c40701c0d0104012502c1c540e000501c441090000f40c000c81c4506c10440d004101c1e4070503500c0181050312400260f80000ca90015080c40c11401040b81480401c016452034200340c82005142c64000c2c407003a26401010810103003400005615420440030780e1147c0b04a00004004114164a070b00301a8000d0115000300040d18400b8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 399581681 1250 399580431 399580451
    0x612020c03090d0c081507031506020c040c020304050301090f0b09030c030a030e1908130509061f14040e060405130b060415030501050a1b020a0c050f040605060d0507021e1209061e090103 82
    0x14031440907a1030b20740080403840ccc100018000105015003030707542107000c28040868150360038050020201c0c060046401201d0346814038102d000d00103041d07802258410402094845004000d0b1455948541400143c01490070030700c50621418100b20f214604075420043c00700840e500182140e50260003e1511440d01ca50900403908410f440c103591042a9120f0001182880707080040e11560518084000c6414a000705c0450707005a000b9040b00441c03003003005a035003418400d159010007100980c0010f20459218150307045000f602d00c0d0301607a2100c01c040b0141008400b0800155441030082140b40740070b40c460b10040080d40103d01c000c5244100c880c104a1000400313001e803981081070183d80314500b0080101d540700350403100e5001350700c90780001050f650309400340914550604001c00c9500c0d000e070000f818810070540c804c60040c08072010507000d44000400c959240b1044251030350741c80380702c4005000c43c040c182c07041d1700a128004450810340c0c2200c014060210081e202800100c1d20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 399582931 1250 399581681 399581711
    0x1d010f06030305070209090f060106030b190e0f0a110703080a050c0309031c06090f0b01030b060426010b03060403171303050322050f070612020c03090d0c08150703 72
    0x41844041e00045081c004030000d4078001040d0364015107c0300803550245000e0391014104031007603010001181d40e0b400101101c1c1441c0000b45000e4030961203101c4007a060140800c02214046c2c00104641c0500700011184950b40d88520303032512400c9030781074640001c1d00c0c000f06600f408680005401742407034040354108c1a41d5065170300508a49000c0c41c01c0002c0128000c00c158242c074900d6407100d444110006400510740b0400c000c882c8003030408606102a0800074056a0904055a004500403c02004008808041c012240403d20350200006410060480c09880f505140e140d150040e50240820150440039400c1c4000309121600c6003070347d40440210001c08113a401402180013000000e00c06070512115081054040c6030b00c04142d80a034544901d030015403400e2040c0b59101580902080d90007c1c41d0101e1601c9136034041d40b8124810380d103e0740380e006d10700c0c0481c010b0200c504640108205140e0b040d015289807402c075164203034240b54002801000b80c3d0520b010078581740711000300c505 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 399584181 1250 399582931 399582941
    0x41410140a080a02060304050a020607030306080c0910050114072a0902070b06120a12020102040801152d09020c0601030b091507080712050906070e010207060f0c020d02041d010f 78
    0x500b0409025404900c2c2c0910505920041040b0348502030440210300591b5103002400304d0354025900000c1c2903003070139850391800319071741da98910900c102420454076102c0c2900a500f5030304280b814460312130b2014850015801002401050891040080301e9450507001d14560b141030410f01001640d1343c2c1c4d11420040303224001c0041d00c0e1170002e800103109402c0000d002405e010780c1d03230101c49403005103454104500c0c480c0d40c0c0000060350000780411140c80c0034081d240405442040c02041302e0310b010742030042d080b034510908110b1030007408420303404007143e06450002c2840e0360041d076440d0303200f40025440786800d00048844241ca6404100c50340c90005407021901c4a0916a810319211f1000903140311000910303284c00c00116a520302454070440c02010f016502c1c030301c010006805c0c42031015280c401900c11030740c110351040d001082001da02c550a442a10f00c80e090405980e0000e001203000310480c400065001030034140d100c101005803080c02102d40300381e00001c2202040d03801020003928 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 399585431 1250 399584181 399584189
    0x4050f0709030f020a0302030303070206040b01150507060f1d03120c0906181906181707151704051f0b0310150e0106050c010501150c030c02041410140a 67
    0x41d44a0001d00004004984101070107000a100902c000c1c1d403540000d103558411202e00c00140c122009100c1001000c502e82030152492800b400c0c0c0201c09500020141c3c02400350291a003900c0f80e003255000d45640e848035149841c2c0c10142c0020110320388201c1e40c0c90340641e10428405810400040300c83d0502400e44d00072900003080c8905c0c18085140c90121080e035421541d520680034081c3ca00603880080e000d80041415032a11803121000d200808113110043d40454040c40c40340d000808a5500070580350142c580080c62102d410040001c03c0b213406a9000c2c4403c051580f0f002031200340000090000702c0c1441c00c10f1048001040d450118094071342c5121610f800d540142c044641040c9039800c4414001f0324500048515aa504074846501e2400c0e4019404120000f4813401c00349428003810b03014051658100d2041c410713040005048059541c0c0c0a8200409640147e08560f215000003008841040207955541443d8203031151000007072040c0e0180a080d40f840603418285907507071038212 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 399586681 1250 399585431 399585437
    0xf0103020d0210030b040f0f1121090c090a0204080d020106060504060c03030b030307120f05130510110d081006020a08040e0405030f04081605041a01120605061804050f07 75
    0x10718000c0d0b09018400658070321103010315440b0401640035880710700c00c4120329845448007164034810007505904807405d0704091030744100c0410442e880d107040c200c06801c1c01c1c4449252481c0a58800084c14248040000060b41c03051584040c0202100310380c01900c01d8840c4a405d5844c1c003880795509034201c3d4824411000407850500003040114000c0c100c0d070311a11f000e8100880c8008007040003a00311b130700100e0704460200ca070361100c050300c6900440040e984a8281451450180328062041051905100d064400e000781e184000070148102500c00d04031000030101d424132a031004001c0d049280c111542c10100703806e00d000080d024400641c07400e500d9041560300b0b10301410103c040101c0c000061003901e080c8020003000c2d54082c11100244028150000078009440391580c1c2900c854940d5442a0311480c10034006120700300c004044202c21102c01d080240300607030754521b2400034003015807042d5030240d004907a10810240764012164044001c035020000b6640d21f0040013060182a00d42c8800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 399587931 1250 399586681 399586699
    0x40b0f010207090e010b130609061d010e180607080f0c0f0f090109030c0b0306010e0904120804031b0503030405010c0305102106020d0212070207141908061e0f010302 73
    0x403568a0713000640c529501c3c4004690f41449030701240e81a4181c000041040e80d40d030700d082008819074403454010f040c5105046c8403c0b8204922480214418005e4002d11141880414201c04030711210121000a500c01d0f81e60503e840c50001d850a0030490300034807058200000500221030348400c90703a60b45010070540d820705000070408103540d04824146d40c10b01000c40000300210b1039001042000b0442904455580e24210000520501001e50400d01407030b8410300b800005000452004030b5034107030f07207480881660b5604044400949400c02c6c44074918a1511050078010080000d520946c0184000e003c0c104c54540214200d420848580030b4000e0f4801c0144040d20801000302409c1099000501000d00591501e8089a008209125400e0f90000c1d003d00340c81e0604003c541c3c4405580041c00d1000d01d090030341c850491103001598400d21502888a4044115900c0c400207802e80800b110401d14000303900100f00094021000100d03030341d10001418200c17994140340e0603030341c0c0540b0010b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 399589181 1250 399587931 399587939
    0x180a061112040516060c0c031b0509100e0c090102150406060902030a0b0f240903070f1419061e1b03030b120c0603270a0c0302040b0f010207 62
    0x911100c1008031541008205820740c15400d1011035000700e005401030400000d492400c181112030070340c04101805800d13100f0b140417544040c1c08a003103d4000a00c0c440b45070040c09890714071040c94000c0342d48198840c05001d1740c0e5508598640564030138018a003410f40390b507904440b40f4018051042d0040e840340b054505500c0d810303419690024801d840106030303d9125000c039030507a0070484d030201d4902d0740c4500505403407820119000e1501425900050704001081400c000c506840b103000401d80d1001a106640c1d880030070004009212a9191030004c3d0f0b100c9140f405402a01e50b445440b035030302c1c00260b113642c0a80516142c00c44125460351030914504010140700000590380c40c205010808081e080624001e03546403100c0d070311980d000240741c503815081240c41240301054004990001700706601549402c0104ca8202c00c465100094000c0e845c1c070704048012013040350000724090010110100584240740c10240c038400c80782070082481090074408840216001140140d02040e0104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 399590431 1250 399589181 399589193
    0x1020c0717030a050c030f0403120f110d03020a0908031204020f09090d03050403120c090807060201020405010504120c12031e0c0b06100306050d0803090c0102010902030709020a120e0303060405180a 87
    0x201c891a81710580b41409200c2c140c1c0c2299400951042e42e50008080342c41c80701315440620b0b061465403604100c100d1644400b1016035a40303400710001c00345503002980e0740d9040e000350003a000604464045035030700c2d160410b9800c400300d4182e60482c01681c0040300b4400318a4400581c5216854000c000d02c0070307010034a011800340401400540c188002c2c1141d801400185020307900c0142e1042d16a1041e9926114000e803502c0c580d54050400c69106010a01150f80c1c09412201241d44507183c4001d001003e0500d0a0303404c00310b52240d0400000c1c010120101500308000c40e024060614110038400703601c101c01d03905802150001070848000340d0001c2d443c2d15280d641040451110320f00001d05603194404191194950320040c0d0f507040c0044100000c0000c108070310b1000c0d0200b8070007800381c10500d0303000c00e59910301030292400c5182c0100c1c800703540e140726600c0c051008a107a40e060180107914083c1545030340c01503c80c1800703142400c0015140421500d940c00700c407200701e402030450b28000e031070700c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 399591681 1250 399590431 399590437
    0x6092c040609060b06071202060c09030a0b0405011b0c1e0308041e020907020c03061006051c0e030a030e0105090d140f1611031605030325020a060201020c0717030a05 73
    0x466515507500450407451710b508025002041c03203003403c04003040c03183c4030281ca00303200180781291189041000000f542c8000c6040c014840c0e1040d40800c0036103c03868800c1c058801c00c0b420303000d58403c545001c10360355440300d018462a0701032000b4800007075180306684101400018041c01056105000c6030002d4800000c40001c6404849800a10718030755000506490003501c0c5c0d0350040c1e000f800740c2c0903c0d1032705020b03441e0403030700000c4448651031a180c8003404902400d0b00b02c400001201c042e4039102840368100112400d400400e0340d640780000300c07028006101d075607511611586400300044458100003120040806240c80c0c820304102e01d0300b40043d00750b1150118024100c8140070840c42d04901041000f0042e1207113040388260340c00c000915241801400140e1201c8100d4241005141c402104032811110f5001800540b407103010252009182ca0080007508120700100004105070b040d1f0182024005031029105a41e5440071010184040399800d4001e80c0c104200e80b9807024021401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 399592931 1250 399591681 399591683
    0x50906041e0c0605030a090606080606120f06040b04030c06050c070b070f0e040e070e0f15100804030f0c140105070f020127021c110103140f04030e03031306092c040609 74
    0x8085904051648c981080d2040741c0d00401e12584202c0500c2a00c0c03030454949400b207100d242c028105281400c4035181d1750100640b0140c000350700e0901050a2520810841c171003640c000c40140b0a40c00d0840c50810698019041580c0f0a1000408200303614451005000c0e4801c003a510345c00480c811000b044000c0c11030305105110352040035000034030150812907082c8200100080d294107403170024140c0e07012002c03102006100316040c4490107086d6401c58a46a0020340502d45100301004081041d0380c1e0044521000d0701824410842900d0303040b054015034418141d550310151114920b02c81a801e0303d00c007115030142c80004040184c40014a01c0c0c200c40c4603400289201c169501c0c01c0c07448007000311103040c184c861a00d1030740c065036656003502413401c4489100c51084028540710955045e22100608010200301510740d1001407a03404100740c409000c001c04040380100d80e95038010300303051403c0c4101c003902c91150800302024003035008491004200c3d501c0d112800d030b907503603141c0c001450b852078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 399594181 1250 399592931 399592951
    0xa051014070215101802070c09020412030e031002040308031008010b01021905160b0d0c0e131503080a0320040509271212060a050303041206020904050906041e0c060503 74
    0x300014801044c1103500b070b05201759a5006a40b6200e90500b51174408964003e08480c03801004204124100c1301c00303004503d40c05180500c020200c0c0300000e41003500f8221001c510710f0001c9404400d010740d08000314007800f21154264400c83da9988510300741c5080c1c0240c1c0b40544c011003203c6940302d404142c98000d070307803244050350380b40304c00040b02c1d205c184001e4004840e0010042181b00c8403403420722a41542c4440c40c10400e22043d0304a001480000407e00004103450b25150351820040c4070180c0c0e500a158080403032034840380710b120300030010000180b00e1000a1150104400210281400c690a484000d020124a603494203004003646c2d41c2e282c00c0c16561040920203c0b489034081c009400b204105c114803c0d1307105101c1c00c0c1040310080140800c0e10403d04c500b81040035940c000700716400c80c1c0d0410707c841b03011956402d0040081c02414455500281824100a02c1e000c010405c2c921541c846c2d1480c90519141e50100c50005110043c01403514044000c2403200c18003c201a603484001c000e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 399595431 1250 399594181 399594211
    0x91009050f060f040210170a0c0507120e0a0918020910150804230a06050703090c0e0708090d0c0f0c03050a0b01081903050405040507050c0a051014070215 68
    0x1c103031601d0800c0407903c2000070710040040c001140340c101d40d5510f0740e520610304400002c038514a13880d84c0b000060181c5034081e80d202240d11500c0e00030700c00d0b51081c0b5001101c000c62180201405002103445c000b94034030554200c3d202040803006482803006582102038411f182c0c08041d801c1c00f001c54405014916009042080083c260025160784040c10319a541e60214500300791070084107102250302c8480c2000c9a2048540308001c0c005000070b440f0b6042440800c543e1503c203000d0700104520440a000c01c8810b21000c54240246020140204410f81d0b03103d8060f0741c0c210070162103040000c030708000100311003505004654102c3c00347c09424015080190704954a544052800603010401c440302c41c5480010413501e181070000d10920042c104010b900c080340b0366030052051259004180c0b207981d0f560007141c14588901c05890100181c08100da41c03005007400c000e980d5200c0c0b030a200d00100d040c0840701c40c0034041d22081038051107480e0000e0078269100ea001c40d440d00340c000c2c10303c05e800e03943c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 399596681 1250 399595431 399595453
    0xc0909140a0f150b090a151b1b17060106080c031b09040513031107080d03180c0f08070b16020108040501110a0c0201120509060c03090109020604090b130509100905 72
    0x2c46000f500900840026035592540704091203a49000c66000e225030407101d000c1d13581803580102034070758203080c0141c071002100818600900400c881404400c01c0a90a0002180e0304000c1006800b060588504665080e039070766100f103a806508031201c80d603000050011078141564108045400140c1000c0740d03082901003004541203840483c0c2d006002c141202c418020716800c142d2502ea078400020142c4501808c10703401c40c0d5907481b134070811820103a070b03079030070015164801d83c00d03c00003a4803000c0c50445a694483e1540b04050794004c0742c005000c1e410000602c3c0b1040d070704071402d13070320009518041c40c201038006440c10305004000381c600b9500c60070b15503403001024004240c9900d030f6844040e01b00c813940c0001003542140d81c00418042e82307400c081c090303170b0140029156400309419010b16039a603500c0305c956014081e48203000750003a60125004c034030b6a0040e0031981c043d0100391307040404902d9a9841d0816603900b91280d080d5504056000ea161030f20071b801002540d070254044031400109 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 399597931 1250 399596681 399596711
    0x5100c12050706050702010903020c13061a04060206010b0c0a08090418080309070e191515050d050606090904030f0516050d110609070e040f06050a0c0909140a0f 71
    0x204400e900008070001030b07400401c0002d1082c550411020710003042801d0302542e010f5135402001e0201445000d211500001e486090b0700014003400f00e46130406003084010101c918240c1041c001c840160081000100d00341040d0f4060340c070b01c040200b0050022481c55102c03000c0561240d0300e4650016280d404181d00e01100261940c8641d200e5041e95640e8030303105807054105820394101400342c19043c0103015001c509074901d0030140c02010b100145400040d40c0a11b5111200c1c0c3c808144154810b41d00b40880d50013502502006040c0c04d014001503542c10100b050920607400d606074002d5481d00403038082403040110205c8240c2508010303182580040d00454445254901298a50f014205010040b40e0001003440c001071104000c041908101041c65100e0480740038103103030003403502d00207402c7c46801c0d034542c030b40160041010046c504020a002020300015139104000c20011b400018500c80c281c401c0441180e4508411200c0341c40d00744030030010f000d1000c014681151528100041e040c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 399599181 1250 399597931 399597953
    0xe012a17161209051b180c130806090a0c060e03031e480307030e1305040605040309060f0906050702120718111602040f0f0e0705130203010f05100c 65
    0x10069004060b02c0030034900905e0350a1011a80b05c0c010104003241c0c0903220007292041d0317000040604441c4e12044440c00c0030178083d080740e104a400384180414401c481c0c002240000c2200c2c020026000482c0d11000c042d6001e6034a80951a0107600800050b00c4030310303141a00722061a840c0705400c0c41d02c90b807600300f070340f06240380404840c40ca4100c0160514013001984461501d18024844070480c04d00c01e601d01e501c0f0300410601500b40203480c140e80005d40d0710005070751141444c02500308090300381420040c0c01402c0440b41100031615000020070749038060101d044000b803440d51030310891400c1c000d0032203c640040c1c0c0d0490f00441950720050303541d4001d110352000b41051100c031a410180384071422040c2d820000c0b0440e140b4204006125089400410301e00c9007680503900410780d40092000840240b4003005200407583c40c021494070300500105840301103c1c011940d00718003412000c1074004a100c20710808595000d480ca0030001801c1ca0424041d5000c00350615101c00810350f01c904010318 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 399600431 1250 399599181 399599183
    0x21f020c0a06050c07140109050907051204060203070e031c0311040302030d050a021b060a0c030c0f0804260a120504080d0f110a0f030809010e012a17161209 69
    0x50f101003546080500e04002c440020b2069100c0f1484820b4100c0000c0e000d40014003407140076071002d10004503218022402c46003030400c903010304890391800b0305100300250005e581d44c07400500030007030b1151185000106100c100c00110f40a00a94211040a6004107902440b940d1041c500f40400405a035042c08502040c504d2a00c540350f0b00c1c03100301c00090524a4510350600c3d4200b008a421a0f07645422080e640661081d040041584040f401c0c04e075421466070300c000b0110602254200100418040a0170132208088516002100069410303040f004996113245140e501401068001c0781c1000d07803021540c000c42c24000c0c5481e484104060030302c001e109031b40f40400ca03c16070300311106500003a01c0d507108001c9406803c0500d503030781e980350b44000b40c1a8003404020340c1d0000300d6071606080d40001c1140f0503041c001c0282d0b0000c9101d1810001041c500404113030343c0f41d00310040c013902400007a0f005070900c030401e20143d40c0d000414111466205941800c12003030079900c10300c901032442119a52 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 399601681 1250 399600431 399600437
    0x40e010605090105010906020a1b0312030b0f0103060b070602091c060e120a050a11030d0f090c05040902060d020a0c0b15040f0b0a0501030906090b040b1602010207021f020c0a06 78
    0x90901c024880c5400c4181d004a0412440c8039040080e41d9010403001000d60740400a954420101c031001081115140c0014106032009203100070810b42650101c02030a01c15200040d41e02a1500107504554041c86049030702c800030484daa000071141e40c018000540c0023441e4162280040414002041c1604070444d41035079260b40c1c03000849410005000252170f1741542e14039005902c00020b145004450345041800071010070303141f0381d01061069550a00080c2d00c10464880c0301c002c1c02c40a481c2c440010360300c01c0c468080205060034903010340c2150503005085945844c0381c420703810b40250302000d1081c04000b102c1001500254604c1d56250041d51446641501c001e907440c2041f007210103680698140d40d1428604803d141c41b1115030700100d0307009007400038903400a424660068000030324003c10503080e8008000400010441c090301820521541c24200d0fa020501a4201d00c074403030001e580085409210001010f5121080c0740c648000c1c41680c10501c175030300c040349002a4540104004c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 399602931 1250 399601681 399601691
    0x91b0414041a0a09200d05030315041a060403120c0b0106090e090a020a060e0103020c030a0504062a110319060507021b0a0509041b080a030314060a0e1302040e01 71
    0x18141070a40030310307000a189007007000032044d0782d40c60014401c05032542c0f005140740c00c908603c0950b02d0f51b180c0c0701a941c111b810f89680b45000c85004d00d41001000c1030f20311840c44c050b5989d10600c81c440325000304600c05000e4a02d840d040d40c81d40711603042c40059001c1006059500400000c4200c40150700034170850704c0b8140701031f007011003450003d04000e0800000d503004811400240e55850420030403100d02e4200141d07140c0e11100100c0c01303032240d844d0300a8940300001c2d50380b00e035603802030060045070060364940e141c14003140e002690001c3e400050b032444603a0000c4440100d80341c8103072a80310400040490b09820380c00c4030411107140c410b00d016076010381c2e10820041129010700c080c1c0c2400c0242c0c03805000c5158208001101041075000307080c0a4008100020b0800c0210191b00342c0e140300c840c2110002c01d84d207070000c5a07034079010541140041d06040b95a81c001c1d41005119000700303002800d4145043c10011041002c010090591400520551042000d601c40d481940c4840d2110000415 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 399604181 1250 399602931 399602963
    0xa2c0606010813051b03012910021b04050a1805060601180302010203040b070309081618060e040204090201210b0906030613140a080f0a0e0306091b041404 68
    0xc4810051100500b001da843e0180b0002d079000c140b0310003484410002442d08402c0138046401040c0400e45568160b00c10f41100e100344100401d550030304d02c0304558011403420a4a030403601d803403c5140e0054007101011100e072142c58641c00960b401200454006070300101011070007100115000180e5203038000e60309101c41c40d644810140a07030307100c07510b9100e130700e61071a0700003503903845a8442c038601d40384c2c0440d4080c1050300c03c15500009180c00c104980d6194690a264080200c05e80f00c0c0c400020b415640703041da100e5080c0550811940e41c082c40340413a40c1c8603000d100142c81e421500701e04101240e5007c284900005524048110302e00360300040700785481051194007031020740614400e6102004010301d440722065000307a601e90044144406030a0340151a2034017480710343c0185640310210340d025a5a0391080980710b01101945d0b11280509200b06064803668262071700c01c1190441c13000030505007000f6000c81150b2038060000903071011540044241c2210a4508460706180451114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 399605431 1250 399604181 399604187
    0x607030f02010f0612080f0c0a03020601060e03070e0c0c070e0c0408011103090a0201140904112a03091002070f120302161404050403021e01050a1a090a2c060601 71
    0xa0340c49562203a040003110300b00305202e45405404c0c880200046030005020400c91703c00401e0314008c0b001242101d03400c1c040e500e030180d00d842c1d003400340200140c4010180b20300351600061004c11104100d0003001d5640754a0420300032070340000c82c0a8034600c00d42d44006000300b0f181c842d0034171811002724105e07100c3e414500080d0035100025404c3c0e20700903091080c05801480803484850241e0f0900700312002e091005040002801000e1845a10600c0c0484292680045000401240c40b150700200b80800000c03c4500b04c0032164101c59017550310500540c4001c1c205107030300640c02009030044422481d55035480c26080f298540102c91100104407160003050340400160402503507074800904003900b0000c00f210404107031104d442c03040b0f03243d00108083c14020b004020080b4040712840b4101844881c40368040d01081e20040b07a80c61814104404050b000c10517000600c500800c5244543c49050114000d005488902e10208901140c841e10510740440d4144030246018041c0c1040e140050000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 399606681 1250 399605431 399605441
    0xf0f010c0209101d0c04050f030f1002030a05130c050112020c0f0a02010306060f141602030d080417090622150f030b04270804050604080102030105041a011211090607030f0201 77
    0x2260000c036100c03d2100710345c0084151025600c00303407205c100719204c0c003001a240004020812100c1c0c0100c0100c42200c1d81c054008512500154030b0070b11a40e101d020002800411110018045661454051246611925010914650498016052129958425041922410040f04684e1000703c0c01021560140035a4000700014106440b00380c1c05444003410281d80c00d0540030807080e00189040c1c0c1c8580e4010010030322500030342298a4004441806080e21805035000d681e40b400400c080100c0a102100301c450408001d80854203100d4400700766440e00880c0c5a48405810b49e802c1d01107641001ca40d41c2e08055103040e44c0e40701c1c00c4031105001400b201c1c00c070f44080d4080c0b03051000f0781500710002c20358800c5d00d03a41800c54412041d17190800b43c69501640d0017455001800040014501d4815000b840c103881048504100f404054086030108180400c0d0080c04240030401644201090340d0040c0700741d04c01d0000c4d03c0e282154002c00103640d03601c241030450100c0d0030304914a0219a091040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 399607931 1250 399606681 399606719
    0x90b0105040e220b010810060f0b071b05181807030807020d1109010b211509040c030609081b0a081b0a1b0e0a02090f0f010c020910 58
    0x80145024280041d020300100000c20420385142c00f250003c109101201c1100c80d00d5820002c40001d0396110074140e0307141c841c1c0000d0308482c241800300100781074010352981c06c110754a895a09242455968078404691040c101030345c4600004000000d01352a81901c002d80c0c2c0301d10040b10340591070070000100350302d40d41e07130740321a03456204030030900010b40300c8021130f5211901150041011610b03450401000c00001c40443d82150219000003604403110000e0300c18030301900340800640215007910703d1070600841d80200110110f003007214080c200012030542050059034160342958680d1602421f40d42d90600440c1c070200001103042c030054240840040089582c80900180c904989845d140c81c02900c0900f003142c244240020008642003100c20042c540c03050070700c00388000700004210309181c544a0200c600d0a40400a210304100303100b200c00d1035000030100403a80b01202d0a2108040901d1641b41c14845c94902c03420250792980d80b442d100d075400701c4980d00d010f41042c0c90b02800391a03010b5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 399609181 1250 399607931 399607937
    0x121a040f1e0201020706031a04060608090106141003090f08040b07060f020720030a0f0b01061e02100506060d140601030b03030a080a0b010c0c080105010509130305090d15060f090b01 80
    0x30751900180e0780414400304550480c60003082174803a504000c441c890447c5d622591040c60000f00003203840c0c1251699100c2d002080003000b1460f5500e5021241c0d03035035401d10b1035014154441605000340258841c5020070300890034044000015518040d80760f11130340003c503950602003084401c0003214050041c0984042c04207504040c1541d07078003550b00b200701300703980d00f0301605c8070013942651010081c10320420782050280d0081b0426040c0020807180038003d42c0c00083c012103103026201e490882c003898020141d030040c641c12500c409402d00814003d0444d42c5e1106c8104822442ca81c02c80c040c4500102071701e40c5680c403a040550002d01100c040030113150091304284844070206802c800d00300d9011010b2400442c0000007800100d907a08545a130080984610090104036000b0543c8494145c4805a6205016488040306041007010050b001000100d0410a42d205401d04040d50310b0a14402c01601e0010f40f00f07014400c054800c0c13508011410160a2810080c0204a00071103600c008207007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 399610431 1250 399609181 399609233
    0xa050412050a02030315061306183c0b0a0302090a0501091802030a0e030310030302010b060913020a0c050d0315050402070c0b0307050706020a0305060306070305010b04121a040f 78
    0x102c00030b9140e000003040706800480c4a00402c5039500c503181140c03012106c0c0103006a4130b58462034003824440314142c1c50400c2c811b1102c4082803400945940c20388552082c540d103c01070400c03218080c80425041c43c40d40d0804416100020300c84c0288014001d860b0301d9450250b1902ca00c80c003070102c110500e40c0704604012510804000007100032009480080c01d01c1c84c00360780c80c0c0da4868100040d08000c5400d50061000000704110198001c1c440d00550b80310340d00038440c08a2540400006020719800d0540c00801c580140c0841c4005074002e01e02501a41850016584640c0b00e140c280490009541c001c40d0f200d024040000b10000c0d45100903004c12079085082c20b9284c0ca526481c0e4225008030030103060b0000201da81da9000d41e06907011300e41e0007442990796030449080140071300b0080e00e51900074801c0394041340c00036000303009141c1070721501100e05003004d26082c000c0801c0c446900042d62140d1004640709014048c400301e0612940c0901200c881c0d5400b41d280c4040c11510784940300c2c5142d1804 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 399611681 1250 399610431 399610447
    0xd05131407060e0d03020102040b18090f09100b03010902090709090e191103120304060902010e1c02091308030a151a0d0c120513030807050702090c07030311030a05041205 75
    0x218850500f029149004214140d00d0140d00a20440e081090702c42c0021a10101d40120728540d80041403007920000c001f500e81380034070310480d40705688000b4103801064070b4240c40030180d4070000300da43c0020004150190a0340100344841c4040c0c40c500001421010240030081090252141107100d52000341000906409a01742d08280c0c0e1380e0041c1440344a0f1101001c0d0f075010480c00619451804003940d4a003045d14150b001406c80300c5080f03000c40d02a21150040745030050000c05905907003020b102c0001450b07420080000801845400135400125542010441c0381f00514404c20300071400080b21540d2401140e1894110341c03081000300c010030450b21203100c1440582d440718a6551003c52807400001e01560314001d03000e03102c0d403aa4504020004007100c032000d001040c50082d00e1703401054076410011145403107010800394106c5451008120700100301c030300600b0198000d02d00000d41050091809081394019203aa099258840b0184421310403c41d0004029080600b0040d24103005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 399612931 1250 399611681 399611687
    0xa0501020c01210e0d03060e070518040b01030e2a03070302060415031b030506040501060311040b0702130c091e06090501110c040204081b0d020303041502030d0513140706 75
    0x200e8041d0060305000000b400009405504400c1300c080e2442c003030b15032240c1e021500400070440e900c0703039441001e180e00215504078019005ca0301d001e0031660755003452048020078480034000c103605140c1095507039005101d8402003401801d40c40f1511000c40900c1c2007060070a00380f81c0607105001403290f040718508000594420b42102c080315148004003e0b034820584064004220901040178015108240c0078499507150340603a01c200f40c01c076020003a50362034040841c11a07044038040e920040d400c1101780649408900a40000b520041c150f050501c0d00956000c2070300c070000380010104141e07540601c40c0c4c1c811940c0440001c403a400d0f02c09070b607918054005000700c0ca24440c450500c60800182d424880c02400443c68400c0d02400c2903559958680040b9540c08840c050440004100d0300500910718044600490b0786070020700450520f402c2c0903402c80d5200342d00b911201503100400913802d11111600441744a58281440c02a400e03d040c10014010040321110245d1274105081c24402190 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 399614181 1250 399612931 399612947
    0x50f060301051018031a0a1a0f0103020c03130e04030807030216140a170306030c0402070507031707120903060b0105090108070e0102150a0507021e061504060e0f060a0501020c01 78
    0x483e407424001d45010400744485540301030f0030280015280c2107000e50b2201e400f01d5214041e840314001088070b00100303804607141c2801d4103800395000724014040d1540c0d601c02c3c1c0151044040070341c1980e1401d203c030300b03880c034800e0301552101903801e240c10100414180c02c8085d4544c4580b00341030075032903d1042c9400748855070010000800952240b6441180d422003008552500f80d4061310360340c00440982c2c034007802508110b419038842e214010b08000c1d10700301802501c84582e0303c00000d04280d41103584940344404030341719800107003a090100c40003142d010f40708140701010700c0d1240c50307030b440c10740c1411001e030780165030a141488420800d54034140d90000c104c56120103145400c503408910200103d040c164015075100050490f03000b40500325005c0e0b8062406151290211030004a40c01c4180426094072001303440300c4e030480b000040745071400341001c1818000c010300000f99507441d41600a40c0d03400540d44042c5c00408141004150304180004201810702400240b84040d485070000301022 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 399615431 1250 399614181 399614209
    0x5030105061909021b030d06030c05100203030c0d0216030504051c050613080d2408120f0a09050603040501050f28270819090b04060f0c05070f050f06030105 69
    0xf50f0f00241c4d06550306407541d8180341703541d54002901c1c0d0b0742c0303820500c0340301500c1d1902040d0b5414250040026035440e100000302d12805103900a58103540daa0410b0b498180c00210030101095020403640100c0240001030740890ba20980381c49403118180f5050180100c84031400040302e140b08125040800c1c0001600b603408074100c40a03c4001e490341c64052107074020070700181c0585044c242c0c0c030b4003800a070303001285940c00462045600315036070b100b5041d543c403615940070840242c2081008180c840f144002e202d000c00c1418142641076841002c122540e008407403c3e01c50707035900d01c02d100e00c88800441e015041007001680d8400070046500c0c81240b910350740701c884201c40c0e603002012800d04600109226075000f0140e071003c0380d05e01c0d0400300b02a40c0018100da0842c240d4130f82200d5070394000d203a2b0381c00b550500e120040c20b25003484403d481c140240c6082105110f0304c0c010350f85c0000c07001c00025010303008040d031460003e4039210604c4001c050361280d01d403140301c051005000c1500d41c2d01c503101c0c2e20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 399616681 1250 399615431 399615449
    0x3020a200a0b0a0605040f02090619020708120a0815090106030207060b0301090f0203160e06060306040912051306080906060f060c071211030a030905191707050301050619 75
    0x4180590140c92034112503910040819001008200b800d0401c1d50200080710303003d0394240203030400360003800200d100f20b0400d10360265041c011220701651001d02d41c841e00750307a401100c0d03050f6143c004941ca0540ca0a0070f48400c682c0000d040300d19154441205a00001c4440c0700499080c001d500045417a40c05000e92000c056005c200c400c14090641c0001c42d060746d014008020303907101d50504214500e0160b00a82c000d115201c0390064481d51802d103101203c00f07540c103405290301c2d500204613090f0f10103031100354800d4880f880940450b50341800d80120046540700c1550795007010541084072198ad038021820b000c045420401c2d0030401041c420b601c01c00490b0524032051820001442c0e40c019540d20030600c1c442c8010100d4026110191702c0300b818081d541250001c140ca0003010790720000040002c00150a203c82081107043c0300c0c4202e000f03c0f400702d8000042a40702c034030700b01c2c0050007086c1b0f543c1c0992243c00d00b004942828460315400c0001900c0c0e01d20090895142d4101059851042c2c20303903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 399617931 1250 399616681 399616727
    0x90f0f1409070b0f13080c191a031b1914040303020c040e150c0a081b071113090503040314070503120703120f090501050a0c020a0b040219080a0506010603020a 70
    0x540b420362000c9620b50440c0743d12505c0515100c034801d42e0b4450760010340d0343c001c82642003c3c01244820300d101c2c0c02180c2e0055604141030a03c0709440190f90005490040244480c0c150245002280302c0544001400e003041c100701d403001700d0310040a51080180c441c80000c0208400d10209a001c2582401c1903c1660045192a003400d17032540b4040c07034130010a00e815801814070a0105c40c80d0300030078240140d503071440d1a03611400030034041c50308001c4c1c10004500301000f2078000207004601000d98010014282c1c0a030300d45080303200003a00c1c10041700b100c0e950400a404c1c81041509112644401d6882e0001d1400c80d080902096844081d0340034110081c901007482000c041c480d111808009007900e206200f1407010030fa40001508079504c007100d05500b86400203150407100e00c1017201c0e580c415401401000342035161505110005402070b6000021852516a044005d204003030003411010010030340000207040c440e00705101a000081098010020300008540c440703204420110f4810004403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 399619181 1250 399617931 399617947
    0x20c0904050a060207031805010306230d0606060314101203111c120b011e0e0a051810150503040b0901140403020d0e090105060d02090a090f0f1409070b 67
    0x3103040b4001800030300c2540001800d40c20541c0c0051256280042c406125000c035480750b0056054580500409807030f52030380f81303628407004a0f031000c0054460028064020104036a1218425104c00b604101c0100f074880404080710003e000d24154400401e66000c400c3c2400e03da54243c0c446003081003c0c080010004134103466a5040c40b803510081d00d880e00d51000801b174040064021010082100102882c3c5500c50070154040c890100303c211000000080d080303001203064441900d803015142c0c00c4611a100401d040c3c5070b600c40c954021038410545400c92810540c00c101413070f4a0f420040b0404040d07842407160541102c00d80b500180d026141e25181e9407103d04c21401071a44041d144c8281c400c2005002c04d068022415080480055807041102c100c08424486409000c0c440c0a8020307a0421025900c0116507010340554000106000c0c0c035180d945107034506503250341518010319591044095103110b481c1c400c8048071152021108101d2800c0091a40c40769042c0c0b003100d0008500040d0b5035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 399620431 1250 399619181 399619183
    0x9011409130908120a150e1b0309010609050c03150a1a03041a1519081e0c03030a05031f0506070609030207121a0f1909020f04230f0601020c090405 65
    0x70f20859119900310501d444c0811070000a4243d529222006040484c0d000c6459a105a0454815000c4154030172a0011500e805070301544000c0c510ac440355a1400d000c50201458040c460280040300c10b416140e007018800040304000d03074001584030349034113002000401c1030301c601099400d42c0380c0340d01916595941404094200f00450107000b00c21954201701a5011400c44480c1020090b504840410028490700000c0e403428010958580e02190844020700e07006030009401c0c1017204e0540710849a0080400d285d0f0300512150300c04074101000f044503050241e1703210502200c02030076a2000a10b4800802c0381480381c608050f10345622010383d201854020070404005011503a0303180c600c000c440c10904124820650485e100c0742d94a40481c40422241c1d00c114044e1011201a01c00d4030303140070851004009601040341c0040c01d1000610071a40c41c1d10074035040398000d4071440c0710703003003805038031449044001c001e809204400010310000b0399001420350906901615042c107542c807541411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 399621681 1250 399620431 399620437
    0x418060b0f1809010f061a071703071e020114040f0c0f120b060406150507060e07060c0b060301090b01140402040314030901090b070b0705030a0207050f0309011409130908 75
    0x72508150002290071002d00d00041841c807030980c01008112019080d94000c0070750f8501d1180c04140140c10010f40210368882d0f0062040510482d01c1344400041e9104140481d042142d1100205620030384038002e07050b107404280a2580144020000c05031008001002d046e4090409001c1e1182d01c07403200308004140000c00c000d03008140c0b01c426660785c0c03005c62048002418008032400c550400105015003442d010700c101f07480041c81009140844042e0440b12504048009c0e05d01e5920744458809100b021710200000e0903460b81c0780c1e500440a42000d1101003005001940240c0c9040ca1f81e0001c120801c1015041d10040b50345500c140180100090207406141c00240c10b20089445c805c44018000009000c030b04002e80b29600b42c10355401114066014611000d00001c1003440040c2099200700015030741b0803c0c000f0300500b440384035224940780010044407030722280c2c40000c801c0055a04001100e050640100d8240d10700000f5402203040c1014001d00c804204c0e40399139451040098132826 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 399622931 1250 399621681 399621709
    0xf14061c06140f060703140d05010f091d0616030f05010b030907050904031b0215070302070305010b0a32060d02030a06140609010f0210020a020c0f0418060b 69
    0x50160050044080d420040000b403040781d498a002144451003030403c4401c071401c4250060015090800035281034034005603134600d20001c00010030052030a481c052141501030400d25078180850b0f030510715003808455406901030b605112004056078805400200300d503000c03010300071782c40c00d04000c0641500a0086441100c2945013800000b25120050101171849269200103c40000d81e035134051003035410050300d0240008070144001c0c50802090425001458405442280e600d5034000c2452120b81180e030b03040b00103070401d045c2003043c4803007401036030194102100e0401c0344130314100c864030141118100c0c091821400040300e0190304c0141408807440340021300728a070340340e14032038145000b540308480c000c001c5441d00d4008600c203542c0784154100c0050181c10140b03008010300040d0b40034130a110000045102d45c40c0a001e0f00c4070a400903000407048d40d00186a040a41e008100d180d140d01148940030f9440d140c1002c40240b500c000050405412080004400004101080441c000e0080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 399624181 1250 399622931 399622957
    0x1308040f081f14010303030207020f09010305010b0906040e0705010c05031e120f041e171c0b1c30080402190b0a11030904061409010803040f1406 64
    0x180008141001003410000e00700d1009001251800c000314001c122542c07907142e04a9503d01c1c100503c0040e01a40c001c198090004200b040d071142300c04001951a03030260400c0783c0d070b079444038680003650820b2000c40750020800c482c00e0005200d060b00e0141d0b14403182c8602030400a80752006024041c0a1040305c140c0c0c802d010318103a519658010312411507108061540e010548180051440f041605a607405070f035100e681c18040340540c034850b20641060160503202d60b240c03124440d21b4015104020a0450a0b5130320682002c030340c541100c0121910704840d1030082860900060001030003400c124095503000c1c0301d188080c00c2c02d0320300c42844c1c01040c0e405280c160040f070101705040e40010482d42b15510841e4480c00c00c10341455050903481c180e100b0f03a0080c03c0f003442140ca8503401510b900e203001c5041d20480c0d05040d100710006090fa8042e074050700c4100300c804054204e5007400011030340900b400900440c0b40529185c140d000c3d10045114418040b4030740c01c6600200e5032070340106c5180f403660b12 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 399625431 1250 399624181 399624209
    0x1009030b1302213406121a06033d15020c030c01081e0109020918040f1e021801090c031a04050402060c1005040303050a02030f130804 59
    0x4007284504655070310182d00c10200c203110400000401e510340520048400080c241e081c24045a852030981000300c454034003411303140e20f0544c0003103003400c0303800809003955000d145c12800251403003120b02800d490030745503030a0503c1d000541c0701d1000710b0760800100c0c41e1070041000c0a0981da10201140b0062200c94014100020f140440c0c4008a0054030f0118a121842c0c18606070706070381d2401c003c0c0071246c060304281c60041241d8050b503845544100d400300c8110350910700c0d5600e1700c80c203042608002081a030100d9030104500700090003644404540101c04070710700300380e00d80c1180600c81e104c0060025100740c1c0d54080d4400007880452803250301800b811012a0403070480c26642e6002d00990200381c0c6002c4494a40070b229001e07113103541300190b0140460b01394400c04c0c0000b0f030074024003da0708008100002904140e04018a072010a4070110004290a0614008041e0741002d418689002d0041c0b00384481d40200c00d0200350031480d84c1100e9003110307a0515000380540107581c02004030060031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 399626681 1250 399625431 399625441
    0x109080c010e011d210c10060e060108040b01180f09200303090d03050c0a0f0b0115090b120711061e100303140310050d110418111009030b 61
    0x5411440d900c110442c02840380d4400020714a00307000c3c0384080100e465214200700c01071404443c455400b101282c00c1d0075442c150000b002140303060141152131100d0703581c0d2103040040c140b13801c1416070400c90901e000d02c102e04080e21a488003d006000751200380707260b1421840a490716a00810345204c0500301030000d2402801c003596001d0361360400449802404041030303c1d07842e0100071140750b0940200b0000b04014a42c50481c0ca60b00007510080701840340c00043c50200c0c058159421040d07104c0c1c0751580f1a50704044084407021076400015090000c118002e003c000e807818162040813401015152080d600d4802c11108440b4ac000029614001d00090103011403040b4003480b86a5091404510b15417280c05010000004c244000740002e00d650201c01c40000500000b19007160b039064080020a450f800000e41c44454034004442c103401401600541d42024003c3d82003201074840d180b00e40d1211621980c000e00324038003c0c1c5101ea0140010340c103c441c01210a180139540040481c15107180c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 399627931 1250 399626681 399626683
    0x2130609090312050f040b0a0b1513060f0503060105040e070507140c100e1c020d12080105040506030a0f060507030204180906140403140a300b031b0906030109080c 72
    0x500c0300414036031420100012030b01e40341700d08084c3c001d0750b04c20b141740c00a5680f411414000c041c0020002c1c1d01c540094a50314004800d00c0c06010880d042540c1c030380b0050710381540070385031130052451942440014410040180e070481c040e6001c1b1910507101410135640e00704100c0b00d61080c0900100041c15510f050030b60004001048418000305030781d07031003070007402c058183c0310003201141580d404403d1000d22209951032030220f64a01e07101400040c80e4984507590100d8603000c04007410002032141004101502e03260203960380000054026066052092b100d44002192924000c2c28072030711000401c05562207541203c0040094140803100a03030004000301c050926000d055820504104a440c0c80b08100f01c0d0700b134012075054907102481690790000603140c0d0465030902c400d101d42d641190342c190000041c1100300c00185c2c6036a00c001d405601190044400c05142c081c002d50280c1007109000c03116003107240003401d040b2040409aa03480c80040d001d460301440050070800040350280d0002d0b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 399629181 1250 399627931 399627947
    0x15050d021e210109060e01031104110d02121302090a050c0903011a13020408030d0c200c033304020d061815020a09050f010207030b090d180e04021306090903 69
    0x2c10560362075056607855902030152a02030040c128000141001040007030f03411002012a4407000c0e00c081b540b02c0c0e158420010030b400a036104401d042d00014261115602d0008042e0300c01c01e40b8940303010030b40c603a0700446d159000013090724015556071000b041c0340740381c0d100540f12050384c014020f0000e942030201c4404911040c1541034000c510010b40d035072030807009000340e4069942507401542404400001040a080c1898042d0284145668950201558400301c4540d00c85c03460003c000c031107106800c1c14584040307a2076860013030551038170340c03d034030301289030184084404401c069405480d01e000298151204100c014a150f01c8c3c00f90110074128034a41448456014900d41c0c8814000004a00180e00c070314148040010712042080c0035a1a0054030241c41c418188104c4200503200da807000f4116409840e4805654801404550205d0344a00c030328220807001d58028400c01d21b44128094041d2000d440284990b0086582e1180615541c0c00a4001c01e07100700207007d820700600b0f0241a000e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 399630431 1250 399629181 399629227
    0xc03031d0303012c01052803171804050907060e12010e070503060a06060905010c1e0b06040c0908060c0307020a0611041503050603071e0902030103081315050d021e 72
    0x121512103116000d011340c0d03400b80e040700d40281014012080c0c4204c4080c02450078550100d01d00940300006c401304102940e613007150403030081c2c844d0b80c0d1111424500040d47c150030301c0a109600340410401040d501003640c10403103030b050810301019040d08001580a104141202e406586451a0b0412a8400250707150450f2026000d903000d40d01d079400400140d8009014000118542380c0c02006103501c05c80a03032140a00442c0900134141500b0300a13603419181c01c1c0d095840340111424401186014400c0341c1c0a06100d0078a64a0303507240c10001c1d600d03002c0091107049003003004800104c00e64002c0c018507118944c0b0020802103174085c00802080d58005001d480e0700024050a40003040e80680700d183d0003441d00600508650f403511440d441c0740b800c10740701e07194050665140000c101c0041d0000d180031310f00c10450680c031061074400100520380180d12440d400c29200800140c2c141d0401c04469000c9514076000da82c801c162008108035003941b111200f20200b00085c035807041214440c060b5009 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 399631681 1250 399630431 399630479
    0xf0a0806030a1a0c0c03160204180507090902030f03030a0c090905011d04050115090603060e0d050f030c04030c030b06120606010f030213151d010503070c03031d030301 74
    0x3500e541041c140e5030340002100400041401c43d03410700301074216044642c0b000100e8655031400305080e031401d041d908200f402904050a10100c0300461a1a025403014803c035002c1801c42420a40c0b04c099480c0b04074402c42c1d802607507d1800741d0075900d007840303900b4180c1d0410088a41e01d090054510b001010500421000902040310100f0622500d000d0740e8120780307103031420403100802c00c00c20781034207080a0400c40342503585100c4489801c50140c1c1640040c1142c9200140715455800e2540646a881ea20100b003074000002c60014903401405460b5019600c0c0940b980b02e50310104d48484d07130711458001400340b044a50000080048444c0783e10302c200c0056807900c0e0105e006000195031208103582440c007050389a280b10100318071030342c041c010300000c2c03211401c41e5650703ca00f01c9418a14500d50900010074440c2006140720200655460b403000a01c2c0891440c50940b40062001038508001010541c45e00c1410481042e03180f03002510b0900035054a0f40ca507595541c8032000310510040c01c487e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 399632931 1250 399631681 399631697
    0x1b030d0207140111030403051215090c04060207120503070b0a09020306240a03051b0105270109080604081605031306200109021003050c0c06130309090903091809080f0a 74
    0x350b613041c5000d0368001c80d455140c460070300e00303042c0c50f00c005200020441c1d110008070000155a594030164100c0c0614171274003900e507131181060002800d0000e0743d000440250740c1c5005d804d000460001c204e40807680c01c20300818290300c42a141c8000b0b0044100003a5141c4524400e01142c038600d500d60f5102e641ca41780000c03044010b10400e00031003074118030001d88581c0145144520b800c50b41d002c2c01100480c140762080c600411040d864410381d00e5a00f40900341c0110f40c042040c10f50700a05000c001c4e00007040282120719003565007001c3c601c6041181e0643d001c4483c0417900304041041a0b03441e072140b04c0241403803d41c446c00001c2c2445c8211032400c580321134080c4104100301d410f200d06503c072074025041040c00840d0640c140d003c0d0002510351a002081081090651101031240ca4098402c012844250440c07a003001400c190b141e811182c0d14614085117100000e400402001c11504242900316020500307600c1e00004210b600c030080d00e050381c00101070801840f09001024002030549420031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 399634181 1250 399632931 399632951
    0x90b04032001080609010902030714120103291303050c010c08150d0302061b0c1b1504120f020406050d080304020909191b030f0f0c080d02031b030d02071401 69
    0xf818400607140603030000000001031000d02102d030011a4000d81b0b9040007120004040503804999004030f100843e090315800c0188204049000322f0040352003841d1248440282002c5180300f030b460042c1078110300c075581c00201c0c81010701a00c281c81216001d0b000820007000d07402c40141c286403040f50b01264655481900c44401c0c642410301c81d190b241c0541c02814196102c405035017001c400002c044882e0030051014406035002040384d406208080c000e00c1c0e400d44813440c1417000303a07029041861109002844140001c0f001c9094171303400301c0d030070001036200c03000c1c5400400c1c010041030700600e17049511900c0c1a01031010220040d40140d200366080038440d914142d0054403201c2d8506c00c1604241c1070f01c07441001c01c22005001d800141001c5d19954441d170703030f036440103650382003d0f004503600b80c040b0314104117000322118180d005204202c06403030b01054030350300251240705d410444603001c0007880f00d0352840c3d038007003041da10340c2111940115030310304450500c081b0840e40421040b500d5030a01e05000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 399635431 1250 399634181 399634187
    0xe0a060501051c0b0d020411070b07020109030807120f0f0915110412051032190f02041205070512010b06040b0306040f14070908060105100f090b04032001 68
    0x141e00c000d2802e00e2205030000000d100d1004d0610849a680c0c00304040302100e0141e07170307644280c500121180b03000039926039407441d08900e9840300074009019a45002c403600d0100341c10100c0990301c912589865040034904a210740c001b40100c200e800a018a00169020240300c00d074409102180108462908003245c0c141c40700503610048514200540280400c1047d04203003610440d00703521a8041c0e80c900340c204081a401c607049840e6090500769281085400d0141c818201062446800304245803460007401281c042c00640d254001029660070344000c0944c06030b07060703c1c050201141c9180240c80300d410204c0c2d40d403669008040c4100f02d0000350811080051103100700c01000940058100b0749888441152034000038041c0d5085074403501c046041c051103210341d40c0d00d1003414441c46a681072a4000a0a500068101900662101f8011b0029a4401c4c101170a41601442c0c5802c880444e40e4040305d030541c041d0702c40c25100750040381c04410088045412505526002c40510403121140011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 399636681 1250 399635431 399635437
    0xa03270305070501080405070e0f0a0605100e0f060912060702010501150e0d060e0102030a0e1e060c0711060301080318010509010e0405150604031b060c050303070f02070f0e0a06050105 81
    0x10029407080b0420400d9500414000754041d01500a58400ca80c1d2032a550480110443d407030004032545c01d04003c0444118414080a4007040c1c501189400d1041805008880294070091107004400361038041d503a035800407200c40c9040038010034036080007a440e0395030303a0105980f1000594200f00c0003068181400c510070144019990f51120f6503044803092290359500094203588807900e0b02295450000c2c00d00066010ba9402c0100060000b94501c202e41080603600076250a02000c03020307881a40400034120b40c000b48071004140d0fa41c1d40b1841e10071118080600360f0b43c3c01c442d0110000038654000f1014043c0700c40d1200c4a408030300c601800444291003110301d101d0110340707003046030800c600305940031a0780300d241e00340c10f40c0ca084081000a081ca400c150f00803148650718010f41d290b80030107444044020b2595062000130340d1560b13a10203481c0d010040103d800c01a150403844951407080083d00018154a000703440940e4651a10250f0301e00c0440320304c01814146507000036294851030032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 399637931 1250 399636681 399636683
    0xd080d050a1b110304091103041406150f120d261b070510020f0a02010b060f19090306050a050426041403120d05071b080706020901110a032703 63
    0x201c2c866402e0b211a043c0d8100d0080e50940b03400d880309202c007007950074042c03061001b980031140315a601c0c1d14140c81e008119000b503034040e0b10300d0381002042c080b0060306611800d80003c000c071003925050030080042091100c99018010aa2082440441c506604905e0f000000c5c1d00840b99410100a059030640307410701c094803d05042c12403120210708082e40500500120f622460a503a602c20002c01d07480241d801c90340760200e000d080047d4084903035070244174000020009a841e00e061071041d60400da000d00522024400c00b62000e00401d02040c801d01c003c501441e4410710410090600301158402400c003101c0071140420241c070f00c0805103c1e2142c2d0031130902c026030161407a180c180150449004081d0f13105540510956020381d0025200e40d020700200084650300050500c2c0c110001410007442c203c051142040410340b4078003060480044900080e040000580c0e00c0c03030303007070012640035401d8100c1081da4000c3e42e0981003010340c800440c5011000118100380300203843d8140003007800003440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 399639181 1250 399637931 399637961
    0xb090705060d05070c0614012c070e0102030c01180c060e13180b0a200f0a0c0c0902160308070e180405070506070c06020723010e0f0d080d050a 63
    0x4114120050103030029540a4a02e1800d01402c5d80b1741d55605003134072141802081142074010041c841441e11405040e0500c5e00c2d1a180d01d400c0304d480c00c81c000c00d6000a489001008405065021941d000f08129800c43d082403008211040c050141511a00700040c0300b02e500551034a00042d220340300f0706072201016402003941c003d811150816000502581c44044c0e100c2d0424440c44010a00c51003607144104c6003403801180074101440c0d4072010010003003400c5207a0ce02403094400360440d620a440081d041401c0100c03600c90a030402450308070742540100c00039800005c64041005024110500700d5200ea111004517072a550020745040b40c0c80b0a240f0742140900325038112405805140d5508079005d070080c2c40a41c2e4807030700804e080f54840b00c0300b910f42510981d02041016410800d02000f4844051030300ba415515080841500300300c3d146207410413400d4907100743d0702c3d503408170b800032941d01c02400c24148440614080c5130f69000681c404110030318060001e0154088c90040e0342002d0b00802c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 399640287 1106 399639181 399639187
    0x90905011d16090f0b0603010b0c10021c05040f0203160f0b16030f02010e030a0c0b0109090b0103081612082205030d021c110301030b09070506 63
    0x44408525481034030502c803200b1101440200b5201207210100e60004442d01000281070188211913014400000008900d19100c004102c42441501500d01c00010358107a20228014500c00540ca07012107446d5052200311640440d0b401489403000b66101030a0390040f9142039114074141510315202c039410303c0720010170603d540c010308072955140d26103422142003400084030b016000b0103100001d40fa0704041d034000e4214900e18011001104e844485580d0010043c5a0390181560b64860000001ca240301013800707028aa1034204045401c0c0383d187d41c3d9401c00d103520021581c2280c61287c2003020000d032261104500c500c010356542c4d8403505020711104141c21840100c12403400000e080b250010714003000f90b4402d942c0745040180c507860541e4200022030072280f01c9a07042443d0a114466981840010358140d030300401a04426680f485203165454101d405038a501500174 = true := by decide +kernel

theorem cover : BRFrame.Cov 399460431 399640287 := by
  have h0 := BRFrame.cov_init 399460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 399460431 ≤ n) (h2 : n < 399640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
