-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2135
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:44:48.846154+00:00
-- url     : https://prove2.me/submissions/9dc926a3-b95e-4fdf-a5e6-4d70dcb248b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 383812949 ≤ n < 383992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 383814199 1250 383812949 383812963
    0x703060e100e2512080906160c061b020a03080306041b020d031508070326030f190e0c04020c0109060c090f08060c09120a0c0b0301050a080c090705090d050105010e01090507020a0302 80
    0x3c1d1134204001a1251160347e1201220940c50003c0100c218a880d5801d0030555041e241c01984003065140d4a6000c804600c0d0542448065004060541403030031540c4004413a0000750489820545440c9400840b01d41c061205418024a60082101001c6084002e054401c60030b1280e44500c007000f41442034a40c04200102902e0b00185140007410480c00c035070081c104407950031a0303140300200c180000c00c6d003184000350081d11a002d4801044031500440c000f111100e01c806600b0b0b600c283c000941381d04254001e4a50081c000b400020044d02503148c0d0003c1c0c4018010400010304942c2c0144403540030500e824000c2d01140004022034607054070380d0350582c400c400b4142d1080280c030a4900304100208000c03075090340d0200748512200c0c0e881540080c0c81d08207004481c440c0081ca140420311102c0000c8800701c810303000340221074603105c030300701070b03032190b10a22256410050004500e000700300e003400389900034403d10004000c10f624201a0804645000c0c000104540141c82d0300400300c1d600203661 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 383815449 1250 383814199 383814203
    0x160f060305091501090204030308160c141e063711090310141303080f0606070c0807030201022109010e04150806160305090703060e100e2512 62
    0x1d05440304000e9030319080a41e40c0300c1c8505070460f400407a0043c842d40140c02103d100351203104154861034640e044440b140e6002c613000404480080d0081800b80f08103007400c0041d84180d51007100f1942856401090000a002140d40304c1000d018080807000907071003800c00400c01d240007803240020380d00407241400c248000b0700d40d00d174011204000b05c00c100f2640385140c018204d440d00802c490f141800740c852003040ca0044105000000d220323a8240703080909007941503854034026650044d00d05150304c4080d020681100080c458a00000c40c0d469901004e07052590041180c24918800245840140343d8103400018108481c40c2c0400b40d41c00c01c0d1a0420030900b0310a00301003240f008036004102090211010b070045903400103980d44d0102d00385019140c001115031000020507030a4040d20015194030030b00c1d0380084001c102188640e032100a8507400d0a0555070803811103940d0005a40c8248603181e6507800000c00c0c50143c40358030110000c841030600c01c0f10855071421410004041c01c5442c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 383816699 1250 383815449 383815451
    0x30304030509010e0a1e09050c04050409060209060c15070903080f0912010f020d050114090f1305070303080717071b0212010c1107170a0204020c010e0d050a02160f0603 74
    0x91400d0fa03015002c18140b03240040c0c6410403c44ea11008008614038040e00c00503100d040070408500040309001d0b591103420100506032074246400203100080c10000b10540d41290700303018800d0340b0340c0d841c0c0013000400e0400300141400d64101d1481c01911101500403020302919480800c002010503041e9205502205113994841c1880d001003880380c80041c068075100d5181000c5142c004d0700c1a0301810340c07803125140802080e0b8845103000c4003801400000307644030140100142030311041d0405d142d80004080410850303481e0315070742d07a458482a90411008501884200b24600794002c08039842004483d0116045080c140c1000e04203030b0001141c0d0411600e1140d01034259101e0f1410040038080365002084034400c0800c0081000c42102d07201c00c070134040c1100014002200c176804440028003071015240e841101c0e400c00000f540102503040055480310303400030400c1028420782007a400c0c80e44030950348464010f40203080c042e021040d82070900307000c003051000c100c81f940c02409880c01410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 383817949 1250 383816699 383816707
    0x607120504050a0c06020f16080a1209030f032105060d08340201021c050f0315130c09080d080604020c0c0913150603020d12200a0212030a020303040305 67
    0x20311a00f001c0f0208400fa00c0440048000252164001100d901042286068590b20014451050b504200f81e104900e42a44100c3c81030001c50160b070150000da09a500b424402d01d5500c3d9600325001d400342c0310660109441c1c40036202448922030441d03003401e0300f54038100010725000c400a0000310003507001800b859000318030000960b507444065001c021004868001091609907249911104002e0403030060140700342d85460001200003010350203180362100c0d0708000349030290b24101d82008200c280d5000c02c03811507540c95110f140c0322031018131581d40c001c0740d90b009800000c0c007030588a500041156000840680f03a05030320110403130700300c0400c45c2c000d031759072115800592401100000855001c4220424444021f0504003200d610700e01c9200c04900b000b081c130b41c10b001180c045110203500050303894049000a84aa54950410706141c01c120850602c1c402620b01c0c02408115a0303255a4020482174003507203045c0c190040c90104540c020b61a005000d44000e4036404003030001018008081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 383819199 1250 383817949 383817953
    0x50105042103030b033301080706030f020d020c010207061505060f0304150c090303030c080c04060e1906090302040b1f1206050d03092603040b0a03090b0c1b0607120504 74
    0x5007004c000504014125a800300104200c9115412010400e0034400a415a400b4003050b010050714101e89510000d070402c0c0e46046410b501408440c500d066109600300708540b5110704510240c0700d6104048001a00c40c002403030700303400321002c1c81c5e0007440515024408020320f590f09401c0300c03005650320030070701c3d141d403500c2c41c140114842e4070452940440c1007040340800b00c0d500280441c101c9000c4d56041c00b9000c00c2c01c8050701c032180103844c4602200d03000c00c41403102900a581044130400003421a0000741d1045079440c40141c0c1c1900850b000035540c02c0c0400a41c5061300404801440446840c04044c88144815441c0d00c00b184030300040c0401c01040401c411910307880f800042c0805001c03924440428600140480ca02d4001d2038100c02c00e007088455080c0040c0d000e440c032000d40c0720045180c10b00306610045c90360822076101e800c1540343c118520020700c801c98007500603d520618181c840000300148902011403200c01840b66001004220507540e02c90004980c20500782d80c00206a10b40b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 383820449 1250 383819199 383819201
    0xe03010e1f09060207060209150a020715050706060e070905040b090112050307050a15061d01090f0b0a09230f0408070606210b1b0d0c051c05060a05010504210303 71
    0x20b80c409041c4903c0850200240f18098000b01003000f01203032203107490b011420f200d030040d000f40e110314030060744100e0080c050b5031800c80b4602d000042c01e042c05414145140d0b2410180c480a0300042c0f101c2c10705105104040f0340003459980600f00c04c540a00800710524040f4180b0f050500c80c984103011036501d418103108061084940c0d19804c141503030610640c3c0e0034041008500d0180180380c05181c040000fa8180000c0311900f8010198101650030f81d1a0500280c06411400660b50304030782d80358102c0381036685521003d8011708810b08003040001c03105501004451002d00c03a000894501c1003040041c000c600d00c1240d2190b40800042d0701d903421030400d90000c10743c50b0000f06c9105410141c245100041445101c8124890b9200301c0d22076a50b6182078210300ca5000c45611103103024001400513482a400015203000b46103421400c00904200d1002141c08240f908100c0a942c2c1c41032005070b090114a000c0908400e007002440c0615003581b801c408002030310751569140c0c849980c4d60403d442 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 383821699 1250 383820449 383820461
    0x903120504140f2404030201082518090608060603100b01050d020c01110a0e131b110f0a030f030b041806090f06050a0b180601051603140406050a0e03010e1f 69
    0x4030041c5010405081c0b80151020703171045c04141c0c04140c01c0000074110309a5503401d10061100c4800122081d20402e8040d80c4580c5203d00c1e20016540852002c03d0500551154100800b4a14020b040c00d091603010b140c00d283d03800c458054074909142c043c8040740d8200e002c542c94002c08000059036034a0040d800790040024001030310301014005414901d030350f800000c20000210445550203840750b01000b450407200b08001000d8440f8201f179403c4401c2c0d0040104a55008607101990145500c9501140c03d01c42100340450124401105090400303915200c2c8000083c0103a90811042100001464601c20400b10080c10300381c1350440d0b202040222941f00a400381d0140050250703040c24401c1d41c02524552150a0003400030703040300e20703040188030500e038024101a100c0c3c500c0c104040301840c480b0f2080031402c0c1c05101c0810401020450070000900041c840c5984c4c4070303280c00b9990401030103650448107207482681411030740000500086070402c10a40602117200e000a030201a66003d080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 383822949 1250 383821699 383821729
    0x50d03020106031505010303020c03071422020a05130602070806010308031f080f1002091f020316060c08060303070c060f200607080f0c09010e130207030903120504140f 74
    0x2000c4c000c24125480ca50011810b9034429020340b0909140702d0705045e03641c0d42d548680400700c200c1741400c0d003160402d0199544207004404102000e44a10210b4000380d90194400343c2c000f440015150840d150607910101c040c14052024280d040e1a02010994900301030101414a0b1000000700e5070b0302e100c0c10410102c0c42d015000c2c411400b90b4415400d03403110151030504009000e51301d98191805018402c4901e0144000c20248a0542011644812820700135040055200421685200c2800811444031061003800003040c2d0003010740380101400c00150210b4060b078014000580002d449200d030788141d40c19031529525421920604880309200c100d0002c04501040455200361000424080c1c8a1026601c50aa50703868030020b6403001d81007140c274034a220b40140701481c195840b622118400000c000c00001d070313010341c001164007280d03c441c100301d0104d400c640c400c02c200488031000e80c1e003c0700756013440da0030145002d2803814980d40208060740b14408001e076082c0b142c0e50b118592030181e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 383824199 1250 383822949 383822963
    0x304050415080f06010303020f0d022109031009150902010503042a06080417030103150f092f09130b060d0803010f0f14132c010911040510050d0302010603 68
    0x11890307150f01500da18081c001030300180522000d03a044160700050000048010341d00800111854002c80da200c207412040c09950f0361410407201300a40d0f020000c10548000102d400602ca20b01480c1040c640403848803441c0509042c01d46000c05030782c11000342c81d8466048201081a041c038100c0100c080c520b0076866600740703025042c000c02c120b540030704203070f1080d88101d8000b441031216403121b80d024002440020071261000c0103101d45a211a04040c40d4612261004140e0788100d40c3d40c0c0641110480d4204e520000480004084041e0342c62080b8410006440b0205a2b0402c04904c8030200d0a0400107130191055802103030341174071048030a1018030342003c04103440b540c54a0321003100f100248280120240c0c8944c010505514038102500305d80b800030000c0070385846c001c161202400103d620304550300040c00d40e04c034080d0291030640c0020441e47d000002c25500c5442c00d820042819400240118501802c20000014001c400c4091782c00031030702c0a001420503d03089024040d540c01c024030794 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 383825449 1250 383824199 383824213
    0x6040f11090307120f02060c122124061804020304030c02150f03070f120e030901021203150d02031e060f060607031d010e0a0f030c0b0408030405041508 67
    0x81011001510a0300000c4040c3e030486952a464100340c030400c25409403a41100484001c01440d00c02d000741042d121a500340d5001032001411340ca0207030080c07040c20440c0350300d0000411000020300c4080e580014501c0742403600030502c0fa0104020552080d000707000712000507403203c02a003203603a101c001040040c010b560303900c0c051030300404c960b86802080380650070362030801c3c65452008003919044550024428115641c24004507003035185203802e0018820340001c00d105031a03041c02980c2e118802d900046548942ca00e00082c40c0c41010402041641814028030142070541c10502070103501c1121000c000c90307100d00001c4c0c2404c600c1b0404010000b0511071241c2c1054010841600c90400043c91000039a40d2600f4450340f031055500040004000e0070f060b0f0060300b102c00355400d10880600d80b40020184101c00b04445000507002401c60304481d0341d08004201d07184115002811010f241542014070308103605940b40581e004403403255484006041800058406040081200c40211110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 383826699 1250 383825449 383825471
    0xa0507020603150906010503070807120605060304061b0e0d142803020c1f0c11030d020303010f0b090108041e0f03030f0b030601060e010513030506071e0309030504030b06040f 77
    0x410000394403030a010348034130700010f100c070760256043e130384560b410b46c54060242d6103080c400c484001100c0761951580da52200c0120f166100d000145118a01ca83c0001908006100078503852a0403400705c201042203001d2080380e0b98a4625190350055404480d941890042c0425039080c1414065800244010346240d0884102104c1003446083d002e5001e4a010030a1107007032100e0590a9030310880e070b88800c00341e00140940300e0344e44c00e003199000c0c11440010501c9040007a08012541162328016407001c4014402510801111001044840e070010b2500322502c0c000b82c034a01000f48094900e00d112040c400203c40390b0003445030360540c00907031202103112500e805001860400b802085061520410815504000070780754143d4100e5154010b2140c040e1004407810703400043c0748a040a480000000090800c004450140720a9103403c068038190b0010a0070218128481508040c24442c80101280d0008100d90a880e00445090340990f00d03d000701f030150140b2101801024a002e5080c40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 383827949 1250 383826699 383826721
    0xe040804083a0806060d0905030f07020f03150f0a020927070e030c0d1104230a05071b080c060f070306080106030203120306190b0d0c170703020a0507020603 69
    0x41001c200d5200d14500b0b10814008410100c0d501051008180400c012400920f842806049009501390022505c6e00c1c5030f40d21142560090b07044c0c0c80c01241301151000071840c1c0800000c5903004107400034520b03201040d0444052410184c130410081407954045200c44202da0101c4402e018090100c3d0280700c4007521280030301000319814000345007500c01045803144602c400c40d001a0009000341400e506880410405029490084900d41c1950180d6240fa40361070040303182d1007a00f0003501c20807007a0703224603982c3d03980014200c4054614003401c0004440d00481d11802c09040844920040b8000d032400c54020b200350015103c05100762002c001c800d0940d886224030a80301d079601803080d240d4509100c0e090307a0103408003e501d508403540301c40b00c0940660185a00c200010140341c00741c0d0148019240480440d0032103440000d0001d000e0000350514014000c2110440c902542a40c032000400610b09202602203000c0640001366511a0b0340710b1070130f4a100c16001060f241e503070b040c0741c0c281103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 383829199 1250 383827949 383827993
    0xf0d0518091303080a020409050f010305060106111c0c0602071209050d021f14030a0219050304030e011211040602060a060803040812030406110f0d0b030f070e04080408 74
    0x251081651a2000c10307401c0c1040703028000e502d0031200c51039000059070107445000008040c0444d040d42800001990034641c01402d001e00c7c403d40b2220f2182d411402d045060100581208041c80000d00855145400c00660782500e000e281c0f614844441076036400710b420750717608040541854008540c0c0c000340040010107510680441c0c9030500d842d0340d240c0500207090b03580c0303002035407001c490002e074400000441e044180c540c02520f000280c48440d840314410355081541e81004050340403d164841c2c2c040e002c042503400c0c00a007016401e500e0b10f41d500421441504000038100301c80b601e0010003404541e00030100c1c10741e5811103030703440d1f03501c8540096868004642c00480c0d6402d007400040e8043c4040115016170342542d010706241800c0e800388080991001c1c1044442a46c0c42c01c00b0700e605980000a0254180324024071a030390300c1140884d03801d4541d0f81001510035004140d000d0901100024958100c85112207004081d0340d85080058460080b540801001d02880e40c4c0e808041e0404440c0c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 383830449 1250 383829199 383829217
    0x4120f08070f06150e01150503060303092e050f03070c0609060f090c170d0c08040801090803060f03060106210e0d0e010224190f060b19030218040c020f0d05 69
    0x211304125076401403104107403001e2288840b01014482181d6010f80b2a400031544034201408603441c19107202d010600d40d113551030341e1040b00c4a06581400c98a04e0001c040c4440c81c0d1076107070140c140308891603001d45d079204c05803640701444160902d0700108800754003c0991150414410030008160248030405003504600495080c05202c10114160300c12100304000b015882c4d00411446036555000e44005501d801c00755240c0100707000005000001f40100494688220b8207a5241d081140c14091524a1078400f944290842401070200540c40490707416841000c4214209410300070311000e00418041c0c020b4107940c020032040116440d04000314042c691030030381c00c45100c90542c0008441d2481501c004ca000c031400d0074007042c03407220008444201140e801c1c600241c0502210160000c8070a10741c424048130300041b40700c0071040d4241e035447d0320305881c03400c0c103600d0000707580e05051a904941e003405118a5540c040d040045108200061001c10703000121401d400800710007400e1b5030850014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 383831699 1250 383830449 383830481
    0x90605090d1103070b1306020406030b0f01020109020108161202030405031902030406080403050a1103130501090902070803011e05100c210f0c05010b10030204030209060604120f08070f06 82
    0x7801c24050700c0342c1a102000d000e190041d50800d0724650b20071198010140102034030740c01025541000c2110740c4024801001c02c0c0d100056034404880600c52039586104650341035925000b40100580d802000040d03100300e04e800d1021003200b560b00c0a80e1404216641c0da028a40702008006c20014008003d02e0005c180101c100000700c210401241c1d01d00c603501440000521400110780028001d5015042c201440d04280c0e01001c2e242c40da9038a0743d000340c22035407403440742c8030410866942c00480940140040110552900141c0d4030792142e28881072140000d20607031500c0144001000c0c44190015000040c82200368030702c100780040c00c11345140020703503403401c24400c40686141c050100ba10040c501e0b1300c4003014462100d80550301080c1150055445540343c0c1c1780000e0725030fa1035442d10b00b80c500c0c6403401600c50f81540184460010002d00150107540f080105003d5842d20780045600f40b54001d0030b07240c58242500d0100ea40703006003007000b0485010203005030b003000410b03044500214003040c0f07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 383832949 1250 383831699 383831713
    0xf121e021815120603030d14060f030303070504140f2808010b0a03020f0414090307050601090b01200304050901090e010b010c030f0e030114070f090902180f0f0409060509 75
    0x1000301c081c840c01d0b0b01e007903544000c00030342d1003c0150f41501c9a0256004042d241045071000b404016105e0114203007143d80c000804000003490907128a600005c070541c02542145404000a44140300c1c900429140106500340e406841d0349400b626812010080d114007400c0203032050702c035003261000c001c180210f42511004650307094140304400309007030003d0015041c180b441d02030001e0b140c0c480e00101c0d080340d180c1c0086062020003084250191815000940d6101c92505089040c040c068101c3c1468906240418030141e80c040d10a4841c521483e00c00204044041030961840c49540d01041c0c0041200000081c50806a803000701800320701c0b40240843c0100c00011921205402e0b0000c0100d011844814000c0d881541e00703507a95000540001004d803209014256080412503d20002070201513140b41d0244d841110740004058200d03084d824454480b41c0400700b91440600e10780141d0801603070010a9a03400886201d140024008100c403604500300140640811102c20200b807182207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 383834199 1250 383832949 383832997
    0x3110609010b0d0305090d0c03080a17091c0c1b17150403030e0a08070f0302012904020304080409020313060605180105060c1c03020a030b100f121e02 66
    0x700a4002c55400200300719624a5183d0302070b5226042104802e8010101e0707000000014244090700b0007840c06400d076070361500b00107880103144014010013070901180c0c40c03061022000b0001141244503443d0489011450107408088544005010002c1c14080720003011841c440d4110307107400192400949507050104107070f0f4060350765412003280344901000c00b40005e80840d200c0d6100304814040802a00c0ca0000c281c5c50740c4040342c000010507030f0142c02c5601240101502407254508d40390301c02040c2c02d50180c08103440320200340c4040445000c0c0b0380020000e410850381c001200c01070003206030115120b0034107241345441c028034107508888a80c6012008a00d91a01d0109a40101003c004074600e036803c1c0014030105400001d80701003070307100740d40e0380c0f00d480504110b0084098a90396001a00d0b0003072480300501f552044010b0750700540076401c01402d15644a044106600100e042c040d00d0071400f0405000100380c0c600002d0f515100b0100e4410403607241d40c00904812643c6501181280c0c481 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 383835449 1250 383834199 383834201
    0x506040b090117100e2e020c0313050301090503070803040f0209090c030f06010f0b13091e0c0e0d0b101a041a0301140121231f09150b070311060901 65
    0x19000940300ba44020030f10b407541c1c3c88000100c00c0b000038025106c0b4056002100c0b24060b60003240c025440c035000400d00f509030f82c0071a0f90090007004214000e004e2071440c2e0312441d85a09c00c43c1009404031a0000004041c000342c0c191504001e9405031810f081e40c5800c9550780d40354103000c3c10140c442d004400c900c0740e080c0d0002070181e042c2c403609010714034614070302802d140096000740032503602002c0f00100000c6040b402d102e103501c8040c242003205001c00d03400f0603800403101101446c100b8805461007041c03541d200c50340c80b080000d501000412081d15103180c0c1030600d0300140e1200100003419807509110400c084090012201d451140700f07180884884d00b9003a500007406030b030305c00d51031a6501c60165889458808892510060501d2546500b145100d0503144440800180f18200711016610600289041c9900c44403480d0021150040e02001c040d106109105002c1e4060b12460030001c90722520250070020700c9204182681d80445140103001420105c501c1a0540110000245a4201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 383836699 1250 383835449 383835461
    0x50703020c0a030c1215140103050d0512060d020607020a080f5104080a0f030213090b03150411030708060c03040b0a02071202060f010b0f0304060506040b09011710 72
    0x1010541c180601e0401082d00c18026030f17150181d070100d41e01c1403500d56840061040c40e26400110301c5103c10781d030440c2001c0b450001808600000c00c0420824500c407000342100b26a04600100c2d0050000400c5000040a9000d001000395000c2800e003000a66224005a103206112648086d50484070840c0d01c00e00240b40c04400543c0d00c00c2c01641e0034400c208203001d440d0070b560b28140284c240c40407582c1e030714030300d424045904403110705000441c14000c0b44c0000340c6909034081d5103000e52402205d40c0900400f40d106114911101e5154106d00083d03070780c00e00c414202d21150a0b440c0c1e1b214501307801d0005030181c040c3d4015010b0b0113485400b040c211301c0031031b0b814840e51a0b060007a1550b00d41da41e5004601e00c00504080000d40e003800101d00007450134000141c0921164010b01e01824441121205003106a2050401e00340401207000100850300549920580011001480e0345e1280085005004a140c0081d8880305110011034440035400702c958031004440110744001441000490490321 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 383837949 1250 383836699 383836703
    0x8270f01050904090807050d0c0201120501051c020a0503030a052d070308100f081c03020309100e0c0a031a090307020f040b1f05091207030b04081e0a050703020c0a03 73
    0x802000342c6545401c1c5500300c00169445010b0403803411185444d0241404c640c1645000010380c0301015000755a13008820919080a26004103ea94503240c00192004102c2e2440c803030035004060a4420344d44c400c407501004150260070340f40da401e11103000500e0303603001d0750003905030071406a12610480d4030f0115240b800c2d22000c0c07001e403520045480c01c0e02d0004004129109140210758081400c0e042421140e0040610400a0004a0744030003558002d4040241e0003041510600801410f10740009040c50340303440c617110000d109050403030640e04101c44400615042108000000100401030100100750300800d2103002203034031600e14260b204d11503010040c0d4484c0500e0810780740317464268008480d50500504015510840d85850550f4030300c0a5181004070f88007040030360701410300140512403290700c48080c0c1500750550303a03080c0411001510140469002198881a401c011200812450866030070652240c0044100030300380c5d40100300880050107541d030403140904004001c01c064035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 383839199 1250 383837949 383837957
    0xc21010302061c1514030609060c0a050a0e0604080319030b1f1205070201060504110c070b130305010e030405130915020901020a0f0606150804080904020a030908270f01 74
    0x7019000c2c0c00c40d100e888205241400f6070b0755110700e1152092811014014848403e200f460b011044042608006008000c036000ba08900300700100145108211040c2015030704295450710a40001103544584416032035401103000140070031001000030280a2018004e20440101051500210142c07010032005c039410003c2d980e400b6801407544840e00e041004a41340000003280000c4921054440c140c0302d150240c4d64514081c840c9040c6405441e900303070000d050f911701d070004401c0155541c00e501d108800d080000881d410700d1000030215110002c40d00800244015000450302036101d83c4103105803071017400000b00e6081b5440c0c440c000c5e0350f4055001101030000f80401e801060207036000c203183c14114016110740f000061504111289210301030800081c60728140801441138000c55400303c818031003104200300010391808203c5694040a403805600d0b0000300300154007030081a600103100003004282210010803210450321b60380f60318515540c18800300010b00c2141801052030a00007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 383840449 1250 383839199 383839207
    0x30510061508061c0503120405071203140a090f03060509010f09052517010515031c030b030304050618091b0901030b13050108030a0809071508040501090b0c2101030206 74
    0x80c500710f5032407103501070b0700d19000b901309007103650303aa08540c000c049007480310030b00f281404140401084104054250241c080c014810280c0300505010410014040400710006101142c43e109002c254010500f40e07140a070310701c0c4c41c0e140400c0600802c4480d80400c0d031a00514a040b089613008880e81a500540905079250148209424608442c01800d5107823202c4180001c1d80030120941d175518407070500000036242860841480c800d8000340150703100c0d510040300745031498216074100541c0d07501801c3c00a0700110301c00c00300713056006542c0b100307900c4a00420800001410702e4420300f420705080b11a07140a564454031b01a60509000300704100b00c0c0144149501540268840001e00760002c3c0785e505e4520503211411b06030380c001d80205a81da0800305000c59955080103003c0d41114100f0082c2c800300b07041c45180c0d43c0703614070003841d001007040c00b0012905001c0c0a50190510f80d0300200200f05070305d0304d0a103111180c0c3c001c08002413101080d0515111142d1240c5a4505030795008100d5454 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 383841699 1250 383840449 383840461
    0x160e09060a1206240602060f01030c18180b010510020a050318040605060c1f0203090a15090b0708010f060305100e10081506040b040c0c031d0406030510061508 70
    0x85048411422221290b58090713641c6075080e821042444a4066422903009030300b000c000038206003000c1d12031080340f081280184002450038520320181c85030340d40f520b182c0f180e000720070750051300f070070030800282c103170000717a10350600c8542c4013024103075070056030784412880e090481203954007540c58024008d07130402d2000c00340b000d0800c46a40f03603540005101082047c2c80e00005500c0c1e500490a040480c2d02200340c000b6103004844000c00c01c01e0308028114110701d00b200d082c81d2160030801c1c00801d00d0565015410340124603501c070003405900043c0b10038561421010207002e1032820f01540200207060900040c00e548a8000c4920508441500301c1a286c0740c02140c4052100207403145030840c41d0450702080440f81044098545000000b08902c1814218180001c41e000c004200d8002c506000100440680200c0c40d10950b6505140070180700b1020303545500c41159500380035503c68142000041448400a00ea4075801b812400070000941d640610380d41035110003441d000071809034000119 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 383842949 1250 383841699 383841719
    0xf0904020d080904090c120b070c080a05030703020409050415060909051e0c0919050a0c021b01050f1b0c0906031c051e0a020c011b02040f06080105160e09060a 70
    0x1640b142c2c0a44049030381d00d525560b04030f06c0310a0b0340190004811100707500e01400108240e0940000b02803e00d01a0f1040301c1e26405180d02c036248001d402c0c04000030101d0305691181d4100c80051140a1040009050a240101c001d1160039007880c000790400d00d010400801c244503150900380d0260003851a1606075075444281d41101808500c940120a14110162a482107643c400c03101000452801c03004d440340101250b1014144c44c411030b24180034481c0043e0005201800041c0c09104403400600b80c0c80100c1d59032140312244e000c07004002c034000c0e072580401044694017000c0e00007910540c0919205100a142049174030742d030315511401d0304035960310a00005103180569454004c0c60292094009186181002c910407603a0600040201c6101c1d4140032501c8204001d18200d0a410a41d05155488844007100039105075078070b42d4001c941580560094006204483c024402e520382580d441d403e038000e0090a4010412507403070198185805c0001e28420380380203040d141c07060b00307101d80341d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 383844199 1250 383842949 383842957
    0xf0c0a03060e0c04020c0303100b0a20010b0a091a0f1807020f07060804140703031d0a0509100608090a0b01060323010e0601090602030f090613030c0303050304020f0904020d08 77
    0x141c02070140f6501c00415440314001804246403800c015656810160615500c4803a10f074400c0740810024000508216480004031034641a242c100500f0a403c0d92512401040b0b2580210391004400038001260801c540048001261481ca810403100400d018480301c2c0102c08485544071a2412140c888101405007003a00b08026204886c00820f852031728a141c46d441d038120f140480d81c07640130841042000035115592002c10005030203440c1c40c1daa005440071641c1240c2c2c140c64050180005003a88071034101400034400144502c4103814000c0011810b8855401400c000030001000111414400a00905074651040b484400c1d686005c504400420140701c0404521040019800340c0d00c041c2c0340718a0107481c21800140690a00b034001600141c010340c0400d040d50001d02110280c40000015160145015a000b80c0d4072110342003000d948403001d4000414030703254014003109266024000e14455407003641c80200c03800c0c0c0a01048454001100e000350302000076010303503001071a020054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 383845449 1250 383844199 383844221
    0x7061412040302030f2107032903032a010b0105040f0e100803070c05120c211c0e0a0f121b050a0311031905030706110d1d0f0c0a0306 59
    0x92810300402554005c0683d1000101c00903042110f0f11680f50081c81000d00380d081038a41c141080020202c1c0a945007600440c1c1204403001d40c13a88518039079840a104039110421001c000c00d450820341c4c1a142c800e01000d07040608a58a8441c1707107036103940514100c805a034180501c03500701d40e2a1046441426000502003107032103003010710000d68a801080035051080c0314a02e2179002034201400e0001840965a480340c6a510040300301e034240d12850f404022000340c800304a034811001d1200c40b0b14240c440030040f40b0070405044264204e030790041c80401820700440300d80e035620750780342e84560540003580142090b040c00f055006c6c0000308071080450114003c510b118042964482c0011058000d41c1d0060b1804508000d0001141c5820b003c400d885400c02d440315801010142c68581d682c0c0120030340148202d41d2942004800ca403048281c0c0c01c80c4056540a21814152885c101d0760000090305404941c0308007060380c500688041031081c031060019021007445855900c40002802040b008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 383846699 1250 383845449 383845453
    0x602061618090c020c011e1103090901030c180c17100f141503010e0f130b07120e070503060a09021207030303091a09030f07060b18070207061412040302 67
    0x100c0c0c0d454260310050200a051403100001c001c2c0708800080d003041348500c00c6038104484010319000148090011154007c15481d002d861400c22070122859480703458507166001420500000420850102c6401581c68000b4201c00d500c06107004c4600381c078803194106010900404d0f03940e244600b48088554001c661800c1c19000396a40c0d14040e500c00c24170740115002e010702c24080841824941049003140181c46d003003520307661404007111109a8080c02c4001d80c1d101040226900d40d542444810b07226403c801251140e0424000c05000f0b1060b0b80410f5140900700300e0848004140400c24004039800580070b8112a69216400c070010300403030004a80c414644c003264144580c0c10004240a0b52003518000340002c0642084680d46400b03490030030f101802e10081104684001c000d450b114084c4141154444a95103014400f5203a040151504100b002401c40c0041d6580da6040d40649407903000c0e540000d86501048404900703240c400c10a10a00701301c00c503080100d2464003541300e4002d03c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 383847949 1250 383846699 383846717
    0x20c03060a1a150c010e0313031101110708011407021504080d022203060e030a0504050d0204020705010912030513050303010302090903090d0309060e1c060e12130e060a06020616 78
    0x18400d206900c215000c5034801044d01d0000900911404003e0640c50000f0750611910080c00c50080d41c5a0100400a000700030750f0004a902801c1401c0b00b0464913000d8644242d1106183c0b03008000604034a0071252408010400e45070010905030110034401c1c0d001841c0d80d5450700c500040307600480700e00941c00da00708000b102284502c6003441e18017a04a05148926180d41800720a0718000030b600e50481d08100024030300c242c4c02030102e4044075416900301c5031908550000800034060041c0c050025420300e1114010004441143e200b00c101d80d032402c010707d449002c1804001170b14507100802caa0700800041c005840d00c1541150f0001d4854100e0b0f140410210202c2c1c0360094414086000c038040040c280440c1d03030012405003083d141034a00c0000500702010038180700303a544e440a84140d43d41d50806a11070307030500c540070b0700300c605c11044d40d43c52a0351101040c000d02e40348211440e4070307910000b081c0c91b80b81c41c5c500141202c0b0359900910b40343c1c6510b0a8501a1a25280d00801340b0503010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 383849199 1250 383847949 383848001
    0x3020702210309040903090f050108070215041703010308210912070507030c06090e0c0a08070c0c09021c0f02070b0f15090c0d0f06062a0f0605040201020706020c03060a 74
    0x200641707180b2403180da15032000918000056116202d070783c00a41c1800f030340c01c0070840390a9002580c805070500c00071034076025072240c0c20a48001c00c10f0f40301d078600e1414000300110500c2060002070148480e004c07160604ca0181e25162080c04000792060582d0360401001c030320000242c1030151a0340d0b8010020360345a0703a80c0380c2c2c030450000d88035800b1101084c0d1401041158031180703a000f680c0304107950840da1410007000c00041c0755100c020902401d103e10048010306004602c01400064050b1110440d40d81a454800000b0402401034414029003000030b0700001030070354020384a4083e4086d4011150740c076079203038421000c0382c0100170601c00d1418007945051a900c00100a009542c0e60308400c0e030760141040d081c0d043d05c00c180c01d01229113042c0841040000c1c0d22505079840301d400d00e2000d1410311602496040c480b08a0080a469024003030600c109204003036201700e015900c03d80880312041c1c0d0707407d400d036182e440c244210b561541241c00003c40540307058101d054000104401c0b660041040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 383850449 1250 383849199 383849201
    0x105090a0e0a0501030546050106080f10180609020310021612080405071505040806180f0d0e19080f0d02060c07080301140103060b19030c0302070221030904 69
    0xc0b11035241c016200d5004109002c1e0601c2450258100703640160035000100268030f1003e020001586a026030040302002d034202d940510804081d480b40c02072080319900d0316000c0d170310328140040060318043c0d4001041d0b428018450305035480c00c80103000b141400d164a0ba05c0090031400000d90309409103855400c601d000070720041c598006403044003025180d290800c00c40d00c032000280c0005101d400818000800d500054110807210140030303400904003102d9044405000740c1d4403c010310701c81c010a20030400d00c9a200d070348408005204070b50f007843d1208211540c60403180c1c15000030902c0320038201c41c241405421444003001e041310b4132403c503035035181031850041d190305004d16941000b9400d2119541c10f011141c0c20513a103040c03d505000d0b0f6a110445144010f00c500c1c1000b81c954210881c181c3d01a4120b400101386928130184c275070301c4080c8140942e041091081f400280740011450000c1c0c081d10a80750001d03000b8000e905401c4804110072510083d50001110a1005000d8810155a5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 383851699 1250 383850449 383850451
    0x50a17041d06030115090c09120503030f09010b100e15090a03030c050c0901090b0f01081506070f020303031003171804020702010909020d1d0d020a03080c1201030c260303060105090a0e 81
    0x11b500c000280030750201000800400070360b004000030f5803807002d440010440000a030390f000703c0d151440400d41e84807480d5941c010402c640032650081500d4a00d45062500508881e00d00d05046d06c006500c1004202101864070540f01c3c1d01394070503425101803001c01d20030716800b144c0034425400c40b035010349828000f5002c01401da020558103515519040c0c2281049150801040d001b820070b01c107903041000b01c44d0140c0c41b141042d5400384001045400600c101001908400c40e00a0143c035a241030410002010b054a80419211048a41e0036111032500541c11165400840280791032018010760030070010b544180c06c140d04100e0540b201081012031440209010600c5c0d41c000500041070500c2c10100c07a8205110f10444c0d000074030110141c58000c030300c2c80c90140d49460110703199036500d815040c9a006000c82001000140f10000c8100500580e4078030030b0b51108603564400003d400e00802c5450101148240281c0080c40482c0c26940190050030106c0b074020900081552034200c00c99030614 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 383852949 1250 383851699 383851709
    0x60306031c090906090603060c020c06030a0908040906080309190b0a0c05010b1504090f15090c140f0a08150109031b080f0303040b0606120c07031209050a17041d06030115 75
    0x1543d840c0c10030402822703200d204500c00490028100c000c008800240240c04010035401915898903520303010084000220b4010340301054040158a0701c1d00f007929600c2d08080780c039070700400011600002c220f601140070400c4500100c8294a4100a0074084519001640c1c0c211159900c4440b00e90640c0d40e58628220b00e0031403139651640b02d074500b0003050b0642360081741c1482400e00d489012182e820040f02802d0694104000100342a0707010700003142d100300c14600b2150442004104000100003000040000842c20354940140da00c031079601e0032500b40050110350100e10008020400074040003084058000035030000340d0b00580d1460224240041c0f0a801e82c00e80d00004108001c2040842440d07030040c5007030f1001824030900c0c3d101c0b6916100080c20312596068041105010140300da8210030040c03608a0040c008079005240c165514403c4500860350341e160700b41d8100c24000544152002c98510740c0e06030301c80300c4150300090215200944810742654a51505585600c400ca01580040c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 383854199 1250 383852949 383852951
    0x80a051b06040b0c090a0302040b0607080406090905011502060f061903060618051006030b0a030812090d1404170a05151009060f0e0a1d010b010e060306031c09090609 73
    0x100c0c0503d04540b801400400640d0011820700089000b03803140301810044e00d40c107907400a000441d1000060b0f040c0a8144002d0050b0780000c0c000c5012648040d41030102d030035441040c00184d80b900c0a01780205100c4550360016030204002507003091113404155000a4081c103d04007a41c0000107610705640b86810603548035490b6501040302800410142c82c0541a80100300420f040c08a01031800f82d1403442450101922000d1030402903942581001c0116807021940f641c0b00740108030b280407183c0c01c541c0000c0c3c901a101402c0b01840c01914200c1c1c903007104010240c6010b05102c69810101c000d5007407002540302c0c42c82441c002403010004c40216034062800030b20a8581200c2c50040440300e601f10100c0c00e82054020041c9809040c0f901e8155187c07083c08008a0341c80e0f07407080000300141b1403621004e03075102c20310102070744040d8800c002c14827081e40e549410305581c1c03050284a200035100319030140c1c00301c0101c604030410a40322900040e0503240c000c1d4000d030340d0760140c0b06a40850300413130201 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 383855449 1250 383854199 383854201
    0xa0605130c110721142e0b06160c2d121a07030e010f060801140103050a02060c1c03150909030e100e0d0807020a1a07080a051b06 57
    0x29a40242c9040c0c4102c041c1c0c0000c08003942840704d04461204100014655410980b2500c010080422014000b5040c6003046a503091154603140c82071400c1e0070343d200c810440020440c00c2400c6280030340511540003900c0c4600d4032401000030095040307802c5003600c1c0a400d800d804112030049100c1c4d002c213600e803114046410b440b4041000c1c0c4041165002d400d01c4e401d45417041d00050305601700300b4030710014003007061001d583e191000c2c0c007c5c0c50000c281e2076165190110300382440c03195a02140649010303000030003070b0f409410210b0451081c03c6c00007402c01e506c45012030700180b50440040205048690030b031111004548880e0a43c00c1c0e10f5000c40300480c0c0ca40d181c00c10a0326840910070010000b105042c810207903d620090001181c0315002c40c01b5098200c54004828025003900e815044007400c0f011b4401131504182034680c2058000302e00c50185004001031501e9009071401e50707a40051156403424045e6a5031a006074881c0c20b078942400000d000003001210583c1d1400481c5450801030501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 383856699 1250 383855449 383855471
    0x1b01090b31080c061e03090604051b01052d1801141918050d0b060a09020a0f0f09051804050d02011b11070806100f0e04080708030a060513 61
    0x7071852611010141c411501010030a1180000e00d240c43c580c001e0b0b801603650f024141503107003543d2071000400c499000002c00c0c86502c1c3c00004215228a001d030007661000c82e681c6004e560140130f81103403d80000d40503c4000032103504040d50380c0c128405442c01680700c14204e9043c2802d6080340c0901c2400280c040c0b11003400d56040511682895560f0341c0092500741800001e06480c010002c6440c10003c590009103516030740c044200010b420b0040404c1c0d014003a601d842d16044000322402d40c011500b5000000343d40f00d40b402070b1111610a616400f45420643c0d50464114000d003072072804200704c60a0015864803030305480451861840004110f510701810300c1413074900144101c10031a031601039060000591400c2014042c21245860b406584580204524150250300f00340c00c1c50103018180302d00350f880440c60300f003107880003c144400700d1f6a0f048000c0503c44210340180601008205080005264000466000c1000c081c00141d458440300407504180c460518044400e58030703410210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 383857949 1250 383856699 383856757
    0xf1502060601141902210903011401081f1107060b041815021b01020a20010509100207020d0f050318040e07051c0b04030509130b01021b01090b 63
    0x741c0701c00c0a081400242c000403898500700d2050110900b22095400b4090102c18824890406244846400300d44240c85940e0240042d031301508420340b00390320344030207281d03886016174995048800c1c91014141d2280c0f00d2401c42a17a01f10b40c442c403041582c1e9200025501c0316000d01078041280a60b000040b52030507a002c1c042251059642c600310140340001000c0040d403110350b00103400000c2200503849500711203100c0d551032000407003602c407940040303090b05202e0307402504840c0c2d4440d400c03054044104d070301c20040d00301d41098400351581e4103e40100c3c105407030b03550010314140c1d1011705212035112213901e84071074060034250304407034580000507501c0d10490301c2d003c0c0800000c011602007104000c42c54003075503101641d10441d402566140c09104810320a00c00340e030a100c6c0c000b0010352440c42d281c03500500d1580961050751003449450070513181f2040c6803240080708001a0001c144809484420709500c1040a211504001781c2d40800b20b003c500940140c01030b410500b100011840884120718 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 383859199 1250 383857949 383857951
    0x200307030807020a02030c010f02072111011106010e0c0c0d17090f0a060908131205120c0c0111160612110304200301020f0c0a020f03061911040f150206 67
    0xb085601034a641005a0350119441944413024240303405942003044d4103900b040b80641c00061000a500ca055088003104070b005600b40d4419111040624042030054440c0000143c500c0d04a07440000144904402401d4454201c9501c40015003441c400820040c0351000705405400021000f040408402ca440008079410a4140b8040c186a0303e8a8000c1c0b50740d001c030401d019201c10341b560801000c5c04a030380308582c111245445030008941d107581e440c8480b000181c008541d28400c981c441c141c0c20072030b1429911248036800c040e0805058601c011540144400400301c441c1c010641703007206604460324403130700608580d2218130051115598a400b22072070b081410940100c10030421001480501c4c0300030242d4080d40041d0103801d01e0340c0109009001e60f82d240c81102030300245103024080e001400c204058802c81d0107400300c10410040c503071a00b40070b9446403184120b00a00482d158007542140041482c12112207061950b580341514000b0101c8d0300020b490f40001c0d0b055040c09034144811 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 383860449 1250 383859199 383859211
    0x5091029180a140607080d0b121c08040b0402040506151911030c06010e10090501140f0d020108130f021804021503070c02010c150c0908010606030605031b012003070308 74
    0xa009903d5a40c0701044442c81600c200030148800024459460412540a1051f843d4040d11010001250098042e83d8003e0013241419100d986004a503d140c41801c0c103511580d80240d4403080c546550b403e0001a20740600155072000d45125030007910110140a007002080841c0001c0451074202c2014040c83c0d03402d004c5890517041001000c1003068009101070448031200410304c03259550819103200c03503041ea00b0903000c0360708210001421000d60700c0c4c121140081262144400080b10040014402c804d1034002c2c0844c1140d00041e8043e040c407128481002c7c014558226074110590010380041c03d60403041a40e048010140019400d00750510040101584c0b529851410720f420041d0040601c484001c1c1003140b215103140030409900d1090300000401c8070180680c21415502401490705809145036030361900d2000103110f032107405110100c503c040c0241052004407440c40c1d190480030013059042c890070000001500040091400046806c040a19110303506460001e050140140030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 383861699 1250 383860449 383860469
    0x5010515030f0609100b0a080a0c0f0804020906132909011d1914061903020108010b03100806151c05030d1a030d02030d0605091029180a 60
    0x800c042c004a02d004203401c0801211070640070b07510b144d280010b14041c1d42041100c20390206001c60303a25000001c0700d0103064200310500410148040403103450440110340303400904400c020401504100c02d8160300084003401c4d103481c80141070340d03200c152280c54520902010f440d60240d0081e52007201005403158049a0040b100c2d4504448008a1081a515440008142004501921030364112001401081d2100f406090100b04003566400c00881d2103901580c0e91035424680c0c2a208980401039a9058484156613401c0081254260300018101d030751700380714041d010900802c20005075105107400c0c0810350840240c80240007242495581c40400001300a03000400500301000342d5200008a170b00005901c034460b6001d082d030b00c402d20241078040c0585103440100a03030100041c1000903401400340440781d0b0b128140480c40e0400c0f035042581c83d007161001d00038035070744459110301d041c00d00614000200000003922855801030402d41441500010202c2c16403e00000310801800e002c16 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 383862949 1250 383861699 383861701
    0x154503120512011a21040b01090618020d11130303030b060a08010e0a0615020c09180c1009030803070e030d08060102030d0c0201060b0409050f0c0a09030305071e060501051503 77
    0x181c04188124103002d801407000c12104d24140e80084241520b08440e2480d03207114605249081c00c8000c80c5085d45c042c1c400c1498100082490455402110f088a051115841a00884c400c00c40f000390844c5038410140b503215010a410069008054681c10f14250080c41c0f04510b14540134044990070325009004d060107002020083c1c0d00300e86004c0c1101c40301c0345c04501c259074040440d80200312036000400d0442d140c1902e030401d680e0015064880040a54100c90140c668000b0001000e001c135030003c5055204078048055820f01c68031200e0b40810130b040c007001080d2207959240f800e4100311103010004030390025000240c90100070208440e0702070b04040342c3c1d42c18203400003510307445a143c1c0c040d0440c5c1c5514a000401d8400d41c000c1c1c1c000c0000f81c4409440c0e0751120140d00162a0030307618100501030503c04070b80e02e49441000c440e850612521402e0060385165401d031a280c204210640e100d0085080e1351260084402c031044580340b103400c2c00103080d070601080140c0c51a80d0000300e0850071080c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 383864199 1250 383862949 383862967
    0x10050d02070c0f0611070902030c070203010911010f09230a080f010c030b010305070c06051803160c0806010806060103110904020c07030c0906050913051e030a0305011545031205 78
    0x4600c800540c2c0107c84c2c0540c2e00e50b25488140b04620910400942640c03030320100505010480300540034260b0240d9480d0002001071000f00c840804500448800c480c040c041803080c0004c2400d003540c2550b02402c0308280640e114011414080c00e46101c07081b9945840230143d0340355062140c031072408003d00381004281420341e0018a18034001038028515030341d507030104425404120350000885101c6044959421152106042002040000300c5001011000114000c00086062410703a0b89400080c402c81d41c40e000111b025242480b10102c2c006400c00c0085038946541c00101800c2d86600001d01341c0c1480c514008580381030a0380001481d80c80e04809002643d90500d01c2a00220b466800050380603283c140710b410081015482c0c032106005940302d440f181008009480d085c5582c5c0c80c1080310b0303a03036402c41c60303500c07110040380100055080d1030701501c00c0203030801b0200101d0906100070300341d940c3d551590b882c000300043d84961900e0340b980810410041d050824902282490b1290030440341c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 383865449 1250 383864199 383864203
    0xc040311010c060f02071b0819060203040f02040606020c12071224061205060919031d0603070302070605060a0303091712040b0405010f0e090610050d02070c0f0611 72
    0x4001c0c10891003200070814072031260484200910b0b421021591000700b40b801c12004200c228001071244034000000078203110205401c05111030408200c0d01040c0c46a403484020740c00184126009441a02110f0150310342e44148005019603400601030000c00e1003c0083c8001700c42c0c0000ca00b42d01500d014803001d4183e444205400303511146429102d100502280401c0c402139998200d0140340ca0000102c0400c559814200140510145c58460316003a00464450400100d20f90400220081070310000788039441c10343c51852001c0c41804081d140d1000212260320503203241001031340116620b018401103101740c64000100b1101402c1591456601400007101841094002ca100d0300c180000c4500520800555030f0031441ca140d0748580343c0c0c4031030030250498003a035400150b20001c010070480c0600c4907244400d200503c0940d05035600d01c100a141e40d403101c0301d101009000d0010301d02428803070024140c41841608101d803a83e080490a4035070380200d41c007140402030342d0307628090b11900c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 383866699 1250 383865449 383865473
    0xb04092901050a0212030709290304020d0f0611030603010c0905030c01050a05130807031a1003081b060f070806060a050307030c0e0319230304050405071b030f080c0403 74
    0x2801c0068656141d0f500a0741800c0194200c3c400030344000040001e02540301d10f0070f10036150204d000700890700e0060514442c144001c203000801c000300b0004a00545800640158941e2098410800c0516a076440c40e00761000b4602c486078260f0f012040c0080f500e005c0c011001c99200e40c0c940521042d181100107990351424150f0213041c407a0004101041600c83c1c0200e034171703078140c0071031ba00038481da1002440d580b0515803205448c1a81c2101c6e00c0c110043e200405180603c10040c102c4c8106419a00d940401e075018031022000001004a00c560104003841040d11820400741044114507140c0b801400c01c15009110703d10038041044505041a041400d0325049102841e0000759030b400d1100030f8400307500d0403480540c984101e90b07000421010401c11402141e20901c134002401a4269100d00500203821f207100040d00705100c107000c142400c0e44441d0780701803d460006220382100d00c0c4a800c50303410384070a41c00a003444100f98660341d005144160000e4000c41040e1903d03103151112400568 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 383867949 1250 383866699 383866781
    0x3010b010915090509130204140c19110111030108070b1905031302060f0703030c0216030b04060f06030f12080f24060a020705030712051906060f0b0409 67
    0xd4550680d0242c01d21545204026000180100d56503061441c0004c04900255000300c1c0b085050000b80c103940152549123074000c3c0b11094120b410401340b0120f074606280c1c8c2581400420031030480ca200d4412003409114180040300010b241e903541000042030400c2ca03103400011098804010605400e000208011810241c1d403411039203a072200b007500031400c103480b00c000e944040041607210307000c082c031401404024400d07101001a00c840c160281d0706d8040e8a0034840d441e5030b81250410215007080350942e8054410180090790701807200750a421600300d80c1040d074203e45000c01810400c4109421300760002521f00344030b01c4030324114042606103107005006499101148141510031601c04103070811000b03004207904e0711f540c84020001c0d0383d0038040c400c09201c2d1041580000e0120f92044806202c44c0e0000c021703142003045881100d40000d900d80c000c480b0290340d02c0c000155035a03c040d07010040c000480d085a900d0f441d218400090341c1083c81303407001c59408200750b019030031703500003c14100301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 383869199 1250 383867949 383867969
    0x9090203040512180406090b090f01060806060c010e0a0c050118030206180102030c3304050d030c110a0f03141222060e060412050403050c040b0402071a04020f03010b0109 75
    0x32488114031800781c40b40030802d17600b003401c242010400c500290840c20001c40d0a4420042c146d0f650090403000b83e5003807069001151104000c5800303400c007903005180c82d03111706001180c603041d900c00c0c0da413030181584010b4403d6484214240702540c2c0c00300160542c403d260b0044e0441a0454001401502ca114503420340c0d00002912504582d00a2040c0d40c120311781c0300150f40c8400c00b440020701800c65206100d505000c00a0007110303c000168030340700c2c01150010010b00c000d80303214800390002c0040594850602005401842502c2c000f044400c0225100c0c510000c00040d4070310f000f40021414122210400c0300a000050300b400d4140b00d82030703100320a64141600500c00c500202e5441b00084800381485052045526482500003005030049201d8102c1300103080314000202c50900031404000c0240d00701020000c0030f49869000040e003401c00074001840d0660079078404e4a4050031800900021044104201c04d40c64009245455844250000d0010b2607400c00001c180d03000600603101c40c1c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 383870449 1250 383869199 383869207
    0x200301110a05032a120a050c04081b04090210030c0210091e0204021b01020304050c010813030c03090b07151506090902161406010e1302010f0c0302010e1603020109090203040512 78
    0x312600500c24280201000902961413401c5c245c8800803800448500c4c803641c1c10036011448044210b0121000c864000000d0004d0070aa455058406c1542d0802c0581c000c8e16142d041d00941c3e1422001010906a610006040e06049401070304020003160354005a9140041c001c0124450440119070b40a07407454003180d041040c030015000340a41c0c1d54002c1120301000a6a290300750541c0198042c50081040300d004140510045400034003c4892508a100d00b05200c0b0029019034541c0f0705041c860304001c07002c10b40302e081140340da820038017007940c1c1d00554402c850000c02291065011501d814540c0c40c840a003805000741c000700d841d10518a41550000c5d122401101a03101c203580da0798081000540b900140060381e68400d001e00406030400c20079004511241c107801b00e801c4070603034107071104556120107100a40d00b16208640a5042d95210480001035131004e100c0c10400e03081c0700c0043c0d80064118000142185125040704244910420900006c11070008080d4113401040f01101d0b0f46d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 383871699 1250 383870449 383870491
    0x2010f110f060106090602060109060303090b07060b06030c09040b0901270f02040801020a0810080601030f0f0c1707051e0d0305120c030433020a020307200301110a0503 74
    0x103021480001110075010303030000811004d502200d12011038005508441059132144080c000701c54207880020b0100b132405004014200c400800b40000758058040098040d00c984086022a84211050954401c0000d075001c042e191511030214001c40a4411030b44030b41c1000303c0a00c11003080303c0590307d4400c1020020f4054403035600034940190240754155100c950701c000160107504083c80340008a91590000394100300744c54213040846880c01300900080e440d64507a0005010403040a585003022400d020000c2541068003100402d0070382c4513001480c1756800118201042d9821003442261f03510113100540201380031038084801c0440d00b8800c503043d00e25040d0788605c13602d6004102d00b85940200441c81c1d008002941c40350b03004141c044844c0235888040a55220f4a500c22b11203950390b40e00151003d507440c0e0181c0f09030340c2180112850680992100c0c45501503030846842c10081c40050b0442506084c082d0200c11607030b801340c15003055100c41e409031007030100600304030240303810a0b40488 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 383872949 1250 383871699 383871703
    0x90f06050a090c09020711030a050a03050a140313030801080c0a090b030c0a08031312080a030c050c0703050f010e010501080d080c1c1b050c0712151b030b0a0302010f11 74
    0x1440c80d81c40b03d10721000c1507440815902075085000d003a10110302c40d004041060a021482c020000d5024010304021a035656041d5201d41041240c0f2081214000046188040311300041d0300504141140c034046561a10303005208040580000c081c41c3c1042c07032400d4007601d62440c50415548014000301c0e0340c4421740042441d00f068044000d0f4003440400d40090607200210061810160366080160a1a1100e103074681101507520000c180c481d00300301120701c0a01c245d10520805e5800d00d4010302d815400c1c01e44501c0c2c40c2841d00191001d0708220107680c640e9a003407145120f10389000c1d00911241d850100545d0f1981ca0b008009018050314200040d80600da01c01100d291261701007510480c002c186051500138040359118050a00c0e254501c0501240075030103031031048803044010911942003003051440002c0190781200c1618030030144148044890045074001079a5183d08151072040d104000c042d258030b4101315020394018681400540d910075804130106803181032980e450403910b04514 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 383874199 1250 383872949 383872961
    0x12040504050c120403170c0301180b030a050102040b2101050a031203021c050114041e0c0e03100b01090e0108070605090d0c0609090e06010506041502071d1801090f06050a 75
    0x3c49038075501c0802c0308142d0002c5800c00000d00c8008007002640c2d50040310b07100e511080c040e0820080882c00410200b2070140c0060200000250540d0850501c030740c3d406007684c004d6086101c0c80c082c00710ba080c2400103490108080040c010780800400d500d0400455140b401c24003028020454044180301030354000d80440350f44018017466241c03811034505104009080038040d61201410490007850b15240070301505000d848080408484000c1051050005002040140040c06405040d80da481e81d0144540a101848204041641040c2c900014066086504000400f18070000180a10403001405506940303050418230307685e040000014500c900311300300040141c1203881d4040380003a80140c410b4200c544001c428441c0d0016200156200c0c2400d01071030790040b05c00d00c002c2003403041030020000e1024480c01903600594640c80040c2d510502c1c02801c0400c22903440601901ca0209140646445500300007006059071582e0742c181c1048c140342c0080c0080d619031001c1008003a85601030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 383875449 1250 383874199 383874217
    0x60e03031201030f020108091506100c05010501081c0f0c0b0c09030f0c040507090806040b06060c1e100e030702130f0c0c120c03051204260c070812040504050c 70
    0x100307541e0b49250482018a50250403400203403000c0125283e044d000a12000505621a030303880540c0d1040184100f94948038000c20401c0068243d00c0003040742845030700d01812010019128002504002031a030459a0380c5040030000740e090301c040b000340c1c00041e02c010f0030350207441c860700c03901c9100e14103046000c2d030200e2580c94021424229a240e07400185c91095030000e072020301c00c50361849003e60b032044003442041107903042500014001505400e041d5400080201071a040c00c8a0031401803525103940110200e01d1000e410124006500b000380001a02c41a0402d00820703001100c138075102d003d41341c0f00038003503901121340c02241c400070307089841010003480c0208414400d844000f05403a00c04c0c0303c1601c641c07600200040400b40302d200d800a00d1340d09504c455203011101e4000304c0c0b1003107000300b05035000442c80c0030900e400c2d510801e4072082e801c82d07464456110002060030070f080c8903499000e4081a44001c0d081000c0342c0745401600e00300d5800b10340000742943c62000c01c40b000c1c820042c81f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 383876699 1250 383875449 383875477
    0xd11071a071a0a0f051909051204120b01360e010e010c031503050c0d0302100908030702061501080105010e040b0d0b16090617061f0302030702100b0a060e0303 70
    0x406240b400c8118152485014458018414021031440301400c070b56003504c410038403080000d0300c01011225500001002881882160f14034440c51040d0700c02500246c00c81a08503249442d02c0e01804001c0c0c0b0f10601401e0084840480814410a4452000007880710820b03520080e42c10442404030a80c440300e030302c509002c024460100040c0c031481c000d008001c040c0c03003c80d1600b0251901811100b08480c20b980e03000c001840421418010002c82441014080342184611482c00b00410305501500d54024883e0303071805e8481c2003000c2c0283c1000002000c2030400304408200d4883c0b40e0340811070074110350003824248410301d180d80105004c1c2c00c2c03140703203c0d0b044055044e0f2041000380240e042842004070a00f800411701c4242d80403907a8050714800c200c0040c4488403001a0039250304030240d04504002e14000b08140000c0940c058074941382c0021001c40d5002c005c00c1546901031003030a40d115460241080403508050001705403641030b0041e1420800e501540701100e440410455034140b880080c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 383877949 1250 383876699 383876723
    0x90d17010e071205040b180c030303010b1c060f060e030c01080c0c2107020126010519080d020d0206090703082a03070602090310140411060f070f02030d11071a07 71
    0x78030b2280c1b0b0070705032200d414225402c0e03e0141205404100c0e1403c2c51070003800b5514603441c1a03c0c1d9030440d00443c048080e41140c84442c204680001d105040c001d040c04000120080d1800001911201c101c070016800303600000310592041c0e030b001c2d14040e481740d224104181c0b94000510440d242041e034400a4484441c004801050305038000d01400406200343e803003208003518840c1e081d904560400032002d8507103922005010324036044802403003406060307002e0114107a5400c581c80c58800200316200140c1c101c280742030040d03541400525404040e00b402007070072034510b90320920780c6e106420b0f140d00e00140b80314020001e04105205c0b0307900c81e2842030459840d58850300708400294000b110080c400e22400d0f1039041541001c0c007031080c071174064003011b90156a60b0b0311303980e518100c00d1171070603030012040203284104803100019000b02405404100345688c03da205041c5000d40300643e240a0040c06052982868000a456415190f849600c245401c6035199061101d000b585001014801086 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 383879199 1250 383877949 383877953
    0x1202104030e0d032106060f030207081903020d150b0405091f1e061706041505210c060408060c0711130f1a01200c0414090d17010e07120504 62
    0x312040c0c00400740c00d080d1504008211701080101c1d221803043c1c03004545168241000e09010380c0c064a0668001e4540c9407900a82800780c40a0002a03d850f4000c29404501007a1030541885111405420102d418580d1400d100212030035001d98803e0f0b910170600040051010a601c0d00c0f5440403601503c01c01d9007098980714007151902c03201001e682e04595045e0001002842469a51001e291045a04400d0b07110b54042c007001d0040c06912401d0280c540b48000340e036490340c1010110044802d440002085440c1d4041e03410940b5240c881c510511007448140300c0306502040480d040075082c100c450f919045440d16991190046801a511110742001860b0001954210131524160490200f04940d0720402041241c3c0110300400d0000d6050f8145c29074040707407615078100e2500c080c001c884130007503000c000506070b0f0801e500280140a13a0001e001e40c6031010850744800041c1030030319807044100c008207010405014031405012860701c5000c039001d6400b4660301101070181480c01d10580c03401d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 383880449 1250 383879199 383879207
    0x1113061205010606080a05060a26060f0106110c0a0504050619090c031d0c150903120901030b060711040207030309050a0303050f060a05181506070501202104030e0d03 73
    0xa4811103000c05c1d1303000002080914203210b01485039030001d2000b0900783c104001c440c0000a00c400700301503800030840038501100d040003030b07901c80c0181541c402d00960501000600e02401d40e20001a030342c1c410480346c4803d564841644040c0c6401360f500090940d149000600510b10b034014010091134030701c0c030215500e00c3d240c10084049600c0c0d01c0c14031401a03500c2400c103040034210402d130709070342108031105424034200c03e2841034529005c074507a0520001400090412011414412503070100066612265805020300708004108480d0745040c055103844821041041480244c8110343c0010350b14101800380d07120030402c9400008840c11001d291802400a2409a900c1c10444c0900300c0003641034500510f00708241e40014200894111035050817000100d40036204014642003202045001e4803178038054040329015400101c0d24103468404041c20f04032102408500d500d0800c210030b1402000d00d048095121108284110b42d41d031401c08403000380403458900e0344042d403004464181a88 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 383881699 1250 383880449 383880461
    0xc01090807080d140606090d030908150a0c05030c0f0a021c180906060c080d06030206131401050403020d020d020a03061d060a0207122a20030109111306120501 70
    0x35000100a10764003061542c0c004c6800b11011039111600300140c0c1900d080805100c2c00b1741e031103805d000115649502c0b01074145022003a110a881321030000700b2406424502480c500e000007420100e285007411680804140724298841c049082c00084202d5020703c2004500b200307005c41c0310b4107455600300c00c80c020500032000140c5000c81c00a0500850340c002c2520541d0221011500c919503142550382d204802904094901c8545a03910080007015842d003500424001007003a100c0056941072140d0b10491400c0040a01c1c1040418041400180c40300c4d0300c01c00f58146c04a42c0349094603c103200140400300c403a00020401410300c05441201c0121b0b04008540c40300f03010540e0500d541d48141d00c000c038041d51b003001c2c0c10040c80b02403009180340540001c1b026040000ca1040c2d002c1c0c1414001210340c141078204030740450783d4081c2a03c3c510f050ad04440d684141c21002400600015250003842d815102d4906101c2c210241030000c1c00d40050340204010041004403448036405406e0160080c08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 383882949 1250 383881699 383881717
    0x2090112030540080d0c020d0506070806010f03090203190837021501030b06060c24070f020a0809030a0606030c031e0f0807030309020904230d020c060c0109080708 72
    0x12440c42c1d485034080d990f01c105820340c0c004500a00b035149550794112522034148406980200300c8a10310804950144500d62003a50300380c40303078041410600001056007a2104d0344900301444c11024a0060760081040201403803610702021120b400ca00704001c0c14440d0700914000c14120890302428089858080400c03000142542003101d25000b40aa0312004240307444d59640da448001800010405110103400400250940d0700f00009051005e2920649180901c1c1500707555501604c6800d0a5418540c0900503142510340c420f0044c4029580320302000300144544008160640913031420040e4601d00e54110800703010781e561700c2c20500300700ca1031400305440d40364005c40c00d1320032420150001419a0341c0f0025410711960a61140c40194014200403010540c603056144d000d0307510507502034083c5e80036014000c2d03520038101504000070a45c1d80194025004211502c80141d004107031101500130503220b0603070b03400d442e4512500500c000c1070020b111040206d50b04090241600141600c0c2c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 383884199 1250 383882949 383883037
    0x51207060906021f0c0203040305030f090f04061d0402270a0e0604021018090218010215060310050c0f0f0d0606090f14010c0209070c031b020901120305 67
    0x60707180c050484e11012454440c03011015400000022030885500100e03041d011441a02d092035145d170365403401c40e03010f00802e070400200440d0104c418540480c91b00d0089500300d038104240c03443c10b0000001030021516090070f40441d680040c05640311060320340c0100c1e04607002e00018402c9105410030b024800d4441002d998030b41208190700a000080300b5015a400920407a881400440f04a41c00c1e00c0c0b1070725001214803254000070f0704503400e00103440b550000000040705c50101e40300081c40c0000c0c11030507003500014541800080d440100b414034003040300e404045125600c0f0300904000d4421281e0650218000061200d060b0380b03608080d28028076100c00034008a5a2581c1c2111080c00c14001c0c00e122641c4907004210f07032400320041021403007041c1000d020103885e6030000340801100325000300200c1ca94520760340415030300608007000d9016084644151142c1500810b88840050140d070401400d0890366105060042d0191801075449540400043d1107150039001030620095001400f4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 383885449 1250 383884199 383884217
    0x207050a02030d020d081e13051501060512091605130209131d0c2d031f060501050301150e211b030607021b0f030f0d08011a030a090201030605120706 66
    0xc901e0030710403841f4140e215000d8003082d1125038a4446003424800101c4040c8121046000544011030106008007800d4440b035480300d4400c62030318000304004004030250780001090901e000b8004100380d060324001d440f50010f000e1080707880e03402031052190343d6a0000c014050b2000c00310080e0440c5422000491511540c0e10080d81c40e45ea440d14070540890340b00f0550450400c104540110720740d440c05000c004c0d00000180c241c0440d080c014007585c00b401c00c103012090006191681c6c007502c00100000e1030030307903d1985020180c40306140000141003c101562900200302d507168111065401c0964105c0da85c5040d14029141e07840d280410601050700013030113007803518903000c0b0314075202c2e4020b500984004240c59000c9203c0c5007000c1c455a61020070f8440600f80e0361410800c1441d001c850700020f1611040c0000c01070704030740059122070103081402d0114615a502c2d001a290000d00d0000045020445440140c000c1d020380d40207107400604e0140c904445007000280b4108940c02a1944524 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 383886699 1250 383885449 383885461
    0x1c06031109010617060a0302060d05040b092a06070218090606100c0303240306270f060c03063209060f060903070f0f0f050913060207050a02030d020d08 67
    0x5900800d00c9100c0c0412024050100440320b800105030b48040f0080101c6d080c140c0366030000f00a50030480582c06000c0c1ea51003004200521840c01642142100d0014420100540380d030701e0614000c15002072154440c02000c43c9180c8401042d1180154000c02c0c0c0303034481c000a000d10b1a589800c845104442c440c180200d155414086500110116241d46081480205490030340240c40d0708140c50242c05200b0501d06628500341c00c011014600c10340000c034001c240b9260801104504200910301c0c0341d003004902d80092000b041400045901032404940d400d807002c07041d00180521380c004904070500f42c0e840d040180510641c056042621650703a0002d0381c0d004140488040d0854035980c1154103244580384514020015183e02a001012101c595480350440404081164401882010b600405102c00703190340001001074a02990354819038a8103c0c1d002031895003601c07020700819800a018824424144540c010103078016044862102860000030343e600700171818040002d40300c0c8080f5175 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 383887949 1250 383886699 383886709
    0xf0a030905010c3f1115010509070f0c0602040f03030f031e0b0f032d030c0c12010b0a030804060e09090c01083c0702030309211c060311 60
    0x1d1002d03040020a240e422156400505180c0c1d00e90200e1540002640c0384c1c0844103100d41002c4610080f82c1d20585010340302032100e0310b007070003d0340c600340250002c100500490704c400d04401d80c4410755140c00280d01000c42002e99a1410001024220600010700429560801342c00700702203170311035500c04505080b0308404400f01e910803460149103240318080400000309640101450810003440d0714854107140700002d142040b0690f110303080045010b24030040300f41081c0a49040050400507528184101d40407689031a032041165128030846420b1011440d400d500030408054050800180292a410a040a500144114000566410405803035420710040e0280036840050041c003145082d480190344030b100c000c00c03080e40310000078240c8150381caa80ba820000c8003211200c0342c2c804410101043e00c0c840300145608203660040013481000b440c006124124030f0352407045a04a6818814079400c1c034407940900e011140c05050141401c0c0c8000d5000c0d0044a1103580340310415400142808 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 383889199 1250 383887949 383887967
    0x7030813090c1d03030d14010501110f0a031d09180d0507030c060b19030b0105031b010f0c03020708010c05090f03120a0507060902040203010b0d05180703230f0a03090501 75
    0xd440c5400f0440314044000c0e6059240e80014203403401c00c140e9044001c112501c1214481141042e1401003204d540c12400b2402e03492641000b034140015000c5050381e4401d01404000c04204102c010001101042010080d02d0780000340b003481c46042c0110700240e402c1c01944210000d015416411000794000d0084586c2c80f83d06803600305c40f018017511070800a0010310b0f0416084141c0c54100401081d5070240740d000355200d200814882d5051030249480c01b110060b03500000c500039420100c05c0c0c0e03080f00340502440218035003040486031515040382041c94aa101c20095824100030002558100000d01b044003801e0340c0d1a0401b440c9203080540c3d0344800c3c0c03000041d200081040c601141d2141005100140c010355001c6009411540810102e038000d034400b0345099400300342c00c030080c605d90080c7c5411a01c0c48024104170103000002d0f81d11b0344200d200081c1a40e40302c04001700a088510602000a60310005a4664694241c1d51a40b14001e07104118001400c1100110310756026070002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 383890449 1250 383889199 383889221
    0x30705060a140306120102070312050a090c030b071e020106060e030303070e060a0c0f0c030605100608010b070204090b0c1b16031203090b0408090f150f070c03050703081309 76
    0x1000d0a80240c4414000d0b0f5400a800d43d030f00108500d040380034a01007400241110703403090b0b81d28079400603503544c00401c8a9024041c00b100909014606021401102e9660266a0820201907094582c00c405031031450070004c44219148007080c00c0501e0315010751190040381e026499150030448840d0400d1303180d02c0b045803681d0101d550144030a0751070518030060f159819460400640301c40b2246c883c10210085003004070707440602d802c1d00b07000f040454000d944d000200c03245a894072030700708803000d003510805024007000e00d40d01103080c100359a180d0f0031032104030f0b401004100171403d003a80c405030107a0212031091b8095100d0800503502c1c1d100003980141c60301c00810800449030856541000d40c003148400c9404150715140e085000c14000982075006510607005196a04451401d10030300040041e04c003803003403540403a1544820501c0085490490100281c81d80e51151843c0c0844903145941001d0b00740d00c910080170042180d25001050940724a42086c10100c2e80c813202748054410300c04903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 383891699 1250 383890449 383890457
    0x1728050a0f2a090b0f0a09140a050405060f0409060e060601080108060708191a0103061d04060509120a020d031811130230092a04060e09030306030705060a 68
    0x119880d202c000b4482d003000d5100a1514480e501d584860ba1070050300001240d1080e5200010700081090304101d03a04001c210b450301502c00f44130345200064184c165442914040e68a68001a1940e41c3d00207805904500080041200442c41e042440041c9124841c01c10039115910200b00a0360003401e1032030403524080300524080d0303190310049811f0b41002e4044414840115048404041103005120741003a61f103440d04040c0d1302d11300c0010107a41481c6d01044203030a140c8088906035484c000c0c81c0740e015800440114140c2c40300007106181640d84844100e4240001c0f0340180310950100d0520501d0100c0c0d81c0078020032044240c8003820401c403d10080400402e9060302013603041180440e2502c40303040000500b080e1082c004501c02502a102011503484144280303403c5010065004d0780015219000b0241807551517902d0111740d24002c59000e031f84c1c2d090703620301b100340da100d40205c0d0107003a09080003846d509004822035039a42060300c015200e4054281c0100f0141001c0717003980d122101c0c60755 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 383892949 1250 383891699 383891741
    0x901080601090c05070c06210221130506040c09050f07080423010513050f010b09010302130603020312040302040c020f0606010c06060f03050a0c14011728050a0f 71
    0x998070b00207010001001043c03000c00d1000710085007413100100000e00807511140c920804c0d0700480d1462601000d10104032501c1400a4140c104940e01c0c0c403158000414440b2106407071b80200f4200325000c18100070001d202d82c004100c20000e802c4659400c03a0000f190501c8a5198032090b5a816501122a040000c100d90001030211b200c1a008911034500141c0d80305481c3d554141c01425254220340800c503241c2e56421b4102000810000001c070b502881000f002a0030036400090190070701840068401c150f0400482600380b4a644030301c00442d4002d040741e1036909080751171101604144001c0e0310851801039120311550020071340c0146041260701030480c40d52050015030b2006502c20060317600c05e40c2d0360008561941005071410166000304000e140c0c4596038600741641f121907400c18014100c6050b201103407660098100201c89a000315420b015130ba0301004800403889400c4107240e4496220080c19124500d80e010b45d0003508141c405000950302c1740704c1181520003c511002e40c40f02442 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 383894199 1250 383892949 383892959
    0x80f070315020d0e0d1e05040e01030f150501090c090803090a0b0c0c04020c0102070c05030d0f1d210d0c150f02041208030f01050d0f0b091903021b0901080601 70
    0x140c000c1c1188140380100113071902102103910b250291170b1044c03402003040000c1100c0c000d401c041c0081c41c1101c00d458054502820a950740741c02c1704040c48018460080d0454410401c9170710145500b50b8001c00208000b290b94402840f00070f00880070b5400c0c0410448074021400d03000c04021244205005800c46030443c1c0382c0080c0c82ea0b80e074840b80d10808130b401103904000f12980d440c0014203e15090500141e1610030608000c035452050b903005074820790000c8103908846402100700720640ca21820050706100700403908138000030380b00c922564000310313101044014aa005040c030050300008030494025403800134003a6460b107298078000d80700502c0ba181200290440d50400b00c03454409100140c10030340d48901d60140b024000c0000c6541503404810021103052080c0f00300c0c01448103d900301000280742d140d4450310061824042c0404c40180001819444200011040c0c060702c418035050b00c81990400030740700d0104109000300d40c41c0358000f41640d031400b4a5134506942c0400003a01160b480c1c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 383895449 1250 383894199 383894201
    0xf0724050403050a11010b042d020a0c0f06020d06080312100b160809060f071209030b04080a1107080f060921030901060506041211100504120302070e040c080f070315 73
    0x200996104071b44d00c6102e041155100d41c007407000f240e00d02c01d449290b00d41c410030005110703c0c0d0350500c061141c1d10601101c0380e00d69100d2028103140d508106488581840750511002a202d441b60b201040c600700000060080f000000070405032480c02d501c0883c6d030305c0b01180818212054820701880c4402440385e0418602a0f07002c0842c0b85110303416061034280b2041c041032030758000303815200c0342d01000f007001030600c0f080c510364140e0704041e071078202d40f21815907644079002200a84007400407000402c1001c1c001d40152445100707022420111107805a80d1038405a0325005042e00b00000d00485001c11821b0340c1c0060203804042c14126600b03c401e40b2030300001303126007008200391045d640b90303103001445445420040000d41004141428040366a080003c1d40e04400301c803080c00b4042d405056607403164010b00356829100300c0001c500d4419401e090480c40d112481e0072464201c81031109001c104281e505840c01110300109c1906d02c00a00c0d540d082d03850b06403034400a0250026890561408851 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 383896699 1250 383895449 383895467
    0x3020706050906070605100f0f0605030415020d140a140f0610090e09030405120c090f10030b0a0e191a07210515040b0f0d05030f0724050403050a 64
    0x405040c0c0d900f0f04c615916a44140c0310240d4407401c139121910028403c9000140c02d00015103c2030318010001d42c5440c800403c0c5100041c00a010881e0003204010b4581aa404031395402e01080b000740410010600240740c002002e03030300705c5145446c04084030b8003109080801e0344191400401d0340d400e13a81c2d142c18000d04034a0a0500400c1107070042c00407802c8880e07441210f00401c50344004544a904050501441850410b1103140395072180495888503a10001e00030350044114114070251380740c03980a803031a194184c100900c0c5058600400c0b186000300d9220300790b2440c8503000c40d503040a01011040c41c0600504001c3d0000300e60301c611614410044d080d050304a09185003100200d040d40c2e070000210700ca5025a40031140d1281300348074403002140542807203941c0443d010010641c0341300001d5500d502141c1c03680e00070329103001c0786024000709000f9102078410108110b0b03900c00d42031406e003494200000094009900c0d20300f00b0000c43d41d0354030482d1b1042e80c4c1911913900d025900181626200740d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 383897949 1250 383896699 383896717
    0x40201090f0605030106020115080d030903030f0908031b0a0c0f020f0907170a02031501030b030115270c1b051f0605011d0d020105030c2b0b0a030302070605 69
    0x1055580000d1071281404501c004200303a5448546039410080020700b921107080140d00001c503405001e228018000c1100054032070340b418009202c0c0034a241c143c029044040052500d035251081c05014004c02000175440b4440512148400705410101c8009602800741c0d00c0300018201c04007600010940d005600c1494002400040220743c2100003403402a0100c0c0c1700400501c400c030036040680d40079228a41c014049540030341c11031074424031010b001d011407a185030405403103452603c0a61001c2d4040500a141d0605880c0e0300e40c0c541105400c08402c0313090041404e0f41015030710100c1c035140c0c480c0030100e490566800c2c0e000747c4042070b506040f0611540503601d500448140c45542810482c1d0000041922440030452918000000d0841c01030074400d0440900070b84d00c5105681d555418070030f51582d0901705140c880d1100528401c280c042d5101c084c40469954080302001c00d440d00c9030510990584030f09001c1080030340709202c0307030325107a1000070b002da400b6850600289020b6005850189 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 383899199 1250 383897949 383897957
    0x20c1f0f02031603050a1119030605130917040b071103240703060f120321110702090106032307030e01020d0e060c03090d08060a0e0a0c0e03150f040201 67
    0x620400d18010899000b5242000052038020342d107441d0316054001d0302d90145402c0707010440c0d4040303542d1788820ba00c1f40d0704800940040164a442c0814040d52049000e40806014648044034084540c0002c10100d00c0603901c02d8400060b00b801104244101c8007940c0008012504001c1190b94003a60080c0d200007481d818064940308181c54003100c1111160641c1c0c03450040d6190600c0c1e50090100d0311660040c03600c881c000402400040740d5402200d0901e0741c180f42c070001030307001c90182c032245904102107580d0040c00c004001039250b014030050304400c0c0c0200c9550580f03998a000603802c0380c00072003c44e071a0b0420401c00b02a511030841d211540b054550502290700c1501e4143c030f0382281e204944d0202440c0d5107441c03110388003004001541d070101855041910358100300c5038090ba10000054078608000310b420014515848605001e4020802c071408020343d8240b0302c640c0d0019041100c0002c0c00100300c5103840a881c0b90001d43c0307810420071041c4660150325800f80c03950784040020000d0b4180 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 383900449 1250 383899199 383899211
    0xd06061e03150902031203060d1506180b03100b0406050a080703050d03090206030a050717010605030f2202210303010303020a030f0807080606091f050418020c1f 71
    0x40310340440c035810400a201088101141185404840c4050707180300078181500c0c003054400182c40000e4810401d82a81048981302e944501c001a004501038400500511034518101540101d5801c00c2058500c3e40840b03c0e280c000d0300944004442c0322001599050303203d03052461404095600115081d80040c1012404940780c0022a00c0000d99910002c3c240d406007400300706000f000d025004442007285000e00040c1195000198103020160560420951307480c089044107004801610326002c01340910000e642e540c460180c4980c0044034101412415a80010b16601d1810310100400810450298080c03040d9020f0001c1252840c140304580c488801554000e00410801f440c000e610907402800c91390390900e002007049100e1400d01003800aa402840031554105a000b9800f03071042ea02c040c0c44e40d00d403000082412680a11140b02d007180b02c41010a0395070301000520942e001c040c2680800303030314400340c2c6d000c07841100904944c58000c4d140c10301001c4030300341f400074407100307112800700d40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 383901699 1250 383900449 383900459
    0x70303063011091005010e0411030c0c070810020702040c11030a05130b0414100c0b04120c021e011106041511071709040b0303030f040b270f010e0708030403020d0606 73
    0xd0182c00d540b009011800444d08200e69070b03202004a940304030540d000d0040700e0b2420000700c3c0600014001034481c0c04085450011076404005000050003072500b150300500a0307030300d0440203500140301a070203141040588074181d03005080a07102c0c0507104000754607240021000300c9198021807142c08091482c0000020341400c100098005800c110800d1071a6001b04070411081b0781c0d03003400100a11040325000d42c0452030300c1c2e202035809038002c1030303079050580700c03000444160100080003540300314170018070034187c650007128500c0c0c100c0030f80350140340b540700b000000e41d5440c0440d801801c51881c00300c0800140300c5a00403048100314442c409081003190381e81c0ba50200c180e208290103902001c0781500c658038160103010340c1c540c410b070301851641c1030007100c100c8400801040a407801402101050091b40b020255403c0c41c1d142e007407003a40c080c005103410358840c1a0700110320499800d008c030410258001007803243c2268903a01c002c5207890700e1a07080c440141e0384454255001d965a031400a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 383902949 1250 383901699 383901709
    0x2010c061802030a080d06050102210f040509091f090b130804050a0905160c050a11010917060108011d070303230c060403030c030b0303040e0a02040b0c03070303063011 74
    0xa140da100d5012a0348400e68814284111007442d84041c1c11075014180700e9580f01c0c0c0c5000b5101800000003000cbe50b651443d51200c10062150f5404240c0101e90401003000c6400c02080400d2000310060301191207121280e128000d0b074800c00000340190101030089100c403000c8515002696200f151840c2c101541c0b0000100c0c40c0300c0c03690061241039200c90070406421807158810781403405a0601240001c500e8582c25603d003002040100800303601c5043c80d08580c0681c003150000c1c20000d42d0b8176401640189001d0302c0d040284508140c0c0d41c202030459140000701400d4500c0e64645600800019146880803145141410b094001c50040c01241c2860000d08400900c0812181350003440d0f58101450007c08845030311084000709840c11003000204d1f41e01104a030100d405900e0180801c0c0c40746403032800244144d62100c1d000c1d0a0009051100c02c5001c4060100c05003c0d4408200840d50340c1c80d034a2010303203003e940424a0001c01c0500c10040494110203072858050800c2021840405001c00d07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 383904199 1250 383902949 383902963
    0x150705090915090f090d08040312180c08031c0b18070c0b01230102120a05070204020d02070b0f010f03030f0809030d051f06030e03090120013602010c06180203 70
    0x140b0704d12a44040080c2808200860a40040d580c500b010551409890003000c116118a101e084640c03502a81e803100c0b158120300700d070100e03088070317040c9101c65441507078a5403a440010307070814988442c602d0759505801c0d80700707050429001030200c1c8114a00e50031000000c240c0141710b0300c10b04c1941d810700004206a101e40e54080d01c4010300001e80c054001600c0b02c0741180d190b10ba1411984001700c55131488042600b42c03900c15441d410665114007407440054007038090992841c40e594408560003042c4140a002ca5010b070548514009035a602d403840044149442d00018010850300c11503640f0080c0310f503a40c1c45c1e20021100550307081c1a50038a1000c26550183d440140410f081e43c0c2c041c1c020700319019000020003403400c00704002039030041c00e00c0d02d034001d503150941400750501001c8829108105500140c549020003005400c8000740030001e0301c103401c1544110b00d5544409911184124400118602d805841c0c2a6010566968240240416014040903801d030340c002d1a0058400304905 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 383905449 1250 383904199 383904211
    0x9030605040c0515030601020d031d15070906050a2102190305180a03020a020d0201210603060c26040212010603050a0b130b0106050a092615070509091509 68
    0x1402c01c9841c0404100c5059a5456050b2900d40700b08180718160382c00080d90b0b0041d2095080128104541c10807030410100940003401c1240141e0019002000b0f91294041c8200c40d540c0722a042262210f4048603039004042c4d42d140418000c2c4000b0f43c0600d00700f01d105480c170304201800351508080d24554009100c02007460008240c0320814441ca04101c4805040c4401480c1c0c002c101c0e103190b80c3c500075910902e000c4068040e42d4004a81800d691041a11001f200c0003649003000260701c1080940c01000720784020744100d0300d1b046441ca002c80c030880c030071842c8401d2003010544402c840500840380c43d00140c0101d9200c5806020050000380030b0180d00e0044d4060303009018481101d04014562050040030701000418521900c07001480050000d410b40d201464055140c480c4c66109070b61101d046c0c0c00ca07004018034840007030100030101c8000041e480141058810341148003000e080729078815542240403480030b1000030020700f000083c0d02d611103081c450071020f507200d050100d0a801025078136 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 383906699 1250 383905449 383905463
    0x160e0603010b09060607170d0203310c05131b050904050901020301120305030c040509040b04140c01050319020904020a050426031b010b0907030c09090204050a0b03070903060504 78
    0x401046190a128015071202c040d55000f5940c941000080c0c0c9903c11000018090515502d40407082c1a08400360b6040300e590007002c6651381019460140010411040c4c0021000c52150705078195020303035011000c4540c000744840c0ba80e4148402c2054009480103440f8403550343e10540c0080e940b042c000c100740d0b000141c03100c83d904c0001c40140800c3d510300070501003031030b801003004102c40318891005080150300b5282484c2c80b034407006450f1120b0710955002c47ea00c5424041404140728090302c04034081c0c0e1017410718180c0000c08842d0152100d45a1841d140402e00600000d9140d1840503000304080300709500c01450b0408800c0000d0498202070802c10002d600403c040c0301489140041903140042ca0b10711404440d050880c1030354a01c60070120702c4d031103900721890410400342500888800380b4014a5000d0700d02d400b1000a000f080540c41c0e0744001407031500005900d003210310031107080d21400781002c107003241404150b81159002410381d10402280c18400000314885110f131900452007404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 383907949 1250 383906699 383906701
    0x2040615020d05180d140109151406090103150f141b12151c1b090603020a1a0903190210030b0d120207120803010f06020c030304060809160e 62
    0x8000b80381c00b001e400150180a4101300100c401c0341c1c0810703801000e41e4202c80c0307600740c101d42d8581380390403c074812901d101560800c540c4808100c150082080d280c003c20707070100b000701107040e6013030403070001614113036040030030900140301180700c4103040c100d0b29104180104420511350451000c480710611848085100785042c4200c07a0202c8000d000d0030100f410120381010b04560f0b0540e46031310040c10400e0329080030300842c40282c4500c199000c400d2300366451465507000301c0c284009407007020690f05030700c07a0306151b0100b903005c0240701d071400382c84d0040d00c9201514208160342c07240d08812410301003000d505100c49c0351513030780812120306800d00e014031111034440c0c58414001400402c080c14402c4c14144908d0008544400c4c040d51445030b0001d51500c491041d10506904003003035130304841d00c0c0010070b640d000144040381005604035035905281c2c50f0035031b65928040380c8904842c4016641a0010401002668410380c03001d9000407509055842401d00ca0810b003407403207403682c400581460110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 383909199 1250 383907949 383907989
    0xa020a0b060402032202030a020a081b030106081504020d020a03120801090b10030c270e0a020c0a030c0c08030a030c1e02101107020a0801060e15060306010e0d020406 73
    0x12555900309030180c40640c00d60078564a510030385e01a841031480900445003080f001c1d55020040042016000b070a2041000c2e01c91407200e49480d001c15500800701d040c42010042c40c10148294801c4950203000781032808880040201050805002642e10428881144c0056614400c0080041d486800b41c82c200b03071500f5201a02030503050303002c0017280e03203410410703902610340600080300c50005207400641455503201c16105050360f120788020308855503045c045175500c2c0019180603903d644007030540541c1c2c3e82000c0800d0703100d500d00080107500100c0e64a400203005501090b500ca204101264915803103000080c0b458108003d2b0900090b100c0d651100142c1d0083c034820440c104801e511044405c008101940e2040155554204d4903034406c10003007104140340c25500e0003980105403408003640da01085000c1c1c00e480c025070700c0034080d08011a001e012200041c500680010305002d0865480200564140e035030f034000d42d60480440840040160390702d01c0741902601d1507111038440d0075140c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 383910449 1250 383909199 383909213
    0x40906150f081b0c0f0d02011a0a05030a060213080f0c10020105070801170f070f030506071b0b1005040509060a15080303180111280e06030f0702120a020a 68
    0x44100d107082c8200441800b40c02094a01e6010401e52041c0c400360343e50954005581c030f40592402c40d40018012998072040455064000f6040a419035901da07019404150401412001c42d10130a0750541c450074010002880a80182164503040e00c2c0000030b20340e5440069040104004000c1da01d138100740c1d44100c2c01e00c1c000150180f00e800c203100820403031800c118040c00041042c002e92100107050303107881703c1d00c290070400203280c52010015120b0482e510303592600c0050850208581e03d000d4013001a107140c2c821889020348003c001c1841102031645e84401d16a00c3c0d01400b0551200c014880100d16511603015040c06400624024480346c03528114801c1256511100c960300d1084824040100303000000c1030701d411880134440d20321007181c49132505004040c02c00b400c0068070008242900c40071202d511003114a0b0000042e1a45083c42e04000c82e1046038806801d9400300742840482c0e2004040d40f506a0301c151355004403403207466400c1a00c40c803504020b01d40c0c03005a119100120800c214 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 383911699 1250 383910449 383910467
    0x31e10050a020304021003050a06050307030507030c0b120c221701140108030a030e190804030c0803040308070b0714030c18090603151e0c040509060a14130204090615 73
    0x58101d0450842c1040d0340060034074188855a9400c041e1580c6c04150301448980c403c00003000d0040441c0d460079680d10701030707803284228070080d80c003000c030240c0c009802d44101048514402c0704080c002d109a58103c680f0105070002e2048907182c9018040b910860040b80305c1580c0542101215122426a45140d031400d440c1c4004501c0000e06100004001500000040d101d031200c40741000718004044032880343c500017402405001e09002c0c1c040c17003030502450740c004000340c81c003440603c11159204c81d00c1550741d205500c4002d14010302005801c01040680c419150000041c1c60003c1c03081c0c840d80d0300d1a0154005440024203083c0005503006200002074001d01c000c3c400361403060543c6030100c000b94039546e8202a40d85920138280014044c1441000f01c041c0070701a40540c103815041244c103110181d08035000b07507409898202c010566610304540d11500300ca46594010030811441d4090001c014580f0008541c00354080c0400306800340e190040130003400c40c82a0402c03a041c92444000c002004c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 383912949 1250 383911699 383911711
    0x20121020f0424030b010806040e100504060203180c03070303030507050c06041101112802061605060105180405101e020f0d051003050d03022b0b010806060c1b031e1005 74
    0x4a004e005c02410f90b042880f443e8411002c0303800141c4c0103854061070307081081000120402514181c200020070203a0b5010710302402042c90810034a000031a0401c0d51180000784e2542d066010b5502080028840e400613580030610749007031070401e00c4401010f0303e4580c0c240d400311607289810b22615140d5a214a4076a1620034071030081800504103000c00b800b4002d94200c40c885000600c000c1e0040d074642c0400c42d410511305021214600c2001e04148d81c403110203028962141240b100341010b903030003001086000320342200240c1003078040f0048070b90040c000c83e04115410840c000058000d400303280301030701c6a80c44412005a46000c440c02040c100e0f0402004085414085141031000c114002480603054101c0e060048e910919031080c0e000300000a140c1d031001410902c490311090403103400c251100b05082e2981035545c1ca40508000b0076000e83d0304d00003501d9100450403a54500c400c9a83c20b00780c0006000d446040d410b00c80340c0340d104071412405680691200c4107007807034081d03680309044d440f40e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 383914199 1250 383912949 383912951
    0x30605090f2802060a051303060b0913020f120115080a0515040f06020f07020406030807021509060901180e0f070e0607020145030308090109020121020f042403 70
    0x40c0b5900700120300615030b600040e0080c1e0b03000c01c0d13070380640b80a202110040071102c1c04004000341d0303d14142c0003a12112035068003968282c40410b20ba842030300502d00c40168010120144810a14180900000040f84003e000c0d901e82002ca00e110941240c90009400400d014080710880350900f11b203018114060410086100070800000c10200c1d42d00c1c0343e0f40d40c3d2140f005a52400d420140d41c15134000c5600296109107068000010002d1200060118500c01d6544034203e91400c0d50b1070f840381c015204d5203034000d90100080c07406507106401c603040f07030400112640744035619420301a010b05011190f24400c041420b05000c1042e07080001844a800101c680d94a0b2618990000b068040c46030347c22070301e07084071898034541011a00054004c841c040724004d8000c40401004070350b4050548030a42c00314003840082642c514045c028002c4643d01a102d8a1001001c42000082006030880f00160150300b405044800c0004030010002403e010944a45106040089103883c51a0842c220f040c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 383915449 1250 383914199 383914243
    0x160206010e01053105070c03030b15090f0102030705012408030a050409050720030a030f050906150d080424260601120f02041706040816030504030605090f 68
    0x81d41d44013881400c0c40001008040090040c0c0401440221040300c4d1200c80d6090030304010f08075600c2014106404d000b982c05018100d40c0000f80f104200c14000c80311036180003044401220305008071612503000041c41201c2c94500691255400c40e0892901c4584000070100603484481d40c08115002412101d4007562424000d294050040c0c0b0640c0709505243c0c3d200c0c000918000d0061003140c0c0ca0368a0749444e1020602d02070309890b00c0f80e202000d1280844e140844d415442c6a40d481450302c50bd04101c02400036032544541e03c04500040c40d02540c0c48090311003a1000501d8220181c0300030200303c03403c95890710030b1690301100c5000360391851003000140380c5803403000500f02c1c0c00c0005600700c40e40e02c6440e075201c0000480d403001c01542c6482e40c060415114126110140d03000300b003150324402c40c503032541c500d40f514944c0f07902040d603026286000038010010715074240300001d8126032003420328501d0580d1342d54440381600c00803110a40300781c12413004900c100e5828000c0d03c1081150305041320300c17 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 383916699 1250 383915449 383915459
    0x13140315070e220e1603080702040e0c1503070e040e0a0f0309051e0a090b01080a0c03060512010b010e010509100804020301060306180c0e01060c0803091203160206010e01 75
    0x4148001411070080008418400582e40c03035800304078500b814443d02441ca01c1150600b52000343c9403c2040d01428401c0b600c40007007441c032003d907500503298004049032030b2994503020040a0071705500070074100c0c0240002c9804030b41d18103807400e01c040814800c180d181c1c81c0040c0050820350300502418010f5040c801007254040002c0780001d0420f1744000300c0c0100c010242030889034401c0303640180740c0029921211810030a000341d40a410507000b00c5c0d0305240e280e11810729605454100354014041707445c040100d000d040d03c81d000b403d1038401034603000440556400019504148248003102140d54810603d5400d5920182000c5581313001e0038110f20f00385820b008201c102100d1003a840400055101007000c41d6400c0d00018011500300c0014070598002c1130102e62a400b071803800300c1c0c1d000000030002800071b4500c101d26040340da0a0301d50020040c91a1903100f82c03039100030301d4900c0c5805070210002c48001b00c1000740d0b0050000c440c0f540c0c03e02540210192602074180c00c4019400a51401003203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 383917949 1250 383916699 383916733
    0x7240f0e0904080a02101107060b0a0303090e09010207081308010c14160201121b08010e09120901030f11041d040503030604090f05150a050f090c19030503131403 71
    0x142150f400101c07195141d44000c0c00700d00b00400401d80e404e02e1820040320070000d4001801a0003c940507902c1081400f6110042001e0141c8900c8000c01040b64203004001100c40e100c41654843c1c001c4001525203507440c0d4803014a988824400400c83d0814801400150001d00ca01e2400100906100310390325400615040540501088641d22200440081c5d045900c00c1340d1080115040c032009002d20a2010413118052910003038100016002c1800040c0c070020034080640201c120310082c0081c0000c0c44448611503200c05c1c00d80b81415101c0c0120706041005101d204108016016142d4907181082920070103000998400010a110b160911000c0b81001c01201d8000c101101c00250300c0072a850f1195249901150103130080c0100e0120b88a12010b00001c0384c03203400f03011010000340d0b4034862015028507085c2c1d01c40314960301004040a65080080340941c9a00001c030103a0501550380c2c1e107452540e40540010700840102c19001c2103c103c40c3c4001c000b03c11070440c040c0c081c81390a4401d0f80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 383919199 1250 383917949 383917951
    0x8060a0512120d0614010216060309080c0a03030f0b03010207171813050106030f05070206040b1f272306150f0909060a060207090e07240f0e09 63
    0x1a01c1005241e40750100d2041c100103100030810001d211603119034001c0c42e000020603c1e4403405820304501d40c4010499840411641d01344038540108140da282048c0c01140100310740401128581c2d0100100c2407a11030030030050b260b661103540c0c0440c00000c00442d42e4280e41d0383c000d686010307a00510038440000c95080013030509001510000791208022029158865a5002c801c1d4200c5070302460070010401e503401c02410384100e514207100403102d01d96460200e400440f081f100603000070000c5800508146a41500810105c0c2c0701520140505070b0025548119400401300c5401c0105d1803840d16200740b120140c55003400d404024032003040f140160401c0840c6400740a101201700040c4840d5a080d05100e542810b402901e41c45010131508100f10317500001c951842a2407040005403186880107903001a00c03000e9000d01101490800b8810151013600d00454070350284030b0003c200b000f5950f00344d41d030449182e004100e025504441c05099020f0450f03a000c108845004054001e4588401d1030b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 383920449 1250 383919199 383919209
    0x330903031b19150605011403070507021f0c150204030b18010e010213050405101505210408070c060201140705090105070b0403032003041a09150a15050108060a 70
    0x100c080404215499040140210307280099564402e10308041c0803041c4002201c4540e144400c00c01e10b0b8031a00150780c00150054900d070b2041041001500407841039014000140c40601000c40d4048400b940d50001c10b1060b03058400a400c0c480000d09200c14544c402d25001c0f00c01a0840c5040c0c15030311a0701003280000d01201504042c1e03002c1c0800c0b01000d5100180c0031200e403000b192284198504013000b2180e40c03003440d108030304040129843e02080e011480c210f91100e14818014a2400b20a403010740220325042e86100d40300301d182124610b54070b85103100350310409181c3c1da201001c0c0f9000341e840d185038008404580c074000034100e02020165009170041898180035454101c004d004841c503100b0742d00000e15146403001403204264164121840c071000101841014000c5148a207403a8002100c000c0c1245944020b50aa10b240341c02c2090b8212100c4d0040d50350084118446400000003500e0b0070500030341c0c821000c400085054001005050246804807040c1002000203400703082c14051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 383921699 1250 383920449 383920477
    0x1e0d02090108102a0e03070e070201050709150c150e1002070b07080f040b180d0e01020709020a0206130f05030a05030708061002060a111611030106090c1e020a0233090303 75
    0x48440ca561b800c02001d00102446405402170340707800c1c44001d0181a0568070603000c0f44101c003000c00c2c400d0600c1103070000c1c01000d54031003000030398907201c610301003007804074811a8565941036a00c00c894140051802c840c3c8028015940b5050303403828860300c440007440d02040150178424416a01407401249070881d401c250098801d40310500e41826010050900350240d210340652240c01c50b03085521055000000d80a46032141c2e0384000c440c2c1a482080c5501006030401d1000601c031204140c213280025009035400c0301c3c0d260301541c1d060303c5c6901200c8003201041000c020010444c0d4000011607000c0d50580b0340840080481c2c1c070107903440760040c0031702c2842d94440018040302d44000041d00e00c50021021029210800c0d424403c1d030b80383d109903140f0300035420300c20b0110300d80085000c0c1c1120203c003a92206603198850943c1504041c000c40e4000450007138030091405030740c403a0b403a4044150740c800c20340001d10160304819592600b400403444422400d110244807654048143c4400c0100040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 383922949 1250 383921699 383921717
    0xa02090609061f0e100c0c06090f0b030a0209030f06010306060f1a0c10110a031b141803010f020301080105090d0f1b0f050106081b1e0d02090108102a 66
    0x20003501c44050200e13015030006408540d003400c2c1940605a18811405070100719484c40d12403d080391600c03041d006074000b2000000d020040c0d0344241c002141d00c00c10340d813030040c20700083d00002400c00c0c030b440306e0000042d405800144180704103841104001c10301061801031091400c3c4160104403c0c8103409180d4280100c0c8480c0d20351000c0c030030340b842d900c01c0410801c02030300c0e030300d400c2e9089410410500c40082d260400e080001404c000c060002408140c0b1070807401d0300f427100c5040060340505e07800c010b2a0001c0e040d08015807400d000e0201c6940c204c10015840352304044950782121001499403075154400d9070081c0225030402c00c1c0360700d01c04152800244c61002c03044151100342074108014082d103204c00201c010b0000640c0100e0a40b0110342c265034041071545e00f405c2c04651008841036004000a50740700c030600c52800d00c0034003c20068603042d0010b0f40c43e000580450401d0380b00c44500d030009000f0314ad08080620032010170004242c0c0350110441d80b0030b4826580d10101e80e4070014001d0f028 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 383924199 1250 383922949 383923009
    0x2070603050703090605070807030c0203033d0f0311030a0b1503010b0306090d021603080a2118030e03120306040b060403080f0a03140609040b1f0303020a0209060906 73
    0x241100d13100369007018040c809802e14107402010280101c481800003803070030107a100704600c08800c0300e00a00e003980062a840c1a20a6104402035060140803a0024061940003128498240c0c3d41c0c010924008000c01c02032071800d00348414100c0405c0d442c800d40101005500107119548542d8014202041040c1c6005c450b034046401850700440b1554184241d0041020301c810001c1c01d07044280e404c1d401d82c2c50300110588048040c035214000103018030000d0107a1414148100841038045510090000301d8a541141c103808543e00c1d0f800303407000021241001400d043e0004281118846c007a40104040c0d40d254910b103a0b5808042d103130302e00c075645611310003000d0741d6000c0079034014581054507160b8421803a6880e400660000c411440807a08010710b800301c606060469902c55100030702005990356503035035a80c19140c5d0051840741d07080101d6942036101c44200500360099072194000740088611401000b1901100401251103039013001c04106c0c10f900c402109000070581703000050040c5040e2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 383925449 1250 383924199 383924201
    0xb031e13051c121a06072609060414010201140403020618070b1e04030515090d03020414010c0f0b0a0608060f06010c030815060f12182109211c02070603050703 70
    0x6422659001c01701007000d0013481404800040c4208051400803601c1d0412940310502e0b025403030603650300c00b03070501013000f02c2540c41d51460115001480005448001d9405040354502c05071804da0050f4840c00400c5042a0614203101c8411003a030004d040c000c5c40c0c8056200b080c4500d146400341001d180b41e96440311402c1d44213580c042c42c1e00000341c0303121841c0d80120580c03144084079040b00b5403190040303520b5000d00a10840d803e441c881006540c0c012460801583c88a000620032503942c1c3c6078091240100d40b0001d102070007441c1264012820a00c0e10402c2890030001600010300c08548605001550380c00c04940c2070304981c181040300c1c25a5880c03000d55507040b00e07042d495401100c00241c0c0d00340702c07844e40300a100188684801c03010340e454512060070441c0555500f01140e510021034030302c0c086110a004080b07001400c030400d00d407004500210303031010310031900803a044090b604007014002c0d0a00107000885490740070440a5000311070000d580703101a1080c1700c00d0554038000705480d42d1107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 383926699 1250 383925449 383925491
    0x306060306251709060915071704080d060e06040f050c040302101806030615020313090e0c03100e21030f0606040b1c06120506010b031e13051c12 64
    0x39042d030f420410f18000201684840084808000701d010381040002d0080c40f04101d940104150742e601d10b242c4050803441d00b0358080150090300c03c400c00740090a1600d01e18007a150140001d1155001542400001d02c0251880c0000c5511070605101c01c021241c14440c098408a0ba0115008044480e80c8402034a0960380c004003054400030b944804103466030507401c90021541d9059494103400304009049071a070041030600504070700c0f20380041100c00c0c40c581040b8a4085c498040d201c80301d10100000f441e01203480c2020f07140d9600c44d100b110b0000c1041c4a004d040d1320404400310610710181100c2c4015201c020088038072400b010700801d2440e243c1e48191000703812001101c41c1c1e1181c02d03031241110f4480300b940851b0100d003060740c0401c1814506240002c0e159006d0014802c40e400e25400c840305e034000603c5050319002000c2c0340d403608040c4d07015a500850081c0e810480816003410014103151028034489010005140c480e54507a500c403501702020300c82c0550018140405601c44064860 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 383927949 1250 383926699 383926727
    0x170c120a21110f0304030210090602030307110309041a0a06080127320703020903030a0c08121e0c0f03010302040b0f030111040609080a0b0112081306030209030606030625 75
    0x100d510300c510f0500b00c0001c014000e032030007203502342d25100b540d040864904805004e8500141c10520202c0d0700240a80c44540c0c203140008141c0e4288154600843c0441e032000c8420809903544804031080c80c10080c40303401c068011860040003541c10060101d15001d103981519540904010301440d42d4034060f070209a840b0341004040c40c5500c0e0441d00d810360005c83c0044d1410110800d0049000d490082c0300301e4500700d2000d0080c5042000e00c4406980b0305480400644102804014020b1400360103240b0520800002c44604d07115815405101c65000c0010200c2d104c6110030407071700f103030b036541c1c082034a04499040300c0110703d10748581d0200d080f10340800360103600f5609045101480e900e80174050410b9170300a40e40c2c0100b00e42d48110950303403200750580c080e20310780d03250f40140107110400c05070002c528010f001e02c0f442c00d401400011850880c0743d100d940001c0d800f1030000114601484a030703400420031002000207080c6280c407900407690100040c804001c1a01150740901d01038646003004003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 383929199 1250 383927949 383927953
    0x409120503041e03120e010b01080a1a060d0e07090c0c0209060607050111091c020a060305100b0403203118060b09090d0203030c0d06170c120a2111 65
    0x64a980ba019054140e40034403e0601800c1c400c91b1480c8110500c50365200d010160754040075612400300d08002400c402e54180c1251031141603004003921008000c1103481d0003010300003401c0c0c803a03940050401030b950304200c8440c0d00706440302c07030302c0b5034001a206880d0380c04503442051074441d84d00040c03552140c80390007031195007440d4000d00c1404040e4041c206007a03081e603800d880c0c01c41000301d01d9084d00005800035840b81c1c4807201400014841d60055a101c8811450009443c0c0c40d01e040403132607049980202c9519240d018956006541c0510881204a0a41e01da20f0304213240342000002326188007c030482c03c1e000d894014200745068000e9504180c4c1d407407104858079010306000000d011031440481c021100c4d103002c100f841200040350034106649174007070350650700e0f0300d12082d05ca80e000c10604c040e00da44400b40071400d0340715040703504036050307509004041000c05c2d0010701c0501600072540740002d400201040c00810071440161280450f04107250000d902d031410140e590704506d0089250034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 383930449 1250 383929199 383929253
    0x3150d021e03070f1d0406180b09011a0105071103011e09050f1f0c14120708150109180e070602030d0b0f28080d02030405010e040912050304 62
    0x20141d445400140100c0560036a1140c60721801d045038550010311650080b44801c2c2c0c1d4441c0710000201c4150741040c807a075004900301120310840c4034088180703c1d040e510a5001d409100f4034820903c00c5104580c480c0d0780310080340e4212000a0040c0c0a1101d01814100100c0462a50303980c0070341c0320710139081203448030b03441c0110402c400c800203002d40c550841e0248a9452444c00d0a500007520746110012481c44c1e0300c030070282c52540c00103004070543c400140b241400e49031303801c0603920000d000d504441034034034401860701040051a03d240030f84840300da4040314140e00c146036406869441624040100842d03220b0450301032a0040a084000c0060381c00b6a90010802941c0440203107415003400c17109002807600c841c10021019814044243d000103515480310800c0710000003c00101813802480c04000c1e070750a64036040103a000c00c81c2c00140c20010b01840300e5030700902c0801a00354203940400855551340da6648460700200840070502ca0040005010845007440c100d1407040c0070365200381c070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 383931699 1250 383930449 383930479
    0x307111c0e28031b0306020d02031f050625050313051314070e1c0c1e080712050307051002030406050a0e060a0c0302041a0d06061403150d02 62
    0x41c255250a1041410385191400956050050180c0100e9035002104280c41d50307a8a8101c0500260034000d4608070341030010200d01c10b0320207401c2d0740244401c056943e25002d0002075446130116400545034941c800107004948a003000d88a00032a01040c10341101c3c208810b04598413041c04000703203180b0002800c440316088030004d0350201c550645d0b21a5416000b00c2d061016520300b8080c43c14401d15000000e11000d10480701820b501402a24081c1c2c0d80b00340740002c0400001003030040e035003a001079604222005156800703000b00e0713030780104d40c1401034200898a07445008500c02c05d40305564003079812060050a00448907002d1340300f400c0350710020301a0086070103500100e40030b4032082e04e072900090b611246070088862607442e4401600342c50b80c503003070311100401c5410014810142d0a11020810f03003550650010b0001d12050503903261008043e5000549140da0480c004006002d035041c00d980303c550058a070481e0043d0001c410f143d10a202040142d000b048020750322499800c817890f4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 383932949 1250 383931699 383931707
    0x3010608030d020a0f0f14070206090d140d030b0604032a0602010f0f090206071b0b040308092e0813060501090902130c090504090203010207020a0e0901180201050307111c 75
    0xc0213005a4a0b44010741d00d81d01c034241c0320004007150900c0491214017044001003003000040035511302c000c1049007400c60074808078040450301d030011140d180c0d020203044070029041205110200311440d042c0f10000c44000812185c0c040c40c0701c000c0207400d00c01da852000d10f80b4001409400340d2100c0404c813046981d003800a01804081d100e6030685440d0144403144446140101e00c0881e030050401440c2c0302c01c990b078403001e41300c002e28165218410b601d00401c500455100810040d07015106460700c9040381c104005d04070300740f40805a072202e1051040d0300ea819880c12604685142401d0510032030f541c000410914052110740240001e14150001c98500f800f60301c0307105072600940d0200e60b0764260640c00710851350580c100001107170f91910b081110b80740c02e4008130140c600c00b50025040201c00d40c04124940003d41102c2c0014001e0001c100c00d14509200c1d600c800c4034441d0110b80c1079056500080c01e1848050184810007401650784100703110704002e01c0340040144030610101d8402000024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 383934199 1250 383932949 383932957
    0x60b030705071a01050d080d0f150305121e07140601120515041106210403090512010218010f110a080d06060503060f010e0d05150a050c0a1d03010608030d02 69
    0x407484407008140880704083c07880c0842c142d500203041c103485034030381d0f844080042e0040b0f117519042c0b9445840c0c0200321021030050400f0394035180c00c192419800c40c90041e0901d8044684c0022054050011217805000e0780d800c07503800e440c91500169182ca65040894480d105100301d02c0301c40c4201c02c00015100d0340444a0ba5070036018500759034009805109150040343e0544001e0220840000b40b01100e292410003840e8003100c00304030210403400d01800701c00075101242c041d00403a0b40c541c0b04015504201c2540010344405034021450803440404500c816650b4925503070410010b4a500c82c0c2290148105201e821450001c80d4540607440c9440c41065200f40400742c0c48504040c3d0008a05004100342c80c001c5c440102120009000c1200444d8805400b1702000d50000c41418071001041091000000c0e0307000b5911300d80c0c40c91502c480c400c401d0358000351005440340420802900425446601460200c0c4e00889502c0b0b00800480000e01400c9140c0180d45680400519041202403980c010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 383935449 1250 383934199 383934203
    0x7050d0e0d0f02151810050a0c09080f15040206070b0a091718131d10140603060403030b0a08100203041407083a021b0901060c020f0301060b03070507 66
    0x4001c9803603440b0b4040741c83d0188a52a01c13038091a10011807510321062001003010030f00c410031203010140f406e581c20207440c4241c0c1c039040c0f0103980300d50480c60154401e69844c00b9090b480c4c0142a20256450b0701c41e901c8c2c1d800b5000f4042402564041021503aa4204070360085400015000c06400d18480c40c0d0011f03c80b00c0740c12135900307403480888108958018107071400461110794600c185a808020302c0020103104000504081c0d4a584001003c07030700500d41010709104c1c100a00c4030040c0c0860700c0049850307041c9145242d014200c01c00550b030f035000403000d41c803507070610300480c3d28901c40010814486d81e64000603418025844003220541e03880d4060b51003076004960541000a002c0306480c0c540c60103008003542034200648542d02d158850b03103040d2404001040041281c509000c800b0302c400908000c6500603003080600c1c10031584100c400070103448c0d04542060040d45464805007a816003440001c0c00b607200660342140607a820b611030350007020030000c481d40c1ca2900c042c00901551000c181 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 383936699 1250 383935449 383935457
    0x70c0902090a1e030311190302060f060901030b0112020a08010c121802010801030f110405040b09160608150102030f0f0403020316060e0f030a020a0e090706051e0307050d0e0d 77
    0x18120481c03441d00503005410f20f0740b12149078203640f802c4820302c4048242020a2182030101c4540310380600c640d0358102d01a034041c3c401030500c13030200300301080007500c014403481102c401400491200840da40c112142003861183d440070b0352022a107420000e0b84407032030315480c1c00001c0d0410780d00090300c0c841c06100300c1c4003041038208085100c0350154548001030300268420340140300003071200d154208078a020b00700303089010a800c2c000505841e000c41e070890b80b0075001410300c40404020410a828403034417026024410381002402408000c3c014095410b2440600d5074001c00d900a01c215180f81c03400c41c1143d41d49008034000d058a039846071008a000b031240c07803252148401e03032080a42c1611199a81c03116012074a038200002c83c01002800c5030302d40503088610b801659100b001200130080a01d0308111447c05025990038038070940d01c40000d0000c20408220702c00700b44c0040404104c0700c003540b55101e48880c0c8040760103002d560804150b88bc9010706a2299050000308200350300c00d1552 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 383937949 1250 383936699 383936719
    0x90e0d0c050309042309010c030b0d050c0105090d06050a0b10022103061503090d0f1103120a0e0717060a020418110f0a030204080618070e070203070c090209 69
    0x2000c40305080c0d8110050100d030024440074500b0b207425005000c0b0492019150501c1002d81020080c401500f03a544c148a60340d0f030242810807513010702804000c0380741118001106445510380c140c6901c0300000b0036040060010702100160b84d801d07100c035138031a0044401c10013440c000c0b200d900103082c440815407043c0c1e110010140e150348000b506030b50803c21150501c0d8201c0111402c02441d42000e80080d034032100d40104440003d1041c801345210308405002000e140c0d03c0414081c02070840030000004002e01c1610403504004008211801c0780204042d01500f983c0d106400c100804000c0c0c6c04a21078011250700041c0d00042d020b440d4414400081518259141d0101480880c8114403c0005210412180440d402c103560f000502c06032000d05460f141c400e0401c40f81086500413030741e0401203036001c9002e02c6100020070105501c06080310045015900240d80b1313a656145c50722842981421940c0007a1003140b0030b10649803000d52003640c0401741601d40c079061019401000d152805131211107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 383939199 1250 383937949 383937973
    0x2060d0e1f020403081801030f0509060601030f111b0715021f02031b090415260c03030f0a0201060b0a08010612061a0a0215010f051002060402010f1b0b01090e 70
    0x110843d0202d0ba4071800280c90141c0682d00c40f6401c8001200c03250501d0f555205072044019076000701817080f120322014055902d008000581140da1a50310040301781e24109142f04100402c0c412209841d031200400814844c0c0c105809280c0200c82c0c00503c04488488449000030b50001800403503040890148001d03c002c0f000c41c10201d000032940b140002128903528410305511000600295002a0000c01e859809500c2c20101c0400c0d41d2091060705c04d203031003c00a03882c4020316000d80c00c6c20080034094501c00500029580d02801c0c01100090380700150b5031b0945030003507100c140203140b480005c9440303100c84000644600000d10524000c542c48a2504113220300c203114900c152070102c4c1400004216038511125941c01000342c50065204600da01103e40000e42032a50003080040e42d101c41c2d0904040502c40444012100d040940d4001402d00c00142e800c1048100700401030718120740c51640410186c50100700c0c80d0310182440d2803203400403131420500d030008000d111001040342d5a100b104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 383940449 1250 383939199 383939201
    0x15210f0b031c0c020d0501140907170606090109021c060602061602150406050c1209030c1218040209040f09030e0301050c0723070f0b0c1e150402060d0e1f 68
    0x1140b038603000540300024600180b40071034a01411038052000061801b4058039904817110040c0c80410055000b54800c00c400751141514418104014014006a08185011404814040c02038420b52600400d2081101025a0320181c00901c010b0051043c1d03039403940c0c080c0d2140e106807065202442c905150507002400095141c2d0041d40c45043d070b42241e41d03542c0320400180307401350801e8034900d8100b03c0c10f95065003102555006001070000346584854440c240341c40d0030700a504103e800e060510940004183c070a544081c82e8409807005640c580d09540018010400c500101d44c07494a02020b403424940d00040c2c0e00d480381c0068008000c9500d0360344a8004601480c1801440200d00301820714201803001c544071031000001084035811038a520307800070502c6940d00411460344020845030700741c071810400d12301da004800c0110111880d4280d50161030310040e0382c4109003611200040703811900c994044a00202000383d04004521030480c900ba141d2540503200c0c141e0f10b0b0401260181007843e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 383941699 1250 383940449 383940493
    0x30b060a080402130b10051b0712060902040b041d01050f28060b070302150f06061803161706010b031006080903040b07060c0201051015210f0b03 64
    0x2194070340c1401d80d52140e081084803e24107140c40d518a48038400040e140e02e0300d0300c1400700750880d40c89030340d15802203805c05400440b1036420103005078080031b0100710482240003441c07003007a04500c0208501c2c9481c00424081d2100d205401d40051030f100a0b401980c42a19000f20001440c400034010b503107404c2c4080400709002d88034210402000d00d08640e12289445c200400b82004010104105984110349001a0000d034025400368000c180d902c090040005c0036540d0049010300b204a5604002e004104940251121204440042e00012215542c1007001e09890952180000d100d0350b00e55450503940c00860098040c0e621603e0008102e000840c03056901c50000c0010903002d843c64500200c401d883c016000080c10b0104010104811030300300000d100711070007058046406110210001d01b1a1030003001001d0400c0e13280350500201c13a4500303400c182d40c10549031100e040c7d690484002080a44040c10310612480d02000e4081c000032a0400c1e42c000c50110300341c8940804804500d251808 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 383942949 1250 383941699 383941717
    0x80703091e15090b24032b080f01090905010f0e030a0f0306030809060a0917030a08060d200a080f07050a05062b0902091305061602060c07020105090607080a030b06 72
    0x7410000007100d82006000f560809080e005c528442054210003107400c0001824103040d40040017402c1403001111640c0b50030440405c0c0c80c1085403844c100021021541d010b02483c0703202902e070800c01c400d0103000d4001c40e44411046a04100a0490148455403580300380d20fa900820040300d0000080d074003074071074035003140d801003a16031a1501250400c00700c0d9102c1f100c00028014001e40100702c04001c180805114101c1a0045070781c1c3c0700c1502c1c0500081001007500e0300c1012100b031284009440d04841c03500d08800c1030390503e80e402020001800501d0141c02855441c0f060304c880b1281e500c00041c400084401c29540500040e4440f42806054030421a1151034a440700305800c0c0b00c80340c1203056405240310180000345402c07041c2e00140c10448240c4101100b400004041000d121043c0f06581e080402080c000b41c0c601c1050201035141c400050070000104c0000c600c15041d64022011190541401850103503907a0f164074000d403903a0000c99024001030314040340040b690400354200c40d4104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 383944199 1250 383942949 383942963
    0x30d0e01120f320c1809062404030b090706050a0f23030f09061005040504020a0e0c180f09040605130b070203071407060f080703091e1509 61
    0x10928040d00607041d41c8580c1000720f0303582c1c8440c0030942c145a003e052110720341d07891030715180a2411030f03034580400602149042c1004005001d4071405041107035902910030394540b96240c0d07400300000c06260044038810841e5076207091081c9002d090600520542c0c2c0b00d60b106001988603402019600c2c1298041c1c803003c02c20030055002c1c01c501904403000e103040c641c038203036104c0300101c0b101c6001071103e403445e010391081c0481800505000c40007559400380741c880003052645011900d08085d07089910840340200e6440002c1829902c0c1c42e01041d018100540b200309041c1084c0c80801c0403940868062210004000c041982624001004c2c5190520080c2109115201c4d915230000511000d4111204140e60580010005510550042c414001500556201c9071103041c44c2d80b4101550107005500c5c1c120350411300c100e51300030a55511100540c50034110541c2c0f5000c0550042c40e50080191040c41c0c0d58aa410b03050b24140100710509226580e4624a03141d08010710701640c0c039030440140701d2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 383945449 1250 383944199 383944217
    0x110706020a0f0c050411070201030506040b0a09090f05010507021c02030901200307060903021027030309080c0102131409090d0f0203040b0c0a02120a051c03141302030d0e01 76
    0xc0b90308000d41c903424500030700c00354140950f10400641240d0321010f48407207035800810004155a010b00c507440c0e00036001e480c1800168000c00008a60000500034507407035955a081010034006c50f410500e07046030f0b011000300403504010030040c0d9510755410000b40b4441c244907902015900c04400e8401240741030f10703240c00c000e0300e010302c0294103d0340703100040e038500c4140444004141b69000705554503000350058000010040002000e549220700e50f100b076852800c100c40403103801020324044480d054030b4001240c0c00c2519009106203c1c01003114003540c000301d0580d0245007040080b0041b1380b00d500003001c1d254400400d20046083c01c80e0101d5180c1c1040c081020003030b0199413800e2025809106a901e0300343c9403964507080e60070003071120f1226403201078080114103285a00707211603240b10000b000300b5501a43c443d540d600c10440c28003e2403200c0740384d610216009420102c804004000004110b18110022602000102000340d12a110b800b44135108a8001c10f2409030318203040c0e445902d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 383946699 1250 383945449 383945453
    0xf022203260a0e011e0c050c0a2706030c03110a0e040503070b100801110c01153b01060804030305160c08160b01150306080601060503010501110a02040608030a110706020a 75
    0x60f16034509030a906210210850903c00380d104001020411802c1d21045094111403d00a26094500b60b00c0c41c0070b01a823107410710000e1004801c203988041e00218541040d100c807060b50b4041e00265000034440d0b05105e0b004400c0155141c0214501242524070003241555061000441c1074140c90180c1039400c01c010310400304620142440d841280f4001e046c030065035400702d00b821140301c040d02c09100d213804a40d440c1d03109428016000704200c100b100705141418a150301e10524120706410419120301c41c0d0f100d18040002c283d02c4d41c0040c4a503040300300c80d80e607114090800d40e802c0b902100024642000180684041101001c3c1c0d00c0031990740c00700c6032009a0710f2585076805100c1c80c0e442488098a4000043c0f500700703150b40a004c0d42810b54400c0c910680c0040c064611b9604038100700d401907801130102642c41030503a41101c0e0709191071260745092200481c100050008080d402c1401c102000c100840c0000091010003d969111945c86a81e0303181c81c0c0e1a1984c80c0602d4005800281c40f03100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 383947949 1250 383946699 383946707
    0x30708040b0402010c02090a0204210201020d0f0912030c020f09190f0b09070917060106050a0804020d15230c0412020111011802100201020a09090f022203260a 70
    0x1034424818101185c1021098000070058801111000126900014148528590041c034800310104550286038500410350000c2d4490200b500c00d542003002d50004007201c07900c0360448400030195403085114903c800d0500410040391040143d0203100e10700003541150400860242c49186101414000c4800d41c10a04001e030100700036038038905864011000700c40e034496220714090340711500d03082405071400c200485d03c079a8040d04401d158104100410040b07421100303d80250b802841c2228156455200166aa10001d400502045541c0c03149990340c444a5102109000c04d10a40c90308a040054040001610071110f03000c054005100800034006012540d00943d0700c141003101000b980c00c0c80007030844141c50358009610b040005200300f5424400c1841d03030030743c020340b00030b519100603958003418407540c51141051031551403841240c128103640c103070344203082c05034a0541c2d8041481100644c1c400140410707604801d20703010002000c0512858123a99120140f08141460141002a1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 383949199 1250 383947949 383947951
    0xa0f0c0c0603021326011b0806090c1605060601080115021b04020702090703020403120903050d1808030d0614060c070303030b030304090603080c010506030c0d060f110a23030708040b 80
    0x103c441001d04e28003150181d5109195004040254102244841c07032075191803c0d40c40c50710b2451032541c600043c4000d450360048142d035000c482603420f8030f90b5481e04840728607107118683c030340c8244c0c00101d0b25090401c84042082070060109a803418403a90303c441c00c0c1205100720381c60b680090b0b8018a12070481002009841e40f140000802c018284107098002c035481c100e0481c2c40c08002603000405100308400110010071075032040c5000100103045594443e07460b0840c18620b001d1100107011401d54002c9079152001600800041d6030701d0302c4803141c5550140000d030160a050281500d800b010608103441034680d0300080b500100102440c60710103400a1406500d4a600750000700004108103110303004810003181b094070642d66403510074210f2421a00043c0c01e1500c0b98103d04030480c9166990403506402c00e421850004110850550640007018408030480e6040f81c042980382c511074001d2920110340e9039038104401076242100300211035100c1221320b140440d68581c04500401c00710b940d01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 383950449 1250 383949199 383949217
    0xb0307051339080c1206090a11270d05120d0603020a030b0a1503050304051c05010903180b031b090d1502090a05031f02090d1202030a0f0c0c060302 65
    0x400d0b260500710b0400c10540070303210840901d100180011600c2c0341e6014070050741c010100c2032882d050004c075090b542d000c20005002c90348610007210100c0e6160305a075210b01c8803810b8070380c0c180303503200d411100d2051520710307200c41056600791411002e031103804c140300e0304080d441c2d0000103008404000d0307000301d403107401c549103043c2400d55411000c8016120096135601441c014004d40045181c10007240d400d4030310f040581c450200f400c000410008000200796004d81d1002c603400503004106a084010824841c41c0191031036082840d17100501d40c002e8410041b81d140c821014000684480040056202c1904d2512907800300b034440d00c0e21205184040c001118004204594822a603240c101c44980c4002c0f031801c403d64001811401e80c80c1c1594480014401540609181c0020315819001000d02c04440c61540b074000406c03101030390301c0540c2e505543d507200d036404107007035200d000007503483d001403c0a00c0400d409005100011780902901c284c0316074019000e00c980d07410008203c1c080d42003c210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 383951699 1250 383950449 383950481
    0x30b011e0c0302160e1902090f040b0d0f06050f0603030301060f18090e010b01090f050a1206020c030c0303070e0906061e19030e0106062f0703060c03020901030b03070513 75
    0x24200307144c4407601580000302a0078020503054105100503601145108024044030f03441046a6440b940f01e4a040c4441c1d030000f11000245076602c41c020a4451000c110014003011220341d86004001c1c0c1a03000901941d103019040d803040c1d031600700b8159a072100380503600100380701140852103644078250074014003005021088070340c1e0307582401e1401d0300c5440140c80d030a41d440e80b0404405d540d20039840350084c200b0300c919124180c5050007107410f40405000d41115800210781c0c0b0014010349804a0303030b1440b0070070100c0343d07540d5121f8110350b1280c10540344c3c0c0c000a0080e800c00b442514080b100d45004110040026213890551600c0a416807010000d1a1684106005100c11403807403040343c0e8441d9070161400324810f40c00c08505802c4a80982204d01804000d0002034581ca04000401061880180301c217418640000030040c80c01c24580d0000b0070309420203000c4d000340c41c0d25030080c007040107081e02c05000d484264030405032154114001c071508000000540840448e00b0f412005107681820741d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 383952949 1250 383951699 383951713
    0x130902060d0617151005010503100302030a0c1404050c030f181b0111070b071202010f020d0905010b100e040b0414090a030f03020c100c050d1b030b011e0c0302 70
    0x140c05440141d4008140e03440b54504042200302c01348148108580c001c3c009224910b4580c001d45c5004c1c0c220b000c2c40c1d040040100029200d510902000d0303018680090443d00384101c10b2408203000c0045004280031401e040c000311100d410a4010a402505003051071411541d03000f070b001c22110001068000101035041440c40250014030040d000b0890dc010365680c00c10440001401c918606020407a9039804158100710b081407890a03510f89547c40402c1d810b2013030380340c2c03070817405000d0030720f2000c0700c2e244006061500b1080c1c0b039100c0040c0d144203034000d0000001c20020000b0f06c545515080c008070361314413070980c080c0c9003960000000342c100900000b00d8540041720426079040841380a0003c1e0b02251409040c075802c0050641100d0891030305506d00142114401d4883c010261079a6015850302501c144e80f034082c006542e00380b04000707002c20510b26580400e15000c80318444202c0440e10341002c815141d4400c0c4112280c13208622040001c075900030800711241e0070079503015011800b54030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 383954199 1250 383952949 383952967
    0x901120e030405150702030a02061c0501060f0f0318020909010f0e0a0309170d050a11030c0c0a15080609090c1302041a21060a08070305060a180213090206 68
    0x4412010300d804124015512a03040000f480000c040385003064000344010b001142c0103035400601d80c4852541038030100d4803905491003107490b0a2a41445c10055400d010001c00e510393f03c14081079010071181c3d2442a040020030303041e003c840c001003a50f0020f50141c0c0e06600907007008001c0541125203a000060032402002103002110f915101260040d0032180a12081c183c0c040480806000d4001826020340320900390660360b60268407030340007400800f14216624500a00c440d4061160034029640e07511004805c2c039884045468400c0d120f52180389001c104669083d06801089141c1d843d0050b180c0c8804003004102000140a40441d20235005003000c1c5072100c482c14208180811030268a4a0030305211090740ca40d24400214800005d00801080e1800700b1480264840b01112508440d11007a010400d00c401e80d03000b0380e00c140300e03c603c00002c0040002d180b91091241d07450802000e16403048003101d034aa5281c019522080001558059466035806045401d10040c10b40c2d02c0d0000710 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 383955449 1250 383954199 383954201
    0xc03040909150b0607030804210e030114070219050c100c0c05030d0e060c0c0621010509060a060f030b040f060302010206090c01120c020a0c0e01060908010207050a08090112 76
    0x2600203002994840a100041011504030405807841c41d01090003191034100114919024075080502003003806004903080c4130804000003000e1040044c240c00340080c915010305070030280300e1014042e6180c219891180081000d0a5024013400e070701504101c01c42050405511091900580e03981c060720300b41c00144d9403848420300c81d40040e900c45003001c06c4242462001000e0b5640403e009400151080d1f82e00c540c000544410000102e544035180c085107080310317140404c0380714101c6e0048400100c0704003c0381d000d5850b401d40c0e00030b11080c0106a80b03440c24401c040d04207880440e005403175a00240320040c00ba20080f18010054500081c0c11616a0b0014043d1851454580a51030f5561001d1003956418003189a00006034402040842c44140008142c0e00340490042011641c946082600034030070300001c4105074101080c1090a43c40304008040c0100a200b100041801e05400240580c8180241c0d2001500140038005440d01c2c1d40f01e058a61f4003111405041020140040704c0090b0307a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 383956699 1250 383955449 383955457
    0x6010b07031e0c030f02070b121312030b03070f03020306012c0717011215020d0b03100b12070605030412050903031605070b09060412030c0f030e0306070816030b060c03 74
    0x5035450141c0800c3c0c6040c040c003c1c0460804010840d0003001062288444203c1211050403420007003034034681e14070f055400b5800c41040300618400c90309900040c80e6a0503044004040821416a0300440d500c0407020050000d5210094050700b244004103c0741241c01e220509a042c0145803045200c00f10380940502d400444040010030410038100b601840c64a01180c00741c004421200348120007a11351051054580c10030700c164a80014140c14400840e0300424620b090250448a421181c00642c40103004066885c6002d002c001645454a1038001410000c82e1602c0e220b240c030755100c0b81c54201d14a40c1d2130002e0014401c003003107080691f0720100010f001c0c600851210450480161402504020301580641e09050003406144499a5442c085070201c07846444c02001514441c6011f644622070424090302081c640000700c2c041c9908048a900c0301c140446c15038140c2c0c1e464040a60710070b40240c031000d40b0762845c004610b207a130b07002c2d0f8440101c7e002c0c0281017a09042c6858029455548 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 383957949 1250 383956699 383956757
    0xc04050d080309011d0d0201112809050a030b0f060105120403080a090f080706060504020a0f080a11030c031501031b112d10060303020307020d06020d060905010501080906060306010b0703 82
    0x2108041b0382d50282e6082c414407600f10350392880740b403403c501c191f40300c1d80600a054058034980504429039402c07600603210076004000c082e1515944580c0e90400e0b140b4181c2c21207140b03201f001c4190008030300c1d605c0b41c01140d0700140140e448012075103454a0444401c1e00003007000c2e4074989d4505448000c0341000581005440c8545100c6a03210704030724107001601d203681d000d83c2c060350040c0441000d6541181a4650180702841c0ca840b15a441d84600000341c440701e07007040100321001090250341540d0340c00641c400e9002c92104040345615800450845000810b0398440c040d0003145c228880348035028a0840851502c115040d88559411542e81500e1034103009003640364042013505003100610803413a01d5014204200300052540d100603440340308002d4001d1007406028801d070100302860341a0b40505141369001c101407074030741600c007000348001e0240902255480000804115001440a22405015014068170b0b480c0120030701040c0c1040200305d06106512030441108541010400c440320 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 383959199 1250 383957949 383957953
    0x20a030318091d010e0a02030705010c1e060605150a09150e030f01050601030606080f0f180d090e130f1103010b280f0e0c09010e04020c0601030b0c04050d080309011d 73
    0x481030f01460ba08441982045401540042d001180540d07404504881140d5003800c082c2070072040751a00c1c0000c000c200380c4900e03145500d610840c007031100c01e6204605481068550b4070003420500c1e1050a0781c050940c1c040005203249106020740346a00502d60281282410400200d41d40240002e0504090800488640c1c1d941d10400c101c540e81401104001c0c000d90405440038180202d800040030801007408000b018940d002c00c0d00b0884032805402c0240e05007050700c80a80c1101ca005021600900c1140c400c0d2500ca40401d2403070010704c04015046a105c00d0200c0380c2e503401c3d40c441c45a61221044568103550f02d401c0c84801d610764003021122215118800b1148190303070340b103c511202c003d40000610001e4480c082c852100c0003520745030001c3d200c264030717038507001710f50012603c05001240e040c5e0498004168801c40f4a800222141a04e20a0002aa044d5582c4210700f1f40c9000d144070741540311580c20344c10b030082004070000b903402c0b494810000c1a03d84000000c420754200381d080e10a030b20703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 383960449 1250 383959199 383959241
    0x51c1e050a0f150305122104080d110a0c020904060b0a09090c080105061021020c030903010b121b040207050616030b180105221118030703020a03031809 67
    0x804038850240f121981c0c620300c540f45400e50322800c0d66800d4010891061040000d5a0350045943c1030f15044003220030005000d1601c0d240c681403200750000c82141840c0f505015200c0319107501102681c0c2c8200c95035139000b9540620f90204170809901610588402d40d0700c03844d468580e2501d0703100078040c0104c540081510901d5141803034203500107620407421645824140320071a07841465004036100c0c9803600012100c02e10004074580000b140700303110b42d40c1c030015034901e5841c40840948401703002280200040c180c1c0074140b0000d600c401d0144400d641000e0b20b415003207200050107600e0420013a100506101c00c80d83c03100d142c608144e03149007104407a40c0b008a14168140140c018020342900c01c1e80302108070b0031410002800c10b0103458421000808082c50565205c1801c407900701015005124a4074504030034000c0303600c0551202040c603608201000c090500040b40e0044035400340903800124a10b441c1200d080e00e11030b040d01c84405030f82c100001d0300082401000c1000307841d80401125 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 383961699 1250 383960449 383960471
    0x7111006060212030c030f0702010f1b020d0f09090e070312020a0228050108090102070c062304080705040e100c050307080604050f010b0a03090b0c03010f06051c1e050a 74
    0x580103ea0100d40741c0c8680400400c44580d2188066a0b0130585605110561307480f900d00c1a8098007100022001651800d40d48544040340ca40d500710040c0156000d0790300d1076190210480703500704041585008104000c6080206401c0c69201e03002d481105819200e001c1c1d22656440c102511046100740180d002c00b16010548c80c020481c40c11078528405008090808682200c00203051441483e050203140c0c4001210028290101c9a1060303008000c292030540314800940300c20412140e04090300c01c01c101172000c00c030381c0c20b0441d01602d8115000b000800d162500f0130018014000c0c020880d8020480d40114050796409551303004551912119160300c0e240ca401000404d00500a0780315600300310502c20840036000314a815100c210b00308a07520092800709134058032072030200a1900d5449410451405041406503040e540200c130124003203503882c201111580500b0321409000744141c4040c503001140e03588200c0c0c0c0e002d280051100340285d0040c4081c1290000c071445000592101002c0340d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 383962949 1250 383961699 383961703
    0x10e01020109022d060309070509070c1a01060206280509030f03010602010b03010f0b0d030c020a0b0a110c0301202b0504170f04030204020c0708030a260402011205071110060602 78
    0x286110107690717090551500d0071b0383d5a0b9418243c410395001d40020700124003000c1c840c0c02c20b0f84003180c000c0c060140800c490281c00003050f40c244600d00c010700030300b400300702c000c0b03403040a1000360380703a0048501f4000103815080005100145c806900c910041002c191705c14503040c0030b140281883c1d0000a0328610a006142c29510101855803190346800d07000d540598940c3e507801031807174061600d14042d442c10310108034001156000315010740400308010002940c03050089114068071816100b04400c0070b0107150985860300044c02c54203030050301454a209840000d030031109084c00c00710010504c0054001300108500003583e07112512101003000740070308506c252223941c45c0303000010314000004041039218099400000e11480c2c0020360020740440802c6174401800d07102c42901c2e07640c0c0350441d000c1c2030076404881c869008490340180701c004208209140e44916010b84910511500410003100182002460300051041c45110281d1551040ac26000302d820200c4001a001341060b201034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 383964199 1250 383962949 383963029
    0xd050d1a180f0c03070c120e1e0109090203101203030b0a090b030610140d03110d08040219030308070f110a030f110705360a1505040b0d02010e0102010902 68
    0x6103c031904000703111450b5884400c0a24003504200956040580320310122802541206150303404080e10385008a601840711003607240181c243c88690542d503841c00018107a0004540c211001c120812003007080000501d1100d80c4e43c0d00c2464001f501c150420005038000600c1c2d008807001c665502068045820100b00c0c03e034004071004c0500007094035107140002c6100e1100a458048e40050782e000342014020f0411070a41700c041801d482d018501d881008011038030842d000e901c10401c29115240004071b41035082c050303a806580b080010b940750001a207194040da10b402d410441e0390a250303c1514010702c04080018441e580e03c5034600030080004006c04140c0c082c18101e0b800c071460802640d51000780d41020410541424091450b803034491501840c1c116501c044075403550000c0010640090340700c1e01440d11401901340311191107001f80002c40d0100c628803a080300a182c1600059801103000c498501c105100200320061341368003003003000d50900421419006d01041c90801900302005030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 383965449 1250 383964199 383964211
    0x30106090608060d201206070315060c1106040b13080d020f15091c0201051603050103050a03180506041806171509031b030711030d050d1a180f 63
    0x800054207042c070001e0388030f062444c001003a0300508520004c44900b9840c0800e90804001d2a828207400c101548540341c5804940503030000b880c006000360000043d411620a80c1d5403686e0b691080c40503a03454200222400c0b95842d4003813800d11001951011050081c0907001414a500c0e00c1c09250040880ca081001003003d8295000246010741001c4005200400c1742102d203e041169124410024140034032940d000d01c004043d00089000c00f901500f00754020340c1d44442d0700344401026031040b02110820b00000300280c10005100d000720344103024a5902c0f00c9281480ba28080e03450f070000e00703240c0c019400682c04e4440c0d0828150b69400d18403640303004100c03d103140040050489505511090040001e9204031030303480c08521804000c2080d81e03112842410345c100408113440c1d11580d84d40200320f0880d80b090028041030b43c0340c01c0c0440e10091000d0f51392911f0b030901c90341c0c500e024054080300c8210800d0b00c41c001401c0c2403954074240c1000c221b10084c00b00c65400d027044001e442c04040f0007000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 383966699 1250 383965449 383965457
    0xf1e0a03050c090607241407021504120c03020705100e01080c1305100509030618101104090e161d0a1a010503040f020a0f08070e01080c04050402031906020301060906 73
    0x86400c1a884484c103d4010a510003240c0d80c003000000803413100c000c800768121072080c0c9070a034510001000081480c3c040e00040d02100c5e11032541740d00c050b00154040750020b0010070149003e0a283d8051400b80304503520a0050722134117610358000c079680300c0300c4020600004200c00e94051065800c8420960450070040956252010001585070103100521500b802990403903558900d09100d5425109040d0005003560068184101d0714411065445840070460041e0280d01901c40503030b01c5501d40e801000d03002c1d0750500349803d25641c000c10a010086010b8006d0103448032524284540e80f2014100f03c044a1126030750010300c110890800901c1c1490721854a0800c000c4450071783c49104911109180c070315500c1d42c0320300d400d03090b03030509200083d00f1041592001c19681ca01010460a0703070040740c2212241c45e07903283c001e03803204000e214680d050b4101ca48800c185040c2a0001e40d071003030000e001c0314201140700311354101c21410f018058403510b501000521032568402d00c1c00d4014101454 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 383967949 1250 383966699 383966707
    0x501090f0b16170c03090916090b030c041a1e0301140f0f040c0c030f02010c080a0f0b03030c01020904111c0906110c0318060304170f1e0a03050c 64
    0x50004250300c1501030300c128a030180c90103242005070140043c80496844850541c80e00714070960181c2e0382d00300501c042d1280e00c0c140c0c00135140141c4071120801350b41c0159100950f1514010000100ea031020b06070a40d818000c000c0417aa05c04180000c018203a1042c01995603152003040801000788131040c0030800d400100f00421214203107941b25403080d40f044a214110f041300c017001442d2410020f20b00c90b000b030f040400d0451000d800103001d00d0568000d8884003038070707540d0f40d1040f801c07580c8214120001c51121004500880d9003076010201817600420001602045140040d203550001107002d4801d80d0000f64a6481e82001c2c090b420f000044c82c9920307070400e12210903c0031084003c4000c40c0c000ea5503a0200c60512441d030300010300e00728200c000c142e960703001c00c83d91944076405480b501c82c00480d005076a043d64103242040782d20840e00312101d00c50640910000250b00d5003e5804146c45000c1405900800c0c01040a03000c2039552115400350b840e90741d0500901a6030005240d2802c16900740 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 383969199 1250 383967949 383967959
    0xc020c030d0809070e010810020a0210060305060708060901051e040207020406291312050a02061b010e0d0f08131a0a0b04090203100f020f070b010501110a02030307060513060c03060501090f 83
    0x1c1e002c0700703482300d0f280c2c096100c01c07040da412450302580401c420701c60f80c202071000080c8400461014014075003030f91030072480ea0b101010322006a8082c46220b42040cac94a0159150144510000c448080005c0000d484c0130f1441d00090251040d43c0c101c42903103003d8201400c0c4000380640000d043c0c080400a050178810320440d8140401c2c0d552185c102503401500c0031310100602481084801903009200700d403103501045612550840294454035039600e4401404000000000c2004000b00d15a031443d90115032010b084402c4000a05103030405d0050384c4500c8000b40b91414032203003900320101807001d103182501c41ca2054030036060b6294007992a0904131405618085122410294048000700b80300c104003800000030310660038505c61000c0007280034004c100351100014101c1700240c0c0c1d13001c1c40140081c4035a45403001c4060003503160740204072000000d103098001c035a02200700440c803a020902500e5078802c1e51241d0280000203951500305114541c5c1180d48803000d0445903259012040c209 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 383970449 1250 383969199 383969203
    0x91e020426011404020d260a0908011a0d080c01020a030f06150c02011805031b040e060118050a0204210308010b040b031f050a090b030705060c0c040c020c030d0809070e0108 76
    0x280020b40a0103201c06c60b4001c1c000ba030001e82c00c002d81c0c3c10010a0001d02c016000c401e90b034000142d001d000a000280020700410140503442e6441c84e04000c2136440820601001b00e01c004a0354201c40d5242e040c025144649001e101506818406850201d101040d602d070100854941d500700300c1082d03102c40368110b6601da02c042d0714064180e080c2000411503002c19184507100d08280d200503410710070b140b11001c07071b40390003845450051b00c1a0b400784203040c3c8000b0780a444440c00d000c0d018144c0e040580400c3c1ea049a60441074005030344080040c90b09480303410042d40000d0114000210301040719500040603800ba000a00400f036041d80c45003004e01b04260f0740704500c0090704280308803c00459a554805030900440c00a005c010903040ea02560b80038014042c01c00305d40c4445c0b1a004079070300000d0700d05040e8216062010307aa8060081410500c0801000b4000007040f1003c40c842d04013583d469403030800c01c0f601101043e0f00c4007407030b900d800310345a45000f14981050456041d1031004020301400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 383971699 1250 383970449 383970451
    0x10060f0602060612070801230109050c0f07060212040807021f020c060304020a080303010f0603050a0203060d0b0405100e0109140a0317150d0c060e0a050a091e0204260114 75
    0x8220b5000700244c240c3c41c1420700e460b03400c1d0400da0480d441d010600c1c011402820071036000074034106548600d682da8080800031204200c85031110800c04000e81c0b01b00f03481d01c80c010903201d40700d0300c801030800d909000013103440c0c3c40403541101e5050780040c00c201549000c40c4107440c881e006d000d80c10300030004035000940b1100885400f5020308070100100c0d0440d6a40d40d03000020b1f04540080703d072a91fa60324490600c00d000e43c80b4043c01301c0d00d460f010844511140c02260312038000a010a4406031880e9250340d090400104240c4203030003505101c41052900c2d0250000e10120710b0000b09030501907041000081c460b800c0109001d51188a400300000e811000c24040061460142203280d52215214540441091340d1141c0c410150620702e002c02c184000300400307840c03455a0781382403450040c0a1000740c144502846a1005401008100c140280d03084510881003011034120383c05c440c40c820406a0308540c0004944502400043d0010010314600042103c0070b00028040620001c224043c0c10340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 383972949 1250 383971699 383971711
    0xf080c040507050d090510020703031530080c0a0c080c010203030f1303120212010e0f24060408070f030512030f010302040c1b06060608090f1506180910060f060206 72
    0x180300e950005c2803000c140700242d00d081c1300003001d541d00c5509140080041082c20a440d500031005c14020800100041c02104008a4860800981100d400360900c441e021900c040350508002c10014039001c0c010b224604149202e8600080391500302000581884600d94803181103620030300810100008001e041c541080641c2144001164103090031100d982c4544015000940005515150150300700c0009040302c0c02c00280e19242d0b141d140410100c80340981d0306000b20801d60403c2c1d000d03003401e10a10074100324001c003194a80703a59680e03614284441a03000034090001c052042042c40f60074007285100c0140351054510398030703065480d15155441804041d01459444020584a5011341d050907003000180706202d2044249140072406404c0a000d00c40c0010341c1c0d000411001764000524194441c2c07800060050030b036034180840a419070042800c2d911040007a1112170320414015001c1c0100074400180070403484050095040c4c50305548081402c280c959401c1240b40d43c081b43e0560004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 383974199 1250 383972949 383972951
    0x7120b22260c0715090e1302090c0306013e10050c25020123210c0a0c05030405090708011415090906040e1903030b060c0d0503090a0b010f080c040507050d 68
    0x1100e40c00c01105c0a9449810a460742c11001c400d121110145010702000b26200f114244055981d8100342e601c90300027500c1c0d09003c40c510b000c02031102c5030201483c1804035010301c0c0e09903412800c4070310112007909048000c40705401c54084012640400d004569019000d2017405203815214442c069003900601100c4a203010303442c200c0d4045a00c02c0c4100003908425803401004442e860040701c210b5070010300c1c101080c65480c40c40c200502c3d0000303138061003180d0510301a4100300302d00342c050320300d0041030000715041d010070807002c151036485510031401805296149040c1e981802110144803010300d04080c07040d450141310f454209010402c44000c80300c140d900b0421510382c940841c000d05102030042665001c3c449960134298a618502c100c0c141c02a54240103542909050010300e00ca207200440103600201120300a150007180110340001034881141c0120005403526441c0b00d2080c0c2109016901e032204c104a0704801b00074408100c2c81c201c908100398102080060b001d4400c012807a0030705 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 383975449 1250 383974199 383974229
    0x60610080c13090c05040501020f0c1e0d0602071110171602100c08150a050310020f0c03070302060106091d071206051e0a0807120b22260c07 62
    0x40031851440304010450a5000d0044c540108006866034006025440c01071142020764180d81000003903801d00307900094940c00c143e0512007800525424600e586542008440c108680000c960f44001c011090046e0762a07120040164204650365150700300a00412550000c0080c07050b1070190079a070081445c07031941800c5010840140d082c4000a0989410380d41b60403202e1110329000b03c4c001d841444d18917890440502c1807410810391543c0390003910f03007540c0681500c0c032a0380c100f5801400c00b000c0400c41282003c0d02e0101c20380c91a84140000c03801a04180700401c05107410062031006416010150070000404031184151003000400440401207034010b05910100180c1c800303c0540005030001c910645141035188c85810003145640c05440d0044c4000780b007042c0425182e043c1d9220300d000c0c0070041c90584a00900320406042e040c001343d5824030f010800071111400d1142c9030301c40d040c0641c0b450000c580400c040464040e24845000041000310001c0714007068000c01c1e00e42c01545405a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 383976699 1250 383975449 383975467
    0xd08060a080a060525020304030f03020c1c050c0d120c021c03170601020a020307060309022e020114060109031b0f0f080f0109080a08091f0b03060610080c 68
    0x18a44107a1200c1a81d0103180e03107101c2808101e42185200382881d01d011141c0220407135406000380482200314006801c140401c1c40050f000b2541002a81e000c1d1044030103514280c40010411003c0001c400c591111001c000003c1100901078076402202c11202079a084d440390311446080ca013859001307070400c010034041c0c43c01c40d6964029131001b5a40c48141c02c031014014500a401400700b24620a100140200040e0444d840019030b80309040c0e0242c080d01c0018038000041e0094010814101e134010354400200d00001c1403045484036110175900810480c602c03600c40a401c445a003c0484400c842c180c04001499801c40c0c4581c0840b5404214030f03400070841450b21a100415070855211009149000980348000a0010040d500b150342521040d20b50285142e00300ca801c403400508040060043c3c5040c1d5010f41001ca030b0182c0d2a03c2030b101e00103044100c0725402c80c4920210b51115544812548040c141040402d50010007500ea201e1003021050b4084c4c0151002040d51110400000350885 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 383977949 1250 383976699 383976709
    0x403051801123902150903160f030813080a050a0e12010506100f0206130302010b030609030a0e0409020d0b1909051e06060a05060c0106050a14210d0806 67
    0x441c8903942c0c0001c000a01ca404119280c5a03414804074a8000c403100205248a98158092029442d03940080016440c5260311400c4054020080c1b02c4500051140c40c0c15030041000c40d0000700e10504040000c10010314000c3e2000c9405001851560f0500c503203100010f050340100e48404009090680c0c9901400d80d00b10ba030100710081d03140c0c100c07a0480c0306e25004441500010300860045400c6412002003072400c407401c89076014114016072000011a220002001081030729600a100100c1d1140804021910300720302a00c01c20035643c4006400344000d580071200c02c640d50401c840c103000342201900002d8400c055003102803c03494181004c0780200302c2d41e6908103d010b203992000d001028403401c0aa446003100003142845010f40b40d060b0389820f902017902c1e403040c0c0340100414151803c200910840b6000342c1910341d415036907035101148a6072021840070041406042d54400401d00b04c2c144980c01d103c0d500030454602c2c06007040c4102410103d40b031312082d00355107400301079944c0f1900021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 383979199 1250 383977949 383977967
    0x50c070f05030408010e060f0a051308030f061002010b090109022d04060e01031b0e03120f1c0501230f12030c01050f070207050108091e030c01140403051801 69
    0x804000038034191500300302000c0003400403900c11000070806108046000c0d0f4564800300d500d0501c002c030740000100a98010b5200701d4020025400d0003031205180d80d039500e940c1c2d005641520208052400704803142c50403c0c40740c20000f0f210f100030320602c0c17810700205d9400071060007a0304460341c02150300e0042840141000d0040e13148200551400741600b40e40c04800c0c0c0c0107003d42c20004080c100032030510b501030b0107840166030941c00000d240546045040311120030034040d059060181181c00c007410620f60001d80303060380e60500656500c050000e0000040c1c4410400e06510754201401000079001c10310007004d41d98410b0100715000445103000400d186581204140c0c0074044916000c40440b00001401c3e840d006070008200940700c0d41d1021007601003c980b1040180e120550a002310752080004580280c04007003159550800c48030218860104440b00015652000c10b0a09410200b40103418003110000c000341680c1c1402d8400500c0ca01c50382030001945d07801c00c0e01d08401648038234410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 383980449 1250 383979199 383979203
    0xd030e030a05010c09060206010f0e160215070906091d0105150c0102030106050306090f090c19083009100c021f0e130605060306010f0c0503040306021e0c0709050c07 73
    0x2013001004400b4094004005401440d005104400000c201403044004550907218060340503903d80e5100c40050045000e000d03210001c50060030200390b90310041c03c1031180651625160401546d04000b4010981180f6501031084500c005455420a96000001a040d12805da50003603030070071006011030044c8603c00401500d58400400000c803650b01c54041d42c00307170004486ea8070b2240c98425011040c01320a0343c140704113801440040c5598a4404800855a00b000d0b02c010402e0707079540016804d04200c0c54040c80842090300501903010340110802d0008100300d80300f60f003440c0c0010041900001c40c002004144080c1448520566448140e82100c41500e89a8484015610540200505013b49185001c1c00484001c09040342090154400740d40019042074203682d1928011204180c0e000e03214024040a4100080410b20030b00080004c1c0d40540c030090b0b036030b41c0803058140d00711040380b191a070094801d01401d040950046038403c21503400080108403903d0b07003501c84440e0b114003280 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 383981699 1250 383980449 383980451
    0x6301020f0f0313060e0f09130203010504050303041226180102180f0a0602120d021303050604020a14061903241d0403091707090c05130501020c0d030e030a0501 70
    0x8140a044001005095108581e144407100030750340d00064900711200c0004c1d6600c0300321403d281005090500c100348d4015807103d0306996a9110b43c01007400c540d02a2401d68040d0000820042405080c003006040c0c9607140ca041c0035002d824a803051303000c5001400b40d0001c0032036600410b614a010500b8843e02801c040000c5650300f11900a615440d42c0c06103406000305484002c0e4615880d02403a00403c0700d4040e000f5242c0300740030b0a01098180d0105071041241c03a4203011102250810302e01c0c0c0c0c0c020310300c10001000f890a0900402ca0440c010358000106809100308101c442e499000980e00010401c004a07004418002000e40251104200d05540920106000c41100d0360400950b0100e40300c0c942c0804803560851200e588801007100c014010035440e0b00304001030103104011540b503180c5803080d2190aa1110042015030700001c160000041d00402c00c0d036a800124548280109024001040e09590440214880c0c104600700902408400c0c801d03082c16850600003070f40c0050b40940 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 383982949 1250 383981699 383981713
    0xb040204090b0901050108010810091a01030c0e0c13030b0907030b0c0a0914090c0a0314010603063f0606030b011d0c03100302156301020f 61
    0x7205401058040640d510603521070f0000a03e82d4018040769040c2c3d6010005440380c0c0800808a401400801d07c0c101c0301742c9207107014901001d140c1480b07107029604c40e0131034002a80c60403510082e02900507011051074601000203200c800c00340d81c241800c40340c3c801c0c0048486c0d60b807451201e0501f04181d001618099580e400c010045c0489401020805d40903100c440d400303500c0710025030303400208004107600801810041001c204000010b01010000ca18011500480c030040280c81c010013a8480c0b00429100c450a200c02c030f01814002910342d1121303241c45041c040354002850307892100d604081001c952554039030103120981e0801d44c061a0010040320940d41d440d4452650740c0d10a1102000307000710742d0046810380d64810112401032103005007034031490382160200702c00c1d885200c40c40c1035001400c00030f0f0540008040304018081040308010688560178900d0b04600c96403101013080d60707210a00040b2016500d01c1849440201861180310b2106210303401030b458400c2e00881c244d21881252 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 383984199 1250 383982949 383982959
    0x90705011e05190806040f180209040f080d09060e010c020709050a060b0304120f0c030f0f030608100903031a1305040305090909060601020c060a020a060b060d0c181a070b0601030b040204 82
    0x30030b41e140200310541b0100190405881900212403503c40a01034100d0580100c0c405032414600c803542080c05512a0f01070070416698555096108007405c48800c1c0e1910425401d0200521400000c03c045000a001e90706600d0b0b0002d40381c2045002e584200c580d5130700480c451902a500c10b001600c0c051240d00e80d2800e040c01c103c1c0c202c0029050840020b02629210105203100d103841c034408903071644490443c40e03020801940e0b00f0704c90301d01c1e00b030070181d032203a0001d1800c10800003080c2c9003100880c00110000c86007401000c4c2ca1034010a02c01105010b903034501ea6444004881e6a00300c81d03c0e0780025180c8035880c00300d1380d41c404d51450313503440659403090218000c2c1c0400c80e00d020380401d03001c44406000307900902c0003034080c0329030210243e00a0710075200454065000a481e508005006074602803500d0301c5901250780141c00c41c1d000400c00e080e000e56031810201060043c010100c3c4821100810030380d0481140b1400000515040180b00030903001c0e4040c0d003202100d0b050080040d503d658441d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 383985449 1250 383984199 383984207
    0xd031b1e0c060e07060e120f06041518031701090507021f060e07120605030a170a360b0304020d021002030405060708030703140f1b04080f0d08090705011e0519 70
    0x4118111f200b55214111005082c60014580c40d05c2c00c040c0c80900180e660b01c0c4c940785444d600301941280c51680355035071511510003009007141d4051298a80302c0c02101c51800151884805170001c0c00b4803864482130000f61600020300030f1482c80ca901c00d00700e02000c3c9080070009080c007603102c1d500c0b580c901c005000004c0c0c0c0082900701e400d03408190800545550344100f550300c038402c0c0409410050b5080c801150194040c008120031501400d28855902074440038111111400c080700e40c8407485141144070101c3c2100035600100140140282141010b400241040203180d5009120300407100301001818024419900241402031105031900c04c5d50810f001d0b1a0300c11211000020700e01407091a0f50b51051041034005c079801c0910290503510007001c40080744000d8007032041070310305120000e103410082100701c00000d1701d8000791503090b2002401604c00d05000d0316900094102107414040d59a0051101014001c06560224480041082a0b8007807080b100f04c52000c1000c00202003540d508 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 383986699 1250 383985449 383985467
    0x7170a0503030c031902180d02040209180601020c010206040503030711070e0106050d1404030e090613020c070306200a0e010507080a030902031b030715110d031b1e0c060e0706 77
    0x810443d92014081007258041f03115840c0140754082c0801003071040c03400c0088c5000300c402c0c40500010328002100c800100403101222800c503100301c0c480200009541e05020380c04850000b80010885800d040d91000e44901004100c90100701810421b250940d500300041c1000b000d0405804001d943c641741e000708140d1000800712803603810810851102c021107000a0320860b09a9110094880ca134002c000e031000f406401c840c0e21000340c100d07200d40c001c1070b8802480c170300d07110400170102c3c00e19619212064409000b00500d414204584c40d080104441c02100d8144d6503030301e000c4000c0d130516001600c06000340030f8064000e140218034100183d070180d112083c424021400c58660300071010303d0100c3d4484d807820715034141e002074a04025583c465650134646034140d0030542455201c038030f130706890076002210500019844007400340d080032040340764941d111010724024214141781c0c2480e005c00e040c450090710130010700c451050203200c544d034060103801090000f42e500c015500c000c000c02c0d103c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 383987949 1250 383986699 383986711
    0x10911040f06180f060804060905010608011109030c030c03060a0b042705210d0207020d020904050706090b07030903030c0c0302040501090204080c0d0210080411030d0306060e1207170a0503030c03 86
    0x1610f0200441d90f0070ba400c401e10112115592007880d00d139140c2d0340d0340300501040c0c41e00f04c50540d2a1040403c41d0312003070041f10070600003030f860142c51300c600d5401c05141020a00d0082e001c5e0b003201016002c0d80e01c0100d8410b522085800c0c002c20840c0c0324002140c02012a400c60100d824200001c4811030710142405c4282c65000d8030072030300c0c078100800c0005211310070354103034010050742017003241d0b4803640b90b0f00130300b40d240e0006054003c605400c0d00403541203882182c084400d0340043c842032003d00d40016448000d801c201140e41c3c1003134000da402400c0d490403400054140310500e46440c00b0401c01640342000307540e02810038821540d60301e0140c0040d420900032000d00d401628940c0007139007040380a0040003900141542003010f07031024142c44841001e0815607a12000400c440d01071344040082d00712850a40c1d030006441d80c44c2c042d00900f00c14207034074264842c0d02c40100c4840584800200c420603981800406a074100c00c4804083c900101e8480042c801c1c00080100812000000080c610403d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 383989199 1250 383987949 383987987
    0x1080607230a112401050d050f0706050408060106050a0504140409060e03191833050304021509100305090a0c0807080705220b0a090f0501030c1d010911040f06 70
    0x482c440e15004003c1d0280384442c50b002c01001300400c05454501d015403031190040080d1503d030040150109c1c103040741c5400031000300e840000c1c1081074020801034180100750520b401811304007007a00090a5118620a680d00340032000c4c454140c0c1c0e5900e0780006111a800a000c200900e05000c40ca1b0b12900f05001180f81c0c3d800800c40795610720700546080801c0b448400903090a941000341e1714008440c04002e00c818000450420300c2101d150b207246041c0c070803c5072201d03900d070715051041140b54140c101c1e818802d00021f22200001d52505618080320030414180130545035904151540303480000b00002d0800d0700c07413420028003518041030880c01c0d1604003060b90007080e05e540501200ba0409034600d8520282092884821041076011821101f0001c0c07280080765569030350202520031104425071502d03a260700402c204030044030365800521503583c085101140c0309a203e1b00f0101d0510031800c90545a400c861105998102158040c00103d0441000c0a440e1440100200c0302c500b1651074503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 383990449 1250 383989199 383989213
    0x30c07110a0b1c150608060907031104380909090c0a03230d091e0e040b0f07020d09030605041703010b0301060206070c0b04154101080607230a11 64
    0x603c044604200c26201d8507106d07444140c0302d020900501b42001003849080595800440c0c6404415000602c0140000d100620428022050080d0b014800700d111401a01c000c0100084e40d01b444429158481011120f0b60241e035586600c4d641021460300d2a40e81c00309421201004003c2c45e4442e0b03c4070030130740d15500d8510340d4054001c01d039103004a00455000c03492880d4100548900320200003640c0a222208003609a40c07960625140d150070380342143c441542100308181040ca80d8110b6500c2a031318401040c1080c0e16a034050000146400080c1040e41c81d40c0009043c854009410110a804034403034075a44e42c1e41d401e0800a51300280200401030140401181c90070f071041c4100c122058211004007102e44a99071042400000b404055071041d403a40744030015032001c2c0501d404e00d940c01c03038100c00301c0040d84540c40e800329030100400d081c41055000180b088080c0012070650040c100d0600301d040f0f94401d007460344d400d021001c5611000d64001002d101003903105500c401190ba14204590325 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 383991699 1250 383990449 383990471
    0x303080108010b0a120c050315040b060904260705030c0106061d0a05011b05060108010e0d022d120307020d030501170c041a0a0e04030212030c07110a0b1c 68
    0x3e8461103103541d580000e00000501018601043c003119aa2145178030340641c543c0c80300400e0400b22010840c8181444500800c028001034604071640000c0c1240c08005906d081d965817407180403040302074504c2d60084003240b0b80581c00c0b80c0807103401c2c03600030b400c680d01d0b0605010788038042c05550250703000082c004401e030804140d04010120301c1042c010004000c0505000c011101e685910040c007024070742c005400c1c800b2420a110441c06000c0c0344c0c0011406014001110740b03444011480b1004540c03009003000741504000780d0012003152505200c41001c4244241c040c945558020500d0701918000240300c842070b00022541401143c5071802d2101f60390752040100f801000017000800c82d042102070410710f10f010b6000950744a09101191b18110000000c10b210780d119402c60300c22140e1540a0000345130f01007043e45242c901c2000194074500d03040314407080a000381d0350700600c2010b014024030b1256441502c444082c01c19100700030380340d0444040c207a986c1c682031306903e01a140f610f855010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 383992805 1106 383991699 383991701
    0x70e04080a17130609150e0c1c0b130201050424021c0c030c02120102040914090109170d1b0c02010905040507230c03030108060414011a0105030a0f15030308010801 72
    0x11b4000b821810700c040c600b49c0100103580082c031046c25800107500d85107c10b034412a58844500024818401a0b40c0780c06641c11514240940c0c1a00180c2003403441070f92546204145d080780c1f900d1001041c60407801882e428550001003910f100b07000803034010781c0101e00c51440909605900c0c40b84055650882e0000d8000000c0c19885005140040143c0494143c2000002008002242d0903a80d00070350000c41360909155045c020402d52981481548507002c1d4030080c0e1010150300800c06001015404100e200720302181410074085014145845500d03c0b5904c0d1f0744a1041c03280c100048011284011140003403a0303102004840c003880c0c02070024500030a00d000040a55050602e42003040803801d00d000c00390751b803500400700031182005400d039015071020300b02240d881d101c400c000005011403c03100000345007890b88403261150003078800000c0341d000742c0e80e0090f04d036200d09040b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 383812949 383992805 := by
  have h0 := BRFrame.cov_init 383812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 383812949 ≤ n) (h2 : n < 383992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
