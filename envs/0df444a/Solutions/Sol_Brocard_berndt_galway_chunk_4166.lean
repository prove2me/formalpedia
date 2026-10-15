-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4166
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:45:35.037567+00:00
-- url     : https://prove2.me/submissions/4aa93337-fbfc-45c2-8b25-b669a99decd6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 749100719 ≤ n < 749280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 749101969 1250 749100719 749100761
    0x6030103060905030c0d1e05120f07121505040605060316030e1f0222121e050613050c04140a150f080703060e03030405061b190e040c080105060a1101 66
    0x480e8064187c2900281c2c01718030405210717040701c01380d8080c81081480141c0460f85c80c0002c41c1100c4a141c0d0750307000207062402c4000168829481c404452100c1507080303042d803103240200300d41d1034940140005040201c610500d10305140e1070100815802149250a064443d038100040441c28840804c0da08100c00b00503103e6580448540e000b54032000160200030144841c103000c0e170300c1030943c41064900c0350002c4480000076448002d08018581c07082d01c0001054502000064814490070740200601d030904519241503141690805407403d00090207946003c4e468840c81840380d041c6d0ba004a0074407030024070b94280105030400e06019801c408815040305400282c02040029410101c0e8041d5408000e002c05a00d2020386a100545016080350b0100010454098504101c101c5900000418030b1038600da4001d0b01c6c1d444160700c0030036000310702622b40b003100b1341c24640108400340515192030781040d8140700015940303000d40074210080040c14440c01018203000d40c0070317014003560403c408001d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 749103219 1250 749101969 749101993
    0x804020d0611040b04031e051908070c0e04050f0d0509040c020c030609100b0a0e07031107060c020618060906040b07020f06180106050603130b04020f040c17100506030103060905030c 80
    0x15035000b4807049801d1403c7c10b008041d4005000914003a1650040260408400c038660a0400140d014003e4803a201d0802080c40040c1756141c00000400305690203070b0561400c5d04159042c5408402e250405801203d000e205050340701c4116102017004480000b000c440f039a404034039210f0a109030300c0d003511822052150340903000400d0000d0080c90f41c400e01c0303054500b20034050103214070700c03d02ca00d83e603903100810080d900035005040404014401c040c1421020780301e010917541038030090340258220304148100c030304c0040d01c4410607103c0078008080505000d0011a40d8500041018140303034040400705840a1092150081c11807500044804600b4250800420010710b20005043c1d580381240000346401c3c03040640c1e116040380701000d44c0040568541030121240148103d0b8060300800e40b020031655148601c1d8100802666128a242d50f0810101001e05001e0f0081c2d8811410780020170069030f4001c21079040d40e0740400c01080401d0b00d0b01e081440c50081907003002042c000c070520b00c4a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 749104469 1250 749103219 749103239
    0x1306090312050c07080301090525051806040e0f060415030507081c12050a110408061504020435070b13090213171513020901080105070804020d061104 66
    0x81c01c91030390030001900d44480c034211a21406000601601d400d1004100f100340640c04242e0008817118440c0010340c8007000c0d03480000d0841e0f21000864004201c8603056190761101c0313561708c407003039450700e02e00b81c1883d4a01e407001e1001094449010490800140301c0c1d222038102c8800041c80c003100a1084da02d034540140c5400940c002d10344240b041d0782007120780c11001c00e80e800540301e6544415a0090382d040c2381e0005400300400752400e940c1c4a002d4204000c3e4200010b00051100d04046c00c01c0d4240704010001020007503901d03600c928014002031140400960b424000b0002c0714040c90026402106050b01641c0e031002e94161a0055020000f40f100d8182e00500c6901129100a009a522030b000d84007280138081400c5100c94062174107002086070480c42940103070382c680c111003100c9000444401d824804640c10300e100b44402c440c0204500748030040d980900034881c0240003e14182000805400005001900c204214a003441c28450150b00c40c94008032014403060fa52a01c0303003411340c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 749105719 1250 749104469 749104487
    0x91003111809150a120c0302060d060503010e0c01080c130b0a03050f0906071d040f0e0c03010b010503040510180605161218033b03010b032413060903 66
    0x502408910001904948442d2082000c840c0010b11101000d400c102c01c0851107105c02508940d51540d030000440540da4450181c0700305820440c0201c0c040d402c105c00c0c5425600c140c80703811101da02840c008405682c0110b0355540c0071025011b41521500d40404071000707000305602c010405880090002102e81d4542c2103140b00303100100382c2e050349071070744200559075072012121100040c0c03140e03212041032001c005039004044801440031809428565002c411114804441c61103580148139450803400c080c025044103580c00d003420b9082d480c00d41c0381d00c1e4482c110f80080e208a50b83d00c01c00c0361486140d000010350341c1908180100050301c1c1c242161030074100c274010100b011881d0101480c1d0802600c1c091030460b048001071200c9043c40b0f99070150b4014590180301c0850a035020302404403120b811041c0c017480612011418a40e00354002130500b11074110203c0d0f80a034000301d8143c10941c940700f6022440404420041819660310319007001800143c0e080201741c0d500304124034003455407004c400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 749106969 1250 749105719 749105767
    0x702010b04020c030903120f1c0b12011e090804090c0203040b0f0304030806060901120506010207090905070302040c0810170c0414040507090b03150414030c03040603050106031109100311 82
    0x16140e5500084641a0030300070071103844502300c42009130015001a0b00c500c120806800040459552121000246450710a4404c569160364418048241030007000f551485107180740000c1101000325105d00b103a52041d40a00000c4e01c0e150b05900400074420403c03070f001000f4044125845010041d0b070f104540e8001e9801340c001a59410100d034251500d04121400404143c452480150000492101401e0018103071410f6000f070350300c00240d40075207018204116200c0c1018295080c01c51040001304d40610089a0400c84a5070412443c450645c040d03100303881d81100710740b03405818006181c2c5040b4000749800c0d0800e090004401041040d0414280103e00c0f68095034420341d220303a0580c0c121005080b0240d030541c042e82e0442040c0c3c1c030f0b81c0807494005000748041c2030312403180f181151940e8054802440355034030004041001591512a0601400c130614042c050802c88822168107405804149441400710750100c000d1180a90f025070594200740b04130303503256000a01c00382d0b8a880d40b101d01c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 749108219 1250 749106969 749106973
    0x13080706090b03040303091b0602030a02010e010207110d4b080307050c12031f060804020f010f27051e061b151005120a05060106080702010b04020c030903 68
    0x480c000380141500d00566030030324442801e5655a4030120080d2104820030f80345812000c10f1803881c65002030a28005d08255001941c3c1c4184043c130003400c4501c0080742400691041c40a58001141c1c03c140100e0301204a1782031609451b5400c0a48850102c1000341350403401c90300c0c007007aa90003e030710401211901e2005025030b81121140803511401c040a0003002050700f0000204a980590040c14010781f050081b600c15460316040e801850348140c56060560b400e1052207150380c03040c0d08680c406408a8a0b003004581403641c003040ca21b408000a540c14000f0000c5c46d10308840c49125030000e080c0f500d0a000300f14008005203141103503007901649016602d980f41200c04072494403041114020040c03d00742c0360003c14550401e48418000400c44c043c001ca0100d92403880b00f4203400c501841c4041081704400f882c2004002e0180c100a12407407880e003101c40c0b05004968007040e00c5045480c0d9042c488402d90b14600101d0040c02e2149240d03a2003072003c1802c41c4400000005010b003500d040d81 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 749109469 1250 749108219 749108233
    0x1060e060d05161b05121e070507030606050a060815010e1903060f111603261e04021e04061d0901181203020702041e0905280b090f031308 61
    0x100032151403240800174000f80d10413403401745440340703130402408202d02054200c48a500c1c0c1403101500c65205003029102544804070030b009206061103000000c100488505080c1ca140c4076000e08600d030020036240b00510070003526500ea0340528076080030315800401c2504803400c7c1407809140c25815000c251001e5203040e144103126803840c41039540c46800c010b0b1b100e050240d0b90a60401401580304102c0070080b140d1a24205d0035008019090848408503840c0384616208101651118094591800104c864000e210168841c1c2c1c0011480c64641d40703654513107080d064007180103000d9030b42c8203940800500445444008505103034500507041d8400a0089581483c4d134100e102c405641c0c05044420000c06180c0114020b03030040808134409840801c0780c82c6c0c034819010000001444100c0c01c1c645907480201040400c0c0054441030741d02d04400c00002d0030140340300c2858000f041000701654625804610000e404022100d100d600d044100c81d43d030030b2504000030b0100c00ca07214034026481054 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 749110719 1250 749109469 749109497
    0x403060203011d0a050618090708060112050c06030606090f0a1701020c0c09010806070807030612080901020d170c0f0403050111040e1e150f0a060504081002070b01060e060d0516 78
    0x3c014075001e01b00c000e001560000030100c030407110340c02c058012940c40c800c00f100064030410502c0840c1c02018440008408600780741400f50910501c1003100703100d41070800c20000340369102425114803a41c00e440403850040c0060110f100700a10360040701060024000107136008005400800c2040c4150050340c000510300810310643d180280075010258114100003058680b083c583e0507400041c80c640420495a5a000d402d01c03500d4550741940c4000e4001490b4500b56010070038904c4c44083c501d8070550b0180150751550503810003811b043c510034400555a10342410a1043d00d01864202c40200b150580705072010070716500912415200c100020009146000b030106882c1c0040925070864500741e48410014081018400c3d415a010030890940f101549960044102521450700c40a40e16410000164a40b0381d030290070005450041161000044846c50901d044400c2410414a50000c48002495600486940e034201e94079000c204440441440e2217100c500556407200d8509001c84 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 749111969 1250 749110719 749110721
    0x2071a09011a180403141b0616020303130204020f041d0a0b0a150c24093e0301141e0105010f05090108070504050604060e0405130222020403060203011d0a 68
    0x840005444140300f0000902290040082c03440e1640c080000500d480340417486c2c0c0c2c90740c61110300c03202c035244d0000b420084200e2424000d0000c021030340c0000c2d4118600840b14440307100c00d942000303002d1500820901b01225162090300d02500c2603e552414000030a42000c045441c11108111442d081002c0c10031075040441c070002c00c0d501814101c0481c80206a010b40c0d00e0051040c0441e42601448001254240079811441001d035400c079012442c2130403410050f909104240b1900c064214003001240701c0e20800e04450362032480541d103010660340050000b80180400d966003184102550100a00b289800790200c40d01c5422402c2024540d80350303001101c00441000380240800d4003000600e0b499801030090503400091440c00502e00780c0c54070040741d29500254408000324050114a190610b018003d01d90300c8070200714124450308032034001651407140c0620000010201d50325070310740849150111800740d50850000c1d541d03565200903280c4000200d0001c1e01040e40f540300411111402 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 749113219 1250 749111969 749111989
    0x20408012003040b04030c15090812010608150d080f0c071502070f0e060d21140c060118060918060c0c0210050f160f0302060117070902071a09011a 65
    0x804d01d5542241e4441e1340075544a00190001d58030311a2400c1075145220450084188940c0300c1d900160f280d0031480200070310319806170400400d01c6074220401078881c444401d41c1040381800c40f0361061011141c205982544201001500800c40001d10b0340310000300044c4071800c0710140802c89045074034031102241c81d60f15601501d008078070801400c1100f98141c0c040603070003850007000c0c3d00c00145503680f030101d03180d44a02c1403685a8054550091820b810150001910003104442071900701d48514032510303581c05018500c00403841221a03522000250302000180c40344140c100040071451861801d40c1c070941904584050611405044030f500c21180300e5000da0b8003500c410718047c0445000d0340c00c0d8000004c0c0d002c5111041c414032710b1800d0000e02100d0303282d001c0d0003481c02c2a501c5050007070414205030418414003011324100c54440c0e20021303016084400314000162201c0b410300d80199802c04200d4640c160403c41e6040c049440010341c410b000d902403c0e000511400402400e0085d003c2c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 749114469 1250 749113219 749113223
    0xf0105060405010309081204141006080303071b240f0903020c04020901030f14010801060e091015080115050306010504061202100903021f0e0103020c250902040801200304 75
    0x4041c0310400c0194001e802a102851280a00e03e00b0045240011881070000b1034040daa1030071500040b84156005000d0003410600304281031241e2424003801958911000d04008100140c620140658141001c0c400d03200540c003a115040c1074402c0c000c403a6014845d080322818082c500000c00d402c054091007401405a13164000c0d0000302800000c000082d00880b20003814180c56660070300d0030143c184580c0000340702c00c1c80c0042c929410201000e086032b0f640c2e00305801c10126130083c0424100c0014900c000c0766030302d03000414620208240c05044001303030390040d140e56080c40341c070001940b082040c0f10280c070415000c40f14140c0c0d03224200010f840403846043c20030303031072600c0308000b50506a059000113030b41800d11181c8155281e0110b510300c3e201c0710b8994200542e100d23a03091803039402107c0c1410200240b03819410304104c0309070140c48002e43c0c40c14400302018082d01c84d040c030707207440c0b03015005240c802411929180e40d40d0101d1f001e011284940d4101d07250803c080c000c29042d0f041680d000d00c1e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 749115719 1250 749114469 749114479
    0x801090c050a181d0307061508060c030a02030a0209150a021513031b140f0d0801030816050c04290a0308190504081603140106060206070f0c170309060f0105 69
    0x4503503018810003041284c00a4440e03c0020080d80411034003000142452442200b000032860720150302c1a91407100c503000300003160800414802400624401d9a070041901c035001a82c9450721310190000740b1130100c0705600003403000b01c4035404402c01c90207401c01300c100d9000d4460410344280485070f05442110403c0014500000030800300740b042323000d800d098050141442c1071210b01d40b184410784502182c0c203480c5901c404050034400100b4425032070100014100b485865056540304041c5000f0070302e12020321600d0021440c00e011041000301c4400b48064020005050f0420404014845900c07008c00380000c001181c40e000c2c28000c05240c1101d400260060401c10301642c000707490344100011004001060002240d0784800340603520b500c020461510802c81d107180307442440140382045090090345801000c02800742c0120704140c0c0140300e490002e150703c084000c2030f6401c101144020f40017000030100503a5075480e1000030360103510240200e800664901d4012003802c82c00b401410341203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 749116969 1250 749115719 749115749
    0x30c2c0703020904060305030c01060816031509033b010e0307150504081f110a09180908031003110607050c090606070501150501030e010c1704080906040801090c050a 73
    0x8244a82c0c081d10690200800c0892101c5e6243c46880c03541d008240c00c40a542d540703450070810018100b19290215208c448441006403550300c864079118584909035030381546410315942090f00c166840100c2c1d401c0d2814022a04100b010b4404d804405441759201c100075068004510b9806000d104003450002401480e825081140303c224000326035121b002031020a100109899030140540d80040d580c40d1500703c0d121048002a1080c0c03119620780a8040c1002c001a00c44150312624401c2643c4240005251881940c1408001051071010260487c0c030007001303101d1100710717220a807012603001c4e1007043c44c44102481042564490950b000300103901c0342d8408000340c03c1100c1c41581c030180080442d4204041603c0329801c0d42c611049207402083e100c0c0b824800e540c4c0500c55002c01c611100020170200400c100080c0000e0941040201040c062030000340401071000121007011402515054465a0b920030b418041d00850208070350341d64001c0c40200321401d0156114040b40c50400e0000301c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 749118219 1250 749116969 749116981
    0xc0c08010b150703110615091506030f07051b0c130501050d0b130f3002070b090406030503300c03010905090703020405090c04050a0605031e0f07030c2c 67
    0x42e41c2c0084022814003035000611010042c0a0013400d1203500345030b042540c00301c0810b04220904400600a02a01e10310311b10203a800e4a419068a600c1804d28880801319150301e0310940d018080e01580401080314040303015075910005c03803410481c2c13000341c038150301e1800010541805d681c1c09000d1a40c0281c808219900032a410005203070308042c0d0420b40c0031480049840300a6203d1076150261003941c0541071b680e5000c864201c0840c0041051031401400b0b03262680003c1d180c440700c0c8034002d51a41e0205611100b0303038499008100465002e0300b126034422143d040d802c01018a28401c3d4500310100100007201610031100c0340c420248008900d20b10b81c01c00c10207100402d006002403d50b4421f29501000507140c40c0304803401007844e04010410a4241d000b008280c0b400200740510050514208202c1ca840010b10485884260700700031064464542c500c500e40a00c81c803445c4902e1007156800414815644c40c1d00040e158851195002904103001940320110349125440c4005268800195 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 749119469 1250 749118219 749118259
    0x20705030f0706021c0e0d020a20030c0604030302060106090f270b100206190e0c06280e10020f0d030b040f0e01360204020f0d0207030c0c08010b 64
    0x1e20b03441200014200000401204100401c86801900e455900e950100c442c030020400706400700424030041c4103600c05a520481c072000c90b030342c05119030a01c81d2410050f9030303400d1002c0c010b1441e002c0c0140e9221540c90400a5641000303124503030200e29480000324000e0310b00c085440503140e1242401c501c601d29050700c460300700f881105000545640f010303203609580d210300094005071440da000b003045d0f00b000218241e0f01d2400941c0008143c3c50185941d071108000309100c61640002c48200303448022031601048050540000a03006045040c00c0e800c800b038114004000b042c1064411560f62034050009036591304903010403401c00e82c0205190310b041482a08041c28046020704081021410410b425090368001f500c1c02040b65100d410171040c48001d46a1a425440c1c4040380070404aa2584640484540d105000c1c0c000c540014071070805041035800c071080c00f10405c104560b245840c2c1001400c0c40d03445142111160482c1900040b4a0014060400020390050a03074030f004140d440f4101c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 749120719 1250 749119469 749119477
    0x20d140903030c0105070e0109050922020a091e02041d06060904141f03020a03030e04090210020307210207060e120a0c090b061e0703030b06220504020705030f 70
    0x881440100610303045a10180003a248540c5044004943d605107004c0152111140700b400a04000c0c80910401c1135945400390030340c019500c0034240001c2030038031810b03d00b8603100850280d04814540f1000441110b10781c400403480c600000b00100c00000840304001764420340c0b1485551803001905650b000e000c91400c10b410400081c400c900d024021004036041d00d41158a0210b011701c5181003140c6448004240c2441450f0403612159041c256800074529800a0201400700000e2040f020050f403229440362008980080c00300c04440300d035110007583c80c1c0c8010400c907406070501e4402c41d42c41c6049a502400d18101d500a4080942000c104486060613440c443d1f90081d6107001643e2054010710030300e482280120803850500e814030265409484c58504042d009000402c000b10920300d00c1900c860b030f485203000380c05503074081e5410304070080d00070700031025800300c4002140355080100020403000c0d80d120075581c0c82c84956440401040b8005d03048094000d801c10007801c0360307172042c10000b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 749121969 1250 749120719 749120747
    0xf1103090a2f010f0909152301050403200406030c05040f060825180b03071e060c020d0212010519110313170c0c120c010e10051611180106020d 63
    0x2502c80c0e565a0300742c49060741c0d0061440200000f00c2d5805001c05003000454440d1448d880040c1080c129490780004c11600c1213100207090700b4403442800b4441411b045640c10304000080050228548a027004c21111a040c0302c3c182c4501c0c90800000d1100004d8011502180e0442010300b0b1140c040c615841490038250007440c10420f181140030070802804640d056064105c5000082d0642618050502e09861170b04584203084448a0700b1010050004405040d154145041e00c20601c0303d2000c2030100d10040c8001f9801540c0e00b80c5100030510542c8003921a030f00700c0304c03650080c81034003034030904817041ca0002c1074044400704002444000450111070403039100346840c1c024000300e0020f0007010f0f008010000b03040c0d0000100d0030780783d182001c111030200340c00c1c10181c0490703034444001800d40c9215403041800b5090400c03805150500500669540b1160300b580c01000c3d000900d00003400002d102c81c010310420022204c680123030204100c56059806680003410940c0c8560401c4d02c0c0c46811801c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 749123219 1250 749121969 749121977
    0xc060a050f030a06150c080415030605030a060b09010b0408120a021e100f0b010c060c0504080a03031b0f080f1012031d06090f01030f1103090a2f010f 66
    0x1280c244044560015803080790f0b090000180103043c041401103c0c02c52100b03070340c06c120300b101d08100401d03250412075044070704e090240d0b13082e02c1c440703282980030708115807003143d01d40280100082030107450340000180c0d001c1100c040a440e0b0300d403103035001d0b240124043d0010035844000417115020000004007404949401250360380d0404800c50800c03521000000b0300c1c1900000160040c04466010b00540701c0300d116000d00080d0500e40000f41650310344003001c4c040319214909a10484e008804a801500b0550140d4010f148107040182c007a125203180c3e4283c5801075230303000418a1080c0003d5110300c1159076000450b40324450b485500500140112601041d81031002860740542540c0d240c1c03551013529801c0c02680852500c07415851244845400360400708409011691070b425500c00d490300034240082c000004c60072450040001c0c7c05a070090000010a000d03036900e00040142c8c445100c1d10001c841d580c020441d080d022800301040b22124050070010502d698000c0644052080701490 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 749124469 1250 749123219 749123227
    0x20a0215041401091a06060315090a111306090509090d05130e070c03021903051e0f03100e0702070b04050904060e0a0c0f0b120a02030c13081f0e0c060a05 68
    0xc62800c40d030b0350fa88101c0d00c8140900301d44001401e1188170304d502040031900641140f40c9980f201800e03120564407184594150400100200b079030b5440354003030080000c0030315102c14410304107907154517640c001e4401141e42c01e0f500085500c0d000c034809206008a00161000070442c10301a201038101c01210b8004029500010400c80109084188921501d0303032202548032044c10046d0a007042d041c08080411441950040440c0e00981151402011881e40304c044084000e2403003100c4c0140e101c1102100340000602010019000c2140e0a5400107a20002941c440d40c0c81640d85091134404c15907098401e000c1044185403650b0304940c014000c0f00c000c140c131051048010708004d44007070116451500900305100310345114010710058030b07040c54080e180490340c001c00e000c490300040c9021f64050b000800100307603c0000c0240c2d0080f81089041000076500c44044a407100d00c4210340c09001040d807004d1080f8104107005640308a030508019101d1080b198084c07125561011141c0b005000e0204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 749125719 1250 749124469 749124503
    0x90904020a031b0f14090105130e0610031b0609150918060305010b04110906070309050603070f032019140c010906200301210822050301020a021504 65
    0x80003c2e9503c28403607103040c030070b04201d0420103240c2190012805840800b440e0350301600c032450313a541541ca0441c2c1098040c000c40510a02500c1245003a5046000e104144030781000781c40030b0502600d1059114140480f00e4014031181041d0a12810000515405c03041000004005e183c042c051824038200442c2626807000ca00541c162001d0540b00c0c543c0c644082003442403c0c03080c0440d1000851341030185641c2c507004030b2894001d10620b98481c00d00000c00000f0580520401001031001405503503c91822140c0039014500103400c81010900b4014a44100391100344895055450030b446981030107003851401c01d002a1103125101803000d182d0003000e1058004004c0d080c044d14040c00401c50a200340391407000c2d2481c51002001c46d800030310300d00b4001188a030a0741d042d500345200346c0c1d000c0a0b00d456400182c04402d14080c7c1590030019091608017080240000301c600100c0c2d49444066940b0180340c01c134415049448010b8001108c4c0b203402c035010b541c2d99900710740510341210354801d002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 749126969 1250 749125719 749125733
    0x60708150402190e030d030e0d030506040603050d0804060b030a1e0303140c220501080402060a0e04090b04061b0f03150518040b01090905030f0304080d3e090904020a03 74
    0x40f048000300c1d0b0000f04609107441c007044440d00d29403082c03405016081220000d25a203420741881d1206040d1180d001481c55200c980c0400011034001003111f0500e0340428028090840640301074620f0b83c14174480f0b08250800146080300700e54049541e030703c9942d00300c00501c030706401140120105602c42c4411005501c0f40143c0d680160304607032a0555804000b00c0c0840d170b8890880c1c5400600110400800c07a6a070040c41c031640c01601070307410716501e50381408204c1700b81c0910200c19601a292201e80d1051003000c921040c0b08038440d03501000740344401c0200c903181c0b4078100c240c1800140f01f60248285030303100c0d4001402900b00d94042014150702c07400050042040080300c28030801404c0304200a00c031048000d180101011501081343d00b080c0d0321200d490b446008a2004042e40000218080207012000c48503071103006d900c10403030300410740c591b0011085506e5a1204681c0310079100d211011102118600034840f5007481c41c50002c0d60000c0c001c281800070030507a40414092070000c0031a9134 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 749128219 1250 749126969 749127007
    0x906090c090904030503090f0609060a1d0303010b130806040f02040c0e1c170a020307031412090a030f0e0a030f02060702271302030c13110408070503010c02060708150402 75
    0x481c5e01c1c0c0913200d00d04038003100e01d0a0380e20000202d05a2024042c00712024000c1742c01c0703401800c1c0704000314a594a103110340000c6806aa00d01245210010000502201e8040548200b6090790b002a1003145e540702d01d1940c3d800103547c003400120000d8049401840e10398806948081d0398244016400d003408001912407001004034085086042001800c11460704030480f255800c40e500c450503c801514020b50328007621000500303110000b4000400c452842c8140e6080b005080d01503c01807034449011500e030302802c0c604a000c5144400c41640d46400b460100541410140c00c0c4500c03585562904421484014030a0303801410802604000d030300d80c149081c10400c8001030127403d240340c4510245111900400d805c403c0002003600e0f0006030340202d802c441503c022a510340c1101c4000c0b2150004229012100790349200c0000c000860105c0819850102c031401c4008009000d100c2c0402e0ba1254805c0383e080340041e900b60000f401108026070380700441d1502400c01400c11010705164070400c41c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 749129469 1250 749128219 749128223
    0x1f030e0f1e01150303020304060503100e09010906060503010b152808070f17011e081b04110711150702040204030b1602010614010e190b090a0b04050906090c090904 72
    0x4080480701203586024042c1036080840d407240344018510b03640340292240180d009220800c0400000306409540c1c904030000580148041c01c2002d080c09600b0034020140584d0449449050060009072480c040c0310b00c00c01c0d03200140407209400c3c0000344840b80c4e588203a8402c24281c200329103901803105c0c03000004404610390340f240d40c4030303040c011405040011240401410045401c142801c0d5500078408541124100300030b1031006a0103040c3d94010410701e80001082e8071584180c1c14a104080a1014032000c1c00c0d2030801001c00c0b0904448500c3c41500005840680452151411400d1620301030f07600084111000781080395540c000b9060742e0080d84140c5000c1d0b814010310004000f06254541c400da0035000801c5001d14080342e8000c1d0b10900c1455506001c0306040440d1592900b00140100d52003d6082c070061907118100c214039a000040040e000e4a040c04020422a02580840303003034400060410082d65909810846035500051060914600a00c0942540e48130380840318080c40c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 749130719 1250 749129469 749129503
    0x215040c03052b0f170f1602031e0705070e15040e0303160e0315040605091e1002030a110a09140d170c0115080601050f1f030e0f 57
    0x181ca14141603150901031041c1d20301c0380000f40980e000900001840300e00040700d9040280c144000d07080d05491020f400700320841c140300c0e031400b00040c201103d045548079510449503e00200c44242c012617030707270240c5940b0480828103c0d0310f2403421202d103809098514404c004803102c40d80c441d0210b4920380010758080040c024003a17070024243c40c19014220144124000071030444c03500c50300c0c01c2c41c2d07081520070100600c1400201039034252000e01ca05a0303003003101350501007241000e14120006040031038540c00d0500030b003002000c81d947c2030b100e00062440514005c0c4001c070002c4c40c45400941c80a4030150343c0f296100200040311540e10050683c500d07c0c0e89400300d01a144c0003508484110848043d8428045c01c41040f000a103607404070b481d0b40784104030003919040c0c0c2035030890040001130720540039640300500004007908002103160689a00750340310400d0801d01010701c0002c005002c8418010a8440f1040000d21701c258810300c10b20016008a91079003560360343c03584c104400390020090301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 749131969 1250 749130719 749130743
    0x50f0307050c01090b18090604020c0a0c14010e012001060f060e0a050103020301210204020f040f03141b240a2006091c020307120519020f0c0f01021504 67
    0x69a0001c45071002017480304449882c0c41c40444144440e04664000c043c0304014034004584103480301c0c3e040d07402003007041d0300301c3e40399541034103040c0d044507330b10310640315001840184030646503c120b000344680a01a15052030402c201001100c8052000c0509012596140710000303580800707504500080406440714040800d04205211b4400c850fa005a8107050042004010032486104450f92a8a034100e950506195910000c5c0103840f80c1d074902e0150b028082408540e0b10070700020300c01141c2c03145000d80f000b4504d84030215100c0c90b8800340c0514400d5910081544e90074000b10a409240801141d000b1445103003d001e400c40c0c00c40410070700026010000031008419444a80009246200090010b490040e00e82580c490043c015903551055105450900c00d008000740c44008e50300500e000c204000c5c5010040a81e04a540c401ba1800c80380d124404142d80041400009450102c1c050b0500000400070700c140080144003041c118820250301c0383c2840900c1c0c44283c081c0d44184001918 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 749133219 1250 749131969 749131993
    0x16020612040b1305120c1005042103141315060f0501020d05040f0302041806021611010c051b0105042633060a3c0503070e04050f030705 60
    0x11a82c00400d005a066045503508000c50000500781c0d80c1d103a91521820381c1c4806801d001420025403038150704256042030144030030007081003c6074100814054402d80d25121a010032400d8507204458208070a402c040440c60450030b07555100c0009025041c1904401410394100e01140c5250307006910030300707203044140030307640e4140b0803407107a403e0500d0980c0c04d09003410301c0382403003010610000344241c1c3c1e1604441c0c0900080b048040d40140c000c90115201c840440c40b0003200000500103d8401c0c0040003488401d40c01280d40904058010303000302030b001130540d07000025074901071901e41404400d000c00550401001c0a01c510348096501408403142c203400400c0c5410440840303102501e0756608819010403200038090b4144000a42c84c0b80e072070b1202d0f00400c10000158210070300e200b400c070401e4008281e042295110b0740d42d0442c0500d40320120183c80401c0c051480c0035695150300801d0f8108254130006c40390700d42190248055800424074040524a181c0c8640b2003155550402203107014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 749134469 1250 749133219 749133233
    0x60111060f100b0405130c0309050d0c0c090203090a0f0215160c050103050f0703050c07201912060504020a080d180b090d0609150f0f05010b0406050304081602061204 73
    0x4010900c1e81c2c103e90801c0c3c14040056168154001d40c80061940c68100209552080d0080721070340707402c18141c034011107078054000d15065000340241e80306035045100080c04691442241c1c41048030034040e02c0260103030381c1d4924143c5400a0300366400452192076034120405107004080c0306802d40c08200c0d42c40369502c2c101101400903840341c2e050500d400208816410012240342d446a40352900040aa46904e009161400307176100141c201c420b00d0440035803030080c038404210041f20440d03400f0001c0e8010000c403c0700c1c8646004800032006600b01810029149402498016100a10403400706455001c007625001b0b240b0358420010700c0754000c0807d5078000100000103440070740d001d60300c1e101c0c0317100100f4000442401e009100940d1690704409021500e80100d1310010100b00c28400807a4082c440005010f181040703000302803500000103502d41140d000c440480346140c490908580e20b03074480d540b2039080300300f0408a150800f01900016a1007070010320b1100c100c03880808890829080840c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 749135719 1250 749134469 749134501
    0xa020a08091501030212070b040b09030f070807120f0b0c07122f01092a050904050c09041403120f0609071e11010f0e0c0108070801030209060111060f 66
    0x300c0301d411034155082c16185070042281503035010b0b40c0e03054110340300601040c034209140d8460258200c021402140c62900d03075005200d44c4204504035410344151480c001d450303a03624481d1040300c0d808241d040006036501000d9184d65030003400002051a06a1581d10840504841442c1c2008000502c4410086684540320124050f0f213442c0241000e5034000b1003440e0b04494415a202050074078029404800350828040d459200101c1045181c00040000c18400c1c0c100355103401c001500e00218650500d0b640e9248180e070040002c02c82d0001c8541030114810340500191050803080c3c00c3c2d1080154100010302510765920b00014013480c00b045c18400511000d0070681c41030400505005d0590b5000091500d107100d901c4100211002200045d035030140003148002155082c40e40e1003c1005456001070004480d510a65030401210401104c410740e00712045000700c0c1d8140014005420b124040c0d50b403203041814891f0310006900240d600d0003004450101c2d99001c2c400c10007241105428200d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 749136969 1250 749135719 749135731
    0x140601080c0f04031113020c06040b0c0c0709090539150d050c25060c032009010c0f0809100305011d041e080d06140112090303090b0a020a08 62
    0xd82c100700360007444490a00c10351001402d400706501c8000510307961841095107024140328215640d07004206002d485800455090b0384038005000010815982c003001c681036804402c0213084131303500745030900f001803244010540e00351007020300b040480e0201303c0ca03800b01121441c14610707200c02410090b1950140c4503a6442c040c00034020115610700d54007050701e0306002e544a003c100c5660b03500190070360380940051000820303007003015020001c4440e44401e1026010710703c20f201c0820f40240070381c01c1c0c4c0c0c0c0320b50080714540303580c621441c01c8000310005010010014500003140d8800c40d2074444000c050518142d504000001d0140124a0b042c1500c1d080f5a9050078184195850600d0a80d41164503600c21280c50140400040c20841c04101c031050084050103551403907005410500d9164100c45139a40d0164a02000131801060121315051100303016501d01c00040ba400701d428001c3c22500c0310407010305445034400382c002000c01c0101e038440c01e0301080050716900c994034000d00c10103001d480 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 749138219 1250 749136969 749136991
    0x3210213170309060d05040311030f04081b030604030804051005250201110301090f090f0302060708090105060918011814010c0801050d06052505120c16060c02010b0414060108 77
    0x10100e070307541340c0390180e0311154218080010580e03103a0400340c2c0c03544c0b134075110342800707007c001203103500e80a420020300243d80c8804129610031100301282000b4042d410303441545940480005000a445002241d5101e071140b000da6040b1099074021106440007a40c0e00020146180c00e00c000001c00c44030b00c00d61900945c07009200002d00403418071150312060084401c090344450380717546010600c0c1c1004c0312060b0b000c4042140504a0f080c02034580906961300000a83c1007800306000080500455026080c0282885440c0c0c5515011850110554140c4600e0f03540b40c24281d0303554814206034951031405103804c3c8011015451001d0308413102012144203001d4558018821034544422003c440b550004001a00341c88032022440d50490b01e45505070b0f0380103600b044c2000194031070050300060810b02d1000c44180c803075820300d55040c050002e200c90b030801c1044119010900d250454240039005000004901540101080c15102200e803c400c4101e004010700404c1d5030301c4081c0c00e601c0610703500c1c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 749139469 1250 749138219 749138227
    0x20307051c14060613090e0f12040f0807060e01050702010c020409050f0f0f060402060d151205010b041e200a02150601031b05030403020705181b090d032102131703 72
    0x5c07103c803101c1d460040b0000030f951524007d0100804100c001d440010420444100b900d01030f0662903036174054014150020340580340003c8000b030009d074500654645495005110021400440d00c503001100207034100101c1d00d28040143c3c0f114812401840e00035006007907009030320290310303192640005048000380e000f018690059800071950036001a4111a12130782c484954800c84050a941e40b80c06044502c80400040c00b0314081818800142c8600f00030320a51174400104811103204034101c0d0503a10b442c20920072020010703401183ca02e4050100514250311507034030901c044e088a030b05c1d10050f84c0004402d5007600440020254059000d18091140401f8482000c25860440056905009010000c101014001e03c03120000d4000a04a210840c00300d44511480d01c1003910034a0040340e020b10f800094500000840d5107011014100c41008000d44d601140d920095040710045480c890001411000b0039000602e406036800c021840d211303040100004880380344030102c1f6010b6100700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 749140719 1250 749139469 749139487
    0x50702011410271b0e03070b1210261903091203020709110703120908030c070218090703030906050c0a150e0d0503011d0f0a020307051c140606 63
    0x41e02c45401e84400208000404804400040c5110780324120382c080241042003201408600c80508a1086810369466401103164424180c9854041c060000c201200b041002010f208802071141c00c00020804040c1c01a61000d200d095034203040005d0f413030381607210034810f01c0c01030402080004000001000101449a130341c0944418080e20482c020506161036020a00d8000d00c1054020300318000d0074020114aa50341d15103d500000301200441c0c1c000e6400d8140030b06500c81e8406556010411a15685480420000c00d4000b0003080741d211001049480511402c583c26078003840c13800c001030640d40c7c15450040d0200e00706800c00020080c050001b5106141c0014a00d00744a800000e075041100003000b00300e029003070024040c2403a01c2040c0b0200c2d0b031680c4c4800154101c8076504c516005d902c000c004984c48400003032351100100c9849001003580b411041d030040d9084181c5013480b5140c200e18404501920f90309900003c0b00d40c0d95500d003014141c810143c903a900c18800c481441c5013a58036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 749141969 1250 749140719 749140741
    0x6080d0309020105070b07020607120e06012304020d05010801060b0c0613061410090506010e0d200901080c010e040504021e061e090a06110a0b06040f0204090507020114 74
    0x100484201515207400c2000d59010f0710840c1d401680200780071409203080403010b96a12415160a00007840c44a501190390041d881003040e8041e82c0f00180c02583d00e000104c01019080105041600401c0442d14020799175920061442641080010920358542610302c0c0c01c543c1c0d07607070208604c103030100556615403401140701c0d54031200044200800714028180500140265a005040c4402c0da0742800b40403183c3c6003010084a0042805101c0d40d80c030070004468041070424100c0e00000000721100c00540f0b4110000e04642840c2c2643c0840c1d444c54002030003640f800e900c010781542080350700715803551307102c0544048801d0030340e81484079017401c2c1d01043d038520b0300011641c0b0300000d1b413101120345c0c3c1d0340504949580782c04110343c0d01d440f400c9540200103a403001c030055204c0e8103018000226103000341117005c4900d004102402d20500c4684815a120034020045070f4801d6031031240800c04c02403440a4400742818010005079803500b001e019084031620b00e028842c4035160420440c865000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 749143219 1250 749141969 749141983
    0x10031b0810290c03041203020c03070f06050f0304060b0303040b1c050103020d12020703020301020a0f030513080403150603050111031e100614091c150203070e04020304031205100501030b040608 85
    0x160b408115514080d02c04502d0550081e60003002c080241070b00c0e441d050513400520307540d14580c01c40c1a6028540d90b41003031581c407e0940301d8000130640600c0307001c50385140e0340041c5500038014840400d003032240e5800a404c5a0050300101201e0b00d011a107600e208800c04070010728002000c00401965042d40c0001d00300c0c0112102c010300c0741d40352410840d0120720901c0f212000795805802591580c0c40e0400c003520349200c400034000000d1501c00060543c41555003050360f03071a0040d0143d441c080c210b8440c581440603241442e603110b030706c4202c0040055030901c00d100c1d9941c06850150b07102c0c1010300c1c6282481c1c41d80c940040280400001380001c58105401c910221800340c14001c00f1014401c84103001409180c044130750102c00003c4440c172506103511a8800700d40700f000c4200c4107810014902c012404151038510000340140f052007450304003075005582040c00f9040c415015201c1480010640c1c10440c0c4003040c0710200202003140d5601402041b40110701141c0034043e0600300260390340c1d0f40c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 749144469 1250 749143219 749143289
    0xb040609050609060c0105040312151809170c1e0303061828020a0905060307020703022205161206030305070b0a02270118050f10031b0810 61
    0x1e0009030f442c03000e90350700c02100d81c0441804000d024030b25003401e0141c64a00c48000c6280035500746003c10054040b0329503854165410600c41020610b40c0700b803060014141c0e6402141d4483d101360100c00300f10080300103080880042e1004044d0b4902880100300d02d03503e00080509294414400c0c4552942e5a00c092102c422090a46507196a0342425590ad6242201c034011b0790800000e82c11256550103400604150b40d00b030b1111101543c0e03690501089100072201080140c000003414030062401e000007040440308110710110703121541e00c100c8111401504ca206501c402041c0b0440880c0e008000090782c050303541c4041101c949144c40180c414468010300810030034040c00010603164040e4162808449403190407008101c104400701d5000f00d1110201d804561501c0c2c81000741038030410020140c0d40302405401c441407a00302404068401501840305141d01c03140d05059002c10710320303400122080d030740d14103200f03040455101e083c0080c0f84c1c1010920b1a0000405420700d02d10304845d5040b41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 749145719 1250 749144469 749144479
    0xc011b05071506050d060609060f060824060a112e1808070302030c010b0901030809010f020c10090e060603160c1a01060e28090902040e0a1208010b04060905 69
    0xb12020b42042c0040556070055940000310f403a500d000e00031180d10039810b46d84010401c01a00c2d0329001c0101d403490b1607125a5001940ca100055600e00b812110b9a801a80032280b401d07008404c0d00002ea000d822050031200000c00030305080001074400c20404910301e40f248002c00c11000440300c0c02441c80030110200c01138a88031b421070b40c0c407032000040b0380b6030703843e001b40c041503d500141c0360083d101d0340300c011902c040b5809c00742102014944429041d0480307501920480c9031490510064900100c1d41050109500991110751000c2d100c900444900010a9a03200d204605020003603480803405004503000c0c00e000d00802c0400c1c15a0502412804480d007098900002540f0b4550407180030310180c0e8100880040000501d030340c104c01000c1c0007100031500039108501c1c10b00c04100c2210055120040600185810013081c103099000b080384034000751001c241d400700e0b4410b10b403074a10b85050440700c0d6400305402c0d200d0310f83d0000d5a6400f402c01d00301c0381d80c0707070601d040300c02802c2103150700616100d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 749146969 1250 749145719 749145743
    0x70f060920041118120601060c1506180c02010b13050603010c080f06090c0f040e0a1d0a0b060109050d080307021515061303061a1309020a12051603080c011b0507 71
    0x3d0b0341e02010190610101c1c1700b00c0d1855a15500014010f0403441000c90f854101c0441d0303071904200d603001d05e400ba00e680803502d460990380004150003512904802400755540d4400d03804c1243c480703030041d0362803407589a008074541c10041d0a150840740e0b40c0784482c1c2008220000e20a41c5200c00c054203400c060304607100a41500c13030440042c0c280c411144160010f030b03000103002820784901c10880b4807070700400c03100b08120036401300894100d83c48038440e10120f070401c6003030032f00140d0b5502e03440744c1003001850031070081500c400109542440d100070640700d520001c400c10400f42c0e810040600c03594400005c0c902541082c5028070f40e003480300b15603140b040700040360f010407105600064500a6400c0305060082c0c1e003c1130303080c05044111442c1035005150f140080480d5880074081c506601c0d42c080c0c030140a280c980380c07050b020341c0708880040f117282c021540300131500c400c103082d440080c40c0a0ba06c4e15070354904003a038041c00c440002e9100b4100162809400340b501c5c0d000015281010780120a417a06 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 749148219 1250 749146969 749147017
    0x140f03090321040b060f060a031505030a0804231c050109021305040b01080615011803080a080a060e04121d03011e050a140c070f0609200411 62
    0x440c001c1494501000022024580804182840302c81c000c40c0074181802142d00d4480074010303032102c400e0190b40c11144c2003000307540c2c1070301c81c1d400220b44800c60280354907400e072130300d00086c04c000400d41c0507074011070007103010b1226075546004800111642000c0c01b410540500206140008020450b8010b0700104131010a200d0290080c00c0a0b41d07001f81040060580851000e0040030140c43c2a02c4646000340007003140240080d0a90040c00905011600f646110004540d04e110b54149000c8805443e50000700040d000000380c2103041143e226100e061820103e00e008883c00360b030080520f098600e0034000442e49102c8503c0f50300049182c4242d20400350341d040384007d010581035035055132815681c040580242e042403203107010107102c144030369200d17946030b5002d0f0382c606a5649030802c0700d1401310703011440700300042c0b000b58443c204208250040d0b0301c2c1e003001c4484201047e00c8642c0c0400504455100007a003941c082d0b40101c0301008030fa0a040d00c081107501599031000d40d1b00c00b682101c800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 749149469 1250 749148219 749148223
    0x50c010c030302040302220b0103050c0d0e0f010204091e021303030507061d011a0603060307060e1513051002030304170306030304090f0207350a0504080607030b0f01140f0309 77
    0x143d50090000387d0360740141c00300204000340440b48140814600490b000c42c56229024003402040c0c0030799a0741c1094a0603802030f0041800d42110222807180404000d0f03012400c0c0003a10007450302020004405000910000e5030010441d400c1c0c000c284100320b050000c5646c4c05200081c1da40500d001600caa440789410002030843c51610328103d4030000101070341000540019a40c03142013400040a80710101c1403002d20f0005689a17035160b0418502171100318072900941c0a0800000d00320311102c5030560503559150b000c01100c206800102c07009004c01e007084e480070700c8101305610055280d03143c1511440000c100303007400c050010320000041280c40c3d81c00c00544015140750201000306680c440e1800c8020341c4444021a0001c0340310404089044140c042e52607000100f221140400860611541c080d6200f0ba2501c4c042c001c050002081c001c008110161081055460014910041c841001001c0b81d280751400d042081e800d401503211030155040d0303021401d42030000d030380780c5c1c0310181d41034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 749150719 1250 749149469 749149477
    0x6071b0803191b020d14121f0807031e120e19090f141003061515050c070f1a0d06030f0f170f070807060b06040620010207050c010c030302 61
    0x28009003403405801035a01c08a003103e05415080e000c803105840c500c08107a848825460702445801414024000d402c54442619580100c00d28401010041031041c00350501c111900720001e030f64000701052042011054030855008226150350086270307a5540c070003000d240d043c29808104102010400c0554489452039411a800d4406030503030b054441c0448401440000c10b48070029081c4020344d0244002d19407241d000746910450001c8441c11511002e0203054070000750350320080041d03000950402143d0068035401c2d816641d466807490180c0000303240c07076110f030030a06055009100410008415040c00304100c21041e111945420b07104807100300625640e48045d240f09480c5110300b0400400e1030f5038144c00d500c100c0c819200b500d02c110f54040a809041444002418100410000b040018024280c258400c1c400400c1800204000c40d03080e07005548101c003c28589401440301da0059205911804020f02c001c60401400d03440e501ea503072074108003e605101c0d11059100500d40310b07030100d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 749151969 1250 749150719 749150761
    0x602012c0f030307020d030b04090515280516030b0a1806150302030402030f0309030706030908070212161d061225090e01090309030b060112090f0506071b0803 70
    0xa203841c4d01c0d1020010b52900c10003400140000d141000701520740c942442010710700c070740140c010003541c030800100000d402805044450644044030055200449180c90551089060400842d003420450000c00c00300c00c1c1e4617101c006060030500207031090385030415100102c2d0080390400c1407031054241180300401300d03074000e403151120b90354400d00c07284d40640007140582d10940465181100d9007486580f2801005187d540c185c00856003003000510070340001c69080d002d04006490645c1d2680051991540d6060f026100d401140c1c03e100991120320080005110304100184c0314841c00e9800295850005e00c007a1040641d10004058002c0400c40703010710708507892031240a076884200c1c400300b44042d44641031085041104d401d95403081802103000ba0b950507240c080f0842c0c1182c1c0c90280069005248504010365002c02040c48820303800780400450050001d50b8280134503007445414940d004200c10248800c00707440381407200d07007149031551080d00400d009440f511a5038081580e40100554 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 749153219 1250 749151969 749151973
    0x6030f0614032806180c0b070b1b0918040b06040c0c1209051c1b050f0d02010e04060e090d030b03030313050705090403020d020c040b060a03022a160602012c0f 70
    0x2444005481718200300c0c60380608410401d441c1d136100005441d108101005180f412958017007030f40741001800c4801c007140e00c0545a030401c00303811b022410000081c04d004e00d40c01a20741c20301041c04050340446030010015101881001246040502914a0340b04010b00c0c070103520004074030003449144488040e20000b08911a008c0c545500000e84010460040d9148000c2c03141a090500d00c0c054000c0440d44054101c00c07010111800300310b040c01c080311040c1d042c020104115000c4e5551846510b002e480d502d00d400e80d0074103080042c00d14180c40e503d0b9000903d40b52465486581e6000816039a110034030700c42e00c401113034040c50300e9800c00c1e0481d4003e41e0060207640c03e00c003c040d004580f0104840480d03007141c140c42c0c2251304220594400a22898009001b0480d908006110350020a0070341909500c10741882880d03a0413518011401200d0300c03481d0000305005081c02c4440d04600c00504c03240c4028000c54100e40c1c0000b8030803806000d4201110b20340b42160b5074150f401d003c550424003250f02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 749154469 1250 749153219 749153231
    0x210221190c050703020d091202010e0d0b0c0403030306090c020c091008120a12092301060f0f0f120c0e0403020f0f030c0106080303100b0a09030501020406030f0614032806 75
    0x1c40507080b40c2003848102e015000c1c142c040e0f50400d2052803898100d41c41400300f4071016805070010354001d40701003a10b23504500d001020002140e0b110302d515006642000b1183d54035851814000c04907010743c2c0000b14064104044001c0f01c0d580000c1e4603410600403540640c00da21010110002001294001906801030311350f81e100f60750040f40607012020450b2a01d40c0081603a9503078500b12110031400074961124502e08412007103103040c10342209440100005141034440880c0380c000f12051348104038100e0403000034080800280c0c0c440000740315858000390001080c1d51011603400d00b81c010803c226a080e0000703014548200700e00c0b455402c02c0380a946e907010942035a19201d50181040244ca036007004c0001492070b400000b124442e0002c804284c0c0c6860502e400012180d0041d00c0d6641042100c0e04007002096003880208002c3c051900e000400d500118528401e0742c000307512504906c50660580c00c1039071004600c0c0c00301e401d030048041d807019496210001250300d0300c00300130f0b080c80e01c0d100c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 749155719 1250 749154469 749154491
    0x1005010902040504061d0c030a0608190c0e090606100509060a0810050a05010c08220e010e01170a030c0503132c0705040e060109090c21022119 63
    0x41d0050069030710648090000e04e48903815130320180500c44400c1e80e500e02d0300001480801446003e160040b82c1e1300f101150781070f070307508243e49080f00c0d40d1415000c55124402d00010010038280e00030040c10501407410642c6070030005151200b20091240d409040a00704241c4810b2103a0229021100300620042d00c1b0399000400500d5024203e480b441800440040403030307145031807002c600803190140e40d02c2811030300740e83c0c03420703003540220641050021441c0c41c0d07204495400144440581340c00020208690316094003480316440692200540488201e00040c5810380820800c41682d01402c04420596040c0341544c40d51144080c1c09040d038610550106240054107490032801e96542520051503113406180590780c08140e40381004554204810841c80c10300161107980500c050402d1a0412340e200000c00c20340e030b060405400003403030003040001604110712a59046118010003103080504924684e2114901c402420890040b4000040e881640c4101d55004404072121f013802008400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 749156969 1250 749155719 749155721
    0x1215050108010c020c010819090602070507060f03140f06040c0905030106080703021f0503160302120c0d0c0807080a020c01021b0d2c01030e0c10090816240210050109 73
    0x540400f80060244101400c00c541c81a5030150042141c000710b4030901e0144480c00000b08104d0740d048801c55000e11094010803000d011090003800c2640398041840c5588100408039001d9030342e000801c25101c024842c241c071a41d00c079240e0141064800103880a00440700341c4240905501c416813540c02c01c4000300f030160002c207a0800b228801d440340140174a0645900c800c00340c0403400b1000141b810320000c0c1c04141010f09070a200581400c2c01481c0030054207034000505011075150480d030b00300207217602100f600e078030503a2041c900c14a0700040ca814244801048410083c0a009545030045162051001d080d81100c2d845551243c00a07101080502e486c2c1e11200004c0c41900403030644402c410304071f0003125000d03101510440c0e030b901100d84140010360040062004100e500e118010800509854100300440403202e0703920780440c052325000840e858500fa1000c003c0c0e5411050306d0401620402c4442c1150340c440d81d040e5980250090706c0101e141010042c18031101c5c40c18000001105601 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 749158219 1250 749156969 749156981
    0x603051504150503012016031b061a01050901080415270620040306023015011b022e1e0504030803040b04020604090e03030105030f0703050601121505010801 69
    0x1003603000380b01b02075040c03030601b83c0507043c039040c412004820172018016005c403441011f0028841d040601c3c00700078080840741043c045075001c40345207a441f401d010800c0c000113403240070f00303909181032460502c541000a2445601402c010b103c3c024894210346100300542207a981c1514684c0c004c50100d01c04920b48203041c1000c541070300d1641c0381c00b10b5250040c1911070a0b03003010315600b8045107002d00c1c41d0b8644000758801920b028410a0102520351100b400300300c00c181c10000c514284850b410500c0022030707104148a1078038103005914a41c031403101c0008402c140c090741c0403111020b1502404440040030b941c02c49009443c6101502c1c035407a01030300b0626180c54102d040c0220140c0c034500080940326071003203020103003001d00c0a03c0000d00140310704a403281c0c85031010700345908041c3d49202c2007054032110307a541d101c25040030005008604003001848018100140201101d0389944c032503503200d110601890b200710303000d074400d1828081c00c00c425000084000708104007942c1d686000342d000b054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 749159469 1250 749158219 749158229
    0x207170307020d140f0f19030506030a0b150a15031401050d06090606051f02071509030b060f10030605090c19140c0d030506090906041509030e030a0c030c0b040f060305150415 77
    0x1fa181d4a4041054440d1082620519001d0018071242c041501c1e03216802000074010000824403510450040d150040c0c00801441032507030081c101c207600c040241c2a5900c9800703d4400840d1900100a19603520364103060481c2c1081c0000340301451428110082c0c1031381e03000145c01600700700716030b04002000701c4803540d9118030340c1c00da03043ca90315003c044910040415800c4009900c2d09010710205034002500d54020000401d0701e5076030f1404401194182c504100400c020903a1480e0070802d60403c0c0c1c510b250f110b102c12060390b20302260f9851074544102c10400e00010000071000700801803a0342d0089564840411045540c0280c6840000300988000c480380e60160143c50701155151700005a107a026552010000503400020342032840102003000041c1c040048112030682e00e80c8041c8408402c060250f070003032503000d055003024008611130354801c03007070341d401007004029941c1a6001002941c040d40f50120391900d580780d4544101c6001c22949901910700400d50300059040005101102c0e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 749160719 1250 749159469 749159497
    0x9090819081e160e0103090f050f01150503070905060a0906091a03061e091504050c19060e01030513080325030e1b0114030a0207170307020d140f0f 65
    0x103880c0e40b007001103a40341642c14244039012055203000c59806441c50340c21011044c50005210b409980b2041c440710a0040d0a1f109a082003040007014482801100c1d010001d03850020301c42450040847c3c0c0d1200310b4401c50f810240d581010616950710711110b00700074600c49000784248e45c1c40d0001800144000488081ca0b102d4030510740c0c4d8503080100c0c125200751089901030b04401c0000d09001102c000080c0564124000d000c20706082030034200d2098080c0e4095002000010312060910413011004085d4160404151100300017050f802409180c14113801c1c600070442c0d03290300071041150302e14804020b1280c9008030800c440c0702c828044082e0548074204122042500243c0c0030340484840607101c11990b0810842e111b03100e416465240900c02d41850301d4101c40d54200c000700820303082036030508030700e80c2c00080c61310900c41e80d92030308030700351b1072007103a080c554200800043e40d21000080d80f4018400505003400c0081510029680c0c0c86400303480c0b4a58406a0b202040b103039074003078811885c140e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 749161969 1250 749160719 749160751
    0x21e010606080a06060c020f0a1505130501020303010806041b030f06020901020607051c023004030906091511121318060f12210c02091501090909081908 67
    0x101100d80134120450b1955103800d454803406409200a10320010150b54002d04850b40015010403680141c19003103285503213042d100d00000306000e1f00801c05500060465009100501c0f81104c0407904a0b04160b229021035141c0001440030281f18040d0740c000703840031074002d80d82002d11110f030300180302914090b4240ca05a41d2503600994490050130a40d100a0203104803004c15040d05600900201d1000d140350400040c1d044084030700e00107010311065801d2203940503c810181c00c805030b54007030308480c00c109590300c1c2800c4400c01d100001101c07003003c104442ea81890070150a10003246284c0001260700d545403000d040c0004004c005105031101c1d003441d010100c0d1140d900e4810340e4141c0380e24603c1403001074503000d241240e6104001c03054960030361520900485c1107020946121008641d1600c0e10071000c0703401002599480180301840001c80c01c4c2e80301c0c815030f0703000b82220f00340c1d5814040003a1300e802c9402e218003680a03041c1200300d07503000c103407150b40707829007000c001440741403180c0025001e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 749163219 1250 749161969 749161981
    0xd090218070f1e11150c0703080f0906060907120504050c0f0a08102304050106030605090303070c08030c041e080d180306020f0921010b0a050901090c021e01060608 72
    0x10185100c01500d01c2030340d00c2d400281101e100300a142c582e07403020011117100004081903440035503000ea509120240002443c0010035400100707a90384843c1071a6110b0071844c3c8601220b45038a0014022803191100d000000e400705d00a082504c0305810003202002a46898a00196100c424205107481400740411806040c5401c1000c003099030061405051407038a4281400c1c0038196080c9104414030001d220031008000e40402d452180d4080c400220311107240d410000200c61014040e544540c00070020404560b41101744285440d60040c3d841e82e49a0f15050740b26664015a00801510346490590040b0b8081741c4a007032080eaa0002c0548410a01c0140e0580305030342e80e9428203402040d6040200007064081d40648840d140d00030700a46002240400150b400443e01303020104041030004036080c822003445000c4070705074142d0f1102c218509001c00184030b075105100300c0d014951240600080d1030f00c03d02013191180112038206000075030f2003420034040c00f680d020b40b0000075800300000e25 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 749164469 1250 749163219 749163227
    0x10b03060105190905060102031b0312010b030f0412020f03041403070506121f0306090501021305030313120609060606051e040509040609050f1914061b0d090218070f 73
    0x102488461021607280000504c06840c000741482d05600048c841200c004018000700c503122000c00018642d83e010100c680f0b1408901a00202642c1d0814420072050350950117040303800035048150820110382404040340b40031400410b541040c0400b0500040201101c044a1900e00301241030301d1085440c0c07010312090b0f0140c54464600743c0c10740740209400030007040b92070811410541007103655a49079200c101c10360b0001c80301194141e41c001007072031000500384565009080700300e0141d85010380e5021000c500148601a4a000d108031210a00800c071003588805405607010506000040c1da6020181054000c09007014100340003982c11510806110201c40548100038041c050503152038481a0007441030001c12039642c130a851440c90b80b81d00420021408809804040324011200d1902000c0445030aa4000311503000f40c061002c1100101001c4803e482c511041c5521106c03140c40d01006040003940c00380d040510007914407401c01d0100001da12501058031030785050b0858001c00c032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 749165719 1250 749164469 749164489
    0x305162616080c03010b3a06060f06020f07051509011101060e04020114030f16050c100e010b030c030706031e020307080609130b0c0d0e0102041212080c030402090a1805010b03060105 80
    0x1103200244220302d0702040c20703246840244d0f401d03c0c1030b0822070980d558823822250140c004c580c042d0b00b0720b2010004940d04102c20b80f00002c0ba0400f07403c0d010319100204d18203a0b225180402101c0021503000c45591180415408001042d03000784640c50b07031400400312502050f90168005201415512455250942105c0c041d8184141022503a922408407241c160907060454007008000c00240014004c1007180524070390107164001039445402c103001e42104e800d624098041e0f0015504480c0325540030405200b210380c1818042084c0170119a000d000344030034a1707a00c1c80b052011080c0400c19901000561084905440680941c0c4420301d90f03a000203041c142c01405903042c2400200104565006040003200d030840c04205545841c04080c2079810035048130061a200c0c0c10381005021190b142c202c210b07002810002d0080c206200281181d2000410290058520310082248201e6503400b00c41818000b00c08088003007102c3c9400c5000e4001e901c29148207205d000700210321460010384003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 749166969 1250 749165719 749165749
    0x816020118080613082a160b1b0c03150103020114030c090d02010909090503071a060108160e1c02040f0506010e010309020d0803100305162616080c03010b 68
    0x2052259115510801314210020f001c072a9100144030445800010b01d4200d03130050305002d03a6100e041c038015130031460101e008485c44205044074104010309a050b4049aa103940384441500c0095100c0c3d54071071074401030540c110707010f20401e00c6c852207032041c5248640c180c0303100b680c401d08544031103101c0c1c0e8001d010664400c04402803c1040c060300d4505001d50320fa00c00e01c103043c5440310341da40d4651a4102c55044ea402e0f01c26404c0040d1490400075106105e903400c40844070910764030b040a800003401d0305d0004210700304900039000602140c901503000840c9100005181c24030078242c91101344542110f0301030032030089040281c5958000254001c45104107070680d078640d00e500c40200110090050f0740c000303980044050758400e01144a94000b18461a48058418101491403400603d80850101c0004000000d00c2c1e05024401c1d410035100c1e0b0786240000c20480a0559594443c2001c4448001c00101a40620002403074034001c2250721380e41a04a00070081c07041d00c0c00034440d0310a200000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 749168219 1250 749166969 749166973
    0x16080703020901090c0c020310091506030308041e0c180e0c060a1d04020c030304200607080a0e0904031d0a0311040507120c021b0d0506160c081602011808 68
    0x14460070513540c1c0036400b0007039186005c0c401e8040c2030700401d041268032500c641ca441e4444081e5070500c00e04070042c00086481c1c4908000451641c3c5000b0305040024000070558440e00c1d800c000c00c0840790b040c1e00b01c0c1e00e40003420b6100e0103030b486a542c10a03007915801300111a00381486031849a40205415024800c0580020302e40000100300711403214034100090f4000c0008032480302c00c0e442d00d01c05003a24140341c100450790307400c250400c0c012401a05460444803940f00b901d81840761603070b0050310960ba92043c901030300d500c0708410540c0c500c6203050255800c0783e000c0b800c00c8140f5901107003204001c0e090320038a01c4407865103c18007250300001d0102501403841080c52440c50708003940910307807180640c40c0c455580341070a0b40110644411054000042e48200441d02400450305046098500c0c1240c0885088045950321a1500002840034103030407016520b0100c85402046404841984070381c459a5515034200c40c07011a015241c1c003640010112800c410002c50204a454113596280700 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 749169469 1250 749168219 749168221
    0x12230c07030909240e070e06030702101d0109050c0118240201200c06160f03051807082103010602070b07080909090c01080c09061227160807030209 65
    0x190700f03c00342240314940312501d00c1031003100e0301480701200803401034858a0700e04281c2c1c1c103000c0401400c0544c0119190321170300d000c00a104680307400040c0350341451030018004c540e0f03400c0802c040c48084106a012801d9509107404081000400710300300a080c84243ca4480400401f030082d09000d11050080c00e62035896903d41071007460384544c0000c3c0b0f000491002050f00b5131030403e1078201e4184030f0415a0f40d500c000c240a8041a4180a034640c0010078500c4601d1100101e000209140c0c151180c400a25035141c001c925100c4140f42e03002d821881d60341c101c40705039981d0007089555001d2001e4454400c0342100510310100c0b4184200c80c1254000c0e40103241083c1000c5851400764000c09044604050801124029072075000324103100704d00010103015880c6100b00050140c3d44010b00003214148100001e01c00e40d0b40391802c1d60b03c2020400000b0480380d48101c010024026003484e4a00b001540f02c41c004240640054140c0c1c400242072008403a441d55000d400b03690b402c0c280070003940400114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 749170719 1250 749169469 749169479
    0x209010c03080a0f0e3009041526071d01030308070e030d05041701060f12030e0310090221031903092315040b041212230c070309 57
    0x3040b1541200b8a04800140300084c031301202c0c21500507819100c0c0903040b08042500d01043e644006101c028911800d00c10400d01000d440907510403c0c00d514425940d454410600041051600020b00f85007039400e80d19034060f0050040466003204040c206200301280400c280d0801184050100000034440f60031b642140c1d0181c0c0c11000040148041003508d2880f144aa6400c0042e401607203850740f0b13007a994030300304032940c070302854060100c800c568100031040040f00c101146100440c0c00001c0c0a0084a01b1071030b04075a013190b03004c83e041d0f062041914000110013968440004d0b00c2c8221181603040f0b1400300114541d041031224074850790020b001e111076441c440c561220402245203000554030110765039004d100740300788902c0c00c03003c0c14003a420f07030312100c040001c0c075902d1650340d0f84076009143c035540343c03c0b156130010001408200c12035040300c50607004078441903004440c02001d02c100054102009130040b07200038540302600004020803000100c039001c071040c10341c01d0741d01d4020a905003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 749171969 1250 749170719 749170727
    0x90403020c0a08241801060312090806241206040804151e0f170f010801050a0e07050609030a0b090109110409030e0f13090809040c03020c150717040f0b0a0209010c03 73
    0x14010700f98407903172480c07400c0c00040a06c141c4029502c0b6100d1684508540d00d0010022000e50f007201c2041c1d0b1100c410700000c403030382c4a10360070b44540b000c92010300d10313881c04003003112001881241d502a00c5510140020000075102030410b444260080c220300342d01030202200c3c03245c4036101814005a40700701e07083e2003910918414444001c1800c00780e001c00701c0d0041c1200840e40481c1d4600c17075807600b00018090024203009898100e2a100801d02814854917561500c8540310b20940e442040001100700b210b450070f01035444120303040840030120b8901460500c0c0a808400021908105a51405a41d5140c10b209940300c40781c040d034401020070740000c2030004440b02c115100c2d601500811754070840110502403000c2803842540310075200e0a010052100343e407100ca800e00705160061140b080c4c9c000c0d0004035400c02c0c1c40a42644c04043e207070454203803000c19900c800a0445801c81041109011401c50240010351240d04041803507034500e002a400c038003400082500181d890001300004ca032107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 749173219 1250 749171969 749171971
    0x80c0102162c010e10050f010e040213170a050721020907030e10201e030c0d0207081207170a020c0c0d03020124030b0601080a0209090403020c0a0824 66
    0x106031003084400c0e482075072842020907480451914408400c0024403110501e200f0010b100c181e035030181a10f041c10000c2e040b511824001350242d07601240d0100000d001290200041001b000400b5043740d0440003d529400c0c201e1040d200381c410710000081110700c40c020b41800038101211030301201125420014299030141c40706040507110004861000c2d001c0c0014030100ca802e00001603403000800460300800f0950050803094101800010303d11180301d000010b001085a180965076619070030307603c0d2103000740d20f41c42e86550b10108801c820030490708000c01e2440308030082c90b00240d444060495510424018a803828803215000c40c80758660354000c2c280b02c83c4c401c01900c0d403062065000c1407100080000540040c2e440340c1e25040c0d0010120301c07100302c0c211010b2030143c800d41991124590079002038102c2d41000404000544d600030320341c0c143c0d89620401408034440b070510f418000d6440e03000c10080d038851070114a000410250001e810141000d4038101000721600d48002001c013504 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 749174469 1250 749173219 749173259
    0x80f0c01050f0d1b080915010506090423042402090d030e010c020415030c05060721090306090c0e0705071a0424020a0206060f0915010203040803040609080c010216 72
    0x40c0380c0d000c401c0c000c0c101818004c0e21995a50710040b07246402d0452600d0039a03a1101072880c0d45240f0300520007502d0300360031505104000e40740410190600c0c808480d09101e1404019901c1d0091428002040740c00c030001c2d03d58181004480816019101c5040d00302e2040c5548654090f4144050500207401100000f1402c04141410245101240c020a007524003642a003159102000003c0c81085030340307865071000e000188c0e140380c24001d460740d810851101071207082c12540c0009441030981403140041c0f45c040c60303008009014400c00b070310f400e0300412020300418100200190029600d68030800946482c1504401d0400003182410707143c0307e840b80003500030784041d0070f00060161041c0103c1803000d500007030680010396421488c0c10090034094040c0419200d501c81810011070360342c51107500da4110490030000b0121840c1d0303500503841e41c0720366400442c83d40004140090159006809001250005c0041c0c8414401c0b407401284c41d040741d0702220002d8142c11340248041050381030300d51040e070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 749175719 1250 749174469 749174471
    0x607030f0f0c02010f0e0312041e080a031a0306060a03110301330504060e040b071206090e07120317040c050d0f0615030c3309080f0c01050f0d 63
    0x842040c020940b0a00051000541c0d1541c4041c400c0208500c20000b0a064100295013007107150030208220010141c00a001096108100c1b03148100000ca00401c140c0e000b01400d0744c030400c02201801400c40300200508803510f200c40e41c075050401180c218490000142207003003082c2155240051060b00c2d002c071541540d60749441841c01d15201c041c48030740300224482e41041d8001c00122a0300ca01098104e140a03130300340750080003001846030106410541c40078118145545070202115804451801001c881d401d00100107802113507648a07401c0c007010031040e10090f0780c40b001d075100350101c071240c0200040d50510440700c1400364115905c0c0c10601c91007030b0303240c003503035500002d1001c400056040d00d854015006407400c0107814810200940e080416441000c2d113142c4444081204610500b1001049403000c102445048801c40303906105640d0001c407400d20100c0c0c0182011403502030107116209000c020415407000103508054600169562807424442034103805480c0c020301c110f2590301d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 749176969 1250 749175719 749175731
    0x190b030c0a1403040605180c01020a0b070e0d0b010f06140703030914010504081201120507090b0402092706031506010f120c1107150203040302091e01031a07080106020607030f 77
    0x140b41401580124001c08001c141414080d814074180c0801091456142c3c0c000107000c0a5640c0114011140940200d01561140c2d10b22038251200b449024607030b50722100b8544144208032080740d540c2d050f960302c031026100d000d4851380c0c161415081c03201811111a018000103000922a401500000e4401c01d080981c60301e1100071a801c0da0303001e80d82146d1603003010030010416604c4400c048d00510040245c01600344160b21115120b031034900030080515151f00c5510302c0341d1155012242d22040c00b42c091103104545418503000714068417950301c00302e260352020400300d10f000100ac41e100c1d040d05c00706150035268a00151454859070301c07080300703210343c1400c0e20340e0044440c0b0429254401545411407000c06050080382000c2c1c882c0c1108118010007651200090380c000142e07425254166440e200d2a1030f0314001155050010150b601000c04500011007000400c41000a107079110000e824015113603c0c6096607107400c00d019990041c0d01c444000340100d03100e508811100c0040034800220 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 749178219 1250 749176969 749176997
    0x6070f0b0403020a1b0621110708090a06031b2f0606330904020c0708070614070213090c090c0c0308090114071112041202190b030c0a 59
    0x80320080700c041d00981c00030b40581c8117004241201070045a41101074200c500e0a0034806080018140c0d000c60031250301012500c070000e400d500190444418160007078451a0078504502d10342c3c45030282c20f000340b010040002d02103010f4019694099030010224000080041084994146100031489000c11021808801c40a845103508800d107a01010300b1461801400f0b10110000404d580361078103010340c100003070690f034000c00307003160340d20095100c0d554840010018010303005102189089008030600059040000160340040b606103450b00048441c1c0c120100300a401a10b030301039044091400c1c000c0200c0100d90001d070015100c0e0903102c851035100d00d12030049806542c04000416101d00c0b4001c280b5400403d183c1e404900030000340300c074082a000503ca01d100180c034038010f104c0304c0d6107080724444040c445a042804619001600d90b99100d9101e4451986d06509074040c4c0141907280d0f01c0c10110045000540348040e95a5141d6120400812070f01d500002c8908100040c1c5106902 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 749179469 1250 749178219 749178233
    0x30c050304050a0b250c05010e06070602040e090d0306030213020f0d090b1e0907060c0f06020313150203040201020a140109020423100e1617040f060b060702010e06070f 74
    0x40a4a915071490341c441401c0e00c56a40a85e854030705042d22501e60000e00f40018100c1324000b003d4410a02c2c10420050895000c039400b4041c0c84c0c0c00038038007400424081001404107178518444d51880c0120f034940844035a040e82102c45078000030703401c29500310344e0384840c4a045d001441c1c89450054240d181c01010340d965000c0b180450303c100c03507005850042c0300c01c1d00c0d450a84138080f2010f81c905103010341801407107a60340b5401c52041e14144103014190000f44605020140c0850360090002d66680c60001e00202080000c2801142e001034010b0300f0307554610461003aa0303c5242d060f0028804022280c4501c541c0d2840c0700d0700600190b48a000800060f00c0d14080d1003041c03640b12603002050070490002e0448190014a031600c03042078080204006680f13000b0803500150080150b400504402c0011280c480001d05200368038400d050a000070440380e64402400240641c0c810443c4101c46810880a80303d204000381c006995090124a0341c9008001403460078402c100c03503110b03040199038000e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 749180719 1250 749179469 749179489
    0x50f0408031b0405030d0f140405060706050406090b100807060f17040203012909130f0f230c01080f150111012714190f03020a08040b0a0e031207030c05030405 70
    0x1c40054030b03030383d0110242032304408a61210038206070064282424000450010300071550b000c0d100a84803004101030109075800b80c2252600300b081907a00b460f11840c607620824051243e03042d1072042d4940014210f214000c0380c0180301072581c5102440c0842c00c0740c070001f4513000c0d00981e4155070310124070400c200140c803080501d089400414840300b030440104028610020940c100100780400101c0001d0180c1c402080038076802644501036004d18104202000c1d034001c480d001d1490300c0b03502281c55079000034481c0b20312a800d0ba00c511103655555280d819540c0d041c2d4060018145000001e1102c1d03000740c0d4103485030b014420000881001000002c4115000441e2204500302540320b00300501002030307402e90118034040001c002c02c43d007000c043c030a8451540c1c00030341000703c1440103000b0144240142803409410500301078489840384601c1031240e0040d44c15101040481901c0c003d01c0c2008150b082c0007001d44c444550600c406500d00f683c141500800171600c90104000103d11341d603681c5003034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 749181969 1250 749180719 749180743
    0xb0709081b0f06040308041a0d02040b04150c24020c030f0903122511030604200f0901090c020304081204030b0619050f180906060103050f0408031b040503 68
    0x70500612861052203160004046514003410b001c1000344046452001190100d81000c04008601038240e0249040c1c0c2c001c1c0038099a030240000740c00640b1111038400703003081d104046600c10500352501d01c25a051100303018001c098014000c050b402184d00e2103420005a2043d11015103407000c91400c45040d944002c2c51211402e50200d481e428070300b003c21800c4145626460b0b800d01c0c0c145200710031920004001055202c14013224920f2081041c4d8100e2074a00900281c210350303150500e49001c0d010f00138070550422214400038603628440c5096605d07400703821000740040c103490b400d01440c200500f140011017415488208000117102404008540c0300d0841034030115200c0782107150112101002521407032140b04c800244090140781400c4000c12100110b448002d012108800716440d800c004000c5c160750700307284e000c0104050020680384c4c8140000d90303040080b0341d500407154070812005c3c0c4001e00000030510006691a800e000b0310007401e5244449281020354400c00a07141088581207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 749183219 1250 749181969 749182003
    0x340905061323060d150911090f0105010813110f0f0a0b03060a0b0406120b121005040519051209011b08070605070e010e092212110606010801030b070908 67
    0x260040c03500030030100c2c2e0f400103000c541124540361991110445e40c801c4124800601d5500c05e4581c040141e019600c0c1c1030010045d2603001245800d80110208050900c0380780d010500c040005440402c040e407c00d10210f6200700c403000b611039190144440c100070325008940201400c65400d10a0b92000380c0e04004150b821111a9030346002418000c10b601107500c083d8030700005120512000ba0004809400303072240250001d10000f100000440200340c2500406050088404a00340b4403420b4000c94495070195040728006042d504c181e0900d0304200308090440c3d00140142071200302c00c030004101d40790051506580111040790100480384901c5c20803210341d100018403c08002c40380c026150b0001007410004078001c82e10001901c440640c511280c85403291034002607a246448601100040c0b44130858103030403100d1300c2d0040d4440710781e070351504c049401d0404000d425500021020b01c100c5d0306a4034800f45920355526091006070240440051040540300032130745110400c6480c0c5d0410120b01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 749184469 1250 749183219 749183261
    0x18061208031503031201050d05011e240609180b090a0e0f060f060112020c07030c0302091315050403050c0124050a03021f020a143409050613 62
    0x10300c4100c0c02d07100e000090080c0c20a002034072002240707030206811900107851140e411003013460144e00609841c0d0380c07a2a005100d507020300c0d0950b101d070301400000552045c90294601950298040d000b09c610a03c0c0004102007814130400756681f420b001c0038140014080303440c45442c4c002601d101002c0317411802d810360311400d0120500080003901d85c2045490b000c1d06890814220380c1c04001d4004180b20305112000d42c0150790740c0c40e030b60b046a980303c596905440e42c4541301e181861010091344001d034032903901100800c405044403800c904506900c690b528009104001d9000302520b8000c2040d402d00c50300788003d41c0e21000c03e0143c4406a202ea02c8420301d070000f4184000b4103180542c20590190030035001c1800140c65682070118000c0301c0018104a100100c50700702d02d0000c4050000700421140b41140342c6071032000a200b1216510040700c01040e050270703101104c0d4181040c500c400305a1141600f003096000340c3d4401504041e015103120542003000c01c071041a903481c42c80c2c00c24082d0240c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 749185719 1250 749184469 749184481
    0x601060206100914041b090e1c050a02060114180406090507080309010219050a080f0a0818191106040803030609090319030c120f0213060f02071806120803 68
    0x442ca58010b031800303400c20003161503c05041c07001e120009100030300000500f00702611886000300d0401c0213100036503041c803000c00b00754503550303c48a20304200301d041c400d44030310408118010420750307500000070750051103541c2c40d01e81001182e000c9030103111741110380112101159034148a4151065000380000700300c1c0c80b0b45103411841e06c10254040c104a410030b11141c20980e81c0860001c99116a800011702c0400440c10000e0901c1d50207800244544c0c80000c000308142d1900020304425001c03901c52a60310380e286024003181e820751200e940d41d90b030880e078940d010144420f44a0036201307000b060240d820314009070114880c2c1c0d105422512841d0b01c040200300d450f02c1c1105401e9445441c400185007008206a0f0030628910b0300e644c00400d01d0f48600c82189094440e100182c0004541c0340280a43d07602c9116420013076220480c01314103810b43c2d00000c00e0281c015028001d25258641c0209400c40c500324402c200c0310020341c5040c17071054507003400007800e41c400c039041c0340014000c010f240e80c0c0e41025 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 749186969 1250 749185719 749185741
    0x30702120a05070f0204020c0f16090507270503010f0f0f06030b040b090a0206031305010b010f0906050903030403080c030a090f05131e05040c14040e10020a020f0601060206 76
    0x2460000c8022004110150500c0e501400ba41d904540c041820400e400c07691002a0190041c540c00c4030092140c01031500700d114000030409072070310300164500d130141e840300146420356401716511800f01e4000c508643c4198206110a4101c101a07224142d01c140c58500080c2551070a24407000300503203a000350f00035200c40c0c2c07285810104880504000c1146540d40d0445000c0f00248003800d4100e52100042140100340300c401e51880e401040103031303640b921043c144200d0343d000909603a590319149610010354021040d03040e0144480e04c0300c049580c644541141e0756270154004a416010074440040092000800740445203801c038060344d107071481c0c250000c0c443c20041d03021808040c4e41100230030140d107a002c0400121240724401003003204c010242e0a4420241c1044050030b40d14000400060000e160003d030140c50343d080c07130344c6040c400b040100416aa00035070704494603000552400201380c02a40108003032050750043d1141355000041e03090900009070301142c0580c1000b0708001c061021 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 749188219 1250 749186969 749186983
    0x30618100608030c070e060a090c09030b0a060e07050304112b06360308060d021309030305060102031206041d0303070306180911010c03030b030709090b070e1f0314010605030702 78
    0x99911b402070070b450000c00090740402ca0b4810401c1d002c0d911412124207910809240b0059600b20a565505052600e03424004256900c1640c10760306a04001c6040a0700c1002201e0190703411104075071034a413052041144505900312887c4001c03140e801014005140102c01c40280b5014110015848486954071801062200c01c2c20065440c10303c940c0f00034038803c2d8101d8907240e40500c0c190b045945d40c1d8020481c00143c0550180d4040d10356121404030f0141d40d004134036054402c0c0c1d4203200382d0b00c6980c010380e601d000760741004545100d0500080e2301410554020040c1007407400100883c6510140001e09550050b24550002230b1140014400c0e05a00a00c401981c1d800c240d0800a145c255103840340d407440704040309810400d00c4000c90090600c81e8010900068005042d6036060396142c107030400602540c10f04442e61a6040300140744203000f440c3c4940800001b0309004140221540000d2034189010752060505690b08018641078a60200c40ca018054940701d082c1d072403c0040010380b809d44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 749189469 1250 749188219 749188229
    0x2a0303030f14090a0602030a181103161d10090c0206071107030807060c0e040c0504141504062601030b0402210309010f030f09051f0209030618100608030c07 69
    0x1880c14041c00800000703c4028990f00085d005860f520b4600300c0801501c0003064054000c020104010244040180000e03128441201100c401074007012043e0300e07014451140e041c143c05a141c0e56013100c0060340d000d41d84480d02d0021300518584401c504003c0391604810f100051740b04404110086800c068030943e1004600001c01144d8079543c0e900d0b000d803007607400041c20b032911403440c6100c8a00900341804403000040c02071140808094004040350043c1c07148104a041d040e2401580381811000d070040200244035030b0b4500303401c0c840d00751498145403100303400d00120541c1d19161401c1c1c48454038042d509c9892044068103142c010071244141c03039060581d20818030345031006000b0b00002180d02c0d000081c201480b0010381a030f000ea0080a5600030125110b00300711042e404c22001142107154959900d80d1400021500d01c5860200d019890649805520060116000044080a0351310404091003164a18105d00e180b20303040c0d544990029100b40c3c0081344102c40e0140030300ca0440984 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 749190719 1250 749189469 749189501
    0x5060307050702180402150c010e0607080a0f02030408090d020d08040306140c0309100b1314160f050301030206130b070c051c020a290c0c010e0103090206072a0303030f 74
    0x30a01780c0019540311420380c47c140320340300000f521202d8100e0a400002152000e81c0680344c252030804806400540111800c4050074940070342011100602d10030f99000310341014150342014041c00612030038903109903059a00003180c030302c10400520b9500007800a984108804140300d03003c588e030140d030000c0c0600540c000b034109200f084141600080c1c1903401e08103041e40070518020410105400202c903410030100c1030f00300081d03141c00a0340348680e903004520018050700940000d00086540c2400c4505002c005034040004102514245001c4d0491101c103000781c0300c00583e1090107482a0b40405403c45002240120030000d40c9004001780c440100c82a500605809050380002c006c01094012138018403028689020520000c01c0a000d0380d24150030095070701c482000884d40d031000285034070390002c2d020300d0001070703c0d500c0303070154040c0140c0c0644803a0400035179a40744504200d1001041402805688001c000325071010080c00044d40251400a1000340c07200c06201511409204e51002c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 749191969 1250 749190719 749190721
    0x6030b0a020906090d26071407050108010603050601260403090b1c02181c05070501090e0a020c011e2307020606060d0b0a030c0501021c23040506030705070218 70
    0x6501c400f021200013080444e403140b1000c0e200c2c605a080d0002c4501c0142000004081c52401c078460760340144180e80c05001000701100b00100102d948004501440c1d001802c00401000304070300a800c5550003041c14104a00303921401c84268000e18100d030785401422110409000a05411850040240c4401c122243c6022482e0001205020501d0007407158a0750019050407200001d1030700e424101c07030080c0002352187c114049150030710481301098980f402140000561580118002d00484001d035214048558988002c2c100079080740200c04401c0d500c500100006035003032803104204100c01a400110701ca0307001c200782c2c03108802c940c19240c00d0700041c1c28416500c0e000104258032440c100c842996030f0791207440840103001e842407500d4200e10820008010020000420401d4500070b0b402c0700c0c0031000f5040c00615009034000d400000c00d40005550418054900030414094900d992403440d16a8410104025500484240c40091804aa0001185440104640c0c0080c10303038003400c02 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 749193219 1250 749191969 749191987
    0xb25090e10150507020a05060301090225030f0c0302031b030c1902030604110109030b0a020703030e030a0c080f120906040204060609030305030609041a0f0a0e01091505070302040b0d06030b0a02 85
    0xc02030107190ba03034052090100f00d80b011540ca2690920142c0320141c041c54680d40d64145800194004c0c2c1807400c00441400300c0c4081c082031203980c000d4210781590712001c0080c0740000540c0d002441c00c130300750118003003005000844085c0200c406c00082000e4029607032058142942400c000d0070040d9110021001c6500740b001d43c4d400684241c020707030440741210b0710300d030808010b07524843c44c3e910007001c90910508109501d507156020b8000e90f80603490500080d03020040c5282c80c0d100c0c0400362000324a1600041002c111200c01030103808100e0740a013460300e0701450008118440c221060040380e805507013000110300705401520000d041c141007546001c0d0845d82c014241c0c3c08000d11450051801900140078802421441c22144944000c40b0b40c40d810654841004007108443c900710803030030065188800e01c3e05120760005c0c180c001510881072050340d076030080a05005804002019024070002c4ad246543e040100f1500200c0303840025100e182d85040307018004000c00b00400b091040c094055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 749194469 1250 749193219 749193239
    0xa0f150503120903120f09030a080316082202041107060509210f030405010618020304171804050c0d14090f03030f01050d02150f0c0f0c010c0b25090e10 67
    0x209002c80486140c0c40d121442004086c83c000c2014460f4540700e0648541c042c484118010350260550078825041d40c803010030141c0b00c01e6410784011249902c85502111820000c8654a07084c6100034004150040354880900c001e80082e0820b40b600b6540b50148081c04d58100700d06000300c6011540301080912500c46042175018500d41c05d0150000000000e003003100c00e62046018001e80b0310303210b4801c40e007038200100035041201c0c00c031080307042408050b60600c46402500d60360111702d044114103444010500000d490043c0245980203000d000c2441d9a000d54041c0041c000c0c41c52111500c1b9141c01c03038055280050040342c00d903036504108103009083c5030301108541598001d440d0256000b01610224100f0100d4003042c0254520200d000600c0716803100050000a000f14202c8210b06002161113031540c403008030160125545140c50000034991140039581b2480c030074123100e40d90040c058900c5a074410400076100061000c0300c2070000c65210f00b10144c01c0450050207640342414035003050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 749195719 1250 749194469 749194483
    0x90d08060d0218181501180b0609060f0405090106033908090a060507080a0f0b0f040b06070f0339031805030f160602160e0a0f150503120903 62
    0x10702c1d58248001a00582c4c0101c8068841a00c400446030103801101d5442c035200d07828010048003442d0541304038040706041c040d09001541c01000300d072510540c8400c0201590165011245682d001c0c4000030b00380e0758600405009180c25200460b90300444d420848141c4610307400441d5506080b04813000403404c0c410f4860040e2881d003446080c03612010030861408040304c3e00100303113504041c03c002d94140c3c85009640079070120402403007900c0010b07402209448123203641907045292034a5002083c5001d82044a9503c0b002d0b02ca14a8201c05480d04030308076514080030780108844241100c43d031007407010b0207160442c86048082c0e0404a10f000780e10354010400380501000320105041d01c4104160400c100100b0000381240d0302c0c50352001115842d2442d4440b104410082c1714800121035002041103885008442d5004080790308082e02c443c01d459002e0300001820355103c003000b5400185211341031004520740382e0048614503140401d45040c814107000c80c410a010300605049450018050f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 749196969 1250 749195719 749195749
    0x150509060a0b0414121b09070f051204020a080f070e0f0105010507030c02040f1409100204080304150e15090f01020102090d02210601031b0e04021003180b090d08060d02 74
    0x141144008013000400038060940c4041c45401507540c0c01080c0b86450b80340ca4420b17282030383e140300d45507035030342058454807072500c040b0022920403c6428800c40c05074452581c01403004040284a5850703120840c40c08400303090000b0564002c940c144060828116501e9102020f494210300541c10800000c6c41801080c00050500c0741c1c500d200c400310756468128410307030840c0010400103460112038001e100f10066914210600684681c0181201c1c0c0c2d00845055508000c004e6140503c1c0c0580071358281c01040c00e0504100720700714218580c1d91134401102461201714185900c61101c0f1040041601d09244550b040d684100180030702c1d510f5410141c64580d804850440408840540341014104000c5112040d030290500100401884c0d03400d100c690542d403d942c80000703884200e0390302008400c7c0c4010394000202d4240c21030b814466044182d24200c5a03020000c0c107901d41e51200141501901c8001c007e030414403001c510160700010305940721030116404080e030080c640210310354111070146 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 749198219 1250 749196969 749196989
    0x706021216081608030705040302150309120a2102030916030c09020d110307020d080a11031810110406141201030f08190302030708251d04150509060a0b04 68
    0x10003000c40e00c0c610780103c0c0c019040651543d5034502540020f2081e030150008074450306003c45c18080098880c404c5d0ba00c038000d804001d10380c000810443c002d541d04510102c00403c4001e280010000710141611501800d15a501580b607051040355282840d280500c200b000401d500300030000f02d00c0241000c0119000400e006035951440e60480340680641c3c00d0001c10428000180250030364002464081030150b96225442a25040f02c000c0545000d00c1c04811280c105001040c91081d4020000780c400c0052022a9000050000c121066412400c001c0c0c000000c0072030704100c0030b50030030920044056000046403038021a801d18200b07140c010b010191a20701c00035a0f290401c03000c01c00704d486c84620700c0040c40d242c6030003240040c088c0d03004031050720002d51401c0106400344a03102c0741d0007407246580d20403080315004e0201103400700800350710700e06030707451010381100691514800c40c2d9040c0581c07498480010b08160501c101c014000d020f0902134005040100400401c1e68142c07004d654070410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 749199469 1250 749198219 749198227
    0x12020604150509031e040f0e190507260106030f0612060207020d08270a0608070804021c03020106080f120f09040b041802010e040b01051204020a0314070602121608 72
    0x310503255018a4400d20301a00413020b40c5c0407a181454041c1044440701e0301d01c002c400f5102d04486090513002c0e90200240318110900d44140081904400d034418a04d240c41e0301c980c00e031807844035418400c400000904c42003407001444840e925004065207104202d03024040c007403420200b0890030170500005807006038045041421580c4080001c0d8400b40c020750642d40382c0c0d00c00000402c5280c040160f80104c1400e400300c43c4110b0501c40c0180040300d03501e0325071807150342d40e14034203940018006104a901070400b60300d030b8401034029546071500320f01a60000424a04041c400f0b444d02c00d90700340e0380d03015a03c44082000091512012a00900d0150548580314081350000c10b020306004051990300c07606021891285499641c03000c25468003d0781d507895008080c0c402e00003156246036540380082c40400101c0d210420300d80850303070807603c041d04443d80d82d5665151070359035003440c00e240351a035080502c0401815034100300d02c0035031140c07110407240381820b401e055100d92011480300a0601038080703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 749200719 1250 749199469 749199481
    0x10f050306010e130f05160f0201061a0903120409021b01090203030f0c070e04080d0b09010f1e1a090306100e3702130e090303040b220f120206041505 66
    0x14000705c1d080c2864050501c45410941c00710318409100030510400107020260034031f101c610501440c000c86e070001c000100e1014030180c0c8168217510101440382c0621070001c9030f004000c4448010801450b0a440c0140c03a4804280e0f06c10030071001e44040d10030b80c1c2c100030185001d42d40110403200c0006c0c0b07107000c0341e6071284d01081050418215500034004192840308220034002590000c05800440010800684106904210a0800130f0159844d00e030850030081c030441070710004408001803481415800342d40d40e001c540181d128000610100000081410300c5c45040410000e90416002c80c001c040e1242004030380890304100502000d0740d01411011902014841844e0003070139007014852051066417082c041c4065801301c03170041c1c0c070401c44400000e000d03619a1401409015014051482d5440d540c07901416107801400105100b00a00d00000c01424400011100d10344520300024440d07403142040c8628002c04030b511429908103608110024102c1c010f40142d210b01c1500000d0030703448a0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 749201969 1250 749200719 749200721
    0x9012702091e030a0f03170708100b0903070305030424020a240605060d0e160311040b1503190f0225110d0b060a05031501060c1a0a02030402010f050306010e13 70
    0x4c144041c0405220907442e406056103e08240c2c1e06940c14030804000c0d48451350100c0f580c0c80c040300d18070407010800704140600e0842a009183d5407a006085a580380e403a030310f609003554840e41c040200d60356201484168040700c03400f056071184860020b0043c5100a4540f0314205171a0308607543c0b22107000303200d102d440030030342c2c406400340c40c01503c00b503150f10440d40d008005155070900d203007030b52260204aa8070400e82e09504401d40f5440104554140f4081c010302002c0c000149200c4e07840300c12481d9807202030b1401d03000745108054000290920912020300c140488811140000101e401044055040c503140d0505c0303010000c0300420104d80c901581010511400c00c03241c002d41c0140f02e4417000301070150340d800f120f0090b1401c49041110b05e0f5204201640d03490070801107441d02070484010000f1030301404612441500400022030303503c00d035409500071100f0803120410184d50200500040d564090798401e41c11050b41402c0d486e40c07c12200180c080c200c1c1c80c07401da210350310800350810742c030442d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 749203219 1250 749201969 749201983
    0x1e04030b07021b0a062304090507121b140d20071a27160f0602060a0b0a05100201020d05040302060906090a15110909012702091e03 58
    0x1000c903015900344800002d4550003601070b85182214800401d901c6480e2030344094013100c40d161200208440c0c0030600b107642051034107030501e80000a0000141480850050390322950403030781d403103084911403070300c2c00200d0729400000c01c03400e55405040d40c046904540d03d83e40743c0342ca0030411502c4000e02ca59a001a10300a81e65446502c01141800915174152024048062040310714034100343c0003c1d18540b440e041114074503005031001c107540e12490040246c030074030300580c4401ea6801c0e210009841240da9590350003070a4410400e0010003010341d0501c01c80d074102e0072060b002c0c09070110410002d0845c1c2800d01540f4818040c072200544401d000754112040704135042e80030301c0b041c0740a0030080d450f010119484201c031b010340350000f1582e032400300328603102582c40030007400e89011042107170700200b020307100421039141d042000000b0759847c80d800358020300d8121300c2c42c0c90b144101132500c120b101100b804181070038010b11644040d070f9074113090500d040b140c040040d1510f064030400286014a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 749204469 1250 749203219 749203223
    0x5010e030a0c090e0c04090b0c161a07030c1827060e04030206070c0302030d1104031b09110a0c260f0405040513020f100315140406050301020c031e0403 67
    0x703910a000a460049a000020541300c0801139074120b400e098103110a0328459140109244000e0000a8041010001030982c17021041c030f0310702103000791380e841a146064079810600c4a120344c408000820b40c2c036006848038410079182c5840c0349406031540f040390352528041c03685000344295207003400305105515401c515440d00d00610041d640d03065110211001900c0940050007000c0008138528012600c0b126120751540c001c600e4481c2031400c4c0c80003494010b04103e01818200800004a0800204903014803050401c1c2d41c40c0074a4030840c1030031500214904440000140000032107560091040ca41064000003900726803410101d5010060b4085580141d4030500800d40c00b80c0c00c0b6091010b4020b40320140c07010070807070301ca61341c0300d0a5149000d0802035011035031201220250804845d06c0010201505000c201414499060f201a40840e0040b248030070480000c82007500c2c2c00e000703003001000c0c240c0c02145441e040014450b2a44501d0a44030041c1d0030441804c520000d9050880d8020740e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 749205719 1250 749204469 749204483
    0x70311120403180f0510080f0f07020a0f050f06010509060a06030213050301290607021003020702010e0a06170606032203020c030118031205070f0c06090c0621020f0405010e030a 78
    0x4c0d11805550035a03d01e84c041d1303a0084203048200c29425015541107401968010700d40b00a65641c0c44007003032050b000078561400c50041000c800001051240b00e107542c580700301c2c094201341a440d02e51502c1d00005902c90b502c103841031014000140c0b03d00c0d85240549066140250b55514607250403c41440c0c0c0d640429050341c0703001001c030400c0a1144003200d01800154005912509540411641d4010f44001a40c004040b20114903034038043d41c020610b03980b060400581c1510010001100c0218591112000c41d10174001c60050103900d00d1107982c00003040710f1482c11800c040c215a144161492403015406007a110f011041c58001c10104d095508020024002c1042404544828000000c5d00714007084d103084042c002d10110f8022135200710481d642c2c071918450700c050100c40b40d08201c0b80541e0441d83d10700f0024007040404103002c000c0c180075201c11101c261301402d60078891441c00b00044003e0b02c14401c042110382c40c142194120b48003403920001c6413042c40c000a0524001850082c019 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 749206969 1250 749205719 749205767
    0x90d05010b1f09060801030336080105092a040525120e0c010c0602090118030c060807300f181101030c02031c06030210050c0105070311120403 63
    0x20000302c01c803180b15200e05075140048960756240c01d07038904100f80401000b0030a0000740c0e82c0c0840c2c0110380103c001e80700c54102e81c0004a070002e08502c0c20740b41e03001000c15035103032420840142070401040c412146401c0c0c101411680301520040e03110101d040c030f544950380300c101040c1d0640b508140f81130600c281070840e88804c4a6490060181c0c2015154010352078248020a0100a8081045002601d060b100c0480c10702040c1d039104001c0d80b0410301d80b81408121556050151883c14580f0f0145102c1c4e400380c00342c0e07401d0004c050a0050004c00000403c40d01c004017100300c500241402c0c07031154041c0d2103203400210340c100f80805008000780101c1c4481c03070082901e4800810b40421000103004091794032041300c910f40110292034100007044096401081184110480644c2c00344500d14000d4000400b42d44940c0040c5214a010064000007900402c28140040080c4202a00102c842c03e00300f03d958843d01150301640202c14051501c920004001800d040c090fa0001c456082c3d8044c5020364 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 749208219 1250 749206969 749206999
    0xb01030207051c0806011e110f01060303020307020f040603051002030a0b0423010602070b3103050a031d010804020d050c1203120c0c060415110a050405130b0105090d05010b 76
    0x240c031030443c0120010ba00c90020130055401800100b98840910881c1da1039118a2201038030404990000070b450b52040603184005c2d11701c28820340d00514440d5014694508075401081449070b404080c840c49140342040c01c00000781c001848203083c01e0900c07009a165a100c824a000510040001542140c00c1400b400d08480042103803018810507042e1b40c082c42c2e621114120703034a03862030195032000a0708100341041200c44210440c15844086482d80002c0303644074941201c400b0903401254141d1005018408040c0c01007138620295842040701d0300ba40702d0f0100024103945028001034003940f950b0b1007510610105100da6034002201030039a04018031b003c625643d03660b0142030303000c04400500020035542c80400003250746d06210000180000d460307a80343c0d240502d01c2c0d05400403a542d039031480d040d211201c502c003502000d840390b2141501c40e4500000c2c07104204051591a40781844c1c8071250715280e130010143c3c2c050740015500320315495507901d003403401007a03250308155104141d00d00c1001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 749209469 1250 749208219 749208253
    0x1018110d05062d04110c070308120705160b060105160308150d05070317190801090c020102070f06051b0309030903161802180d060c080105060901080a0b0103020705 72
    0x80220381c181c0d040c15801c0107860803a8071050791040341c48031060400b00303e92100d14164100394180008901c002c0d140060342e943d82440d107141a0b10440d00800080380034a00043d069210651084c041e0070030031325110312040c02481d840075542000f40410b2500c07002c20011f910541c00e0b01c1d008902031500c1c0308501000e080181000c882180c401c000035a4405a402c6c0d242408a880c3c5d0225900100a298042c11580c5080040c090100000d070420b106204010b5808082844101080440d4441d8141541000f1a1030f055801003140304040d6801003200740e0015038226000300a43d0380010002a00da100c0036020070000100b480208001711010060101006001c402030111031402c0f4100c602c20328080514003c2d0954a04c15051590090315400d2002813042d0020034000481c4074281e0001d504480001d90000c4d00b2040a136450f5aa8848005505800005280c0580012902d82c3d00300904040002c0c0080e4000b480d104145484402c0d0581d1a4001c0d01602c481303980c003405807680056402c8202c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 749210719 1250 749209469 749209471
    0x61308010c2c0f09070c15060e06130b0a060801091a03120a030603170304020a0b04050f240f07060605060708071b030503160b06091018110d05 63
    0x154865103044980d01d08280501c00c0b041c103080b41c2d03584800304807005079500d040c0054044159900b02002d003038810102e54500002d103126200c07136240e0b40e07403400103400c0030384021390400790821203a480c2103001e0122068941c18291300000c11100c2c07001ea198205003034400382120501068118029001c00705400d500b050446040e140800810404902c1050420040040c0703452034a0b0181c0181c0140106615600300600302c0040d9410086209640da80d03900d00050103155110600307032300c040203000443ca40b0881904c0186066440303981428202070018030fa1081c01c031900c500c03401704034880500c004000880750b80d40e0a1004011911185940c0d201105030348112000c65035145005000718083c5002400c0e1403c0c0d42d005480c440c2000465501c003071014001100c0400302d02000c244c00800540100000e100320002c1c07841e80b031452442483c0015100001400540c42165041c0411441e0300a00301d0100840305035001402c45d514101c54050001d081742ca0390f40d40303200f00000e13010403600c00c0c6070070032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 749211969 1250 749210719 749210729
    0x103023c010e0d0804030807170f07020118060e0f030a0b0a050103120f0e0103111b1e0c152110150f0c1103010f05040f0218042d020613 60
    0x80c001d401d03039501040326050350600001c060202c140001d10208801f8405007c800f171040f2a1064446941c04082550f0307000300001100d0720390005500821546c2c080e8200f004641031340340c480c42c5241045409040100d0110700140101320381800c3c00115602004400c46080d00f1100a03001400c003000300c100500824042500c04040c50079210072250711980042d200b80300c0c95034a1a0745400024011405080082d040001401c0c081c0280c400c2400d80210700e14103514100000d185040f110745190742d00192260b40c00020390071081282115445040b01d001342c0c0f9002c4002c82d690340300800034200e491103000403100200c1280b9010007608480c07980b0030030242ca03240c10b0b4803440304e085000100c07001417001d0048000260450a036000080b407401c00458480c0c0001d002103a043c01d20390900c0211794080704e05503141c0328090521800e604017003000850070516010421518078150300c4611070000104111100c00d0341600d0022050351541070442410350b8000e0110b030380c541d147c101c0007a41049074062 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 749213219 1250 749211969 749211977
    0x150909011205070f0b1e0d02160606080309060f0904021b03131a1e0c0d031d030307021203060307030b010e04030e0609010207060c0203010b0913050708150103023c01 73
    0x3c08124100901c3c0d00004035802c691600d071070100300c01c03509040e2840c00c0407441038509080c400f08040c010300b40080c2030b03001060858548204281c0c10100144c42d01907004030966001000058980c0c3c880c041101d811646a9011340e60354860100031500a10401010340c003070390354003101c0a00d49070001c001001442008442c240c10961913440301000e81d22080003051540100704800c40d007a404840780c0d80c074001c40f171002c0c0c20b04040070814640d0911507038035585800282e94000300700002e642e81000e0a040c0034610019421342c5450030000c0e5503054103103003902890001000250542e5000c01c04007000e1584400380741c200d56900d00007079018103026141100840c43c0081504d00900b8400c0c2511307400d0405034020130344189410416a01d22440300303005d0b030b015521003902c041e00b41c9609500ba800381208400001080400381132490505c50990001000354111008072010203158001c52415650110380b0f02c40e840004030100e00010040101410740041d2225240c2c02c82412585140901c06007070725 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 749214469 1250 749213219 749213233
    0x21815040b1e03070312030c090b070c030807150615030c23071103160303140306011e020a0605070504080d090806040803060102100e01050a060909050705150909011205 74
    0x420055480c80d039029a0441454076504840030b48071030561040340d60140a461400c0c0d120f48519030704204100703091001c207480c0c910f1040e0955006d00ca080c0180884c10720942010001e13030310f92020461500c40900000008100c140a01c08100300107010f01e094448100f1111b990f40c804441d80d542c500c040b04000c02e04c1c050b003044200e03008079003210000030f03001c8103107191150b2940140f040d50130401050f504a058802d9048a50710b00700301025010314210001031646285150052100301458005540404284141701c46079070883c09c00804114448002d40d085101c50300100e28203000d020f070260110341130005008017142c09ca070040040e114004251004410f0700700042c4c4035200a0310032416640c0c07000c8005000700d250311005d984c0050052040e2201d6580c001c0403030381610a4030b501e0000c180d5480c001e00c0180c0841e0b2041c41c00400001d43c090104030f0f955121103440719454460315004159020910300044040803c98820b214000c0000a203540c480c182d401001135210011075191280398 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 749215719 1250 749214469 749214511
    0x120f0b0609091f090c0308030a0e070b0406030207081c0501050906010306030f020f190f0927060902060f0403060203100503033a05040b150a06020c010311070218 71
    0x25000e54825100180102803000e426049506411048440310f035515946000c000c0010b0000d00c010b500642c000c03900320340c580c18525441c40c21140c850b0003000082e400b0a10400919031810140e4048510b58203005845e039626017003600d1144940504820305008480c41d074043c540450380f05034183d80b0309890303c00a50785e540005404560140c00082d111201014145d0018902524801c20040b0007034450507140c188035019065a040a0b0000000745620181c2440486020b10840058051261002c2c00c400a122440c0348a4920800064203072510b4207000002d645558080b602131086280205644998070f0070517034009d4000b550844d1100450460006003403400000b940c00424445c1c00794500c011481200f0f1000310448554100d5014154014003208601440707010b02c2140512811300b1949010040c850013025650a03140c8a2640507509001044e400151100507000c2800c00080c50304540c641e8040394000e60200a43c4003062217140500000040c1c412400f90b5001c06804110a48070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 749216969 1250 749215719 749215729
    0x2a03070309081614030709181208060a051e1509010329060309010603021509010f0f050409020d020714010b15070206030c07060e010f0e070504091502070c120f0b06 72
    0x10300c141c0300c2510f00e00020702000f400d411102112140090456000a503164507001c1691504040c4480c00c1c2907101c0b00f40306102c1c42002d01c1002c41002d140a00e010f00e000c2c4001444000700340541d5004491031070001a5807601d4005403c00c1c043c00500e074070007040b40d81c01c071500c0550244010714002130074143c207a404103d07103010100300181313070108400740046014140a102d070001425450699201c06000016886240d010940e40440d0342295070340e001e07008005400260f00c5100403040005001c01c501d82950300000f44c0e4140e811030b00d40980c2c4d4040ac0c10009020740600d003c041c00e81100a0000f6040143c154400d1803c950213a0302107008601810043c4a0b40c019a48060b400000800000d045842c0c0ba00040c0790952040400195182020865070308440840c00100c1c12a96141e400617a01141002202c00801c1c04540c180203034205540c0d817005607007440f5524114a6000f05000c070411424a10b004064507210110342503d61050900900315809654281c0e00000e200c1c0c04216903041c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 749218219 1250 749216969 749216983
    0x1508070e0c0d0b1318170a0f0f020f0609010c0311030903041401090e04050a0507051017060d02030a0303020423240409090312050702030c0a082a0307030908 69
    0x110000c058203120b03514203100c01900142d40c607207a01207103c0008600d0507489100c0e40c40400d07081c1e410103840c6445494507002800300000d1340041c0c200d0a02650061581c0040c4207400e54605151142e024199000264500020406841918010740041210700304055119019100d0159001d201c819050b42210b02c1c203120995021856400c1044180410751a003035690845c40011f141540340303207a44c0d803100503520802b66022a0940c001c2114802070040c10040748020780003c032074149200302408801781c03022880c0300800e04912545400910a5542c0e0902c8045880d0041e058403411196490014001c1d40b080c050b0414071401d1840c10501c803882ca5602038500000034141410000175580485c8801040024800c0c4080c820440420b46c5800742c050480914820380341c45d134509901d180c50f0404c0d2070300204001c04660044c0610110b10000080c03000700c540c5c000142d5aa80c18007060228500040c3c0c1c41d1400701d14114480340c9008010000040001a000b41d485400180d2100005902e07601 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 749219469 1250 749218219 749218231
    0x1012050a030804030216080a0c0501052b20032a07240f06060201060b0304050304060f0c0f140c01091406131203080121020303121305011508070e 64
    0x1000040910010740955611500280217004840e08241c01210307404441e04075400c0400d0681102100034100007103002440003030882402e140e810140300d1003038042504101d950815044440c000150441d44469200c0a10000c4000281c803031060000240050343d441034520100001301d0050203540b003811014031120099540c036150345490407a44880701d4003084036048005c80030006080c41030901d80c1d40700f122038030301c0341c980e01090762454981301a0071640e60380c1c0490600340c0c0400c100700004001008a805079105070170902c00591b0000c0c003c403a814600000184100c3d846a00c18082c0724409404801c505c030000102c4450240311380045800c260188a40c03034000b9a022122210392824501407c0b800306010580c0906581c0c841000d9183d9401c14004d50103d401e6100500002810000c1c03034200964407402098881101c0e4042583c0307110f0021244c07402c50880c4003141240d40c10305503084060b41c01c00000e00c08180c000b41500030307500061007a10380d1849000030000c1c080142090403480381c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 749220719 1250 749219469 749219473
    0x191103160819032f071e0e040c03031103041d0414010b090a180614060901050a031109060402040306020d0606080a06051e060712120612050a030309080c070e101205 72
    0x14890001050b0442d404c8580020f03000c1d070210300c00c0e200541003188900420640c4441501c440d254a990030640000380c202c6503410322501c0402c4042841c104680013204d0340f61401d010207900e0780301310605600850300704510515001406082d8a040411502d0140340141da00308580200c0320140303400c039071b1030047c8a034000842d40b00181c4820016805201d0301c8203901c20360400f1021507980c030b10817645001c1051880c82c00c0c0c6001d000d0641020700c00c1501408041d83c0b000001c6045031104140034507150f51b85807149400c60300188858031590183c0e4021544081c041d52034404041c0002c02900542c01258000741580d4002000d08009015200442c0c01c098000d550344c10880340d02e0300160f040c120107150481070410045c8001074038140058000c4207190741e1007001c0750a401c0c00c1000d1700c4484d40800001c42c010000c1c00d000c9400452282074065140c200010b02c28803c0c900040680a4050444010301034011300042c0c0c40600b16005209060300c2205004194031544003401d404005000500310f9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 749221969 1250 749220719 749220737
    0x30b100e0907020f12070b01060903020603191d0303091b0f040f090203070e0124140318030307030f0b09071e110a110118060219110316081903 63
    0x1420701403101600500c180c4140c40240c1c1e4007043c6203180524100464108071800540402408204035040d4050030303580ca001e02e4003902d10780002d1030500025001c00e0a940c0e01d800176016070501da500860008803081424410300d144660002d03120b81044401b00518021501003002112484480400c5c00c035000303010703412a018220601c4001c0042c0e2540b0081e695594a030720000d80e80c10015100181040b007031052441d810f100c1c100c055002c03100d5000e584c00114003440c1203550340161840409040803a0400c1c0c499407a01801c400032070968800c00c050340400800e00c84d002d58117400119245a90389014044400e2a505104045100b100c00600085003040ca130820b041441030044020f541d240f07459003903080741d181124204648554101d880700d0442c8111582541c001c0c0c804040c08070a4401e480c1e000c0d2902c040a511810003040d540d24018030900c0b400100501c0740440090018051b086038019241c030280030382442c44e5809010071610503ca00303111113007404507940c030b85580c1c07682e200340b10b17 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 749223219 1250 749221969 749221997
    0x8190c060e0a1e030507060305070e0909030d050103060605122103131e1109151002070f090e1c020a1b0504050405060a050718030b0c040509011203030b10 68
    0x1040010180003a4030050b541c4000032144116140058030101e039018420f019482c6180ca28908900c40d88a482810b0821040240407030f002000d09000319815244100d180d581d150b0051300b1032041980c02181c0901d401700102c244202540640f041c4c900549141d9030000103030701000c0ea248802013100c02d801d01c4801c5601d1003444500091500f00114103210b080921903030b941e18224503d0000348003550003100310483d0520090200f48001000b0969030451075050030624000582c011171100c5002c0c1d400f1a1507407140c94420402c100084c200d8240120440c0e8960a07244090401c2c52101441881a221036450000d482224480c0021898004000102c441c1e614000000007000460788a0212218000303100c2d122070041c184a54441c1000e0400740c41d003e6081012280040d001d00100f0035290721040d81003605e41000c2d81500d8004480c00c00c0340d07a4815034190684500d400054000c43d00000000f400903070301070002043c0b4071036103050000d10310050901c0f0808241c15018400160703140c060081c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 749224469 1250 749223219 749223227
    0xf0216090c030e03040305060406110f091005090a14090c0a050301092d020a080121020d050f0a050a0b01060815040f0b03030a180509010b0a0503090705090a050108190c06 75
    0x141e054480c0c02c02049414102402c61300b19045907209031074541020b41000100003003403040820103130403004040c0c01d10051991000490040b4030900740903090f00c5550181050150b82139624141d0024010b10b030684c0c48100f40443c0c0c40000c1c80880c00780600101182500031060700b0394404480c26030340d260a680c6010003842c0581500201e469040c40262031603041a03071004140c00320b0f000050000759503840d0214000f40b01e214160320607640c50061002c45034040085e54001d880c2240c0440d848001c080301410001c0c03c10040b40445002807103440706074410070001003041c9403c07d0190030180901da90700d66080d203118404403403103a0301d021802e0000c6510b15041c0d001d100c0040f02c50300c0024041002c2000f091559004013140b10104508510b40c0744694000d20207880030300410b4811007050f51504003840c03000c1c05083d05200521001000155000404000789401071800416500d0281401c1c42604009c0800b802440341d140211003968902c0d40c41e44800021080d4440b141035a03040ca000022a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 749225719 1250 749224469 749224481
    0x110c0604031b060501230f0108061504090c0e030f06070f05030a0905152a030c030402030f060403200d020606130f020403060e0c090c03060d0f050303040b070f021609 73
    0xa521021102c6080040f03403181c82001d000c1c2020900135a020542c41c1e030090901c07605038080318420a80f6994100440c0d900c0314005410070b009842e10307000704900842c1c3d00d00d40c2c0129080808002d1404e4582c900ca240c0c4000d040102d228250b040c1c545202c0048407058175032a04890100100300101249114103121300700035540a14807480014184489990b51800c00019141c07181c002c4602e5410f1011071451400c0c1031382104c0d6a40c00248480283d03c50003c0d890100900900c4001d802100240a5450a102d08007041044070b098841d40e18080c94050103142088c02c02d8004105600e0040d0400782002542890030085070b0002d05503030b603c07141000100c460405072400a640c542640c03051110140c0040c102641c42101c000c100c102c4509c82181c0380c1030b10b031481a8401d041c05020f0000c6421010200e03074005800741c50200104107a4100301800c1c450f085801412407000104100500860020b142e01641c0c450360b5400b01c1c0c9284270400c0b6a11044105c045203400c032011020402c030031fa16401a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 749226969 1250 749225719 749225747
    0xc110a0b0402041103040302010507081e06191220060703020c040f021605070320011209020105090a060503090732040e070b130506031006030b010c06050903040306110c060403 77
    0x410604e020f010310040741e40007aa81280036079116414094156004400e40e9800f1a400344403d10201c0d110308091000100545618010340c007451a000c00c4c0071182205002501c9901840d10003c803d600c0c20506c80101d40c447c008451134007030440c0e1094600281120040c94040c1d0003031903404040b00403c4000e200c18003008010903820442c50000c03da520348007901841c0201d018210480c40c0d810a0b40400c6911000b0041d0b843c207440c8405060b0b03070400088207002a045030300282c2104140b0058078540b00f14a03116610105540001410f658004c0086101e0080c0f0001c2c0e40940365500c017080102500c00c3d08090740c040c0c0840d040300c244900010103921040f0000c0010406000042034682858101e400c1030140101c0060042c0586d040d08400300010141510500e1030340c0307040110b6170210103590043c20205610f505003e07041d80c0c45401800b000b5508034a04101508015041da41d1b40d502600c001c641050600d801c1183d0300c0140d0003950480300024000d0051a91a9a4100c07100b82003c010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 749228219 1250 749226969 749226971
    0x13090b0d0c090f0f020930120a0e0406030206091c06020d0902190e010302130b15042d1a0705030c010213080c031e0c19090c110a0b040204 61
    0x80c0411100222a00104181440003990074440c681e03001c16502c40c0d0010100c50350040040305402d0b142e04441d041140c0341c6510940c0c0181c80190465100306c1c2c44030100800d803040244203840030400000902040c680f030b03158040c411031000c081c00280d61842c4006580400240031046881c103015100d51400b0210303120040714920075982e00d40803031b00809100e18156603522507107403c601b4040341c411890342d80481e420400741c2c5000154541c3e0710301400000d00841a86603140110120f40c2c01c419017810b401000300403810400120340c4280c1c3c003e0b2140f24401c4400382030811405600041501000010030100e00c002d41c107101d2081c6a0130792603011081e03008010850312010070401e0001c2e14000c40001e001680e0b8032b40f001c03107000701805240c200240c19040380d001c003401070768001004211500c060310000c004041c518102401c0440d80c00c600e0f80c200308030400c4080c207803100c606240140c41c040c01c002c0108040103907044500741214000c410103507010500600c04101d4840c43c49900c5440180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 749229469 1250 749228219 749228239
    0x7260109030816020c13020406111506040902131d011116080901141b0c0901080c0f0f0a0b0304060c030b030d080c13090c0f03020313110310020318060a0213090b 71
    0x102041b40e410140c001e6000c00740e0301050900c010341e84210458100e407441d0000f440032090300803e0013076100001d40100d02c40c03030b5540380f00000c640342c40c4000c5c0311124040d071003006a0403501201c50000d603200b04002c03010794032f044001264006014103480c1140c41140080c1000011540c6940c03460f40001c080c3c80c140182c4a0548076071803016001004c1001d10000c0c245007025404402c18504180d403201540b040c8102001841b017984c0018110400712012a003450500c1000c001040b01c204180c0e03085508900710703550202e01001204010b42c0914072032402000000e600c40011030840d5001582da6a040d008440050340310740c40b440b9541e4020707804071141890035803000c41d41d280c0b400e01c40d4801090503458003001d49142d81c004658145190311030405528510b4000c808030411002d06030010039000c0c803d40ca805054400b08440c102c2c8000c8014119543e06010101c1c074000e22040c00004240d00c215030000345080e2250082e0b4a80c45030f86c60b5501c0180b0304049940c005401d80074607503a04405005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 749230719 1250 749229469 749229493
    0xe04230a0609060821160308130203101e110405123a080402151b01020318120c121b0a060e2104120201050c0726010903081602 56
    0x440348034004d100060041141d904801c0408054900041c020010303500e00740140f080c2d4031490500c89900550500c2c00c0c1c2603555a48080030b4120341c145c0c0011790540b10340e4855128410842c3d2114081d0200e101d22802509050441803068a101c4604e101c61300609100402403400d04501c079144500708a001e40703070390000515145060140034000d05496858100182001d904004818800607010f850848442e1905070041000000700181d0219020700009038403c0b50304581c45d8040000511038002d56503800c2181060840e0341488401ca611401841c9080c504500c100084818000c40b42c0051711080110b840b001074683c20002c00401c647d4600820b24240710010f011601070303240320307100000d1120003100030fa5142c00e110903444140c154005014078140b54415080e2811030716540302401c00003415100484990007030003490b00d0107200700c1d003021840c100540d40e19800128400202e002c0c40d8004a2410b0a07560303c080064081052000442c0300803c82c0001083e0440f200d004440041000c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 749231969 1250 749230719 749230721
    0xf0102210702010809010e1b12030318010e0d1b110306130c060e0f060f090d05060103031b0b0402240406050d050105030d05181f0c030e04230a0609 65
    0x906980e80e90404001000002c540e004800980c000400000801428080150081e50750142d10201d1001030070400503040b441e550060201082e11001c3e0559849081000007002000c1038014404031039401c010a01054031320009e4a560303280c0746075451780035000904103410701c000c00030b840950380701c041000c001142ea201044a1030185840b10140200e003016428a0300c4040d40c9900301c00100414030a101d051950346610000c410002280d90f140e0b5400c20036540c5000e84664102c0b5504200c051640c107041c050040f03103282c103c82c000d4660001031120030a2410045a40901c0149520020340101c1c001d801d0420a000741031206100500109612940d0240240c001c2d90000b4005400011625910000343c00380ea40100320641c018600304135110809071940c0144d40326810036031480036005c401c99880c4000d540c000203142c000c0c40d501d64020306c40108605026101030b00401c4412200d403003035080511501f0001d446150000c0040c1c081851500c2d88680007400c8441f2107500c2d104041030003049 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 749233219 1250 749231969 749232013
    0x90308070305132001030f0c020d1d0a03050a0317010e0a09020a09110403030905060909011e090204090e1603050606010f0302091908061003110607050f010e060714040f03020f0102 79
    0x41c4110340c03032080e113420000605484018840f40d0304c2506142a20030030940004903145d1710103071800c0000c408920039501036010b0180b84501988a080356000006000003c03441c80005402551103141031003040080c640030a100f803040340c0840460b4400643c146003643e001000b114030051401840c150340d4a800e200307950075600b00c03402000000a04104054002612900030141611100c1c1044032090000b960940140316101781190003581c1000404c0e01c15030394402600b020081107448684a1141d100108410b0030080c0f2544922642815030303141c440d030540c04807a8000b00801550f9101401102d0800720110030006258082c400e031030682e92a142140b0580180380c4540c081079140140840c90000c0142c1040b0009840705ca060010502d5031010380205581650381c25650807052900e03503d01521410006490351078150f080209042c0803582d0781c040d040c0c03641c0d0341304412503420380d8141c188940d1141c11242c0b84400340030401414010740c20f02c610310050051340d07140703650303c00c1c8e1f28540a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 749234469 1250 749233219 749233253
    0x4031106090306040b3304020a200706080105190311012d0f110a060c1209030f02060106050906040509070908030301180c080403021e01021918080109030807030513 72
    0x1900408005110500c000306c19440403241c40090501085800c05940d184c0b100310301039014a4002810144460207040c8603a100f03030005901e511400340d040e84190711880280202c0d00060300031000054607103410700000d0303a410541c010740011146165100d40c1c803944107005207414040760801c4820100d0030721040010024150001c0100c0120051004003407020f03038400042071246017821403a1110001418101c156808140020818981c8006940445c142050003005a0801e000c9501301680002c90070940403040d000c030784040c1d0303d60030240c5150080102290b04480180410880e42c03030320300c802a40010340e50508006141d103c2500303d0941d0701c01d0304154041684812401249146407184240290340c92501d06413a003080c2d44e009454501031803d56640999904500910a0007981203540403040c2c1c00ca140300047e0b000c0c0300a0b02c0d58981c3e1500707400310a030078040016450010301030402200d03071650b40d080d113543d40c8490a8005120240031003c013040d00b00030450001d194641e26000180d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 749235719 1250 749234469 749234483
    0x2030303130c09020f090a08012c01140a14090f151503030703050c0c0108061305040303141e0105030a050d0f02010207200909120406050a02010207050618100b060403110609030604 79
    0x842080d06201800d020b507408103420740c1c9004c03602b20a914400f00f040003031410703c400c440383e0b510310f81c0b4200b03000d00408034403120101178070303820b0140b522003e83c043c810890846a444010b83d03640403600d62540740b080d920311803c0d00600344940403400b00c0211550b003d142000d0110915805101091460f000b221044010940000f00800d2036923040001c0d1a0707681e001d10301a8410700c0c0180110380901c1c10010800402900c50000c9020107019801000f50380342030100020440c940500802c05c000901c1d1081000340c0000030000c20f00f4200403035810203080e08000240482c05880c101102c041c1c2041701010215503080c0244400602042400c642e000049072050411248540800c084400050250340442d4450200c500100260300f058904a92050400546030034034114183c2c003a101c0e1404c024440d02502e005c21504405546008610010002c2195070042160038801c0071203d443c1c1ca41ea51290081c031081002a02c03c0c1e9400b00a01d0307016090034184403054001c245003070001c2d00e080f1800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 749236969 1250 749235719 749235727
    0x13030212070f15060f03110102010b300a2a0806010801270312050c090402131505072607061803020f0d0e040207050c09090a021c02030303130c09020f 66
    0x10143c1d201c184a40200c500700200071061400c0c850b04038607000d52100421901e182a03038900380740e0003944400043d000242c058041190b00c821002c000c5251410081d01d84c3da881c0b06504480c8400080b14445283e02c4103038400d0808032111050722010030107414440a62030101c020503010010321002d402880c1410000c20103079101895046400c1218000c0b5408040c25000640072941c01480c04e003850642032000650354564007510f0010b44100032a00b0f4100d8000901c0300102080034032407004a91041c440b0a03204810b86004680300c2c89000000b0300007240c0e134510001ca031a103c040100d038406004060516000c6c80e903275080181e4402003041410f01844825070802d058051080d40d521902d03a00c080d2200d980d004101070040a104072025004640c0400c048040220030020124100350007828840e040c903103500e4599541d814428128000d6100070311110843e01c0700144445070903401400f0714116a41c0780e10b10074000c41d10400603503e6003146000001c81c2040380c401072034450024404113641e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 749238219 1250 749236969 749236973
    0x40b07061d0723010c030305190903020615040501050303030a020c0c090702010b0f0111100509160e1b0901052502300c030a0201050c010f050f04050c030601050913030212070f 77
    0x72101c200d0070f400301c80814006001550380c0c40710f01103620580c1400c0006803616445024800c1c2070705940311140c4d01c0c0ca0005210103164001907280c0c401d500b03021901070300c200500c0621043c3c840a201f91509030f403040c0007086001030f85802824441803001304807000d456050001500655003940c5200241c0d540c1c1640d800b403410001d20400c0500802c0c00c0090540716050301076651110a441108066645c401c00301c2c1e500c00f42070080c503001c0301c80200c046800940b40d10311440f18010076030b01d4100381c4030900c21100300c030750b00c502c2a2401c09005864041c1001344544410015480d1f03000340c45031000c41300d10305400503911400700140312805101c10040902000d140d0301020300070340d55911015480034264001d02da400050080d643c99080c680b02d52511a104c4005000d8071108881070070440c20541000086140c0e1080c030b83c4554000c0d0220740c1803002020615403920428012181c0221500000807400d00c1160070b0044841e01c00e10485411800b03200351a82c42e030f0000c0b442290000c907c1c0401200f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 749239469 1250 749238219 749238239
    0x19050406021c090803160c020a0305010219030e0d0518041109030f0f06063001020a0f181a070204092901060c020108070504091e110f040b07061d07 65
    0xc1020741c8864100400c0c002d030344813100d680c000100908022611504840751310b43c450f110751041070ba4080d012401880d201d20b031a81c080d403c1100301000d80340382c0c8041190309038800c1c01940c0080700280060300681c1d04862088840b98030480504d03002009640c0080c405444510896090943c00307000c42e916014020201428010411503100c2c1560081a21040200021408640241003107800c800c0300200385a501c40040f03000d0708003020300c028201205403003810640041000e80135a640e4046400c268a4064a12000e092100c00103517120359420f024114502040825200680700c959080080f1580000c042d9822064111081c3d03c0c14440350b010741560304800007606c1c0380b04090344a05d40c180400144401d4100101904000130000442d0501c1d025008407000380c1003982c02404aa4805100111030643c1e243c1768050044c40c0204820f078207601c400640c1c1c8458101c104041c80d0616041410002d50480c88041e980c0381c2d0366843c00b0b911103816404c400c1c81c02c503000700504007807458004054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 749240719 1250 749239469 749239507
    0x162312060306130b0609040201110d0804150c051b01060504020c07050a080102040b220509040f03080f01061d060f0304031701060207060c23070602010218031605091905040602 77
    0x2c0020b401d442d200b01c0019003607204c40e56010006a4103240290703250300040b0344141100c4044580d034054454521860307035000700c1041c810b0b4052100c0d15003682c40b50503103800b103940050442d03000620901a840ca14201d84040c25141c00710700c0c0c0080b55180d21580000c007240e000f4040004664000390040041c1c0c00d299003600c0040032005c000710b061614203080d002041c821826180c020002103c1e100b8149140b14888002400307001d401098203182074501070441940710503003500030421403400100d60014500d101c5041c0d42d195564840e1020720421150b0b061150440803c2e44560140100507042c80e01002940c4200c1c003a40d84c2000325012000764107840003040c0c203c0300c2150841700c004c0c0308031504a80c0d8002d0b4070b0344c4070a04081618225980c200101c2031201254068051500c00041c00381e415000381400c090405c0910000f01b640d4800c240d5105030769011310808500e881c0041049103042502a80d102160880412480c1740c4119403004980084504990143c1c2c0800c0851046c0d020490075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 749241969 1250 749240719 749240731
    0xa0b0405010c0219080d08010303030b10020714120610063b03010b03010c02031903060f0b0c120d0903030c020a031409030a1a01090e06162312060306 66
    0x1451605040400081501107a07a80c06801400004494203445628049100043c03540e5421351b0062410100010030f1008280f00640010b401c100100056242080e458401000290020f00c02c041c545901c1d04501c00035100c40c241d100030030907108003e81005001151042d060344100300251420700d00301521940000300d80d240280c110001403000c0c180c4010003021120701800380c50a0352055080000e0240c006151180d807d03500b8011004942038001024003110304060802c000d00d40f41075481202100d145124418041007146020415141c1d500000c000b1045002c054960001840301b04e4500d075444804c00001c0d5555804494040c550b15100e1900341c0d0180b0310181c0352860440e107000740f05007010301d048940741d40005600000d580c0c007080382000c515030000c440f501c550001880b49202c1c5509200d0100840d060041c8441c50104c0410b40901c221400c075802144c0c1c610074101110814818800d0035015807000105070100c4650750041d218105200000d641546002c01c00c0c142085805005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 749243219 1250 749241969 749241989
    0xc01020f0f0c060711100206010524070605060a030c06080708160507030e041506050c010e030309031804060321030e010507091703070f20030a030c0308040201110f0c0a 74
    0x140d4030800d0800b02d018a000102181e00903112450741c00e100308421901000b640c0d001c1081c1450302c01d100d130082501d034101c1d003007120409051401001e2544c1800c2074031f1b00711400300b4410040030300083c1066002c20340186028000212044c0c41c0c0d079400060071043c2d0410f0011800803410800816070110b039440d0300220005e00d00754519141039000c2d284ac0070b41e0070024148000504c500c1a142c0fa00d60152081e9854410204551942d406028003194414090b03445d580d42840050190640e0010841e4000c000c03010065143c104000c0e002c0c8580035a401c0e01c958803903100d10000010403882c6610018000c00704100040344c42030140d0103000c95281441c0e04565074145010800441d4001100030203da0b58007015070300214142c05994158483c80500405118a0303803c0d11051128800d064030a406013950303100740040d1418101a5607154204008000640d40300b08400000c2c42100c1041c1c0091060520078001c00c411301405c1c0c02c014844a290b4015070219110101529001744154014110300903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 749244469 1250 749243219 749243233
    0x3010905070c0c05101202130305010605030c01020607110a0515070201200d0e0c0d050309010207080604080d090f0f080901020c09040209152701030227010303230c0c01020f 76
    0x744100302c00743c561140341d01ca06085107034a0901390280070303404550281810110766500301008200402000d500042e2190362030030502040074180000e001e0350402050b001441d507a69450b80483d11024401c034940e14a00603d20180009a8204451820700f89424020000b85c03900d183c00070300b116100e00c0710300203904800b007025400030000411104042040600864a0aa00c0700c100e840c0c5480880485d0b000001d1011400030710001002030102c2c12002d03800c1d1581f0300c0c3e507114100e5a801302031301c010345100401c00010895941d140d22a0440501c5180010048001c1d51590140382c00c151030241c541800c0002d6040031507a05004808007800100c48100990405801180449400a04801d460101000e0b10301d010703600c2c13107120400e44140b1354000c2c0041c54120b42845a0310f0342807200328010000404542468004490325501c01001d5810544983c1c1c03035900c086584c0d01e803601480342c892484104a400f01400503008250140000380282120301070180024a410850303141c281103508058 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 749245719 1250 749244469 749244473
    0x30a0b0d020d06020903071d060405100f0504020d090510150f030515040f021f03060522150b220504150911090618030d1b06020f09060f03010905070c 66
    0x640c0b24805607402c24001a00c0365007040c0428079208160708401c03418030144c0c01181c0440510a44140b0402c002d880600545c1c980c038501c079944500a01a4009603200290140160f05050380503040c800380b044400b10301050700351980350816500c40254207c04e41c035014051104c900d0381c45060000c00605003666800d81c0f0356110161107c80c0c444c00000f90040203070101c0d0500421001c0d004c00745030010100c400382003820001141030028100c881010a080080010b842e2425030030305004d4110608204250000c44040c0e140180140200900c034003040c42408540c41000341c000c0c1c9003e00388041c81030302600701099081e1100c02c807640050312076130030300880d03602d1813103150a9001114029907010070015400d0303815800170301807900709580060380459120400100b0517448000b0702829000e40c0c10214400904840c003905604803c000417109141d1240001c1c0c1c80d5009108042e603100406040901c000000b03816a401041c00d014150400700c010b100515145c0304407908516642051f0340107000396 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 749246969 1250 749245719 749245729
    0xc01020f0307170d020f0a0e1c08030a060902030c0903010510050a0512010b1f201b0f04330503060a0b04150602010606090f0e0604051902030903030a0b0d02 69
    0x12401064100a103c820020481c61402e1310040501413009640722040381400300c2503608989038000000b04040d04d0071041d400c01c070704c65111208030692104280051074403400c0c1d00340e1014108900e1070b03070f07960400101421244040c40c016168084d000f661045404d0405081d5500981600b499800240e800c0081d5620790707000d802210810788040400802000c0901c0c01001040c0d903007030304402c440c400f641241c034a503410b0240550304e580703d1020004120640014032140100d80141a0340803c40d00d84c142c85440381c8800102400405850f000c091400101e004c0d1880882541054020020b00c6145c80e03500390000079040b40e1740b0181510003403501000980c4c03060302074010049155614a5000c043c3c4954214001d030543d0f8a03480707507a4550310b58000380285031034403401000460b40040070440704032861258048921004082c5c2c0b0b0743d101c2900304401410f02030146c050074444014002c1d080c1c00719001662080d94060080d548918011322107000b40c44a2081240c030400780b04140350016910 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 749248219 1250 749246969 749246977
    0x61609090e03091207270f0c210e03070501020309070b1e0d020d0e0c0909010b060405040b06091503060406050a08030a031a18180102030105090424020c01020c0c01020f03 75
    0x20813070b48210345100741041c5504050f00e030b810004403051001c2e4404d0460004480788800414070390801c01038010300d47da0031821500700501602c0090404161144100700041056030012200e0000003000302d0310b440030525641c0030140454180e50044100710b0030b404c042c05100001c044034605c99260cc0c044000c1401d2105070b0f01182d08c5100404240c1240740817080d810f98000181e070100c00c02882d001d84082d150748404c03910880788a107411900262440c24103001c2c03a42007075405042642002e05040410000e00765066015810110038003151840360307904010460381450003940345d96282000400d101c241c58540d00064000c4400300400c100b80b031000002c0b0781c7d44d90124030780045c1a00400d021010200e050a0041d54000e52100781d005450b00c000e04038600418100c03203050050b54550b2040c5003030340001d01c5100d51007501e0500180200f8031350ba8030070054481e008070740d2140386e400050950481c1c03c186035600c050b0b13501240e06502c060042001c00c804030000d00007011081d0881e59a50baa07845 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 749249469 1250 749248219 749248237
    0x708010e0406110a0e1504120803090a1a0f060108070c111306090c0201050130060e1005040b06010201050c040506090103063602090d081b061609090e03 67
    0xd280000350a02c50079911549030403c00c074032203035a11000d5010050440c9203440c280303441840482c03034034140ca02d40e40041740c00f150921009040d490f07010f901c41c0c40d455000244519280c1c0690000080082d5900c403240c07116583c5401846d285080c040e10050f0022802410341d4144040207003407122141d005802c0160003940300d1241d41c402c41042c03000c20180c0e4003031300708100c0c0c0509100c4d000c61518a01d8204020010841c0d0081115a9913041038170301c440e5842c40c0050b071940080104000c1c54030b41003540990305004040104100010314a51480d140c03540b540660800c0d55203051004011101d42501d804c42424070090100d42851050b11845114070300c149803003440b0004a00280b40d020341c010340010309004501c0200900e0000b400860011100650808140d10754511040920f241c42910046400640003007442c0c0c0050703071001c4039680a40c0b00048081b800203210401c0e2441000254811950040107050910805c1c4002d0326803a020381265001c0e40c01d100080c3c225641c000140d9103008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 749250719 1250 749249469 749249489
    0x412020f06040f110d080c0d03060f05040e070e33090117071208040f05010c0305030601030203040f0f05100e03091e041e091101050423040e0318030d08070801 70
    0x700f03180342081300d03280240c034040d801020301200401801801c60240907606001000d403004c65603200300441c00c85001303000398031414010807428041d506155011481d030860b100b04840c180740e20791035540041c03401161041c0072504071040845803c080c4200701d03412800d4030b03035040003000e401900182d011072050158024001c802c00305000c030b810003080140c006002410601600300d8803800c00b04076680c414050402002c2c455200002e0952040035019040d40d0590359903030441e200d44c4011400b81d48003400c1550048840c0c4528404603c502000d604130610890080400c0290703800303404c0949900d11218007a540080c05041400e80311000030700c0f56241d00c0e47c805110400c400b00001c0c002e10061142804c5951010440d90070303021107a02a0092602484d007680ca0444410011120b911842c001d810030307002a036018800300103000606144880001b0000b1800420240c1018a180c10110440300100ca48041c00100341c1030920407040d420703040349048141881d0600c005040741c030040c03023821720301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 749251969 1250 749250719 749250743
    0x3141f210b07021905060f070e060d110f040909030906030e0c0f180123030604151d03030705070605090703020f010f0e03010615020105090616030b030a0605010303080412020f0604 79
    0x80340c0f080c000c200c80c101903641140090800d60504030b581e09000c072400a009011600030443c2c59000700422088030000811140c40c1641d041c9548000e06003101101d80006014440303441450400c001600c00f07010103400010344103985040c02400c03100168490030501d458540e04840d103080103d4000c08020b401c3d01c0644c40d1082e0702000ca400d4140450501c140304910000205400c0341e1800601100d40355940003019034680201010b494010694008000704500c06001804003529040242251010196040c000c9103003c1c10b142107500880d440c1001a03800948081080824890160054407002c0100201e0341594089a11a5503503401c081c144010001c41007a064803030101e10301c24500280c020300102d42d440c180d0b03112010b2002c030b84001650905000989058000803180d204510000d4030102e00543d00340203800524400845603014040c1c14000c0e804100c0714000e0500030362080d900e0942d01e00c0e05007450b2000803805418942150850420b07040c90510008a05800c103801c03800381088 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 749253219 1250 749251969 749251981
    0xc10050f03040b01080d0e130905031306020d0323042d11010e191e0b040f1e030b060f06040504050a0f0f060e010b030703141f210b 58
    0x1080c0100004003031010000800c0000b004100d01d100e034122550041100c40343c0000380f07416118180e40c65a032640203120031103039508080c04d642081c5002070141003940d00e402c0f072030398604c045500c85421000c00343e030260302c203200030356407521030881c081080c0e03d10258400d0038108140c40303080303000c2d201070514644583c0040303044034404440206550480004c3c6050240b0303151040e03c0c2648001c0c1c150110312485005065824101c4444184814071518003a900341071544900c01100030b032405101403216004049407030f22050f401032001d03048054416000c0c915000ba81041103054034052201114041c60410000e0300c1560700c3c9070041021601d06407122014804501c0c1401242d11190b4041e044c902031144215491b030040aa24280701c1c0c0074018418510901c1d420703540b49219001d24020100300400801c0300e60b002642d0460681c1c9008a14804441e01000e030a080507100034003c102d80c02040e642d0f54010b160b40f24024800c060403221070300c4600c02c41c4800600d8004015041b000e050002802c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 749254469 1250 749253219 749253227
    0x40b16200f0d21020711041e09060504210203040b0d180605060112060503100902030705120708061609090c0210020a0e040f020f09120705030a0b090c0a06020c10 71
    0x801005103022584951104031008000020320082000300702d02c5603141c10540c03c410b0003141e05941d08840c0d06455403600e41e0034440109078407900d00d1036010743da003103286410071039009040790240103030700c080303101e0030142012580d401c80808040b85061150034166081e81d00801524120340074821a65140c0c9003405030140605510403aa800164040c50f4040400606c0d078000d5026080030380e070707000005000d01c4500301281c0181c09100e13031540c171104071111510f5840e04009a001d1000d015140c1d115507031000f0402c041002c412850b4250403119003401300b044100312036948210181035400c0a00c088a5018152007012f024650999840e46100a0614006c215000c000140e4010855580c04803102c021b000c000c1110005104078289044240c80702c92a000355043c580d600703540e45103400300080c1001854000d25801d00240d0060070000110b07a42c01307100012209001d0540c90250b450034101180c20040c010207090301c00c0510b0305c5c05200d502e60009100001c42025551400c0d4604003a40982d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 749255719 1250 749254469 749254483
    0x61b02030601150807030b01091202040209100e0108090102070b07050a020f150106030c0e0a12050f01020a020c041b0c020103020d0b150903010e0a110d060603080c06040b1620 77
    0x80e4140c89110000030740d9001020a0780890030b071a030346080007a2a0b0301000c90a0b140c400413594005170403003a0500001c80007018200340c052000b800180760298040210303541c502c851103030801003161a042d040d4a03503080014280c4c0100d1701c1c8000c52400e841540c41040ca80310203840701c000c2210220324405240d000b00714482c4040c411000301c1d004200d4072004020603001c24060b1000103400d201301810880d0180a0f0101d244800820400400b814080f4000103c03d000c40d098800c3e1040a031412403c4000384002d201400c207907405001c0c0329058805010644800b1a160103000000030603d0400c16840400781504550900c1e0150303079030010580c2d020140c0320307028603e0b600080c0c0c10f1606852240300c0000704014481034000340483e039031240720591240400c4401a10b0304104031601040c40c034080b0481c01a8910441c4c000403215140d03240c0040c55084500d103401650712581c2404207012528036001d6115508104801020054100c0103020489220a00d0101c3c80b103000306242d140b078188014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 749256969 1250 749255719 749255723
    0x61315020c0604170403110609010302090a08071409090d030c120e100e07060f2307080909010b0f090d06061703070b060301060b07020f0307170c091f061b 68
    0x15520352115109450b01c411060b68202c40e2034002d0200c0300086501001650100c4c7d4202c4684003401030008107201403540000d0003181019401c1180300b1040e42c510140c20003804131381e00107200003410054003e0b4003169000005110380d460070100700c8480c1000075419944041443c020030111042030040e6843c4600307262281d1041d081801082001c4c1000a00300c02c60001d9440501140c25400a807a40350049400b8803000900f807a8072607031b0014060820100900c0d1141040c1421160700002d040803a000210700302d038512000100110781d0725180c1c4000b805805271404051504501c2110081544100300e0346a014401c9080900c0500815034000c1e4000c02c5c1d4028240b140d8034544800c661607600411044a030031112402182050a0511508003502c44003045945002166020000100402000c095262003100d4000c90340d42c450745000d030003c00641004003864402c0740200040303903030300804009a59500e1007070940417010420b1407a003115540d00709400a200b5204c00b00c0e550000070400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 749258219 1250 749256969 749256971
    0x30a0c0915030207170c0a02120f0607050901030b04060605250b04061e1406010809160f06090e0f0a0b0607080a1223160201060f031b0611061315 64
    0x19141c140d54040e0002c2820500c81c070b0782106902c86056241100e03000e100c5001d4810ba10169042005045c080030390510030740480c2c101d41d0140d42e402131580c9010401c454650000b0300c0071541010658140c011000c902c00b040790244002c9081140041507409010002681141820981252281c8d60200c00e1452500200003c601d0316140c00c255026000c2014142c0c41007030710706085021502c0510a14802050318104d01c10701d03880d503100440340e003c0c025211482a004541c9041503038210b040c1d5042c014075806244440d50b45c0380c80da000c0c240f5a004d5005d0780800c01e000e020410b03c69500d450042c1c1c407501855001070041c0024001c100940506100100300b803800080d4203410980190282901d000c99400070301007203040d2414200142c0c40c41c0c08040c501d401e141e02050707001c040d5075540410020140700004460380d0701d00740c0d03103075548599105440714103150400d52014241300e0040740c09410503051410092019042c0e15658a038010011542e404a405c140c004120b460300d122000801c039004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 749259469 1250 749258219 749258249
    0xa0f031a091311060c0a08210403110105010b090a170f06010e0108071406030708070e060406080405010e0f0d08190204031103060106020c0a1a0d1d21030a0c09 70
    0x1544407040600d00c801d4807031a46401283d040c5150280468010700f1985001d814602d40d175a0f5400d0460300011120103a0703000e40780e98440c8041d801c00b29240705502903a40d84240c810044551421240180c0240b480c1a6041002c001503881d9000840e00722861100c0c40c035400b8460506c0d06017022004120108180034000c0000742050008915906950f001d00c15182d2140d5511a880808030104287d15040102070000584041c050054150300403580d00300307007945c418450000784507039016400c5400401c21242c240400d01c4404d1248111401040000301810313506404070f1940c501d1240030000401610310b0000d0103000161a40e40b010701040c140030b648503512454180c0c200440064018024464140001070080c4000b0380181035000c01703442107102a06240d1101140101c05100c820f07050f80402002912140911420352000520404100c0554040c00403178100b4015045070001d126100f91000c8208584100712a00920103103c006001604450b080d5801501d95020810681c00a9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 749260719 1250 749259469 749259481
    0x6022d070b030115030c0c0b0402040b030d05070c140d0803100e1501110d0806130e0a05030c0f060105090c0904091709101b0807051002030a090c08030a0f031a09 71
    0x8030155040c4c0c0c0401c5001402a4484c003401c400700d41e151100303080012601c9040b040415460300e200ca07003282c005000814100800740200b0303d0900307080e20040010320005940d4003441000f6480e0780c041c0860790b164501d0b810440c40005d05103150300b00d010702041000000314a0070000780d400c050090500d0080701c40300345005000254801692142e41d40030400d0014074901c0d041c00818408038100713030341e280c4400c0c1d51510780902018480303403d0381e60301c01c0350340b0840c00c590107000308440c81e06144201c00442d42c4d041d0003c0c00c54100000b0180e6010168800d100601441e9a8080030b140d01c1303901c0000c444c0d101c85003000004c015040c1040007411f240700ca441c4000c1c40e01d130380c02c1c0141000e03541618210a400301e580f004071034003914003074221000c0044c2141c203c005403121008160850041e012107020030703240d00d46002280d10075200045925565407140c0708100750741038041d0051020f40080c500b090702c0d6035006408911075080820400d0356a00703880000744920040741c0349450000c0c007404c182e85800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 749261969 1250 749260719 749260739
    0x2703050a090e370207060603120c0305030408032203020f12070c09050c071b060201050105010507030e24070308090c1009060302090f06030c120c0406022d07 69
    0x5040c400000340c50700c501140210072501041e028154844851280650700300c2c00c00c00d40d0342c2c2c07111680c00141d52020a40181c0b0102d00203000380702d00881000803054594500002064400f00685041c40703207c00d0710b000460713080020b0300e91003604072020956a5407000e261804520070048202c40e060b402c1030020040c50713800185604002504c404071a12502d20251080090080c1007006105554442d001d0101c41c03c0c1c1d810241c1c210a03803c202d43d0500210350b4401c5804603c80341505030b1400c4c19002007040641c240071701401400207007015441d001c0302d6100100116603580420b8001c401200d00c4450560f103181c0c0701c04c1810051a0302d15121460751030010090703013054681c03200620030103d0f2010fa1749000d04508a50304a2522240c000510301007040d0060340120500c694030501582101301c403a103501c8004d41c450b196010341c540e41d4500340c030f40ea080010000303091400710000c1400140b10041d000542c90f044542020300140d0349851300b44002480e007092107054505402901c4000800e0028 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 749263219 1250 749261969 749261977
    0x607081f0f0e040b010608090705040905010e0d1812020f1002070905150a05090906073501181a12120414100507050c010806120106061211040810270305 67
    0x10031484c6a00590380c41d801100e410700203840301c404a0300078010410640c6000e44c46411054420350000c9000342207501141d00f086130250304503011403a280d00030b40c126120b1300d01a1000d0300480c42c21100203c000e8010482406450350f91900a9086103038100c6030360b00800001c0700800000703a061081e8901174442014030141060094050880842c021842d072a0109005225201043c001e10260303803003c43c00c4a01040c005d000c0b0075101c450a01c0340382c81941031203002881c034044039021229540360003400c1d04008034410b40c0e940b8561400340110034140380c101103000d0080049039010134981041d483c05080c88511884501170b000001400101c00c9070020306084c00380e500300e400c0740e02e02981d0281526070b44504400180740d504240c2c91a0350560198800342d401140250254401c0120004030310308480054012101048200100c80081c80041c000c24091024001c000d5081518100e940c42d40d0f100e00e403045000594442150307800d000e01209c1e001c840c000c0c1c07044640400d510582000741203030744 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 749264469 1250 749263219 749263223
    0xe131e150f0c03050f0c0a14030c040e0c1812070e01031208060d030c060903090e04030305060f030f0c090c0909011503050a0513030809030d020c01050114030607081f0f0e04 76
    0x41040c012100070b600a01c82e081c4185a0ba0912801a5a94060b5a2201d07031000004806001640040384001100c82014510400009410303e9896090804404d400b28008199005006007009248070515821005903440901a02c180400c04060200181050070b55048039020440d80d800010600440340e1400301c0701a4540c0340d2541507102c0d14144014002e440b00c002d000301c0c000403d0800041d160741e0003030348105c0c06031900d8051a5220f81500d103513410150b4056000030b440c5e0341807013250700c0d100141c0b50300310034100c004007582d000040c0b00c99159080c46410500c903240301030020b904000d07028200c940c135140041016042c2d6844408205140d0040041038000034680030000d6003c205900c1100d0084030b20002248003144540d8040390f406800501c410090b00080c4008540d480441c0003801480030f00d000046030b00d60401c003104100c9542001064403a0348101d09004880d03400180c5a03410500001c00000190aa440003003c9120260f01022540d1102c10f00010328882600d800340c0214 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 749265719 1250 749264469 749264471
    0x80f071e030209010308090102190327230402041d0708060108040f020607110a060c0317040b0f130b010617180d120e06010602060f010e131e150f 64
    0xc10304250a90040041d01009402004000c0184046180080542074000d0140704844044c0300801d2107091684100e90f0407404038042102000d048051000f405910459401c08800706a1074a0802c911009507100f414480b0400c40340da4810079211501240c0c0980044598006c1c103800c075000d0174405071011241270000444231004a0b110350700c5200030f40e01440d000300c0c0c01c0d1a071180326001c108059001d04000c94001040d07100324502c03600c1d201c84003001018030751181d0030740c026a4203010303040c41e4103120306030803400890b820000000c89c80b1404a41261a04100d520340ea034800501d6100c04030340380c2c0094004140b00000003112648030030300c04249900301902d00b54503103611654954565064061621903000414203118251041840201d01c5a80c10404a2504104c2c403000f410103500303821580042e0010010041c3d9401c044a203030340148504074041c4400d1400c03c05082c458610780700020308203508000d0a10706640d07411a4044060740000051890150103d00c04004041d14580388240c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 749266969 1250 749265719 749265749
    0x51510150c051f0b13050a0606020303042102030d0e010b040e01090c030210090e04110117130b04060608030d0c020f0d0912062c0c0906030c040f06080f07 68
    0x5501c40c03949480210b0380240103100e21080e40502c40c4082a40102c20f101580d501c0f080c0c01d965030b450001c1d02e5250140900d000581c0d01b4a0403118050719507030382044041d58010000c1c0000114901e103c0c94090035118001d1144081e40d8604a00314481c40b0059100d090400864042003113066105591001003200c003040018000c020042c240e4400c510b011700309038807060b010800b6003090740c8800c40c408414a451038038a625802180391500f802c1d5801e58105004251050942d60071018564042d207000c10800c01c9481c1c402d0000b0700e01240b401000303000710340350000b140410456070040e0003e0700c90070302600d0702c8516115041c4010882040c200c0018418101c4480c03071000c001c00e155400e1201a90744444181c14040041d406903049034040f0f074840e980c0c01e40e04401310100c00468000303464500d0544200e00c0c210041c14070b04104580100d1040718488144411070340c00066144141c0415200850400c07290040e84000700718550001038240964071054407001004030710417007641c104006071058 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 749268219 1250 749266969 749267009
    0x105060a0f0308310b13090203101503020708370207061d040c1d1509041e0606091d010e010b18061204140c1c051510 52
    0x80d20148005068203504205421071307803e6695901e40076030302800085030a14001888141c1d802c443c0c0c0e0010604c07102c0483e83c8500010309000d0b03003004000b0803800b507045040075035030852503041c548502040244440060071003540290140c503c401e13044030125880c0d004225011142d415120315003007040a800903250007540000441c009004c4803907000f0690f160070440c0941d9600c0c6180700740b400c0c0d0b408542c0c01280e0356449008005100302c4603501d40203292061448220414000c40070a0b201e0700c01000210750681441d02a42e0110300304840100701d10319a004814560210641004d0b1102d04106000c150190048049002c9640d2148d103000c080d1001c02d2403441c035040c21300038a42e17610106401000052004400740000110319900c03e080c400034003002444036480030080c10003e40d0348c40200001e012440e1403080a40c00d44074041c0042d68007542c005908040c0402c940c80700c0c100d40028140034070a04114070406000a006216903a041a0728044084074052041c0d50309a103d0b8054005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 749269469 1250 749268219 749268239
    0x304080408010f0504030e0d031101020a03020a110d020d0c021f05030912070b010b0304150e0705150a081f05040531080901031119120513080315010306030f050105060a 74
    0x205c180d40682d079500024160008108003005440d8080d82002001480400d110100788028021140c840c0c80059890410101c0541020a401403003140c079048a007a440c29280c0120301f21442c0e0b032103403800c400c040d0030340c0c40041c415401d8040b007407c1c403442450383c00102070340207402540a4070a80080f1480c8601b064251038543c458201c000b8200038219004225400444c070145070001c3c031411458800000224030f0404490905a21354201ea0003040c0030041e60900000302210703002c0c180308052400c0082600900746400107451182c11406803a046144901d003009410090034000b0010b00c0181480302140c5000b0000503007900804d182d6554129a601040c1201440c03e50f000415074248450b0100560040400d41c80c000d4040c5400c010301400821140e1208140407010b0b210918100288075549080300c078010404140221498180c0300880c003050141c0e5030015010300c11824a000380c02c0100c3c050103455100a00e034a41d212950f000300715040d0006480b070348065540c2d40b6060394401d0380030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 749270719 1250 749269469 749269471
    0x5060604030f0b060d020603100f062f03041d0114090f07110c040905030c0609030c0705060d0f0203040c091b050304060b1f02070f051f081b0304080408010f05 70
    0xc0c01080d1402c0d220000a550103205980114010058003c0c03580c0e540101c1d809905c22a41101602410401071092051142113240506514a000210220414003030034405281c07826501c40d0100c00401224104401c00c1264040d003178005001c04a2540303c100b41035507420a004081c480749200000c6000d5040104010307109200e0070000d0340042d22010410f9035040143c00403002e00b40103860081807141c945000b5413030b803c2d22074002141d4400c00d81d00081d003414009813441c99642c104001c80c102ca0000061500d00fa900b0483d01103540d03c0001043c2d0009141a007040114103001200304030500c02c031010994116010002d040c000c0d40d00001001e05407000c001c0800d00422014408107002c200e5582c0041c80a0802628000c02c0c004454a00325640c441a80c038240164404401400041a40c8000800800701070300d04035195420103820802c194403208110f801c200c011000204410020101c9110100321071310a40e90724105410a03042e1a445030140304015070900c407804000520713501c0340c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 749271969 1250 749270719 749270723
    0xe030c1e12032809080102070b220b0c0c010f06060e190e180c0916110115060c0318080a020909030702090105040c0302090301020c0a0212070303020d12091b05040506060403 76
    0x410500c030082d007103450a0f090404038020803c2040c00804d040c1d009100900c98107014020413212403414031089940c1580180c2260318600c0141002d40c002030400381c000c0c1d0001c040c001056103510248680c240103161a02e0318010044c10810b0000704190407094210441c24261003d4408840011196661046c64030404200108000c000b03442d4a11824400864001c400c0945400c280c19100043c006031040e150b04403116107d50300b9103080d580000074491080040d50091100700d02403000580c803801c1c5407003040107120345110300348100342c880c072032880500480c61380083d02c0e60784544019070740e140d030141e04900410154000c501c0714070303000090741c0840754001c044050680c200810304c8090301c1c8454280741855000c1c4401d04070b55400703002411b0911951002415000d1940c010800840d034240328440854000c2e0030203001181e0301040d420355130140e90904c204404010401c03030340244241e0710060700d20300b0350087d170303c00803000d04001134100c4004480921154484c0000c01c40984164400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 749273219 1250 749271969 749271997
    0x10b0307150f0203130b07080d0903080a05060d0f201905010314090a030c050f120d050604020304080d2708030a0c02010e070e0c04051906021207080a0e030c1e1203 72
    0x8000406c1d07810000d0003014070510849050010300c40c4020b082d00d20180f021004901c880b01082102042da03ca490741c02942101c0380281d80d4450348542d18010220a40a4120070f10050710700001d02147d070048240690181020003640b83d04541104461140d016641c000707814601440a0684c080114502807000d54000d000e00b000c950303a0540300c40100c0c45007101c443c01030300c1408010701014440c21100203005c07088036542e490f06409004c1254001800d00c2d00c41d61042c010700002c60000400c0c0c840c2c21249910006660790102e107c020141600000718290303164100c3c56070108403001010b10301590540e9020310040240510681c00e80e04c1140d04010b4503404900208902504d0310080394010654510b92850b16850b000850b10404810706800311442e804541080711642c100720340801c0d040d0100119051074060b990f41403142c42400300c004200402c18003001429641404202c902e060010201111200242d010781608034602c04014458001c0203101041c181020085443e841e8035550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 749274469 1250 749273219 749273257
    0x3230105071710090e0a061103010e060d051203250903030509100e0319030207060315090c020c1305060a0b04050306040b07140f0403060b041814010b0307150f0203 72
    0x1d40354802001030880740d0ba00703202c0e10f0000e05294644075100f02c0b2245600130b401e241c80d65043c2101502c1c02002400e001602c00c00c0108030758481c0981e10b0750401411200e200701007040d400c0c4030707142ca840d04220a00101c0000144200d0601c0440c01030407200901010a1019050460944200d000382c40054080b8204002e031290354588203d40810741c0d01e050406c0e4100846007800300b4640340280c0020100c0350b4071100790301d091540401c50480100600d00d418441c0006c0c039514520a5011032107004006a105c217190483c842c002d01054401407400b5203400c000c640701c1f41c0c1e440c0140800741c03261401480b00c3e10300442d00c855690100c8042e6030300903005014948031a582c40c00350040003000c4108206108140e10080808100100380c0e22030180f414070b40791800c500f040d40460342484002c6210307a1601d05442d403102404281200d0036a00003201050540c00601c040d8054991020955810300610001140500080d07001e01c4124410f80e864904010002100341c0e904c2c8240710714420803181c114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 749275719 1250 749274469 749274497
    0x6060d080306131a01110d050406030f0207080313020901060c050c061605060702010501030c06051813110f0c0615011d03120403030201020a030b03070b0f0915040323010507 76
    0x30000c54020b000680102c04900c11a500743e0704680da9244600130300520007050b000300e51b82c001c0c8215400903080000c0c180c20b1078105c0300500103105034490b0308103154442458074401c0080b6419990155002140240e0341d140074544a1085811600c0c2248541340400022078858071410740f40c00796650102c010178011651908002d00d64024914000488000810000c0000c2c808e00c150b0b801010702c2c0c6c0011030554198074040c125010203070410020020140716042c1802502c00c06001568030507100c190100c00c40e1741c98940640207042400744500e80000740034842040e070760000c00c3d19800322401e40714140c40d542245aa69114040300714000340c81d40f0794040e5412850122650b0b041c0300281150304003001c0d4400c13544607410550080d00546d40c00b1a0004045805018505202a04030042e000c0c0c2d5052011007141070141001c0e02c5482c1c2400f184100560301e036502001030824200c01e200d6110b40c0e03685096510240361440304022000d4502100c1051326050041c14003514170354490458003446d030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 749276969 1250 749275719 749275733
    0x4030602030411030703050a051c0c0320030a0c0501110f040510030e1c080f0105010f05180607060603021309020f010809010f06140307120b01140d171b06060d 70
    0x380003559080c000320f402101e5a80e0401103c80118819000780000e1016800c2c05410071610000c842c4450705e541c5682074119074040480c8034000d6141c20002e0103030035400c4001c0424100e0a601c24801e200c0050400141030700000038007001441603000303010f2003400c3c0340d9015090242c5904003442030400d00c014005841c01404006600506133000140102c1c00b2714054074241001c0f1036200d14000f6040e00b1303101258015441d5034002d03030b20808044c59500d0200004e02041c00802610108080810200609500c0b10800114858002e080a84460701801d01d6802843c840c8000c910803000c0b9035141803800c203d80540800c01c0c0d0001d14034020101d6140054034035550040c0040c40c40d5590302c41e580354101451003800301030415030310304e0401d68001d40c2c00c0c54034200c6641c000841d10342c070303081d060300004810341080f40c1074070642e5400200f400380f81808560403208214004121103900f25400d0b140413040c00c040c0503900d05180f0900010a0103a1425440340000d95403030340c0250301000158041122 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 749278219 1250 749276969 749276971
    0x11101509180c091506110c011107030203060916080607050d0504020a030f0506160c02030601120804030b01150905010c05060f1909050322050a030b1306020412050f010606050403060203 81
    0x3040445000400c1c1d40c1c038454aa01c00e6088445081c0d0395082c1c804001c0030075802c050140c01d030740c10005180d10520501541d1410081d03c1d83d81041110f01d000040144140071400041d5400f80c00c40d105410540a0161105540207900d584c409501c040000c0080740090b4580c01161503031100e924041d648200b800140c0002001030340c100c1c944860020014000c403190004180c0904007415980c00e01c000794001e6007007203078030003400c0020300c61458000da80c0100f0386904480c4680090459034036a8686210326026640c0041c0c00c0c4868400006000f00c9204182441041d05540d9070300c6480e00c0301d0066803124410700e0042c0480d400100040c1c4d1a010f041900c5422500e9444017132072036154050303143c050700c7e10541c0c200c9030b0fa0808985840f80300c002403030781c812111442d54040412070070880415034848452001500e214441004994a6454240100360300c6401080565580b5224955500e2100003200f04403028400c00d042d06900440600c10344094504554a00e49080e19540f150006908 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 749279469 1250 749278219 749278241
    0x6012f190302250b041e05270606191b080408010b09240105072a0311040603050c01050a02011d060f0109020306061c0e01050711101509 60
    0x2003804104200c0d1005044080d000e9407080d4010000312070b94080040811115103c01c0d070f1404106801480085541400d40303003603581000b481c040301c400c051040014000d00d580b280790400c19aa85140c10380080148030501c091040316a1404c8d503c1d000240000d620031076146d20f07012400c890488089030b00c10510301000e00f18000c2d4512403040c441d16a154160f000794854a4503a540e10380d10340c000c0c28202051a8800c0490398045179085c401512200d590122264190420800250b007800300440901d0340e5508001d10b182091003482040c07c8104504541d01054903c10940b050a500502c0c05004140560f64880060302d201c82c10381d8015184c13a04040001c905654880120418284514070541025448070340101000c0c206206411004075060304580500c1d80100200101a00c9103412161600700c2040a40340d80081ea0300844020050f03404019403035401c0c0000c0c00b091540c03111181c401103140505135861540f089007014211007454410140d07082d50700c2c104019281d001e81c40714031084 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 749280575 1106 749279469 749279473
    0x100602010e01181101050714070f12020f04051b190807090609120204020c19030f0509091803130f1a09010804110a05040c021506012f 59
    0x2c1006003d003140c4c1e80d02681c03c2459110344101e407402500488280045c0c40d0902985840701001c2c400c03142003500a103408100101e202e5050000c01c0d900800564003410004180809808000d000b409514880049207440b00f0fa40802044003401e1500080008030003d0710150030b0500c00380940d410841c0c9203109202060b00800c01c80c0a5460940d501350750040c2500c00100a8450920f03c0401402503020401c4c00034007080b0300c00b41d0544203072640c098442e420b4a0031a041d0103424100d07684031b0602e40108010441c01101d00340c180c2556810b492604500c0c0b00e00480c4c66025a02140400e10301d070b0340404c603840a03c0a40800f030440c0146451a060300800000d100c00d2000e040070300803030211410381c00191707101c02c5550000d140c00341083c48207188814003e500c4610b01c02c50100c0141440c00040ca6541c455111044582c80d01040310341c52800d0a1100104c0d41c1d40141203040038 = true := by decide +kernel

theorem cover : BRFrame.Cov 749100719 749280575 := by
  have h0 := BRFrame.cov_init 749100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 749100719 ≤ n) (h2 : n < 749280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
