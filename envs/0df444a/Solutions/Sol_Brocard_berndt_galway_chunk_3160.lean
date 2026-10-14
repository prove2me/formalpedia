-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3160
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:50:20.44762+00:00
-- url     : https://prove2.me/submissions/c9a3944b-819b-44e0-ab80-73ab25111f55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 568165467 ≤ n < 568345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 568166717 1250 568165467 568165519
    0xf050c1602040b030c0604080303070206130305030a09020406090606030501051203070b130201090f0b09130b031b190303080702010c09060f03051e0114031b010e09090109061a 77
    0x25a58214032030080140c981038000140b240c00203401c4d19031103000d60001c21495441500300d804603500c0002880034443c8d042200c150b21004141d034400b50082140d070004d11a01c03001c1c0071846034503111701c01c020543d91158440001441d6107030041043c541d9401003d40608400d104641c820310301d00e4044650950044101ca03000e6910180076102c540d11aa000945c82a000d041641000081c0d1800f0611120b01d00404e00a40401514103840e05065000c12204046282580c84454140114900c4039100003880c140802030081100010220050211f6071070ba25040e92000d001c0035800700001407540040c4040d01403401680203005c00b68109206442d0480c0500c50380c80000c681d18103035412603110f503000581007540103408601e824890702003410003010a03085015a161030100040091804000380196203c40d0010305074290040340019151440054000d800380b0b0171800040c00d07107c0c007075004c418100e40c840d4041050340001d010103207416800d44002070240182501d80126000c0c1000d17221 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 568167967 1250 568166717 568166737
    0x30c1914181303030b040507110f07060504300602131a0702010e0301140c040609060201150306180c0e06150313080a03110304080307020c090c04030b070e04020d0f050c 74
    0x20460b4660842e2100009400501a02003617a00c0c00d4400495559018072800f43d941c40e40d40d80f01708a45010314a00f07003480700304404c0240c2d0260404110582d00042914115901b100c101d0081e100940120500f80c0f01c0440400712070a0308280010801107694081c2c48001e4680d005000025241d0001e4074180044a40c80c0b4000c0f4001d0010f000150b100b212850134082c0081c0c004202c09131050f42510b50030300240d403102e840315000714040c030156600031000001015188005d01c6803002d602001180100c42e404003034022a03c0c2c0b40b294111880b0000300e0900d081c1d218421800c8035030341c3e482c03107459800180d50081c4103120341c1042c00c00341e48110f015240035884584004042110590358843c15510003c0304600b4940c5403025400a10784d4000518415805804001c1c3d491600003002814100354900b2144100da00c0c0c810b0060b44c038402000d40302581c0d40070034819065100c0700001e90b52141c40040040c0c0c40f500000b96203051242e103802c00c10180300d001005000325102e46180400070702540301d0f14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 568169217 1250 568167967 568168009
    0x32715030a020f041203030605040c0e09010b0304050703120302041d0606090108040507090c18060f0206040803070302090603130212010c1202341106070f060b030c1914 74
    0x415810580ca030b00800703d1500e40e060315860030341d85a00d9284098550b40007903000c665521410005801c0038040c2210300d00480c9130080704171a01000140c841701060044409254020000408026042040e58090758001e9080401f0710440100180a9071050083d000f030008001c90308902e0302031a042c1107000300320090589080c40c00b1000111204103006202396000e02c104100060084814480c0044204842d520408843e1a00020344294944c0e0360050b81000105524561429800306500d50041d42c4039003500d5480c0c480560484c081c0c0079044100c0d070b003c0400010312a50403004010342e00b03510300c2601c03442001c002e005105400c0f900b0205800010407046920096091490b50003010090008400d9000301c03609001004d140240e459030052165907520a828188501c28014041c44403044400919001150341c9101e42940d40313410061083e0749030402004156030a1108641443c0040c0c003005100030030f800000c0f4540e0240c0320f805134109002c520818036080c5000c81400808400c055 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 568170467 1250 568169217 568169221
    0x2070809130f060f090e0606090105060f0c070b0403060e0c0603070e04090f03051312080d09020d0213020a172e030f050c01140705100e030c03271503 66
    0x5001d0500ca80d0030500c40580e07a540e0220700c822020b4031074400585501d0401c0612541402d41a000302e8240c8100444030703500c48010003145a45138a50541527903003c3e540e55403100c8052242e20000c0c050100b521030310b405400c1d800f042041003100540104d90188509200d011020803c064403165080310f00354000d8810000690020b00544004460120207080042e98284a0711416042918980110001807000a0710400d000440d500e46e00a004100003820114201d503076001c02c0c2c0d00c5580e403003a00c1a0f442c2c0c239a4409556607004120a1241c000e45000c48403800008602d00952008041f900032581481c4081440c2d100710130041d00c03400e5660744440000506a074004640d1080e19a911444150001c0c00703c0003804141c040d0113100e02c20345c000c00a12002400241039128040d03815603c015003801440042100000d82c4d8902400340000000e40d400c44008450941c4038800300901c8510001424028108240c900d0742e5160b0741245a0121400c101003c200300d000354466020041e0384d003400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 568171717 1250 568170467 568170469
    0x4060b041a211605210304030303110c15041202010e0304030b090c131a0d021c05030f071b08061b0f1308060604050c09032a0a120c05010302070809 65
    0x3010402c40050b0000c50b80861090940603141075080392500051610b519010402410103078070f81c4076040c11029070800548141a80c2a83c1c074025840f0207020192107580000c02a50070bc0704540c0080b40410640309410224000d0f071942d803405a03001c072141207200d58907503503442c07040c4a00c01c0ca102c1c450010710301e0203203183c85080e018000603122580d02c1c028103005040540d101a103900f101c0100000100b4102080441c40b0801e802c0d00c3d03103142c0200e03158685200180e0310304941540034003c860010301c07080340781d043c1149036004000981240400005498007401440c181c1507010001c842e800c0381c03106489449103a21060141c0e0b00d2881007250055500d000e54246020305102060b421440e4100780b01c03500414014042c42d4800d28a98212606105850034240100390384004885401803a20600d000403a981d4419000c001c0e150341c1031203491646084101180e00f403c260f009210032400c507190300c00c565140c4240581160380c1d4201c1140051103500034001e0715082d81d00700320380509081c1184 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 568172967 1250 568171717 568171729
    0x1d03011b11010f1416020c09040602070609020a0611070f0305060708040f0206030c0c010e0c01050a0509011b21081311060c010903031b0509060405060703140c0604060b041a 76
    0x250301c10720954032065800030a444a119030321100145400c890590f08018580c12025070007410510b04540081c070224071142c60f40c040640d00715911100059940c0200c0c1040c100803c090a8025070150280b0400944a07070701004503091100c0c05001c2c3d0301d0b103542e01d40402c07410000d9840002c08030342002d000a15402c3c000c411950303219000e1f8000d4415101c03182c0c00507600d9401151521140c41000c122440612004d00c6200f03000540d0000501a1031708480c0040c1a078003902408904100c40012400358a900c182241c440c1031501e100c4240c40c000d02032824400d5a50f0b01c8030340c0480c0620100e09541c0c40e034413400c0f01900880300c80c40300b4140c2e95000c0d01c0f0409200e0013008469040407082211581c0c170030003441107070355282c044c4d03900189100b03c00403004400c030a900c128504002060007401883e40c0c4680071201254000ca400f10741d01c5c02203142c00d0b1591803620002003490080800c41e401c0e0b0401c003040345441140700d4003040051200031340c01c210440c0d5040c240321802840805104425050030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 568174217 1250 568172967 568172987
    0x8060603120906041a180d05100218041109121501090f090503030901050105010e0d020a0b0c0705061b0c150d09031b210201020f030c03040f02101d03011b 68
    0x10707000304d10b05616850060780d00340b080440107144039000200d00d0228400120800545042100c00d0350303107140542c0b1759650310300c40030038896202d91303000600c80001c41e103040001d01d00550140c82401800c210340380e1203850340c026072903150142c2c1c1200000d0f00f51010100303c4041ca0041e100c09104035900b4420000c000705462020501045c4e628803d0f0b901040c0c0400141d4840d42c000000410355604000004001001c5044d8007805003c60250000040c0e1710341407002c4c240c0d010149a15228007004011915140e03003a40240c1d0800e20029044c01003107401c3d00c1030314144004004403110300100c0010b11845a20800751400b10f08401d1003202c081400035000b840c01030303000b440e00c000303600602a250301514100c0c51040711454403205100c11070040f00182c000300d810450008608000703201100c80b29620006089100b220340000006082005100d0194040c82e0041d1500e409004801000f0b8294600440c0141c9140480d030700051640c5030501625020180700320408a034000f03488030a403800521 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 568175467 1250 568174217 568174219
    0x3100501150c0503040e010b09040b040506031203040611121006050703120b03160f03031d091b0d110301080606040603050c010e041b091719030807031e15080606031209 74
    0x1000b0003d41c2e0301146da000c601a03c04615801e5517030341d42108000c211880c0410043c0194208010000c10341c1d80444c058810258502046a49664602e080320007030280c40800300b0311050104d103440180302100403a600c207003158180100d6031a11ba100c00d544a00805400a00240303900c0c0e032003895000ca64003c110b206030082c0c110f030131b10741603424001c1c5245001d4003d1500900c445900700705150380580d01c00c0301c0c2d080c4031803050807180400d0003060502c0380040450314906840c01c4490000180002216038041e60000200801500184c3e0300340c107036000b8440c4610398881d00d008079955152a224210840c0c0d0310400828140d03100c1130040d6018004581030710740c0b1075990f25020100c0203500c001818010120b03070b50030384100d080412500030010303506000303406940026204108444c0c5c0b030b800c2000464141c20141816516440d040700940702500c03181401d03111320041d000c00c0c540309802010484180560968446465416041d600e2030101d504544c583e210010f981c4803061294020818804 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 568176717 1250 568175467 568175473
    0x180503060c071a18070b18060306030a0605040b01030b070e0a0603050a060f030b090d091404050421020105100b07030e10031b0f09090605130c0909090804030203100501150c05 77
    0x2d000e5004400c007008a840d01038078134800000d0b818544080c400d08002d4000005a1800d1105648989607a201002d40c01806000c0000210f030b0959000c01c10005601c0d40098140310703910f402d14010031844402e1204075800040c61002c601c040c1d00a00540020041c0500300c01101d83c6060400c170040d0001402c01e14405685180100343c880c0c82c1144040a0350166a030b080c403034200701c08880e03d080140d2600320304016404106002201c5c403030b00c1440d10540100c50100f0b603920f544c200301d4a0755a40f9500840b900032520001640181c064020522a8541454156580d90765070366814046c407401800070001020012190302c40c0c43c10308046003c0100a02c0d00040c4180c0303001501c2050b2680c2030121380440d20a410ba21010742d031003c0680d02815078004280015890080450b0304884249244030402d0b840d10400c014940c807030000c1400806110a0030f00501c030ba2400c25100d1544640001d901034050b811195407001981c0c069075048400c00019460f165020120458210340980011513441c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 568177967 1250 568176717 568176743
    0x4020406050a03140c0d1a040204020d050a0c020606010e060d05041b0b0d0b010f08010e060d05030a0f030b0a290f04060908010c0215130c03050709050601180503060c07 74
    0x7803200b500d258055845103c1401c000d0041e45040380c40c1a10550340c2921a111449103100010b8824000c4415450340515031811500e992000178040d00442e151b03404910b1400e010030a250400e0340012400721a19002c0c0c0b1055120700c40116450404044225000b0f4010071480a0010302507202a50041c00303a00029844003202041004411030b59201d14030361b01d8042a000304170f080921a0042c9454242071808244070300000241060303605200796081c100704803001818540742c6c0307664200030f1503209058070b0741c580240030007500030b089010354000042e1a242c1da02e96581401c004050980720341c072180e5120500400703e41808030322101c441805a030014400c0e5040600f000024002403c0316846040c2c48500b407502c4c4c0790131a0100d0b5074142c11035009031034010208400c3c2200c01e40207403608492510b0320115082041c1003210640c801010740c41030080000300c1300041d074000d0f4000e810903038820f02c440d840c00d0300c19040300049004e0345515810003800304000e030340c641d00100640e40c42030002c00488 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 568179217 1250 568177967 568177969
    0x1409040908070b1b0705070e1305150a06060c0203031206210c010806030d0e0105130f09090b1305070509060117040317100819080c0307150b040b180402040605 70
    0x2507004031a0403143c800c0e08200348111070b10448000301d401000441c020b818007643c1d44603184e031103070b01d40702c0e491412100380c0100e0602d40d151904511403a401c6401c4803204002c071827004401c00720480b040d50501d80703480300c08034110740319540c1c40d500c01d41c0080095080040850015080c8100a08941c0d0310414402032000f1011002418103400c04110002c1d00404c0400c00015001c01c0d80181854400c1e0444124110323440e41000301c80066550070318020392503c07406c0003041840300d83c1d41c01c5111400b240440004901d0015040702441070700c01c000308640c40e1203200484e44000541c01004003c1d0b0024181481030381400f00000341e01120505d170081032500201058001d50500fa01c0541c00101002014151290a0382d107454000c20003030080350840e883c3c07100c030342d44400203810b01846014070101ca82082c008000d041c0d90000e00c3c00b005803581d9000303a00e810020740d0490301d446100340e414000024070f02d20b494465a00c031018050b010b80140100254280305060303008100b264000e5803a0390200b85 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 568180467 1250 568179217 568179233
    0x3090c090103060209041d03180604050d0b0901200315150307030c020c09130f05070b0f04090c031103040b09010e030d0b03010f06061e112b0f14090409 67
    0x21809200d005a4a02c0b451040c44113587c0e1131422455070b03030220300c002a9041c50000446080c25102d215080358002041e0000d001442582c0c46684c0c446206c80c40f200030300c00700181c254021707607061000700314554107400880c0c104140400d214120303107001d000140c0002002030030f04104c0c01c00108298201c4118200c00000c0f0380058900e44006680d516004070916010050f140c0700150403200080d00e840e0400041407040050400206032901e0007610a040242c01c014200291069003505030301e484070305c554611a50450b101c0e108241d400c20b8868403c80b4064400c40d00207090240d100d0b8038541e40d82d00c0307181140c2c00140003030f8007030340d6038240640203003600784041c0031a12055440416800c2c00a0100350a4445a500901c01380340340034410030a103a00300403d4584042965180510140013002c1a11601d40b064512407050041980304035100e41d51072500001041c400143d2103040c0d00c241e10441e0501c0d01500003801188103950fa08841102d0f940180103800402003011852000d195a0342803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 568181717 1250 568180467 568180469
    0x210110a0206070c1e270b06040305010902090c030903030117030c07030303150f080a0b0915070207151707030e0a02060f0414030a0b06010333030302010b06180603090c0901 76
    0x106044010020f00542d22002040b524048002a03d024081d0404046c0c24001d40c0c006a980c0c0ca0030b11481d001c1c055440d046c2c0001b8122400244100d440d96031b20708109010344090002284511b00c2c0d000090f0218a0310b109490040c04401d00540c2141e0810b01190849004040d200c034036448244880e9454100800124000e948030f90b401003800c11074007407a01a0020079070000404004011000d20099400240c03112080380c00c0300c110903107030f140c9480c81405e21003a07644a0683c0000102001101900011484210f80002e202e003200600c400d0001c5410341448106010001e03001c001141c10103209401c6446000101000d50304180d01c0d560016107564031610701140003d00c08501040420b107404504c240c447c60031740241c001c0e201207649084803490014016411b040c1e480d1990b5044100740301010720501c4c04003d00303402d0b11442242018824003240b00850056092100010b5181031603003c0c1d400b2203007104417680b07012103140100825600300402603030795032103504138544160f910000824 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 568182967 1250 568181717 568181723
    0xb030f011e0b0714192012120414040506090711100e0a1a0403020a03080a0f06260c0d060914060c04080706030207030503010e150907030b01020c09040210110a020607 73
    0x441801c2060f81c5080124070174114038200b43c04245180419200c800d428443c8041c80d26205851035070034001100c0940007112174000344a01520201030310321400042c020b07a42c068004060300d02c20f1900308002d49100319101074105014070041807a25011f41d14104003026243d06a4010308078090b015422514448400d040d180e04c014030700f0042c80b5020300c9941122902140c04d010303515042d28081d503605207600004013008500c0002840c0f03d4141e6110711000c00d0300040902c00310b9138994105001407050042108120000c2040641119000421550600b00600f0103114003c1c69100c0200410700e0002c02c2da00422000440b05192806000a03407003204111800d940322400d06a0300c0c2d1800e1083c2d00f1140c20b05104101c2c520220b034105003628112000440801402d6554100d4042c0780d0110280c2e00d5000603402041c4801550141c106055a60080e400c44000c071070301400304030414005443c040e4120303442900408d0030502c07501d03509040d074600724211000c82d0320642c0441c0099101081c15 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 568184217 1250 568182967 568182983
    0x11211150a0e010e10050301050d08071a07030e0706230403020904030f0f0201060e0103080a1b2109030b150a1203090e010b0c1e01060f08030409060b030f011e0b07 72
    0x302c0700540c1c1108042842c103609440f8000d400b0718040c00031780540700c1801402d00c101145003600e0200710091045403401584041c46450700d00d46814407500c4604152000c0000c0390500d28010054a0300042d1241124659942c1816209407014a1204101003032041e404101c3c0410004c000368032011100d6000d58826031764100842092000201405014040c940841e41004000c1100a4070350441b01c2c152500000100e0b80c03100304c4007068070a080c5440c0001c103c44031030705020090045058002420405240d0a0071940380074035002c440c80d131181d020040c403140c1c0308004a40d13802c0304509001e000e4040074125091998841d1480005481c940504500041c1c101d4021701200e5086412180180140c203500c40c01c0c40d0150a90ba5142c400081340030400c0548504801481242508000d0003082c1c03000c10a981262500c001588a9019000d02c881003424a04006141038100c0e003213074172036401c85c850903017582d080c58020041280404000084c5825517100072400c41e1065008041d054426200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 568185467 1250 568184217 568184237
    0x20103231311030a110f0103020d0c1e0509090f0907080708010c0906170f040501060504020d1512150b0f100201051b0415110307080406210203011211150a 68
    0x403540745203035a4049000350400c28031352000410200d07004900340d008895050b0090380200040f070081c0110380305d0015081c00e200381e41010b903401046190341941c0c102c48523500040703001c0d8161818403c040d100c640140d2140b002074005031000c40c0c440d4000442a086c0c484480c1e9070b000040c0f40000c95041568075964411416007515006030b10b4500a190500f080d54030319900082c40b541542c0300a00c0f1643c2d82103420000b608016007036001c440585001081151200d000c6c10340f10009025488030200d00000000c4040f419161034108446c030154001c0c4d07501c10540150001d90003500f03c818901c2c0c0c000f10386032400c1c0c1459032900c091407507031280d40e8000149807074024070404601e51aa6140504540c080100340411151403600501a18150034044002c48014581e10303d10300c2503c0c009000740300042404240d4960100d2180038011100350945080d9a080380e104040744005c1c401c0001030b180b000d80450014018031400c8410580051280345149090315115016174009100400090050340d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 568186717 1250 568185467 568185473
    0x20d051204062309120f060112020a0806090a120905040501180c0c210c0b010b04080601090b06181c06051806060609010e060705011514060909040201032313 69
    0x2024505040d240c0c421034905220100b14070f2141e200c0d034421203004044d07038265020854401c04c41441411401811248036682d42c203040c0e11171000d00c003012441101c025000144002000514501880b03484014090350314042d541e1741002158440542c1c10300092080004056a980c072909008001c042010010140d80c000e4090444643c0d840c0e12040c04107200f1f040d004155507845840060520155044065007c04801d0340e081030f65a00040c401401400040b6101210314040c10899108000700d916130303603c41024405540005601d145c1002090202e001d00701d11030364650117a003102404610329840010360b05000310060034000d894154a41c0288100031404031904038441403110301515450510400043d0540b155408042c1009100500740c11560341e180c1c1220034060703000008000401c80384201d003211304800e22a0b1b00035000b0902d0010954208441188c0c1d00b420000c1450341183d0b2264015130051041e030b401e80c4c050440c00030824a640004001c1c480c020400031420961494080c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 568187967 1250 568186717 568186727
    0x17070305010f210204020f040801020408010f0e1903050a0e190e0a020f1b1207050d030c11100e0106090e03041401090312050703030b09040303141f060c020d05120406 73
    0x64004107006900c0242d030002401c0b40300e11031040984c110382c003507940d442c9024120050b01981d041071289510014000880c1c480540c40f04881104185061042166440405e5292907c5216082006a08640500000344140010945003100742001c01d5032400e102c0214821600740100e400142066807414440009440050307588403410300c2d020b61500b03040b545250040e000c2c9a9018500101c1c103040d59071481400c0c090f444500f40c80080041c0c8a105a0a15981d00d420750010b040c04030303180c900c9440305180b00d0303111014401d46110082c140d40401405000040070306540c200081c0d5a60100032a000e2030600520320100c8100e0025600d484c2441807451802442c00f85050500035403607000c000142401d1540d4092030340300e08100307484456a090603009403a06005c0306501020300c1041100b055055442640c4c98030848840c8466680c40788801e0000682291030007070401500c0c48104006841071a0711105284003401c105199101039a421b441c180b011000103240d102d000c40c0902c907069002c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 568189217 1250 568187967 568187969
    0xb070314030705070609060204030209071d06120c070606050306090304061e022a0604031a132609090c091906050906030a0b0306070806041103010503060f0717070305010f 75
    0x580002407450428400140c0203101d4281c004125540300e040c0c690030311419505640041d070f005031a4064919103100014200300411200d2001003c52414805407802e210301078450240315200031000640b00c6807404c003215000a0003c441d807076292500401c172a00d041c00130b07502401500c801191510700f0b040001e4603203041011040034103001d4250140c1000d500142400c405c00c9541054400c9060121140701c00841c40c000c031503008500010000b0810945072105c20151040c1c81c0031654986400800b48031110f1171450103094050765600d0400300c7e5481a032542003d210652403540307464600800305600c018105c3d05081c03200008201d0700312a0415402c0168002a00446030481c51b0501e10040c0c11401103007000e600410300800041c2d070100c15030380090a40340000b0104c0d00c003031500e40ea00910b01101200c001d4052428004016940803070041981d05031a0004c024000f241c2e20110f01c04014800100306408000c10842560340c0801290303081c0e8007500c900d80e0302080d6503040a013426400135076 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 568190467 1250 568189217 568189247
    0xf0b03070512060a020a18061e080f1f03060906020a08060109030512030601050c0a2a1a031f03050703030e010c0b060f03030903030d020403020f06070803010909020315010b0703 78
    0x1600c038446801d0400300383c0f40e03401070482d480180c851030380724400c40d08841b0b0040c4007912442d4146c008030302e81c1d07041445250341c41850007080d00c1400140004558004003628070f0100041042c02040703814005082040f42d60000c901c1d005452541d07900c40d8020342d121a80240e8585600044000d08154000c0c000f50f4000c00c2801e21040442c910742e20160742c5c00c110806544601d0300400806c1442e03126604581003003840008440760b4171803a0070202001040540d07940a00403540b0807010380c0b04032510504080b15650110101410b05101048455a0008240410b06035000d08008542c4142c05040805035015500805c1c4041c01c51030050000400415941c2c188103813020554005107000f00342e9680410261400584503a55002191560040d016025130600000c160f10481b07071066400740c000c0300d0003110b5410504001000740025403140b00d0000d8441e610800042c0614841074005000b4140302030308803840600c800c20f181d4130740f0100382c0041d07507030f18800564041415489050403101d420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 568191717 1250 568190467 568190479
    0x2160b10080d1409030c0d032105070e061309090506010303110303132012250f030f1e0f03030c0e0108070f110d0302090a0801140a09050f010f0b030705 67
    0x80c00e50042c125003c0700e4000220341d80e000440100740c2e00c2c2440741308000301015040000da400640b8006d0641c5518070042c00c40311811352100741c091042400741c05d00a01840c0c407060011241d01081c40300c0b6500c20b82901440c030201110014400700b091040d2100d41d800b80e0007811055055150080406243c80b8505076280e0003402840225031071103490504c41c0d98407409901c40d841000e50b83c542e1741e030110901283e1008072004984103840010442c100040c220817050403440799a0007220768440468090360000c149846418000584042c00c4242d40b2806044001c000090455841591000380c4c07508884404035121103904050701070181c0d59012001e0300300610380d07801d01d20008040440040443c801c20201c0000001014090280000400410b00582c0d0603403034280300280196110b01c20207030040030000070024200c0700c188242c180803802da4044103187c0e12101c500710040c025104007070b1860300952003600d5044000b44226240c4040020300400d0540d00c0400305401c207092988a94000c0c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 568192967 1250 568191717 568191733
    0x30c06020115140414090d0f020f03030f07050d0234050d140c010603050a020a0b040609060518060a0801050f0d030503040b0a02040812030f0709150c020402160b1008 73
    0x800701040b101c069441c09900f03d21190844000980600010240074480c4d954603030500a04e0140844c80080c040c44a8032441030420502d4402c903620f2030b022031000b1301d6030802d102096100004440c99070700f2002d1840d0250071f0040340c03201c007400c84c0c0c040070410103401001c80303000415210818200c40351a44488200203021221b03110030351140641c1c41100d040040003205044200c00000c16641901803c0d002041807513242d20f055543c540556405a07c940c028160000700c0c48444c904132070039205950398812030b441c5008000e0b900c40d00241c241c01c242d064490748103455a00c0303907006460b808041d0b94454805500d40400d0240c061466800c5a00035044490300ca008283c006044a42040c1d00c9541d04006030356820101c0d000740140c0e0040c40850055801590517020700c84061402000b20600d003410a494540c1709560018292007580c15440c00354000d010313024016103102d44c0301c1c0e00180c000f600c0c16400024103400001040411181810450103000290340f92982d0320000d41450f10080c4918 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 568194217 1250 568192967 568192991
    0x50105010215040201141b060606091c030e04050c030f0106050a090513060b0703051902060103030e091f06021006050301060f2d0b030f1005060307120b0306040606030c060201 77
    0x707000c1e86614207070b500c4804000ca403c6900c907201c060540c0201c0000c860302d801e0506a12140886100c9884140f403081001040b07841c50a4001c540414000604001c9210900c07003416180c100007080650510908140074506611a805214420305808604e2030392843c1141890aa184060308a031041220501c068000c4c1900519041d090f643c0845403010001c10700c1200c7e101410b03068100001c80000803034283c0c1016002405001c000c807845101440a00d1141c0742241c0c0c502092001400060342c8100310800c1e4113001c001650040006c0791000c01c1e0800e00d04024010f1040c55100600681c001c0041c2c544c0c00c0240d1148101900d001c030000c0c8480d51829042e03404001041c05500c0300640300040035165401c18000d02044c840c83d640c100d008044d41ca0903401c41940040300c0c2110200f680c81c0005130003e51004040041e150f0040c00c0301d040d43c9a81000b1076000c4501e80c80e4151182e0b0350806c02c151541c04101c0544034034482d4501243e59411840e1a00c08004580d0040040da81406011089 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 568195467 1250 568194217 568194223
    0x2031219081911040b0c03130e060d06020702040e150601020705031605060a05070501060320041407080c0c01051317181306051314071d04050601110708150a0501050102 74
    0xc0611120004110f03880d0948900145100726401981e00c403100241400b400640807003e42036102c0302810503a104c940c1c0d000c010705048403c43d01e056010400c036981a00244407a405010168009440014449003407078801d03150a10f562054041844641d003000025a410000d40025240560107062030542008500301441114001c0c103101311408506c020003507101d0b505403568141c100e0020311141d696800d010b200703c13104260064a5645140280a1604050140201103000c0d05401c1029aa1f071040444000c2006019522006010444064090404d0143c64003861891200e400501d4503450301c2c00100040d81c00348160071200b408258000c00c0580202600810107071200803400707020714441d40c010b003035540216911040034180d1995204140d0307c0108003060341c0d0f085611341e8480000982c0c3c20502c4201c0d0f00c00f03034448110507001c2c41c2000d800942c2c100d241070511848819041e100e103810306a154003c4032041c1d000308016400080d404103060341181c201c0604001b594100780000f91 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 568196717 1250 568195467 568195501
    0xd020a0f030219061a010c031b03031112180601081c0903151a0411090d020d060615080f0112030507050f073206030f0907030203121908 60
    0x44000d6400314881418000d001c1c0c24040030740140385000140840c90400000d2440b2800b0084412001d107000046500440040135402d406446c1e500480d03500d42c540d00070004d1603001c2101010344401c0c21109002c0d072000500024403203021000e03032a1038081c03010488802e804009070042c0d8885c0004000311600030400e192201003818150b0035008450b58241c4842e47e4992004201d400c682d007610418034010703805a1094101d2241c8552a1480701c02000151110051a1640b00308104000b02140c035086031040d01c0d0910260041c2c411a810b07484403000c450260344040f231b05844800000e88401e42c0f01c0f0035254400300c8204443e00d99418070a0740f09505180700001001e0150009805050020800034049480a24130403281074503290101d42c03c10b034080e85d4502000e205808075541188580280d01790800c00302074161400d50392054041044044041c05091541c00303540790100250300e05024641d500c005080c2c2c1240c0d643e001000d061110180c02a1250400004506000c8031141030041c0036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 568197967 1250 568196717 568196723
    0xc0f0327071a0909220b0f0711070f05060c0708010606170a20030a020d06240305060607022202040303031d0303060f190e090105070e0114222d080d020a 67
    0x3501005c00e0403d00c80e00302140c5070300a0140301c4100b08208042c0080307001d0718031500c6d150366214080300840d9055070b40c509540c043c1e420820710003041801181000d07406080aa00900c0440700d81c141d4510780c1c00e00315a00c68112800040e0300204a800c0030005012050b08510811410400e021402104440c44ac0b500800701030500000004103040d945a50191070304001100700800c4034941c5e8030000d00036044008100780c850901e40a404100c540203115144c42008044d0146180c0313481035080000d10703c0d0900c0505540d40310645412415080c600c068009184662000104c80020800d141040c8505680251032940200104400c40c0c440605c0f6003070681060350182c0384148002003036502c0d00290303046413135820440000c102400341c05400460042c0a580c90780030010070010011284050030581d04905070004200188107400400d040e5a9805906903c1c4902d003616a41ea030b100094903c0112550f0203001c0c0e100f42c003c0d00070010751000030500c0d040140105045408007a45600300000c000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 568199217 1250 568197967 568197991
    0x60203040c0312090806090106031a062701031b03030c030305150319020a05030a1e0303020412080d0509061b070f05120304060e03030c0f0327071a0909 67
    0x3140401034030302518800703154054118000540c10034801400340301a485030002034400c1d1303800301e08030742018401d41080c0c81d044003080c2c81d100310008042a0f80c8401070280d85c0c108103d80312001044240d01c1c2000740b17280308114404000d501d10300b041541915042000d40d0b001000c203504000280c0c00840002555034103007408200c90381ca03a510002080180d46007550580140040b04962491140218071424800c80f20a100c50b91540141a524801e6140040200584004180540e07940c03c085440d01c501c245030144c03601d903c4950b0011301010f16401141c01c80c0001c1000d1803013501601800e54020365a41c000c0020b454040318100b1000780c0103600e4014a44009010001d00c20462944009150080b0451304503400c1e0351001d4445030310032a0265030300c91078805480505207000c01124065034490a40c04d0904110356906040c59001030a0f86030301e10610100403100c14010000030448a803c040501840e91030100c03a48180c10701e90700759071100c0504001c1c1101d555641c140542d0000c011b9040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 568200467 1250 568199217 568199221
    0xf030f0318011d030409150503030702011202090d0c06120b060a0c020a09150f0b03160e03011812030b01110a0803060319050a020f121e07031b090b03031303060203 72
    0x80c0d00d004181003580b000d83d0640d0709240f03241d8000c002000b0800c590905401700074004020458244003034060083c950715030402c200e036002662045080009601e0203000c01450046001d001544400c0384100885584985910030051240c12081195500990b000180600d0390782d40e0010b0200d10032a103031038042c051031410040642d1100d1070280c01400541104002c84004184080c0c02c600b01c81c13050105c10390401c48085800b80030002660301031074801003404c0c2d0110240074180c80b407001a031702d615055980c0b05003051117070701c0341441c5501060103143c0b00c4514035100c402c024161045500d1042c14041c064042c040c00c3c0c1000030b050848a9041040c0c6900ca48442000900340301c07280d00164035044603c100d520a21001040110a00384203d03240012409444248800c80c0d42d00c01d20503855410101069284080030003d4004043c10501983d54041d01c950b1840c100030700c2d50b00c80c0b82e10100320540a0020708014890701240050442c02103082400410222820300034900004103095000700c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 568201717 1250 568200467 568200511
    0x110703080c0c0703060501090b03072705190207061e0e031b03090d082106010c0b27150f0609011502012a020105181002030613061203020f030f03 64
    0x115011359800395060000e0350303643c0003060181124008580c8640180400081c1080d8001c00804500b40219440b140800e2580e4505000300001041810040d500c2c2031242ca543c030710ba10051010512450300080c452020000c590185143d840c140c407100362801c2012280c01c00000152000e1070380101c50380241102d07501c811380c00e6018131481140c002a01c003808800b0401044041c28070f4080c0305001c480e110007078026084243e10103541c2c07a130108178141c0c541d4001ca0745080401e076001208911224110143c8140381c006080000074807020f030f4000801d4281603001c1c00740b043d504074021513048925800c01600080c403250043c03080c80f05107040402c2207a00d1600030b40141405000d4086c002c0c1900c3d84424206050304030300700c00f10303006528000c0010040c0c20f40700310b002c882c7c0402c203006002e0740c00c003c55460001e40c00600600e070300512401c4468200031045c010a4050039004a088550017903070302d0081c3c6401041031420801e0380080c0300c0c0008040407582903a41c8204610b400ca15180c2c0710394 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 568202967 1250 568201717 568201723
    0x512160c0f11100807140307051b120a0302180609150d060b0f03010e06010f2a020a090b120303060f2803050c0102071a0406030b061912110703080c0c 66
    0x280c00302c3c0d080380103181503014064000e8001d030302c50001a280c2c4102ca81010901c60a248400c5480d200400c40501c141c2c5181d00d441c9504030820680b200844192008903480000c6940000b0300190000380c0024141104070000c052560014406403420307800c20042e9000201d960326014032403011040041035a0403030340c0c0c80f80c00c02c070300a1030f0400c00e003075580e00046034074010350f407090050380e00f088a02c1c5d004c510194421001d511004d102c507a05c9c920300c0c030704030480503c448008a240401840700c10341ca40015907200e4248030010b2040d0340b800901d001e16030301444205094400e00000ca50000c4c01040b099850342d40400e20004c404441711440c1849801c1001d01c5c650710450b42d685103004100c404020000c0000b142540d00a0076002c4500203a5035101011956482d03101e03000d181d000c28801000528001d03000809e14000041510342070500c80c0d900900b0902a90b940d000020300320104500c00110716103c0c0705024841c00148030b14103074050b1030107001e481020b0a0380c0d01c441400100c66403458018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 568204217 1250 568202967 568202993
    0x709150b0309060a0b030606030d051b030f0a03110a050d09021206160908191b180218090105030c12010e0f070f05010305100915150512160c0f 63
    0x603061003900c0b42012070100d80e48400494110440b1450084019260310300001d043e0300c02c150060003441026000482200c26402440580354200000300c0348070050101407000d0000394205a08181d110020203c0040507190040e901c04001807081154140c5250b0080c220f484d40200c950021849025070b101180362011447c0d1803040f81c0c0260403d10007088610741145901000039919030f40e9054540941c1d0751209400d00b5940c0e03103840c80c418850001903000e2085ea40040d88400e036400440c1c1c1e1b03104401c200c82c6100d6015446180d000820711010380e032001d8040d402c03c0007950210354079030600c0e021a960f4003002460b00d00c141001c0c212103012020035000380380400103101c20b88551150100301644e035100e6074040c14000c00c0d1521004034041d4400c0c4205031203820b503509102085880c04d24101c000307100d6a80c480300303a1192a43c000c0341d80c08094010070202011036580030395070b1000120800c0b04080280c00e1448100c0300c0080d0301041607003d032401d45800c0d084040650942c40c2441c1ca8181d1541d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 568205467 1250 568204217 568204229
    0x10e04030e1c0602180307140409060b06070b010e070c0309090e120408010207140a0f03140d050117011803020c0105220905011805010609261221040203070915 70
    0x200c010b1038410003c1ca6005000c60000b92521011301504180070035072100341502070001c100602c00c640c00b1803840d02d60440150103015110001d0080110000300d041e40d4410002900d403a00700d8001005410141c0325860fa00c1500e40c03500094410b010b41c1c0c01480403809110f900ca049481d10941d9202140c00c0c0b185840340400c10507100d50300c65a4155640c00b0350041d900c2031700c3c40c0204c1640850b215101080d0021415800050354200464603902680c2c07038402e01d25800080362080c40740300302d1401e0620915001e00403842809021402222400b420741d5030400070008180c8041a1440003e40c000954024291003401c00d5500c8805a0542c081080d01c15150034101100c0700100041c5106580c1c0070905803020317015100b0014000b405403100740d440a10800b000038011240420182e10f201410b6011a54400c0e105120b04290300e94451078640030b20500c0d84107540005d0880036000040c0e80a407c400d001d140c0750306542c640381d00025101d2040d44200c44066458003d60740c00707a82072000c1c840c09084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 568206717 1250 568205467 568205509
    0x30f0a1407200a0c05033a021203150907020d09180221060a120c050d230d082a0f0c06040302030a0311030606091002191103060c03010e04030e 63
    0x2030380c10302d1110700450b03104007402405405070000800c0030b061103000500c0c940c109146030941f00800c1408009001c0090341085001c0d0150310040c10011900541c021211103442c100e9400c000e01c104040c40348064031030b00070f543c4101c11103903585400c100f01504442c2c980d201e507000c80c802c5030005406072007035155401c40e20440f0b020044000e0404403c403400351a00ba1740a00e04140c950014603003640042c4006060282400020401490826045c02c500c61044803440c01c41c000780101180342c604103a4000180382c20440300e280301694003235100c99111024159400d005914038265011540c42010b4030664407100140b80d0214139104402c039180b00c2550703000c4500903e024100251079400600c03280002904044444460801d0030040d0ba000d440001c02542c900700c80e2904200c60948102507000c01c0d40221b08841001c1d159040595910383d000b04140fa0041d0240c0b42094208100186071080b0103400b40010710003602c03140c010300d5005a042c203140d0305c80c40000c80000c0c0110b0248805039000340d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 568207967 1250 568206717 568206733
    0x1c18020117060f060d09060b01020a020102100504060902040911030c0105090f09040c0b0c03030a050a0c050901210204080d0311040e060d0503040308040f150801060f1b02030111030f0a140720 84
    0x8405131b440400802c0c0286c01c10000c40c0c0c00c4100481c3c456001d0f80010740184d003c03c80404140031243e1006820a124503c00905144184c2c045001d40e03543c20340680315403c0040011005090a000005049030709281c01d034130707216103c80010030008030b1102c6240201e50301e100080400c6001c80d03008000e401c4260156445d0f80d0301c1d81619a480d801110807655440c14200030a030f103203107240180c84510741e654440c907041c071105100440341c41540d20100c006400903035084800c3c0d84194401000035110324000303030080d1040c00ca000303020f643c4480303240c9002c140200301c00c004410001100130b40258003154681c01c520410304202e071a50140b5040500402c1d000100040d00d001a1300d020800c941035440700014400c814034044e034580409100302c0002c182c1c000a40c04046100d5100e8001075000301c0b50b030300ca1048203a008603084400040c00000b28060010900064040c190f2800b917205060031414802e03004041207503a2040c8016281c2001e02c03452000e0800c81c04955208882041600301c1141c00c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 568209217 1250 568207967 568207987
    0x41203140d091205160b090a0f03030b0f0105030103020604030206340b01050d1106030a02071a060931080d05070c1b0f03170f1c18020117060f06 64
    0x140b611100858058003101d81d071410f01c41c0502c007580c100420400030100c41d44084c2d1074100314048000e01035031081c0601c2d82c004d00000d4464648188082c02941c0000b0300720501c005018070984122840e90510005000410059031032504803416a03a041d00c0081d1070780300c00c0e02d040b0004e4222401c1d030703403600071241d512110039458142c801132110301440741e025459a8440c00d100864451101c054200780c015010021141440001580c00010202c801031030701c6459104d40042c1d10307c0d04240f15442205806111042c50712540040d000300e1032200091098540520003c04104114a020f917500800341118040c0950001550f40003108400700380060700d84044002c0c106101810121140c103101c000301c5840131203107a14a07094801c8a100d10b000c0c0382c219224840320001c2c924035000552410021001000c1401018120982a005400c1a500911610881580c80c1c40400d03029101d460704800c0c0142c1c0c0e10010358042411114095030300381e00c9040104011751114982c0680001c070000310840c107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 568210467 1250 568209217 568209221
    0xb060f0c1005090d030c0e1e031002040608040b0c091804060f020c072121111c050304060b060c030702090108210c1c0306050301051506041203140d 65
    0x558690300a40d00e010310740400140403200191100c0c1c1680c2e100c0c814500015000340e0256110071450b003000da10207500d1000103021201e011100c0b0000740c0622088000341e0904100c0841030242d070560540c189810490000d090b100b00400c050315102100003c5119009801d0840da140c1d070740030f04a400ca2040160b0704800c41a0103840c01c8130b00310b10308203100792031084a2007990b80201c5a040900350702803905c0d2503018050f4060b00c8400d0008880901840040c41c002d00e424a00d00410b40402c01c0700018800291103a0500c003041419600040c1110781d5034961001050122402818016200d4540d41428402040e031034800542000c00050108244030303001000e0702003144210f40103044d5030f07258041c0d1626480c0401c0d501007820041c81658404c40041c01c05001e4004c40f4004941e0200307410260000303034205440c0c0075004207541d040207000508007801400c1e807000c0c2c0124076041c00d40b00000031410390300c100e21a010764204981c103850101440380049507000301c084c01d0003540b0f4550f0840c3c1c0c0d04c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 568211717 1250 568210467 568210477
    0x60c0d0905160524090d020102010e0114041e030e13021908062103030105040c02030c011406130b0f0f010203130f0e01151b140d080414010b0609040f0b060f 69
    0x203c9400c568800f04028018148050131060300102d019080030000001d118468240030002ca05554135030b02001a011001d01c50227070649041710341c0d264682001d050003c090005144a2010200e2009100b80407a40059a014419070250340c0e4504c005503000e142d1000f806020800f9011120400000c0c040c00d1788802e480d4090380d000c035513688110305824032000400e071701585080ca00740c01c2070004001500d060f610142483e055801541d140c0040b22001500310344007007038130105069600081c441507081c0004a400003001005040140d500001c1c0094406011070100b01e1242c1003c0c03560540301d91081c4113542c01420210881c00500e5241d0320103e10320030543c09510303c0c0043d003800024040c00640d800710040243c580b01c110101c0c0500d0f01d952014948070106903041d43c1c1d902010b8005400c10400b840b80a48540c0d21224076082c03074501200e41e01c0310100f803e40243e04004400348244c2e034001c02c540d10200c0445001582002d00382d40500038001c800d462603402240440c034140c140d0306400040c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 568212967 1250 568211717 568211719
    0x909070612090b06060d0605191404050f040f02011806050306040b100c03120207080d0902090115090501050d060e1e130f02060a110d0306090617060c0d09051605 71
    0x11101c1180020504102e641d0010081c20100486010503040d04100c001881c400c0340d00c0001082c05511500400c010104040d0b40d581c41d01402213040141c4200590320588040e4111400d102e00e003090603610b0719a004c0900041c00003051045020b0440e80100e28080c0d01c60000c402c6801d15a945400181c00c5030411600540164104000c13265a494480d1469541c028562514174a1582503101141c801e8150074a200d4102d50070041e032000f0035840800f80c0f82c801c50043e000700f50840140b040c802c000d08107a10007a4404003034800c80100b5500b018060068803401c0ca4960f446d062002101e1019040d6503004d6004040c400c024045000c00c10101142c00040b07401c00d0000c281c8905602072055440218041c180007000b1a4140052500c035006014400a81c03400c80c800c4a59490755500f045442400100401d5441c6020800340b0038034000c0000800e1280004c17414504880d4045850364001000846280c6001031811200281503101080144d0008212036000310100f10b034001c414000d000742 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 568214217 1250 568212967 568212977
    0x12150f0602100608030a140708070809011214070324031407080303011a070305070209070e030c0405150d020d0c060f0e040c0207230402120618040b2409090706 70
    0x8915240d01a020f0a400c494035200218034000340507404452000048008a070070300300410050740807483c0c0c0b00141160340d0140321419901e85d904800500f54645485403040118100074501514000700c10a40f0b034410a1414003003800704c200442d03010320226500380500c1000540c6800b006102c241c40d20150103071f0300344048400a80d207031080b003540c03800244280d0080f003a9002140702e15070141c0001d0405144603083c242d09203e020350000d41703800c900b200c0200000340601c5031641d0070300e010881c0342c48180c02a5000c1081d410b082c0f0300b6400f505004c1c403072640182c038501104421510344a60f50207081d0f0700580300c2914a41c8814000305400f0401a0000001d03140e1515034410389050300c20007004071590340090115500e0141615a071103504420310940d806d20008900c0d45071601d0000f414401c049218098a03440d0503010040001c10088000074956084e01c20000014032002480390400c3c00b8001804494901e041c04002603039034200850340040c0101c0a01c04c080ea80052000140c61940d166 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 568215467 1250 568214217 568214233
    0x11030d02030f070801030b0705090a1502061f060503060f0d02060c0d020c0f0306040605180717120703050f0705120a0806030f06190e0304080a08030a0b09130312150f0602 75
    0x8441001082c0005081c0741f40c0c1c0b80c00316000900400c01020b400101410000b1425920440d03107035200880b030380c50310140c5c01c10004c011051aa00044d940d081c4410300b2603031344e1281068001821400004c0107140918845107580718642d80703910114060b2a80101540e0f510f0710041c20150b21032049920384405445608400045403401602800c000b000140041600c0c3da210303105c10000d000d01410010400105039024494280244100c002405000001805e0040505106450011038409081020805221032000254000304503034088441200d407580b2442e4609009052140e8201518600640003c24500c400d81000007a4440c5804905499480c64041c1d0001d40350f40c001c440c82c0d030104841044040f1071480c0ca601145040c5142c0c01280e05154480c44e00038a000540780c420b44075000b0100030000c1944882c040c1048240007560395200714100301d041d60f1044503240c1001400e22039a00782110901d40647e10418401809400b80f00c140b90751005100352954050050740018000c0b020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 568216717 1250 568215467 568215481
    0x406021201260d1205040f02040e070302010801081c1d03030a080906070206070e01031505030a060e1b0a0504020c2416021203010501140708040305070620070504050711030d02030f 79
    0x38401c0c41c9030341c3c0e607250400380d40d4a640d42c4000420004000b25040c2450104031005605d50340320704140361035108000e0103038a08500024140c0304050380440d2217640060b00750705800440880c9542e202c40e00d82008142e09d01315000034015800403e1070301d80c2501c00418060f80c0d03d0351207013000d400303170320b503602561841e440300c030000ca80b1030100b20b0310b40000c26000780d03000341594442d03030000940c50000001041c803580c0b19000139042c81c03138042c0c050390010b440300c0b001d0303188440921100c06d42d0b0004000f03c0d0300d10101d400103d00c1c030864a01c6158415503002c1130b483d015807018000313002c403200d0f28170300568000f142501100520b1001e5403d0110062503101441846000198042000950b81250307030031a840c0c540111980440e800c1c40200e140710030b0058500143c0081c000e8409180305102a007107090034203a0007014040d611600184110b02c0c8040c030602d131000407414606844095401049503565004240d48a003001d0740070002c288400211700d90680d17540c5d03000d540100135040044000b629964 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 568217967 1250 568216717 568216723
    0x22b09060f0f12020702030f0a0303060f060c0b180d0f1b0206030103110d150f0b150a030c030e10050f01050904080415020a21020f01020c0c09040602120126 69
    0x401070300c04112010004070800303004600224030516280381c003515140c2290b001c070742408100551030300c50340d0040040790105909405010003421034868020a41c600d48800148a41c08100c0d0141c145c2810001081880004851500c103010f543d004450b42400403c1006005540c4010780c44002100c3c082001d5422a0100003100c015400903c0b42e81075900310b8845183c404401d2001903840000c0ca207000f000a070307801408048080100c3c4000840341d807944002015035403034a0368a803188001401d02012192848143c600d1300f019840c0001d403041040509a00501031500310388000c1c454410004d504a4040d0004d61141c02c10014041403640d8500502040e91425100100703036540503c028002f000c1d080104803e4094588101c54982585c0c2e00d40107540c0d0400c15019101409072900c0e0502a0740410074030b1400040480214604190480c1d225201d4884070401807080b808807001c1414010540c0503103008442d08180c40d101540c0d5041d20f90041c0640381c9140c0d40340c001101d00542c0d00c0b5408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 568219217 1250 568217967 568217987
    0x2010f08060604030213090606180b0108060112050601020a08130609210f1b0b0901020f1203060d0201140c1c031509050a0207060509061e041e03022b0906 68
    0x50b00290030f050550382000b48680d46000d200800e155960b03990004030f61503004040c000c001c0c1c1c404884803500070119007402d46010412541c14440180c0a00402c0c0e43e0018411305401082480010207854100040307060a808900140c800704012501101008600988004840e15a2a18100103aa8107a041022860070400440ea00428182000400c441001c4c041003a40300340b0141c510b80e0b000c101e00030420080c030b030000c1800000c0070551001e1941c04001e1201070211010041a02070824485a1140c0c4401010350340104100301484046900131a0007404051a141505407a00038404141d80ea0740400085400c6034421078001c144618000e101c1c80704004000c10581c0496418080b803000902005000516441e40c01c001c414040303521886035900a00148003e8080d50a00041040c0d80304014454800752a410b44207102c0020007510b0744000000c1d6001c1e005a0402c45401e0030707424501c40c84030100300302e00460700c622007200744114000b20240c00340d1103104410303440308002c640c20780070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 568220467 1250 568219217 568219219
    0x1b03020a111902060307020f0106030807140a0c05060a140c0d17010b0403060506120d170c040f090b06070b04062f0901031505060c0705040b060a02070e0a0612080702010f0806 77
    0xe2106080140c00c4c80001164030a000c0d00448142000c4941c44a085800682c0140d91840000c200d6a04100d2491141c42000c070182e0001d14204000340c85a0b042c1c03541c40d02c16a0301ca42d100249058507107014404074003568161039815a00c4020f00d40380c076500e40c1544002800020085c180d80c586401c05041c0c001d040c2d07031905400f1400c1604540c0d13284000c00014000b02c3c1c2c0301c03003000303c40c890780481040148584001540c803070b030040555102d04040e00401410a540c1c1c00e034140000d0211090150720b0000316403d0480c04503241c00c2050120b16688100140a0143d80c0008200704c1809919001100606e10040c40c6144803e905142556510365440070301140c041d080165592030b61184c0c104852400d0304043d1041485c0d44d5900146441c0e05c02885907105400c0490100150710741351141c1c1c80884401d59a90b0f1815020354030003501c4400c1800f41040a02040010803a610103507400303d005841d2100b82158000051b0400700b44035080a1012800208822021030125100d01c801038000d180c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 568221717 1250 568220467 568220503
    0xc02010519020a020a08031e0601031a1c061107120f09090b01110f010b0a09061a1b070306060503100b1c0f120801060f020c03060402040b041b03020a11 67
    0xe0007041103000ba50080c0c16003002c40c80741c80c07258000f240000300254002c40f03c50646481d04c0c0d010503001d800345040100820306140c0b5011300e00411000380c1498044607801218005452581031b01110303900500c650024090610300389950384684a900700034141c0310b00825988040b090443c00071280d410000a5004c002000070404124002003600401c02105050418400d079178a03005020303142440904a1a2860f03440e405040e0712420581e040c5409800c1c2883c060244a0800d044060401521b400c0e4000c800000540c0c07030208612141c0b00c282d801c07240e000b6982030f01c0e82c81c2084e101802103405103902ca4040c0109211168009105103021030b0005056104c480c80008003040c0880c50030703002918042e0045c08100f0001e1a0f5880c007210043c185d4503515140c0d414000024840307100201c20b1401d540c1f00125051507580c00290071031340140d04640100d400400100461302902400000280407e4000c490010481e01131300a02011840340d50f50400d000b4030240340390381d0303010480c102100200e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 568222967 1250 568221717 568221751
    0x16140a090b031504030f1b0b040b13050a0605040c171b06090303031614070b0c0a090504023f01050405220b01060306061706010f02210304060c020105 66
    0x54015040054520700041c29034601111011841540b41c4045070b08078006030584c0030000c40b540d000611000400024089040c10000d02e541c0c4410900024002400c41000d01000954141050345400039141d8000103071100c085403840d05c2005044181c81c1201c10901400010840544013252640080c2407240108003030183c01c10103c40b0300c1c1c110b24000b41c1200702000703208400d4030700304011801005081945481d000c0c0101c0010098000f80701c408405200c2001000f0224101524139a080440340e100251b603000588801c0d214101c0a40c04650018008610a612a403a005c0c620408420959200c6048080644502c44200c4014401c020b4800c0c03080040c40b00c2d0070f20342e100b6580400350202020300030540c05440024400300c08000c44042c5240c0c070050150380c2d8103000b20740040000f03040c9202c00d10809106944007540090240d4100650104541d4020303200300086c2000518800c15400294903855000e00103503c1294291407079803c061084080620503c50544600d0003909100100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 568224217 1250 568222967 568222979
    0x91406061801030609090f1401050403050415180305010f1505030703150f02040f03170301060801060c051e01020706150303020309060c07080d0f08060301060b1b03160516140a 77
    0x1100c405030510b04266031180f001c504585d00b88a4940c826000d10b090030310046c2c8074688921040110790411101c1c0c1d0602e000c1c0710019070440b05a50503904000e07101c000560034200304546510b0501d880d01540b15002c2d100105019065202282c0d281e040c03075050000d02c0801e181400010f8903481015010360050f001007020592030f4140c6c4030300782d006140103d03802d000c1041c000d0998100e82c12859000c0031121040080040700b01d5142c40061454100f6400d540c03422102a1031141c0520444050180008520007000410320030118418860010044800c00c0850300d14000d4004100131240d0a26083c6003d400c070788641405c0d022a40d047d40254649401e420a1109130b41001c5c0f41c2c483c0c0d0b0700c1188404110b41720b091181003074240840e031b108000701104240c0141710314000380940b8020703498270710248650403c0000700c415044000d900c8550208826100c0c0c0d1441c40b170452101445064040500104800840c0050314054551072210b1031645a0103802d10081c40c0400c402d0b4012441da80c00c002e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 568225467 1250 568224217 568224247
    0x602060106050d0b03031801020d0309050607030b0d020315100e090304060f02070f060503040b13050c0418060e071d0903070f0c05130e07060201180f02120a0b0109140606 75
    0x3d2011425012801c0e55201c804079103141c1101c01c00d8950a4902c001c85812540d041000d6210003443d85400d0180740403036100c3c140c46000142405003010744444181c8000e44502c5120b42c2900e50181c01c4801d240c040f0010844804000d54402c0340300c0c600c0050000e90519410f092500a0005074080c51419240503070a45009018030382d44d4095004101002801d10b8103100c1c41c030014000343e1629035881c5001c3c5410126140b0050101c40072201268862010402c001804184080c0503030340083d040668100c0224a90503001009003da07040dd464034070011000f164202c121541210455811040f6011a40805400715071601c101d500520070100800e1100142038030b61405040c845400c1500d035008101d4007410100e00595441d200e0f04203502da00c00800c00e800042a107840204002c0880400001d000e28840201078160300b9414900c0e0155a44c0002c4002054101e2003120340c2c2c000d152801240f03100c0e09208403840e682c60040b5054803d0345070103442d44115401401d19141020100725000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 568226717 1250 568225467 568225477
    0xd150b0f1009170c062106150a0e01180902040806070c1709011e0c0c090204081f06051f08090d05030c030a0e061305071a031b070803160e0901060206010605 69
    0x250501c2130b4084128079841d6800180f04e042104010203100d0744030001c024114540281865008882c6141c0045408880070140c3d28050654904403014038802d0b40101c4901140d10b6035100c400602e24030000311719550360b004000700d40e8a40d0907940d456496003000d03240000381c82c902800c0d032108883c40404543d26040200300751901414034207219100c11a00f541d0380c1421018400104d5058503c98062000d40741081e8014000300405600e0641404200c58a860820040d070403260345d802d00b060300048094010101410001e0f050403c01d042c524010043e000c009000c50b00862038400201d81e118102180c00480b8589a803500d034035503203c81c40382c07c8041c5d2004017101c08850717603080c84485803170701404201d000e0601440c000c000203100d8102642803410650020401c000e5481c0b41302101d008100035643e01c08020340aa10b1030f840b88000342029881600001401094000f0803c501d0031412040c10041c03401554403419aa960b04e07050042c171082c00c3c056400507a01c0741c40100213844c45140100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 568227967 1250 568226717 568226759
    0x5161511150f09150c0a1b06020a030c180b090108040201020f0d0f1805130c1403130606051012022b05011a04140402090d150b0f1009 59
    0x440101c00850340c824820400d403402d9100c0a800c509000c070141c4100b141071590b040d40c00050341c075070805030030414483c458240704c030052203503070b50b040c845281200c4000919a90451819903440101c0780008000f0a407404900c0045010b0107000315030020340e8291041035400550788607280540c400e0042d01c691100070822411881800340c02180b140050000c0300c6c003031016856901a0406241003d017601c079072079a03406940440000b04003c15503d5490000c02c014514100150644400404940d0704284c101c074200c425200100b440700c1501418410101030740501d03400c00105840d8000c1121b403441b10000320300000c44105010031481c130581d00a14000d680c4501d1182d0030110100d85582cad0884491860316040d58036001001a81440c078640c0b00504c00c920b0b8603e292a04000120300884240ca80040c011a40414103848540301d480141c1303842c0d500715010101c0c00303084200990181035800c080c0d40c000d1240c0411504182400d0000103124009601c1e2404098240407450045505d2026a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 568229217 1250 568227967 568227973
    0x712080c031326340e01051003050103110906040e1213050d0807080d02090a17010b030d0504120501021b1011041203050c010b03030a0c05161511 64
    0xe00101104200074100e4101c08940380c000300e0320b0403607101020980070400c62500d100c0c2000074401400d0100e01000d0310140b000300c0000c411504400c1c0c2c41807035214500a496019206030208a8449001100b8103d0304200c50321042040e005500302c2c2a03400a1000402c44c0c072084d8240007580c6407181c001a44a18050800941c1401d0382c0c0d03800b45001d64156500c544c03540002140e0064050704042080a00b00c00c0d030f501c0310548150b60360f0202510a140c0d014250701c0d008280c884401034180c040b00e06601000b0403061149889541c80030070071682c81a50317075a075072034280410111701700402d0b0340e910004542c46584c286407510000369450f04600c9021a01c42d5820007503425058516454880c44100c008018441c03c60201c01b06001c07a511502005004e41081c0010840f00640808400c1c40952614055840d003205041e5079001d407106004455050001180285400d51300c40384c80940c183c026001c0b200300c06185a0410200c4515010308020101e81e18100050b00740980340d400c44617032202c012 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 568230467 1250 568229217 568229227
    0x70f0902270310180204181a0a1b0e0909011a01050a0908030d0203061e0907030f0e0d02160e0411190306050408120108060f180a02062109070305071208 67
    0x30002260300c1810349135044942c8203101010b41c10944180720581902485900009105848188400c07221129401c003021011000944040c1280c0081c0062621440c08200104895001800c0b0f0340c81c03201814010500e4800194540d03405014000010603000001ea080d05040c13001160340e9800707400f1000c1404400980000e800104100520302c00170351000040e00c0b410810100400100350303544840ca40c0749000c070300454640d510741c0c4403134100c0c000d420b0008880c03140641c40c0c0e01034002c60928824078051a06036549064001c00e200036802140182c1108a6403128000280b00b03a090b5405805802c181c02c0d404118108404840044070710164403203542656592068103a800031501101c02e004081864550b034400c02c00e400f805003800602601c2c3c41d203451510340d100e81200409004402094001c03464148101307104103415650040c20960b591101600e14180481070540554083c00005000035401e2401144c0c00041c0e0350311030050b019851074007204151410080f002504ca000702040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 568231717 1250 568230467 568230493
    0xc030e0606090c21160201060503070f06030b0d08070f050d03090f0b0717070507050d0f1e050c0d0504050306070203042304021309051e010b0703030e0a060e070f09022703 75
    0x190040c03050381d10282c05009441701c440c009003035070004e0780110700a42c084903080c0031001c01404098142c0e07440e0302d0000741c0c002c0e2920008407a2035000c0b80181440000080080c00d01c0305c21301130012100c2c0118101c85107642d03010001c4040f20111007028000c58a20070000e40001d01c840c6810b60042c0e554608400104078944828186c03020503201d05011075000102070007001024000d201500c1194104080044c0d5070070030103030035610b0680d07252402c1c1a403440c903a0b400c5c40c0120306444c1e210f4044002c89082240c25203000d4034039030141c001e09110b0b10070700d00084c100510010460301960302a00b003003507540b07141040550044c4031000703156900a40a01c913090404002d01054030041047c0c1c000030426080c05c204c4c801e50b00c44a8120b5007610241c01c401071000e0f01103e0f00711800103601d840c0021b08858040021800c190146900070002403d000c0f20881100000030014162000c0640045203555100082800c038803902d06004800c00994244000300c400d0b1600311480c000700942994040030150f4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 568232967 1250 568231717 568231777
    0x110c0a0b0d1b110f0105060d0f0f06050a020405030c03010626070e0f01090e07080316021804050601180203090d1d0918010e0703080306040c09090c030c030e0606090c 73
    0x842e550014520004400c44580100001003143c5001d0008000c0d5040043c0402d42810b0038042c05883c400c6000c02c01e81c02c000849000031084d41e000481000305051240c90b0001960052140c01e209102d640c071441914581803090b00101d035002140341132445600c40e85071310100c44c140e00f0582140291040003400410540c4414803441c1c04c01003414966040440310001c850340c4203810101a03019050900040382c000040354401e1001191007420b460882c07000840030b04100000c8802c1c915084240020001c000491a05803900c00d14400c1e50820700041540481c00701721001c2041c0ea010b92102d81c62175003d4590b408c81c08580f0f18410181307850f84008a10141c506554084901c0302082e800180c0031401c1c824070b41910742a2001d4a41c1c2403454880050301c0c000a4050362089594070010004107015045801c003c2030b00000920002480034800790007002410070700c8022038141511a60b2030b040101d40030b4800c0c58000c100070840d44508000240680000101070f0350716942c5199013070034140c01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 568234217 1250 568232967 568233011
    0x90c020c1318021e04090503121317030a0204031202060907050f010c30030b0306010f08030307300b0f040c0f14070204021801110c0a0b0d 61
    0x65001000c88810050500c4120490500300c030724068503090014440c20406250000d105804494050004255141e501603513040c019420b5441440c2017400b07002c00c28040054020911040511038039542c0741c080d0300662800a42000700b1034825121030f8240c0c003403524081e682140311008014100f540b41d944000c82000001800005039100b41c040200d00403007004908080e0100340c5150700c00c1d19903030002a28554850030000e2604103402e09404030031103410504002610400700d1000718908541015004020603001c85000c0d0207610000303e900032200328484101c030038070b00055145949802c1d08503980740c400340c0c101c0800e01c20005541d0702d1058200315400154015100012504e480c2000c0150103045004e0090155042c611103100c01904290200d099000508203c42401080026008c04d03100d140c1000f50b010f48041421a495804030080104000c030a80b51054281c00141d412941c84800e4003103994000c0d510042400f040c02070390042c2203e081081c902081321400c1c1e0000000c2c00c40c003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 568235467 1250 568234217 568234241
    0xc0c0e0705031014030d030509160617151806040b211b090f13020301110903160f06031104050604031a0f0405070b210702010c02120f071b09 62
    0x2109019843e060401204010300c00200c154880c2c15005002c00e8039040c100c0300490031b05070f0350b0002500c0700070280407040d840c0444d4110301c26181e4442d54041c000310302c81300410030b1006ca03e00000d0b2034040c2035103008015450041c8001c13107a0545520200360600f00802c0d03180c0080e210981407010381c540c0e00440010a000c00d00100342c40519480032803402c61210b480942c80c00076210440704d9521045940c54200861032841c0034581d441c1684410f551402d1280203415620708046903c600c1c00e0321010b4810724030110259070703400402c807110109410307041c0070f00211954040c074100a4107000783d002440d100d1480180e07504155441000078200e0f041030f44155154011003800010340400301105d56070100098070f0140143c2002c1d1221952408035004590940c8070006100105d8507203004540400c0b012018448a146485480240644814400d640261051000702c0e007480e624001620030140ca07107601d5500f0203516440e1507031303241d20707480c0003518003401c0343c06c00304140d107a038016040001c00b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 568236717 1250 568235467 568235477
    0x504140d03061719020d0f080d02070210050325140d0f1401301b06020609010903080606030406060b1204170703020a140106080708100e0304060503070c0c0e07 70
    0x1140581d0500390303402d00c4101c4440c0e900700b422940286041d44e80d4855071142c0555500034203484030301e010b00505c1172210004d400b08801194081100321550002c0903840d100380c0300386444041090003a1164003080c0ca268024100031001c41240c08030320080c001c40f1106038541100c00310b0126229404070340c4202014120075454051223048110b0074007034a4082d5001c1900c1c16207139850083c0061011103810440d02c0c00c1110302083c9800010302c0080d0320f00c1c058100c8618110b00381c101ca608511507150f0300c0740c400940a11070000d00303488410700c20303070310070f5509619118059034404d41000065400140200c030002d03514580840e5002000c80a04016140c03010300189a0400d41003545a408d82060011030b114010400e500000c1c1e8080303207214040d42d000941102d03043c4071130b5406000d0907403500003040600c22280b0000b401200002c00c880c60101e4070908001010000d940c2e40d840c1d100d1805040f0100d0420800706a0f5540320351401074031940960f40f015803060b100d41410012410a444040020f0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 568237967 1250 568236717 568236719
    0x3021c140c150c19030903030621020f04020a0905090402030304080a030f12090f0305160b07030f0b0a080a021203070803010b03010302120d080a0f1806021c0504050a02040504140d0306 81
    0x18401c2ca4640c2c010440d081c2c0e036802c0c20900c080d40407029858200742402c0549400e520000c160103034201c00040d2621074090640e0400d40c40b01e01412107000c1000ba4401c402052403020b250510307108940702c080e080d596a00c101741c1480c081c400c50359400780040741c040c407040200050200044c0610506288030b50b1315401142c82c40b0400911003084490300404540c507001c1a280001c1c00150840c0ba080c9c0c0c0740c200300307842d000124500440700c003080a000d00700d14041d20030412080e61550001c042c954408100300300000789103003842048117660080601a44c48068107002515010314201d0494a6080c1105e01d4140d82d81e8560003103420a0f4000c2d00444000700c014400c514061190003d201d801701c00a102c10103c0c0200100317201400341034601290f940b8101c0519a80442e000201508480d03000103600c003d1518001d070007580030703580840e040720704403000b1203090281c0c3c022603018941010040c40c00c601e503502000002d250141003111150307014041c0e491410303070074001c01c034620790942c40009d40d0b6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 568239217 1250 568237967 568237993
    0x4081501030507060203130e090f0a03050316090e0a05190204030c0e0703050720070305031201030b010e150f0f031615020c01050409020d0e0a06240303021c140c 71
    0x8074405800c81015501b05000010b0f8003a00303a00c6d40822501510420b59560302c0300074100382400c84144400c10f079800f400407103405064202000754003c00c0b2049003104544005202101c0c2100c0c140203072040d801510001c1502e12a507a041540c110782e034000ca03441000c0708454100201d92040c3c0c01101d4103500d1070410007004480d0f607a8641e0188003410144285e02d050800281180380003400304100d195442002701c4490003c0210034059944602180c1c0d03a0450854240c41800b001d01c8100c4044400400100e5031085445245014210080e1140d000d030005004211b6142100c0c4946a08540d881804114035941048410584a505420350f25001d041c55024811460001d80d1041550310100d040d4049980c0070781154111604030300c0068503514540b00040c0686907a11035280540f04850b2038800340425540041d0800944400881c61218210210b41d50081c1d944406409a041150a0341e410b40340c0104604803500a4980903010412684400c40203412014070b42215500040262a42c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 568240467 1250 568239217 568239223
    0xc1c0e1804050c09101d070503070827071a0712050306010c060507080405010f0e070b03041a010b0c01181106030901060e01140f03010b09060105070501060503011a1009230303040815010305 83
    0x50303074a80d030346c014105281c0008050114032018200d44100020700e400107495058005060700b10003448402000311100c40d01400791317214034a0284503a00c40f6029a08003007000d51008036039034103501100c4042600c00f03400081d592500300804181c107100721048840c0c00650a03104941c4216600d0b242c100541c05e2038103080d401c6406448103400c0040c13030726071054047c0000150301303021101d07240c020a07500d9a840c40c10181c401208601100c00e42ca840c8008130b89020711130081d0203100d0440d8020088160400084100042d0480014200307051607843c5502c030342018401550700241034000400e400e565240c0101c46404242c1c040414000140184240e52030701b01310800503844201d00900001c00c0060008540d19005040742d41800400078484081006c290481c2005120003402000301c40c6c0110790308046107a111f240d440c421070421640c000742c0d600405991003541d001200818405100009002c1488140320a05a02d0722080c080099104010002580d0342c044c0707488c9401d00ca5165140c5246 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 568241717 1250 568240467 568240499
    0x120b0d0f0614011406210115170c04061b050f01022203110405131a0613050708040611130f030605010503030c10020d060b0c1c0e1804050c0910 63
    0x1140c0403600c1c01000a8001c40744500d44440c021035030941c2e00c01c03015001e41e040021200310700c460405d000c00001500103000c640381548c5001c0d5140d0741c01d51022501c422540399800c41d02d01d100040309100034410030788a101040c0350041e09c443e0307624041c4620b03140c00c1c0c83c1900d02a10303202169000034660340318100e4205a0402e0080c450503072000d0318215554040103044080900d805141e40320009500d050400841903205604030800c5092055034401080c180340c003c40351280204850341480302d2240c1d807881002e11811180d60b40141a4a13581e44440140c100714482c0300c5622401c0c021b1010381030b110011000141155101032511920318a4481c05132101603204900c250014011740042c1800401c400000440e90b0500590780c01045801c0c030001c21260700001002c1c0c2d00800d4444003200006131182e6200b40ea2901007040c4c8a41c0b10085640c80c43c03194409410035415800c07001040c00140820313030402e1081c030a980c0035108081c00f044045404441c0409100b20a0108100380310a50078100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 568242967 1250 568241717 568241741
    0x11041109010e190518160c1a040503220801060e010302031002070204110304151d101508030a2c0a0b0304030905150c010608030403020a06120b0d0f06 66
    0x6040038080c0001800721084400114003502d030000c2085079041e41c9400020182000401510600c66542c80e03c6040410854403000303c400400f05214811f030040e46810707a200d0344050105011034440e810004c081c3c401820407250b9220030700006510b030783c1200203400204802c1d050440d015182540f400c3c00d4030b02c2d60b8448080342442d42c0050025840100303e0968001200d1000360b9903440c070388040340c01411072142140e00402c0c04000c0c00100700700d9050141d401b0000b03110070303c819207500210300c0c0c200c03030b00e60031480256101d601c4500101101390004186501c0d80d00344104425900d00c03480d0b003141d12001c012400603d075510b0494000d204611004041c036075100440200d400c0f0000400d040050f24010422413140200c006020148900f02240203020302816a2001034800f02d20764807203410101c5401865402c103100031031010340020582c1c04503a0024031510704640b409106441211003918002480ea0700c0d8140c25120303803100c8032200c0641d84207180c800c000c0351942c1401003c88569083c84 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 568244217 1250 568242967 568243001
    0x7082d1623030417030f0a0c02130b0102030a0c15140108060c030721090507030b0603120906030a09020109080a0302060403030f1e020a020a0b1003030305010b070f0b0705040902071104 81
    0x801c005900001a101070343d803621040002203003c0c620342440d40c060400d208510940000c5d81f00c03100d40d4840c4166007035920a46060142c42072005e90072003901c02512600d80183c0c4180310300d5030118422401d83c040710340102000d0104420544810b8180c0c0e82c40300c0000c900b415510010440403900f00301495010400c80a40350440c2030080009143c020074007505482c940541d0301100b604200b0b54049045a07a10104031000d00b81d4a19003c0d0b000c610450342e80b4481d01810680c0c1c81c80c46011011940601d60080c00c0914581c1e4421460005000181c426810020140008161400100221084075021307400601307141c902468020140c0e1859644901600d081a84151245480040d440d41d40551071b02c0251f1224042801285040d1042401800f0000000b05102c1031400429034081540d00940d01444503a07200d086800e800c1c881c22000400306041c202415001c14041d807007203500814241303449450140d0740d0001000303a801c1000d042c1d07050b0320403002d0500c25107068480c1c50301c60041800d203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 568245467 1250 568244217 568244273
    0x120301060c0b04080c0607120614010c02090901021603030f1a0105030a200f040905060d0c12051005090d02010506010912060e19030206010906060507082d16 69
    0x100600c1d48044650003081c05040b080400d080110305019940951161411103405182c000c50082c5550912121703590102d1034443c0100345a405c90308444640341041e120f2200c0c00e80310380d0038401c15040080245150b55401e1002c0501e01c0c109404444026001e90307000b04210012003112000c0300c4071581d00c1e06514030f80d41148a416600301007a00c0d400554a44002012a150b440c08001002070400e01c1201d100001164951051110b000c1c0c0141e400030481040311307903144401d000114a1000c4040c000207420030041002507450383c54454031611031420b441c0f9114240d8408015201d05603614440b81d0407181500100c254240b01309036001c0c50928005040f14908031581c4001030b0458030140c80a40c03902c03800e2024000402c2005000c08020342c10103082001814029101c600a0007104440c909044000500e02d100b4001d1f60740345034100710050701e0321200003002140d81d904500300c2a5401044881d5507042c49401024003508207080c050b889200c1c0b1107242c110701c1c082290b40c69036000008a42 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 568246717 1250 568245467 568245479
    0x80a0b0c09010207031b1805070504030f0501060e01060903150c0e010c0204110a0c14070b1c0b040504080405040c050f0d0e0708060916050f0d12171503120301 70
    0x2450340200209100a0341c52100000407820326905030805025143c012040482c041e410742900c00844a01e01d4486c15185516035040c1c0680380140e4140740000c0c421310040c030202d000300900d6054213201e080005041a41e400e102c3d402410244c1c402404105c0c00c600400a0141044819420882501c420081c1c580b482c1009001c014070000c07120304102c2c0000f2004110b4880368012901c00100700381d21915a4941000109490900a02180c000083c0500c00c54803000005140095070344403074500742045d80045044403000241c0d060070403615242c04140b0038513240c600c9400d000d00e02558189990301c0c28a400e2005032410a4140c00821074208100c00d50312102d0001e440b0b41250301000840c03142c0410a82924042094200c02c0c0180a40c0c0b0900c8051180007518100b0507207003401064000fa40e4a041000c07101d5014071150b000540c00505900040d012418406105064201090502c160301c40700200d00030101c1e03514503c242c1040d401c1d0032030b1904001c50142c20021020140c5507604101d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 568247967 1250 568246717 568246733
    0x50712030203090109050a05300a0815060c0a061b0e1e0907030b0108070503160f20030c010b04060b25060c0f090801050106090e040c0e0403090609080a 67
    0x460041059404004203c00040a411020700e040c0c10200b2688500903c0c1441900c9010b03101d944421807440c0c10800b110a0107045401c2884080304511a040180c200801e032121a4001c2015008469441400426a40302c9000c0e0007801c1d03500300140341440340e9107007074401c60744440d4040141c1e4044d52070030980181c1c0005100c5101c403050783c50840d90250300498681c1e402440c445654020000410410420b034598009000000243d8414440d1348580c0030981d60b0b0702c0169203604030158211a0103241a00444001d0044c800c00e207040d07081e10362201c030700700300e25140d12014140d590400a4140c054800074060500035103411a010083d05151403a5401d90748100d000d030380c0d0442105005402d00c61b074200c1101c0c1e1705d40e030800800d01244c0700c0b00f44000c00040c021022403021034405440424041b40520415050310003e8940c54402802c1c201d50b0010207000510854004124040c080380b43c0b18202c5445005903c00e0b00ea0003c40b82c00c104010380510283d801905090381320002c1c1d803010070664 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 568249217 1250 568247967 568247993
    0x705100f020706033c020f03040c0e06010f0c1a01060302070b24010f05210a1803050901210603030f090b0c0c1c05070b0301090b01080402030d1b060c1e0507 69
    0x14070b00d21003001c0181c440c580f480d145d005284412940c80030420178464101e24000b0f51045100301c41c403070719854688802c103d421340183c603010b001401e40c00812050310300032011000c07031074011201294007024002164105801c01d0700404002034000c16400200000290310580042c04440050f0006004003083e00c051811072231100d04200e691680c03400e0540c007990844411045500e0708801258144554011a000c00d4940048003860700070a00000642e0756240c640ea16450350b41c0d903150028250044580c0c80c041c400140c0740303410003980c401d0720074101c1c42458000d51103515441422127100501800365101036002491040c01001704151810010030f0005680f8012140300608102d01102d40f4070031201440014954415070300c0c08103003000c1080245040b0340b101c1307009120145003540112011401610300030740603072024208800c03290054104450481c40300303250507524a2a5210203041e5900c054841011403014403a50707000c00c43d070f055001c900d642c0d42d040a83c54105140c0c3c8006400500e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 568250467 1250 568249217 568249271
    0x50105060f1b0303040f0c06031a100318060f050108060702060a150b0c0115050103020405130b01050c06040b15010903080307030504021c05071d010f03080c0705100f02070603 77
    0x80d0b0440103401c09101840c1d00c5100c1c034100da49034074192600750440541d03108156801c414000e80064601d2280c00f40004281c0b90f000302c1c40d08400a14140030074001040144018140c40e602d004088107440d103080303056940524000704950380940d5011044802c103030800c0c21107400140030000902e07000203019404c04440c7c1d20000300740d4100e10302d2525550880d00005110000094030700c03600f150540140352288030144009032490b540d4801035080340314601c00e2540003a441800350311a040290b000c0c4040a0060410311310f068941042c032070828604039400ca500c480907106000110349115601380e04500c00f820a0424541145c42d102000d000c01044901019181c100040071501e840b182140740f0865049000b4002003d441c115440c1c09144c000d1040055001599020240c04ca411050498040c4c520300240355003103403103056141d48000188805171080040c00503542d00c400c014500c030b40c0940d5a0310312980d011224000d00b06225a4445030815061114210800c03070100c02c54601c07409 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 568251717 1250 568250467 568250497
    0xe3906040302010525020a15110304050112021606022101050103090b010e041a010609080c0609090f040303060b0d0e062a0a030e0111090a09050103031b081306050a1205010506 77
    0x4a1076019106240c110b000035080302d0191f030b00007600c1d0290008825042d00079107504940a05210300990380b4080c91007400d0014003162034420240807a64003c00d807446825400c2155403801d17481ea4400c1ea0701100c103e001556046401c41e401c44207041145014000c246004d00280c010783c1c07101c0d10411810b01602d03c5050044000c2003c001c3c140c5c0900c0011036000740c1001c11984d49400291444407a4829101e881c0540c801051403450448101e44000c04010203a072426141c1d00c91b48032405034010011000e150b40c80001240c908810009030a207686008804039003090124405400e00801610380061007412120328110b200407016804407030408021880d841700030400081740038005140c070070780a075480c100700d09850307410321030041100140c203440c0340416a035180c3c0780c0e80848000344800390000d06007096022440c40003828a50600707014130482401d14419024610039140360ba4020004210000366551000b41c0000d910700d0944d400c0403003084035624100201d60b60b4414605136480b650 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 568252967 1250 568251717 568251757
    0xc0a03020c15040b0f1b0604060b030106050f091602030d0f0603030e0409051005090c040203040b0103020108060625030e060a1d0f0d0b0919050706021e100e39060403020105 76
    0x740d80080000301c900030303c200c42c47c034140360815900410070a10078a00950070300030045141d007848100c002c8050300260010f10555039190b031500c03290032428555000c50008202c69600b00036140500d8119090020380007801d00d1651030060b0203144401c1c08a4010790a088d1400003056000c6051003031500c03415000302d866500e60b501030307042c50184000b45034000e00c00700a01052080300200203050364400c1c0c82d2102030341c49280400c65140541c0c1000038100381c0c0c803000d02148943e80112403101c20300c682071103e1030050440014000740c100d800101c002407140001c100000481042c81501000700340e8080b44c000590300003141520000c02d101400451b05a00420084141004240340c02c2c00c0400e100d001403d007921b01152108568443c41e001480b0303182401411407020342e03039402041e201600805c8443e505007100c401414025400718224068804842e08480300002541d4407050203c02d00e044030080c0002c2d6140710702d03c0b5801c09028080920080c00140d801c8021942880c0085001880c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 568254217 1250 568252967 568252987
    0x3020c0c310b12030c010c0c02060a1107030204050c130f15030908090a08030d050f070c03111608011d06090601030201212d0b0f0409080c0a03020c15040b0f 69
    0x640b807203a80c1c0c1078100701c0c0c0320345886039160f001c03001c0c010b030080d11402402a2549210200d0b90382c0020310010354001c0c0100704811906005030056241c07460108103580000f59079400180440c2c0b411034644a904c0c0b000914034045414280010000d40b0320712852048150502101502140080c171402041c19030311000101409402001e0310354040005140b42480d5486800907a01d941000c00041001c60502c00412800c2d0712940e45d0300d11900c0c4560703132100d1540ae242ca0403500d180001e2060012405400313801003c14800e04440c1e8003815641002144000799001180c000c51003080016006800030340c180100030300041003142c1102d1302440d00d90106440f4030030401407d140103040c0c94803240f60514503441b900d500c8018034801004801e1403044207808828540030f0302c1800800725401104444649803d103405c4e4000d0139128010707060b0600340355400440318030380200c1880540140e8000102096640b410400c0c111034111116012820321b0300e4290480d503103024010740d04507070901c00304400020b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 568255467 1250 568254217 568254221
    0x11b0210020901020721020319020f012d0f02070506070503090f0604081c17150427392306030f09060108070806062e03020c0c31 57
    0x540700507001d2103041140d0040107120b1071301b0145c04038041e0042c40340203001b00e83c03120b0725882e0268024104000e078002030801141c40362000082942e5040540e158480c0704503a0f040120090845a1562400c0d9811000e0103071516900d030b4011440707094200055000203401000b942c03030381031003035a003c011000740c2e00c00901030380500d8006401a10034000e07501010340354110301c84a4945c031901c8184101503415403141d8014030480d1100b00c090350403a6030031154100b070382c0030441d10082e001caa12144c400c40303100a001041c8000b010f40d103a004134818170301c600001c000c4041c040c0042047c803a00d00c2d0482c0900320203401a601c12000359440d0f0382110181c101a0451801031480020b0081c0d50780d2410000585c01850261100141441080b00201d820400050494180d508490092041e03a0783c02e410418a0500f41c000c1120b407044142150480300920081c91845509503140540c4401c9240074561806481040d4a841603e4001c0c15002c0035000c0100c48000d40c48004903040302028140e00040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 568256717 1250 568255467 568255469
    0x30e0c030309210303070e0103050703060803070f020f0d1104051e010b07020112140a0b010807020c0415080a030c1a06010f320a030b0d0308011707180c02011b02100209010207 77
    0xf00e03000001c10403200b654840301c2d032440c03120700342c80400c034586450900b1411a40c4500500e4200d62040001d00c0108520041c2000201d1000382840b01c000b00030b80100f0031290f0466403c03031f0700081c40403205089180601449074440500000c03c08842444451001300c0007040c416070030b00702400241d090039644214120034504e1201c00c4e0030f1248600d54200c5004841d801c5480382031552426480360402e40c884c06c1d0441c004c03011a4000d24920342004100002819100b440c680c0c5005200b40029400134184004020702d0b0003034542c1c150051690800385070b0301442001841d03650130a80d0420006a13000300e0100c1c1031420314a0415090340000c800c013003c014078124085401582e0440f00034200d003041c00180f061600d540c0d4180b20234603009041c480e4881d070810004010038141001809036092480c5012513159408040b1400c26503200454080c400c0711014082050b030302ca540c01004c480c6c09026950780341d04814034603100c0700b441c40c4000351a80040240c1c0204980c0000b000c6026030b2080003260 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 568257967 1250 568256717 568256779
    0x50d090503030114011b0b061507050d03050402120c090109020a050d06031b0b040e1b160f020a2301110c03060c0d0b010f0c030c06091506030201030e0c030309 70
    0xaa995031655458200b200354408a140010501e50b489610016110000b81c0415806411f03200c1c0c0303480719410001800d00d0800d0100841006101c2400420070401c040c0c40098801c2c1c40018540c2080e00622172030324240e201950240d407000c107000c00580c80b40386c903003070442c0c0074048011f0300c902c48444121001e100303111801d4002e90070310344040140310b0401d00e2460001106000341501a590350348140e0240100d1240d030940340b0703280000404403088e60048030f00005c02c10120615014440d24100c515110850702a120180c0200b003060450034a03132078100c080c0c103494000108036007013021811201d50354000068100411400003100040342003000110340180201940d0482c42d050322014031907000b107080e00303808030b00701404840741d54010034000b01d100708a13030f44148108003151030995000c040140112402962100300002185000302d800342400404000429078030300d5400014182d8a0a40340c006080d00051490301440d9400801c03281c0c842c0003610325a80c031800740c64090103545400b000704 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 568259217 1250 568257967 568257973
    0x3020d0204031a06091e010e04050f0d110c06120601030b0604050d0602091009060c0303020a0912050109031e1b020a1703040305010c0804020d1e050706210b030c01050d0905 76
    0x9001c00d03011607030f0000c2c841c24050b00d090130207a4840c5140800c614890440c40c040400701c000501111480d040340c03552080c0503100b02c4420484503107000e481e2070040300c021070024001203c039a02040c41485401c51000c000ca81c03181c1005004448020b10500c041c241030b0505035902c16aa8140d20b4840c243c80c01040000c102c0320301c5601038145040a940001000c0e84035400348807000280c94068106201620030980d01d04540680f1580c003500254811049a8203100003240005401900b5514a0b40028401e800102d03d0783c01d540b80180000e0651440c070164500310f4100294100d51041051f8039564101c2c0d401082e4844031b0022a00d068402e420203c1548110303101150702daa80000108100e901c500000c105120405600b1904404242c074004d6000502555100124003401d00b120305800c42c46510200c905c28070b43c1d59629003010341c0d001d440880c07070700180180281860030143d21500350303400c1c003802221a1480040e444c2d0450700c50142c1844000b04400c0741c1c2c01426030081c001503900000f1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 568260467 1250 568259217 568259243
    0x601030c200a0b0f040803040b07030902040501060e100e10031808031021080f07051f0501140108011d0c0d0e032a070303110c040f0204060813030801050103020d020403 74
    0x6516112040c852040d02d641c00d007a0046070a80c240030b10794605c43c1c2c0c0c010003028256203617682e541e036003000c0161125040540350182d02c0d0150f038551062500805032900c80703202e41d03441001409001081850140b051003501c1a01005a442d981200f6820400f14580080c424001c0032080b03180c01030403030010b844002c010040041c0c030f000148103201900c6000007400c40e48102c01844c42da482c0400b05000301030139414400744040070100405403c40c0d81c41030042c3c541200d603c41a1640d090038010b2201c00c641d8031a40100840640402d500000807002c0c0f82c000020b40c1070070b2020f8940d110315016403d103e0303481c4c00091840c1c0150400d99103e584000700a01c224107100c00032583c0c0c0c1e0002154031022a1150010000d04408030098510b40b080072030103000c070740b880c5032025914101e11240125560244000e01495550b89104420b02c41c0250500142c0341c030b040030001844208028001e68840c0036501411000c82d4002a01c58115030007460301598134002da2003600046d000da035000030500c101d6140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 568261717 1250 568260467 568260527
    0x180106170d03060f0617130204142d0606180603100f06090302091303020c0414010f0b030118020d060f080303160905150d020c0f1e060403080601030c 66
    0x7080c07900ea04031541e05110703c6444031080140b00840e0310426021030041c5840c00c4801030f280804a611140075505040c01a40c950040381c03ea50382c0300040744020014008012882c84031106101c0c1d1000200c03070510300500340c0401019030000141445100b810041000030124100c80c22488c104032000d0301c0300342c881c24070b030007403254440c194000c0c070320008074101b408920309201f4100d160403a0b400810703813410f546450317008a54040035194254214001da40042c0e01da5101c0b80103c10004400800c00c07065989010010300c2e05d440f09401c00002404204010800c4449250840790380d1602c0e03502c0140d99400780e40707142d0014100c60780285020300304004005001c0c0c2d4040055031185640500380d80100b074454804403000d0b0700d14002d10741c0c026a242c01180c0c150800700058017003145d0321440185807442d03a54243e4540050141500410340c007043d03500082e650321800d1b036801d818040f401001c0e00e0038590b41c041e191034001461241050360700c01d40c2c080f0251161080c032240075180e0803594403d0241030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 568262967 1250 568261717 568261723
    0x1060618080c0f04021305100c020a0b0304080a200703080301080105060306040206041a1204050d1b050304150c0b011401020d1d0118030b010e0a05060f030618010617 73
    0x5a01565600395400c00003924000100c1c05100d80d400007420881841c030001c1c00c1000940200c0f291540710344e450071000c2440c0c1c4500704c0080c0c2607841c07031b260200308000910402001c50352942114007105418824400001c003100190380c0e03102d8441c1049401003c000e4200009042d500303c0c0030b0407a04c1205400014465040d0042d070581c2d071050002e004a503280d9061613500d9100740c400941010003048200070344030f00988108550820a02403a240110010842c0102d041c1902c0075140341d0071a003910b00b045500861518006d110380b0b03110b41c140140c2505c7e4039403640a5813080c80101c0356a50484035a00307105888001003558010344441c41544c58415000500008600e440d000d8450f0a448482950103840105401d010703110101607503840c4d0b0401150341c89289081e4400e01c07480600d000c03000a04080445000c2c11050a2040c00c03490100d01803403d032000604824040e204141d4500c1480d200400c5095005998070400032030440c0b424295401041e0940c020f0303c0c821940694501104408 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 568264217 1250 568262967 568262987
    0xc0601060525020d0b18030706141b03040204090f02030105040507171207110114120411120307061d0109030914010503014703061516060518010606 65
    0x140c81010b482c4440c2c8003184014001418040d510203d5003022000003800c600300c0b107510070303201920640f85802401c03180f40395800029040394001d40304d904100210383e02514840e0f20075903c0d42460600e010800c2d50b60300314070014002030b004680b214940f0045c400c11200c015034a95001c1c000300303c00e21305070805a0319482d0764052101c4401440c0410350009000113161004204190380a9241651968800400464245103e410300c0303e007070700311094101c0308009000703203c071700031540b210b54605480c3c81c2811003201c400d0148500d20350301d618060001e00100740e500d0680d21000004016500909070b4100d00100c2248000540c2010b404000b010f9020f01001e007101c011190149801c0c10300401951140002d0103140b503000e8980e01060011a03e01c0304030040850f040040384031650904001d10081b40480720940d01480000061000c00d040c4415030410242441c0305190519030500d40d642d40c2407202000241050b41c0705c60108400c402d894080c0c5400020000007001480d50b1490054100c01c50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 568265467 1250 568264217 568264237
    0x141603081206120d0c3810030c0e060f09090c010806060f09090c1204030306150306080d230301150f020a02090402010807020120091c0f03050f0c06010605 68
    0x1d5002c074040d401c021140d690b0419480c0040c2400c0c10a02074211150812180300755845d219400b0040c0401d212012419507040700300440ea54030710302420314550140c50140808015100011b010808540342d07601e0302058403030b1140c9842440e100d180c00100c0e44104c211841d58030590365000e012001c200003e075016003240030780f18400383d0359804c800c0013964000d00d040000020010841401c036032074004030342503114025450240c10704584209854031480220b5003200401c0d941c0006000880c4c81794101d4000400320b140c02c0c443e041c204400d882c0ca506d409201a41407148240c1d10003100000354020080c004103100d85151203613035690700d4000c01362141c045400810205041c810455102041c05031400b030f00640590240d480d40d0b401141c080400401e1102195030390600080607040c2035200b0000c0042c03110220352942900c208119007404081d6414804d0090140c0100004644850259450760103051858503500b0184009610b44103c0003040110b002c0c160020900c2c0340c004010b42020782c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 568266717 1250 568265467 568265497
    0x903061503070518010905070507120306060801050d020d150b12030a030b09130f080c01050703050124120b030703020a0b130b040302010e0906130c0203092b14160308 73
    0x150715001e100c04c180100e0b00d0001c145240708010b20604c03100b5002940c1184a0345000c03858171180d80c6801c45d03001098010300c00080e07201c0500304a80c59016140d6805004112150001100c003640011001020008000c04c4c01100740c0e60f02e100300156621005544101130242c900c194220310700b550b281c0c0c1c0500c10440110740382c20103501460a00d84d1885115502035020441106021b498480203034603020341c12101024100065050001d081c02018010001a01d001c180e6504151034806900c00e052513000324008103600c49402e035603204620f80e0109040c1c040024a041190707003c039081040c51342019411030104080081c0080100b4000c110041440603030111264032011500c03098803a9102c040d00082416810403103624000c10199001a401030200c800c040031070602c0344c250360351100c00c6000350300003084501b4181840239401c144420721001140400e503e1801c2002000a100710280442c41d4034000311030300c501d003000350320352042c692a00900c1e111303a01c1c613092425600900c100d4403030314 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 568267967 1250 568266717 568266719
    0xc0a030b04170306280306021210061d090c0903010c08010821121510050a03050a020301060912030c0c12140105040305030112020609041a0108090f1e03090306150307 73
    0x240d004010b0f01c3c0107000040c282c3d160b40204580b10004088401c40280d260000c8110000005142d44002c206c0c1c248001015125407400340800046c2640e613034490700030310015148018048002c64100350840d081142c9281141e01e0b003203105825406003003411505581b0f4610050741042c0c00a0f40310f8101e40904086441001a84614034042d4210309490b20f0580c40900c140719500e001c1c80d00c580da10001c0080030b0030000c4400400682101c0c04603c01070086280010602e903110b03030501490b54000d1400700c00b9442c42d454010000d02c90400d901c00c14202c0d002084058081600c20020040c206030444507860150740c684915034040c40d2a250126800140c40f44090b00041048c000e2605c1244c26442c0c080c1140c1c40c0c0b807900c8000c015402c0c0c08032303442230013005607000b0307a9914400c1c4204c8881201080c80d803507030b6103000500081c0020b008400030380c3c8610010030608200280740a0842a05104845181c0c20300240d1031079809070036078199044c080c0108110380008054400410780400303c0485000c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 568269217 1250 568267967 568268003
    0x3020306070f0507030f020c1005091915080702030f030a050f070201051506030a0b030303010b0711120606040209040605090405100c17061c170c101812020c0a030b04 73
    0xd19000e40125011503c00c0c0407100100b80181120401020302d40180c0750040c91300742c0000c0f014081a070303002022590126804000342481b07206e00e182800c0451004000c203040c007035440b140554004410040103076220000f02035a00c28030640e00c032600d108545035101c0c20110002130160108580c81c1c0300f8102c038000092012071050050303902401c00f0048640c962610b4105004869200030848500381e91242c06160081d2010801580280807511105881da0081d1400e1403840d5124101e0f40d01c0384004e40320314140d60f81f0104032550801d02c121401a6030345440c01c0403c018219603805550b1003040f10040100f0b014010030f040b014814074580400003000d4402d0301740c514440a9601095100c00c950009031542031078816044003c0031260656030704407055a07141c41c03500d02c00910150700c0c0c0c808185000160b0741000200002035060106024900107540c1c610303a882c0034020068446640130116040c9c0740d00030b1140340000903020345200d40254490802da0b1345140c0580b0200c0390707540741c03146c01c00c07c2c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 568270467 1250 568269217 568269227
    0x426010b150d1104050316170c011b020d02150901023d1d0304140303071205130f060f120b090103080f0f040914060a0501050f0c030c06040c0302030607 67
    0x1c032089000c1c0790300340342d419840c100040800d1104051850b004010110751550b0070040096074000c0e520810684600b850307401a0003000301d0700103407080d51103032005224a03a001a012078504240f019040c0040e1524000601384407694807000e90002c200d00d1460b8407100c500001046807407800c1c2c0840e09130507031150006803900b409004032440726a0010740d0040701d8010100151030a440751201040060707140c15140c42c00a040e0040c07011507400081d01304003080c2e1032841c00343d01e564100c000c0c600f4030388a07484186c5501d6600c03554408206000403111444080c0a1420300504403140b13103079019584500001e40408610089a0081908401140680c06250003811060000901006016483c540d03900031035030000d81c0d0a49001c5010301034200c10016a0b00540000c14040b8008140f500c0301c036144052001c07020f441d19001d00b01620051145981000455101601c240d000e40d40c1c8808034217003d4210b000c0c1d24192079890041030b09200601058050902c1900e0086043c1c40c10707501c2e0550240c607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 568271717 1250 568270467 568270489
    0xc0d090503030d0e01020d2a050c07122102010f0f05011d0603030712080f010602191202010e030711100206070c030509270103060606030b011b05030426010b 69
    0x107410742c030401200c90400c82903000840401c04140000d03042c005100006070503034021503801c0d20b04441c060101d5422100c8000007140c024114104589005042050b0175181d1080340103140f0030b01c003010608810402010000080c80c168641410340d14114404000e019180a0007a891800d04291036081848281d12a581c1240c40544600000d41341e00880310202d560014021581400180100c4020401210100310640038540d15004c251030042151010340906800010455021058841c41c4a60f201009220070340c000300218008159500101c2c098100c40102104c6804042501001c1000280500702c941004a55900f441450b9007000c0741d0b920310840b0345030000342c0c09290000102e07000380020728090710007408034400040c100b4a501c010110410940491070742c03000040081c02102c0c480d00014040364a410701a9104940c0003e107503c515166101003141898981c004101c4208100d030001c0c050240061502e400399444a03005e16218102c0300346650034220082038501d440c0100d11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 568272967 1250 568271717 568271719
    0x5010f0605040521120306030d031b30050a06090c0c0b270f28032105010605070c05090c040902090409021903061104050102120f09040c050c0d0905 65
    0x79040a00e030404200109901003052608401c00d0410400096414072070318115911800c802c65036070600c3c0e13041c185003c07001107000040510742241400c410141481c46070140c1210f1420303031780c46011a105070013890b0070341034002101d2450f800001d014400c0c0c1c2c1c2000d4800c0702c6a0700200b210b240e07a03074141000c0e190303144465030004800d005e01000003403603862036541001c1c40820300200e80c0c0300300d040440e048c2200b40b00300c0d616620500d07007014204410040c1004400003542443e95120070910f081012034030a902c000c0134846c00a03000500a07224002174094a50783c09003d008650390340380041c0060b40500d130300ba200c0ca28503000124042c14141c464038010208040d219241c6031410b000e81009400c1a400b41d5030040d240e42480000d0303036400401101c1240d001d8840302c002491860910221496190b182804500500003044541c2c0c002c20794200c240d48003014140d85011100204501d8865000000ea1192904540c40072090b80b081c080c000402024045a0100d800c4282c1503a404540d88605 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 568274217 1250 568272967 568272977
    0xc090906071d03011104260c040906021204261219090b04060b040609090803130201020f030c03070b0f090735030a08061009050108060d0b0a0b0405010f06 68
    0x12072000c0d48920840380426a40c0b0803481400c0049400007401c0d12141e90b40030501c080086824000220386c001007080440c481002c3c40c038480f0841503c80c1d04d039940d0300c3c8914070443c6d841c1c42c4901400703074a40480300c0304e01070041c145a40e03252501d0158120002cad03c0c0400640c400d007821085210633041e00315002d080043e4034104440c0d03124800c0c250807808180000040b6929a444000040d44013400346000c0e61154030b0200d024104002403004a0700c81d940100100ca041c0312001d0089681407044907002040b030b404041c481422400140d143c501d035030840500500c4001800841480d010001e0031506116488114098880840c0c590054400b603c84070300c6500b00d000d0401540c044280c0030b0300c103481d881e01602582110300c0c60702681120019000316042d04005401d02946512a45069108104031408907092030110b9000b00510514080c46050110070b81c00700711141d0304c10050000d42c1350304c004901039a00c1d1002a0382c024009041e0400e00aa003040d00210715030a9101508050b60350b00e07650 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 568275467 1250 568274217 568274221
    0x501021918140d06060e25140904020309031b0606090f04081603020c060408100605301f020712090b0d05180d0c030e092202010e0a080f0c090906 64
    0x30080d000694200c100c13080c035a15100011110720441e01c40388129a8941d11070110741c0300c9145c52400320060614001000520f40024810b620b801040d1480041c0680d4010707200e40d20510800e1a500c02c101400b214035a40301e005007420000000e0b882d1103500d09403200a4140c1ba90a00078a90102c192401800083d040c0a05040340101c400507102e002d00074811a05d4290218001c552241c0c070a070429509500100d01c5070301c42030094010303140107101c142d8062110002115283c203180032030103002d07070b00c1445074500c0b0880b8803001c00c40500c00e007085c02c400c2c4884110004a02e00294085107044484401c001b403182e45030750080d081403040702d20380c0b50ba8914001c1402da0100090600034601c142d404030440c0c40c600c0014040180404000490300c604640760071500b00a40360845908418ac881c1030310404226441c4010014a1894548004a000c030034265200583d8068201c0d502590003038864070f400a02c00b5030000d0441c103000c00040c10b46281089040a004c4500d0088400135803941c00080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 568276717 1250 568275467 568275469
    0x16030b090f01120515011d093708040b0415022a031c0c0b0c04121106121512030c07030308070c060501090518210306010903050102191814 61
    0xe05074201e4840e00a540300b00c44500c2903081400c0003a0000400d0940061a08262540d200a080d40023440c0c3e0300101000c0e2500341c901c2601c60103040940055550b0715210b424904404286214220b0b4801c101c5a2200c0d00d03198450116003007440740c801400c2401609035107540c00403540e4103820481a01d04800d08601e5995190400d200900d041e80600c10114550b203c00b810451004203800c080e9142000d8000ba07042a962003500680b016291040420041013148042d02e0000d01859000c0220403640e01080006001401504840c004040c010700c10050f8002e203100101c6061303d012214200e076104920400d541e28007a1100e10181d5910941040c000f00c0c1c0901c2c8020703401720b52450800c540e01c0460303440200780c900031307403002c452180c0f1282401801c850f04208c9111200b0301341e00411102c15260f552103800c00c16007d01401c4e040000000c9a8980d200c2c520420185803c0402555034400301c41181d5454002000070300000360303c01000d480b04c1d102c4201c1100880f000c580506609a080750 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 568277967 1250 568276717 568276739
    0x1e1d0c030903160f05071a0a12062301020607020325060e0318030606060304150e12071a0a02040e0f13060f09120228110916030b090f01 60
    0x103030404400340b109000040006521203c1c8206142c481c0c0c04400780c0c03584a241041c0341000a40080c1c0c00311050710403ea50411070341041e41c9001c035603031401c1c1c010b5944400414001303012541200e5004074612014021406914a512240007001c1e400c4845690702c00404980368010285c041c690380010324550805101c1d60241d400200e40a90400142c1980a4102c07926690080d080c5c0800061080e40c0f00d205850b0600035140d20a40560b80685107203885d075545c1107a90fa6500e000304010b90b86c3c8546600b0510200000c10cd061084001c00740d03185072905102d008a514075240b1040f00e10072100180980300d8a0007a00c04440203c034040d0519190b20300f040420f10b0b0000c0282c503074640708261503000720b0031a0103008205030003000001020703d010305003034501c2d0303040203800c1c41958001c1c044142106640d1042daa907680c044101c0c081fa240252520501401068404550002c8014148002c0007603c050040700d11002da00e04010040d212414071104020454141051070040001081065030403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 568279217 1250 568277967 568277971
    0xf06100f052a07031b080705060316031b02030417010605180c090406030809100c080301210203030a05031008120304030f1e023304020d020114041e1d0c03 68
    0x35901801c42c05007005910700d071100035071042d6100c203004119a40004540c0c0f00d048060f00342c000c0600030950501c004650288001340580d0740707480c090560a110b1034403c2c0d000040c07e103201c1c40300350784130700140400075561340140c0109042d040680802c40b42d08581481220111500500058022013014190010b1458020000081000100305401969859100340c001551082c1d0f81aa02ea070740801c00d2004201c04900c08405003ea20b44484e0302148048041d24112581010915039014480000762076003085444000d405100120321800520b80050241d88106004100c0f620125940c14240e0b503140650032000f00203010030030118002c20310484540b4041c88080c24010400c1400385421165a0403461504005030008041102c01001e540004035030003010707610034051001c2c8480b00403c0c201c000b402c000e108000f0741544004690045411502e00200190700c207446503500d5030700608152450880720310724440c1e8400454660315045807003101918000745001a0381e1004504a03043d440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 568280467 1250 568279217 568279267
    0x2040c050d0f0903030b010302030f150a090e0303090118030c110a08101407030605031506010c02270c03011d0403090801060603020d14010501021906090b0f06100f05 73
    0x8001840312000315005400340c1c8502c4800026550120b81001002c5942c90310020b41014010401e00403491001c8042c0c1d030b0008024801380c0b40d0101c1d203400049011095510036a00340781071404070440e0b09008800356200b030b07034124024003503040d83c80700e14000100554002404a0401c1c0241404141070780103504031000040c00c203030141030b02c7c0d240c000d20b002d034585041503060b52201c010aa600c0018014660005210304041c8103a80c07c0400003a00c56040e610b002c4c401015140000d032b443ea01c90442d0800c010740180c803074240d401c00381680041c04004200300d605040740d07500200d0b00c0c0303030803800c2168100e540c2c000b0060182ca65081461701c01d00806003003a81000500e402c00316240c1002e01c20030004101070f890041e6112042c1216806403640c10341c0d6168107544e250010811a600440d003044074148444411154014a2a01900034084400c004e092034800c5d104019200316040c014601900088542d200400c1d1030340011550b20001e02c410320006001444031884130710407401e22038100c42d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 568281717 1250 568280467 568280477
    0x3152d0f04030318060c0905040b01170a14090d021b0f010804050a0c06030608010614010c032007030303050103030305060a0f120807080c24060f010e031c050c07081902040c 76
    0x1032030f40e2105004c1d9a000e02540d416aa0b0010901804e80105200d0024401030740d09000900b08003002070802c6000d0f141d4402008104800200b04c0001940102c000c1e4840c000252014186004070540e60304142e41404054414009016131074660001a20161000107041d4409405014011100c251000c0d104130790610500d280c000c0050684502d003030103400c0a83e030020380c003840d2030103e42c29103540e907001965146910a400c072059920a40c1c511805803d4104821880e104d00b04580c05072200380c800f5580e500920358044209941601f0440c1283d000b0340e0140301a4841c002004400e5501c0d100d2a94414a0041d00300321583c0902c008404c218001c0c2a52424040c0b03a0b1240c51060b4031021714005c0b10b030004881c01c01d44400308490300814400d00001c2c0c81c0c451400c8004500d50391660b04445050046811540015540030819101185507000c0c00b0714001285401c051b029070000b80c4c00800070300841d40080341d00b180000f46680d20085220101495010540900008059150401041003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 568282967 1250 568281717 568281731
    0x61c03020a120206160c050615060d0204030f030306410d260c03030604090204060b0d0b0a05060c0304030230060910052403070503152d0f040303 64
    0x70180001d844109502d6009044185860a003805899845940354824440c85030b00d4a0049900022521345c07201000300c0680c1643d80004c005800341c040c0d00c00300c40d581400000c01208018211030a2142c583c403c0d2012301c030b001d8585915400030000c1ca00d2200400c003000000e07003078499600920a651298024400c810080004085000c40000a030140c945c00c11264041c5050b0000700070500c2d07001d4901c20402c1c10002803c01c200d03202c1c0303c080d1103e842a9200d49207031041d950303664001001408003800d050350305c0d103694005002800010781c00170721330948024000342900300b8500304c032042107201025500e02400d681c200010381c07100b10b03003d00001c080c036803151001d840c100c0e807a81c112065500c020520362408890b0300c1d151003014454044054201410300024059070314a81c80207154050304144030800050100e85046051f502c680d50501c07480341248180240450301d107002d20b180034200420030003041c1c45c8031603803032604042c0054440040300042c0139405185005421034402d180c081851 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 568284217 1250 568282967 568282973
    0x1a0a140405150334210905010b1003020a051e121e0c0a0c0b0a11030106030b1e09040308180d2604020307090c0302040e090d1205061c03020a 62
    0xa1280d01c050340342da6040010034400090200041200300c0090040d20001c00c4003110554054811a0403101091042403031058000a0703141642e0303800020b0300740003001211803604089019103080b2075000d0040d07150200c10f49040c2c0c420700031250180c1c00b40c1ca500f441c105000d0681e098404078404004c4043c8018021422951405421540640039152001404440801d000650500090703c0c91040020400643c1441900080d10542c401d82003548808241e4444910001618402500640b418130010000c40c06a0301940108034201c82603507160040e60100c0ba0b4403d07a400b42180095010720ba4000240001e4840e559a079801583c2d03e02c51100301d103a00c07800e40d00c1d00c4100700b0311401040c0c80340344d61500306820101c1300f0300085a86071442c41030305040d00481d0f12440d040c090b001d10503491b201c2815803503009404840c0205140003440200b80b03041c81c1c1158941d0702d900340d4400040c1d442d0b9800403901e19140582405460020661207624070300e20b0301c2410700b826100044007035003e030300c8808000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 568285467 1250 568284217 568284229
    0x2060c190908120702010210020712050315090a1e050f16210b010e030114071803020312070203010e07080706050a030e1009020a06090e0f150907090801061a0a140405 73
    0xb240c03c0d0090318075160442e40c030002e0304080d0701d520701d500124414442a404503560b916040400499030900503503d131144a00004d0b00010080c030b05812250749018080030a415512070403e40010307503140703032850250903080826218295400c540310140e00f40070034082c4280c0384d00b4039000901410f08805020705042c113068140e11006020301029602c03461401203580190314036a42c000110002c02c030b664a400c2ca14019644060450001c000c0e800180400c0f0840f0000310b84050341d00103044821400c942480e005442d03108400c101e0195081c803034880800324002a0340e200b035800050242002504085007198650001d000c2c6104258880d448868001000d000880103001c04010101b49280c10340140304803105258800c000300880054200180744501d01c1068200020b07110038003007511050346d000d111804040a241d4015449414451001c1d0032007030031422070302840003d0144c07075500c00020304104100c51111104000800820700703540d100c1c09903640d0120112000303604044c3c0328030100c0d40c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 568286717 1250 568285467 568285483
    0x110705101a0907050904050c160f02010e130207050f03120103241e11030601050f1305030102160b010f03080904020d0f0501081605150f070c0e0a1a0102060c190908 72
    0x1000c91800140800141050301500f03508c00c2c03210396440c1c900300b04200150381d0b0440040c0d0240c10742c010302410204680c03060100c6000b19200030000c114024220b03000500130360194408440501c103c0780c2101000b0408010390700c001e15016a000b090741c1c80d54541d00840b000109507540d00b90f0b0045464004214117120340c2d000c8070750106a02c48001c59001e60082220410380644481c0c0a00340204030940e1380c03050442d5129130b00000141d07100c906103104201040006e0b0000c5500d0b50002c00e41c001c0e640d50011507100c0c4035003e03400d0161284d03078860800301100711600021300081000c03c100403503410b180d0010101c1844400c00000c107048038040b030030100ca000307030804e40b4140c004000d220007601d055010040179020455100048400100c00c0e50384a1080a1044461180126001043c0f1184404020007451360700401840762405400c408010405100c40050240c0c1c007846100300c3d540300240040c03040500d0441d0360b1800300a950540c51003102029040c2c100450000041882d02042c08000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 568287967 1250 568286717 568286731
    0x1f1503020307230a1419030c0504090201030204080d03050f1b070204050402060d060b0417031305010309021c0b04200f010302160f0b01031406071403040206220801110705101a09 78
    0x1041e03055100082085c45002c44041d0b4121111b00d41c03051002c55540078682048800446000540c003001c2e10042c0c4c041d000703d50021025009010003420b401c1d0301608420310404030300c0400215a84d4136000f00d0a003808486104080001c140003100041c100340c1c0c407031a0402c2c0010f201d2400c2070311804040003074401503003010084c4c480226003008112211528008000304400285007410700d90a030fa00300c0c0c4441c0e44a024101500e800d10340044d034407030324000901c510240c0340300708211540d818140d00b00f00041d60200c1f0401c45415080500001c4140c08045801c4010820300751505102c0c011406034204c3d82030f00114002010720040040c4035000e05ca03901510404111b2450340c50341c10500480120107010b121540c00c407400300041103130310000c6602070a2440034915103946403800071030390710b0044509007912442c5680380300c2418955100100c040300d65150091103007105102c0341860038015904024546e901a290003000c815064001240741039030b810711504404054400a040c1e884e040d1f50071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 568289217 1250 568287967 568287989
    0x9020405100602010c0c0218060d080a02070f050103050c0919170a06060f0f0603050403051c09060506010201110904020c01020f0304120305060102071a0a02010e1f1503020307230a 79
    0xb003008540a004124007000c59003415248090340381c000ca40c0c0059001c1311000d00c030100100084055984c414030302d50698103d2540c2d510f03034030203441c041d41e10342e524041d4008840d000310700028151710074054980f1481d400d6440c0c0c2d04004051050055080020850148c0d1403442280132540d96081c4a0368510031082d00000c0507091a45e041400480341a500030080400143d40300740005115204000212420742c038001426540e41d040846081c0030b0180d52594201f1340107030b010f03450242c9d90030550000d40240b0041180c0d41302c590042e82281d030301e8204614441d40c10700060b00c8a15103503010b00405101d842c005031426002d03104225066100700d40c1240c5202115000003a80d990512074998028400c0c001010b90b00c0c1803080c050302c0250302842c01c00d607000002511407403a9100790040c01d802e40620045a1400075042200203229100358800103000e4504032a0b8450b050201c24000304498000e0080c0c00c106007448115031000245402e105440320002100444684840d09140b000b49001404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 568290467 1250 568289217 568289219
    0x30c06020a0221120105010c0302010e0d09080d020606010e0105071403040314060c030702030d0b011803081b01111608070b0f1b07120305180a05031305030f030405040b040902040510 80
    0x30000440d120500000080f61042c029040246004030146054031824208141030a08618049000d406200c48140707003030041d05c16561100e42c10100c80803d503000001500c407041a0011f080340d8840007204d245000440441841e00342e5402840140341082c042c04640000400031a0054556400307a0300842e1403840412500048200600405410140c81c2c1b0f0028034500b41018001e549002d042080709030560740700300211305a80a20600401c22510610300d222580d030b40d041515040d000313410300100c2c407000c604803480440740c1803095100044000c043c0c103082200041059038900c055410480c1c03010420031418ac08110b2099101b445401c810700b4100752843c0000e0041e21450903210f0141c0c03a000d06000c00c20010345a003040b00c007554028600054295649040d0700304003a00c0c2c03d9214980e0013583c1d284014001c010004101c0c41ca100039020000c0365440e018144d07550281d681200d0702e60070500c0b003400316280540146940713a50041c00850702c3d45240e00000c045540c01e89030503204102d001c0f4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 568291717 1250 568290467 568290493
    0x60315090a030f0513230306040b06010e100909090501061212021606120e19080405090906040506010e060d060608030903060c041412010908161b0609090207030c06020a02 75
    0x1c1c100e049a0249031071303400d20441c26404403a0705014081c428840c00304168144108110104000681e000201211f005040c1030501700801c00342590510300181820445282c581413004414480c0f200f15581c07602941e10b0503018400404c000c402c2180d1554a44200007075880c0180200b845490144034050b080c00003800c07000e442e00d441d450003148040e0040c4010080950420300c100b42c00040e049000c50040320307401da010300b409110701c0d9030000401220f2415050241c3e04010780142c9a05076041241900c0300411035640d1041160000c2c9aa0f1240c2c00500400b5903c0030f0003274001c6400303405182c5098442d0f460f482652240e8021010580c8041494000c0e45000c1200c0ca402890360301c030300b40c649414240319a60020048807000e00854044581c030f1103400007540300990540c1c01c5095540ca54650446401c10440b40141c01e41d50b01c21840c078060504000340c10024200c0302c030303a1a10b4984034074064291001e5005800150117000780c0490180118000d030004120a0322140c0c050100c00f20012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 568292967 1250 568291717 568291727
    0xe0708070603050a050613020c070b0d020d27021e03060c0304050c09011a0715090819050a0c12020309030a0311010c031104030602130f090903030f020918060315090a03 74
    0x140301800580c05c210900c1682c1e20348400e0b4980800e020040540d94801c4c8950007864030a050340803c21131070780081c03d000040269130260812940300241803103621034000d440150010b0341d0300807103044000d000c04880140b43c500152031081d80007001e8607580210400001c1c1c01c0c01400ca0f410301c0350701c20000c108400c01805005124210f41e081340d070700503154144209840500c800c0040d1031805e42000030340c82e00303014502e40f001345070042c60001803101410903d8162a01d4002d00500c5403515403508400560f1030040c03080d60010030040e90303440b010070102d45840c0950212907034050103501082160090a85050154468144c000c2c4ca80340810001100d4150071a040e440400741050f14100e007201c1c011180504540480b60014400750300c5180c003600008009800e58003071100014144c8002a16510a41107a002d42d07000b41c80c10092280740000c0b59050740b0a0011041e40541d4a50400503036014000a0940010015003180c1444200340c0e201e201003a819218940b143d8081103820b0101a808 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 568294217 1250 568292967 568292971
    0x70905010c030806090711070308040302090112170a0309050f0f070602031315020c1c031d13050421092c18030909070f120b0f01080603010e070807060305 68
    0x1c1c40e00d22407076900c5860080c040080502042c1c442e0180801050319640b260702d0141820007003105691405503245401c01d603d5002d44004c901901a20000052021482c84e40407480c5810065504450403d40744210003a806a41c656090658030007030760340841e00802480c040c5000c1300000702011000c4004141c83c01c86958002c44c21940100310000c0340302154461740d0308803501c542e0441300c1c0110b07110f41a420580c00fa0401c90b040f1401c03501040f0104070504100c0c42040c0252100c1880c40c04450b070001d80b032140f100c441342d0003440c1506c490050b8610382c1d0219500038041c2840c404611a410810800b01820380009000180824030520600080d400600c100c200d40c0c10211000141c00c2e03044101d04c43c0c0042210703515025040a851044505000300d42600c2001070040003680b03041803024001501020780c0f200000c0c1d52940e0100750b1183d500c258880620300034a5410040c2d030440c011a03240600034103240e015522144c00300e010074010004074010702780080190851a0402c2401800c403600 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 568295467 1250 568294217 568294219
    0xa0b040e0309011d0f060c06100f05010c0b071206080d080a0902090414070506041d24060a17010308040503061f03030c1a0f0a0b04091101051309050f070905 69
    0x4101c2002c07507a1300700580444e0360411400203110311041e0700009110595402015401c510001044142d60303a020800510038000c0110418690351100c12500421060f0302965012551103940392000c100c4c446000b0394890200e00d09281c0d900410400300090f10740680c80b0480d154001e1015820300c541002e115544400000300421910a0680014034490000f910140c01d1207200500d0101c200d43c1400b003803001c0d04000d4181c07a555981c85002c48076041c241c1c40e04843e007ca0340f030003180d44041241c0104418100c0140315444c07101e141010800b56074810b580403410f108910b0440000c408081c0c0000340218011320b2a6a12103103464245800c1103401001c01142c10000ca5046a100d00c584c03240e0001d0b203030540f82c6803400000a1410400600b040407883c00380e1401001044040891102194480c0713100113414803c080001c0c05000a03655a9031001701307201300015442c02154032a50141c00302c9240e010441481c156a040c94004540302980c411140100f66000c20054030341000c030300002420 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 568296717 1250 568295467 568295473
    0x503010b090c07080306060706020f030105090601110a0321060807030308010b0304080a0e040e0f01090c05041a060309031605010b01080f09151518041406071b0c09050a0b040e 77
    0x1820303102e004071901c282240103000b402c0100110300b03151103800541c0d0031a0352000003190380340410507003e90580c0092044910a1300040006507013548214410104440c0000042580304400c0d501a540c0c02d00d09101e8103002500d007003042d136000d2900e000340c10081c0b18850140003c682581002401c10405801c002c0c0081c00c00c01c10300001aa460085503070009162070300c0e07140849003000040160241d0308007140d080c0308004000154090644c00300f96020f1282c80202c0029a80b2070620042d100303074030484122074050311400303686410908000c1d46c0c0881e400050b80c0c0342486410900070303040225081a68036030f41d501d060032665600304904c0d070380103506652080418034082c06071503a40d006051400b4060210303100480c0ca0106c44040c9802c807210010520761800d0a925604501704070104c40079030b0001800c0c4840c2d9520000850304030b001e5213065446501c100c4000718030003103064102404641c880361610002802c03440c00e203d0325004002d000d80214a0710309d84c01c200402d030f542c091031420542d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 568297967 1250 568296717 568296721
    0x12a080c1b01020d030e030f03161e20031603110d050f040b16020604080d1803020d140708061312030e492c090405250503010b09 57
    0x10fa000501100c041400307241c0410011084c030480303421400b82140c0d040d800c0e84040148034907481065410b06041040e0790300d000791001c13840c0c405140982146103c0001c5140150840440110005101c03c40d00d81542100e01c3d0420070090480030b85046881900010880d100101c8240f40034800e243e41c0c20580e14110b400c0c002000148d9495111703e01c07488299a5000911080e88a8103a400703240c0e284d002020b00f6140c070380c0c8a042d50344501c1405980301c001760950b849460414412a13890040d0b0740c002c0c4c400100c465160b51840c00002c0511500324091041c0f00c1e000407450410800740e842150108250500c0e15044d18054080c80c983c00818130900d070030501440c0040d5400914860002100d9280d0101160f0310f54104078001044184040c0c0312004c41726501c00e00c031a2225080400c8426032301d000d0a1310350004810f10030074800090b0034400d4000c5021001d1841c5c0540a00e8202c0d0051081d0707540c0e0500d100101744503185281030301c18041a4240e0800140c5001e104402c5c01c4d031000d4401d81180c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 568299217 1250 568297967 568297969
    0xc080a1a0c0a080106030225080414090c040b0306030f0f0d0f02150601031107020d111801210c150807080c0f0409020c07051504081902030309012a080c1b 68
    0x400c0b014000c0c001003640c0840d5030300402400d61202503009000c07610800404041c2d04140709c440d4081d0082d620100407081c010002410050401440f494488104e14105824040100c0f01e583c8080c10a981c1842101c0c00f00203072082c10700c000c41810803000b00500d20401c1403200640b4200d4171080820a540000d82c01104034203500c032056038001424a400201d054000424003014011900080d400500b0402040c0800040c25500c4001c0041144c0d0645501e030f003804955400701c0c00f4081c0d40550b0701400ea554004062003840541010711a2845041c0300f522210300c0300c0d44240e80742801c800605030764140017055400c2150950003c029100580c50020f1000301c104641c0706500c81c0e00b150590010340601f120f1800d200303440c06000003e115000403d002c0c0c03418036041e080342c01030b07041a00070700340c1c4d04140c0c030080741032a004254003502450030b0072070740c80040d074003081202010000b10450b0171505101014248400b64110b100300e44003500c1e501201c0100d07142a032006440850599482400396603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 568300467 1250 568299217 568299227
    0xa0c0c0b06040509030f0705070f0b071716060f050a0b0f0a03021201150609030302100516180e090d0e0f030c09070201110f0702120c0114070c080a1a0c0a 68
    0x3200741c0036200451a601c0300c0009629611034900412800c1c0408034010003040b0000c24458101e4441c0d2a02c0107001e034407035130141441d20035074900500031080c40c0c2030944116510390280862243c00c0c290b010000d4415298032054410179045a00e003e0365420410909200e54451030329681001da80803060a007042e070110f1455441ca00019120f00d16044136144c802d0b0094100c00380e80c0540c8500c1510242d650280500090100d00080703000d402106440b186005d41885014450708030407040100060101d41c096a031540b1488070201c04a824820119030f44600d04152409040510018100d00c0425040100034006c01285584500c040d260440c5803035400140000d1100c0d01218505625105c20006a0060501c0741c180202d010300800c100844030418801360100c03a000f92594880352003140f00054441e210801c4030360114030f0148052000c0480f0b800a1322400d0310034400704074465101d01c0c0c92843c1c190510740c2100c03a410381640c414514a840e03008030382c21100d90b4800505040140e40c001e0f003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 568301717 1250 568300467 568300471
    0x17090d0f060513200303070204090302010c121b08070309051c0e030601030b0106030e0a06060f0f0603020a08160302130306021b07030506060d0f0209040f050c15090d0314040e0a0c0c0b 81
    0x1003e00349922044c0d01c0d0750184122a003031580100300308419a10f510740607000c1c101c1480c9040220b0103061545084032030300e003c2da407a003210312501d1003103104100c501595210341c080c10050403d6507030058a0000348082048442800841d10482c01b91030047c0c90050010070f01c180c696001e41c210b00b00400024001904180c1504e48506004c182180400e80481c6080382c010030142c040c9040410004034145170300340360750a45a400c050b40b20b8041d01d0344425000e91248660850001e646000041c054245160724045042064500580b400c1513002400502d41c01035001600d00f203600040c4554410360413411408c045081034042c0071014516110b40780c80d80e81c01040540112107a400020030051094a60b43d01d4660041400407141818202024003043e18081200e982c8120310f503800e02c030719041c0c007100f481410300700340307286448030325000e01090100300f00049080c803211210030070200b000b4801410103401c00d1a50341010740f03040c8005400790707519100c0840510481156213000b241e05010026 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 568302967 1250 568301717 568301753
    0x21f0207020f031506010f0e030c010e0301060810050a0e060403020703111801060206070201291201020d060303110712080d0203060a0317040302010810080a17090d0f060513 76
    0x1616150140041040d0050003002c440d89030003140e8898004010007a2280d018441c2a40c41881d401c0c0401c4043e1140c3c00d41003542541035005c0702544203658410301d03029000510160010070183d0b960707034501e89811000408910040e450310104410410746218070105000d108d13000b464141084d89010303444825500001d00b003040c10455294480d00c5968003458001100c11010341c2079070792100002d458000070359005d00103500b0038228840f03081e0544ca0080b26062100d0600441030034980401c5080d02001c0b5140155540900080441e0841d6110b00c900860003911040740a000052825003480c806070420314042d1410b20110b0082500035080e1085218a41c80050703403501c4201c005404c0c03145552006160035400d450070300c1001c591101a00c1100c0c401c0e00c8000c180d8030f59140c1c4414845250003103040f0790740078069660220300714011684c0c100401003d1a480c04d0a004041058481d9900040d5000b5a0303684000701000004c3c400d055000054104101e11110150740360100c03868885409 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 568304217 1250 568302967 568302971
    0xe0a050f030a1e0e06070b0411220f0f0903081e01060c02010c050a0b1017060f0c092103130806090a030e030705130501060f1404031e05011505040606021f 68
    0x3031041c1d40104c0000a291900400380c1d40c584c0c159191404141e402100c080380c07611108005582c1d207040c501111001c070203100e0034000041d1607031b0418200401000424148881d10381d005a400b44580380310b150102402030b40c0702442c51800c003420b51104560340301d202c003101c5850001000940e41c040c0301c5011181c2c1c240b03011400740b0b00504200d0b28013000d81f00301a108031890001d02c2001c1e01071040300c3c0b04403030020209201d00300051680740d466420172074626044420740c0700005c102d14070240c01050030a8001300b1101d2040428903c140080200c1c680300c0364103500c00611200c0c0d0b49203160b1210018240d6400a10091801d110156114445510b00030240201110b6046040d502400544090400a4a050a0340b9058100c50007e1329003882804045407440100700f0526200f801409401038003860110b01d01443c6030303194610341c050407074800b000c418001c01e44400120700703015a458001440000c5503030581808100002ca80c02d5620060a40d8000040030404581d14014101000844500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 568305467 1250 568304217 568304267
    0xb030d0e0108041a1003120203090303090d0218011d10060f11030c030c160510050f0c0c090a021335010b12060108060a09020d02060a020a02040e0a050f030a 69
    0x31404e40c20300109412040d40030301d04208080003603001280411203009130624142d00c80c50103000d907202c1c403c070001160143c10030031a4052a0603c01c942c1014a0302c081e0600c0030440000541d000c440700280c0140080c001441c01e403a113420307a82d130506a0000c40e50150006c68a103030a0303001d407000032100401002d102a10450828208080c416aa40020100250707950340c100343d1407685c0c07148000400c085080c2d82400000c00c080c204140d1090308194540c841c0303803800c85200d0201e060380d084045011594442c044012a01d9205c60a03c4d5008080010015841d42100c01d0122903134440d68018010500c00d0411031048207040d02d04162100c4003141c12615011a0b00b0b6081c0c3c050011004581d4114807401c080c0d11410750300041d200d04881060081e58140c0d180c68080c60281c907410900603510011044945025180c5030700204001c51a0780125000240641d0208040c0e54088540326860f41180900c00f06105051140400e81c91040c4091480d1140d40034000d404540d030880f480d2102c818500c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 568306717 1250 568305467 568305473
    0x3020f04141e090d020d181508041a070807050702031603030f02101a0f01121103010501030e03130e0601020a050a060b1f090e370b030d0e010804 64
    0x101024079158000400001031074142184041001c0041250381d6000d00180000c401c240d000c41e00440c0d03010250701078400c032a0031078000c46840b01c05880000210140d5080042c514110340c00c0c04107250300725164400a480c003400e01400600356001100f8501c0c40b044200003005a005511561011450909548800e40c500210b0704d442920a215040181450004014140c02600340c0750880102d50031035040e5081c00d5820015600c0981e4038915071020b6081d41001440e110b9000d901e100303018500344070703a65072041400040e1861110300031207002001006100ea561b1500034001c500c02d14400461410014001d144001c5440f031180201140e418800326503d40c0c4248207498080350030800300c0c1c5111001d07081100042ca0400340191045145011b82c91105900744180d10781010151910400d483ca040c101c07510400004280407211848068079004000745841000c2003022800d0060000d20382c1c52a08100319208074800394402c1e480101c00400c400c3d4800e089014000d028a800485500c841c0303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 568307967 1250 568306717 568306721
    0x3020c061308031c1b020601090504030e04051006090f03020609040207030201090b2410021507020708031804110405030a03050a0507060e06090705060c190f08070b01090501050303040f03020f04 85
    0xc0c0042580c0d010010308420401580d560744004c060065508004031000040d000c1d0520513104003100c090f800400041111070b0181c1c1c0b040d54050302a007001c1c9440035205001404556044810b102e10760300a100501c0003562082c00a00646401000030500b1419a000119503000e440710303062007a6000030f500400c01d072003900008103d07640f2030301c40e0a51b820044c0c000d80d0008916443c40600350030302850415070b0b2816480340c400c0c500e165009804803402102807a40310440c028101810346c4108100026a000c040004003007881d100c030564140d0211020400058400007030a00d01050400e1205109030398000c642d01d0701955160500e00d5440e0310180e000e81d03039406487c5002d00180e2a010a003100150f02007026441680d0803130556289540b52000c002e128010316000504039446868443c1020784188040a9001d0044c698526080190350314095542d00c8140100c0385000618010003440030382e4003946001d0401180918201400d2100102c08054030384030180c03040034410062103041d1a19 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 568309217 1250 568307967 568307969
    0x20d0807020409080c1507050a0c0218100e06060306220b090a0e0609013606060618090e030901120213091a19050111070807180c0c03020c0613 63
    0x151040c02680624282082d480d04a0002e1030700c24020030352914203080c0c1c0039110b00c7c414141501e4090034a0712040044440014120301240c10144000e0b51840c0003241038180d0344582a078000c1c0030300d91414003680c0200801c0140225000d1030081c8203002d9141d5882814442c4d102001044840c003912000090014000c4180e400fa007208400041c003481c44000d80050b2110041c0004480c002e840d460130080c22102100441c41204a501103880085220750201c007c1c0c0009404044540800310b445240c01c50b000c60380014046048148031844002c0c90a400c03000901c9400d500b007040d80b402e07410312501d9100b000305440c10041a0f6240c012013405940c142c40c4000d815007080386104d901d40071541c0061130340e03540d5100c110300701101c4101140742020100a01103182440f0805a43c500310056441d0020241d000b405070141d6100880c155208000318001050314906191418001d071030000119440b09001ca07080080340e288040220b9000504039605903402d5451964075980b01411403400c01c56 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 568310467 1250 568309217 568309219
    0x605091e0106030b011e031101030e01051005030111030c0f030705041e0305010f1a040c11030d0b100504060516020103061d040b010e040b0a09020418030c0c0e0c07020d080702 77
    0x4914104800310540c03046050324072901c809071450b6221040c640c019104004d5074503a07028034403018030003d402102d01c003002c404d0605010940585520307620b030944034111207403060003000c01410070a528003400f41c003001240f0f1010031880c41c1424814440a0311075807824188a0000001040c0c0181c400d000302e03070080882c200325074032805009200015103d22488107549543c00c10022544031101c2c1c1c41403407550001c03164101c00b50100720040c000584440384006003400100c4101d00c4e00503800b8401007220341003540c40007030407a00080420086000d40c1e0031300f400300402480280300300341c0c000c0104c45191810780a0340610001d6440120040c080301d4010003280f805032904403561080c071200300c40c00b6070310600ba526216030b01c4130020b500c140812200502402000000714440c40d41907880301e15030302d0000d07001107030352245041c2e98000c00380c2010040300002c81c0280617805100d0b800301001c01070f060760b00481405003400c61520b00140a6428084d20030780e807103e4000100031b000c1e0101d4484a038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 568311717 1250 568310467 568310503
    0x60b011b1202161508060f0603010e1b0a05030424020d0b0f3a0c1d0a09050c0f0102010e0f0c0a06050406080a02090f09010b0c07090501080307060509 66
    0xa649007200c409000c81d20303000054810050582110583c0e41900425198400c04001443c1d900281c119036108000e01000d4020b5040400c4a0140e02c4010003103010785400c0b40313403400303508110700d061416a11210241c01c644605110102034558001c045a4002e50800b0788040103040c60011051601c80c041215040c05100003100a021443d0f40c21408040c401141d0321002c080d150000d0002413a48070b400c003514202103203220706598904035013400c0c1041c8034408001640708990f544001c0b00f60b440d01726110b48407000c51060070760300c40302207440e07800480c1078024031580041b917407066541c04a604402d03101c2c402c80d24641500364400d510a00303208400c2811201c00e01410740c0050b841e00c0714807180a014008161020031a81e0084045900700c0381280e550010581d14160715800940169100319408034132002c20108a554909506001e010b0b1410712960382c503000c0128a1501d00d281c2e016041250401004006055000c429103100c1ca801c035802050035074074502032a0400b01001000400a2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 568312967 1250 568311717 568311767
    0x414010209030105070e010905090610030e12070b040c0902120c1b10060806090d050315060d0903090524030402150412080913061401031104120609060c0302070807060b01 75
    0x2aa0001b0701d00010307102a2038000586440c1e40502c1000e5400700c4035603030002d110110811655220354000d00c00f60586905541484802a244000c10380c01000c0070307602c2c040d0007000e220a1144070501c0700020301147e4421840c054000b41e6030600340c180144071a40040003c140c0070b10203503240410140860400d0195400703a0640402ca600504080c0980040340c45460005601c2c2d201c00188900c8400c070310b454460171907544c0d0100d600f00b41240004660400410300202020504178001c40081d54440e071034500d805c600300401e0240580c3c0014800561040070350703400b1103040382ca5080726042901075410042d003110f4550000114441c03584414803110040204206100e039880107002c00400031586c0310039059100d034410b010799589006440701401c0c0b0300c000082c06e60103544900c00b0100c0b81e00d6464101aa9580b802c4a14101604240e502544400f010010440148030348000c0c7c100c2400c08505110043d00d50360014041d501e4010081982c0d14000a80b9a010b2413807100d042c0c80e1302216080c54 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 568314217 1250 568312967 568312981
    0x6021309060e010806040506160504050d03030507030e03190509061308030c060a0204051c05070e150411120f04150c030c1206080c060d110f041a030105090414010209030105 76
    0xd0499102d01daaa00c2d807100b0010460540101d143c2d80110b41000c000c0c48c054031405200707003558105d0001c1e0f406100d03007000005920f0311303002c0e4411109030194034005054940a403014040c0c030401420080b0b40d4000700324072041c0a980d41303050041c0560b149402a100c480e0940843c4e0f04d44503600401c0800c0c000c242c4001102c800000082249421110aa44003134a075110650140e0185016180e0b21080c0b4004aa0303100c4c03914065111103a01513012904d0403079646d541d04005410641d0341501d6009540b02c18202e41c1400e0082c0c8004013626840300e4900902004000d41c0740c54050f002e4804400c1e200c01040c10701985c8441143c011403a2a001c200d0540300e000d010700100f0207602e003800452501c1c1c2c3c07149030303842151145000f1900300102500c6138008807410008958000480c490301d4aa80c1c03401296400900005000c0500804892660355400e00c100720541024240e081182d81da010001400380381c98004040d6001503100003200d030100700c0d02e05800c1c0079016050010b0340541c41d0404001076 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 568315467 1250 568314217 568314221
    0x50f06040201140d0b041a2107090b220b010f170609070c060c120b03030a09150309051b1f0906031805010227040b0d080702030a02030f012307120906021309 69
    0x1d81c0003248ca2100401203607001001e0707080741c02031020b032070f81107543c0421028020350042620018000d0500103030800d00c08101e158a401800c0340c1d8155075850004541c2d80d6040880c1c0d6000010341c0c00c1030480080031b0125074100302c0008120724007480e0b481010941060007104910003265000405110710703002603d009010070714400ba5002c4140c04c05c000c10000d41008421079410710780d2503881d110202d08040490111009281008040555031103880c004214140300a64200f819080540001803800c403c002151508804211000364440ca01c4142030f900305240508884e42d601f00442c12040c034850800f1580c2600d18061300550000804005010380707881c9403134150840700501007084181c0c509200c129401d803051b0940116010b11403038003265000020303141c6036100400710b69070803003e0703030110f82480307581e500d0100746070744841c0810008200e070303561003d004000090700c22140c980310a00a1083c5040400d00000990300c107180c40900400d40c0440f43c50700140c04d51a074929642d5003203480 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 568316717 1250 568315467 568315511
    0x601060e01140c060628080a051b100813080a020a12050f0a18120b0414120702130b0429030a08070b090102040306090807050f06040201140d0b04 64
    0x20001d200500e80b401a005002d095500e04845030005002c00d507101400c3c0a079aa0705004070307a00c0844501140c00c010b804501a42000d003080c14068216000607181c0146815070043c090b81000520f02902c407081e03156000c01d2017082c10246424100c80e159480e90070300c200c41610300a040c1c4600001c00501ca5600040c641c440c80d40316a000d5206c02400f400111028060781d0850005e0030002c10a411040d441001085080580d40b03888044040c0d64100206c03140428200807981e10b2035190403c8140200d65251550b414010005030211281800e6001407921800100a11030071841c10401002c02c0e42d41d01030100d90101400802c00d0b1112034151055401d4040700e004185001c0b91102d0b0603c3c140418810b0405078131840450500310390307580d45441040010080101c42d90309001c0017000c68198000c444419000d206543d070780c0c040e1810590300300848000da0560960201c002d000060f648008060200b1032404043d40c2c4450035404843c026241161245a20905000d5941d20351007142c00044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 568317967 1250 568316717 568316719
    0xd050403080901061a0a0918140a0c0203030a090311060f100f050d080c1203070302091302030714031008060103050f06010816180b090a0c120e0c100509030601060e 72
    0x100d0142d80741d099507400c0e40c416000344000029078507406104643c0031400341411005a042000c2801e0303c070551051124012503a00322860b4807001d03281b1a410161201c1c83d044030760030406109117408114065520311000e020305140f10313591641d510038140f29038512950305000b102070715246d052408890054800035211081c180c807480400081110b16040e04030308039180500014041004c503141c1c1101038026250036000c5000340141d060498007004011441000d031610010786800064051041c0702c66a2542d1001043c03041040c072004503044000083c40e40500f0316103942d40d680b40281c4581104490b448041d0910801c40003004011000c940c15a54440d003504450180e0f0b030341c50240f6540e160411310350041ca030700340100b48000c0500103807107120001d01c0840850a404007502061070450120f5420000700e9581e010040c00507480f00b0184081454201e051041c0080c2d01c14581e1103000c45140300384964071a07114025410f00910030f0307542c210741c01803e55010790f9407040042c0c1810360f9000700c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 568319217 1250 568317967 568317977
    0x2604110108060d1707030302040e0c041a0301060518040b0604082a010c0b04110a03030c05060609010609120c1d07020111040b0d0c140f040302090f0c0f0304060e030d050403 76
    0x94590a26000f60100c4903003000301821007090f12180d04007541d010b4402507080603000c003c0806c002c0030302c500107030003020b41e48509a952884c1080c89501d607c0303c0220659102030400042205a030702400f600d901020292090004007901000200103000f0000500e800040c045400545c9190203d401c02c0a48821242c40c0740c50308898081d200445203580c01075022a403804c0b800030104e000001c5075940203120b020b014809544442c00114070428903070080340001c0c10703030100f40d003002028050b0b40d030010002c0e00d500c0019410100058a8030246010b404400d5844014980901042095080050511503417003025170b690424041581c2004585400242d82404041d5074400d803201c088034119203006282da07003010f440d11110409000300888480403c81c0e82100c2e8000030203420001e0115485003410250740750701d0f40c4107200056000a1410414101600802118811480c2190700001802540300c0d600d6881e403511030000c00e04040e034408544808603029145d003500e6800240220300076116 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 568320467 1250 568319217 568319221
    0xa020913061401030201022505150405030f0d080613020d110405120a02221b0f120e0a0602030603100f06030614161124011e152604110108 61
    0x2e184841d0001c0c440280142d12140b602d850001c807400306807040c81403000c2a4607455550384001103031904942c0b80d401f0454400a0204424541001104081d90814014028100503040068105140140120b0050a4084683c921003c850b4100c1d2521420344401300445510001005241d400a001c3c8901640c0d00710a100001e140004400d44943e60042070f80301d000e140c250f60120000d0030803030001406030b2155041e043d0412403020745c4125441d155110070440301c20703000042c00b04130214a5100494a4a00300008103c000f182140e001e9420120141c0d0f29100d4102007031505801c83c00d07100c90700e071409030950076000d101d400030350403039000344d5060000342642c820800c481403084d100c41c1c2d8440d03025200d01940a0280c0400020203410409494502400d11690220f200c14508101a20700296005020500110042e030b440c1101c2116100e8005003400700611600e00d083c81214203001410808010030f103a101d50803a4100c0030703486028485c0c00d10b03103050300d10042266841c80c08076a0781d0340 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 568321717 1250 568320467 568320491
    0x16090e010807060f020723060d140411040603020a0323030c1c050301060e0906040605130f140609040308061306030312060501031b1101091b14090f0601030209030a02091306 76
    0x6d090b01591100141c5481071181429411682d000d07519110750008018444440720000a1180c480c81c42c10a94100b010361500e40b4000e0800c0300c0c807982a03407013603103410414800b5854600a00098a074040503c00841c03000054520010b03c0c0d00301c00c00d44030b210000d090340810002150300903444040d4040204103a501302010b4034580403d014040000e4802c06403a0b004c2e2401c001c1031034200f030001d40000785050b11740001ca8446007007802c80801e4075484100d4200610b41c603104400a003948441d10364240c1c00e01400150f003005024101a04120780240480c0e8240c0c5d07034500035905c480c01060f08000301941c0f403030302030300310140c410903230000600e421000560765010380a030181310600091003400d40d424051040d121610600440340301503507100e076540c0000d0000c041c1c01c0000c41c0f0807104541101d240528400b6078181c490035082c00b841500e800c1c040b42080071415240c10400900f009601c0b2410240441d03c0c1891000010354071810380340900c000c900c0d0b0580c40e02c19890060702e0074813240400b54 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 568322967 1250 568321717 568321723
    0x2010e19030f0c09140c1308030f280e0d0302010e03120a0f060f060f0c06060e09100b030604140c0405041104060902090303070b040311060405031c0c0816090e010807060f02 76
    0x80e003600000000000042c1b641e25401d000f0701c01101558000e01d04e0540b03603401c11389944c100d04054412080c2c00601d081c0d0059007082d020840e02e1101210f112101e207034001c020501d81501c50ba0300d00071080000d08204160007900200c000683c1d01e0304036512980c3c19a0301c010b2485c803c0d21403a251520303007081c00560300a04c2c0500c5040d10a0780011101b503034038000e000c07941000b8982010081045621801001a400b8019540200000c1c1e07a01c0d0a1410409000c4ac102481040a5040b862070002c503810b440e203011401d1544a41c21031011381c2c40900c210303d5241880c0701c2c01500c90b803141c502420801008004044c60202180a660400003151202010002c0348141520141d160744248a46c10019075440100c5601503c20315086c1181506922040c0c681716050b5801c680980010541c0c0360442c3c1703d88800982003c1040301405640c003544c030081d00c032200c060b1031580851070400070102040d000c0d81c3c4072402001c104d4020741e010360352003074801e0300c072480390007408000b031440551524040d00c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 568324217 1250 568322967 568322981
    0xf03020a030909140c030a1806061e030f02150c0a0609060507090501020a08091f08040b0c12060108040809100801051008090607050a09090c0c02010e1203040302010e19030f0c09 78
    0x80304c44c590f0076121180c600895810081c00724a0050702c0c4c6a031491960b0466801c0c42c14180b0403940444c21a00f8030b211603e440c1903a043d034118131171101c072080010910b4880d417595a030b80c0643e22007680c5000d0b000310151504c00c900c11004180f10f042c8200b010404030303510215501340640010010350301c800f8812a6600312603c509401079000216580205408400410803001c00500c0b2850a0107208107410880302000d803914040b8200b0000c2109008540c00003075400328070703007400c5450075042c070105504640c0d024001d40d041004c06000103080143c00c604580001703030000c24800380307503000385001031900c90240102da000e4495215960303040c134054100d15010745041400b074402030340e860ba0100c803c1d41008510b0f00403c0511980060724144070f205064640e21541c0d50280e401d07610340009003d01541f24003150094260741700e644441c48020050300d065980c2460a1031802c4180b40000b903040701d03050399038940340c000c0c0c2c2000000c0203100c802c43c261341d40c420b0b00340c0401d00c0d94481141c1e08980030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 568325467 1250 568324217 568324241
    0x1312020105061518120607020c060723070f0906061106060603010320060d0c030c09140d0f0206160b0708090a02010e1206011e1a120c070f03020a030909 67
    0x240c0642c403508050740d5000341801c03d13192072142c0d0302e21280c0c0d00002c480c0d0703101410130b84850b0400300c140925280d0500c0fa910b60090b00740c42d10346c0781650940d00c1401426402114400d080207215500c295440d0903c07001c0300400460407540c0a19442d022800c000704401d100380001f00304d5100e6481c0e0b8001000c19118801ca900810942c290307840c41c0c440841d92401c100f80030704a02d850080d2440f450751102c014110109040e1000100d15494000c0601110703082613001003807004505041060100860500c031001d03800350f9449032a2652460100c1002c0e020000007948100d010a064089850600e1440b110501075038003148175071210281640c081009480b101085d0308441d5040016500500d054020484003030308111020b800c05200303a081120a820010541c010242e50206104038949000701801d040c0c54a8000191035548401d014400e00d07050100c01d004a20005180104010550b400d45d9013010343c03071008410500d8001e40b9501304090880c041040c80d080420700c00310b988184118208 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 568326717 1250 568325467 568325479
    0x106091a010306051311070605070f030c050c06010b0901020a050a050f150412030b01050c010c030b09061009090f09020306011d0c0c0c010e130e03030a1a03070b070204090b131202010506 82
    0x2000752071440141a125070108140032040091f100010858445d051140c1750964580e28000100302006040c1c400020741c20b010810144402050300c03c004c0b07680390466051020a03a42c9241080050f030610103c00c0c0068418080c50410005104010440762034588413002610161000700014042a000580e00601030411003458004d01700c1c080c0d880075411100505106040a031035001207400d54200c6008400007070b440c0e40c0d01d5111820002c0740c181d080310080b00e628282810391980200300c81c50307611070100c1c03845d149c258a0400c840241e12292040f80c003c1c0940310b4540c0c54450b2043e81407010780581400001200000e0b002d1501d03002960010300100005c0c003032110000c001141c03001c0d0144203288c0e2007246000d400d1182d2803140b1036084600101c8000c0c0d916440d0504032481190120407112880c10301f0350083c80000c0d41d02180f00c20555100601d5241c0394501800800d0040400c0e402c000c1c0b0307078100002804969110f441c840d1007002c2c4284010305030000c4404040b800e071071050395000c0e0410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 568327967 1250 568326717 568326739
    0xf04030303050c070f1401050a1107030e061e190e010f0302090a0906080106050f0f09131712010305210a030f0e0d0804290f07020c030106091a01030605 67
    0x207120780c102641141c04094550304000f5107840c0d10040007000c0c80211003000e150040700c24421801c0c01400d03407003080f0035400c000e0503014506210316807150385401001c00807118000003190383d40c01e069034400480c0d041c05a2a180340c030040c06ea0709500400c1d060301c200c0c0f4403c080d1880c0328810032207501054010307500c10401030b0310740d441540a50844210990310200341c1501042038485403052070f00606420001041d420710301010f00c021040c03999040740c000d5904000d00d010070f0700c1c2d1a000581119800710080326180e107904001a07450089a2905d85145000801c448049400001036060764007070015542d9009070b000390920124200e03007101c03151203800d00104008a000c0d80c8a081a041100e20209468410201403410086829500004501c1c1030060205001d680b1449804102c001400c1c16070161440d03906031440c08006000308048075013800044c3d00d041c801e012400c0441030180003070240d80c0e15980b00001500ca9500c01c282681d14410905010758400c1c0540012030740c02801e02000b003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 568329217 1250 568327967 568327973
    0x503130b0703051e161506050f090f180304060906080c120f0a0207083903040302040c0507140601060f02010c0519090b0313051e0627030a0918020f0403 67
    0x850000080110307a54043c041084040340012858003810700c2941106d030800d0464501b40211007141c0c0256004410303890245803580c807151541900030a6201080700e0640d5016002e50034194045903c411038040410001805a0000b04075802c2d0303070458507401d07900c0d940c401d603070100c5000c0c00341c00c44140da09a1003c1625000100301c0c541e0044940c440140c81d020070764490f05041d40c810100320b0340c40c0c3c04020718401603800400f410b0380f000ea003880c011007034080c0d4002c9043e0380340243c1c000640720f16615040002c14034003910846014941c420140d401055041041507200d00c0b0900c00c241c04a00d80300c1c10700e44240c0c410711174280608400d4907043e083c003a01c00c94401414401e400c5501c244445400c2c0802c94004004c00341d0b116460404100e8104112440c0c107605014944d01c2c041c650400019451b4034100000c94002d522201d4003000c0103283c14072005514200947c00c1e044561400000f410414040e031040301902a00c80350300da1400c00324000001003040740301c0c0001d00164540144818000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 568330467 1250 568329217 568329247
    0x100905030714190c050423040303022104060209030c03030c152e150305010b0a120603020a0815060f011b05010204180c0320030c0a1b0503130b070305 66
    0x251000070221010b100316410400030510911030213590629030700da010440751400780034290680c0d45405201040d5441c040c441c0b4002c1c030020704000c0a05d9000700c6c54020440c8921401d00d55084210358440c1d06007001c0c10321000030340c0120b680d20b01901030580b0410150078004208c03411088500f005105102001f170442c80070440c080c1404014075001544401a0002d2403030240104c9100e502c442a4180b4140c0011102d0303503210300c45010305082074010800c9200480680d04a1501070078030740c0343c0c50000b220104c014101038200a600c6404c01602040303916000800c018056050900703898103071110800c100710020000d140c1c50005103e10802c021031527080d824103810a10030750015041644540040b50401800e2001d024402e030785081c3c04292035810700504c0e42600d048410490703081e22004940d00700f884018050640c5200000e950211240308101c01707a41884803017000310f03468400b45041500d0350720174401c1c1c011030300c414040410540c180318210f82a0503450f44402e45005000d40780360791 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 568331717 1250 568330467 568330493
    0x42f120c030105091c14030c180a06080601030b03030f0d42060503090d0e06130311091806040b04020d080d050106110106030201090e04022803051009050307 69
    0x680380100215110580c03824040c860266500d4005010503488200703c3c1a18080c078925040204286003034031615004006c411030341c00c820715600315a6100062034070004507240c0703036846030b0700301000c40000500550b2000c16a40035a809036001d003c10465102010394902030a402d0020040041000d5000110a03501045051605502118140d00c05030311071001e2081c096681403000b0300c001e05002d1100d110311505009031145003401801c504140c000c241d40c13401740c1007540044c0140f103107034082240d40e1007064500d8030800d00b00b04203005441c0e152000c401d03c02c0103042c078018400240402e540385080c01e411490410134100403c1540e4840d2a00300c0002d101400503070b00700b00c52802003000314100100401c5d00b64080140429954509500140b11084100e081c0743e160b490710390b09000503a401801c40701180c4c0c0c2c415940d4803985450000070601020300d00f0040c40c00040040710802e0003010040d6004590061041e1480500c84c0e080550070303610040401000358004010340710015840d001452 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 568332967 1250 568331717 568331749
    0x80a0309051309021012110c1c030e070f0312080603030f03100e180607020607050702040f02122d100b18061b0708030a021c02010b1008042f 62
    0xc00d0f504240d4011a5107003080700a804006001a02d1004031410b0b14050071600d049100074580c6030080300d0082c162151030000e0b03041c103440000c1f00c107070030482d01c02d4000d030010b00f51002c26540d64a6644550032881240c5201c121a100c04140551542d1030165492500c62107010700918902000c01410307515650006100c0c1100a00d00080815070b217001d650264480c45d449000c1e0115030741d48101813440d02c0c500402d55001c541c0420704120801e50300c542550003095042e50041a00090340c030641001e4012010864202403203074007007054400300201900c12410f182c3d0080b02d0440000c6080d04d03c00b090803540154403e103040c40c10400200b8400041103185240181030f2030030304145000680542c400859004007603050001e2513606d841c144001001001248000c618245d12240c0103500e03440d07042140c0409104a040604a00303000303401003061424010401008040c050f0005040741d103040c1e80540d83d082c1ca501c0c1490360082903c0520390344100e14a14118060714400801000c900600444 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 568334217 1250 568332967 568332971
    0x1060806130816140a03080105011b0c09020715231b040b0c0c0a0b03090c0d020906010522031217100302090613090b0609071806081005031e0601080a03090513 70
    0x840321302030b001e00c1480031140c883da4602c03409514100004041c104004d001d400904420300c03d4000003000403441c241202d070078550258469041d424903000d41c407512100c01d101d40d0700f00461b64810030007400b600203080718141040c505a840b00f41c01c030a480c4840d00b280002d00d0030104420b01440703009901078048100000121212b100d25440419002c43c4d0507030201c03801400c04000d00c20410170034005a8030000003901d0b920100c3d04290001207903018064000c506010000849215141502c2d06900201c107d042541204a07906e1030152400e1002100707601c0020403003541201c01d000c04c00149030048043d4030341072510909640070020041ea01808007940f00703080b034030450000c45090044d00d00d818041c01442c40285032020900039007100060104082005080740d480ca800c00d241d0414003604d0062914442555502c030065081034901e1704004d9140c480d4120400100401601c0b2080c4000794038107aa1503641c4e104090ba5691981c500002c010807030300c01c030510150800c440c0180d0001c0000d000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 568335467 1250 568334217 568334243
    0x1b06040b0a02070503121312020d050d020c0307062d0513120b06150706180f0b1609080a060e010b060403030503100e01030b07030c14040801060806130816 68
    0x1003401164803a10302000581c2003c1d030200702d5450107208003072041200003000361505150b140454410051402256103221545040f07005548882c1184060709600008070382311211103800296803003190968045c4244030b400b00c00300b1030728410030700000b01600c074082103022820140c402044000f22050071500f007010502501842007600d1724090004c205181e04c10351100c1043c02c003000e04c403100030061406540d015100144036007100044911864110900091464410350491036607140842c000e0400303404028600244820680b02c0c5008074280444154060301e108010f4803120350134820010580c0004007a0404035185412591a81d00d1a5000090800325140082c006400a0300203500280c40130041007070044d402030012000d499000c141110070b40c0745940300140c611004295604040d00d03004542c89060080011018200303000c07541e55219a216587e4500901c50f41c85804418402d00340841c00c80344086840741c03030f01030f004000180741c0b000c540000d1500e07840005044903204071000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 568336717 1250 568335467 568335479
    0x20f030a051807270204080304050d0615060509030d0905010e100905090405010501061205090c0111010f0e0309100c1a07021e010c03050a0c0f180801060801021b0d021b0604 76
    0x550009401100107000000e032801c04c551100302c001c000c2510030310740304000070b1100d60390000c01c1d94101da8045861511307852840c980b0030302030403c3e04910481d003078428001181054101c40941050706042c2d003210044c9071810000c03542519248a0a1302180c15803a0351103480c1030052110b070b0360710400e082440072136030340d14007003901c00074119015034169554500612055912a80c004104c2c03220721414021070030645903680d1260720210400f03050282d901402c0c50050000e40042c140c098141104000b80c1040f01c0c0c5803070b120381c05201241e1040020a1040ea00c07640910080c1d851242c0041c7da0301d418124800489840040240010301544100c5000b0784d545441a078908003108402c40c0003040040f070320078015068071006018084220b041480e005007407030380700e2415800c04c20289000d03801e0040b0f0f840b801007201c9841d006840e5550901c42c011814a805400500311100020441081090004041c607100c950341c4074000300680000c101952401500407c1c2150f1030001840340e4a400da440c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 568337967 1250 568336717 568336723
    0x90f020702030609010c1b0b0f040618050d111501050907200f1513061a060c0601030b060604080a0b09120403060c020601170d120f02030405070315020f030a0518 71
    0x210480016911180206e0480b07a1043d4045c0908402d6801d070343c0342c141c55a0310f4084507140140360707070a01405103001a00b4003400760010360000091150120041d03401d828070540724440c5540c40b002190800380e0f4001448000121030f08a0b42c040e50100c0d0b40c0307034280704c200301c030395031000d4006010008151900c1c0d41c001803034075051003101c036a01c0091046008450b105400c00c0955507507a42400142010005148440c40150403a181d00a0b40051558052100d002c0c441240122003a00510007050060003648001240341c140c03801181080803558600b002c11480703209502500813a504222000000a01110f0713a080d04031484005450700c01c0c0d01069010000d411a070300586e400d0b9100c44900300303401e4043c00b0a40c007510b0107078000d1b281000c9804419a49003817858106007007065921886a02c80380b2544042c4a0866885042d903690815040c110390302d090500080e9a25a403648066542c00d100344211000520503611083c2156a2a01000001c20b002407c00c0f080400301c41d40610440824 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 568339217 1250 568337967 568337971
    0x50312071104050c220e0412170c040e06040b0f09070e040906020a0f03050603060714270901060f091a0904110c0c030307021c0302031e0306010e030a0309090f0207020306 75
    0x1014031916040020020b50381d00700b1500d911170243d91904130911050304a07210071980309821558101c240241c0301e40031a00011041c201701c201214400500114194000040c07045542c0f81e0000d01480c0c80d00020030044500200150b5401040e1154240703150822003901980000d2a0420051102101020805403851581c0072122141e00080344160a5001f640c07440e5481c1080c50f00b00060303c0c11602107a0f40e603502406207814440b0b0000d44801002c510012212008050401d421048501c1152200350f80b049942140c0f02e00000400420f8251040c104000b4807696580ca10601c1464040b0600228030030480821950204000204550311103006162500094900c0255161725100400e81004103010001c3d00c2600b0401c06400580c0c4c070380760818900c00301500d14025800280c035050380345218044101548850544451240e041d004001c0c41c8a50000e0721018125011001003540310f0a038501c00802141040d4030078001c1402c1640704891090302c00c0001460a801c0e500040c1c6010b9003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 568340467 1250 568339217 568339231
    0x20030c12250f0b0405130b130509011d0303010e07080403140310052e0e0f090c1603110d052a010b04060806010906050604050105190224071805031207110405 69
    0x4c082041e0b052190320300020a601403020004c10210100003024400b00d0f4400d5140e09896001107942c240080d884541802150700f002115020407081c482d869400074814503032030842041c0050070351809800458440c81c0e150b6224107000081e540c0d1403002c0c0d000a072031025001041b44001c211340d110290602038640300d00b4485400000300d02600d200440f50451610108424035110700c80b5501c402c00203005403a03044a040b41150b481c2c01c0340405a0154001c907151005461903190240f640001e85900056440015591068a45801a00c4030f1103161008541c1f000c4410560950ba43d251040c0d00e400042200041900d241850010b0207440303842e000000a600050010000d0390042d204002c020041a00c24508003403030072001030f0842c00351310a10100d40c03228088030040b90b4801c3c4a00c242c50303c41280340e6014448070000e8100840700441d9500040360344660344040b0000941548000c443d00100100314840c1680c0025200c2d400c400c0c400ca5001c03407900d56895656a40d8010380c0c1c42404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 568341717 1250 568340467 568340489
    0x501030533090f07061e030203040519080d06050402190f0909061e0f06021207140703200d0b13020301020d050a0c090b0403020603010b0c0a20030c12250f 68
    0x1c1c844012424528183d0000003448415120b01c40d8450030200e1440340101d81f4240103844c0d0352036041c440c2c01c3c00c02c00030203400221074205403413040101800140092020003d01005041d031124281700c00c80c0700e40712040c0c10400e003851481011f00d104100c02242c1392268501466003c0d82c2d040484141c07400c64002070171000c0c3c0c2220000000741603568890091101e86640310410345001006521025440391110218500160305c0f41030040242c1c0300c1e0502c2500d04115a85199207040a08071640c0789541e55a507500d101c0c8030704246251401956010642240c4102c0030360303e42807882c80164402e0300c0105d030903540a00420614001a100d281d214840310b8401089035006002c0080454a0a40010003c1081440b0520242e22003070241d074190350080581d03a99a40e00b8042107441d001d44414014203007400e400b00c0214034000e80401a2100c1802e604543c0010030301001c014014158a100303181076132004000c043c01d083e1101c00f1180701d4074000000b1121684a90403a01210041e4104180c044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 568342967 1250 568341717 568341733
    0x20d2609010338190b0a030b011814040e030d0e070e0c041e0e131502040501020a11061308070e070e24041203120609050103053309 58
    0x15815001d51001c00f00140101d55201c4600c07900d4102c0195107808105100030300c21420382c0a031302c40107110740040c3daa0000180006550b200380c24510382c070507152103002074105007074640294090050249100314070081000001d04104031480d814203020302d503036401502c0300c3d01140c403e041400140003e0303851010110f0500c88000321145000059480b40300e12004003c204901c408070501a5800d4510000c50102240901c0c0034902c07034100c2ca80c000d03c10b0f981c0c3e49414808074084144041518a106074140080040d0100d41d51049020743d104d2780340983c2140c10301000098030081100780208000b80340506021024508542684054001d50801d0744035150610040001040395030b8003248034503100c05580003480228444503480c441c64511110f43e410038031200744410050303501824281c01d586402181606005116448969a1569030780c90803034003140c0340b022406410305803a0014014002141232550a1046c203041305004210a902e0310500c143d48182c0030900c42c0540396880003003840d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 568344217 1250 568342967 568342969
    0x60d0e21030609070f050403260a0203091302040501020c220501060906110607090302060901121e14040b0606070f0b07050c010c0e030c061312030507031218020d2609 73
    0x2400041e05000174040c2400c0e00c40400c41d800382c100c60580f60300540342c5012181c410402c7c880c00c01900c0d00f0301c101e6103011400160066002015000b513134811200382e040c0d8010755211904901c118002c40b80182c21801c0300c600241001420815a0319190081f248208002c0424400703d0740280c00030400509064820007926910050304015450180007074003441c142401c01800c410000e00c802070003450045201411b42c0e004980e18124400000c00c140650707081544a1229000d1041507086000d15100c1c148403d40e000d034070381c4c0f84542d81c454035030159078641000b002120380040b00c0464400100704042c40000e903060740164090000740d00c41d1070712049641c5186080d9801d9000d17500421101c80c074020403990b400102e00e0300e00801541e8003959564418500081c041c00c90f0007500c40808950005c00c01c1580c460010481e05000703036101c0803000b4003d840f80c8255407a02405a03441060300500501501d032601c102c03001c241c840d00300c46002ca4180c40c4205a0f49881e00342071040300b68046a41d03051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 568345323 1106 568344217 568344229
    0x50103051503010f0b0a0815010605070f12030b01080a05192c0c24030103120e030a03030911030109080f03060f0913150b060d0e210306 60
    0x24065090044c003412100258078004c040d542000a0002c2c0e0102c0c031100c82d0901c41e01d820200c1d0b407030444221002e800c4840d00f80c07010849050b0348000030340441860050541151801305032041000009400f080c00180405c0c000c078100340800c181d1041003108009001c5010340005081e5850000460000220310545503003501c0b10903c800b4032540014030020345420498240800d40100502c070909150122003003094080b040c0300500021700407203841454404036160400c001c00103107001a1404101050039400701c1e540341010010300c0100300303d00a1001c0c042d8000c1c4955062a42e07009101e100f20100d6542256010000c540260b4600c80760001e200402414006141002c12400c1404200e8842c1141d030008003545011284555008110019400520341380c01c2ca441ea403020300c00ba0061000003c041d0081c803481903130800e04410b102400040c201c0d81a5180d140c0740041c443e0b = true := by decide +kernel

theorem cover : BRFrame.Cov 568165467 568345323 := by
  have h0 := BRFrame.cov_init 568165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 568165467 ≤ n) (h2 : n < 568345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
