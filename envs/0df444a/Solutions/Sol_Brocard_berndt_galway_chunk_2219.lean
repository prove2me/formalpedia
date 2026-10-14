-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2219
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:02:06.690571+00:00
-- url     : https://prove2.me/submissions/ba813b08-526b-4ec1-a293-dee9da9b61c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 398920863 ≤ n < 399100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 398922113 1250 398920863 398920871
    0x2090f04060e1c09090203010308030a1116030c0219030317090c041e0b1e090a0b0a0e0412031505010f09030215120112020303090d060209210607020c060a0f090e0a 72
    0xa10003400c2d6441940644174043c410401030002c10025012690f2090340484007240042480700b24800621070500005c0c030348a6141d80032030401d580801280c0b0154021101c011b00103e62001e110440c00c030074880200491100302c0004a407000075250740745d1280c1e405064a00141d04080818262a001d910000c1d81400c00220108100042d10901411720019500c105000c0c10000f00f00b91034607000112180302d81801c500281a40185800014032076601501d80380185d9610080c00e61071807410381c0c1c100c1c1c40e0004c440354200400e10a00c20000052800e07142c0c0d060f02c80c07601c001500c3c0710350000c0c901c1c801c0014a400c003001588803888509084080100da456840d210a001c68015200603001824421210001900941d46c004156005070400711000d4200005a10b003a034001d114518006e900601d285042100ea14402e000320208250700d4010740e0303860b9564010407600c5804111030607620010900c24503002e148035650032a034644040c100380224945551003010056011a5510801074903 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 398923363 1250 398922113 398922163
    0xb06090d26041d07110712150908030423060f1e0f070e0a0513022101060801140102060702210403140c03160f06080424050a0509070302090f04060e 65
    0xc0c40f01c0c00759001d552850001c04188200d01515214070352403003081d8010712240740c480180301103000c240229550a100400001a00b4942508160030446041e1901c6844032940400012042c90700c1c14031500d010080c00190703035005001c0502010141208401c0b40390803034200d810701c03203044c0c0f050f018029800c01082d691511000081c044410320613147e004002003030042180740c403041c40202001c0100742c00561104a511403004070010030011158400c0c41810000038000d4001c100c250585607045d454403070102084c801642c1e942419200c890042e404400e92081d11040981201501101281390342e180a0ba00c0d15021608441c2004a00c9940c21004c0c5030760755490208101e120140c1c00501c0f0f40c43c40d600e0040000c504404034030512040c4040c42c400034040050743e583c1009078074036900d1110711913100c04c0c00800c000d1a04440e0540f03214509404036494440c00074803401101c0e4010036001d43c581c0ca8816003002282c1c0034008450664848a0030490b200c000d12030b05108415000d41e000c41c1400d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 398924613 1250 398923363 398923409
    0xe04080d09140c0d051002030601020102270907080105030d110111041d01080604050d1107050409060209011206150309060e060c030405011410050f010212040609030203010b06090d2604 81
    0x441118004d104804110180002030008254400394001030140140c0b20390314100143d001e0300c200844856220109100c6c101000403002001090000585140c0041c0c1d0700e0b450241c0398000b084c001c079507050340104058240d681c4118201001c0b0f8038454000704082c1420407038502290026004800c03c020501d0200c42803600035510580140380d604028015824a511041d403203800e10070310072082264400c1d82c8030242d0f0782000003800a000107402009021410f0500a00035084442c40328009030244141c6e0301541607902030034040c4c80c82c1048040c01e0b19400d21066000744003c01d402c85026440b504201140101449080c2c403844107a50125034038a0701d890300c5400c4900c41c000d0100c03046515420302c0380300b902440004040d140c0589080b00c00101d4100107074a444da100407103c100000004020406c00d07449000d80302140d200303030007d00c10502c00c0c2042001da4002c0e1080b11390019a080c07c0030010820305040c20103c100c02981c0030102d40d103200000f00746070b40309400a0440150300b01c4030518400e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 398925863 1250 398924613 398924623
    0x1230408060a050408071e0507031a06030a030504091802040e0c1207060f0c030201020c06070518010306080a1b03060219080114030606130f020c0a03030c0f090e04080d0914 76
    0x60b244407402c11480c83e081d0b0710200e140c06402d40103000c0d030824640130640f01c055850807034001d0307401904407949140c1c0d030701e0b0903108540082920080da8001c2004a24142400141c07101c61342d0303240e141c85040908140184004090403061002c41c800c1c1d02e4000d4002d0b0703c403841940d8601c03610f400600b40c5203c40409000f2103202c0d11f80081c00036400786c40b0420086a10020000c1650124501b1003d10001d6050482c0a40500450000580541000d11100a42050040072401c07030302c1d02000034007000030006500700d44061080e1a46c0d60440300d900e40020f01c002c0b84031088030341200800101035440303032240c201701e0f04541e00c900840c142d030b402a48546604039100c40c1c01041d900b02c0120203001c0800101ea10390030b029044d140242c450100c17039259000d05030096540326003004421034480e61401038150383c4030000d100507004a40303841d440340d02c0e0030b00c02e6241580340c9a01c0d8541d020ba05180c04580e80c09032038024070a0303508038828803012102d04045e01880b4110303405105990b03102d0302e400704403070b00740 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 398927113 1250 398925863 398925871
    0x30706290604030f0308040305091207060e040204030336060c02010e060304030203220519090c020f120903030f07061a01110c01080a0603021c060b0405040c0308090123040806 77
    0x928050204000040709046840c4c0402c0c0c0c14036081c6101e03155441c041c0d42e9130090b1254694080115844c00e11104c0b80028100211002e40e568a0204401001030104034440d034000940002e001e0040745c8540a02c40e01c0c0404442102010030242002480301c0e07095840d030940021000507030080340c00007590380c40310441c000403c044880610310b040a81d8080c3da03900c0381c0c041610200c0e400182444007180c0081e0048000c0c01c0180080c041c4025845e03090038152600e000f00000e1501e420034a240152002806050b02c69101009040100b4403000100769600200e0b0b40d103515100400401c02c07005240300241c699984030307000100b030800c0c500c0c040400e004900c00360030341000f08034078481142e8070b40002e00c0000707882c00303090448650f2501c5405c0b001508241e00081e41200f4111030590a55242007071000459014850410040c00b40b50100426034100384c40243c1502d504105c140042400311004000e20070f014101204180900c0c1e400390001061803403176120a403000301e010002000c0c01c0c0049540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 398928363 1250 398927113 398927119
    0xf0e0709060816140f22080c19030c0603020a110c01050a03021629010e040512030a1401060905030d0306030f06020304053f0c0a0305090303070629 65
    0x15081c501e000b0102a80149951401100c000d2150282030190211a0b1141030000c242c0390780e103562200d809540da11006050b41e52502d5003440d60f00d04001d060806042d2907140c4098240500b110701000300004074503862102ca034078170340c41c00000150049940e4005041d181c40150b00c13038a1901020300f03040302220010490740c00408805d107060303a01c40102e60024403a03003801a00d480c01d000d4084182e0410b102d0060913060380000380d04004065400c0091020655106402c030343c0c1e216802c0c2440a441541c000b0247d40c444e5440e1000101400040d5900801501000840b0001081400c260f10f87c02c0c2e100d130002ca0002d450074070040c20140859040e5103140e04003402071600c2c586d82d140c3e0810045e47c1c080c00080d80170000c642007180c14040346880d0311014074081a0040701c2c42990300400001c0d9043c1c0c9103034131b0680040410b4034650f0150f4030219604409003030005a90f80701030b6803540c40454000c1d0705000401283c0c0024800b8483c2d171404d01c02103200605031858940b0007800c01d64003031810503c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 398929613 1250 398928363 398928377
    0xe0d05010e0309030c0108160c140303041a06220f02090402030c12010f0807301406010b12041101052110050a0321030b0a0b040315060b0a0f0302120c030f01090c091707030209010f0e07 81
    0x83c1c00e012103074445000d00030035140090547182c000070140c0207001b071846056205000000b4410100c040ca4050640217200c2c1d41c042da40c99a998950303110b031414922075032016810444042202610380d040035411002180e64007460603001c00c400200e42500d0803012916003030604030310000f16000700701ca5409040031840e40b516001d504600c0d400b4040e0010700c000c0101180814080329644035005503084000d20302882c85c0c8144048603500300ca0942116401070084054100107846d10304200b480c0112500302200d881c10038100303040900d4101140350303a10300380740d100e100074000b0384c6400c0714210040121628a54590b42189044222180000c40c03880a090038000240003001c104412501c00e010755050542240035004d41c16406402804490140070320950f04003d804030018000354852071182041c0c1d46943e80391040b040032506808060b0000501141041c030080b24029100b2954140c0c54003140c00070745c0e0b20f60020f040701400340c00c100d0b20300320050002c21084034202403040e001816428500703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 398930863 1250 398929613 398929639
    0x14180304062f010e061e07050a030f060302130b090f01080c100e0a030f0605061e04020705030d050711120403080a0e0d05010e0309030c0108160c140303041a06 70
    0x414021590b400d841058110441c0e9480b11900803400c0421201402d000f0300c101e042003542c09440c0c110031200d0310f0507600c0071400620300c10b054820842c403450380f6480b41c0d13041042c4040110010014416140c7d031460391100c0201c0540d940c1e00b401442903010301008a070800c222002e2000180c40038050f07000d030600400040c02a0b5002040d1180303048801d988070b5000303076111003080750700038070758044540c1003030307010002005026400024031005400b520041c0041d490318014451003000250f00112010543d0110a03a0341c94160003c0c204a03004608581c20622040049811904241c1c0c0c100e01260a480311908011428001c86194001c120149410b10f8556103400c1d035144641034003503040001c1e4507101d016540d9014101b40c04507030804020400d48124a44940c0d9a5100c2c03003440d4071a00c42c5000c054190361003844054030500c401d0254610740441a04260b61380c001010045400c05917446403080d04500070405544a140100302e03104046044100f800d03490700000c5c4c80340d80520344440c60740d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 398932113 1250 398930863 398930867
    0x6100b0301150e0324040614060307090c0c060f090606050105030411010305250c06061403071202030102210a05010501032901050f070c08010b04060503150403050d1418030406 77
    0x200000190a041c819010030710f080c0000d00f0242101900b1540a207110b80042003026104012881355100d01800c0100b4000c400c160b08101400702e41c5035038190700400c41400001141c2d0001c801a629a0900302214021b0b60b03214426211000200d8514581c2e800212085c0001405814014102820500c0c41c5040c591110b01503004501d4000d814151200f0101d08051100d81c0c02c2c281c603141164044c05444080780c00107115480c1c48606460f01400c1ca1030200e54940011400400b0781d400600034100d0078500030350000604121f0005070b0b8955400d20074600441480019509210b015980c2c90300c0320b04e004c100e04402c035003040e04118109481d00d500510300e192404111a4040c0305030101400343d41905004031303518450780134082500c070400309001042007801d0100304261450301c00240452000441400300f15500307031050f42c0c0c1c164030094007195420442e00400360864001e18005141505006c00982552035100720a114892040200141018407146056681e02d092000d1031900b8604000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 398933363 1250 398932113 398932139
    0x150e0111220605040e09120703030207050d09050a030b09070509010612060608011d1005041a0301181703100b2808041113090b04050604020312040b0d0911040e06100b0301 75
    0x4040c5824040c00104038070071b504010b1060100c84100003141c2c0e07030007d450010003035084680d04440c2842414161142140123890f454247c56020b003818540601d15114091014406040418640103100000c2507540350000c826001e003116852302c44106001902c00780440d403503a40101d08201800c0010f200d420344d00c80c0002d40080ba2040102465229500a0725a00c4415800f1710fa03c18500381c403c001103014a072032085644803c40082101804040c054024207103401c034000d1650301000f41658900c990140919081030703050004500c820344400110125038042102e02c0f0f642505011303185000180034844c0f2410030503d180c000f0950625540c2c003203940110380782e02813244d269040042140c60803030340714004040c1c00003948141e500b46424515102e44094500fa40603018440a070000010b461f0121800c55401d4000540b900c9051b02415000301840042150308100f800440c00d440c1e6110b024041000b803405020700310b0750a041e0a2074003900c59540c4032817100c103c02d20041200c80d41c1144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 398934613 1250 398933363 398933369
    0xe010e010309021c11100509092a0c061b091311090a260a0807020405060d0204090327080a0206250302010204030b060402040e04150e011122060504 65
    0x20007241000d40e42c400903040701c0008031a0702554006241c0e0800b4000505d03203d0b40c1c04001500c626141d4240b00004803503d1041200c000c2e04130082001203000840743c0c0440c98008488849240000c041c80d00d81c1201035404500c0207607403a4001400d10076144c81034100301c11000c0f68010024a00284200801d590f00a0342c0c60303002c4515558910403044a0404040740c10780f1400500b0303070340a02d454a1480a040c04544003421558005180c41030f40d10100182c8071050b80e410001071414889954204030280000410341c1d500700f28216400c4005858602032582640d11a851714201e001078090702010b0340c9009101000740301039281c0c00704455500803801e4403c072501500d141e9a100706442a00381e84140e05002001c420022400d14414541c0c1903000d042524458486906c0d00d884003801c102c140d0080380950303165143d44001240008840390407600c0703001c42407103011521415800c506400c4600f2010381d442165400680540f00b220342e05081402a1194020400300d00e0614500409a001b41c0c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 398935863 1250 398934613 398934617
    0x60e010c02040926072a031203060308300c0d0e030f0c0601060207050d02090708130503040f050123031602030708070303060303080a0902060a0e040212040b01050a060e010e01 77
    0x1440d0310521002d40000d150795856182c0005400b2003186070340805901060090b21b102c03903403001030b8004503181d1203100380d9100c008201d0304c881030031920340c00b603089407008100e014541c1e03510002000a29070005003c80c1e00c0352000a090302102c480c514800340d4101641e80c980c8510070002c0244640b10482a14101490000009011901102c0c4149140b1840d12220700303008000c00c441c1c0d40140e0001d6141d06072403e41d400d0741d00f441d9844d005d01659245800c80207520911a00001b8a5540f0031424180d1011f01e070009101c0c0704880c1d4845608661051b0000c1c0110008010144134030350b0007500952400e10803203803152246a4040c0500da041c00041c20f90782d00c0c18554012116450310810940700116000f0f00310a40e103030014540907004040b82d100440105003d80c0018911401c02d100b0800d03d240c000d0282850b01110040c01c80310071041c404045c3c2d01640c24005080041504071049110700d1098603402c0155040c1001c20800d010f5a600c440100140809200c98990380f00542d004c400d8428 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 398937113 1250 398935863 398935871
    0x30105092d10090509010e06220c0f0f0f050105070b0a1e0b030118050a110105070b1e09010b0f062b0c03053304060e07090609120803010519030b071107060e010c0204 73
    0xd40da4444c02c0032482704060b203103c4200b94045110030303030807802a08480d1140171005009654000000b06a211441428081075003805440b011484505a2560040700300c800041d24007440100d51030b40d1b080361251005041c0d41c42a04100c1030034248a0380c503225a150340d6050140c1213581c0e07095554088280000c1a100101e100c9440d0b99003c0e00940e0070f003030340c400ca00a10307525240384a2079100144010800d1031907051404a208a001031280300f804001c0500428503258000061000340e610203842c0d203040b0007005a0081031340081441e04180c0342c190000114040380200b10050030784a0151040711804410603001360710701d88c04841500f1410b4014907101440150500040003800300d03134042c4540d03102e032408000c40c6550002c004030507155a9100c551301981c440018006c49403240384002c7c0faa02c030800061040c2d01d41103d603941e02d18214000d520740b03242c0f030380d486143d1080240e81c02e00201c0c04104031000d00d4502801008040c0500b46000c2071600c804000080c035841c0100030190003240da0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 398938363 1250 398937113 398937151
    0xa02030120041715040b04060b060c0d110c040e010207020325090f11031f08070605090111030403060c1d040c080f091c0c1502030105092d10090509010e06 68
    0x180034810b5080700c61307103142c1094641410030040d403802c221400c88015140c201c0700401440c000056034141c004000090001c090100d0301610440e6407110450820701c03610050204950f540c1c05010720103e0b03c1d0001588071a081e2040c5850480306017401081403002d07118a103207201c00c800c0303042d00b00c0c1d14203000840c490700c2c0080c0e6140280030030f501c0410402c0c000010071403080142c400d071514104001030181e111769641c2d90309a031580340314001d010001c0c50070400c034006d540c4a01c0e43d03030b60b031340315243c0c1501d00e42541c0c1d980c2c05044032407042e41000840e03004441d10244031201c00041c0e07076006d011b0380d0601001620000042c01b040000b454000507201c104003143c0034013003c00c101c070310340050840c1c0e0b01000c0d40e0048015200c10000c0c04116420402d107414624078416500039a41202c030058005846e5031582000b80340c1c6541c04107a10b0351080340f80c23004081780200e070b42d54007070055008070000380d03d95043c4100c9070145c403401008a102c680c1401c0099814082c000342480e400701302d0410710020b20107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 398939613 1250 398938363 398938409
    0x20a050901050d150e180604030e120f0339100207060e01060906080c0d02031b011707050d06090b030d18170d0e010f020601150306080604050a0203012004 68
    0x42c0d0100c0081c1c2c4c0c03c100200032030501e00483c510341c0284682e40030300c00495000c18056035078050498008001840c041245201ca00302000b03c8110003000e08141e0b07000c134038400501451900051444a00400151041142070340707001c0807154414081910702c58000400c032444c3d5652240000301d000c0484d80001c0003018004a54030a502c031303da07000024010585d680804102801e0a80600302c00c600a0240c410b8291a052404d0b00b64682e0150103041c042e030748045640c4001d030545110340d05120071035082c81d40380080c0c007000c04c0c400c1220b0f03141d1b0740e15556444252002c4400c107402010b0044c0c0341010700d081e60b550000303101008075254540a81400ba0725428003412900f136912183e009581c207032a040c0c03620000329904007c00310f0b030307030740d140318100d0110044a04a120b0b040c000e001d40c02040050240010000d01c140c16030303003d4100803c2c4280d54504481c43c11800b00c8054803142c20610300802140790070b004422044801e0a1040c0480c0d11000302071100f0b104038443d5042d0780403030104c103420380d035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 398940863 1250 398939613 398939621
    0x414010e190b121501050a0e0f1b041e06090b1b010b1008010e06040207020109140103200a02010606021b13060503010207031e020303071407020406080d0918020a050901050d 76
    0xb8034054041e9141551080c00983d5a02005120010013200c440000c641814036145501c1181c103140103c000c03035102c1d07070030358507103c8800f5003000c0c0501c00e50000242e015011500502c002c080d0a40042300c0030130214501040628030390404010014845c1003003004080c40000d0714040019104010f40740414421614014443c0c44681c580002c40c1005401e401034002c4447d504030340794003203c10b80c20394403007041000328411800024046200741d04240507600c810b8420651204040c10b0000728050b03001c20044a501d01c9000300b090b050800140007064070350a028580040826000425800c807220075a01d800400b003081080c0902007010120b0541d54450700b103003000345005402103680e418030b42002001e2400e0390004003a10540300c85034010240c40002101e00c16105591060900c44507802c40c05801c1e4401030080e42e200d910340502007440a018030044c044940344d5141e614100c0d140003105002d0044c500c80c50a40b844c410b2204245d082d0700002110f50100c0c092800075914821050f02d60010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 398942113 1250 398940863 398940881
    0x90b030a020a060f0921080703050702061315080405120c030d1803090b03040c05090c0702030105090d110a1101050307110307030309060e01020313060209010504050411090414010e19 80
    0xc02c40c038410002d00e842d0000c507000d511881c1942d40140280d10360703182143c40c5a03508217581102482c0c04074480458503080240c40c203580b00b4500300741b170411903400040e0720750007400c001c182d0707005681c00401c0040722414000003d04d21505080c603d0b4501364549984444240c3d0086500000000d20303c41201d1040c0b080310503455843d04200549c10301c00c026140c010708500c1084002ca062054081070411b803080c02d0b03034403071031340915800406410300e801d021070001c0103031103410568414003008005035402e00400307100390b5490004195481024000805114007100c91344c4080d004400003801240401c034003440341d4842820800c3d0f490f1a4020100c5d018a180c003d5a6030501000c81c14004140d81504001d03c0c0a0042c002441440d00d40e4080038204d10003503880c4941401d1701d146000024600f60080c20742a40c05041c00c6040a50312000724003a1440c994090101c0400014003001c1450580728015400315204400040703581000f408098095000d00249403061020054640d4441190001100c1e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 398943363 1250 398942113 398942119
    0xb210f061c0f261309020703111b04050c0405011202030c0c07080d1d10031e0c030203041a06060304111507260f07110406050a03240b060301090b030a02 67
    0x4401241000d1000f44101e0000000000e6151424801040ca820646041c400400c260100e418a883c404030000d50144400b00c0501501c1d4401e40d0040710709100401c2c81c00280c009414800c2105c000300011148000c103100103c080074001442281d07031155681c03120220b03002c0010303035a44030402540c1c582d00581040e0030f8588604280420002008955044000d200c1d0300e4107c210762801351842210702c0e0220059401c084072160703d91005203e504945c581246407500980c428056541480680d10007400080100e0b800009120420280031602850401580944405403c003400001d41510000e04082d006028001e802103281e902c0c4030081c100c1d8442c0495082d92403c09240c41884c480e070255000c071100c14084101c1003c04160811600e4200464200901c1e0220b03035501c0360030a40104c07034400d41040d514000800d41e5200c1041c540c0140d4003658a12015000d05036482a5a0200c1c0c42044040d03400c065140445407902026203056420b00031021135a00b1112002c80c1c504801c0b4a80030354 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 398944613 1250 398943363 398943383
    0xb25050a0507080f0604030c110a031e031b0c0302190e01060305180a020901091509020403060b280504050a0902280b0705070e1306060b210f061c 64
    0x200440042d003002180c0f06101561401c1400d00b030615143d40044034080d0206101840c000c0c0055004000380b01d150308014104114036840e80c131400070640c0c004101811000700000208289608002c9604c001212061001011002030343e9130407121886110083c0030b0940c61442c0c0c0d2104060a145178040c00688501c6205584e483d03c0050107071030241e9045040d55808080c1200c00c01010601996007900607003c010944d190207042c10080460112203500c5107048100440d107015140020f00003180580380104684015100700000c04004a0303015240542842c9180316046032031441a00325041150000381c55500c00325418080d00d00690029031040114120795580050403178070349401132211400000c804d8490407050201d100e4040302600640c00132000b0030008403c240761a074006403c0c81c40342d107048000e60b5408291001900080380426001c1031032020003e400311031030080384200004c0f03c1a42000c10301085d16140c041c15840c0070301a0080308025880c4109010b190700c6a00c101055 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 398945863 1250 398944613 398944633
    0x60408120717090c090105040203130305090a17070806091911041103130605010501050f0f0304031119030212030610030c05270f0d030f23040305030a1101060b2505 72
    0x1a104c0320785a1a02c1d01c2a08600004900c50070f040c405e40c1d100f003e1010308813050403c140c030706407010380001e01225441450402c1c0800d1841d0000e4080b002c03001950300600b106420600c440d81010f43c01420510309038441c00300790b00d0b150215401c6a0010390408003c1c3c000b1281c000100d03000d003000d8486124549800018040e02914003111003600c00c1c0512020850f83e44c07a0001110944070f00049840c14030424815001800d846000940d001031207800d00140c980c0803410755504260503000408102d29075030f03d076181495018849034802c50b2031099440e16510f0014009076900c0b4600f49000c040641d140c51446485000c0c10403142c44821620940301e44000e5400c1c0f440b000c40c1c10940362800341030007803581407440c201010810b40d0260305131034200152103014030855816982240f2107100551105844895054147c001c0c0059070050300516501c501c20140036040703100d4030004490b503a14013070003040206902010b45000c07844104101c1b4200103118196049160700040c040c20a0041d10050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 398947113 1250 398945863 398945881
    0x261203040302150f0402030f030a020a230607050c0c0933060c0706170c0702090403030f05190e06040302120906070203070e0723030f0402011209110102070503060408120717 76
    0xc5d110b0362089040f00c02d00300c42210016241d000303041450340541c1c441c804170300000c0c4e07041c123140d11301068860460046d003408401803840c1910035140ea00208100099803400c140c014001911101c0050b12892502d0800002d10600480c08000c041182ca0113025915540d0980007003440780c40000400041c0c4a0801c1140c46450380700034443e24010810403651003405a94503200e0070301c42c0404203852420200349800380004c00e00b004008404041d80c81c801107008021901c94540100e19211603000c100421038070790006c407016849864865840b420821001a030b0000d080c507081c0b00c54800b0140c03100340f0000030426034064043c0095060040c0385020072180150b1180912420041c6d0790304005245604108010b00482c12540c80c4c50801000095110701800c101d66400a106140c500a00403000f050313202240d88480d411034480b0711700440302c007003580d040105034040c0800301c01a1600c4d040665805040d48034540118110f0740070540095440c40c00b91880140b80e55640361080c440780b5094100d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 398948363 1250 398947113 398947141
    0x302060403030e0d05070e1e011802090102030c01140a050f0f040602220801051510092c040b06030d030e0309040c051308030409110c060f06060c010e010626120304030215 75
    0x514011088036422544123152219652812522002ea850a50981c00c41e0f0842c040e520940031941944010000310080620910820140c00c40004950809090600c0e002041d514003800310801074081c070b000c0c411149050403100c3d4101e540700200507a9a02c86054421850010324840204030b2420040041c0090064212a02c1003540b00031100b0403283c003d04000e54503000c2389a03a00054000442804110400440c40078106400c01c0d4000071507a0f1011520403c980c11102103aa9405c414288281420208000c1d400c00089080a10001150700050f0707642c0e00424901600c03440d109c161002402d0b010b4000c513a02c0e810a40c100f050b10350348a0008640c0ca0b80075104050303e091410744451040a511006c0e1280800c0c45030181c03840d626101c0002004501c0600660390056003005011042c040901c0b03800c050f00440b000100d103c3d8a094544056100c0c1c0059503400310350b102e0368003c036a81c404aa031b1100b4280384a0b1494494486013000c915100110a840040324882c02c01d0000410311006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 398949613 1250 398948363 398948371
    0x30207050105071b2418030306050406290c06090a030f02060f0a240603090209060d0f030f0e0d030818070f12020f1302120c040302060403030e0d05070e 67
    0x80240310b140c840745012500c107060a03041c0b0a6229800410100040303402500d035501d51751400000009aa00c2403070b06003118042c104405074008084c004604060b014040c82d80203220445042141a00e0300c40d130a40d64120a2004e4803044941f00230b109a0411400180d68050b180103080354061301d44032a03a150745640d022030a5000c140c1080751500164400101d4a200d00709400c1c2846e5240c8a03884004090320013070702100c841c81060441e8071200e498040101000b40210b640101d20b20207640103012100d00050403160042503400d201001041545204039015989446c210101541268007110b60103600012581d002c60300200440078541d010820030700880002400f10b00f003070600300d01ca030740d2818a407240074017241c0500020000c21a00c4038110394000d00203000c1100803200da6000411242d50700c10103040c1d0640c0850340340f04426071520132a920103400341400b490303e415900022000d0085110081c10440c58401c00941c1da150518000d41040d07210080340d00c0c4988a2207801842e4008079 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 398950863 1250 398949613 398949623
    0x1e070305101d0309010c11040e0a06150504180206090613080618030901090e090304031a070f0914100507060e0129010c022707081902070201080601110f010c030207 72
    0x405030308600b030340100c01c4512001050311040c010030004d039030307142c2d410f070540030b41d01e074440d5503245006d14520061041c0c1d040c00380f04040014104505c500170581c3d02540c0c0e00024000e515100400320038401c00004903c0745078046072425119441c0300c001840340c0c41340c0b4001d102c40c2d002c01400083c61070300000d00c0038005c484200a00400c0028450195541d006059016000030010b4004225110324195100e8005ca035a1023600c0c50141c49442c0c8440500d202d02c1c0341c054040b0900304101c48d4652205060748003181a180801075185040d04100300e1843d00014144558800e81c8501c000e039024104440c941603000c0c40910140c001c0e88000e6008081c0b20f09809440f8980d110180f031541031010409000c2c92050b100d001c8900400d13002c0c411035106086044040860050302d01c006003010305015842070400b60344156080c43d01100030048030b240400c41d01d0308030b070040c068040141c0c0c012242950001081c60510704190364500d03a289044262041c00030325510b08402c10904a40c50740081c8400c9000e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 398952113 1250 398950863 398950901
    0x30c0703030314060121020d02070803010504060609080604420f02030903120405030d051006110115090b0d12090e09060103050c090a0b0a0608010302040f0605031e07030510 76
    0x3800c40800d00c1c802c04c4803510b0009140201381012019903101c40c8404114a100c014106a498490141203902100050b50700c1140400100f010349094003525000e1309007450132084803440c3c2010a40d40d0200a00010620991f84500402c8807202e45c030300c901c6c91021186500310403d107041c44400d00c1c05040c55400c01441c1092a0011444014003c890203330700001e005520744078001420300b41d0041c01030001c4603180010048040c4a1500b406828021030018a044640c54500180640600c1c3c12580c202050790501e42c000646480d01003442046910f14080411008103500015503000b40e003000c02021281e104581001e5a0360054803081950300443c0b44c00026200c03c242980c1d40c040900c00280360750b000c051001102c1c00c01180058114500800c08140828000e0007c0d080d215150007800001d040c001c0100150b207040d010700c1107090700da09410040b003410304000c291110310344a5101015000c001c5403000b9407030100801d4008540100c26100a840703241502009490300d2580ca002103101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 398953363 1250 398952113 398952131
    0x5030a111c1d0a180f24150c08041203051308030c07081906022506050712090309030b07181202030106050102030f07020103050604110a0e0306090d080a09050f030c07030303 76
    0x212200c008191952800e070700c510640b42e4401d0f90060305505d401d0254003501d0700c00e080700b01c2c0c41c24205091a0094050a03920040c00d205980c0c94049020940c0b004000c07048901a01165202c81128243c40c0c0d4885406003910703c034201925140325034903d030340244290441c000380d401c2c0d0101c040c0894903400d00c152114241d0782c503042a620341c8603a020580c408401c100040015070258000d2074a0b03d0020182c0c0b60710b4a181c4041070000c1031180080d075070036459504002c80f042c1d1009080c0a6540300d41410018000c10b030b1001040c1004030300000b0300600c060000702e034801d40110708982d194059040c076000300300d440f01c0d5500e45100340d03644200d000758201103003c1031540c008410354004c014105d208508003030540d00110041c000c06460160800e03602d0300910718504c40d0900400c5454a5034807240174205c00d00e400d16203051030007454910349400880840444030390202c0015040148000041801d400c3c07030a04c7e50800ea00351100c51528440000c01c0025200c1c00b24101048a010340ca0421a8181c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 398954613 1250 398953363 398953369
    0xc10050a0606051e36010930060f0207230d021b0607140d0905041e051e040c030b0c0306090c210127020705030a111c1d 53
    0x140c24240c40c4059404c28802d05014022018003180700841c0007602503800036820141c055040050b00141486454081c000c40d541c00491480c02000c0c540c80d010142c0c80c1e410101c40d8242081c004042070852510104028029a82c204500d45511403004540d5003070585010542c0d02d10380050f030002d6906905122190a2010880d12841119900600403480c071380117045108421083c0b02e10360206041c813103207000c1407455106c0d859200340c03d0002c0403881c01d00b500103000d0268540c01030b0310903030030301000240b06604d85007045000115103001003101d8a0b240102c464810b403412841c000010f0b003104110a00400f002e4031002c8900403c0440700039102c0041c1c801440c401100d059030003400ca400407410807802e4200410b00c04020100c8a416184900381ea40d2030300e00280c0c03000f42e00d400319142c0c0c2c100d40c95401503100c1000e401401d003185042501d0f07031050f4480c043e0280d10400e000c031485400e9034401e020b02c440c80d48900e9201e039500d500c179041c040140106552040c42202d1041d00c038980c0748141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 398955863 1250 398954613 398954617
    0x30a02010605030f061333150b0a050906040b070305040510091202150d060b04060e0102060f01030201030506190303030f05070c0f1b18140610140f0c10050a060605 72
    0x81d2000c0506175903600d4001248100440703000031030344601000164407001e1401c0c94411480449006110036141c04400004150764610013802229402c0b04003c215803218401121100c0c00039040ca561074112100c005a5207000f00c1d0310401c41c204002481c24209603018004005075042200d8144621b072260344122161101c80c0648806510800703540805450182d003100744d000c070848000f5150401c5e44140d0380581c0d00c5039000c04103c000128007400718641003141405520401e2004000f2440e200009030040281888060305060382d40d004034031191107584c02c103400c1b01890420704141c1950303440d004004119003070710400b51625003800b00360114810300507801d0b8607030801607a41049841e500c40484001410780e4841500305154400034580c0121400401105c9101d5070001d4518070324030011301c0750400240181d00c00c07d10842c2040400742c100400c0595102218040ba46030580c2284404071441001c13011100c80c0b2070054054003000c507540005124002c6010180002036a1700020f171214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 398957113 1250 398955863 398955883
    0x415080f10030305070807140618011415030a02060a09050112111905040801090c0305010e0c0d0326150f01021b090a0b180703050106020a030e040903140309030a0201060503 76
    0x104441e01003022074410005050000d000d400708902c1d0004036580c1085640107048014443e411001c104002c044103200290540c945d040024400f086a4100507182c46900504103860304402d13012041c0a920204091004c0c2a8050010b942da078810801c040d0401c0310b64403071280091143ea0710017281c03550074000d54506002d80c1c04014140407481140701c0c1039022070301503841000018840012090b00074015009000e0152040024150960078001d0075520480314100309a0300c2041445e0302c64880500c038000302501407030804014a1891080100007014000b6820340c0c40c1c4080502a070b20740880c2086103904e004a61041e1200c03800070040e40c0303d09a00100e041d0001483c4481022414401442a8450200c04000448000e64000103041c0f0442c0d11440c071420918504016425800d4443c86002d040305000030854400281d600800d20120100c80e540100d0b03c07074425070700b014061050100000802144c2d80d48900d4000e007200e0b83c80c0c010070400401913003441030014940c1404a03400b024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 398958363 1250 398957113 398957131
    0x1f080c0c15160e060a0c11060f07020f0a05091603020c01050a0506100309031b05010e03030112020307170304091d06070e0a0e04020a05090705071703010303080702190b1302060415080f 81
    0x20f090480605071000c800400d02529014052600f9007030f88e0b5504002484000d61419040707440380818014010b0489024840070302424807007509100d155a094001da5020429822246084d054003800310080e004140300f100300d0390b0810062280c607002c41e81001d4401e901c1030700c01704800c0d201b6480c1101601c014071405800704100002c2c98100600044e2a004150b00136000801c450641c0c05010b0310390341c826840111504138024613032045103001d00c003143c02403e51489108a40303058800490316403040f44610081c0d280d80e1480800742103103c00081e805607003c41c00365100c918000e0340203000315051105240c0305480300e500110b6560f040c4080306001c2c54002c0c01d1004020b0914062107645003000c0c01c070405016051100100140701c541c0000c0b0b0301c881e1400c90326280e51451401500045010f4021000d541104024600d0801403004082006801c101070214544aa6903021080e15021a011750003120000d070200c0c80003514503500300c203a02c10f6540d124282d91641061840c04806960481c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 398959613 1250 398958363 398958367
    0x150903360b030915090d141c0f09050f060f0a0c08040f08160303061a0a051204020a0503241f12110d0b04030206061f080c0c15160e06 59
    0x851650000b82d03921a4000085882100e0040684c0fa00610100e405442c10b500960b800102640c0c883e014050b41c01400d090a0b06001184020000301d0403030744810440e90742e950303620040780a405d40103c0015500042902c520221544289803911800c40d045029031038640045103113012148038204101003e980d03520304076182d60740c0703407400c803419241e0603507130000d0911140c02403c01803908614028802d840010301180b6115844207080b00c10080100240c00c24046841c202c0d030010121200d41c803071040208000c0da5203100083d40000d968209941511500c40140709503e005210800341d1500024182c80c9542d500d0b00d803049100c10007001181100e40a04100000009070542000c5d091003a1011000d80c484803011036640c0f1a00e000c25145108107030300b40001d040d0140314140d00214151022105408021a546404020034400d40f042000050010340400c40c9101503681c00418a816618001c0581407144040e03c0162140f00c12229078150300c110350380c0034110f021215031024100d18 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 398960863 1250 398959613 398959619
    0x70b0f150111030f0415030606030522170c010f06080105060a061115070e0108090109020a050f06041a070b09030a1e1b0b0108010c1704060915090336 66
    0x1212490050750800b40d5200502110b0300c1000c9102c082d10103070613011031103000000c01ca00e000b01584e4140d03010300f0a25242c5420700c10004018400d030195028200286c2015641a20307064035801001d110703443c130280010404c041030f20010b401c00c004c843d41c03020b000e0045503101c1e9200c908030744058903103d03400030f00c40304104080783c0034010307424040e41e0400c2036840501d000090303151882401c0b600300001034100010140d0079a040901c1541000340750000700f2840d07000c0e03800714942610b0384c0500c520828200c0a404090f5460900711406400b0000340603071110880d840d04c1100303030410b0304111543c68804001920600f4000107540c5a50000d81e20f4480c4108e0b200101c0d0403000106a07004200a00303001c00b07014102a204807101285d226081201c999803401c40d0076421100340003a0a820440d04100c40c28141c1c1441d2000c0f6006a08400001054519460070260108003403128100090401d030740c0340d042c141c200d03800c0c903140204500034840f15480d11840780108410b5800d0700c110444401f40c00c6c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 398962113 1250 398960863 398960867
    0x906081605040c09080105010303051b0c090a0f0b1801050a0b12070c0f051c02070b0a020307020f0415090b04060605030702030712180902040513090c0b070c0302090903070b0f1501 79
    0x1014900c8004c0c02c120010755181c60b40182541c200b6042079020401c001001c0001380c005d800007100c504640f0024041011440c400106114006404044c0050312000600011400da034000d09482800030031007002000380b500502c4203010240305607442100409000150480d00350f00316400c842c0c1e200d400c0c1510f50398601c000d0360b901c1401003050b5540c1d002d48140c07034000341080064001d841c413419115582c41d00d400b60002d1401078107800035104180309010b4002d02c030360004280c40046604448000211107000045402011888805451441081000908140d03654080300228106030f0301444082d80f191800d40700380c4805d071031180041e0b1040012401081c000c115075641103155144c564442440c0b49a00601c1007000d81000460743d0f0700140c1000710340f40071501424a034070303000410710400102c0e44030b200c40144103204101c54050f00081d44820850b15280c6640034550080c613400c1380d41400382800769250003022044540d074100c50046901d0000c40e0a80a00c6101800d00305001c00e6814001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 398963363 1250 398962113 398962121
    0x10b060702181f0608060307151709010213031b0b03010f030b13021207050a050901060c150216030815120d14090406030b07081e0606072307090608160504 68
    0x102d100030b03c152003091070150258084038001c103400d986a40440c1021410141044d160ba401891007200d4800403441d010303005180010541c0d1481c40d10710301030b910051424068810481d03c1610286045004001c00800201a80c00c0b024020199445941c407050600041c1c0300030300850000242a400c10000503051380d040a03803024203540d4901903c50b03203070b020507207640d1400600052a00440b106114900700a07804400924007210543c0c0c580d49020009480701901700c0015200d1880c07001001e00c904041e4040f074920b5190014641d81060550900030805401500c0c000500a0080c420040b5490f1034500500d03007040100180c07000e00f03204181558410070284003506c10070010700c1000d880e0399551203190b0046005e0f0000300107520741389500900300e45004007449280b55045a6003070b58003440095075a809001a240c9a65800c100d050400c00d045070868066003210180e0114a10360101003590130480e4003d24051003032540340d2804a8a4100e0420034000d40d07a20000c04009510300703504 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 398964613 1250 398963363 398963371
    0xa020f011521060c0503010915150509030a0b0f0a0b010206190e1e0703060e0f0613080d0c030c030c03020f0d09170c0a031202160f0201260603010b06070218 69
    0x107038880082c03202e603203000945049039604800301e000072004205902c00c41c080c5034060300c0c81c11078010b6141e04117043d500b1030010801d184004c10001054030b81058408108041e0b0b02074100700d1110700c614001e100d410715594222180d104042c200281c0c400c80d5400000c11034002c0040721070307000b000314481205400608080128070294840c0c91006540d501d011444100c60700d0403000a86800d0342181001c80c19601945982242540868507210b003403100458415013090340e05040801400041c00c16454600884d1140c1c0c0d04c00e4641a02c50034040e41580c0301c2e044084482d00c0030f105424903180150200c0c01444980040c400007040000903e6085600c400300891145050540321941d80a00c0c40381e903040030341c0602c81c5510042d042010b00d0741000d9100780c9c00740a0b20081d481e282910050740010081548001c0101c1c1d0420400400c680c0200015807881109044490300b0035296820341c0070419054070703041c1c0030303500e003040745d84150620301c0880740141c1d00030340388842181d0781400145451030014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 398965863 1250 398964613 398964659
    0x27060e030415021c230d1407030b01020c330c071d0a050c0405040518030d062c07050c0106081914010623060d05010602030a020f0115 59
    0x20002c1000806840d42c510b0701911603004085134441d44132514018942280074030705000c107001902250b00e101e0751010100f00a00440711b030700d0f12003010700c03540a00030342601915000da004003000802941340e0700000301070000341c0c00c8840561b000d40601030029100c002580440c0704001290000c080074802c2c00c140882078014092901a003020b01c11b044c042141c0240c0c40904000000c03450001420200c240c0001c1d203500100660b092803255000e840c45503114807400b40c0d0312000081c0078180c4414402c00c40c5284441560741d45c0c4210302002004143c2400b611030f402c40c10410a00e2409642c509600500c400b445070b07070156441d50007064810b60085240d211066498003004104600e040c8204210410020180d0590401e00d141880b881c2054000721200d0342e160100800101401c4002d507401e000243da003254400710204003061b500c0c0301d145c2643c5d84003400d010002803000d6000000b4070b070b00c032034540c2a2540009070031000380c240c036201c0e07104171000448650240070340450091100303400b40c00e00d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 398967113 1250 398965863 398965867
    0xb091b180a030308010303021e07090902010c021305010504180f0201032c030a080c070b06060315030304080c041103070c03050a051c06030201090501090f120c080f030c0127060e03 79
    0x40c4001940842940d00100c1c00103044400410401da0100800004556448a002c1800407120000c03941c0c0d10144c030072a0b0703405440c0c920f090305690140160344141a0050008001d0001d40740400d0040d25083c4205801240f034240144a0003450680c04000c0e00c4d130203402c49071504040d0b00118007038861a018203102d0442c201c4e403416a4050f884100c6150f03103008018545540b1201005000160300904402d0401c0c000c00110002540103a10117602c00d80c22a07110351a52144201c0b0054a2050b107401600b5200c002000f0503082000204100d0301030003280c00340240049007088508074081a15440042440e4018001c00a80204007518420030140b81c441c3c280b045070301104528985d40200c41005690300e010034000d650f4001c001030090308003800d003002c109140160840c3c107007103680708005050752121000300800242c124480004c010400c00c5402100600446986983c00060204515071800e80c5030074400c00c2c111341c0c00b24120301e4101c1000d072500c844c2e214900600b1880255100070b001c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 398968363 1250 398967113 398967157
    0x15130c03020909040506071e0519030b10110c060903100b01020c0924040c02030d0207021314010905010f0b09120a05010c020309040614150706060302030709020d0b091b 74
    0x1a440045218034010340086c4520b04003410007a0030081560102072020554203e007012485d084001c5803483e940440d4120f42c000042c1e4812401009001c4101d9031100c1c2454140840e150f21034003006aa081003016202040704100401c08140f15110030b02d40c00d078001160005220f02a0f502c050f8180406005407076006070200001084108111120740d52551044105c101303c000070319000c09010790950301040041142e00f0080d640340654101c0a80064000075540112348809200144140a804041c49540141c2282001c280000d00400e94520b1408000003107280301c10800c00c00300c1e640d88801c4c51511858406200c000200d4503044641885020a8400012030920072014240310355809103880350381c20b40803c02541c245034041d0350107100358030541095039a5400710080030b10901d03c0c400c0c0c0e14600e902d0200040c18988d480654540541c00001a130030308070350020010041c590710100540d42e000307020413009900607905031b000100102e51140403620f07080004e0111038906403560019440b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 398969613 1250 398968363 398968369
    0x2011107090f020408060702060903180d020a08010501051c020904080322030201020a020c01232d300c0904090803270604080f070303110d0e0615130c030209 69
    0xb010300070800e1001e500013020085102c0600c85560841d04d10302c0502128141a80c00030342d00d0190352561300000f90007020b12580c6a84441c403121260794050507104c000f503030f2030b09028001c1800b44940b50041c07610240303111852070700416607c150b0340d000780700004030f07100d0352031310a10f40d007000302030000800002001c0c41c0380e02d549400705101c1521035800076030340741c1d0789034402070800c09020074290500040d2204200340307440030b5000c0200700c80200681e07501d8101c0d03c2d0010b4455008460304a40503880e41a141d99100705d81c034002d00755207105000e00f040404182c242c0828110181c80c0d10481541940049000c0249000003417001c508000e2000c103a20310036032140765142d442a81d202941e03480c07824210280a0318500c0c0401840c5c1c2e10b20146c1030518164607446154030810b8800307407000c81d0010780c1c001010b0107540002440c1102d4a1070079151300700071168100414211808081c640320303c2c030001d240d450a640c0400358092000e003a00c041034040d030308894090700034a20120b00b4550248102c2015803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 398970863 1250 398969613 398969621
    0x28170a03050901111b04110c06010312020c0d14070b0a02030d050601030608030f0301030605010e0403090314070e040f0212030a021009060207060c0c0b06060f090904050c03070b040806061c0201110709 88
    0x30001c2985d12001000c07400c00c8100c0741c1102261074040028001c031510703418081401411650081d00c8000306996140049040040624610740d001c490f038180b040501c00401c007801007890b503020449070529100c03041d0348124003404a00d0300059108100798001c404803600081d42005060402141c1151600c1c60f603403c54202d0fa80c680d0b02180044010020301100e406030a004001c05020020307941400d450042001d0618040078007c80b0313080140c030443d07100c20401c810080c09140c0e0201c210381003500d0122002d00802d5000d91250003c000381c0c840c0042c020044590b405d03143d800911030207060241c0c450240c400f5810642c2c01d60360920031440030174814000c3c0ca2002005944101010b0b80f1031404295803603020b408580205010b0058140c4944500e04840580604551915640e41c0398039101d45000398101107141c05000e18100040d0051210000e070007500c0011003680c030716507035003402d100300915550340c0341419540c00120400594082e182240c202c000720001d480c60152a00048400d03a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 398972113 1250 398970863 398970883
    0x20c0901080d18061b1703010303110c0909071806090e06010513020405010c030c0f0f110f030127140f16060206060f040506060928170a0305090111 65
    0x250040401a0491607002070b2030981046440c0c4801d03c807504100c00100070400e1244421051040c0d8003508060200051640c8100c100c1d0002c6541d40790384034a07005001a00c0191043c10a1080007070b815070758580751900c240704200c40f100030134015280203018100c2d00810707124080042c1d580c007404901c5000740d02900307a0450605000f00995450300c0c1c248400301410381000d003000d03072050100303000d42d0307038403c485464607505440c01088441c010704040c9440e040e0b00c140142240709006200041140303100602101d24000c642c1200120840380915081c2c40d03860004152035004111144100f1040401054074a0701950010032410107910b546807500544000055041d4855111088560780c50b0518402808181c8042c0103142011004101c40745102d4207118030440c0c803440006c407940c40d01d01c1518582c042c0108150061844c00b07101c0416003005042da020f20844800012403035140c3c100360842200d000740e00400038180551000c03a00b0f60440342441d410842c50486d112a2543c04010103440c4d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 398973363 1250 398972113 398972129
    0x303050703020c0708240103050c0d080918010e09010b0d06020c011401060504050a090e0309121002070f0b0106140307080702070b040b1305150406030209150c060108121810020c0901 80
    0x31811800d10510349610b1905048843c03400c44014400604c0c0407440c200b143c4814be038442c94000e800d103441090390041d0400203801c161140c940c980a15450782001d8100d41d4500144c10305610340b080f9140c01e0762260311641d03420031011440100000d0803980140f005005c43d000008500180c61700100b00110217034819000140003103002c0c022031038008103d2000f00000f20707041003900360050b4076940b039000e82400e0601c50001c4c404007010415092040c1200f100e05041c1c11540c44140e4038020350300e4020000d05840c1d48207000c0000c80c61900508d501d81d0f42d4144035160354110b0f40d0f8500100c4a503980113105c0000c50183c6040090924014000b50015010308000c05480b042c001c01c0c1006690b602c2d81c8000d00c19110020750115070443c5804480580d089031401590f0350100c1d801103070400c2039851256402070000544101440d401003103060680710a281a20b050f07042030141c52000303014400c681e403003100303109101242c80d140c0100c0111070891940140e80c0105c9882c40000d80701d1500342c0c04410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 398974613 1250 398973363 398973373
    0x9020705030a0809060f0f18070f061106070203040326040e0403030b1906031508060103060e2a0d020319060b0a120b0c0c0a0c03030504060801050f09040303050703020c0708 76
    0x10b5a07035000903000d42d100340d0040c0200014074103807651205001015024000702000c44c03000c1025101c810381801e11612100003100c82c240c0e9184a10440b1419902c40c400004050403c907a4a4050108209024041d80e60017103080034211b4980400c02410a00c1e6401c9400f441f816102c0c106007480050001044041202c0000d4035050402405549200b40118440c0c88414a1030003030007039941d14002035640c0c5140c006a134503840b4200d0ba21140150b00072029610035400000100f0049030400311504039060b00740c0d00c000c815040c0729110448a081d0400c03052522401c00740141c2407501000c2202400101150100c1660810384802010b602d2000c1e00e859894000d61b0150741009119000104400e901140102a0310340725030290540241c02c0300d04031000041c4003424100100b00341c0c00015000f200040d40f6a40c0c80c40e0103041e651142c0b0610002c2142d20380000362a181800e8910200340001c1d041894aa40341d0b5002c5009200040444003450703402d0140d00c050030b5040140f900a4426440201 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 398975863 1250 398974613 398974627
    0x50310060813050f162408071214040201090b0a0206220b0f01050307171903090f0608090105011403190201030f090c170606010c0609050c280503010c0e0d08040902070503 75
    0x3c008940c1a400c0000d0031040c02d0803032500f070400301148091409042c50825000e403a00e410854220342c040c9d078004a00ca0802109110200041020a001d18401d0300c84070442d136034598400b40e950040940d5100580c01000025011001d0200880d510f5a40403c5451103544541d4842018980903114104a050820300521030742c2400c1081130041c02d162005000300705408000c595541c21040301503c456801d0903074103801c03d805005810058150050841501600c1d4500181004c0c000c50b800c000c03030342c28070000080c01c1070403070302c2034810000190117440030085048012207012150305d012030425940f0100301000b225179220b45c00c0c2c9244550b0000d01002c2c80c11840c510604403100c0c0d0305200e0340001b018441107a800020641a607a88580080740030700d000d0405508000c4d00160054202940c88216003007003080030106175a1940360f6003802c03c40c6803200181805c0754055502d8602140205142c40c0b42e6140c0701e0302804442e403041035900e00d403c1e142c94120040c0d8101040840d29540701041e11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 398977113 1250 398975863 398975893
    0x308010b0d291206130f02030c03011410060906050a050c07150c020f100813060b040f05040b100803040902130306020417101a0103020d0e06180d050310060813050f 72
    0x10412182c003c8014091420502c0d04500c40042100307000f032884004242180840d2001c0c000e1049148006000308001034628070038450450003105c8100303108070b50140210b699800303000c403801541c3e207558402d41040f41504041c1c0f02d50f4085c15484103280300b8000300050084015051f107030f80104a90328018808501d20503c4020511191428481c060b40031803182195401034003264419001d01080d220380070b04e4104540144181c02c0030b1500142406a01800c03c89507401a0380210310607402181140d0b2200e800700c64600060260b00d4140d00108010059200203402a164a0b42a1242e03040d00559036a10941268004d80c066504a15402c03001184164207000061101070b1041041c401c07420050f2402d010b0030352401050703061513800b103512200c0c820a0340c072401b2140320203c200e809030300340a00015440e244907210040f05128440d01d100c1d22920501c241c0307019040c0b28040300300e0582455001e855548005004403104e6402020040109204102c45011000f6000150000d40400140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 398978363 1250 398977113 398977129
    0x322120207082406010f0c06090b0f06061c05090f07180605010807090e102606090a0209040b0421050a020607030b030a06050a1b030515010c0308010b0d29 68
    0x103000300e020b045110740c00074042000c1e00707650b04c0301007442d0000300702e0801c2e40203403805401c21034050885841c000080c010051110641c500400b5590740107032242da580800c101c00740c818140020b1031010602c110b18011521900401e0300301e81040147e980a28460401740c2c9401c10366400071300030481d1101c1d003100400c4548503c4000c9d00c001e1074500304900e89100b01808541040c41102c8941688100240c20b0030700103145900546040e800a544030700480f8110782d40007507100400a45d40c003c20300400d00d00240007a0019403240d015060070740e04d68603906c6000c840f40d0014400d0315401103020300440d0303695082d0750100d40c2e01c6003900c40c19221580000005d2816500400c1441411b180c46600355641e0b0380002e0005070b00d94440404112555074201c070a015040840c64082600b40c002c0d500d052007500360b0031052107409409500180b403c80c1000440fa52100300c1340182c046102c007001880072661080040c40b074540000000b00d019071806d0314580350f00003030901281d00f5000b00065940d142c41d004d24 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 398979613 1250 398978363 398978383
    0x612050c09160203070b09100e100e030901090b090f220c0903020a0b09010915030915020712260708010305060609090309100207090e01050106081803032212020708 72
    0x14000180c20b0008042e690740704050f4040c1a41e1550301c001840e50004000c13515108020b0306041c0320301200b07880411343e102c0200242a0750705003480c0000350544800020b66400280582d110301e441442c001c9031410a9101caa401a04140003c40d540401d071030f4900c06030880810a002ca00c180032a09544500f00c43c9000c80c0e0b18200726000c0010400b591703810549030706072480200d403180d80386040b0b00103032420011a0300225000e10080919070005400d544103038900d81c001e00c03a0410041070302c06804124403d400006080030f99480c03034100d0f06407240590030b900340203620861140d540e451750302034020003045a4250016108900500820005011880e0030040c191500300381d5003000002c4030341768000c160764a4010200100304c800038a1007004040010004298100a00e2103040c51190282c0001d0045801007080100031507003d9180d40c104242620381c001c007840c01c503201c2e86010400d8a581580e20543c41e850207144102084604080ea03505030340c0c41c3c0041403400c5c0381c07546460520510340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 398980863 1250 398979613 398979631
    0x60a08010e15010f12090209040b091908071b090204030c180504030c030806010207050406091a010903080d0218060c0a03080924070519080106021c020a0b06040612050c09 75
    0x3010390350b503600499901805103031400d06448500b20010084000d1820f028081e500c51000317024070050080c0c144038240508500401c1c0c03241c0821170050f0410b0f0104144004105c05410009d0001080184502c00039034800300b9000d5035055a070303241043c2a608180c0094425800c024010042481d42c000081c00590a00c10705106038641924045c0c0444042c0700054280089140094400d0b8400d001c2d04025001c0104208a01500c81051100070158410385900220854018400541c003403400002200d5201030068904001540781c04d01a420020121200021110b140300f03146d9a5003001d01030002070200208101010b07410700078045c14024107614599083310320180100e1052020425106c0c00c03180d8064059150300100321024824294809143c4a01601400010f0b40c0403003024120f400ca90700301d8a0920300e44020100a99030b070b10002e80964014444d5100148002598584c081c3c4000c000041c095518100c20009540c0810101c1d4190030400000001d40f0f440e91031590007600318 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 398982113 1250 398980863 398980891
    0x705041a0901031808031602031c0e060105030604020603011404091e0507090605031b0609060a180b03330306010f0f08031204020904060603020d0326060f120c060a08010e 75
    0x1390715065182d00c4003421542607003413403c2003521050300820031280400f501413010a8000300a100000c01408044400c2a042c010b600000545180010b40300b8020b03900140120301e10791814220080c21080010341c650000c1d210850340700895900300001d5501c1411a2010741c42801924049090075030507040308401c103117000d030240b160780c4000075461800008158195403644075800042d020340541d200c50b49c0c1c0000300141b84a0505d034405c1201c403100c003604414007440c41e00e170326a0400ba40005c40301408031420480b4685851242c1030f01200c1d0b616002000c01d401c420300c00b40400e013413000076007002072084510b07502048100440003da034014440f000142d402c11003108062890b903140030300302038413480c0c20101050911451342c4c422402542c0c018107130441044149006011440612821b00140e10707400b42101008501280395403045100800300a074100c2428104074130f18050aa81c0980791240d22604e032526211b8034002d0106810507141c0380c14540c98180405104c10707000b4400b040301e82074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 398983363 1250 398982113 398982161
    0x7030f08010b1e040504020705160e070c20030a031121220b1207171015090b040b030103020f010c050c04020717070b0a050901060305060406050705041a090103 70
    0x106020340340035103d20740449003050000348040740c0d5405540c002c20740c020b20006440d020040c00080c80c65064168010513041d483e503813906900c441d08100c4601003c641c5e43c1c84004002000c02c41158801d5000c29034140e0503015080110f4074040c0700040031408103001030355201c80b0000c2000386114015040c42000795807c04005840504e00400c0003041c80c0d0601050401c40b5510a41d881c8000380c000328000396164900304c00c0d44401c2440584954010450050050150b80e071421a81445080b64843c1e01c2c201610b42024042814004030040e810404544400726125000707400a00090920320078841d169410b5004021381013603480190343c1403100701040e10002400c04100c1414a140845006894020302d0802400d002c071041c0001c0c0c040302c400107861080241103540a4040c00b4151000c0000e0365660074620308940d4240000f030100c0d0300450001e00020ba16400003540441149005810107990b5100c01280c03d10501c40343d042203401054242c51541e05114101e160203508942c0d60800724 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 398984613 1250 398983363 398983379
    0x311160c17031902030f070f06180f0201120f02131d0103150902010e04020423060343020a050d020102030f070521100306060f03082a0307030507030f0801 68
    0x10a00b2443d600411801100707148003030003031060f2070100a040c181260b555180b454200403031280e80350102c1b112490148092400c500d013100c06102d0300d9001542011494054006454010505c28540c0c0041c4d15281203420b6007007103002030034829142304074101e01e00e81031100781d0401d542c3c1100748a145003030360001000880d1402150642a46403c1c20024800c1c1e0709000480380c18030028032441c0c0040c000500014030280b0701013a50318244005690115040d42c0c0000c106091109881c0d0040c03614505070b686802c012075081d245c000d03040300b81c60f03ea085c0e56241c0715501082420200318016030410f44101c801c0c40403e008131000e06400e88021840c600e020900c500641c1005000c4c4802c01c1000714140c2011100c09086855082401c04074400525015078200e1104403140002c0315110b08145000800c82101d551b10804e80703600401c01c40c217042d00d420004d0254502514803030302c000c6200000142c415000d20080006c1c80c0295600c03555040b003401d0140c0102820380c950410400d400b001044948 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 398985863 1250 398984613 398984617
    0x110a2c041e08070b280e0309150c01050c0406020f0610140409061e0c0c170c0724081e01290d0905010c021b060304030311160c1703 58
    0x4001c0c84a03000180e245401d19108901920400030b01e11045441409803000003a06001c0703c080c5803400c40906504442c0c921000e5036100b0383d0011480d401809440340b81d203400d1440303001000108242030300304114034105500303489054a4201b410b84001400b4010b40780e051141c0021461107038010b00260801d0110311350070410511510725114096000398100740d880e07410114001d03030030940c180440c000099a162540881c00c030295003542c40d102c556000321b8029150340e040d0700e0700021501c034071080c162080140380d40280c0e031201007405440340224148025150b80b400490890001c0e806c101003000b0043c00540d0060b02103869644020f10022100c1ea64828450545a501d141075001d43c4440c501030000548090040c10321800c0450f503901032844a910040d40680168024070107418185026070b16800585940340c0d0f469410404107005003094401907402501c20310380005c0420384003900000c0f6420004070400c11948400d50801880b0107091404054440c0205160000400f032255a680f4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 398987113 1250 398985863 398985893
    0xf0f1401060906090e06210a030f02100e1203060d020616020f0a050f10050904140a1d03070f020d12050705120408030d09060b0d12020d050a09050904110a2c04 70
    0x550355580004020b07d00d4200588800b0072104204e0701c5501c9a884e0142406c1004c00711040144202091880341c0c10413406811000d08c144005814290200940254581e1000f001c40e03800080d00016040180c0700d420050007411240300582c13134090316901c10031080c8a800b15820f441ba018a40080c0600d54603400355140510303089490840c080c52542055030f003801f40c01e85607a40700303181c070504510060750010b4140c4141c0410b0000c0011514980764040184080751803c00036038424420007000075116041200e03042c0c00241620525103e503901d00d9910520b40400900140e0042010303020040c041040a90809103080d01604150405508a9690184181151405c7d4603024460280911a0b01086950002424100307141026041010480e400b400d0300c00d0049c82410060351103103109000303440089440356500c1c41c00754508800c1020303035003001e0010764684882a12055042c2d5030381e20036100a01000580808118070003034603012120181564245400d2600108000075480d01000c3c02a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 398988363 1250 398987113 398987119
    0x605010c08040501050306010908161e031220060a020703020c010c15021c09030203131e05041e1e11070f08070c080d0e0f030d0c060f0f1401060906090e06 68
    0x182d60f1f80300700403034600142d544141054090f05020b1140225640900b8095442c807680380e034940c0c0c0d0042001c0b40c11143c14440540140c00084070840014404c2d645ca02600480c03882035940f8403402d85500e4100101550520801540040c2c48001c054041c040001d00003403d09140f030003821640c940c10340304040d405400e0f46191703000480f100c07809942d5401c2014600540020006a1024a4080d540b40c0c018041102c406102043c0002d80111100d840341c44a0105c0410213545c518000500010385942d40c50440d0540480d10b11200b090828404c0e8902e4444500c01401202e0406c1c609008813500c1510a68045400f040b40c20702081024074071440c513a509c80101030362595641418030781e0104c82d800c400902e020381c0e20040c004640c40000422850b40c1182c58820310a114410185c1c0e4124505080e80418100708060703001c61080e5211141d100c55560001ca036050300d034009e100454080107040310180c00c1d0100140f00165000b6052800f5088604040b4011f5051400d1110f0390340b4000c00244c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 398989613 1250 398988363 398988367
    0x801050115052b060306060f0302011404140112020705060405070501080a02090306041203021c0203010f050402070b0601030f0e150103060b09042a0e04080a11030f0a1803050607020708010605010c0804050105 91
    0x10000c069010000846d0018010010303103882c0d600202e0201c0e1f05200581c0090b104a0384040010070f49003c42c1c088400c03801c007a540000030305005469a41c44c90f145408042c3d424003445002c10014001c50344124414000382080904140001d03211900140003000d00d144140201c1d9016240003031015003141e0801c411900010f1500d10840280c800d10810400003550b03440c1e580188a41a000b65040c3d034445000f504200707403590148030807405103101c042d000c1c2c0d04100100d59294020352000701000c80540004c035841340301d421130500e826005c01d40c000c4c41030440380c0100184140c600c00c00000c42c030219400402d5090503112100c0724171240c0c440b001041c00e02032022003140341c1060040002c04a0f02d03491241843d00d41000541900907441581c0442c000c1c1246101501c3c001c401c60b1400d0030200c1540303040204807501200c0119043d170440c01440d590070804400300341c0810901d482600154002c1600c82d0030840440c0c02d40740d403a80325905100030100f480000491200943c0d05490f02840c0c030507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 398990863 1250 398989613 398989687
    0x207050f06061507210c030905040207020f0f040e0303071805040504050d0825170a09080301090e071a0c0d09050915040b0d060230040204111201080105011505 70
    0x2c5081812045c20680c0050440d040300303901c0c1c1000e81c0f40645406911b8401d2110350b16420300040e44078032100203501042013452032441d40350455a00540190290000030a2074a415103d4615401942c00c1004200c0704841d8841241540a2210140000751018012410aa9999599400800f10710401d0101c06000588603810b07840e02842d09109040c141d0000b9001c8450145c400b01d03545802d015000300703807800102c1c0302a650044041155108002600e03680c41c00388000c000b881c94402d100c0a43c0282039002983c2c034105400d028108074a050302c1e035900d0102007030003880c0c0110007880d00180040241c0410840c2c5d0350007070855000c4100380420808414480020b001400c1c0c000109601852564070901804031a40c0038107081190400251300303400a84107410b200044000441d013a4071682c200280050400340c00140c0c0c50305034191034508107104801306081e03040098010359210381d585e400406c540203400303666084c41c0320303942000361038260b0340049803441d4000d40742100a03640074180030b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 398992113 1250 398990863 398990873
    0x41a120309030d110f0607090f0b030f0a0b0a12060218090115080a0e0609100b0f030a060207061805030a1209021c020604081b040f060609090b180a0207050f06061507 73
    0xc1941d8403907150551b42d80d890030000191400c43c1900035608a01180507000c01c030008040c0449011b03058407a40940ea9596003004080540301601215030056910000007d900708032090b40d0410318400d000140e1240c46420029032080300e50800300f4815660400104405114450301c003c04c0000e51400584582c1e4055a81020304100800030f0a14172941d0b0400c03100200100384090189503100c0305202c0301700e0090401c031911410300c20042d41a04402c01600020341c03207600a141d051700c0f4081c04100d01100409001886841c03031003d450982000885920f081c2e880301c80046101c00705a8100015a050303008070b40b03501c81d521159001c2e443e41701c500005660340c000c1554000c21102c01141e42002410300c411541d503401d50246401541060002d401400171401a1010395102369100c1d401c030740c035200d081b8010740344900c055a00101c1c0d403015662041c0301c2c0da09c0c16206507030944005d0303076074502403801610b810b000035910700040d084a010322000b41c0d903209400f007441180b14603d946440080c101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 398993363 1250 398992113 398992123
    0x80d11010e0a020618061606020904060501030605150d0608070618092315090a060501030506090f0705220b070308070306080304060c1a04050c0910081c0e041a120309030d11 76
    0x20465034a481510204100728103074005114ac5a000c0d074003401441d07960001941503854038021130354010280801c80b800f0700e13889400b41c1400c42c00004007107659035440c4940d500389909038011200042450110090303c0240c00d0b504030080826200170800c64503101944041e04045a0540303000346031150124400d52902c2100044444001748010024202840c91900420140c41a2404241440d0010f00940341c044441c5101d240b15005144d85a564484116940c5e4409840700a804418640881c9100502c00280700940040e40410303680e11210304010b00000c60080c848020181000c0e0284a0a20084140c4088074440d00305150041c0583c40c040b40e0045a10a42141e070422010400051200000340880d10300c03c140e412541a48481400d664200914004c3d0031840c4c2c803085560000311000c072400220060b0345c0c50038560300d40c240d200280c00e80c1d10342d10905000f01d803100c00641e101c6c076001d40c000c02d4447c80c0d02c0003036140c40002c80109490b070601c4070448050001d4078402418504090003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 398994613 1250 398993363 398993377
    0x9010e060c0625020319030203040c031403040306050a0209010e12010906050915091513020f10020609010c0309020901090b150a1115070c1b080d11010e0a02061806 72
    0x100b5100549481d1680340b0350b1031440f0300d40109604440c141c24240b01d0010080701c10240e04110003100e4546d000c0815006540040c104032072902c103038040000480e5054540170824401c44010719aa2446d605024080d580f025280078006403040090800c2c41c0c1e0403000043c503219003654040e004240c80c1c03103954014104051702902075410003040240c0c4c407501052010346030754004d002d00304544405a40d15a00c035008034031030800c10a47c2c0d000c2002050007030703180b02d0b210b44002d00c0d1030f04a50b01d0310042519004d207035100c1c402503400802030010b6100c0c01e00802100040341d00d0700f040b10802d01d07000504080b20600c5404401699035190f0140c5031500040c030000c00d9113420032141e6500c020300f001410860b24100c5604d01e402044181000e01d03598a02c40340c0610764a641d64060701c0750b071341c0302e492090950300b241d02c0321020701c0100081c0320201440007070310b95080e82c0c0310704040d200c2c0c0142c0203094800d100181311694020861590069079114282d80740c410740c090440d02e41e880380d600425103910800b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 398995863 1250 398994613 398994637
    0x13050f0115170102090d0b040f020616050d1b080c0a0804030b0708010b2115032a0a08150414121b01060b030c07110a0e01060212040b09010e06 63
    0x41c0781c4008100e00e00c003a10044032182d00801020b948649402400c0b800380c0c0780e01c0e950000f054200302000c5904c0700607680e0441d0041e29010034141480d03002400307036485162000606803d600310702c002d0040c01d20000c0060342541c1481c2e00c1c180f07100004405890286180200004e2004c41c0540c5019010000a55260380c425450340d65141c8078286480e0030b60707040b52804002145640045200c2020405540345141c0e8a101c46c840711112001030b90580310000d100741402e040c920010070580e070b010442a158007002d40c20283c074540d03c202690880a2403e2000790080c055001e003041303144800500d41c0d4000424203908920341d00c0d54508040c0c52490451444000d00c01c0e04a4952000c81c100c0060036480001c65220708407440c0708080743c0c02e8400d035118011050b03909000043d040414103000340501c0f0b104040c40c46c4101d00700f400045805030a50040140444200018404141c04100c842c04080102c4469810980740200501c100c4c81508d00e2a030401100d0890126942c44410545011011003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 398997113 1250 398995863 398995871
    0x504153507031419090f0807050613170706020702130c09050925020a140d0f02010903020a080319051005150309120a050f0a030c032403110a03051207060c0801080613050f01 76
    0xa01f411184e03034001d144203a502d4040c10b004070310754501d400489040c255109000c881070800c50100d958003500a02c4090701c400e41c0030800c000041e81c55109004581d0105400024200400d07180142000f034035070000c40c0100006001e00001540e80034101c5035240500302c0004c621081c00808908014004d00001c16021004489600427180401c074080601a25515010032220707451007242070300c4c0e030081e0140150300300100800100b0700340e00c019680690a0500340c040d0110b42041030040f240220b0715000c0c0c5120b040c43c1401349141003041e440d1488102c07610582103080c5003a50320748038094901c002025100000344011100d00502c16190041049501e00e601c5641d0400090041c14101c6d0045001038644003c824860f48980b20114040700d108080d000400e05690306c1108400e9081038075980f0198007040040080c4040200000e081d00790060340380c4a80e07007440d207241900c540e01078980911080078010f004d821000201c0d2940083c4c0d1144000540080b8245207091440c10b9061511550030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 398998363 1250 398997113 398997143
    0x306040207062d0c08070503040b150a0b09030c040e03040b09190909030807050a09050f0301150303021b040603020f06030a1401121b06050415350703141909 69
    0xc1082070001c030f00c2140c806100f14056080200d40c000b20844803140822002d01c0400c0100e10070717686855001e20742e90600d1300d203040c840b80081d8a5520300c1e40450016000010701828a0034240708580b02e42c0030994051044080e0400007680740c1c0a24020340f0251320b004a200c2c091561840c6442d10200d030034150082601c1d403114020409040794840690210340e03401c0100b0b10051040c01100e542200700d5860940140c1007504203c408410184103560540d2168400d15048078a800c00c640158826002040001d400140140301c0c054202000c900c036030700c3c104e82000541c81d00e1002c17904840003151004d55954659002100600300c40110068019041001255100591341e107503800034083c51485040a0f421404c8556070f801030f02076000021014030007008583c20b281d410900980c081c0c1411050041041115000011511a90700e04003c0401c10540e1200003041c0298000714585418407a2000d0f1105521004002070001005009220071401c18000554809002258000c800080c007600c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 398999613 1250 398998363 398998421
    0x50406020c06060910060c02060409020307092c04080d180320060610080405121201030c050f15130803071b0e1302010309060216050d0e0d08030604020706 68
    0x1070300440c1128810503010803040d00c1d180346001c3c41003054002da565110f003000b034121080022540103e0300304000340404a450041d50001d148140301c1c0340d40701510341e4600210b01c884882104901c03003640d113124103091540300603138a07107a80c0305030080c01942c1d03145040d42c030503c0180000c00500301002c200101d6a8200750780042001d10240710b40c058050744a0a400d5050344800007a220a076001000499582545011b800e219a00034012000d90b2a000b180c400c0d642c1c0f031035120003030000c5104080c0c4014820001a44e00703002c0600030607541c2e250074100d540c0105028803601e03205400041004240380c03c0021807007582c1005006d000341500d031181c00510b46170f40648e22006080821a25030709002c41d08074150b0900521500060000f5904404203400540042a03c00310582d5110303001c02c03c8a140b943c00b0881130440a209400500c215003607a4802010003010002d070a00c90086055102e01154414056a40040040760016079031056031400c02c0061400303403061104102d541a0303402e0b00003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 399000863 1250 398999613 398999617
    0x5100207260c10030b0618210c0d0204020c01290d1208091009030e01170105010c06020c07081204090605030c06221a040314030a050a080a0f05040602 66
    0x9038010098a000e185101c001091040520406080a502c08652034500b8030b01810303161249620360070002003401038000410400c0d0b22490111401d40c080e0031228002c1e080c603000c0302c400741e150104400388991010b42820f07212011502101d10602a104019040d5643c2c0d0b4119180c07400380784020840c0c61500c6800740080500022203070200c2c0740c40c40b1545c4460400040240540b40c4c014103480c8070b055485c0003500d000e18043c1c4401101e00c1034003001315800e0407074452426481e0203034850794501c1d5480b6000424031510500c024686510030741c010420390b6040000c1c0710280303600200150301c444580c00ca5500c2e003840e60740168003500c01e0408241d403003030744040100165106c2040500c00c49845130141941d515818400740c0e00030404102c2001c0f110805800d0071105c0c400c242c1c404040580d90b1103003003680b00501d40310051600001904000b04160a2400505591080061428003076410406000d030702503010402d0500800500090071200c40380d1002c031040298100801c40c500702400e0250080d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 399002113 1250 399000863 399000869
    0x2303180105010506040302150703090807090b2d1002030d060b030702100b0904030c0501090606093206120f06010914060d0209010312020703080711030606010516030e010905100207 79
    0xa546032000201e400d041102c12201941e801520300300c204c4069609240041c2e200401c04c0e0100034403194040340b003002c20b105907002080071020200e9914000c0003003100d208449500500d006c607115442e030b410079411500040b43c00782c003124840d5586c44218030903030951150401c040480c13460100c022403980312144c05140034000c9a0300f10b801c00c0e4130040d400411990307402c12440d40218050300150009208681e0000014411400460300c0c1c1100c1c2e4611060364060380005181544606100600000b869403d05025684040305052400301c1c2039540e0707580c40f02405460182d0303812070b8481d480c10010884289611031401c1115050360790703820480b009241c0c1c8201c1d81c102c0032284000c44e0f0303185407408006003001d40040504032103920310758810000d2540c004240c4107500405a0000c0460501d901900445026220029144401030201800c111005114605101042c807000990300c502c0000780c4129940350401500c00180c080c0141c1d070810b040d1344440c0d03100103101c01900300e00b5404130300c000813 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 399003363 1250 399002113 399002161
    0x20109051504030809060c09040b040b03030a02010605190f0909110a06090306050708070f030c021204060306050405010e09060a0c0207210303050708060303090402030408130b0c060c07122303 84
    0x41501d8401d600c03030302c0e540165814001032006100c82348003860554456030342118014000110481d140011030304682001c86210b0150b59944410081c50900ba8400ca80110080c0068590903007050207505008c01c25000340c09280e03a0740c1800c04200b02440d0074005404030028507a181040d5100d0004001d15024041181d400d404c18003c901c80501030603003036004100c5629054000c1400c01000c80c0100700e03050070901180301c3c01840459100241c4018009806540d40c041001410030042c04140d41e4180e210b031403403c1c0740c0c504200d800c04000c500150070240c0d84401040c42064203900701c1c60000d4a411103c0d00c2907d40c29510055120f0401d80301c50f0070720a4070b0601c42a42c541c201501d45800c01c8a0b91509600100048030f11850281d0045034403910031500c107400c0c01d01426040300078000c1038002c0c9a540d040010b4000c848001004a00e60100719203101520b07140c400d580b40c08440c1d5014208409008080e0800c2020a120281b80840000544044ca840341703041c0d001c0c003000046500342d1b0340d5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 399004613 1250 399003363 399003377
    0x30803150103020a140901022a1e010c020603090c090a050603011404020a1814010303031d07060504150309140319050c0a033504031704120f02010905150403 69
    0x9103075010340241c0304c1590003612000c1c0c0d211800391500403264041d610107811401944030106411644026400c07409140500460000045206100c617050031240a00c070852a0070740b04046582e448181810a15815a0416160f0b11043d107040e00d05041041c40c10340c48030181c01003218001030f5501c0503208801c00c50092200107580300c1490080d42e003c0e1307006504101840414001c07401001e0b00b58241155a142c0000c1c4058003000ca1103049070207030401c50009480704a641141e4680e10804030303d00c080e940140441d6481c1c000040c200348a075115540050360800c0e1002c421600903413007904c090307412001c41c0021201407040c203900e9a101121400c008407108e900315450b1807048013035840f1a480344008242420359034400791045580070007414503982070100c0c6030140d8058900544009079008500841c20b040030300d005802c0305100d2000b0340481c413115082202207050140b0703141703103050182498108031082080803805409520409441c0d0f2056611209103c0078000c2e0081c8201d00a5907000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 399005863 1250 399004613 399004651
    0x20108060904020904030807020a060911010206092e0f02130f08010204120f0f050f0a30180f08100f020c102f030609070e1c020a030b01030803 63
    0x80000070a40c0e02075000b00e0b06400140003c1d0003000740b142c009034140102d0703803503140c0f90b91050141c4101c1001114030300380303080c01004956010020b190700000103070041d05070505130080c440720110f20f191510f103086d190f0195900c601409540111031803c5a80c1080d0750303a004055840000c1c0901e48120000340405410008901006100707950030349081c404902020392440d01c0d0300c10308280c0f03807405035091401600d403c0000f0760108030050b00308042002030b10129031a07052000810310300e1505045882c0c84103c0c80f11000e0304a400c0c00008998504040e070704256607038811030491003144c00003650005030000c0401c100000003200541000818414003030800f02c50016805d0740140c9035032140a50000145da02400c945400c41b2103c07100c0103090b210104850b4001105428601255208150000040c80600c0c246031180c1a841061820100f040800040105400c5201004640e415009140c20501103545440105008641203c0b0000455031281031000c440c0d40203440024810095030004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 399007113 1250 399005863 399005869
    0x5040f080c19050d0201030e0c0303030f0403020f0601050901060c03020c060a020705120a08040512030c06160221033103090513051506030604090b04110a090e0c15040f09020702010806 81
    0x10075039201401ca0a480013040d40154064205800304050700d00070110740501a40703040000c1c501c141441070100b803003410242000380c02d1507292502c00c1100d800010040c0156126141c1035811101d051034507245200541c00c0c203c2c03c0458144845600500001e42c031b0500e2035000910301c042d1a01111500f0ba130441e8a51503d940e1842d08800400a050601007042180303046503141c81051031400c2540e16044810715150304100c01115221000140b80040e00c0445504000f410805820341e14030300032140201031020100d00000b00030080b21038180c0d10601b81620441c1c03d03c91181c0e040d9007070908800c414540504071814138041d590040640d40980580c829690107039501481d49100000c0b01c42d0780160a024075a440204065000758a40b64590000b6241c0301409100342d000301880e400150f452420045852031651003101002d0500042c1e245107000442e280410000450b51940d100c0120f290b02e1070349000b40e900c1088605003440c0c0009101c00340750010703d10f49200340da41c0703401d59481c0810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 399008363 1250 399007113 399007159
    0x7080907061805040c0c050d1d0607020108040b0703110d050a140103110d031704060c1103130e04020f06190318050c040f02040f030317060102030903150705040f080c 73
    0x402d42000780305030382c2000941015070000315140035520f00845080b43c0c0351941403074001d65205400c0010800141020b0014843c8c0910721002c00c2101c0b0075162039090780000b0306514010780080c0400800e4000318948034029406040000003440105032618074008150300100401c039050b100320f5003004003c1007841e00618055050700d61000341c03612400c218005010102602d05011000d104441a0b03403c1918400001c3c0d030300c50361180c440440d034541c41800092140c01000001503540d841880003481502c110901841903d1500301100f001e0341c1c03203000049900041c2200e46400020003c1c244403503400c80f4622a000607034a8a09020300b1958002e400940e138400c40015100790088407000c5294541504480400c1c00711401c0942810344640140100060541c0210007060346584200e03441205c2c1280741da880700090001e54140b06641d0003281d200c24440c11001810704042000414050180c1c06580c027504000d0700d8140341c2c07501c0c0d0704c00d50f59400b030740000c0900c40c445d448103c902040000b41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 399009613 1250 399008363 399008387
    0x1a0919030c15050717090313032a140904080702040203040f0b090604032001110a030c02150408040506070510060609080c090405250302060f070b0c070803011406070b0708090706 78
    0x34800369600c0a452030400c841c403018080c410310f03010030040170b00c54408181080018501455074100ac00042a450103130319000300c01503441d0358107020810803684510f444100100503042d6190245c0d9941c07442d086842d4464408000e61051011050001f80500c002c4c0342d11805104034034818841e00d0f09203c8a0340c840c1c0443c1e00400003405200b0021540c103034090740c0040b00041c480042030030290104600c0d00c80d08402240000280d8966950000b1a4100a08842e04040112400160070643c8074900c080c0b0407401050b0192600017007250410504120a62071815206070402045844000c01040f4010511403010030b4031130080380016501c3c100030618096940314009200c41c50000b100b100c000340707143c03205c00030005007400004096200c0c1c070018031a59604208491346c611003031400054040024140b0500c2c0e5006101140009010364100c0381903c0b40c085003000041000c50001f800c610590078004c2000160000b4400c0701d40d040ba50890064601000703907003801c0d4642034103d42c051040c007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 399010863 1250 399009613 399009617
    0x7080408030705090118270605100c020118090218061201050103110c03071407120506060d0807080c0a02030d03020c1903020a200f09041a0919030c150507 68
    0x70210b1480c1d40110300602c0c60500c107040c0702d903640791605001003002c01c0d29841001e6490700c600384400c84a900060f0100000d0741c0c035004000450030a0049501c0c44031042c0d5100501049409907000c0d68003d40b0700100c0c032544040040f042030340790005100030b50008001403001d002201640c43c4d06190040a84003076418003034015006030b2914004402901003219001014501041004407140d018001042003600920241030306080b010401c07850000b440d8880f030034a503029a4a28002580400e80d0745d0130980031100000300d460306060020030752154040040280c60700144200c1c00a08c00f240302c10340c1600803030a49102500481d0140d00341d100344180c8070030641216103000b14282d0b14010a5044c980a8411501d00c14060740c1c0c2d0740c280d503040d1407035072802da502c200900410f45807a03064111418030507100d4070694185a0f841f4000581106507407000c01d0b16140016210050030086e100b85814071064011100110381400b070080e0412800507540c06044030501504404e841c01500d00803402c90b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 399012113 1250 399010863 399010867
    0x21c050a0c02090a0e0a0f0b1305060106050903010b060a0809010623010302030a112d0435010204140f0f0d0807060f0908030a0c0305100b1303020402030403110607080408 75
    0x15803c22100d440c000340f41501aa43d00c00c025090500f08220303400f2102d10928140f45031800c01e00b801201002d0040801000449000d1340300d00084020916a045600130309003aa201c034807400001c2d014111145180744c01c400c001c0b07500328100e40d01c440c60f5401b4940390b60007041000e4a600442020342c042401203240d580184179150960b5200e940155404003441000003011221881400740a62016914984030b0b454050424010a4400c1c1d45044d40304568100b07500d4545000d40000e40c904844440305020804003560306224004902711040c03042074880210f40e5207844442290f92000081c2c01c03280907c440c1e11085000e414480c01c8070392405001400d80c400c42c88503075900103450b808207108a171a6a1260700d48403900b0f00500800030180d20640b2050b44a29140040104a0f00240c2005081606000134440305142030040c12007036607505000c0c10703030300c243c2c2d0305c5110914041944000c0d00319100200300014940d0100350000710120050a039001916204805c854500f000d4602400f84001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 399013363 1250 399012113 399012137
    0xf030902101101091b03141c030515030d03051005030708060105040b0d05010608010501090b03190809012606010e010207150818100b0405100303020c1509090106021c050a 75
    0x79003464102c2c0c404540c008100744000790b46110a03903081d51101042e065200005104110b101890182e1100b8800d005202491113841c054030040711100c0c0035018165258086014007010708002000e40c4006003c88140c101958001401030804071900e908485d480d10001c00d1516010540798100c41404005003040d9080c542004010304c200b041c510350100c148200d42d00002d50070f002d544011f20300301c4000142503261140e804180c503003d0003110700c0394021100204025200420580313841c2d8128500d0354407160b50340d006a40c00400a0f41c038001600c214548050341d88261644244680001e0b80d4190711403800c10016641c440460250306d034100342c1c441c03088002ca40b04410b481c0d4001e00c91103002e5040100c4105660410f40b46030540c1e03a1107034540e4601d03107880c10a40141500002c07012003100c00f052458400075111211400c026202e050041162035074002010f0549658440040110300a541e5400e40039580b070340507040400c0815840030a480100d40900241d8a2050b213980714000c00e003071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 399014613 1250 399013363 399013367
    0x2010b0f01120e24010807050105030c0a030f020c0106090501180203090d1803020a0909060e030405030d11100507082d011503060f0b09090109180b091513030f03090210 74
    0xf40c0b594845520b11500440744d41c00600e03844500307090b5421403483c03001d650501407450b050401c0c60308841e040c48020401c2c410403000e02c0044820700605450006002144034040c03002030f208412002d14030390700f031042c0410a45999030115049030051000c1c46825451030290b01e0590004440d44805030f00034444699050340a0504a28545030802c0d0310001c00b600c1e6400182e68180d00d40040c201e2503910315901c030800440348102c1e0b180001c04402503041614000000303585071903003030002c4100900d2103c0450006410003420300e0f8402c902105004524107090700074034200301160700d01614078003046521001d01030030340040000b0a01c01d000c000751340c0c01c1003d00b038805440100b696042540e40c6200007580c503141054080a0440590510f583d803042404200705c281040c0c01084d600d40c43d10003405105a1400c44010032507a000004490a40c2c032162058100b045450111060b81002c0c410072081c10081e00e07031400c007280701b81c4038040c40c00d01d140707421821100d134038a000703401507005081500c1143c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 399015863 1250 399014613 399014621
    0x909060d060e2a010e15090406030309290306040216080f07031b020306070c02060d11090a0b03090c19030503040305060a0c0e0906120c1f02071d010902030402060c06040b01030302010b0f0112 84
    0x42d0303800c50342d1f498a05030001007011500c82d50310540000d0b00c0e06d9400c0c402162813110251012034404450305407410b10030b000700c030309200c0a40414851603000880c54000031205980a0041b40c01403801d40e1100c00d540c010503042e5019080031400190840351b1003490b00a18a500540d4070780103002402c040c1d44058058031017034a1030740181d80c00141032011640090300743c01194168515003000a440d41045403e2201088050300a02c2858009000b0071101d48400135000b18060400c8a103240d4080200c80c0008440c08181c0000d403080c000014040240711002403d14081d100100c1d042100700d040c10000c50f6100501e98856034040444030100d2800c1ca0101161071030000b080090720403146081002071411260342441290070540049268601c2d60184007840050501d101d141c0803031920240164580c4405004800802da4080301050070740d2650000d986c030048000d4216690707428103062241c0380f10000d11040f8015070a0942c25202400c01c6010748411000685507400ca0605034204134001d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 399017113 1250 399015863 399015889
    0x6060b0901080105120d0807140a11190b0a0c03020408150601200a12021614150c0703080f0d390e210d080702010c020102040b0909060d060e2a010e 65
    0x214030b074000c000080c40268003c20380684151160392f02403a10192450928803004a05090841c0607050f420105038540f03581503202e642d4080000e1030458145080e0000d0203190083c0129104600e100540340d078403003d526001d100c003600c48100d840c1d00142d04540c203100002030300d032a40c0c00c82d0704a5000174800d200c5281e202c0019005440303031800403408010200d401380d401078480c0c640d071200c83c0d0301c5c600301100e0562b00303001c40c0b000091030a141c1800e919a110076600c4000c2c00131100082d010170203044501640c4c4114a102024080c060403911800803403845c00c001c050488404030b14065240f20040c030a580001600d40f0b6150368448100100642c1000d084600c5040080b08100b002d070103e0184034504005801c0d4480070610308248400030300b11100d5141840075a03204001c140118545d440a888546100721074010180c0d54003408603642c3c40dd003a000520305401d180500540e20404030744440803500076002c407a030544400c621108a2203190102d5400315400c0014090700c1d04103041e00e4409 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 399018363 1250 399017113 399017117
    0xb06090d0f02040f020702040e0a03140703090f270915180f0605100e01030305030414010209040525030b060301090b150307020c041a03070e0601020a06060b0901080105120d0807 78
    0x3840d680da030003003000e841035428042d044645c0029858111701d083d1040c0903554043c40000c0c11141d03e01e54020785100e2000307540403000c8002080700020588030300e1340c00001e0620407264601007039442d01f1a4170000ba00d1100381e42c0030000d01a4607a0403001034071500d9089038000888002c00d5402488510080009100d010203040b03150381c000380462004801402154407807900043c2d10306e481203500360b010a00e0f80048082c007086900401c003099000040c0d0350041d41040e401801c001c84040f01500a00c146401d641e0403c0c146410040600d444e0000328031301c81010300c261030740002070340822422581c81c08803490b4003810500060100800a071302440c0300b89406003803a0700d000072171b405034003070703504101d51030343c0164065480c03011039040c03501481c000f401441e40144446412070000030348a91150040c8240c642c400380000d04107a01c00c00c104903103983c000d81c080007415101d0014030204d03400b42420398045200600001450700b0300c400020104494080500b1080101d0201101ca5000c05450502 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 399019613 1250 399018363 399018383
    0x213020307171512030301030201031503151119110f070e0412090b071415060904060b03160909050c06040602070e15060d02030907090e030a21020406020d0905040b06090d 75
    0x401d80700c084d042c20125034a035000b161079614520004003610592020b0b1801303844441d44c10800101418800d61111400d48000703d0b003202220f1440b9043e002d100080458181540b507c0c600f01a0048000d040d0488600103817504601103501c1c03650b80e1034142c81141f2404942d04000b0b0041a4004030b0316104044510303240801c0c075901c40780e0200c2038000c0c0509480e1140890f58003080028108404005c40021100f00c0d08145040c00014505000007031001c1e00d00c40d101d400d0110155002d00641c8107412400740f0b0000310036110880c41c2c00070500b2000071900c1380f180350358541a0749007080688085800a9006010340b0781410711001c03500402a100603000c1e0b02d200c00c81c1402d81d0f660806000c5594001c50016228688241c49500d00403269000000c4103181030003660706904040100c030042d000c1c0e811300f090b41c01d0400d10a41c0d400c1d141c200010303200c00d10201c0d0110740e41c0d6000c644904c1034906070351900030864030b81e01007000301c3e03001c403040c00e60100042100055609107021514030440c01a54509 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 399020863 1250 399019613 399019651
    0x1051503061f090602070e01051e0307030b07030c09081b15090d1a0a0506060d0218030d0804020909150a0b04020d0c0f27030602070f140703021302030717 68
    0x80e10300082c004180c0c042043c18400344442a4108040e00080104c883d45078641d515080c0440c0c00303003c0004c802c41282c0c224500442c081e071410040e81d03004580c042c1e54070146250559008004104904c48070700090b0ba003040004422100140d050b81d04441c1c000e000082c0c010b0402000040000d40300402c1b034819050040542941c0c9035030082c0c01007401340c2004a02c4892074031038072000090040c030f0940610b241c2000e201894881005451801025080040c1e55160345000350b141c1c80c01240d10b440c0d00d40311303100a5055a07a4800b180340c1c0594400d0368003040d2515002c0f807079500c4520701d09a400518400d9800108400340a80261503d0400034000518140400030303c1016900486401408108800f0301070002a074091000c000c85200c0c039000c03016a000c1c03034540d45800e84103444068a800d0300856170009004280d406078149a50081c5020396504100b00c0142c0c031210503110603403084420030b07041000041d19000f1a03210b01016a203180084144044c0c0c8510000c0181603020101000c01d010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 399022113 1250 399020863 399020899
    0x20a08070e04030f050c2e050c1803070303050d05040c05061306080604091e05120301030c05011209031e0e0a0e011a09010504150509130b0312030105150306 69
    0x380d006801400360700c1900b4502810003030b18285240060703404008041000004411000c00c0d9802d15285a800c689058114848403c401244950b1140c0026261006001d0316110b81c80003018900100394824010b031700310b44201900c03805648000f0300450002c01c40480300c0080d03503120541c840e1040400c0c1702c400ba156170108007240c106191044e408502c4000c140310070b6402c00c2d01c030f07544100d0454050152515694681c2334030b0404018007079904241c00c1c1c01504016042c0309200365241e15028403031326907a4034100503d26041c0c41c4104c81c040f82410408440c19030850296007901501903c521039030304450b941d82c13480c5406a05c2d241042012101c40500c069035280340c1c50004141000c0400203550400402c0c00010040d5041e02c044131f28101b0600d01141d0b0031006550480340030b1034514107010300702d440986a500c2104000c0e50300949003048000d4078859030b8010090210281c04551403000880610079442c4402c1c0500b81d1700800600d01c2e41201c91885004542c400c03c041c1c80300407004405005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 399023363 1250 399022113 399022123
    0xc151d04022803050105041a040504050304080a0804140907090b180402190306080a03080127020a0504081501140f012c0907030507090911120405010c030e0601050a0b07020a08 77
    0x200d040c010b01880049410365070b040c05840d0140404440800581c48440d40d1491700801e0818410b011b180c40390001000e100c03050007610000c09401099600355244e42c45e108545900c02c1c007895402141a051801250078000c0cc0281308907442d4030b811800a050025050f180c0e04800520009900b0030304917203890361224005818590b500e00b2030262281c20708080a0f0a48000750025041f9900040713584005c84e500000003411518034500807906e0b44800c0000e0040c1c1d400c45800e510002c0d00028a41843c40d910500800480b1095029640322200e2003c11601c580402e00c1850816140c1c140100490703c2d280da9210001f400504201200040c20414009403004488c079031200604180e00029650414180c1c49511039298602040589090078000d400e051950080400c41783d0396007450180750300c0d160100d500c28403540b10908003c0c5058a040d5001c0d00346100e00310b0003e400c202c1c4900d4409000203910303044c3c0320001c0a505c50a42440303050340080d0020002640e001891400009040809010b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 399024613 1250 399023363 399023407
    0x30c0213150f060212030c03130f080d06060e0a06120902090109090303050c0a05071704090222050f010e0402032203080a1a010f0f02120c0a0c151d0402 67
    0x7034900703581e4a025252010402c0c01c0d440ba9081d904520440101c00502c00101d0b0342c04140803d0705a00c2c0e490b0350160fa29007000d22a0001d000d440b1500704030051142031b0303028080000358030f403082c007945407102c0c03048070300f500543c45080d082810710000f0300215000300780d0708410380c0c442c0000164051f41ca40014050240a0344202c1e007450340c400360402415890f018281e402420312034030500d4121026402002c1d4071400f0320151035041e40203141c00e040e8499a08940003041c5a19055454001401d0700d4542c0c031481e0343d074691b02420998400945401c0c151494034414074144c50302c48001c04404180400703540010300110203450300d418007094403818090400321181c025968002946424000700d0215141848a0300e00302c403103403503000c0940e0f0784184040d240010501c3c001410031054030060b46000b403024840349030380d1004240e480707910034001141c0d82c002d070144642140711541c1d61302901f109185003504070b0010f80d02e4070100c990101000780700410400003800c014507210748034050782003841c05a8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 399025863 1250 399024613 399024641
    0x5041b1701141b03040309090e0102090108010e0603150a110403052a0604170109120e1503090312090c180a14010f060c020f1f0f09050607030c0213 65
    0x154020066440c24822440140d07107268030b540d114203144540c0e03c0b00c030903030a16407440d01c0c0001000508147c8074001000003841844400c0c0000d440d107840c1d0501030b40100801074001040c12000088066111501c9401540702078051703d81e01e20350007200c0303074140030041c52004600d41300c0b03000a5132900f06100400045006401402c401c004400070041044021140c1c2140da0a1441c00e0505070356852084400b240d810a0340c1d03030030300d2904aa0036400350100f00c5002d4101e1601c10703031003040b90760410301996080c41c00b110888444004901c4503c078030700040da01028140d01c140b280206a020f6084513540045410040714012030b041000155000a0f602640d14000c443c0c400b400030040310b500480b10240f0228400f06a550304240c0b005144e041c6a100c1c910402180602c00002e540303030104200101a0041c1c04900f003c20702850107034941781c1040c0c01c4d40c002603903030f07003480c40031446071072140155040204001d00d40005514100e82c8401c40070401e0364032402070a00360000714994418880000001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 399027113 1250 399025863 399025889
    0x102010e07060801080f060103021005031302040615020c19060e060c060423010e0c01031505060408011a0d0314090111060703060510030902090a05090a14160909031205041b 76
    0x30013003c60500b06c8082c40c20f90154080e00061005a07942c8800c0c401c1101c0c24a0711580300c1d92440441ea03088030f65590040d4010f850701c040801c214443c10314051010950fa022249a15400c00500803040c200c0c881d0980011440700c000d220540c450b56400910b01001051300e03013412140309000f420720005a0302202c038048003040700d940c1c440301e01c00800418074180c4020030203843e28203142c903166101003141707038109965903120141c3c1189058086c005481d029007516210342c1c581419034024030b030380c0004540c0c1881e1605203420520302222001043d9515a0300c1c0b0001d58048484889030340c204140e441c1c1841070b0400b4a60034003004011142c410b04050b5030200c2c1721454103081c003803510081c0d00c4020030181404002b0b000745c0c47c1d10401640040032244009900c0d80c60a0b040e600b0a050400b004010300e6942c0c1c0300c1507402000140544591000718640e2b490315684a40f588210b415101e002404540c035484408904d10441d48455070050090440d030401c0144004d00c10595140d41d0851940324600c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 399028363 1250 399027113 399027119
    0xe030a08010e06010809100c05040909051b0f0303180114030718150f1b050604030c0606090c0c0209040c0306050c07150e12130902040e0103120221090102010e07060801 74
    0x40d451542d5040042030a021500b07007880e0b6046c640300d00014030328900881c1c03a14004802507108034100c0d002010545000c10401243d850320b40e03120b000b001c000e40c00440d04206030310550310700081d00d5032407840024025440d020041484002450461a009050001c03070303a24403203880601c000451148c1c440b950340510b05070034202c3c040d4410302660492500ca0100004844070150040059884403003075041aa00350080341050b4401c81c1d540c0500140140101c1040c03000701900110b2007500030384207640034401c0f5a2640e60807030840d200200c640e030004058010610240c1860100325801c03d004444114810751a502d13414182c40003914030700e142d08800a0300b00f0510030005c0400ca081c00c1c000030107110381113503d04001d40d02c0c4004102d0f074504171000240800c008102c20a0a0006d001c13192056484030360310842c0d000311030424070040e41c03c1d401c001e0034103050074030105007204101d061260700b40c07004010141629941e0020a0418150365131120702c04940380040210740010301ea2561050181d40c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 399029613 1250 399028363 399028379
    0xa21140105090703090507170c10030b0a06050906030412030b0307081e03120609100e0106031a0102030910050d0b120f010b0307080c01080c04050d060b040506060f0301031103010e030a0801 83
    0x60020300392400c041c544218107000441c042007d4080303800740c0e405220310380c00030044d05052442420a0580c8041103901103041305406130411024442c00f2500e4424260b40c5000c103440a100302d50100f0340c081ca040000070001225642400180d410600d07001072800006c6011030302d0b121140c0c001001c56441718040d808004003242612107400d144a01540c20620302280451a416000d020700f44035403072440c0018859040c407038103500100ba0038030348100f8650707403600041c00502440111039001d0070001c5081c07200e540008120380b14560040e00e510080711044008079155009100343e507150036140c542070505507440500b0640814502e101400d20480c04821079402c494070b201080e03000350002c24041240c4900841c0000e10180e0a00700120070350b40b80040540c01d4071464210300e0f440f28681010409000031640000740b080c0013902d08010545805c010040ca40c01080003501460004000500000380210b13204c0d442c00b01c0182c0007141c6e8002a41605046400049080c000246009c0c01084004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 399030863 1250 399029613 399029629
    0x1d19050406051903080711031c080a091104090519080904050906040c06030c260601031406030d0e0604121b050f1509012f100b01050a21140105 63
    0x70800700d60004041140703c841c880e02c01c2c01484090b1900c000452060240310340814009407001c3c0080c152840c042040365411040740503030001c3e07000594890001400300c03c140c4903081c41944c2110225502c220600200006080603410840c1c142c01040c00c054001e4030b40c0c40e0040306143c030403040540c64804c807105000494400074402c0c056680301e80244800304001401c140150b41c40f600d80444c401552803000e49034240310307c1d4140c0343c1a201010728a09215061296402030209a82c03d000c0503600c100164075416007900c3e17682d4190800d607002c0d00403d000702042d10030640040d2080703003801d07a40d030f1148400c80b45c0741e941030b549075141c00901552403003048810006880301f100c01080c092410070100344088081010802c0b5050002001c0f0526030242195039000d41c02450345810f0014126a87c6c2141c000d0116129050b109100901c1625960350013200c010703001c103070343d81424103800d240110349400f0100803840380100c0742d00312014041c481c0d000e80da1504540500e1001c0551400741480300d51 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 399032113 1250 399030863 399030869
    0x5010821040f03020607030c05070902030702010e070312120f0f0c0f02030408030d02030910110c0c010e0904121b0c051005091806040f0f0e010b10020d1d19050406 72
    0x150000304400d20180c400040c80900f5250107403811354580b0418a0b00341c800d01c84001c03000d4079034840e40c000025068007035001180300c2e40480c0d00a00545000c6500b00d6034030000c60000400e040706042c03401450500c04c14803142440c03003065010901c0c49051800c0c004494103001030818844e02c80d090b243c0350700e030004d00211803140c5a20007185414540b40c80e4903207034047e07591078480140e0008082014403c2c1000380d50000301d03400b2002c00801d000c80701d201c4101e40c84a41c10300c08a00035440514540e40c0503042440542c60042c20b2281c1c2580c5075651524801810040031050103008102d510b1410741300310012142912903044a00011f05100400081d404001c0d1110104001000045c0e020384400700140781403011031001c000c0e29140d400000300942690038038180440d04d00700c00d541c84a4a260441185010803000801c0011040d03403d0090301c1500071080d1016a0003114001c0d60680f05041c0c3c07000600c910460071084c164448001406c80c658015621551341c00c1a0050046181500c550302c01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 399033363 1250 399032113 399032173
    0x50637060c0c05011b020301020d050402270a0e07080d17010b030105060a0c1103010f02030f0901050417280518031c050708070b040b040606050103020f07140f01050108 74
    0x81c100c00c0d90301c41250210b5402098100440350140760910403110521454159004000b90340302c0d89080d04c1c103401071908481c103034800c41140304010f041c600c4440e10351700404a4820490001d6407050b48a202a0040b0340000d01148185a0000740140c0103010101903290300c1c1e901c8070701e160001c550b9000c0790f40741a044030104541c10001001103540f20012103244c0340c5142000f144030001802c040081d05030741c614054041d401c00e03c0010150500d41c0c021071085140c500b9100313141d120070030464200c030801c80300208480000c55038400300c160f28601170b1801a0107105a0f40c1c21000c1d5040c0703001e00120100074000072407408640084c840358010009a1403035410340050005810214240c1c00460306181d103c0c0130310500054042c148000c100c2200c00c0c00303030090758019150501e450304200360601103500396110744c60081c0108080d0f1080c000c4954a00c0025146420191240c41c2c40c00c03c1c150187c1c40000360710400700b115080d10b10a005540c02080c0f1680942100088450b00c1c2c03090b00c2e2080da107005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 399034613 1250 399033363 399033377
    0xe18120c0f030301061e1403010801020424020a080f0721030e0d0f03020f0c01060308070209070207032001020309031f0b060712081b040f140d0203060a05063706 71
    0x2008980c0704206c001040f032480c3d0038000e6003c5541056490420280c010b1300406400000498003490540041c03003210008540303c10806d042c400d0030399180440c43d1101005030801000c840c086910300001e4410040c00c24a01d510748070307099407041c84644454164000042c085036000c002240c1521034407054011034400349c02c06640c107c40c020a040305000f0300310305241d03001ca80d101c815008a002c2e0703010618840001c1040603100c4c10000190340203640201c2c0b090340c000001803409440860000c084070350062118200303c05c0001c00d1441220409110b5046100c10700c10901140d4080010343c2c421010540c0300001c28030104401010f5034200000c07240a95020008680005d0007082e0348910542d040c9041244e0761076a02060301c801040c2030005600800c00705001c244100c810865100302c03882e1a100101a034003000510100d02c81d0031301d020350f05410900014104000541015900100c010072400e1070003245a802d0754181c1140365210032181c1d100c00e404003500310390514400074091a0400071703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 399035863 1250 399034613 399034619
    0x207050f250e0609040213091e0623041203140708040c12050312180303041406070e1305090723090601030e0a0611040b070b09011a06040e18120c0f030301 68
    0x44c40d0000007a00c024001c103025483d034600180240e102c0e015181e0300c801865180768003071128040c021204002641c807280303009070516401d005402412448001e1803c01007070782e40c032910740e4221040100403c506154965601c0f8a41810507502c00d8410071194580d1030311410b041c1070814250b000e9410103806c40c800d06287e40007180d400000e41c5e8510640418105050b603e10450104172400c0308080d8400388404030600003080501ca10030190103248908540d0030b40c1e1600c10450b00303000b005103070640106100994130420407003a000751354045003610032902e041c0d0361143d1021605101c0309201a0700c0090700380b42c1003a8030307040c002c0d0750300042c007464203000d0102003d14040e220545e4103801020255900c001070071000c80303003080e5001400c1d6446000d81328401c41c2801e004041c1c00311032403580d9521b401c1c55080110000c8004004200020f000d15081c1810700940c0003ea11002e0300a4000c05c07816156521070f82e4003000710302c00310b041d0785414545441d00d0b1101c203031601d02c001d02490305a0700244018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 399037113 1250 399035863 399035869
    0x20d0c030612021507080f0a0e030a0c0302040504110907021b0f0906120a12050c150403270b07080705070b04081506040b0907030c11011a040207050f250e06 69
    0x340150f01215981513040c40085014010320030113200070550700b00400c54100390782c1c5150140040601f55110f01c410102500c081544560030300034003c001140303601e03088c405404c0c01d900181c1c3c040c1c031503843d01410724001c4001944208085945500607032100325007034181250368022001c4641c09032100503860692800040540e44020b02c510302030302c1102354640d440801000f09100181c1c02020004c051649004010020f41c440c0c041c5903014400c1d03a41c0e0b01410300c041c80600741700d0742c0c05070307101d4200b4280007200101442104003c2001d6040c0d182021454900c10f02c0108003e034410401c2d9507403420b0030301d081070400f5540e510900b04840140401c0100d40c501240805015010307802940e166994440040c0040403245240790300801c4c0d10080116803500341e80903d68400141d11070b0344604442c14501800c1e60b00900000002d0740d5030038030348017440c20250040c052841c0300d030050b241051084419245004447c100b140501c0c071600910005ca2202d407a8240302a218101845d06603203000b4002c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 399038363 1250 399037113 399037139
    0x27050606130e060601030b1c03030204240c0305130503070905091903090909021c0b04030306090207030504031101050903030c0705010f1e08220302010902030c0a080604030e0301140a020d0c0306 85
    0x5194141a1247d9604120341c0d00c00000c0010054443d1201c0c3c030000740c50034014029005801421106c0c1c5078982c1264600c5071220005508001d01d41d100c03070910700390340e03001c807030b10b4104140901c1400c02d48840070500b03030303414415180540710240c400107451810001140c83c00f03c5501c40449088060054200401e900951602c15100390b0000412100e16074808100c0500100100c41035600103001c01104124a041006000300c0c06960180511600c032940760301248168040103001c00e104000c1000028205003d05d03e88a405040c0981400401400319085500142c40380035907401c0035009110a60300480702c80d10821562400c504500a2303a505451991041c5e41d0110500c40c016000400f10071007203800c1c1000368070f030320b50b00a118216032a000e8007170103008400320712900030710212f605542019000030084600c0d46004003820740301c0e61000e5074450a00d44440ea095522200585000b8941e000514019a512000140d540882c0d0311607008a41c40c0104802c2098100341007000307070349031002e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 399039613 1250 399038363 399038371
    0x40c05010e060d05090c060c0d0806090c0d0e19050a060c0905010917070503030a0906080f090703020904110415031b29040905040303020a080c0a0f0327050606130e06 73
    0x50000b1541c0700e05d18000d00c4c064a5002e034603401030000510012081010400106600a607220300707001e612200100403090404842d005a401403e00041101907496005a2221110300042d2460380417140246104490aa0b405580941c007004602d4200449441100101e9200c0c0c03426901c82400c0c04c0008003281110310655030580c0482913003403c2c529061002c4401450700404813030f07442c1d00c1510003900381d40d0148500004294014001030145608402c0035215a003030300090078009080d0b50030000310f071034068030690706048a1400204c1c1c1d034540340b1484c11480320350302c3d201074214514507000e40303500e0201c1c2c0e50004c0401946420000e124a0b195421788003905000340c500c500b100400a055940100d40c4003840382401c20090000b4540c040d0b000301b40108095031103405550740c44820840c079120f082c01a00000d03041100c840840c038400d5100c1a21120f030703246c9103d001c0b003c50384900e032104007410381554070307412100921001d850080c844801e0000284420b01c110b2a10b44002619400010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 399040863 1250 399039613 399039637
    0xf0a02031e1603060602010b061210090e0c1f0207050f011101050406020c0c01090305070303031a040903030f0513030207050f0a0e01090f06050105070519020f0a0303020303040c05010e06 82
    0xc80407540148040020701c10380307034011075a4605441c004848400d01d002107224800032074502100031850342c0c4180a079602d48070010b040f0350b203480007050340c102d140c010003070a40060070310308140401c0703400c1c003400b5903d45202846c0092180c41c82d042e00300a545503048200f2062888210340400120b07170081107500c02c07100b00300d403480500301d010320050300c02444040c003a008552034582000200070b540c5d4090100c0040e04411140c1e500c0040f001500c0c1c00c2024000a0050f5100390801c1001030b2107504000314000291510780c409200c00070125096a80c04082103011903107400c03000d07083c00864402c00358000d07203010b0b0b100d210350300d01d4901039140c982600038140110640c203440a0304d41c03907a40d69003008105a0310300300855a503030b0a00ca001040b10200c0c0308402c9080c4a400165584100150342c01d0070380000207028842604409001919148841203810036440e035016446684d48503459130040d402038000d50780c1c0749130a1404079804034254102c181840f96220441c003c540b070707540c191200c4203000d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 399042113 1250 399040863 399040867
    0x16060824030304080f06010312020a02060d05130204180b0726060f062106030a1e051c0e010306051813151107030f09320d0303230f0a02 60
    0x40c000c24214481c94010003454030407444214100d0f403000038000d04030381c0589103029981030410030498a0320111413004e035011030180081560385509901503500128002e0050000403410b501240035201d15110540d40c013000c4818660500c140c40001a40c819450318181c4000c9005107030283c1000504d24100c4043d02e0004006901c544808040c0d0b800e04000500c0c131074075910324440c0c0284042d403a01240c04000d81500104615007000103020700c08070b0340002c1c421420805070205808420b460441903800303115805401680b00012603c40400d01d4096440003e488d0190001400b0713100c140e402540120803080e00c0d41c860030069410541c000d51510740041c1650041d04280520601140c00d00a689103407841c15004410904001c0c0356162007501c41d02800920900d00f039030f1910607032140e002c10510414002101c22081d55400581e14140e031030380508040088045201041c20b0501280400d0351505005601c0f2480300790381c13052401c41c0b401140c0d64501004141c0140034054450003040b900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 399043363 1250 399042113 399042181
    0xa08281d0406030f05031e03150d03051b071a071203050403051e0901030e0607020a14100501290a1209020f0306071706151207051605160608 62
    0x1d1500311000554100002d040303d25490b00b0729507104e901034943d508001404010708144982c10006a07032240c0f00d800350300580c0214142c20700403030034402d80089042003020041d013220120030581a0000172540d074000c080160405204440852030310200820f0000e06001c1e100001d00d030340c8514101008589408109034645280c2503400c0d001d44001d000f03000556003170300d1481800320009404030f0103003640c050118030104540e0b182c48003419540c50300160401d00b51034011030303024889107606807501000c8a0f840c03007400e0100000c41d6820703044900c44281008601205242c1000600803100d624800d00e86010107e00d00601003203501a00c05030580e8880700d1580075940c1d00d9410301910703040070b01a5481840c200c080285111000c0001c40e01c02c00c45107010074203d040244050481440301c40e030032481d1108041a000301640700500490411008100c040d20143d2800d802050040c812001450f00119200030304d920140c043c2c00000401c9416804c00824a03030b03180e030700e2600000d0098010600d180c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 399044613 1250 399043363 399043369
    0x30708250302100c03020c010c0b04020d050309040c09030b010f15080903040f080607110607090e09010b040608070e010e06010c12020a06150504060b0c0d050a110a08281d 75
    0x805900107503100a00f0000c500400c4e801800840d0000c0c401d5003520000d4a2180055540c4003280300f0140241c145140080c0040c20310541d144d0500340140c040780c0c00e00d101071002a040d0345d1404011400903107003000c1001008008d40126016044120102203403070305042050107079410a210810800104101040c04404e040c01154003524984151190075510340220301e90340c01041c0d88600000b8694606c84101c0760340491514007802131035503040315162504814513070849025100350303555503940e40181d40f1075845100362001020040c01074400186171044088002d1f8050380083c0840542400b0040c441e079000e0230b001001544114410340c0d103e0700c102c040780f404010076030081019107003d0800c000020094030043c1140c804031403e1015a445610b45c0030a0b000d10200c3c0d00c01c5034401070011a03001d0281001d05504004ca01c5c2139202c4800702c0c05036925201203c1d4041c0c490301c0300094800441030148510b44454a803841030140710030b00f001b0000f00302d0620525030011212003240c44c0c40030b40da = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 399045863 1250 399044613 399044683
    0x90603130809030a061d120307030914030a030603021e030c1c0b0c0409060f0302030d0309051002040b0d0506100e120f03190822020925030c020c030708 67
    0x80301c00f4003182d1840031a49440700c001c00310304030700d03031310b094042a12031401c1600020a522003502c00341c011419074544840540240031051003c072154502d41141082c0d05c0c80403c090660303050681d80201e8910700c0c3d4014000c540fa12045a20b81c5030202006400040d180001e5512034088180c41c0300500740b0b0114082000554800e000a18240c81ca4060046a000c8a0007030800e03508050803c21055a50b50070200345080913100080d00f41d0407000c2c444648a0080e403128110341e001c1c400340c4bc012500300403205d04176409504606460308002caa144800840c0d44125a8040020398201c65003151090700648082070a240c0c1602c139001518150402c11000c0c001404900c0414044a4651244481c110690440d5807082e030001481e880005111003450032650b40b91804c402c001d00c0c6801003a0702844001b600040c08503c01150a021840c05603181440c619103000c1e6691b000250001c4481009040424000e20b02d07100e44d024500600521001049614424150300c510742c42030542c1c0c0315042941 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 399047113 1250 399045863 399045877
    0x503040b07060b030d02060906160e1009081005220206031305031314030f1c0c020402090d150f020a050a0c0c030b0c07060c030c09060e01021e0c04050603030906031308 74
    0x10b00401c5d407921422500001e0f00d0380189104010355141e0b90700d000c440700b54500000f11000020745034828a55a90074840d011505a041a02d0201c200e551181009807034000e10303c000d21100d070745e203000300550002c0804030f041c0c44130240c0c8001c0b084080301e500082c40600009c0c108205407100c0d20841c41c2001410001c0700e45001c20f140c0d00c02106079403520b400060706078009201d8040d000b044c09003007e45201041042c01003000d02540c40c0c140c0f4043d6811102c01c00002c0b000c0360080da0070010401c041c0c1d20032078500c040511501c01440d501c2c43d407003009010794480c40342e02c112650061081480c080e4104c4250380645015180010990007a400d100c0c030030700d40560020308060300c40c1d803d0104c540356200040004601415092002c9502400e003107084554401c541d00001c0c0c0d8820040c040c0c1c6205100724440005c0520484080c88941c2e140c15000d00400312041d5242d504c0740c6030f83c03141030500e40102a03120404801550900c000c0e1400305400c2d12005181c1d502c4100107076030440070040a20203584030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 399048363 1250 399047113 399047119
    0x5040e010f0f05040c0b0c070305010f09140c031b0a0509040b071d01050306150d1b230f0a1b030302030a05011203020a03030b040603060e030306100c0503040b07060b 73
    0x1090904215160091004510304140c01d8101100c4941c85001405501c0c00b1301c2e4001d01c40a403480c074041d01c500d16900b0188501c030b6030780243c0710b001003c078000f4002ca4554000340c180019005420307280c000c00c400b0220160781d2580d044403608283c26500460205030202201100300c07406020500062200b90007904800ea01850310428030091201da0104c0e00c0c0709940030f480f1880c0c0d002882c01c0c035885001c03054a0b1180043c1c3c04000190785030906080c60b203042d40c29001c0813403d02103035122000c00c4e20b94903030b440300392a483c07800c25101c42030307012484911819101c840801c0302a4020340700c6850744a030b1440e0841115000402131040740c414280014200995501c40340c00313018038035000740654420b841c01e513001403d0400105545c1c50041c81c03105842d506400404600b440d55809801502e543c5001c141c0c402d0744e23a44000085042d034022028034103240c030040d40c0d80e450300d10204400a51020411010000e9a207821800108000201c03021303071f0f1000c980c0ca5141c02e00d0303141c108040c242000415030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 399049613 1250 399048363 399048371
    0x90c180905101505060313170c011d251a090316090507030e101d03070602120c090612090705040f0b0a0e060d020f0d0b010806180a21090504 62
    0x2698442c1030380884005002c02d08040384442e601c00400055010940358819045040e1000f440050a091901c800d502480c41e0b099040459400a0508503040002c42040044070f000006000c8202848000c240010803d074100140048600001c0690582e008503400310547c52680075a01c1e1407141034072010100202101e42802520044181c0b408191061503001800c0c20086406e15000b07000d000e80c0d032100c20300100308480640720301d0400b8007680b01003551440d0b440346200f00c90040500090910b240120300140c0c0d51464400c240e1030a2400404800d0840e00030b200c64030340c40d99002d0440c0c0b400803103942081d036149c03220038041e42049026481583c0c8240340490102c0f41034200d41021402c503001721602262683d468400c8421040221001503001603070995200051910400001c10300f6405001070280002690340e03518120000c0e00920420b512500400a002d4640054949400341040242501c0c1099580c1d0b06400c1e10095003440070003400010000485101c1d01101c1c0040200500600c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 399050863 1250 399049613 399049633
    0x8091212040f0f03020d0308180102030106050a08180a29070903110108070e100509040e061b04060816020c03070b130603090c0b280215070201090c180905 68
    0x140c0c103500a1045008000d2146800a10049507101c14801c41c2d402800a105030b08080e5022110854024001e6840c0d01034242d00a4800300240301960203044561101940c88014060241804000803e2244074000650310042c203a480406e44404003580a010080195104002c02142502e02c1406030980c128032001c10003c158084024000c40380555082d040c1d01010000443d0920001c4640d1400309a190710562450b041c013000307140410b40c4520f4081e0411301e0840025040e00d401c00001209a4000e030240502c101d800f5080a220700d02051116103014608000901351072402009407a101c521184640c01150080c4017001c13212000800b91445036131101d040b558140c1080c8009641145641404a4810b001c2d100b440601c6030082443d4030203510b05103c0e8445540118003e180b44e503400203002104000030f01c0204c0007100c00743c000d0400c4000891000c509000010454421603040080d0b14006c6240c8448000948910701404442c950301c5100c1200602060304004005102d07400c005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 399052113 1250 399050863 399050893
    0x1509061603091805071d04090602070b150306011d130506040609170a020304050409020301060308070501140a0207030804031416030e101719060506040303210507020a080912 76
    0x7400d03299880710343d11907402e0036941c000495004403141c0000c103082d4440428000e402002d0f040d5201c41c0188041003084407587c610050740c101e00400c99600d42c1c032005022100309100003200c0004d000ba1300400540d890328001c024a040d4a40035034003035030076410120b00340e4034882681589803a0080119541c03030520b85048002050800e5081d2054201101402c05003102002115005200e6500a500305400c1400304030041103000c0040741d00d90360b260000030000b40804043e110f014043c1c40001050703010242c0810072024018104140b0f04d2042008400281c0c0000d2002c0c0c01c9078141c0f400d50150034507818404d40c28820905468055810f8040d04c100b01944a8003400141d44180c60b480415072030f0080c241c841d180c02e802141384c1c82029000041d012088401d0100c0358143e00103002c10360310760b140d000c141590303c150029030004401c8510b854141c8450050202016041e18040015260407072009448001d501d900a01c0e080001411580c540d6400381490340a80c0c000d800c1e03036100e01e000820 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 399053363 1250 399052113 399052127
    0x1050a05090607021f0201050604150911220303080f040f06021308060c0903211207031b030c0f1e0e0d08030708040201080903130b0c10050106090519051509061603 72
    0x3030170015800d01c40090310f54241806a0440b50074151103510101e410402000041c00002c0c9581c1010b10b0180202c00032000c039080c07200d401c51006030514028504604004008440003010b20030410368400c1488000762103241031559040c1c000000684403004a01c013203680102070fa10001241c810380e0244110808054000c00a5001c1102215941900842c610f1040000f00304110740180c0140400c0392055514810650700c004036140014480c9810361140600310190300701240004da4610105040c0d9030041d800d600c40e01881e0420401074a20702040601c014008a100000c0144041c000034183c0c403501080d619a540c0a40856144d2030044802060030750201e4041c1c0c0042e1480c170200d24458404400c9400d1a002e54448220807030402c1c0b20a10319a0055540e180c2e94030411001c0e2940c420b0510455028020664400e510a46403d0400069118001d01e640403030460080811199950261a0701c6514594203a551144000000184c103030154002c08100c0034a0400000101640a85 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 399054613 1250 399053363 399053419
    0x15051e090406030c09140108060a200408070603111303031d0603090a03030c0c03020c090c0405060310090b1008130812010303110610030b131b090501031203090201050a0509060702 79
    0x6410800884100e4039030080f0542231143e4941034006001050008a00303800c08a400d01c1d024415403003503480b18882040c01d40c8103500000710780d007007400140600796145c041c3d0a800c844255150f400d00803840800c90040f001840000c09200040d06d00c00d042d609440c5e03076851050002041c2d99101c0c9800d603101d5440340c018940c21000649445207802055000b078081c08840c0b90035078024000030900c07000703200030f507400541040744004040c08009559520000258400c001c2c0382c082d96621407034454848183c4524000803841581100203d02c0d0403540000d00a80c00014440c407116105540c0c1000a0b091195048030001d010149001000381030700101301039449940c4104880141c1c0e1402a449404805800000c10f1080250b020070718007502c00c0c803000103403405503551720514500040305001003c0c040d0b20807031f500e035203130001082406001e2540201920745400e0501403e066540020858419120800148500031a4403401a20b464040d5032104e0b501921842e5401d001c000400464500c901e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 399055863 1250 399054613 399054629
    0x305070e01082a01120513050c0603160e041107030908070e0c0702061c0e070305120309120c12040b04050918070501030b03010905070f05090115051e090406030c 71
    0x30000900400001d80da107075104485140b4015a50141c090b0072940700303500010b90411a01302c000440024841c42560301070714000008005825076850b00794200310b40c00001030f00c00c280c14800c10036440c2c55490111010542440d00712071100d030b9103000400030004820300c0810080c01155070020190010141d0007a60682c1045444460303407182c11400d68881140d0030310004805205160043c04c20070058280f6610182e104101da090703054500341109c110040c018015840581c0400c2800010b00c0000c150071400b42a0a2071442c0c003d800390340c0d0380302c00c01030b07124220800501501f544005015201c501400c15180300d55a564400d03042050390841d010342845041c1701c80c003052010380b40c541c1c455400030340351300941102c51038900154010480c069449815540ba58605400120240505406842450151402d040c18801440385403113050300103410585c00e6624107200542c11800340c0e0902074a0003500c01000d03161500051040c0209101190020f0416401000304486007a27003400741c070011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 399057113 1250 399055863 399055889
    0x60103150203070509040f140f1608061e060c0d05090a0503190611070204050a0204082515090b0c0708190305040b0c3909061c150204030507 62
    0x1400c04542248400d44400001c100b0801640e407490419801000d4401007607074000800c0302c1c00018210810314204c1d101400c0341c0c100700c10400140025503601d01751020134a030089480c40e00c4008181c1c06641003507035841a0000041c4014203541e01e4003101d40b6801784605980380040d030100040e02603042581c100303229a88043c80030519090000342c12030751007051018008441e0702034075201d0090000740c0c140c001401c3c0800c03e240168546e0f0007090b02030100844016512490440402c0c02c1030010381100100091405040001c101501ca0aa050300c080107110000c1402c52203040e1152002540071030314080b80482c0d082407001c004101c00301120084016510130040d500c810018903140c0741801008144240800d01071f0340c800fa006040e5100c0d201003141c0d255120703a020000300d00f800c46800d42030042080611310030001d00140c489980001910343e4410707414880c0c000f50380150400790307588080c00c09030f4000081c808450000008011800c8086544135103904050307842d22054040da414030201 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 399058363 1250 399057113 399057143
    0xb181c0804030c060807020604031d06040e040c27020f09090414070b0426010f0504080304110402031b09010903230f070501090b0d09050d0504050405060405090c010309020120060103 80
    0x1c03180170344603440d5507001d0451a07590342da0a407400c549203c0c0300070808240068040f0503880311001080505045100491240382c00e02d40038608a0160308400720304009000c00c0c1c130921031411407069206100c07040150700d4190032900c05940e8003401d80c450382d22804200a002c18859001b0103a40d01280309020345814685a50ba074100f244a0344c424100d0742001754a0381c00b041d0244a07440c90210302c0c2c80740045502070343c0d0403c00003034400546065610003000020300c020483c1c420242c0c030004000755401e6040d03142c9030400c110070700e41001110300501400503491072242e100b064407030065a884007941141888206009005003035070340300c0701c0c1140f00d040252452010006411001c0310b105039156200ca40c02c081c42440c07190050300541140d107403220380340c0740050018400c04143c40d4413a587c60b0745881c548800c01c019550301800c800e009521b0b001c03e100411304040340c5140032280a007400f040c2c2211034401281d901f03c001c4124403404000e010985090f0001055080c12240206078900c1c2c0542 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 399059613 1250 399058363 399058367
    0x405030d080601020d0c140a06050f28020d1506080a0e03040f1401050c01060b030613090b0f0903072001020d18030609210e01180b181c0804030c06 65
    0x5042e602c80d070250344030701c2a06a071280720300c041e40080c61180303828040c51301c0401e100900c0c010010f4011a51180c07101c0030800164506108182e01c103030000d004d00440721070003180e40780740081c180c1070712501500060701440d014520b03000314814203403815441c88060f0f52a0002081c242c019103620402505003c030800e0100d400000f940c05892960081e80016880c00c1c030038055507504042401c3c180300c0c0c140070030b10144500b0700c40c010080061440440d500d1800204010303a01c0b400000300c8030994079210071a030105103803001590380404403204902054551070400303450b500032114001d01e0b03e6082081c400034600241c400c0c2900020a80840e15030b0405414240d40d40f4400f84840403640f00c203507000f000800c641c2c1e0031a007100c034065000040300c1c1c00c00b1000152030000c0c1440030004607151411848580d640000b800309110302c00710f03008c905e260808510110070700c0307440c1f103150801072070300c140c0f40082c0d640c035a6070284540c8006004240078600c0c602510b86820920069407040380e50300300020030328 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 399060863 1250 399059613 399059627
    0x1030e01020f1e040b25140c1e0310050406090b151305040312150f08100b030106230105160b09100b0d0305180a12060b042706110a090801110f0405010f030f110405030d 74
    0x1600501070031504465216810033030000520946205840d02d030640049007002ea5114010340100100c8000d2425110030707c0140e602c01081404410715020030840400c0d0300c14280c01d004411421702052103140a02c0c141c0305501160080b0681d082240e100286111000030a00d080008442007030060703004036410507080750b00500c50050000c205d9410f600c41080203440403603c0c503205050581c2040c924060890303040c44bc0d05400c6524044c40d030140003001c0c4003000700340c40c82c500c801810310a60b00e00801150800c6c07041c4400600340140401d00c1d000101c2401c484d9202d0500207020b04000b0359480c18000012654442c05841081c035242103a0050304090068614964a003500010080c4918800042c7c100740400c00f86c2e01e46642e5007001c0304081f560402400c0d0f8080f20354810004134108000c0508607400480075110b0080c0400c040a45510481c0c103540448400342010304080001600070f078058a00403405828040c60949500401004000a4030540c1e4054080b20b0907442c03010790a840362 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 399062113 1250 399060863 399060919
    0x10c02071202030c01050328051807080c01050c010615180b030402090103020607020f1819061424030703090303060909020109050f01030e01020f1e040b25140c 70
    0x2d600488030044c40e55005400443d0030080c900c82d103199107001c05158902c2c0c1507218410300d003840d44400503c415241e820b03080d1145185081d0181c03000c4d074070304812280d42d12031040c0e800d8103100c3e0104002412200c294001c02c010212949084180300b460180180b00200942c00080d102d207900b90040383c02101c09040c3c030f105950140003190035900f503800b005803607001a4012603200f0401100c81c00543c03a066110000171000c4070401049040c240d00080b030118001940c0010149401020014112400318814107600181d600c00d0516405400600682060111080102c00000180044030b40e155200c4d0303003518045d1b030307041001e541c445005105032002031078003a00164505c6014011407800f11b103241c4224505041c000362860301e241c0d02a00b6038100300c400d11800c6001042c400103c0c858020141d500d1312100030b003189043c0c100b26040301140552403042c0c01c0c0c40b0000c02008190242c00d0b0202c1e4280b60000d02c1c80b00070030a00e2515a60341e1282844880c09040580c0070b004100468407001512 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 399063363 1250 399062113 399062119
    0x100608160918060b2a0c0303040510020106150f03050c0313021e10030b0306010806220201021e0115051e06130906180c08070c030e150a02010c02071202 67
    0xa018500381c469558030b000c54000251007540c8910005440305608002c00c80e202400d0b05421861254031124220780c41ca140403104c4a800c2140407892994001c001c46059840843d440c0c5642580d00004074010302c0705801034250b98012a1500c2c01680c0c2084003201d480540f65001d01042da610301303107001035000a6401c101c0d013030158241d100040c607205003a111a6003000185540038031001c0005543d0341e801d28400b80200366a0b0382001c1182c10188400350140801c0c20041a03d0b00f0044513080d05c00040b40c00440c0003411540480c4116032003446021014825208145240c035918880c1500800c8800030f901026602d079240020141004469058840d10710000c1048103020101407003803640c05040c1d00610340c0241c1c100410103c0061291001800684442c91030b034000c042150801c640c50001c07002c0c18800040100480b20744d0007450042440d90500e460510f41c10003002181c02540380c0b092281c3c0021010030b007807441c03c4d81507200000140ca01d500310b4001139500c03002407090301624a13020390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 399064613 1250 399063363 399063377
    0x61c0509060118230a14150102010e06131e151e06050102030406111e07031a0f0112050316150b0f130209150d0f0c110a03081e10060816 60
    0x10a02c84d603010a5201c10386650100d51030300888500000c20900703c4014540303400702c850130a0596424800d144180000301e00410160504906200c0411402c1100400340600e841001c0380540d03054008440c1558005902c02c1d2040c40b1032a080043c103103104ac46442071314030110000d411207940c00707031400726481a000381d85040d09016048a41503001080c1060921030700c04410400e44018a0011524008602a08a45040d403800c1e401c9104480052602415910280000110011a00b604554041c410101000c145103009810343c01201c4070f0310300f020000541071041c03050b095199016281c00c04070412107900e441c2d00b04100c4010104109800147d906200541c4801981c000c241d1090010040004062154103403060381c1c4c001000401c0c02d0744c031519901d0302402d6034003898400a001c0c6c01c02007040034025450907520701c3d46800c090b04120000c0045503150381c3c01c1c0d1402c80101d104400889180c980b1100c924003911082c4100c500151108000446101e01c640241d0040141e642e5104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 399065863 1250 399064613 399064661
    0x30f090209011a070f0b07030c020706140d27050c030a171305030f011a04020304030c0b060105130b030f0106020a020d0b09070b1812010e0c061c0509060118 69
    0x4043e07400c440c070340c11003080010003d00000c10300340200101100d00c40c0498000c64505114002c0668201202c06010755001b8181804508d8108030785c000c85c04a074041c22500d0b030449814410103444403007004000d000100e008003440005a90030201180d014808803100c00103040180350707880c00200006400d44007001c84ca00310700c4000d00000c00d400b855140c0d0711418603840d5000039007019121143c174207260f99501035404841c10780d050b11090303c07030707088500318203501e4039450103402044484401810940f4050005020307a02410035103800b41c42c10400000b8030ba4413250060044c2d40180c0d550300c80c501d111030000900c3d0f40300041d08151654050443c0c4001496a0785000328a00043c0c00e840c16401004c501003400580680503210018400700f0310703480c03003940006100180e0002840344d0440d9060035029595101d0006140503d00816184513548904500011200f4000c0540c03043c001d504000c240206502c001414034140d83c403c0001032942480180101c040760a120120050294901900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 399067113 1250 399065863 399065879
    0x30b1915120507082118121b010c0309050105031b1812030403080712120504080306040b03060603120c0f0102070606061d0f04021612200f0616050d060f0303030f09020901 75
    0x280607041d003c400300c3c0d080c151058002a00c08000ca0350981c1f51a0b22160b0004c00e100341e13000b80d900d4004000c0c01d00021005454900034890f003104d008080c10f00c4000004605401e06074181c0101c50c692510496450f0015191a2201c038a407840c2000c1c49032180d40003035035440a010040300c04407176010000524100e082d5503629a8040070044070014002c0701c1340309003480c00035401920300c258410342010b40c0c0d0385840d1040004440c030b800c103964000e501071402c001c001d450000d103589445800766190713038031514540342c000c0c50481b0901d07148290354008500002000b5a03900800d040c1c030003503101c002001e50301e00c5220900715014000e8503408404030405041c242080e900500903e00d00d00c40d2855040ca0544803010b4a44006550038006400850b403000f0f001000c410391860b03d5189800351964100415540d0780d50080604036034050164901d0034080d107405082111200f1001c600c0c207020325691802c0c42180301d0000d11040e408a810110001e000c64124443d41d0380040c4d00402d001c0385e0364200010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 399068363 1250 399067113 399067117
    0x90b0f031612020d02040f090203090c040f09021c11060a050a0c0c0b03090615100903110d051515040e060a0507030e151f030b19151205070821 63
    0x7014422109041c1c1e00c19800c9000400140c140c144001d640d039850701007000c0c0d045100c1d0784000500c91060060141941d00442c0e2140d04001c101d03030108005188074504070003041c0b14000254040749134159900032428087c21104a2030045220344840e030402020b100c100d2040919100008800f0040d0140040c06840c0e090086801842150b580035220382e01040b0a5106503015060759104600700800b240481c8400c51750f40000f41e030800e1250031080d00140c405041808000c10384241c001500b0840d80f2001a6600c00e01d4000b030441d40700c030a040e0405505580143c07810065a002c03801d050b1071a00746400341c0480090400024011913441ca800a0002e0001400c80c0e8105511960a05c400d030404004101d4284089550308102d8100140910f50310840d14918110010203a0400c002007a0141c41c02940020030401c4000c201c0201c542c100000d00c8052190041d042c1961030102d40c0450202e0001c1c44540b00e0801c0f1807145465040c500d6585000107106040060310300056a0a1800040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 399069613 1250 399068363 399068401
    0x12030c020c09040503090f040c09030b040510020a110c0a030803270708010b0a14030a1217070c1a010305070504180215030718050f121005040b0601090b0f03 69
    0x810784801c01c0d050340c00103040000646043e41c4540c0081050303103480c540b100a400c0c603c5d00880c1d0030000464030100103411100c2500c03000d019203050000090034060248100d8002150440d000c659800c1e1621015200103406046184a8030403070021140b18240224202d05813138008540a040d40e56122a0320302d03107a000c12038000d0400c005068210075a07001c01500c00503044420011640140c5201071000244a40e8803074540d8003140403000d02c043c0c40208a0320019a040074096010580e403180c166184410180d00f07117150340144081280081d0f2003090300409a00c00d511403103641c1101d40070444294828080540031f0342100d481044546051307482549244180701803a07445916540005040340c610300384610361060700000f00405c4a9010300e1000c200356600d904004100d04107004145520303502c41d03020b409030a84c41115040c105c401c03c0750035031400142c20107205604e014940104840c405a44840c0070ac2c1c210400802c006081c1c10a41c1d80184107048021304607611039000c0e081110f4040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 399070863 1250 399069613 399069617
    0x6220203010b0d0309152c0102070b0301030506071d1e0102150c040501080919080702040b040207050a0b0c04080c15130b04060210141306020c1b030706080412030c 72
    0x89001490b03224040203070009802501c84005462412030415140c50881c0310403810050103064200d00805005001447c82c5003198150546140c0303d40182d2034171034140c2001e0401c2c2c0020000000f0040c0005055101e016140c0d2852014a107a03208000c03018500b204080d0300800b4080b528400d201c80410440000300144100c0b00c0040010b6095004968241d90440c4500343c006000e0050356000784000d6000900c40d4010200404525200c03105a18002802400c1c200002803c50965540b0b400a1803400c400410440d95000c01d072422035558040c651044540f001c0c003000080510124030199003c440b4044080d1407000308070010010807043e1164982d038280e1081c4850003040c05ca80403084040d01c200c510107641c0d14185407001e850503184071522030205081846101c070342030041c1e1b0f44942014018070302040c42c200d40c2c603102000e0f01880c200c0c000f0500c0303549005005410f9044036440000c00075001c0d07a800325100d080441d502c03941220080c04034003004500c80c80c060310a0303200f40740c1c08ac924 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 399072113 1250 399070863 399070871
    0x4050a2c061f120e0109060506010503040c0315020d061205010b010503011d18010501080d18140103050711010e070911090306130302070f060c0317101205070b070309080f0622020301 80
    0x200c05000f08540c0200c00407080c503992400a00304004482c0304007034000d1030900f451421450141d84120041c0b00c6404020f0051403552902000400341c6d40540d04035118482e424050345842c2c8205d4101100c1444056403558203003011004c95500170021a03042e90b00003d009103100515100c05004000c0180607060b000144034420400c0d401e0a00c90240a00020406008034042040005110300d0701c09104000301c4280000800c0001c13142e00440c50510001c1c200132400f696245410b440e0800a4580944503500700f450f40c81604a01043e4081a16420001040703800360340c074040e04040c080c0010103170700350340b0910116003940e007078010401080d482841140d21541c1c42e800c0f0040b0400d420b41c06400891142041131081603045540000d0002c2104158051440c0c9102c030195641843d11409145a61554041b428003000740505d0000e82a5015810340d501d00d20305d0010400c080d40e2140f1000c5004d40d443e803128039640402c009001c1c01c00e1541e02010000c800791001917070f0ba10401c049130301d5035030703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 399073363 1250 399072113 399072137
    0x9060507110a08010e070602030a050a0806010512090d030f0b090106051e04080703030e030a0b180106030611040f170a0201052a0a05070510050301120804050a2c061f 73
    0x341c5000e01c000e0410f10740082a4040c140584030701d08401604500c0a5400501c01711400317681c8081501e01c212850b1914189607190800127032036a21a2102d54914003072a2800c102c80c00c14002440c018101c102d03902001081c0c1580303002011a0a540301d1258840f690300010041184518050a1b6125450f890740c1004003021041c100c8642c480c0c0e0142155410941040003890381120320340d110368500364050a041100b640c2d402011071300c02000402425903c41c80300091410035030089000d994050700412014001c01541007064005120302840ca1049040211303144d401459150442d4401a0041c000f500c40c60740151900c3e013141201002940c060503407003040400207414a81c0f50340c0550082c0c406603c9900700b083c20141e164002500440006001241f035a03401011281111440344200450480707610f0950aa40f045a201a62200780c4803804203070083c22b01302c2d0004800500c0b60712206000380079034421710b41c0d80c11940d05a0200c0c04016060349401300829007078101000b8640b071508516 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 399074613 1250 399073363 399073369
    0x30f0e0117070e031009020114031614091011120a080c0901031503150e01020a020c040b031504080a0906021b010513050a1e080703110120071d0a06060906050711 71
    0x1445e0001c0802c00d0b032200d0b00f41c000c1d075800140014a550070341e042a444d516000d01c500c1d2600c4815081e03182007213000041440d0746010702e81a5132207010024044508a041244d00520001c083c4243c6503c80c00741c20104c145500c001d00c1103800401664541104a0756003100b560140c1d08891102418075440d0501d0701507144002e4024400745108103c1c0400c0004030006c203500321508040e6032a44c903881000391307841ca00c2d00091070f403542040c03c96022407200000e01c0400e082c4203030155a036000182c10400d000404c0407910203400e00310440c0d0b4440b0b1005030b0381c5070203c0c2d8400540c5244001c5180c03000100c091944907038018003040785614a02d14600f80c1e10808034915440750b601c50b0358000c12603003812100301d11a040207002403003150001c00701e403400e60303c2d0140d0511038101064180a03990001012160840e811411400400c00640d00800e03178407280d00e061078151000b140c90f10307401309000981c014124030483c01662035650b120807290b400d00d072094929902c0101d0a640c1c91180c201240034603a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 399075863 1250 399074613 399074623
    0x140c281e12120f020706020c06071a13020312030f13210f021207020a0e1b04080a0c090504030c06020307030e03070c0608010602031204060f140a09030f0e0117070e03 73
    0x1d8402c540b0ba01042c5000c0e0002009100d4264180c0c0442d0402c000402500340d0000e0b000d0b05034401121101c3d507403041850071088a01d061042c000c116041c990130059400a180000c600c2c00f402030741a20f403a1110040280043d05c0222021803696001c0d0001c5001240551100c2603217038480c1d0001101078100802010b0f9140c48542e070300001605900c0c0395542c0c20f50601032013003040041034805007400e46950015040c5103180c0200c0e024010444000342640c00d00782500390300f4641d240c130407a41d2ba41c4c95100079900e42c0c2d140381050350013503445240018011082d10425109035007540c0c0d502251110f44d0b1301c40380a0340c000b030b00c028209a2200c2c1030391042c440c20300040803000e10801504050b2441c2040c0a024190168480801d40d08140700803403c0c1d01c440c3c0e078210b900a5000400080c07114008042d8401802c80c1261286108842d03000c00940040e0b82d40003032450340c025101c100211451010444041401421260024803080000d0b1150303500e5030b0300c3e44d4009485052140c0e14400d1200403910741 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 399077113 1250 399075863 399075899
    0x30f1703150112110306060a090302060708090108060a0b07030c020126040501050a0e21040e010b030a0506100c1506122d02150c0109140c281e 63
    0x350400841c2070825038108014090301c1120003401e004190041d5081c500901000f0142ca00581c000603564400f107128000036000303103500610aa880b0070140c02c04080c0f41d0090b02c00c07140411a680089806460503040e4841100e5055400a03c1c201d22558202d41448600c10124180141504858640070080489074100c58600780d04014a25003410400e0a641c2c0280501c4c10b411f1a061080500b050040740035508409101d100c1d0324213074000c5006081600c12680042841b40400001180c0000f1003802180101c2a80f4401e12030b5844035010402c01c3c0313104401ca8000f00380702102d68000680b42c0c8124240c0c4140807600040e0060b642c25440050122004040340d2040007110301c51010029408612600c035030f031040c0c206140e04030b81e010894812030b40c3c403046202a00800c42c07088046c000d4000085165206e100f08900f81121000740341e40707005869071a8400c1d402c000c0001d02552600405a644103000340211448903c0c10b40581040030b003035000d410302c86401410118143d02c4012440c0e500f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 399078363 1250 399077113 399077131
    0x30c181401062309100c151406040f050f240607061b1e030e011803030e070915050402090d0b0403170906190b0a05130b1513030f1703 59
    0x166079228405001c1d10840961501d580200380141c03104c5444850034460440340c142055800b0006600f0b003c8848081071349945015410608450b410700c4200341c840340030302000d8501303114052030400241c3c183c0d0000c40d1882910b15140e4001084004207041805008600280180c2142403c40220b0099408400309440141c5c8982c6e000403200000040d64400700c4062500b244401c40c0c035680b06400f02e03506090b1000301030b186c82c01686242020340c01140c031031040e400101c82034501442d0140c040c0503900180c4800f400741d2200040c1e00301c0c840c0581c00c01480402c0d00410007605000810009411070f000c000c4d0011801e452000014000c2071156000301d0003501c56110102c5103000c0c00e88003640c024004600c0f50054024000c0043c542441c0344102c00c60f070080400e03080107040100366491000e600c120b0713014000c44000b16100000d0b0b84408a007540680da401a440070079801c1c9406807281210814602680d07030402c0002c111250400c6800a11030605882ca070a1210f02608176500144d5800ca0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 399079613 1250 399078363 399078377
    0x1b0d060e06100b0a020606100e040504050709110c060c0a0219030809010b0d0506060904060e0a080408011b09090f0f110a03050106080903220305011506110106030c18140106 76
    0x148620604400302d004041007002203203080994580203450391405030803140140030514081d164940200f00b500e0214a014100304114503290070000d070350b55494030a03d0b0181703250000004283c00303803c040381c034070b414040000c0200380c4408452400ca980204501d00c114001c5100307000c03001544100a888841c0241d689080c1c43c200040410b0845070440c041e00d2052110721401c0d0b0011750f000c241c80341c0c400011682006941c0e03442c20000c2c05003c00d036a00c41594000c40c1c00360000c20040c1c40260099507120300017048101d03191000006404040c8110402040411b030041005a0361500030320384803444818041410000307800444240e90b9010b06481c400d01010440440c07030b5030b042c0306050041c40c284c80c2c40f281e50b040009181e5201c0c46820710314840a40f40c41708002d1180c2150300d40000035a4840020408942c0ca816070b076011121a006810000e0043d2240c5610148140074050641e074002108045851070401d0f18100b4002051b0708000c0e181d140c842c903058070452544a28000d020b80d89401b5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 399080863 1250 399079613 399079621
    0xf0c0515010e04120806090408030406090c120b0a050f0402090a060b04060906030b0109061e02071703210903041815030302010e010c17040b07050d150e0610021b0d060e06 75
    0x622130054054440c04229503141080720300c0e6a8101030302c0d00590098203d6a480e1241d0070124040c020003c400f0b040303d00300c03000006800f01c80305054013400d4043d25465a00d6112039443d40159030b019540030b030024517503402240161500c44091a006029400001803040d512103a105003908194008400b14a49400410030103400d406250141e1009282407000c0d00e08000c0044e00d07007042d0031023904483c04a001c40e0181240200007150150009402018080c00350303452036550b0703502000038400c100807034141c20008180c00004450203407042c00003940c1041c0c24080ba1901140c9840d104d05031540e103034402c484e0149961820140514001d82c004175021403c01c0400d402d4461400034401046881c2c0028001581c40300003207904598010343c00c108980729120b08803114003582c41d81d02103451608030719100b01090748035010704a4100003440742044e03548008101000320b090102801580040000d603801c2081c1704a0a031141c10010201444142c181c1c80e01402ca8101e50400303c01a80294240 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 399082113 1250 399080863 399080873
    0xc160804170105090604150b0303160516080c040b0f0d1a01210b1e09010204030302120f0307140415021501080a02010c0f1e060b0f0406060f0c0515010e04 68
    0x141d01c0503040000a00040c181420101e64602c0020006450605000701d51400c424403500300c03201e990303401011030351a000d550a90521540603608122882c4c0b052070707501605403540e0b403024400c590441c00a8041204154281b05c0906442c542d1070360301501040c180300d21540d81030040320740280660380c601012518449003200c1c002060704401096010040307168894140034803000d440395480400030104e07880d0a01c924541c45a90a072074006046100c0802041c0304056028004886c0203030b08841c14503125512200c0c1510804641c1c003140501000019052400b801e40e0a0324401d41c1c0400e41e2405694030b2046400d8440d031501c880058000e10034501050702d01c0e0310764030f01428084e13015148c102002d60000c0d0400b01b4004c0014113401343d80148406201140074000c0d0a6040c0a15080c0b016102d440c0000041c4070716014a031203508070740034008240c10036102d000152020703520b03880401d400c0b9000a030f40e041c000328400c0740c1d40c4c81020506c01e14a195990414006e205940050445092a01d01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 399083363 1250 399082113 399082139
    0x3060212090c0913060e071a1309140604052502030406140a1e0903050a030c030807210b1203041e0801200f09030105010b04061101020705060703050c160804 69
    0x80c1d503c02c918503028421200c1050b81d14000c3c5503480b80c8000b510f20002c144445c18a030031540500c90f420a00e401c80080144140020148907039180040240e95803201c0c001421194031600c1e08200e8034418000074140e00302980041e406c4202980c454000301141107908144a0a804400d00140c0000c02e003042490703008a0f40070030b0440340480103801c0440b10342d001020355501c11501400b001080104a103203a0090381100c000e5030304581035408441c03003800c018003c3d81c00828128009681440000d00083c441e01c18000101c1107910b101d0240c5c14490b010714041e06070b11142d580e1180f04c1c0343e108426080304000070001000c60a100206141c20703141c040c2c20044483c1d020300626414580f062035800c80d4150398401c3c0300340c41c0e003a03152580500030005c1d402d40200071207141c1541c60400040343c807501380700c00f500844105a842011190111003050300780d0180110041181c0c2c080b0700440d80c640d0107a00610b60088a81c00034504010644c500190a0000d400c01901c0b44040000c0031300c418214042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 399084613 1250 399083363 399083383
    0x30c191e030203030904092102061602210a0201141311031b01031e020c070e0a0204030b0105060a0e0d12021204140108061302040b04080f010b0a0b130306021209 71
    0x1985101103207180c010030b4480c0b00380301100d4419035403003014004100c003d40b850f110104e601c00003030040800c00b0740b011359034003019140901a8a0050310a62001c0d200251281c0c600741e1019104c050904081c11100c85074100c0e0f03030740400f55500d59902074041d5031440c10148c490300110064800b0a12981403a07101202d5000c0c3c124000c4d00000c1e400101d030794521302d44035125202880c00080c01403544801c640003280128404101c54000520740c48084400607210065414098141a040e00e94581250481c030403440010b02302e80c1c2120040086143c82d1014006905003428099000c05c10000000d240170303942902110060b039442c03058029654104000b03c1540d10b90100c10380340608190180c0d000c0614074811904000704c0600007691900c800c0c050828000c1000029901d941c0c40e0220841d840c3c10074002c0310310504c26508035a415541c140503400748110080c00441c84181006004070107540600c2100c5c840005980d40040040c0c071502c01841c540c1c0012200b5070850908030390090801c5a502 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 399085863 1250 399084613 399084659
    0xc120222020f0c0a0b010614160c18020702010e0109050d11030a0c120b010501181202210f060903040e0f070c02031921021015050306010303082a030402040209030c19 73
    0x34640c00c230712009200444540d92605040d0000000041c41c00c3e51403203d4a4000e00ca4407d1a01c40c1217100d074049402411515100b600c40840846410b00119041507203842201e501082107030110011541098258603241d8003d001e4a500d40e000381c44485d210804d0b98010328820307403081c03185001d00c180d080c5c0a17409000c007440c0c410052140040c240380402414080c001d1008a0344812108640e500d809840501030400720301d074400b801c40d90b031294580505450f060024010640001c401c3e11006c0102e41c141c0305490f8070080c40b5100c80404030038051000f40888140b0420f000c0301d0015a804110100300001c10b03068803001604103291600e80002811001c010701d00c55000c0840d034031038010800300072100700164006480d850783c0e0045800303158203034822501400b4030030010043c164015062072040c6200300c03403d103084a01117481201078425422131845035a0910100d001880e0071303002408000c85c024100e400e1a82c007440010b01d400071080208216400d6154104401220b2507009040e10040c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 399087113 1250 399085863 399085877
    0x20f03090604050907051e0301060e09060901120312050124030b01080c090a0506070804060216080712030306180f0c020c01051204020a030804060203070c120222020f0c0a0b0106 78
    0x12402081c414050340c0141c0e40f0450401000a60316441003056800c03910020040044e4580071020090f203d078400e0082000103081e080ca81c0ea2076040c180960f90003540054000303c856031070500b00c5409990030100440801000c60b00c284541d0b0607500845000e8040005268000d40f20103404180c401122070300302041c1410030b00c3c0314010740e0f008440d0692080c60000080d0b55007030355800142c2c01c5031064000380da20038008646001804241d00c01361059810540803509000d0348803d42180449440c8603507400c5600403003040c0704080300f06203030380d10461083c20042285a11403207000c021010303030710000070003650f60808840380405c0b6001d4150207002c90f0018000c51403d03040020068420141011640070304000814210f442c0c141e0b50300001e503084031803291200c1c4c41c2c00d802503e940c4807102c10b0350051103009001c01d04c001d42002944081ba401440b0201c00c00110100244594041da500b070b40f02ca13403d1001052000038040182510780000e00941542580391900b68400541070304280100420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 399088363 1250 399087113 399087127
    0x120601091d18030f0d0f060b2701020309060301060806031203100b031e0f0a1407090e040201020a05010e031b01020a051b100f09050606010806060912190b07020f03 72
    0x181d1071160040103008104456841d03110030b461962207030900e0b80481e014001100c82ca168250342c044c8100300f09100051144903616000c06c0f1603402070f201c020207004404a13200c1c09200e0f2264110000c5070060041c0c034140041c2c50b0016800f6082640254040303011302c000c21234a8541400181111000c1001d11400e6040c414a02ca007201d1041c0141001864004045207084426585901e11403a03407080c2c048461900c640304201c54101900c910142d582018200440416121162845600755598090319140340200c049012400a007059041d4015840c3c4040400c00a0048400455070344000b15a520038401040b980c08080511800070350b407061001a02c042d9015044456007244601c1d10302441b01c10100d00c80c240411410010805842c00b8000032a034113807500003001c86070180301969a00e90301c8200546414104075011580400104405500ca140c910084298a101402141c40038000c7e010034807542e2001c94000daa458032060100501994104811a0f11041c2a0095820088 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 399089613 1250 399088363 399088409
    0x1030803041a07120908070c060e010801090603390801021801020102090a06111015150e0a06080a110f0903010e1606080406020c030d0b100306061d06040b12060109 72
    0x1a4840100c4d01161200003000078424501d00381d94010303030000701e580e024603940d013400340c907007894903240b140411090000010a060b0a10072003044a4000d030310100c0600c5041000500d19004404540118010039854400c2c02d500355880d00103440c0420005a541c03c2c00030202e8510078114600904581c01004018210345607091001c08880d140e0a205d002808103a041c0b5040070302d2850344114441c50614050100b94404104004640c14a000c940084207041e804613501c2200201541d006612480c08001a9100d01c0c0300980c802c04c0d8510000b000180f014a0140c00e502c10342340080948400f01d816012032070284144070b444694a002003108030300c00b80b008050b00650b0303c180001c1c096550001400e1020540480750140c4100e030580c0e40d13030743c20700f02450002e10000c0c0364140108801c1ca803480304180244a88420380740b09880382c0340e072414014110071006480303002c0c0c1900080d0500c000502d04248101034460411a00c410507a2440c021000400c0102151b00800c3e2180c2248034000d4140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 399090863 1250 399089613 399089627
    0x50702100b130908070f0308151f21060609030b010f06090b090102010209100c150b0604030609060f020703171509070c0f0203250801060b161a01030803041a07 70
    0x21607159004155020350303013418641402a01c8001d0b15404070320400b4010940c0c0242624801e118161008212640000610400c0d10a4800303c03000c200208100800c05c0c0d000d0a0303025603804044501c00c2c0b840d914410074000303131141503025002040300b01c4c2060080001c00c3c034500d40500058010010180d01d0154002c01845551040425000d000502c1c2d00460f4801e404031002a0030141c80203c0c0c5e00e440d01e02c01401a62134280031390b485000150040710030144c07801482800880105480c0c00c081c1561902002070440b041d04a40c815512001c06400c5041400030340080f9000c1c4c2c41d460380f54000b4110030156540018001d41c40c2082092100c01c4070ba40300c07401303076400481070b181c64902c5a005241100145440303a134065454400c883c3c50002e82001250024480c1c0d00300740c0c01d003c0c0150f65140007802d90310385000740d0000c0c58007444001c06281107194000d00d486d00071654084060019100130700312420a8100b83d481c40400010007040c81241624140c8904079000c40107440c1c603140100900c41 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 399092113 1250 399090863 399090889
    0x40504271b030209040b040b1f06111005070822241e0b010906111002371b0b010e060604091109030c0307030c0e130f0501050702100b 59
    0x25000c03050001001225201c81c07102039907014140b41030721300706810940703c07140040b901111517200000005801a050b00700800b02003035414081c44a0609024003610202e0350714464107018882c03141e1056040c1406e008140c01a101c3d910340700c2e0142040ca02e0420000201c58032404038004400010b00052245500d0b215141e02007160003940c006880c0c4203d0240840c400072954020014002c0c801050007948904901602602c40d0303001d5560b150030a0782e04040400b42000d107a048010301e008840c03d150000c2141401c4ca081c444090900781e1107140c1340b40185200c0203200c04120301030449594100080c1c0e8803a8003a55501810448650781d16074085105014100301c1c0c86810700840d60a8460200350340c00342032940c10500100c110b07410109880c0e00b22030300d00c511902c20070500000034107011494105680e080060b003a45c1e00d0070264014030500000e0050b29000c0d000810210100ea82030a1110303070389100d8000450981405031000780360003c0c16001e201714a2a10300c428841d41e44d0302081c4444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 399093363 1250 399092113 399092123
    0x10030b0f0408040e090d030b030c061c0905070308070b0c031302040e070506040b0706060f150c0201090b0a021005060301050601020d030b040b0d14010f11040311220204050427 77
    0x6503501e500e0500150b020f00d1344080800300124081c40b10140010030030024200701550200803203500042056561106480a80e401500c10450b5411842c40c0314502082c5203d09600840e013240c41d942e030780385058801e5006440200012a0705400c1185030a00d0f190046080408642141401c805004070500d041d10024451996403010580b560f400703000b148014a4000c2c405034030366698420140c1340c0e034002a011030f0028034086022668030380c6210102c00b80c0300c8541c1c49106602e841c041c10760b03595981c542c0a074103002c2500c40009070a2042e4000b0b0005099650240c0f80010009015000369103000e42858030a90410303040003041e90f40000e10403401c454a14000c5000c500000204004007058402c0030780244407080b03a1000d02c00347c400c480000c8400c3c480200180c6407010204800c43e20080c010f4041c14204000c20008507849074541940f0040c02848114121401009108052582002e4440300c07900030034100040d20306407040198003003942d01c11941201e401245a20404410040201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 399094613 1250 399093363 399093391
    0x2d07031b050a0501050a0902040e030703050a110709050a0c08090f030d110c0a08040f080d0903060902040f050f01080d17160c0501060b120c19050901140403060b0910030b 75
    0x24000200640340c0740e160003c008105500f0810b42c03481c00341a450105078001c9051500c001244940001110f1010350180e4543e403e01c00401c5007103450010340d13060b40312540b064020218601d09148100c0d80625500c0a0018003424051806071405400524020042e00310082045c148071000c4100d450b40c4044080000d10341903604c440481c207014182c5d809a00e8400d40451104000b8046c0013007007940e41c8900b8051202c5d0740c40d12070aa482a06c00e005000081a49500b08001103440d00400e04145c1b008002241c0802e0f0500c1c2002203407421141c0707000c143c001600400144200707000d10701c12620b0360f29111000d00a50384202041c000098000c2e03d0410380e842c030f1030038014030980140000315800b0009001542d900c041c4e1070080d41083ea4000302c03034003c000100d802405080c08031003034089251180070001da140d41090320307a90844000c442c18040500d44640d07941c04150b0003400507500c1460009404e500035010310040060040c01801d1079042d00c5000d2010821800c88180d209c404056012 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 399095863 1250 399094613 399094667
    0xc0309010905010608032208121318090213020a05090f04060e0403030504110109060f030b010504091107050c0324130606030308070e030d09030b06040b062d0703 71
    0x20300624000c480602154038009020940d0f1201100500350300c0814200842da001944080b03500762103280c0709030102c1c0c0c1c0c03201410705c0000c0701d00c0026181e04083d82c03c0902005503148522100607081ca004c0705071495271170140008500e0001e0480b0701030010306008600b0540080d201906c1442080f09040c801c1500c06a03000c004e0b078581e0840c1d000780080d6494481c59080030300d00a00901000d66088918800c1d284851b083d80d442071040c10100c03907842d500d000441f10010002e030014848560350a0404c8003c000c04600010305004d418580d075034260359280d03258024107000d42049120040b05100e85c100c1c1a0302040548032070303001510740304114441b07078a5484400c880c43c2d541910140051600341441000402c0c1900070202030312402254841101e280c4944c0109171711001503460220128a80000600105030154441984450007420005011042400041d05e6030003518900c4045c0c0002003070309850f03078040c0c11303010451143d07000d80604101055801034825440030f8882c2800303084040c079803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 399097113 1250 399095863 399095881
    0xf05011503140618091903120b0405100e0403090b0c0321060a2105010c0f1b080f09041107080a0f05070f0f150c1d010504080d0e060c1c030b0609090c03 67
    0x3a081c0801b2040103045044482c43c004d000c6140e803268203c070f020700d00750310b81e1414140fa0007400d1180b42c0301380d00e0344482400c101741c0c071000c0c00c0040c00607404c022402c0030214160320644014924011848015074071070200102d02c1001c104410380402c0442c2410003442101d40b5003113018810358140030003140700d04c01025002c0114082c3c910300946a582015240840c20342c0103102c105d40d0500c42d6607240c0c1c1d080030344005800341e00c100750401440c0180420030301500001e18406000d45600c01000860111086180e003291a044141700382c0b1030b00c6c8000340c4807038140e80100111100c19041c1c00c0c82c500304405038a6004008080b080060b0080d40c80044081c02c001c00c00c0044101c903502e0781c0082041c4481c2e100010544001c0b0341100c0180c84010014409a601450a03141103a2080e40104040081117000301d80881020200c41c0d0088001c0c401f41c840030a0a00200420802cbd80300000300c0e40460207170003000e270b820028895000d01003c110140907511010146a801501d060240d035489c0c4800440e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 399098363 1250 399097113 399097123
    0x503061302041202060c1c1d031b040518060a0501081606020d14070213050601030606021515031504032c0904060b0120070302180121060f0501150314061809 69
    0x15904c4c7d40b00382d4031810003c90b4114007104445003505c0700d004070b9021b0400c03c6c981e4603d041e426049030000b621703034100002d2a0580019030310200e0040300e40066502103a09528002d016a4190341c0d16840307000512015108100c0d28020818550700c0303a038907500d07081010b9100c2c0d4041c2909010072490013840d80144039850100c6e040305601411450100e041d40e4082401000b055070003600003410800d00082891000500107800c81e003205c2d45102544468084a007040e40d501d405c1c40c0c150140e500380c024007114100100d4401c83c040c2d211042ca0307107600304440d600021003280f00820004040e0000e07103d81c40d0400182d43c0642e00c490700080750000c40c001a83e0030100100700a00340200c04a401018036000300f00c15048034030a990040200700403100244074480240168441e11b0142c1d050210141d070032162030700f0a140101d41c00503800e50400006410b45009070800305c0111840c034100f083c01c99061103800441c0984101070011418074000041c2c0c3e100c8000b403440901101c0c2d002151411206000b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 399099613 1250 399098363 399098383
    0x30106030e0c1203070302010b06091c050a0501020c0304080d14040303030c181d01120b0c0f09040204170628020c01060b040303030603140303010501120207050f0109030503061302041202060c 84
    0x1c0f41000440700700b83c0044e602e5000c40c50131001942030520f415610b007072102c2a210310043c020700402d040c1a83e0010401264001c041c25641e511800ea148004140c0c00e10040500043c1e02e0061680c03642000200c51a00744559107d004000210b201c40000740348541c10766003078907498038000c104100c07816021901c548100050306101003a10000194600406940040514085a250381583e030f079080c18000f8404400f00c050000340f0b04074002100840014001c14003200e12900003810490307804080340c1280c0098000d0900c00c40782c20180c1c5011070003001070961100648012048400c040c0c0204d01800702c005036a0640c1a4002c180f44413076501c29000403020742090406652038035681e01b00203000e4070b81c0b0320095031744842003e10448502004011641601c406845101300d40302405100d80003940409001d0f0341c11302909424480900f802c0c0210310700c0c01e00070b54606860307007806800c002e02c035400b840550801ea03104200c100001241500140001501141c06070b44514014601c28281103a00b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 399100719 1106 399099613 399099619
    0x4080403022403090105061806031b010e04150f0b070503031f03120c14010605010c0206370e010806010c140106090f020d0c08040305030106030e0c 65
    0x18029000e07501454114041014003240e81c0c20b040d80080d2180381242e5180c0c410f001640c078041d000c008030300c00c0350a0080c045041080c0081da50300380300801341d819280039103949807040c2e015010703640c82400050014800e100d00c021031882245400d004004441e0003c0704007041c60340440055500b5558084010362071904c07094031304400c42c442c0040c004240000ca01000c4001810b1a02d6840e14a80b161103000c3c07400940c3c609281c140000420342406623240440810150b81d02008203800340d80c0548045998840c41c50484014000915a890182648407004001c150211018840405480d03842030f01ca049010011101001c0a6a1140c001110300f4060004204820566a450035242e0000500641c1c0c50100d83e080e0380384ac450740d9000031340c00704810300020901d011721700c80642c50386060750701c500d040e590160050206001d06000c00d0b40d101124140c2080400041b41941002 = true := by decide +kernel

theorem cover : BRFrame.Cov 398920863 399100719 := by
  have h0 := BRFrame.cov_init 398920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 398920863 ≤ n) (h2 : n < 399100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
