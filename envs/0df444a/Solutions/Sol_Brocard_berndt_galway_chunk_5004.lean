-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5004
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:25:56.137686+00:00
-- url     : https://prove2.me/submissions/7fb329d5-80b1-41e4-8bfd-a31beedb83c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 899820143 ≤ n < 900000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 899821393 1250 899820143 899820157
    0xa0e16110606150712091d310c180e0106050a0603020703020307080c030a1d0306011520030d0c09082e020703020c04151d0a090b01060e15 61
    0x10307800080410500c1c103001c41c95003050300800400d503281a40548900200d9210f1541c0a0f000903411001005014490168201c44407001000d081e90f9090009889205c16400c00c0c80343c46d041c0001041d400e0701036143c5503010305036a110410f00492552651580c6406480c0c4484510443c24134603810360241040c814081170315001407540b1001420300d40d0480080d04009012400c0d44410004580810342100240c240405220300955030392031024802030000d0102c0c811803003e0050407100c40301d290f4000c140c960544008071000c00004c00e0888040f6044810084c2d01e510f80601074640406208001c401480d8402c04000140a1304c0881001102c02c840366101d441140c0c0c00440005e40c03102c0072184030f83c1001400515291243c450642404100d034000341d001c0700941e0082e10f001d801c5040501540c0b803407014031110155030707600d80074800b4002e04403100200c45104003c0c000030034994999024083d10380e04240c60380b07429a1140005001d0301056a000d07445600a00011110070030b02104580741 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 899822643 1250 899821393 899821427
    0x90d18050901031403040e04050c131406090606040b0a0201090506061f2d020a0b0c1912092316030c060c050703021c02040e07050303070b13020a0e16 66
    0x65038616210079512242100807904c140c0801c00c000648840c5122259001b50702800181440310360050811907590400301c8542112804d101c07204000c1c1c820a1032007980704e6400d4428a6440d5600d0b0000b404910542d00041c1c4c5082000c194038545503415030041003040e2203107086a0b1280c07505070170401030780c038220f40040903c0c0400321883c0170144180060580400207071117007a60090401c103048400c031002c180790401070340030b80c00c1c490078010541a050f80000030585e1051501580207168031182107008410010310240c8103803a05070001c02d92150650a400c00544000c911400039040c0d4240d200e084450b0081c440c848041410100144016003101e5000c0c1850315050314140e4280c84050040c4000e42d0796000f111000400b6840b0501da800b842c4181d908684651207580c81004102d80042d18610311680c040202809552000811a0a81030b0404920f1885540b040303426034120b6041343d0025000360284030001001002c0d414850b02501c20080c0622103504c05110032030712032110440c8070319 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 899823893 1250 899822643 899822659
    0x390a0f0f0b030f1911120f13021c1506032301020901020304050f06191e110604020f19151103070201090317040306060b0a031503030206150a030b090d1805 68
    0x80504d0341c03c0188075004400008201c80344003920160154024a0030000d1246c1300c48200582c9204420410b6803001c429890f407414002e158000c503580310b00784c1c080c0d06039071036580803514240078a55902c04007404040400380082d175140d14106004410740c0150040060707c00c4047c00d00d484041c029200d010300306034011402d02d80b8250030407400070b0824500c036404ca0400c01000911145401c1280702035101c0e41c954606486694004c0811074042c982c4140c2003010f08841c884007101c011030025003140e01103840b1848041008009240d07034902d51a820060351301281d0014154a4016a41c1984486178860381c0040030101000d648911503400000d001581c200802e00000346035100522029000c00079031418903484e9500e030421250b142c1c0024422040c0400c409282c40d505000f2510707002900702c002c038015499076030040d43d00c00018020001840003080d1509468030740b5503000004503080b003c1403040b03081c0076800c1500c80c170003100c2c40340010716024110708000c1c03c62030345042207900241881c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 899825143 1250 899823893 899823901
    0x10020a150f0906050403020109050d0f050f0a030612053003040f0813080a0c0602031201150c120804060605120d080613051017390a0f0f0b030f 63
    0x480140621a000c490050b6202ca140022540500c181c0c1d2043e4400d80001a41d542d684c00c0240ca1300c0710903403030782d030411041c01720001c0030aa105080d15040744101880c0c0780c4900d044001540a04616001081e01c900104103103c00c0c442d000032103500382c003032400320f000035503221146c030501c903100c8240e101c680140104080340004500608101081e800f4240d03507403d24188880c03012464078282e001d10b040f41d00090f801024001c54110900081c4050300055242403106040500387c500148030f02580008040e80e40c46505004070303944022280d01c4030801d5441c104d0b02d4000f51440c0415102a98460315090003c42c003070900d01d402c1c0ba0102043c80040081d0810414110388890000704465005804011100055112802414011a1001e40350071070395003005504c0001070040051004203900010620601691604140440600450b12240340080040940641d10707060a201d541001100e280050b0f06140b00da0a41c050b44c01052003001166035030311446120340400e480c02080c80940744089 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 899826393 1250 899825143 899825183
    0x30106031208270c1203120403110a060903030f0c020d090504110f030705030f0f0f06011101090c30110105030615030108010b0901061e080a06050402041410020a 71
    0x8550120749840d8603000c1208541c40e03840d009910f00101206688500c1c5428954034000c44480070b1824090010360418035080300742d8007185800b4001400707001c00c802901e66042014004004580d40154050001402a00e00100106541c1001c091110f00c2c000720440c800b0710104149080462030b5644400031401c06040000405040c2102040c2603820821001c204170300e030014500c0b030040758841503182c0c1b5002c00740b03480800000f054509151810020041c00c110b1403d14150010400e191080d501c00785134113602c1c01401036803c0505000b10006c000190102490108080708003000000300c0c3d04192403081c0b142071500000000c1100c1355200e91915107500c540301842c1c1c01407004000d0f801507040c884201b003c590082c1c00820403a51122034500e0b150401260090040180d4a0940c690802d21500491502e588951325400c0000d40b0300401c110764100e800c840041c28000f44110351350f43d902c480c40340c82d15104418850090ba025110121003a00102d2010b542c5500003241c40d189040300d03144 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 899827643 1250 899826393 899826407
    0x307080105010519030c0c02040f0903170f0411120609060601110d140a1404060521070f030e0c0418020324181603030e091005060a0809010b0613060e0301060312 71
    0x51b1000b0407400c0c2c45410090303030750b5000764070340f407511a6000034060a076801c00410300e4031107400703407000c0354cc4440501100c50180d011031075201d6048500507000128080000d0b030224007420450700c1610881090084030500401c0716030082201740c0740d100a428080488a4561351a010340d100407426044d60000c2c0c1c0d4003035500811000116180050b507c8029a5249401380c1180e003040c2c0001e10003040000c18400c065258500c6040081d6a00e1020305e049d120040c0280d031200c1172a010980c540035503041c81081008201c001c007800600520048035044c401c02c20f00c0c01c100030180e10a101e1034407941e1969101d50840c1031080428400c14030503641c0c4001c1888e401d8203152410341c0d40d2084151444189288640650141d8803aa036001c1240c15103400300301148801800610121141600811a582d00e41e070480340c001400d402c02000307581c1c850030103074010000c40d403aa5400600000f09000194a1000c0d81410340e0341e181c94611807860054107141c04c03a016400028521620702100c0f034a010f010302c0d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 899828893 1250 899827643 899827661
    0x1e03090904111f030b06180415150c111e193b09210c0a050c09010e10120809040606020325020913140d05030708010501051903 56
    0x40c460101844010100700b86030030020b9915114003c1c1040030f081c1c2603060052160802d001c0b05c400307041000510000501c0d484507840103210f0b507902c0c050008040b6481032050b00620305c03c09941080441404090000042c55004549030021845254821701e0400c00400c243c40480d0700d40e01c005140c0409120300281000c035140320141b000c0500081543c0080000c0e2012180c5000819400e940d001c000c1d140100950075503099011311500b046000701c0c00090312000d02c6000e02c40c00c801d450195a0041c0640314a03440d032600ea0007815101428004000744400c00e6413030030f603a41c00b01aa61088055822107060310301100b44102020200711010066a10340401d0340250802443c00e09103000185c115034550703000700c025030408600c0c1c00400c20b401d0860402250012403a00100d0700e03d41c00034922210042c910201b0f003000081c0700301400a28100b00009600400c201c40130ba901d50b0070701a1854108a90480003d04070000101c2d555104000b903075000c06642d80c900900244101c4254040c082c021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 899830143 1250 899828893 899828903
    0xe07031b230f120313050f0108070e010f051c0203010317070804030821100f1a09151c050906070f05120615040303031a0406061d010201060e01090e1e03090904 70
    0x1412002590070f0600c01032000c0804004494500c6290109001010040341c005a040c4111142003220294000e081d040c5004000d00c0c009050510750381d002c1c0c1d0240074800d944800382e90310032038000001d94290b0066050380d005070320078850742d5291340c0a000d0601c682d000c020000350043c0402c0000410381d00c098082540242041120030001000007014400704071445401081c40c00000c2010340042e00b058005019502c031b04d580c4411100c504109648561030b00382d400b07075001400004c49101c0c0c140030744104640d00d100d0142070800d80d0981001a12054a407e40d840c02581e0100b0040c500490103003100e1314090315101c1c01d0411081c5046900380004100b0354004103900d01142440301c1c924010000756100b5107000800c8581d001d140020284d40d402d03068045e501c0e1480070b1200c00e4014001344006402c603840000c2400c11000101d014081e968010740d4075040f032400214112100b0341280154110304400c80d0705044007100342c04000c0241c0b80c031044050300208503070026810007a44403940140a4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 899831393 1250 899830143 899830159
    0x3080a030903090b0309030702090a0b0a1e0801150312031e0e0f190303181106030a0f0f020a111f0213080a060903080702150f0a0e07031b230f 63
    0x1652008985034001c80e00706d41d545d000000d045045103484404240c1021032450304000400420000c1051004180038804c00480002d00b00c1c4101007550382c0b0384000d0031100000780880b0b80a280400e40b49491030108450000b803c4000c141000d00c2441101c40c0702d00d10040c190302c240800c0040e031009140c4242280356600030ba02d807100c4d520104011865030694220a54a410741031410000c0c1140c42030179060801000b43c9250b240401c00340c40e5103c41011084980c0c1e5079036240c3d501d43c5402460040030048901c1d080c01c0b00c514100c651617001c0c02d12841c5540f00c01c10710f41a12110b081d15168081030090b07900409148610700480306070f005d0315500b45a080ea2850361520b0b8205546030001116080f964151116888010181d00c4868250401101d00040401810701d8480100d1120010556202901c0c01000035041074069008161904036040c1517843c0c85890f4100900200310b003100c8031440c12034403074000405074000c0f69569203040024001b100c06d26915410044802d10400040e80d100c01a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 899832643 1250 899831393 899831399
    0x60618030114010612020c030316090e040305030610053916080c09041707030c1223180d03030b090a02070c05090403020a030f020304081f0e0703080a03090309 70
    0x424840c001080d19030082e44100c41d0f01d00140101407488900c86019114018402d12815a070000300752a000284c000c3e54100b00b8500007001c07a9420780a52160f204202000c0c10702c001d144c0c200000310700841060307400f044a68a03014065655108080744910300241e980611010300f844d80c42c4030070400300c40d010b8441c0c07100d0505010f54542005176404600e02321803070702c0070000c07040100503200c01602c2c10795a40754103150170707100d0005820303400d00406030713030800020f6800030984210311a4070030a50180d480c041e003c0611800810180340f141c0c1841da4030448000c020200d00c01e84064a10380d801125400326041d000790b041c02403a10607003000310181500c400803964540e9808000520400c12801d0060315200c0c07500f051020360400e540101e0080030020240b001003a0b02003001004241c060410000012441c1030813440c5100b280d0080d070303c5009004440c0405605400550b55a080020090103801d000000c0d075912590503104c000c0c074011003007042e49000b9000b50428032056000f404c0c1020b20300d40e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 899833893 1250 899832643 899832649
    0x30109240510080c270a0504060b04030605041502042c010b0d111e0c0d18120c1505091905220603060603032a02130905280c0b03070206060618 63
    0xc085c454290b01200c20885415080030101c02c40144803ca5040c40365510340840709125100703e010280500340c0780c4001900b80842c5120041e00740480c0c0804641e2550361316003a51683c10303002c0b801078412030030b204161407803034501e0b5005d8140d49090240514046e40d201c0c108006005076003c0c00309110050140ca5000381c66a1684410441a42c4400740c3d07a015010116040c070240721420414001d18050f002e0712171500c007045900703540c2855694101c2c10b0090424041600d03051f808030040180c0303100c103c2d00e0f050344940544010340f41500d0350900410300c42850780c05030b000c0e80145034105029070f5190451062005280c000700101090004042c0d45a480b03081c1505c02e9a0015004500000883e0228081802024561406070f076014400c10b03000e58000307140c2220b00c80f000c08206460700024410712000340110389008180307803c0041b1100c0ca08c1a1420f84a03400e41d0250380c03208556100142c012400741c1100d214003426030260016a8400d01000800c1d0414200d1b00b0606110000043c8592 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 899835143 1250 899833893 899833927
    0x70c1a1b0a082203022106090303010f060c050307060f060906050d02130513210f05160308090c06031302090c0f030106201b03010f0c050d0f020c03030109240510080c 73
    0x991044202080a071b005080141f0b003280240000b0441d5208100400c0360f41105030f407640940d020b0703280c040f02e94809418400d1960050160103020701d0301d8051a61400e40d070a5019104858020708207121482d9160208024045488030294000110304e00003489909994440d41e4861035446900c8000740c02a1200c000400a1000320304107210009903a02d221900309a4071007a0352442d04c1c0903480c2001c0c5420503020400303c10780007418400314801043c11404184181165103034007604550300c901e0246da0a80440c0360f401c000b81d0084680001186011000400f110700009008403030301d1959280030821900700071801d00540300c203100120310f4048060280a030304400142e80b0f0a401d60010113104050840d141090900015031030b0401030345040382c000c000d40f1202da011000000d1224100401d041c0a4400c103014400d02c2d000000010071030031642c0e48a50f8004840300d0b60003007a00303022898540c8010850098a034808000b01040403018481d1024580c065440f03c941420041d02c441028200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 899836393 1250 899835143 899835169
    0x11107050a0b060a03121101110f12071b08031026120319020912070b07030306050603060a0902070f12020a020916050f070c1a1b0a08220302 62
    0x3070704900450401e100b85480400d42212046a036000340c54990b03643d1a4505002d50b50517803d00031000080c5440810a5002080703000c0344104003560f0791417040c440300c9103921800c0481100b503004c8000c900490701c550390380411500b107120200000345d2552681e000b2600000c000c0a41c21080c0540407948046c542001031461003034001600340001400c461b1801d2416450402e05080000d03c1003140c2c10800c00554441041e55003001a81c612150f80416401691100c10003081e10841c10300181c000398070002843c1c414001d42c0c0c1041043e0300c40040004502c000d4521580c00740d290380c000d2082d0440d0350b00418a0621409485401350740968030b043c000f802c3d503050b00d009600b0413010403040d4240903008560240d6000c10f408084017142c80c0c007074214000e80c7c1180f950140081480d0041244183e6508090700340d20700445454413614a0800e1194011440168a03145070121481e00040026050030065405540c1c0c60070918440d84004003a041003500700c0c500004810000003607121080d500b401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 899837643 1250 899836393 899836403
    0x1082d030f1908190e01090b1003140601030f0b090a0f141002030423070e01080c0126190b040608010c081006081f090c020601050f040b03030d0b03011107 68
    0x1c8603020114403840b100d0405200c0103101121042102044400410000d20100010700080d41405040d8590050030b40c400e001700342048040a10105691003180981200c0c45240c0c803000034400c031031059446010030311008001c00c01401c1c5641c0040c8594041c0341c1d0020b01002152207544141d00c421700702d00c91450040c0c841034081a0300c5440c2c143d0a215507003201c004840150b1660803e82d40391140054824000522186030701d190081c000000d005d1503004004a03d80f607042561140d94642d1100c001480391404215241010701190707240c090484000c2c101403023040c1080c0d69270130000e0540c0401050341509a55a11610841d0380e07250b01c6141c0180ca8180c00000c0c1004a01074081e040340b1000c0c10158010000205c100303d4154003c1b48103074000301e404984031151801d280c106189403215080420614109080207041c13560004010341240d00407541a140f400b4102d00303120032103d82d181d8031a0560001c12611a00b01d5254222201002b00900002031a0a1240c20030040350042e04040b20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 899838893 1250 899837643 899837647
    0x130b161110140a111b03091302030a0c0f0f120b100503010f0e1b09031c02010b090f190e0f060115030506041116050a0506010f1701020301082d030f 65
    0x3900010303002200d64003c44550b42040210b00940700d010050141102c0000750144600c0ca44603007082c2401501c018010250443e08034041d61006400a90422100c00c401c413450021000081413140341c901001100f1920362000141c0c06c11412544076004c1c01a419405490301c072a80380319201c005400750040440d40d2100d859506140013807680c007880d68010315400d034140090019020603055880020380441d14601c0c0c2d42c1d10484042400c0c0140003a11f52020000d4444800b505030f01034101c004a01000c48880d052071b130b200384508406031700a48040c0108110410884042c000544c00043c002001804030741c10902071800c2c0038a4003200760405405400b90a14102d44c0030703050300509810000c01c07a0188006032600042031814010002c010b5074640391005400c0512500317001500e030342900310060740e103d50f071140001c080c100d80503c0740d50900c08207100c00482c1d1070341c1072081d40e040c4c801400c040d00c5414054826000649a80c1800320101038a1078a240c8101c00100300404c205c640d241e524503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 899840143 1250 899838893 899838911
    0x30a0c050c0f060f03090c060418240909020102030702041d24161205012303030412020f01090b0a020109031719360b130b161110 57
    0x260400c10007448260182080006030b01c1c5a5450106640e1906898041c142d102d0b59840d20341450000039401e11504010300240116014001031a0f220b03204c24103440a02040302060310009114401109010518840c0c44040c40b0340c001036005140840d005204507800d101654001174100d88030040340c2c0841e030340030b103110ba6882d50040c0001040c04070882a1040e8148151072090060f41008040c0c0b590901400384842032039000f883d810308032940800d010405503840b89042045040103c0c600b1395112120100c40c0554a000000c403010344120340303a4415904375a6092100000e100c0c074409043c022003c40100c1c20301421406064010704542c00481c62403454100500710080c5040c0c6041158490410021030281d0512100542c0100724000940c42441141103000380d10601c4008000341c0300300000c441c0110b00c5001c1652428010301c6c0c040c1482d01e0b0003007400900da5840c040100800c000700300240ca00030101070852201411410003001b004c13039036031800d4207082d071070301d00000681d5030b401c600 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 899841393 1250 899840143 899840153
    0xb071418010e0a12080f0d0e0c15090a050f0d141b090403081303140a0804060e0304080703030507080d061511032a070e040305071b12060c11030a0c 65
    0x350241c44000d030303038103000c243c14030800307000041a04130040c0c03c4000c0000c040b0030101c041c0c012204255800350b420400034501204594540f0880c2c261148070710840004c42c0590010241121003000c0300800c1c100345e40d40b60030103000d900319130540c200e82c0c48051010700f4004900c600840d14880403009000d00017400b8160941d00b1f55100121002e07000300300b50400c000000f40c0000503150410748001c04800880c2283c902141c015140743c01c02039a185000c6984e0a0240e04100000c2c060b9100c0d50701070003151101c204660350b0703005601c5841d441d03501c07107d41080403038001d000403c010b90042d4181854031541000741c1c000c1d07912952000f008020340b1005052100d50240380381152059420207185002d00000c00d11805062030a90041c80c03400ca01c41c0041c1c1d61208000700d42c0100318a4101c080386141c42d08001d0200c0d000600161120780d03400c0c03001580501006016015500364a11028071142c2c0c82d182d120041c000b80c10f4030407d105042c2d41d4140d00307803c00c0015088001440d1350345842d0b00058900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 899842643 1250 899841393 899841407
    0x130204091e06060f0c021c0602040b090f0609030c1c05030a0c1b060e130f050a0516110a0f050114150102070608060a1a120907061b020d0b07141801 65
    0x320b4030404c5070083c0c60b8800117501081c22140150100c80c2d900e210f5091350030b040d100398100080186828800280001d0a40040d40540f00d640401c4070510031000002d014015944102c0b0a026490380122507148200c1c5400c50f480700b42001403208101e2003030015541c131451a4030440012020820140e1158100b00000740e1400c0390000c020401c98805262500152586c044c04040501c58200d5031121004580c5231360151300b10b00c2100009201c07070304240e2040001090152003400b02d17106111f0084c5410350141c1810341600c0f00c034000400f03107010a03480d00c1c01007907500d0300101e0700740d5240c241e910501440180150301a010307000b642282c029009001924000702d80e8818010b1103082000c10805a44901042048030b07140200c0b40300a20b511101014544500c82486085005880502815110004048080e500c094407880e14800380085400540455544020750192040e070b00500010b42c080303603242d040300c003500b459001c039511051001c13100e400508156615080c900c111b66865030380000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 899843893 1250 899842643 899842649
    0x703020115120507050103020906132d080d2604151b02060417040f0b0a080705030f1302010306180f0c03060305060a05150a0e19020c0c130204091e06 66
    0x2642e05480c1c55500d50740c07210b80c00d1180030705140d404240c5a95a45910040760b1b111211010b048400580715001072402101e041104010035131880030b0b03401507030f05d50740000b004e952802c4c000300012a644101152208004803450b02e88682c66036458801440c40c18056001e14030654000780850206042c500440b45079903403410307602a030017000c0c0007081c2d000b0950981054200c0c2e60404130f000401142031803440b07241e204403d240040782c00064448a000b01808003215a42d80c0d00042c0e850380c00003111140000e079198030410741c80601051900495410308603215106050100c4c0007591a0503985c41d00000b9070062400b00d03143d00c5580c002000d0341c41842120320706406c0412420781581c5880d80e880070010f1014103902d0303849010900c80003c0020340c1842080c010101e02e4155120052084285410b640b0003500b00b43c0c00d0049808045a8029220b900030b03058000c0603060b074401c0801008041d20a40c0b10000baa0811000c2800601806281803001c005200c100f151301c0403415080494410b64 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 899845143 1250 899843893 899843909
    0x8040806061e060f0d0b060403031d03071401080603010f050106030e011803092105030403030e030c150a0f200c090c03011d1909052a0303030a050c07080703020115 72
    0xb01040c080c542e01d4030191140300340c001c0d00385a00e82d0307601c540100051085141544d40840d010a0010803d0350019446883c08101c240310a5441c0d50181032665071829401509486800642d45c0486544201c019640c4218002c001107540003207030592504841003a007088001a807260811602c800c2c090240001d400340c0001180d03000301440c1c50080c41240c850091506041403110443d542110320000040956082420340303580e25034030b10340a0090303052000d80a00078094000b00590620b44400200440c0c109006c1d41440c3c035074031180c1150703001a20064581840300c1d00a500e4540010700d2801903441d504403000744045602001084681c0e00000c01803980510200300601000d640008042e50300c031280c00380d11800d0303180c234078604c1590300344e060040390744070300d00f0310088140720000800c110700d220080c650030701c0c080045030b4103e0601310f88101641c065204101084a070046980001d9020350300441e0306041030350b01c0d559966a50301150090b030060791659100c1100e070700350070580030060400c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 899846393 1250 899845143 899845189
    0x90c0303020c01091e1a0c01050c131203020a0b1f080a0c0b0a02071e0b1c06050604030f0f02012003030a0501090b030c010c0203071a190f1d0d0804080606 68
    0x4010090303d6183c01e02807607200116001d04d83c540c0010600c25241441c00147c002c0c0a00d01d0300700c2002c800343e0004c003c580201000400009400c0d415400c50760000d581541c05849c0002c03958846c10501c0e43d02824080000080345001c0c15094001d01006010b04404800f60001108908107440120341c507810000032000d0070001a10304035000292a011202c3c0c031500140340c1c4058401a030826112030f0701524040500113654003513690050003d0501c1c1020103401c01c9000d4030b07002800900d0042c0d000c0180110b000041c820003003485039800134011481454400803240c2d00359400713441d04070f040045540541c00441401a0a1000e00a49014010b40c07071007040104c42c0b00c80081d80e5804400005414003003014000d00030364a041c01141d01620b410800c1c005140551600c039040303036205035100310311441c81c00c248001c250b20400050302c50440315520811081310541c0d0314009281410404e0350302507489401c03080010003160103040140a0440942118a040d10600031400d03038007000e8200103480 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 899847643 1250 899846393 899846429
    0x3303010b0102010e071a0d110705010f020c07090b040e1203190b13020318120d06120c0b0a12090b06030f0c0a150c021806031002070f15090c0303020c0109 68
    0x5100c0110742c0c0045a806c0b0207036001600c00802e02c030760300c42030301c0071070038135005040140006e4000c150359807140c4000c2114450040c111012402581c0004c0c5007030f0402c1c14100101c03922078001902c107035402003000031004d42c1007640520748001c6c596002d400040200c10420a00340c2c0c1002000000e036440c0d028401a144400007901e81c0007015410030070681d0100105021040303400103444004080d10032511003900344052941c8907004646250240b03401c100b80031850100500b8088052a4032030180224542801020941608005440c00800400c606164060b645d1802800151800fa0341700011302c4c1400d4041c1030030804010010465079102d001c1019480d16604642c200300c618405c86044841c441c0507040310f800c044548003a6000303547c00c200c1c0940d03807010f449203401682c0c214129000841c0d001c4501042e4040d43c82c2c054041502101d050001c1030300c10442c004040d00c1c0c2c9034002949006660307501148100e541040e401640300010303040d00c6580052802029240c44480e040b14031034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 899848893 1250 899847643 899847671
    0x12304030602030a02070203071701060819020d02030f0312060406060519050a020111070b1e1009050403120e060106121e090212100c0807050715053303010b010201 72
    0x46544030042400341c0c0000011450141681945e200650040940790003a40c3c8180080d00120607520b924290751074040002885040023802703840d124071501c030f502006001a000c00c1080e00c400c91080c5d80500072000da81514441c140010301c0354404502d403040030703824000107000440304c00d90001c2d0180841001000320382d4958001d10203041d08a80f600641c1c921f01039204a01421080110161b103a8010502400704200e502130544034081002d1252102520400f890507081402e481c000120000b08006101d245034a4006507446406418030708800c4814000b000b084481007850031040e5000341d0014020107a1144800036100707800074061024031b1040301c07804030740c0d40b111a0042e10213540340d603000c2c215245c054201e004103900c00305884202c20303082519000744c110320020600044809000400030303402070781a610407a0300080c4101180e4003120214009000142183d01039508c02c402d44044480c40214414260402400701d000f811034103800e00d400d5a00e600025819a41400f203c0c1510030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 899850143 1250 899848893 899848897
    0xf1f1508030328020a0201091203090305040e1e090d080606041d040501141e160c030e010309080406110c0904260f030f1611030d020a0504080610050123 67
    0x1001100054030f00040c0b0182c0040c1411003aa00380d80960010804415283e01035001d20441c0f07002d5101d44d40c02c00c030444c000b01c040361500500100842c01c203100a0103c166541c0d2025804014242c0c003c0703121488040c0ea11494108455000700c95015400e0721680c2540282441d03040441501d009060900b03040303450681c9503031036000b408425080d400280074810250040110080c0c103082d10009424a40e11001c1c0503d1005513282080701d40e00041000300c0070303644003212465680d40d01c240c0310900640c0c0807540083c00c0d40000d1704058886c0304840114650f200140018482c42d01d4455000348002c5070305007400801c002d0740c0d1080520408000110305050308040d50f81441a00ba542501c4d4803c0d040c6800c0c0c016050005811003000c000c01030601b4030201000d000c2d87e008039900d0b0310218440002c65900c0204002000e45030018042c02c030400d100c5802030721180d00035050117801d00380c03550700c6030785407003011202e00d03862500055003044603503001041c01c2c0a030203025140403420424102d00b04468 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 899851393 1250 899850143 899850151
    0x7031401060203040911041a09030d0e030307020105070f171902070810150306050c03040c050f0f0910092301060c08030106140d1a10020a110f030f1f15080303 70
    0x1044d10380b00c582c4006c2007943e04990261050030340307003000040c0406624540d904044100c0c1d0080c4100880810824024203260070005401030041d46130a400d0741c011261604001001c9480e40004546000003072058200c42c1031100b016031075980c5070151990051034824400c15908155002510184852100494014481e8121110200b08481d01c02c03000d00c0708000a0f071024080d90701e0003003485003904c40d800003980910301070140f82e00c14070b0301c0b40c007080480d10075055004e5000c6810341600711941000c0100c641c1c00340c8003103210b00c00140da441c2e0900555400000c4034800f08003004044040ba014124050301406179031810003009010360b40e40311410300c010301401d0148403040c0c0c07000e25282009811101901032400c000e01c51003452840000b607030000550200c0c4550080c8a8007072075184000350381c01e09150042101c0f482c0b80c00c07000612006c038494405030f83d014000e040040c5110001002550420101944107403012041d03c2504011640d071010002415032002404224145c0000f05403500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 899852643 1250 899851393 899851409
    0x6010e040302191103150106050d150b070b0906010b1603110a060c0c020306060f15091512010608060303070312020c010e0706050901080109050c030f131a0703140106020304 76
    0x12a44481c10240c0c81c041804000308001c940355444441041006189111400c50a030100c0c0ea01c5000c6240c1240451000d0007220300013401481a002d402c46076410903e40510081402c0c1c000d69199002c00074540d00041007601c4840c0460309004d00300c0c00411845004042034203505d4280b01e08070703081013451903000801a0401100740003a03a030340041800540b00c0315078494030810201c206000083c0102e00b0200090b4441c1c010000003d405051001e400001000000d080d034003001881c00d500c4400e900310119032a00449180e28800481803c41c00610300f000c0b40c0c0000d5481c6600d0200020108003005240d24042c3c6c1060026000180d08244035000c64034002c01c000d80c0b2421410061070042c040107211701101d108620b0000740c1c4940013001048403207002c0c3d8803402c5680c1c81d14a0300301500c0c0296800e0902e8941000040e01400e20030902c140c001503c200004502c182c0364488221034510740c01d04040105424040c000c1c880e40500c216410030b1020180d860072589001406501e90180d8450040c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 899853893 1250 899852643 899852669
    0x403030c020d14060f07020d09050a12030909050c03040c0923040515161101060b0906160615050f0904021f03150e041b0b03070c080f0706150f03050601 67
    0x4110141d1440d440c0380c1d04040844c0e005141145104410540660311a4090f00844d0048222503205050260566034003400c00820140742124120030021188801d40c200048060046940b14030b44c0105401003c0300395081d41c0b20308090034038140301ea882d6404840304600d04545400c00406640840c0c160203094154403a190b55182441814122030155080000580e88100142240303003003603090607095255a17403500c54500094181c03c80301640140410550103200e00c10b050325210004000c5a10008841400707800543c1d40d5000741c51924110302414440b0000501c4a420681916110031f901140c3d00407150034a42c011801d1400030030f60390340c5112508400d07a2091402074002103034a903461084440d101d55a40044403203100151400c40b108003009440f80904440202c448040d2028440d0b50352840e21140710540c0d0300302c800c040c01c44140f00e017132261640c0c181441d009840d10500a80b80031a1041001d80403408400c00341c0c0151402d940700c8441030004c6600010ba1905440fa01c44107a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 899855143 1250 899853893 899853919
    0x301050903070b060d0204020d0f0c09350717010b150f09042c0a1106071a0709090c081005121509340b1204060911150912030403030c02 60
    0x14023034441d000b0140941b904110581d2441c44081e071046030381514a0751011110790320b600e404560030300c004003880100c00003242030300d2060305525a0f103c1c00190220446040c15030300d0242041e6002d040c40c12180701d03550f039680140c0302d0610428890440d1400b0000c140b42142c4401c0c21862405070591a6005507078400c0c200c0c8440c00c030040540c20211000c90301c881724144503400150381e030344441412030300075020008501c42801e0140580d16403940c010a941619180c00c1d01074660a007008110108100e003a200001e401c40b40c902c01c00b682401c441c2d69a50003031802c03000c048000360f5a540302078000c20f081c1e4962120b080707020407610030b01c003d016400802d54860340d440e00e01e008161a05a00e00245a40d0901c07944192150300e042c103100c00008542ca903030b0b55012079050314024400c01c0410500710070001000105940d0151070200d10030070102c0041c1e9410700c003041440084441201d654400060340003528900b00c03181003045402c4000940c907090440e40c0041669403d0340d0024041c80410100c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 899856393 1250 899855143 899855149
    0x606030c0c0b04021810050a090e0601171213060f0e0121240602060903090904030f05071704170601080a0b09030c1c0e030a020906060d0b0604080c0301050903070b060d02 75
    0x190344540d04070045c1d89040000545114144034480c99201e01c481d80400075001b40c450040405280a2002130308a0781e191284031035899203412101d00380390140f070042ca0701c0c81e411100035081d0344148514181406040c400e01814441c0c0008040061040300660f48113503a0b8407101242c12684005809a82c0601c0302900002030108024450240241c80c0e000c41d0140c41400c10101c1240e103290700f00d65198560350f040984070f20034a0b09140e0030002c8500010003290003003d1901d110101458002d151101948840d284a8901c0400c0082c414001a0400144207100000544a080711000d8222075160400d00c40d036400300c2d0309000b0319070b458410005100150600580b9095813049040d0b40720388020b64000b0400c504001e181002040d003005524606040004900c1070783e5034040c0c071250b55034a84004000303040c3c00150604d100e051701c071405005143c551501400080c61814018040180c0316401c160a440d03004041c40410780c014441c03500842c00e5004025007103441641d03950520140b0b4004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 899857643 1250 899856393 899856409
    0xc0a0309020a09050604150b070206090d0b28060b030f06040b030609060a0f0b01020d0305152214250302130e250c080d060312050d0606030c0c0b0402 66
    0xe54011110440082c50340926001315100781800c6604010001044d086a0070704101c900070700c20043d03001d0040380e00604100000302a921401808041c5142d0ba136546c844041c1011140b00c6100015802c4007614604d0407215800da0150980c403c0c40414200217aa001900000b024000b42c4503082d0049840727074071b443d80300921900340a0140c8060b4500b520165640e00c1c400d44880f100c06140000740c00c17a508042c451400c1c030160590240c084d011140404074050300000e0f000b002d0820740303082005400d41c3d4403850414641a8010001c1da221100d102c2e90007107858003a000050807007100104643c40424520300000d11101c40e00c4001600180c0200702c000307007c0c20702403150780d41020401180e0030001c005076078410707842048100784011103901007100210000d25801d01240100c2c90540009a000014010404c0c29540000f10190380b911154000142e038408034010900000e40040a4201d50062101420843c101403040c2b1604100040048010b840040c005001e0b4a01050465556a83d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 899858893 1250 899857643 899857661
    0xc0f06020408070e0a06031104090c05040c020c030f0303011d190515030d0f0203030c07150903030b01120e060115050c0d0302180a0b0f0a09080f01060f06170c0a03 72
    0x2021034980d6100d0700915628100c074050580e144140d54001000e524190140e90180c4c2d60001c03580000780c110b4401e00000d041e041000f141c10b81340040000c01c45413102d1207010003482580d8000e1a5401491080c542010f010361844d81c816041000140160361706000001060f40408000d04a035030785900c10000540380c0040e029a00a00b400c00b481196405111740e0003403200b0841c03d44103104c003d8881500d00a10705400340000d60024000604a400030b00003800b10b00d40918540c2841100300d900310401c0300e462100440210350303206140300c42540d000018441406000c0c008000d010802c551065490344148500c0724121000310a0701800e034459000e80340c85030110070403141000524900039010390420031054403103400c07607500c2d50a00d2420701022011209120391643c90000c0d081c540049503804188104140814188000350005c0e081011140001182c00005111814880e00703500701c14803607011008109034102c82403a4043c0b0310030300304e80003190414000d96030240b61800f6005810001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 899860143 1250 899858893 899858903
    0x90901062d0c210e12032101140d051f0609092a1a0a0512040c050f09090618072105070504050c04061d0a0305010c0f08070f0c0f 57
    0x400315100c0da00014030001c0c4901c6200c000003000c4001942c0010340100f10000c000054905614161030b05242031104c054180300300550b403800f5030f00c0b030440c004094044191020511100c004000d8034140055400c0c0016046480210400c1282c8a0541d514120306400300e20003000740c0c81c40c68055140e0301000040c06c00040900c26100f860818a07201020303182e2440e820b2408103041c81d40030744141c3c0240240c9221019015408881c3c4d0580050390b00603003100030070b000081048180ca021041c400c0b030f01c503510170402903c90b24101000c0c440701603011607880340515401c40910812800c0415210340c4111a4010b00274210320b901c0403140342080b01c2e0700c0459131040c1142c41d1020f015084a203102d80030301500484240942e107000744400c440301164503050100c010b00c01400319510030111041c1203645001c1010b20b14100000144504895034402c84841e03545580d8421040c1c0c01444441e203290701828180c1c200d1410420240c41e80101c1c2215004000b442d041280400c44034440300d80d03c0c95000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 899861393 1250 899860143 899860217
    0x7030b0a0b040f0e0303040203012a050d1d0601150e0d02310b0103150f050d060f06090207140606010503160504260736090203100c030b010509090106 66
    0x302081170303c030b600698043e4000c1d42004190228549040c4503240302185200c80b041e503c0c6c400f0242141d540d0071a410820145803552182c03288144a07950b01981c1c0340448019008551500c11000c4a2429900040781444172a0780a9149507549002081000f0f0301980c4c0c1c00240d0707040741d0144441c1c0d81e001c02945039646040900b50110f80580d4040b01000c4006e0f242041610a0945034000400c080e1003103401840540b0700c240501c0c01c04101c03007042c141c8141000308090424110410903109a5044107035465400700b600014400c0e501c14900480310144d01030700309400c000000a010303100040007000f60382c1c19410a01e040500c07c000300c81c02403a505140c1f11013006c0d60b5160251020b0002100c2d40c403441512404111800440704018000300a0120300713924828540e403801c00742c5128510648070703680d42d0b03100b0805a10244500700c0c0b50000300c0c1c0d0000300e0b5440c0c01006011100120a43c3d81088401c2c045c50000f5150740c00204c0c19034010341000c084204070300c0307441c144203c5400400703095036900c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 899862643 1250 899861393 899861411
    0x1b050d02090a080127020901090c110f030901140324030a020a090609050f010806240306130605070906140c070302120d12020c0604021504081515010207030b0a0b040f 73
    0x2042d071008880c102824202e031350340d510a8905c0100600340402c041e51102d21440100700a241ca40c0c0020f03060b0000b42440c03180d241c00d002d1140c0c101440c02d04442070756000020741c01348540e0b00565030301c121001c02d880342d415410400713100408201104091080191164501e44044d0f40402a40c6007080e40200355507121510b480c50b10002d00920302c200d600300b40c1010003040c071014003120914145c4088070001e120f10352381c90f0080c80324100656407131200e00c0c00740e0503d804652010301a0b503104980000311400810058603040b412108010110801c10940d018144082035000070301c21030718403640ba40151210000e0310f03140e05240c40c903030009501c5201666812a04500422100041c403500c1e200c6001808100d42c46109070b20440844403d60741200d40018010b18105d5000c90034080080c0e5030a040903100d0414910349071468140e46000e080500030030540c461143c2210038000001c3c80504107062460f0f9840c4031420010f071240000070b072580f039031181584565111040281da03254041c0300c0c0b048 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 899863893 1250 899862643 899862659
    0xe19090e031801050405010c03120b041416020d0c0609050c09040309031103060421021f090c05031203010303140f0703092102090109020a0212040e01181b050d02090a 73
    0xb002a0782040400d208490b2031110350f028005982c119a41a1604c800e09040d40d501241e04c5110940304201907039031000c0000c03564450b8418200c034140c6820426125041130740c2000306c1c2d1000984030108543c0b104e080e500d0140d40c0072100c0d0420650020000c03584040a24100d801c0c24005440a40c00583d000c0821040c1a405034400d4101d9000e4910910092400d03805c1c1516440c3c100c0e40039185448074820480a00c40c54038408140080506c1902d03140012400c3e04010607170300c81c02c104901138031042c0c10024001f20b0b075580b2006000443c024030b03c0440c4001c403a151404140700141c24080c032261403105210001003100c4410301c0d07100d9401d60340c110340e1030081c060091034050040c801080302c0c0c490842034264101c0403c0740f5002014003005a01c0c010459000c1c2d4440010740b0114002d106803d00003030300e007101078009468422006000c5604103445c1c40c460014a05150201c0e03410a0383d000d00d015034120402c0c80d185030501e0010f580e420180040d0f0084d100e02240f0641144040b040011480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 899865143 1250 899863893 899863897
    0x51c0b040f022103190e040903030605030d030203160309050a0804080601060915020a0b060409080f0a0e061323060703030f0f0209030304090203180a03080901140103030e19090e03 79
    0x3030701c22940f0003014802041d0030815030b100c0042c1c80605910820000a07415024035010080c401c10b0b10b0104d400d58400c03008141941c3c4404130440109440348020f02180c6020320001c01914a5072404506501c1c00484010790101200450f806140c0da031496070302400030502008031850b03040388049980d203030303104040ca030340d0314091290900186070a00081851440850000403102960b4020051540700351100031107000c020744000e50080d03681d48040000380800000d000342195400a50303803211692a03001d0410030710241c12600c00d00f000c00031141034030054602a02a1040e003c6e089181c1d40c0f034200440c203800e4503100110752048010032407104141c1d140c1c102c801d02100301601800b441e51801220000e9004204019600d50030a100c103020405459000c1d5520080c80100e80b1a07181d9010b032000c0c14040124400d90003d00f40d9030410941007402d014a80180b03107403080090340f079803564070001e01000004100324854040c00c0f07141a007081c00000840040c14a14504003e450aa042031964903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 899866393 1250 899865143 899865173
    0x206030c03041a0106020a061a03010c030207060e03040509190207020d05010c0e0901050d08280908150c0f09010210061502060604110a1b0605070801051207060504051c0b04 76
    0x44140c43c1c002c001d486002400300c0e049030340c1c640042c411940c0c1d642e6004c002d48548101c0b19419200b0705204821030381d00b40103c1c800314a40341c03030050391807515040103020b07503075461140b1103958420881007000303894080000e81e100c0700c403c1c0710101280705c11801101074030420a000c0e50000741a940b1500307001040d40b215100000c903031509248c04102d082440141030782481155408500c003000c05d804245c044000f0070710103110f20601d1a4540503444555201d0a01030702c0c101c0041c030b820317605015004080180744840c01503514200010724041d04070510358480c048140d000f149011844441990003001010104012150244039650300d40d160885009401c496007001842200701154035030900740f04509803282c03126406440c001c42201c1c19074140d012040000c80010070551003501040b101e11a50b401600c00359161101940340c0710410001d5110080d143c82541c001c60750030040700d43c00c03008440490300140c0b115100640f4101003000520041072018104a01c0e40c0c00304010022000d03d14016 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 899867643 1250 899866393 899866403
    0x3010e090f01050105100f0e06070c06090806060a050d021305010915090203040b0a1107080c151e0a0c091a040323061b1c0b0a0515250206030c0304 65
    0x10080140d41103803d0395001e01c503941d00059070f030554061042c80b40201e201d0814140c20011104440b0f00080b5038654860b00050704c804c6240300d018403800350722000e280c00a010a8004040c03074141800080c0714000a4030071075210b50700110f102011500c2c1c0044180b460308141c5420407296945600800c090081c039030348403403030b40b030040300100c1c40d2821842624040d80c1c02c1240c001d160b9503010320280042042050f143c0200005208030030004240c0c8000b45100c0804002900c10420703c0b0101030f140300710260400310301c00c0190207209404018060b040b5440b141c00f4002003603103040c1c5203095600005075002050003908240d0305e071015100080051007141e1207081c200c1083e1106403500225840300c036240403c640c20030404101143d038030303510021900701c0c0356442c20b250cd0000703170141005500802e24040100e0f12044500c1c0c06150180065004020a9541c403000b01c0d10b08610310b1051190b030b038594005440481d8034400c000b80900d07461300000e501a00c0230341c0e20308200c004010107400454040394 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 899868893 1250 899867643 899867653
    0x1020607030c1d1809010204080d081324020f03100b0c060f1b030708160f20070f180e03040302130504031806110f07050a05010f031103010e09 63
    0x400244248903440a0400c2c40c3d40300e569010f40d0b00400e40c9000baa0b034807a1540215807001c0354814480740d0041c41e01900443c400140d0b243e2610910a0804c00141095018420403800b000a40c0c5860848030208a074400080303c07248600d040c1c0200c50440c01121240d00c144041084a6010076220046016081b50302d80c41d1380b150380c0c501120a9a01c1043c0760150107807c050081546001c80707109150b08040da0f50401000741882c485882c030650801c651040025107034000344a10003020311452010425141f0f07280181f0900840c1c0503180d504400c5c000c042010007000080d11414051000c80b029000c41c18210b1405540c88412113807000c0c400072007a11452811a514900d160000100c1e8212035003e403108841c0300c1c01440d094001c000041c025420b014540d019000650b40e1802004082e0840b511782058491041080d03e1400d083d604030315030303540c2c046a0284070940d14007080c0c03801c0304e6017460101d1103104044021006400e03408410301d0007817004000030034032005519101e445030a810040b58 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 899870143 1250 899868893 899868901
    0xc0617090307112b11010f03050c090114090607030503010e070504030f0b0a14090106080f2404050703140705040e0109030f08100f0e060f090903040e10180902010206 73
    0x1038480c407540500078000700c2d0720303141560346013095031080c8201100002184115814039000d2650650200402c070340e0002c0311010760480b0b60304102c401101045624080009103040707440c5109621681e00c5403818440d0f00192401c545208008031115014040c00d05034940c1c0040c600601290020300402c0070b01c07500040002c89207445403050b1000c90360003201c0441c1545058030344c101c0d0081d0141402004540b1402000900f6028a01c00750042c4031313110001885a140c07568050038000c40312240901c54006096a12002800c5013805e0707140f101200100701103844074a40946014400d90008002d60030034032029006402c0400e018003180e000783e805000071008456503a088510142008011030403403807a1800040c814031102e0b621941900d140500703244c03104022841034009510014100b100582044000d041004056006440c10754443e4514185034001d00d48900660044141036181400051b0380410b85035240c0c0028910301e890304d10540c141503501c202900101e4000c0e4050720031207002c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 899871393 1250 899870143 899870161
    0xa08010b090a0b18030f0328091802040504180201020d0509031b041515080708091c05040503010f09170f03070f0e0d23030405060f07150612170306060f03060a030c0617 74
    0x2e23411540392543d0b54880b031414500ca100b01110740340240c41549038280004107640d11548941d101c5c9819518002c0010b0689100091500341c81d0800041007110501100003680c030300140003017002c8002e00e03d2486880c02c902c0810018001e50036410605c440710300c1c0026032101d00034550400040c1503030701e008007695040019266841c1c01d842041507503020b20500c0703018070011a19807a220340d8900e4581c0c0b078541e60724002800d40780c00780c20712201c80b9545c039043d90401c0002d40303540150f2880c11040307a06140284040d240c0c9400020400000d00100c100451001c1d40f050003c50341007000100705400c5601a4103045034120320a4605170051402c00740040c0b0766100c004103950032207000901052515030b070304160007415004000c045800a003c0309d2340a0074442c0e140254009811419000300c80140d403407c25402c21a205a46d07a41001020410b00405446040407030302901154480103649407100008240b00318010f41c00904118403803000403540d50b40c03141c810149150b05403420409500e4107448 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 899872643 1250 899871393 899871457
    0x160b1806040b0402040b0d14030a0e0a05030a03120e0a0c0501020c0f1509180903031b0403020d02041a040905030c0123011203020f03030c0a08010b090a0b18030f03 72
    0x40c0900080b500003c0040c035050700320201205001e41000300b01e0700d40f90380e002c942d21190181c01c8203a8101103003010005034481d41c01e580308481210541000c13482c02011035181c2031003041c09010420440031402034040160450700c08422000115480303030405040804000c10103005080c014014403000d030307031903140c44600c0d00700721440140341500d0840d0310f48000a690b40318580c0301c1d82066100800022510042c000c0600c5000414051503a81c5480d06c04600881d14102c2c40400d000028003050000d622016400310301c0d141e041e1000240046c1c4114032400c100300840c0115402401d080c0417904000021001d03001d45a20356000b80030645e140407250500100032800b04019501850041207002281e8a040101c03d0190040d11004180c035068181036600c00c40d600d1301300001c00984520b0340c3c0d44c804030090044c080448002d051184210000d4401c0000c1c0c8074080256001085226030140c0151031142c0003e8004c0442d40200d130001241901c03a04401d2840741501c07044801c245070500b440003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 899873893 1250 899872643 899872651
    0xa0c0b01170718090f051b030a110918060a1401081f1521020a15230913050613020915130f0e1611070303080606160b1806 54
    0x341400324203140603c81801e40000c061851580c9840b295408240c864405508181c001ca010b408800d032a900c0340400044002103487c06035101c0c0210700040b81c1548800f8941a0701200c0100340d0381c8601600380440030407240b1a015a004500a02030a0155a030010300032010313805080290384ea882c0186038445080160250348401e1000c07014000e014642d120001e5100d80124205409485848500c00da10041c02c8140e41030341000241015032030920246401004801d030040d0301c0060210000740348020300c0580c680740582c003407102014040300f034082d501c09210240c8407a000701d00580c0043c1c098881550500c0c040c1c5490f000c6240300b20700c1c60080f0342540c1c80282240089201d240001720440d4440000da11b1800360303002010520848410043c402408644498403207401e010710906640c0c1c4044e11003000780842e8800d5503003003600100e140c80480360942401c03003141d521000421424400c814083e604038408407d148100041038062901544a00a400156100d82c400d003d58a5400359 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 899875143 1250 899873893 899873939
    0x71409010e0d0609050708030a02011a0114070614090d0e0a08060c0c0c150d0b1909020714071e080102030105090a0b060705010c09290d200a0c0b01 65
    0x1c90140e000303041c502d0724111a248540c80c00548844940c5400d03042c01d0450b0080c60080d00002005510300764240142c1d074840c2a603050b541c01d2100f0280c00070300400e50000d02c00400034030101d402820700455500115039014102e404034598a451048152244020101d4801040485c0007210315814040748030030a440d10100201495200c4100210007034010903003115032480343c5200201251100b1801d40092045d44070050f0b29607018883c00401d55041044040c003030f00024401d50440c6034085405400c032014203000694510b59810181c6005c2408108000a031140b440002201c00320401d05001820741070b01400400754071821030900381d10082c0b08459000c07078001d012824a1200794801e40c90341710018010fa2505000d50356407400d4508074410107002c00c0c3c9546040211841204039501021400d180480b1702d00561007106c0b40030300941c1030f664006a5240c001074040485d07900c01d01c1e0034a5642420585400820000408040502c8812901e914a0200000d01481120101d00f0304d02d030f002c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 899876393 1250 899875143 899875157
    0x10e1606021519090203210405040b04090b0f190510090608070e010510031806062301020a1419140714030a0605040219031121070311030c04020a050307140901 70
    0x43d0310030060300614a003039a0501486040c4145080d00842c0680c100c00b9101c3c005071698900030810040300e0000c0c440d14040d41c20481484002101701214a80c856600c02e10035800c0d884160b41d0700d008074928404c2140f203e01d4103042c07106489105c03124500f201c03030b10001031001d44d0303d4001940c0c450015204903200c0c50204001800701d480d150745125981c041e5841c000403030a9a200d00d036150f150070ad00040d50210360350f80060080c4554580c1200044400d450707401000d0303c110000035542d81e0f00ca42c020301000e2a50031310b010201018421860411512009141c001140f400d2204a62032445820090361144140000b03d03c980c80c0460000b6000083c05080681d6181d2501805000c0c02081203900c1a90200b4001120520011110255000328144070f01c2c50098410f0014070501071a8881c01c0d42d00c004074031074034200c001440c102600c0c2e100403546642000200841d01d0164480c550710f901c41d0001c964826030f190b115000e184a007405958000356144000c0c520000352150b17038800b034006510 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 899877643 1250 899876393 899876431
    0xf01052104050307080f280c060207020f1002100f14071110060b0c0c0d0f170d0c081509010302031018020a080312010b04050d060905010e16060215 65
    0x1840c5003030341c1c0700380204107aa1401d40340755507044080c0e000340030807415901c02184081e20860350907100a595018151040503000001300050706040d0f01c2070004204540003e214011511003100385481c140019010100017161340310065210300294100f000042d181c06c0d0200e4174100b05005014510105041140c99a2110f07003080ba181818190503180344d10515200348113010ba01c4c4039020080520041d500c0e2a5180b0744042420080001b1a03544105503d00041021602c11200364510580c801ca602c80024821034403c4418091444c01071845498008202c1c001900140303014452451700d103012180f0301c2c0900c1081204042800041d40550004103080890019984660030184011050703403000c203007035800141038002c2a040f00c0074a030001700b441e10000342c0540c8120f02402400c440c841c1014100300210340221009523014045d69110b00700e42c0e09216080d070295103800d00309400e0350610740940e941600f035100740b8841e10006125003656854541801d4205c80d000e40136000d41c0402e040c1c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 899878893 1250 899877643 899877697
    0x206010e09210a11060408030a0e010e062215090c051e040c0e12070806090304061b060b0d111f0519170f01090b0409030507150612110f0105 62
    0x72503d4400c09100301070000c2c0d40b4000c02080045c0c812441411450350f649098504082510700c86808409207a040501442e004180800c800d030b0300138020750090b0101408602c420012071550f000c0a00140aa0002030380800280e0b00b05c000c8035806130003035080f0559168140000c0740c9006120003401c101590303025929250541124128038810315040b4411460320000035030501004c014881c1540c1700b001c082003440c105204155001803264040c40c01c0c24178103003004c0d0139102d21165101c441440c1681190400c46c03d548246007108001d0886c0080c0891854403040090940c40490720076209941a207901304400c00404042015541e42e09007040a964100451043d00300c60400601c40d01140c0a101029482c4e94113100e0104081400640e51408544408540104003843c0c00340b03040c0018074005c2500403046540e007582c0030203001c0401c2148048200202046d400203c0119002c10b82c2c4418030044200c2940c059100b1030b12264000408001981c0d01e104a0f01d035540d641e03020312100d0710600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 899880143 1250 899878893 899878897
    0xa180b0a0c023d09030b1b13060302090906030d0c14032b0c02030a050304030e011215060206060904050d11030c010906091a070824100206010e0921 65
    0x380b002d0184654002c80e540321000d0f58000304440301107942400d8840c1c0c1d400603034100d0411120150f0400505150031621800e00c2140010101c101081d182d035081020100007200704d07503810203003800c8180c2d45515841c0080203076208076903181c419841c840100f00d00d0302c0c0c04203000341562525150300c407540525a503103040c0000f210103440800d0205000c550603030002c200711070700c034043c2d07000c041c0c01e000c1c80b00948181241e20007143c031400c551007800785043c86604141200d40040d01030a01c038000500c6880100c910340d0442103400c14150030306160403000e4500340a5203040d120300e03409403a13150340c84100380409003004841c0034001d45e20450358107031542e0045800c01d03554070201081e139203030007071000300709003074a100100232900e40f6134841454040c40324440083c20f564a04000300306042c14480f1005021640141c03001c0ca02c141d0b0031285203501c101c84c51818405000203070030041601203000019445940910464011100c04000034505480105641200b0140b810f03064081903c00c0e410f084140d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 899881393 1250 899880143 899880167
    0x406110106060f0e0a1d0f0702031908060f0d061a0105430506190b010f0315030b011701110403051203100b31081528020a180b0a 57
    0x34440f080c042003c5614072a81d1b414000f400740d6030703c1e490900c890800c5003140018500c00c11500f00744140e03217000042c0081402d00c0a40d9240c40d24240e203901c00000d960081204105910070301d2a15141d0421080da00a0036103c00d00c48450050440410015507052090340082000341c07025041d0354004900040c00f100681c440035580c0d46c07c812100340300712134040160405444139031000c400c10500311101010518840070040041c044c03010382c07400281529018900450a06856600500c6810340b001107010040d900501142031a5030348003a50301100b102c0c224102515402c0255105d02054644110740803a81e0040042c59042c0e0b81290480d502d400240c156010280c0c000d00002d40c412000e4040c1034184901c0c5c2c00314150980f81080c415003001601c400000608a0344010004030501180060b4202c4901102240035595290300c64480d9580081e80e5282001d215071045c075540080d8090460a00c903a11150844036100d960001d411320310388245880c007003080052200d1301c2c0c403440c0c0100e08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 899882643 1250 899881393 899881399
    0x9320405060709030b01090e011401140321090f010e15070b0c070201050403110409142a2b02100815011d1e03100b0103051003080a0c0f0c0b0406110106060f0e 70
    0x412800d00f079180c4081e0400f030340045101a04204159030320300c2e05000c60380917073b002c4a02d03034403a03098010083d4015004501c101c92041d440000f65404a90042c94483d20340d0100a08600c10400c9001c00d141c102c0d0803071207003500c4840001c0001041c002910703080b034090345e405856081c2403034519510344080201e012141a041500c4200e03200c0000c600b40700744100d03588203601078404080c0c4044060f00d100c00841c5169250080c000b1501c100303131140e034007550485c41001d803070040c107840200003006059003404009400014641f201e0502591100381980101c00e40d488920061131054011141082410070003102e0710991105242035140001c142e40d0039091100c1900130301c400300000a4104080e0300d100e46445234407030440740707413641e454071500d6400400a00c494011390705503210303c54523019010001d000c0c064802c0307818007885816002014510761100c0e1500156440c6e40030291113401c1841030f0b1005c42c0b81006102c40c2e02d0700600610303090f90385903aa220000203030604c04032003c075480840550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 899883893 1250 899882643 899882651
    0x108030a0804081b0d0302040602010f1e150518180607021005041514011404140615040902040b071106070506041e0c08070f080f0709320405060709030b01090e01 71
    0x300704d490500c00d00d0007003859078034010384031480e10781c029094429030707994854480d280c0394002d80f8141e000100c3c0c10907440c01410000b200410b02c200000b28510680080d41e0120b40140c111782c000320008181840340081c04240d4640e0b40c0500d20140d920388040e00c580d0b0158104003e41c00b82c01d0300991019501070f000f44113020034040448260070442c1c1240c1c0c03030520100c1d924001840001005040c0c0301055800341d9003000801600b00d1003c0740c03050080c2171a0310a02d41e04101080d0091000c05503006490300000c01c540e950b03603444106009901c040700881e004060315201248a250081c1501c610030780000203042580d9540e40e03403040c0c044070320003c001080340c09142840450003104601c0040d01004004000341d50a000480018150030f80c082c401641c807010302c2c0c100c02c020116205040b13603510100451301420b0b400e488019200306c83c4010f109421030300c2d0410502c018028825004034020000c2d1201902c0d910b604403100195400007609102007140100414030b200e6101010256258000003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 899885143 1250 899883893 899883937
    0x120f13030b0703060e010b0708040311010e12012403150e120d0603110a08030a080603032b1103100b0c010609150303030c05090d0305070204060e0c040e0108030a080408 74
    0x40081d1000380c5040780000d44c0c500007400390309110907560703014101c6801500d06000c80d55491303000c00e10503408020030b1030704010741002041e4010414415000b00c024000545540c0322040180201b210700305624000704040b00f21002070082c0b10f81e520903240c01c110000c1d28602d104540c180a080100071001240c0700e20000c25010420010180200c0360500b035021484c41c0c55810030018a99003c0000c61144c0c1c1e84910401807080000308442502c055801c1c000c8290362039200280c114050000d10380140c1e507940302000c1d12030010300809900341021000130010b1040c1c0420711040c5000440b04a8807041c0c9141c07040c0b180f610028041d10006141000200f241a1a071f00b0840c180c82164412a4141ea00140b081c420150540070340d40721000780d0300d061350410351890000303001104000c4000d428081c000072107100b951202d80294000d0044186003444608002e1141c0440e544103110390440f410403540042030b01c0c0c07004403c951200c00b695540c00503a03150383d21098101d500400a000700c402803000f0364 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 899886393 1250 899885143 899885153
    0xb0c123907120c060804031e180f080601051c17070615080f0c06090f0f04020d05040201110109031407061d0d02010e1209011110060608040b010501030e0d050307021e010f0e120f1303 80
    0x20000303042c40403404401145080c8bd000d19150301030304035900c41d00b04c21004400a100004140c100706400c000c1c41044940622045000d44c45109000780ca190b09000180825240d8140c82c04211096801220341040315016500e481d62085045c403640107004001d1005540341c40300400004080042c903001400e030000000800300d070300a20030020031310f07100c0042009640e00511180b00700c01180c002401410701c913036801401d80b51942100d908948001c5514020b000441d0f220344a1082c00e00d103026000c807906500950340b892840b40900c0151300340103520070500e0001c42c0c40350034488640c0704542001c0b1040015513881507030708100d40d458403601042241c01c40b118043d450050480f501c40c42c495040500f80903203030b020141c004a0600d07040c030750300100c0801d0000380c456064043d4a0126126145c1c100c2c102d08054000701d2080000661541101e030984042d4403414004070450030402c0a44828040c0c2500d40d01042c0191106601c180100741940002c88001d00400700c0300c812550b00c45d038481da64 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 899887643 1250 899886393 899886437
    0x61215030609020f0a030512031306150e010b0a050d020706021c060905011d1f0504110d0e0d091e030b010b0c123907120c060804031e 59
    0x42507070100d8940c2400c805506150319940800081900c0500c040c0e419515650b90700c078038015052501d00c40c000b000480c01c040e507030580c2505541c411410f100e050b50100c103429500400d4000d582c00d12044c003000048880c5440704403000385019845e89424145901d411200a4002150a8820381c4d000c010300c0c20003855600c5c113100c4010301d03030780c000880c1810b01c19031b80200c9105070000d460444001000b24196842c24801c550b01aa050040c0780e0030101c052204800500c49610070780d00a030501450398614031030140980b0030307a44202e4080180300c0c007880180d5074038141c3d06100400301d010404203024038100d58240c0d52501d1030503054880e640d55207565148000340d099224888102c00465007030101e81c0c062044484040c040b10b4002e0414000c080b0f0b554010607060110310740f4044140c02107494144c01030f14a10250415000d0745c40d82c5a03950800f00f20701503080000c98030600e041c0c002240301c0f406000030900458056903408044000e50004080e0070204005076024030198006182d200341c0c41883e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 899888893 1250 899887643 899887649
    0x3030705060f06041107230d02010c17161803150b040b012c2409180f04030c30030e0325031e090e0f0709061215 50
    0x4014009460039016503005030380080e000e10320581c103017802c814064181c0010b8441e030b01d40200c48400038491804041444450007124134196000c0c03d5507000d8241e8041d8072035035001d002c5440702201d4220040102d01c00940031100317140892580e51381100e08a1290700c891032008034460410f070b0269180e44484003080d1504e910642503644070b000c0b02c5240d04017402001204282801c0010030490030390403540402c910070302900f07201403800c0285802552008164a4111103605104803884c02010b110300141e8081c0c10400d0003003d511031103440250300204040c0c400c44000101c0702d019100e0766812144102c0c0550244c50601403c010070941520f0401c40007101c3c48016502c0d20301404a0b800502616280c5144a1454001348035031890f41d03040e0b00c1d112400e5840354403100d101549603d0140c455104600d200c03803001d00c19180710401c594125a140080d00c4001001d0046035603a01d0b04042018411556030b4000741c2614400c003d034500405411082e07558065000c640c64030100400320180400794 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 899890143 1250 899888893 899888903
    0x70506010923042d080d02130b0f07020603040606081b01030e01060806061c0b010e09160506120403031b03150e010b0f1c110c10020a021005060f030307 67
    0x2031020141d2031181c075581600000598510002c40c5010b032643c01d844a0b44040007620b10000488918061140b0566190307481d0380078034400e40f1048400003050003134207d22840c5a20020544021480704084801c0c0e8003108419881285880c5039642840426040038000b1151141c03a000c0114201d0001d02c00d1108149440004003103c0d1601c5000405449042900703407010791401206101000021484544c04181038916542404405850751005c82040348003030050b650300e1001040d2520180101405440c0f000201d6404000390f084407100703070301503106296001d034041001036100a02c2e00a07980d8802e00a040001d410b4103136218013101c50804100d03060001e0794505c0004000400301c01201c02500500020f0052503041034045103182c802c0745580e800c07006010444240241c0346503100f5441c02e00281e41480f1301e03002c0c00341c00d001c990415403407220309006103071040001e5201032080c0d0b01100265030042a130008042c103500e00030072010309095004040c0c540c000405840410040019612070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 899891393 1250 899890143 899890151
    0x15030c07151b02011103010f0b0c0709020f0403050d0e0a05090a110426060f04030c05010b060d0209040b100e0d02030a02030a050a031107030c140d0c0602070f0603140a0506060705060109 82
    0x15140c020308440c4100c00101d0510010303c0180b222300c000c1566241070b0380c8401c460a60b40d88251180f68a484415484040d6060002841c0302d5038031403000107002101d101d1022104051a04201501c2c0500d20082c110f82040303c0050401c2146448106560010080c400010300e0b107803088104c0945a1007a084100a40d2644820148001c545100d0344114981c0001500550600c1e10881082d00c00c00351001d820001c0003160b0b003080c40001e503c10010580003d00c040e603515540c14401020b0740241c0481d0744179a00d40f40e001c0401c6d0030904021b09134020103541b1680159001020042d06801103401aa010f100c0c800c7c841d001600c08004076490b40b40901c00901e0060400c0c94000c0190158140900d04e0b900308160410000c0e1080c003000081e81c0d03424010800c40040403020030700d042e0041c40050801c510070100010450f4000c9649810ba85108205802554980c9004d8040c1c2c1c1403102130307070114904400080c05840c01980032642041008100f646480c0036511050300e0072800781c11840c1204e9507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 899892643 1250 899891393 899891441
    0x50a0905030606150306120a0c060906020c030c040f060e2406040605090d0618030c152a200304050307091812091203031a15030c0715 59
    0x420a4000100411002004149040300202d403680245007075031003400d1404400b1030601d9842140c0790072202030010844915810034103080c4c0082600e0b100b40c40c00300d403581c40d0102d0004e101281c060340484000d401800f45610500510004020b0700c001c44140942d501c00c04a041880020018001e001c0c0380903a02e590340407003500c03040c55034150348403502c20b03181080108490307900182036480309901124406d07866001810700300003801070088149000941071848104060300000b801f022140224051074914203108890000c50b4182203420040030550414590b00c101281e102c00c1c01380c0c805280004c050106107824403c4a009080c030888950008142407080c0e00b420403151004003c1890248025505130098203806080301c08003401404035400c03e010a9409000c0c90b40c01020900c0740c1213407440300b07420010010100340314000e04144c0707822039507440c61404812401d226042e55242c0351450716500665412940807600c1221822044111403864650038414051074440c2e409480111490b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 899893893 1250 899892643 899892647
    0xb060f2d0a0503210f0a081f0303090902160803040305180919090602190909050f0c09270a0b0301110a020723030706050306040c03060810110903010203100810060803030f0403050c070303050a 84
    0x8499403101c88e004180e03008101095214094108460f600c203001030b03449000e03010500301d5003050130780502414000024401050f600c200100300b0b0803c0e20040d411080d0043c010080802e00a462540352546440070380350200303c07160b10a000840c0710707072001460403600140401c0c1d03807401740d1101c1d80480d01d4032108000154860081c41ea00441c040c45400b842c0c500303c2c8240c800e0f40030303140c4140c3c000c0e07900d4150740d2141e2181403c101c602401c1012a01481e10b40100600041d01c110f1310454065400c1010741c04412074107100740c41d0100701e190007421103181000c541c240d610004c8640503050351411040c81c452078409005074005482c07203950b41c0f030740d80c540001440181c54004d100e03081014034180003041440e002240c05e00a501d5240c0c2d0104460300006000f42c13450140f011580c7d41544000309001e050040031241404903100401920103802c18168268200c44480c410552950010030020342c0303584044c007010750b010384a414810700f4020440c50407440c00c046900102d0204100082c0313022895 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 899895143 1250 899893893 899893921
    0xe0312010f051201150614130b0912010e0a03050c2b140915160204050f041e0b040b1b0a09050306011707030b060f2d0a0503210f0a08 59
    0xc088802840b820b805c1516a165541c9248035040c101704803043c150f04003c813030070100c90040c00c41586180080d52200d41c02c00f8141d05c14500507104491441a070100c290040c00361841e404040f070040c094000b6180c405891603030200c1c03105e2000740203044200c103c51114080000c00310903c0741c41c084612001010180141c2c0381810758105024042c48400b0241c0c0e00c29440b400c051200011250312911f541031000c2d210407800030003d51040c104400c01c4409020300004c02c1c030590050640c0b045c25480c214010b440407080540141c400001d00000070080341c16146c036560800350b40d28480b020502c070960f025425400182250340020028181048145420003025014000f021400c0701080302c5541d00f00e80d038242a110080442d619680010403565580b55664407000001c0c050320522441e00040c407516840048c0500072000400d401c010903030512000c20006d944010700102501c80ca030f8000c49010200003034405812040820543d400d0b03203c850041c244551064880c0f49040c105040601c40b01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 899896393 1250 899895143 899895169
    0x40e1213061e0f0e030a081309050f151302030c030708060105090102101d030c030301060f0801030c03112818050c041e151205090705130e0312010f05 66
    0x148554540c0742e00701030050b450707a07a46103040c24019141d0011003526403c1c41020f00d0b60745401490417001c2800700c2c0e54020140f80604020f884044c13600c428070003007210700641d2a15201c0b5100000148003920042c46142d01d094020009041c26600350014801d980c4210741c2e840f001240030040c01007007508601030380e030042c3c800d0030224246000d03140000c1d6075080c52400001c455854456808034050350a084284900248040c0c81c0c0da00c840034013855483c1d0084c4290400651540e0409091a100e2086c060585e40d01100442003a803960303e408001040700480035038007400000c4055101c0380d151407500420450811511015407800081c0642c0700902c41c10303601e0141c02c1c00204820418820212803d0311209840389400c20440303104004608a1500580c20340408030303200ca082c983d040180c02c0c24440041205018682e1107003611500c070380d0709211306170300b000ca0b4040c0401c101c2500d810445000100e041220b007007907480044404071010a80c40110b003e25820000e00407428a6144000300c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 899897643 1250 899896393 899896397
    0x2040312030e030d091b0905070906021b0621250c0b0612120711040f09051506010309080310091107050a2603071d1914040e121306 58
    0x90510300d0b900680c482c42013554030703a81a135950303030184100048405510903114002044c4030b0003a0b203490300840140000d848120109041d4003002039820710005800c840220f41800c0300c1400441c0d00c1c00c4c000341c2e420003c540741c203401d04c0614070110a440040003920a80d2448895607a841c101180f40008803403540c1084200082c03144000302140c030390604580c100200f40c540d50b1561204020141c127144501e1b542c041201c0703001400000b40a07102495040210040368204010928a4000d100b240c08080008100d608904c100b42c41461000384c00ca684000103045c0030803201e120b03035140d01c074070780c812030b070a41608003910310600413020640302c1c1180d1055036200003407a00d503c0b82c565076581c0c10026402050b219030a41c02c00164515041e804480c40c1140b50640c0d2242002ca5000c4c4c4a0044002e107107604107030741041c200f4246054010070301c042a5031021441000d08140c01c0a0442c50010b50054000342c613002c07940280101040503445580c9014030380c40d10b9071000301807080720f0341607903102d441 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 899898893 1250 899897643 899897651
    0x180b010f0609030f05070308070b09011a011d01110d03020c0601050f060712020c0d11011815080a090b1303090f1401030902030a200103060812070f11130204031203 72
    0x210311500003202e002500e410002e01c084406a500d0134030701e404100d4100605181c00400c54804110134000d66902030295503000340440102003051600700800e03203200c5800101821103210306118a110780c0c000490040c034058520011949071940303040780300c41c101d900180c1c1c00111488040340030b20045001d0102210000c5c292518500003550500801c8806401c44103404c40400c03500b4000c101d009100003003d4501e00520881c3c1c00d2448040300d039a0b51040c00304000c4810b0a44400325648004150b0340744a104058605243d42c04441c1720400508040c5041d556009602c0490000d440451042920640c04184000c3ca45030051284100d9440015a4684500d050000c034050060b4504404428a400907041a0703500001c1c0c1b42810415000e04025040d41c40076011111a080a000480083c0c80078003d007a1b03a4140196513560700012010442c2050055000041c004895020040d002c0c070104100140380c040044e00c5020f9181c022054664000707010010080c80c0020001c0c1c242846c18204 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 899900143 1250 899898893 899898899
    0x80a0204080a0215070f14010b150d110405120309010f020a0f0206090d0c0e15010c0203060c0a1103030907170102030601020d1206081e0106120c030201050f0d180b010f 74
    0x180c0c1d02c9071588802445901c2d6885141308a4035210150b4041d2504000140b83c0400c2070700b0700100c103800702c42c0400000d500b040c800403010700382038003c00782c080800e060310352400741e4441207000100740c1c550080c1c0551030108000a01c5540d00c010048a68440d0809965a821290009065503000d81c80180c19034011031940d03004140103044a5203070640503220256611041d070001101100840f000924031440020085140c194441615100d6004040b014842c00303040c03801941e50180000000794594030800c00102c24200c10070181692100ba070508120303140c105070a19003982c00881d01001940d102c540308112000d0010036000b03035500303642d008614508140000035200d0109120950500410030101c210315261940b0030801010120700b541d13400c2240503da880201c01050f14921150f0801e20041085885070340e0082e21690701409100049107160b0042d5190703040000b04504242d03007444540e0f00d4040d00e010b180304031960030841d81e800300c5043c58840743e0400d042e0400300700c50030b091504ac = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 899901393 1250 899900143 899900159
    0x150515010c0b0a0c0504031b0806100e01120830060604180c1413180c020d0c0f0b0f0f160507021203040909031e0f0807080a0e0d0c03080a0204 63
    0x14a410060b040f5000c1001e030000182500d283c403072544010001c6040034400c1125045840b00c0000399800982a075001d51940900711a981815000d0340904118a00040100000012010800a1103954254140b42042c4807104010b440e45030126040c884128482134000e68480c1100d81c004011078008e42020305280c8418211038184060720f0344580c0c1d0701c544420300307402003030000002403601480e01e0781c500d42c0461070380310840c00e4401d00c00b280c0d03401010325410044d18096000da0f05c801c0c0d070003017003140c000e84021202c021030b4a1041d0f840e640310560f41004180680308075440340d65105207801c2541402c160704c0c501407030010643e120300703038180c128142400d134818115074215804944a501041006032401d081d4481c2e90b00090b13543d80791072907001c200f60b0002c0309205050300b134030072a049601883d0025220700d4030a060310303030004003580001050f043c0580711b45500105680d100082d00310405516600d000707104007802c008605840c541300f08150344085503aa120390708510550500b8540011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 899902643 1250 899901393 899901413
    0x8060a0207110907020c03120d0b100f0c060e07030605040201021b100e03010615111c0e040f0b090a0f06051e10051c0f06080312041509150515010c 65
    0x10b40d44030b904440c001c5941c0714400c00045000900003802c0e200d91000708400c0003101d5204e640440c001904002d402c80840c6070082c1d0307110b050381160b00d03008a12440724000711200318645c101203072425135511518194640403c0030b4005144210000501c60400b800064517003805003c18140c00402d174001202c40d41c03900289410f103400907081a90f24a03480a001034058034240d0888044003181c200100300d5640e200348112103802c4ca0400703968030081c50110810744000150710703a1000c0348202d00e181107a8205a849003800e003105210010b0884403550000d00d290034147c038100c0407030f0f868080b0194852207038802e4100034482220007044442418142000300c49402040c0791160b50741b4030588441a018204aa9056071207500c3c1042c50420319503180020a51145503143c65490321001050780034000088880c4200a1005088103079033300d0350b03020040d03990056403402c1151252011800030312138494264070412001000308942c81d00005403545280e03941075843c1040780b40d0841401040c41841 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 899903893 1250 899902643 899902673
    0x21e040f0501030f051b0d230f010e0f1b040305011401030c05040e07090e0c030613030201110f0315131a1c0b0a09021f050d150501050d050a091b08060a0207 69
    0x5141912211628003210040c82232902130303021182c0d9408005c045130301104160b403044110b03d81040d0280d80303480010079004007c4400704600e66510010501d020000000c490000841e500c6203482c29489558a0313003501e00c806800700000c1400380041c410440300000800241c0400e40b01048101c41c00c801196a4414034030030388001039912402c084118400b440305000d035510243c1100c103e400e249814425202841100341d005528200c404103041c41d900e400ca890100d22031350a181103481c0c1c9240040070458051102e548001c14600e0200030360a14020f00001070303030064400f00c40c001c608083c825800030005c6440c0050344404444000911400307074850b00400043c00000d4005d80c030b840860240d400300c001001c4c404100041c0d0f00e910540c044002c0203040203208007400354000c44152102c040200303014081c0811804d1104443c07402c150b600190b40242d1055000c80da62150ba00c9184082100e244100419045800306010041081050681010414404600e440fa407034403801d15a000c0c4003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 899905143 1250 899903893 899903941
    0x40e011a06030c070c08030c151b1b06010906060215040b07050c0102090a0b0a1e0509060a02070e04050304030318050604030f020102100c05180603010302060d021e040f0501030f05 79
    0x44040f440c1d8022001c15118100e91041d034919406803a60843c0743d480d000041038022600c506044002440c00c141c2e8854021100001d5811000304403610702912500320b0700c00402e04004202e41d07200c03c0311041105a00038a402400010041c0c102032000303040a00f200020040710710000180000100176000301c0740e000140740761142c0c5038045401c0c2280a4821040303107607031200d080900420040120340040080f40c0c078544070000c250303200e0045031044000c0440d690740418000d0140c0c0c601410000e008200718201841610000c0303488400946001e10700380d40c160361503440840d05204041d0030150a0650107240d501c80001a0b00e06800036001e40300d5804000c0400443c1c136441004c5900811010006030034410050103003514034000103182d5000040355103111803c40c940001d840c18003101301c034140c80d00504024604403a55806902941c030224107114a110300005101c0030f0306e044800381011304003028600548514060004058810f120040b0071241c0c034010074088025000504848058108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 899906393 1250 899905143 899905147
    0xf06170f1f09021c0c14040e0705010302030c120117070608091b0427151103040602032d1006050301150e1504080106030c060c02012a12020c040e011a06 67
    0x9840410244c01c603904d0078104001034003605904008100301c04401381ca40c60078940603015500400c100c10f40342e0b40030b407030483c80e00141001c3c403680d4402d070011a40148007288007480e04840c186052084074090380303e480744003000c0b42003500030030003889000002c1440c1d01e00700e5503e0408602c420f49909803104400c0d4548010154054203403203d070003048000c08400116102504210300507120700c0700c0c48000300d841490305010340c000715030184100120440c0765081c46095548954911000394400b4040784840300c062100c001648210383e003244454591041c5864a07401d040003074844001e00768210806100041c0014080600042c0c0c120308102040e240581440007928040303078404501540d01c4c49006c1c400540403a500380b0542200c02260300c0b4411212134280c0d20b02007101d94955462009002030080000d501210404d401650001000c0c03203101280c3c01b5082e50350300c1902441d03588241c050b070440804d0802034035141c0300b005586200f140c02484000d0001182d41c0c0e160141c640304a11420300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 899907643 1250 899906393 899906411
    0x90a0e0a0609021b010c03020f0720120d09140904020d0c0902030c070c05030d050301050d0611120603010c02070303081807050a090510140306060f040f06170f1f 71
    0x6070040002480c540404540d120145400741d1007403003030041c0b00c8800e5030a00f510310a40a1081c82200c00070081c241045003002055540c0c1d40c04180c400040c156800f416044442c407681d10b014484c030000d8070100040c030100c1e810aa02411100b000da00140014918038291f0b04561601040181d00981c1190728100d60f9a146ca040308442801d90030045900d40b010042020710711a01c0c00500031140158005c412040da25001c0543d5507140f0341c50302c00028024401003005040460022040e1032007114042242804c40300200d07800d030400c42840c42040250303c140b0844c2c2c14288070384c1c1783c00102c2d4030240c13035102c0c110303100034145600107410040171550751210305100b102c06102c0340c406400010034441140380d1751162030018000694468901d00102040020402c083c0d860700307000064060003030106aa075000402140c540440c10701070b000742d16400308003096190741c41030002502d6030101012480c9a9100b1151601d1000d418020080c0d0190b00c007456003061202206000f82c14020000c1050b0003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 899908893 1250 899907643 899907661
    0x201050901051207021f110912071d250e090612060103060606140a09030b100e041518051b24040501020d0f17072001061a090a0e 57
    0x1040c2108030000a080c0d209001c013040c0d01040314461080c5c0c40038480c10507143c2c0155034003240c0c00141000b40e03000040044403c18185140242460040001621000c69448014002e90007030b000b04150615240020403c0400301003045010b90718003064407400c0b03080d00d00c0c0b0240a00c50000d134422710030780078100082c906964030f6140248c44403075501038540307a5940303207002c1700903140c180030f60f5000ca0039085801c1c0005800100762444001641d0321102441e00e1a22040c01050025020200300071210740f000c0b901d130506034441405581714028980c0d0a24000c0068000c4400c5100c070514454519080301001c00c0700010000c0801480e4420880942a15000100c071001039000590b90542c1f4011800d0080d4504000743c02200c00a80035642030f070043d01e804480c2c00848009040210f040b400d00501c68502300040c1c00d41c0244141400091083d0304420b50741140a401400d54560391502402d020b0303c084404020342c050083d030720071401d01158400040018801d0b00451000d50341c0c040005045e00c1d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 899910143 1250 899908893 899908897
    0x507020f03030904021c06080a0506130302010b06160209010b13030b101502070801060602150109020307030e162309070f0302090d0308060f1927062c0103030903020105090105 77
    0x4440100115500c81c2541c0d145854902c1031820f5150303947c9003450005105e440490100b41c40f036800400b9000a0307464210036601c05940240a60456594003940c180c25280e540040c0254542004c0c2480705c00c40520410026910503004070b03040070028408102e5480d028203a01d42540c0e446641c5440c1a03aa070030303d000301a442607005117640034102d1103082c076003070700400c0810940700484000d00c856501e03900d050340c0e2000d40500340d070203425081d00104070340046540910b400c22000d00c1d022400c0030240c10810310701400c0c410024006070320180d041104200c25001c62001c0451542410ad4400e002d00010f241d074103000301440e0070701c00b4255500d048030707101750b044600b805401444030080c1d041e6410001c101c5102160071a0082c046110803004038039101c900a01e8107100250000001406c1c8411025113034050540c14121400a01e070118982c07070b241c016000508542030b07030285a441e80c2c00701c00340c81c00c1c1d81d804003100805a0303500620100303500070340803010b0340c1c0c0a090090750b440d00880100c07158 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 899911393 1250 899910143 899910157
    0xc09140f0402030a090515090a110315040b010602150606040605130f03080d0501060e0f0f0604170309030d09030803060603250e102606040e060a020306010f08070507020f0303 77
    0xd02c000200300c0800b000f940201e40140c02036044400303040f40460000510441550a804650b1201c1c052100140081040281807a0081d00342c44e151070404011801d8840c0a46d006ca856145210060001c19410000c20141034001c2d10194070604099020622031311803030140340d0802c4000651122042400d8000c44000c1814044084038030b80d40c0d05203c1c805800c0031001403459809d11000041c070910a5140600d0491300074107419003094034500b084100c400c4041e0140c8c0100003072100107407000c0c641071004c074501005000366641c0c6070311004242c10000c15040301000d01144150510100758a00103590344941d0940e04076681380c5070b4114039090406010100e8600d5989124be90780c055030711080301e284e40d103003d0f030300745074403000150003a0b41c1e01109800c40c04041c4404032001d5450511215000d400c41806400010303410080000c541c24040215440010183c0000c244105542d00c0028a43c02c10030320701e460070050820181c014480c0c4540e00c80a403051012104148441e9420b01c116008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 899912643 1250 899911393 899911399
    0x31008060c0d0b300c060a0201050603120313081309020d0c0801090501120b13050601030b040b0714040504091506090c1d031c0203040e0f060909010c09140f 69
    0x25107490341018040d40c0c401e401c4809464103102c0301550350b0030550b0103900020410404a243d906000b60020440d200890b1150410321644102c2051a00c9180c001d105000710340e40082682d103052400e051801103041c0b44020320800c01c03c2089024401d500700d00701c0160b80840e08668800c4503120804420b400f40d001807500510000d074056000080c2c1d808201c03170704119110f80185030f030707943c0003103044070f41c2449407c410220107004000022220b03064560300202c82000c1c06034440c61501d580385000f5013600b081316010781f0300f414003003482003075004180e00c80d84a240c201240d05d21052030000502941c420306015544a003070f854200070032441080b02c4c940c088407082024550b82c1c2c111a0117400c27149010070200d400203040c08401020030701048041240a0001e010644007254540303554000e041905003140010b00010a045080c1c01d0400d0007055001c0c5074201c0342c105081082884000507103c0c03440d50b89010444905c91b03810240b9001111405c28a580b00c9080305000316510525401090b54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 899913893 1250 899912643 899912653
    0xb1303020f16060e010801080c0d171911010e031e0c0d02030301051207140d1a04120305060303270303071a0a181a0c0c0109031707030b15031008 64
    0x58200821400042103c5542d510b01032081043c0b8015100d00d00280104241034000d48000c099605000c80001c1405202d85d0303a000008100c0c80741d04000b03820400f1940c09a11040c144c96005680c0308000010014091000708044182e03075001039035a201e14503454407a12031040c00c0303989413142c43c0c3c283c4600b012003278142c92620540e40d03002920f03039109014203403180c80c6070b40c1021100e031300005c1e800c801c0e00c100b0840c0c6c0c02886110000c00c2408104800120b41e14070342c0d58400b40d0854051020640106d00ca840d4185040c54803540c094152100104801d00951050090300056040c0319000074507851035030004800b06803a0004607095115800c0050032110021581944080c280005a0b11641140804101c0130000c6c0c1d00c00138a00440c801b0240103414140b0b04407103010142e220054010f02a103601900d000c0d819a040c03801c0d1410150103801081c01403c1c0000301e1601111619400b5803613250401000160304001307010b80078403c00200a10310044000740c02416010320b00000740014504071a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 899915143 1250 899913893 899913913
    0x180629040b0622050a0611150c0708180405010603140402120f070f0807080102040b0a050a03180b150402090a0b031009092306220507030624120b1303020f 68
    0xe95a6203544c42402d000b405400c00c006a41031041802204007401580038040584a41c078a01c600d9800150010325200420000c03100055192801003564000701d02e110310899900b0b03002c000c02c0f5281640600145400c00c0201c142044031465141c3c1e2033581102d00c590040c0101208601e1719400601041152158440c0803c2c05a607582c021b000319084141290070785602c44004030b0907801244554881c441302480183d900d540500701a2094400038580043c0c6a091000d01c00840c600b02241a20704420354018082d80c180040da01d01050201554154505560240824103003011031148405003071005c408034400c10505403601c5d0007031280b0f2000707010700403c40c100348000c004500034001d09803025a154910f00384000c51580d00c502c030b92403200c000401540118891620b000041126180a0b0102c04000100b403486558060121850007000c0e444560320401e898810b241c000385001c03400c2c1d4801a002602c45e50002d5440081310380c03021560a058542a840c2140580c003480c02070140e0b26001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 899916393 1250 899915143 899915197
    0x15150a081317181e0123030f010e100e0106140c030a05030906090c0a1a13080601142d12060f06010305070806010207030303110d180629040b06 63
    0x2914400104180070741c031140140c010003030080d03803152107060107811044c0d8083c0550f00600d00001440d003a803440541c1201542c00d186481d40c4110b0b460042d80010030014130648101c0d041655004c0340450f40300400c5810040c8000030246d051142104000c05500b103501c000a1760320565007107100180440340c0701c064040015000b5007040b110350340180300320b17000110700c62400180c7d40e010f0703400a0684c12102d0f062500126a0318070641e14500e20340410012003074180c8000b8401001400641d010b045e0a50410700d00f07840da05111000140f142c2101802c4180d038a0b20682e40144104224842c9482e011003203011030702d1202039400b002414043c4104008180036454401481504240d80c100090780c0c0f1a00300b544c85240c1592071500580c0702d000d003807000900a50140303a4084031200558140b003000c40c444019102404a100c8035032003d06200800c2003030341d010f001000c2c007030800011003c5012801a9040d451300e01a0503224503100d43d11003245032145011a000c04c040c848004180b034003241c3c26 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 899917643 1250 899916393 899916397
    0x31c0507030612380601030917030901091b0806180c1c17070506060d03020c040908040e2a16020405070e180601050a0503060307050d03020615150a081317 68
    0x112480c0316140e48141c04c402c13000a00140e41381c1d000d1141c1201d1502c0c0d1000460091429140c1180d80b0203079195850351200001c409144900072303980000c203140029142882c2c56040c08010750031140002d6500348a8654007003401a440725118803050503a860319003000d440e1180030010250442c144400800451800e0384560301e20a0051302d44d0b03509034450315a668058810010064078680124010800615007110030b110042c1c064070440302c5541c01900001e04560140d1000c0320070250010b002c214006440750655800040c8800500141044016000e5001c62181c5031030900480010548071b1170803040c1c9049246038000d40200802d141421002d8445a8101d10360f0f0b104045000320100480c1001c0090340c0315801c1a540d0038201841407000f1764013034102030041d590600840c5804112600c4260741420060302982c000d0840d410500c0e20340040440c0e40807143e01417124240b0202585296070204c1d040c1c042c07e0b18010026076520080711040345051600107080241c0c9050190303003c280240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 899918893 1250 899917643 899917673
    0x17041d0907080a080f0d0905100209030c04060f06080c0408010513021c020604121505070201240303020a080304061811040e01060e0f040807051504060e031c0507030612 74
    0x801c40707003002c0d101d502e2542c1d03a50380c1160050041c24204941030040702d20700050030481c0c8460038003142004103961100c1c00c00d540048542070107a800315988000d0310701000f1205900c841590208074650500000c5d200810780f6001e50414000380340c011401c034180000444001389159002008181000c050708201c0303806000e001da100b11071000b00200842c282402145150307600030f10685c0360501e0004d42c0c030000307130300010251513031460031104040708015030040c288a18203907400052408032a401190602030035005c00d1805140945061001a40010f011001e2a4010328015101d540742e240c440050004044001c1c80942030010a1040100380f084000b8000b100721014440c42c440318031100d00300c5000784202c1c158014000040b0b13200349040b00341c0980080c001c451291410768180c0b2100d2030440c131481c0a481c940c000350100024800705100d007142408041c400340d4a403540034103964448005d061000e1003290756035004202d425009a120a0040005d03020010843c0c080d800c1c040440e0030b01d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 899920143 1250 899918893 899918911
    0x110d0305011518050405090307061a0901230d2901080706180b0703020307050d0e0411040e16020c0a06050c010605150441030d02030a02030717041d 65
    0x200da61940f801019880440d09462030811405441e0808103c0a48800380c410310b0103010070030860020034024020640b014800340d140a074070360002414083e8401059101144034810b4514281e900e4441e01718040300081c04581a984c4c2c070045042400e00310381e061010740044102c861220105054078103640e030480f15010299100c043e40c9030f4041e07030702180c0e5a0b00d0602105c2005018082001d0050280510701e000c0d10481e41041413a6882600d4041c020f11050049030800924000b1440c0c1400382c041c90f204420000e1342091f107801a20302ca2141c001d03000700d074054495501e050b200b40c800c00c82008040b000501c001071031030b980c8101900d19030203001c60040729420510b0207e490b040c5801101c82d00700c0380d035600c02d142a20b0001c0c4001e05070019185250a400b0040c220300c0c2d0250420031210076004802011541c1c1000750301003500c0c3c208501c0e07800080d50414099aa0001e0300481911841c0703800c41801d030401c2c0d03101c030440d001a128680020300c08024103404240f05000480c81c080c442c407501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 899921393 1250 899920143 899920169
    0xe09070e100201061a0c121b0c040c0c03080a09021e130c020a03050c15010611011802061e09032401080a02100302180a090b010e09090703030f110d030501 68
    0x540c1c800c90982d405405600030340301c8241003001d0f036001c510000f80078800f0f81d04292002c10a6102540c140f80d40120408104070341d1202e040e5010300000d01a5100e1280101d50400c028200d0700001f812114101001806024603c0c000441100c50741e00708080c072a03401072145800183d50044e003c07070344046100b8180030b000d400b003500c4140c00651080b090701c40c080c0d4000f00b036401c55603642103440303511144a00c03140e03029001d07081403400044030f1100e005c4c0a0b03c3d151200543c940300703085400c5440c42c02482c118251409032030009a12401c0403241840c564940d1412a044418043c800038400c0c0c00f00c40d03405210740750300151000003008204040b49800c21030b4001d1a40c0c0c880b407069840804074400b0b5403147d0312030324100d031490003903004000400520320300d40080722441c00001d44142580d8428400140c45881c003554941e440b800d042d00550013101d0028142c2004899155980001d00000301400100d10043c88110b020780030074801002c80d1421140091481c0d080180905401c0c03080d0b003942420303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 899922643 1250 899921393 899921419
    0x915041122110c03090f0a0f0605270904080d020408240906010b0307082203030e060c040305070e06061e090a122a1503050906180a06020a0e09070e 65
    0x11000440c0c3d40308000744011814419000c0030000b000200c800100da200e11420380010303036040d44103003000c0200000e450740c82e01c0d81a02030181c1c000b02c1d0b60700c281913848a03440c0d00901c1d003075440e43c0d00503800c643c110780015103800300c0ca484000248101c0c0c015481c60710440071540c950100c9031401405c81840c3d1512000562201c00c81944c0c1e40301c1c20f00070b461207940148000b07110f040c8208070729640032680308404c3d0480b0140c2058815001c0e4040402e07400282c40c0c2e0484005010100041a000203a079003007035203454515190261a0b06150041c48410145000429099580d600503103c04441082c092101c9511000301004184d200601250052906c3d0318005509040c4290090b00310b80c02290718800e50050003c0165000c26544102105000f070503004107d246510480c861120502c1d100005c80b810710081403441e24600400c003078000c1c008102c4111010303402154501030140e0101c405601c5107030080055070941c06100e1900c1c1c201c3da01d103081096040d440000b107500703100217840c07580c04018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 899923893 1250 899922643 899922671
    0xf012f1e0c0a06050f031b160b090706020f070902070602090a06051209010606091e0b0f040e010e0402211c0503070e0409020f010f0c0203030706090302060f0915041122 74
    0x15400b10124180d0306000107081c110000303200504202d102047c00c1d01c0c018182a600e5401e411514003034400104903c1085030310f200801c00f90007d04003e0000b481081031011040d1354a480902400b85543e2b00811848100708141e01034500e109001441c032030117180c48690003005500b00c40000d2141c100c40d0400314075070101c18030801c0141d90305561901324141c10600740d81e882c03180c60a0007481443c06a2800680ca8130900c01070505074a0960b0040e580710700d05500c0121b40c2d003042e08000c440c01030f003505020040c3d1b500c483c100012028580d080200c50610100c041c100000711034032103c1501c490b00040280740d0700100440c404c01450f26200c03503030b130047d005000482e207072071a00079004034080107503170701c59801160440d00f5504039207021000000c82d81c2c0442d0850300040400c40e446d43e02c48008504140d01400519406094001c0c0c8052514101900035503d0070300e200c0400085100102013024008c1c4440518080380001d0094801c3e2804601e4110140a0301040032460600c1d2052891b6259 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 899925143 1250 899923893 899923897
    0x6030203010b0f071b0303120e01062d080f1e01050702101104030c1203030507052701140316120b010c060f0b0d0506060f012f1e0c0a0605 61
    0x5480d010201d00f40a0b0301500d680041c0e00c2110252070719613403c040030100d00b0101c10010b02541c46542e03080040c048105546c01692004e140201d5941d04000e420300000d800404c00c82e403d0504145810150a00b445990140041270342212095002d41c400d0b02080e04800501e034440d10411443c03114600c10069046422184181c42000050b000081c0c00d0107500b055401c40440104940300c005e00e80b07503890b500d4140e260002d030310200e400c21100000400385601885a0755202259081c081e1030701010f490040c110481c00d568170340040350710100c112101d034461480000c182d001074402581d0307030a100c0d8410317110751600c000090019480148100000d202401195840c54060b180c1405000a9070f5a80c0003402c20602c903500640c5c2e1715078080710307656190f910480c202800346003e4046420000c040c00070b0308a0b007403006410f1001c4204c2d05031145848119603200c1030555801500f10b0500e15203143e003041d485da8034040146400001c100b61a642c00715007203509000484200000e1541d40300d09555034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 899926393 1250 899925143 899925149
    0xf090106120c020c031912080103020a090e0109080a0c020405060a150819110711041401091a03030a030e160e0f0405011401180e0c031c03090f0503130603020301 71
    0xa01400c10701061511540140b0740d0035410f4015110704000340390110385000aa940c03580031982c40c0001100a1103030000350b100361280c1c14a0400a80c2d030440d0049803851140c2d12030b1180b02d554800d80004000001c0d0b0049500560040045581c2c00704094000c1000a2015040e4840c1e0315000104080c0c0c5400c51140c002c4400c0c1c4032045000510841065603039010081004100910b00642004041c189200758150745c0842040c680d00c801c00c030305119040b19030340840075000340d18286070305041020230094941102c54000002c2502c1d00c50b00c0403200007801010301941c143c4004112110b0080c2c0540100c5d541e4114070044170000182e40108941001c0241714000459400c9004251140c1c001ca52540d07109000f00000301c0d014880e40c4090700420403d90000712507450b054007441074050207001c0c00288400300c10041c4012081400000c0d11030390342207101c400c13451104c40c5165140f0b0282d0070440070690007480b520b881c1c0a85050007501c1c1e610142000316902c03811107010413034902a01c280c070b050f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 899927643 1250 899926393 899926397
    0x6090f060402070303150303050403051c02190201021f05010810142d0a060501110a05071e1a040503010c0203040f05060304140105090708100204030201050d02030604060f03050c0f090106 82
    0x1480c0c4440081c00001e5110a000b0360426440b0042d805034130301034141e210025486943d82036900c1d0720798144107090028406408010340004460003d44940c00215001850708441d28291b0f025940d10050380740082001004c8202190b8913000c140003481030380228101c580100a48000c181004180ca04441c0304014800400c9001d4010495114040c20421421124203241000381c4c8000d01c160300400d017044800b1990280c0b100390034051075074031807902c080c2040303241c0003024243e0650f510301e03491f10950b0181c0c1480c00106456a01c400c02500f6582c402081e05200d520841a04c40e80209481e41c001d014540c081c1d8202000d140c0c1ea24400011981101c00d00200c0c0f50034070b03040008018581c1d10252064800c202e003590021901d40080c40f6080c0105030490090140d81d10340070703041c1d0510342140416182c0e14414031003040580d030482e0441d03041490605006a030381d907803040000c0c010b00094101800042c280f1101104001000800c801905011145598011500740070406009824050580 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 899928893 1250 899927643 899927671
    0xe030708032b09050f060601140403020108040b0a110a0504030c0f030816030e04050f04020a0e0c0d0f0e120301030303061203050d151502100608010b0d12021c0908060609 75
    0x511003840b0030140c4520410080b0202d40b07901c00761243c91a141c41860b072400300fa0801024000203603040905404036503034942ca41410030707180da00040c213084d600800c05410001090001402c01120381c0c0700c4080e0016140c0e0b0710b600c0d00111807000f0080d4105000c21911b00703c440101080c1a0707544a1a2422250720400092412441006010281000803021810b100d0850b1070300075140d40354000c00e40f02d40724140030300d882c40c07800740104224805241e00501080c508003090082c45001e41f01203c400d503106141c0820b00180c0030352544001d142c480b0885000d400b03500c280750b0700300713420070000c504982c000e84d0248505a2100c03040d1503480c44035240280442c600300030180703c4c1806500030311000541803166460340790392900d04103210b5092511020040c0c10049810710f403400548150f001038105d0341e000700907403400e60011a41042c410400548032003101014804800d100708641031040d108240d0b184000821642c025001c003c003806000503034080c0d400011704509140714987d104824403000300c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 899930143 1250 899928893 899928937
    0x501050d03120227030c1002030406031e110406080a18151b030506011202090906010e06250c09090302061801090f1b050a06050a0f031b0e03070803 65
    0x146803081c0000d03030303801000e809025520300c40801420fa50314180d68400c140822800300d00070541441c446c403034090300c12140d08640c130445d554004213031000e503511410002443c1c00309003488014031401032540d6040d035007444240809115288058400c440c82034613540903d44403200031106442d80ca4400d1070340340c01200280808240c1c603100354800b0a021480004040190003090001101100d070342a0101c0d860340184455964840d80c204810f003501c410071400c0500c0c407000900000d03009030049042240090001c007030360b61030104441c500c00000c0414232140750520300ca4080303005c80240654807a0420784001500c0750f8103008080d10940d1541c06800a60b4459061008000c14000c142a40350358507400c9100040d0f0b40c008440d00709000c0d80001400c119644440290821560404e50141050140030440f46821009031403210302c040c24645842c0004c000100c0003424086d142e8074030305602d103200d09421740e08840301114124065090340d100b0f0ba01c8280c815900d204241d0341501c0390960304600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 899931393 1250 899930143 899930147
    0x2100222170d0f050904091218030b0c090f06040f06080606210703020f0d0f060b09061602010c020901030b0601020d0f02030f132c13030f0e01020a0203061e06040501050d03 76
    0x103d4803c200a040090600003400089021a058108220380b03615004031500f01140e00241c4150f05180b0340812480c90034203507580c0882c090700140550303a0340380d07010640707004a64413891140c80040002c1c11043d00d42e5034800c1c00001c8900d441c8611800b00c0e001c44041031007401d100c0c04540900c44d040400300c0740c1080301e5429030b802c1200101000100f507824000308800030f41c403030b00508c4521001000400c012024001074002ca480550042c03000600070045c04105c3e481d20016560410003004044e5a0041c4600060740d942650200080d400300c072040001c810032201001d0180548000c0c1d01310756002680c100265808171072002c12a0141e4401d01c0b00308900c001d04c070000c100e4200d80c0710501a5070381da10400c480803160500c023030705099088401003981c40c0c075292035a982d204180b82c43d18903042ca10b584000c1c00b090000600f01d420458590064541640208140c0004550103003c035034aa1800307292000c000c0f40d003915a8030414403400b000c1000391403d801140d05950008280c141e02240320703502 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 899932643 1250 899931393 899931407
    0x203061c0c030233040e010e220f1101090f050d0212030c010c1403060a06052101060809011a06161e11090106050a080a0b0102100222170d 61
    0x71221414508004001602da00d058816580344031007081240c00038130300c0e5402c4440350300b45184120040500003081200e17400d4449504681a41c1150b2a15450b54107440308401e03056000c091916405002e0340e0208044248281c0c1814005c41413554540841001121480348621608080610b100f030284840c1c60014200143c1134401000e440d06c0e00603403081d8a0030368110000c646056559035400000b1540c1005503489000d0301d115036545189403080000b0145c00c2940a000b08010010803110b08001e00d000015203d10584c80d42a5032569403460005c1c07809401716603043d00b9509040c640b21030341520f92401900e5640060503641050407842180500c40300a01c41a5030045c9440381c0903a260044c590010919030040041381c41d054040c005201507000c060f44044100581040102040c2764000481d681150341140c2c042441011540100c0c5051816101001401e100040007451107034401c1042810212004000403810b6032403a03803048481040030f640c140c54001c1c504d0404050302c500030b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 899933893 1250 899932643 899932699
    0x601050702090622060905070810060836070f21020402090303071406071716120b1e10020f0d1101091e151b030218060c0a15020306 58
    0x1c12003c4a00c81c0d043c0034000d440b12031b840800d000d59642c090190b40ea9100070b425900440401480101c1c0e8075000c80141170583c0200607070000740b02c1040b0840100da40310009265034249410264050400748142c0c1c0d10340c8258480d0388020742e030b6001c0000380180c100450304000550100d01032680c400c1342c0c0902c000ba52003005004d9042c007007009120005607034840545080100c590042c00035151042d0090100c078a1800b41c24188150582003001441003488200c840104501d17040d00301507450f00e486405420607105555004100c1e0141440584c0d03104100c0281001c22501c075900c500c07182030144c1e200e40a03500da04205410205101f02ca0700d0182d8480c0c000c1094110000940c1c40c44c2d5141c601c0a078020b0032641421600c1c40400a05100b8038400c103d400d41070403001041101d032003030040c0140c0c03498110040305050b00481d03440d403146501c3e42090410140601400e42da10400003513540c590300a074104548141e801d001068070800c1510035284142000780c65100b003140e01c0d0f0041003000b85015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 899935143 1250 899933893 899933929
    0xb07060f1517010b010201360b0901020a1706090720010609090209091501090905033714120406180615060503040c0603050c250b06010507020906 64
    0x788400981001e000c10207002000302203030200c1d0b00d05621401a082da01c0030000d6504581c1440218510011450544816641d590700e41000b2442c00c0502d03000c5542144401030096400001089071088047d001400e00010503038910360205032501180d0709098058526982008120f0005aa40da00950604141b580110001c120b42c1c3c185a0030642502c055400c2004074503140c1c068401182000c0d0202d07a080b014500c00b400d4460070b040407030880780c01c051041030b41843c0c80c0c04010007440404c0c01112501e024423007403900113000c00520a00140702030b110382500194016154852107100d41120540b0001c0c403910145410f0700341240612003038000d030059542c036940304050400414003c04040d00d00307116003c0410b42035031503504041c92248075440300d014024100100000903c6500c501800d940c007605001801e034444851400300d03409681d0804419444183d40e011000007098026441241b143d00164040e6464500445242c040c1e40d00003900312180d80041005071500e00102034420102d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 899936393 1250 899935143 899935151
    0x80303220507032004050601211d210c0303011401090e13050f0a0b0a0c09030c081b040240030f060c080c070308060d0204050c030a06050a0b07060f 65
    0x541c40e0582081e045500460344086568644010001c003440c1400b2520030444041186140c0800060450fa4a5070b05081000300c41c400c0c4810444c04a038003c4030440003460220640071410307289181c0c0e0382030303540c800107058420700303e0101d1002490049a108204003009141503910380807400405a0310700c240241070103c01c5001064004003640e0070340c41017031000c8011420010f24107141e41061030f440f40070061034011824400208032007822054001c000c8141c0018000860729045030003450b00c0d000104107241c2c84100003404d01000806080060010000c02400d1074414200800c0380b043d0202c200c0b800c009500c803040449200d5581c0d41c0700c03148803480640740102880240c880545290421150415400301e01024080184101034004c001c40c1415045400e0000c07841050b4084e040c0001e0801c142040000d04545802490703c06550b40604144641c1c1010804c1052682040320844003080c5031080014803440c003851044105d48050526503d401203a485841c080c200c2c0000301c16105840e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 899937643 1250 899936393 899936461
    0x105030a0b0903120c0316020714090a020d0c0503040506060a060c080a1e1106010902030c1909030609030c1101090510110a0f0c030201080c0f04090b03011b031b020601080303 77
    0x16600d09100307604071425a0b40c6c918090141c10f04c6500181d90135004c550000e80c062000d94504682094217490850700c11506550300070201010b0b201c0e0144602c0a107041002d16040c80f80c04c2800f95000d40c0c1b00300e043e60040c1c4c0c0c5003010f2080e42200e42c0320781c2000844c010300100100b02c1c24402015410384500e4080404901400c8102c2c58107030100c40c01c2c00090010390001607010050224602503c0103080039480c2d810f0404502001c0c1c0102214103140c10000300f46d040840c0d0207100520011a88000b040c8021a03003404c001e40802c0c9605c070180e601c0e82c8080c224500c5036100c0c075654401d440d40200b03100d821004c481070072685003031060380017071151240c0700c0002c02182288903103c09a52260314441243c5080d03200040c0758840240c000101c0311800e011400321040d44105580907143d0100e4009400c0e0400400079024145205111a0111001080c0346005526404c002441030380f0802501d9001c48100089a44010074801d981d0f03030350400d10224010f1041662a004410aa0034540c031942c14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 899938893 1250 899937643 899937667
    0x2030a0b030a080a0908070b0406050c033001050105270301090506093703080406060506030405070e06060a0c0b100e01170606041a010309060e2e02030105030a0b0903 73
    0x3000b00400d03200380c0c001181c1c0c0071010f0360210744072001d001e5540140c1682c615006406000380190f0040d081030200c00302c0e8124003e0010411f803401da0b100001000c803d90525020b188034025070354011183d0600b010f00100300c81d4040d83c211412901c1d444c1c3d07002800018145852a0300803004507035030341952100d900c00d01180c1c00b008894040c8075240050b114032100920400c007006d0701c0510f40d11152001c2514000e081d1410404254280d0b0941021140c542d2249002c100030546600302550080e000700070300c010302500144c03480a580d040b081d001255150b42c8101b190600503020f0460003d00c3c4003110200142035603401940126040e01f070503102a464200d40300100000360070107105840d9a010000b0303001002c000d541d03008541034804001c9102c030b05080c0c0540d803c0300c3c00841e0625460700c00e03940c100a807951040301d4460510060b1802c21071b01e8071030718000d4024040340b1a800d451440c0081007010b441e20031a4121013005000700f000d51456039070060341c1000100003501900082c040600042 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 899940143 1250 899938893 899938903
    0x60e01110717030c0615031c090e071d1e120703292d15031014011a120c090406060c03020f071406072d0308150108060402030a0b03 58
    0x140b5040003a58950300c014102528140e4000e05640f480001a00d80c8125a1400b01d1f02d800c456500e100d1003108108514016505031045911607989164050200230800d9800981581031030714446140f9400a205400c00c241c6180c20201c416205404140461607441c0c0781d0164141c0e86110340c241c0300f00b02c1d17a03a156055039007a81c144421107102c105600003184045903000d95071091507000c075502e18542143e1500c04440e21b14808846c0f480d1154042818644940c019901c10b000007800c50303840798111002100500918074010030300010002c0049840101c5e4110400740840494480d4140003060201c00c20a40014104520b04d620410821040380c94500884000c0d00c06901d54270307401842d620340249031044c1e10b007600b02c0e150040d4005101009560011541c5018111102512510300d810003500c0031071125401c0001104c0e448041c0c01020440307500c6032025009403a40100ea0340c610404000245c40c1d088070a00042c0c1d0140012403030714150340519000005c80700c002468034443e4004c01d10308 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 899941393 1250 899940143 899940179
    0xf020a0603090b0a0507020a120201140403030c031413020f01180e01180207031d010504091a010e0312030103020d150906200c1902060f0a03020405010216060e011107 73
    0x252100e9001040c0f1034448201a003100306030004110354604004020340301d8030b10f040c0040142c4030f1000c00d01c10045c403d401c030744805030180014460718102850090020b00b5414840000311b401d1099035461406e2404d141e074801c3c40e45040d0561110707070590811a0301107942c0c6c040341c140081094401c150b0292018500094003c0480b10b036010b504080245185240c4049000b10007801007050000295001d0050060742510803c01406a4140801696036003d10b0304400103041c907103540d9001018110381030030203070b01c1c1c00c0e20b0708070f00b0701515024980c542c020300c9103c04a00404100410050030130805421155010f01000034405c114441100305440c0c0b06202a079047d600c0e0941203c1501076000e2010245460704222440c081310958515261704400740340d580700c3c490001d1580195103a46040710201030b11440344a03a581c085910280094015001d850f0052142c0101090030080404103074042d80c0c0035807140f805d1305491070011100760350381881c400900c0c025468002041d80c104240c034511 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 899942643 1250 899941393 899941397
    0x3071407080a1d1c0507050319060506030a080301061b080412030905040501080c0d0609050a051e030315100e060c030d05090102130e09070e150108070e0f0d0f020a06 73
    0x1440c000400014600070300402c91409903c02e4880a141c90360f20b0000400600990300f036090420651820403509000d059800075805018180d041010811218600071f15588134900400040e1203200c00d0666031200004020305140041005201d002e0196400c5c10961745404e01500042d2082c1c1d1b620812074010303621603810741c07100d0300c145020142c106041d8009404159000c1007a513240c446a5035840411850150148410308036450a10140f40c0245128075004400c80d0010b18551420542d502c114403002c4a0701c4402c1c130300220840c0000310469010303116110301e0110000d46c2d0400c20160200700f502550602c0403030000448103403150000b03041c010340340101075500c4440001c00101903c5005013001c907680d104202000d80ca02100401800f95562403034120159944c1c02c103070300c1c41e00714240c0243c890096480c0c10011050805040000040c80c213994111090311014002d86010301d0302d00802c3d5121032901c01010140c10600c100c151070b203003d5050380e403000c0000d40204103052030907045280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 899943893 1250 899942643 899942647
    0x181e120801081902031b010302070c0e0f090d020607031a030604030e0f0105191404120602030106031103103807210203040506090a03020418031d03120307140708 71
    0x400d280080c441c00c3c03940203281090109510a40c0e00180d1680000080355002d00c0d00020600d815911076815101e04e250301c882c0c01d542031380e03c0d00c07443c0300042c0c0121400000060f4041c0040c544500210307001060700650f800074000c68a450f90240c01409014000000051a80003c4540755074108102806a0300980305c4100c00c003212420310140c81a00709001d81444010041c081c0240300e03550142c0d1015030300d4a03010b4862149800d1000d29480340782d01004040605103031610078007841d60f00660490703006403030070445250a0400c1444502040318040d0449a14550803c648004800c006100000c0300345000003c803020000c076070011130700520011266001048103c2009100280c0c401c0101c20b10180c00344c1c86000c0d40000795a442980030b41d5014080200c2d08040340c0d00e5045d031034409160300810500440e142281c0945044804150580009a91741e0289081d509d20000c0711404850141c05410315140c140d40c03038002c5510160418003017000d2036140c0c0c120108404e0160145912605061f5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 899945143 1250 899943893 899943899
    0x206160b04030e100203041401030b030d03150e010503100b01110307050f0c031c0302070206073806010c03030504050307060c0206100806074815181e120801 69
    0x203010b80d840032405405000440413514107a50008169001c603409502405550f400b400c0c0100d000e00581d117041d54040c03080401a0317076050341642100070000e4641624690302a07660f9a01818400f0a00ca9650150401004640240c0c4190005149414181008503020540e4220507103194001d40040d54107820120488041c1034080c403050b0703c0d45008034010807910741074000421441600e044e0040a05034002000f40c2151541030986540d140c00c00c0103040d4500301311009428642c600049910506400420581c0d00802580c40c1806180e0613564140b8649250f9010307170051401a2083d0f5191109204010011b41580140e0480f41c5441d8007402190034031204c40340c1d0580c2d140e0485126138005130208850203a012510f03088410b0169410541c4c122040c3e4031240c6d42000d00d082c418404400d68528480401d80e5091390b021501c24402200c0c2c841800b905c41003243e1090032081c1c02503c101c50554081030804101d203055007591307254084440215034500b5404407010b1a0308010030300100c010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 899946393 1250 899945143 899945147
    0xd0b0f1518060304020130091208060102120904150b040b042402061302040f060e100905010e0105041d0d0c030e09100501031a09010f0e101a03040206160b0403 70
    0x10a0760700c020794050341142810340c00a0302e00500002448100040c120024410404000344410204a8058100000e14660034182c2c82480c64040c443c0c0402d1603140481c0301c0d54800103900400c03101e01840c450421401c00104001341440e00f0920a5031105e5030004101904090028030050004c03041d81940da51400402541000c6140010f130640e498040203a84e0590b0049a115404649582c11160a081d188001401028003090401c142480e00710041007001c08000114064000050b15003250384c1d4402c0440d00380c420034003500744071b1020580100038604064001c1c4802c0d4444016005a41107105038244c03802ca004401c960010700c00f98843c07001e164000e0200480035205845544142c03502e83d0201c1c558441c18401c0300c0c1010fa94600c03107846145081034600c1c0c06032000300401c0280d40d40d5002801441524003507080550000c9011900900d200e40c1a08100c0e25180f8040401304c000c075441164580008200341d0b00140200b01c070440e52040d001c1c400085520504100146003480c1c100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 899947643 1250 899946393 899946427
    0x121104090c08100306020313060c0c0c05030706140f0f03070f0e09010303020a020111191103011103131203060f060315090b150c0a14060f0907030201050d0b0f15 71
    0x3591003031254090520a21409450030102030707941002c0c2c01b40e0b07640c841c030140e2500c240303002501420280c80d040502c82c5030745c0d020540c000d2140c0100d50b0607003d56141c0c000c158070b4003c60722402c00440c0c4010f0003803410215110103008168281d896017424504031202d000c80c01d0b401100c00c140081d80e41580a602182c01c0f02914965104c00e03102c5503915030440d0380181d03680041d00c0b0043c0c144162042000300100040041b040c100400706a421500c0d41c1910b400040c8031609007500348a5420b00e02a001302034204010389115421004041102e1401ca840e696050b40088a07404101038555601107200c0004c160113900502d444d0b500020310040d0f400184506c2f648540006144604000c580501961082480000103e49003076481c1d0b500c6220081030b00d003020150300100021140f60314881400000b02c1c1c0380c0d11401042c0c44820260b0f031386410b507a460f22114000203021800138010072401c45030703d0340325107081e40003d002d54060311451000100c08200e00d0607410381d00800010444444c5d00d013038807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 899948893 1250 899947643 899947661
    0x6030f120c0615010512130804120201021c0806120f0316140c0a1e0e07110f0f1c020c040509070f0e0408040b0a05160b010303030c0203031b0a12110409 67
    0x240c512100720782000000e1603445078032901b480703003100e0101140129450402100c11150f10a541c255111b64907441c11034110454241a07000d401102c10301c42d030b51030a021080001100594032090705a03242d80402c000c4010768032007070705644203801d005507801a04000900700c0441070942044045400d2610180760400c0c070802038040d4210780d020f0540d60303c070541c0b9401900c14030305017602c03043c58200000200800d1a480945420b020500340101c4c1504541d110580341d50007030540d21103420303080500e5500e403601800c00c41c1c03c0c0e00014040c061030204078010380b2002440d1060343c00d0085280005400d80390240c0f0050003e8005000401084403040e1441c001041c0112840490b880c4c1500e4600c0c40f401035104d41115550002524020944540c0484403402100c50443c802c000c40c50070203003070050302404102d0210b03282c0440064031900000c182c910406010121040da508401a40005a00084510790500480b50f0080c4414403990203003440401080c000162254a8541c4000554030000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 899950143 1250 899948893 899948911
    0x9100c060c031b0518041802030307080a0320031603020d0504030e131404080a02010e070e040605010603060311040b150d020c0105060406120f080706091202061f03020906030f120c06 80
    0x80c1599007001700b5580b0001d545d08035400103d8428141300f207540743c200314000070f605001c0040d42d0701c00c000038000641101c450039601003004401010030000c115291003901040c1300e40600016004071640c0c940740e400070a05180241c1400002c25103070041d40d80c16034044021030b000d40e80034921820142031045054900c040e0610094202005c040c4800c3d40182c005070200800181d2031110354000d4001c08130310301681048543c0250750f5945c0424404080d2001c480590400000140032072003402140c040d80c1d0400d0094403d86148400c120050030440515a001360344840b218504080c0a0301030144441075102c0580da4140300c2c0f552030300b1074500401140c402e81c40d2110030f0100d100d003441c460040d185e000540b0800c0c1d0029040c040344a0140160042c00f55081110410401404100b100810601e03a000c4800c6500d80d0b104202c055100030b129903884802da0781d02000035241030110140c10080c080d0a43c1e0000b2101c52803181060f059101c04941c110f0000f5825004003410403020340e0220441c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 899951393 1250 899950143 899950147
    0x7170a0f032918090d02011b0e04022b0b09011203090b0a050f040306020c0d0306030809060d06091a190506030a111c050a0f0603020609100c060c031b05 67
    0x18080100b0700714908182e144031540c1900c40c0c1c03141a11031810070241d044070a00c0c1e20915141411140707546112280c4c268005508102c08201c925424100802008405d9103c0d05102581d070001d00000307410003e00303454942d030070040c40800b48280b035110075a803680d0501c010501110301014044480c03c182d00c50342100600c24120305c082503019555405071070580240c150346048811040b60039005030500b112448400250020810840d503004144154411064480c00d1a841c1c5054080f10380e01d12018000e0300c2c0402014401d460104018a0020344070314002545070b8880e5030b030000f281d0b83d4130614820200030982d441050318007103c133449442c1c8000b41014070981000c0c007041203400003030003034010141c4892480d034004010000f03640c0c3c08011488881c00d1032403040c1441c00a010300341c544410485c68030b031214500c881d180c0510000c1da90060300061400810304144105002903103144410400000c80d00000108640206e00700c481c11560041022102c40403880c0e269075034001c0304400d00c181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 899952643 1250 899951393 899951411
    0x506061903120f110d02100c05030906070f02010608190629210a0606060305010501090501020a08090406330c030c02040b060d020c10060f0e010902070201030207170a0f03 75
    0x8224036030b04224055151401d0004403500f010b881d40c00b40b12003100e0150142c40200c4070b41039400240042144001007083c08202c00b0785000391503034402074640c0040354110b5000030702290b0040c690107a0b02d085500c00002d1480da284249424050310080404000c07140c400002c0030700099025075241c2c1513244500d600010136035140c2e80c42201c00300ae54240140c01114a00502341c0460400c11009008202581c1d542a80d620700000140400d024000201c1d18140010525500c1031180c00241e0301e0680050200c0100381d1940611604000a040d52098031b07021702045908100500000b40d180c48801e55136900036800030407a201c1c00100390b100c20031410742150008241e00080c1c1090540d011f07a4005181d81100c0046841441039140740141c06000003800c450303078403001500c5e40b46410224070070840c5039141c0d80508200100c511881003048014070050102802ca41d00408115105060061034501c1c19600c058000000982a2414100101d031034401550094940c4202e155585410006022 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 899953893 1250 899952643 899952653
    0x3040609030b091606180e06060f0706060f080714030c060415020c0306070f090f05090c030702070302040603060f0c08010b030106110f030c060118061811160506061903 74
    0xd00d5220152034121100b001c00c510000501181c0768010003000c19500d055150480030f4043c40d08803c241124003490240082c240404041d184d0081d10010401c5181c40c1c44036070b18411642014000342d691179610354000480c14019203c01707000f41840700c06044a1803816900d00020700d1740c0743d010f5010382c10504012034a80c0cbc03448121070588004d103960b1110a419100220f2421040c504d281e5014420310060001058105080b5502402e5513072310400001d44860070080340e50340c81d1080940001080011410103040d000145500c100c1600c11100c03499520303000a016601c0b50b80c016100603a644600d0850000c84d8041c44c6030220345800c1000041d45050684410380c8030500c13410080111032640b0406140051100c011489a00c1d01181c2d140e90310103088a0b15004280310394100541c600300414084404c1f07004401c1102e00c2c81c0040000c010120121802500300045a01c00d50401000940912906003004800c1e140c000c1000305400e00d080d10512000407010381e40002061111031b000c0001032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 899955143 1250 899953893 899953907
    0x8070f08010c050d0906020c0a0803011a191b050706120f0504030e040b03070b180405070f1d0d0506070e10033e07050c030613050c0d14011a04060602030406 69
    0x1132245040000c20341401c4c2400320090190041c80b840303174010f0050890601041c40041d5042c0c03864591a4106030040d60b04000061003018100310804e890303c20400c400724012040d81c11344495207400c02c0f4860700700f0390714507040a01030b40141c00800c603d01207030a050310103882132840c000040001044682001e480142ca115220b510740e13445662a401501156203060204000410025a59a07110b10a510700039000010702c122460007545814000340300180300e50110b48024003103454040340382c00c0c0390058441200044000c2c54200801c904d10310002001013054900c9016541d42d0300365040780740e9042040315a407521a41d81014101610b071400d00300000d28046601405041003056000544422034400c20200c4e0040240781c40821614144071000c10182c0394000c0480070303210035541c2c8000a020581c1840806840740d4010100700185040068082245d180601c102c07120000c03520394013a003503400e5450441e00d0348442c981e01c24068107040c001c003409801c0c02c1c0046d50629041c00d070020420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 899956393 1250 899955143 899955157
    0x40b031906050105010c0308060d0305090d03050405100e09010306200a02011401050108010f0b030603010612030f0f03021809070c08040609060e031b0904080f070c030b0619090e0f0708070f08010c05 87
    0x59a402b507600810140035000710f0741030f840c3c09040001c000c2d0341d07814080c20581151150502410b91500840044d0b80303d5030818541a03c001d1064070640d09589440c0f00918116034501c9540ca030f00e1a698042e400800042c101d2940305600200d0324001c4d811400b4160b130340c10703404103041c00702c8100140644184c0b04d2811041d540000c60081d120780d00c0b140003a000d0045688041d10030090b0480e00b03800e0562058050101050340e456150b060240104224202e104091040013103442074068030070107151840405030403245610b44030b00c10f00343c80d8640d40403d03030041c1c0c0a4004100041c500304440c0d034010b0116580440118041d1200c1401b503945025100700100e0010f00c1641000001010007588000341c403038001d04c280415071600e00515080009441c50301054940c80c2d1103100140e154500f000c82d41c01c8101c228582c01003054902030700b032005000c0003082c9600c00d003c2c46589124110003005000001d02c805401000c150340340450a80c40d81582d50043c8030755904241c10b40302c03601e070044201c03228 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 899957643 1250 899956393 899956399
    0x3061401030b0c1602090403020d020d08091504050c04050a05061c0f0b0c0d110a0e0613150e03060c040e0c0403051b0120011a010e0a14040b031906050105010c030806 73
    0x349a4604c080c4114030919110001d510240000901090590000c0d21a40f2014245c08403400b02565203000d44065a080300d807018140e114110a04800c903c0700181a0844c1c0310b113080747c00c030030029400242682c4045a0140300180e0320020801d030740c94217941c1e0f0301900d024103a501d001d00340316407200d0003485600c1d0380c040e20002e9090080303400c0084d188116144250300641c00c00c0030790042a40c1540744d0b44104c10810014031082018206860040110ba060150548900f200700f850300728034440401149061400b4004402420340c03250700c0a00c41684034541c0804116038803030030160045181c480c041d151200780d00040c0028000030b000054040150038a41c0002109001c5281c0101c1d006d040889040e904a041c81c210b031248588150003030595030000041e000002282d42004607415600f940d41560710221100c0700300a200c844440f00140c20344064000300c2e105a80001092500a07905c018040300501c841c0b00301300f40721413881094050642460b03c1d14108015840c001e001c3d11028045504c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 899958893 1250 899957643 899957647
    0x14071401081302010c0203100203012c040303050c0c03070f02150c03041a0702040905010c020c150a0e0301091a0708060a0608150a080708070503070906060206070c030c051603061401030b0c 83
    0x400c3da800340c5141d03810036500500300c90507800e0054100c4007a410a20609031030728a80c1e248441071120780100d00074250070462007805650b80343e803000c8010340400380490810401c02c21150007981d00a00c000d03e07002c2e0094200000203001072060080f40c480000981c1c824040511001c0c4d46241e02004503802c0300c0c001182444100001c40380c43e8042d11843c40d00035407003451b01814100304403064120fa420400d081c1c0946070408500307411f0001c0421403800c60000041c08012010009001e00c1c042d1100707800240000070046215640c11071041201c01c505810105140100324103151f02a6903564130260513a10a000c0c1d61034801c0c09402984080e140a0000650548101254440405440c010240001120029965030152a86403403d80c0900c0e802409441030101d040580d5006d800c00715103440d8014040c550701c0300800c98401015a070201d0800ca4000e440d00b0203e002000300c2200e103040b56020480701461032602e5800c541c05240180181c21041d001000851400c4080992003000c0d600125 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 899960143 1250 899958893 899958931
    0x1215051006110106090f060602060708060a09230421031a091f030606150201201b073203060c090303070b160207080f03041e050d1407140108 62
    0x2405402d13140c11030b09855160040c41108000540c101108840180d002c0c3c0d1303031030b4403042c108480c2d48604031050783d0404119101007100d4040c550114082000c40f0780050141015150842c5000c0c90542d82071b600720b98402d01c2c260844a10350041c402d0050b846c01c2c01c0110320180001098550744c1200010310502818000a011400c5c00042d180c001d03e107000c4001082d62203141940080440c0d000700103040746950101d1001c1401481b5440c0013001e001d001ca104028403c19407052584000714080b49807140688600308a04104032040191a42150280840f040c80701c0314007440b0750b42841c0101c0022450380c8100039480202c1c40d07035049000039000941c0c504459002c01d01e03600c43d0b000010100300900c03042003100d0501c0d80ca070040d0b444441d400e40c2c080d242d490805c280d84401d80394101c00f140d00100810003980c0041003803c2d145241c403420407203950380c1c0d40000812250049000b40c86901480407907446003541482103001900100001c51801803420300000c181440c02440d0501500b620b81d108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 899961393 1250 899960143 899960177
    0x518010f1527080706170f070e06030a0e100c0e010807030b0d050619060803040b0a1812150618020c0c060307051b0a0b07030c14041215051006 63
    0x202078003161800340b91000c0450301401c8400381552048040074012103801180c1184502d85a40030f03040320221000790358403807890f00003605d003024001c2c00900000035400e03645526240080c41c03144118400010b048440e1900305801c0022a0303038400f10051918214600241d00610300c202541820f00e40b030203031541c0307007802640188590824150b01811801030391040200004a60744030700710b0b00c0d010b00908086400104140d9005000381c070410b030014841071040d1a02c040280022803e1361801010b4034100c580d00c002041900e0300720044c1c107808000c101d03052216a664000d2400342c00c1508106040c901340503c11658404449810300740d800083e074a404480410071a82404001402d030380ea82d091281c0045c0142d030042e012910744800c61555041c001c1e0f404034800c0029600482c1075019950b59140803401000e094141c1404c1c005003101156400c40e511018001900001c9040541000c840c104480400b0b00c034007030141545d00f40820421178208a03003080c81140d0036810594407a08941c00c0b8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 899962643 1250 899961393 899961407
    0x30b040c050307091d0d080705030a0b04091202010b09061c061508010603051002040b03040f15090303020d0f090f141906020a1d150a21060518010f15 66
    0x10869041c49030303a4011500544607442145c010001c42d56015500c0c0d401c01103642c40e0a901c1806030041412480000e1400e400b0704000c50784550310420004500351114005000c5401403001680c04000b515034403000f9540910407040c0c20b9030100c42d860810301d4000005940d00c00f0350401c0715400d083c1d148080c400c02c000c981109580e00800070840c150183c603201ea4500a00240c40150345d54482e10451021401c164400c035002d890101920314910381d950344800100740c00002c821103d402c1e0600c4810000b86041c456806041d22030765016958030b00c2d808851080e22809007032010003c3c0303887d0000c0300081c90304005500d03ca900c2040f401408541041650070030b0303031844100c0d2900c441342d0031791420440c8039401040c1030404c54840052140490b40745e03005074069443e4081e089035a026501070811034407405042000c3c818680003030040703021003584c035100c1102c1c0c1141460301e0311104c050240d4640509900022055080c01400342c1d0300d4480140c1d07008031540300c1d0351106108040e81c101c24030300c1007003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 899963893 1250 899962643 899962649
    0x28020c010608061510080606070201050904022703010e1b011b0803100b0c0303130c0b040915050f030604060b1f080a06080c0a03380412021204030b040c 67
    0x4000c20040790b035203100300c1c0c9801d011070b4108844858100c4820300c42ca070281c103c01c2541c90580c1c8002065803580b082c043d5507804024184d06021041c031040ca5645d803a80002c113008aa02c4207010a04100c0440789440c10007a102410b2090741400e003d03581c003050000e5844100c0e49800c042036140c3c90100300581e810345c0100108007103013600d02440c2042c000791078000c50142104801010000c0d07560003800086010300403a2421680040010903400d844d42c0c08181c8566001d207410301c00c1c4071340e1000d03000c4080d44190312a10703045880c1d034180c0c030003200500c5002d00240800d40320710709120702010000e034071054010f100409056540311880030b1a00c0706c5485c2c000c0c00e2211052040015081d10010740500c800322883d00c50f960500d0f0300400e00c00c001281c106100c02000d40748081007821030703680c8426020000703a40d0005100c1c0214045000034445d0002c0720300340c0d0b58600d408581c1407d0500c0d4444120080c1c01809651021703050322824103d110442d012280c0182031405c1d03540f82c5250400a07114603034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 899965143 1250 899963893 899963917
    0x90f060603111c021e190c03090302060310080106121703040206071403120f061f051603030e011b0207060801050a0e0a0905010f0506030f150f10030f0510050703052802 74
    0x28414090340344641c00403c07500403986e44180e1100c5044504651000250320028002118482c081005050140103135401000c405841400d807500e0b445000d0840b49aa80803607400501016a5820300c2805d811226048410202c518070b145895000f04005120340030006015003151000341609010074801e41f919601e654019207140d0810000c0b20700211025103285105404080d00c500800c40c42d02034100d13024129032101c070300f49210791040346240030130b440d0180c05050b100c569070b842181c801c0c407602d84a01c42c190745618000001321030003441e09040340c03c20001e2040b0030340180119039410380103104807600d0050b543c8803a601d1203d102d001d08220703031005101e0b60a0059481c00700c4410b0304003601c9150241c04032000303084402c8410b030340c8043e010550b0031044a42c9002c00c04003605441980c0d07121524900c9206aa6500e030349610008000034000c1d078039500103188255210a06000785030f0444014a030600260410102036010031142c1c55012030750700744d50314094401d00c10f00d405403900092a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 899966393 1250 899965143 899965177
    0x303070b0a020a030f0207020a060f03060f0b0403030215010e04080702060c061e0a091109130c1503050a0905030a030c18030f02040f05041505040c0f090f060603111c02 74
    0x1c03400200650080320029000c42e00b000280200c040c107520a403000c0070380042c41482844c0c0782400c1900c41c507807950082c400705526200003054060003080c0400c0284600a00d92307560341c2ca50b0400900302803000d0741480e4462104801004214131300c10200340c0043e081101547d498505100140d42807141c40354030102405010b0401080b8ad1541d42109a10075030412001c19582d11003020404940e0490001440318160341803005407030515001d040c1e070110544400e0240142c148d1600414601107074018541c0f1240201c1140005902d03004180d081004000103000040346641da141e100d00270280309800305a918084161410320510222812000e03042d02c001c421340c0c41c0d04041031035540c0d01e0300c16070146041048914410b081403080d98070032a0092080c42803074500c0720000c0c01904000e4010740d19080728210114640d2400c080600080220f25000900c201d024090722060381c0c002d6000c81d00381443d281a616003820080c0c1241d000b1050b080c400c81710110910170b010700901480a003841d1f14441 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 899967643 1250 899966393 899966401
    0xf060f1b19120f020a1b051002071b0504060e0c0c100e031b07060905100918020301031a1b0a200a0201080f06210336010314070507020303070b 63
    0x14441208102c14148194492107a902060740309004141000900030140f820410b00300101c44d1000741c0c8034805458106400401034426604000c0080d20b401c40124035082802d0034030003c08005000580b000d02a4601e07140d4a10301c8007000814001e094032002442101001c030a1280e54118075102400304043d43e0710040301c0756030350400240302d509250b00d40400003000b440007c6110803210359968801640341403405116080000000503070900003618400b00e4801000c02ca40d03040c103108118010780b00e40c9142401b101040b00d5001280301c6071400c0c4c1c10b003c18030403034051404810a10f910800c0d03039030036036000c00c4480100c2c5072402504048800600030f55100e000c10200c020900036a50190072b6225084406084d12007624481c4d40b156004404074202e180070286030f080101c003001501d003001e00e00c1c10103074071200a0070414000300484d5034818010030004c2c0c40340d801004081c81c0800070780444c1030380041015130242804082c0400800d5a004540d03040007291180c070ba0100d0140d4441c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 899968893 1250 899967643 899967647
    0x201121b0503060a0902041202010e010c080403030e0f0405040b0f15121014090307020d240606020f010b0306010e060a081b03010507031a150c01060e0402030f060f1b19 74
    0x9071020f43c400c1c0451000007a4510840c0207130b50954003072960034101700c01c856006480307000110b07400b10305000f00000c110b004110803a0140001358001d0300d42d40800c118020800a203426080320040c07040e4644070502000c02c07100d80b121540a00740c1444c517034140d1103400641c58107000f60301404e54440c00740c0444401e058004180000310003035614090044038544074214604084c2107441d10542d910600c40400907141002f00d1503074003030003902403514001104241a20703100c3c041101c0f81025440c0c0b0400c025441d8104900300ca9500e880b0000c010b0540d000300040e03200d0f0410f1150713629141101000c52119504e11040100030441c020803141003400300d01450210600400229220303520b0100040d5825010340540000980c0d280005100704035082c007002003208143c2141c11a03000f062000b00d414190910904018001060350540340346020f104261800e240e6050030186a0090f1051021070104090310b00c1d000b0301421000148030004024030f9072a030107a2000034030543c0b01d44410301c11142d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 899970143 1250 899968893 899968897
    0x12f0304050604030303140105040c1202030c13090c080109050717061503040c14030a0b0412020a02030708010e061003080702060d0207150b01110607080c4806040803040201121b05 79
    0x200c2030725100c04103070303a2780c100704411140c461104401003080e81c101080d201744160700459129820343c1c0c0c0d0706d080c07940c140000d0290504a4011800f19680d83c0f00c1404219001810f00c0d00411a000c010320661500850050030344011084205a0744505004542980d07140620030022000c901e803061345034030701424440c480004c50f114407144a8030542361120541000310320700d00d5664000d4000c5505480d1641c401c40c1e0301d20174070054811801501f0410700140d5060007400018180c401c002300301000401000c6081480251119544415000080000900e00d509032580302d50100d45003130b203500384c003081d06002c1c1c07041c000d0041100120406071613411304960700410036030a0a03a14504c1d10002100100d9030b0301c1003620040d0210302000c2c0001c1065440c0030051640c0c900c010320381000340c02c9007102c0c407840840030000d10000140703401065481d0841807682d1720070001c061004009600b8541c98060382440041d202a041164000c2c2e919494500c070b8103c00c0d210701b4a52502c016041c00500020810303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 899971393 1250 899970143 899970161
    0x25030e0a110a0e010305060f0405150405061902091011100510090501090b031b01090807150305070c030c02040b0f120601140117010506070f21030b012f0304050604030303 75
    0x982c80ca8400420102d55078041141600d5106000b070a103922028600d0aa90341d006004032002d104100072070100f44042c5d20094007407880740c401004181841ea440c2c101a2f030342d0309840c0d003540e032040c090004c5568a680d00c4032144001c5061443c09110000d02c00390030060074030000c003411400c00d000d02560034040801e1000b22882598204503036603d030b01680341a20850802c00d64980d2017040310354a141901e441100498405051010710550b444041c00d040080b42d40c41300b07200c0c196001ca840e00c81a050b014050b03100d0100e02e800035040e402d55501800401002070060b003c0c555a0784610055203500700c0e52001444020b007822681602e00f111a07540b81400d000f886516000b0350604a440d50146003600f8400400c102440920780c2041c0501c4015045090155001c0119109000105110302031242d0404005690a4100c15107002d01030161121400c109040005200501940760701500c50140c40d00f4081c4000030300c4501c020400c0745540140e0b0003007079024500040000406070560710000721 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 899972643 1250 899971393 899971399
    0x102010c05030f1902160309030c15090b090d0804030602180f03100513080a0c05060c0f031801090b010b131d0412020703060c080f0f25030e0a11 64
    0x240341010100c0703440c001610b14941d45400140441c2060208104652010f41c600340018113103002c20b0351072510b61030742c50401d50104840460520511000c602007001404004454542c2c44081c480028201152071042896200d80401c641d01c0f10303641c140010801a0300300450684458680c00d00e0740096000700c0070035186464003248001c880c06c103e807682128500041c050030109108810f90130182c50000d00580d001441140c0441c001490030f00500fa8000c40e0f9130766402002d0040c90010301d0440017a0041c2c0c0001014801e4004c100910800c42e5400709400010314110f840000310240589086000184400224030000c40c001c0f80d0300020300461100710b1a00d94030036031340d41c4000344c2c603407031044503070603504180000a008602440000d1410548910446070b10307550301d481d0081180c04603001440001c4402051050f40c0401d084503a401200005c00c000d054104001d041704901d00300300911407441801c6c024000309502070b5000c0c008002c401010f5820106217440e015690b0107081c40c00600c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 899973893 1250 899972643 899972651
    0x3120506031204060f170f041a090a02040c020f07060f030606050f0d091a070f110606010c110d060608030d0e070312180b0c0c090a090503040911041e05010201 70
    0x4032072034009158490182194055072400d410b1100884510f0301c854251001d00517a070810520140d207220f101441613040d100c024a81341801e15059680101c14410142140a200c041c80b283d86400310308600c03555030488000501f1426514241d04041205000c98240d015510340001d0840e00003003420704460950743d0400025403903010a0b54540910041d81038528400d021100d28100740382e20080d000b41c003424812070000d200001c1c1011b03132501120b0f8800010306440102144a0f00542040340c42d800201c0601400d00c0e1101c002854000405005050480b880c07890000b1600d40102e07103000e482e0404024000d450302c0781196070350713a070101d0001006a460207200303400c03070000850004240c0e584517808204940d0108011114981c0140ca100380c082e0003c0740026a68024000409044a003c03019101a042140802246040040c6174009040c1041c03030701c000240707020085a042c0d038000a030020300c011544041034000d009540100d040240458604001e1038400080403080314402d0380280 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 899975143 1250 899973893 899973901
    0x302042c031606110f070f060c0e030d03050a0e01090f02130c050f030a1107051b030106141504170f0105090705010e1c0b07030e0709091101081302060403031205 71
    0x540c0d81c0700c0c41c03109440d003200807000c600010f803840d08454200100311180906140300729512050641c000201240d8030219504020100b0242d40501d9518800e01e08001080b803441c080441c0c0c445400f02140d808040c0d541000405500040d03102c10000f442c1c03c0300800019555181901e90b9410250042e44144800c51a84012035298019074444c0b4041d41e0b00c480c2000d5151500d58100d0300054551001e160311440651a1995418050042a8041d00081041001000d03035600c5889185292070b0081e41003400900100a40488080d079195042d121441d003043c403000540340b035003d01c0e00a0500ca105100403007410950018120341e140010a008100035241c68000c00e40d603100da0700c1440e011480d888241a907a103029030009030a030814040340146403c41e645c030000000021100800440e6491210300c01441c01001440040c0a005074100301c1d1860940b6000d43c504841c41925041020712800a1b0094544c41051004d035640a004145c40b9903d034a400380c40c21006010422059103404005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 899976393 1250 899975143 899975231
    0x2011103070207050d0305040302192d050d0609060219080a061a0a020a0506180c0a05130e031e0325080a02030a0b06030c041d04170310030204 63
    0x681c01034203140c0003400300501c1c000c1403082181c14081c040d070901100344000405a128084c1c60520401070240c01c07400303142800d843c09031492800207400b544044500000030920300840ea46015201c3c112003906542e0b40e40c1c0741c10300c0545107040008011034008109148e03400f155005030401844c02d501c41c4c07031040e9101501d5404072886445444da0b20010481c201601207082c0005181c0b00d0384904c150303080302a05440b91450020141c5215107121440c0c04200210041032260950a190454a88150902c0c1800150080707140030f80c650445a030f2408001c0703203400c00b041120003808110304101862800d190022005130021184000d961b15040e041a0101c0c50701e001c0c100104d22103880b5503040e0b84401c18081d0082d00001c1104076000da4456019404d41d03580000b85210390b0170003110550321400c0c0362000a070081e84007482000101c40324103000000d0003e030a0071031605c0ca00360480e07031690354000500c1403000c0d2540c00030b50000d20f4114421084034071001301c405102403d10010b000c0d82c0140c074203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 899977643 1250 899976393 899976397
    0xb09032b0b09090d0c0f0b07020a15020408060109180c2c0610030504080d150f06020f0307260406031a01090812090f06040e0117030a0f050d09060f060303020111 71
    0x44240f250000c00b00201403030301890300760725150701445481c0502031160b55041d12005007036400d0b40142c0d001c2204201001070241c100185103440c00341c01d50820b8949500541c3da84410700502994544500e480711140703000c0c884045400d41c1054041c217000d03135034031030080720342d0744a004aa00341405000281c0f1182d903d0700030f69004003c007400740b006a4040d90030481c000e010184c0100d0740039004000c040741054060280d40d2118010400280c0c20900c0c094800d1114400b95100106641040c4049444602d012082d0f4440700d800008a000c118034500a040c52100e64900c204950440443e006c80c10a6266001010a00150084803540c01c900c4005403400005440b0709101680300310021403048000f40068401c070540038103168001a850800152190000c0d0410030300f005580004004c061510303851021072100000282d860448400c1c00104189000705150050000c00078010503134000c1940030100141e0003035800c011120201c5a441c01074121884140d0040d030a0046852200c2440c5003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 899978893 1250 899977643 899977651
    0xb0307030f02161113020f090910031703040303140c0306010e0d080d02070602041203020a0b0708150907020f1605010f090e011703120907030308010b07050a0b09032b0b09 75
    0x40c0b0030f00030405580d540705050a6143c015045500303400e02c400304201c180003400070106028082c584880e6250f06201d141d40d4000d003000d1280844030010400314040100ca8040850644080ba640755124201900030b048600101115030310210204028a580d08001e50b008003c26a40c48025414660404c01c00341c481900140140f001044052030540081e401410321510030803000d030400766a00100600803409440039070150704501c4161080000c11305141da40a0403e0821110604200451501510408100318019486d100c04075030594004c101a44014040c00211000d411207119000c036080414410035001c00c00e05841d5050190160a4002c11384040c040451150313880d00e0340d40360600101031006440d5010800141104100c5607200c2841001c0d10320042140c10710f10b207001045040705034004d0240d0300c800c1c000980000d2000c29040e4544d038102c0c03030f1030b0420b4580000036429441800d00601c8515a1481c4200045100300302102400d00d0305542003000e200c5860500c140110308903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 899980143 1250 899978893 899978917
    0x4021201290102010605060c030a031803020c0d1406041421030417070c090212060a050d1103070803120906090703031205041a0901050a06140a050f0612010b0307030f02 74
    0xa0401d8003141d20300c55011000c0d8605100214003103541e01701080203540030303000ea1003903600001403000f10540c1500034034210504801d80d411031a0300b030f501c4c020f441d405200c514130f101d542006425004e01190081c0c0c840c1c0f024061041e15184c0c107140c9020058014204a147d21501a8030903410210840c1301e0644201c80700ca05080f447c5a445075680b1210950b0b901c19400710f00c109104500104003c0340c000005040b81203001643d4030000c240b84608918000c102c107118400c0e41ca002e01264070b403c6100307408180d1054600322410107660009003002c0301c41d04901d07160301c00400d0b0410010840c83d5450700032440001079584a0f00c0c0c44011948403004c0c3d01024002c14552861001e80e800c140c3c4c0917550141c014403041d06980c0c0c011022011519003995006602e039100c0301800340742002885488014480d09052903000980b543c040b81c0420504c2c0705103845800c0405243d8070751b440b00c00c200d0310415a0411440403646e11741e08038000580081d103050000a24280c8201c400c4203d0b4422581001208 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 899981393 1250 899980143 899980181
    0x60b0408010c02151e0c0f0c07060908070302100c020d060c0509120d02032a0712120c24180303230105221b050d0b06070b040b07020f0604050604021201 67
    0x49008140402400742080306c0984040010b81c541c0031541011308045c070802000350801902e0030000500004458111036161b03004a0410801a55201c1c4044200e20f2241060654800c95000007030003501480710242c030450801d224610000d5004000300b00e038040480d6001307036220041080c580d440f000ba0200c40c0146c3d0007040300074940c004500c0340307a10544a201800d860480400715540c10450a940801009105451005d0412006c0ca02c0304001c032149142c40e60b40802c045d25402c0404041d0410101501c94901c400c16407000180c100c0703d8281b01c2104415003440841c42c0080040c8640514100080c3c0f0f524541050030100044440c1201c0d801000d0801c40521150305006103443c603403c1d004119070310000071041e4021301c100d50400301c03282c1e00c41039110102c00003030744192050340b00e0341445001c080141c00c001850100c0308070f421940150126640f940d9031a41607280015100249681d441208104400c100d00019028442c5100b9101600b40988a20046007604c0035034424500059031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 899982643 1250 899981393 899981431
    0xb0403020d0f05160305030d0e0c100f110624060414092d150d150203040609082701080705070b06031e160609120312060b0408010c0215 60
    0x10101d1102c01c198040c0b015529007103144028040744440c1c40e4400c84441e0000f240e8603602c44210312503c41c0c0f95540c000a030140c11a04c1c00051181201500500140700300d1101039009148203416058541c810001104c40c03500304030342e040180300e20b4200c0e119050740707a202d03580145050100a440460302e038840c00850f40b4030034004008036104d0007842500c040003141030090500b003100740400c0c0c90000d039485440c007500300000920070b682c500800791802600ca1044283c0014100c1e10280306480c140000140c03079459a16042c1c000d0320f100000900074400101d0800004000d1103d408a64000c0083c5041500004070040d2942842242c84001290007880304002064508161541c0028014144c58880d0f20205010424401c001401587d6503c81c26014007000d150640c4440a0000780c105260349600d41501030b4420b50fa03510005007042801d4501c500c200e071040c0c100c100500325488803980c40f1a1690301382402400c5002c08040144950381d850700030120400d4540307019401100b01a241071507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 899983893 1250 899982643 899982653
    0x16020d1b0210300612020d0b2208090f0a05180415020a020f0105010509010e01050f0f03100204050117010b071b1d07120e120a021606020607020f0615040b010507020a0605130b0403020d 81
    0x401041c0d001d03803801e286482010018200c03103140381203105803203040d00c0d08010bd0500428008800300c0760b018003091a01403040390340b644010240d9203965103503505660391380c1c0f4160f1180101012000da205002003200d20116801142d8085454410402000a80e982e2000c01ca000c29080c8030340500c465065006110908184a200ca41968040c00b951500304039031010074903002e2038000c40c0600650118003070080e0740c1d0095804018a00c072007400122541002c0000040340300c0c2d10401006100d607820004c4600b82a046400014281c03030300864100c500804500003228001c50303030040001c00740c4801c50b0341503c003449490495410840100100103140b400c1280d01c2d4448680d440035840341c080c0344004503100e50000800307050a0703030160406007000480603203800081b00c00a2001c1d0007180c01c01c020121700003100d04501c031003150080780f000d91401c0160b906108000c00a90007205003000410942d81001c01041c0c141090840c600006030f80d0311592180740110301000394402501510400860707 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 899985143 1250 899983893 899983913
    0xe01030b030102070c0f090e0102030432060a06090f05090c010503090703020607060b040b090c0a030908040302130c02190c050f011716020d1b0210300612020d 70
    0x1100160006213400c405803100d4082c217155500c0442c030764462443c00d1203419454040c0e60000801d0800035401e50405a541e88200244891420340740c0c14000d811100030b05900c11505009211403040e14854101a4010000381c10389028012009060018443c00c00e0b07400d1040f68072842404018141021203500110f034a0743c006040e41c1158459460044051380d03400001303220f0248910310006510b958202804140d50314110b49500c5100c0308801c1045100000301240c05180445c500000e00e00001d00e403003907182c0556040650080750244002e02003441c65481006440c0c0385800712088001010f54070f4075400640703a801054807011361002c003c031b0f003488081e01c0280b00701414000c989040d0006c50610217001120f61202c055071484c1c942450603014041540d2803072041c9055100400d0044d82da6220103030b00407009005071039070600b050049120b00360b6105118081c4640d0b0400303401e0205400c0c1000011800c80f600b10b0f1800800088241a0b03845000317155078050005092820030351a0700c2c0e820 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 899986393 1250 899985143 899985161
    0x27050c0415080712111005030c1c020712020f060c12100824010e0f0f040311010e0c012006010b180d0803150409020f04020a0302091e01120c0e0103 65
    0x496075540c020074108818024107000c0c282020302d01d001c0380e03031606202c007103003100441c020301414501d4040322900c0c0c1e0060850340d016001c15242c0c0c0c0d403000c9645070030a100030020a05012144089070007400c1041000c0e441d0543c0320b42c3d0342190210020b0f85c0c1105c0d126002501c40003103040c0c08001d549a0780d04c03031140c030315400a40301000030445c6135901441410039244d4811488104500201040101c2001408034007500d9001007001c070302e01e0280c000280320800507009402d0a1900d8000404040c49a12030241c0791425038000d00040603100c60456983c4114484039010a6000034800c00003202c01d0440080a001f04005016607460b2403810511a80300003501c1e0b00325102c490802c4040d8817080014080036124005241d03591414a1042c0c049605101d12580f10300d0805072007901681da0081c2e46410040c040310f0040c3d94a13035410040d03009100c0d01403002d41202c80e000b00d1050a03000440c090081100a072121141407800560f0102100d40358a4482c003c50140481401c140d40b09600840c41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 899987643 1250 899986393 899986421
    0x10c02070b192724091206240503070e060603160504081606030609090302070614090306011202010f021c080a020d0f0b100e03030f0313140127050c04 66
    0x107820308061a038541a11040d040000700b00f0110200504d400e010981da81c60084085440244400020014080810f5200d84404010392506450500229521070707122806404000300b010f8420710924041e41c821807040500c40d00607004000344100072503440350b100700c02c0213115a18540d2882c0031507106a0008441508100c2c0034400440c00b82c004000c5a00ca00c02d0f540c29403610740c0d2070300800405589440d0098694103060225602c002500081c103031041e9032090800400c402012489a00240a152051949485038100004e40e500800301401500350003a41c400c04200007220043e0383c0c807c903640307403100d40b01c040404550842d80300e40d2049400040080c0050b140800c1d00b04c154050320034146603103d5960750f990341400113190120700d02c80007a2403030a01110104103200042d881e40160401294910300001c00122100b888220818a80e50711041516848080315401402030844500100d5881114108034405224160450184541c084d005014070520790b02444060a181034580718 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 899988893 1250 899987643 899987657
    0x30c0212070503120706064b0e150105070803040b040f0b09011a011107061803060618060b040b0316170915011508041b0812030405010c02070b19 64
    0xc241c1e506001c2c0f03225100d200d450403600c1c0d420b45e0600b07004458150380081d4141d081060319440082c00414842340c082c40c6c0c2d01001c0e2170113a03121200c1e12054024041100d9007e2015070105010940c8484580600490414001a2239441005444c03a1140d880050000d5006000040004500c0c0081d6a03126200b051030140f11040c55581c0d4103008000d03111440c09945411500103014042010103c201401b46080302d260800240c0441c0c60f29076901803d010804200840f4820500443c0c03c07070700541d07224000300b14803542c03000914010003c00307640d20f01050911100064440f02a030544003030f80c0787c25001c5440e52320740c0100c0d07501d80350480400c0401d02a104138000b00300090b0440481c031039140540503010306c0004103410f48170403d05070024030480c402047e44101003a4015180d1f41d0017980300580d030550150403c001045500075a02c9a280e620071100114400b0012001640c000d41c443d02c001d006144450406a88038400b6000750760100c40c080c01300b94500400c0e45800000c440d42424084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 899990143 1250 899988893 899988899
    0x9030c081c0203180f01152603030702071a0405010509010c02120106030c1503060815090703050304140a0509040209040602031b040e061c110d060605090702070602100207030c021207 80
    0x2600303030f800032a0001007080482d43d5040f44848280249604094054001c1100c000c4401c580e130f10b40c040754040d403a036030940041c5070010164080006241540b001040300c0d00ca14201a000b0751b1000c25010b140741090611821021060f501c100b80c500341e5005031100d9003042c0210004440602c03100c101a41d02440c46400c03410808030038824003002d103001d9080b0100d028240001c2d401083c0b0040d04440c10145003841c00c00412002040380c20703a4030034220065400e5150003a243e860a03850307030000381c40d07070000003000188800049030801030950b00740c9252180c40e5a480401c070039160100c0e0003030340109031600010006070f02503004550050000031002c441e014055102102d41d00300e5086071510004910a004d03540c40c0c1400b0890f2080710410f1110b5031120746a58100c00a10b00c060700c90701454806028208015107500401d02804002c0d00345145d0f031601100096995000e88210b07000350003412002c0303403802024021100455015200c044030f0010703a03801e1201ea540032411034606800703030440c04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 899991393 1250 899990143 899990197
    0x10e2b030f1107060c020105100b070f030509030601120c150806010c0203030c012d05061008060d14031b0303150607050a05060c0301030506152d2d0409030c08 70
    0x500f0b0b00300e0182e080020b40840c249000790031150301174000d21540c86907d5080240b00e914100311180c4035030000c001c14501c202860b00b030300d540c040d804070154940a03a2002048800c050500110340c1406030084651030faa484808001d500410302c882c0300000c1c6c1600000b41c07154001c1d0480c00c402407001c3c0481c2c0c035001c0903c0400d03013120b254801c054403101e00031554166800c15a211010407892050041049040040005040174040c0380c690b414014001c0001c0d409984042001d0040ca4000c0c4d6000742040400c1d03143d98903548044800300b0318183d4001c40002024000095a11a20062524071400310040c0d003003000f2904010b90840b0144030b14030066000900501c0303154092080d201e0442d40360350443c03034018100400206035070000c2d02d0010f075512541e0b031361003501500c05010003030242c4080244001406030300c00c62051a40c008140c192505c002c0c00402c83c020004001004c0300c070f55048005c400300000d4400410001e00000c088a0315840480d4101d07000b480404904406443c22a07215502 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 899992643 1250 899991393 899991397
    0x150609110d05090a060204080d0e2e09050a03150507020703032f1203180309010203070b04021c0305190e1f0207080d020c040b03010213090e1e010e2b030f11 69
    0x40030300541c01c00341108008582100c061103c1d11403c0312808005d4076907940d10302011009050f484000030101c01e499034164004d004442c0a40003b0700070048554490810646800784802c0c0034004a1804001466140c03012903a0801e49034542c0d210805e04802003900120002c0301d90b00ca002c40046e4000e4024000030030050709520100c4172405c0b82c0c4915284104000c001d50800c40e42c501904200712004660f0713070100460326502d610425850007500c49002050078030350000340d01a041c2c00030341c0b05001415003100c003a041d54408000300f105900a4010210b07000b01c0d6148000e0740080c1c0404507004062014662643c1a413154411205503c0d80ca0000314504800900f031711340075800501e40c8140505081c0540a00c0711010303002549400c50740ea00c401100c030384501c1108105a55591170400341030043c003a010406400c40e5590807c40c003494190f500a200c90007900725117110b444a00e10184903000d0f184d0000900211a121050220ba9829070217080045140d00c0340ca6500d10f0585c6207134000d880 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 899993893 1250 899992643 899992649
    0x5030a02160c0305070f03030503060103110712030b0a080703022d090c0c0601060306051f02010605060a08010503150c0f030907030b070c03080a0510121509150609110d05090a060204 80
    0xb02c0b40700c03007031450400c2c0303042241580106120840382034060010940100c01c0f260050380030b06c0d0000b001f02c1c0140882b0f04600549a004180003d0100030083e00356058004084130407003103503000c10f540e54404110b940c0e040356100080d00004440b10b80484407101d0310a0035500341d1403559240c00054094002524000210340e000c009035000304003502000744c200074072405059203007030802000e410000006c4001e9242d940b00c0c140c0360900b54280a40c540300b90003d00c0104009001a03444810052003c1d0401c1024051700e03010b8852081044031800001a9640c0201007404003d440e1003980885c01241e80e1006190021741d100b004000070014a024070321500c0b444042e9203000c14100103142c02003401401515001c0d1903410325007440510b01f07070f01220004a9001c45100c00401e410303440c010035503400c81000701c22050704d40110042441302c0210110000c0488110800207980c8800fa06e408880710302190404c06070051081c034100c072140c0e52140360054150021118100703e81d80d284020390b070080d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 899995143 1250 899993893 899993903
    0x324031704120c031a0f060d060f11070302010b0603040c050105031803030c03060103150e070c05011401141203180f01020109060e0d02070b19050a120e390105030a0216 74
    0x40c0f000c1051044000d80d20640d95a048041043d40c10003280810350010064442841181461003150030803103103610100c00500b03a280240140380c40c1d0515614a034000c40d2060b030140d4240b001070f9031240340c40b808880c880c079480441c0b45a05402c240044503c1c1c2c20007000000c0f080281d00803050070040810103107109811046031a540c91400900060550b6101c0d6400c40080c29100c209000000022441c540d0040d41c91402030070101c9c0608141e4050503e2a0085c000b401c0346a00110b40702c642030340c828030f5000c81540d5041e004032040203038503031324401c0791280b009141c20b0305140800751801c1d5820b0414400c0501c0007096024054559108841c1c40a001540c140d000f000312002294051120700001c00043c1c018606000c0c501100d2038100650040328020400e002600ea804540126010307028500c446104002c0020060100c80da18120410084407250700000c10000034001001251505140071840c0084d414141005646580001c3d0103103510b03d800703001000c00004119800f6038518020703 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 899996393 1250 899995143 899995163
    0x12050405060a11070b0612010906140108010e120d021308300f1803070e0f1b04080318040f11090f010c020d110303091f032403170412 59
    0x42c008000700c1c0c1c04442e26a250010920251000c0b03900e0030a01ca62110007603807900c0d80c541d0a003110b6401804903000051909260000707a194040c0859015411703580c0d06402002050b40207128103075900301d00109514110b82c1003012010926080d000740800032030702030b01028415100e04c0ca084c1002c550384168206180a501c83e0313440440201444920320380110b80d4549024441c03000c00c1c00f540300d079001d003280b64500b610840310903840c2042007030010300048036404424100b80004031200701c01968503054011403100d43c400000e052408980c1162501c41c0154076280b480c522025510806101c40c5600a944501c1001c0ca40b24074080d0840c2114007405444d941c04800d002c20a001d00440c506604000b500c4542d403005032941498411450382240c4840c030040100c0d03001a1442c484c07440090340200009544084100942c0b803401c4121001e61020320129040d0700c01403520264640d140d007540b80010f0350404c0400c4414501c03010348820201600d10703040e101c143c00c01100d0345200302118990380b0303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 899997643 1250 899996393 899996401
    0xc0305150f010e120a020a0305060f0109151511060c091903031b0804150306050418030207061803060e030316030207080702010f1e08180f060f0402011205040506 71
    0x10102009803400d000c940400c03054001000090107140140c00e2039014041d11540752010000c10444040038a03030061160403480d44a14207240c48075001e0b6007036045441800000b0072101c3c031900406403690101500050050b1030003490521a102690b800d00c184030380c071760001c10028400c0c041c4910030702551650581c0c0c4c401a00c1402100e10445001c00c440d200400c200b4000241d0140500d1039072250f0412b103040403021410251524030659110030744a440d58100c03100c910350143c20400c1250300440f402c10910600312804405043d03c00c400500582101d02c0620009003c1d042204800f010a0711544030070f83c5030b0f83da400484150700001e00c0790754004400c1010020010a99002c42d142c4c0346019414000b01e90740f014101d000d0060005c1c184080e0610107048a031048000507140c0e8400060002469a00b40d0054100c410542c0c00300b050034040301c650340c03200340300040308a06504100010982c40d1b4491410011030301c0060002c9040103603001040721000864024540030380d009801900b21414 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 899998893 1250 899997643 899997661
    0xd150c0504051809101d0a0c090608010b0d030302130308070b0a0c090f05040207031b140127060903140403031106010f030b0f06130c020a0b071701030f0201120c0305 73
    0x4161041601d03c0007035000b000000040410105100c140e804408111154000131781c400d0040c5a04440190344554048001030102c15240c2c54100e542d01541008001c0d10fa900103401d0320840141e19402481d4182c0300703000030b8030aa0080035903010142103403d6450301c0b0f980d0418250300c2441e0070340c2c07106072100520414000e144102d00d00c051490030500c4a151601d10103942c042aa80304c0c0c1c51241d030340450200181405003020300b038801445940340c96580100e107030009201c408042444015884c1040c0112901102580b0091240300001d804140071001e0f42c0300c4014143d60700c0110200700032a40e40100180203038014002440c402c1e15079080500000040501c2c140c0305034015145c90340c401c03000b0000300740d001c5c41039600005a40d41c020a00d41d50413002c500016044004034690310300e0300c01281019540481c00c0d01c2e0f034510940001c00c40b6100c0c180d0031941c184076500d0301700480d4080790041001aa04054107a540da00c1814886540b28015a203e130440d2222032142000c6500c850410482c52 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 900000000 1107 899998893 899998909
    0xc0807060f181104053106020a090801142e1a040501031817071109070804110919110c030c0a0218010e04020d150c050405 54
    0x40c6001d00c14140701e100c000c0036183e882c1c0d084014641ca10f098000d041c000c02d20201030b07041e1085c0d49140500706081c88a05008500031030500500014120b0020704081c003400d4403000011440c101503e42918006044000040111020003e001e60b49000382980300080090855030028240d68100c52034000b81c001608061603122441016010000240150b45085c0e80034031044050480d90720110000050061980d050340307070340e002300208070000761034014090700d40084286000f901181c032609041d02d64000080d418000c01051046200003400c201c00159484030203071a1802d0403441c0101000c408500054a90300030384142000b440549035501012020b4907900c0703901d038401e2540c1e80e040c51412401107446481c41c507100f100080469040360404107120702c80341e0f1503900b089502da0724600100c0c0ca007482108003504078462480f0b00010310106850302a80d0b141014104080740e = true := by decide +kernel

theorem cover : BRFrame.Cov 899820143 900000000 := by
  have h0 := BRFrame.cov_init 899820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 899820143 ≤ n) (h2 : n < 900000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
