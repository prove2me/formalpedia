-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2387
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:33:48.912684+00:00
-- url     : https://prove2.me/submissions/d0e658d2-1318-4593-a697-23195404f298

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 429136690 ≤ n < 429316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 429137940 1250 429136690 429136703
    0x20a08070309021c03020141100302040504031b0f1a040c030b0703020c100204030b0f011805061804031106070212040e0a0605060315130b1e06160f 65
    0x203103045110348107010301581c00800e0700d07444031140346409040f0090f000c02a02195250001641006250305500c1800f00010300825240083c0c111a070720420b01804086100c45800c2c0103020315900680310680a607034045030005456240d40c41c003070b41c90760110044080c42620840484040c4010087c2c1c55400300d003e1006081e0904004231045202c10040390000c180c0080c2800074030201d5040301e070599001c5442d0034014035162680410a1400046013a0300484940000d824000c001075041d03015000002480c00a0a5504ac80d1030145020118581100b5295481c400a61145e8903400d086800d2011401e914400d820305080040642d80c0300b441604a030b00c10480420000c1c1d1000904e1080c12034030090050409007040300c500d4914401a00381000c0035100d400100751340d502d078801940104007031885c48685010700c030180300c94002072944403400949000010742c5d01d516142907001000c3c04030460315801103841c10004415005400344040440309500c041010090034150b41e050b030b50700810 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 429139190 1250 429137940 429137957
    0x81201090506010210090204150b0310090b030d03090206040315200f0405010e1908160b180907090e0a09031d1c050f1b010e03010605010e010e0301020f0706020a 71
    0x540200030788606581041c0141d1201e0700c5120600407550003405c095100800100c0e400310444d0f0102c145080507008186110000003e00032904840c083c514001c1c01c56034418058101c07580002a101e044441000051580310402c400031581c0e07020455000d5948200346200c1c61000058140c0100304001d030071074000c10049040c3c41070307890b000305072510100c80807003462405040c04011545000c2c410f050940245504060b440a0180301079804090013401e0000c00b10f5261016915140c040903610001843d40304128140606040403445800c005060720322907072946035400d04541101c1e5035400140d5480c03075a0207020f00010950440313030310180250345029444c4059540b1601c903041d45d5038090303400307542429030628800520703046561850080c01920080c90040343d2103801c020640510031051080c5801e02e1070703c0d40e0040c1c3d0f100030f00c4c0002d8008019850415002034400c0c1d45040750300b4184500c480b043c507110b580940407a404080011704154036490705181043c082d41252110300e0108560303c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 429140440 1250 429139190 429139199
    0x7032a03110604020f0609030c0310020a091d070f020f0f01020405030106091505010309031404060c03080c1e0306030a0f050d0e09100b070606150905030f0304060804080a090e04081201 81
    0xb9200d401075400812084020512a042080c0da80c811250690503010340751802e58280d40900c40d11250300c004540c0940d541c2421003005142203541c3d00116019810f4007000c580c0240e900300c5603940200c04d400c0c06c18074240b0900040e40307003040000344c039281840f405001003040d0b507040d0050001c6401c268020b00401da10ba041310b80503184000140d07000004140b20800096100f50054004d8174001d041880c9044040c3c480c52000e98040e0300050081205280940b08041c0d00501f070f280c1c01440801c0b400c1c148102c0d00090301e0002c1811040c04c4030340380d0100c0480c2c0d156405110070350656600080900c0e80b4003151800b10b845040031100311b004900d0081403459141403104116228151505894040c035061290340425500300d0002a03a403140c0d42c10020441c0951004001d0181c405502d64900a619140c01c06141c100303200000a0180c00500c4100840364100d103c1c07a07003180d07010400ca61250501d440480d040c0c210b50340402d40041c4410113000a1018660040c07030100d1041d01031101d103030b888 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 429141690 1250 429140440 429140443
    0x714131502031606020a0903020d2d1101030b1210061e060807082d04050c011b080c012415020304050d06020306040605100f030b04090506060607032a0311 68
    0x510341400d003006243e03040301000800c0d0360300400e040f01c0756043c45580b064494010480c05c012031042200e030400c40001a1044111819220034060208c0051100110f13030355a032854001c0d148820181070644454001c4038555a00d51605084400b400490b030041d00c0503040075014180ca44a00030404112035801700c8400c0d480e0b210307002690b2060b2039188080d290581d08a4038030038002c115100b07140b400d4091071090b20140303a403000c501504480c0161a401c0034102181014210348825050220000d0001c036a111b9204079800d1041d0070842117034075012007540c201c0c090400d40d4070300340300303d1400340122041c030f600c0200960607a181c0070440b01800f003541d103040c0d03600d11940c040e2076844100c092401c00019065001540d10140242010880d25906c0c400b24000102030444c0c1d4021402e451400301d1184d525102d80b004895007103805010000d10303034807a60b03200c94018001a0082500050550a0601500c650781143c000024034442c50340c40b50212004516040608900041040c2c6110448a10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 429142940 1250 429141690 429141697
    0x18020108011502030a200a030806011214070e061213050706090305060f13320c09070e2106061002060f0a18020604121704080c0108071413150203 64
    0xc2c94000b0361604500304002c3d03400c490850004e103030103880c9501d20300c1c20b00c5d0300b4064004205d100703450f40496400e15400161443d2611079030054820701c2c20b001c446121140d1060550031035901d0900c2072005200c1408121144203c030340010000c0d9074072052001c10f03030302c8039403106030240a402135031140d9854600803214000588409420f552205010580c9460520702654102c26a03e071041d10704042540c0314100c1c059003402080900345a40c0b0490b000815102c40e00c506038100d031003d4a119110100010000b82c0050704140c00c12013030b002c24400644520000b11021000311800d1610300018180142da5004100c3c0c00c0390154681c075007040c440c20b0000800034021030000c0601035580d601c4070311820003080352500c1042404545c3c22602c0c0540c882500a101401d140d00c051452440c0d6402c00b290480e10b600300b501c42139102008201b100d040042a00780c4600400d00e090401c3c0e84a69404540c08810280110030100002825401c4000c2100f4000c5c00c91700d101c0c1020119160606003070743c4901 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 429144190 1250 429142940 429142979
    0x810060b0a0507060c09050d0b0f180318040204170606041a030a020f011206090e070819081c1406040501050109350601080a05060a091e0c091802010801 67
    0x2e0b424020b040014280d50002c4400c5951494900341d0070b6585d00c0084e01d00790b2250011b582c00c230381d42000c0c80b007131a1403030390907644c00811a40028480314103107064580d21311486001d40d806d080c00b03100840055540d501180c00400d049403a205400d1072650000340c072003005541d042e206600c0d1000004819459002100c0b0f2500c00070003031b0503280d040b42c0038010f990883d295210f0400c4a0078401031000701032071103948058020160002040c2c4d0044034001d01d011426000340b07400c0d0713204030040b402c8d14840344254880c45511542c240e8079100b01000c0041013990b501c01d4617a095041842c0501c955901c1c0084030310644007110107205503660340300152103841e01c6000e41c4420001480c00020b00d0003004c0c1e12403544041001e03504042c0384c80040c0d5203040407000c2e004088a5004050104284030082007110341100d100380d0200800c40e02030750341001c90a0108000228600c8041da0001840355007008407005040000003481131400d08039840b84e0482c0e03848412400710b030703070f410011491a100d08905400031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 429145440 1250 429144190 429144197
    0x30703181203020a0c121d0405090607050f070f150b0901030309050f030309040509240105100e040f090309150203030103020d110319050d090602030c15130c0810060b0a 74
    0x1d50091070450196100514030f00500010021000004e090320041e5504140180d0320300b80002c503800ca05e103100e0078084008070700c11810b001c140310740317542c01203503141d00801c1d58100213544400c44515020680030f10480589070500c400109024481140c2c0384042d0001c11400403c4900414410018991420b000203400110002420300090a111301a07035088400101143e0408030107038000b9066502c2112142d415400403001034420018070044c0900c043e01d106809051503045c1004511010400c0f1a5001000249409040c0f1601c8a07401100c40514181e024010b4602d9400c020313000a845101e507528041d0001c55102e126440401a01d060b01d600070010040041c040d00c0309841c0350881141141c0c103006038808205421003002c44d041681d4440c1029042c0c14440a0014002480a80c00b140035074104000007543c801022603652a1280100d03008103007525001020071061044540c0205410328840c3e000c101880c0005061811201c885410b01080b0b8480601d14020301a061000001c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 429146690 1250 429145440 429145463
    0xc0e09030a0804170405040218040b011106070f03060e1303091505040b0304080903030a030515042705010e0304080124050a170a06180b01062102030c041a03070318 72
    0x2510060014580c0c0ca8401d129405c09490b10001422a0301c003410041c80c000c1581c0d86050203003460700803192103041c2400e02c4d0400007a800c085035210a0300520000803c0301015040c030013140a0f0340720001410f84d0304140321003441c02c28241c204e40041c01809a02080d8504000915a0b1076101c1c00b558200342540c80504085c9406440c002c10b82000d441110a0801400444003c1d02c0c100040d1148102658010405041c02503c06032071440d10501c02c4e0185041c508a010070302c181d00c0540440e2010ba40b02600d140003d03080142c010941c4020341001400006400900140f0541203152103101a0302030402da2803595554032101c10682c17240c2504101145410006020f48601c000904800002507400d0841c40740c0d1003c045520305030030404005600c04001090141202115001d0520340c1004550070b0302c11814018070020f040b0700c5804a50f00003001030b03d00809942540d005000446031400c1d0545511108003442d002101c802c00042c1c40c15008402c415501c02d048401142c0043c05a440d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 429147940 1250 429146690 429146693
    0x902031b090303040b0c06010603050604050408031603060816050111010605012001020c0102040b0c0105070f2c060301030320010510381b1513020a080a0c0e09030a0804 74
    0x1040c0c1c12200501e0780c14001404001031001420001301050460000a04025814820003604581380a805180958600802c0100042c407180c21203030080e15207201c4800c00010080c040f40a010140c0101039a802a00c0c1d0803020003601c952228141c1d402600c801d040080526061070803501c1c14858103001a11000d0b0344c26240400000800226030884005440c02c0240840c09013a40d001d54005170070494000b403002d605040a00c1398980218a51800300340e08204800b004101307a044035124805160307011540100765041c21003c8003400c101410380b035203c1d0b0f900c4c18094508806800004a0501c000600011802c0d041c465280f180c2c00c0111200e180c00e080490b910202010b0040101c510b1a44c214040407602040100c200102802e8000c169241d0350314121a400103801e0075500311980c801d5030a900e091000180a036401070a28054054405590000400740580d80d40b0003010350240802e04c0061208028021060b030380c0c100240c0d12b00351036115249640348196201000001c120001040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 429149190 1250 429147940 429147991
    0x303062d0f0112110d0608300c0a150518150c16050a140111030a0908040e16080f0f041101050415180506030f010608041a040f0309090203 61
    0x26003000c41032400190402d002c03c070242c11190180c0407504102c001281c601c040e03802d107015a4014100c0d24002d040622104803091081c031074400b03080465691385030100300300d26002c074041d611120301e03210803207035400080c1c02d02c00048a00040d24084060402d80054100d00c840240c1031400e101d0030008000351100a1014030128401500a20302198200040c03400c1402c4290345510050003a4040d101701d440c3c81c030304640c0c0140001481c02199040c00010003661a601041da94010314807100494801183e140002d95071145030421403070b00d1040790a0201d207103162501054248415140d6810940b22545102c117048022620039440400503030025000034641d54100c904c050060400342e00705921041001c3c0b850060b0200200010301c0030b00c90341c0003801200c1d0030000a0005595035403860402201500c0c0380ca82c140110020b0002c0000480c04105c02c0f00300d11000980c5400c10106e071170906103000d07c050000c24805070001042c909005c110b51b000f80c400c80b80101844a019407030001d1003403019 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 429150440 1250 429149190 429149209
    0x608060a090c0302040c1e09050d02121212090d020114040201180810020a0e090601090512030f0409020306040f052502030f0409050106080a0b1806040f0c020303062d 73
    0x202c0349900c60038400801030b251402090501c0c24a911444c0c1c00a05604001d030f81c005541c5031074410409a51401c0281e916030a41110b21079030140c410703100c20020403604074502020b003d910029003030002101c1e18070700100b41c4070038080c03502d95040e59262240d00a0481c05e071005404408075034001e020205c1d0040d80510521505e00040f1f01c2d04d4a09180c2c0e40300510f091000c0c0460308000180c00040e00039500e90321150b0303146114811905590346080c114002046414030b4011340e801642c1c100039024601030700b003056801c400600688550707103580741c4078000042e400c00d0355014022070800440c081c1c02d2480f800b4241c4680d404500340a00380701d94000d1500d0005201c100c420640c00100048081e1b8985080108050007240c407010a441d4509140140345060041c8880d07019481c0c644816859074980c40807428001c4841c0031141c481d11b42c500040d0040407004c54541d642490000544450313a00032014501c1030300d080b25910412100000711208001c0f09019500d0791170a0b51460700c0b114502143d14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 429151690 1250 429150440 429150443
    0x80f0604050a0f0c11010b01020610151b12090803070317060d020312040501090f0f06050901140a020a0203071226120403080103170723011e0603020f03010608060a09 73
    0x1c260510064030342404c40300c1d80310120002420341940000d64242c24060500700400a2000300010701c1c01564000354030b20107010f03424111445c284070790940c52003948041110781c0044540f841c090b4442ca001d01401c82c0503450140856601e00e0001102e43c808020389100c01c0e00344c0ca40140e0b1912850310031400c1c90b0f004056076070150584505001613141005054104014800520b5407542400005042102603500040a82d07103034040910941c0a001640001c840709414140e44072050b4a005860030700f031000c02a0000b10300480c100c180150b0002d5291303c0d660007541515034003030300da00603142080b24002014000e41c8002081100301c05002401c001407200c8030310161b040200800180301191030984090340000d507102c0c01407080c80700c007210b01007001e8082c03058207142070010ba8948100b080403241241403d40355058941d040c880a410440c1c10000171400260540d40c041d04d42402410107000c103900611b850b4000c100705050503c1580140d440c880002c004643ea62a60800a0611850f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 429152940 1250 429151690 429151711
    0x601080733020f0102070605100806130b250206041211030f07060605090c0c070b1812070b04091a03030c060c07060618060612050402220e030a0905030706080f060405 73
    0x160036507260f401c1c8007a100661003a04080341da404c10b16011a64810aa003254805070081028401d00c041ea49000d1250700ea44180034450954660740d240b042020221030b203030701e80081c50128060956012076110312641c0310b00d8581614413810201211151802c02b081d007801d900820050522280c2c040c05010000d01ca2013020982580b00d80104e522842c0a980718000d400300482c020300000801d00c440070207007018a000c281415203040b0312402468030788c60128020a84032040014900d01800a0b00241c051032800f195075564408481c00100328400c002c40350390300d01d10500400c40c40d0100890349007180240c000c16184d12900181820780d4040030048071000d0b40d40307400080340c0b000a9500140c4410005000802c00d1a00102410201781c613108201500d01e800d00b007200694400c4d0380b03811485070001c02d0b14021038135001800001e0860174085a800d1002140c2181e085520072040303030a80b2001d9042d210820707903c013001e6419000c1900c429240395134420029186003030960100c0d07401b0b82e2006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 429154190 1250 429152940 429152953
    0x1050f0d060b0d0507050102070605030c070f0807050d02030a0f08061e031c0306050a0918060e010213090605010207060206040b0f06130e1b0d020603060d02031e060108073302 77
    0x400052070f12506000480741600002e80070049503070148003c200405090401e28035600e00254407182da44030f480c0340101200607080d103041c01d0001000550321480d80c0081240d10103890403c3c0a03540360024084900060a02c0542503401c0d4411b5101741d0060001820051202000a2500301d41d081b4800b0071541503c00c4950b581404058030040410410860302c1c0040c0142c185010b0102e5540c040e0015000203003003188009080c040445004882d0780c00c01d1000070034246840c03907540648140c0007406c0600c0f164139800310f5150b00c07550225003140c0c0240c00f165065541c9100698640030102c50242811110314009415141c2c0c403610140e22002c02406480010b0060900404560842c0d1402c100c6500c04600349a00e66045516000754400480c4c3d4250508610390026003075101c01443c060007680401c00e4402151010000e540403078032482d140806011000c85003550342c0d502442081d10b203100c0c58000082c0d64401807884c070b03042e50203441c41880c40c0d504040c5080e40310b05402c02c01030440c41104c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 429155440 1250 429154190 429154211
    0x60f0e0406050406200406030b0a03080a0305091011041d070f031a060d0f05010602031813020f120f2a130b0408030c011109012f011d011401050f0d06 66
    0x1e02c0050303403800111710000d8541d03040a50050848450300c4115024502c007410604c00b2404680039115000f41c00d10f00410075070786019030281804d01c07401032104802d040614180c81c1d00312101c05001074508060308106403681c1400074801c0c091042c0d65040104035034400e608403040c800d42145098802c8a4802c0c200310001c40003040a03a4003010000800075030300d103803901c0c1d421700c00c0c0181740c010201480110b041c51a504440200300c41040d013400d11800002d03100e907243c8001501605e1040725010040d94907240c0100c5003071030600381118031030b03145199070000400500d500c1054942e09484207210300c00e02c1c0503400030480309031310035410501883e80070400011b1150b05400188081c0c00244080c545071640035000b5402d603440800c1c0e00410305414050056980d03440364040c0c8d81c0044440c10340700c0c00b000d04000c41d0348403544241e01d607800d0b501b001c41070403034403180d007503801c000c00b081100801c40202da0503594004400c080c024203070f012a03e1a1001c4e950f00d48050450f4855015950000b0040e890 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 429156690 1250 429155440 429155471
    0x302061305090f01050306130c0b0a0905031002070c1a04090209040905060405010e0d020106153504021309122001090f1209210f121101060f0e0406050406 68
    0x11a41c4241c40305a10005200c5406c1c00d103d07151f0080304480450800304416610807500c0c038554001d07140c14402c0482c10b808101e1246080308002c203400780581e0307105201064100040d600c1420180c03618101d159000440245130031104070341e1112111010700703041c141010300300651b0004003a00d1781700303481f000c104021035024001d40b4002d510500000441c0303400c156005090483e0444030000307591600404100102d08020840a030582d0b034940064405d0b41c540344200d0428240d000504103c000c0c3e0940d5a01c8100714603103e0060b4001c454814481048030b0060003600c1c400720009000c4140f41d242c46091134002c503480c0c120849442401804003a032030a0b03050840361284826921500d8103130004060040746030303014011100b1840c0c040007031421310042c5507042e500400c1d00034800c0502c58140c8280840507480540069020440c541258000d0030010074800905814401035441c0003c0081e1300f40d181c560010488482e0400c120701da9846468030002000010420b841c101c0c1c0f00c00c68614000807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 429157940 1250 429156690 429156709
    0x303130f111e0307050409020a0306090206130608150402180103111b0304230a170717010c0e01030606020a0b090312040302060907060f0903120306051009030b0f0c040302061305 78
    0x780001004100600d1a08051134111654402c90295141602600141c5c403078482004c25a82c12141c0030402511501c0480e903072f84117200a60702400701756000403d6441d844200b40340680803503c0c080503030191920800080b0f114882e69107100c982e1403100c1038aa54081d81000c4984074011102a041c84d002c03558502841c540810780c84e003180c00000f81030007060200c407a020a28070600030610345c550904008211a5141401041d82443c42c0d295182c56001041000e1400380100c52514446502d1810650303000c0d003010502e100100d2031f980380310311041d4801e1240c08204c800b02c1c0c1c0203101010040d21941c0c0041741c050541c602d0f44c0010403040700c071079040d03c03900d5004502c01d9004140c0341c54140441d07418980b050b0020010020360405034024158011a25410340342c00c0303846010700085100b01640108115440307540c2102c0140d40300344000c1d410964a0341142d000303035080c0035550381e4045030040c40c16007100c840503055420b000900160510101070085d1011140300e00704940d0700c1d0b0740066455038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 429159190 1250 429157940 429157969
    0x30308010510080103061821090b040302090106140f07060b180f1504021308071701020306010f0509011815110309130b01021f020304021003021602040b01031d0a140303130f11 77
    0x14848c000810709561007185100100788800447e81802c0c1154000350050b6418402c5104000c200c0708080000d150f95011240103580401c07e050755012245040c2c8058160603440c0b6210301100303000480101c0c1260701d40c030311a40c5046003d40d0150b9a07c690f0b1060007022005041c0c0042d801d019007240c4010b07482ca18006840c9001c000c0c40d006141c09035071249400901d5680d081030340144148803407079030070124154440300300342081c5031596452030040321440c8818003038a50009400c0c20000c0c1b1004540c80c48094412503a480c10f03450fa04900b0540d40d00d00c26038407801d40014040701883c5004480c4c2d031058002000510540c0c0c02d404030310850ba940c02e001004440364690b400420303c02149040c0c12600c0105442d42829810109000c0d181d5100708418800039004036142d4001c1400c50784654000004c40f025108000d2402c142050780a81e1040320b02c4003212100200b04520036520b07000001c5d0323445042407020760100c01070f0301c0d0340c1c8a20300b203448034084940c01d41400b8444e1a55494190070442d10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 429160440 1250 429159190 429159233
    0xc090b0705160b1201030f080906130612020406140904110d0c0e010c030203120a110f071202070302091602120c031e030105010c020f03070902130303080105100801030618 75
    0x307841d161441c00700702c00c2940002c041074020441c40e440204034480040c1100c0d04a40c2c1ca41642c040c40c2030816003031155078156540b0001c0000d4005404203400501e5040d59001d0343e4000c08000300e400800120b01c01e901400c4042820655400942003201004140300c1d1005031002ca002ca24448090384aa00485c5400361003907202c0803440441503110b4155284a1004d20f0701c0c02c0380070110b86000e900ca200d0444a020f002e031a100010ba0400466000341500400100d41c40b581c40301c2c001d00005064100c40310886814000205520000d44000b0b0060b00b41c030b800a0103c19542c58052984030700708102c3c810031342075001d40c03284080c1d4034802c10302500440e1144006966100422017a4501c054003e4082c480c400d60103000600080c2da10000050049505440782100741800200180c40e044941e40489002400019a000c2080751400154101c1c0c1c807070340710218107076210b2081007203188203981545d0020b004503004001040c41d039004100600c00d000302259602c2d07056103407144040c03c1c01c032025941c0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 429161690 1250 429160440 429160453
    0x30f050f0706230a080c0c010b030708031c0626010b03120405030d0906080a09020316091d03040308070809190e10090603150e190f02010e09060906040c090b0705 71
    0x10041400810350780501074aa90f00d25041c0c04d020040c00c800005000082d40030404155688408401d60000f6402c1c00c00a0485400c5981da01c000f9940358401e03c42d1801000e01c0e05115a649070403030040c24140c41c0301d600c071111020b105140d0548800712020502d1a15034031080d00243d0368505201401d43c1e0840d0060b1940d50360f0800e0709042c42c10580c00b44040c100460901d0400500358006600c039045080d40c00042082411400002c1c03404692029050b940c550b8441c0c00101d42815034045c000e241038580e0003142a155512009403030780114400508801c030704101a400103000b02000301043c100040900c0c1d000d86408007091100f41e01900444042141c40c000d10010780340303405080c8000e01c2c610710300303001060455071f84411000000c41441603841d241d035070300300b12007009000310a0b4203070030480d00d0240f040407401c1c0090350146401081c0d01181704030610791043d00b40100c00500c90303000584160a40d48906003803000a00c0741d07501a0041100b004004580c2d640c01d10010541e03e40138400038a803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 429162940 1250 429161690 429161717
    0x90e010c030509030a023d06030302070b03010305070504091403070f02130608100515100e0f0103020a1b0201020106120303050412080405100e030405130903090e01050a030f050f0706 80
    0x32248050f28201d504d50081c481daa41c2e4503070001d010a2100360240400c4070b84210550b4660403c880b801c00d901800a0118220150304150351003841240c1c02582200c0c01a56504041c1d44144000c0c040644103403c500000c0c001c60038182c201480741d82c450055030414074428110a4151780000d0b004035000c03003009044000b0751808101c44800103d203990204119850558403554540c902085201410b07111030011307c07640c40c415180c0c0541a00580038901c907030b03c4600300800d1014017500003442880c901100b001194401e20030b40c2d22101143c0c464480c0e540c00980b04080346c4c00340c0ca00032811503494070400320304070400d44d001c0c880040c0300e600c010a0346c2c100362810f4904800e43c2e800c80d0040100f22403c0002086002800e60003800350341500250709444030f0300546c1144101c1e08034070380140c5440c075203042e240c01070303441060031720f0203951018452038850005164110080c45040e0744001e8901092020440650301e03031032840d101d0342c1205c4043d004045924100350050340030501141c40c1410820 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 429164190 1250 429162940 429162947
    0xc05070c060201240b040905060d02100519050a1d03160b0915030f0f220b07030b04050912220b03092e05070509030f07080f0a050303071404090e010c 66
    0x403401308850460b50702407400c007010034541d4000c6108011203183c541d008a5130719114101002441034014120740c81042071001e01502990100c20300191a5041c07417000300b80c0510807801c0d41d0b0707000c510f90788007080074102204210789c0200c50030700980d244c0a2051107440049071207680000400c5900340040d122800c28003000f050b681070040d5500f00480400801141c010032003001c0e075000b0a1284c1010040c0c42e2039405400714540c000240c0d5110b1040d15004007800f501c1003031180b003810143d034184207c194030001d020070703a42c0603508014582e1140940764641040c1c0ba01600c018010f00d8060002c0820b5200004041c040590281440200000c1400307020b00e418000019045403280f00b284088480e1008144c00403924403446230100e9441e400314244921540440d503155a0080859a00a81107000242c844200c0d200c2d000c0503104200c1c601950307140c04600000440d812501035411540d901d101510841550304500308142010800800c04101c50300c92090f012440d04000240c1d0805181c5c040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 429165440 1250 429164190 429164231
    0x601060816140a030905100e01021306020a03080610050d11180d0804030206091c150b01091805100f03050d0e01090311010c020310061d060d03050a030c05070c060201 73
    0x110402c196120800c851480c501d040311880c0c0c80d24500041c03154140d0800320304101c103040321034040b141461001c4e200c01c2c0c015009040c2c6494841c0640d1184c81c1e450b003080e6a00d40e00940d00801141501000034410b160004001d44d090314141840e034540b03103a40315840c0880d90f0b0741108071003402010601000e0007008080814443d40151812040c80a0544588005000341e200080c4a5030000603030f6001a02c0d010019051454080c0d00380818000ad450009541c0011166043c100b920b400e5889039107600c1603544100307e030b5080f407407090408403c03282c140c05408000d11841000e03401e440001240300175034981034000d60082c006081004031001e0010810b41e00130b00481d04100b07001c00d00f440880e0455210b201d04030001d0801d485000f259101007410441d10707080110800c2d01d048400140c0400c00b1920381807055201031404640e0b0f07542410007002500810740903000440500c9201002c0b4029071044840c501c15003170607410b214507035440580e01441a040200103035116040343e288040801c100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 429166690 1250 429165440 429165481
    0xb04050708030906180105070209151201061809140f03030405010b060a050a030f090b1e0a0e07060810080d05042916060b0a030b160f092606010608 65
    0x10b5494080020001003050050b8400c141d590180c401c0c681d08070f0ba024004a0f0115030b8090031002d850700e00150210369001c1d002a12500520344140c84a800d03100600c00d4106458072108200c02a111513a035240040c0001030003150307588a032a52550074036000708511039410400b44000d540d83d00c2c1902d841800e6681e00075116001d0074043c805003070400d4100003079851003941c901c0c0008984160859000280443c0d29001e404071401d4400d2000c8000c940403490640010402c40880e15240d4500f0607048544203c4000296002044240700340341c400e84289401010064202400c2c6440d80107031810154005500c4000c68030000b8104009460a584480d101c01e44e003101301e41030403010b101030102d4403a00c05110000813002040d4000c00c5182d03031101c104018003410841c0750507260b203030445c240d200a495009444a1440c851026030703204008000d030110107955407582092620060300341c8441824011100c14920314420f2104100800c12140200025921940c541c20201407034098888140751 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 429167940 1250 429166690 429166693
    0x18150c0d0906051c290f012307050709020d02090f0105030615090604030c0e060a1e0608070e0603040b060f0a080c0f06120f01030204061d06010315120b04050708 71
    0xc0402000f41c01c02c00740ca8600030504411000b60802180d2400204491003580c40402804845041c050030301d040100d110640540312010443c00c50300046d5080948001d00d00601d140282c800d001d45001d14000d4501184140112295135480d05200b40030f0ba000224065181540828800b40500e444190b0343c82e901406c0c02c1a5145083c15404aa00c80f200d001c110305020200180301100c42e12a84201c500641d0032030110402c041d120b030360403048100c003a10302620840394080e000c170f00d91061801c42d03030710781c40f4810040ca986442d024080d80c0042004089901f40090103e08480c03e8403010001c52060744a001c3d000c440c2e103400d008100750190052040341c000d82540e0401e1000310030000b03c1203510b8604403982680c6070403240025189229000001d07a4840103107003403041000e02d604030746042c0da200300c1c2d06001d05900c0e03448a5062215020910307409075a59008607415501980c00042d10b20600048001c00307948507015102060414001282d20007400403c000c107012003030107105c001d454040c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 429169190 1250 429167940 429167957
    0xe0705040c200712030c0c0609240215010905040212160608180307120e04091505060f040c0f0206060307060e1009150c060b010f02060c18150c0d 64
    0x10003480c00b561100071241000d50542200760b042020441c000040c0307003003402c402a050103450010b0495081003001c0f0381c0000801d10219400f406039511109481c040d0300b01030710b5603103509201700c0c0c80140d0411134415030150301d9010300c100c520302c2c081c10b000e000c040c5404105402c1c2171061004440c4081c0c61001740ba0400c410951950a149441e03000301d401c146400403107508c44010401d072804000d00254418480007410904102e450b40302c10032580343c3d0740c940450107040003041c0000c3d03d400360401840c41c500c00f000790456030080c1d4011034220101512a50480c1c0501340032800b1200d840244c40c0210317903490548001d81c0e034100201d81d030111060f0090400f041c5080b501800d60085c105c19203114402103d0318515070381c4502d0f500300062164a11054071034240300f40180c015046014107444540c100741c403040a80d406010b03285640802e0364018aa40e54400d170088040e0340104014070360500e4281380101450f6145500c2000e21140ea0f200c00c0da440000030302507840c00400740c02d440c00303005904 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 429170440 1250 429169190 429169211
    0x90a021903090c0b07050304080f0a02090c0301051305130c0f051306030209060d150f0606080a0903081504021c02090a0e19050c070203250812180d0210030e070504 72
    0x100d01910444d071200004a0300c2d030710f90307140003410744c0a16000100248540e922881d50341d90b000074001c100c94002e44085034180c444c0f070b840040a00c400d000c1c15030010003544204110f0741c01d56001a60044180758090040c508903914909500450b50000320703406003c01b018011464a01d051403285034035560100001403855011460002000341014071485c180380c2c0362400d020804001c500012007980c3d003040603960340c120000c000c0501e4042c6000285000e0002100800d042c81a80340e840e4040c0c03100b80703980c0d444601300000d9000c0c1c080300c0b6802c141c0038001085d00000c1c0c0709910b5203182d1281ca015860306a000c0901c0240c1d00f06900482e0150030540620058001c940b07000150030103a03840214881d5940c0400210078407400303030300a40612904101d4881e205401101d480015505a0700150b001d51b100c803c1540d03400007a0351140600030810843c0e0700fa1200103800c030814040986603c03124400b0380c00156100d610b0480500109440d41006207e000c400d22001014010441d010403418160 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 429171690 1250 429170440 429170453
    0x6030b03010207020d060e03071704060848040308030603060a09022d0a06020c09061e1306080f0d090b132105060703020a020f071a0307030b090a02190309 68
    0xc505c0151456a03038411304084543c00748216020f5035002842c201130b0042c40041105503a10500c14071000481000c0440c1d1030321658508040b803288100001022403440c00c2209100c8048044007200c0040e403810382030080741030306010f4401540913250395612481d2070707014542400001480c1c0380ca518501504130307006036988c2c14000d0844c07041550040d510aa81c00074a00401c5000b902181c0c400c0300000006103c50740040d803403c42103004d89406119413649800c0c88015090b03c184203617420544000181123091880119819055600001c00c2c0b0560b155100c80c2020070444044416802c0780c5001e42646810403514001000c010040c680390411801007040d43c0304581c090b41c101061800e010a2603c04c0b400406401d00d500581620401e040045025000390300c54060341c0054014401400c14001012544200f1941b01e010503008600400c00003107940d41c001802d410038169110700e00f1086072110700ac101c1c444d8420702e0005a841c01d1010503001191820302041080608040900000825 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 429172940 1250 429171690 429171709
    0x3070f0602030f130f090b1008040c0512030d0f0e2e051e090d0311071101080910090b042a141c08120c0f03041e050a0c06030b0301020702 61
    0xa11640c4645400c04840080c541ca07401d944099191600900013065486c1554014114198212030b01401c5480404040e544800210303800761903100b4001041041e42400c10003140620011026285401d500340c00800807114241c01d100d4805a0310715280b851140300b040171b441000d01481c1c2c400080480d101c0b01040000f21442c2440301380d45c951010521504024505141600520034910418603140c4609a80c1e4200a031b00b4000003402c0c01c040400810300e000860341e480d41c001c201a6441410540196280740e0041c24000c807a1088550402c0c1211300c511230601014800c481d04c040900341401c1541c1e904299200e01e412150003039210501c0d05d10052400002c64035a406442001e8507031400144040d4482c0c0d0101d541c1c01000880d1a0420140400901c0100c00d1600003885a072101001c54890740140a1890807102040001c200401c0c90345501401842d41e4200c000414040c1d640c03150309101340464211192031074040d0502c92a03806000b944c803040405c1d4000c5041c0501038001900148 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 429174190 1250 429172940 429172957
    0xc040c020307082505030315030705010f08010b03270705011205010e040b09030d0f05041403070203030706020d0b1c03031415010c1716061404080d020c010603060f02070203070f060203 81
    0x4c3c0303181080c0304400d058418180400c2d4101c4180d036182d1900350000c90b0709103251120b491080c06190404102c0b9802176070412034954550703968550680c2824101c1e2581e42c0041c1c03045030066440304400040700c0e40d09141c1c224815040000d81041850200054000407201040b5188181400014004440c001c8880783c4d120ba040110044d241e103600680320b05502c01e450007503140700d0400070130501d030056540040f1702462240d607605405003154900c0766107038001c0000003545900200915000710300d00f50050400d801c407082c40010294800b8001a121404100c1041031008159090105043c0c0603c00c921564402a40008461500c01e5429030400140000e035418000d901250a0501c020110421104026500020796840b0130104206001c1103c1404407189401c3c2921070000744039801210b4000ea2f40240340c075041448071480302c4042d4100d489203520715980c86071300001085c50b0f07026080c6582c3d0342c2e460060b910450390040c581008210340202c2a41c0900340000c0064a03400002c9407141e8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 429175440 1250 429174190 429174217
    0x313060c1a181b13020406020601122a181a10050d050c07050d1e050a0c020a06110d05070b0601030213030f1209240509010309060e0c040c02030708 65
    0xa5665100d03084603411400705440300c9102c1c49040107180a6500312101070103100f26501d004c0480c01100c1c00003648a80c0c001ca00040e0052001041a41c00000c1c013045014400c04e41c204043d07208030740c0030144e203101e02481032442d41682c208003c2010f0703502800a84500d490810311405103040c0b004046280700c0490907014038405024004598882d1081c0c817011010b006040c88a81046094010b440c1c01010b402d49090298014a4030043d015910200c06042400000300c6215448081a00d503900070806500c2031043c0002030000583d5030075110400360130161241040302d910103003240d1501d0020074400d0144001000f1040c0452076007070100d039125409183c0581ea0b9806c2040c40e170310100c60707a8001800108480c0d82001048000451214440f8081c0e0b01d110801c1d81e13030501c149102c0f200c0181c0508000c8949540d804052080009140c01401070402181d45581951181c0480f140c06a4800c0103800c0208041c46d140703018055071452080f103100450410141d6124400710b48200d22440340038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 429176690 1250 429175440 429175493
    0x130302060901050909090109060b0a08073b0106030e0a0506040605090309060301180f0c120f0b1c0506100501080a020915030906180d090902090310020c0313060c 71
    0x1581c40340c000c542c840c4c04003400c10f0500f4204030b0b030494083e102d02d40044504a090403003400d4582001d19140341141c0240000b09a894070707003041a00003e01800304401c007000f00000100c0d0030105180c203403800780c0d0006114002da61500300d0040460f0315840110701d6941004641402042c400284a604142c02072400a40b0340ca484060764658820b461020f0341140c3c0100001907010415484041003e0045c1e05c1440030300c2855058800319005808204045542070041e889800e0080e030010000745545140010303c00c207020001018032030008502102441c1c506150070820070280700458202d0700c1c040011502905100018000f10300003031015070035503408603108050340e95005003001903514504110780d80342040c511950b02c4820072510921803a20407200070442c41400606008a03071041d940717440006040c1034100002e5402014010790612540006401146a80c0300070074045281c00010350b61103c00c04003199812405900003024010082c800780040b41d00025542d502d01105104d2502 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 429177940 1250 429176690 429176707
    0x40b1f020636161e120b0f04140f0703020a0e060a1502150408041e18020d0e06090a0b010e06010e01050d1e0c0306080a0f110d050d0206010f0b13030206 67
    0x180c03001d008030f0f0600000520800150036214004210f410340304050541416076180c6103c2c8000c050f40c2c1900600c8500f00383d001980f080740e04071015801034410441c244440c00d00350035440c0341225203080c43c0d081d0381041800304210f250100c42100240100071b004100c80c030349400003445100661041070160031102000e240403d200f4029010010346651044502d42003e040c04501381e0003a00801003290150301004084407043c00c640c404850801d0005120440944485806034101910640d842600e0700c42000c2c04c620240100c0780b180101030000c02d00d00240b41441805014103a00004201c0494828002964bc0c40001803090140030300f030007a900c4210360065002440d601013040b800c0b40a00c812100d260005400c47c6048180956007880000e0f22556899207c0400c010000c1c81d9030400010200004c2c20040c07189003c150040c86840340950a4460780c2c100b040100c207a10041e004507005010300703034040003100050400300303650905016a103201e6109030002404017138800e840205410b070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 429179190 1250 429177940 429177943
    0x601030b09010f1739121b060408010e010b090f130f0c150c02011214060918060907210305031b1308100c0e1e040b1f020636 55
    0x5041211401001d070000d503440e41409040816003146500317003e102c22481c1c0c1c00307250590408140ea1003c5000d0700c002a00060700c00140a1100385190704600c00b8030001900318000c0c8145c1032101144000491080f4201d810007402440041c8018030311104c0032309001999820b9000703010b00980c000c40b0212001c5182c2800000c90b00107038003200311080e030f071980350301e996a21060041c9118404c7c1ca4891150720014a55004e0311034100f0744000001c60500091994074001c06139581081824096000c8080f0700d4921038141841114100310750341c420201009000000444001c890034885a440030440850354002c0c070611000c1c0490402c0048408100c0041010004517010640c00d443c0c000c400c5503403613071001d4031307010f450380301c40102c51400e5842c0700e1250103000a00860a0010112001140302d0080700303160001102180b50000e944041c1c0500d0358988210004004808002a2907442d088400c020f141100c01028000501002c554011080154a00d0b03081c01f01ca0841070004409500c5080a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 429180440 1250 429179190 429179203
    0x307062c09090a0506090f0a031b02040203131205091c06140703090506060f010207030201050304030302040902071505180c0d0519060203010e2a1b0d03050601030b09010f17 76
    0xc40e8072820940a000078a10006400d100321403041055507007560b60112901e4032040c4050940066801800580c800284289d032000c1e60f0780803100681c0c40c1509030340c01227002c0b600119100004080d8062020f814071686000c0c40244501c2071a10b24071700700c0c18001080f5881100c0003040058103000c6052420028560091240462202903180c001d1a11400046c041d1801010588081c0104408100da40c10400b02185000ba01a001816030f68615801101e4507413000f031054041550078000415260801d000906507140203c4c4040b28043d4030400c0042160005022298603c18080802d07072140008102850494011155101914031070f0070058100390b160801d0740b80805211100d4010032843d0b501440c183d40c1e1380c10340c00c2e501d42e6960038000504084089a49015040d040f044280107810700020510150701c1c5450818801004c0122450711120b40071310b00200392504108040780d41c3c144901d42c00d0200031107204903154504080c1d881c01a1a602034842d845101000c2e01102d0070080180 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 429181690 1250 429180440 429180527
    0x310050612010e1c020a020904021207150309022803020f0f120a0c0501020706081b0403061b12020f03061212031f0608190b031c030911030706 63
    0x81c0070340986107071030f01d48501450040030b50607841c2c2c034003002c1154070000d40100e201d81d028203507803503c1c1c4a54080104c1064030440791165440340d44c4010034140c02030014040000d41c0b645021603451818410400044d00350380c46e201300c0b51000208440d8062440200c0011603805688407089002158041503050454600c01034011f0030308071007030710380b2080010b00e03c60450054428140058a80d0012a100c0e00c803845607030000f8520030082a041c81c09031142c3c6424180c6062030915180d0b40e40d982e003003038402000d41a07142e045a10f2450300b186410490a81405d0340150046140c80000310081480740005040076004030742c1e0760580b103032207141000012007150b00394803480e4036450224101e00340d500340f803489030b01c1041d0b01c0200016058040d080d4180501c0c240e108581c0c0c540d006243e03880042220500f81d5505200b4000b44076020031100c40c00c0300a0070415540859265003605200611048600300c0ca8000d07880f0304410465203500c0003c011200008217403800310021070341180200110728051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 429182940 1250 429181690 429181693
    0x200301060b04030605090a02060f090d0f050f070f06050f0f1e0304030311181215011502010e0309150307031b030203040203100b010912020a0b0a11070e060310050612 73
    0x100480c540341c0210107031040340d10407642444243d581115143d1520100007009410880c140451181030280c1001707071203c103a001c0c000b14141e0380070703803111085d0445900041d20181c00c694101668990140100d001510504c810722019a2820710010050b200745000c0200100300841c1404050160200f11020440003e1106460b0390300304c20303500311652066900301c01003403400490311305610064050341c517800858400c008504803294144803030500c510102101a005408031803800380011030900d400b808c02c5c0c000440009400c140301a084403980b4450308583c0d8001e0040205035540e0213100640142001c05142e00c82d101c403901034000c0e080104002c0c6500c0c11034401a050350b40e041d0301071441a8000c408845102868058200031201051000e6000442410051280b03c01c0b007001c041d60103102404003d8682d56a410715041c5401903098500059441d4283e98001c0ca0200a2103024280d16001c0190a04100d40006d41d07940e124255070f40140d07114400144159180c049800d00903aa0740d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 429184190 1250 429182940 429182951
    0x3030a03020d3315050904050601020a060e0304050a0e091b0d06061e0b030f010e0c0c030c010b0a0e0f0a0c1209060501050a08010207080f09191220010c200301 70
    0xd40c5814000c1d040c0e03c003038421000a200000d1041e03140d0210080340c04860b140c9610b414800d00a1001070400105198103600c075601d802c00010341c0c1886000c41d01e0900802860311503040c50304001ca840d00750760118000c0750a010500c4486100441e01d076055000e1301c071110140e5044680483c0c031111a04c0310160a103440c1820014801a404942410b103202010301c0e41050717910341d89100054001980d10b0a500441040180682c19500079801e800c02074001002c1c0c00c002021109510f03661101c54100d6244c0d456280b118030b075003402600b00c3c2c05469580118290361404044440c02c0003c01000800426110031003210424099542000000383d0883d00b03000d0b11180e030418030301909082c45014041c40411200281400303040c402e40f000245d02202c4075107406210000010107400008103a81c0c0b040c1041c4024107590003582d0740710b0003001080000c142e07940ca42c5c03c1c0314401c1c0482e0794510142c2440425101510ba074440d9202401b80ea0010010040b02c0851040c000424a6406807a4140d1300e4039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 429185440 1250 429184190 429184241
    0x13230105040b01050405010b070609060f06080102040905010e220f0f030206060108010803180607150c1d0108060a051215070e0f0a030209042d0807060c08040203030a03020d 76
    0x64000512a9000e07003002c0c0c0c2140d030799100303000440d4024410000141d40900c02c503000503040360460b8240b903004800119284020740d66500441d40301d075200d0b003a03603940001c0821800b461401070380c3c0141140b485e829058a03000d05c042003404000a030240c013901d00030041e80d0400800c1c03003e008903c2e0308942c3d0b10000c0c440529019548403403c0e207046020034000c1000181c030702c4000048401d10400502010644100170b01440101e420409080340d10f9075203280384d0b800743c221522481c0210070a0b641c881c42c10340b24a845208401a0502881d8100724040c03040000320788541c5941022140b003940da2620703c48030001c4041c00c1151000c084001c9403c46010301030420f520007800c0c16030400c100e4140e00701c44004002c06c00140c0b200d1000a401c2510100002d010625a820140942d81d916050510041070210128060303820304a04075403103200410203c040c04542e1084422611542c10001103d045c190002540c0c1d001e07580b0104109900043c1e441d50f02c09541e0001e40181004407602046041403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 429186690 1250 429185440 429185443
    0xf040801020a030b1903170901020c06130e0c041d090a050d1d060315040903020307060f06060e041424120d0f051c110f0307080411030f061323 63
    0x305012072042d032200c1401205c6413111004c01040f2070b0b02000c14425941144256640368001e1b54003c5c0c150300541d00d11401980f210b0000381101001e1410040d0035a0800b42c2c028a001c00c050501a03010a05010511100080c001040100554540e003080103540d01200c0502c0e02d050004002c4c06400341c11a60f802ca542c000808140e00002092894065858042484043d00048a982003d40034041e07211140d410154401c1d4031082c02071068924104140e00c40c401612100c84281729116940c9008201c01c0d0792101c01d840c8410402c039024003108040d00c410300b1070144042c052951403440d0b81048503a1488550700101c0c00b19000e400c2ea410032081102c440c1d12001602040004522040c00701804a80b040048030501c101c507802004528444d008407000900c1d110f010300e600d0350307010450141d8646d900806580308030244d0b500c07404186010301e8483e401e544e10001c0c29001c0d41c04501a44010300001c40d840d5072005108441007040519800c2c034a400381c202e0380c80c2d180c10000083c2c6c0500804070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 429187940 1250 429186690 429186701
    0x21905040b0607050a0609050a0c060504060f0f17072001020d0b0901030506041205070c091e060501021209181603180209060d0507151d0306060f060f040801020a03 72
    0x10484003000810600028040c0b80d1055807001055500080b6410000550b168060b007407030f038050021501c1d500429034030170001c031610fa00000041000030404100303c075807200d0285036003041d030700d000c2441c40c000d01405486d01081c0004401040140da0004402c0c601c240034840026604c081d4011940710030f054114001d5110045190149090a0003101542003400e1528100c0358044000c26003030f602c0d87c89180100b000c40c51900208401001385001080c00d048401020b0413802900080c2110380103030498250001070904001c05050102c2041680c3c2c02140d00a414065450040d036070300d16000004410000d4400244051500201404440d561906c1440c1d02d004951311304120100001020541e0a041410000e601440480c000364450915890a105003449141250086038617803038000003e0400162406c0060340300c4004111009100c014101d035140305a0250100b828401c0c00300e4014918042c0307960042c04000382360568800750500301c81c002c1207014008c43d03c802c0380800c010042c14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 429189190 1250 429187940 429187949
    0x30a0e030705040b030a140a0b040c051009060e06090d020d03180b040312052101351009170307030213141008151210060f0803070305070f0219 63
    0x30950341e0209442c2003503c100c0d00d8241004004121080c0265500640802d0504440085c1e01038060b000000035100e0300a0b90080c0d209011800c070f41c0b401c01c014030801c80c420f04020030810000710800c001c029000018800111801d840c1039aa4a00300c50100700c0420003880000d42060741907005205042d84001024111541c1420340d0303074050380d14201d4151501860102910b401c1c52102040443d9011340e00400e100240300000c82d55000364003116094401d000d80c07012000c21400030507060850045005a034846c40c802049031210203202c0b00155640c0443c01c8045072440d40d59182c64107200a000c2d600c080c1000c81151103980780707805003005000e0b401001c0c8441d1180100d40001c25991040b20b0001080d12001c1c006410404a43c0e4049500110151102880401d2540100c1c065102e02454801e002c081c24014000303051049031401c22503041340c0c011707511241d00101c02d1050741000b00443d070800d901490000c0d110700b034074180300b0600340403000000c1d030001a900e0210309845e00101e43c81d0498 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 429190440 1250 429189190 429189193
    0x40302061306110a0305090f12010513060e030406230c030a0c0c09021602042004031a010509010b0a080c1b0c100e0612040c1a04031403040510080711030a0e03 70
    0x40b05034510b050384c0c44151200081c0852020f000c017050030b0030090001744100d6402440b6490741d0036540e50007402c552040d0703a01c0080324171104002e41884014050038000b548060001c1d45482d1404900030a0320f1003d410341c4421241880102400d264488203844054a186041d41c0c0d5078480c28034094805c0e121890200e5191800c0c1c0c500040716081031080e2840c00744807489080c2c026255a00b0400140600741c2c05012550101c008154001202c10281010b503100b40204e603010031100c80c2c041d082c0c42b4168800f52080b044040140f020b044205c007941e0003a003050410f10041d855051400b2618000c000022401198600c0a40c4080d24001915041891b040d90000c0352074601f00001c0f5111a05001e400d600110708202d83e500000c100100194032902a905086045071940c482e4102079154a6440c6000d5002040610902000b10b00702c610043c0c0a6008614003854074000c40d031901d000049040a0001d204000b94120703001301d01805012690a0136640e40380c044a202070043d10241023020300a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 429191690 1250 429190440 429190457
    0x19110d02030115090911090d0f0c0f0e0612190c093b0613020d05030304060204050901120b060d03031503050313061809180b0f070807080402010f14040302061306 71
    0x1032200c1403041214108682c01b1003407502c0d22406c240701004071100b00c101c41080504610780c021400d9081c0c1d1801a0000c0000340613031610f440d242200d406006001c40b40310f1901c0ca942c0d810800300c0055503e0800c074185071000850340300c6007401c4220007000c1e03200007601414280c0e031621a0080c072400100149440c1400711007003041c07401200c9400701d0343e490ba0130690b0180002c41e44c1d90010184071403086200420b0360840b000e4541d00c0034103540003900c04a46694020909001c41c0c54454805030142001001c2d142400300c5540724941c42c0d000c05024280250300142c666414580b290308089030080c054007804085540c0c23071400329503a40c001010a039216810410101d0306600c80c03000e40c03850740100744000c0481401d1441010007042424a2448854000781c42c1d000050424150980f2030524502c24600314507004074080c0074540f005010004000500c0c04100050781c000350046c1c24200e041c03814a17901d072981c5442c204181306903040603500010108180c004004000000c00c1581c0042e41e51019 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 429192940 1250 429191690 429191699
    0x50a05041217010b0d1512051c050405011d040c021515030703080a020c030706090602120702090411040f0e010b040e0613060f1803020606150319110d0203011509 71
    0x9440c240c1102c885075401600d8010403d103d220701c068a0340d10804a40001c540701d6480720302504100a9000c80c503085500c03143c1c01c041c000c06210600c000c0d180100ca030030100340201c0d0300a00f148210b004107030502820301030841e07240002072048100701c5000f0308104000b007a4420041d585801101d5091241c403500707000a01c0d50101940418180c50b4080c005140c400d056a03103104445e00204148002c51040301711084140d5000c00c0307168003c020302c5c0c59066049040c11002414180d2100c2102130001742000002e00680390f856001d82d001d1f030801414582c03a1105070005025080d0b035040d000f81e00e81040544842424194880601c0d074000316000c00051042020260320ac0c0002c4440e2240c800e9448603540114455400c4401802c4c1c0440c800181c0004005036507004124110703080e0b005a002c0010028203080c00b61030f0700c0c0d01d048804038007401c40c038244a0090170300c070000c0a5891010707180c1444001000310541038846060001c0000e40d00d0750f0f142d03041c203459008001002c40003e10018000074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 429194190 1250 429192940 429192947
    0x8090a080a02241804090b0408210c07080c070911040819030206070c0512130611060c04060c030203040f0305010b01090e040804050904020d060c32030a1e050a050412 73
    0x64984044842e051160301c0801c82c02007000c211206412039100c886c03a60011350401c514a1141d0310600e82d00d0388445101048131150400f41c0b03143c508415194092201a1036010305a4a500d5403141805503219407a030000790502001d640b09411503401c0041d4003400b44c9414010708240c81140080781d00c0c0800301200c070030f0000d11031500680580c0280300401c4d030403071180c0c1d03224413190700440c200d4460f8071800b007407101b44d030303104016010071104291030a12165a008100100c42a29000140094100386040044a109621070b10701804207803000704003010b0080c01590000c0c51984004080540d40b818480d01a05255500c580000c5001d0000716480c01c0003c00c036801960800141400c0034141020301072020400760041ea030055280104000045050042500340003241d500c031340c01d001b40d007503141407101001c4c849402c1d030101a9900820740b15590b01030700e5014078002c2e8040b440317030b4a40803042d5800b0018070302c03103034068200400c01c0340c0d0f002d075604002c0c011442082a040400b0080310100e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 429195440 1250 429194190 429194239
    0xf0b040c031505040504050a080f07030801051f050a11030f041703280909020c010e0d0f050d050705040810050103031d030303060f0102011e0b030c01050a0f050708090a080a02 77
    0x4164038964010030f0146081550007142d03c94400c204445000c0c009032114003041d04561040c132070b1044c0014901c000c165018030308074010141501d40440305101d9411100c4135486665503e4100034001ca00360b00d90500c140350048106141c41e0669566031000313030403801154003600800040c08010301c0515000b460000c1100c4240454108031560901c410350b0141d440103134190030f0010003500040105455072030344010110307091024000105912558000c0d81850405907145050102c400c0010603001d8000080740d4980c100100005001d543c2c0a1094480340a40e400940a501c100740703501c0201043d0f507110b1410390313001e501c6113800c04c00d0701040400b44003400050250150810300202e6940d050095804080900500021030b0307102040d46820650021a0074101c0c0a64440041c180982001c3c080c1c046464000e18005180850018001d07000340f106e2800c000401000095090500200310162070400c113000b004502515590b0010541d40c0390b0000003a0b12940c143c543c82c0c3c0142040c001c90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 429196690 1250 429195440 429195461
    0xe0606031b031b0a0f0e0a11090d060209030708060f3102010804050106031e11060c0a020d03090305011b121505010e0406030609230a02090f0406020d0f0b040c03 71
    0x4116a0100038900d422040f001c031030443d00412000f5010981c44c4c0c080391010301604000901c0f840c1c0745030200885090f16800044c071701503d20708208500d090703154a031500400030f4000201580c0e40103014042450000742d135200c03c00e2402101c0038848809800090740d4050701c42c02c4440340511041c1c061800e603401c403103008100700f0003005100e400194001c410751a40140107000010b0034940d01d403a8145400198204e0080c051211a09241000784400100078411030aa5405e414000c000c8089503030340c0e084000c083d11415034a0641c01c105031186070703002c1c06940e1040c000d00c180c1e900c4000c5808085200404600451108000c0d000840c0c8144207001c0350210084010750030780d01d081d0040d0742c100043c118141d00240c071110048042001c070f0042d611003910039407090441045540a0740d14548011000f14205e801c07095450300540d035030280c5240c1200009a03509559100d501c1d2210080c41020f0345200c400c0d007051fa0f8030030301d012a80e000340040c400a0f01c05000400d42004120f0469000006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 429197940 1250 429196690 429196693
    0x6020304030f1406090c030d020622080c150106030e0d0c060e07080a080c010501060c0507062114040224030a0c020705060f130902072003100e0606031b03 68
    0xc2000071410030400d18842c1c5010f01240c100100680c0121418680100c070061000e0b8040c1042803014201040095256061440600740609042c0c4101082040e03984048407490f000d102c242040c4035a440807500581e49400499900d08403003c403141c104413003440740ba000b0a1a04000304901c9801003074640050802d559111740ba8130fd40e80d113500c0140b812000503c03041c4107840012500180800107100000e0040c2032464451941500f041d09562058021034200816011100c0c0043c00c0040d96806688042c10f040341c1483e0320714807500c8049046241240a035042c40c0712090002e840002c0315015900a80b6071960069030f8066007140c0ea1000c0c4106d0602400c1000040d40c101110340c02507504100d103206588096a5503000640396821144004500510010304010558260004030000302101c800a5051a5007511410501070401c4480c0294031042d8040e085c05680511410b1070001000508002c150440c5510607592030040701c5250203441603188c44020320565030840030120300d0040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 429199190 1250 429197940 429197947
    0x260a110c1c09051002030c0f030403120518041a0901140f0f0a0503030304080a0f021203060d030e03032a1519020408010513060b01030b100e0a0e090c100801060203 72
    0x16510108111288000c0070041d82c600080781c0c503610b02d0140c203c1e02107682c3c015502c5010300030103c1c1c1000310000d44003d00361302c01c03c420400500030205400542c5040e04010346c0314000b69205d000c0741145001c2440e0321510704499804881402e6940940d0000117454004003683c03900a031f03150001c030010b0000d41c003c04454459500389002e03a80c840030303000041c01c0000495035840c00f09155410966080b6107030740011401e4591264850030740004840c0c688010030580182e541980c07058800909002c1c0100d0703002401303009040c0503041886244001a0031a555450b0403410011200044440c0b5009104100c070006580000003458071180310b1211135508994031005110240d21003a03088041880d80c0922000405030004e04c40c3d10f03c075034100510781e2841d0207a854660300303c2d4080c4407101d0500d4608080010706803100c102c0d003000c400040c2060542c818082001812442c815400a0502c2d0121000c000ca480c0020902034002c4409503a0b00300c00d0760b40000d041e11190300900903140181d0003403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 429200440 1250 429199190 429199213
    0x40c030906150e0a0b0a0302030d0f021c080705220e0106020c040209060d02030601021515010e04050f0105091819060b060a0203030c03180114010620061303260a110c 73
    0x5a111760100701d40180407582c1643d50340c2c0840e0800b581c1089080120309008603500b05550140040040900c0c001c40b40d03040b0020580014024141c01380040b41000400304c0c80e4407819000101c502c2150070480009404c0c0c5940e213660f00007e5409000344030050048100c03560841c2024000d80349480002480d050502c0c0d49008600001d420003007201d0704500c50303485000d0071070480c0341c0201e00910003e584424070040380000900442c00a4030102d000c0e92610082282c0a036030f11000c40c1c191002120a9041d60305c41c450885100050203181090390301070103403a0b00b103507085181c40b01c45044c840c41091080015810401682d80500c0e944e10015810400c0054424110f500c000d5500094a8104c100c241c000780e4025421a40e42840e000d03005085113006200d2250004110310401c02984c003162070101005c904d02b5101d107002342601c80e80c034001407480404c040c0134102c000d142c00b89440c0e260300c202070062032a100980090b14076005031031410340054580840302044440503050f0380003c03c44117000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 429201690 1250 429200440 429200461
    0x81603020f01060321030209060c030409060b0a080f1b0c0106090606050712081e01090c02060f01150c1a0f010f050307030b01060e040e01060801020705070e011d09010b040c030906150e 81
    0x45c5400c4010182e080010b02150755078040501110b046e030390000c640346c505150102c03040380c10a0f00000100a03080c0700000c00240e00481c00c55204405111552031510303103100700326210185c41e5450441600200b005007002c80158406000c5030404402403180558030b560664591041d2178001c1c0c10503040700d041d42801ca000e1030782990810038005000c02c0e40703001c101840c2451203080e0800300703461b82c0340e40d09030002d2a810002c103900301243c1c0b0280102945000e0040d0841240c0c860300c9405c1c010300c0c4105c04217100144c003030125000c1c400c141e12546441d110000640058003405221a1000440c0300800e03070b4203000601c03500381c0b548454031981c00d900b0128165a801c0003d0411076000340c4440091520800a000c0d08005042190000d601c424080c42c2190400c02d0f103811031840421454010091201c18140f071101001801c0b50184d2281c60300c5060318050706400d034038180c000e402c04c40911101a0305a0005030041d0094804220311a03004100c0c180141491040c04020030242010036040c640 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 429202940 1250 429201690 429201743
    0x3060b0310032a0e07030b010e030c0d0201051306020f07060305040b0106050c010207060e21070206030711030408121e09361e01080a1a04020a03081603020f010603 72
    0x6814481100b6220b9030349190043c0782403a0024804011340605101889415010703d84103074000b401c0000c294103450300400c1e80c400ca00304450341300d03c40c10f03003030481036900030380444668007803080380d8a144541b1010040c0d551307501e1030411031135803240800c00540ba6110340704990241c0d0748416084c140303034640b020489642c3c000d00d4000142c0e55003040003400140c0303148680d00b0342e605a040130345102c000700a81210350540580f0b10b2041c081007086414010790302d150490b94000c1c1d80e03080002c80c60a440c00050314600554004100760701c02c40716050010400c0324040c2c1319641c840484c0e803c8001c50300c82c1035046070045142441c3c20031424440b0015074000c9183d50000385003008030000c4200c0341c207400c15507203c800f65000820b6075020800382c0343d40401304aa03c3d000d00080002004141d2055030303400209050340d004030514000d9000030408640d1600302c1c000086401c0030301152594002504200744030f81000c0110054481e445800700a11010700030705089907000724480e12220442d1038206000b10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 429204190 1250 429202940 429202973
    0x8070c080d091a1603020609011d07050613030f03020f0115050306070806061312020406050d1a1f090509060108060915090f0102030709080114040b01090b210d03060b031003 76
    0x4000713104044008000704520b00240f40281c0c0200a0360902050103400c40d1400420754100a141c00300c281c0b00c50900103480c03011103100303590300d9903103c002030060300c15004281c10007061910b0750b240c034005240d4000342d59900009014002c2005c01108412110080905d02c200e5406170000303400a40310b5030013000300940c00304010b003c45103401c03482d450109541c8070541048101d040441c8d40d40302036041ca4031403607000d4403003603910609040f0251910541552640c3d94030703940c00e003814001360680c0805404841e1245112800c81040c9844a5900014080840724240350744200f100008240d103000a0b0030740540951030160132030500c0f007840b21200ca03400074840c610510808a02203400b0f0b0092000b1071181059a4a1442242c10910400c1c25030740c51640c1414404030050901000c65010080181142e411030b070002111f10300000840d0003a4071030005801c9072400041c45a00d140d60106901001d001a07a8080142d240c035019410a0f83c001540c00001d0102071302e1080c0005821040c0c42507461 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 429205440 1250 429204190 429204239
    0x70f030c0f1203150b0304051c0302040503030f0405040f060510050906041211090901020c0303070e040e011d010f060305030f03061203031009050c0304033908070c080d09 75
    0x441c0d584940440000340c1106400007a52800201400c4100c000300d0300c00b40051403244c502e541426100c03195121291001c41d5120b000001615a40314080d0341240c000341400340507240c4405240740d2111081d0894403d06004d80d0502c1345440f451441842104140d0ba070040844580c0d03c166a0100d6040e007140d036469410000800010a0380d00e101550280528880d08590108600f81d030f041c803901501c054560026a80144150040d818020003603940c001824542901e81e0f85090300020090458000d2800d0194a065456803405013901d01304424607034540c00038412009a00248402c80300540302c047c05c075400a01101c4003010300c0500035600410000e04665056100200150841d4001d484804030b03803908450030850b2094500589621240c1c00e441c0d03a0131403402d503c0c003070b005800301e000d054621104100c0c00b48048503203030303040002501503849401000079903141c040070950024a0681d00306500c2140014101c0c40012140c00ca4142c6549000b44185040d084041c01d9488910100b100d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 429206690 1250 429205440 429205463
    0x30e040b040204080309010f0203040e07050a0c060f0c02010b010207050312030a1e2319050903041a120a061206020d0204050d150b09070207140d02062706070f030c 72
    0x3203640302d0000d40060310811003e0341d03407242c105e400946401885d64500d801d40d0030510040103800c055407400e6500c01d4503030805966903580d00300101ca0100c0c0381c51000304414600410301880711400d90041e403c00c0400d40080040505070320040e07aaa070407a10403954150b22480b491010746d0a03000282d5041005010702251981da04101844050080001800391541c0e44900c410030350480c1404804443d547ea07035440d5035050500c0030300f02d503094003801c8044042d200c0004c43c00c0250200203c4000b070071111805104101c00481c0410f09a0045410b00011600d5801081c58008584107140440340780800b40e04280100b50b5641c1e000c0e4111481c200007803036003400001b500b9201c03521020341c000c0c860300c50a400440c9900c0311504503800001e5550080c80800300300000503400254020503220742e010702c030040200002c0016545107074940029000000480c00c0001214445240e1b0440c910078840b89905910740c030103001c5140640365015250325000b84005010134000d00301404118000d00c0280b15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 429207940 1250 429206690 429206711
    0x30e060d3e0c10050c071b060504050907090906080708010f110403020d1b1d0f1605090406030218070221040303050a020a0609050f0708161a1209060609060103090b04030e04 76
    0x84803070407208224282c5e0002201c1007004845203000082c800e94524442410741007410003403041c011405550b004542410100e06191300032403002c00100500030050010540741d00c2403a0701c1e60324074400e0034901e40c240120075044900500640f44410b051030142402c15286408004503055207101c00d403079107056025580c29142903500c045003d04040030043c5490105100400c0780c0c2e4900401c1c11095015a0050141c110341e5580c02803005820b51030b0a40c1c030741205000007401090384d41d10080d44019200704007030303034820081c0100d44034501c10340a8400f20b0090b03101b1910720700d50000c000701103a00208001d200182c007400c050500020148100c818600c40c81d91010102c0303c1140b01500c144e44000851015030804000040c0a0001040035000d0500c01b180c20b8204004140207080040c3c075451202d410710207100d81901c0c04c8090f01d6901010900f040c804c8691103100a44125024103080000501554000e006601403a5803105100c80640c0e184e80701141e02c003200050342540300351605803110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 429209190 1250 429207940 429207973
    0x6020a0e0f240d0e0a1514040209330f0109080706080411060304050f010506010912140a021c060c0807050717090a0e0f060f0a12030e060d3e0c 63
    0x4044e460340801048601c46a0a2446428404a5101800c40c0c18000300b1051445640d2210360007550541d80030300e854840012442c800514480310a200c441503028640c2c510b2035000594500301c9041e1104804210a1801120205500d020b83c00e050351220004102c0d161007269a50b42c0180100d03d40e40c648200030f03000034600e50054500740c402d0344c8050048071007000284216500b12009007022041546002c07407941c0c0c028840e02c0007034080d0782000b0303c010154074140414400903500400303407024443e0810843c9480031500c641690424582400100c2060048040500074506038130b43c03038240348050b919054400d00d800396040428405100e801e0103030306e500e0341c0743c0080d28000025102c1460014001e4403942d40041034540315040310301400410762036410100094550711142d04807056240d0134203039650001041440d03008180080d800c5804a03440c2d0000d80600444031007007805014820302c040c0c040102100070200304103440079030b141c00e5003110020300c0c40380c8001c4260ba2125a4200105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 429210440 1250 429209190 429209201
    0x117090703140a0213021309090c050d03051b07300804120302061501090e130804260a083705090907050406120504031b06020a0e0f240d 60
    0x4240a0f400035000c2c40c210310b010030218500405c010070440c1418003640b03c001440b40c0034480c040d0042c0c1d9891440c414090000100e00c040d01004c0c02210b400502b503e0f00406a0344019a40c00c0b07001103601e1541040c0c0750104591044641082d5022590f006490310108041c01d164440b5920b5185680c2ca18006840d071405080146041d03282e8036110700d082d0601030b08005008003038503000d01c01c010322a201a81c2041c4a9410340c0c0581c4040b0708199103000c6c04083c129800503010b0208800032400281c0c1441140d582c5040000c038140c4071299100384441d00d6621500d06c0350040103028103220400b2040178480d2400c607004c03c42c0d40440f90348038140381c10b14111881d1500220009000003990000c0d4144090b1080d0401410320b40700303160030300e000d100600d1101450100c0b4041c903140d00109091501c40c2c06040b5450501598010100001d490500029448083c549000c21192840381722280741c090034030284100013074020300500c60b5107021401c00d50f199000c258090802440005114621031080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 429211690 1250 429210440 429210473
    0xf020a031119140c0a0e1b1e0405130212060909030d020708030901050105010908060705130914070806060903030904022203030216050402071511040918140c0117090703 74
    0x440403043c00d100146810644100c400700c0c040e03503114008115086000a00c140e00000c6600c071441c00b010085011085817107003003980c583e002840f40d40f5940d0500c541008000302d4800b1030b41e6021880c1c10f082d81d141a4003402e80c5203422906004d000034000c5c28202c00541d44040c2001c2942e1400711864002e84c1260010300f01a1a0860f01104002040109116890141000b42420442a0b02e007410050340c43e08010085010041701040071211118290103401c06407190321030910070407120003604255600d0485a0b04002040000801c005041c0801196510040500903500d0981d400081c00060351010b00c0700d40c4070071712092820821400302c00300d61026520990103004681946081e40074016800e801442c881e501c100850000114221505012059003200218219030345003000b40441c01117600854040d400c092030241b000c04441200c86d15284035414814080c00b001c50701e0740e514941c45a48a0105800d0b0500c80400802031010313a9000c82d03900200c40d800c03600d07903491070b5490b00c88050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 429212940 1250 429211690 429211703
    0x51503010509060405130f020f10050d06050f010518030304052709010209060304020d030c060e0304060311040e19110426010b0a051909020f04030507060f020a031119 73
    0x14011480c200d007446820950031135081c0b10a00708000c000c1c190440c012801001468000580c0c01107491b590051400c4020042090540300c94440340076245603c008a91500300e85407000101e024502a03402044400d4180d582e2400c0407480c881003041070030490300c0180c0c1f512041c400001d00d0f03a030340c802d00500c600303d0001c0300201518580c4240244000540028039603401440403003281e1700e03240300343c079802a011200030311600014102174441c1c1c410740102074150f5007840c1a07d540644008010801c0350b090340d800300000a400303a8110440d00407070250303494500c50700c800b0840d81440240100f0034640240000030721105d414803501d682d03074042d07805000740822070a12070141c2c0c1400542c90010090b42c000031702c00e40f0200c4e00001d4581d5000e000b800e02c915982c04011001100c925a21009030800b84802c554400703100b41600002c1d042440300b21070602ca15003000c5502031060750b034030064290940041c09200c03456682a01c00c10304a444281d038920031130703e03404841c0e0b00b00c05e40c28120034003440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 429214190 1250 429212940 429212947
    0x240a0b0a0f09080d020d021006030b040f1a0c0309190210050c03040906150306060c02030703031b02040204092a09051c02180106030e0a0b0a09030201020705071404060906060e040c05040515 83
    0x3000070381444650b48d40c0003c480d1810300d0800124000d44525039020b80d000c41c001c0c1a143c1c1032b147c182c14043c2078003110710140c101c030020410b80c244403d0080d40a101c94408841d00274040c0f0001d501c2e0b40310b4540000b50030000c600d14480c6120f018a000e440d0110030882a2070500e44c941000c10120b070450751084024255100c85da06800d41c051103900c1c040c03c00d500e006401c0403000d40200b944e4141034440281001604003014038060a000400503005134010410756840341d441681d4000f600903502c0c030301312095003c0c2c41001422100c0030384411382006030b2980e1000c2c0b441c2c502000008012860b207080b00c0302e60112010700682d01c822421540e002110501c90301941030840c02021101c40c500311801a600c802c00e8600800c45252900d80e00c02d40c040300125442d002480c1c00c9019004100b0014858410400c000c103423010b0204181c07113000d200b960100b007041d540369000c0090324403a20480021521b00200c500301400c0a8000b0f0401c83d175a42840b40c6010b5a480110302051003a03401c03590400f4011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 429215440 1250 429214190 429214213
    0x120f07020301321302210106090906020306150c07092309030a03050a0c05070206130b0c060702010c020d08010509101707180603081210030803240a0b0a0f09080d02 72
    0x201000350041d54144021081d2411076020407030040045810b021b6440591522000c203141c00d400c6000603040000c0c05000e00c4401c0d141c107802039001035402c0b6106403c421454280241b140080e41e21b842100001010b90914040148000380400d1818812f0760a01c0100c0b101880300c6200400d0060700c060005558880400c0002011a50082c20010b025810a080041283e910205075610160100e070740310740d01e5610065056082a20b5170100d030242e6408501d00003103844c04100c182c4948002d030000d210303115440b1801c0707803a00d2000d0342d0341e004184c040c001800603051070140781c0d5100d0f0300034400115041c1c41e0607030329502d044004514951544540010302041c80c105810318a007100386039050000b1800e50341e807908640540010384140f11181400525010062181413000b103400106c11903482c104040c680c0b080c00044044065504502c0f0f00a5000d410141c3d2148212205202d916080c911045002c4a4020000801008000d2600d2001c03564003428411030900362280d800515080f11003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 429216690 1250 429215440 429215531
    0x206070c05180601300f05041b080d0c110a0f080c010c08091c080708071406061503060f090c0d05010b03011a070215031314120f07020301 61
    0x8415141c00e8400c5200f40040360342c12160400c1c0308008070740c0b45202c0c120400400c1543c3c1e00c0502a03a0503040c01d08a590000701c0c5c0d0b82d84041d0140d8004c103c062846002c001e0f00c02500803151184240c0c90340080c0051504a1140c401440480c0c0300b41c4200e04558003a00c001642d01500f82c100c0b41c03800b010502c0400c8456020480010815403e080c40c002d0b011054441840e5809505803a5004422640100070040740ca04a003240050348003016075119074540c20540030039080048110f0340c440d8540f092038015840000d800d031203480002e0130b0041e2100142c0b41d90300241c00c003404441c2c000c52201e04580f00781e0385040e40309100e40b40c1e4040c050346401e0fa9082d0541903400c10380c020025a8000c00c0144102c040d510100e240700c203c2003a48640c0c030030b0302d403000c10140c81e084204214a22070110501140701603003500307001642c0c001c4150849640b00000300c90340b0341d41c042c050701c11442000c000100c100c0e0f040c0000f03800d183d40001c000149462800001907981f208040c0d2205840105001c81e41c00f2889 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 429217940 1250 429216690 429216709
    0x18060909281817040e04050706121802010e0609060c0102090f01030e0d050f07080a120c08090c1306031208040b07020109152013080708010504031403130206070c05 72
    0x40490042c0481c1ca10040c00d41031040c06604042e00072100d03030500c00e0300c007000c0008481c01028442000c8509181c035040c8a500c0f145103010302c4002941410380d060070720070140641d034043c03080007076040b5600100b41e005403a44050000728030f42000d82400302408654410010f0100f1420343c5d0005603950414400304016000b20007203044c1410715103000702e203180c0f0001600e401c00710801e05106540c1c10b960145025107000e92100104285400182409815400170280f01c11102c207900900c0700c12113010707003580ca001c4100c8040752258480c011115041c074182560314290000802c0000c0c181d5200d8580504000c62100c20742c0118081006210400c054190b0150744007100f840208402607055444a021054444442c051641c85001d142283c000070308450b0000940145503550b1090b54100811408400340305805982c051280d0014510038103024840c4030f90760550f038810161000325038083c0b0b140c0010b8021003508189604185c0180c680718010032102d801100c1c0c0c00c040c280350204229034600e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 429219190 1250 429217940 429218011
    0x180302100315091407210203070906021509120a2c0111030a0903021e0a0312090816060507030c05030d1401090e120a020f1c081b18060909 61
    0x40ca0106040e00b044041300d00c0c16080101880c00710250041c1207a00c0012070300c03600400b041203100000b0320424503000f078541e408403603554090b581c40881440301100702d13820880d0000803035080186042481e2400380f00800c00001141040903044841030108040540c449140e00700144000405a14039a08064200070400340304009500d000500d500040500041d440700078060148600035a40d000e45018100741ca83c6000781660103c2c55a9051811841011402c80008500b102d0f070013096176900460036070b1040301c0300e894203905140ba01300c045a0755401540700364100443c503408900000d03070500041c49149104200070072085641c0c0f500c1d00e02040107a008200c4513280c160405185da1000c40d0411703400550080c0a0740f80da00002c003c1c1c0c00c0c9600380168040038064131006031100030985000c51400b100036681d41403907940d00c0891401000c1480c2c0c44620300201400080c800700520033151444131406041d09041025103004101c3e281070a60f5254003108101e00d1030002d45c21808650712420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 429220440 1250 429219190 429219209
    0x306050108011b020309220e071a070b06060706020403082206210b0a21150902030a0f03120218040e06060d060203090a1b0801140610180302100315 65
    0x10050301d801170750f00c0c861104080e010b07010101c064900002c1e81c0c6201d0440f51a1000305000441c008140c49407545118001d2841e2071410031a00744204081c242030301c20b0558003250050550b281c62080104513001140d08031500c80e001c200100000e80914080c01e240b0130f07100380d100240d01e4400d280709207001c29900800c040000349413040344108a0003080101c005111400082d01d48401400b160203545950040c40c4481a003040c8218924186066007601ca03028400c4100c1450001001100355418010301035810740c040c61000010501020040c40da9070b00c01e04080d510300e0701c84c80058060ba00b00d901d85403448815600c040c507150801d8000d02041d0300b00c2e10094011443c000d80001e41c00c1850040151020f0b6000c0300003400d052081100e00c0640c1d030003c1060b944025014806035880040740185a025400d0000079114054800302090003003d0081c100f03801d8020080003161104405003e10f981f1985100300000943c5078030110b4005800550382c0030072441d1340a0355004142d02c156001c031001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 429221690 1250 429220440 429220481
    0x3090608091f0504050111030c090906040b1014190f080f1909050c03070f03050709060e04060905150c0415111b0a090f0914010207051b120106030605010801 69
    0x90700400071282d400a039903154000b038282c80da820078034014440c002c5110707407564000042c401903600303200240c010518119013400c601d03641e05060005888080090f140c01a004084943d11107005014103410000c01504442c140070010b4070000c0401c0c030824034030300816500d04c410203000d540492601e41c08840c061281d240d40c02c1a00032211034002181c2814082d6603244002401c1200c280120070b4442002000c42d10225212190342406032210711003250680719842001800789410f01a2401321401c118100d4403d0f51140c40c0c1502904124400b00c5040c041c184070507401c00c464141541c000d00b50825280c0d2507034101440707052134100c04140703032080c002880c40c074405103180010b03660340080c252040700720800412804981c0e049810741110254900b005100d4081c005103505c0f03400d82900035003c0302200c6040410707080c02c0b413142220141c019080801e90041020381480c2100c0300c108017420200003043e80401040c2140c0c1d06400460344562510010041c800c001d000d028080d402c56800e071041c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 429222940 1250 429221690 429221713
    0x51207110906030a03050f0c0618010c0804030e040f0f020a110610210309170109060524120c1017060a121407051503191e05041b030309060809 63
    0x1640c030800500201000400034044090500803800d441d82342e0301c100104e80150801d18002843d1b0f01102c50541525880c03c04150803171445130000d50b0149030161101110429420144800381400c0e480c03603001070b522410250a07501d410b00c01003032500d2150391880c2c216010421024145080501400d15005207000d050200100d240c0316040c1f079161150344010320002ca4501901c01d020b86610008035904400b803010000c0b4010342141e09c0041c880c00c400c012990f10418603900c8001c85404c045400700c1881c1b80c4021500b80310340c0080e01110b080007214030712100c3e0700018811255040c4800002542401071a885910340c440c0b0700e0700040d04a40074580181400c402c40e02984910318041d0001c0145078041142e076030184003501c05000003501001c41e9159105000040740c0c0151501d5203d99821802c5008080c4184503600300e44140d4001122910050107044d030180001610a0780c40c0140d00500503454803526083c8001144240c0303908400c1d41c07900e03201900b42c0d03c0081c10b403407090300140e44045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 429224190 1250 429222940 429222943
    0x3070b0a020d090b0301061d0d0501051614040b0a030c03091b08060105120312100e2e0f090207031808010516030b01020703030f12140a0b031603030804020d05120711090603 76
    0x114123010440d014942481600182000942c0c501c003400c0f41d4648820300c20100021400c0703120040c00c1c0c1d01d031400c10b0000054401058844e0b8480c03258405010710010300318603c2904802500200c503e001710f6012465110101c1050164140507040c0002e00e0f01013090010520180c0d00501d4211074506050074059203a03078903449004450147c01d0301340f00c001440d40b4101490b21010b1b1950810407007083c500248000ba0040000070110100c8622450394151100f15004581c25508400b0002a2040c03034180590040c2d081402c044092000500c5c06c1c0903100100702d680303001003a2030303000401c1c80c3c207000c62541c442400072090319040600b442c1201901c1c1c0d0f00010090100d9505140c11340c414140c5c4201210302141c5100e48450480c10013207003400003103090400c1402140800c4040001480050815540d0803d0140303a50b01980001410130229010324906e03a4040d0002c0d11301040d0080751799030300c1e00b810540c881c2258048004241c6900303001d00040081c910b18001d440241c0e9609040e00040e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 429225440 1250 429224190 429224207
    0x50910050316111606080f0a0e070302010305090c040f0207020a15080610200d08070c050703080904020412080c010b040204050f21030a02060118021908040203070b0a020d090b030106 80
    0x6050010f44860404400420800245001801d01921420548039400208203c2055407070307031040928040811485181481b410601d80749070300083c81c4c841c0c9150b005401502c0d0040410815000305000080715803a030f4016001e080711508030060740c6545510421003104002e070801000449514101d031801d540007000c0c5034000c0f200305d07829001001c0d80b0204980d140401000603c01014044407040d01001c0003901501141c140d0f2908401562486000c43c3d02c100405c0018085511543d8204042401007008000c0620f000e080940b03405d840f0031800300e00b041c95803401c07208450009102401d0003400e00c50407115020465040d071426140000184000c4007000c0d0b000e2080f0400d41110840f184403815040c030520030042500d484000c4e0180213500c0300f03800d115026085200520703843c00d1507c00d208030344113403121501041c014900303081c080352030350402001241c140c480d10601240300d400390000360156a1641c0c1c000d00101ca120716004207074410661049030503040c184010712120781c110045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 429226690 1250 429225440 429225481
    0x33f051b0a141c031a060d0906140c070b060f03062712040902090406030b18010615090e07020709020d05070f020a050d03020d09080c030406020f0a24090c060509100503 74
    0x100c2c0d64205c9450a40300c3c0310300c800105500c40e0000852038a41c01c0c1540140300c10f140500350402680c2010120b02020080842d00521006801c00040e000251012001c80e00400003034801d500d1310482e0804a45003441c15517480c0890b03411114100000590601301580381103288016040e6002c84100c4041c060181d0b0003103484041d00418a01d4154480d580003100860700200c036240368ac10b01d9090380000241001c09414154240b59000c40e01e032044001c0a0350b600100c0e51341445c00c500e8508403006c80d08002c2e041104500407004005028040780c000307000c8400f1aa4400190ba080c290030140c9010b160454610a41d0000e81494020034004214525000b02e00e08015030341e610440810401050550f4009081c2540400d004000010000141003907400e5078003114004016118510b50751036410000030040b80720b000304030403c002090030740c102e0546201d00104907070789542d6540f2203214040d0013107800560003184501d90761501120854103001c660414528508122101b1080c0340c0f40501c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 429227940 1250 429226690 429226697
    0x30613060e04152901021203101e03061b09060e011211040f0b03100506070512340b0601090b190c050d09033f051b0a141c 54
    0x201e007450703421142c10030800201c0c040d044c404101a03103804041801c00c20901c440c01881220025038007060038404030307402118843d21403030342c00b450051000ca4110315051142c00200f0001400000a03409001e103001c4c1d2005400c401586400c4c1e00340042421605a21a0080003400e0401c6145646c0000ca031044d0040e880401140300511850f030b90640d031048d94001041d0324501e0000040906101000e54014001042d52145640d621020000ca034000c41c54040d08541213400c00d6001440000010502e000d244000502c0e455400b82c68100210109100c0281465080075243e0070001520701c2140d0003170090138050840790810405d8441c50180c044180c000700c2c01203100e40111800340c00b0f401c0055074030800300c4021a1001100420201c04c1d484110303041c010940707808103a44100c84009001241e403c6100d00307005500441d0400035907085a900c41484400c000c2c5c003041c0d4a9031100e880140304884020220000285804100101118039031903040c3c00030741c054007103015810400702d0300c610ce628 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 429229190 1250 429227940 429227963
    0x110c0d0b0402040f0608030f19020d30050c0702120102211b1c050901060501170a0f0e1b09070c170c0102030a1a0d0206090103090507030b0903030613060e04 69
    0x180f00500a00c05038200140c6e5100c007040c0c0342c4d03020062500900b003400c03c031110590801d2542ca0300781c6e40e440f00d00b0302113404074081d0500d01502e005034820b901032000c1041c0f4000340160124074401c08668064540180849000a0300001d504102d00c085254104200003107241c400032400743e803400d145c050000d0000d0403469010800d080c00030285c01040054003c82c0c2940d80407580e24803091404540038683d0098103020004800c12018403500c0110b81060b180d440c07510a0903800c50740030388002420b003640c2d40c1d0b8031070359a01c0468040c0700c0c0902d808440d0303000b01160400e50b074004c1854088040000e201e00700e82c1e410402ca283c0d1001c601040280e209a10064600b40c01d04c1c41c413002d014600304550191b10203c100300304011a600018640300300390012500d0340044005008010f091441c020390002ca00b001160255442680b1960415029400341c650340c079141c0e44d40c0381c0c0c400408e5034103072282d501c00310a03c14280780c2045004002b14040000b08159850080400c05418008101601600c1c081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 429230440 1250 429229190 429229211
    0x10030308090a0b1501020f0609011d0f0601090b01020a050a05030c1b06040902210f0f0609090c01050d02070b04080406031d0a020d03030222030b010b04050a0b0d020c0706110c0d0b040204 82
    0xc007e9610310312144130035030700c5901d0300c0c0c540503000b4010322a104c0800038110000c0c03014103001044031843e030800030015000b5a82408186030103480d80364010390461084855403004204244910307210180320324069691005070510003440c000c1d044020402c6080e210001114aa56650480d01200d00e148009a2a0300e004030130389410b0348084103080c1d4041007840c200301a0f241c01c3d51040c1d114000c5010007a2503600c401003400300d8034200315003601e095071180544000e42e41c0104080c11401c0000361015103800c406a803440e001400a8404440c5014042418045680c040c05191403e848200060b480c10800646180e9078080b4290041d00075040e030140d160906109804070340d20540c4582c1c04603284050801000d844072410720040d14107860807030001c00c540040700200d50498a000300f030441080e003012034095080d800705020341d035120340c03c214a0105c810103100c1d0000070310503501e40e01c68129140d0a010304243d181e07403000b8442c81002c501400020310b00300e0507a030420780682d40060800400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 429231690 1250 429230440 429230443
    0x4060905040e070e04050304050102070e060108180c0604060215010902070b010909030909110306030c0303032a0d06060207180216082d07060f14010506130e10030308090a0b150102 79
    0x744e000b080d402c5024108010502c1000401441111020380c00c4030707080c0780d071451840e5120070b0075203034980002c9aa00c0460f0743c0031840541d8405411551060743c100328100e50004225620641c03100016812a00140c0e42040050020f00e00424062600350703d030100301da8500c03035000c82c14018407100c2650b171000001450b00c2100400060040820100321511160801012039042214401d20910462164001038140030003030380c0c0100d0741843c030441c41c150b5115590740003c3e00001d80407900c84091020801203111030003120b0050007a03130003800985040201c0c410710245080001c16885004001900120740341f584a00109a00b1902c16030300c1380001c59100120124070150b54411880714a0303011080c503c91001042d00764803501e002c112144c4038074096010b8600c80382d6220140c500441c010449c0c1d0500000600010020380140d035846501c84040790000b050030b6802c0c00f03000811039410b00405400065a9030400d0540380148120740c42a919400748d000c0040000e080d0140300d07420419103900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 429232940 1250 429231690 429231703
    0x6160306241b150902240f090d050a0c0302120d0f030509030d0507020606010e09010b03131a09061b120a0f0609090602180114070f0f0203100501030606090204060905040e 75
    0x912207807000d42100c80d070a40360043d0450042c02d03032060002103c601030302d550b4101258201b4452000c00d600780850400000780907000302505541045800c074119000403814040300110741c0c4a00b900a51042c11401480100c126090300d40c1c8065001601c0f0817001508080701d858008943d10300440e055440201207400c50245e0f98100400c030b0308280901032480d0b0007080c3d41d88141d1b002c0c4d0705e40c03940000721410405211820710843c04040f03420004a1740600000c1003514005000e0203080604070022914800249421a8035594640200c020701500400500d49100382e21802e10400d402c0404682145c071851502409568402d544e03240d07080c00e2030303007240c200718000d0243e0f100800c0301100500b003440280d806a039030324043e091000510450340d80200c09061001443c2203290b03013001c54a58960f840181849030a6a04a00078015a00142e404015401c4103200c461400319155145160000550724982c0100d4900d60040c04107001c6150301a07a20412a801200c0120b003010b000500d071401c162 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 429234190 1250 429232940 429232943
    0x501020d081f0e2517060d060b03030a02010c020607030e0c0f150a02071d0f07110c130b040c0e0f0105180a0605040810020f090603090f06160306241b 66
    0x40c0007410081c0e415a0265030600c10840300d200c5001303010700c2040c1103854220703c80701c0000c3c160301c12010960343d01308031501c0504584649000514089908006481c6030002814100181c0d1122101d001ca158180302c0b5a4201c0d15a04061016800c450005da0f19041c80000b46801288034407a811455a9622600072040b100c03050019a11040800002d450b0700340c034000c900050003c46442e20303810502500d414400d0450584090003a00c03401812290b00ca5260814842445402040306451f40c03611110380410500341800620305000c41c06001c203550887d4042e006022891411416686844002400100e024a0b006580c0c2902d0311542c9030881000c00140c1c0c00c0102200c010911940080044c004ea640003400c82d00c403e0f0f001284030050341704030302854a0140091041d4005070800134083c41d0020580c4c3c00340c0e00c000c0300ca102040d141c01390881d911141d010034504524100c5406220710000b500755250190303680c01400b2560f4034140115803a2030f040107040440c40030100b00c81140c20481300e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 429235440 1250 429234190 429234209
    0x307030902060c1b06070302060106050711040203070e130606050a0e030a0f081b010203011202040209041e020d0b030c151e0304150e030a0f110102040b0708040e010501020d081f 78
    0x160442c8080c01da680200490f403084c281a4040001c285142110a5900d11075161b402002c1d640e00749541190641c01500046030905009003044d10b0036610f90025610520760b60741c40c014180042420232011095200f000600541341170428040c00b5440000c0320401405410500294594172002c6850001c0788200a0140c0ea900545002081185e400070808610302d0340f4a040462411010300e8200d20081c82003200b03803002c404901005081c550041e11105100a00c0068440c001038100040c0e40390440624482690000d01c2207043c000512a2a200b40010303001040ca005950020441080403015503917110303000860405640c4e00840204400881e01c040c106449042510346881d121014034034654000c4d00f4445102c1c40c80038008141ca084c1c00044d6126103505044903400c0c0ca02840c008140300c0710355020000031682d50583d2000305120313882056a0350f80c541c079010b801c90080f00180c100604542103c508030a40c60351000c43c1640048034800091145c1c650400c014007d00003942c00000032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 429236690 1250 429235440 429235447
    0x709080a0c03050610060c120c06050f0117030f09150c1e0715050d150801090309091103010f0e0a0906050a051b0f040303030f02070812090d09051302030703090206 72
    0x308a40c1d8212641240e10402c11200262503559254903c55201c0c040c90001030141079004000c9107015424040d000c9030740c20144020300081c0c50307120503240b08840003050040b16000401c42c0310b0644102c501d10012110156081082d812030038640d906c140c039400391054144500c0c100f544101c0700d044404454a0b4021034807003000c1d6070b81c0018030490003003c080700c1d8040c480303001074910841c1e11622240f03549036840034074081000c2000381c024402010f8240c0c403070300c841c01c000c24001301c240b003072110560198603440a140d144c1150141592420184c2601c00da01c140b004000ba444040008025264000303501c042e1540d07440f142c400103080382000a0100c80c2000113001009895510160040c0c2d4200e800c00c071026044130308485c240c4295840d4008640c0c040008001080c800d51081140d00044107015140c00c1d2507450307032052500216400350003162443c3c00c0c0072500d68204448151030707a8504181041c14900f074001480040d620352800085a000400120024420f510034900581e000b4905501c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 429237940 1250 429236690 429236693
    0x50406180f031b0803190b0411040e010b040501020613140d0905040b01031e02070f02150a081f0308030a0209130f0b0d020907030e10090305130512070e0709080a 71
    0xc0740d50200040d400720303112485100c9450b038882c40ea20b6481e40c01000d118915200e140c00b020f60314140a086041e01c2d6620b99040c40d586c0c2d0781d4000e4a1076446189041034850b81483c90241235164103903c0049070807000c001c10001a40c01040c0c85070722a030141603001c180151070030310110042c0042d20210241c0225100c080b0aa0b42190502044d62410741c0c00b0011012002c005404480c1089141840c51013400e01e00c2c4940d5480380c00818006e8482c250000e500765103a40802c1d00c090f500032107640d032400040303098880f040d441340c403013584010f0348008003110706544184464289400d000141036880000000b0300303200c0302501160580340b03014000b614100041c0c41443c000f0101e401a090131541421034601440c030b0b1040c64141c6280d0010010402a00e455406030024084103292a6040c082e440700b0a4044c4124450307404541d010392562940c0f0344800400c90740c0649030340c119038800d8581d00141d0782484c0001501c00c0654008000d0070b6202c0e1903074001500c1000c600d611203486880703400141c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 429239190 1250 429237940 429237953
    0xb090a0813060905030606011202030603030403050601030f02091b0f07060605100f1d0105090d060b10080f0c03011215060b041202030709111204230a050705060a050d05040618 77
    0x411128143d4031040b01588902c101a292074040d40c1c0c460000d40c10000300312507202c20b03078011038101c00e000301220301e030a0356a0b60386403c002d0240d10965072018101e540c0c60035030031302241441c1c5c0706024500c0d802c2200680c618619080c010b444a0452941004c61120304002156125601400380144000b02c0c0801c046c0e8000c00255001014500213890246400700f840c03501c10680550341816140ca9060020001c01c2c80fa404416076000c2d543d254466400d2a015140d042c088041114280d4903402c4518100104000074203000c0d1194444a208200410403054626000e03010260710914070103445140c4420200503140c1c6401441d10740d9000540000d03c40341008644207243d10907000d4883c180e0b5a0710b9400119220750344106104001086007a03c280380031906164407500c954010520003a801e016119580c20964401180e07501020702c1c08103010042203080000c00040780d4841c54442505401400d81c0108940c0441041d2200301140400c41c282e00084011030390003001400c104102c0c103110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 429240440 1250 429239190 429239227
    0x50d0f060c0e0a050607080f0708040e0f010e0a05150619020f24040501180f110d1e020d1a0f0703061208030411040c09050319020a030b090a08 63
    0x4031105881d0504019465014a081c020201c50080c10002c03114540801d2007030b607034408541210318030000c10009240201c0000036001050003880c04d552103d080c011036841400300030f080c02c140906c61400400ca80002150340f158000c0444101083c0b079103c40c0740320740c04502c555090a130301c58000318641d1080d0002c1c1a10128005050b400c0f0b0355001080c1d002580c5544d025001421040461586414418400d071031154016101c4d00c0001035403c00d40804194105541030304842c2d02181416850510a90794164012000c08441c1140003440940d100207200d12800c81d000c80b000c100011000655483c895805074880d0054a02428111301c50220680f200084818108006040380410309440c440d1113150b056552045240740d400384140c803000083d0704024401c664492501d1140702098440c3d024800b6925a00d0f201c0003142410b045c2018240300d00fa16148207410318031a44000507030f0360000076108403500300d0301d00300c420341702c0445050600450342d001814940d80041c5481d035100b420b0915 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 429241690 1250 429240440 429240443
    0x80406110c220c0c02030a0f03021e0d080a020a0e04110909090d0f020712170c010f05040224030a0e0a082805121b04080a030806040f09150c0207050d0f 67
    0x10440c900b0a903100782c0d0200c0c000c4101a4150f403000c7d0540d0005400400c2141c1400d0185c0119a0051f0b000c2c907a88600840403604502141c10102e038105115400418403508404c10683c1581808501c82004100e40111107040c0e00c515120612442081c2c05641110007011010f041c41c1440c3c500000d11a5450102c2c401400c001100c5502c80061749201182c120b0a440e8030400d120510503a82d120b014410800011481202504000c03001c00020240f04100031000c14480c041400d00d00340c01080b104814405000c1c62001601c00341644d100e80c003008603a40401d8a001c0016504180ea464910744080402d000780400d0b00050b480c9948417500c0b454a121017070142c030507406903027905001c440c203020750021074074440211300104400f0fa003844019a19000b4614074103040542e0303001c1e190720b00f802c040c1050300850011410b01083d07080c81d003d0320145420b154014400310301d80795034222040310507000e140005030361100b0031082d461080c0184e5004000041a45030006203600303012a0003410802c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 429242940 1250 429241690 429241759
    0x1f0f0e06120d0c1101090e07020d09080f030703030f0b0d0c08060703020901120902180a06080106080703020603011e030c090b040c170c07062a110a080406110c 70
    0x1e045600000001c0c501c241400340307036694a0b803810195114a20583c01c2411a41444a490000b00e0807000c41001c1d40e2242406500502011844c010301412410441e08800990307006100800800c80000049948243c1d02d403500040d051b1b40d40c0d06107801010070b825000d80c84103c402c0c8074810701c500d8132100701c25101c2c0740090b14002e454002e000d904900c201262103001c10b142032410181019240d11000e0360394009810308a407501034181e02c6101c2c4904450703000301c113541c850041c0000d0703c1c2480f0760000b0785840402006528155000103017039010520a1006c1e9005840c100305600c060654800c0041d603000308450a8203864408440181000b1031101d4082c500d040d00c4d00c182c40c1e118011568241c810400d80d0032031600c40d090440c1c1c0036030045106503502c60f154888914088941000c404001c91460481018000b1025004041004040d80d10800341d024110710004502d5440c22a4201c0301582401c4600106040f942c608005554403480d501c40100707003240390084490b00c00700c40e0300240d00c42d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 429244190 1250 429242940 429242959
    0x60a2903130c0605031003122303010f0f0b07260a020606090606031e1e01080a050f06040c05060d09140c0418030e0423040809190e1f0f0e06 62
    0x890490b44c501044440103040c80d483e0500f00040398540308040e40403010f524007000c0c0b015400e139840c00d44040a03802e442140c6000001000002c15015001001c0c1c405070001101c0c840c600b041981c000c3c0904400074280001c07200d8014040002c1001036202d103007107209042d0b2030720400100a900d8020441d9040d0041e1003410014580340761100031079108880319100f02d4a06a1036000d0007110607070040c9164100384580d034005c40000b0711400c4180c020405140100918401442e1043c103160030302840641c3c0b82d20070b00501c400a419512010251081030f102c441c0c46407411629040517025411000c0e18508009416203007000e401724580304000000d41741444403040d16561001d1200d08448054001020081c900c00d444c94540c1010404070700c900c0c1c00009100f4400440010500251400c03a408500044d149010f4180720340c1c01c4480042500911110300d107820005166604d0081030010b6908a10888051100350212048050328800300700542e540d4070384480d01d40750ba1007907400034814051903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 429245440 1250 429244190 429244199
    0x6090608010510030509210c010b042a0903060501080606010f0f02030a0518040e1b04050103030c111809010207021201110901110705061c0f05060a2903130c 69
    0x200803a074122a00a828000c0800000008400134840600074080a0084810480d51a2544600d0000c4510390400740c03a644e014145800d800c40d070603107944c0c6002da42041005510034404903010881412044e016491001c941141100c2d50b0718550001440c181c0340800103d5032f40f800080d401d2003041d00b070320791134140040c20780c3c1a1490100b2071348400040e402084102c03141403203500036100700c00d00d904281c00700881800004044c2c5a52212800d056800101c0d40d45106500300c50f011000307174042d40d0030005075045441c020180121010003a00303049014400c2c6400e41c481d4070080b5080c04401202240c02d050624000c1e000c0d51000006902c5080c19211340c000d15039046c480c0c544400c0045503014038214074000191541c1203200b5484010b40140c03140010b1a4031420002c040c56806102c160010110503c1c96604a82d044203102404a00e0441003003e1920b42c10450130035607030303508100c1d00c0f203150346605c00c003155071144100400d041c000b1050040c1945000c0c1c4030904203101c0c00c3c4400001e13480307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 429246690 1250 429245440 429245447
    0x110d0503151f21020a030203041e050304090b0102031624140a050c0c0a05010504020916080f0603030423010f1107031113050403110606030703020d120c0b0106050301060906 76
    0x640001c1c41c03100c0d8a0b00914070b00f0701511014002c003e6074282031298070364001d2000203d800c04207004000c00d4000040100308403a401044521041c146410780201e29151600d66aa0056002d2107803480da031800c0300500f60f0b000300280c940c04016002c1d15a206455864605094202003c000042c51015002c0310740040040c0074440360418000b44035581e82c0e0b11500c2880207014003030702111803008100b280081c001b0381402101d4602d8000d800104c0d0b981428070500070210001481810707040340f100c0307680c00010b601844294000b0142035500409881e0307030300044e003076110f00d911000003d510306086a22800300301050660a80090300c0380041c0e500c440c8015182d0000c042c440d980d2030340007280240005170039124030000f04000030f020f03e800440a0602001124404d5601350f002c110607130819807843c541042119400403043d805041818515408503284141c0742d840204200e401450300d5460328820302e490b000d09034010b00311072420b50703440101924640c428091100029185403010640601 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 429247940 1250 429246690 429246709
    0x1020c030c03030313030e10181a030a110d2a0306380c010213051207061b02150c06060d082b020a05040e160e10110d050315 55
    0x400b4026500d9a81c070780075919807417003100800301c041c8203520f41000c0c0301d41c0740d6614541020311030b40c950f102d0510290104000c6034000d644030f089400e0f040c450400c80180f400d07007a240c0000420102041e42c5882c09001e000500560b13040c410113624250303810701005003080704c1c0304d9003810891082115942802e4210155a11402401040142003a613213144000112064050144006581030306000030003200c10664000c1211005603074010a80103103400b14400c0740401403c0440307095000b04200c7d650b0a403030701c080384225010b02c18910f410300309100c481d0424114280c1e004060040c5108516910070582c0c22400031054039200b81c0e0000380460810050100703545800403003c504200c9100c8500244e01c0e0124605d55101d05594824980c0b46054005403005102c0c9403181901d403803c065804180300401065807030700c00c10241d0640015a00071944000f8004184e42d075494043c1e10b10400e0b525075040c0f9001c00441d22401000d0480254040e001c0c6006442110320828046c0c07a442c20001e1803107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 429249190 1250 429247940 429247963
    0x3050f010302180c0c0706030912080403140708070f05030319090807111201060b030a0f15032306070914030615011101060308030f0702010c02030c070303050a1202160201020c03 78
    0x502c5210704110200f003c4846991208078090014039082c0300442c80d50920507290300440200b43c07a00070440401c0b003c0d600d42508481103190003426464180c800401c04072000901d0181a003001030b41c0300c14080d2440c110307030032a504200d001443d0381c52443c29a40d40d0340109c2e1120880c00740d280c20115003020b00d01502a2503508850700340d06020040c0c482c41e206841c201c021980c040e980c4c17041d12012000a001d00d0004044034900507840b407070400035040642d80407019003070040380f80403c1d255051030305460801c140c9402034030142c1400003900c0d00551034030742110420128480d6404100d00240e00240184c00d465101d0140300240c040d0340c0a050340c2e0036058500006006030115050359a5200e40c402810b0104520004a5155941e0f200e14a1590041d07403003149010b842c104009616809015845483c490b520045207009000c98125407240c3c4607000c000e0400100103140080144524161401960010800c546d0f410081001070700c141c8807201c00303d0140c0030708a9006d44d54034000c02c00d25140d0b07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 429250440 1250 429249190 429249199
    0x32203053a050103060539040f09020703020d051809060301060909030309020f01020c01050307080406110a03090501060e0112140109082a030432031b0103050f010302 73
    0x188800385100010720010350700240d418034404203401181d0746a030415407249094030700054594154180401503581c02801c01010800341144088405204d00b40d058085005045201c00440920807003205071280f40e000e80c004404100c004140e0306815030003041d055100b41c007100d90240c0b100d01c007035071207004061303002060002c84603140785541000030741607a0107000280001803142e100e001c0b003011100c50b02015400a555079502d5411402d25401d0b40440c00000d00040603c4012040004c081b44401840f250800001e50302280c1008070035003180840e99001e804030b0382c581012010090007090000d03401c0d21150b00700400003130840d03120740841c0d0580700c402c14051a00503c036200c8044034030340707a1a5a40c9540da122240f10108200001901d0301d032038074241800000e54103100400c99545421080320301030300104010407100d21842c0101001c032022007410759446140c08000d4601c242080140f640500811411040c0e07842607a14007207824200362030400403a141c0c5481710214140901000390007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 429251690 1250 429250440 429250447
    0x90706030516050a030f020a02100f020f041502010627051608010b0f130b090907020d050d0c1106070810080606030c011421040b0a0b01121d070b03220305 68
    0x8a03440f61000300300c10b80302420003161075921055120126800f0b04002070040e040181170f4a0102018090242e0022074402c041d411304003040c035507412910031403143d404e048600100303121040d4001e40140005003808030440300d03050034440c3c292886188194401e41658541b400240c1c601e582c1c4050004480c2c81d0703036600d41e04c50b820004c20902540c009518031300c82c50410300241400502c02c141e58005400e00f800c0283e03ca109020912041c00300213011b01d0700b950448404801404e034001c003611460080c4060126625004642c2980d4141ca030388840306a03401620b0401c09855040042180203a1011281140f0a43d440300003540b100400da940c25803607081040354403425841244100d110500d6143c840c0d140c60190840148240301c03030202851404104410007080c00300a05d04c00c2d90005c2e040609000e001d50079000200541903802210442035520510800720b01102c544280c2800d44000c2140c0340782d5144c1106d2000703034104544a910911a01450400d048200d0390120300380359245e240e0a00303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 429252940 1250 429251690 429251731
    0x9061d15100c06060b090315070203070b06120604050f0d0c1104020f04050a14010305070302032205030912030316050405150a050706021c0b1903060905100e060907060305 75
    0x4200140c0d816841c1007188004440c808107940c1d20036240140748900e10541c0d500840010303d803c00380d1071170100e401d40110b10708100c010342d004411a4850365004c006036080b540d4103030020348411101c0a0480840c820f01c003c000420800251050795429504129407460780d4501080f5450a031118006041c125180c01c0c05286007401d0300688442c10104054030b090035107942c089820b01800d50b0108402d0b0820000021076035030540314a982200c0c1c42d140a5165240c4405003440b04004070034049100b07510440790105100041c0242c0e07223440e40040080803c0c8107519200741c0e4a81007914a01e021030305101d61190201d0043c4112001c50380041d20604440c003c2c030200e05026088200071b40140300f01000600000b5070544004d010382d00030303644803084040c4041c41701000c86140b00a51402170001942d510462146140102c0c11a0b90151010805c0030152406d54101245070a15118440c03c04440500c0300360085281842a002201220b03c8030b66a140210255030381614500c40540d5902100d54 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 429254190 1250 429252940 429252949
    0x160e0f0c0901051209190807060e1605100216120203060a050f040f050114160f0914040b131a01080f0402090f043f050403050303060f01110102030109061d15 69
    0x641c003082c0035096880b540c0451801c560b001c1c0b0745031b00c1150440d0707000902e04200300c803a2145070300d4125214011f08840c4c4085c609074007500024080c0314411031241070841c0885108000000c1d20b01c2c540e040481c00107542c6d80c8000350744616074008a21074043d0400080140300e01e480341c540300e0f00403800c0448032515a900c4001d180200060181d6255484041400320424080045400b9120702c55141d0000840504020103d1440020b00001c100303481d80c0810400401c118140e041010840e80091002e0000000503206034042c03e0070207080d4103042c914400b5402c4000074904c2d580c42a00c5a00041d0794500070388524400840e4001d500000640c08600d0700e240c2c04c0030150b88181b00d59400c100c8a01d03d20a0486814100d05000183c9940c7d406051280321088a031403008000c1420075034106420359680b252039000041100c6c0c015040c00d00c100c5456032250b1446011100406d008540d0b9584030300000740170f0015800f0b035001c00d41404076010307032000341020405d115101c091010030b9100524030402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 429255440 1250 429254190 429254227
    0x70306090e100504170a020c01030501080c0904021908010504060e0d020312130c1d04030905030a0b0a0b190e060109050108060d0f0311010c0207031209060906050309160e0f0c090105 80
    0x688001d10348030061503890071190006c08868035103030010620554480d00042c01c1e92016004000c1d070307402a1a03001d00ba5211204801d40107071703040718110354400341e0025604503403140c0d41c010071040d800c0c40203000610080358040121281142e0507915175940d02e520030b0365207110b07141107401d20fa52004001a0009410340811455510402404071910350342d04071400219080d80c101c1890310038000900c820941c024401c4001440300345c1c00b800f0206000c2c2c642c10f0a031400144004403198550071605441e50b9500740c070183d5500c4040028140c1c5440c0c4240040c00c61084070024003242d41c01d8000304003507000e02d68440c070a410041a030400c4041d10b03a81d50007001140710084043c0003c0075091514140203005180340800c4a500410000d40707181000080245403144c51400e01c01e0b030030810f03c615507210001c1c0b807c0c3c410b02d0500e01c1d6651200200c091424800341a400105401450b01040019400407098004c0038005814084e41d10390b01002061841404001804200d04000800000c504491035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 429256690 1250 429255440 429255443
    0x1806141b1f021909050f06180306040f05010c030b0609040207060902060c0a17120f190c1e0906020c19080102120f0c03070f0e03010207120206070306090e100504 71
    0x1500c0540c0400514000007407070440504010a40203c1c1000c0f41010740c851041c0100303c03901c4d00340c951a140201095506000e264824001c241c00034502e1000d6180700c02140c0e0384030000d000c0303484602c0e150401e00c0080f541501c0465175942464503581d4418030900404005003001001649040312140030400250711000e070840300741d91501e5140015a071240d028140201841d00a40448159864031448400307408900000ea4042800b00c510078090400546900081c1283c0501d11521410060a418180186484e2400d41414099031500d6440781541e00514140341300030743c400d10780d03600590703002005004203401070b071280031038515501e86404801410340f10426400c1c1d1312a203a0b211242a6480910440c8800c94a8014424905a40008a030703100700351006007819400e12180060078618084038080401002058402240d5001c0d8100e07106540d101c55100e10b01c10013004040c0d01d4a908407070440109281c9400051800400c1c00703480900c203034640c0600001c2482070341c1d40f030003044043e10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 429257940 1250 429256690 429256693
    0x2151303030b03010c0504050a050306040b0f1306180b0c1c0c180807030b0705040e040204112a070602070e060603090f060a0204030b061206280603031806141b 70
    0x26241c4840d2428850750703905d00c690343d4865543c1c44c104000e200d080c100d164081d5001c1c0e0f010300c0410010a01c040c210907000b81da802801c2e852038840f00604a0681c0480e600584800e1400385603007a060050368400d1546480b580b02080d4641e6003000e40d5020713000d0545041c03603c00a0250750090312031550702c031695100150514920f110104a550407040003141c000c03580d80d5001000a1041c802404001544609903140241c58541460381c440324110020f413000303016940390f16543c02e8244212007662010328000c0e4048404c410f4561118a424000b40c1c0c80c440c5601400c8000705000c0c0c80411310105841d00c0407102011a01c1d0001445070991005100307928500800c0704808081a05101d4103000c0c41c0b150034056112411802c00d0682e01001824aa1092900c8001140b4100002c500f06c3d90242c080e1455450b000108943c6504103179080f01328450300c83c40c02134040308054106411703d03110303070b005030601100c1519420b0603a540c02088845400c0c8401c10f01003d03103c04004151340c50f50700d06000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 429259190 1250 429257940 429257951
    0x20c2103040608180708150601020c06030c03040620161a0711010b0f0a06081302060301060207091d07031704030b0c0301080d0306060e120309030f0604120215130303 73
    0x84403421908182c201a000036415401d00c03048220356082041218140005030128600d000c0020b03594809040c0801400355a900001e0320a0b0b001b48540040c195001d84a195a803401101031000c41e881218110b80c0c0c40c8ca0120311144e0448032100308041c0c0315075841003516212244508041c1d2441d813200c1214285051900c441907487c401048170f000300c40d01d481d2465108000b014450030f44040d06002802260050100c05041d903d08003200301300c81a50404035010b8490181002c0c07101c04c0d8400180d04204004000614298002203000884030b8a603002c00413128489896a0030f100442203058241c5d00100c0d05001280040300411002c00150404030b107004c0d41c0360f9038602c10b07010440310650300c084044010040c000b0f040c00119940203041ca130400c401c85c100040030740120381c0003002e9401500390b12010307000004100300f118200d42004040b41d88402040806659030b1a045904481742070890100080290000440301c0390240054042c0700140d491040042c244c468902c2d0582c02c064540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 429260440 1250 429259190 429259249
    0x201090504020c0109120306081e1203060f0d0b010915030b04120c05010c030b010f021f0b01140720190b0d141f08070506030a090c05130b0f010906020c 67
    0x101b10750807140e80f6a1030204100c4c0c5800500d504100302c000d00181103003a00c0c0340e81010000041641c0401d040d83c10310325074a03600d0b140003203004e031058050210b4000c1d1091036900d01b40600c00108034100d801ca2101400600194013040c0102081844000e101c5406100410009006164482c2c0207018520b003461380c5404584038a829600b001401000cca03603165020011075038080b1a05520500c940014040c0e810361489a032510803c0c102001605a51140c14150740c1c1c1c0301d8907505d0b141e0503400c503e56858120b10b04014100500c107008200d207820380502c184903a400d0100012400c2c0bc803401c3e409a03294580840743c0d03001d034081700d1040c0500d03075941c490055014010800d00d0040c4080004a810b41242c1602d0040b0700100c0d40101c205035100d80010080c41e0344031404c50b9030100040c600405d0b03207521480c0c00a00d0003101d0700101c1c1d00031020801808444c100303500c49550720204480701103420750800f0040d03814641e03c0c003e5100680095003044043c2c01c00d468001e00c4003840d003445200d002d104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 429261690 1250 429260440 429260453
    0xf0b0a140a0b09011205061b1303030207050a05100504030305181c050d03150605130801110304031b0b040b04020a05090a0e0123041203020f13031406040201090504020c0109 76
    0x2203480c1c1189a0b51090010740908065000318003400c8406584548032401d0341311640d480c40300810160300702030340b004600144203c05003a554040300c500c4010000648034078020b500d03202c0600980b07009240802c80011580707880701c2c00e07460200e159141c26241c14116102140d803540800b141d0007a44501c1d401401c15511074030f0341c0740d0103031185d406220151015440d200d81030144c41c464090070181001c04041c40fa84a000b08803040382c605041180d03032402420042c1c1e071040e80039400043d6039441c2900300360142d51a00700451090784640d84040c1b40c0c0100401d0680002225400604a07842580000e400640c080340107030f8105000401c1c02c204180d42e2400503900002c1280c4a414081e2600c441f281240302c07d0058040d4290300c18003070b031499800c00701030b61b40d0098024005008480d541d50105842c0d4002d0381141c0786080c194003055036508950190b2414004c42c0c3c401110b1f110300c04011145032039008204507005540c1651907001c0e151414082101a40007a05282555540c0d10000b40010b100c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 429262940 1250 429261690 429261731
    0x3081b0a0c0f1404050c0a03090302010f0e06221a07110604030207050a080a15020708130b070308090f07150e0a090504020405092415060a030509070801090f0b0a 71
    0xb0740804550031603081801c50350f0107880101003140510305003c04d2020001d00700d801d640400e0302c0d510380050b07030300d0007800d007203000d0071090041c2070000b890099000c0807040c022030304500c101c00210140c1e01c00340040504004144004170090242040c26181e000d11900201d13040e40c2203102440d010400b4119100302a0a0010a8408801581c0050300c204130504001c25104024004100600310b1500b080d00c03400c02e00201014020020381e800252002041480c02c19945261401c00d40c010213203844401c0c8080d00d034420030301a00418103100000c0c226030000506031880c4140e94010b45026880d11908407900c1c0a211200c03410300c400121a10815240d03812101c0060118003000308030740c2046e0041c03004a403000781c0319440e986c0014546850880d00103420802580d08980f95402c0342c1c3d144031241550050030302490382e01210004101603c10340c181c00c2107005140481c2540c50055403214034608071840d015000b0020001104070b6000301d0440b0b918558850074101020644400c5400d96440085 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 429264190 1250 429262940 429262949
    0x9100c060509060106081602100b04060308030c0304060b0402160221122101061d1818010e061902030a0b0d050f07060e0f10021c05121003081b0a0c 65
    0x103200f1030041114a41c06a40190000c6194020510065031110001e4076038290800d402103080d2a0841c80556032116400303100110b07004400240ca80c00e2000d0004815401920305556039401c14030074010300d1a00f8401ca91540081401a803020a01a424840b14502c454500f032001c0c004050800f011070340a014410318510070202207513491500403100d60704000810342044040300e0040c014004650030511680d881d09041d0644c2c51283c08441c0010002042c0b050141d2254005000340241c0c11000c0d0169180b02c12440024484029400b00c0103a840c04c1c01c56412400c1e80000b054518100c20343d0f801140c100e03420520204449400401240001814800489003a0f100400c3c2607491607062100300c020b428246442d261681d4290300280401e0030302c1140030700c10b15004048010890080294141d4503040790f804034035002c0030000162094020090804500044c0e000007142e44a10900940c107032a4440c40302802e1041c000e10b050090314800c032584102d1b1088003542004161000507480081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 429265440 1250 429264190 429264193
    0x8060604270f060f120c0b1b03070305270a0b091f050301030311012a030b0a0306050105040b0103051b16150f1b0e01080606040e0405010e0c0d0809100c060509 70
    0x42d03207015800d00b900c1d01d40358170060305500041d800000003107406800c801190509260799440f90000c060031032011a520145040c50b1100283c00c10030503400402508821035107840544040050741d50100711000720366140d80e440314a2603014455004108040c115a403005009800e264a004245810340d552006400300842d00100c01042015032000c484150b61a00d94024081c24000345d01d031903070120912101000141528800005042c0301e42e10440c0d29001c010074490704c00382d070b80c10500010030080c020140910300381120154254001d02074940101c044040203138003425591882144ca410400030b200c090003020007503c000c20f54140000c58512203110002601c40d1124150070222075204400b4003d0413078000409124641004114107a05800e08241c1c240303a40e88400551207219030b8000300d50301441e000500003030000550048030110000c400b103c0c0003100f02d400304007541c0c0224000500500c001c0001003003504041866941c2c0150b03904244c11800b040b56194000d0350000c4480e142076 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 429266690 1250 429265440 429265451
    0x4020a050f12061c0314030403030905031602100203070c1217040e090d110c0d0816060906060e0c03010909031e0e010206181b0f0a060f03050708060604270f 69
    0x515144004203040703044640300344c16520559801409812620304941100d26010002030309050094010501c80350b4444c0030340b40d0310b051400801200c41000c62042e40a05650015801810300001c11039150710341104500700d08500c1c01c80c28840c00a8400c9040321a490100750303d01f0310360140c401401c0900302c0d803250007015140c541802d9280800c800c4c891030411107924030a0b070513800080307107420203214259121865007015081a000921840c48030a981003400d00302c010a100d40795010301442442820148185943c0f0382c2c481500d11300c15100b0281c0e00008000401c003030480740c0d1011001c00c6c404c2c1045003c000d401000050740d02000d64041e80421164010b00419680c18440e4952180114650b4200008205107440d9207008004400e01d89031910703981c401c15a41c6003000f405440c0d900500300c0400584030080207050300d5807091480082030500d400700d007450380207420440c42024044c0265003081e1400d2507505a40820701955481040d000c5c13101500340415000c0c04401d81440d0201050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 429267940 1250 429266690 429266701
    0x102090d0b04060e011a040e150709081501050f010c1b1221050f1b0d031d0a030c03050a0c0609081b0109020307090b190905010609090e070504020a050f12 68
    0x141c44c100028034681da4034142c3c4034451401d2440101524103415180000d01d4104800c6903031510800324400e5400312444010003440d150302c4210582500c0b1180181c0e42c401104495405035610203020b034076488014111200310552040e40803400030b0707015010000c0c44184d08104d0054800c02034000d041070003245000003042c00030b4440c0e0344250070b180f039414540012401d000244240511105104d60303420028048d1260301201f1412844a420030040d1010542e68500240c0205031114402c00e80b15403806e214000c105001c11a205100d80549400e40c1d1070019613001c503100e07070040b081c14051220560b02840803034038500c51404114441d04100b91b41e85407114420003555684218456203a0500d00800e0058402003162411980048000702d40041100002107050750b200c01e90407500000c11000152030303041074020303504a560f10b840d0425055207506801094405540b520001648444805c00c014201707540104800c110f545040f60602e0074a0112140ca603006594091304000404103004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 429269190 1250 429267940 429267953
    0x14090d081e090a022b03140f0301090504020f0108040314070c09090f0201030e0d0c12030b091f0b0a050711040b04020d05010e0c0309060f28051608270102090d0b04 72
    0xd202d103101d1500360034040d080800071758042141000040810500800100800e500d51055501c4c44c0101482107450750b03101c001450040c07100b16400c0c0d11030000144030000075409811001e001e5601741c4d41c1d0621200302901110b00f240c7c01500708442074640040009000340c528840c4d82402c0e0b02c22500384040700480d00005042c1c4041d00384e003000c1600003501107080d10b504915001200303940a00302d10500c03403c217402074005100e24842c05421040c85d00400a00300048101d1501c0d00d50811616098152900044403450040510b03050110720200804000310707021903041d100301d0400400210b540403122020805a0f0004640e8000140d2203200601520011088031580102d841c0840c83c10740c64640c0c0f051f9602c01014081e101d1080c0d00601181c41e108ca181558508162412841011a2004c4221100500f01102c404030b039030314800c509010b03551203400403c1c060783c0c0911440031258a0b07916031101641300d035800d030142c41d0b508201c500c03d0b903118920549000c9000340c1ca0f1403090302e071130704226 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 429270440 1250 429269190 429269209
    0xf06050c0f0622050a05150121080906070521070b0105041b0c060f02130602060615041a040302041d060a02040503060406050c070b010308040914090d081e090a02 71
    0xc00030740000c4100800c0010f01200d11580740c1c88035003048110103541c2005418204c03924005403440c0540d03c400c0b018105401800c904030348080c2034002840c0d645515a030001c65260340010311f20702040060b440c0c0d500e450300c060079151740076001360303402c600f60701d0300c1c40030121045000310482c0c2d00040759603c20b00448404040c0100810f031002d1001c148040100012140000803100a01196403071410610a103a0b000003051030942c4d400b1561070b00c510380000e030704500c2407003981c00500c0b40000040c0d540c180721121103408102c030341201d802c090404031003000d04100e1300c1c03c10046079414800000543c1d214056964280c907005100c070545418854483c1c2400e400070101030520340100000c114540b40001d400c0d83c826000704002496441e003102510540c425524042c0450706010000300c14480d41400a008440c0c0c000804c101006030710030441805072040f40c49201c1d41d041442662519406080c1103940030400c00c519905c01d5582c650380070544402074459002a512024a5404601780109034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 429271690 1250 429270440 429270463
    0xc0406120204020c0304090501060c0c05011d060c0f1006060906020613030807030b060706050f180a0605040201020a020d140712050303060d030e060706150b030613090c0f06050c 78
    0x6004990900900c0c600845035084000d014076400a0b210502c05130610542d4064180420103106d03a581d241c0c0c00074482005020165000d040a400002e40b560007851001032111002d24404020000681004080e420001c4912020b01820501917080c0c1800d000502d02858811000144e040c2403a1000304408030941020003954040c009015590312013074901c0240c550301d858500c0d0123075031b142d000310054540024010b40042c0c1c0070030714a0030030030103804c41c1d44180c0d407100c224409507aa41d900c0f4041e40030301c0111a0240e0700311640204c00302d041500134030340c82401030048840403580760307001c6411943e40f4501511700281d000103410382c42e00c040c0b0801c2d00038aa1a8000b40f084403181d140e6a85034440a0039962245046007510001c0500034500d20f071500c100103040d551a00c182c0c1c00c00e00041d012169401801c20b09032003002c0ba41c11180d2094900a032406800d00030854143d000c500c0040c05409006e40c3c00e10102000006c4107079606040030023a180c2961402c0d11891444000c0e85041d000c00310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 429272940 1250 429271690 429271699
    0x603050126010b12010e010b06180910030812090705030c101818060e061e060a03090506040f0519030f0c0201121109010f02030a050a0302180301050f090c 68
    0x10400300011600c0000d1805001c1c04040031107070a14141ca0043c80780340d90103a0020300030108460b0748201907000b00034650249000748110814642003004030311520485010500b43d43c0c50641e01824415515540806403005a1140a40300e86428545030401780c05a072682000404001d8410f4045c481c0701c005003000c0e002002543c080f10300140c00310003501c0c5040b04218615003888400484140c00900411481c00840c0700030504c0185000a0181c50107800340d16070441002c0f5005080260001420885a550aa1806401004015103a4030207902c2004264980b5035a2000c140c2c140b00c007a016034414101007110224900e402e6042103008594040701001d080d845001081c0c010080d00032000051600310300d66066840141c41d0f0f4001400a042d000e40b524420482c1078040000600d4040703000d032150507618000103812070783c034411090000001182840400350050298000d031aa0703c1001c002c0c0805400f909022130b08541c03086460308980b4800f0b8091040e443d00900010160400503034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 429274190 1250 429272940 429272951
    0x90210050a09090902010c021002010e0c09010f09050c0705030a0509010906110607051b010e010c09080a080a0e01030b031914190b100e0705030f01090b0306070e0604090c050d05010603 81
    0x30005480c10306a480743e402204c0d119410503007168460f003884914243d00801812080901b084c00130b00904824031500740305c0c8142901000e00b480c0181380d450407030f0b14409580784110308000d00c82d4064240030300f0f01d000c2c0305414001000042d40600c083d190025a65640f140c40302d00710000101060309036800b04051000c5030011841c1a040032880680c40f00182c02e0040c2c0d5000011640c140c2e49144040464280d40703005110719000b81c043d003103c100b0030740c985e945d80680340c1c4900032a51142040354000705850402c002c54503074680146842c0d20444814140024a20b1690b0003007410041c01940e031442c4491a01c48103400c100d0301101c0b8207881410100108a06090140c07420740840300e1f824007074080f01141c00040d20000308a0020006003039030030104a014100120050b00c140c00c02d0b1041100020050300209143c241d501c201c1516401c0240181b0641d10399600648150122120003a00203070200300c0410070901c2405010078160055036155501c0c404805c510007120740c181c101000300b50410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 429275440 1250 429274190 429274207
    0x61504180b150a080f010f0203090709050903120f06030609011e24030804170c0901050f03150108030c1e0c220618140106020d0513050405090109021005 67
    0x114584055600140220294841d40041c03420b403148085220340c00700e40366070b021440e0b2402040c0301641c41c032020002c1c40150121380216007030f0f001c02c5801c3e01e00b0b44e22047c420013440030325800c10360700141c00030250b034039024070b00c075000190340070841d9516203002c14913042c03040c3d6050030030031242c2c0070007004020050785000400b400000d9400d02c142500c1592035504090f6915403110344220b441c0201d5041c0801140c1d2440c10b0b01454020344a1004200904508801391007000705041c1d0214600405022032030b0300300300c100600010303411885505841200780200c84a480141c4d030300c2c040c04111000759100c2ca20001c080d45411070340c8a00001708140c4013042044031100180b45d0001c4001100e081802c9280000c07400e51001c14004003a18107030601000148544901a0b9440804009a030603c440804c0c500420a8410280b00b4200140c0c032000a1076005071141d000b5200c804a80a84942c0c5243e5035000039056682c1038500304010707503480d4003080271490307c000020192103540c10010700f0301c07002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 429276690 1250 429275440 429275471
    0x10e0d12050903010e16050a0605041a0313021e030d0513050609031f0c03050f06030a0b0c0408010608030901031b1e0c06095a080408061504 62
    0xe4810400c0c0301e004200445166001c1d045820210410400c5a140842c10030700302c944a1100e1040f680603031801500070940724480c408403800d907104410f0100c40361520175407808080d1702c001c041440021100102600503618494190350b19120740400d603e06450307003420181020204410b030402c0c040100075604050024408000850708112000c81d118079880006ca0f0074441c42000f07420480000a40c5c01c00094085d900c6141d01e04803561b001c204564580d5840b00c00032609554403581581710400303850001d104030b0803465000544c00d40305814107560f00c4142c5d09446054001903801d42001c54400920759061161461481009060350104220740201520a00640c100d114170b45813020740314803809016480d00c0101682c4900704004411007410b01c50601d030911601044e0b02c402e0750240f0090040b2822104504031010104810040c800703412146185100c00d218500041300310b00c808001ca0f0540025000800000020380a6454000003a1110459506500b4030851401260035460b011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 429277940 1250 429276690 429276713
    0x31003290a0b010c141905010e0c0409020105070b190f0204050f06031e070216080a0606091e020d0902181519150207090612031706010525020907030902010e0d 70
    0x40090080c0050300d82c145c505400e0040c4181814503410140320403508200c815800410820740391070591329803207901010801a10724003c1c021740010024020180071801c481115500302c0004503200000010505a030000d0362844415001c0d12940400c00300141e081800304001c0b00c0c0b40c1203800c60700e18075002201d41d43c4040110030022140c02d504c0009040c1c0d5008004e292106c400070f0101109a075500c00c51141e82e03401003035040b0391550500c0f81c00104901d40307000380b00030001c1c00425410030f4081c00c0e00400c02500101e488000c0b5546461117140980c84811140c0144032a6007101055880c0404100b40611002c55a0900803507020b110700d80c41c102102008407c5d100304004400f040312030746004a04e8582c01d40c03c0070640302e160400001349255000e541031101803080d2944000c900584170681c04260040381c050740428410000029508400003940c5020781800ba1511901200d60700413600705003048075030001096669007000d096680100480c1d201250880e52000060100d60750301d101d02e076 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 429279190 1250 429277940 429277943
    0x20f1501051c060b0a0e0105030d0c08031b120a02030417040303050d381002160b0a050f030c03040b090a02150a11060f15011d06031003290a0b010c 65
    0x200000c80e94403c2024a400c00e4141c0c4100400d0290343c1174884080651655003803060602c0380c071516105003c4a401211f40340d060f80e40140003641199220301c4000c0c2409108601c866081004000d41102011022401c0e4041c4500e48001a01c07485c0c98506030652010050099081003c24801000040d510408403214a854840b0100b8661900601004480301032a0128821b002c066080070440b103101c40c6400c05400700b02ca001d080c0d0b400070701e01a40c540e0b031541d24024240300342c0601405001d01080041401d080c1c02d2501501e415035001c50600b06810540b190b42003280700100740000c1c00403101c0b05c41d8000c1005006040c8464082e400208017445004550740c142034040b550600c110302a624000c031204201c0b003510308510340300240040ea880d040b19a0f02d98560302c4155186075502c16494014000c04011704040380460301c900704401da4000620709541c00e0000130b40400020f8840300030a0384181c42c0082c980e440792150134011044a4002c1030f82b04d907240f5009085c6140e0381e1081d002c2004a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 429280440 1250 429279190 429279229
    0x307060e1c050721110d080610090e0c1b06010b130e01081b0f0604060c21020727112701050913020d05190501081f020901030912020f150105 62
    0x4400f10030640d44030b040d00c980a040c46c005d4090b08410030f6001900316102e42c104039081d0503281c241c40c00070b490004040c0903040301340401800150304207001c6001071002c10440c001210303c0406183c3c10360310b485403d82103a2100400400d814004410f20402c01d00a0030300054595015814000e00700c1c0c2e110794001e0440c070f003805a4030316407600b911581c6c402c0186803005000316030b980f40c841c000600540c01406048071003098502082c9021100e842280c6400c0c0071682c00780c8402464030040c0880700c5030140304560000c10400491204010320705c140c000c0c01d0b00c40040b80351030f000040c80e8182060840700311076620200d06840c1000c0344c0c0c0d1106c215400b001c1c080b42d0b11a8941c00751a1945d0007070081030003080e2101d160030300780100c00712040d5210341100030a0304180180da0b01c812017141c89540d0700c149900300c039020200b441031891060b005061140e50601d000030704042c40791241d50203042100c02070342c0960020004c003000f20b0300510092001c45040c21010a0a51401d8007142c50860064030030080f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 429281690 1250 429280440 429280493
    0x5030604150b04062f0c010c05010b0901030b0604050a0b0303030105150403020a060503010f0f0e06040c032a120513020409080d051501110f0a020f030307060e1c0507 73
    0x31800341d105000c05844034980039030f1500c1c3c075404081d055060440200c001c1c9000e1400280700c25070b040318201c20b100e46901c041c0c681440b00d0700056850401800d1b0444482d501ca0b00c0010403601c40c40ca4160007107005524241c05402d021083c04103d800160101100c14100340510070103450010032241110405d86445165003d10044281c11340102d40009500c81805e080000b6802c0c0d108010718140c4905840324040950f403511070160001482c42402020100140020814034055000344544583c07402c1c040f9403080501d6500500702c03400a03040540c0740c0b21a250090542d4088207150346038940103c10026810260030b2500c469a01d4071000340f05a840d140d13004200001401aa030407242181414811820310460440703003001c10300d060ba070003d011103182c4030641100007445010104400080c2121484640034801c2281c032841341913030544000c0094900007081d0b4401d4644c40902400606282c14803048400f06903d03150130b0810400c007041c0645408105280000301031242c0e00007103000c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 429282940 1250 429281690 429281711
    0x160608130b0c090a0506031b07111305040c080f071a041806232404211e02010207150309120206040c05220504080706090c140108010605030604 63
    0x1011190040c14001036809024a01d0149006000b60000490b9106813154403841400001d010031035981d40e0b081101c0380c5a1002400010040c4489401a0700f440755100082005c240384100440700d80160640d2001040117001c0b2800c00000542501c0010b030141e094410f1030303247d88001c5400742d0340e100300608040710810a102000c0750700400e000032481c28800c0013240400000c02d42c510800300c901d60400c60070862043c90300c1c0107500107100141a045204411058450058200f42d2200d00d00d40c0d0403c00401c0c24144680c5400700d64036600b442c0d131001c618515026000c90b61030201181011800c041c60760040c0e80105030101643d40070b00308a20b410540d0b41003103000d02000400035068600100408a0081e404590180700ea0300030300d03070000c4145c3c3d50020721001c4520300500c0e40542049170040400c80c03d42e0b402640e00305000b40141802d14650752030715002c0350303a038841c1111038044541d01080001c101e6200300d80b1454090902c03035020741c501a005851480000c181034455945c840b1190b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 429284190 1250 429282940 429282961
    0x9030a151b05070c0f061d010903080f0c0709050105030303130321020705150601140c1e06040b070509030a021507050a030e010e060910051b01020a20160608 69
    0xa05200c81d900203488011060340003410541c81081c0030f40c4d0907940088042042994400c0c0c010803103826a46441012416800c000c03041d108004800e4100400000004085003040020384082003c52500d981d488400151681c43c2014692180a07800e080c0001080913980c0030042c0c0398040c00388490528221001c1c80c04440240b5114412020074890446442c10403840307601424043c1d20510031901c014081c02c255102c900c8082f41c0c010f00054000013240c15802c00030700a000110500c0d0111500001c4111400d0340b41c0100b900040b845074000c03810007042c80b040d0031885820038050305144e403074000c016020a0301c40d5101d0b940a40165250803290060001c4039003100c031644c0e00242540c0c4000d11b1460020480c4d03c1b41c2c101d4500050510f0030380318491030071400b2a40d045000a02d40f01a520700854103582c00d41102c00c10b004d10640900071201211002c0c0001e1480c410507036944035030030340304d03128803028071aa031014038815a000c0451506020380300e540310015076202c1c1c1028089c03583d0305035005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 429285440 1250 429284190 429284201
    0x15060d0f0f05010f0b0d050d052506150b0f040b13090e0615010e01021510120b040507060302030c12090309060403050c0907020a2402040e040f021509030a15 69
    0x4040c840241e55100900c00b065001da02c00c022000411300c20903070a24100600f220070440060a990840210601c105026100501600324050a10300b6440108200c00d02c5000d4540c0d001e90320f090301c0710f000c440741d403c3d00700703c90303000d468522110b50030840d80c0e56148925000c1c0307008900e021000000c2c822140110840080c0042818080c14002481d141c25080c1d241c071003e0762205251a41c90103030900c9907001e483e88490028040c0e004000301c180d0101c121102c0c01005e00090600c1401e484082000215403100c031500c103000e0f83c0344200fa82401e01d0f08524024260f40705104051051040c018203407400c3c030071a00941c000345401000e42c0c4441c2c02b180e007588185803074681e115000207000000c0090118900b00810000ca428034103580d1241e40990300c1e130500880080c40300f0a40c505e06030f08240c3e0b04c0e52150010451000050400d5200d0024002e8604e00395002d445001070816003a045141100112556504400e0031a040000280c0420303a80e00d44108020b0407507a459200100e10200ea0303011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 429286690 1250 429285440 429285443
    0xf05040f0b0903012901080a140c131401120b150d0f050c0c06071409210c0102010908030a02090f042a091511010e06010603020c0f15060d0f 62
    0x640031903a600203241954080072805000b0350030400e001036450101d0b000300c51080c07003004036107245041100044410302c10042000b100c80d503507660f00d000da1140c10070240b4401d42007c401156100258100710003204500c1e4000f000c00741440c50000c1c01c0b66407024006220481d0140c1c0411041100310014400e00b20a80d10400002000b00b0070608171480c540040c40203ea041404100645038060000e0051040701907103a5240d01a001240d0103030310580100401c10319000802d800e0a940c180041e41d80b20010741020705940721703152504540001400801e8461400340001c20803881e1680c6c0d48001408014907074100c1550110313072084107071940b82c1c6980440c28028810410031040c0b602c1e5a030103079035003071910450500341c01c2c00e05819070080d0701000a462140c0a12600b6078402c2008846503005c2702d2104c030070341d503c0b0103c0a401010801c2094064040b0b030302c01603240c6130681c19162070720b0100320811445034400c40a00000f04209042c1c0d680143d81601e428082c032549007000c90038202c60040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 429287940 1250 429286690 429286709
    0x3190219061b0527210601090c050304020d060b0109031403040f0b120105040f0f0c09060e0a1a07020d02060403240b0108071808010903050d050901050c0a0f0504 71
    0x544108119480e40305868038a80440d0320402c0740c000c2901280c441c01800120740120031001c903000c40c124a42c8800c14041c96006001420240d2a0043c070300b0441ca8010101d8080e50028005010301070350341c0503100d0080282c0c540340d404c40c07034583c0008840201141c0003074003060380c400e48102940d1294440b00007464000a1801901641e203007429600e070b2142c0703d0880c3e9801c0a10707020500502c0760007110b207101100c80d01c09890f6420902000f00a144481d010090315070340c0c0360a00803034043d50040800e4450280c0307034a44403d00d0079902801c54006240c0c1c15100d02d039045820302010303040c0703109541c0000d0265103881d214a12440840c200c1d80700380c00702950084c000b01d000002c0000088a04a4607180f01c4518081e00a44a01030301c02d564202048601250340d13907001803460391213025460407040c0c91850304244181c2d00c1e401d4500b1601c11803400d90000790b00140d23144030428680241c60300f102c554070003003200e8505201c0500c1d550091540400070041d81e04904603d43d446001910007070910042d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 429289190 1250 429287940 429287983
    0x15071806050403050601060305010807060810050a090207120e01050a0810030206120108010f2a0c12030e120c0a0206160606060c050c0406030237030b0f010f0305031902 74
    0x40034100b0b400c54401252030344100000850740c0c6101e8007540b4120340c4000024207801c2c0c10040f007038604050042000402180901c00011301d0341d01d440d15034008101c2240c006a84140f075081c080741040142c5640d000340009801506a03c0e603100e012204515024905900940c880c0240d03807941040c01e610280d071008000c40c0704007049140405260481d080080200103401e102d03030f142d609031519008890442020030441800d10b40824203e81e00c00340003031400c90400b5035190740b003091008803601c0440000707607524580c0c0c0000804100b44981140c0c44030302e95082410288180d555600507081c001d020380e030003240c418030400c200f02c1220300380c0d03034003020501100c0d07200d0318000d1140c240c100056419104400c401300c5507040900c1544192600074090115085281721001a010b4800781403004515030301c44903200c0801401060805144174440d0000c2500740240c10803e48403043e0080002d04101600c100009080041240c9414035481a00210003109140c11f03401d01c02d031030b00d80402199021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 429290440 1250 429289190 429289199
    0x819110c01020d0e061303050a03051512010b031e07090e1e0606090f07080106031107050a0b060111030418111902100c140d2f03012402150718 63
    0x4d400140d520034480c0101c401650355004820620211820060042541000001c4040703211742c1020b54080300c00001c0c0001c0c12a85000b08050054410140d140c1da55100080071451405102ca4050064140d254040110114400c142c46078058402c0f17101182d41c1d0f0a01cac242007001840a03900c0001c0824201007243c6058001544ad1082241c40f50b21410f400c3d000100c1900c50601014021481e56503500c01c107078244142a00185000d41c00e8144e508000d014000c001031007013280020701e510031713a034424403410084000340c000c1c0c0c4510284082da400501c42400785240d500b0741c400129002017008140c41c030007581034250701d218101035001a25a904240301981d6000900c000b91000d004400b004400311105003154141020f10388115035850800c50f030b50030060140c210f41990701c0c000c03075600d114502c00c0d4154075000c0c105801000c410707100030004000e01910048044001004900d40031942464107070025100e69120601a003d0410200458801441510f03102501105400d13243c3c84151103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 429291690 1250 429290440 429290467
    0x91515030702010c1b1101050408030423030a0b0c131d0906060604210c0902190e030a0f1428022e0f031404030c030e010819110c0102 59
    0x884201c40035600b00300d540c41005108424035031903208810444c91000c00700d69100104403504918080c100a41444003080c10703401840140b0083c0030000b40c0c2e80300a0580c0558140b401c00640c1b00380c3c842e030000414400400c4a180c15990321a17480c00e440b41c0d4071405c8000305c0b07402c6061707508003400100011082c5038001c074109016500442a00c01111460383d01c2c4410400c0d240325501588a40d941030301c0100d0f0000403d41c0b40b07040d6442c03041d0800421a031f25408160226000409020182c0c4d00300010030201c4d60b00542001041c12080d0040e000c0903640340ca81c0004401845401064407000c0182d0140c021130038000d00012089902e034603e561544506100400c2803040000da00c40c41080c4008264040701e2650402d190407140c000b1035064001d090306a4030800c3c2c05040302c06040c0c441614008100000c00d492f84160b200c0e488001c490101ca06001b0400f01c0300e040240d0500c00e0744820700695801c0800c404075203030310700e1348003107944d400044400b0003501a400352040158008615036503400078 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 429292940 1250 429291690 429291697
    0x30f0a030b030115030210030b010210020a030b010917070b070f051b0a14150a0516031707050309120c070504050a05150117040209040321060602010c09060509091515 73
    0x400b14020701096100c44c1d110041d11400d880001d44c84094200081d400074080e800040c0801c60500580d0310045640004c07906036070000041c90300103030741c4000c840150360b04404004050318403034441c00014140c0c83c0b9010b40d0703081140100c401165001c82c0314810010082203040342507038004152410040342c3c00e00031045010700840b883c0f05031220703c80032403206441e03010302c0c0d801840100402d03d811044400c12a555022aa10300100b11040009174081c18042c82c0c850b8441e0322a5545e00c420443da482402c94402001c2c1c071050801c1002c20500219840025004070b00c1082e0514042e95840031401c4103240914680c480b682060130a001c01c0701d1204141d01240c499100000441400a0308200440d0028440c1d02400c44400201c000305002d41482d1100caa88a44603042c04403881100c11840c6030341c1060032060384027081d141c41003406625820301540300d810043d405d10a1300c0504042c4050a1070250709140ba014183d00d0000a1580c40c40141b100c88058014100183c424240381c01e215640e803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 429294190 1250 429292940 429292961
    0x3070c0501090605270117010b1801080103030e1207080129030f1f09150b031606050417030f04030812070203030403080a020a022a09090c0a0e09030f0a03 68
    0x100c901e034000460300d010f10211a0b02c850301c0a00c0780e503217000b080c400f48030489032051030b141004283c520b070329150f9030704020403400b1309820360b0020f84418000007400d140c128003c1207d0704000348a00100000390700805203100303060303045a405030b81203031192941d85011466400086990700300010452458109080303d4010001c05450ba40840485410f050341d078002c0d0b18180d41507500c140114204114103042c05c804246070002c010a200d1040c0d1519402007540074001107800365250ba4101da1890200407502c0064180c0226030391091030000045d109000314070440041d00030000c3c18481c400b206100301c40110140205151b1100e03240c2c1040113554204d1103854904100003008110303540e00000503a8800c0743e0560b180f00c400d50718540c000001c0e4001452031030640c4182ca002c424590b2a550482c548895809a4400fa064005080003140b500c06090840e00e500b0069a40340c0039100c3c007203004282c80c0175a04510b5030b030311010f05d01865031003011a040c00c00c03c000b091401c5403035030541000d0f5018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 429295440 1250 429294190 429294197
    0x130f0218030c040504030215090705031f05090106032003070e040c180e0a060b0f10120b0402030411040e0f0a050717030c0c04200c0304060906052d040803070c0501 72
    0x303082d0340c000e0108580041d140900503030b01440d5903107003102c020b0b03d5855004100f401034842c840d0b90384011925140d10f001074040c4010103944c3e01c01d500181880b1752517101c400c2400070b0000b10301e075441d50001c05900c0e00c400d001000c00600700940d981c50400081c0c00420541c099032107580f4050420400040e40d5002c0e0210031020240403008146060007a6130582d50b860026141079015a44c030300008152080038a900180b072040d509001c0d9030b03600996069810141c0b40d004030f046d00d5103c00000c0700c03048500c81d48100e00c14014032000c10003c8065a006141c03d035000030308002c100418a14100841d01c000245200f207001c0c200070094081404400c40e001c0b07481e00050440212160354890142014a6401d5400504940000e00d03068100b071b6040310030b4401c114050641c548070030250350700c80c961307080642d4000034007000250350000960f80104030758a421810429000a4540060100706142004e0210501c001c00c16003081c40407580101201401c5a5031082d040ca0310321030032005171241d45d010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 429296690 1250 429295440 429295453
    0xd0807020910030506060108042d020f04110d0b04020408370206030a09030908070306021206100503010b0705032a0d0810180e010e100b0114040302130f021803 70
    0x203102c03a401502c00e0720ba110018100d16641c80b8011203c02c54000c1042d50305903035002034000074141140b8442002c65030b8a1032100801008e006000290390101d801c81d0003a407622500c1c0820741c0c0301c50144c0d010040121070102e08075601000140103030155400c030708194001c1c20b52181d00c030b0000d84481c603441068404404002d2441c000c0d4003003c0c01c1400006904000708200103606440954003e400c2d040c440e041c460360b46a00c800d036551419005400c222201540051701c02810b040c0030740c00030b500c890100d40703000d5100d4407401c005015020600ca41030800d000850707200304001060081da200c0701420441a8180340d42485050049003403000184907601076034280300c2c4c00511546642d48904110406140d807107140410b8121450140705060b48c4090b0750341c82c0044103060138003030a02c0d42c1e002c0c2001007200c800780c4070850085448804213581030003440c3c0d401060200b0716009075011213404039100a030380c0082d1200080940400300d500c2014510025401c80d0100c0503955401d080034007030f81100e40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 429297940 1250 429296690 429296701
    0xc15030f0209090103060906090b0709050a08010c0e060f0712030902040515030318030c0d0605010f060206040218130b09061503060f06090c133b070e0a050d08070209 73
    0x80b48200e156050300f2920040042c8042051900601e0041e403080c180091010010b40320b50103254829216a070014400325402c000a1a01e01521006400090300070020240c00140c094070107210386510310700841010580d0101d182030035082e61400342e0011807a81e801e1140c0a8006d00400003103200302d2046180c00c01041040c61400e40001109201900941c03601d40c4408019122070400f04159905100d5140c85100700d0303d505013580b0000d481000046515410951555043c501e030341c004004544c403d10030040581d581c031200f81c13450700030b21105801c103844130605601c9003411203401418030a031400c14462000400100e4a20920003c90180d1050041c2010141c031001e0035100e6060f80e201c035202048441c907118921541082c400300c0c03441d02d0911142c44044610b4032135400307000182100d81420410b0303200220088030040c0303903000b603140300f0184c2403c00e10003a001502c82c1d02000701c40031134000103441302d022080c0941002055845007049500d06515694014902207014290b42c401041c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 429299190 1250 429297940 429297971
    0x408030d1a010804110411070807050d0c120c15020a1101110403150c1b0609020108060d020d110f0406090501080d090e040b2701140601090b090f0d0c1503 68
    0x420701d840507940e400c0700361281e4076403032440f815400b90260b0085d602d082da440b4192404005180d82c500c40c0000b035844004605000d802c004d0317155001014081012007d1000900c1e58140c0d1101035214140f0b080d00324440d0910701101c1c045400d00b214411320025042c0351890704984d2444100d041e0500901801a4000603061503001d0780c03100600652007400d001c0c858030b0705a00201482c02c4a46042c0060341c0b010400949086000745c1c0540e42241e980c5103803030555900c805103a40c4001c00b81c500f80c01d42c07031550f0f0220745101011000688544103050034098030b56600016212901001007051140e42c0d2640c10001c0140720038400d426440c400c000c0c0e4100d000c2d024210030000c071805480520900d0341c864542451100d40103040d08514103540030304c4481110305400a8070004100d0000040c0043c80c481c1c074406484000d0700300307414803888000c1040002e12000c200c50000000b522200201400c100c08202c5260785034200030025030b1800d02c041800d00d8845540303080394140f90307003d200c040510745210 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 429300440 1250 429299190 429299231
    0x180a080c100f0c1709220f0b0127261908070821010e061e0303091c05010e0102032a18010c140d110102250213020408030d 54
    0x1100032403032003214070004c5150804a0303601c0c09120340c0700c01d00c2d20101100140d10b84040c10200c0000d44040e405a81140d44c041c841c401c030021400c0c8040112800040000c0c03d41c184103800e0205519910703060f044d2a4508070b18040042c0b02c031050781e540c0d0719a0341d1b4428545c1000350b203041c2c469200d4040140c40ca504025200750340e540d049104940307852060b848010407a4071507660b21811350402d903044120071482004040c001d000300c9041c010241801020000164000c00300c00f082203411581a0130b0695003c800c56000c001c00b11803d0511a1040484507044000d01b01c000d006946814140301003550103400035413150381d090603150002103024202042c1d0104480703a540e1030a00500060140104000071400c0c804414100f14209030381c0c66640c012000703007003506604079800281d5144c0150390000195400350350107000940c00c3c001040003484100300240c92240c50005024490015900c8804202041070064441955226207986c0001e030307a58000c15185801502d0001188441001c040c0b90 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 429301690 1250 429300440 429300467
    0xe100906051e011d18030c070e0601030507120c030b06030907090605090915100302100306030c050a050d0204020f0f0a030903020d110c040e190501230408040308180a080c10 76
    0x14000d030164804d0129401e448000c0524880c00504403100d015404c041000e860341003494001080342d18100103d03040761203800342c074180c1494244010b0182d00c5810000d90221501e4007500040c0d41181c5031403c401501c072003891a50000c0f000405c1c0070b00b0040100e0404240c5901001c10720007903680340140b01440d0070484004106400c840f00c5941c2d00300503103030801d402c590001510401c0f1303510394000906075524030701c02902007075450608200300101603495000400303040341e4840c075040c5411b021810701142c4c40c07002485554005288039060351b4600c1076032002480424403d880d844c42c104041e0007000009015070151143c9010210268466007448079111150703c00740865510b07072020320001d04024280780d0368034011003001007044170004210700500e0780200c0000c00d1f4031100d90505d01c81007010568084003010030340200804901080c08840407280c0c0f25017001d0351307101c41c0b040603000342c00b0150200d6406580d81c00c0020301d515002501440441049078441c0d1020650030702130360808080040d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 429302940 1250 429301690 429301709
    0x120a05130201021e0703080c100e030310030204200f040321094203110f1c0e0601180b0a051c080705191515090e100906051e01 56
    0x4a1060f480380f00100b0100001c040000c445c50036480c0d54030004140c025940720442c1d40e02021614400b544907000c0c10a2084581010710700e035003481030690703510340211f01000c0d00440c0c0344e2204440d500c14030000041d02040684189403145600c440b0030200d940f042c4419100d102c0081e00800a402c0b0064006a0100940c4ca88022451400503400ea0281c5040c403842149400615008110006003000701152210b61240b040b60205110024044031103081c0d9064030071100b40b0001943c80c8a020440c1e00034080c5e04075010340444080c0c441009003d90351480c03100340c00f541c00001003a80d013500702400b400741058014400c501c2c2c50014400310388803a00c01c540e4800ca900c03484640b1070b520380e02a0032072540a15403040c9000440d4807032a2500e4405680000310f510038a5160090210403207200080c43c003140e03c00d200382000000c50120660b841e015240b002a550083d90a50160812050158010910080c40200086e0400c500102011694603800d1420302ca408032001c03040e402c030b440c140c500c0c040c1e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 429304190 1250 429302940 429302953
    0x20102150606030103020418061526031e07060c051c0209130218060c071406040605030106120603061a0f030f06040b0702250807090c0206190b0402120a0513020102 72
    0x1020400609602c2346084600b42c80e401818001c00d60a001c1c048078411008064081d552502d0040d20168881c9403400b03d07481d52980540722641e02c080100e6151002d008080d01c811005441110300d5882103a5000308101d2800e00c60094498122014029032034121031009401580d08040000364480c036031216601111042d040030003c22280e0180610f01107a1070003520300e221500101760740754490400180950700070386080016220355041c1441c0b402d001c2da19281881c1c07400c44007a03c01d0006009150510001c5a6134010400450740300d40002e41c0c110409109402882c4803400d5101504925a809005081a162240d050000e0b100241d1074120b0f00400803071b80c8075214042e02540162a14045011300130203074008040004100c1c02d0a9070004850079a546009041854091a5070040d04030b141056054100e46030049203071030748680e14400c428401c0301d100803020010261300d000c00e075100b4400315100c0c1c140201d01900310f205644065040105031580c46400d501002d04100c001d00591282 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 429305440 1250 429304190 429304193
    0x60e0115140406050d050a0209061210091112090c060403110f0a150302030c13060207081005160507030201060f1202040e07030507031b0b03010b0c3018060d09020102150606030103 79
    0x1076004940c41036547c10014140424040050700781c0c2e0103e031b0180300b05489101403000f20300d1040020f90040641b024100401069200514030328007480301d030308a1074410000000c03003a150600008405080040c000c0b9580c644900d07003072080c0d41c00e01052a000e013598072650302c518104241110f00b9244042100182100311480031000380d400104210b2503040c040c04028580b0404070724081c081c0840c3d40140c000340b130a140069107000010740901c1400350803c0c0c18410004120442ca52845000d46056940c0311604d08042c0c0c09070a1903805411110b420260008001000300c0342a04070510031a0113010035030744000c00c1da540e9001400041c0854014050400000700403c0400300d81000c0c03c00030070b02182da20550011650000d0740540c410300000603210320910800d00002c060390051130201c8000c0d010020500c13114100c0c848a8034085000003d0100c03040386182c6102c2048040100480d58451408a440000c0e28403ca4104e000d4491180e680905902e076004180c400c0401400407411030b07185 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 429306690 1250 429305440 429305467
    0x3120b0102031603030615031a010c03110d081006180b03040f05010e061b0705060c030a0e06180105010e070c020118030b0f010f06050403030c0f06060e011514040605 73
    0x915a06a041d48000c024040f0418100143c3c41035040c003a4900007400fa1925002940c914003280e1084109482c2507400c41d41d4070034504a60641420a10f040503034107803e454155440050030070b0941c600d104d030181003204164420019440fa0f8840015000410b07510841941e0308090003e61810202080ea0103000600d02100038542c4240207001100d09000d040e00d4042c21540c07549407009094020404000340c425000c07055100c080348100c103035440c000c0244c85060b00c03400064800b41d0501800030101b100c0070840c3c0c20061113440c103c0c0aa420a041c4607540c1250b21b91a08120580340d403c0ca8000075407481d0000b01d0b18445c0c002ca417980340d40d840d0390340e004403003814004118551280c0504008404240f0386144d03030f8440c1402c5103418003154100101090100c3c0950b0200c2c04100b0200003d00c00241d0010844030740c51750101c0d000d1070384040c500d06040178101c0c50b0800c10396140c5a4000064510350400404141c40d180d45a9800f04240c00c035006541f48603038020503010480070411522008034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 429307940 1250 429306690 429306701
    0x5030c010c020d030c0b07050d150e04062c01050103150903020a0f0503120f0a2405120102040510020607030509010606090302090a060801021305011101090c0b1c020a0306031e0312 79
    0xf082c0380000c5c1154444e600c0a150f80416140781000030b002044d8144401018400c11007030380e4101c0021900e0a10345201c042c42458001c0004002c41c1d20788001c000c0560031040c059400b80f400c40c0454584041c410401c0e40204400d200595405d0700c00b01c4a000c000c0f010307118807801c864140d8041c0c2208203454441b000c0d6248e101c0f004449510080200802c1c401501c020140208103c0620480300d00340a81c004e000c0d02d090003150455640751000c0340203042032340c02846003110700a0f1262140c800520038821700a01030f6620030303500031015a039251000da80c08074a1501c1000035480400c10348d02d81200503400c841035030040300041000800140003602d00344640b81d601071184803000c180c00351500001420381c0c1101600f0a007109401d94180020340c2c100035024014105080200f2400c0340580310015008541d1091881c52200014942e0071110300d00042c2c0106030703a20382c0940d41c460400c0300040c001d0109200582d280001082c4844440700035100140e440c03601a602e1403440003038900c01000404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 429309190 1250 429307940 429307943
    0x7110a0311010c14062409090304060c080405090901020702091008120d090c0305030408120f0f07030207121a0105061e030619030c090b03060405070303050702271005030c010c020d 79
    0x5113146910f41810003003010600c210680074681c8620040b25954840b0342645030706892007504ca40003005801c2c0d00c00020f54003158030500e0008130031141c90034074404230b20131a048141c1220f005400c2000d000015002044118401e80e4146200d56500403800003203400d6025842407904980801e5250740d4400007d803c0440760303d04d0024a40c40c240d910004200e40035441140d06800c042810003140c0018000ca012288401c843c0600c1c0004410895405202c2d82010320300d04200400c0d001c0c2414401c0220002501c031904085e4a10765142c100784111801500a01006407010300000c10301e42408401d40302c3d003001160f005015584404800c00541d040180041d0308000390190400680c000140365100440c014461000042c0c1843e4480382601e10351203180b070013a0b11442c1400006040002e07504100c03038152038902d450b02140d200080120484d0485440c000600d0030f5500000141b41450034003c0390481c01c4401c000b0341d50824143c413883c0c11500b280c0440c02440510015003443e01c00d121099 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 429310440 1250 429309190 429309203
    0xf12050303040b0612010c080105100c1a0a0e030d02041a04061d0301150e09010b0a0f03060245150d090606050301020309070e06090103020904120c05030d0207110a0311010c 76
    0x300c9441d0300c42c0c1d003143c004900c7e0800280c03a80300100030700d080190f241c05580f10030303240c10304a10016440d00d040c0e90101c80680f16000795554001203801030701e0ba110b20765855440041d60b68400840405034080d40190103075401c91a60b141d803008801e081007003106e003181c000d078a41000d4130080901800b504480c8207686909075481d0f00b20352095502c895244030140c50901000d009a00f0a60841421a00383c12000c030b00600801400303004088206401c80200d07a8003010260751203528004c040a41201c100100390544481c3c2010300045540c1d603006264070044144c00d012000416042104101070031000e00104c40b020000c520740c0c40001e4021501d854010744012442c10b03500e07404039007280d00c100d4052800da00070352018002e040f08412a1078010908413042070007541143c002035a40c8801604c02460110081c090240940c0592074002000360044152a2100469420f441c065070040d42c003140d00d40e2001e00160054a01800c441d0140d07600004021600c0c0b82100044d1049140d01d02e094404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 429311690 1250 429310440 429310459
    0x103051509063c090f01030f151803080901050f01150306180e07060206070e010c02030a05100221091209030a06020d09060612021018080f070f12050303040b06 70
    0x2e8128124590000c2d1040d003805105030f42500a640003002d05014007144210310810900005520312403190381075940045030b804c8007100c2890080b030902c00c03d0a0711101d0900304080d011450301400030100f05107010781c4075029150750b101089401c0318404c41d0f0440c0c3e6820213400610040c4500300155080b440e0130b090010302d030354030b4003031544000e090300c200101115254074880f02640402c1c4002002000036000400d00f41c00c10500190110b503070703600540e040140f4401c00c1001c1d5502001091001500a400c3d9403c1c112424901300c0698030200b4882121540d08205007a826106e9800612034400d070130150420859083c44400160b0101e0341c0d9071742c140302c0c010141001c91003c0c0700900a01c215400b0000f00c0d0f2046103801003d541e95940b2914003501e13020b013100096110300f030301c0c107159070b64500d02a07a00c1c80ca0419403455200068200d1401072181091429603403200040c2081660041c14080280a0380d5000d42012180410303c01041c640061000c0340014000051113900110000c24081e032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 429312940 1250 429311690 429311719
    0x90a020702102f031305030a170d111902010506121e0304230312030402131d0a06060305010e0f071a0403022805010521090102070f0f11010305150906 66
    0x583c1100500002c0c030981000516000c0d0130518030f540030003440c050b009842ca14600742c07107104560840081b401d5001200040200d61032000342d01c6024206030800d1000d40720044040d8122240320b501d03140c140958030744400318480f868004124042041007400030f0020b0040c441851481c002c0b03500c07241001d84014000130444c40c01c00c041e400382000207000751403074424054040514040074081c100700b441e1010400e01c000b50304c0302c55294040f900f40101c00302e81c03404a52020401110341803900c040710f0080a06620401c060f0380c1101049a006000078089807481440c082e4480d800078084481c15070040404000c4100128003031410814a000c0803402d00c2e07a65004103031910000c0c1040700e0442c40c181d6074104c19007a42812180644428a0f1a41c14108040101c5e0358214444107030340d0103802d00000088800714250115090030b07500a40e41400c019003407a01d00b0b0110103800040f201e100740406200b02c0740d48248a154420182d915100d00903102e894217212070404041d00180e04480d1401d41200c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 429314190 1250 429312940 429313007
    0x1a1b07020411070606030803240604050d020d0b011e050603010b03160201060506030703140703050103031d0a1a1c0b03030405090403110601030b01060e0102010b03060718030c080c090a02070210 85
    0x400550165042c01d580f45041c00b840b070270209252002c441c081e08019800f44460300d90f40d06540c10b0311130036910784010f02018000900403086001c001407003040c40400108034481c482c54000014107030034110b42031954841041000500003405105c1e021f9506100040182c210306502000800560000280d40364540c4042401e580c011154100800d44580d0150310f6209a5409141c0c0148a85810807255045070f0f00200b00245100b0040869181d03485e8050581e6a5111900020942101c1c45155808148408911500100d45440d291000c080035000c43c10f6560050b0085444018083c0d0704e0142008100301081001800030380402c241d0034141680300000b007260038083c501409034402c4641c90a400100712002e003000090440e4148244054562030024200d80c0005407400e00012000718100f220040c421641d002603c1c811000e00009400c0102007101d6400381c0050781c04200325a07422010805900c40e13844002c1d008490007402d600d40700d1041c01180c0b494440d0140d2000c82c3c0001000c0305 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 429315440 1250 429314190 429314201
    0x3021e0313030905040b0d17040f030c0503011118060a0509090712060b07210c0c061812050303070f0203190809190308010608060d020a031a1b070204110706 69
    0x2800000c0c064800c000600d504190158014001190f052009946d0080403c0e00400315130b10041011403511207a00241c41120292405040d048810401181d601c6c101402e00f05802d00c40c3c00d010354680010300c15071200c002d040710803000840d14182440e51135082441002c0c2d1120011200b008428480c41185581c0ca001090180c1d800340d440044851103510141c04503625a401aa4020410010305002400e030b110680c103e0b403d078202000600f000244195080c00c8240780c0140f021101a0021540b03580181c80c0825002452082c5940c0a8803000001c00b5a4101c00c0060580e0340705100240c0316600c941d5940100c0001c89c0b054038109000c0ca42c000c03803d0110341076210041070781d60003080035005081056014003054200c5041440055807009888500103004030810003118000145058455243d51285c0c96800343c2580d0625a5030b05100c4400c11407040700002004898000c6891620044100f5031200804209607107000e040340e0070040286150045642c00460901000000c10050301c80d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 429316546 1106 429315440 429315451
    0x71d0604090206210f060112180204022704051302010f020f0a03171f060f0c0501050405010b0310020a09060503091c02101d0d03021e03 60
    0x1140140c030a2807030280d000200082c4007407032121201481d840740604280510b646031548017054011120554042e800151400d1030f40d8264181035000341285c4030117020712900e201340c03603000c2401c0e41c000f0034081030704040078150049203000781000d81243da001124200140e00c0c02c48010552900031141c040d042040700750301040e0b40d030f0003084480d4402c6202c82c00c5617001030321443c0003484031040c10102053310075560081200721602000a01208140d020310b8041103060810803103480b280700210300100680440100d01049007071080303070b0090707019500108592815030203142c50542d41c00d01a0700c5640c410441175030b506074429585026a00185005556611074a960602d82604203c1c2d041201902c1c9484004039a000903030280c544500c014148500100142820203581c0c01ca803040660740c02130180740d0b1070b01d84a94001c012141d604c80d041041d80c140040c01c6d488681080380d2 = true := by decide +kernel

theorem cover : BRFrame.Cov 429136690 429316546 := by
  have h0 := BRFrame.cov_init 429136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 429136690 ≤ n) (h2 : n < 429316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
