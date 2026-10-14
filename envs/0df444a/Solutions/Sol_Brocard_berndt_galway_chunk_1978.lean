-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1978
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:22:13.99627+00:00
-- url     : https://prove2.me/submissions/70a9d806-70c0-4eeb-bfff-04a38f81bac5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 355575539 ≤ n < 355755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 355576789 1250 355575539 355575547
    0x120b01051623031c1a0307030f05010f0c17071e050c060115020705190e100e090105070503011e0b04030804060206070207080d140706090b090f0708060c070305130e0615 74
    0x454203080701c00c0249004940ca80d165400e0328521743c0001c001602103c007905079041d503a680e04019000c13400e0300000740e840e54200383c1c0d1000b00140502c01c40f03040b200340780c8403400c00500d88444000701030700080c4001c0c1801010040320a007040c101a404564403125034486a90780080351500d4107112040c0c2c0403110b6003402101e000201038001c20400155001562243e004800300644205e502600354080240c440e80c280034003520707c1d4044140c0c2c05035076481000100c2c40d2140a07080c0d00322201101d4481c000b0300c003400180808140c0324040c1c0c40c84040d03518291072940d01e030701c150191503101c0e41c421251140f000604019050301480783c81d0f8000c1c500d00151410320b2030204040d0b00d42c05080364000410040b02008200800c1c29000d5604942d00003c0401c0024000d1411184400703050310502c880c0d210b0341c1c00c000103106001401101f61818040600001d880b0301404640941004404401344007060203505191841195528020b00c10710408007014244101484070742d420100f1251038a81c0100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 355578039 1250 355576789 355576807
    0x30b04090206031303090e07021c051201030204050a060509090708160b0d02030c041e180e07170a02090f16080c1b1029030c01120b0105162303 63
    0x28068a520401184136500b031404180ba0441341101d460700044959071205c3e0a0020113a400155929138440030041d030319032105803540c107507914014102c2045180302444011703c01814260021500304031b00c41d0300450025147e0001440b142411a03e400281d40540020802003908100c4001c1c010301c08280a0f464600b0710402e60a14425043d4440800390000b001c21500d00110045400501c2d58105852541d50200f8820780900031a1081909010a0365100e81c04030203644603000d0001c0902c4020400e5901e0415030508000402d51181440c0c014143e001d400740e00c501034554405c070304a641003400703454002c5640680c070309400daa02c000c200e02c0c44200120b01d00e400c411225111001545000c5d400101140d00b071074480d0304100161079a00780180c021119154803001d0880c8070300ba49114a81c00c4a003010306607104651080507000500d084013a0151801a07030000e9801d03038040c5000c3e0720300659601c44500d03558041200300c4003000905030f00c41c10666024401c45443c02810050361038201c02c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 355579289 1250 355578039 355578049
    0x120703031b0c030206150f0a0b070501290d020607020a08031b241302150c0705040212010b030703180c032901170f0607050703180e04061a09010b0a030b040902 70
    0xb400d0003110304061441b003000c0d9594105100c0c404400501c201c6107151102c0c1004201c2c1c100d01e104881a40c20407401461915048840602900d008445a2100c017040c004004c0484007140050760014003c00c0840050307260310500d41c000d89280d60065548690700b0312203800a180308482550146c001540308030f02c41422440380f10300c40e4120342c1054003a0704c40300b800c00c0c1c503906000303002540095462a0f5034030003d601c1024180c007c15600c10780d0300c0144c1e148288801c0e4840c4cd00301001102503c0d00611607000700502840d04501c80307141c0021080cac0401c9154134031080865003982c00e010800400c02c1005403100b01c0c04d000700d62440040142400c01c91341d800b82110103005116010310413039410b0020700c204221030100000d400048481a0502e5040034046500507402940081c0100030203281c64080d900240040b1102d594079001140d8441e1214401406c443c4407607800f40c04d03006a900d407942d84224840c1d0181c0048000140d03150b28007503002d4212040106028015410045800017694803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 355580539 1250 355579289 355579291
    0xe1006140f0d1a09090601230907200d05181903020f0d0203030423030706120207030903020d11130903050f1305120607080109020f071103120703031b0c030206 70
    0x688501203040310340c40036007002c5910f981030669042120a000c01200070b40008815040302c40c075103c85c040082030311814518130105e12064541101c416070200350700c1840361400e031071810304924010000d0024000c40300d082603046500d1100081c804184200380500d9014054503034002101e402d640d00724010040a284e06071440702a106552550104009407250b0404401c4140d00600b175941e0f9a84605092201039004034100907070422020001030b150070f000030708005071140390b01d4a049408140003403034040d500040040341040801d0000000507110540110074481c4140b504450f06255a024400076581d405010201d45003840c6081000c80c1d085401c0fa40000c4443c10126a152490010200700b49929402590400415103c041c6c01c5a804902c0c3c0b80111280d50b500e00c03490340d0307441d0171005a0041c00f603203a41c3c004041110200007681d034004420605000340031384605054030700079501d082e004184145c000c261201c005184603c411000032405a03481c0c14076a100541a8400030741ea014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 355581789 1250 355580539 355580557
    0x30306060c1109060103230a050a0903081b0d020309031c02130e0604020c1f1812120e0609100b030303090706050c1204060c030806010e010806010c0602040e1006140f 73
    0x403203002113205030b4440e42110030b407a03050404004041d0851111208010000c0f291070141626100100d04103d0050103071700011601a80c600142d038541a0811042010000c40710300030820401903100c44000c04c0c00598401c0c0d403820041d41e00c1d40b0300664010034000700e440c010508107204102580100701c8410302d035800d480c0c000d0000c00c6030b17556200c0490001c0c8511500c0407814458031222209a482041c0303074011086421000303020310b402e0030768401c074a0100c09500500c0c1040d00488604518425807400c1d4104060311000304440c918403410a0a2640a85000c3c409030451403090941e8495030194800c24041a0025843c500d4000c00355038035001540147e00c100040003800040c1e0390700030807201d1030b446049144c89542e555298405000c4c01c1017210101c2c080b8084500140300341d8010b1414403403441d4180c54125107541e909c001159a00031210003110403a900307000c04a40e60311741c070740c016101c2c43c10503100580301410480c0103041000c00c50040d84014008000d030300440d40c1804142e610390a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 355583039 1250 355581789 355581799
    0x90602030f0a1b0807020316050901090203090118060e120f0313030c08040e10150212090307080717070e010f0909110301020a09090b01030b0102031204050a02030d080103030306060c11 81
    0x945200021101c4080050040081d03124803280f400c1440f100c03600521602e0f100300d04031101130300340040481c080d0000d803180a40c813100310001040301d90b05a800455000b10804000100b1240c480081c070303d4401001c2c01610401c5e950b030811030b0118020030901d155007100b10091400d0080d0000f8046d903601c0020020b00109160b0b280c01d0007014024030742910041e40c005e01207074403030b5201e110524808038200c810701110b0303581040000c0e0312251400c1100044a0355805840c845000442c1b061440c0d01074000903425108030b0f00300095004090007140064415050341804146004100a24203c82608030035504c00107080100240200029001c0032500e80a0001c1030001039820401c0c0f1088041c0031b09600b42d400096000115540015000142c03003854008100e404214401103040710fa818031890b000d40d000700f021400c4510040e8005034080d02c203d0890b00401400c1e404642020400b1090001140316540107204041c0c2500440d00134026615108011601795160f1083c0034000c0074001e8051 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 355584289 1250 355583039 355583047
    0x90914160c12050306030c040c020a1101090f0b031501020309010c0f030c06050c0a02070f050a0605070807020d03020a03030f0903090501050c0c04110c0c06030c070206030a1806020316090602030f 86
    0x1a40260104800c480d0041c42c0c0340325103002000058404d900449800f03200f40140200c48100d880d05100c2c0402c0355406070f00401240d446c1e907803580f1080c4900b1075505d0506c400b0100c00110701200c0c0043e240a8020aa02140c980c01c012951402081d101c80c0c8145c10354100740020f5421b13991190146005a41052010ba908080c3c2d0500707a40c2d200c52171002500042c00c04041043e8500c2d038200030f00c415075040d402c071082103a5803014001d45400c3c90154a500500d014800c2001502c41c1007e001288d010700c440c903280c9134403030f40001c0903540035010840160708046800e2040c181c06100d00441300b194000c040c05880b2065030020405080c0340201810710501041d111603402d01003103080e03413a040180042002c0c504400c3e007003040ba00200720b08802b910614404241f28140b200070b59010f00404070145040103100d60800845805c02001c0e022072650301c1c000d44100c51000760140844038090000141d5900b0302c00c8403d420049446111828801070b08800c000060340003048a8040b503d6003a5a41c071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 355585539 1250 355584289 355584331
    0x30c07061d011b120905190f0204090f050f0d0503070c060b040203100e0f13031d040606020601290702010e060c030a03020409050106020613020402030603120403060c02150118020901032703090914 86
    0x1517003e02314000c1d402c50325103142141009403d1024148560155013141d8444980e46400c543d61041201000000703001400443c10720b500035180716103447d228000c00f18040c403c0782d000c05c0881e00126209548201b400008000d2101841e09042d001001048001110320703254a14803a14111010000d08010410740c0c8403400c111014060112040010070610040d5030762040259504000c2c0582d47c40fa007044407003607082103102d40c4595600046085042e00301049500151030110291415036003100e800c20010701710f07075400c1c0000d02c140784540d01c0050302d07182400603110071124160091419940300b88140b1010300a20309055003010b504440250760384d901c04010a0500e0a1403c07008803961001c2404020480c0c2904080c1c0210001c1c0c0c00c59800d00c0d0b07902c0ca030704d104250a11444040d921211603a401c40c9106400400d08143d043c14040344a8040d16285582e0400303500800b4040400d181800c1c080551100100c0c00600c2050705c03d01041d101c2010581c03000b003010300420b484c40120f8208081d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 355586789 1250 355585539 355585553
    0x140604080d18050d03080708060301060e010308090114040e041214121f06020a06050f07050d0903030b060a02031903051b031027060803030c07061d011b12090519 71
    0x20301030140064018445624006d0032a1005071189004200c4840000b11079090500c2904100c0c0c42040b4103400a91858031081000d40c4406003160422041850b9503800401d140001c100410390400c06c0403003440c080c01c004c2160b60300f0b0241e601c100f000d81651401410011700a8920000e05041e201c10541c90340300c04848400341c80881c0c103c0b03400481800190301d030740108404d0542401040f0511156907201010441030900b1961400810310a0207030107400b03007580d440100d40620a080001d080f91242000811a40004a040e801a0320000d00100003480c60021034041c000141000d100500b4003d440c00000c2543c0070310300480d628080000f5112461100340480145059042c1d42580f1000c2000580014084c008000003d401c0010014070118000110b80c0324840380024141000560798820018264a0824820001415031820382d042c00038883d503000d800c41c0303212110000300310300000351505250000d40c8071800d00d021601000f00c1c5003c50a0a21f0030300d200b40b05040107500380b0b4010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 355588039 1250 355586789 355586837
    0x603010204180209011e09050109140306040f0606080a080301090c02011506140f1605121206010c11030706020d03180c09020708070c1d010e090d110a06050f01140604080d 75
    0x1341b5101598001e00d5050380210300c034001c0d10800e903200e10310b09440d42030410580503c1c3d80c2c450342540c4640300040c0492040a11510070610514004c80c4a90391500054a000d00408043e2039441002004001600032403040c1c000d2008140024090540d10040d41c0d042180c661040a080c8440c0421006848a40000b100c080c8103900300f042c0d45030302d01e80c41551204020000101d5940c4220304d026042680c262042c1c030701107500b034181d184066a500004403240c0c00b41040496901c68003801690b002d680500210016001d20703802440c1800300e6020041c01d803508000800c400312444840d01c800b040054a140b01a1080d85102503a03850403031400740e0031072040e480c000d819688480b0000c00d04c42540d0b094110003503000c0c03400108590302d81600e040383e85425a400111741c1e0001001c002d50b01c0c0180c0d424103494442d28103035404a00583c990106a420484074002403509820051000c24006426050303a004103440083c1024182400c46584036801014a000d00a440304110b2600c0c107000511 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 355589289 1250 355588039 355588067
    0x1b0b03010f0510110c011d031b01121107061d030d1b0906050904110c1608010606020303071d0301060b0d0c030b060f0403060209030307080a0f08060301020418020901 73
    0x5594969584280168000e41400307524031030b401c801c0e05184410b11070b82040c001c0b49620000342c4400d01c07907080156440060004d1710a0341c3c26120b840c107034050742c0500c289101020100c41070845c10305a41c000414111010b030000002c03901c0c003220101c40d94880019240030b258040800034902407440314050748414034468103140e42c03200150b451504041500404100d001550a5070710502280d0426a0000c1580c0100301c00210184000d6101d840c050308204c5114484423482d034a0042900d03082400c01e110000f01000321124800104010b00c0300b44141c0005140e00e2020b1415802c1c401e030010031010450700080040c0c1c1e030035039002c042d0303a80030341c031180042c5100c00c0d03c291b55403c03406031000684807489910700880e10b4001003e4403402d04108903850038000c040200d2a007415030391040001d4205062003909803106000c424001910000181440312568484409100c55288020400c100080000340641d00500c4200304071803060050600310003200354007607244e154130b000481f4095004000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 355590539 1250 355589289 355589309
    0x20f0901060203071208010b03040303090204140a15090b332a010603050717011e050919120c15060608160e18071e080f060d0c031b 58
    0xa4070341d0000000d01e103152042c05100480601000180d507250300910810070300301c004000180020b4401c0c1d202d2210184010b00004400b80c07000082c0c0c4490408480c02c0311030310340e6041c0801002d480e405071800140508201846403980150120f00210100c1c409501c4541d18241030104404144e103e440358620065922502d5010307001003242145010b040044c41d081e0308022240300c490060007100305480c2c2140c0241503140c9010001c480b008101c0c0b041030b030a5585c589502c09040e026003105041489a44000b25050070300710241414100800030121408405240e000b000810002c21034900101a04040702c1d2041d040c00d00a0b1060b210fa000d00c030f032440c503110340031a032581c000403035a000340c5071072481e144a10130440050310403012221510394040c040301301d00e4803c101d0f0420880d6020f01245071030001c0610001258500c001e800300480e020400071010003000450741079480b940000102c800b0403000c3c0041d203170401003038024080a0320109400d11450042c41c00e583d100e00082020f0f5031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 355591789 1250 355590539 355590541
    0x2030f100906060602010506010c080310080f2107030e06070c0503010c08040b07020d020a0b0606090d080403060c08190b21011a03121602030c0a06030b01081b09010309020f09 77
    0x844000412100381c08449091502d00d002c5006441442042c3c400c0006844042c99203140d034640c602150401011010000754240001c1004c0c8810306c055110184201d0050081440f2480790000051189032901c0c0006014003440d00420f034010b023080c0900d0810745180da41d4090b01d080c04500e480303e80d00103a403d58280381d044009107900203c040e1040780694400c154a0b2140ba00c1242c0740d0144454650050384451410404581100041500400000c00b8589016008004540e50002c006410350700350002181c10030a001e01030180360540042844c00c00480e14161085100e4940c400445c034011664851110364507403208180d082152800c90300340700c49800510013840c040d290b40d85001880c42207079404100300b8100010410300128110209505108250221414101e20000d0585c0c2c188580c8580d12100c1e210282080090001c075540070810310002c00c0003400c01200904103002c450f0307900501c1000d1514440940d1610b05091034086100303009800000c5504500341c0c110795010903198 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 355593039 1250 355591789 355591813
    0x3050316020c030d0f0c02060307084204060510120e0307080f03070c0c0b210c070b04051f0b01030c0c050d0e0d060c05030103050d03151202030f010f020d060e011d0402030f 76
    0x20112611800402c1039100b81c0045e0b945405000504151041c80001d94059203190033390651000b0322050400900006a101d607550000352040500c8180075021503044010342d88000198050300c52800107045c003e5240041035610000540300e0b03180121070500c0c0110104041611803d80e0b80300d0150400d661011003a203501d003018555000b06010031081d004000c168030b0184c241c030b074454450b005004100d8100501c5440e18410450002c0007141c66020f05040c02e050403840300c603541c0011040c10800a440c468550014080312620411a018041320704950300005030001240d081b148050314000008a00d48008186800300d0f0920051481c1c0c2401a50b07140598048007443c1280d0003081117950790301da018415801c075a190142c1d1244140d501d041401020b802409012540f84007400f00e42502d83e41c42445400c445540c549408080e03000113401e0a519120300902d801313403003214611030940d490200b24156505500415a030b61045c020001420340d40e0038002414400c14940075500202801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 355594289 1250 355593039 355593047
    0x3071101060b0405120f0f1f051e06120604050c1008060a0b161a040b10030809040209061c0617011a040510030b01031506090203040b18010b030a03050316020c030d0f0c02060307 78
    0x100c01c1588458286802c0b03098140511700415000351445400f2b807408034160712044507880301c010030b0150082c10038403084c2d00c00e1408208062266000768003408001e0f182404000c41900d22900e42c01c00c0008580a1242b00d6551086440880700e81d040006d5541d0f035007440d0400c8490301c0c01f4010380101c1081003c040d07114092401188500d01c154906413955580c90b82ca4000d8060a00020b0714603201402507001c2824954020141210001d2204d41442d00800354a9a01ca043c6800d0310b0401d80c540e07500704a81d100c0803602c070302ca00a4041c020b11a01070341100c0664a00c6a0000e040e20842e20b800c0403070541004490300c0c83c040c0d500b040071131240750f8480c18115040070100340c606050b549407039000102807099100b900e000f15400090400c2d15200d64030603940f10042c108120109541e5803201c0d502664040002284c0c552180e1907040e1030349024100d142c40c140e1042c2c40306055410003204141d01e076070003203503640c00c201c1c071400c00c24020740295400700c4451282c1c5070000d40200780081880822504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 355595539 1250 355594289 355594303
    0xb09161b0c0305060f100b0f040902030a1a01050307020d0c02150304030f080705090108010303030504020f060409091403040302010f081f060e03010c0f091403011503060203071101060b0405120f0f 86
    0x5107048401a80311820440d1217002e0841c1c2c000740381500d080090109540807001021100281840306040c191110600030482e44203440784540580d8400c0c40d032007000107102207681e0103042400c207030b8210b2408000c040c2d12400b640b0012010040781c030a40004640d60b0101403011429481481500c0c0d10307080c80c015000341c43c001c0e02200814418800241c81510510444a014606139650407543c0d1a603982070700038000c0940104d07880040d404d5800540d481c0c0c003020700300414000303401261964a0327082440c140001507504101f04d800030081440940d800c907000300c00441c081e10f4650491f075101520400c0700740f68081d0340901310075991000070780710368011610000f00304110f00820926841d00000d8034000750384118107010a840140030040c1c0040181c1c280c0bc020000740011607140c0d900d0910b800085c0c1c85401c00c45440d540802401040c0c1e5015065040c9018201c0080002c5402e03c400341c9010700951007401d03c201d1401039240f4102c0c1080c08190511409041162440002404419150b41c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 355596789 1250 355595539 355595543
    0x1005030112050a0501090c08072916051b0103060f1223010227040203040c0608091002130603050105090702031e0c0f0d0f020d09030210090b0d0905060a0b09161b0c03 73
    0x20801c1008540d0003210810a49280102100d2b0000101000084101c0d03401181c0c401201c0c207940000340000c10b005000704c81003e6601c07510325422007007080002d0100e4415801c04803803421055030900c517032240804540c0020303030070402d030001287e0180b00544060303800c4a490170855001040d0600c07011020800968100e04141c0b050407600d1500003400200d000444014001111101d000c01c0f0042c0542041500403042c1401d6801c445602c02041c0180e0b40f00c5044811602c600750801c01c14503034107110395405040e00311040302084c04c264000a40e40d000c0c0750383c041c0d65a080c140401c95104018003c0343c0c40f0291406c10340300d5801da104ca545440301e9040204c0004a4011300b04422524030220fa405a0040a902d03640506400c40d001d228005102812a01c14054030300804100301d0300002c0500720b11340f488040840c03103075054a040360030410050540103c95040040801c0103682c1d0040c403c4d0300910003684200e117100061800c0301c0f18403600d0005001851001c044006101c0c11100c3c00303054078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 355598039 1250 355596789 355596793
    0x71509030311160201080702031b0726060103110a0504060803030420181b03100305070807061d130f0b030f0d02070e090c040c0c0506061005030112050a0501090c08 72
    0x44407942c0c2121880c414840c00c03480a0b0100800040198000c6803002d42250551045034106184202e00d0f2000e5080010003e8450340105000c100f41100c4801c00d80d00c110003000c001c1c40305041441080d5a07420180170040590026003c01e020903160741c5101001401c00603c1407100e42d644015540e101c3c0d00580d0155140180d80710803a4601c14408520070300075001805503118403900203218600d822000e0680d000c10490060301003400f1841c58003440c02410b01d01e0030120303032a1551071311510340025540011020340008030304014040d0065242d1158824a190341d48000c100e01e4001034400000c3d1403030592091420041c500c040175141c0c006e00707004d1001d9044400e280007101201d0b50b078090011a010040c2e010a5050060a020b03010b05034004001d4000c95544400c0d20300041c3c01d13649130b110000002103081594205005d81003004541241d01660003150040809034000c18900c814000c80d001da20b50700d0305040801c501003003072100082d0014000c00171150180b03881a02c040c0b103480740d986c0034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 355599289 1250 355598039 355598051
    0xc12030f07030504020a0504090f050a14070e01030c050103180b01090f0b0a1503020c03120108061b0306010f031e0f2004060c0201120605030d02010c02120913050c0715090303 77
    0x1e4080e00c10030b40115001070880007002e1a00b000c010251080440c12103941581005450010300100300c81404244540040080c03c1d06150b4a00d01d030106c0c80c0c0c00710700400d501c00700420201d0131828082082c2e03034003881c01085506d040c04e10f6020350392007440000d00200f401d000014407441250301918240000c1441801203001c3c40c820800303900d059008041c281403025214120490080e0700404030805048181d80c18a018116a40b0803100264041132460700040304000380c502401c0d005002d0345000383d0006045040a0000a01c0385460244040078150b4404a9011400c9107012044034015140814415400320000d9000a400343c403954108040300c810783c0c2c0d54a085404107441c20b8903c03641d41d140750340689400458890a0764800780104035a00c1c1008a1a9101444801c0b6001c4003600086420185102c00a01d0600c841c03000d0720240100f417244200c141e0790001c160700c3c0401444004605030f00e80000300380e500d20403810010240e505035000400c40e031031542c0100080b580240c03000c00031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 355600539 1250 355599289 355599301
    0xb0a051002060609070c0f030e040c05161202120f0d151a030a02040b040e150108060a090e030c0601030c090501080c09160c05120d0b1203030c0d020c12030f 69
    0x310009140d841400350304030200040141c10001e81c1d445e8070000781c1c039168108042603101d002100f840b10304242e00051380c480c1c0070201400d09000e040b28400c0f681c64a1840c0c880d0321064180c50308089100100789055070894941220300c00c000c4608502c40c0b441c1842d9507101400440c80c855480750911142550400e82030b84101c0b1031081081d4212401c8220310104000701144002d207580c4000d01d80510b40b03600f800046842050400540044c041c1d10001e05500e040092140481481c03000741d15041042e203608000e0030f91685c8942c1b404030b07001844d022075403811040342d9a0841c02050304040d0948500e000000502080e92400d00803035100d85410805641c0304d46e01142c466080756452600b02030100c002c41d040303004400c1c4010800626182050080a06d661800c1c1004a101412424540080784201c51071885120320f0203408011240c440041000a50b111f440740002000c1c10354070417021030341e1006c0c1d44154049410007240642981d59446011074810925001500c51680c00d005400c00140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 355601789 1250 355600539 355600549
    0x10b0a0f0812030403030207061811090c0a030e0c04090b060109061b0f05031201091e02071104240909031e17060a0f03080403030806090708011e03050f010b0a05 71
    0x58912100140124040000321410b150703001030030407000c0550801c180004105203200b5240d501021050300f000c2c80c041c0b400d0081c01c009440400c14455400041400400c41c4600215030b5001c0c0c140c14041240150724184a042c030004e0301013541c120381480782c2c071001c0004509405124000980b281d04070035440c0c1c1d200300c640f00d15080301d440e03240c00c0c0c041805005c038044001d03002209100b40b0880e490811100401c081d900360a82c025154145c690070203800425140a41d4150300e440100c046080030707050f407100c0c4200d0b41c1030000b680c011944c40c41104000090700104001c0303c0d07190741c40c4c400d10341d82e5000a2802004500001c0e4000741070805000c1d48180b0184c41c26941c84d0540e51039201c1925010107407034084901030405075000c084500009058202d0780c001c880198010144185c44610303609000e0305542c0d0041540c1d2240b0405020043c003a0342010b14541540c100c1c1d01320100d40f8103548a00b90b0340310b01540000d4031610036500442500c010541101c100142d0076140301ca54180d4030401d201c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 355603039 1250 355601789 355601819
    0x180c111902010e12010f0e120a021506030106051002150604050c091306090c05041a0a081302030309210705030d0c0311030915220b04060c051509010b0a 67
    0xe00d648248840d84005036204450040d411040100006100d443c114451030855000d840040c60320f54440c0346c1f0f076040300003c1c003008000d40c1e80e0500071444c1c0314152400a45513803070000d01d4404900241c000ca00b0301d450950203680603003005461800c4405542c080690344991a040072400c41d5a0080090418103180c000c01d030203411a049902e00300f01041081000d03084020403c001c0c0f040e0384407000581d07105a401078000d0030003e511401c0d982e5003440042448810180c0b232441780800204205000980d005050a501404138100485990100e20020741940b00f400d0f00c00364004104140b62040c04483d0740848a03000e1a0300440d84640ea0350303014141c0300e102c4040c80d500031990340491400864054800d40d1403840c4c01c081503a280641c402d000400c940038842030400c0986d404240720818405c5254080c880071060314160400c540340c1161034040744620b0042a040088084110003008020041000701c5c085c1ca80e001c84281c13800da071009009243e424200791003a1680440007076007000c581a00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 355604289 1250 355603039 355603063
    0x1e0e030301180c1202090d17090a14090402060a05040b040303050909090c0f0f01031104030b09060c0c0a120c021305060109050603040c060f02070f180615020d0f0504180c11 76
    0x7201c42e905114010800a40000c40c1407a00140c2047c92a400517464000703054404070044102629410120240442074031a03403c07020001c90601200d074115507600310515070040d0b04880a560710052100101d9050190b41d21880d0748680c0803502004040e00a0058034021000751001c581e10b6540e010704943d00c0801940f0b40c0d4000e050440c03420350b80d04212a0130001c5800604000c2100c100003019241e081d44107a20650710208120700b0302c10395090902050360031826050342c0604041640002645034140c0880040918402245096540b8007550011840c0c075002400c28a03081e080c0c1100001501040b550b081c00511540b00118007840c200c819240110342125004050303d0a0500c03d4440e0b060b0b20100b00254802c020780080c10280010540c0301404884103041002c03141d403150032041c1c2e201d540102d0440310072907c0342c000481c0e0004031500e0f411440d29118007a0907103103005540134456904024a00d0300009202a4a24945e40101c142c1c4011681c1c1c031039000040d25051a102d2641d0408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 355605539 1250 355604289 355604297
    0xc0f06110109151a060f0d0b010207080706080403031404050705091b0904020a0903021f02060c070305180f040e06010312091d0a021902211801031e0e030301180c 71
    0x11880d946400c1e50040000300f01ca454042848120b01380000c14a4003d8a00d403609072000150300d071a80100c501445441040030f00007029028209400e1a403551441d0003038030704010360107002406040c42500f00c528001080072030780d0b000c0e0030300c0c0c02c0864841c4154041c01c0c0c05406801d0200d44c0315042c6e50764500d42908100348450820824004210280d44001002e504100c000740d004030140c2c0c0c070640d201002e080c025406180181c9000406814414000d15a1a1010b0700388800d10201c1e80040441c0c009a01c44803019170360308000d01c000f801d220800989035820502d0207181410b91000000d00038140e80c0524071050440206100442d10716201d801151074944d99851944140d8141c0c405160308110540400b40c207142c4038a0200034241c0c15842c00b034006030302410202c0c0e030380c103840c240c0d100f0f11402e900007007450030509208440c0f54030000300c0414105580c40000103038058814a1034200c000700c0510030700244040001d09075032508203024224118075510002c80d1259035610920640e02d0746070322 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 355606789 1250 355605539 355605563
    0x1404140f0c13140f1503010507050f16050303090114060307060e090c071e020f01020105041e020d05240114030a06020304060902030601060906020c030102071a0705070c0f06110109 79
    0x2c0c0702d40100303808602c0a1481e01d0710b203046003160081d4002841441c03a040b540c0081d00d060030400c8030540c1008881402a4500310510030803940c007404580002c920038200640d00c161280c000524404e5000003d481800040184504010103420040d02c10002c91107007001c5031240410140c03202d246104460108403080e0740c0d400b003818a80c00142d80034072009909404c1440302e4540310808514a8803010305d03100c0610803002185008440c080943d5400c3c4001c0000307103031550798403964a805124020040c40c0c1300400204664078075000c0409c841d4008141d502c7c00e07500c02d01210b5030144688202001c240a0b800225203000507041c82d00014a000300144501400b0343c945400030352001e0000d640c1c803611040480c0c05030710200540b074001c01e010795540c03900320328010000b8140380125034441c2c800d9004100460205402d020082424a1214500700f12500c6008054815100381c240080c0302c1300b4202c0e400112103000700418011901c50b601d41c00c0702c1048100d6054222200c00d180108031400c03200c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 355608039 1250 355606789 355606813
    0xd2001090f0b0415020327090708070905090c0904020f0408060f09060a0c0909090308070306140306151906020a0209070f08160e060414040608070f06211404140f 71
    0x750f135600002c00d005592034054041003000b02140c1410b211500f484003100c8801c454200313a0401c550004003842d01c04c049082c0000c00800542e814468a0702c59001c0d40701081010030080125560541c000340308541e03801a4600041164002c0d20581080b0300800c00043c01c010302540381a8403a5004c00d0241c44640c2e1002c01c3c42d4010480c000c03000003004202c62000c02c0408644c45a81e00c128060740710306155140c120341c02000d5641c0c54110003e80d0a80c4125600c45413000144030703030801d0005640c0c1c501d080c0a035002c2210182801824048602600000214140c01140b030b003080324000c0d036080000b565071401c1950100e00c10240c000004800f2000100300d807465104e0344000300c01d1407400000751001000025000d40080d040202c08010a01c01c9290702e141902c1050700a15110001c9e041e90f51900c9448442168544112030500178403070b8400074807c41e101d100d80118030902004219510401c2d0300c600f02210115400c4031803001540070400346840000b03241200615040c028100c4084030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 355609289 1250 355608039 355608059
    0x509030a0507050703021c0c0504020a0c08090609091305010e03070b060d0219060215090a030504060804110613030201030e0114011707030b0a0203091605030c09060d2001090f0b04 79
    0x810341070b20b83e07005640b400310059813484c514610f1002403408611000c0207500341074074644060fa2145200d984104280203103543c01050311001d031500b00307110b0381e150088040414014890480f016501c804110104000d040704100ea00400c81d0142c07008200042014a081eaa28440c400c009030171050158001955407a0598061403d00d10140070b01d034040c0b442441e0044010700e240c01c0200560024a07542003403185810804d0f5101e40d00c000148220001e40d1806025480799000700da040140600000b818040d05184c500403b0740041c01d0749690782d10380c0041540402c0c8030300040740001d0802e940d142c8018014081d40d0aa00503513014106940d203840a0116440030351101c600541c098504000041070b036800c40a4400c021801c1c0160703407031411000c800d0a0401c40070070a10403076501c140034420307030314001904490260142c075441000d88541000609814030100024101c280e440f4810095202080013a100e1660a803105144103440d10720041d950049030207400350580080c03008006105003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 355610539 1250 355609289 355609297
    0xa11040905010207050105040308011a0306060d050c041208120c0c1b0f0414100506130510030b030d020106090e01090506041e1b080607080106020d030f11120a0507030509030a05 78
    0x7254000515090041c2c0d40c031800c0d01c2c411101640441c04020040200c40700b00f0980e11286242202d040345140340c2100020920b00400206104050b59800001e980c1c0701d08138102c40103004a000101508202441c280d1801e078400924510001c6460b00415039003040c0ea016594085205006030a04c0c412020144000d8030403100f0b440e600c0018202c0a91290f115031144d001441c040ba03075500c10524001485141c40c159a52104d03001d61020800c4000c0030480006040a0b00e07021100030041d04502d68040b40a06240ca10361545070060030307420342007c0c1d01544010200d4000305000c2c04480700048180c1d080340c69100004c1c03c80d03045040040e0004980202a0300400c999104000040d1041d440b0740003100c61900d092000e100d580541408040800c211072507020f078061900505641c14154002e4070341000c230180c3e40506403104622044480c8907009100c0d549035940205440c1d00b120030740342c80840d009603481c0c1929031911002c40c828502c02d0052612070f04010b001145032250b4030500715001c0e40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 355611789 1250 355610539 355610543
    0xd0602030a11070519260706050c07021f090f060314010906080a0f02040204080609030d050f06011b140102030901060609080105070507030813050106120203160e0a022d0a09080a110409 81
    0x101040c1080301148858640203140ea06c07440c82d9110b08181c80c2880441302c0280c8640d01411041c000c0380016a5040c0303800007001003060110920716003c01050310201c0e01900f00e40c116501a040105855030705600ca41c84d40c545900f43d130162640d0741c0c4460000c40340319010310f0301c540c0c0010809030041601180581015071014000614103079581704000e0070003c080d039404600d274000292410324405980241354110b00721f110b101c075180c2030035000a4214098890f001080c1c142080078038040c090007034441800030399014020b6540307144c07504c8118000c04090203440f0106020103030100340f144051243c6849211243c582610f0300102d0f403000e40d40500c0c010003a81c0c100c0205200807000510a00828004001f01c40088014003403603c1014103101e80c1906804451681050400084008000b4590010942400165280354004c880d640b2010503054409a840c510032010002d455944014140200c6564440300b404d9180c044c4182c903644100d101804440d00540201007914143d0721000c1c110b4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 355613039 1250 355611789 355611803
    0x100803040b0a090807091b0e06090405090102070507091508031e0304080408121e0a0e0906210f0105160807030209041b080a0501080f0a110f0d0602030a11070519 71
    0x144c0d1426520305d0036055403c40707104c550300c40c030a1704500e0814115000f144880ea0500a10158545010601c18091300300b01c144180d848401043c3d160200b941282c2d0b690b5000780a656000307071101101000381041c80078058444204200004901a002c020740362000c000d03082c1d8101140502d001c240300c5070006403064680b4102080002020041040fa5485c1d42e0700490400d51990145440c4d220551062141c2540900b0200b200c0030450750321148060224208640454003510740e01c011642809281c0c40d10302d810318480c000007402031390008894150b21845002407255031b6440c1102d66a0ad0045682c050201c1c800c800841e404500036000341c90a1440544009010200205825514641031a41c034002c54221818003010000c10702985001d0305e41080280075541814030341c1c52b940d12400d4070103024451490035030384041d0703a442100340c2c0c8904004c004074050b40903410900000e500035240504450b00c0c101c5448a03c046a00c140e41e00107801002924134204042400c4460380001c2c00120307291 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 355614289 1250 355613039 355613057
    0xe0f15010c11150c0f070f0504020903030307030f0f0e0a1209080a1415010909020a080601080c04090c030221070911091003200a111207021c061112100803040b0a 71
    0x3e130010041002803d92000013001e8091410408900700c0c40c00b034001da4003403070041010f01120785000040b650071031a00d00c2c000440e50014a850b00c010715581003502c002c0360602c2612500302d8000140c204049000304101e555207501d203002641c001c40355200385581ca4002e141c0c0b280105880d803c02d0458541d002c010f9400702c1e9240844104c003054260041d403241075841b500441542804040e0002070442d00000f44410f5042030702440e238900581b0342c064416070311604441d0030442c0000000c001036501808004092409020410b1b448040d00541116413040440024000b0400d005004c01c0c9041c1040007803914205009000f2000c0b01c100081d0f05063301c0d00303040010f00a486034882c54841000e04155240e04002c0002040160724105403546603106c001e503110602c40083c219174400383d0440e003800c501204814900003045140e90301800c8149045803004004404800404058980c02c50048141c2d644891244422120740207403400341e401440140102c0364080018036000341d85052003128 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 355615539 1250 355614289 355614307
    0x4032303070f03080f100e0c070c090e0c011b21030e06010b040602071703030a0207050a050a080d0b060a020d05031509190513031b020a0e0f15010c1115 67
    0x7a010441c0100c1c00110054100202119122045ca070849000c1440e49141440c0040540301000040c012040800c030000d43c0204011620f0107010080482800a10803030603a4000151502c9030305500da130101e9441c0305501c080012522008809903805403011a9003a80044484d224440c4030000009061b038030303189001012801c000355030080c0386140900daa21400c04100a007080b0706684501940440e00102440302140402030301d5100c0d160520050b01d52600e810310034900320b914600030700b140c000c4110000510080e44020312000c81e085100b07118814180b4140301c014410601c2c8400160401241c90a0443c450002907401071041d01c0260003240c0c0c04c3c1c0002e9000d080644090884000c04a148080800a4064a1380c025241d504110300d0f002030b84c40c054009048201e03a06002614250808115562440c0e001f01400c521081043d2502d401d08035070041080544803202000c800c0c024041e010b40c8181c09100802da0f202400d1400150547c0500110300100080d10102078402e01999007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 355616789 1250 355615539 355615553
    0x3070804020a05061c0b0a060801030f0609080a0c1a06100e150f031009050907090c090918050106050f010e0405040212010c05250c030b0a090204020a050406020c060403230307 77
    0x5c0030078150b140c9403022090410301402c03070b81000340c480e002d00d02654040084e25042101c0c41d04494011203010309100c8a8a40013004080070343e001044100c021030100b480c640c1c40400740c84101c1c4a11503181c2c1e2128640e00722881c0c401e04460240d07010f241c8200d11039095206240381a002c1703d000d00001031110b4000d01c040d0141d00841c0c2501e040074008010421f58140342d03c261030040090140400c100d0170000031300c82c1c0702d4119004441c85c154561a6558406114529500003030080d0036040000400f25614100d8903400c080c8140c9803503080000204052412448403c5d058005031620241c81c05440240000350100420a981c0240400c031500d108010a00456034030000c2640e030380e680c40003100c5403025070840f2040040100325510400c400005d4000305100f00f43c1e1342001c80c0e05a16a5041001c0001c0c01040348022f410134000b19014071b019070804040d00030b480154080e2100044a541800700b1800b8500c406800f00041a01c000c40c5122540000107002280005a9190030525202c183c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 355618039 1250 355616789 355616797
    0x210602041202010e09090c092e03141c0f0201060b12040b0a06060c022803150605190303050f04030606180e0a0302100e03040e090d080c0c0303070804020a0506 70
    0x494020301d51100344115a80403003806191070040707503e03540e5070a1100600d5030741d0b003035855000e025825440100e861749403240c5181c400820034001ca9086200543d0951541d00d000b03100498808840c10f044040c910404a4000000b80700d540703120740b0014214004450210484026405555076407501060310b034194402462801c1040d0407611003406c080c58444000b500c02401c40c2c10481c07802000707114a5a0051200c08003e404130340c518031400300c1002c44107000b000b0355140f01b044c2e00f030807400104004400c98018401e802410041000d155140c00b0300c4000361002a6404a10200400070700000c2d00a40c0034000303035080380340388500f400d44990341c110441e200703030300042c207440015a543d009000081c003a412840c0303810000313001403200d0f6a070040d40e500301c03041413060030f1500c551840800302d03802c105560090644000f0f051080c1130001c603964640c1040c00b1240005000b030400566180c0b402c604840844852200540c550380d41c4003011a041203000d07008a0740708041000001d801c0d95484050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 355619289 1250 355618039 355618049
    0x5130f080a1101020a1502030411030a0b04030305180709021e03040f0b0a1e0f020d1d0f0a150c03090206040b0309061510030e01090b160f0203070b0121060204 70
    0x40111106508004907008a91200349046500c85c42903c00020341109610101c0d1850078000350712a1510300c1c08044584c010200640c0501ca409400300920a950500e103005d940aa04d04100c242c50304103411044a4000e8a074803c10340c0494020032842001d40d000f03040c0503071181d2281c0824200c1d81e010511650055900f9079250100e00301c0c08003030002c1c0d495010781050548400300700703652001015421511101d44854001e40d41d580040a5411854045030002d80020b50100704140705c3e241c0110100303800340c10074407032071050b07400d500803034100091a480b015802c80100000324024000f02c00141c4050102c544c10540c884003400016240d0728085d02c0544a00e409441c0c480c03400782d00c2649008030042c1040c144020b41042d030307031040d141d031250200c44a20b40d1501184030590f403800240540204880100807295039410040201c202d1160414001c9440c1d45520078064a514207d0b070364001d44002402780c0700c0303030801000042c42005c040141c400041c3c051741040b800340e171202022600f05a000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 355620539 1250 355619289 355619293
    0x9030d0818060f1909050102031915060c08070f0507030c031e021c0602041e080d0816030903120c050405210d030528020d0f140705130f08 61
    0x5004010320200310100546030780200070802da10f0481c0044902c0000a044510000264030008990394410b8101021554120b4002c1d90750b420195440c017600c500b90030024021a2400c80d034000320314560301ea1607048a41d0b40e80c402681d204141c0b00e40c000341d449900d0480d6051030b4452414000b887c2400281c0003035010b4007501d00c1c95840c6040c407065aa07030100381c101050300c0441071140140e44011484601080c80818507142c10b240780740c50303002403045030800740c03843c54503270241c0941646815901c410f032900e410a40705181d80e00d10055a5032081628035038201040441d0101e0f01601ca84d104d030007418040c4c5072441641d42421003203c00c0700d82d60304c280c8000600000d400d1095041000c0c80d103003903042d00d1140c150340200e01604c481d1190031070161f10f4201070320b0301d000c5061006030000700080c0d5403008102901d121440c0c42410025803100d03080c08841400c04104c02c4d01c2c24124410007103940811140a0860307a100a02141c4541c17114010343c1c12085146c80204094940d4241349002d0149400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 355621789 1250 355620539 355620541
    0x1c08071b180212071701060503070908070b09040b03061302060a09030816020307080d080115200a050613050a020f1c202d01030212090a0303060e1608090309030d08 72
    0x2010000000044c540d0b41403281000c0c0740700c0c905000b200520304451300c52130500d1f101d4035020360865441d00b1030741c0565504e110b000380109110541c4401441c440b90200c0d020020602400c2c1031540394942260004012074211040c0009420854001c2210b141d45140c1260445e03206e654500190b0040d40da0b07003541da00008404004c50904004000140c40c2c3c150080401020109006140c00014080e88004007001120043c0d0399020b09424880c0f020a050311404c0c00d081004c0c01c66072581c0c02c49040e40c40b4032651010034100c182100f01081100c0c0c200001c1c10114155800f1303c000140007c0c4007641041e0680e0b0b0040340c2c51150950b075803800e4400c0403000c0b080c1e9145400400c515001030100b07032081030650310360142e00130361401360703a00c2c02e075aa1903100b003060213400160002d0040150095103144a441001074400300400c001c64901e1007510100209500c03a0000488400b04031444243c40702d004c000d00c0080c50061402940c415407081c05c80c1c0c0341c0504003000c28100900710040e00c020800f418 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 355623039 1250 355621789 355621807
    0x60203091005010506090d02030f15070329010e13050921090109030321091a070c0c09020d060801090602040806160c02010c080c0d0e1c08071b1802 65
    0x31020401e119540d0800380510750401c000111903120b02840d07148150322054160045441c14842036260194403402d690056000150b83da00c40c80d4100c42100c00a894181c0d5007004441c588407100320042190005002d002c0c1000054401c1d020301010550b00c03450307801144410007810b0140f503120341d4164010b032008060a1020401c0c0e5051500d5040c005c5100703003c040c0007030742d000e40303040226038042c03030684125000e061403030281c816040f030300184240c14151032030140070074007440100003c1c92054800c1d007591201c000319840025200010484000b042d0b040205201070780103480d1a0080041c0010125514990103013190030344141160644d4010504204510051100a91002c00020420801c1460040080c91103580351402414040e0701c51011050020f944180c0300d02d0b800301800c0300c41c54141c180c006001051590300c3c0c0d0340f00c2c10b40d0b410b60150001840741005603461740419000d0030055107030340c0c48500d00d040514404a04c001c441e000200600c40c564241e2a86291200043e80c8d96914 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 355624289 1250 355623039 355623043
    0x302121519140628150c0b090c090a110c01020d0c09052b1e03080108120a170402030c030607050a0905060a0c060b0103061a0c071706041101050906040306020309 71
    0xa5600084242107400c01c10000d40c903540080303000a01c0f01e200e4101074050081e581450243c15801c010814141034442404194200d8403600055000e40b841f000103680c0c0e41c501725550090b0180490300500c50001145154140d0f0304a801a6034190a03814240310001040500320f812607603150354074944030801203c500f50880440c0000d002c040d5002d400d00c00201402090b40c1a40920740d400f02000e011003130041c410900104100b03604807038500034012200d41001422143c080c001c000d414010180c0d69692807200408940b2003004940b00d081c03240310988203010382014001d2041c0c0c2c01d401640c44e5050250350500015220301c04940b0f581d6100c40311603074014681217154000d14041c040800082d1422070700040b2484545a00060200e071401705000100d01a15a41d44420401d119040401517080700106c003802c08641c2ca8011903002a54602d482c000754450702028440941280000c5404158a180680031510040c14007c3c0b0700400e50340440da42303034000d90043d5541035002c810b00208a4007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 355625539 1250 355624289 355624301
    0x4030908030d09061b05070b06010909050a0c020f0303090c0904020a0506041d01050103020412060c14030a09050111030f07080c040f0b04030629060c0c0307030b0402010906080f010302121519 84
    0x402d86507560031170800006e052480349400191562485100003102a0320503010724010344100e12051156041072000c410160103160700b00d5000d40070320075100035a400004145c910a1002c04000e04000e0f50300c90502002c010003610607a00f04a000e280803843d41c40310300041c801040d07200708c95503003501e89031204e0340c0341c90068004604141c01084108038005044034104401c3e50411000100c12203000c4d02036a600c07a00400c00c1d544a0350102c2040090001c6601a0303020387c2c0140c00901c140251510070540900c8110344a881d5484001d000c100000e1140740095800030382c03c68814503107070f1148011144102182d01030000380341d0004060041001d0b80c02480c1540400c011040d210901c040081e66002107015001802561301140001030b1403410840215800801740540303998a459042c540c00200c0e00720b8080c2c0c0420f10561001420768401c940d413a20418201076003900d1070342075908100340ca94001401c10f405105182000e8810342000e1110750003000c034500c41e24050700700c5032212010380b81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 355626789 1250 355625539 355625561
    0x201080c070507170109020409050606190302060a0813080d05070e0414070305090c09191b08130f020414040b010b0906030a0f14070c0b0a18060504030908030d0906 72
    0x40c041c400e01000600016103d000c0d42d0300000e040a280c295004000d00601707607100c01940c000e003021005400d01001089450141d20165160b16604040182905203c07070300d880700a401800400050650754865812150841540d0b41d00388503414142c0c507182100d401c41c12091600c5542c070403e01880d640c10941d035941c060000d440a000341c0600c100c2c0826944401842030045c161100300241711214103010300c5186090041c15502c05003085800c10b071851003107900a00800f0b1070820f00c840ea0051200034528041d08656070340768559170320381030300c170805c803c8102c01c842207403a40e041d60300140c0c4c2e035014801946407081c0340e1001900c0c0a00b8041244101a400032a480034100025180fa45030394046980c8000141000f144244020170458001c299100103005401c00c040d0600ca05960300c0400124100d00801c81201940c55004150040340c139450f039603008030034170080751200040700380e0803541d4001d000c0d00300301d0401907541c0b000e2411503201c00b404005050359804d030001040b900d48545640d0070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 355628039 1250 355626789 355626811
    0xc1407091d0c10090f0609080f07030c030303090c030210081504021303030e03030403050d0c050c0402042111130b01030509010b010903150b030703060b040507020604110402070201110609030304020108 88
    0x1207072104000d5200c201c0b0988a034081e40d10340d02c85840d01030140a59200400b4004ea9540b5400d41d10b000040c031111a5000720f080a003d40d01000008200015180065980106072040c1403403071658243e006180360401202c02c0d1600d2840000581c1d13480c002941112081e45882c42ca41c13802c100c4002c0240030040d070040c0300d01d1050010203960b40683c64800152036240c1002c0303080e4180e007000a032860142d030388010424450b0754040c203034169111a1510381e540c42401182d882c5001201000164041c901500070212840280c42e5101e04c0c2201310030603100c0c040c101c0f0414810610003c0f40c003055400d0800352189880d440e20742800c0d42d141c4206a8003071b010200800410000b003000801400c00e40c440581031a140c15003542804006600c8014401c6000f4100da014958918002c4090140c81c5500c9118525040001c0c4010340040b80f0360f803003a9403140070800a0000310040200941022030b0076410803600003c198845231080103040d00809d012001940c86c1e20b05480014410740c40108182090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 355629289 1250 355628039 355628081
    0x12110a080717040809060901020c04090c05130c02030a0302031f0801061805150f03071203170c09090c0d060906030606030210050c03090105030a0b10120b010e0607080a0c140709 78
    0x10070480410388261890446d4940c1e550700702c050040385010788000c0c0c1d6a83c028641800e03101048600c401f030b5070803900e082d80c01d045c0f0825141001421168000e0002e805a0010031040d06600e1081d4001d5034130460b030750001e078012803c0f4800c1c41c01e4245250031a28250b955040207005031505039040c07000c1d80140c2c410600c4035191001c03918005201201074a17025000070303140829299030921110000c7e122107075964059203040e00f8001d0050b22110107801d04008030302c02082c21500345800b00e0b4080b50b8050301640b11921062a049000e17401256080b01030b40d910500032400b51040e0065070019401558049078440c114010071020004081540040c40020002d86c0d400620100649a840500742056034503070780d60705410000b074941c3c480090386c0605000da5200b4030580000d00c0d4485200e1801c010030004807088010b4466080b81c2e0501075004d4020307c44078000400d044005c00156496240c4491818095507401c030200d030001d0b00302c11660701704201c2409503c0d00780c0300b210070210035040c00d8804 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 355630539 1250 355629289 355629293
    0x90106050d081206150c06040b070f020c090414010e03091306030312090f02040608060f0f0907050409081228021305060705010b15070506010f0b0a12110a08071704 72
    0x40b03105521014400f0794001c0001842942e80032040d00041c61104040340d0b0381d21042e8500c90700e0b10303030403030301156010013842c04030780c3c003034486c900c20b0700c5041d0030360000e1500000c0d0307800304202c40200400032100d110812070805203030320702809014104d1680000464031500c0d1601041114401c01b18500b040da454400d081022a40c4051003442a10724143c00040c880b51604040711598040f03903001c0e4010781400d000140c402000192523220f101410701603103030754958482e03c0d002d00e40195407a60083d405020284941c2c40c1560092a01e01c0c85140d001e86800042081104c007050104d031004015210755598004142c5c4a10b00d40c0c001403c0407004500c0e1213801000915500c80c503005560080c040804c1380d4007000740942c031614010000178846c40c00c940130754058005943c04084112140e000e010000500c8004680240003503803581c20b4220300f400c0320100101c80e2152500340e00c0070801d46a40c031452511101500600324941d86a0315101580341c10b000152883d1a82c0c007001c0c4d80b90000e4403c01c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 355631789 1250 355630539 355630553
    0x1110604170d02040308031e1510051305040501060f021513060e2514011409060a14070302031207020f301227030a0311071505090106050d 61
    0xe1441c4040d00055200d904151400000740110703080113005110010900c0304041c0684d943c00c9241d104079064500c41d0380d0701080580700801035502d03036400c03100035085128464047c1014005245525401d4104981d0f43c00020b4252602a0b20040c0410310350130007852074170f6061006441d190070041c81d041c01800c01401cde40812940d41c1c00054a019600c0801603400030080c04040f6a8408890802c101c4161800000041e45040c0c804d0171780c0d5100301e500c801041d500034030054010142d5a4001420010b00205007c1143e1000805100b0041400701c44030754140000f02400f18035010741c0c0159110540f0314039038207500b032020349100190b50140f00314400240780002d8003e01080d48001c486210381d10450b0b05800b0795803401c2504580200490107241c0004c2c040d01052042e80801d903c1810540300051140c40500311007000304054000700300f011401b500a81264049090840310030b407810740c683c1c40b003441c03034000d10a0801c482c1c0d880790140302c403030042405004041c000403a140748184040d41e413100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 355633039 1250 355631789 355631813
    0x9030c030213090602120106200624120303160c0803070f03020d02070602130e0705190e060c0f01060b03070207140d14030301060329060d0e160501110604 68
    0x24400c07000075808002101c2c1c1d82d0041d1038060342c8a8415510388080c40100303103015a090080c0d10009401d000034082e0900c1140300c80701e24400d0351000e0a86511100c1ca2071041140d4040d85008090244030009410345800b070513840c0c0008890051512800d1250304420700b5041c0309109803c100c5807046010102c0c11290031a07800c1441c504040c0030304004504150080d0044c1d114258100c3d00c00f240c80c8040c4055a00106404180e442282400c80c0e190510989160301c02d50b000000950300b80400e1500f13121441c0e5004060400d4207000c180c42c0d580d100011401e5110001030480c9800c50400300d200394409000e00009883c1c03400c01c50f070862601c200000e6564000c0d104800141c11641d02c00007036610355030b030151500c681042960001844180c030550b50707a0300030f115820010f446c5c0500310f01031040c6036039292060301c10341044a403044410002c200982d0032111086242540c2e644161807039103c20041d01120200e01c92a84151600c0e040015005280310010150190814010000003820b680701d11 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 355634289 1250 355633039 355633043
    0xa140102030610080406150f0302090f070918110703052206020c0d0f050f030c0f030301030c1a0d1407020d030e06040245062d0f04060314010c09030c03 67
    0x3404003507440c6d081040241c0100550b080a001110340c012403402d4005d0100401d0b40e00a45001e4407a8650030002c03503000000300d5000c800255005014000c50506010f52050f18513070000101c0e209002901c00c0e44190300540c000c401064001405000350310040031240440019400481c043da440c1c258081d49922001c1c440070f02c07580000880130b00308410800340f00d0196410104580040d400e080d4095a81da02c0400401464410b580315540710010000440703040e41d82c00488491803928050310088241454807d40740c80c0d10090100c001c80074110b104804880e100f080724281360341404e60020f403e01c7c0d29612918105420500c0310152a07400062541d0000d0f81511a0013115010300503940400703404110326028016107076840341084210040b15400ca840107141e4020b241c40e03000410440420042c40d0910105503490402d906804d081041444c0b680b01070280d08001c1c06080005081314007a400803610b80c0081c0d29085282d030001d02c41c0d0b40001e81c3d5801e10703004140c01c40e1503000c0001c000c0e00c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 355635539 1250 355634289 355634297
    0x1701060810080105010e07030e0a03020c0130090303050c070f0f0602090306070c05070e0115080a0605032407050717030c091f110115060e0301110c0a140102030610 72
    0x200c0c00554003081d1050040003950000c02039540c407060080031491050740c1400009081500d00b5408810210f006039035168550010b01d018146d900054890300c0b003c0585a00025946000700004500768050030780d21035040100240b0454146005000c81c0c6028110070340c0b00c5010310003c80000d0180c003600100c40d070001c4880394180134514048010740f061820a07a00f5018110600c05c3d0103811989207000c07903100d001540c1100e0348a68941c148c00d502441a40e40c441444140410311a0003451901e4100040304030200d070ac00e03150340109240400404803105d00921020390700000c024007000440d000702c1c031071401c64075001d5151540c00c0f0300c1e01c0c00c1100080d050340000114204d404080101c41080c807018000c529145504a886200740c00181c00650114448404140b9080010711514160050300080c0c007000302d05001d42101c90060b5069095007540d80d401400c00071040031806001150b0742d000060900b1115031a040119008410002c03103587c0c0140140000e91341d07210710f028004286450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 355636789 1250 355635539 355635541
    0xc0f120307020a06050c0705011e050a0324061808070605030a0f050a02180d02240409050124020307050303040807020d0213050726060d0f0b190c17010608 68
    0x48504600c9031000003540719511000c000b0315150840c001d401d002224506503805180e440e00156a80080507044c1080c000320301c504082907500910140c14920550315002408003400c10860203400401101ca42000c2142c0104020031030f809418294045c3d10241c0c0301034000c0c58000c000355102c41c0b60180205101001c4001010340090f035011100181c202c0c00d040c42541440448100254001e603480420207044440361080c50900425111070164041c2a81d4005045c0748144800c0e10a8400c1032150b42400b008002052480c80c0505030203403859540542d140c04010f14100810348030b00040006541040c07221002192002c025241e100b074020380c200380d50741d8880c0f0000f00984443c1710300030f5112198280e070401d68560380c1c1c4034510131051502c603080b20b06201109040c0c03c0420b440d1007035801c1c01140001c0c0303442c20402d081855603881054213500c860705664400044032000c5852260703481684d40c4c05107608503680180915028581022070840400c0844102440414001d00b000c1c004a44 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 355638039 1250 355636789 355636819
    0x6080709091a15090601020a0f170c1b030d02210f0d0f0e0d0c1106181003320f19060305010b090f0106090e060a0e0717090c0f 56
    0x1d42c501e1140e00382844801014030b0103501c0c188041c0b0140080c140210458000164254000941c104400384c010884c55280c0d010741e680c4100e95501c00d140b000051409110a107030006040002d034007032418200803c000241e4000615140c2202194100308541c044a0710003c15401e522211440030413594041d81d4860013840b011806200c0c802404568514160031540c49084543c032101c5100c80c9001501c40724040d80c91300b1242c0c1484444043c084881e0410060b80c41d281a07070023001c0d40a1624504517074000d0340b07000070352443e1590f01d1400c0869141c406403545840520300c000c020142c07165040c403800144004030035000000a0114817280f1681000c10310006213480b900e501111030102c14400e15899151a0703018105004145024081c0c080215043c20038428155041c4e80c40c541d14030400714601100e4814110300680300680080143c04081100d1005100c1d45200d41d0154880c81801d10703014111101110004085e9041c40d001402c149a40741d50305140000711a070300721403c00c40c40d07080d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 355639289 1250 355638039 355638053
    0x5090d0c060c0e0d06020315030606010e010c1b080706110a0305120403090b0c030d0f0207021f0507060f0e0d09060f11030c06150a120503030601050711040606120b040608070909 78
    0x162500f95000e10307a1801c4100b0040c15400961040f130300c1c0840c80800700a807509065071004240d440c1c601003101c402c080e6100c1e5100b411603118082c010050004d0b003514681c00c5801d49821a002200300750010081400503d07046005406140f015900816030440380f5100107210340100b43c044001c4401040110b403d0601c214590030141c90710071b007060340c1d800100d08011b07034a03401116003c603e90f0400700c003407420110510903141c0003900509681007080200038240400401c0c00380f40703000d02c8028416800031540a2185240d1844024000141082c481b00308a00d44000e0098010800c41c1e00c03c414003100c1d60140039086024501d0502c6120112007803074113800c6000704101c4880c02d100310810081110085d03040b20f448020700b61141c0e0b0056880b510b01056104001e50040e20a500400c0403039519446100100b003e40c3c041c13007403032035142446000034098030010741c056800907680008000c1da4088034420340d9255003045504200d80c038134012460792213411074030440200660740d40c01341041c0116 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 355640539 1250 355639289 355639307
    0xf091406091e0102010b01020c100305090a080c150604020711060a1205040b010f0f0311090711010e0606091e010302060a090e01060801090f11032404091505090d0c060c 74
    0x90081200000c0024020700c640c1407521464011741c20804400300c554008038140030b100314041d269185100c50910250040c00025021542a02c1802034540219440d90064460b800c110405001808940060024141d4018101c07500c9148100041c500180c42c4810752070340f946003078460f65214580c012064070703a400080703012002c1c1c508040810041002d00c1da034081c1600c0c00e03001004c03201a1110303194141c00c08240402080c00040d0700c1c40f4800c501e40080b149902c070b415480c0104070190324580d8182034030f0108220b01c403503034410410f024151034504a40d59210b0b0400f26510000d004800b08060322074010700c4003a000b41e20001d030110314644101068009441c14003090f00d6607595915005095100c2441030900891502440f070f0702c5940710b40980c00f1002d03c885946030464442c40403d031014440305d1040c0d1321440a54280690584407401007080c030310300071420100381d12000d400c02e0041d41c1d0000c0140200303800c1180801d8816410222200019820000000308140240e02c01e46075800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 355641789 1250 355640539 355640557
    0x91e0912040b09030d17040b09070b0c06090607030b010c1b03020901030f05010c020105040f02010f09150c020f030d020a032307060506120105060609041e0204080d0f0f091406 77
    0x40005010440c1d91602d00101640c240c103900310380502a04143c2143d41c030b1104409080100d80c0040818081104585402d400100010a403040c03103940b60290700c501c1e4010450079441e41c114404000c0358110034082c96500066604041c008840c10b04002040c281020790000c1402011020018105528a844001866000e054040f40303503102e04020296511001c0100e5440d030030b01c5090b40640e4418000c8034000c6034082192071941c00b056005543c1c0700d1f11451000100040d40c0c1c00000c4c1d0074070103070350035a0b40320700343c0c0700d608400451780113001861916030105406944248420400c1c01e500080c2c4841d00703601460041800c41104541807030a0103c0c0900c418002d2006c243c0300c040c08001da0000e406440221515042135102032056420303500100c50340d036071060044c00620380c141031a40084140317052003104141131502031601502281c22a0701310307800303560120040c0322409407c100d00c05203901c0203041000440300c0100f80100310030494000c03800804682d0304103550b9a110311040d201142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 355643039 1250 355641789 355641823
    0x7030e0d0545101b021509040518070911040e04051c02031803012003090703020306091e07180b060403020913110f03030304020d140f01020406080105091e09 69
    0x854080361042c035a0400001051088810000f0345101c0c60056816885901c2c40c03d115000c50b8085800b00020320489804a450f00001081014403950300c03842494480c2a04140d5005203990040c0f1191070a81ca40c0c00000d080d80c41c0034000c1d00e8800c0718400f035600b01e800300e00341c404050f41e492404500340090a4032680c030080241c0070f091038481d0040080c00340c80300305082c1c8540311816481014281c0703e401c000b82c91140d0314140b00752002c911741401158000d040d0404ca8a080341d503503003c82d181c000211070148c0a50000c0440c40040c110605407105280f0010300140200c0782003c2200c280c961182c0b1161000643d650b1b81e03800030740c50340c0050320001c58004102c03403207030324007d0807000704a03000c072500301c2e500902c1f079401d80300a2030300e0340041856440180013903007555200e900340224ac060110041d00c013100c101c0800c1c400700004000e0300340c15030300420000d40c40c2c0f03203040d030050240725041e0801c0b0f125519040030044038045588600e8408507090840607c0d50700c81482c910305050348154801d10b00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 355644289 1250 355643039 355643137
    0x140c1002071404020f0702010c031b0503030609060a0819051002040602010c090801020c0a0305030907081905060f06130c0905131413030e060c071d07030e0d05 70
    0x400e8012456a0031100c000a07190241007010782003200324030a100c07040c0540a8240a150059403046020f440e0b85407107414400c100400307031960035040b1054401c2c00c40d0390360b00000c00c1002c51704004100540180c8c0a40322102c1d1681171914a07903c5915480030342440e556030b0107083c07007440410050900103248a0384219600d9860b080d000f8046d081c0300303c0c00404602c54500c00100641c0510072603940000d281d01408051541f56422110b42c0e00140100202d032281e04c0c00803d10401c140203050440d00e41d035050344443d280e00d1600700d041c00402801d11115115031000c02249444031607902c00080f4a4520014001c1040e0805440441654001680085071052080441d91156000030030078a080401241107903600c13002c248000f42c52000080025402044a01c3c0034140403020b4020341000100b40c50950780c0f90400300715610078016910070020103200501074596090320614541c1007141015101109540601400c948556088403030301e4058a13138003407808005110070701d04040c1d5a201000c2d0b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 355645539 1250 355644289 355644319
    0x302060304021c1e0209070c050d05070218070f081008060c030a180c08070801150603110c1f0b01050304110f040e1213170c04091505100305010b0f0d140c 68
    0x101c420044106d000f617240d14085184c45009406030b802d080d074084000c02c04141e1348601100d0942000d04100e0704940c811108010f441c03451900c8600c070b18000d541d0f030a1020040700300140300c80130140c00342c44128002d41041c40b0203203021803081e91021040b408203a0704d4440c00c1d1000300808680079407a03200c501c446c1c540f20030010403951000840380036100310380405403a9031409007280c5d101c81c01e02142d01d8001104100c201e0084d04801c11000c0710021090900d0940141c01d81001010300903490141c500d507a10f010b214000e4800d01402d0b04003860910300791301c0c141e903ca80b4074444001c64184a007610140c0350b00583e40f107410602e261078409007503a101801010b00300703519401c080368081e58002c05d0340002c9460052420111003120a00004007000f0f400003043c40300074003e0318000e645841e000040d0502c04442c0f400744034066203252040c001001d282d4107005007120024044103120301000075442e2011ba56a01c4030b050f44d41e4009407a90304d001e0042c102e403440c1810158489420444007408250 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 355646789 1250 355645539 355645583
    0xd02060d09240e07050f181f270b0a05040216120f02060a09061401080d0305010f180f0e16150504030b220c090c020106050a0302060304021c 62
    0xd198809051402c1d8607071815401c25040d07030003201c50f080c072551000004112520b412002c0c0313115010081c00d5150a0f2070399201d60071800d0070844042c000e50484603d80c1c4510120481450000e00079800f02010441d00c10ba14070a01c1403140c485185507a4464a401e4000e542d03070018036000f058020821952030a2240d041d0403460452181603483c0b41260031fa003480580505440d01d0b041c0482d5010740015554070070000d00820300ca11090b0355a0396903104122960302135055090103030400718010220715210640007001e0351416009100c40441308103003003001e0380e07030820219902030f00c00b1801305200c8412007651700145800d8041e21a01e22911910b20204564949540c080e02c1402403244405482d891040d00c180c4a103110080064a004001404004403400b1b06410b10028030b49600c44540e20361620300e02d1101035000000c0069883c4140328003540c09101d0003000300340950300a4400ea2940d00001d080b400010006405294108040f00030265141e0300102d82d80d5003c031080741c0402c0411b50004d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 355648039 1250 355646789 355646813
    0xc0115060e0a05030714100c0c0303051c0c0e1e040c031d0705030a0b13141006050a03080901180e1608090c03100c05040803030c030603070b040f050d02060d09 70
    0x1030040c81d08042c00b20b028180403540c50240d41b030400307001e400d00890b0002e218001050380d403884d0411590702100c13000260f102c0105002140256100c07a01e80303030140d0b030740c00c924020b0001d011040f03850301c500e145c2c02a81004102e201107804035801246032030300c0d200314182d1f5046200e030b103139010703203070041c411000358150b40041e0b005400700001c0041e01c001d20b1046692140140200f070b40c554031840801e400a511b500a2541c82030b4011100040d0380002ea940d044035000041c03000c0180c0d0080c91020071003045611421000b0401100d85d100d040340b468580421500c40c0d91201410820248409003011307c0c2420188010701400e00346600350b00e0b02c03007842c0209881901345600054440d0740032500400b03000440c0b1900c20700040107411070348001c500c580c005005032150030b014820240000154241d0900180d4490440c9600d007030f6580c6400f004040c00c2c04a2030b082000044001e0000f80520515500e180c401d54600303444401200500b4000200340d8002c0c44c102d55081818000c10404002d00782440b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 355649289 1250 355648039 355648067
    0x9010203070e100801120602120915060406050f090901180302012f0d091e030216120309030b06040f0204061107050406080c090615031e01060507030f050c011506 71
    0x15000148240308000f040c0180b86142800640b00380010300080c0322000804400c684915001403400b084000e00340c500c2041150302c050715410001d000c44442c1c80390f000072030307001e0001c07502005094100000184040e21103070040780940905400980d05220943c04070005a003600b0710900d200102c1c0c80c000303000c2c103086440c1c030f9001d11050300c0300404a0380c4400e002091101d0b840c1085e0a140c85d2100000c018101c0d8030b02500d80ca03061080c4c0c0c0500c8000720030b5100410340280d010307000400f8060010384c00b030f03145580f110565006040790030000c02d17403007600201500d5001040030081c3e1503000001d006864501e0703080c803600d8400100010150340280300d55540c2400070090340e0b02e0700c0e42c440803c0704a595034070070b2401d9508280e400301041e180c4150b002e039100d940140040d102c002940d11622840d0412034074014820351196007011211201681e890050070031f883c0c1315150034810741e0700400810442c4500c400744940861500341c0c4040a40041e1107010104a806998690301d880c0205440480990 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 355650539 1250 355649289 355649297
    0x31b06090a080f1b060403020d020d0215130e041a090c060a0518010819090320010c12090804060f02150702060105100e0306042411030601030f051b0a14030901020307 73
    0xa22001c0714042c034136402d0701c2c0b0340101821305040c07464090004094000f04101d074400703254242031006940303184c0340003005e01d101140f45844002805800c80001f0b059000280c012618804200015081070148444c2c0030540c003050095868011049240c2074421300304a500040201c1c06600d019403260140c41004050040582c07421121401074402c0310054921200e000c102803440300c2041c5198000803e200c0c42032610b01150312032500c06101c4503840c0000d500c0c1594440c1c40c5101c1648e40441c05a00500c48031400b04002031140e1b4844200b80b00e244220070910004214003201d0703078002c2c4a1900541085000e860007482d00d10f1303000f5212842401414440e0111030f0f049404d180c0b1445c0e01414031500076000b049991034649440c060350300000c403c21410140349403000b404101a018110850041d0b24500b9140d081150000d000d90703000c200c030444040d1401007001952141804210071002c2c09002d05a9104092241161034110b10b900104000400106201d1040c9055000314131803101552 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 355651789 1250 355650539 355650553
    0x702190603050f1f060f0e04050408072603010311010c14010b09100602060a0b120d050c0c0f03060a050a0b0a0e0f1602030307050f16050313080705031b06090a080f 72
    0x5151a03c950030502141400d0242c404103021040c010b0349000700d80e10260420070301f0b2007004c500040030303600c00315000c5400020201e045000c001c4505406006142940b00c42c000c07001005d0304040590105100c003030090781d5008010400f41c0d01612220040c290800c2e0713611140f1615046c003034060401d03060781a00608603280021b030003000b02c6200c07006942082d80a043c3c83d46801030003402501803008910b91110300d10b0466540c1042c2003040d400001c0d02500c50b07035141c00010300403a01301401e81200364010840f04a250020b03640105101c1d601112000c00015140c0b207854001c4000e152180d40c0c0b43d0000100e02022411841d03400b01c8900c00c0080d4a81301806546603000880345400184403800560b10034404500100d016802801544101c0340c081030a2541c0b0391410350590082d0a003d40b00341e003000481000c5070120040d0b44018081000c01011414070308130209548141c00380d5840200b660000300082159552812119003480041034021001e4440303070002e4031004114401c1c141c0e0721880d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 355653039 1250 355651789 355651801
    0x1e050903010e0f03072d2603060d060e150108070e0c0310090c12150305060114090f04170f091e060406050d09020d0c05010818070315021e03011503050103080f0702190603050f 77
    0x4108c9104000182c001c0b01110816516000545445002003003d8098000e140211a00a005c0c19008101c0c0d60000d1003010302d040031138002890003900044c1c2c1140100b0401420407541981c0d90700702c0382c1085000407800e1903410101e890307610004400709054201301c0703051101010011030605882c003802c1540c0e0b07243d030b07103030000280e00c0d401002c07030707604a501c80c00014030041c050300030954400e0266090014202c44c030138a030f2a555026000c8207801c81300109e110b0034641042101142030462a012614070b1000c800001005e6006612a000410500242990020413107401000d0055400752010840c13020314030301208040898001e69000a80c92000510000c0300c4c01c01320f40031100010b01401f240c0c2d007945c8800d014680b100b0401400035400b04070140c0c06400c903204c0c142d449019000555140e5042c40a58810505080d50001c200350074600140301085003001218800840c0380c00440e680c040354804108001c0c141203d00030f82100d20b480000754660107030803003807181200384030b14601c550b240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 355654289 1250 355653039 355653113
    0x3020a0908160b070218040507140108070c15021b0303010e074413050c010201060b0910090b0406030209040b10020309010305071e050903010e0f03072d 67
    0x4504240b0107140168400c100103034a140041940c0380c00600010384590340c003280321111100642d01201c6980c0402d000300112020301e200e084440360246003555003401d20308030040000d92031400207020039514030344c00300704521030358102e44900f0001504d1400c0007521030200c60b03c80d0002d10550300e480d440d002c00202124426030100c40c440003c2c1c2d549410b00a01c400c110241c1c402003900d54400401c80119071034107c2900701170380d0710038075109480d0b07000c2481c540f80290401640508003410b6a0424005000d64004213055030120a001c0c0d81071100362640400480b0f24004c80d81c003d00e01c090703000501080182c0d141d0010a00d0f003c0c2a101480044154001c2c008038154550007400140c0050040320382e150704c00c4e000550480c0719841c01c01d50003907407a100c858090100584e041c000c2807001800c403071181028040e9104014502c0081c002d50141140d001d074981c0304135203000f080141e0000384001da007100350f01e2506022800c0060070608542d9448c080340102a00d0904440c00745110690544407240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 355655539 1250 355654289 355654303
    0xc0909160b0301031115040306090203160311030106080f1009052d010b0d0c05011817030714010e07030206031f0e190902010f0c150c02030307120c090605030a0e0d03020a0908 77
    0x11b1416041c5418910703112000101b1401c0c0d0102d900d8011540c120a00400d000e4400003e140262010030f4030584030000c05027110219031040d030203500490170712401d0303032004594103c152801c1c050102c1e07011010703e4118100392010180e5107058401d81401020b80746520301012141c44100002c214400b4080c0c1040300d000400b000c02040011003003002d00070781d4401d0001c4a84802c46211418110b900c0c0c0c240300800101800c030490407684081081001d0140348610300c03c1100c0143d00810440240b28002900c03080c2e0b034000039000f01c50000209005111030840045005106840c02d540070ba01e07000e003408008000d48041040524455483e82c03146050711850158a605850b011a030b013102400540382c41804010030307100d98800901d02010804140124140754030280e02441d542e181804002d00594034140c40c9080403464140c081c0c08198105c4019815a505424030320345030b80d0f46540c0c40c4c010b08200d403807845aa0043e040f6104030160940c0207060000300c603450b0702076244d031100ca81c40d680d140307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 355656789 1250 355655539 355655569
    0x1512020c0c1806060328061503110306100c050307080d09030e03010e07051011030d0c032f0706320703020901080103060c03060503070f050a0b03090c0909160b03010311 74
    0x401040403810309070f4000d0741d003400402030042810a01d064122100121902540614050b88a51002080540d0304ac4500d145034860030040d2170071070a00b8000302d0700c0300b01e0700030707008007400750a001d200c0500c4010000d0707404c140e6100584d1580e4042251600000d010070840480c00b08688000c070320b10b140380c18090030226000c1c0790000c002e803610345020044c40c0c8041c201c14200f40800d2000500180703800f80001d02c22140c0709a00070507000441c080c002d0840b00c00c0242c01512000c5215060a40541804070414040c0b10131341150301d550440c117018004285074004104202c07040c0c00347c0c66000c12070b01e074000c507112040c540501541e61004000e40c280d218980030703a07000401c214010300018466900900d4000c3c1c040c80c0008485807180c0101c2e1400e502a000364030303c5400d03940f003002245444819940604a2840582e0179410a641034659800344040614441d9002100085120030304000e6a59024078052241a11555486216034a80d100b0300055a5103861403070785503540d0610b03e0035000366507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 355658039 1250 355656789 355656799
    0x90207020306180604021519210c020d050a050f0715050f060a050d0c09060e01080d0219022e031d0a1e03030b0301050106032406091512020c0c1806 65
    0x20769a6420004210805090312207907c0007881001c0c0381c80810504601d298100303444550a0111b4401c0d50208010010b803402103450038012100c450f40da0200f040510310340542800768440340c810809460500070341e8890000e80c88007140319414807803076a8548142e1400b261003002680c0300d811103001e020204030b6096421684111081103a410303c0540302c3d090b98018034000701b91589910300d003804c0c0d80159000311001e01000005008564040c0181080c0e510240000d03c80e000420051f00c0000b0401d44000e44101d500039450102404841c201d154801410980c050707864607603910284c000c1004414105507a01002e0b4030a500c0c51001030304180d240c2d0041c2c1c02140d0f400d060700b0580d42151964504800309238440c50700e020103440900503c5c1c045c0000c0e40f4080340344d140d05800e41b001030b9500e00c28803041380d040300c908020a58100ca100701c240c584a894400c900c0f441d1846c1030b9001d1006000c540801803001540342c130380107004100401d040c1c9080310f034003210a03000c2e0f00340c50080e94113403140c07640a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 355659289 1250 355658039 355658041
    0x20303041202030309030d0807021005070e04050403050c5d160c0504111306120917090301060f03110402092704050c1e06030a150902070203061806 65
    0x7000090003145000340300074112131901a101000c02c1c10306070b44228403000b15486005010000d0780600c0002200035031503404014030b1402c158000d04d52100c8014450089a0354800b103001d161103003040751003005e001000c4030b02601c001110145a0014201081c10705000a080c0108400004140c2c1c85002c0742648000c000108094401008040290348908a100108489402c8030180c098040314207000d65030720030845151105103c00e444c44400d88246408081011002c00c0303c6481c0340c40300ba15010b18000808540559801004058505020300004a58801c40a1181310301e07008124100c0c00703030001d000503036559070111404d1810b400002d01c11914501965082d081550207045020700c000c080d0b400b4012240307105031040449080c041013404442c01000248802000040f018850030f44d044c4600c1218a410030784660164410340f4454903000002c00e070030456580010001ca640b00342c0d12a01641c3d5200b40c00003d42c00001e080b40240603031400920b0f80f03c0d100044004490840c8003400032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 355660539 1250 355659289 355659299
    0x703090905070302040e01061d1c030c02131406041416033603021501290c0d0210050105010c0f0b1306050c0705071415161a0f060d02030304 62
    0x80c1c070340144120304040d03082c840002c02c0600149005c0c0240304a4540013480301e2230700d040c040c170700b0b030000003860041c2180f010081d030a003410581540d90a03050301d030041c2c000d5028030003d0124003141c80c0c2c00b0b0400c3c0c20007030807900403c80c00c088240901c40456080003000c3e0400007910b035202c421142d0300400392890b8021400e0500075041a003960b94100d1000038000b40d400d070181b2501c0c048a166104000f0a40e106404043d01003181f40d07800010740d44c6002c50f80d0b00d480c0003881d0740c01402403103e00d0142d2202c402000004440c0540b0710788580c4006440c0101800c51000395a00030084504403642d051600000c1d29500034050040600e40100441c16080c10940f0b076500c04080203070108c603254821080b44000310303071700740b00301402100c9400700143d80b400c041c10400d252081c3d940082d54041d001039031070000c0ea9519000300e000c41561540b000e488040182503c02c0c5000c032181c024107440c1801c0c10202c642002a00d074680b055039441060a081e455503024001c042d0313400d48000350168010001441 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 355661789 1250 355660539 355660541
    0x105010c050703021005030604050a06080601090b0102150f070917030f160b040305030613111204140a0b1e1302090a09080d0b040e190b061807020d1407030909 70
    0x19a600070011110100d540394080380034020030700c1c100030010307401100b80207151820b4007550340c0142000e8414019103091000c0141c03600010700c507070788005507111b80c0c0036510b900034000700172580002e4503464614038110100d002250011210380001440090010030f0100c02c5141581c9030b044020f00035400d02d00110031040d10395020725510380a015000c3c814000080c40030900c507200301d1083d55100c1e10303070400c04184004100c00807039504145060541d00c03d005054401542c918400440700420b980c0c4507400c058a8940983c2840e003094010100d41f6002d118511310400d00809248403000c84c005280c58540b810711070309640b80c0300584440507201015203021180c03030741c0203480c912000a189030741d9910000103a1100204a0f00c0f03540729035045a0b0b600d0700e48111030000e41150041c05041c0000c4010040c42c1d4000140201a40380c6000401c0a42d01d031400b160b40d551013240c00b070200a0400c01c0e0081d5490201400240001e80914548515a1a01829030301d02c0b81e4140c0701c40b1945828422288 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 355663039 1250 355661789 355661807
    0x11010215250512090a0501061202010e090a0902090f15010c050309090405030d090f020a0b03060a15020c04050c07021e0a140409080f180d08071410060f06170f010501 73
    0x10302003040501400708000d540390f050500a400700401480c1303407865407420a0175903c3c603920540d0200314500c90000544d070001d6440d00c0b0b038081103c0c803407003940c1e490505500511051300302942182c003140070070948185d0452058014042c505a003007040d80b003880116072806804d04010820b420038080b420780e50808160064000348113005030303801c0403002d080c402c0031248074540c159441c030b00c085111415410100c4480b8040d01e9040c3d0780e1451450054007254080480c0d108681603000c105608a01080c820b012710001094020828032080c1055022111142c1294009034482ca1300300c0d120b800200d8549042014a041c0a001800341501c0c0214202018000f0304800fa00b09840d6042c100009411100510202d445108615242e0410110702c43e00c0c1544c094042d809411441c0100010601c03c10030f458140e0b52116aa0344003050120a460610b410041d803902c1003418508089591003038070b506003050307071029551046060712030a01c0b1407030058103440d4007464668040c01070100d544500044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 355664289 1250 355663039 355663111
    0x714030a09120f020316180203010e060105070602041508011d01081c0216030c0f060e0a05060708090a0b030a0c080c1206120303091605120709022511010215 69
    0x220641d0f03030301e90f00800d09159001c4010300500d00f41d00d0040c000c1c1c221803c00b00e02c04c0d80c10301c0803c500303660400708035140c0e000000c1d0049043c4903003c00c034027041003040c0d01180d0280c40f041d5810000036400c1407002d01803503420300984500324140a00075140ca03004402160484085100420340b0f24040d500314003a0100030300004085004202c10380c211420180a0381d8025403040c43c030a481e01c2d1178183d9100101e50036800410401c903400d40038200d140e0b1102402015a842218042d81c2c0b4200b9240603400c1d03204030071000c1c0d040760b41814001400211400510b2080860100500080150503c11180a0022980404031503c20b00c2500e1040701d01d40701e00e070b51003e0301a012000400d0081001462b54004540d280d030140e00112251003c003010102090080c40203440850102030b01b0703800d46803180ca0901074070042d00d81c0801d0403250840c0e42c030442d0070041d202c40492010412507040108190180d418a0ba026118882e4906a40d01c00010140e102e100400ca5000c131032180c0c0c1041d04103206034850b80f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 355665539 1250 355664289 355664303
    0x5010911070f0201030e10110304020102010e06070503062e030606024b060c04051e0607200a0e01031e021804050c04060e16020f07050d0212120714030a0912 69
    0x130000100d42c2d84103140d908d0080c03844054a901d49440028207403220b00d0100d11300d80d00f0510074480c000d50010117407508101c080315040c07240d070100c1d9000503020118003408030b070b6829018110054aa05544410305540b555401d07a5941566a1004001400315a11414000c445905840307075503a220f034042c07aa08031001d40d0720007440b0b094841030b41c941581070390b8444010302c00040401c03092500d80881c03a0300004200c5840041135080e00054058051850040c00041145a1b82144c201c0300c0e081560380319100411922140c2d40310b518038241020300740002c64400b015980713150500c1801680c440f01c900c0d8024850718044008034101c981c0f0f00d4000d002191903200b2403014101039903950250070046c090064039540c01e03103840042d400503503440d00501006d40d088045184414200032809078251041980c40c0090350701c9510214000b10b107540103034131160081d000c0c481c10142c50705004003603c50148584032011441040742a480e88114410100800d501420800c0102c03108528802e155000d007038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 355666789 1250 355665539 355665553
    0x403020118090510080609070b1b07030c081f050408090d0302120d0507081f090b0f03071409070f020c131e02040612050105090106050c070b0c0105010911070f0201030e 74
    0xb14003050340e100740e410084000d0429414041800c007000078682c40b00162000300686498034090104511580000743c0100300c125680d101c002070104a000021a40001c041030b076684d0fa1050310340c46003002600880340da401a0071141d904035a5014403400b036078000f2122480d18064008110f07441c5449002241940640f00344801c2c1014080c0140040c066005000b040c1c0703251148006110801c01804266403260019044a0ba2550001c124003514a10100082c41d01202d0000414007620a0400d92f410320076000081003c07030440180302002c035800c0d100021240c440c80002e4940b65014880c00307005074400e030302c81c0e0446d14045420a640003190b400024100107200300c3c0b031581c031112800d4401c0c500c2e00050100141c42d4040200048030788600d60411455050400190040c4010b00c81c034001c0010200d40303032500381000c0c0200320041664400b02507031000b101070200d000e841c091103155111450212003c211828070000c4502e0070703600c450100c864010560065000b4a0824a9860a40702e400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 355668039 1250 355666789 355666799
    0x22050609240703200312010b090d05030706020a020d170c030a0204030f030804050c0105042103020c130c1407050d0f0905060a020102040e010512150606070b040305070c090209060403020118 83
    0x3803545070301990340c01091101601c6071051350240207468001e5640f042000501150085d019181500e642182c01c80d611664140020020900150042d16500000a28204020140c4c0c014000164184c0a41c3c0e4041c4041605483d140881e0500045101070f0400003440800f8170001107a00c081940340050810b610790303c0700c900350000c40c0812030206003100c0a000600004004e0308407035000902c0c1503490070741803800c0c147ca80542c010b1501c0404250b1030810701098002e20044010000240c008510b40058920800190000825040116100c481100e6041c1407840c00c50302402c1e000b01c02803106980c210030891310340044003400001c003c005600425280d8402008200c40c21140d400541c680741042600e8031191410307480940309028001c0e80c0c1e442040701189124036180740d4410340e1082d036a86800b1502c148100c0d10b00810015040c4200010140c111002d405124050354944440c0358840d09510100c1c400d141c26141d020409020800056114901c8444415900810327407a45594070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 355669289 1250 355668039 355668109
    0x11090406180b0a0b030c2503050307021614010c0807060504050a12050f09240301260d0e190306050a05070e010e03060115020718020301180606120207050109050604060222050609 78
    0x4000840000d2400000d12014a90411148482c45030005237120001e1800303000b244c1003400c0001c09818084400601024070543c0001c0e04d00080d00808140003501d000c0c9000340c0c0321400d00c071080310001e03100e03004114072502ca00300f51454000410600c80c94440d5038800c1105a885009071140341300840d0014100e400b5154010314004d190540751003103c00541c0c0760940f01e8007044807880109522901c1e207801541d43c00140d035054284203441a01000155881d02e000d406440c0c0c00c054413450801e01802051031702d0b54882c61040d06c160352690301050140004442108402d41029071690007100140654903800c1045003480000340105d580540d40c40b010180c45011101d04844459030100c010070040590005841003031080001c10400c1c2d606200703000c0e002804a1001c200090381c0442c4860810909501440c0403e8000040350b169180070f26100e000381d807040494407803001c64030416500d000000b82c03841040d181d005000c1c074180619401803101c408030600700d2000c071005a0780d40d00903e80036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 355670539 1250 355669289 355669357
    0x30a0e0f0a11010f02210a050403050f0703020a090216030e030a151b021f090311030d0603140d0504121e05060106092102010311090406180b0a0b030c 66
    0x1050140002840b410000907092007440c103c00030a540103401c021240c00350141412880b03c0e03c002c040c80c1c940301940021580d50050740c200408600c03440b0b0070340c1401c03180000d05c0d004a80c801c85030449065110b10040d81030703000380d442a080c41e260700411000000e0296400302c0444074040c2c00ca82c0c0725a03164070b52540b00000c2c4825029440e503104400b520308220410117007012011800100000d4140012651010000007404c031003565031a4150010540300e01040543d291030681140d80391503040c620907009041d140b00c111401601c0810000c413080012600c1c01075002151a07079420545002180c0c1100707410340004440910f4000c0b640d083c0c911742400c2c00003080340a04000c18443d0f0610710045d02140c2d69130806881d031500007000980c0c5110755184002103036420310f8007080c0c9030801006071046000c2e40310300310f84c000d013000e20200300359074aa403403280418004e0005001501882d418442004418041c001001e8410000100b2031080c48000b086070f09200341e44d4a0320800308030001045849 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 355671789 1250 355670539 355670543
    0x51e0402310602030a0f0c0507030f0b07020f0d090905060619020304170601140d060f0612020307090b030309061308011a0405090610180f020c0a05060901060b030a0e0f0a 75
    0x2a40c00c1c444070080038040c80038014002c07600040d07203060383c1004040c0c6002c00328800a01048000d01c0328404200c1c0a025100085030b12000f10007030503840e4903180c0300000c01164a000140300d0039481c0306220000040e01d07a810891a29a03003142401d00c0c2c4060090400101529048a800c0002d4019124422852442d04100d070b030246440d20705201d80c1202c0701e242c41e0310150344d65105900510001c50003c5640c009030740122084c03210744400b4a00301003e00580d4041c42440c80c90800001840d401905003102c18900c2103007540c280b161a11103d90403141125003860301030b841881000c0c4c1074181a4000e2640702d0814a004021a0b0340d602c40b942075074a000d405425018540c028080541814042c094000446602514040c50142202510341c0100d11074040303614044d41a01088102c1a03200b10303004034455805640d03c1d18080803c941c0e139120100d0441c0e030741c400d0034002150805c040c45080305503841403c840345142c9034800e400020b40300040098030039010f005403000b00190700704a04d5107864 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 355673039 1250 355671789 355671847
    0x1502030c0708061b0405060a050309010f06030506070e040e060a05090a0f030c140a02030a06110d060e06010f020f0a0206131509081b0603060d030309080403080c06070306051e0402 79
    0x124004d6000c1111301d40100350701c0c21040f4180b2041c0410b6580c0c40941d07140c466149000e584941c2c43c0500305001d00080501992100d00d0a0f101009004021500030b110ba001c3c0d4403010517410419052100303d611141d0f4040882c1c01c0003002c42d242084ca5000103403c5410881184d905680b5030310745184811640700e0440100c2d1200d40c141c0c041140130b4003214444500040074244007805a0042902e0f03a0301e044000b00505d03030354006103d0030f0100c00e003900c1f4500d0101c1020404d076034980e8008810341105486071070214074200002c00e03a480c400240681f611b02c00c000604540180d55081c041aa0003412700c00e00781414031b880101d1030b1045507008400d83e540e036a5a0b050b8a40c038007050b0701e041102485891403e5403c41e00a00031300d03101e8400b2aa084001660403003c480780340e0400710001c101c9060010184040041d00106100e1307440003401500c01108241ca81c2c54171039a609604480c582e100da59040b0100c0c0214041100a0f2030748805407403000341c4054a444183c9103911034000442208420304 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 355674289 1250 355673039 355673041
    0x8040b21061804170c030d0209280e0912030c07110603070207120f0503220509060f01180b0f22050105071203060911030a0b010c0c1502030c070806 65
    0x325081480d0340012081c0c8240c500b181e540901203000c00710041001e80602000d143c24200071142c40100c40c400c1050b181502c1d1280c1d4609100006544800758052148200140d5490310800d4100034820751200c81802d40c220500e0440305400c0c130080204060380c42d0103102026030030300e04020300031486001c10140c01d550342d205928064000100800b5440c0c00b640b0240100715003c1d80014440040d01c1786403010040141d41071078214135100c02144010319134007022a2039150b100c030711089400b8114001c003140181d2502e0308144100540e045440c15070001800306400e0840d4005c022950045004a5400d1a050f84a00d0300701030ba0f030300130484806411000116004040c031f45a80038000300311242e0780101d140e850301000a000380910a4080c1c604c200f0081d003524000e000303034800c41c02482c2100c0103200385c4100500000b01c54108441503000503041020310760700c5611501c014004c050744000d40c42110f600741040000310b050003608400c15403004005000384444200300100042100c03c0040210f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 355675539 1250 355674289 355674337
    0x60306030b100b030c070c1205011401080d0507031119080901121a0402090d060903030501030213050403021c09031a010603060b0c030a080705121e090d0c02040908040b 74
    0x1960340c01420580b5450740060244002c0c0c0b441c074110317038110891948054454003582402d403141c0c04a540701b60030a005c1c1022903001c008040d040081005180800c10b26143c0c1c1c0e59200350b0700c4548210340c02001900400814000a00521101c820390b00c8140845140090303a4040c22290207084800390740c8018007180440d00d66a00002406c4040020141032105940b8520007801040d2203000482c495a004030742a1031301e48034030307808584181d0484d005100340942418003a0042c002070105a010340034454134810148020b000359805540e00d5401088180d60300790400c418440b41c040c40c40c00b000384090b0000086061680201c0b000c88140013207030240c2d4902000642240c005500c6484042824000c1c0100c0322008000c5d9550741015080214103a136400030101c80303502c0b594009030741e122140301c140a00c0320400c0c4403071202c40071010441c441c02e4658404003540c60b0240142400000d0840380c0560041c281074200c45100f5114000d201c1c10f041d20307000310240c19084070a420803240a84403460b00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 355676789 1250 355675539 355675553
    0xd0209031504021f02062d0106030f060b03010620030408010608010e07050405010803040608250e040b01031a06090319080a0905010c02090109021612030c1706090f040f0b0106030603 80
    0x281000d024074604804c603d04000c042c4d2200c0d4020410007107220b20b018045e40e10705c0c43c00081c1c1c000a01c10100050650703101c60740a0000d02d100241c0301d0b1042d10b0722002191040100b0b080307a040e81e907a5190010350140c105060661000803504008244c041400006595482400785601420b00e640003c40d00c090b4010700305150000c590302551041d4240070040003405800300880341a2401468102c2959a0314850441c09a003c88128580c0c07804002401d444c00307500080d83c1b0a80c4c10200c80520400007200011001c0e144402040300e1120045041c100d603a20303000c0020304224001805a82d03641b01e46803007030140119400c82c15508200005051079a07a9809000f01d0081e20b4242050700d540f1009801180c4843c0050183c403211550000700d0460303200d00280820601c641c00b26403410040800c4000901411000d0b17400c1c80070442180300b0040e80c0190b1004036106240c00742450580b0342e540079100102181c040c105684855048498070003155121a80b0b502804c0c0f5038030301081c000c0c0b549c60821 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 355678039 1250 355676789 355676809
    0x52a12030a1409010207081b03070210050a0809010606120905120a05070c0906030b240a170c010201110a0e0105040e100303080c12010e07021203040c17030414060d020903150402 78
    0x1a444e4810082d9000042d03955080d80c078030660342400c40f10b4011200e6400d5256220300d90f406540b00c42400014800158801c000700b090101c0c3d80d44101c6152905817106003a5201400340b2004200e4440100c04052000e50000240c6405582203038800012101000040e5014440c1d800005100242074018012035441d03d500420f000300341080034a1840d00d64100000003c7c2c03c1c003140308404141c1210649600610b50703001d1000401d0303a003001d0340c0d91401c040f600100c0c3d00000035034081d0018400035503006214034028001d60302c408030729205c00c000c000c0f6494804503920505006050001003001810314443c02d200c1c001040c110b901490445c00c0240c16410b0040c9900104030080058a03d88440440710a045951808a00ca019101d51000f81c1c149240710f01e0420101902008010a01c05805004d90403100203040f080e0441d07550194403500c0c0c1c441d50003004161072050f080c00748607040400040c04080c50010b4010306001410700001e0416412281c01ca41d400034480c20702040d442d060380702c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 355679289 1250 355678039 355678051
    0x501020f061009110405030d32120406110301080c0a0f06051605010b06070506060913020619120606051801030b13021b01090b0115052a12030a14 64
    0x1040c1da031408100c03144001da5180030b51040c90352525003500031300d1918020340d0085c1800400b6030354030640600004000382d200300700d18449030b0003080032200b0200d00401400c003080010441c440c40c1005080d01c41d1443c69000d0011523007a956030010313a07e44402d550196020b400740c0ca014003203a40308001000060186501b01c0389030003a00d10420032660307420008035202e90440043c14101290581820740c0104803644055400400c0090300c00104000440c40710b2080c4000ca07045801ca07141e40c00b0f07d252a201c0602d000390002001c01c0780140d03030100228141d10380c920500d0a0304041c6d01000c0c00c9019a00c1c16886031001c01c40100700c85160b040c01d044d15145c041c80a02e420810802e64400203001c4100a2884440c05980024144550809103000b81110b120101c02804043e100c0c4c0741111120b5000d204001d5900003440c5401100382c0324408407241c441104084036031100d0b03210192008500c2803060210030b4440e201060075103154100c040c52080d0020000026030300c03642100d400c0982001801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 355680539 1250 355679289 355679293
    0x6030804150801051e0112061712160807050a1b061215050d02150708040e010914310c0501020f01020430081303112409031204080102040501020f 64
    0x6004507180c007a14645105c0e00c10140701200700d8030200503030b80d8190402c1031202c0c0c1820308002141d14a003ca03420880d650920040f120610006003021945009801042e86240c10003520080841c05200c0a001581e01074011380314056480c0da20780802501592142c0351101c14010200006ca400c070541e40c80148440d44c1c02e03c80c00d0300003490000010350750f000342441003050401b45000d5495541304040000001d0421595400090400d0030064003d4031440c083c40c101c0700c00100e005d00c1c2d58002d0300c4101e0400c000b80004c035200d032200003001403419072004000c00f000c0b24500ea110040b80c51404205c9014501d00070705981001c000900700007807108045896801040100150000e0b4002c0d2030310b041411203861481d6050301040b1440d0072900102410a2501007117000d09540000400c0701240e1241c00504020350811003030142d4502c070504600303004c0c8602075910b60b65103043c03002050104d0008065521826440307250005941040d01300114680d030110381030158bd41c040001d03064100f07490300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 355681789 1250 355680539 355680541
    0x3181212050f04120503090f1c060903031e0c0906020705030a11031e0105010609050d0b070e030f0f0109050d050c070611011514010e04050c0901180801060308041508 73
    0x9480e811940300310304050070090002a4645841040d0081d10f01802481e00ea00304151403a050159072504040c840303d1054096508500745407404003129013000c1c0908540000c03846007912146e00900c1811410740034180c0720040100000006252200b04101c1e5030400140c1004d0600300034482102a085081958003c19091029aa00080c81c81c080d99021009040c032280304000300c4c2c04d0456100f40008601510307045404083c80640216068402715a46e01442655520820010201a008c06418000c0c10404260714038441c0200a44164020702180d0ba1148035004c02031034012100b0340c0403c00d9564030b030520104007040c4185040c0401d645041414811551040354840039540315842c28000107448214949800390440d002c0700201402c4020031039900e0f1a500d03140b2032440240390000302d05204803e01403400c0e205190183d4000400d45007050708290044d94a9000c00c2251f00b041d210f83c0d0300002d2641c07401d0003514042e5204440c5142c45603c5c2070a01c2d1000b0540001020501010f10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 355683039 1250 355681789 355681793
    0xb131401050d021b0706020a030809060403090b0a09030822120809010810080d05030624190c020406080f0d02030c060408070f14010c090603060f0909080d0504031812 73
    0x41500c5040e090b0030340050ba240880c140d1420800145107040c0041d000312500040c3e00c0382c01003119400e50b40647c40d41030080e59030811240d1211021034005020451400c41403001e4803000020b070440b0841c40c04c2c0b1140861716034880d1695600400744a00c42203071040f035103084400f4100000f40c001c01007101384404812940c1d6500c4403600845020504111001000800600920107814020241c0d042940c50000380800014600e920480e0b603503024071030985500c1c94401c070001c00c0b18488200314059908040b43d031640c51100c0307201844d1a00801c030041d00f5080c090b0744c5038442c680c01080040001c02d16114800e41043c00c104070312100b40103641040c44003003207020012480c507902a03400b88041d65107441903d4520040d01e800e0300054000b13040c0b602e00789030040055008604502c2d46480315191169102c80c12001da82e03240c0901440014000d03c01c000c001480e4000c04900c9209008503402c102c202c4882d0320444134212000d0300000e160569085040c0e0f061010280600244820001003012135 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 355684289 1250 355683039 355683047
    0x8070906140f0f0d080a0c06050606130314070f14040617060a0f0f02070506010f051e04091e0609020108060904080a0f0504121103011103100603020d0f05010b131401 73
    0x18104090081c5030f559441a00341c0c2c0ca1160108020b0352107004031303446024150004104100244088400320701d41004190380c0d00d440c00903525054280000e1400b80c5003140d0b212070407204140311030070861203011804940181541d8850015244614903030321074110350300412083c0c034801e50080140094208000380480c1000c1002c0da40880a01404502d00c4104200c41005004283e1507981d194030104000c02000404141c05048a480d00740103008161901c1c10003614903c02c0c7e1485c41d01858042e40310101e820642c04c80b040950182d1b800c10101d00c400d00700c05450140c1e02c0401c0347c10507031301d81ca17400840d038000c0000c0740c2100003917541e0341c0b1038036040d90747d484c0602c81d02c1c440d0024070100030070050700a8441c01c1190003504043e15030055540d41c03840d01200722003460395168070a508040c41d0020104014080c2c070b129128110100b064180390a5082d0020f610940d0910401501c5000f0481c900d042405030794002e0200c0e03440c140d50340842c00810b20390b00c8225080b4401c040082c0900c40c08503a40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 355685539 1250 355684289 355684309
    0x606040b0307090f0e0403090812070b1e1e0c04060c020d0212010204120611031006081b03070f0f02010911130b030604050a0b18070306020a030e070807090614 70
    0x4210503103075682c0340c00b0341c241d40c1c0140f00c0d4043c40380b400c61000041035645840d1015805070388a510f60350401912085e13035945075054030740d1403c01900700b0321584000c5594034047c5a00100c40f0510a01031681d1840c51030403600302180d0040c41d180c8000800030103001c14482855101420040060520381032040c001c105050358a4040c0c0701d40780340740111095590340784081d400108144004c559a079070350003148080804802c0c09840c040c1c604081201031000789007c03070784a800403101d0107400d281021800d945c20000901440c00c680410f4000c10b8440c03203850001d5014440c00e45690500a0340345000501842c81e0b2004c860459040964800001e00d0f40541610031400448954100c1ca50300b403516130080075030640c000d40c148104000d1109201c3c011400e002210300908103810295521204110308034aa80b40c0606a58031481007000400d02039800703000009198503000c9000008944498642040c60b00083d100303800a410401510f030603842004000c299044c04001c00c04810030029a060030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 355686789 1250 355685539 355685549
    0x80304200d0c050301060b09060904021b07080c0a080d0806010e0609060f04030b0f130b25120c02010c090312020a05060109050a0501140d2d0302060a0f0203060604 72
    0x28000d20390554400d1048640d2010340d6018120741c42980040c1000510180d561081602035460f112000c602018044202d0307000c0d10000e05039a2611011606000095116140d00c0c1315400002d03050b6042d420083c00500d0040200d07100910030380101d8000c00c0a03480c80b0744e00c0341603107038041c02d503a501c903a03044448a5805482401c250608510200100f00030741310700e400b030f543d03c09000210541c02003198405070050b24059003201c10656100c00000c5423240040e25014181c90b9415002c00004440c040743d41d5100310041606000050301d400720030108070b04024848081810021500740c040340c103110315000300505200a01c82000b02880c060900c880382d000103080421811030318a181c0c0d000300882c3c4811580102207500545c1d45514200c01420107544200181f8101000040c40e4800740ca03080308040c0f4010a1703120380348036954401c03c50001110004955a072541e107544007031103000d403040481c07034000d8000d401d5502d0020244011102c0c0014482c1e1414810f0003070018a0325150156002d4071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 355688039 1250 355686789 355686803
    0xe1b031f1706130219030317071701180917030603010f20031b0307050c0c01080f011214010e0a0302070e070e1201110a09030302010e0a030e0d020609040903050a08070c080304 77
    0x20f00900100d075030018140e19940c0591020b89000040507880340c0c0c0e6540b034407a52040c000c0991900382c000c5030b07000d08401c03424040d40a14001481038040741103403035070400c650203400280c00340319030740b120b03688200310800c01c3d4021400310800500b400d081c00f404140003401c5100300901012150b80014002ca00b00c1410303040000880000e20682d10700c80a45600c0070707408001030701ca180c60840100150711400e00084103005502c240d40503540152a00c6004d0211090f039241c941e82000101c281d000d000e100141d420811120b0001c0c2d0745002842040461071209022f48551042d50070701915080040d80440c1903812414104000d241e4070000d80540e06000f1500400d07402460140d450241503000c4100a0b0b610740051445241c070340090340074080764401c0c1c00a1005c3c199020b00030703844403000704000d004115080441c0c40d55140c802210100f080c03004244905000300034003c5800c0343c8021804030701180300000d03c50301c4030744c02641311079010b031080c60110f040c2401c4d0f59841030140401f074401440c0c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 355689289 1250 355688039 355688071
    0xc02160e0a0c0e06040305010e1507090b0f091206101202060d0b010909050907030215092b08030109020c0601150f0c110909010c1d03070e1b031f1706 66
    0xd10035030f9030048802004054545039520b07400c0132402803411003456040b038480c085d1030004004039908190721403105625002042c07441d10304100d000c0d61105d1840d2000b80410420b0f0342059503109c601d5004281e102004100300d11740340c00305001100341900900341e080006c50380d0000696412040720b00020810001040e18804d190060312080b050360042c64030107041400b040400100090124200c0e40200c0e01d2180311161420010110310804140342e4200d222044480000e20004000d96404c51644c01e203400c0c40b001070348410995030000c1c1c1104510f141c00181110700345004004542c003400100003e41e0b0040f401110282800074000380c0c02040c400d51905003418428515281e04030708101504151175450a5605140200140003208012402c03121801f2648803403d0f0040344845000340003410103c0c10f00b800080f854070f0013041948524900501400200c4211000d580039240c12200398a0910302c401e401d056a20064003d1000100100c0482000100000380780ea0003071504000c24802d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 355690539 1250 355689289 355689311
    0xe0a0207021207060203180103022106061b0109290103060f02070807111906022e060303021005011d04320c090c03010f06050c011e0c02160e0a 63
    0x407030b4a0607500c0007035028500700001c0554001c402426088402006a401c41481c000150100d000e00b00c1da02d40c101e138401c103035085010001078550760000f0b0001c0030f03a4100507110240c41c2d00d002505a400029944801c07215003000640768418548110b04500001c0c020608038584645110521000d40030703c3d251101c902c10421240d04444400ea0414081c6036112110308000d000003182520341801080c50ba0382824460200003400004d40b401e41c0d001c0c000315201d401068801500c00d01e4840c4911900004d080e1108000d42b140b07500441c404d801900a4a4000070345200303d60050b070140c80c04408028040100070301380102c2170b078080e510641107011500201550320344480764803041c02244000b410000404e15002a40204000045441d0781c210340c2c6136882e00500d40000c0c030501740800d4130203406200c00381c00340001d091080d4021000003489030f01c4561841c0342e50100c240c0644040c3c0d5071804502c00d55410310400c82031011003002c07805041d00c0c0911484291500400c00e100c13240d590701400e06 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 355691789 1250 355690539 355690549
    0x109080f0c1009051e0906120d030c09080d110d08060108010b070302160e0a060803072312070602040e0c031b0f0f0304230a151d1506010201050901060e0a020702 71
    0x29120240c2070109041703000400041c44861444024490204140007070914580b10501501d86e04451014215800c03040750b040d00500381c00d448040c02d005c441d045c003041c0f40004002940d60348000b6900c14201d0201214240c0c00c00004504902c10081007074104040c590300100320604441c1c004034148e40d00c90b01070a040b400c004c00d250b01108103ca02e4400040c0441800d200a401881c44100800c80e00f507441494580da407286080080074040381c1c2d00030108804000000492180d05041500c0d90094002c0702408283d104070000c0300c500b80c1c041001c0c08182d51030310101d40e012101520036803a604000000001c4080c0b403c50840d0702d01000643c2581e140c00c04400c1d41c00603245001a15141e0516140119911280d000343c40700305425070004200c2084000b07041204260000f4100c01c0c1c0da80a511250041c060096491803089840825000d008500300041d14841c07900d64600c00040c1814000282551030162090000340e061001c14051407402c10051908000c0e0035000603607038840e520200b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 355693039 1250 355691789 355691807
    0x7030903080307030506031207020a09110f0408060a0b010804030806120c04020a0c05010b010e01140304031b050102030a0c020609030a031802180906010e040c03060902010201091b050109080f0c10 86
    0x38030a03072020052200c903030b07056000300740104000c4040e00c08401a05070011707a14018410042c0d0300000390b4104000e820b02a500004071020002c010a01d05201d540b001c51156106a00c01c00d00303a070060b810401e0241c070318440d5903244030b024a0508502c1c10a0346000b4852600a024603100c1c0312602d800031441c1408000c1e095006001030015503c80d582c1040290403892a40310a45595003021140c1026611481d00380808100503104d50b10021802c90a19140390001481102400803080c0070810028502e51213422051040c0b0003d40c0c0c1e480e101c02c01e007007902c1d45014a00b00350b500040620501003c00710540e03050741403034a000100348010040b000240c80c2406000382d0844045405000b030074502c41072152180c0710503400c0300c641c0e90381c600801302d18544c02c4030302070040103001d501480018100d400480050f4014400805c5182d015260a100301c00008815440b08002460400165030005a11401071131180058800e5104040d001c64650b13061810983c814000c00858410141c0541c81e10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 355694289 1250 355693039 355693043
    0x140909011511010e0705151e1b060a021801030905030d0b24070c0b0c03250c0b0306010e1503010302010e0312270d02031002090406030f0b0105010311030f01030807030903 75
    0x1c0c410b003840798440c107171100306038001c180c0120100112020003d00001c2110700120268440307005080303480c04c1c001000c1c3c210070840b0001194080082c00c89810402800f8024018800016070350403007484015640005035100d14189420010b5510100d680401920300443d842800403c041c0600d00002e00e061003003049904180079414200700451142102910b1a580320741400c10819885080c40d0303946000300542c050043d0302c10040c1030b00d0381d80a00d04060044202d1061982130b401541d40b4021340c1141a0860525160080300f0450550b0340803840c0d41c400141952203000c1e065103a0003002d99031005020190500404c04450110303610104030019100f0b0003081c8558894868500b20000d50000d010001801149460b6940703403803424201d290507280d4000c00501c1808901c008160181d0801c3d1000395000790b540d840000459420b0146065480c400c00880710070750706000024040b02c4c44500c00c0d048844042c810044003503149048181541d4126260070f4944401c0d107811110003640d9000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 355695539 1250 355694289 355694291
    0x20c0a05011d04090b0a060e09030a03021b0f010903020c0f130b01050c0a050c0102061b070b2a0408070b03040f030e0f04020c060412020d0e120c0a080a0314090901151101 75
    0x808240685c4425180c00742d0b501d40c03001d00c40d0f5592803181e011012401d03500516503420410a00e1001d42c02507009041c29004071000c6956128654070050810018200402459445008400806074140007031030b00074004a885001d904200d1012071414030410a004210f5940e940c1004200c0c3e000b40c0c01d488121090004440c507d4002d803405544910806844038054410007000c6000c9200754080049800e00412140f400c2445903180c074460000094140c00c88014100141840b821000720402c20010180403540d660751b02d010303951171401d14160701110b03c2007014024480010312410325a046241c240c509540028040780000e0303628800b4100d241ea10510010322070020700004602031b40300341c5c0104028a03001c2c1d1000f44c02da072600c44480c10a0b0028401003560340e4146072150721040e140d10303120300b120102c140d2030010070001700903504460201e5011300e107113108040d800307144503200501100100d810700ca4850045943c0c0c80c010b000d0210410f04821101a03454414030142450140840c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 355696789 1250 355695539 355695551
    0x100608191d1e010f06150e0a21030e0a05030a021e1908011b0f180b070503130b09060a0807030e070b0a110313030f050709020a050316020c0a05011d04 66
    0x41e80400c00d0807054240b0a20b5082103c0c0b40d0000e0b4041c418282200d06c0c10070500c41c4550220800c80e0480d0321142d4440c0e00200c419070119002904281d2080314034410700942900c3c403003a04004e02800904282e4610880b03074000140140d48010800d4200f265050b5000068400c114030340a52610560f01184c1d04001c5200851565807031110780401161a094000c00415515010030000a0300c0d940f40703440411901103004654900c10079110030018103c000c00c40d0b0094071051040081c2d40241d1040c0d82c05d600104007025800000d46081000f464a030300703958504144840032035200d002e940440414841210000f40040d4040d1300440c41d50301c40c2800b50340c1243c0d15142240d146170080183c050003d45240710300350508400100710b84a900001d941400c81038035507a1840c645a024807000c60383c074007a4070000200b8413140c0c0003500880c2c195880f2a910fa14101c0c4051000902489185045510446d4410616201c82120070240d81007840c0101450401c0030072207513241070220320742e83c0040c42c00b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 355698039 1250 355696789 355696813
    0x21010e010b01140a0e1509030313090509030703021510080a050703050c190e04020f060a0e0f1017280506211207030e090f100608191d 59
    0x1d4480d4000a000b602e405030080500c0ca40c030903e9006400155010550070301c804066858405180d40302200760aa00317134a0f005001d40400d0444c0c004141c0c400c030103102c90b1010301078a1014040c00b03500c120281c0056040c5952624002d540301680c40b101184150943d0204030320a01220448024007030302c90444444e2840c0740381c465038405562206490710b0042d00c0103200c280c50700081d5103c19a24050102401900300480300200d40800390040703170300400903414185503890300000b514051070143c0311290712810a8040c8105032001d42c40141c030503100a068030a40c01d42000520140d00d4868043e03407080d40d40c1c03400a4100b11034007003040034060103140c1d840641240301e030043d038841d0340c0c25550f031038100030340c4a000e5080d030350a010000c10b1a00b080c0c0142003202c002c000601141c2d030203450040240d221142c042a03042000340c450360800a4108204060941c204400d0b100410f07940c034250146140001c0c1449000b002001c0a0a04649815a00d441844402c41c8900442c46180503106015403071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 355699289 1250 355698039 355698041
    0x7080a0903080a0f14090a2319090c03090c0303031e0516090b040503060c030a090b0f04060507020a0201080c0c070f2c01180207021c0308150a08070521010e01 70
    0x40080240014032020001105003070945c107803041008080e02041300d013800e010400078006054503084060105402030809650f9902180070150814044610096400c1130405401e482e0513400c07410505080504a000040d00303041010100c030341525000600c40034034030712942001400184d0000d030600303010500526020400303002d05181400e0b00c5040046585610072140e9003d036101d034030346c55084500011129010040195408802c04000003103c1d98103a5840044e210141e511402d26626081048100281c1e4030071a5003000e0540002c02d0301d01c1603607000810416004207118a0804081010a0b02d09404c00800015181903070f9541c02054540f8a400c2c50b0034021000d500354406005101c82d480d07541952241c0c1072b504005d43d4102d03244035801c00d10001e136200c0d400898000f04e465800715070104200c0c2c26141d0042c420740c0da0201508110344507108200494520328450601c000c0c0820440c0307000240c08044a2080d1400700c04801d030a42d210228200c2c40172500c00c0c550030b0444072001d40d001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 355700539 1250 355699289 355699307
    0x103060c022d07060801030c06031e0204080c011202090a14121905070b03070206010e130b040c050f0402120a0c090f0e0105040c030515150c1005010504060909030507080a0903080a 79
    0x10300b40448440a50321a022a440d210070b10018010680018040c00014440e4000d44004103200c0d00424405155030401012a481a0300001c0c098110b90010385456a100440c2030310851b49081c294106481c5c400001c003104000c1c030841107829030501c083c440c90b8030740b41043e808100702c0006960703401c0725000000ca003c1004403400c48007401201c402080720b40c0e024050381e003d070b601540140f525a007002d03070600c10281c01034000c141100e500308036000040c10a0900c0740c07050344030310700a902542c40d120030300c001d4210183c142031181e13005218040b0031203600785040b07600160713504000c074400d00c2030070b8152440301d46038200300c684421a040c0030480b0024a0801d0341258400d80341004601e00d40035048013103840650f00d074560082098803003c441d1038040780089080c03055003030242c41c04503040d802c140780c5041c00940d01449500c403001085189001e01c200340050010207418440340a0b103690007842e6103c2c0000090802c040441d004049900c602c607940065079101c01500d0741c4504400c400781103215 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 355701789 1250 355700539 355700623
    0x15030f020a0602060f0a0e0c090103050c042f090a0f170f07031a0402010216060c0201020f070b0702010c15060e060420040b0a051204030309050d080f0103060c02 71
    0x4038401000405910000e1450300c9400c824540c2c2e4070030b80710100c60700087c003a140c802400728810b540010602d0355803a9905d07070003180714038010010b0615013800d0009950011400300000e034244545027800c0641080c0441c40c0d0400850000c1d901c044c500c0000b280800d00c0e8004802c1001344400200d2442410240d6803911a1b0840480e4540038640c02d550340d413a096404020002441584012009000c6140f507981007481401541c0b5100112840c1d43e0504400303502c0000054a03c40b185000d65030140040c44500c0c00c420040e1103140c0c1000d2030300c0380910840a000781000003031012103040c0280740b4200c4410b210180c10038400d5564400901e5660041038404a100350b24125100d401c1080020203510040d0743c05c3c0b400c905241c80c00d440410b00c0c0d0442d202c00d00510004001007080f02030803140d114451482078500040030302807400c0062401e00b100300303440240310648041c00031220380c0d00d41d0941129844000030514103200740c0201d040070030107070365a42400510702c04040b100040e541801d075525 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 355703039 1250 355701789 355701799
    0x204120b060a0e090703080a0309141c2a031b08121305120c15010803070605010e010b0d0b010507050a0b01030213141518010303030f050a0608100c0315030f02 70
    0xb40c0b1605070580c14441600d02c0140350740405e10400004140c00c01030302d42a00b05060011350011686c507410101690010319040680003480c000340d00740c4e03407141c1903ca40d4a2525210000701d01011403080c106008213048440008016500c504040c400e440558000c258016407001e1807540780380c4000250020355550040c4070a0000207500c1d61440d0700305c00030180d00400202102d181848080f8140e07800f40407040700301c2c0940f00700c9082c00003000003801c0c000e08180008540d00c0c401130801804440040e040341c0380c042c1d00b042c010001a03900d070b42a81c0010541400000e41744502c100161351034840c06a0007001402840031500610100c0c0101c0340c1224000c5d1001860407600816203000c4501a07066045080c10010120f10b03040000f80b0740315820340001c5c020500108416440e40c1412100368411800240c41d4802003540000500070720350080d2410400340801801d01c0c001903240c1c15610103a20306290381d0140c050320325100e80c0004244141e81c80a0305003c545030b0410b0f1113030000c42041070703003c4c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 355704289 1250 355703039 355703059
    0x3190b070e040b0603060d150e0a05010b01030b0a14031c081b03060d0822170d03090215030a110301090207060e03070c0e1305030f03091b060a0e03010204120b06 71
    0x1d82880c1c0225072036008004c0c02c062950340d450007044070100303503507500b0b072221140410484016446c0c4e1240c4a4140b4000e0010105c00c030383c0d45046400d480740300c1c3c103840c10181081c0c07020149445042e00681a217541c0078105582a040301d01180c9009241102440c140341320b1003003490f490360001141405484d04a08121070a0800d02503584140300564080d900f0021880703404000c0381c111000b41406a08220006c50104c1e0581141c0d8640c44003a0030540000200456800c00d103681040300412243c014101484144c01c43d40010300e9054041641165190000001440c460076a502c48074444414800694681d611812203100a4214013811540240740c2285030305100740000c260340301180d000c040404200d0500b00101108940640800680107144000b070000030418070280c408a1581a159926031600001d6285442c1622844d8104174114400d40026900c1d0325088400c080c2190401c50318075102480070030b00a22450b1b00c40480114080808000c1182041190b400b5680403140f44040c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 355705539 1250 355704289 355704317
    0x30507020c152703070914010f06080606030618010b0d0608031312031103040b0702040609021602011b050703050105040b0603031305010c02040902040e1c020d020703020f03190b07 79
    0x4401c403240807000b00d0144600d942c502912400401c140f40d10468480d042854000403915041458020000180e11200e0031070640107694107442c0104041c00d960480c0354a8101c02a100c818041e191502426002000a5003900c40b41c8010440c0b80e00c03000c181005607034543c14400d60340c014242a40940f03040c10301c002003140b00081944c00114418070342c580b00a1512222850403001c01e10220103203d45c810002d240c0040c14806400240700341d2010030364a070f41038410013003210065000030100500c10702545401e000d000d040000b100d54207007408010f8202d445040310104268140040152207988008801c022043d04000c0c061481001c002c1040d0700c43d1807c241e120300629100c10f007569411402000198840c10004003058000f60002034040520780105040d038030b542c103144469502c0131a407001d81e41c640ca15075403000e40884c800b0781019110214025103a62140c44081d00c2009075a940704c18075a42032046801c050201070f800d04ca003240c1c070324019910400480f0280042072102c003120070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 355706789 1250 355705539 355705549
    0x30b0a0c02120702120609030403020a05040e1009330608011116061806020702030f120f070c1511010501051005030708150a0f090b040e0d0c03031407030507020c 71
    0x40380015009000894640c1c9141034040e0000d9800742e07406a52a0f10242040e9020300880f4042d0000001a581d944d0460050058038500f030340c0001d002d14902050002c3d03888002c42e40d805504503450011411121900701220700004400540555501c004104c00d40c03004498031150040c0200401488480d6031240e16a08817031580703e88034008103080090901440e01d405c7c1c1c940d0300620440340010030882c000310321070131103d050700c049402990018441056143c00c02c964011242ca5000401510440b0440021a4000c0001c580000c1002203043c804000f01181860080d100c074298220b0f012448074002002c0b011024622051546800000b103200d0428038071120603030400b922080d144d510b8890040f66805402010003807005030b11032021303850b0355400342d0300c0008290625440c522181090000000c8880e05000c481c89507180603858090030801280d540c00e41902400d0260007007403541019401750445201c02c856665001c820040f032a43c16038000d5008130690307403c4074811081d80b41408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 355708039 1250 355706789 355706801
    0x10110a08151f030207120509010210062102010c1506180b030606090603160906090c09030f1e21031a01020705190506030c1e07032316030801030b0a 65
    0x168002c1140d0031200000700990011080300c00861800501c1c00c15584c0304e11074244405d40c480c80004100040d65a80b07907074100115003000c1440c100c00c00090b460300b0405c40d00b041181002d038620511a148100a580c01100500c4405811800006030301c1240301c5400000c0125009000c154100117440c02c59040003486214800794001d4002c040341d895110030042500d000070181580751140584040307603440200300000051408402c0401c20509015030314003a6081c016141c0704001c500c000030004943c500300b003c081e50b600300e8644540c403540011b00403098910104050b185060900b2a0048840d8038024103118522076a41003003550940321050512100c00b40c0303500e00603402000140300520344400c0c00c031018100c0c0c810381000030b40e943e004207400d1740080f1400310312200c001c2194240324903030711041e0915803e0b85003801d1a214496030040c08400c1201600240782001c03240c0c0380c0c1186011011204c5070b42c0004c00c507603070800041c07400a020010901003110740c00142c1020a400b045680520 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 355709289 1250 355708039 355708081
    0x702060604050442151a0c0d0504090501120f14030903010c0e030105100302010f030b06070c12030e090108070311192310050d0e10110a08 61
    0x2414864851404010281c00064000d031903818140c5400c5043e039030200654030707403d030316540c03078036070341c05070218030402d40200301e406402d000e4140424640e80800c0c00c281d07202911004a040c174620300c1100c1c496100c5010380e404c404210301c1103841e0144080c1c2c0210180049442d4a8001e1280341c3c0c031641e103425a0440c40340010210f40ca550716220004174162405145e17901c0748001c403801c0019040000703017034413120700c2c80b4004642d244d150031b241c2e414280900b56209e401071400c1d0044600c0c683c0002d00c140309001c0c0d4081016a12040c1c141c041d5200011603000c142c0020302c001d4225100c588000e42c05800c1d0b0811408034208220100c40350400110040c12100000b01a044091940c3c55081d80d0008242d8105c1d8001902d500d0070f80203003030000c40f80c4040c1a440c11007025505040404400d02e0034000b0405101c0c0e02c20540c88210369a214003124410340d021000405c5000c0300c925150715040038040301441e01c0b410701c4110140c481e100c1e8080c1c60380c07040d1552450529246c904034040d01031611004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 355710539 1250 355709289 355709293
    0x70203190c1d01050607050a0519020306010503012a03060810020301180b0312090a05060d020a11061027090803070f110a030f05040b07030306060e032a03030c150604140702 76
    0x104658640b0001401b04c00303000742c082c1e50f10382106940d224184107091400e074280e445103181000c15820100f000901402041d8003c1106602aa000c2c0781100c075400d4052444c2c0c9613000324160118804c0e04410005c0c000741c0308540c984207140c1c014002a4100340079608a00e00e604000c046000d0203406600c40c6140c01a001c2d01c115110b114174811075902c05e1880b01e400c40d40e000c01c00212600d410004002c2402a450b0068403400c480000030310310013251b0000c0310541c1c040028020002220030300c0340112000b840710006c0c007419514840310048021204140303010300d40842041807144407001507210305042d540c1c490240c05600d40a50b120380352040d20040644c01030703032500002401550410524840e0781001c508007599081c2000d241c1d0301100048001a8680f4020004903070884038070800804d0440280c0380e060700c142c08421500703882c124030310b1005003014152107a5440900480f44418104801c1e02c1750503051a40c0c240341030340f0070340d80035002368076003520302d09040c8040300394502541709030780 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 355711789 1250 355710539 355710541
    0xb010e090901060b0f0c330a06090903030501050a0503070e16050906070606032319110a0602010509060903070c0b0d0b0d03021f020f1c02070203190c1d 67
    0xa108038100001c1068031659038515020030350b0301522004d045074100100d007490390340301244000350922601e440781d040c2d12408801004034070904003207c84410b458440d81d0030421364546a0b0600500819400310140354a45800002403562503000796041e207000307503201440389075644141680c40c0c2c801d00c10709030400d044001040b00f4071141000c0f0b4a415526252403414a8040400215207a0080500b01e440d50380d2480100108a00d11140741400040f02c2c82eaa0b03480149807044944607500c0d94180024000716100d600100030b510121101341c00f0b800b504030343c0f000f80c840d10082d000b0700e41610044514414040051900080001160b180c2607110040701d074580e01d4074001508a410243c50b81000a0320b5440450172511010003036208580250300800158400342c2170a0b4881c00c1802001c000d4900400000c2c14103074034542169240d89042200d40e0042c1c5048003d500240107a02000354507005502020f0107210001200c201e85034095800007405a5032101c0641131b168800e0a94010306180034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 355713039 1250 355711789 355711817
    0x1509030f1602060c0f07091b050309010609020d06050102060a0b010203040521031c05090f12090409020d030206040213060e01031e1401020a021005100b07050a240507030b01 76
    0x12018041c14210504508041011a40042c009400c04074201144d41d2007880c5062400008002007001007880036010010300c4035068032100c0207440c161001040c040b00001040416209500850040ca40a0740442d00c424640204001608a610410b8010301c00c16004c103555550700c1c494010318443c140c00030b6290518010a102581c499034040780c010745002d107485505403e043c0001c020000c0ba80c1c001c8104642240810011110090000902a1305c000d41000b000400060f41074850b00c28010b145032221000000a8041c180d40c4000941110417800607a04054001403424010f034400c40d0b844054000903065241142e1180c4150034810700c107c00100041005041100c0c0e248a0000b1080d1805000ea01e840e0300308a031403440100240c0d0300283c0a04199818003443d0310101044900384058103003e0004000c40d9800c0c081e00c1c013066400107510701002030070800e04d070b41940c0c410410b0401c1c03200c1860219038214010300c0141c1450038800000c1c5410302c01e11940b10001016140c2a951451030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 355714289 1250 355713039 355713067
    0xd060e070b09090a23130314090a170705040204080a0506062d010c050303040b010e0a0c0806120f07080307030305060d050a060b0f121f27020307050a17150903 70
    0x3080b20395403d0020342d258030200180a8100702d1261980640c46d1203c000180780050051801c101c1c541070b4560280311800b995a00c22a80c1d01c100d5120465017000140130824141c02d24100b40d022640c010f100240000f0040310101d501307c899401601602c11541d140001e100c0d2660522000e0750310070188070f040f40500b1141c460350760119070061402140c0c3d00d4041d501c0074610b51041e1015101001d000c40100300842c03080d811258001c010084c24401e4111440d800740071024080c015610a10b42001e4012081200300201c42035182c481e81210301290359498441c0d06c80d8030652041d00064240f20000e805410100510081c1c00c1d0300600500ca01129030321f07080024911108003a600024000010390180d5130040a102c108071410080d0003050820000c001c22000c0d15003520108900b814401c6d510303d030504109000340321000e007070303e49240a1440003d092201503040a07a10505614003c50b4103481c0e500101d4038581644d04660001c1c00c048020720341c0800c122001b01d00b562042080002400304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 355715539 1250 355714289 355714301
    0x140a0816020a050706050c2e0b100f0309020315040b0109060506090f01030b121212060f010801030201050304030302040b030c03061c150e030c0303181b01020606060a0e0d060e070b09090a 82
    0x540040c1d80b80d011410805400100e81d11170500d80110089408404012321846003840b220001c40d0504000080244054031070600500300c50149a41c07141d010055450500421181d0b82003460441c9032490103180c4501405020b01850754401c1c0303452800700386800e004040703c1140388000d00b2201e032803c0c80c20044001d811a1440705030803040407941507820760420800c0c0c119500c030520101c0d88480942c500c00e00c0010b8010086445071020400c0034805980080907241540c0d0280782446e602d5480b0b0070142c01910482c3c0c0215140c900c0002002614001d85018600582088840c0c00300891b0340744410004106101000d4144100c2101c03c80215006600c000c0303003440f90500341e0f0f0238407048004035411034004444003000c014244d244410428414060280c0c06400c44119143c2c60804000007540d036540145a503004400001e486c12000307004a80101220b00c0040c0381d0900c00c01e41d45403c0c00980700f0f00d60b007403107580318045010510b242176a040d41d4603030380050b0030a43c0c3e9a44682082003d845 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 355716789 1250 355715539 355715557
    0xf0c0a030b0a091202010605040c090b07030507050f160f0b120a1e05010306150506040b0d05040c1e06020d1d040c05121503070905061f140a0816020a05070605 70
    0x181d250f0400c000100e40320842c1040b118503400010b9450325000520007900c082c90104402c01c408080c2c2801400c10b00380a480c03a150700361920035101d4030315260803860a540014140c600b4410217021421003104030020106444000c176400c0449e81c0c0c1c904000e2614001c040820040c01000c50004d40341c80c050303601c5081c0306429081507412000c100035000c07003111001c0c0c0040d41d8403a00d031080110151140e4580b000180800c2c1e800b18501480c003040c0020138080c80700160b0705147c44802081c10300901c04c3c40344018042803141c03c04500d51075110f035580e4200511401025002d04400810f0703071030150320b0202c019003041c4140418030304a00100001800c00a00e40c5050040c240241060301071600c07c2c2c180300316130303030313031501c5d01020074041094a000007960249200b070781480c00f0414180c64a2a01d070324014450b11000b03050f1465814180c62a07200b40e49220071508002c150030152641c08000140074800840c200000f14030341d00b604a8881c08114000b4100303078440c802c20400c5a10400081484d59 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 355718039 1250 355716789 355716791
    0x70c1b05060c031206030d17071e0206060411040f051315151202030c0708030910020d020a08090a0203032d0f0a0f0f2a0b040803090f0c0a030b0a 64
    0x2600d9000052854000b0081c1c1d01d1158004555110803a03626195944c01001c100c0c020a2800305100c40244a41104c8000088050301000840c04140c051000041c1200c144a00d180301c2c41d40f8050001d685105c03c560030345c030450a0506445a0000200880e030585600512000446040105000c05070703032128a2251070903a118540c0000c18080d074171841c0a405c2c48003040455404886001340071207240d0312480042441007043c4841c1da1100070450386c070150b20501241e126640d40082d41d0425035444442c04095000085503c4021116030040030900c505458074401511030107022030395030b09001e4000350564000c0000742c03841401d207108401d841c504010000c10303003941c03490560000c1c1c00800c41034000c81c0000c47c414a801350001d502022141c480e15080803503200c1c24000030017281c2c0c0301040e0303031076803480e11a114015803c8071107403034409030403144e0781c85503090a1410002c184d0040702c0c4008940901c01040740542c50101d8142c00d8000c00a208040301811501c42d50b224140c0604200750309 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 355719289 1250 355718039 355718093
    0x3121b08120a05160c110a0603050402010212030906070e21010609180b01030204023403030501081504030f0203070c0b18010903050c010e04180302011407051c05130b010906050a0e070c 81
    0x10b942c47e09a140d02504185e07a0100381410648000fa1910640555507450f43e0001d004004a0403400503030158000120f150468a5802c0100403c003000c0c42086894480380c1651030116210304150058411520300d03000030008408500079030001d1700031520b8000c00172541c05c0010000740c641500540ba801c20340e103921050380c41c02e8800320920700501075a2240710201130300f04102459007610406005004000c0903181c00c644100b40c030041c8840003800101440076120400c07402a00c2001901d180c10b1b40441222070094603100009244e81051074124040f0140b1011441c00354417a40102003180c8d80080100089255040155100104480c0b270070782140d03890102036a00140c0040103100c0c98041e40000540b0f500e000845041070000803c000c043c4401000030a4400704c000746c90302c607201d00b4880009016128418040390301810610082c0c002d003040300c0045a4422107174040340031110205e4039620010b5941c3d60704c6010140c103c0d28403000c5041c08903180301250380c1e056402c108083c0d90344000b0326 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 355720539 1250 355719289 355719323
    0x403151d0d032004030b04031808030a05041a040f030609320c040c0c08130b030103080d050106030501030305070b150301380a03121b08120a05160c 65
    0xa07051591866400082c0c48502444500003814083e0081c000400740d10b514250071611054408100603200504004024410306801c8001c0e00071003000c1c10742201900d6031400c0c000340092250300079001d205010072200c0040c1003074100350001c0314115401480564543c52564a80f0380007000b0580c1305440120668152550000302c203c00c010510001e0742c941c080c034070485002c40c1d1900c24080c1c4001d000301d252000308100a80c00040301c00000b540500caa0383c0e2080410030f490310080e01580801e000d50300c080008001c2003c4440501501d14083c1400c04c1182e0380d400048041d0781080c807001d404501c04205210111300112100759001041102900c0341d40e44e01c80119085420b0100400da040750007100806900c1205811010f6848185083c800c80920071000659045514800240750907e4034810300c500c503010b200100300740b0f03440d07609111010243d0305000b0250740c0041c42864880c03142c0300c0041c003041c42d030348541c5002d4140c3c100b414051100d0643c0a403a00050031900317480d41c0e5000188688 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 355721789 1250 355720539 355720543
    0x21090b1909020910061710051c021206090f06060f0d02011107061d010806090a0e0a080c030406030c110a08030c041a04091d03190c1a0f07050403151d 66
    0x10281c0780714001c4c40c0f00716140043c010604910755200c0d40d00c3c052807406002115503d0541007080c2d403c11140c65030f079100d401c4d5815030300f4070010304000d4106c0b8a0030a0b40c0c0300d44001294441c4a20294016034611350341e10043c50b07454400071108158040303840000c040c81d070304000300b1803008644181044802003004003c40c5143c01c845501c400e001074840c89426065160000c0413901c40c11080c2010390303ca082980c0041e1a400d002001c00201e9513071400181e03150740f400c000844000360007100ca5a501c480c005009600ca5100e030082a000c00e0070441c5010441d40300d14100795100038900040c142ea0030082d60703205a0381d4006007401c440c2355818000880c00c142d41c0b0b205084140007418200c0e5440e07141844100c03d403600407941803107285013058070304c090362008000c44209001d00350060300c002942d140207440d0042108800f51800c503030004c00c4800450b0347c818180c082e500c003035031411080d070b600725003143e00d48aa800700410030f11010540042085694101020780d40d00141ea030440c1e1954410400c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 355723039 1250 355721789 355721791
    0x6120f02030a0b010e060702011205040602070c06050d0c080c070b09030c100605120d1b0c030f0b0405010b03030910050306030a05010e250b1b0c0301050721090b19090209 75
    0x10b5441c40d990000900d0f1580c200240840c8450241c44060420f038180c0c001a03c0d14000150b454039594684000408100459040750b44172070384107008810040e05c4190043c40c039005145500003003032071b1102c0030051340d00070744141d4421400b0743e03c001d2411a07a561004a41c01000d061f40245110621413601c5100c010300003ca01140003100000d062482c14040160b920050340401c00250800828130382c2165001517403801d045021007202c48403850616011030188401c0d40b001c1c1040c80d0820f4004100018040003e0140340540000e10202200804041d201d12520700c5195011a00000007001c050080d0041c55204400405a40300381c2d0b00384d1141800d41ea4040c00c8d981e1150441c4072286a05030701780003000c440d00c8441c080154a941040c03c1512244a400611b400001c0203c0c281b64003c0002c02000c034126902800038481800c041e0350103442d80211008090b03440c4400301611000100c1482208541341d0444c00800d003a4039241c000984140c0c090043c007078250345507004400981c0720403602c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 355724289 1250 355723039 355723051
    0x3020d15060c0611030106050a2307140c040605090711010e0f0706090f081005041122060501020307050a0b04020604031205120c07020d03051b071805090a0b0106120f0203 75
    0x110500101c0c1c0f40081c101c074001c0c003902080c541c0030f02c01442120740c010b0507600350b1503642c145150303882400743c8081112007400c522062609000594401000320a42c50800003017a88021102e04061440c01c100079034009008042d0003035211070000e00f0359440344040021008140c0000600c0601c2c0e00e49241c140141c5007010a11940110f00030802141c0c48007440000300700c01d0700304680c032a06081b0044d403110711410002c0c040c43e842c0c1c000b10b000d0000000b0009400c41006111030110280c0524882c1c3c4401800c49151100d440e20500003003550010048030142a84040030306641485a50790841180c806481660458010b01000c00011803450b4100545001078886a0300d0315404114140c4000c1c0043c01e4445018042c070841005840f4546899103807549420a1620b90704107110904407124174000c0740c00c0c10720500d01c00041c080d41c6040302e10030058042c403050002d9941c010049980d00801b0320000e2038030a0407401040103610030180c0380000c02d030000021601424405182c4280d030815a10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 355725539 1250 355724289 355724297
    0xf0408100b0f010c08070807060b030616090f050612040c0b0a05070219031a06010e060a2105090304091802061b061b160f0507120b0606030c0a03020d1506 68
    0x741056030710340030042041041091a200c040c4154959400d02c441c062600020100c540110301101001810381104203041d00181c100d075002e15065103480c800300380c00501e10012a00e90a40030459544680384e03c010b40b000a0500c80c900140c0e1989108500d2009005036061070540c5004211010218010301451120350341d0503482d85105d004100100544c4900d00700c0001c0b0b41201003000904c076084468100d00601200080c80e510b5500586042da540311141c0d60000c000517070400701c1500060f003242d1183d030a8020000c41c9002c20301d807404440b03050b1441647caa009210070042da00090300f10f403600d0506001c182c41206180e6000c12030980106640200042903d88461030103003003001001c0c1d00081c01c5031080c0509440c0c1c10100864450f02c5e0b041d1b40d00b00000d822140501002c5601d0320074403540311040b2040559a110a0140003a0710001100c80000382c00c0822410300e40a03017600e000e5545000d00e240f404240c40d10640003507004040d50f606c2180ca440141d40700703001018941d8003c02d02515 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 355726789 1250 355725539 355725551
    0xf0c070335040614010608070e01030b060c0703030305011a090603150409120806010c0c35060106111c030506130509030903010c0201020c0c0f1203030a02040f0603090201140f040810 80
    0x90941c003950780c0702803031341c00c206040001081803d5124161a42103c0ca50414005c1c029072140103c010309501c1c40343d00d400c1500002c54186003400041d07494101d03402941e08115590322251010005078110440700c440f05000c1c0103801c60342c43e007031006542155082a006030841800d4000c14240e90440b002a41c1c8070807448034174801e2940141c015940850b003445d102e004190b242d42d803202c114816019035140320001001c0c9002c81c4103681350a80380b0503440710042d0141c8030701c5000e080c0c1e41c540901800b80042c0c0c050901003400c880004010388503a5011640358054610814110700400006100039801446d40900c3e113044501c0d0b100d070a0107443d90743c002d10350300c540c141d040c113094400d4080464110f82c8100410300c4a0003012030321803201141216500c8641d4490350008061113803200c541c0403940000000c1c4152030348158010012609681c0c003035001560390f0720041d4100d1382d051b40007a001c1640c0303882c601c10b4888140c00a0650703007654083c1a0070643c68000892504444084010705690b41d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 355728039 1250 355726789 355726793
    0x80702250e1608010902090402040305060f0403030e07080a17040b0c01050604050705091507140d0e03073201180305010b0901051903030c06060e0c09090f0c07033504 73
    0x9160558020607038040d80715460b1400c94010f000400500c83d103241941e021882c5000c680d0340e03804039002150410304032403680c01c00350000103030300300c090300e044012a00d41108071458407401700b0f20718125550300e406041110300c1a1513512241703041c101503101e114070030800403510110101c041c091803802d41d400001c1c113182c01d0041c4070031654058010303414032a0910201a00c0d84c2e0303031150f00300101c4029852649541280c944601c21000b1082c14a206020b0383c018200e00d50f40c451125007038030004408440c2c1c415590040340d1003010a6035900001d00c1046003400d11503001c100880d030052203062403c05c5101e080103011500341c0d1078641086030141d448000720140c9107461038846000d828122034800d800300911183d002000f990788401403c0c8507414110740240406580094001c01210329030090310701d00101c85103550703840f420301c043c0b0906010b0003107540c1850141d145071050714507a03892803801e5500e072000c0e2501d0702c040c095400488840c4091140301c00c080c00b0448284518001004401d00f414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 355729289 1250 355728039 355728059
    0xc030703021005010b070f06021303080c014205030d020c1306060e1c0503030406051609030b130c0b0406020a03021b1804140616030b01081608070225 66
    0x400b01401d039040c2001031005020703e1040b1203a495200c0300c0460811303a03c1c500030010b03004003550040b150001040000a00507201c00511403400084000c201d140800803c094014a12840780041403503601c400e0401204002da08d50655114500201d107140d5a60001030316190064000d480160410003590f0880d0406000a8003110781000c8240401800d10000811318010b25504502c29080506115080c510252078074041e41d030414143d076500d14090801001810003910a1159458102c4020308081d129004d8075042c1c070307800681d15a4944034000400d03017507044035006640e40c000411340000c41d0f00d20580100010280768000e000714100d5414064101014500300c035540710025030420407030303554804800c51000030602c0340010648441c20491100a0b20315941c9505104842c1444008000484c508090348042c0d9414000c640720700004460810040d40e00e665294241400d5840c130a004080066000125204480103191440c943c420101c90b01303101044000d030480c205001c42540c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 355730539 1250 355729289 355729303
    0x1a010311070210030b0616110a0e040c030303020307020c041a010206060312041206060b2706070f020f06090a1d070318021302041203030e0f0c06031801060b0c03070302 74
    0x20001200d07092803402d4000c550009806070302e0768200b59654480100580d509410b950103040341c18240c00406d1502d00d84944148100c40000740300c1d48030110002004100c0310010f03071040d40d02c104d00480031403555034140c010707403c05480b020650141c0c001350f622584803846a003004850349508840c1d907402000003e8100361014128500039000b00720702030040404201142c0440384542c95024003420f4606002005145980100d4048440025951406402c2802c24000200001400c01c21050031008011280c82010030040000f00002e071160007501e05490800704401c3e003d0b1125107484603500010b0380e00761007600110305a40302181000e00d00c40500c403103980c1c0000c590038200300d440141d501a80c42c0c05100c0310000d108a910525944481603250150303030080c030390039240c0d030071025640c038016002d428400d100300098410414003d40790a000100080c5615015000034130319103a031198600c1d002540c500720005036480340000601c14241320f008000c0010088051078681d81513140003410000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 355731789 1250 355730539 355730561
    0x60402090604090519240b0f2209060b041803030b0607020a141302030702240c030c1b0706030f0f0b01080106050d1b0906080a02071104020d0f1a0103 66
    0x40b0305144400011000581410302c2c6489502d02c0507082000d250045c6006d04c0c1c41a0310038243c1c03c80f4500302e011a0141c021034500c0790111500203407082e034102840b040b41c0e100c0c2401800e84032060801103400701c040c0c2c00007000c035000d03100105a10314444082404d440000c05084c03140c00e01c15030098141a854812031001d04000c450542c5004503580004144880c5070003030036100d1400d2819171115603212441c40c0403d1480000554603807400320303006034407840740e01b01e000158013502540b00659044038480030720682c481200303d07055807250070025000f03411088604d000c181c83c6a80050301c5000400044005003415600422426199910181070701c02031440d0700c104a04016103450f860ba0003c401b40e064480e03500d42580c580c07404803c1d0070098264201c1c2c1543d180d044083c4281915808083c3c0c10a80d242a1034615564031a08600002c0744107042010300b1450100841c0751302417905800038142e00d0003a0102103005601c140ea01d10498003940d040a201082c1d1015210386942c0600442a240c8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 355733039 1250 355731789 355731791
    0x2060712060308091309060e0105102909030304090f0b0f061e0c031b0708010c021209100e041812020c1c03030603080d02130909031e050417060402090604 68
    0x6850740d07030f40b45640d0051040e8184078440c00c542e40808048568815640103030040014000d0910301c40b000c0c3d000344001e84149805119240c40032980e0760214401c0320190208250032075440110b00c1540300d51782c04c00740c00564580400c000c00a417400b00c0707000e040001a0410300016402440034200410203809203102d602806080c8050144042c904220f020011110384901d69200c40c840011420b41c0700e00100000c0c0e10700601004140040c00040c42000da03004080208202d0b002c6d010166591074043d00041001c807000c121003011030a00080d030b58071085282c1424001310038100c0020f0256080e01c43c100503089400c04038075041c0b0071005481c14401b189800940f40f039105d08000b2540303100d00802100000c0d020300040d2300030144690720080045401c190555140d03041102d402c0043d50066448105248daa000c1c0401c00740d40d588500b00311b0a5064840040d08440e03c10040f83c46c0c030001040c1c4041c040280300c0081c1300c00d001220300301820346903000343c201441e10384100300000a01420180c000c1d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 355734289 1250 355733039 355733051
    0x20606130c05070b0c0903150103020306060f0a1a0f0c161719111518030c10180b0d02040e0901050c0306060c071805090123181c02060712 61
    0x1d94000045840300780c2c0100c05011036581d100c00110b201d20410100c650140300b104804800e02c1c1d1030240f00c1c0c6c142ca10071003d80e40261a031004000da04404030300c03002c0d07205481d003104001c0b0301e081c10281c500b40960300c0d00543c2060395025088072284c11004042c5040d80110100002015852541c080540420382003011400f1014010541e15032940b041402940744c1c041c8620107100ac1003040343e05c966002042c1c01c0060f0200d22240031160045e51459494146803070f1005170918020035081c9616601801c55903010f20340032022507500070500038021120302081000b00310b0301d4100b001400814900d001c0135a440d03103003407084210380000416446041c0d00d0038080c4400c4483c0d8900300c1e42c00c2901200e003140c5960001040f24240403640e4403400b54003503a415101c0c1510581d401c00c0744552030100081245145a03805044181c408800c0d042214803c400044d4800c0844044909614100001c482c48201a40702140420040f4213101000d030b800b01d01000b19a541c000742203160901c11481c24413030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 355735539 1250 355734289 355734311
    0x31e20150c07050c030105011d0c0a050d0c0507140303060a0f0e070c0c0b0a120c0201020304020d0b07170c130b0f182b12030c08130201020304031202060613 69
    0x204600160001d202400005880340034060304115080c03d04400900802465a580c4c58403c0d440360780200903000c0c40108000500b80f070381844103a8a4103a002d1711402d1400c040340c031560307000f0009000c092042c0310007400841d02144036074805600501d5000010741c0e90f4140301041001c100d89541c0046101e403030441c01480240910b451054000c02d903810081d884000d41d00d03001ea5030420721342000e00c282c800400d44143c0c42c1d074040b0601c0715200e0350303403000c0140728080f2500701e00340d102c1101c0203074104002442401c00104040c000750f42c00017041c0380000030450a01c01e0315078030220035200e85008070b60105401c407890500c00f400c80000c00401c80d03500c2c80d084000103810403074018440c82c03000520351a43da882440c1c690b16414840b0508000e0018214002e803004e031000c40b81158010b98610b01180c0300e00044600a00c5188038401d0f003900d0f140760550710582409425420b40324100e04600003440000002003266000c1d4450080c00d0700542120314006007401440315800406a41c40d504001103701 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 355736789 1250 355735539 355735573
    0xc141014131a09031c0504021309032f070e1806010303020a03031526010b0f0f12011103040b0702011a09011412031605061b09060304031e20 62
    0x144403214482000c2280e035006a002d0031340c010880e101c180c8150b19a00d1100c3c103002c6031720032889584202c51b2088400d8101c2d071620100d8101d0800200400c4c1100d0080084107064480741034207142c41d002aa403559444004c55007400010b0b484541d241c0d49540c14010700d18089442600181490002003200f9032450702e000f5560380c20380d00050207150340d5031001d2044819044400000d494913803041c20703280a42108604503c1c22a60b0003a800d540703040130342c1c1605d290046240c1c0400000070801d40404468008001c1405103085500019650344e41e07034210341046c0e01000c0c5200301c0c06940c000c01c0925041c24040d0035280c980180b40e440090700070300c00c101642c1c0d940186040d903080e222881c3c0c0701c0340104007088a20075024060b51a511010031440000e5883e5020403a41078440d805a50b40b42d1288031040752a40508034a0703840a0605000012090901d0005141e101d0b009160103221109003000c3d02407400030004e03601d8001402d510940610001d0141e81540a14091004112000c0340d800545 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 355738039 1250 355736789 355736813
    0x150703080c0c032a190605070e1e010e0310061e120f030219120905060306030a120c060f09111008060f0a030602130905070c0f02010c14101413 63
    0xc400780c0030f01d0903070740218140c02c4e510107a51061101200c03420862100c40400d00504100c00700d03802424800003401c040d00c1181910300007040541460503401032100b403800c4000c86040480d040000405000015940c02c00c00804445158440058203509115800030600c4036501c0030b559080b2040410083c44910940c1103034455007121881030101c400d450201d080483c0200c802403120a1403111000b4004a220a80b908003c00e80718041c102d0303a142e06020480c04101c030880d0b0b050b0400066080480c0110014101c0024103150001004d4103a03030340c14085420303580b5074180305580c2d42800b6041200c1c00c1d264a68540045500405200d90000c0083c0f240781e0042015002d810342100086a9840c0da03200200030f103504c04419529256083d05505103000b1a1080aa00904240c00b00750481d014101b04580e9980001400c6030345107164005403a141c1c0407280499290108409c5607a20440074440d01056201202010600500c0c0403066015a40003900d00c1c2c4144c10304a106a00080f6000d00c14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 355739289 1250 355738039 355738057
    0xd0605010e06030c0603130f08040320040605100816050f040308070c050f0d110f03030c0303060a0b0a12021c060e0a05151c060e0a03021f05010b0a030b0f150703080c0c03 75
    0x8d5100502071404140c0ea01071540f00a03c1e80030742000721200c050305410725411440090303408000c956901c504002c2c90394010000324010810640c08141c0c20002c1c01d610007040b0045040c290318000041801600541c41984142c409203400305461040011010f0844010682210001001c40d0030328001034414000800003007500c4404d00036401d1503100c42e10462031410380201540c6d124404104441c1c1c0f04c2c0d0040b030380d0500c10540c3d0500810380242000030b407240861555500b1140060040841d4004d5002c80c0710800b404408600042a1007a20f000f01030140c071042240b0341081c100344200e1002d444001d042400d426080c1415806c01d0f840b83c402e005030180400c20410601905810000300420042c01e01281501079040010305050300001c0489484400100030782c2e580400001d01401c4810078001d030081c92100708402403406200390400c20009070020040300201e0f004e00001000707a0031106000c07000c4a00404d8000615400201d469032100d40038520f00d14116007000034a0700d9120325508 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 355740539 1250 355739289 355739303
    0xd081f090b1206010b04030605060a080a1b0b0d0e16060f051614030405010f080601020304060e3c0103110409050403090b0d0b0909010e06150d0605010e06030c060313 73
    0x10320034680d0b410310380c1d42002034807400f502c0c842c1d611450040c0c041e5005010030349159080c030000c54040e090141d08281141c0000014001c803114580d106520341100c50481000929510804070385034003100024810b044002d080040d400316403184050800c0c14105044050724059a410020360360004045d000051251400994601e0034400c05c40000070100405440c8100710745032410021400802401524800d8903000704041c0c030303487c080300c0300003003207450b9401030f00103200800445005600480039688000c0c00901a103060111542c0e100e82400410000f65807401666030805142202d0034401c00e0342842c05209000540c00c1000691086206014034242c1c0c4200042c01d043c0700303025000260000a4499988101b40140031002d00040c1000d01d00c40d42108000c10760040b0b052144c0c02c0c50780f5580002d080241c0d944c800f07017400c2108805440d604015040c02140020318507105983c040c1c100040c0d19881810312400b070615180d2001c29003030044800f00240848009940135620180da0b105075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 355741789 1250 355740539 355740551
    0x50a0308091906090b060901180c050415080601031d070b0a020a02060a030f0b041a0d17070c0f0f030b0c0702010507061a13050105060f0c0102040f03050d081f09 71
    0x10782140b4022840020720b18007107089041e0300400c812a080b0140072401800d8800250f2504400c00888a0086c4500c0030080480032801d4046080c070740100000703840354280315003816510049400441c002c2030545001514240811070f1039a01440b03100b0801c100d0010300490000300d60b07440c070b075145a01d0007070720303484040810101c01c280e01c200311030903d1a50181c5459203410041a004e005000b142c10712000c11801c04003080c0c1030307092038410b0040c0c0070045083c00049030354060511442c000e4500c41606c0c4c10040c800c030300181c014403000416205101d003000910003407034a0700700403012402c0d401c9185900054502040810f0070f03211910740283d41d01013001d036560711303030701c010707140752043c018010000e03820810440010f404e10001032584403c00d642074080149141c100408a5130240160740d401542030040e00051070450010303080034464203000503e1b00c0d446420362006054250300455140e800900c0c988506507105181c00d810006c041031440c0d04125201038000e02c50958011140d2881c0d641d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 355743039 1250 355741789 355741801
    0x3040b2d040639050a060e01021e03040c1e05030715052b1a09060a0803030a18060e012414010e03032101140d020904030c020a03061802100c050a0308 66
    0x1099030044035542100350f2510711114686180c403503911070801c1e5151494070400100d042010b00848034440d01c1c0340d44004880c100392070491341715000070b4401e85030141c0e10b4901203403000d00b1b85240c0c006222201014607140d4608400c00d031402c1a660001400f04041c0928500800c0c0c20805030755024588501104a0302d0402d06090722204c45206280c510f031b824003a40000562440e145a810490266603e1405030341c2d0034140b107400c0c100c078417078200c3c0c0368010000120018407a600100c0110322054000c4010620764039410280c9010041601490b5556041328442d1f41d01c104400403580c81200703d805095151240c507000321a2500540780c14000f1014500619075811710494015009989180d4280208104201c003200401d00400680041c501d00c51403047c9880c04180e510198002c0c0709445590329030350701b21348007078013400206c0c1c20045542000c00000c0c09400740c180040d82d09404007020010710b0041044240d032181c0ca03902400702ea10300301b20203e04040380300b51512b90503042062560310382c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 355744289 1250 355743039 355743107
    0x1d0114060c01020f1b06090a060e0705040912080f0f1b160b01080708010e060c0a03060f0b1210050f01030509070503010c050d050f0c03130503040b2d0406 68
    0x70040c0c0c1005520002e18901800704030b1024212104121038855140342d859100304e60f48002c152420310407907004a40c40d4000039a83d41040310b540c4040d400792400e0507a26070102c1d0540d820344100301c0340f01c420b0105160303c1030361102c111644004c0e81d0042d12243d04000e507060104020160585503118103500f0318034041c0381c0300402c440c05c0c01040300002e00c1c50f41030790502c650000c03020300607240c40e4051140002008101401a5080c1007940d40190149444e0f21134000100d9000351000018140c5030400003c1ca0300f188195030008001e108162696412520807070300c5400d00041c806140c80d840b0150611040e114201e6401c918507080c20f0002d030945801c20788928140f00f45e444568190300b002001031125610201510400c0742c41b144c10b101c9034861900c446500d5108582c003081c2c00c1c2d0140001202a000d10141204240c024000d4070720301512490000442d074842c1c0c080c140124410600c0900c60101000304210790707880c00307079440d01305400c01e03c004102e0f03100701d0503001c81140d005102c0030445e171007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 355745539 1250 355744289 355744297
    0x60d060c0c02090c07030e031b0d02030c120d030506040606050d020d1d011a1806130603060c0c02030c03010902010522150807080f280e06010314071d011406 69
    0xb80103c0007460030259141c1580e100d990100c0000e84118480007042c00c0005d054003034800146600e600d1100585c080c071488591400c2c080c2c0e410301c41d100c1c0c20252900c0d00003010314807550003c05040c401c0d0b81541c015080d110301420441c011407601030104469039001050b07a86d10643ca41001d03a035400f5007c00c02003d00a8bd0140b0303070440c4101c1825802d855030541c40100c9094002e92180d0310080603400b08009102e21400380b017030062380c842c0018668600390540718501400040000380c280e40725100c5c10112041003201d000410303500041038040d898108200d4a104e0300440090000d90001c3d0f0000341103000d80d01c001c0c80d481040b40b580104841e090142c40010300f105882c15613031074024180081c2900e00c07d9802e000481c50100c04107003240d0114130b5081c071030040ca00c1c218803450708044001d0170b0562408074102d0041d507281d10100c003000301030060500a600905001000c0c20b40140f49a0803e1050f40c45655005902c607444c0072110b0815210364110341080402041d028601300105555201d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 355746789 1250 355745539 355745543
    0x60304080a0c0c06020f10140c1b2a03010903140901121b0e09220606080d08040b07030c020c0411040305060109093e01030b030312040b06030105060d060c0c 69
    0xe1010b0003044ca00d03800074102102c075042c90b00301e881507640000d1000459420341944402020310000180018035824024a1f020306ca40320100185c82c40c80e07c4803401c0c0540c8120043d1011521411152040c01e48040f40d4080c00c011802008050100ea80140c48603071141001c1c55901302c085070801240c0e000301502c000c024044001400313006018080050f20450345424007000c20183d0340004803604200980324442c021900b03c0e040c41030a8000a051000c0c4050030440341c280e11081c1c041043c810500c0b4910511441e500c9280f0a4203040c50861481000180090f04140c036120803080c1403030f80000c1019a41c01c0541740041c00b02e51100650005120307603040544507110b00400040e5050250340102e05040c003030800300c81c159a01c00700d80108000d01101c1c00358034428040032021f415040c2c000041c13240c841410b000840400240c08a415234101010042c0d51102c040304000c00d001c0345034200c1e6030003441100204403d103480c800081c6801d86803040030300903560704ca10b204419070240500d10035141e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 355748039 1250 355746789 355746803
    0x1020c060c06221e060207080c06060108060418080304230f100513060b0415060c060f060321050f041412060105060301090b130c0503101202060304080a0c 68
    0x20354000031540c0d54070b03064403e14102646400401004007900c2c900c400000e40c004e901204200340740e806050760010702042500c40c540d00700681e40c0051080001000c4006800018001610704140003600e003c8001301464095418009182e071031102c0c60040828682e80403c600ba165201d82c14030644116140c4a0a222003580b00380c0760440f91400600c000c04201800b041350b014109030708070fa0080e40d2081c0e07840c125030158950060002125070b000307004904030261000481062072006400488129800b602c042400c10842e030061222901502585840000040c85058510350355100c480c02080c8500150b25403403001c104800c0c0c4a030701144d041c5403090300c07243c0e1120380302e030750032542c101800c04960f1091040420b50004100e010840c18101d580003048282180c1ca051401405802000d0342c442d840010700401844200c4144a142e1104010742c2d9002d0300c1c1e10b000081d00c03480d00da540d000400c4054802c2d19542c0181d072540126175105901400f0380c0e854101d490029645204240c100504503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 355749289 1250 355748039 355748047
    0x702090a0e0601120503180103021606020d110711060a11010c09090c0e13020d0b090a060306050f0408030a0f14042d0c03080c120313030f05090906010c0201020c06 72
    0x2610054000c5103000281e6030690340542d903900701484444071010801480c41d002440140c3c180018280605071808040c1000b61a00702c81c6070300311121403014141200c21642c040380c05203a10710140b155800600c00c1f24406868000c59445400010b005001d10a114410000b031001c40c0c0741c03050b40481c40c0c04641000a010410a05c40081d0940000d8018000348600d0071190341e0043c0c1c07259490b4843c42002403d00f4401c00060ba0703a0708042d503c01c440300200e060f1100d0301800c441d210454a00e1090350940400541c150130351030a201585e4002d407491803c0c000440921001c01c0640741181d40151816200080c2822107200c0e2130054200e00d104481122954030400c8140450b07280ca98144a1001d01e20149900600c00b10b10000030304140e010381922200441800010b564500800c2102140c0f0200c90195150789050f42c07956100300e40c100480320003c05a0810540c1001441411a0fa01d0a0490401c0340000c0441e142000040400b81005140744016055900a01142c0d007603000c050040c50b51 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 355750539 1250 355749289 355749301
    0x60f01030b0904110f0f010813050331060206061509030106050604091d070602100504140109031110020f0306092a09010e0604030302060408030726161706100302070209 74
    0x4800c4e1072011241c0221320382609641240342c4134072120101718050711041c819455980c3e4403613120b0740c4280d00b00c589200400410520583e003805110307481000d942401045119420110131010207036001c181554001d000784001540c80c40000902c0c00c2507220003640324010071000a014001039440a908103070700280104001c0304680003080c03100d400380c82510b40074011109040e907520161043c0130060b04005c1006400250340e07046260014015003d0000d00304403003103614210790594100f10b0126807071881d03342068000b03101c000294a00c5000031424120300300c41c41d840510000303001a1065280b280001c0d0030600e0026092202f1440c254401040b100c00c00221200c0e030300a103016404107460282c40d08544c981407080b03074240d0ba450383c040e10b520340b5140d5036081c55400160014041c096a41c0c150404074030074000019007802c141500403114203140814a14201c0020386d50300800c080c040041a074180301b80107440d040b070000d42d804101d6860520045000b03009890000f54400d43c20000e1080e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 355751789 1250 355750539 355750553
    0x10f1214150d0201080a090302160f0806011e03060207210801052e0c030c0f0303050106120203100b1c050a0c020c030d020d080c1902010510060c0209060f01030b0904 73
    0x100c0752505600310604141d5003410064128078441000b40001c0040c0b001422000701034101005040c0310380115444110450f5800c0e1808d0303401d402007641403c00380e800b0450700200700690350041c00c1c0d03c100000e54800c07041903640c000d07a8a0001800141c0c00140d100e0412501c45030b0000000e0200c1d405450700b03242c00700000d00501080c0305040c030901c408102071440c1d214a80e0300350b80081d40d5019101142842050680b54014040c500f078090001c040c00f5103000c5a401848400710500c650381c0020b55604019000e0f0115039500403003c1d05500c14001c04c5501c03096184003000303407002e6400007a100c14172890248840b642e05036403949020300300820b11540c8006900700b24040165502038400305400c90050560368070907a4135100060b1f10916441084901504050b0f4004852071121071920040b41c40060550106505420040c5c1d52041003026421000203c034002d0715444c0350403094491039400040d800d2001400a41c03060817400d0710402642c1c003070343c40080c1204001d07000303413011302c0c2a040c0a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 355753039 1250 355751789 355751791
    0x2d040201120203130606050a080303040f060905031210060f020c040e0c03030c070509070315030f1a070c030914031203060d0f12030605010e0d0b04110619020705100e010f1214 77
    0xc80b05c0c1c1c14000041020b2928015110544292070021411617583d0303250f211110030081da0903030b506036450140d640822000d20007000c1400b1035480264242c2001c0b000e0444000c2a5800402008803414402c1004d0380d000c0f40015140c2012100071640792803001c04242000710004078650b0600c40001e007240180e00100700101200c40843c2c10411944e511482a410f540f607180ca401a84090504180006040c4c2b01024502c503000d103402050300c810300d6a5140245070240d815901144482d9203200c00c0540c44542c000c003414400d141e00b128003031703010046a07a90b40414002210007a0210002e0b40035116440e00c061005c0c0c0103801800041000c1c14140d072031200300c11110f80040c1c1020b10104080d4000c400314070769031001601c41c40b0f107880b8a0312014206c00020b4401c48900a640030748105c1c0313907949000b42c0351080b9042d080d003940101c41030020b403904083d644514041e80003c0c0000702c0340ea401c803240481c0d4060a081ca4165107a200c2c8045840c1c01000d21040061490400c4600d40e140c901c0c4001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 355754289 1250 355753039 355753043
    0x170a05071406070219120b090d0e01020d0e04091b0f060c02030c010f031404150b03150109090c081218030f0d03111b0c01082d04020112020313 63
    0x40c400c52601d801c08075401c15920403201c0e422040c100320690050400320074500c021060725141c2001c1548030340000400c103c1e620fa05603425041d007024850403000500000b42d045850342460f104544441e00041d407034543d80c2e9800340910540408001c031a407525000403811651041c0c141c0d01d00c42c1d00b4500c2852070811402040050b498a0f5030200c0c50b1802110b018051a8005004001d0030132070f000116004104c0d480214200340d00d42d00205602c11240150b507000758840c207078015861814045503c100c0c0d00b000002c501c02c0e40b000ca1007501c0e003880100860305641c000340c00401d4070803d90900c04441c840b281d0040c04a84101600c2503881244c0401410340c90011240006601500d0010140c4d181d0804020b0085a0400b02c86441010300a0b84480481c1140401c05400e0861105003c11020b02401a008594100b80c1005401d5030348000700603072004000c1c070b10751000440e07440f000701c00714540b00c0c18585000d45a80030a065a01600090000e0f5140002c10365681c0380950501012140d04402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 355755395 1106 355754289 355754293
    0x212010f1a07030e10030f0c020a02090a0218100905090c04150e0321030609070c050a060515040513031403091f060e16080a091a0a06170a05 62
    0xa9241700c500e141e1000100c142c0d00d1110507064030095070030741d001c5402c40e02609006a540c0104650403003085800142c585609001001500315101e80c0c0aa1100d401c142c0c520310705901003444001c0da0801e54031244191950411900503015038090b128104887c404207080d03072403080a08080f0100c004046131034002000c16400f00c0c1036003000d0901070390100002000601e0034480103454001e40603140ac0c420b0070400d03444458840307088070310040a031510b90004c20b4295100301400420407030300820401041c2410303100000e01c0004000b0440100c1c01b2030220016840c0c2c207009607440307004c4507400b8050141481d0390052004010bc101e45042d0b079916103011480b44c61411500f88144502060804523556014011b040520300800003150542040750440c0000e9a01e50710034000004d90129900c01c0c1c07a40d040110141489070000617078141018550122846c000500f4001c003806281 = true := by decide +kernel

theorem cover : BRFrame.Cov 355575539 355755395 := by
  have h0 := BRFrame.cov_init 355575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 355575539 ≤ n) (h2 : n < 355755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
