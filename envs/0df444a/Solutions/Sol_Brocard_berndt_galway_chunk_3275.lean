-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3275
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:11:04.339166+00:00
-- url     : https://prove2.me/submissions/1debb054-f4b1-4f55-8e02-e49531773554

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 588848920 ≤ n < 589028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 588850170 1250 588848920 588848933
    0x10902030706032a2604150b0108040f030201020706090809031605030a02010c05010b0d030c0c0801090305121b0a030c12110406050a17010311030114090c01140405060d0b1c110d 78
    0x240294480380390030441801c640c4052103a405ea024a0003403401c1c410041d48000d1240030394280e41440c50108040001190005210401985c215030003840010b0412010384d0320041034031030400b001e51f02000080b4070340e5460300e01401240b40d0008050861074900c1d00e0580482e888504034080641031040300c1030000305001e001c1d00090800200202040c401c460b55140240ca00103034400103036201c43c10002e007c10254014032652080c507030181c071107c0c2402c0307003c078810190303810082480722480c03241c0d680c18685825000c080c0080b4000d0f620089400586110010103041039540003004040c2843e0340400044400012101074482ca0302d00780d0b99403006624140c0700013100c80101489440151300000601c400c002c442c1800c000110004c0c485044022402c0f00003900c151560045c42c2c0102101e0709181d07018650700c25680140003151b500b403555940020769581c0105080d58038a80c2c03105001030292400d00b0303004170045c461940081020307201e074403240401d40a004005000300d1241c054081400324 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 588851420 1250 588850170 588850187
    0xb030f0601030b044a01060609060c0c03060504050a06050a0518070b07030302070c12050102070c080a0b0a0c091208030f0f0c042102060705150c040302060904020307051308010902030706032a 84
    0x4e205e4801d20b0140c44c10000c25000741280c2c484e0030f001401c5998081460382c820b030311407070000d900152242c0b207050035a00c841c8010007020f04100c1d01031240001d1040000c0c1d82d4001c1500c1003100d83c20001c0c1d00d1038200020b40e0078003a182d50104164100903800d1280314004402e5415140d010315005854070f0303d502e03184036000f209400c101c200c11b0b49511200200a815002449443d120381126560159520710980c0d490310300080081c4041c070040000b03160310030280c0c00a184200706203031803214580d80c1c408281c805090284141d070912000010030030806080b00c0c103160014400ba066a6482c03030001c0016965010794040c46a580c0004045a104e194014558054168008111039600e1b05103181003a0340ba40056817031020000304800051442000005580817290040c040e1454480001e003003200031351008142c1ca0500405009001e8000902450f460140504500004604d215401014a0400d040d8801410141042a000612903440b03200020802241070346080b00d00b00440162144807 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 588852670 1250 588851420 588851531
    0xc0703022d0f0a0c0b03370c030e011104050d0f02010201110a110601140d080c030d0513060609021603031a06180a0b09180703060b030f0601030b04 65
    0x8a4003162200410000c140f003400280b04060b9410125a111800304090104075a20090140300c0600020502400001321040e018840411042007204080300f0013124428010305c0002640c4685d2841041404d2140784500c0b1422014203040602d8003002400c0c01c10002001009941030000401c00c5900035000044101481a001034480d02101c0c0700130420202d16060b01d010748282d8000041081d08120701008a0300301070150000c08000707456129565002a9140f4200d1008002c0c608072080c0b203204050083c29201110007443c006420320303d064072130030b030080c500b558410400b01110340802c0c0000310301644d06d820003244407480b42c3c885186c020703445c482c1c29400540001d1200c40c41840c078a00d14070454000c40f03411140c42e45034420108140110240d19800c000f07600580d1140e102c0e4030702c100b54000389a01d004a800d42d1680901d200c150420b9940030001941042405500d40c1c25000d0794054040c00c0d2410808550f40484421401540500d60061071032000114000101e80c1c429068076007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 588853920 1250 588852670 588852673
    0x206031b070c0e040201021005060a052202072609090402090a0b04050f01090c02030702060a2714010314100e0c0f0301120c050d05060c2107020601030b0c0703022d 72
    0x15595102500f811038202c60890044c001c528504540c0781c0c6a201c5c850003040c01410b80c2c1e0100e801c003c1070040c47c0042c3d0103003443c000405050600d070558240014030741d1520541d61100c0b5441641d405084581c040302e006910b0000c207000c07865550f20341d1956164001e0301102ca43c24151241c1d44013030028198801266002403c00e02000021840d4000c194100d07050030004004109040000300e86034011080003c1d4820b408100c4071039070520a13081e600c40101c820a107040544002405141c544031168040307000f141040100208941c2c1511031701c541b501c00b090008040e4130f0682c1850075000f540d03010300c0e03401146441c080340c420040349042d108a00e60a1200c280d407961074203150400c1002c103182c00c031822400b2030000b107030f582455810010b446501100500f03850311030881400064002d10b00c201400741140301032098917032a0ba410603008000a40142056505604020f21603240040c0b42090310ba00130440390000a030b0010707029528441c1082110b017550030281d641c96400b8085010699503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 588855170 1250 588853920 588853943
    0xa020a0302043201050a02030d0515091006090e040519060b06070c030506130213051504020d0c030c03020c0325051f0e01060501090b070f0b0123030102070206031b07 73
    0x28083e04550b101c64102000510303002250b0303d180116054455802480700507042030100d07240c2c3c0c85642c0c12442e0450300001800440410070000300f10112030840c0c2c00301c042c02000b0b030200302d202d40040994014020481d890342c01d5280135140c0655074100028041703c80c052080f0f1b20014407046500039103c0c003130004c188076902c444908100e040348469001c15105d0b03000c0c3d20003040b407142d5400380002d081d55014041001c4d1002e00a1b450004001c02030080c41d0030810030041000303035907a0344010040e116140d000000e007421110030050841700002d12803020315104010b4046e04a00c00401d403041d501940138a510300b102480001250048a070340c00414510668881c00d040070503045085880c07040b0140100918041f0030182400e030380c10303882040e000c1a200c43c401c0c4000070200b4002e03c401c6014045041c5101455605e03403c50000c01d90000704100c84860224014013502082000d0503c411002541041401d4000036401d1201074403881b41090350070900c2c82404040d0040e00c07141038000024201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 588856420 1250 588855170 588855209
    0xa02010e0f070515030106200f030f0706153204020412051002341401050709060302040e1512030316030f1e020d090c0f08070803120a020a030204 64
    0x80d220ba440c01074504c02c0c025442d042d81100400c0c0280c038126412961005880f40200704800c060304103410020406024002e404c20140004000410a00241c3c0c071116a0ba200d860800004650424007110782e0404c0028041084002c007152010070040e140c181d5005d14110901d14403d19040c002800c0d800a00101d400140e15004415004030280940c0540f60340800611840c1c0c224403403890000c180740c1d25401003403120052130005140c10a031014115144241ca0b40322030954a6402d45003000a030744543c200030b03a050740956058014115402c09601b050b0524015030100c200c01000d003c0d0464451007800c4c0e959030340000c50311803c15940b080c0c0c0d80d00c1c10028008200c80c0c1ca080385a4010034180907001959007003912070551f0450050314801070604446022034043d5000062401e99551102515030210b00501a4000102070b400b200740d250310700c1c0500d05420140c1d9944003204c950010b100e410310514040207040c0e0300c9210030a005a4401310810207400902441c1c0000c00044a00e01c072400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 588857670 1250 588856420 588856423
    0xe0a15060602190302030d0c140304050703111c120509090a0b032109010c080d060611010f06050904080a1815090504051e0a0f020f03100f06140a02010e0f 68
    0x380c58190b8281c91203005041d107980c51049000a000b00141d1041007440380c543c200707a110380304041561522580d0301d071a05031901810b810a13034043e41c071074101207001c004008841d00004240039060300d8544c0701000941c10500742140503100a01043e4604005051892040080b00c2100300001c000d83d2150405811a0008041e46180c0314060300c28518141d1100c03400381882400070b109052182e1520000c1401180d100c00606400c59442006001902d03e60a590064202401c0b00d5039804024000c0c000109094a0a01c80f034084590320f040d10601190303d80140b0725905c180c00c8480da607a030318846241112002c826850315201d600e50940c01241034803403200203680c648525035070100407540320820402101e9040d90b8084182e603480e0020091748400013501540040c50700c01c0000c509002144890607684003000d20b01c03500e07100008000300301e40750400c1031010748200714044000e20708001016002959400c8104441c00c4040350308000c1034800d404c0301c0c00307565080741512030710440030b031801c0e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 588858920 1250 588857670 588857681
    0x304030209070c1109040804090c02010f0f0b0918030703050f0c1006060f020f060106030b03160311090a060f060e04151e0801180318150c020f0102060f0601030e0a15 73
    0x200d0300d41a40c408049050705e00244028000c0b0f4203c481940781c00e04d40b100f120010301401e841c400c155525200c0d071001c0d540b55486a003880e0b4103840400300c0c1c008201c034100301030040c0040550083c90440321803d003030b1031130000555554a9241c14815034640341c5000300c850324000c446000030b86100d0850280c0c0e404559800c0b110072151283c440d004058081201aa02c1d218031890b401c25550110004001c01c0d403184d040130401c0380c406429100031031044100801100c1c400d40064400e0303440b240c1100c400d400c01242882d8010074000d406c2000382d0900a0016041c4541d10550003080b83c0c030002001d541c3d684ea0b2000c44625904102c0498107130380d600c03080c100e00c800000220000301c0b40c0000041d81f51010f0050240c00b030303012a4140110409980c06440b551940b18800c0074807440c1d1f94004c07070b802d13185e001c02024842d119249da50940d0a40e204110074040403035000d5045400820901c28540344840c0015003003202400c01040c910702d20309829250030241e0724043c08110449005c041c00c207002c6d5018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 588860170 1250 588858920 588858923
    0xb1608130b280806090c091504081c0203070f14010e10050a06080601120501110a020304031b03020102101109031002030a0501060908150405011e021c0b0112020c0304030209070c 78
    0x406840301c0c07010704040c00e80b6141c2c0012002c21a0240001c20900c0c2034030706580e1040d00360070b00a04107046080802e90080420708405106100020140300740749041050742e203800c841c01042a03080c1840e51009480340605e10340180401d509855040800c400130168142c54000c04008000c40b4959203011603441c200c078800060f10074500303004180c05900a0003038500b41d40d401002400540d18001c09404045201b41c0207035a19581da90b03c030028041c200000b081d8a402e540d005686480c290300b40b8000540c800384898036201c9406400700f0050f43c0214003a400190f4846001406540d000415010341c4542c40000d80d1602482d500c041980381e50b0303409180074910180c000c00450385c94820640e0074207a02d001f03032191383d407107d07c8001c450079260304072591046c03041c00049800c540c5001484030109250040080e01c0b900801c0030085401110203031000b1050040007070060701900c10000c1d080f00310700600004401d0b000288260702100420860b0001c56015110070350500d41a000280301c180390220 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 588861420 1250 588860170 588860197
    0x1c060c0507120f14030c091c0f0c14061c0e120c01140f0c191b08071a0f1b04030b0a060510030209060f0904090b012702040b1608130b 59
    0x480c4e0f0011025094906c20071441607041d00d4001f81004004c0b00f4140d6001d03003088003880402203c00120034003201d03101c2511030180c02d4041c60625000c40002c0d5483c604080c080e010522240c030715060300f500d21400d174036242c07100042c1c2907040d00c0b202401d20050f1021800c402500050515103a80154004030381c0842c003c50038072580c0c036034102d010f481d050300b80c0d481c81c0340c1c9805120b8045840307800d003420110111181400d043d441c4601c00c03040c2d22110b4141e000e6400400115105062188140314414460b4040302094940e10744007400101c421b0010308900401c24034148404040000031702160040c5400c0044400c5500d808441c40c4080c00305030041074003508980442140c41c90084c0295030380b1040c000d08050810107404005c900b19000641410362041d142c03080140847c403c800c0a074042c0c610300b40c03040701c10024409001c40a01c200301c2821500d40c8100010000750351140c09452520316031601035840085141414049400f0700205000901d1802e04d002440940c00b1000b4440e01d03941d00c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 588862670 1250 588861420 588861437
    0x705030d170106141b10051e0411040212011806080d1d04140405010902030c030d0c12051207020a0c0b030105090402040506120f0102090307051c060c0507120f 70
    0x3003044030001050209401d1242a40c40180032441c040c0200c10001180840d00c02c1c02c01002180d900c172007880b0b05200b201c20750080d0010400e07400c0c00c3d004a40c0e1008201d080c1c203050f0300c0300d03420041d40c8203401803000d0080214210f0034aa03643d651380485e0040155103a40200c256103c017070001018803c284416030040c6401d60008034039030007052500c0900c0c4aa00c54107501c40901e080c07103280d10b440da0b541592240e07842100c3e18407411520101802036001c0c2000050515441c03046c54600f0021080303251082e072111020010b0198444030155a00ba800090030110880164040e20309010301ca201c03440c481c0b01c1030300304580c0300c0d0b00090324601c0d1800b07001014001607440100303c0b4603100a01540350040005000503000d41859080150081405000012200c1000c0c85460421f0160840c515281c4d40008204e04c00e0b00e01003125002400d400c0740d40c2108803119466010101d24103c600801c0107413034405c5000c0e4540100242c6190a8000c1c900002110f100d600c02041d95011881e01404160f40a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 588863920 1250 588862670 588862693
    0x30b0d05060907082a0d080309030703030f0203010b1e0d05010b0a0206011512020915040f23010c02190803042601090507090b0a03020612060a080105090a02120c03070602070503 78
    0x7010b802c0310794100d0b4440030344620001e44170080c04401c1030254218400145440010f40f00701300841c411900f52010b943c940d001490001e0984443d15021607030b003401400144054440e06044482c0100c0303001c03d4480400b862049800f00740944801c130001035141070000100541907100402c107201142d400da0302c0e03503030701c41d0020702e0000903402c49000001c0c1c00000142150382d099004000f8014024190401030110404181c1c1d10b501c01d070010000c60400d444200040d4001400f040300001c0081c1c168080e840076100001c002c91001140648500c4210005014814941800002034142c82e42074075544d648035400e51140701c90074000300c0d25202040da441d44440c8818407908001c590300c4005858003a240c50019800b501c0410901603000c01c501f4400001665200700034524004010922519444c010040140c82240d40d41304001e5a4104002c00808140224498001300e07811661850058644400c0918100c408969141c0610400c840440c449400080a20448000b02c08507264803111 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 588865170 1250 588863920 588863923
    0x30905070f06111506060702030a060606091e0b03070804022704031e020706050d1103010801060e09240709050301050f010503010c05090612090a02060a1101060f05060a0807030b0d0506090708 84
    0x151144d03882c441841c9012070003034a010300042002ca40002c00311040000c0c5a217078042210000d0f0310080101c0c030901c5041000540c51118420003800380c0d420043d0807881c00c83c1903210307488001c10320020881c10400003000c55545c1c2c050200d81c07090f07240c5140391544d0039070307031a40c00180140c80a502190040c03c24a200300c1c0010000c10180762107a01916445140880503601c0e5040710340140ba03000d4035801441080d03424500a107008241490010800078500081580c05030000f52040b1500c0c2c102d54801da60442540d41004040004582c141d00c0550f40c98204442030030503608103980c9035003008140404004000c0ca494144c46c0128020401e44807607003c191041d1064800194008030140403204005038420149644481c150b070549000541a6000812640c4032a06070780100f0001d10500d0301000017442404085d00d4019000f980b00d40c1000002400740c003985050000b045036840014242038800d0b00150007954002e805450801090b18109480c0c2200f250002920300c640000010210070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 588866420 1250 588865170 588865183
    0x3120114190923041104060f032112090c05150a02072c010e09010507030515060d1104030b160504050a05130f0218010e06070c26070e0106180b0d0c030905070f0611 72
    0x1803204900110040c1c03550b034201d20752039140b084001d0003100700d000c46442d08113001c4c207502c035485204109259813b00c0c041041006011a078540c2002c2d0600189002613000203003101980c815032103900f80400c031148500907900b09408030100d01080030000103421550640501e010b0b401c848000d000719580e29008130122182120b2400b1545100c681c4d08070f11b0f0070540001c1100c119071080100b41444010031140495025038011140d0600c8082045140c402503c038403c078103442482e04500d082d00e03110001305142d00764040c403440740e009240f0800c401c040c00d80c0107800440c1e02010135500c1d06100c080c0c0182c0003c010175200c1c0401c60490070320645140c000c0445004c59800483c031042d4608060302c5da043c10380c20184800781150400c0340b00c8103001c0100b12032001880c03140b01790303140c66041490050506a81040e18011070840400502440598030241e811013140d183c0005181e8000100480140400c120080c1042c0103825010070f40d0250400c4135401c0d682c541c0c842c40c00011004c009142d42c0c08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 588867670 1250 588866420 588866423
    0x5010c111b011409040f05070e0109081b10110d0e040c0c0c0e07020708150106030c080f07053618010b0f0706020c03120114190923041104060f03 64
    0x80e41c943c408003840c0751500180154100241000442400340303a2500102c5109468040210b5441200d00d4592342e032142c01b40c009004014041d2000c140c1c002030b041b5103014689143c3e446000b0b002e40c0121228810080e00341c008204404a80c0140381443c800740440740c0c500c00382401941401c0c21010501d000d541110312003a0301245040c42c0c20702d8801030714000300026100030110b009011780000e844101b0810351010020000c078034000c5514258014084420600302030060000c5c8904102601018500003940581c02d42841540c50180c1005142d0380d6403201c0004118030031501e0707840107450f20603110000900b010745500a128107d0360088003000e009200390702c68864108949124040d1020103009c1e2507214800140c10b10b0703080c90100e800c41e04140110f40c149955003004002c4002c0207041c018a50500b0faa807140d980d100307049a852040110b01904228030384400401106a400b25070301c610100c1b42003081201400d140c0303001040520141d1545101e5400e200b00482c042554038001021207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 588868920 1250 588867670 588867677
    0x2012613020319060e0601050a0305150916090f0c020f0a1401020702060412030f03022109120c1506100503040209060a0305060106121a01020a0312060305010c111b01 73
    0x150354803660024008800402260540039003107801d0b41c03034400110b90051a521a800120700404101e100924080703050740024458000c42c081000401c901003200d412000581468042680d90034007801c2c9480340c1011041a840d0b6013100c00610b4a01a030311180c40320900042c144803580440c14202d9848424051440c50758000340d80c2000052244002c0c8030424002c40005414420760740c000501070380203076000403130222048a80c1c4040642c802c2c0068811341882c10111f09205000380070f0148040c150f80d2195110011901041070b011040005d20045400d800c4d403140e0302c0081ca021181c40343c0300070014407080d80c1d580020801c24034040e0001100c2038800c2d551f0604540e40e54080225210b0003030102604418002000300210754180130680c06030403580c8940051a1001c038940c03048400c0c00300403031080c1c0307000790024003143e178080303284456640c261074001d01d0622203080d2400180815880140190b00c1c18001089082d0401049100002c8040030b0b42c1c10000c18007154966484c1110025000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 588870170 1250 588868920 588868997
    0xa08060f090f0703060510030c0806090f060f0102100c030905120c0a0b27011505010503060a060f022812050309150702010605030f0307020a0f030507060309022b0201 73
    0x5010507003101c0b503440703101440d0101e6920b94510215244d0803654400c000082e4403862a01b106a80054203a03800080a460171000d601d420000251080d201406071881801c42e056615681e030b108102c0c5442041c01820100120528848042c00808141d4800c845c0b6001d80305a41d43d480d9030304001c0c0c50800f0208001740000e0304160f0f4a01d02c1d0b0080040403030380a04900f1601103144109001811440f01c803800000ad42c2ca06c00c03421503881030b02181e1116042120410401ca65602c50000c80c0c01150740c941420041074852705016400c111580950704441c040366010072200d00c0740c0560702886240680e03040700d507900c40100c08407614801141d030003031507602002c2900d180f0008298100e52200140c4000199039031103000290a202d4422000c4012b0390010900310258a400001503000b40181e400c100360031480c41d0b07281a203500031442107200307045c0e80e2000d031015900d414a0030408100032039120010b0a6000d0441ea490b8400c810742a400a2400600102002d0b801c0e6031300100c00e96442c240fa10f1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 588871420 1250 588870170 588870181
    0x6010906270b070516081603081621030f090515060609061201050310090c090207110a03030804060e0606030a1e0b0907180507050307050c0a05060c0a08060f09 70
    0x4191407800c1014107109800240c0d000c2c8850190a8a0344a00701503c8800d2a8181c00702c0c02107503d03008024a03401c0089646103554414010034100d950110791547c84501442482c0c0258510304005015982903c1c0b0400043c03443c0782010030280342d951020026104025000f00407110b0000b0014143d034040c4000e4100e40e08841119035100c68010310042c41d00c83d280c0c0106609400030040340307940c1c0200c80b0042c8540d10301400400f10a12600900300012030607900c07048412401c0348101201b0a81c0020280709100d900c48454285400203004095540d641345001441c1840490301aa0b1140c034000030b2038003554001ca01603001d070304014010710300d02405498411102039040b940500701c500c1d01c841c40000131500019140b20301c00010182c038120780f5000c1c5010110395808455995070f440c0000304000950840262508002ca92401c03e454420741115145001c99025002e00706200b40020402400142d2005280381d040c182c9d2350006986441c018018114501603000b948080000002071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 588872670 1250 588871420 588871457
    0x1f0816060521091e030c06061009030312020c0102070b04022d1c0f060518030a050d0905150f07030608010b0a05010531061706130c02032203050606010906 68
    0x150000ca83e03030240c940c0f4940800c50350742103102c07490040d141508040f400d5005c3d15800e02c581588007406468140041c182014014460b01c0c0303900008040c070100000080c2c03142e21b01d506840194800100866036140d003820720b450f8040044904070311942600408151414035220901030461000504c070004910301000c100011200c2517031584505013400701100400c4001070388041c040d0042100185030b04001d0080aa4400703070002010b0310b5441000880724140d886006c95520f43d08028002070245103510f0410b04000d40510460104c60748602841001c02190000c0c82c0202d5468600304501540d81d05007c1c01c0e6090288001d5200700041410021540039030002c000c054410440d40e16158403540d01c0e001084805000810844a80b0106000e400c2e0041811800c00000072135512503450a0310000f040c0c8500e07100003440241d1180e266030000b500030000c4e00c44419031006581208502402d180e862100c0b00e1000365480d104040c04600c1c00d50040c1c1c2d0b000140e0307032181d4032600c40204505e00d08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 588873920 1250 588872670 588872737
    0x91a0a050a0605041514190b03180d0c0611070206030a0c080109180605070302270f04021216090b0d0f0b0f100513030c060503070e010201051501081f08160605 70
    0x180c0003000c5401d4250000d87c0c0d003c01501510b1720040440d140d00348170a1300300850400c00c107100c500303511074402104242c0c3c01005020303809a11450110304030000700c0080069002d4084000d411030b10120900002c2e801c180c1121002c00c40c00d9a40a145a03a505015070a0701e04c10301c0c102c0c210115405010f00400c0568101d15805a041d08026140040e50040040a4800e62811002002a00100c41c45502d420221034900100c00c40f0294142400200300000006018004034212a41c144800c054a400b03502c200c4d000b0031107800155240c0c40034070b07419005040d80310400c050951500c040b04206140551640c541d410001d8000131145080c810b0a4503642d22410308418110140c403c00000240000040005070420b5640c5a80320304101801030128046000034905590424081021719051140745000010382481d00c40445d03280c0c81c00d02440c8070003c00300074223107598801c4003090804000549040b9080381c09110320b580341e035582c011a024060020410f01d81c042141c85601c8a05400400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 588875170 1250 588873920 588873959
    0x9062706060c0d0507050114040c0b0a11010e07060810060f05070c0b0a03020909180c0d08040914010f06020d051603020f16090605010309080a03091a0a050a06050415 73
    0x840c1c2c903140c031100300e4900d41144042c52000113440000d080007001001c1c0588404a04039000342c03a0181016070720060001d506024040c00c980002c50240c0c110740c414103a07015104074a100030007005403145000c1d52520518012040401c4600c0049003408081c040590121f600580e10303403108811a5a080f0f17030b1640918000e86680600200105a04e040c01e402004c1403050768030016542c1d50480248000307440c0c02803c551807042c010400c2416035102040392007aa2001b214502d0300a0500e15191b03506016a410201c8910b16002402c0702c07080420401505032020b5104100c0b03501d5039000304903641c0d0200300c5074000044043c040c80541540340b9503100562403190041e284d551802044003882c1c4100c50603094844918210704012070032403841a40f020301800c0c64288040c40183e00d1351030340c0740b1078084c5181c2059600c6030b107402400300c1602d0300800d40b031190303042d21a981000c00150028000c20f0340d00810280c90318000281c00c3c07416118000c548800c2d00c4c00c0d008810710b0b2a0005200003c0480c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 588876420 1250 588875170 588875179
    0x1e3a0b0102120a0f1d01120203060d050a0c06021504030e06070602040801021303060b010f0504121110030b030d0815091b070f0501060b0a05071b090c03050609062706 73
    0x640100c0b090a40140007a04001d40d550310340c04110880c0203054007140c14602e2890f501c0142c0048850364040003070340140b1240c1d5005aa0ba444180210b1042380d040c410203400d1380034a60b46081000111264002182d00540c01ca8000140c801c0026102034816034004000c10301c0c0b02c01d080500d003004d4015001031400340c2030050078195901801e600b664800c0013180d40780100105c0038030030841a880703840001c00081c80c05207841c0c0da0100014140b4803850003480d0503062400d440e90308011080c0303500301034480058516a20340007180d070f0143c003070711080088610034020314130072221452089401a120340c1114007908030814140061101c101000340c4030060402d135039540f4052400d01040104100781c0b241c203040840c10384505255003194441d0b0000f01c0714900420002c608140d004040e9600e00c0d0700802d06c007c0545a0002d651800282c1d0b40c441c21010341032814502e02242c142d80800e1080300c0070303039002c0619540c810030010310b140c1848030603204c4080c03005034081c8200903140041e4810300180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 588877670 1250 588876420 588876433
    0x2061f05100c170d0b0a0609150309050f0d09030b010e100314070509150315060f01120605040507030902040e0c010f1206051306170115030b06061e3a0b0102 69
    0x103a0894076408004c2c4525580c0d140c2081c48090b0a0400c0c0f0540103100610300405402c1c00d1810101c0d524200b59440401c02d034035150b11905000d03060003642c1801d8079840440e1800d002d001406400c48081c1c1c03005a40c1c44803044000250822046065849140058000c2c030166045669003c46004030400c00c05052050400108882e11820b484600840b981603481e00711000c207004041c80c04196140f1744040380020000d2110503165002300f070580181c01d003040352011204050410081c681c1740d0000741c0c440e0600040c45a281c0c0c07d58804860503000ba0307814440c003840c980d0460f964501880c8014009401c0410301409c0342e02c00c0380c4440142d010300c0c2000c0b800e03e03503c100082002c11206411071007580d54003800c02c2443c0303000040b2116a6003c400900c00448204034500010b4200c1c80701402c4640c0761000034169648600895812240384c100ca0710410b10400a02da50319007000b0180701040348203c3e044c907004d01624544898040320800010803060f41080c4800181c60a80445810f500c10078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 588878920 1250 588877670 588877703
    0x2030c12010305010e0f01060807120302030d0c08100b0703091406090306010b030a27020918060a0f18150b010903050f0a02011e0f0807050c030a02061f05100c 70
    0x1448094000c2d4001c000110f100c400c50203803103040404141c500005685400001c01c41c03140085554000c888601800c040c8414040c14203a00b14810b00c440c2d041080c3c50801a0400c440e00001c19034010024194803402080d240c070200209031041032400340202d00581d10401450a080c05013294201028209030708040c00000464504138080c3c000400064001c820080f2034582c6200e45082d004c03000182c80c0c1e000e0004882071100d0000141b0281c01a09080002030303015410b0309088003038006460845100f45820381c81000141415801d440840741890016080410440058a800752f00b04000741000c2d0344a10012009042004059040c0a1a03c01c0000450014849a9042d50440c1d003d42440e52451000605030603d440d0545010003488002c902003684c046047c11540c10700e400c01d083c107602e6079401980c06006403d0000441c2c0700000b850000c050740400d145000ba4014100c0030070001180d070154118054502070070340c0000030729454104462060081452881c0540a490303070f000041c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 588880170 1250 588878920 588878947
    0xc01060306020711060304120c0606120f0c0b030105011d042c190b0402130e2a0d2a03020406030b090c030a120c05030f070c0501020f15040602030c 65
    0x100d60054601030741c040703041e500740310210303080c40480101200d0441c61403405036140210741c40e80c1d2401c2820002d144040004101180c0d0000307010b80002415040c0c0c05150746020f01201d042c10804072014210f0380c50000c0c441385100705407416610305840303031448040e4208030019264203081c2c103654090b440d5014803084041e03160781c00d030040c440070030b8000d070f04800c440c0074602d44482d84000c81a2100707000d04400100341c0740d95595410543c1182d9100303003808a80d05040c040c00ea03505444c0c0c45d900803503908100364079821b85120703c0c11502d62000700c94001d40800b0005050a18440903000d02c2c00e00c1c0c4480c0c0014071041c1000b03400e810142105032025120380102c0c04650310394204030b82d086403010621070720820400241601130300890050152200769903608100181c415060024011014601402c118050045d2062409500710058407041e4900340031608506070b10a160160090004c0364100720705c08103441c0c410800344950b0642a03269039403007c0003980018424484100180105880d1250 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 588881420 1250 588880170 588880181
    0x140d0c020a020109080706020d080405030714010203180105093a0512010e270111070b0114060f0403110609120a0204061e0306020a1b05072115050703020c01 69
    0x11103900801008040c0d10000d0902481a000704415500c0039408205d219400584d440c803051031440e140d17151303460710307d4014514002d81c0002490000400074503008040d055020714824030002c2e00140c0321002511701c55007260b109503210361072034020301001090301180700c0f4160f4803407502040081c1d00f586035070315000f201403601e084000007a000042c03a05548a121500324090444020054401e0824036a0080b0394181190200041e801039151051524001c0d44103550a00905031482c4e500c2d01540360140a800b004d005100100c0000380c503c84c0301b42004001e94100b040c182011a16282c1580c86007005000420f180c0d40c0d011400704103500d411b40751404d10142202c01e010040100c480144100400e5038426041129006602f0a207060780400050100046030b0b080301c030044c0d49040310402140c01c000203207141007040c0581c2401c1c0d0204100020750404464420242005642c0701c00000c0051008540000d00703116840e519948480c800c1ea8407a80d00b020060500524181c50744004031300b9200c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 588882670 1250 588881420 588881441
    0x9090303070311090105070201030f021c02030f0a050903030c03100b0c011a120d03090c03020405090d080a0203041a130c0603150b0a0525050105040c08240106140d 72
    0x40020003072014158040c022402403408003001c840c1400744050000306240150a03001e4100b40d00c0302070301c11800b12a54100c0381e09d41851707030301030300c804a03014540f0300130794815244400305800b0320303000550100c1d10340304080c000d8000340c000e185113440722420301000340c0014014243c010301c5c00c24001911000e890091011b04102030020901c41c0c015541221121b0311004181d008007010301442095003400310740c1c8401030541e810300040d21032183c185840f83c41d01c0c0b0b4000030341040ca0302c1d0038800342140019188248055a6031501c01c0c0d0760f50341c0402410ba00003901c0062045006040700180d498540e80981d030b00610a05151041224a45800c0c081c0c0725580d002d01c0c0880d40e80d0a841002800008030324001e0102c00114034078203611520000c05502c1508a4160445504848691851202451002000d401c40002d03c40d508040c1007400100c200741c41072407038501c00e40c200003107220010340c43e81c0400d0003000202c039916132916005980d10108403085501d01e00301000200240d150521a111180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 588883920 1250 588882670 588882673
    0x405090403230a110d020c010906051305060706060819020a0b030604240f0609181e1b120b0a0e1308041e0e0903030c16021c031206030b01030f110909 66
    0x50011044e9401c00700010f54800031504210010742059804c4804a01164914a4401c0da0b07070f640c04064031504103040c0c10040e03105000051302d0041c0442030b00f01c01c0580c0c0c910000d541021200a0518010115900c00290000310007541086415442c401569001c500034001190502514502c459003141c4600c05c151001907118040c000c41060141e0180648580c0c00c2040b0010b0801c5140b00100c1d00f030413442d610041d2614040c2e08001d80c03100301c04e00440071102007401001c000900b5440d90320b103400769080010340522020103510001d8001c00c80541d41c00792192001034240300b1480c090940082c00b0385909880700300c2100021382c4420041008081c40441c214540e188144140c2d0103000d43d501050b601e00580c000c0c0701e203040011007101e07040101500c4040e507a480c140c007003440c01400c08501946c480d40e5000038490301d50311008503000c014440d9599940c07400084d008a01124014000900b04080b42001070000640c00038110072070070300520106010301900e000042c5090340807142300c40503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 588885170 1250 588883920 588883937
    0x602280326150d0218150306014101030b030106052701061403011202240c01050604020f04030219081903020d02070317030402040e03130314030405090403230a 70
    0xc0b0300003080540340e52401110244110b0541d5000603401458081c41800419041d10214448502c0100034404480006d17055910039030795000100000ca04165080c18095800c01c2c0e441d02d0062030071518160008903544034014000f500004600410041c064190159038509000c13840f03540f40248541d59014000c8400c94a1800d03908516010406034860003e1250301818003030068801c40030780c1d040d00d000c000c01d544070a00030b00004000340b010f9100ca28000c514103c0030050a44070f40000c003040c818050007440303191106d070180f00891044503021580303120b0a02040c00107144c00c3d80a178640d51007001400c54050b844040c034906008645d07244075010207121681e50b040507018400c4014200d218000f0b4540b8501d50b46030801c000304002d502d4040303800300000040840d5200d90290040e1075244080341d44554407150450441052070100742c400c101c0c0282d200010420000c201ea040c0c0e6809440041580c481e99000c2c0c80700007281d08100d04a50440d500900c146088901400303184006548072a003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 588886420 1250 588885170 588885181
    0x60906090e010b06040b070c090f060302010e0a0503030d0f0e072c1017010216050f160b0a0825021e01050601020a030807021e0a0c0602280326 63
    0x3140c51585901c040c90341000300780281903442505032003c48041042c09a5528032034078001d8440b0700e881d08441041c0785800c0c5d10601924240e80610256071003a07c80c003903445450010800c60315054454580d25a01c2004400c0140a0365003009800e007078510008030f205884d03144010706103401500821021000f080d207095031181a0040c05d00305440250062417642031203030341c00740200b40500550b6480e032407025021421403070942c1140c14052451075820748100e1545030045d11b030008038820b901c542c4130b0b0410402c148403c03041480e00711680c03124010b180c1401ca0301c040c0d072440001001c61803164020b4682800f002c0c0c6606181005031155030140140c44102c81d4070080100350040600501e078500001c00840e44d0300011401603881c3c043c14034807e00c0e650700000300c0c0341818007141215020280c01400c07081003400034034850450f01c00c0803071039401905d99130200e984074510750702084282242410502114114425148000c0c000d251060413003402c00882030701000308007840502407043c08104030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 588887670 1250 588886420 588886439
    0x40b2d0610300c180b0f0f030906010302040501150e090403020703171306030902010e09180d0804110d0b011a1209030705012912030912100c020a17031504060906 71
    0x4150f080d41c0c1040b1401022000284001c000107000d100841381c0b000a034020300485040a840c541c85015880c96543d1505481c065210b54080c0320803406a402c1200201d00c120403851001301c020701d255600514408440300300601040054419010b502030800040040340c030b022840c10101a00c841c002d90340d01e1000101c40e001c650298084001c16160481c40d10040c3e0b881040c180f80d003441101e86070416150300c40100154548100b031440c1d607101c0d10606c9824140c110080502c16801070b0300c0d0613440306e0345105211401c451f40c0802000750700140014804101d85650741c01c040307001d0041040c00c002082d820501458002e444185c2c00c3d0b030003c6001c0c1c081110901a90f241071001050201a0a0040e40c041c0484044000524840c80c00a5120100090100300341c0e260450300501c611810b030f09484401c0e45441d042d0321442e44d05814407100e44543c0c0c1c00005c4008c10b25501c082e16818044a84107151030341d4001810340d000644074080c405c1a6643c0d0781c01003c0140018000019440740782601c000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 588888920 1250 588887670 588887681
    0x702060709050112050a0b041802030709060f06050d02091804150c0203251e14070806060402070f14030a110c0a03030309021503040b2d061030 63
    0x100401c00009002e0000da41c1c800c008615540407400c01048503114a42c05401610440708240e0b007051a2110044001c0c0b4420329091207580240e054404544d224100d140a590803405480440686039500304420b512900081aa006020900500300380b02a070000740c100c403441c3c01c01c0340400300d070000b400b060040c071414041c1412400c0400700008500f40c1d002a4490080d01000c0110b10949005284070400c0f0000101c100c6034411100c003007042186600244044500b18113503194208030b243d05044040001382c80c026550b5041c000c064903610303841000060751000300120740c07144025013100c0020b850340c454215116a1640550307111400a58010300030038040100c004107030f02c424108010f40c0c849020040540342c2500d0702113171400541c004102992801d51403074625003030000410061140750064640542441d5070b07001c6d03500048a95000301c0c0107060710031070078500030000030402c41c2c503100c5410004c810300340c100301c070380c1840d04203d83c042120314020300c100e0807120b0320918444401c180314a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 588890170 1250 588888920 588888931
    0x50609010602010c09090c110f1c1409130b040f0603050d090e011701020705030a09061e0f0e041b02030306090709030b010b070303060f031a010902270d0218070206 72
    0x2c0000c0d07072070302400401707543c01c6104082d6455038070303569a40c00501c1000300c00e03001e0b001e140c1110704090b40244d81940e980048481000d90b14400048640020710842006c81c0d88a004070700b46082c540d64034104004a203080980c040351307503501c001041e101d0301c0354060080e0546000000188162840c285241050700d100440070070070040d081c1c18031661448441180c1980c1039103450000e49a01c0115050082c85003050107049440040782300c00d921640b1840103403e40d885699110b0030404440d610101c28044000e00c0c80100c1d0400000400c1a8400c01c13100042c0700004101245d07694400701140442080f803d0101d006070400010043d83e400c2440007540c00030a03504e00f04403514991740b41e20002c113806019000c00c000b4006003c0082c136210790400b07005012610005119150741e881e0111082d54045104080712808500000f500c290900c290354401c0880e440d01882c0d4074010160812000c40d00f5901e60340312121980c58000340c0c44110700000c445580120815181c101070381c01a2420700700411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 588891420 1250 588890170 588890173
    0x180b07080606070b1504090c060e01090e1f180b010908190f0503040509070f02250b07030302040f0b0301170d12050402011b030305071205041a0402030a0c0801050609010602 76
    0x41c00541e03180c00040352042c541041c80a021919410141034099004408141d4094100030909080c4003941ca00c10040b20003544403210020b0b0394500660300b10300d141c0306484589101d03d0000c1e0b41c03c8502d840446038508042c001c04400c684507512150041d4258103d511900d54600b0055019600030240304007400103100180b250300708801d4000e64100e0f400c080141125140790f000010000b08209980280000400c03401041c070701020020600c44070202036000601c18011901d0b1100f0f0f0000044442c03540c1400b03040700450822081241a5102500460801d9400c010005d21540d83c0b81004021701500640143d50f540342440007001c504039007868a03590b8200d03040700d0310025000b60140300c088220b00d4001c00e140e580c500041e0f442ca01c1108100010319120584001003540c141e101c1d070f1140c0c0340c60b190723154082c60310502d200448404980080070700254000c130f544540c52070042294070a00c000e0460b0a40c4000380d0b9034141004150384981e4090303441e01b0902c2070501e0500700719800b4040520 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 588892670 1250 588891420 588891437
    0xc08060711030c0601052205011d06100e09130b0a05041202061501030513080705331803042403110f1803070519031101080603210409180b07 62
    0xd0158035842c4c1845501d205100c49240800380c504010810842411024010070096945050360f005c641d40030041014a84500c00c0000c8261401401c022148032041c0e032000d41300e0207240103110004a000c1c3c030804812240c0340054001621540c4814400c4608190115260421b854070b4641001c10719001c20954120b00c00300034140d240c0c00c01103115030760246004203103511081c0801c8815a041c403005040d4070300005146050190010303091510008441450148403c400e06c0001081c01500b1030049081c8014040340021f035074100080881d146c0d52050f2444e1641c0c0300c02ca11044007070803104003090b2041c031503a60032803501441541d106100c0008014600680c81c8158420340c0b1036501c06410344000c1d4454103080740c40810001000c0c21014105000f02540000310a510321b080b84070485000180030042001940b0541d070b40c40c02a20054000c001d0100e0074030013a40980211060b02603001c0007070100103885140d82c00f51980308064940305031115551410300c1c0c19030305e00c010010360070f101650 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 588893920 1250 588892670 588892687
    0xd03021b03120307030b1302040905062103040e0402060903010608070602010e1203042618120102070b0c03071103070c171c0e040f1419141308070c0806071103 70
    0x5400c40303504c40014513001400410f4040040e014103400c090506841c1d1001c900400c01040c682c0c001740c05818115040444480c80f00a09a0890b0246645e4001a04140820800c00440b4510036400c248018142420001d9000100e800c4075000d41c0100281c3d8481201000550f4082c807503034045151410142c1480480420550b40070711004d880240401ca101030545400310020b440300c50085001e40c007907a03941402d60030041600201c2580c60b0710402e03030400d042900c1a414400c44642a5004040d000c0a41d2005039155090300b00074071000c2440111581e002c0c00040900c001c000c054031603270720301c03048605011048811781c01d1389031480b0aa912a002030225900808400301a2150030705e0710129408a0384082070181880c1406180101d05080150f400700091015540c424400c0102c461441c40e00c1600b8141a200801030882c20321002202190201100e648900d0002e03010340c1031103103001a0b03603a8813205100d0903400700f04a500074405100301190710000e241c2c0b200e03004100650404025 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 588895170 1250 588893920 588893953
    0x80405060114060d050703020423090411060c190b0f09070306020a02030405030304080a0302010507020604110907050f0a09060201060b0418021b0307080909330f0d03021b03 76
    0x6006000301c041420300040165a03940c0f00700c82d400e40943d941400035080c40d100180c0a508280a0407080c05212100d40241c000342e101e80c0740030361000400d00c05407074540c0d4880138422401c0700c07506500101c08000005049a007045403c50700c0c1340d02544110501007908148005040240002d04e0004e1040140100504001124130685ea00000e00603654900001c0580c618495070340882d8040c04081000141d805020416024190194000313100c10380d19080100d03114041207030000c0c089040c0c1d006c04003140c2421a01c1903404165800d109241c8000d500c0018100c0e04005007801c0015210310041c40055428001c0d0b600511001000b030f4140f9007440821017860310f4074215103c4003030b400700303010000010100c032400c801c030540340907695200318038144100a6481203010a00a0000002213140d440030884c10303084081e01c1701130032109038410301000200c1c600c0441a456016017803d40c15031050380ca04114074040f070b1181e0002e003541a0062040c041c81a03c80b10307114800d81107401d004402020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 588896420 1250 588895170 588895183
    0x1209281112100b010915200601080706181d150f0d0209040f0803010312170705091e1c0b0a090506040f080708070b0a15050105090f01030f1103070807080405 69
    0x10342e40411910780315401261548080d50284400040c003060a0000c40c0c0c01c405085950780384a81c82c00d00c10102e0300300c041da56000c28442c0540300e038003d420070845c4510402043c80c07181c50110100c490706030307500d4188000380442480300048140440034081110014115050030b004d00362071201080158000203900754a42c50400380c051711155000800b00845007150000c1d290340402c50f10b40740d50f160308003403d000d0040400710001c9031903c1d0075200300b000004810344c440d41c1e056446615210842e000d10103001e15180c0320b2500d08401115200c850395811801014410007448859048030180c245060041005421020068503181c00c1101189000c40d515a21603005413209180c200d081c68268214400c10b50080c1403903c1c0030441d20200019000c3c2c40b03004400d4400c0512070305070303640700c807800d0055140f0a20307020400030090107a603400d00c1e0780780700503d00d4141400518100ba160880054850700c0100724141d4030000104242150840542c80d081105031070300048614083c0c0d1516a6001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 588897670 1250 588896420 588896443
    0x61819030801060516050a06090b09060c0412110a080d0909020315120a050d050a1706031b031f020306010f090e0406180f05010614010c03051209281112 67
    0x40005102d0170502c02044000a03d507484801c41e400c513840d40c200070b8003d01e000345049480394000d4010494000c4005031050003a005010030502e0240703021408100c030300c5038103000c840c0c1c89000c68501c03407156240c001520082072044040c1c008045043c0c001845807500b03410000030148107000b0b200300308160ba1603c410618003601c2c5c4c0e010b8038290034086454030000010046c1745204000701005007a42c07110240c000c82055480340d0207025071554040520040841d0066090782c4003030049030000301c0490014a546001074141c0f40d840100c2104000b10074640481107040380c0e000014000e555074400309180c070004891030854650303800c040c0201c002d80000b0f000500610b0f11900c0075807681d040c810703d11010710383c0407c0c0030181c12242d18100d80030f0050352199451b0381071002e6020f007295005500703180050780d140e540c4c2464940480107604480e0800b602c7c001240c401e40300036202030541042000303801400446115081001c902d4084e0002c605038500a00500c1c49444120050400096001005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 588898920 1250 588897670 588897677
    0x10e0a0c0212070305220f150c032003071a0a052401031e0c021c0c06150803071a0112080d0c030b03120d0b060301030c0506030c040806181903080106 66
    0x5441a013012191800b69440d00c076500395400450a07040c01a100c2030600715404a08a007002a80e00c001c0904001800006c10000c0380f56007507080d0000e4858044403110201e2002550803c000b9021203601d1030308441001c40700300700307500d40000417201d280031513540c020044c10342408140b420941038000014103204010300450054103080c1181e000750400c44114000480300c1800320030400c24440500f1807860f95a0150041c0c14818038a90106030f0210010b07035554446000700300380d43d80c4d000e004002c039410340c18080d1811a008100080140001d244481c050f0400c07940f42c0c1d0381030036801120001a071145c2c2d504d00700c80c2110000100b143c03064461000b682080014840240e04054019020414186e076040c020300300722031165040729000d400034041400301000080c5090f414440070384070a01014152031101003003044507140600045034440f5a40c00400c1c1082e55404101d40380200555243c080110300112601007400e00700000690074180d4216110040c20580b4050000d0781d0602500040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 588900170 1250 588898920 588898927
    0x207030f03020f060703061d0721061214160f0b030702010e010905061b030c0304260a0c1a0f0121020307030b06090603030307020c090703060815010e0a0c0212 70
    0x900d80240081030b00f000382401660702070316190714014004c04050280710352941c1416072a10601d00301481e200d12440c2c0a4403003880c01d10180c51001c00b0000403803c5281e0785912403402040c07a891100385550514820042040d08002c007406c03490502425003400f43c04581c8a540400c00f560800c2c0002c02201c0c5102a520741d2034881060807030141c044410414019803c01401004002c4c0000c0d001e849500d0b0104000851745009000000c203100c1a00c10303d00c45c100900c08100490103607440c1c0000d20040f180305100301c511000c0100c0c1d00b40c02032894880401d010891403424030183c4078000c0c4403003c0b91904414245402d01d0040041d41e0180216000400c0402d041c1140c8071006400104140d0001c044920355039a038609604644401c440b990302912608002c1009400c00100762401503100b0303001341c283d400d03110040c80794100c0020000e0080688910002458803028010049240c0c42c07201c0d05c80312981041c26030b00402e94098444c800540c681101408840d502080c00b502252051900ca41e4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 588901420 1250 588900170 588900173
    0x170d0c021203070507090c0c0201020a02040218090a0903080a0b0d03030504022706031009080706020307050403060e0a06050603030414060f0409060e0405010b040209060904150312021b0906010207030f 88
    0xa9001e0082228416031200044100512000007094012260424018800d120075200b040300e658a03042c8009015034000c42e8070400514054015119038880e070b96452030104903100000f0100b810507542c64201c00c0d039402403d404e06074040300300c07036000d26295024000301c15281c01040c00950a840050700700360751a0b0204045545d6440300c00d05240c1c244030740070903a5218080c0c1a0080c1000d60301d0901c00e2240452202800486010b0a05556000b0300401d003440300944840010f584020700340000c000c0104008000540c09203d0080e802103888000d060403034462800304201d51015103030912031741c01403104100c410b450144604544000b0740340541c942c014500400c20a0040c2d030400c0c0c44a40c10040086404020140e0715132003070340110001c1c800c8070880c80510040340708004041d40c0200701004550903905054001c0482940117180c40e6003180c4d40c1c0d85800c054507074158401c10058100105415812111440c800303542e2500b21849041801e1080003c2c0d40c0d1203591000071310500100e1101c07030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 588902670 1250 588901420 588901429
    0x40b01090803130504240b1309140106080a1109010f021203090a0201080c0403110411190509010e030c060403060e250501081f050f0409061a0a170d0c02 67
    0x40c9511411603407503102d82c0240906500d01c034024a0b020701d2038992406e202000c11300b14042e80d5020000702d200d903141441080032072640040c0003180c200c900304500184a143c00d106030400030100508501c200c0d410010b00805800010740685800c9007446580e4602c00fa02200703c4030702d0042424580c00300051700e0000d17403d0100341c40e6007031008400407040100007040801c00a084a01c00d0f640c106d145c1c0c1d200540d03007085010b0307800040c0c1a182181910f501a040a511590345c40141d0181c85082c0301e151000c000010300940c0e9050002400440c900980c0d580100d01b049842c90200c0180c0701d10341030390000c20120300503488050111078a03a0046c80c0018014005481c92640c2d11048000709428906100c000f03011074800d181c0007541000006540700310003084442c01c45101d002c42090103180008221070114888901a8010381e10390010340060f600744203205502c20844505130071440341d01d04004180060345d0040001260310010181c40502c0070507070388450344003810b00f24603a114a00108 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 588903920 1250 588902670 588902687
    0x2d1603060f11180108060117090109050f06070e1c020402181c02090c0a051b030901140325120606270302010813061808031f0513020f130609060905031209040b01 71
    0x500e1080c0c048c1c0b0511082480640000c4001401541100d00b070308002c116003503803402d088460000103101c1cfc0d240c0040a261044044d00044815800d08178000240e030000b8080380c0c0f080c884580401c1100341c0000c01c0c2d0070045116a8005c001c802d000c822030f527141e00403a4180b4002042106c50385c1e00080c0d0082c0da640280309494007051034000c06006e07409000ca00c0c42d50791b808220360a01041007224200030708502070003141d11075071090742c05680203008080400740c00000c1c0d06024080c03000e50400060301d4007a51041900a243c2036842d00040c040c1c015003624200003811b035a08a0801e215003d20240c0d030030000417900700d0b050040b41c0c101c4942da420848020802c01074901c0b00128201590010f00150130042d501a99101d00c803c9407281c4100d00c124041390840c820150003407013101501d040310b86a94003500d03480f000088035a20b4115200040e000360b0440360070080104401d07460a005450388400088080e04080d4004e20400e04030401c182c800380208107956218030b0312202c0c208003691040040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 588905170 1250 588903920 588903947
    0x6050a0e0a03080a1401120204050702100f320705070f020a03060209011e0801050607020f04060602071a040b0d110c070f14032d1603060f111801080601 67
    0x140da403040c06910b00207000a10960b4001950f9040032251510b00e04c050400d141280c101501400c000f122560900004e400c0c024020030030760244811042074800c0c03900414604550310030300010646040d5540700c5d150300010282c480d804010400042041c2003c1c0f0020780c100c5070034180651100c00c50f1400580020701c60328000d41200c1c5d120030000c20481e20b80c020300210902626210340c002e083c425103520440d0301410b41400a03070840010805c2d410642c000300b00b1a4000351103008101e01b1100402e003603031042c0d480341c40164080c000400c107000d100c1d040c80c48007800d94060f00f4034007403628941c010700e40141c44c400350107160740d40b1507044802d4001d41103c0b1821440f10681c1c00f4107942d2000b81c07100c41e13043e02c9007910b010b00b0000c45114528002c9940c0c9010950308921001080040d07442c0c00d401e400c00940c3e90490301c03c1c0b03076640c0c02d1081c1ca041148000c5100704404900100410310180030b940b0b07500c034405030850060141e0303181d00181d5040002002400e1920079082d40d558001203590350130350300d072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 588906420 1250 588905170 588905173
    0x12020c0628020f19020f0a0b13020a0308070b0907060e060a09090e0607030c0203070b240d060203040201020c04050105100804081605010e010509030f030115020a02060c0105160e01090306050a0e 85
    0x5a0442a545000103028101e44804d07000034081200613081c0e80714041d001c0341c02140d80060048000150003028104d07003211132580e20401c6071801e035001ca010f00303655030400e941c00e9601150040400c216000d50590040d001c20203000080d1812001504004c24485510f01c00d4201144000c01c2510171920007005084a42083c0040507890622079241c503819944100000c0c01c095166030460700000445401c16480648911a6034a80192084990184c25803601a00b41090300580d6075890300003202e0343d0342c0103400040e40d0b41440d200180c500b2410300c40c4540035a041c10010046a83c0d10200c1d030b90441241c3c107240e00725583c0ca20f4001014030034141006603141c50446000300788001544105010342141c4001c00043c0c0368002503560b01d02034041e100748030650400050046801b100c18405501415004403102c4880d0f66000400e0741c9c001109501007a0740d40c00412820b0750014010028a10715405e03d420452180800201800c41c503000c06803d180e2280089442003a071503006003102e421340720 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 588907670 1250 588906420 588906427
    0x409020405130c0504020f18040e070303051201150509040f090c08070509010902040e01051302070215120708040203061515070b0907090c0518060904090501020a12020c062802 77
    0x202074a907220b0031410a03540100004400300c2c2c07504080c4211404503480c0c20b801d0303040501a01004200d6803c03a503111b13820549401140d88107003000c0000b14090751203601c0b01c0707448180c005102984030905a000c1f06410a803000d030b2a03d802c1d040400c5858103001a2000705029000c0643d00c8060020150b0081001c800329000048c80c50000ca129000d44000321403004190742e0302c82c1034000b039010714000c007020301c5078000042080e071034000c54041d0310052894000d400c1003900d8000034003180c0ea02508400c41080000c109000d00000c55685501c40c0481c180aa42d80c03c1ca07402103035680000130910000f1751407182c4644403a556000301c1015140b9100c020303a60310740075858401c00d020801c0d11045024800d60381f0104460034a405092810121030f50345604000d1000c0407800c80c0403581d1241c82d00030004100c02c01040e02c850040c00c4005002d01d0000d80d40d480c1500c0c0c024a00d41c3c4000c150592284144058001404c012608680040500c3c031000d141006240301d40c0380412140368500036491002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 588908920 1250 588907670 588907681
    0xb0a0602010b0f0f0f0907020703080a0306090f1811060f0705010e0f07060c06020d0b040515090603030a0c060902120a0b090c01110a031d030714150c0601140409020405 74
    0x5401080b42c4080907541d55420040c84000c0c40400f101c200000e5a1010b0700d07040004d0141001407890b584021144101d0b95959900d4a405080380d02403150300000070384130341c404d004405150107852400d8408100410800c00351000051001d142c2c00e0780142500787c82c00081322302c0d944070f505441e01a2518051969142903901e003036802001c046609020602590458105041000c40c440e003c803020381c0c550f1030015400b503a07a44001c1d800540721011203595404040c0194441e031182a20480d8010a25054a0f0307a442c100100000018407051081d0700070040c2c1c1d540c241e880001c1e00c013010fa109e000450401003a100003240c92500c601003110600c00d82c04100240f0107510240350060001c2c5003640c8038450000d004403544803c08101801c2d82e8131807802100060311425141b030480a088040303801f0070740c8420010707050a20a9000345901c808000301d10095103010140000480c44a21169251401ca520035503180c200c14403c0b52010100504901340d0313030302c59400030b580c42903004bc4100010b1400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 588910170 1250 588908920 588908923
    0x8011517070918020d0b0f090f0a230618011a130e0f010e0a0b060304030509030106030c0f030507091a0d111f23032d04031106090c100507060b0a0602 66
    0x82040040705d5800c2000d40c0a603402c00c00c00301200c0304c0c00035006500545e6918054a400900075200000b92076940c8564041544002c4089110604225a41300c00d800c014040003050501740d600b006038181c403880100103002e2030300b01d08554500171400458403000c5030034400c0c00c401c003154024070f06040d8050401121203802c06d101416500d1800415105480d640070717450072210400e1005400040400215020900490180804110003070006c40c5094036035480801c41301076503000002c0282644401d00400109200e00800b51085071020400e5101600900c4040383c103a50791135000e1144005640c0a0001c0700082c0c0900e120f000d00488130507241d1050100c84500e14007240c1d0300003004c2140000c2c040c03028082920110450407001801e54032481481e0500c01d0b82c52050381c15210024020002e10311000c0075840c8254000c0e242d840b072844204d00c49604015000b08140610b42040c5448091035441c070070302d0059502d0768075166480313013210310348a0b004003520090706902c220920300c0092200d50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 588911420 1250 588910170 588910177
    0x11107091103010510020304060c0f0501020d0c180504200c07090525020a331a0a0b0c07060f09050315070219050604020906010c0b04030206070801151707091802 71
    0x240d841549017241e002c0100d03203e01030340c0030f914002a240078061010a9460701401c10a40c020000103152125040c18002150b50324140c203800301d00020107460824862000140050506560070701004000c071401e025142440c403000e141c0480702141040030b4000030460180500410041040079041000103d043c1010051f0390303000035236a61014254151000c10301d84410f50740300700014200100005c420b1112800701180c08a012900e0809000c3ca424a00480d00840c41115036404c8080c0700d84107005900b4030300c0d0010058040c04003c134404401e800030380f55080f94a0781c680040243d0250200302e80302e40700ba50029a051180000c4c4104284612000a02400d116004c032a03c400400303196a000090a031405445504080300142c05802c160703000941c0f20005141428000b021683c44403184103041c0c5c1c050700180e00440400c07860f01c0e001452240945046483e088a02001c0c2c2402031680c0c00e9000200300c0ca81d07044002c200350b180103030050006000d02d08480d010715840361400400a41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 588912670 1250 588911420 588911429
    0x20010b06030a0c0903120210110c031903020c07170c03032703010b0a0312020f060c0a030f0b0406030c0905150913050f010204090b042007020603071103070f1a090c01110709110301 79
    0x924104009c00c80e03a2980c422269013010101c080d50a200306640509802030f9107400040600da0204101d40340d40300706000c81006004c0030401c000c12030903d000c9481c90600e4681c5580e0099000304034048051183c400072a0404a00031443c51001d04d290021a000d01400361074a500807850000100802003a62800c6c0e0408a00d58215544440c400103526070742c10058070381068074502000030000341c2d8407903080504144810040441e015564a0124080350000c2d84140c0741e18859a100303002c80440c034003e20b80c1100340100d269040030007480c0000c41d190b001500e092068185501150108003007809480342c48403854000b15101c0f6a1408244007030f0079121002c070f100e685000300d8002d600d14005094007013041a40510303410302a49500b8001107500c050905001c0c40301c59880180341400400050600501c41c0b40001041e001c0f03441e121344400e514245080e140f6000400b00400c2400c00203040c54804400d1903e2031492054203140c908015040d0028601242031034950914425200002c50484 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 588913920 1250 588912670 588912703
    0xa0207031701030201080a09170703020708100c09053d03140910110c0a050d08070804020d06020d0b0303030f1506180121020a20010b06030a0c09031202 67
    0x1103001e03440c8244285003400000d01040083d0049003040751161f112010003407154502c45604882c54101d4516900500030440050340312010900a50100703103e5501c00d511699001c0c44451100040a4400e6099014850160310404036080c807000750450040060301010340042d1704900180d101428444201101e03401090401c1101050300300400e02e81c1d0f1282d4540f0f406000c222200d12206c4010f48130b01c400302440407009000c10710300c0038028003445024910441c003c06000c1c0ca51030024108060043c0944284a102020000580c558410084c01503030302c000300580e141070543c180e10040c031320f13104403a40521012041040c14006c58030300500807041c025480c80c404000000300020f5104a2046115610314040200b03107d5005001002e00c1c0f01c00c80300b003010100741c0411008203d0300030000d030f5000200070740e004905c904e42429100e080b150070f1500a00807640d40c0c1d4003188151001504095071240d503002d0800c41103200b0240c0720042c1d540208407018a03008800c00175a1080b0001d0240641d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 588915170 1250 588913920 588913937
    0x3110a081603020d0f29180a060b1206100303020d0e130915021308010b060a09142706011e020307031b14031c0c0f080a1e0c091502120c070503060a020703 68
    0x1d07035041f248503904002020004001d424481c0e80d41724050151701c0195508042441407082c200041844680c6c4076241124014803240c2c41c6041c02841e03c0449001042800bc2215100c402520b40300ca50384045080a030020540b40fa880ca84071240c0040059900015072010070454144911034124004940802c4024040817a00d02d08201d80d510400112801141990100f044502c40054003072045410080010440d40350640410540c41004503901010800b04010800c403582c1044188281d2202c0c1080b420270787c4c40440001c0d50300d02c5805405810700c040e0015000c1c40160300c0c901d5269091740f159240307044e1415408015660f401c0111034150a00d04210030b8808092203100300110500c1d60b50f18854210b104c44030681c0d800d01302420305981c071911040380062070015011022404502128000b4500541010040085015401c01000030402000000045074004cc0142c180c80581891076540c1552201c21031070121254841a01401010100620034017140e02524840d80280c450101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 588916420 1250 588915170 588915181
    0x1020a09080c1903170403050102131502060702031e041809031b02030a0b0a0b100f02161a0306012105060a05190b030a090b0103110a081603020d0f29 66
    0x255241c100a0100e9050b010f501c1000400c0c400c035010701c404c40e03007600d070300b481c103512034540909903070180c10801521040060104031652000c4110507842c00b00d031025000d0f81c00c140f2030080d220311842400803502c44a180742401e04092441c03c44005120300c03440906130030000e0090740003814801105802180c441c00031141c80e01c80c01100d00c42c4055006026001081084c2e032108501e01d0058801000d056917184201a01e895003840c2041c00c0e03003540c645081c50a07030100002e1130503080146c8200c004804003c10010002e00c1c0d0106c2400740550381100b0386070707600d10004a0b07240c07000c442c82c440c0c0e80c0c40c41090320384041556030215001c0c200a42d00301c2440780d142d10074030010081542440d00c0c54403040c1c10820a00075508051600084641404140302074182c440c040e504100b82c00503665407240650021030f51504100f00c0e0014001c28018008c4070000760303009045c890007807002074094051b110317407a02003046c40c4590b1b0602540c8030503000c0084075000c00203200007440d0214598000e9011000c40c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 588917670 1250 588916420 588916429
    0x310050907060212040501050313020d061406010e130902010e0d06050115090602060a150503070e0105030c090f1501020a20010306091b0c06090b0c07050d08040b0f04031101020a09080c 81
    0x2c02d0501c0203013103480d191a1a004486030b030700080580034586141c501410050f80c030392041140070b6003c1d40d008074045070a014001a84203019111704d05100c20000003070880d890340641022407822040c00090340050380c1c0016600c0404448141e03600040c00b100050811265a01040c180e813000f00c18841c084607044801d81d6024141c0c083c80340035a01040c00140310b15110b070062518005980c3c40060950b0b59480400d140c07016940243e24680461401486a8182080948400f080c2100c2d850b0603410300412502c0c2028018005c40d2000d20b1190100a4507402084421106035200001e030300f002d80942150301e03d00100714041800281441c100041c0714407107000340c80b403951110b5180010040c1c640011380354030401480482d1000d4640c042d407008248200a41442804025002da5990b885460868103110030840781c3e00c2800020024040801e0702d4101043e4806400c034444202911582415207020b1201904c400c03482d8000034102d61116407160b140c40c00c84010307804031420b1200c44130400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 588918920 1250 588917670 588917683
    0x210c04030b041e02150901020114040809100219030305180a0503031f090e0309120d050406110114250e1c031e0e0901140d0201051803100509070602 65
    0x40e2071100040042404103401180915182c0703c21203101040807459408544190003140403101518404280480c89503028080d000010f00d407944164100c1c5007641c1e4030500d030300072010309074003500368003603000940c0d8000c024051043c00c0307519860000e04141d190040241c41c1c00c9030140480d2010780041a42c0e43c81c00920030501540c400301940c00e641e02da000307150008000440e00000300c1c0003520001502e062030300c500d5001c012010003641d507840d0b0104c1803104407034410702e03100260340c0008070303401c003c035071000560701950994503042e0384840e041c072701040c00340c641c400801490b0706400d00bc1c054414914000700c43d4110315182c4c1c044a1100d69030040c2c03012054008c6940d0800f032005010026000041088010944a400c20365a040001c0d81c3c00c803580214000b200f4081900380f48003906619192110703500518030007001500484145010641e40802084000e0600002140485004122003400106440d01030102d031001040c0348101c50103003100b659aa50346005400d0003003202440400c09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 588920170 1250 588918920 588918923
    0x60f040806160c05060105010f050702120706030c021501050d0204020405120f0f16120f080a02011a0d08071704121109010801180f111e010305011509030809060f210c0403 75
    0x548961ba20b40001980c8684103d0a0401080b0b800c00c14040160345441030709164a1401d002480080e04015028045440101070801035502018400d0050550076a020b07040d104180c4a808000301e0902c0414041c1c050344e04240c2c0d00000d04280151002d00001e9206100d082d00000c41c1c51502e142c0c01c589484060300400703018042a001418040703160145100e4101511521800e00d800d070113601c0301c4804d600064021801071751209800c04a10b00406600040098102c7c1e04040c09080e43e60b851030240b0881c2c1c4020079a508950610800048600564004025402c50910007100610b07242a00c81c0c051550036104580c60303400400c55a00501c5118011104041c040808c1001c503102c0c0d41e40390b0a04e0104483c00d29844041002a07144c0c0c07240490450003650b802103006260b000050240c480c16000b41c00c244012202d101c0c18950b01140034411290800006956030300c201002c50071500c81c2c0d480100c1c6074240054440d4440c1500d03144818158240c5d07503451065140c2011140b0079210703d100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 588921420 1250 588920170 588920173
    0x41104030201030504080c060f161416060e030d0b04050a0e073809100f140d0204030803011d011706040308060d1a01181104060509060f040806160c05 66
    0x818030041d4000d5205582203401a807a1504160a51902d540350103030440e03564860710100d1040c0b05070036401c5000c104814409080401d14a03c1c800200c8809008168460512100c58101031080c065558030038120000680d082c0d0b07641d104401070b1a4040c0030310100705d0307001d54039110000d400060a445404140c03113240c0d02825925140c4441007202060000c0848601c0c0500c0480c500709410010f40c905c80c1c044080c40f101c0d103515962081242c2e85d2080b80b55001400700000035861401e52001410390503151092806807914200c00301c4100078010342d0801041a100080081b400769188000307688912101501d0503002c0e81c80304005800030070b00d20041000d03907209802040000c1d0103040748070f500c104090101040404c03d600c81640e2544c000c4034068144448d1401401000b03010100d661f15036903514014001018200c0003000c00c3d01c0b40e840345400f085804500c140c1c50f82d071200110b0301d08061300c070060303070b1124cc4880090343c80c2c4c10140c0700016800c1c441ca00c0750034001d0103170300d440d94040d41020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 588922670 1250 588921420 588921427
    0x307120b010b0901111006090b03010b150310031407051005130e0402062107020c0f03030904090503090a0312020d2f01060b0d02091008390d1a0411 65
    0x100880b816812034103456041c00000c1168840c041420440043e00d04074904000c0341851400168404441c981c12507940641d051424081d0389468401c20342d01340700c545510482d941c1d40c0d81003454450054542006110303003030440204a11143c000340c030b5000d545040310030210501c6209000d6a07140300710440481c01800300c1d01c0c1001004607580c5840d03800b6002030400342c42c0410640d1811145030075992200b014041c500300b440a03c942c104030083c032681d010358041340d015008400203503882c0035200f000c0344210b0320f41090404000e0140181d58904001408045140e5140d03d8500e2006400c4501e050051080b0b8a071040124403030320840984807181080788081c05900c00040c50705003494201901d00c0d40d02c0ea40b0000e01101080e008100303040ca40600181ca509481040044503014040814100002c40c0140402e00c03200381c038000700000c070401495204240c201c00c100c0003104808141000c002011549030702c5010715401c40d0384d4002c41000e81c603000d40d541030304020807035510742c40702c0510300e0051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 588923920 1250 588922670 588922679
    0xf1401050309071509030210030c030605030718090c0806090303040b1e0103030f020106081e0106150203030c070f1b0608070816030207050a08030a060f0b03070f080619060e0307120b01 81
    0x82e81c100460307410341752841500341c883c2c000c1048840305160800011f80e50388145008103505129000103400101c0281c01d4091400e03176055681a0720451185040365508016020080f46030300305030040c010b10054489030314052900c0c0752a50002c8030103540b0391082c10000b4a54507021285403580361319907101c03200c043e400c50b181182d4600400c20b041e000d56685040c0030405450030800c201e99503150301101160b4000080800d402e40d2907c0d0300c5060428409155900d80710740202c160380e440a100011a80c54843e0360900a814404015018150812094036145000b88400000c0b040e2442900c0380c0ca45502c40250031105080201c0c1c0c086a09070064000030041c0380300c0e40081446a0003074003291110200c41d02c1e50407086d4000c0e241482000d80da01c004000d080c0144d40c1400c01000f81040c0036055151031107014100c0c03090402c48400f00700c05038002a140d42c2c1d5010391040103000c4084c0350800944c5071070740503010b6010300c0c0600703119202d00400002c011022041e900c003080d81c0700003060400d0740390 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 588925170 1250 588923920 588923939
    0x9130209070f110f0f12030c0403020121050901020318061501181a0d180c050906041b0c110307030c170304030530092101150f140105030907 62
    0xc00c00c1440402250a055108644080046089400c901805807101842a600c00c620f843c0402d40d200074400c6c014402c1120360320b80300040e01d04480e0282488103013100e1240083c88541c00364032224124515201c20701102e100d055000d1480340204c0030720b051030b000c91800c4890303071a078080b0f812001d0f1240c55843c480b02d65100304220b1403425812030032050300c9600c03003d070380040522048101400080105801c000e0301554001d4403a10f003048a8583c60480c100c1c0c071000500044e078001d00c0d0103100f0b0140401c0407916585e00c545564070103102c9142d5007580c2400024050b14074800f0503190403c0c1c520340044c007172038081402e0089035485403c9a2220740303000c3d100d48000c0141e03042d0000901051200001003a81400021360700d9056141c021071207241e10123503151a143e58401501a285c0070301c001c0c81c40740c8924070f280141041c80410741c012a0b1400c41d065015000c07240504080348480d070030000790912400c6c12402a12030700070600303400c000a81c004690710301040701e05429950101b0000c100c0c1c00303007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 588926420 1250 588925170 588925187
    0x1b050307060914010c080a0c091206020903030f040b0d05150f0405060316030308100b03010303051623030a11010209060a1b061a0405070e010207051c0c0b090913020907 74
    0x420000c0748014804aa510382c05c40b680c030108000850800d00801c0350340c560600c00d200c16001d041c02c140c1d010a09201c8180c08003009044001c01e0b450b8005410440c81e5800c0055500004120041035a5641c940742400d016070042c0f00d00e100c00314101170100d4a017000600c010310040c01c6c0a03203000e802c640c040c420080a03100c05818290140205040313901c2030101c00407100061402074452040c1c03070500100304480b80703000c1c1c0d0200c41d54400500042c00045c0d407100458900000300042d580c881421410919603c10020140b102500c001000001d03550740044090003a1111a440e0f940490f2228001700d820b0340b0607054041e81c0100c00700210b41700c1c03031b008a0320b030707801c12035411803400d210078030782e9296011241c5034290088071491000ca106003625181c080d580c0d0002080c50721031046200e000c0041d540d070340d15001e4580701e00d120480454240b0720716100c08800350307000840c442000d80e0b9100d00745100d40c460002280210050000030b24400e582201c5c40e046154040d102480c1c0d035a03030f28021a00707e00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 588927670 1250 588926420 588926423
    0x191404020729060109090905060105060f0d0615020132070c050f0c040b03030c100c1103040b0a030b01110616050c101a041103060d0201030b0607080a1b0503070609 72
    0x44150141c20080d0040c01c10300c1014541c00103000740f400d2850001d00a000c4a85c002c1602a08080c003150020380e003c50030718115035043d200d290f00d4240c0c4075261a540d0090800c40714529141050000e14500c002c448001d07144800c4c0c00801c07544038652010304014003c002c0420300c01e03000042c03198443d000840ba082e880b01d0341f40b51124031540c1d00d5960301d0502c48000302010b00e5900007200151a8135052190202506003140254900002020000d81724802e42c0841c01d48a0354803000d0180301800340540c0c40148000c0c405699556464298460f83e68000c1150300e000640340007035401c0320754050300c4c0d400182030520b030082509590340039918500d00d1900342a882046024000072040c0d002c1041641080035a10b600480c41040741034400c02c0e0042c507404294805c605103911100301390401c02c112900035000380d9070b000301c0784414001a006805044c07846038112900040440500145a020b0540300e0100e0340c0300d51040c0c00140301000c8201c59070300c01600c00d81040180328001441548202c0605 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 588928920 1250 588927670 588927683
    0x803040e0c0f071704180b01021902040b060f03011818080a021e010b090a050606181804030f02010e01090c090f090b07110c03070303020c0111030f03070903021914040207 75
    0x43e2941d543c01c802031010520f0310b40355010100d03040c008000384005c001c41c04019038404020261189000035030711030f0003c601d0003000030742c0d00030b0106544880c0c21192401c44c001d0240c954070650204225482d5200744945140100030b20782110540a4a0151170340d011403907200768080c1d0a203522100c00c2c940c80030495805520900e695070480e48902c3305580c040d04c0004000280100c030683c20700c44503400007030050b0501c0d071902d0300304012a41c03840c064030a00c8500040c0c013038555861070007095103107404e51241d40702c00210500300010943d001a030b07445a10034aa0003072104003050345009007600c081a1000303011000d01c24051000e0910f80d402040942d0405401060801c00c4d9102c8140300001650700c070002606441ca11f034401b00007000750704204007058006002c001e142d510700a488250508415040040c40f9050724003003241041510000790b4014601681c90800300c0028050107010710040f40200021540c401050f004c0f6203042080300c00c1d041040a10100c1c5800700700003580146021500c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 588930170 1250 588928920 588928927
    0xa05150405090a061518140109090e0c0307062c03010b101d0d0c03170c16050906031c03110d05160813150f09020d0302070f0803040e0c0f 61
    0x260380d40c81c0d81290160464140000384a403e00940c0f0607030012845c00c0ca818460314007800c45071041c9820b6410206c0c1d130742400100d6134008020040f100b0f2035103a440911041e081410040501402244511010f402281120710940d541c0d44196840449920314054090741509400240c10041c081c9001c1800018000614907040b9000524084030b165000fa000503100c0c802991401c86014070405020380c201c6140e10181c1003513907000f00500e514000140720b145c5040003001880580c10907110040702c500c0030342d4507040c491800000003092a20400d84110300c0381c00458420705020864000b00800406071080c500701294042c1c000c0c050b015107000b00c40c03e081000d144d41c644244030310b40c001c0c0f4208540002c9114071900081c80341c00054610b60440d46007507507040005012400d410034034a001000821180200d01383c9000a20280002941007080381e8469010142d001c21848107440e806643c984085884910f000c2d030341cac0a1030007400d2001d4103580104050300001805841d9510320114400e14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 588931420 1250 588930170 588930179
    0x91009061202031b03040f030f0c02150a030b0a030b0703050606030f06040c120204090614120d03090804030b09010f05090708071a0d060b0a0e01031112060d1e05060112020a051504 79
    0x5958422101074499200340c40d07051f410107031300c03e84203176120f505480e16008050407600007070081c0c1e1807900c45000e032150000300c060850740a90802c01c640325006180180d8a99641003004520b1404c454980010f031134500021010f00d00981500e02680040800305159507503041848001c0140d1845082405001540300f4200c22081c0020b00241201d000b011611300c3c0380140f8500441d03129084a480780080c441c8c8015040c000182407180301e00a4640419a0159420020781520540c1c002a0511103944100455080305400c1150742c140e001808110b260390b0382503810b44414a500944001da0440841044214031440d034810340c0c100700442c0180740c03607034414155040700c401da80940c0c4002e0005c02c031401a581c000702e041948007001e00301071201c2e90302140b0181c942c0c419848001e6001c1d64002c08542d60f0b8845003080300003281e000504004548034a540c20b00e100a42c0e4008445c40d00c1504001f01e0103c108100456813154098050f640d003c0c180000c020120b00000000082d0700000e100009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 588932670 1250 588931420 588931471
    0x1022d0109120e010e0a08030f0a03020415111005041104022101030b1b031501050c0a0c0315061403120912070e0610050a0804110d1709100906120203 66
    0x484820280c0b5401d00031200c0c0d0f000901150070740e00c0e2070391040000982c1080940780100c11a01c954546c0c5080541c0c40780300303520940c000e001d80e8005031105c0f140034ed024026603401918009031801803104480c40c0700d440901040039541e08a2b0000d0003100360383c0403c051313410715401500384c0c903180c1d140c40d0004401c0c07503c100580000c264000c0d518840c010b0140b000c2d4046208800e60b9004030314244a1451409a02d024507020215000b6410482c1c0010781000741e81040c0200e141680d03012000344040b0355241030942200107101c184120700c52030001d00044844030612240c3d072802e4098058035031552510400001c9400800321a81c21001000450b140c0c844140056000381c452111840344c01e042c188140503013040b1030a000410b016040148500c0c540d0040b02450380203910542c0c44c444240031030042040c0c20310044005040380d58038009000c010842201408250030281c5140c03040d08492141200c03510554402c20012520880301d144101055400455000159001300b80c00d0214100780329 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 588933920 1250 588932670 588932693
    0x2040e0901050402091b0a0813050a030306050a060c03020a06020304110907031407090e0609040510110d110405010507030311090d080702030c0406180504051e150601022d0109 77
    0x156659542d50100002c51a00500d42c58000b150080342c40642e45140744000703002c3c80303444000d0051103408000507040304098201400c0080d842010703078103142070307919014018003014091584110307160100802c1d02c0744980030740d00c50300e6055401800006159203641d00207600c040c0c4103031090720081e46a4003250b02c5145c8014054036565a0000c1d03400d021208002d10a00068101c500b003004035641003083c40c20707190032103400020454581c2c80603142ca14200703140c44081d22000304168109182000002c0322240a01004641024240100301c0d0030b000c1e0b04464410b9000e5940032800c00d000b0407010031b1081e440040c3c220290002a0310740160500040c003030b500c100720100d43c0b100b00003800c1c03011814103018000145c141a50140103031414000281d04418200e086042c5081d07540b000242440400c000d6026141c6180e03290520b40c0e80c80f42e42c1141c07241004c003202000d40700a140807070b500d944005a5104402e100018402181d40b104204110984240c40b03410340329925034040d280400c0848130307407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 588935170 1250 588933920 588933931
    0x30a1d030a020c06070209010b0a030b0a0f030c0f0608160c08070807150506011b030302040e0f071103091c0303022b15031a04020d0506010f03170c0d0e0402040e 71
    0x464807103880c184001c1c6099004070525000312414400440144c03900240c2e10705540030441d050b512043c012204400400034180f0541d4445030a400002d03084201000310030a13280648000d40c480c5480f8040526041142c0c400d100010341000c000030400c00e148800c82c2100280f9161802c1e0040d900c1d202c6a4090b046a082038808840005544081000c2000500300706107450f8410b1001c2e01c1c0c9100003070559412400c0000403903480844070400c1500c254103c902420606c0790391446820074402d00105d0020850f1000e022601440d040c0e0480307800042940c3d46510f004120380b015601c14072406d011443c002c1021800c2c15024400700388004022003585c0d0456100850500c6406201e01d13004040c0c0f2060303215003070b02801c101e50070b001080100c2034102c0741d04002104003460740c4491010a07101c0c403901401401501540c1c0001c1180481c00d1651022a406a11421060011240500f1191207076210303521550344400300c140d40141c0103010b560f07810540100010b040c69030b51030403540c000c00204c50 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 588936420 1250 588935170 588935173
    0x102030a1a0a0306200d0b01030b010908060103030f11150709050a050109030803090a02060406031515050306090a0617011e060e041b09020f030609060f06040b030a1d 73
    0x80291461403846040720010105019020041c0150045101034500c0d000160065449240703110381070201700f06080342c501c20050700554074118030200c00005c050410006001a0401e6a905203940c4a2080c51060f82c140b2409411035918540d416920752140400c85000d01c40d0310b1015410030b51007800218624031a9035400340d214a0700e5034000740703400e0780b42e0040b91051000d42014009a40d106541c1011780740e010ba40c10b50350380c640202d01868421a20002507010000040c0803800b075078036801c40c0c02d52052503400114074940702d00034848941041040c0c0c00010308103100081842c6000c54603150802d0145a002076020f03190440600000100c1c5c43c0d001d4640e440d8030105840c0c4504403a800d828003481001084201d0914101030850714001d040900100d5a42d0380503104101042d0b0708400901c410345c800c540c0c0d45c040080b000e8458000f207440078810151300000a40d1410052542c04c9404002052030b860941045039084c0207070006031510f051a030351002c0041d071034155103500300d40b244000d50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 588937670 1250 588936420 588936427
    0x20c010206010602011b080901060b0c1b041a0423010609030c0e070f11070b0a030504110d11270a050f0907240c0213020c0705091005010c0503070c080102 68
    0x100003a1410030107910031811a8980459a18825020b003ca8011050b480c600303c03a29448441505014081c1900700c0341c124400082e840e00e85600004000002003030641d1402412211101004102c81c40380414040d100c0d0285e4082046143c40e0b17114100c02890810540c4a85903c1d030484050a0701c00d0704404c010540c2c048041c0180034020f903c020046c0545800103c1510f0184002004100c00f03070740b00313028001042c50085429505014010203003000c0160b05860301d13078541004000d440103035030598040b13134046001e80150500d601c0c802c03042504614245018040c0074140b0016034408134018901030080b440d8659140e1550313886501481800300040340a040030031400191150151094425034040d10701080181401441407102d0040103042c0c1800085e0054151003c02880070000d52041c07850b1030784e40c9011000d5000e40312804a8104445403551182c044c0440719006a500022450300c0440400c5998407990805042c01e101d501940e0130480d040d0340b0035424180c2a00700f9442a50040f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 588938920 1250 588937670 588937693
    0x1090803090f010b030703080313060507051b03090f060f090307080a05012904020307032d050a0605010905040b150d050702011b050318031e030415141501031401030302 74
    0x4020386191080b0002c0204119900b4500199035200c1c14400245175840220010b4050711607400f40765a803e03000b8000340309a18003840b000305030303501ca14480640200445600b80003c0000400d840e01d424014140c100b0900480c020410703650400c5043c880b02c0c030000c010300044c1d0b031014400c900041039510000c10315603c491030620300b528035183c56842c108041142c6044910118446a8518101a06c0061b07480d15880001c43c003500310b0b4190004a038081000c0b00b0341c0c200400d400e100c9407401c0100104419241c03183d0020940b415881000e0000e000c210051240e860968040f01d0f0943d07000740088521402c607080c11085400c44c0c41d900c87c0c060703070740c10030800003580a018000c41c9540c941c1400d042c61500b628050143c1c0009014040101102100d0304941c003420800c03141000385d428071a404416514001e800541e10442e0f003200c4a08000702c0c50303644001140138410800401c2551800b41e0780d9045148103440303c01840e400e04058a82c01c48000c244101c54a113800f0310301a50117420611060b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 588940170 1250 588938920 588938923
    0x1603050a110603090604110607020a06260603030d0e2518020405100e010306170d120c02071203050723060f101a0705150612190b060d050109080309 65
    0x5010120340500010001c0000d4a580420780617801b9a100c21500d4244400b140810740c1c030700400b2402074018000c48408248a5006250321401e00e0f44401008501e4403606403580004006441881c0c041e442804803c0f5401d680750051b08044507402e040716090864541c0407070351460301030403200b041e1654660a10268004412480c200240b075035040d4505440c04c2d000c07034070400c03a10940304104100469510941d038400d030401c138010080001c07181c0130080c10b0102e10751160000c92441c80170441c8181d20741800c0186014040400700e042d000380007010710708000f003020040d041400b241082010800d00c07000440079040301400540c151086000641c0f00d0070306500d000d10190070074056540384002c01a5442030240c243c019618100c0c00320034504100120342d1032a00036594001c03d40d006405400f40880d4103844828030507141181c00d83d5901a400c0350407a1621100401085244601d5075080c02007821041c180c1e4000030040c0412400310001e85409084402100040760542c600100380300045a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 588941420 1250 588940170 588940193
    0x1d03030d181a040803060d020f090403120e16060507031b0c06030c03051009200f1206150a03051b0c010e0123130204020903151b0a050909091603050a 66
    0x240d8002d040c40c03d0500751a1400d0078080108450301c50518006148210349842000d5034111402400c0315666051618000c1c00c059442540d400d401890010281411100001e00300c0c80400440038542c8107604001c003c54440c0d10a49054081c401481005501d121000550040c094020698400000e0038000c00805869111864004243c2050180501e50b13032508440b40c00c50f150b0b0400028044822100c9942440d1071402d2450720f240080340741c205032014040100b81410a80d10300312a540c9e240c00c10003031038410442c400d0302403003802d0151110017806984540c0d04164000c2003a8041d0842c80480c20746ca0f400189140d81c0c07a5112031081035200000d000359100f4085190501003440301124056076820001090a16280020800c580554071154101e407007c1c00060f06445040c03e84d1071160980c0b407000c0c1c034103034070a518006864221300c450b4821b5804860040d59141d00d019610b004003d10403101030700130a080c0c014021140c280105640c800c00c003c520a2020346945051410002c00d03008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 588942670 1250 588941420 588941453
    0x80903240a021213020a051c050f0607080c0a092d06090501020c090a09020406030f0c05180a0b0f0405011503060816030213020903010c030204080c040c1d03030d18 72
    0x1c1c014030224840404142c03e442d80040440420401000d00e40001084902e441e4001e680262100707048160764149810092005070240b401c6825020030780c01d40e10303641ca00494098001800030703404076281503690002003c6140340c40c03030014a075030348031a00d02c281d0808400c098040400d240a64803440100004001c00070410341c1001552180390100103500c4510000045115166440000d40d40000171b0344210b002e10b4002d401003000640fa072070a2018488109420340d80000d00c43c000007824545241c90f5604032140c03403228030f0a03450742880c4c1400351400c2c070910350b40b00c401c0350502c2d11030f034940e441450b000704140080301c1020140e00c0b2000d82141e030f042c0c100728216004400c0d050554090700c003d503412a941a90f44071818070a544900d4000d0062400300c90b070550800701042080d5a05401030426144070704181c401d45080401008200e03001c400d000381c0171440088900c01500380180d01e110410b074000d4143c81c908425010340030b0845000c0c2111018824200903034000b44003090701103c0100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 588943920 1250 588942670 588942691
    0x60c080c0102211f060c05100c020304051906092c0903250507030b130c03150b0f150c100608010c08010e010608060d02060d18060b0a05090103060908090324 69
    0x10711913042d25281c3c0d82000d000b004113010701c6010034001c01000b0000315112601c2ca40040000c1c000c0e10310001d4680d1f10612406104000e842180e074001034842d01480c040750841d40702c8518030f074644090b43c000c0091540c2c003241c80300c1c20004400308840c00d18241074820300d00c090280d541c0300d038510041240200608a0030303034141e04400d02e550002e0000612201502e4003d5280b02d00c03952050a1000d058080c8840148000310149000042181c03504076140304900d414010720024a0300d0007031200080d880c8910311340c4803200f041003442200f8000c0062004200ea28103540034010b049001400b07860081e48007580e660354a040c3c071600103900002040c050003d42014650315450600300810000e00685540c0c40b8000b18400442103640f41800c4802e040401c440c01d001d102d50480400324440440001503984030704200484030640340c54900304040d968014100411a403c640702e103401020009012180c0c840204100d4581eaa070400402036802d2004c03145440070700c3c1f40000210310401c05001d09070710 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 588945170 1250 588943920 588943951
    0xd090b090102212503060e07030b0d030807021015080d0305071d0319060b10020d0516170708041d040c030206090a0b0d0e010b030703020901060c080c010221 69
    0x4401c44031a07004426041003e07054a26229002d03c84500362141c044950f003410011090303d92150503410000c1180d01c0c200da003221030764502c407056080d54006111164001d8140140c440002e00072410240c0000c0984111208480f120411303004070b0301802c0d540e500401610504001c0c03600100859031941d941c600d014025070405800240c940360145580c005c944040c800d80d41c2858800700300341849200ca01999800b42041414284000c4c800005120300030030140e11a84c1c08680002100005009547c0d5503500d0001c01c5040601c03484103401d81114801a021080e5903808030b0300010745106e600801003980d60300e143c211524040c0e00000180141e03200c000f403c001c00700322040e40100440e90150f581c81c1d81c44d0f1080000810222994008403c0c1c03080104551010011540c0001300381d107042e80c002c0080481540c1055524500d80c440258020808030041c4a007030310070807200648503ca0996a814130016444941c2a0303005200340ca2003c50850065000900c4150015034118020300c008182 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 588946420 1250 588945170 588945187
    0x5070518190b0a11030d061d040302120d090c0b030702100e03030f2508060f0103020325050705010203040b060a050f0d0201110705120705040606050f0403110f03030d090b090102 78
    0x484414855500b01003404107000c0c10403400381e00784a50440c140400d4958030940e25036980c004203e039001d051285e611030a140c1040c0100968241d000b20b4060b0002d00c042080d408040207640d102c04c8090b0a15901c510700740001501050500303000e011541091a245d180000307000781b8001d034080b46401868101015521b41c84408011260001030100c4241c08a071b440d00c05900244400940312010f000c41300b90101440d603488182a401208100d4442480011005c011003e9001c241d0350080740180341d44d680040c1d08016242c101340e0b00014288030b81802c0301c64846034220f820031642a5801c0e092070003004690b01d40941c84c14060700342214038617107040300c500c04103842408050009040c00341000807007420b00030402c14803004020003804100c22a0050884944440c114031843e4040c50520a010408d240140182c030003c51180c140791b420f0600e140c59800c60010300e0190140c0240c1440400030407074906200501c08031080000c04203006040d45030088050300018128001c81c1d10501c032095 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 588947670 1250 588946420 588946459
    0x30c010504051c0e0d022101050609130b0a0b1903080a1b0b061e040c031a04060e1506070c0b03100b0426030d0c110616051b070905070518 61
    0x144130003c1130700c5004141e140c0340f01013959039000c66418064801090050340003481c05402c81345c403500c0d09440b54080d545072007641040c4015040700c01402e881007000040c074000d03030550201d192048000e10f40d890090f51051310008800460300269481e010004500b0001c90b00102e1084040040b2503401d00c40308125141c00001c1c80380940310f00c0c13041480e004003110b00800c5080d0144942c100810030004e821002201a00501c0b500d01150420500380c0d4501803285003611410007124100c1500112a1360b54201c40b41c0a40c19425a1b540e00c1101404088042010765050f400505000050250380c2d090018222500c8105540910b8140e44200402d0040d015840708000311114280d030076040c04000b0f40d4006084d07000f2010302c84105403038008032506440d4400c8007000d0700180c130410703a030068039050300100384214100c40000202d2820014410b40403550b80c00d83c51071070381820580341c2d41a180e40821007074034425510300e00019004150a44400101022003c02c40c0007101c42e10800e80c0c104c032980 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 588948920 1250 588947670 588947687
    0x90d0c0303080c0909041e1401020c06010f050609010f0201180605010314010905030a0f02010e0109300c031209141e010b03060a1e02031e0c0901020c061b030c010504051c 75
    0x80140c04101e920380441c030f1012400319007da13480080180c41f0070310003c50034000e401c1048442128810b00c0000203001c65860140340950780003408030362501042c100150b90382403068603030104542d0f85048440c22118803104030165103103e40b202254035451030a0410941e4003404c42621140d16080003500060800003c071a4106106d0800001000d64810203a00400c185900c00c2225400c01d1040401c221101d00d07030401c0225880640008000c0e0142056150b965409014012846814103140803d0260590740e00703034141c00001040d4600030f0fa441c1d000c0b903c61400e060103140d11515581080760440b00320301811401d080001c10030302c0040e10000760340d12405800c1c80f15440e13481d0064074030707121100c0c00d0030710380186590155982c0c2800b003030240d0f104520210110052100201003405005100d04480001e413050b07008007aa4090a4100403142d0300103418103a000480e030072600c3e0b9441050000e0000e0194060000816180c541000c1d0308014044088103040b5140080c0004140e4000281 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 588950170 1250 588948920 588948923
    0x1706090711030403020901030b0109060614090103020711041a010201180b0c07210c0201020d03020403030804020922080c0c04110307080a0f052707061211090d0c0303080c090904 78
    0x4180c650541c0c1c001401c5204903000a0742060380200007000307101c600c0d0051030403140020b10070442c0603a5154120365640d41d90208007001d0208000840c030039031094002c2c1603181d002e403195145601003a80007400302d0306a41c400388010400400803891542e020f00c2113181c0080301e2142c04d28141e03410f6540488415004141c582d10790300100c3c0f0507041c046040007410000c400984030140001440030042c002d5818003c040303005205114031078407800c2c400c0c001e0b1821240d050b221158203481c1c503420031000c0c030b00040c00c5a644491500209074113048050180c15654050352013943d64000307040400d03023011024180140254100500000b5903244d48040303a50221440c0340c01c821607102d0452100141c03282d060881039041c142401d00c03d6540300359042100078141100c0c824092412004070649030746041c480c120115007081203110080e1807a81116680038a40080c40345001889800030f1111400880280e0f844103003210300380304040c0c20244545c0c018944040203800d200d00c5800040501d00010b10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 588951420 1250 588950170 588950177
    0x309060309190b18071a090d060c0504061103030124230301051305010b0f0703091208040e1e0403031a0901060f030f0b060409050c120c0a17060907 65
    0x340781c9041c10300800e8070040c0c140b41c85186004290909888000c016604910440c1050b420a901c0010008600c4100c684100d00540ca0041011407205c6a4200000503038024803810b441a000800c10301c01d241e01e081507501c2d41d985942c10414028503820340c007811000903910420062120300b02d031001c2c1810359188401c590240f5a17200e80c0031074450b8082d503176211242d103521807104035200c200405181615007e40702070003c00380c1c0039244c0044c0c503820700c10724501031410015030598101040003440414040c0c24906407580c2d0750b003011244103a1b2024142d80b032040c04103042c004d10003c2910035400003c121a58403004152030411101b41d01c001e040142416520800a041c40c03e103248201c003000300c018030000180d80d4407500944210342c409014000245050302c0310f50040440d10a81c403d40c000030700440c0c10181020410700003410701a000c401c0c008000c1c45010140322681c01260310a092140803252283d06500d0007a01048034101c0c1400c904401c0001c211280c1c0322840c0c2281e00100518 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 588952670 1250 588951420 588951427
    0x102010902090f04080f16060b0402070b0615040b0301090e010b031c26070c0302060703090510020c0705120d17010e13060209061224031b0102070b12070e01050903030906 75
    0x9045c0c02c1034860104004c0b0003400200349117002182445140303c0840c0521002d02c810300c1c00c001044100d10510500034140110440030908908161400380014180c80304014074003500c44e501000580c009920090b0065200c08800300040800e029150383d034401900100001500c0c03649021034811044a440104024a4501d07000c005445060b0100d01c0c4071513500c00740381d0030541d80003000c2c1007144006801601c507074000b01e04942d1003403081140c481d4002d0301416014101996400203542b056403040f4840c85081c0011038a9503600301c00d800340c0c0c0c1c443c0008020b50b05a841d4050a03211000980c0c83c203000401004000a00104011950190095240c2c06030007403035142c580002e01459028582000000c168242c0039510861443d0161003440040d40d200c4400c005071540b0124000a02500b503040070490040441c0c3c11407000400003c14010358200c5038480d00d104402e41c000c0300c1c4175003d107640501403040c0140c104944222622013860042e24060080010950780d11510490030301624000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 588953920 1250 588952670 588952673
    0x1204060525050313081204061b05010e030c070e0c04060507050f01050a06290702131b050d05060d0c1206090b0406020408120309150403020a0501150f050102010902090f04 75
    0x401d450058580c1651100c403491555040003590b0340c11420b80c0c510241440c10b07021900307500001c0da94000128003641c0c64a8181040003c8614484460798040280c0850028500198080c000c4c81030103140c4030700940e202c00381d214055181003003c0d803160941155080c14420001154000c840507900c00742403003952180245065450209100f604070910751070729060010726032840c0c002004540e44500e00c0d951600024100040364511400a4000e05000b080410018100b59107420304007050404002045910340508000d444d0b0022481c1002a50019840078195040d12401c1d411110544004980400030303a107100314100b1500664844640c6400e0ba80b040011079040000165440134480c54241801e00e0100b010f034105002e8000c1d24051402c50b0b011740007603601941d22540d13110004010038417076804c0101190030060001d03000c6008107144080404d100340141650003a20a0300305080910b06829031290210b6900401c0c11641403d4880700035079a507030401504864499080011038845 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 588955170 1250 588953920 588953947
    0x8061e0a18120c120504091505130e03040905130b0f0609071119120207120c090c09051903020109051002030f09010c050a030201020408060f041212180b1812040605 72
    0x640c00c0c0101034031032025001d90411780c060083c1c81210301007842031000c000e40f021342c42c1802d0041c0c02a1500300d41440c00c0c42e81901d145811025181202c40160391401d612082180700740c0b0001c4402c000c117008640545800c00c01c40c071386116805080052100807030304020000900000c8040e00d801e0421811120b0803440f401c1c00d1100d420820500075103604c50902610b00307809240c03001410350000d0300540e04001819040c1031111283d20303900606151042d03050a08050042c4806582c4004002070440040717461f854060041c1c0e01d07e800901354030201d03491480010064602a00154090441a40800084c940000c151440b40e81c1d0340d0900e40e220117403580102e4200003500c40142052052000329001d264041d402082642c1514095a52607940e008800600180658005200300700000301100c1c214851802d1101013030310b5910101d000b52000b80c0200c001c01ca180c0b0300303075034148005091040b0341d02d071002042c0f400c60041000d88106844100a52441e000394418071060150010704920424031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 588956420 1250 588955170 588955187
    0x60201052a0a0c080d06030308091e102313200f01030b270702060f04020d150b040203180c0f09040f030c05010c033309110408061e0a1812 61
    0x89505c02003240583e203090040a20340c0550b088001805600100c00707400c800c02c400303a990419080c005050055404078100020241500c0c1c0c1c69000d00303201401c1c48911a80b00c075107402a49200f010300c034506003c0c04c1091060034003c1c843d09481080003207403000c540b500802c0e45501c000900700080e8000103070b0302207148840d940207070108070300c408040713102e4001d02030502e1409441e279075003110b01c0d6603038032400c481c2500380c15200a5844140d000d00c00b40000d02a1500d0040301000c80d802007032121042012409a0300187d840f241200c010404189044500300601138045204a5010406402e40004503000e20b00182c0064400701c240c10146081c54040e82d140ca5100d54000020083c062189600400402c090400d05031030516a105252107141a0801580400b0143c040d8041c1c451400000c0303c003c0c00c44000c68003915005000025240310203100c0c9070f2041c6d504020122140c1d1025000180d0114018480c41106151035500d92a05080d030315a409031560018a0181054005009440816 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 588957670 1250 588956420 588956437
    0x91f050d05030c0d0e010c0605090f0604060615020a0f0204180b070e0405010e090706050c07180b0405130c060804020f10031e0c05031519060201052a0a0c08 69
    0x8104140310300c108a4000020f0071032207203100566080080c00300c400c03500341d240c242e60540010480b1080b1004100943e12094100382c82d28104c620325a803483c001030034020101ca00791500c5035030b1801007100507603014501201a00d14400740100e0456a03480c20b404900e2550040e014a60340c00c0c3d08443d1400444584128640100c05043d0340d10b01318030010324001c8580c1030726016a050400000e2a000750b00e401e00d0103070483d08041c180031414900104d546811080f441c001c14482c440c000280e20003400c2c00501e403420380710404203187d002c2e50f0903c01607030006484444440c0d6142088000704d003e007040c00003030719240d103001031040e21240009180000c00801e00c640c0f15103420071041d0358a030541c1c070146080003200c85083e42c03031140c182e0b050100c616964440c404283c041001502d110000c0540c0c20391040000c1a00d101c80403040858002014260009000341c0c3d5905c0074807000003004810500d880107142840c1e0540c0b00e00b80c08a00e403c2c05481c4003401441000c0008104121190042d1841e90 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 588958920 1250 588957670 588957679
    0x1802070b0a0605030c010c0f0f020121060305070506041802090307050402041d090303070e0d08121611070b090108040c0302031b0f030307030906210c0806041a091f05 73
    0x1820304454100082c0714500c0340a00c41e100e2500e4100d07080d405604603c4115800c12800024624551240040c05202d007404904104190242460361501c8403108040100c1000c030014800307065140c41da00d00580d5401142c0720700340c01d2104024000381c842c013860b200d010040b40540c4440b4140c001ca480c00c044d0741c00c5203a0007030010602003152640401011050702e03081c1030000310b40e200c003401645c41b8072007640d101d00004d850160403d00c0d4100288465400c40c4140b82c01460281420294119506d00ba12151031182c080b5081c1070310181c2c0f00d440a40c4a4180300301422000e841d00a40b2031862080c050100e042c07060302c0c00002e0511080c131001c0c3c1e0046401500340c41c441d040c800c156000025009003050312851281c907500c03a0908000054461507503240d11000c1d0034508201c0285c074a00e00e245d18a98103820310002c0030f45a45854082d158400c00c403501e80382c8050804500300015144030160350640b0300940f207000022641c980c9804c68008901c0908001e1502614445d01c104450541110344c02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 588960170 1250 588958920 588958943
    0x3060a33050303190e0f06030c070c1e0305150c0304030f03150b13060513060318060c0201090c060518042715110403210306031202070807140307180207 67
    0x1c2018480c00344e0095407035a455a0301c5812420402405403d55404160010024000508518009401402260302481d64140b000b40d482d180d40045000801203102c6110749403e00b081049000c10030948901e80041e41042203142c41410162280001003000c2c00700603905101200749402640300d400900c5036a10754414041c1c03150804c44107a4040c826a11801c00a50340008000e842401030300c6481c4400c4509100180c44c1c500128041d004807046540509181304070580014024403489452040366000410000c40310304005c1403c11041c3e01034000e22501b00100712409202c0366541e030b59280c00316030005115411034545640b600271158941005148030a801d0305000812645c2860254000000d000e0000145051005030003176210003061440d0000d54007182c04000d47c0340250402e40740c640054860764079203402541040c05010f030800350308001414000c022090010801820605150114003080e02c070229540f045603203d500c907070307402c10b4021480d400d941c2d4040383c0906401401c031040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 588961420 1250 588960170 588960187
    0x1e0e0a0e070306060807030623040b060c010911060702010e01141308060f0105010e060708071109181e0a140106090c020303070215040b060105071506060e03060a33050303 75
    0x42c00c007030140d480440c0b0036000050001c0d04c08d015003000d851140d00d44040f1307658013420544035446075140e665801610b440b9820459201c4c9406010150f005000208107540b03a420864014071121301400d0284208100040c00750f4bc1050010074502c00a01c1c10001d22042140911110f0050f070000300c468030f051000c0019020300c00902c0c1402450030004846090340e8842c01991100340b80070265801890510480011560302c0001d0312209000b40d11305444440d00384001800200c085600d503048034600ca40c0040d04240402c11140b07010445001000d20140714001d0035030b51080303114010302642006190312101c00e000e401400081000c201c1c00d000303007001c0b0302000e51a50801c075035210042c400e6040207081d0042c0b000d2a02e00442d007118a5180701d071901d10045466501c241000c0d1120030480c103201c803014440d44203800084c0000c0c4d880b2540140a90101410702c80050300e0607800d241031119840c0c400001440c1c0c08400221084001d0002c1d5811500f108101e078035a02059050101052509 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 588962670 1250 588961420 588961427
    0x11030a050f03040603053904050d0303091e02030303060d080702040c0e2e031d0703050115051e0d02011803030c0b1e0c0c0a060908070c061e0e0a0e07 66
    0x1040d80c4e15a181440715546842c1101c64140001e5500f58071074410150300142d61022031001c48114601c07514152a00d0b485802103036120b014040100d0009079070b40403c0090008401c5d80010746150640c01140d5048160001f1340c3d13a0102501d01c611540303410000d00e040111040482e085164081e1090102c0682100040c02101c1480780e2140540d0101004280f074000b6510401c907100c00012900c02c00e80c44444040b0000d01d60403059840f80a15541200500003080200d400110b11500000c1000c0317040c0364484810602c5035001c80c8c024030a00135803150f107407401c0d0030200c907044003900c9035a00c1481d14001210740781011400e01680400c580004070515a12501c03190711a40a051046619100e04c440008070030400c4501d1000480e00501140042c10f00320024000c1d04c4110040351903606464171041d04a03009564101e82401c4000748100401004031650350050400313040c4807004d4100021034800316402a0300b407000700207010000c19a42d42e61032813124050031541c80070403d02d2500300c9025 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 588963920 1250 588962670 588962677
    0x10207150c0f05030706180b0103060b0609060315010e041a100c1e0b130f12050d0204080318010215011404110d140a061206110d05160801060903080711030a050f03 72
    0x1d4840c1410b140100c1f900d1a174600c0e80604503540030650081687c03940d01c55000920501031030b0b507071103402004802215510180554011f8000c0600a6080b420800015100e2902440002c2c011070404041050810700d084d41d0050880b010313160b00300c001d48030700802c54070b01c90f124000921114210900507404420b44040701c450a1140b0075081040c2c80340170117001b03484404400105400e079240007040000710400c0180101a0842c10030078200010080c030481681c10640006031503620118020728024119420441c2108080c0060040d000007800703c0300528405000d400710a104a010f007100580b21584910080100c0041aa445c3c00341c000010000e40340f401c80442e8059140b43c08103006044901c5410304a6004034400241740c04960b0f90ba60182070300c0c0041810301d840034010310700c20380d03418001e40f84903040e41c01d0a076400501d1603001030302100041e00500204030b50f142c018800100100d048550264011410442d608880b20020f454400b1940008180d401540b08217000080d000014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 588965170 1250 588963920 588963923
    0x40303050c13060f020a0209090c011205010b04170309060307050901030f0e030316051201080a03090e10031122050a0c05091f0c080307210506010207150c0f050307 72
    0x244101d880c0c11490641501070042001d50b2420000c2d400c1040314000c241d0108007107014015186941119000145150006ca560069a400004d00da1202c0e60303001490120102c43e1510420103541820300c50302441c000c034021000d14228a40442803d40420001e64880600080441d662031800c4480200b00d500484500707400307c1c0c10700c001f1441e500550301034102039840000040d81943d582200002e0f40d0354202d050f644c28403c2c100300e0401c0c103803c000c1c8068081c044010042880030700f5881d00400350901540280f920410850078082c448140d43c1c654402c07a03411103000c14091100c20b0000749440c0c0310320720000d4480c00d070810100c4210300c6600a14444c40ba0542d08000b0420542000d80d410310036084005d500c0122944450f04900304036145122510f030170302d011003c42d00301c1ea03034581881d070003522404085105200d40d400d82184450b012840e50f84691000d02a0703042090022b075450305c06028909078070450550704980f09108900302074445030442a140798000c80360603c182c80c2e44c0030007130 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 588966420 1250 588965170 588965177
    0xc03191b06020d050112050d03050601140c070e09030316050d0608030c06040204060510020304090207050a0c0b07020924010c080f22060206130f060b130221072f070e0403 75
    0x107001104106e6034030b01d581c0c0010180c20b4092007071804070f0007400300605841c10b002109034942d51920b0018081d20b00c40c42514020001c26081c02c04d0020900c0d03000785281050b510800400200d80750240b111410380595040823a11440324242e03120207080641c00102540c840032a00503414680018154040d60082e10200801c40d1208144124807501d60b080c0000f5900c2000208961422a80200703a41405002a60740c0000c00360749281154140b5400800914401700b2080254a40b844415420080d40c441800d424441c16140130303da0b40d68181c032039051181c03005c00d40040c801000c088a02c0c00095803442950350400450090304c03a00c100600c411300005040c00070840c00d000040482c0200c0b184000e9080a514070703541c0c006510300700c0c80103c880756100c01c404034903a02c03034401c10596088071402c0943c41700fa10340c1c070483e10000e511845441c645402c60038000d00c0c039048452844070030a03074210005d2469030349034030986c2064800185170316803082e024000340703444e0201045409107209a5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 588967670 1250 588966420 588966431
    0x905010212040b100e0730020c0d0801090c0c12030905061602010e06091e010905010c090503161401030b030c06030c04030c060306031203022a0706140c03191b06020d 73
    0x16010902e103542160080042080c002c106c400d19820000d41c200c10125103000444000300c16035803d010f9801083c07272a005075200c103480c00c051503040040c441c05066808000c0103000da80310746c0140094000d55014204030300d0309a9a40c04144250840d500c0c20350440112013660030103008000800e10021540c3c1c00651030801c4055080c940410441d01541e1110f00402402c14411009800340074481ca505189644e901007038800540c0a01035a40100600c3d00c2d0b5400243c5800203050902203095540e070b8001135510b0b001d012804032988100c0d01d07010213281c005035a07401840460f03d80b5800c84810791340010044104640c215885005000b62842062002e03142a81e44905805581075408000c01c40e030b0492142d00e00d4248030394080c24003a443c2e1191030f00301c00051012000716451040d407400e16500b020740d00740680c9402c5481e5400d605601c4560a240c42d0ba140e02c016140c5c0541921901480301425600c1c4190348288a042c00300c82620042260500326803400000035031000800300c200318100b6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 588968920 1250 588967670 588967679
    0xc1202061509040b01051002071706060f0d03020a06320601030b010c030806090c04090507020f0c0d15020a03020f280e0310050a060803040611060105060408030d0905010212040b10 79
    0x705000d40c01240c4c04012000f459007048100440503800c5501d1300218400d10800140d1504040245c0e0940da40c041c0103000e01c1d06080341407241510044505600034240707000c280300002da00044070b070111500400002201d41c2d1200e0300c29484149400c21880d400d10320f524002c613141030f6450207401048248c804010241c000340c0191800300321000050049050319000440d603042400b03116900a0100c4003a078500364a443c4014119201511075000503800700a1070204114108085240e101c0d007200d2155140d80d5941d42e980b00389041d40300c8001d03a103801280000e907060017078050740c42c0e051024040c1c9865260300090043c954021400e0300040c40003c1042c8070f0030034050303810280c1841002e80603100c22010703110329501a001c0540030413450380e5541d00000b08100240058409002c290307403001c0d80c14807403001031880c0c000d068002c3da100e00c2c0d0400c400c0007040c0300001180e9000c01010008503548846051407802409120107403184851040304000401400f150b40c00e1107640588407030032019454 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 588970170 1250 588968920 588968929
    0xd2603012d0909050a02041409010606110d030e01020405090c070501050c031608061906110c0f031f0f061530091e08030601110d021207030c12020615 66
    0x44074040d01148056500034840b101507600a20140350041c0115410000c1c075501107821141802c0751240303285010014808a04400e01420303005000d546400c0915000020740384e51034000308070403601810703941e4012607001c410a4055500524004050350810300e044d0150b003032180d0242c14210307055441c280c0010b90314010841035a00501c003080c070303500010084040035203003c9806040e4035440019101c2608188a10046c4d00000d46125511074000025810f019032074032440341a01d622aa4806140d0301c55510009200c102801d034100c260342c40303030f040000c640d00100040384010031814104040850103501d154400708000c805641d480c60040b140d840109a81c0f400340c20210488a0100341c0c488a444098000400007070244520525100302d9840c4011003411003202115811008001c1000c0381d07820903045a03d4014640240005900380031000703440c1c030050101c5070f01609011620340141403080980d07800c040d500440c80100552103800207951180111501b000d107150251040c401d41c02c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 588971420 1250 588970170 588970229
    0xc12020c0a0603140c0f070b0720010501080a2d1109090102070c1e05030a0b010302100c0312110f071406010f0b070807051906060f0e150d260301 64
    0x84d038040c48207442d1100550024158007044000070340d54400d000010100701424151405004180c440241e0320f911000305801c1c108010001c0326260345010010803075800c011485144480d4020650610162401448644a50580c000403103050144446c8410422201a81a001e900c101c9001803183e071a0760026080c1e10898400070201e1340c1116081080104144141400f91054850030841030780702d8000c24a05030724010261270045010b401081542450a210035482d0160702c0c2003012070781c1585025041710040b05143c00050755a80300c3c5035002c3c81c03000c01c0c0d41640d4800310803281e07140c5460601262000707200b15000c2450107203800004610300b4040b40e920807161003c41d42d45c20b010b5503031981106a00000c901352454010f08988000352941500c0405480c2d100e100f00081c80e034200340600e107100741030760468034021401d90b0501c000c905c2c404c0e0011689440403030b88448016014900008000951107110400035034144400c1c0e07180b6030b0900514162450a01140045c0c600303803010810554 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 588972670 1250 588971420 588971441
    0x120210020102121302012c01031e0f1505030d0815010903080d0203090705031c03051f0806010e0a0504030504170a06050a0e0c0f014b0e0a05010e010f0c12020c0a0603 73
    0x307860f555030707c01a5000ba0400d070a44107081c160b60050169604402d020b071003968140c080a02c1d81d4060080c8031052440000010b4602500104210540700c0005054800c1c0a004100012042020303101a603114400d0580074640c010141c81d2243e2402e070300380c006504140c9030545680206117000c101402c00003030a016841e54240200c2c601c03c004d003c00c0d0f000301005840350404440c1e40b4040d071022148515850000c0444500605007523151005003001c3c00c1001e401d038020181402c1c00d01002c81c0d840000d89042e15030103402060580c4034151803a01d4500301c5403004004c0d030b04100800500046c551b00c08015030304228140c45440401d20100003680d0268070380540410b00180c00d2040c0c540c484101c60034071400c4070900c40c1d502c811000042a840c840861191030701808018030100f1a603010310110403840054500211090074040080e01d02a80301b0b000e00d040146912100001c648504010b00c08107800103041d50102c011000000e45408c0003c61450082c01e94440000302e0a2081c0316035800304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 588973920 1250 588972670 588972737
    0x1a090c0d3603020304060f120c11060709050f120c03010e0102090a060801080a06020c0f07090204051003050f072f0601063218090a0501051912021002010212130201 72
    0x242004070554411041517a5002081600c523040c1e1014090703842240c48664140e11072a00e40900c900c901440c01400034080740c108559801d00700b20316240d002c11030002e400300300c4200124074503c5405c1480e05a0700304040b41d1542c2412031121070f04006500802c6480320a0311403844142e00d50505843d110380c00e10950078180c2c41010820045091540940101d031100e0040c0c9000c842c2941c251868803400303400c058095036000504111500e08540000c0c01040d0600742404140303041050075202c1c0d0402031014041c0141810103606404c280b504041e0034490803562419150710784500d0990b02c8800340501c40100d00c0c01d40382040720742c5c0b050001c0000506400102ca00705610f410041110341c01c00307002e12415060110b04607220351b886401d9079200b118181e00006030740d0b140004200d19440c2c0040d49140e030880145040c021150a40031090005805540300a090408240101e00920030f0b0711294211f181d20750144190a10031132801e6403a14002d036603a4500c0500b51000d11880e180980700e60212 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 588975170 1250 588973920 588973927
    0x1080607020c2803050709021207030c0e042403081908060303030711070e07020102090102070b04061b11090412030e031227120417011a090c0d36030203 67
    0x19400940f0458031008401c0c0f10207121694a6541626003005600200e2656402140460405a00f01900c4c1e511040b50b1805101100c010380d0050081d003d140c0340940034a450b4038550102d080070403841c2e24403119103406040d059a8900748503110b40c00c5084402d14542d80c11a291031100d00c14240305006a00040141d032454481f0b030015652207441c00d80b50134140c019000000745048003815098450070b070710f070000759543e02d66800084c280034541c5c1203004401c0060200f8000303103502009032002c40710401e0160300c4036001d90402c0391840884040e10382e8003042c10000c05c4104800690800c52b1454240c9062000030300880702c60f9160701522901080600c820b1000405540da40046524042c003010401c04494074400c50040c10100e4040400c580c4810000b010004404000c405103044500c3c1c1000300814012000440300310f035a035100f440d20aa02450108500d64905e0f011a0b41210806034100409180880d070801809200310b0382d80200b5000c00c4880c0000b0a0702d00c1268601c640c981e028614 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 588976420 1250 588975170 588975199
    0x3051003080f0706061e0503010e0703031202090301020d1b080a020405090403050f130e1806010305030f0c150403090303030f0507090308160605040803040506160210112101080607020c 81
    0xb0368015980c156206512441c000984000104124082c80d520b001c0c00b9110300d0400042c1420755040c0058034205510519041002c0b9500219854200c0d61248001da5034048850010340640145c00c00e510780280703000c00318114594808115181600c40d82c682401c1c0e6a08c00c9501404ca02a5101c3d450700310665000140000c1d125a0007007d900f151803132440d0a148940c2c80711002480142c000b4509011442d0612501003002c1078000000b580607802400d940d070440d0b803640d07200c0c02840b01d8503c00d81c1e8007060f117408919042c010461000040d0050046515050400070aa0245840140c1c04a49040c2d00c58009480501443c0d200702410303120255a00d02d0b40d5034075501da5021040110402c03544003103c00000ea1207014542c0601d02601c0d25503241d0600381400e5040160140801d420380160b012a510459004140c03001c0d1044003110000340110542072001062041e0701500d4204503030750411090744c1006d03e801d0390603110084100c803407641c1c0b03500082c1e940b0382e0110329551303200000d040c0014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 588977670 1250 588976420 588976447
    0x20c090a0e33071d060307210b010801080102070c12020a0515180f0108070804020f03011e1107021804050a0b25050c03070b101d04030210051b03100519060305100308 73
    0x103130070410910703023800d61890361212007200446662070642e856072100d298607050344e030107803000b40900400d1000710310780040e80e40c5494242503984281c1d03072650054440c03a0159a10860a2401004d0140c495096030348848601d559031741c0042071b4120414542d46d40380c030083c102294104801901030319131403e284ca4824080d2110440288203c0c4d00051308984400c1d01c1e2800c3c01650b100701034140e0007100029080302c41000b07680708000146242241840b0346409651518620503400030404e600030690344460800a040180c0104040d004440c0c3c8801c1c444a0401c10b0b03081c0302115401038170310303504c011040e200301d840344541c0040c1c0100303030b200380300f0781001c5032081c20740e280c00454034125586020f944650480c44207075a44940320070004100100410315405021406000411840c01c0085182030222109801101c1401125542c0003200161100100c00040c40140c00014940d01c0c061411400c00c50584001c1d0161000282c185000300e03d110842c0c0390010141c83d402094542008084030056 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 588978920 1250 588977670 588977677
    0x20607090e07390b0604050c0a08131e020306060a181d010501080106051503060612060d06060806090115120222050c030412020c090a0e33071d06 64
    0x121140707664401203035100803a48001c0804140f0140c4410100d181c981424005404010b0805020703900b03007070400190307000d03500449141903030b81c2c108038629480301c0c0c06c03120b117182100d1002441c0c1034082010440440400e21103405013071088048034516610141841801021446003d40c003a599990900719903035540c1098600480c4a2050014804c0080109003525001c1e8800403190355107002c2805142003818605404809140e5180d01e1402c25401040d4036108088ae281c0084042e8400f2501943c3c41090303007030120381c01000030301119480b40c81154a503002620440d9a40d803a01001006214002c46040c080700d04080500b0407144d80e030380034481030f064042c23241c0040b50017101030f1002d140b100d0700c01e0502072010121215181c0c0740a282000700c0e00c141c16540419980300034030741c403440e96807107141c5903001c00c1004000c00c00d9001641d815180030a200700048036254264806a48480e10340422130381100103a040a80c2510f031840261081d4881c803821a1400c0100c00c0b075400d2606017140207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 588980170 1250 588978920 588978947
    0x3020901020d0f110303040c052805090601030209090403020607020c0d0f020f03010e03040611070e06091311040f0b031c050307080705040f171b0a120c050607080307020607090e07 79
    0x50240340d001300306003168800c40b03040751807a25201050016061010031030b0303404101c02e486d8040d185007507000e50500c12030b10700c6203c1c403c0b80602c00013081030342310350140c0e0003000000c2d0181d1094101864041d446000803180c28005228170540d60000b845e000348241c016a8000060303455051107a02805110b4030a105196015034861341c146c5041231003000107000034102d5070f46030013a11840d00c40360b074103002403507110f0300e50b0441080c2400701030380d12142500e070018004030f43c0210701e04817445c0007c00076031081d0800e50710a29080142c3c00c0040260450314030100c044080c0da5076500b000c001c541141e1036402011740014024000545981d01400000b5002012800d100341030642c3c030b8000907104034981e0032141202c00389040c2a0311950040044209114414030445800000c68021409021151240a82a03609503d520082c080c561882d80081c0201800e081e6403541242892803140d0b1054408100510480c800038000070321a1101c0c606884144004400540b40d8200c11904406140413 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 588981420 1250 588980170 588980177
    0x7030f0608060403180f0909050c100c050d0c030f080403020a051c030f0c050306060c03040e1914060609190902161a04050316030216090c090501022d0a0b04060b04050703020901020d0f 81
    0x1c0981090755040003140e1780f000259903d40d521a61807030403d003488008110700c001c1c0241200fc6600180c4c102c1c2d2051070b04101d901e07086681d9950f904089141c244d150700c1c0544140102014840130890603107220007074016544090213040007200c981c2c004c6800d039140d41000100c0a0010a601346014802070a00541c0441141d041c076455192a01803560252603401c41034401c580b089d207403214207002d071001401145d90790515501c1c0280125201e0311540310070500c0b40d4120051914500704603c03001025020580c021901d60b0000e0406c1c103258403000d4410b4501120a0107030719203519114400c580308a41c80b401640c241030a0300c0e00718480c5440140110306502903145084001c20403554140000d0803c040701040e05002e0290240444c000ca030401411904104a0b0265041610094041c1d0012030202000e02d0026184e5181c1401d50f546401480e5881002c140828400030360400c0030258800c0b2000c01c050707182e40b20705800300d20460000d14050b810036080303075000138015649466444410705 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 588982670 1250 588981420 588981433
    0x3040e070c0c090609020d0e010b03072c0a09020f0316030605040f060507030b090a0e0705061317010e01050a060302011706012a05010c0203030402060403080307030f0608060403180f090905 83
    0x203d580040d52002c1d0040f010840d800311b0400da40c00c4550240307945441c00038000700141060740c0f020a403506010f01541c1440c885d02450892512000003000788010b0b0303400034501c0c0d942004000340340900714805069102e401c102180031598540400c0c0101082d601c03041e006591459a0307100e60203090300810070b81e55811007035004408100180205c0344503000c603960001c2d2681180041204802000d0000c00b96640b504d1008042528005038010554008a801603156a00215440100c0c0642e401c4031241a01c4076440c03111a5605403c500a101c10250091210750b6503c0c101c82e0850303c0710b21000e4002422685405060305507184003d41021b010700d00761940080190344180650002000620b4041c0750702010800e021003841401400380c02840035602d1800d1503000120140110300029084000000110386024006d070b01191401080081c1440010b5841c03c145407296000c88096010900742c459460b0b40102d0300d000c92060f101080700d4040003a08050701c11004040022046a00b44142c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 588983920 1250 588982670 588982679
    0x1506040509060f09011506120e03030702150a0b0d0b090106080d0906180521060112030f1b0515180a170c01020f070605071e02060a05090a0b16030e03040e070c0c 71
    0x328074001c0508200c8d2036806404400005043c1143d69044507001a50418010300506a9000c07880707802510450340e4107442a140c20f480b0b9802064401e0100d079000c1c00582103101040b115581d40392040302c0b8080200b01c10307641d0301000c548400c00091928001201c2110a1007414010540c0c0d103d1503a0310322060300c60a031100c0c08030341042078441251990050745038105002400070007565000d0450a0f806802d2001c1907500074000e03807540c070b40040901c030858404040401c81840c00340c0200d45c000c02105d100502404480201c004c05861403841d80700404080e1a2032034000400c1e00c005944155904114141d420201000d40c1221152050702d5400304a10742484d00b420300a0440d150045400007540c0c2001030000d000c1e8124015281006134018002c4504d540c1c0202e903240d0f1241965601048070f540307002c1d40354180000300500a01000c148020b08c00d016000c8030300170742c85810685040154240d1682080e03a24090b41c420307074505407007050000305403621400241d00914483c0d41d10b2003a05444 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 588985170 1250 588983920 588983951
    0x307020d0221160906090b03060714190f09080a1208090f03040b122413060302090a090b1b072d0f0b0601050403050c0f150c1506040509060f0901 64
    0x1e41ca408100380d80007a03c284201c0d51076101d0311000b810603040030405401010040303070f00c84000a2044017407200c0700b4400c1c041804450200d4440a09545070000d00c01c2c04100040e040240f40c42e100f43c0010f00030300700840c600c00300013412900c0701d4200c40d021b00d1202e80d11104488240005044509600030080908010030003000940301a0030041f0301d10f44c81d0301c0652107041c4030410050400107a04c4440380071011011200d002812011400c0c0e07a0715880e018070240300d10142000340e10007500414403208101c442c0440d980400c3d0401c4c4910480002c0791182130b0520300b41000044000300010b41001458002240324038016031404894400025011a2542c8107455260181c1c050360200c064000700301c100300f9a1400345034804000d00340142498112f860301c95650f0303e1880c00600440b0121000051a51040022135510f40212000b654031f10302d100c020781d00c6240705c4200040f40f03070306400860074600c0e00d4003d20b489081c14000814143d40d81860351282190041d240078015562880c125040c0300d034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 588986420 1250 588985170 588985183
    0x13030216030b060405070f080a0902040213060c0b07050406020c0f0301201306020a080409020d0603020a0909050c0f1804030e091501120b0303040626010311120307020d0221 76
    0x6190a0003503883d042d01413200342c40340145200108100e12080c9022950008801a0800c00b109c1c40001e0b1003000f1301c0403900a2084200b600700703d250307104000a01581c00580103488500c20f464020303054445a80688450049000384005a00409104c2072039041c4010036020094004001007411910091001c601c01d00c003010301410440f00182041c611300340c0d494100010b0030248020402c4a056171100b14282c00f81e4010807828940015410100c0000d40e00308601071a00102445001a0789040243c02061036560485490060824007400c600e000010140154005060094110003c0440c641d445400500c220300b0b001c44126100d400e52501d180351846802111000c04004041c1030001d8498034041c502c001101d0304100d241190f5880120544040b22401e0070080d48005040e100e0103407015025a501c0d00992058000105122240c60301956000042d07801640a02584c041035440340318511029420022500c06400141481503544c1d4105400310070440001e00540c10060034480d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 588987670 1250 588986420 588986423
    0x9030507020307060f0c060221070306050420070b0606072a080f100b04061a091c0b0705091f0806030c0a06080a09141f1d03031303021603 61
    0x60010954030218142000201c0c043c00e8203050200741013036403d000425410500000820140e0045021020420014041500d8407000b10290788585018440203004284501c9018451401c1c031294110740400d44643c183c2104240e110340d45082e0642d182c0203001880130b000c042d04a00204410800306200700c0b0700b082252009c2006a00c01008410309141800780c50b088881550814090600304c0350b00080c2c0030f03500c0320078a0700c04900798002c17100050040aa5600850310040ea80707081110307450440c0d00510141404503003885608500c03a0000030f80a14507100104000841c20118080500590140c040d04034020010385d400d844045c01080740d0303202c0a12a00c00b050354202405298501031181103040007091b01c40201c00c914103130000304868405008044010707501c001d400140084590541940e4814100312517000c04001c04401d0318441800300c0103182803038142034500000d071000b80c41080140c100011805c64680030705100c446100400101e01358805ea82c00081010300c031898403402076 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 588988920 1250 588987670 588987677
    0x9030803040b060406050603010806190615030f06140612040609060e0d030507110d110f0105090303151005040612090209101d040b0f070c080316031404020a050d05100903 75
    0x60400c0c00500c005d4940c9500601d00c5107809100500090a0028107a075219100500b06c8003a03058082d1054003d00990304071890b5242d55500d01c4c85080d0f0542c00004500e0007003401000201d5171802e4000500c003c0e11041a4070420411407005d0b281d1400384500c0d0413034080d510020300d0b210313960744981c00c491b00700c42410002e801450900d40495058820b80c1c0d80039145060120401140741410b6450ba42d4600c48041032001e460350540f0251010031412444408a130000c101c00c2c140300c0141036507908100c901010058540100c013041d81004000701d00908801c0d21020b007064103154040d90041e030030005204500e980c0d0500034000d07965451803507006a030308424500880d803c00c0e01140b40030b0b0b00b5240e20b020426000080c0000036007400c00080d406203188090448944503a00116055880b004002d48070010210900402020855038002c1c02071003910b0800c01d0600d00e0341e0301c0302880012600607511880d109000c120710700b400540142420310039000e4030f004d00107000b0231404407100b180c02600003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 588990170 1250 588988920 588988943
    0x40b0705130906180c090b0a02030904050a020919030201080f0903070c0905100b07210512070f270b0309030d02070501060f0e01080601060c0206190206070f0e060702100903080304 79
    0x51101300c2d101a9075824660180310501c803800380035000c00903071700c00d188001d41c0026a01c01c0740c40c030038000d0710049035006006008a0520b0126a0080c0d040b0340c115902c91300c00a030079000f1064104080908980d410384030702d0307800c0d56110000200541d004102c040c1c58003041000500040c442400e4002030204648001032605110b0b006010301c99003608a044411b0b820441840807400c6000c10820700d620701c03e480f0080c0c6107031600885150189010001e6040f5810003070011a07a0445031501030300c003a554550900850030102900c2d440c1980381d140107420f8164006100c1c0c000141c004542c03000004d4200c3c0d14200101039100c5c101da220350780c25103160b50343d07241c00d1202451a60761400200308201d5410300c0e03941070482441e166070040c03040c4801e01c42d030140c0701e00c219103440c1e00741d0b1030a2035000600c10342c0c640c0801010751142c10488192000500c0c90070f100c10220702801460342c11540240c800790030700c0d00a500f03000e08420031410740002c0c0507404038000b0000e41c111006521903032003200c85904 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 588991420 1250 588990170 588990179
    0x1e020d0206100f031202011d0a0302121c0b0f0d050708010608010c02060a020904062c0703020c07030f05100c021b030718091103120c0c18040b0705130906 68
    0x401030701508101d0612155a0100401030280f201d10081d07070740001101d042e00080c0700050f801030104003609214070f490320f89071280d080d03004961104418003a8082c0c445000075840c142c1e00700e210312b0110340180002240702c1c0800390102e0340a00d0861002504080703810142d600004c451913000c84080b100340e030042009100700c04080c05000010007060001f032107001c003100e1000c2d4072000700074004e13400c0a81c08141c0c0c0c0c800ba500c43c1c00c11b400810400020001050b02003442142e00244852000340640c0c0300804921550b01c00c2c400c90381c0c2c1c8040b100243c55541c0c250381c0c071044c130354902480559503881122042180c101f25841050300d60300d0560000c4c103d0300401c4050350060302440e49a0b82c0300e9088410b0401c000c1d034144480f005010818540082e01000c00c0c5882480100807084141c0c143c411840c2403800c0385094801050910201070407181100640f034204804101c02c2c108902c11b840d00c02000c03500084095589036040542c2e0f003070103414481206101243c50050358041c450054482c0320410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 588992670 1250 588991420 588991423
    0x16020106150503070f090504021204110d0c051e0a0f0510050f1b0115230a03050c120312090a12050a0804030e0103020906030f10081504030c031e020d02 67
    0x800410380c1042440d01c0464041015000e800010310740d1090180c00d081d40b1048501c220410fa002c0c00004208548903485003020007050201103c0440d15030042111401d06880c00c40e617000c622a900c208548003050428081c4007260000c0c00c482c8000303144112590000f59155540076005c0e0110041c080345152a2100b04100d07074102955140500104009203144266101c0c02c440c045640b10109081503187c00404a005001290b506500056036003c00708224001807036481c81c0100c80d68034020121a00c1c0200110300c0300e0f5210003400c6500881440c62035042c02c40c20354541c10104d0781900d041a03820251440c0000040b61f02d00300c590001c0350f01a00304240944048443e0301c0d180780907811b104042001a0228201600140c18011080207801c8280e210760112400c0303c90203000b0b1a164100256406400314040c0c0740b85c0c010000081d00402c1080d0005070400d4488065041d5464903280e40c0ca06860406804105504014403210880094002d800100b40b5102c07aa41c024943c0410520000307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 588993920 1250 588992670 588992681
    0x330f02031b0a17060a08010e010f06090c170408090907020303010618080c01180f0f03061803120f141302090105010809070302091e07021c0801030b0c03150405160201 73
    0xa0076003031001c0c00010300c0c469012008036501d45040e43c006095407103030800100d28070002c1c0c1c0080e40c031f076007868251054500c06410a1083c00b140c580280a2982c80d01c40c6d8400b50b402c0c1510120001e909690440165002e0030219030300309000307110176881e24039003d001c17030103080040382c0308405603000000400441da4060340d100e40401c0d904011030b840c1410183c209403a8407410f007000c0d0410209098424003041c205010500030300507180c441c0407071139807a01ca04054410340d02c0141c0e503091400803d0302079040e28510405000c0c1d0700d6941c50030048000d4003103800400502040c060003541c0c3c0d040282c3c0320314a400c0d5540c0a5003c05070203191124036841001380c40107058101c64100800b400c2444000e0340001141c1e400d9941c101d941c60f0066441100b401c0c2c400580307402b842041e07071414091041c082d8020502d0007010800c50b0200c25580d0b4001010341d0745400030310004103041d41c1c010014988881e9840990740041d00001d040d1070703140740c100c001810b0711015682112030142000000318695024440e9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 588995170 1250 588993920 588993961
    0xc08090c0603010f090c030f02180306090307111302130f03061a030304061103090306010e040215090603012c0a0e0d03090807030818070905040c060507330f0203 71
    0x95440d5605010200440d842d05100b250621a1200306c0b182007107000340c00110f0380d075081c640704544840842454000c40701600d11221301174025000802d200d44000300868440a405c100580701d08031864043c0310a2002c0d4021200d101c030703402d01415a8601400c0b05440c000c01182900c1c0e0202802c60419204480005c00300041342402180209031a44021064404440041c01d00c10710b103000407203415083d0701c110302003158140202400403d10030b8034004203030f0049000366031042000b0000807408c10f09105600000b83e00441c140010010841a9004a40301e14800718203188903103034a0500000321075099640d4a60b807a190b03900f510000c03004110000f8040e0b05407502b03100c143c08648402150303201c0d41c40003030101301462000900081b0541780306003100001c0012951841d45c0d4500c0c0d140103120640301161030540f000c00005201d44a00142c0d60902c2d0003c0c0701c3c03444000170305c0c0046600012000c5c40e2401e802840701c4e40328003040c984214112001003640c00350340c902d084087e40c00f224104080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 588996420 1250 588995170 588995179
    0x61401030e0a0b100f09020c0115060e0609151c0e010603022d031207051c0e100e032a090118020711090a0f0c0509010f120608010c08090c 61
    0x1041c4401d41c000081000216030403a02c40540c9450b407407850041811160010140c80c99440030010f90004240d0007041c0a4507500000c11003602043c0182c17161481c00d1268100040003030090307540c00d07d0828020321040e4001007446c00e441500120b0320255800c00c00050305880243c1c0b40e030f4602403059000c1c865880c440a0020003089045600048403002c4800f0703011004001c4a9005c4c0311002810305104108000038202d4207101032805001020358801002182c1502501018001d00d1101c62400e911803000343d100c0e440071200880034894812010a00b03c000c1059869100c20710381c6090041c144181d0840031941e46501618501078980032203500309078043d03100880100a5082131981d2040007014002c8007582c0e8000e94201050f00009540640c0d6008044e203040c4504095668003003103450304001824420440306000c01e6582d401108200344c046500d12020841440c802c02c0e08101582d003036640041c0442c0c81d101d81d50300311240c441d0000d0100d048041030140194017004089542c036030071603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 588997670 1250 588996420 588996431
    0x303120103030c17031e0a020708070c0f090902090103140705120c04140705270307260d02031c1d010c2d0e1305090102090109051206040f0318080106140103 69
    0x2820440c0c0180740000c07071801040d00004201200c01f950110b425a03a00610300545400303550400300b02400480c405ca40350394510500000e00d024041c040d8a080a8005205d030420707a1031031303d90070020b0b24003c12400700e902501c040802e040da21020f07004600f044981c0140300da0318504040c4022105020303100c0c1c0302c120420b01003000883d0b015049030348a1405495030101d010000c80c01d036480314a03100b03903298503019130540400c5026201010369103480398040503685000d07001da545611000401e43c2070006070403c01015081454640700610100c0391a032000a400c1c0d81d2400c1020342c00c14040403015665115107035101309a43c002e51032000001c021490090320b0500010340e4100b11420148a021300460034091451680c40e9680703038412a02014043c481880d1090800c0e00031350049080501190060001107841d00300311b01c0d080301c481042002018a61200d459040c4103102c52700080f0b0411011803012a2010000021480102090000403400f85d0030302540c03c0d001c10300f09002038105031424 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 588998920 1250 588997670 588997681
    0x1e05030322020a0506070201090825050909060a0b0312030a02030403080108061915090c09050a0b0f04211a1b03040203060a0f0e03070f0b060105090315060303120103030c1703 77
    0xb2903043c0b04a40040790915561541403006807004078607a8403203901401544902441c0360107081412405250250003600b84d980c96201304400742101b43e5a0745250344c0040c00195422026902000350004000d0407180900c1c1050700005065008580040e0900c0d00401440101074000780168050189540035111a151102c0010100700d00c0a1940380080c0e107803002c0502c0d00406481110151404075400d201401400c10050b004284d240310f458001c1c0320845000545101040980d83c85a0481c810f0750b14040c80d000307406e0f8071507451660020f00448202001d000181076110700100400d034050399108240b40912184010311180d418205042004004200060b41c0200d0000c0e0f0003a1030243c00180190200992030050504500418040c07100140110901849c00072041d40e0600c075880700d109681c1e0303400c01110140031f0b4245054240e0f01682c4100d9142c4492002c8580c42040a001c8a041120300071000441003400e0b8015008111401e507114180b01100b4000444403041c1003015145081a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 589000170 1250 588998920 588998929
    0x30b12010b15030c0409141608070e06130e0f012c0415090803070201020d0f0204080c0607060f11090f040e070911040f0311010906030605090609041e0503032202 71
    0x80600c0004110b00000040e05100001044d103010f00440d40d01004064942c030210614484280e03200c01c0c0e01c0e241c6054920600d84030342c2241d841030784166141001000040284405504014000b0049000c02c104c045542d4a005030340601c228540080e04619524210a00040c00070020b1480010394613505286c00960541c50141d070455070113074100c041149090107260042c844e0b8680101000000000c0c8100d550341500a880c60030f20840003048183c0d140e038403403003c134030562164500319040303110342c060740e482d0907800740c04441d0150101041c60502d00340403001710344030221601800da50128400c0f01c1d9003480342e82030410300030a40701000305524442c1616a0f030201c138032030428400d0301c0f0050000360305405000da0700100600c0300c414030708648034600360f149615100c04480c0000e40c600e8002600d28130a0142000b2114045c2941203661101802c0c841000b10060040c1d0b0301a4143c3c4005440307603c11016040554000c002660b00da05003101c1c0c020310307a114003101c0b40c45a181d4410704805603a5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 589001420 1250 589000170 589000189
    0x3160206150f030c0301051801060501020f0709050c130f0f09090f081e0c0109050d09030b0f0c04170106090f0b1c020d020604031101080a0c0f1101110a030b12010b 72
    0x42200d112030b8110103403000900c2c2000c20302c1e03d1500344d404c0c4000d0229001c404500e84141c003521500070710202e901c03840120380d0f400d050032220310341340e000d8001000504030b2a400b860f080380300118840e01e0b22204580f5100c1c2200300341d00c503a10365240204100180c3c241401040e000c3d00c1c01c1c80003030190054540711050541d146440c0949920300c0055940490410181e4944200602088250302c2d07601c1c411035903000740410441435600f8040c070203140c240309119000310002e41c0d40c083d40341daa003516000e1030105056130050221109032001c01c4081807a021560001e00b4a80c940030000ca5114103202288040c1d400003d0b00b5068681000d42103079030741d07444031032480071a203840c1100f80c1100124000071310b100340c160b600603400c0900040e0100a00465000ba00180d080030b8903001440e886648440d4200c42810b07003000e000445211031007160074841c905264826900d8000455003440d000c80f0140c265104c400352402103980c900301400c80d800c1c4402c500c101012100000c016030704042000c03560048 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 589002670 1250 589001420 589001461
    0x70e0102100b0126040213020705060403181a0d1a01051602040b0d0503070309060203090603010303030b0109030203010f060503010b0f060a08221101030509010c2f06070503160206 79
    0xd40b2058900080d034880d4680310751141c60b0f01c04104003104950580070300050280d83c00c1e400342c2e40d000c00c0540c083c1032600072a980c90fa8050010300745030740ca54400300e80b9030500d00390858010b403007008009018042d020724100040e004018541d039440c1c0040d00041228a8481e65110055060f071023a1840d0780c101040e5810768121107041098018240300140040851000059108801401480a020000001c0d00f0010720039150071004035102d00081e80e0300d0140070182c030b5000000700010300020f48241c21a840300f02042c1042000c964480d030019080d2580f00620f85580f40d030701d2a040190346800d004400141301c09175408050711829802180c8940b082900c4401440518408250600b407014168644090490f141500072171003490188444190302400e5400281000c000c40e00c0758206100b0b0710400010f0b62101b0220f021070080007000100d003074650502045032074003001605d0401740041841342034240e480564910305030078001454850305001800310340c4013031304201500381d07100398400000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 589003920 1250 589002670 589002703
    0xc080709030201082701020a02011d060f041403160b0603070509010b0301030602030711010f051603020909060f031e0c12030a0e0405040c081005220312020a030608070e04020108070e0102 82
    0x45c0001c42602400080004084905601c001810307081c8660660100040e88144030032031040700300314034000b035440c0d90650361204070301031001c00f2800140703c1c078030804080c0c4c0c224820349041c030f682c11101d03280c04d038030825055540d181c0c03171300401c103491070144901c0025182c03c440015003541401107114980c0014040100a20350010108920724040c20340034042c81060380092101003104107062026020948420190118103201512028040e00071342c2c0013014003030a5000c00b69521020450340070710416106826005000810050084000c40503a41941000c020300000d1880d000303100c4450305000c030b40c000300d030800e102108981e5440900500b03425001ca40c04100c544960600740d42c51000b540c804005031040c040030464420759900241d1098160380c3c6044140d4000000d02010040344120050009090035904031004003540d003e0000c852052030001481621018200c1c42e02c05241c01c10b03600702034020100000c560f0306c03414155004540d0f191002c0c0014040f030010307554100c000b102c603e48 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 589005170 1250 589003920 589003951
    0x90b0f040f171207030b0105120403050f04030f0203060903090d110612010608060102010f0606170c0706060f03121b02060a020f19050c03030309031b0703020907030c08070903020108 80
    0x1804000e04081000c99003080100741c2e500b41c2e410340c09666601c840c1020030150004000a44090300034850318182081c1a12003500d0844071a039040f001d0500107008074240f00c41440031000009502000c2c0001e1445015280c0c0d040c400307030040500d803002c000d1003804039a10403c51454039450303c400d003038031031640b05280410240004001a0950203005a04c50003200d60b0000000c2c5594002d03040c03070082030207030000c02c18030204144200540e0b046000303540c0840c008c1d41062a540a14180d81948071140c0b0318003a08000b50742d511001907500b01d90000300400c086041c1030050100340495a00540000d041054507260803c00600301e01210b004042d22540f0003080606d512030081c495a0750007520b000503031304680d030030080e030703107032401c00c500d0b00795202c0c40785e083c190395103081c004100c90141e40b681e0020b60400310380c000109401004085800714074000d004000005865845460740030b4681500d000c03600320341140c070041031010000e080000304a143d800400160340c02c1050385411401506a0290 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 589006420 1250 589005170 589005173
    0x90506071e0c08011505100c0228030204020d090215040302030601090b041d070609171b0310090b1902070f0209070215130209100b16020f0d060b1201090b0f04 70
    0x201c2c0507103079002c50700325400d154100e03144d0b011071001c240c1550012500784860555100003110317000880d0100a410031844c500d10542c030410784080d803031b5400b00c51540c0042103480c0d0f80402c1c10307a080b106801c10100c2d25160290110b1178030f054050250601c00001908241c9107800080c1d440c0010301c11035030305580d280060f6540d030702c1d9a0421008221032082c54400c1001142505a0701c421a10446001410740c0e00f022510038403290341a180c5040308402011450f4000611000903054003016a90520841088140a001601a002d0581c0c0a5080c2c00c69520b060307008103046d00451107903042200e20400c50742c4000740e110b0f8002030940f601611704840941d168041a4544082e4080301602001104100081b41203080e00882140d4400d9480e100302e619494000305c403003400360042220000040c0305010b1031048500c4600d07141d900060142d21000d030502c1c0403032000310644500b92000c60704e640ba40b2203035080c0052840c141400c084020048940c860b12440203614000e09220002500f0001040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 589007670 1250 589006420 589006433
    0x90a0303050621060106350907031202010203090c0a150e060c0304180c030605030613031202121006020705030705012003041205010f0621170a02010c090506071e 71
    0x683c43c2c4040708541400b0074800100d60381c1c00b092143c00700050010800c0200901d050b59450499026404c20400c00364030f60402565032400107100740b105101d00c10700003000c01d0780b0106060014103c0d0f000140c0d0f0b8180341c9891410103d80342c1c50b9074090012a40100a0380742c0c014803142c0c99030340320700e405060300b001f040c006901072081100b00c0c085440301150215011101c0a02c03103007d43c00b5034074200000c2d400c89005400f5100c25104003941a000040040c1e41006401a810780b883d200785015030807900d180440340c00b02c2c0c001c2c20002042c4243c420030404540b0725111b440c07000d00041e00090500501e04800203548050901680c0e04101030103c4012a07010355514a01e0824550425661145d40318113400e52603281507281541c0a41c242180300c0d42d4407183c2e10901c01a00e507010741c103050850300007080641c01d130f0408030201c0d2030000c2c035441d060410080c40040d100301602540081547c3c4000c450040ca50760445d000a0701c1207a04009402c009400074484210300c490388000d000906466003041c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 589008920 1250 589007670 589007689
    0x9031e05033405060106110307020303041d0901091707020a093603020c1c022116050609010f12060306050f09150c03060a21050c0603090a03030506 65
    0x40641c4000300e0007503040240c4041c1500d03224522806480442155503007101412110400501540c200324014011203201c0e0180d48246040d1204403071518100b9030100b85141d0040c0d108012a0303004800c0d0700c1d6246c030180302c4680c002035010300a0110300481e4a840244d10401180404031000004842c030845d01c81000040041000765410003140c40708240f003003030502c620002c42c0071100540d0629511004040708581002c2c1d0140e00400d850703641d820611110b2004c10a6010b02c00480e1042d4a00503584d8810300d89152051640c00f1262400110120b441e00310b412209020803c0c1542d4188000c1d12010280c4514207001d28246110b000c0701002a2070000349601800c205a09290780032080c094107030000e0b8081ca0210045007500c1e6a5180e4960712406044c8000881a017400f003c00c50051546014542110009002200e40744c1d8a0b56481e030703e03a10701551600052000d00000003400700c1801406c480c2c01d07050302d94600e54600014601d40328100840003c0034540d4500c04540729840c2d00249 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 589010170 1250 589008920 589008923
    0x50709050d050708120f0d05071b050a0209060d05060f040f0b0127050402060702041e02210106020105040b011a19180504021c05040602070206070c0e01050102030a09031e 75
    0x81030089025810050f40383d0750607020707040e042d104010b10360080070b981c0c0048402403444200e485d824040342105450103014064000000c10200c40140f24808403d9030802a86034401c42c003c040906061050100d14071000304510301c07644107944c070003001c200086411540f00140e01c1d2390200c156168135003914000400d0801411130751030f910001c1102140b041e1414000e1842801f8040c2060440405074203035402180d0007034000500f4010880141003580090325002c1282c10324008406411444400300c0e0072000c040000304e8040c210541404120078120307409044a440244418074181d02d420842c0075043c803030700000c2d40f0080c481510201170741040c0c50f00340d00003a0f000310600e030104400802220311120040410801d1540005582c980307442140d030480504250750b00c04002550b000d1008100c014800d84d4059020000003006a40e00e00042140501c9040b01c40182c0d414140c0c00344071b200c030580000d03040d58410000342211640103d401d608880e07105003041e4428a01c0c09543d0003829842c0310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 589011420 1250 589010170 589010179
    0x60608150922030804210912020d080c0a0c08030a090509070c0609140d020c010219020301020904060902030f0c03070c230604121803020a1203090b0409021305040506030c0405070905 80
    0x801090781c00404d242c000da000c1c201d03000000101e058401c4040c4100107005001ca40b80140c2000441c00325646101103c1c00148403108004150301c070b0141c554400c00c211546070b0400719040081202c58560700000e020712800442c00c11803038841c0030f461140e09004941c80b0b50071070000208658824198060115030003c001d22014000e441c201903d02c50001c0518128002c01c0646800144001071107492448140c2c024240203d11401179041c3e1510064243d070503540070000301085071914040c050080107007542c010307070324039181d801c803940b00340d0150021042d10010030a12100c02da00c0001c1c144115007001900304002c2c0107100c5548074078141400c403019070107200104014010301c01e40c1601c0000c8642c40d40c82c107400e101200f4000034460b90000a50111342010107100c450185c81c0c888403017601c07a080c00c089594803041c201e1201e8200b80d00002e2000d40000e6010010601140d10381c0041000360340500c81800d24400081c0c032103c10fa1a00b1340199136a00000f580d85110321a54001000c0252 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 589012670 1250 589011420 589011481
    0x40303020f0c19060e0c012001060e0907060f0f0f080606300601030605030312090f06040c08160e18011803020f1209060703050d02070602040801020c010606081509 72
    0x100d0140c00c0d0b054243c00b503402c40e26100f034580c0e5a03130011802c0790707a04e44140e4a444205c0c0c3c22071010300800c4818240c4d584650b60701da401144820780e83d65107500828071320000b4070115191010040c06103030303126580c1041040a4000031900b41d00308440456002440c140607030700d55503400109026014070082c001c04020b080103070b0201f090b201c070351084107041003130660881a59138000540582e229403040c103405500401411041d03c4140c0c0c070103600030814109841c0c10032015800c0300d2400e101030714143c92142c001002008401000c111491070504681c140345409450720f131241090110050481341c2c50710748265240e120140030351003450024000301c0003601038041810001d64400400c4070100076413080810004003048103c003030303c0a05030001c00d00b504e000d045540c21140384e0845054460b59640a01002000034480d00103007002d060010001030f1581c1e9482201400c0d50074646c030a81c18803444500344120192000035442e02400190b46c5510345880c1c134201c0e152000d251003001d950041201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 589013920 1250 589012670 589012693
    0x40312230412110301060f09050a060905161e050306040207050109061503020f030f0c010c0f0b160816020c0f130e01090309080c0a05010f020a0221120f03040303020f0c 74
    0x41d240c64907818000c81d11000f90f03119800030b01d8202c0e5903d00690352403061140040199807056003100740d00480303065000c10390310b03a2118031206468040d54a901401c44004184031400c0c1e20011440c40700d41ca0504880c0040070310311024240e0710024240902803600000d000e81802825006114220390040c4100903100d0860040030044200f40402c0348030340384100c1040403a01c1d00241a94140c1c40c00c40c050b02c25030800344e0056034541c545400c1215850701000c141804240808112403240c2e0f1001305906000d03003410f40043c481580241503482d40f00c0282d81c68994a0350000301680b04040a99000120387e41c0d5034001480420341108581606040c100c0800740c2ca0b030306412030007045210f0b440740b20115496180316521210710100c1540c000314001010042c542c030038008046502c03540d0054800741d041980220710703550b0510144150001e003595170108081030401035562a00f414042a0b8144000500b4003040c40c44042c101508064001c00c503464440014000c4560440d0710710201e5400c140c42 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 589015170 1250 589013920 589013939
    0x6010206240d060213080319031406060306030703150c0e090907090e01060f030f0b130f0803070c0b090c0f0f010206010b0c1c02010e070506250813170708030403122304 74
    0x1c600081d00541a50302170080a40c0079000713117030ac07540170f00124144075030702c00d01840859000209140d40c98402c19400101007044e07440401c0720111003183c04181842140000b901803a425074415018942000800c2201107010a0b0101550780d850400b217440140108524003402c080c0e044240480030034600041041034a0412084091241001d0104c5a445540c1001800c010007809050740c00f010a0080005001d00021540210369003420500500f142e20f40b007481ca41d0403650140c0d01ea00464a4081c680350600076048040d03802c07984801d4030703040300380005e4440c031041c890040f0099011070080c0c1141002e201030118011105080c004007a101c3c600203028110b80000b4103224026031102103510304022084500080c3c000c40e035090303400d4501034505802c0c903401c1c0060f50002424445d1469640c0000d88610081c110740c0c07903d5a02c6403080171910b05003d900c0d40001c0300da91080004000040b01200202c1d480002c80c10f10404046000c42b800041c180500c100180c9804002000310f04d400c232 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 589016420 1250 589015170 589015177
    0x702121c02031b0102030108030f0f0d05011715060d03031503140607031b0905010c0201020703170c060105030307020f121906020a031b090b0a0e0303030a020306010206240d0602130803 81
    0x8076680780e101120207005130300303d2101307000d4084142c000300080303504080d410004002104102c0d44c21480d2810718403e11045400a81140313050148070007441c0c4d03e220b800c124102c608800000d083e41c1c1c81c00e084000905400e901000201031603111160b50311142d805c200600e00954000a01d84401c1101c030b0300d55521054100d8882000c00d28280c00391000c41c1200c1480d8214040e552500a812410403006403040201103000700c1c110320414002000180c07500b08a1a07800c900d51070800e86800440e0642410003005070001030007a8024424000035a07980700c5412200c4405581c45814030400524940c00e0824821501c4608480324840c1400c00205a000304008280c559003007102d0f003090f0386403086a00d042c10a01d4001000c0303000c00d00010444034003e2050640c1ca003800900e41d11108003003401c5070411a200f6540550110400c60390b03503014001c4540c410500c1c03000344039054003048003521101c401520540100c0340584507400f0480341e58102c1d0108071700944292800d941d2071000c0c0d0b81e65030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 589017670 1250 589016420 589016437
    0x4050103030806090a1b0c140f031306030b0f060f0c0f070303030c0c03122408030429031603091e030f020312011e03081c0b0904080702121c0203 64
    0x20013a00081c0c05a44034441c175180380c01d10001d015a40315074000100c400490790b2400380e406c800c6c00c518141074a10b0802c401ca8034070007100050b5856100011034a4202d4801c2c3d0302580600d402d045c40c10f10b45503144c00d603c2c01170000c1150120f48544840b82440c0c01130281c2a1019114800d00e048103c1004001a220b07003100d1107179400b0700c15130280d010100c5190482e0b50300140030842c80003e26a41081c6500001d09640706034400c0e00e413510b4095008414855aa07001c048241c000007002d00102c904840d62203000390312207507521145078260412a603944002410711240f0b85443d4096150103201b1f802c52030030769400110088024150540b07441058491300801c0300840c015074542042c141c000300c19a40c012030780110b611003583ca014002d007044c01e0b0742507203225101c4103d140440014070717400180000400416812415070070013140380003294544e07031015100b00d20f81c0c0d04200015250304221a46160b040c0d60f010004c0d800005c0c1280340200c0c1e42c2803886e150380c000110516040d03000005d070034a42e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 589018920 1250 589017670 589017679
    0x2609060a02071109060f060f0d0b040903020714030a0605040501020c0f01050c0a03090203030904020307050c01050105010e06031501201f0b030706050a27050f1207050415030204050103030806 84
    0x944401040c8400c03440340010042c045a0380042d68040f40c6007030701100c0e03401500035100030301d0010424001850b613442142441c0606802003540342090449201d9072401c15016039041104030382d04d80b40030707589048500c248041d9044015444140391811300203245450340c405014030840c141450710324041c1d04560060b014904c2105184220f244050240a0040d0010710321540707043c181400481c05012190300598140c0b004001c074142c03946840c8015031040d0715560f613898540c00c0b020407031801e440040e44042d0402142c036806d6012582d8003002c43e90049060344031114138030310b190010b840207402c65040e40006190148010111640400c0280c46002d002c0350700c4108403807031410325007110782c4035003d01d81661000a00303004490042c801410300300644c0c1801c1e4102e5001c00340d40c0c00b04580d076401e4030f960441c5072102040942801889010032240803200b024800c80719079003140d9500304900c1103911460b1200d072078440c81400710820304081e40d00588240015a105d05000c0c20b00e02042d100103000d07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 589020170 1250 589018920 589018933
    0xb040b07140601091b021f0b0109080f061f050303030f25030608010b060f0706050402062832090f03010515090610020706050a030225060501081b102609 67
    0x5c261010402c15403c8000079803800c22450302550102c020804414410705106200d0f401081c0304600308105000d001c1d44800600003482c03c401440c6c40380c81d204201046200d500b0b10280207541c1e002c4180c913070001d02c111a0b029184d8502820000d0141e02107030304990030b41003040c52041d02c1d51580280301031307902d0b660003844513402c12030900046114102d41181801014080100040c0d0590030042d001400180000d04103c52245811008801c00960302c4042029511032404103402903070700401d03004d4400040698821808469180406250101d005404001112249a0346007400240d000c980980208400d1820300049014807400d240c072140710b10b490000040b0613151142d000c082d040302a40c0504429854034100380d03026003241850b4001e143c1c0074088449645405900c805195031804002045449a414140304858043e040f402c2d01d5004003201d015076640d003820503100008160340020740d00300300d0101255400c00082200caa440089034a1a81e41a02c0f105030900810308502500c09 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 589021420 1250 589020170 589020221
    0xf06031e15011d030304050a17120f161511030f090d0c171c050a1416050714030307020d030e0105060d0609150204081014010b040b0714060109 63
    0x66414070510b80010724104204242d04402901c110344404060100da040640703a000040280509401000310458a034070444d940c0f201c104207109050385185040e03031400303549600040d510321400140c01e40c4038030290108803c0000c6105214201c0903403160800003494100300108180d0300c151000c01c005c1d48090045080034a0100301c10609449613190000c941816959640002c00f0710000b2011715242445004409902540010502c00c00716000103550320309801c110003142d50010410100e82012410800003200c4071051045080040c1031190f110b5000340b40c110348829800080502c6c5010220600041a1300081ca800303240171951030a110b40c0307942c1015075088940403298658440036454485001c1442c5520540145003d0000c0003011113240048100b40e038095400802c40398803e03a6804590301c00742c820000320b0341441c504241594540820012980510b00600200c0c11000651000704182e00e50101889040e02003501c2c0c42c0c0d0f07503178007071440101170600b60921a522035042606 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 589022670 1250 589021420 589021441
    0x7081c140c0601060f11150103050105101404021e0c0a0507080102030708060603130b040b06011215050f1305010b1b010219050a0918021306022103060f06031e 70
    0x901d0550200d0040c11542e28152007228602c448140701d109028283c122803039202002c2c880640c0b40c08141280c442c1c0c82d4035600e011421164010000382c4a40d140d40303030038083c010070015500c0c0751410846005d0f860312044c1040362032010f90030794050548240020301540701d04010071001d08840c0250700360740221b641d48004a090b4031048031440002607005000a41500d0007001554001c00301651007554450903565000700601d060310180c50240d1500104041580d110000c1540040c0181c024800c0a1056240c201003091a0180910800099014090580300e20304506403c0d413549105100c1f03075940e80d04403980c980c090b030389420301c858088846411b401014000c4032a502c00701c840d07813203580304049011585904011405001c01003108800580d80c114681c400d21580102180140e0351742c40c641c0c56035500d60f1698420015500207215000715507070b2400159942e50756600b030166132603039550002103080e07244a1b04c3c00d9004602005000c5191003103912a900020003062000c5d082d1620302080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 589023920 1250 589022670 589022677
    0x70206040809011b02131410030201090e180a080307140301080a0b0405010608101e060f060827060f06041503060e07091d190f0803070207081c14 64
    0x1e0010401040105119442014a01c0302000540c4108080048560009149001d03510805003003c1d02d0340200300540c03035198905a008201454070310400340c6150700180075404144928144141c10784005249213120254800507103030010165610340f03146250044203078005035000340008240040c0d042c0309103103400480c1d041c0d44c0b1440003480180ea10b1350717444584083c010412640c035520b03044000345156040019407840c418420001c10120110a0320181403c002240000114180441048028030070b085400039144280341100040e030311501070264203010343c1c10a241c3d4240840b07403442c403160003050b05030141042c002054600c2d00c0302c808100a64402d044000314200b00301f83c0820028555a0005001c600b2001c20742d0b45c8a03540301d050600325685c042c4010f440100300c0c9a8051f0b01c2c00b0610031007501c0d05200e441c48020703008944408030b8007021300e00d00410319000040030a88a074001c1000800501e2000c080f540b210b081000407005e05020f9810650103e90b0340c5980b0221000f504095 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 589025170 1250 589023920 589023923
    0x8071511013c05042118080a0227010b0304050313260109020906060c100c0f090f081c05070b0703020903100e15041a0c1b010203090d0f020c06130e07020604 69
    0x44903460201e45542040303010801c0c940d00c140401c05001480406420071b4030801400c20306c0c06000e070b030000c0707006020248010041071034010a5100d80c02d0481c42c10850543c3c19180c0d8485040c1e22559140341603072440c032600e0f00d91400601040303400100211020380d13680110300c11414505010441040790740c2600c1c80c8400003507019000100007503103801c04601400c1c0c410f40400480345040c904d00c1406040b5002100c0c2d820010340d002440140305600250b0410003061440f00004415182c031200300d80310500c07200b1207802d0885c44501800d181303228606503040d441d0806410078040c100f1420242c0203500c4094014000d0041d41c5a610700351400d84a002070342c403041b8018160980c0f040d50036402c90309008000701d900741c04580b08003440e40404002e43d481944444200baa4403810350590000c80841c440b5483d405078010800c0181546020803103540b0009142403080c0d04100c408030982c01c2000d498106030304400d01094091445081100400c111a010059290543c8a280080b82c40360000c480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 589026420 1250 589025170 589025183
    0x1621150b09030d14120a0b0102010e030304030801150c150605010216030804090504020312040b0d39110d020a12030203060105030f0a0b09040609030908071511013c0504 74
    0x402d1083c4034080c0010b81e61400e0a500042d1800810980d03803401d80b8000d55805d07440d5a80c0c0d1010036903035602449403100c034103000401542545450303580184030050502070f000860602080d035407092402074051600c5030340c4c040d00484e112400a03e4003c000e02c5e603441050300610800c5e0f1500f4a04040d40384810544e60072030b607100d14140c2091061809040080c200700e8141c0300341c0c518540c0d01c02165000d44043c0411001003969980c4144448050ba8113070700001c6902000051004408007088014005811450411783c0820b20000c00c00e540c0c00700d0035240c00a00e401011000d6451550200d00c4140c0d00b4490400300c5104040c0344c40480407400120350760340c007213981000403d031513121120200d644000108800325800074044c0102c0c40d40c503c103544c211003140e06d0ba0318403000c040d017100006001e05401c078000c081c40d2b171521960050110354034501b4014403049500c000f04082d820b410620460b2040c19034040807644000d40404800060000000c031480b002210a03804440d07030003000d004580001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 589027670 1250 589026420 589026433
    0x2090d051c08090c010309020f04020301180b030304060503190f0e03040305060c131e08030a0804060506011d100915180905130308150a0f080f0c091621150b0903 71
    0x41d40101f2400d2000d17a4805488441c902c0300c0c0c0e07902d00065002c0e107905401400b1641c1c9100c00700059680e40c14115100c0e8200303100130301c12294000b0941c0d9010281840343e00d401c952042c8640d00038452815030710700c442d0801d128141c140704004024011603200b20101c441c0c5a5030705c0c454424a00910402c6c031191181500d041101d0107403001e05900480c481032030020182d41e5282c1c0f00d451940305442030408980460100320034403040744a11a4410000e08101d4040d031445941800c10100c00044148500440c039010072000340f02c2c400c920f002c2c140210500d20b41d9070301100b0140c42c50603038903802000e820818801017600b0510380100c80c0145299010b0024080301590300b650300300001096045801007124001960781d4501c6500c400916240003100e9489043c40506414446040c1804a640e848500320090341d071170324400243d00004110846103108412041242c00c2034582c0b90b07940344540028440e110210003548240c0e07030700c5089041c4c00c210650752024400c5a004041c40d00c0d0749074000e038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 589028776 1106 589027670 589027693
    0x40206131d070e041806020310080102160c0f0e1b090405150405010801020a05030c031302090910140108030d0b0424050f01050301030210050a0302090d051c0809 71
    0x213840502080581200130381d81c803042028001c4c09140e0010010b20390b08032009481028012000095540c5e215040141090907003005068400f0b001d17010b000201400e110710004222640c0d04412806540c446013a20040c007003020020103245010040d1141a0392607102e1180703d40c840200c1c540d40f120340d0030203200460b40141c11010450380704010b500c6210782c01406076030f840f1b420700070016030f2030382d5040304001d42c80110080290030400030700610184a0000c12014050005000100003201c000e4000d203400341c0e028441c45009400400030900c0801854100c254403110203070020a0740c0c260f110407a8406a209075207624041c5102e8030a00c01490540c2020203403400900e80b8074215411034000a0641184170317420f03001d1107000079000303c0781406501034a0200701c0003461164050001d041c903584070521428401c00c0860101030b030915290082d0421401443c44070000c0403001c140 = true := by decide +kernel

theorem cover : BRFrame.Cov 588848920 589028776 := by
  have h0 := BRFrame.cov_init 588848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 588848920 ≤ n) (h2 : n < 589028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
