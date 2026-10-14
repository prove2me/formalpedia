-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2441
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:43:43.603469+00:00
-- url     : https://prove2.me/submissions/2eac1a28-e757-4fb4-8db8-c6df5d3ee125

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 438848920 ≤ n < 439028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 438850170 1250 438848920 438848923
    0x803040315090822030c0305152518030b040b010e01060f05070305090a0b040f030b060301050106090e190501140405060f010906141908070908030712080a0906050c0307030f0e 77
    0x41040303004411071201001110b0480542c0c0c00b0005d10303009640002143c0c0e881c81c040d80e075000e41222050382961084002407900030394a0034035031384c03044064400300200344010b401c40358150400c8070a0742e03521074204c0101c041601c50192a1080b441110407107040d5040000c0180103100592040f0104902282c0c403465003940710f82581c40195050138110303150021400082c400116a0f01310b1550f40f00080340000f442880800480d003240c1c003545c1c00b910140c50b028240360a0300d5003405100003280c50b00c102080041c3c00991700302e41c400000200c0001200f82e00124000b80c4000303038401d500c800740c0d51180080c5483c2070f225560b040740c021503803240003241050019019441c40d1203440144a00d0120302248801904100c440b020381d2114108520440c0841c0a005c8074015600341c0700286400001045900001044400403600114806038041c070000044508000040c44c0c0d42c03c8a440d0701c8444009040c030f0090a008644001086480e07282001e030042c212011040184d4480c0d01700594012240300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 438851420 1250 438850170 438850177
    0x1e020604020a14030a060902030c040e010b010e040510151103030a06050109060e150f07051c02060c04060210020d1b02011422060218060d0c02150c090904060b060408030403150908 79
    0xa0000d40840d40c9900c0b1b00012b8200b04005404a80250402da4084005401036106050b031030802d80300d06c0a0800c0c0d5070240400c0301e00458002c1a20481d500c01404001406034080c0d540813800d241907003428041c03034000c1d4215002542c0c212036498903078400b44960360b08404400040e21440ca010751880c1c81e00c000241c10040d40d4100d61500c039100041d4813144888120440d00f091fa00001103800103290038040c600c0540c4000307200401809448089507942041d4421035041f182a6801011901208001c1000035400f6910b40b403500ca80d05d02d40712510880008820701000c465400000b0403411241038010381c40001045800e1912160340703403003150191849944002d03908690016203404909800f011018941d2011690000c0c010412a54440c140e400c50015542241c2c00d4554024604550040f0f000042d50100d41010003401001120300303058000e9644540076080228241047d100840d400d6403054000d007100750800a01801440701d180c800620600d14034200b0000013030141c0b05c0303191500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 438852670 1250 438851420 438851423
    0x919181101090e090a0f02040605040606080603010b010e18060d0b18010b030708070605030901180c03060e1207120903060e0d030b0303040f03080a17100e0703052202011e020604020a14030a 83
    0x1b074201001c030300b503441c0d9503c007101400c00a0300c00c2041d03a4590b5006004040215035451080d820812042d14a5108110300c4414410107014110711480d118512100c1c514010a1a0380194042c0003407008143c00054440c02014140d5260300240350400c001400e40e81280700c000d010394800201000600b20028040c4200c07103861400700c0e00d0f81c94400b640c40c0034040046040c000700b840e90540074280690a07290008507480b0f500100492038000050030b0f22a270545040450000c010320400c80031540404600e0043c80305807619100b15a203e0f520700d4100c84810451510326445060108a1070340c1604c10a5042d0b40100c004508043c50242c007218501084d000082058201240001e805c03405110101e583c1101181c150310149880c101400668030300d4880c81c20301894041c0415065802481454054008020b8400400d140c511554040c9404100104d04000950100345007884181c0444000c3c020542d0241c9114109401007184080603034000001c2d4941640d044616994001607100509 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 438853920 1250 438852670 438852683
    0x240507050a031e0903030c111204090b060702040903120b060c3d0c09050612060913080d0903081e1501030207140601180b0919181101090e090a 63
    0xc0d80f04600320388403150b491001d0001c0a0614501d00209a01030700540d10201d6281e41c2c2003100342800003183d0740c9942c105001e02040404000502500703a07070340c01c034640786a800741c0a0751402c2441e5000c40c003250200d02c426030000c0c0080c44074010700c4c4403a010b2031010200481d00c2900385200340320110307151110610080c0458443c0381174403d2420035441d031b0900c1050f001008240072098005040c0c0270300052107032100021655040400c041c50480d05403229141c0381c801e031000310303039540044c800c0010018105480e4000f201c00031b000041c403003000800f840100b8400c0880d041d0050314020700a440302902038165400640c0022840e02c0c2414903040e070010074200d256031010341c07940041e0024401e10f400600206085410014280c0740001d04604a80b62a8030220b41c0c802c040407000c0441d0f03d24990b0755802505a0003085440160b48140b0000c0c2c45602c0c8001411502c00c8420416007207400000c440c080c01d680061701582d03800c02e205c90001c11852811039101d1070419052500c4a00e1124000d060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 438855170 1250 438853920 438853931
    0x302031513150906050a06031505040201230705060c0a0c060b011404080d0206071826061305010c0207050114031801050a0b040e0a0201090515090409240507050a03 72
    0x10311009404080c480c9401030380b01080c0580503044034014001c1071805030781d07180c181804110a28520b00c104004c980e000013031024214030045500000c0e1002400a174100314501d2803001d55043d800c030340221000303c00e00320155a1507440c0303007482c00c140004000c001001030a0002601a41e000b0710888803456100000191881403000142d501309103d030582c0740d001c1070205000c12400d800141e1001c56010680844425655425080342c1d110208007280a1505c8030400411407004110810410280340395641d40d0103014899503a450b100040700d21007040b4100240c01d03c1804402c1c42800c1005002e44050910319042400180c1200410070714100408400000584d1b400503c003028403048268a000f408a81010b500440180006d00e5020344110b15003802c14503000c400081241c0d6142c1d060319481d00d2a45480200500854102100b0070090380403c5404541e6075513114103111140300b4800d04203c0208110350040040c11304000c0040c1a107003405202e402c2e9000400c1e2200c00400b0300e004106c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 438856420 1250 438855170 438855181
    0x1c051902030705160e090d022a181e060a150528020d020102192d09030c0e0702120903010207060e030409051e0a0902060408031b010605030703020315 66
    0x9180325a12000d40749005440901c0c4400c2901e00b003401c05c4816a92901d602a00c40b00c5401c0c1d140c41203c0098030160f408804031300042c0328081e001d40000981d07d4050305003a0100e40108058107403101c0101d00c0728803090104091592000414a142410f5030300780941443c006001c5610f10041d4000c04042c02c6455070b19000c050312400803210001c030341c4c0501450300c0c40140704880031084400d09050160141200710200940305109490b845c244010550801555081054800341d8010b00a219600408454008400c0c4038017002051040c45aa81c00355040c1382d418025106149904812251102c8009200f182c0d6400501404451030664803581d5030602d10b4002802845505c42c0140412308000005c903ca00300800900101c48040f07100340443c1c0c0c0c682110709100307440c10303040240d6610030300c0c041551030440c0c3d4400c04805202520342440d00741c450440700e180d50003c8290042d0640308200311030701080c00780200310040000754000c0c102d0909540c0080e80750703044021468900102e4000044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 438857670 1250 438856420 438856423
    0x6020706090f05010f1b0905040b010e0a06120501060302040602061b040f091e20090402070602120403030608010b0d0303020322200102060705040e07120f0204081c051902 75
    0x1c0000b0b0b8862035070481c5442520781680030709006030b00340c115603107840050000c0144440a00004000c2aa68808018288010000100548411070b4100802c2403101100c586030702081c403000e08810380b1020036244400f030300c1e003098030340503040101007500500007000400d40005090f500550703c514008001800c0140190700c41c00749034400301000c07a00000c005805c0c0c0c02988000055808003103c12402c0c16148054800c5d90715004045500c088a08955130348640303204042d0000403030081000d40750060030386400701642c1041214030064101001031008044d0140b04110003826204028040f54161030000b519480000c034028003030540020000e25400e0000144120906203211072001d40000c80c18a0b03010035280035100010340081602d4914150300005000e8070400e030359580c003032401d41403050803e4010009800e400c14403036400f030f4203920034030b0740e00486140a60704c2000503103e0389041045841c0041c0b01c01c10300464080c43c0000031030b441e440011110791b0303080384040010a08140030704a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 438858920 1250 438857670 438857681
    0x90c09030201052703030f040602010501050406150f11010921020a12030c0309051204170106080703230604111018050609060d05040b06040e011b030509121909080d020a06020706 78
    0x42e505000000d101fa00481c01c0c0c102902c00d48401d9070080280c7c0c0c0e00c0328180301c1180c42038041c1e841201c0504500c24491446001e40103150903e5140c06004641c1c0b00340798609643e4074000c00c035007004245c2e10003503440b26030002c25042c82d1002c0c80148943e001d10f4440000d0100910b80c51001c042c2c48803000030743d05000390808450158000c00300d442c09282d00c0803181294000e0f004a255000300da40d041c2c000380105014960a444001c0c000e0108a8503564600c0b041c2e010f56070110035420752120b0440151442480303100c0c8264024400900b13156401702c104003000200d02e04080501002040040c0c110070003000031030580d20256200d0381c1c3c841204000030224058511b18400d1941400c00300402c012031000343c18007030301003542c090080d50400600b06007a1000084032044003d4684038210082d0b20170303081143c01440d000d0540d8800860585103100c140c1c000403a800a5032071054030707191841d5100400070300515040d000340502d10100350000f0344902007900301400030350300800c4082c18050640c0c0003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 438860170 1250 438858920 438858997
    0x17130212190501051f03050c09042102060117190210020f03180a0b12060d0204020d0c020606030705090f010e0c090a1701060e0106140d060519090c0903020105 70
    0xc001c00e010350b0b16119020300401c4a90036020314043d21100c001061003038011055950050140445030300f9102800741c86040140203aa05004880100048405106100032501c5181d405855107604080b06000c684012260088180d401a5040705000404449210b545641103a2a09081410090072860501d04000380e401600001908003818644070b0400980d1120070b84820708420341e00c40d4911580d005010b01c10302000140c1000400e10b24140b030350980c56601c0100018200580c0844600c21140301c1074161016a100d030003400300926042001d00300410046030b04105900e8440e07101503003480188100ca1a100c42100400c0b002c0c1e40031001d4440050024000903006582c40c04104440b100b02d0540c04125441d101c00458000b001009013030513a141900c0b8641941c103c4469513120f45d10070344c040c4803500e649038004945540c80703880040e0003d5201a002c003000c0d040c01c0900f01268400d14551003407285481003000141d030003200b03849000450603201c0e4000090940ca83d002d8000c1d003042c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 438861420 1250 438860170 438860203
    0x12080c0406031a060a080f0702060f07050a030905070803040f08030f3f16080705180303090405070509270c03041109010b030a0c02070317030c04120506040317130212 73
    0x8164015aa00400381b6111303081108200309551502981030340c0f9000140d54546001c1c074020002036000d07019500810385030348103140c0050003046540350795052261170740000301aa00005010040c4500e1828008040c00c9140080c51a102d18038685040ca48500a910715800500501035100b000c18007003142d4542d00b04044c03480d040d00f22001c0c01d00c5100c40c104c07801261840c05600900701c040c03140130130510844690310b42c5460b0490b044e100c007035012000400c1c0c81c1d2510040050f05201d455034042e50b03005800d00e844290300c0705c12170300410140d014480300b410944a40d8460741410b05071061003503034104210950513a40c07074446042014000c103001101ca5042018000006031ba06000030047d8440c100413003040242a81600003282c0724581448080c001c040080140820742100e5402140c010303104112061a180e81d8103910000c80d018141d054a541c2c02038000c0209040e08100d07440500040c0613420b03951450814149441d0b01d00035440070780680c055019180c030410b020401181c0400540f80b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 438862670 1250 438861420 438861427
    0x10030c1b0b041415010b09190b071e030e0405150319050106090603020306060603070207120503130e0609041b1806080f0a03020d080901020702041812080c0406031a06 73
    0x3070075459a5000e0302c1c11120000c803060a044140004104400b40200801540719903034038103c9100c4068014502c01d0383c1c0404103540c00381c1e54026000c0250020a4640c000d1038440850381020b01410f04c903000004425a4012581400030b0b074481000764607200229000190740d101d494850294814054840350076204170b02000d110755214212800300b42d03102c0d000a21005860380c0e0901d0944005100094065102c400400c20518005001c1d65100015204450441c1d84c2c0d0b802d40c0409030b254032404e5541d50800958801801c0c0c0315100350014250b0b540101a06041107000b11746800300003040600344214105124074a84030b5801810002d00100030070712207840040154000500141c0314044a503c903495003180d42880124105c001d440d010b0b005420781c000c00d11400e40f0100c00090009000f07550030810600160b0b6144036881c600310607401c0741ca19105041c544040c04070300100118051080f800200600b4000590844040d2009840c0106040c100f08201490303407140000126031102022 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 438863920 1250 438862670 438862673
    0xf0e06101805220501022809030b04050c09130605071e1b0813080f060402150c0f0d0302190c2001090b030411130c090608040f050105090c01031a10030c1b 68
    0x5402410342464022500b2038000104107020301a0080d0003900e0002c04e448401c104003158081e0000b991003030050040d40c00dc100701d00c0024091040c11910401d800344200c3d00c00e41130002d18840c1c50f90188040c102103ea510322420848104034840a01c0c90400082101d411000400240e90360400303544988616120040c103003030110211740500680e00c0c14811444580e500c0180024224000c540150003180000c0c50240940c03000d52040d005815240700e201400701007007104100c401c0b0301c581150360068031080c01d01850301503128039500d50007c01c404001ca800203d40740108100300c0c060a4401005180d50a000680e40303030301258000114100003000f04014054002130020004000b102d04100041194410204964081008100040c1a80d50611902d0b00441c49540c0082c020038081380e15101c0c030790305d0030309694040301c510400d6001204604141c0d40c050041c0da0141510302e190405c200b40c14008520540300d41005001010384420f80002010701480300c203419448000302c0c030014101a17 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 438865170 1250 438863920 438863923
    0x1206141005010210050c0a0e060c030c06040b06030a02220f020d14010e1b0a030b04020a020c03121c1104030f050a050610050d030c150f0e061018052205 67
    0x551090728054040c0704c8440c0f80344109441158030800c3c3c100e0032541002c16052040710f00d030076007110840d081103003000302030b000c200100050000c260154004080c40d240a2404102c5044c0c0500024020303441182e00c0801a511100d042040c1d081882e4102c4280303440039015805030880c0300404110303a02c002001c1c41d4141a0703803c44842c49410f040381c8100c5076072710b000810071068203e40e41d411441c0f02004d001d031040310400040c041c185041c0380109001303100800180c00ca038070108034403015903ca00b403451010b060902554101400c108050360505481d00000d012021010706080d40d01342d5507545031208000c0043c15074020350f4118000058400081c03030311590714100c143c003d5401d4400c000001e905a01700c50782060a4480207050b41c80c01d40c440f5901aa00e02400c41805c80b0201250062261a9041440b80c0075961805000104404845200190400308054600c1000d29131640701409010344840c085401d002c0706480c0021551760380c9481c02c21503100010f007a0035061a6030060400c0c07040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 438866420 1250 438865170 438865201
    0x4050a080a0c08070803070602070c03081c06060509030d110a05190c05030a021f02010605041a0906030f2a04022719060c1a010807031208060109120614 67
    0x1003030b80030865203610740403020340d1840144542101c6034000c0015000149403a00940181d501c126000074001e51266220107030b90700718480d01c049007009004003012683d0540510b0f001800e40303007050313803410f030b14030001c00e4032408500345140038000e4840c0c0d0441101c40c1000500c1600b1b403c00103846608000d022180d2072980c250750280c031440c1185502141c68540440c3d40050740b5401000020480d8240c1c0c00710048201101615003555681d00c000181500d49001d0140d40607410703041403484c81c900740704201c502c40d4040d01441c0282e10104012810040000f030180340c1d03065280c405a804c1480c14202c500440003886025040b90022444540d50b91004640303c0110b900200074029040011007401600b032004048841070510348481006498001c4c071424000d1380c001c1c80c55951001d00b1405813100100c1c03c0e8444041940034080c00c00907c82e52101d400040c034860326212a19042050000700718581d640074500e48003014144000810206500c01c5e01c00c2025800040001e00c1d003804240c29840 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 438867670 1250 438866420 438866423
    0x1002060402130c050403141005010816060806130e03160302060109140f16030e2506090e0f070c05060405010903111f02090f0603040803040215031504050c04050a080a 73
    0x10b003454a0030742a0b140e030241c07004044240d40c0f1a41000d1461300c90307071290f900300d0303000c0c42c4240a4059080760100040c0107860180114034000c04184c81c000a4069401243e6441441009000c1e403c4c0412640c07042900014100e000b2400305d404108544913504600c0ac04251448491340c0341c804130109900403500c0d80c1242d04500017088400c854000740052210200e903d02d03107075141c010010b4400604030301245514503462030b0011310304a00c5200f035454500c001950700702440041c2c0e000b400c48282c401143d4081c0c5400e243c0942c24070b00d401d08420300044060110650718001c0c0f0300140155102e08542002d8640100c201c07034050409003000c5008084501003603002a18120980c5100400011000712040e07440d01d00c05090619441f410700250403418550398802c0d01641d54100c0356803000003460190340556102e654030304042c810001c6d6803802d0103c02c00d001800b07104020303919100b0074281144010948020845a40300d002c0f602e4a84256000309612200f40e90b0007092a1100003100c843e4107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 438868920 1250 438867670 438867679
    0xa020f03031003120c08090409051c1101050a0c0f0c2414010501020c0f01030506130501060914031507050d0605030d03060e060612070c08040f0605070615050307050609030a021002060402 82
    0x14130210408803150803c01101503c083c0302000606900d00f0300390b12454181c0d0040d0140c82c00740401518407601412140301a40c0010880c0e001400026002e1140030741000841d0b60070410405002d42c090064440080200103000742448000280540c07507882c1d503010800c6214150081c003503412941d0003458a40605201072a182c000881e2a50000402068000c0020481c1008100000045000d40402410707140c01c41610f014451048001c0d0140318040d2820f500c443c94118181081030f03010846025449100b81e02009030a100400b120800d19000241450301702c0d5a0141c5410001c00f0700203170390066406220b03844164a249506a01c2001070300d10810006003a42c5813142080b11a0180100e030719200b0816101003112180601c542041192003525940d040c5070f5949000c20030540194000d00101da0006408402c12029200301004c1e0340300317480214440c41c01c14011960f614081c4c01014062a400910031b82596010003840e40c90310b60091010315000da0526000351603140a5408a009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 438870170 1250 438868920 438868943
    0x3032a1d060d020a1205070215101211010516050c010e01030209060d090f0501062402160611150420030f0604062a09052b080a020f03031003 62
    0x41803010342112524038010105810604912420b5009500841001080c07103151041080030f4001d6014040c8556065005800503006080c00c4c00c80a4400800c25103103205051800e0000102410564011310b8001407130301c803060703c450016141c3c2e00c00c1101d880e80e115050712090040200020310a4058802aa5003c010165280040d801ea001d0035104a41c001000d00c0540c896401075400305039030a000f42d070318030380450403074507400d00311086a00308500a40c024003c02c11601010403c8000c041d9140c4010001d01982c2400805404002c2c0600410482118803110001c2c000300200c07008020750800740390f028102407500c82c049401d030358009008c905115122510a240210b10040520340078005004260350300d503600001440c9080d07070394510307485140c1031240805000160803048001c42e291080d05908041c01c1004030050480c0170368024842d42e08482da81c8946c1051016100d42c403850841c1c9820701c02005904040d08103000420b2031002104101140000741d6003081141c1c02078094044 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 438871420 1250 438870170 438870197
    0xc0b3103031514060c03070f05060f01051210052a090a09150306050601051b10050a020903070612240914131b0302040e0a020301050a05101203032a 65
    0x100c4006403180e0200703400e60365200ca0140c01c4c0080180085031614003580e2030201140c1d0b0b4001080d00c40d0340103442540c0038104000750102c11800190243c00c08843c480e40100e040703014a641d500c052058268002d4980d030101d2f0381410400808802002d080a1005048010700c10f4040a6042859241d01c50560468002100405882003c440d291248603075401c10b0300f1621240060b02002d085241008000c0004503070743d030058918659400d84000282070300b0003a540c6000190380000e080341c0d146ca031042054207560307038000414000725603036818034813580c0c3c2c0d038000c0c607000411030030341014041c40303a41e003120285000000e0240300b0380b600103504210700c03079105540030a0800b04070b03810742010b00c0710a90900444c04031000401900341560b902000203407a60702180035101d4000003c582d5a100c0c80c445011441c0a0080d65030165201800b084a841c2202050301051a80c2c810f211004e10081c1c44082854460341206611003d400c1640d08501c0c46d602e079043c04508548028000200901143e18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 438872670 1250 438871420 438871451
    0xc0b3001080304030320030a0914040e1b011103040f03020102120f04090203041b06050409110702180903070b090a14010c080103030f0201091b03020a050603070c0b310303 75
    0x14141c07403a5a006605041c00c660b400e5812044807440e540301510007828946402e402000140765a607003990f9460307070040ca8080405042510200c41620031424104014642c80740024100701d210b100c0d01c02000305445040c0180c50b04449040d92000c030340070015010503111000307105e44003140e10070303401c0f92401404a803008003076014805d100210100100f008101c500310b550040d40d0064000c5403014099108051404106d4007298801c801180003c54204440300c02413055400900b00b540c501c130300e015002c0d80041d50000c060000203a0007180c1c031020492a62003001a0742d940c5502400c0341ca070b68101138040320341d2084076190843d0070310101c161700151000c0600408543d04030706d4a030324001c0c2c2d095540945000741c0c1c1008940440d0750318240340010030b03140311000c460400313012041d01b947c6040d0300520942000c3c03908440d010f40410424049500d030b014180591542d08800303000c03c9501c0d84012880014882c1c400c01c6005041044c00f0b0381d5004c5218a0488603505c43e13182080300e01500c3c00c445 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 438873920 1250 438872670 438872767
    0x9020a080903070b011a0d02130807050d02060d0f020906040308040311011704020f04110d0218040b0907120617030a0806090108030a081e070f0210050112020d0c0b 72
    0x84c144100c0c4e0004000c50b20400841240c050428400582441400c100f55412a0004e8015000280d01e4503403c12245009000003406080c0640b40030700c003032480d600420740c1c0748100d01c981c00d00290303070314440f61403008180e05032807640400803d400e0382d442c0e0740c0c2400c1c20250071501080d5000a0044412a09903010314050040b00d240d5001c486840e42d9540c08100c071040d8004141608940c4600300b03040455130031070003013a000403403020042e00d0311a210110803040c59140038460240b841c00f901c1c000e0f150390790280950f1158281c40e0081041800c0b41d4201c0c060102988408440c0e420820700002c0b0142c08809040a1181540d070104250755140400000380800c0c0f00d408281e0b0001c00c254000c86200e80d64080e03001c40009144180c3d40c000a019007016042255030b13500080e4018507010010345d05014200024030222000d0007154104140d5a80c81c5801c150001d2181e10a282c0e948100b0001039a12002480f8840040d9240c0400c1422106800140d005c801c03142581d8458016010101c00c415 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 438875170 1250 438873920 438873923
    0x309090b01230901020c21060928260904150b040b0c240f07020c01020c06071a0a021903020c100c1107081e0307051c031509020a08090307 61
    0x115100c503051240102e076a0f90008085030b0442c0203400343e44041c2e4444001000310f824003d03070640e0909690066242c104907000e410300c00075401c150588055001600c40c1c9110801c010301d1034800e409040e02d0000c242c83d41041c8070351074402c0c0440103101e0086525000c0c00058100340e078280031600302e846988040014602441880705001e01003400142d00b604054071104d015641160205402258aa0030007049011103e4030300120800b000303080e0300000070740e44d000b00d242d000a090318021200047d40b18210a01710303900943c004228001404850f00740c20fa01c03030321080c6469640d0b0402d11b84090181d404140a43d0600303910b10404034a1901c603100701d418030040d1402a1548c088410310b00006030402c0951401040014504548a000b00780000360007402094010003009205a07100351006204014440c0300340c0043c000040800c40100c3e40154250006d0980c0c0718010350100141d00503c006251304544240280001c140c8000a0303005104000781502c0d840e10903540d10031165a02c1c0b041080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 438876420 1250 438875170 438875207
    0x132408010e0d23070c06020d26040807080a030606141e0d0905030315040b1203070b1008120909060a051309170304080a0801150c0803090102070507030309090b01 71
    0x5840c00c20b61103281001400003d0120703d104000d6022405400e80e000441c040d200c1c140d40003420003581c2e40400c500b450742c03103231410700310a000d003810840020040910100d0300c01070b003107100042c208000c24040756580c2c1d40c070200150f200e038038601009000700824003415010070420002400d014080e80243e605c0c45050780714034400d05401101c0c19107660400581100420386480d107c00008905101070352050030084406040040b200c001c000c260354001c0300c03581c080d20f1000c2200203122070110403108507a40141d00740d60300752241c1e0f41608560309654000304150080040724080b900e0120001c1500c0442110300c20b00d55200d181c10032000d2010386c4911076001024440c031003280201c0e07402c101c0225000d40d08050400e100060900002ea00844049420440c0013803940c00f60307604440d20502400d06c49101c0150086022005009802888000b402cbc0320800f00019941202c01d40440d50782603400400c0c0da445990301d180290810156014140c4844e0400c169500a544118441200843c4001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 438877670 1250 438876420 438876433
    0x303090c1c0803090a03080a05010b070b06210a060e03040501050a1d06160515190b0307050a0b03070f0f1d2806090603020c070e06132408010e 63
    0x1801c0001140c1012414140300076202600000b040c001c1020750722443c801c1c0c0190081c1c50151800030300c9100001c1003800260314103401800550b01407402d8841013613000c0082465a203035440083c0c842c004640800c0099003c070041410703010408a2001c200e10f104420a00050380070300303825034a9004900800f40040c0d42401520901c0344903003c2400240c018580c15590790741500d0205a140e80a4004011000d12030640b00040003020030406100340c03c51a4110010300b403801703144000d549540c921a207966214030301803003140d50500c110320050200030041c0002681e01c1082502c150001c031400400704a00300d000f0400d40780550181090440384c2d80d40c014100c03030b141c2050124012104800c40d0041010701081d00301141c2c4803091040001c1011020300c0072444d2201c000c1400c003040e000103003014018040f6010802002034818262040e44407001d82941e00c0c030001ca5180340ca000c24103410b40e82002c040d80c028000c00802c0c410407800148806c040c3c60344900d015400d803400c0895014542d48040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 438878920 1250 438877670 438877693
    0x150e0c0405011a1e0c010203040c080a0f03210e281115090613030b0a180204020d0905120405010206070e18152e140301060e010311040801050f0108030309 68
    0x40180050342c1c4011102c5011540c030000640180c2000c10410b01e2694000103010512200ad4544001048190000c2412160543d01c1e080901c10302d40004043c40506000440c011002c0c1e15800060454481c08010180c2c103a240c8590300c208008108075504401c1428008109011404055031908070b201c0d110b1115a10003401720483e11080144c24402042c85103100c6a42c0e540700030030940d101402c03496421802c40c101030481c1d2102425019455140010f1002e0190400009803400f0f601180e0040c0c82703100b00e29840d4042c020310310006081c0d0080c074070003a540700d0412016005441c020780c211140746d566580240d40d101d51000c0050b910210101c000c698564042e201e156100305001d00c4006281414004101c45042d0141d080d06485030a620f05450f04043e20440d0904410b41c1c6032100351403822442c042c841c0d1206025034001c0044c545841c0d8003c1e4001d8101c1e6803504040342015946030350f80d1001d18001c0c030055079100c0008503180d0001a025400000b602d0042d10044080c20203240b80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 438880170 1250 438878920 438878969
    0x150f0d062603031306091211070b0301080a0807050705090112050d03060605030a09060902090910270b0a0204030c030f03110a2a050301020d0203090d090e190207150e0c040501 77
    0x544004981072519164500c00147d0300040710207480040340c60703211090603030400721f40c10803200350010146001c041c4010407030443c000900c0359901d60491001a0b41c0e40d0942085400d10f8801d0700004d4011080000025040880382d135440c2402c0d0061080d2288107a15400890035075586110f031500049051003c508000000d91101000c0c078404c000028460205a0106420000445001920740c2150a51410300007240c02201045210543c407407124400150740180f040e10740303560240ca0481c0140004080b044240d0481d405180c01c5410240980c0e03032880c1801405600c02c0301140007404c0c1d032041140038a000140407590780d60285900304c48203c0c030505e105000c1040c001c14a046800c034100001e860310288014842d00c1c0803000702681d60b2a01e440c80a29003461442c03000c0410541640400c28904200b00094000344000410400600c0059000d07000e80105500580a03003080c0800c029804040c3d88014046407507002550075410010080104513902445205480031045065141e90b41300b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 438881420 1250 438880170 438880201
    0x1508100204030503120c13091b090506030408031008100917031509070c06020d02030403030605090f0703020f220e0c12150424210809150f0d06260303 66
    0x40d841c0020341004001144145412107030348c0700d04540d541e1150070011410024816602c111098140845010300d0200444c03060301c001000649428804030102c0c0c98101200003102c02000740800b2240d5544c44101e80500400b01040122500042100c1c600044480e64040e130f0311440d056481c0a1194150400740003100d20001c140c00c0800640314984000a4281c0c40034010204128100580f81c5c5000e24018040700c1d0980c00c0148140710340401c01216004907210280c0c452802e142c050303141d83c0f007071596003101d01811451489091043c01d021900180d2940c0140484000114201d102d84910b14107900d03600c1030380444c0d1600d20115002840c9c00924400d00d650005001d000059409a80b0b15008078030701e0070071111480344401c11010030a42c0d175101058410b0081d8028203068400c02ca41e110740d0703d03102d14000980200400c1c1400a2401000301c1070b03c4820b01e000c0500c43d62440642c01e40b0004010758001c1e80011400c0b002220840328004001043c000aa0001907255440d4401c00c804c0c1d20b070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 438882670 1250 438881420 438881431
    0x507081b210615011b2603060919111606061a040506070503070b0f040b060102010b0108010501030e0c040e150a2d061d0f090615012001150810020403050312 69
    0x20600d10103040407410292000c80755008a104c4c242c000c1c0d02011046c984500700d002c07024001018402d2007069070310395aa044d040a1940040100410400c01c024042d09100207000d9071448007061625050b400200030300101481442e040014a8980c0d00081c1503080d05100f43c001c1d070300140003c0c445810f1a00007010b40c41d0040d0b0440381458030f41d50340c4205d0f60100f2a003a0690b0304580090104002c20751081d241c00c61024002800303450f50903000206152014481d4504040e1603141d05210780f54140540100c11101400900c00700b501c1008156403006080c02c00034000040d000041d910021912411510810001029110340002c2d8080f2a42c1c064404040000707a540c0c205c00226a03403145030521080c844103010102130710784414003ca90210003070030314503203401100410410038101c14140c12024401d0a0416454000c510318541a180c5090042d40b00c1d880e1000741e410722103150b04a441107904500031140201c1d81c0d85034900a034000e61100501c0b81c1e100380140c00d5041040c01c1c6455001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 438883920 1250 438882670 438882677
    0x2a120d09060b040c051908011202100c0605090d021203040203060106050a110d090f0918261812030c060a021b03030709060801050303070c0308070507081b21061501 72
    0x441c0d42d500080c00c41e1081c240b0359010810010b03100070041d22034403080c00c0c0000d0038101400650b1401000c0303500c40681500080c0300d02900b2401c000001d018846002030300360419801c000234074015140c5642d0383e003034501c000c001d0300c01d01d451080c4040c1e105040301d1140c2e07400303000b50400364a414001e54403600a1001a8144840c6002402c0e01000030084080c203003d00e079807a40305c0d2914094800700b164105070002140303a81000080c0c841c48144051800040e607020323004076448099115a48102c02d181100440030490001d4480c2e80c41e0740b010b1007988400000c441d0614a50210000e00c1e0380ca100d14540c0301b8a6400000000f0340035850b0b40d001d008082e0a40c1c1c00140300800c0102c580342141e10445079040480c44072001031144039441518640034000c182d0080d071030701500e0340f10520700f20801e200c01800c1c0240042c141003004001c0c40b07401c000781800c40882d41d4a020b0a000b000d07a5001c0074100c80c0c000d149040901601d1041c4650300d51a5824540c0500059125000034400a040c2d81030740c0e6041c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 438885170 1250 438883920 438883931
    0xf140c0d0c030c050901050607030e030705060c0115080c0108070c0c0f0603201303080d0608030703051b1b01110a050610170303060609010804060e01022a120d0906 72
    0x468985400244489200750015240c1506514020001034415002940188021001403159403500c00440d1a05501400c0280d228080d0000092070100243c0101d1b800103c04100c403c3d081c041500140301881c103440d10440708545502002d41d407001590800c0d4005120310011855560003429040d00c0d42d03000744c13141c2c60381e15280c07510003280c0c01c095401000000d60700c4075070346245404a5041680d810704080c0003864541e094600e5510101c080c0009010300600017071762a8400d500303a1101008201d600250381d01c0b00c185040c0038285070405500c20900121061400c0700200000c0750b480c41c400c0c3c10a00c15840d04030035000444901000050704284ca00c41c542440c1d000c031b48100702c02d40c412100691a0004070717080200c001380341d43c00700c0d0304620720754018400c1c85003c1c3e44001c15100e45d0340003840e00f44c006560ba410703d00b01610004049400651001840ca8583c00c0c0102c400104e074600f1101c02c10807480348440c203cdd511400103160700207000060180b01040d01440d08103c0c100750045501103503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 438886420 1250 438885170 438885193
    0x17030c190314040807020405162120030714040e07080a1d061509010b040603020306190603091e0201020a030509030c1207080d090e1504020d0207030c140a0f14 70
    0x4004415101075600c4c90300812510f0451801c2e00030b083c0d01c594080c0c6205d0007818981006000c0783c03107000c813001101e608508808001c107810340c4070701000c02c014821103001100074000c0341340540c015254000000e0f0020000030b810502d0400b00c2e4203c1d43c00354500b001654440100b181c2840d070162403c40c07a10344a0090420b00d030f102890000d03000842c080070301040c0c18208903001c4030903800c50346940661034075001001050f41d0403081e41c045401504016a0780d0b542e10001034040305200080e0301080ba030780003000c2170099040c1d100c100d00b80d110707041504a2040060740c2108402145000a00592100814000091095003d046079039809801c0320510b407406000075940f44804009113150b80c0c44140d08021030441081001c2c210304460503c1c1c00500d0500c102d508801200078552503416200e000248259207ca034101e506021401c102152a40a289401005082c480074151108100c1c8604c42012480204210f56001d81c45080c4001c40030700d580c3c03103000442c240380d0305081d00d008800d01d021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 438887670 1250 438886420 438886451
    0x605250204050a0501051f02030702040902031204060f081803190908030a0509041103060a032a14030114070c03030e0c0307030515010e060604030303020d0b0a0603060317030c1903 79
    0x2801048083c0c4080756070360505017400074200e000381c2e4604d11201510411004281c01001701c582043e0103403004a61502c0600110786000c1c000140703020660700015000400c0341c0d00c01050004950b80da660003401d03482d03803c406600302c80759802c03803245a0001c1144c000242c020b020030701e03100b00c01409c20701e003071540d00ca07400d90440d0041d041840106074009291401450030384110705054468124007411070038601c0101b201112240801082400c070800c95618200440e0b100500740c6141125403210780d40c8ad400702c80080f4a45640d000e00940c281840c40c205040c448005034030403400c0d036a410916540d140c400300c000c1e001100903640913025844001029840031300200c005140200b00405010155032005800c065050344074012407030440050120f603540d50803c49007169010b142c0580c45a2504140c0c41c000d0002c180500d90281070008001201500354228204590041000d40d180b0b183c9180c40d2a40c2c3c0c03004541c00c20b0705440400ca03880c04455a00c4214400e0246c40c9030016141101d00d0128 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 438888920 1250 438887670 438887681
    0x30718180b03100e03120c0909040f110108040512070312092a14090901182103020306030601050616060612060b06190302210f07110303010605250204 66
    0xc28040e11098421058103003080080d2110004507010030104840004003503c074020020340c1c1e10f00002120104030080c200c001901d1003400c00170080c0003282401e280c100c1541040303030f0b4102e58046210750b00065560088150b94031454008001c2e1041d11084ca0004585a00440044051100185450155000c02e100b820015032150350194101c4610410820000c0035009490180b2900d260741440083c070000c04a440030700d810307555a01c01d500c60046682c05854903103a031540c1b80c1e00c0e01c060641400400101e0034901805035001011002c8007800841c1a884100d401c1c0e43c2503403003903004115904010b80104400007100d9800031075090507030b03184810307603d565011040684103812510244100343c4504035000e4001c5646a240041c5409501408a54141400180f50b40071507004808088a401c442c0ea50217001c4e8941c413507140149107111100e80c281c0350200092039031030385205050000800c43e41620626215070741007041c02090064a80704200c000c87e0a034092404e4400143c44a001c0e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 438890170 1250 438888920 438888959
    0x2090702030f0f0409180c06050a03021215120d1e020f0f0304031e020d0605061917070e0106020304090c200d11010b0d060f0207081b1b06030718 64
    0x944c3d11031428074510180c68444c4201e0600795894901c800c0000c42a648003000c4031400d0401945949441e0400e40090250514210703500801404024018514240e48455040101c07075266071521b0f8980c880d9550150400c101c808110101c03085c080c0c1001010103110500030320f1040b5281184500190f50410b8061008002c241d440890144204410898542c003403004940d0291055055900052201c2c026584050000360707a902c0031840b82d07124030400e40054460030350b03c40015542c440d55085129601580e101e40d60140010220b409411114130314100c03442a80190300f0300782810b2240000740a00c03881c000031300a0890511009a81422200094105450207410b08000100000d89902ca550300c4000366070f45040b03040d03101c03a60b520540403100e540007039000440380c410b00200c1000344904003002e44040804145c0100004551b081c2c030a001c2003140a4560b0340c3d21800c0d50090f060403404803194403210610004800d940b1070502601340002e048410680da0303980d50110502d19540e500b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 438891420 1250 438890170 438890197
    0xf0c080406060e0c0906075c0d03030605030f150a140402061303060513031e050a0f17040809150c060a02070201031d0709061a0403032304080705040c081302090702030f 74
    0x2d600c80505043c85400d100c0341d8482c24000d26174041c840c02d146881c44a22000e84243c9c0c0030004182414441d80c480b00207030102a04542244020b11700c1d0300e5030761040305003803d18500c03800c0c0020b071004e101c1d0088512540428a03820340c50348440d420030a082d0000d041000f5942d10b05807000000c98041d000e801c0c0202c01884c900104041a82001001039102c2588401501d4085a480c0102076000040702d11136007082c6401514090b03d25001c40e070a444941c021940c42e180c2409100512000100038000311100319803d580c40c0403c1140840705000380d002400d410b8100d1340004038101803035002010501e00c145030020b0180122130010185213051000d444142d4400034044c061011139104881c007600c051f0b0045c141d9001c1c041350380045445240401002c12000d958010803071032810035100101d50189441035122503c0b04284d076079560452198a12071810f000324041c10380d000d9803050f40225040c0f8940175011a0355020b00200c610003800180841c4420001e15a0280450001d0020102e5424 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 438892670 1250 438891420 438891503
    0x2030606071e0b132004020f0f09031903091e050409050a050d031401092703050a080f0105010c021009080d02160605040e01180f0c080406060e0c090607 67
    0x3881003802c1d070020b1413a10410004090500411480a403001a200500c03071015500307100f100105020307019501c02041038980100b00c080e20003090380c01500d01180309908440c04810020390368009240214000b0700071421001043c8110300040102c5109100c81d40d03480d4201c0b95448004c10110b4010f0802610590042e55450003000801c2c41341401c1540c0d20b25007888440100d00da0520214018403514143d681e030344e420f019603c5148003421640515070502c2c8101d4000c0703410054100d80c070413640030340059070003c00121202d50f41d40300207060741c1c0181e544c110f02514a0703003030240d034003240724810044c80703d507000001e007104003085407a901c50000c2d40508441c41440d007404221415541028040c4a0244014041c68002c02d081504682561904040314031030140000c0007000324410030f02480b030a109207a40459000b184043c0140e210f64001c0058590b2401180006070043e110300407450800c000480252030450042c01b00307103010350b0092482d01c64021005280402031152040355401c0b00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 438893920 1250 438892670 438892673
    0x180402010e0301020307050a08090709060b040303091e030f0204060b03070302070203060f0f04021c020604030321051005010c1b0e0405100509060609040807120504050f1503040602030606071e 84
    0x5000c40300d210002d40003941113040820001d00300f40959100e6204206012002900302d910401440e0700401110008110080c0c50b0ac203c0c140540c402d01055001c0703092860001100710b02c410000e5905020744030702e81c2c1c0b240c0c15070f6520f034000142c0d004207a0340262590720226000324418010340c0039458a8600503a10466072043c5030800030700074040d407043e42d295020011f02c01071030300d40aa0300036812195048108020b04143c18625403060020303410090210300401016000300c446041440010800801c00010102440503990110341c11620031401201c1000b442d40105230109609110304001c51103d1229140c00c000d50b41039900122100c2c4828041c0420301c0414410702c03240c1c1c242c0d150107200518080001a60303404000e0015030050080d140001c05001811040d43c62040e840010074154020004000b07000c4e81082c01103e20507018884c0c003503010301d0710103c80310b070708400240020b042d59182c1d2626002500020079036a004441080b0030000650380c82103504c0c860032003105401407280035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 438895170 1250 438893920 438893927
    0x308161401020a0306060c02030c15040806150a14010f030c09090504111203031b09011e0804030806060705070911220305190b040f050f07031109060103060b030a090c030218040201 79
    0x1d942c04541441f09100b01c003400b503140805c21514166007500c2c100045140099400f01a2150364000b00d010300400003130001121023812450032001d400c5895a5403683c890405940d078414689041e0301045580d148140c0441c0030740c1103280d045507541090500590b44100340c506480c02203404945000241042c5412803405040031103078404100000c50561800c5103020503200e0201d40c520014400109203000280e01c01d03081206601e452000418522480c5038016015030703010b0f14201c01041c0e452000800b2424000d0542d3368080c0c00c8030050442500d4002002e0081c15040c00400a0241c10868010000c1d0848049105113841d905042406880c41c1007143c00d110700e0303c1c500503a91889500720404190b95040b40c9801c150881c00c51400440da40c5041c9103003911100b40080e403401510000011301260b80003441c03428000b500e400321142d40340c4004408031080c90058001240060001c50183d031030751381c040301145100c0c03420310b502d080e1240c0004104c1102e04076100340c41b040e010100802c5590 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 438896420 1250 438895170 438895181
    0x30106080601090e0f030f130302130f0b0301020a020c060d0603050706020d0908070303170603011e020913020306030307032a0b0106020d0903030e060a090e04080c060f0f010308161401020a03 84
    0x40d13010151500c946000302940d100d204008080c1c901e403c000c00e140c03d040c50201c4c000401964000c2404000c9070040f002e80c001b42c034140c1d050303614640c54070400c880c49003418000c071480c6400c990702a09203522010100229a000403940090150743d94a001c400240d0801104000d0003e81d001030044141510009040242542009040750007412003040066080f0000204242c4020f000ca20325684020103e4010b00400014400c00d4400d40010740e070080565000340075907d0191010031880f076490441409a2105881c0142c15610400610021a01c1508504940c45010342c0303092000b005082030300d00c001c16181003626070121b824010415241c04109110501c0c1352401c01c0e100040c950380b00600101644811640510030015000010a2280318004054100c046c0e5826460600382040c9040341c00508140c0394612907a40840c0c40c40e9502e4101611070302c41148085003c0c0e080d03035114285c64001d1031812110701c00500c0f0b030100081d07104c9125000b003c1d00030b00046c0c17681d40c1d4160090903541c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 438897670 1250 438896420 438896441
    0x90a0b09092a03040809090709050f060313020d050a0503070b0f0108061603150807030c030302120304110d021314370507052506060504060608180c03010608060109 72
    0x2200500c084607240882a20442c003a042c1000ca640c49503078a04240c00144034611000f03500803620810056507030303044011070050f650700361203243d40c2222080500206100a907000c0803070154000005005182480e402280385102e1015100940e03080e45d03a1a2440e00101070484d0302d0102002042100301c5850481401400c14200811590400c0f1584050200f2140146010591a800041e001c40c48a070420401015100c00703c030701d159543d007000107500c111070008500500450082002c60141d14042c0c90055070807007152108003d5500030046401386498049800c04944030841089065512402c80d501e21900c1c0e6161491908904544030740141150081e0b840024072a10a07032501ca08000702411005204006400e4880000c196102c2c020318407409503620403441d280c4209000200b441042c070b8410003007031021a85070410003081d140349010700f000151420f00019030f6000401d0081e00e8400c0700c80160341e00c0e080c00c400401c0c2074546d160480c80043d0b2010004124583d6544590075002c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 438898920 1250 438897670 438897691
    0x308030f0c0f220503100603050f030307120e070b071506090203071b081612030f0612060207170316020c060c070e07021018060c031406040e03090a0b0909 68
    0x11200700080c402c50b001c0e54080900010190075885124428418210301910000b41100e041080c10721000000e00b225000498440c0241d01e42e412811100000f0341c0c0c010700140d00c0d0361100c42c00c1c10403d44000c1c0803071800981c0d07610441c8000121011010000c1c020580110600420760000468490550b902e552142405034810420803200a41c425003420700700701005601e246000c040e0900e441e103801080c02d0700d00380c001076928101c200310b04049601d4510b81d007520188545045110310000302c520902c1000c10411a609a18000802e035600911641d0700ca10900c501c43c00c006601d100b0703280c00c120790030094409403142c43e036100c6404109000c49141d08807007a0340340111405c0740a0b07e4100c103102d0100c2d403140200110700c0c510300a01410844042030361041201c0c420120b03102d840881c8100301607401e0b9140c030542c841447d1290240d40034050310342c0036000b0a13444020900004100c101000c81c1c3c2d500040c0031940b41c50359a0b024070801080450072480d11044d13144208900003c0240505010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 438900170 1250 438898920 438898927
    0x100f0e030d08010b0901020715110d050301030c09020c030d291903081b0d030501030312050f07140d02070b06040506061602090703060306140f011e1217040308030f0c 73
    0x6003507002100394190313005082e020703413100c0e072100c0140d00d4a4995082a40c1807580050328000d46580071500280c0b0084900032180030303160300c29003540d4511080c04090f04036404094240142102c58000702040c0c0c480d501120300c0c08008520900440300700200034180088550f0700d000d20383d042a4111344500c00b04450350591800d030304010386e203009111310004002140c0030851515001d4085851081821004e0030f40d00304108401d00140144824001140414a480c050405134040c5201e15449410a000e501c1c4160302e51400035140082d40000d003040c146820041030600362003600290102c188a080c03814014109241004241c4d20000d1450313004005c14424542040104900440080c1d0140e035174800907160210201c01a210540000e007d4604000e04001d44c2140301b0419481503400e0242c8000698807001000e080031081c018078600000c0706a804d024801c549803c1c0780d2030f84d200301200220080303010f04000c0650025841a20500e0005c000c00a04101c120324040d40204010459441c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 438901420 1250 438900170 438900193
    0x30b150a180b0f12040f0c080309011d03190c08030705010f0c05070b070c020105070b0717180c01080a14011514130b03040f050714030c0907090e0a0b100f0e03 70
    0x3c0034000c1c1c4844680400c0d2500c003107001c2c80040840c1054a0303030420b400c643c03415160403000340c0c0ca62007801001e00107400300444502e002e0400079407080010000340501012055000c05100c1c5020140066900100456000603507590401c001d0014506c140f0002c0380c09001d1100300b00494031502000d4080c40410010407000841d004401e83d41b00815003071040790a001400126114003903503200510111003a000e110750142c100700140c021420035a51110f059450400c1011300344024200007100340e0041c0f00c001545c2d8000c842480e0300c1030310004005901054007111490310301003a4408410042040103850001d0b6100b00e60382001064000340d540f4154403444906a4100644200c418014000c00490104401c0c901e807450b01d690040f04032140c291700c400c4140342941121010b00d00c6485031080292482c2420101d05100d890036880f00c1880600d400c80c0718649102c02801c00350890380e1105910400c3c1e5400180003092075642c2c0d900016003000c02d001074000075500d03003502d20076448010300c0d6a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 438902670 1250 438901420 438901447
    0x60111031c0e0c011e0207050618030d0e0a090218060d0b1305090d050c010e160906080f1e0a06091505010801150302040b06070519230c01030b150a180b 67
    0x500500380e40703074800c0141490100700c0c24244523030020b0703034031110024418611515000c1080c1d6222004c07170039510561100d200c142d8440e003100c00407540001b0000420000c5a45960107000048410314041504000346000030b1440e50007460010343c00b598440d040902428802c241558104048900700000c2c102809025542c01d4000b084100300003001420410000c8290892802c2c04405011500390340c541c0b580c540d0700c05200b800748107240d500e00701d00080c98081c00071794407c1c4d01802c54040c1120300c0000428521806c2620b03080d24051069115540008820707101d25500c65004007030400d145004044100140c0b00180c2c8052b0150307050640a100c0c0c01c0d810030010007100d60495000550388000e6001c190307140207604020304540a10500013115a013119001450548180c020040c4042540c0f0400c20002c44060010174903840140040c2995000c0c0d4800300c44100b00030050010345a41c0511000780d81d000b10400c00000d880c4240c151480e203100383c02c540113080c02045050610080380381c0f20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 438903920 1250 438902670 438902687
    0x1f05090c10121107080703030e010b030111030f100e1003030e01030b010e122107050c04060b04090b0415170d0908120d0605030105040309030c1d0a05060111031c0e0c01 74
    0x1180302c41ea1140c800d00c01040b24400c9443e0103034821001d136107503100350901034010000750003000015402d010f201030b40383c47c041c840c040c3c00841c2c1024150a507214452951440c04006104a00903032a600020941c02c0e22800298400ea140c60b40000c0a2800d5142c0140340c1003c1d0b034600c034149400c0c4100428940e0300030508100c90042920800005000040d4103490000f44100d070001b41801c05601189111080c002410064060030481c0d042101c08400d00086500d64825100132800c280014482c5261b503070011040da03c0000d02c082a64010b0350500110800c44c0e903c0401482c660400d900d1030220140203504294420f42000780740c0f1490810403a4030b40b5841c2c0c04d1070701d6803c40055205480c4005074020000f411000c0c3c02040685420325020781480400c0c00181c07004414018001150300c840c1140355080c0c00060180316090315410007503009414003070302a605001660b14084010002000a00358101116600c00000c4010501c40d07030440340d20803081d04064100c034840c09111f9030011680e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 438905170 1250 438903920 438903947
    0x1150f0f21210306050a080604050309090903040801020f09130c020d030b031903081905100b0a03091703060f0a2315040f150e010c0209091f05090c10 66
    0x1012801c030080c41e01d4141c1c0c0040a044140349840c0d60244003200303a0690100c400d5841c1034409000321500c480c141540c0f102c046070014101d030f00c10800ca1000781041c441558002400c0702c11070782401c0d01d9414031820b91f0485040380349000401f18001c0614941b0001c804034000c031030724003040110f05100d002500c0d07000d00b401050605071101d55001c44c6460402c41c1c3c542c00c0f11100d400c0d4a00c14000c0c41e00500741c0b07005407801030460116281030111080c40b442103501a0300503551810310245030141a00c410b80025000c41e0074581c2c0d54121001003401c1c08124102014802e8400381d5910b082c0c010448000e030000300351030040301000000c2c490050403800080d50140070280d11044c9a07a030400051800c040002c00140640b404500000c0b9030606464030003c0d41c1d07651032100302d900c0e000e000888003001608078080c001918000c04d0340141c1041d007903160b00040500700340c42a04508105c11114174004401c203200041d9103104004c01c00d0014010500d550340202c0c2c0359024032074075000080043d6141c0c5170 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 438906420 1250 438905170 438905219
    0x905040515040203010801020a03052202091e0a050603010c0306060e040207110a0902031614030a091e0302030c10020406080a02090f09040f0212030f0a031d01150f0f 73
    0x101e40829041c40800e90040c40c014015907613981c540c05a14080e40140b83e5150209080c000416141c04581503d00710034503200c01198240761454003084400140070781140c42203a840b006481101c1c0261700d415120306108180801ca44c11b2010a00d42100c0341e080d01d10042610b4910180516648000750001140044801507154030050a00c40c07003540011003060b5101031a200d00040424494016510031002c55414404008402030141d8143c3d070080b2130960b5400381080050605106544825009801200c04603860308185000202192580350290050b07800800d180d001b0100c00c01c1a4840d20800c1c00c0309505051070f022010b044554003510320140b04c0e8000c10071000340d88440d1000c4020b040b00801515a50820f030a0819880400a400741c1c0a245600706c2100c0c446000400c8403a400c204980292402c452044102d004180b0881801540c2e410400c800079214000d00541c01800d04124048242a10385038240c0c10018165024101c42c040c111b004120f9501107240d100100d50a100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 438907670 1250 438906420 438906431
    0xc03061005011d0405090706080a11040b03090f1609151a0c0a050d0302041d0601021207050a0b040b07020d030605011e1701270b03100e10062310090504 67
    0x19015402880165030f0030f0740091504040109500c0001404001c4074000d840b41051510350708900c000303403103c200110103021420030080000c00c201c01c005680c01b00e500001e41724140b100c1c1c0901c0d030400000d4039414110000d410014000698940705501e06c150402c803110401c10b281a800064280e604a10500182d10204451103014000e0100840007503104040e590501800d000103402500039001d40c20301130281840300b0900080b05400d0314000d02058004100515850307038001740a40c000541101c190040340d40c0d24000840e020100ca0040c1d100703a2034030407285091070001f0700d80b0420340c5541c0d08244c02d100081003075903000341041c11455450340008c4403036981140d00392403c850b010205519022050000a02c0d503417a12428600149103201c035610741c040d0903918500f524101954113034503030419001c62b0f403045102c0c0c0c42a00c600501100340c482315510500c0080072200e159102d400b1342d556840c0c40059882c2c08900c03495080c942141e6800c014842c000006042d07200c07a000356030285940c0c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 438908920 1250 438907670 438907697
    0x1050d12050712020105041101080603060612120304051c1d091e041505330d1a04050d0c03020607030c02010e011806060515070b0c09130e0c0306100501 67
    0x20000c0b2010319801003610030b4011110007000303000305401c450035034103d00040321056956119201c5240200c10041c000c01480d1070341c00c1081480c5191182c140d40e280300b16131865000c2e102c0c01c0d0145100d1401040175040a610300381c00120300c1038040d0f590004016144211101c48004083c02851201040e0381c04040f0707a541c8000c84806000241c0744039030726a095803c0000b041001010361a0101c0c07404805e00941d120494040c1b0020002c500108aa07003680782003915080b00207948102e0031000030650b04810356143c0350000e0810040c1c40c2c08407499250400c010900108110b05242c408441c03414001c0b030803023174a00940314400030b000c409c10076469040541d00e46100b50031851130700d11083c0080102186a40c7c038030b101030ba98040112842c030704ac01e03000182ca203000c958410580310081d007264a010403c1e965280c41000041800103d59002d004c403c803a91160391110b8006441c2c0b81000800d040720520052415a940d03c900344a6445201044841c0007a107c1520031900c00f804c0160354240c1301d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 438910170 1250 438908920 438908927
    0x2190302090103030f0516080c070b040602071806090501180c050f070f0201020c1c0b0606030606071e06020409020406170601051615020304050c090c040302030303070c23010507120501050d12 84
    0x20355541f440c00c0e4500907c241c0a11000c200104000c1c0b1521045640f1550380307080f0080c40c1d028a105020168000c6902000740b101c004160820b28a10701034002038007500c0f006001d088403000c0c0c000c004c1c00144a01c9013150200b4a1051400703104c1d039410300b213080001e0341d0142c0034140b00300c1e00001c0c90f401a4001300340469008000505464100502d02c59043c1c45061007803141010740d5a040d42d100c05400c0c013080483c280481120b02130340c1301030b212034038040d1a51562b440e41213444140d00550240411000003107030309440a0409801d21103000340c2e88500e0640c00070003d000300e40c2030714120743c0c14a045c1b102c981c0e000802c594042d001c403c0744171094141ea040100520848680144025000004105c10417101088100301138070300301c0d05041152680210a401802035000080d00b59000300040b40c029400342c07900500700c07482190640343d00300301c1446059107100146400b9000d691100d00f80505a6008001c21038646140c00041005602d04030000c0d884c0401d400c400342044640c209200600c920 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 438911420 1250 438910170 438910177
    0x7050c060d0f060b090a06090311060f130b1e1206120109020301090b04030f0f050f03060d050a05070303121109150f03011202010e0d0b06040b060c011802190302090103030f05 77
    0x144004000f02d03a603c0c895401c15a101d00f004c81c1c0301b03c14003800071402a0254106500b602d4012440c260707182c0048040c003086500100d6170828141050141030790002611244001034118500ca070754440b601e06c100000d80d06003240010000c9201840034200b41d18400900340e5008a0031a207601150820843c40c138010207481d400a5019401c007144d140c24405c41f0440f541c025407007552402691004407104891450360100040d00080c01000b07624040c020b82c0f130145420420003040c07075400c100c450387c0e200d1800c0101813003100d068200c283c040050580000711410580c40d142d1046c072002c20070300d100d600b05208030810700788500590030703503880b0048160b81918081e8a07888880303541c030f51712081c01c030030a0295500d003240020303408402c814850400d05400345415500021045054507440c08000142a107180c0c8550040d4041c402c00c0100482405401040c4140203414006001030780144912142140c0c6410360350321150a0802c01610761440f400e04590301458500304141c3d450104690030b20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 438912670 1250 438911420 438911441
    0x6020715361805100603021204031107052215050a2702070c0305010b060702180405120301150206060a08061f0b0a030b04140907050d06060b0d020301051507050c060d 73
    0x41042c44041c100803440e0744101d02601d8569000b80140303640e400104c09910581c1c65070360041040c04041000a0f001e2101495202160000e03642c8172078488001c00c0a5542c86015002c200561210140321100385100d0703049151090040b1503c1941850301041018182d886820311204c110782d00b40f01d40903412404203500315001c034400d660b0350301581002140461540025503803135190600511480c90000d0403203c0450703010302204260395901a4000a055005201303031654082c00003801d80f08007001e0000c0d030280045440c40c81c01c801301050f00074988040108400d0052040714014012a14002103041d0700200d80c01032008851000d403a54000d481c002c0e400765440c1e8038085800d501c1590103800400b54150705075410040c20b081c0244407180d0300010b4881d4003054006182c180302d181891a84184803070702030f0601140c1c9aa5403c0c0200c0705902824141403845c0d404001408145040c1c0e445143c4603005071241406c00b0034540301c0f1034441000942d05803240300009001041c132052600f005203140b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 438913920 1250 438912670 438912689
    0x1020d0f09050607080709030215160803100506040513151a0d050c0702090610020c090a05040c06050a02060c031305100b040b0301060b0405100c0c0602071536 70
    0xc02054a41001a1400010850703250041500151540e1320461480d4803d28550ba80da80503035145070280000d07250b4540460403500c1007000b04111541141c041c0312109881030035030660782c2c50036100c81031210701181c00452180008020811980e03a80003169801c0350114100012040e01c111451384086032150300061080c124a01c448001040d801c01400d4a103400210a006c2a540c54010716060310a00384002d601c00c0041c80400d500f420007401d00107011a0600444d8450903802000801e900400c5036000c0e0f1464a941c01c002c100070f55554214010185c2d8242241000b41c0c1d40c4001e5100e01b8010b0804154000200014001290648500c4880c41e004000d5640d02155a0030040180180d02c00311401141000c982e90101d003014400d101c100c840b10400c49042500302810031804e002000c840b641085124580e603004120740200700f030020591500285802c40c034108078282c5010181012905002004c0b42e01314040c104591000d549080c042421100ca50111401506a0105411050a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 438915170 1250 438913920 438913931
    0x6040e0d03050114090402010f03050c0f16110f0108010320090c03060a3602130b070b0618040201051605010606090617100e0405100203041203050702210c01020d 71
    0x261034041c2c0c019416103404a0314220b26190f50400d105100c0020703100240050f1454040b914810b12035808581c208140511052401c042c2c0c07040708510f81c000c4000c90300d903594011408401c0020342d90001c0e0f40020242c4805001501d07650001c1c200038814840a000c04001d5801a6803a961a0300c08020703507000141a8100d07402c02e03203081829500205d810380c1c02484000c802107040084010418100301c01c5c60102e101c0c00c0c5c444400d00100320300720031712001c0c00c0307409028010404540388610301c00340c40e44040c22921540c05013003030924020040c04640c0100a0356203c1c00c565900b4141541d070258081c200780d542c602d1102e03000440c0e80c048003405002c0c2d5190240105001d40d2298a0004944041e0340307150030100600038960f82c81c00300350340140680328075400800c200801500d07840d0740700e80501c0c00d0350760190303404245001380d90003128226025440c103000d28400c44d406200d11900805988011b0041500e500745281103404541080075034000b0200d040542d0b9038094040780c0518404170030610a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 438916420 1250 438915170 438915193
    0x1305030304030c1b0302031c2015070503010305030703051602041b02240a0e070902030703020307300e251508190209040e1905011107030210020306040e 67
    0x3035031008408541d9a284002c051310700100c48102601030780d4009002e41110880600c1e900ea0303800d400141042445076140f4100e50540741c05100b071080060078000340100c550380ba840c544030703560000c00c8034040c04018001800468070001c117507080c082d81030821954401003040000c1090b0b214210080d4060700300b45203281450341c10341d11030701c8004894080707600004540c800340f1301b01c4c2c0d14040c4600381c600d0004001050285141c101619905c4401c1c142e0700f20545490000c0c060364400c84210010a800100b4800240d41c8003202410024650704025010142403800c041d40445003140f64015a0300c0d184103036240d1205004824074054110210141140c20800b2490079148a01c0b91444041d03400340b08150a5000f900c94074403a444d4a490200002c900c60341e044029040000d4a1f40c02981c0c5003440004500d0421011002e8814940304c040394030b00602d869400d44150810f54900400c01380441c3c1c0c00260000780201d54007a008101586070755462012030002c00e0f211180344040c0c496544800f1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 438917670 1250 438916420 438916427
    0x1306050d0b130c020d0f1710030803040305040609050a0b031302040e100b0414040c06050309011407020618011112130b010605030411010c02010e101404081e0a0c0e130503030403 78
    0xf5400001602580c210000804c1e041e628100300c0803c2001044d814414107800d05820548507602452610106034203d03125160400035806c04c0383c013240400d200050502c00503070422040002000c080b2244144a818048544110300000d06140894400c0010280465855401a07001c9860600c01c0301c4401c0c0300c03903010074045d010000005000c0e07442d110300d10802c00c03040506d00748540d03001240c01c2d207002d1401d401260207a200510031509550f0701c0070316044090541c3e0300603000d59100d500400c3e05081607840d04900707086108a2200350781c50040013410360324405064844030300300000b00320135581e241c05141c000c80309030040017405c0d11f003040008240141c004002d1401280070340301100408640200642d61507940c003401901042628044425070b241240180045001030301c1c4c501080200e040144449811540150125411407854140f102c04d41c503040c0d4810342c0b8803200801140c8410f031a518070782c00b51405103030680c400d000c0010b0401c0c3c030001d480000e4030364070804880d580e141c1420000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 438918920 1250 438917670 438917681
    0x302130603151104170309040501060806031006150c0204060909030807091203020705060a0c0204050702061f05090601050c0a05160e060301020a14030718120302060601051306050d0b13 81
    0x845003018100d40e909888045440342c00700312142d105540f0314107410100000001da403030540a141794401000004200d86890040c0c500900494590911500b01602003600703200400b4408004146495030070070034810100d101000404490910b444800303901e00215001d022141c00620020b41404d4a078400c140e030010760217124a081c1c3d91030070369041d250380b9481a034195100014005a01c8100140854a082801401070312014107021190728440d50105081c0c0340100c0d408030150704640108460080d081c00030065240680e070440d0ba06508203c0002e40c5100c01070300e003a04000303000c500400b20000c200034041900350400119030802030250b0701518045c030140640312510380b068002c2060380c00c0c140250782e200880d9864208805407032030f0000f04150002040001001800300403940b140081c88189009131501e15138410107076160707040203072809501034040c50421000b001106040001041c101c8143c50217031600c542d0382c2c4181a40c40020744001241f099110030700090303040030001103031f020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 438920170 1250 438918920 438918923
    0x40b010527030d0c0809060d06081f11040623040b22090509100915230106210507090b03130606060806130b060403080a1215050d0b0901060302130603 66
    0x441d0f40700103007224215644441002e00404d60300702400f914a6620b0024080c00641170708030f500041c2e1558440e0034a20341840c80ca007202c20740143d40720301d1078140c620b4004d2818001c0300d4401c0f00d160524004000380390501e22600c1800001c40c1807140c002031300801080710010003100c0107658031825142d52494411000010707140c001d0045502c0028400201d00905201d080e903500900991400d40b144400901007100c004c88121032100c842010303004852013900180100110203910002449440d00b003d01411303003140062014070480141e598404c400d208800244082d0041541d071103044007903a800d0355036017208000c28404010002c080c0600805a0790071401100107004507a5598400c0e600303031105840c00e07a0003a00c0199164015034043c0c02400c603940d40a400d8a2a01e991381e100c81d03103d601f1a04000c1c0000e251406c22034a04540d50040081c00144594540c1c006481c1000280f6150a0b080000300149558030004104101c290f2242c0019500503000140c0ca10544240e10000c1105000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 438921420 1250 438920170 438920173
    0x308030411091e1617091f09031101090506160513240e06090111070b180a1502060f06180f09010f150308030907030c260c0102070302040b01052703 65
    0x5040c1c404c8107020b1001c40d000070f131289400140b0400012041a50040c01c004040c070800001d0005195262840c002038084100b002501f05654680100800a8000007224580c1000104008285c0100b55075030042542c00442407400040301041c0e50502552581a9204075002400a99000d5003070042d00b001c5d0b90401c1e007400390600d0050a40b036031351607020b490303412031024000d1650a5019103100185a1f0786d8000325a04075507640403a2030203078061744d12040e04000342c01c2a1802810903a64660107414200340d801245402e001e030080d542c050091400c00b03811040703408225142c9907d2461030020940d401d6440e03103854a03036010700c2400e07002e49000a01c0c1d03203070124800c0b41607058441c3d4880002c1c07803204040c031030b1300d1038660510982016001030b01500030010000300085480c4420300c010100b0b0b0180021a50005140d113031200080c10b910300c0150000642c1c81c0d20f40ea40864002d05581d411a40011a0508103004031554020725049484481c681c205e0700d4289040c024a22003180c000b20b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 438922670 1250 438921420 438921481
    0x2030109060504051e01060e011403090a0302070b16110402160605070f090303051b0102040b03040c0302040510061707050c0a05030304020319031706010210020406030b01020d0305010b04030803041109 88
    0x2185004c172020400c4022005011000040c090580700300004403d00c081454006040385d1052003c10180e40700b565800c1e41e60744010b290351304043e01842000010554a642035041045642c3c5030705441d04083e40c000d0005000708541003c0d42d5540e410b640010200a400a0308480719142a4004010985104000c51224000959018400d02460058039456a00d0505003484400788414048500c62003034200c1d5005d0202292443d000c03c00355106500802c00e00c140340345180180b001f02c880240120030301056142c024002c16412803040c500c031030100301441000b44e4884400303d815000d07003008415503000300c068210078000e0000185000301d000310160b80521800020000c0c00c02100c0c2c82c010041254049403c4060484440042d031100e01030054820818080594100700c1e403007500400d011a82e03074070005800b5641000401e25041c2642401c110b95410030b0390181c01c81c001d070703c00284500b01c00000101005840401c003c50045d0142541e0041d00304441d8080c1035088a4500d0f138141c40c00034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 438923920 1250 438922670 438922681
    0x3040c0f0605040b030c0702101e021c110c0613140414040825150b01020c0604050d170c030a02060c0a0906030504030203160c080c0619030c0c060203010906050405 72
    0x5020311421985a074880603d020b00d000c0700d8122a400040c40f005443c0403c1c48204c0261b02c4480d41d0070001c2215a03900e0600d5000602c401202e468401c0820046510520703c801400c51070410700b401e880f0290500c0f00074400e4903e1020b142c12800e40e0700c19000070020075100c020300d01301c40c44201aa40041180300c440c5d02c4101c18042181c0b071545803019000101000b05011484050080070407001500c0c000604030b50060401c03024682064003103c5010f44e40a80e500400102c1c4204800d00c4000d2016040310780c03c40002610034001c600441c1e12450071012860200f01010802245403444140750035141c0301c113105016101c0e00048020005030007510001001d280c05041110012829070302c441c1484c1d414040100e009100040c000c405500c0100710b008007203424261014020391050814103c100e0a024215060000801603503001c3c2c042802100c20303111408060141d07409040c90b0005003680d01c0c04c0220354004000f0740c0544180d1000001040c41c1003d601b040d400d541058600344011b0311030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 438925170 1250 438923920 438923939
    0x6030e0316321b010315030b0a0b040e1005070207120809180405062203020a0b060a0f030303020c07171b061306030519050405150712050103060203040c 67
    0x1810700c020035041c42110540006403440d07072030018a000c4071510750302c00e100c000d00020212028010702100d940c40102c52286041c1124512011802c0a00c0c0602c03c051035001041245056800000d05c090010340014245000640c440c0c1c0401d5001403040c80401c1c07201c0400b40d241c5d480c0c240100c0500e414540025a10350001520700100c402102d880604580f0684030300c1c4a94000303201c48c951005030885030b28086289412100e0007030340618080d040d2410038180c0c029501c528024400e002c0c6000b60003a00104e03070041100e0700141c2e0401484004c0d83c1d2544001005034070950019400340d00c50398004014180e15501030580741500d641241c1c0643d44030064070190031010301c000c00c1240d0140c201070f102100d803580d01130180c6038050501400d10b1010701080c00c5000c45900020b00007540d400400c058110400103100c005012018100090304158a52170b84541081ca182d00380c0443c600042422a44120303995520311001110802c503a503160318180e806540180e40a841001c00000017040c64001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 438926420 1250 438925170 438925177
    0xf141207200907051804020414090108060106020a11030c0d0b0405010501050102011a0f2b060b09060a1205030c03030c0a0e010e030c010e132f090a1404020d1506030e03 74
    0xb01142d0303290b9140d0804850b80d5001c400c4403000b0310000d0300303400c03090b44990015201804584d007000352140c09110504c54041c00c140e00640d070652000c401084030310303000705201c0c2c441134014450400c0700010902007458280301d0110703940c1050756425844140402d09009600a80c46540244083d0740d0f40c20049083c0d6405108003090001c09800184031031502e100c0b00740303140310302410208201701c01d4444980c3c0110041c03286003c5054800054040191a02c1541001b04d400c80d03907450035040c100c0120301c2419490051440307188000b11340d0002c1c170001700159005146001b085a07960302c1e1034003401444d030304640c600001003005000011410742c014140b00548a0000d001800003150036401110100750b501c4149802001c100c07200c0b900ea003c40e02600341c1d4580e006103d807506041d00035050203500d54600c4003641c0c4000510200740a070380d500544100700c1d0107403500031013040c1a4074001002441500c5181064514040c07981c1c1c5181c0c00511040115581c68400304030010182d40001c3e224031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 438927670 1250 438926420 438926483
    0x20c01170609280e01020d110f0306040b1305070f030c0206062215080303070206010b0301080a0b04140a0c14030d05030c0f1b0105010306060902040b03040f141207 72
    0x481c42c2001075014080003100c10305640342c1c5160702001c10b52000aa000302d4105004203c0d2594001a4040907a0142e003c1d100c1810001c04140b8030b0003e0444200300b0a020180071588500d8a5420081007a5220306407040c182902c51820066800e0141c2d0242105191004042c046030800c4d600400032400031400314819030700a08a0700c5800700c0d4450b48540c40d0710340b1500f464215070361241405121036540d08003024188002c010743e900d0030440c0020740741080580c080d40c91510300700014000c5034804100c8034410b03617104c08008010344617031421241001404002446520903540d00c4c409001c4010741003821103e02162016100481c0403d01d52121000002100880c501300041004840751000070003012210340c5046080614660342d00803010040e0207945850380d103840c010320030300c982440303408014000801c0443c6072610b0103030800f50314000217001610502800d5903107820300403551500c103203691121f4180d1314041b42000c2074500503008114140c841d04283d0910040b01c078550115080b40b807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 438928920 1250 438927670 438927679
    0x30918010e01091812031508070e0105030d121820040b0405071d1f020715020a020a0303080a1d010c08100302030a0803040c030b1305010c09051c0503090a0303020c011706 75
    0x132001500d440510101e2500010304141da11380c9403550a403a607200e03040181c03070480054a101450071340c0140c0c0815040c3c10251194000d00743c40c59072581c209211281403802c4c414081812000403d140340002c0740d03084060207845201c00022100e0000e04441d190003102150100b000c030318404c09000c00c8030300c00c503286404101300c06120307030007219882c03110f44000034010200e6840030703440004040307000502c14000b805a0b205900c241309070005c07000e10b25403d8044d03100400903e03d05030006020174020744005010f1049444c00f141c040c1680d608a02c04440f8001200301c018100c02c031b04030f802002407024060000300c0d40740c0460841d452089944048940040081a0740c070702549512032140d1000c0c0003290ba01c0003644c0700100007515080000e100f081d20000c0e00400c262641071103802e403841c05c2c003c6020031641e00030910aa0b03039441070130030340701c1d0b0825806005010300c1d203003030713407843c0302e80f24030b155000c02d4007440003040507400191302c048041e085c5c0c0c52400f101d00c014020f002d0440240c95240e0b02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 438930170 1250 438928920 438928961
    0x603030210092a030501020f04051e0321070507140f0910060509010c050d090303080609040506010e100b04150e030f0d0804020424060801080304060905040e030918010e0109 76
    0xa103c14180c8000c054012900b18a90081d0340359100b50883c0d0242d04d0165081801041c01c00c414981030641488001c011340b4034680c6d12400100003901c4078444003001d01d030203e581825507040c414a200703031014527500c01c040b00c0c4880e8070340d80d00d184448240104076110350151440a042d50030702641c6c7c0c0c0e000d0340c414000303580900d08012040d0303042d401c040740c4c4604104001e007504010034010400c074050b40b40d882c0c403a40851815414028480a4010241c6000d4440c140c2400009200007600c01d04544a1031480021612041103400c1030700500c0e4807429041c04042000f00310034144e44900343c480040c90b1241c0b4404182d010500da1940d840352200300c4ca035040503101d489010701607985250301910041000038415034009078a06a10003003a203540810001c0107041c401d440e00311851502500b0384030000d50a00d894000c000340440c51034050320b4052510750270003020700703c01007040d100d822000030300324482c030009a40320485000c400d1203044c1c0000019800040c6181842c4900c43c00d641c000a860141c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 438931420 1250 438930170 438930203
    0x1d06070305091c0c1409011202060910021f0b0306070306080613030e090c07050d02300d0203010806091b010f180806090a020f09070207060c03050408060a060303021009 74
    0x10043c9480e4500149100481424400203014610f040054490441d990090110034001d000003050160003900c070b80c0c22402003a5003d42d58a00658001c20011205002040ea01800807414410071410030703040e1a8030110440c1c1e2900840e003000189038000e4003151266618200101e0a8400922071826143c0042d400b08030018071040070400c20a01074141b44940310200c101061411808031640100325401041c00e9003000428051150b04107030620050070076080c8034046031a0340360503c8604000043c2e0f0079142000c5900d04041d42c0003295980700440d02da6a540c00802c0d12400c00701c882039035900680b02c0120000546011001e480041a075640e00e1032080c8850a036800310762140d403a4080700400c0c0c40000d04038420012030b44966640400782806901d94070612032100b800c03185103840340006004101d421580001d0355000c940c0c40380703041040503440e41800d0380d0f0791055800c550703031034000c1604200c0300c40301d2600071034101e80c420341c01c89402e107203030f031480c041101da40007402400804031505100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 438932670 1250 438931420 438931429
    0x405092d0102090604060c0501051308090f0f13090203070609080d080601020307050601180b18070503040812040506180c0a090e100501030b09160b0d020a0c080a1d0607030509 77
    0x2034110410600042c0b9000041c00028080c1d001540641c0c000740040ba81030041040c00c2c00355541040e40c20007a400b07841d1555940261900500c16064003803d032410b5448541e91b101c041d880d80070741303014064602d40b060000581000c1d03e00441c0c164064858440009005480380186204591070103001e0103608000701801c0701d090b20050120750440c0b005100d0007003c40e000348207940c001c0c0104041c0240f24000303c800c050949224400c07492107281800060f1042c4a0313111800b650010b0300b0b10b403040d6a41d44601e46a412800b405141c0c1207211031120401040280004000c6e0254001200d42000d201d03000c4045a41e98500c0d01946400080d802810080c0f0150b03600148071240e42c9034142c0b10043c403840c102c00201d60f0242e00c1620038100c04000d10410800034000c0400c0d082840d020b02200c079090014000c1c00d44540844030705460350004801040e503109140014034140c2c0702e508565507030342c1040b00400c01c09405031041404130310300c082c841451400308100d40c1081d40c19118030b403c2040348800c01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 438933920 1250 438932670 438932743
    0x304050a24141c0518010207021c17130303080f0114010e1f0519020606010221091c0204050921030a0b0901030305071a0408090409020a090218040509 66
    0x10320007208148151500e06200c0e50f1404940700e0714142c0019a4a01803524403101302c007064907590681d1042102c0d50158548100803a00a4115100740034100c8092800700502c0c0342e1801d014810b1803010408000c100d00340e200f160100c0e07000b50781e18071a17a120342000840c61402072081444851030b2540a0030254018006e04441d058001c4c04506014046207145000c2c41c0d20107820070020700d0003d44020100100140001d0800280c40249060301d00074001070358403021410202c9074038030071a03010580d00d520001199600400500700302c07a8001d048000c0c1016401c0200d080784180e0500000544032a070001c2c2e10807200201c59601c03956400c0348104501182d1000c0c2142c1c0b03440c0e440b1514107401d03885450100b03000310311a68440d40d0f207947d1410a01b0019003020702d9a1040750f03e800520001c50b8403e010b4403007a0000705d90010700750307401e8400643c4410440e07200181060002c0354020f8010320a61000450510544003886195903903032025440e59005a03401d10441e41782040c4040280064108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 438935170 1250 438933920 438933947
    0x1502072313050a0902030f0f0709050f01060c060207020a2606090706051c0e0d2309130f24091e02031e0c040906080102191407080403050304050a24 65
    0x50743c042c440c5c0101e0704000c0f0100aa801a034419094005201c500b0003000c4018580b1500400842c28900c203250549075061098000300103450300000e05110603581140c0d01154000d04280d80d01d961010381401c00041f0000d0180408403003c540208524042a0148a4481d0310f0142405509010094030380d070f0450314004120250882c0f10411003c0b603072240d04910100e0000038001403400712001001440396190220081d40007180020720350302200203441c040381c0c0403681c0100d50500c807030180009003002120b02c601c0c2e9052007010401d402041500e00381c00c0010174020400e0603103484080055900d82d410031055a4034854002c41d02d4103e0f580619040704144100214140390000c0424400000303841c41d0601000c006410001019584146402400c000c002542410f400c078080400000820722540c09203d02e5414071402c400720f11048402850f406601aa02c1e19100e040455881d0001d020300c0d409442e40c44000f20300a54a040000c04034030030b562403860302c0d0111103800c80712481003c03017 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 438936420 1250 438935170 438935191
    0x70303080c0d02030c0403120c11060307110303161e09050904020f060708031509011d0c19030207050f071a0c0c060f07020a1a0d050c04150207231305 66
    0x150301c2e00b00703528001103011740c007240c4503192124214101248000d00140882c414840644101c00004401d031002581d00c6204841c250748a988441c81610400f002540c64034080c00001f007000661494000e94000c80c8185a0301e8070180780380c44520000020a1066220214030a060100314a00c0e2086031242c0c0540f02416610710019000040707201394218401c01c0b9400c3c403000c403c01a01c0c5503070130041c29035054111181d010a52401050703120184a46c00c07410101030251300011068010003080780c046a00c0c0c00c1040c204064030010050094000040c02c44560145d02081140010300054032000c2d0741261106045030b116007410342d022984030001c0480705009000300c401790740d902ea4003d0400e40d044810a166181964410400300074210b800944100c100d0420080b4078007604000e4855600c035408002810307843e14600701c0355a00a9502c822140442107401460301540407400d502181c0c42100c000030001d034003004c250808401e465501e6084514205000860562a0403003908243d0110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 438937670 1250 438936420 438936427
    0x30216032102071a090f0411030717040b060d0c171501080d020c240d0204050f0a031110020118030c051e15060f120f07050f10030e03120109050601110f070303080c 72
    0x880e05503100b5044510901c8004420080c8007500035140503145c2c0e11102c46990bc514095660001c1000007a0041e40200100d0f41c81000300016105e400000c1e0020141c958101109140b5443e1746062082d01956044211400054500b0000564021007550340d00034101d021919030522800c5003003104010280f0b032406021440130108100203280700c400034000941c1d10f034240024880b4002c070002c1014082d90b450042000480c0c0030b1002124062821226034600d4800120124050440c441c0c00a00d8417680c084204101900803030f111107864400e0702520940010b100e00460340c80c10136000c20505420040000001c00040c5404a61055005014031440780540340405c0260140d0103170700905521000501c100c42030100102c200624040b1007000102ca803010200d800321012103846000c0c5901c5a4810401c5031060081d03a5940d401b0101d82c0f100c543c0d40d0f0b09500d000d050203850300c50102c1e56400380042c850001080206d2a03d04460090010074916070b0201c030007410040c00c5141214092 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 438938920 1250 438937670 438937699
    0x1e0a05040306050703060f050d05070306240e04060605100c1212150509090133080f03070c0f030503032a0c010203011e051804030216032102071a09 65
    0x82c03241030b00680941d40c0001d025418070003012000003850700624410348040c0c100072700090b000114441079035400100401c0040da8460b500da400080c000c2241c40500140201190b000409050b40e03205a000340c05c1413103260340d10824410300e5040458a0000582d4440360940415080d64800c5038404242c500745485000200071001120f041c038109081d20042620204168985905040d0700000d11400802a09072030320314070030280c1101d01c8507082d4030b58032054045030300640440e401c004007242c000740d510f04c03d51314003103507100d0303020b590121a18985c45801246417800010001e090325031084c021451502c860540a20f0040c183c0b01500000c60210300455810002d0710140410459280c0090381320f50511000c1882c10181e00c4603903a0000d586002009559100c40c200e03601c4011107414070f4103644583c18120f04008400501c0749071061600000410040c5480e00220481210b01c0e0780d070200f40b0001c0d4101d0301da07003140c4154040d00c011420785801e031070b601e80c00601c034420000300300840a2128 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 438940170 1250 438938920 438938933
    0x30405120f1303030c030201050a05150d020f062802030301050d03080433060b090a120c1a030402210607032f030601020610120605130c0308030702121e0a050403 71
    0x103d4100700e000400c5031022408254090050710382207c01d01409210f1132400400143e203220240b40102c3c41181c005c032400741503449a1307400b418014000381c009030b0344245c00c0b020450300c1c078460f50206403403840c0300401214491010080d24165540141110408042d1f51411180800090401d4424071350315000c02d111559003044174440b0010451806007101c2d200160309080f107440343e000340380c4c0e03080070000a45656100d4001e00e0943c1c0c10880541003d072007505040b090120140c00c13290180c00074130340305407017480c00c0006148664401c84020107068402a081c0a030b002282400209561100020904403402504a002510608400740c50002842c402080050301090f111400c95140041031200c0c42d40d05000b031039407107400e00301c04820b0185800041811080c82c2c6001500007584c1c2c0000c00c000d00d5601c03030412035a81d048402d0615454983c01c0c8406545c0c0142d13040005480b5640c4a41302c1d03c00c8000a596810b807002898044021120007040c5480e44044c2c481d500b000360404c0040009803a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 438941420 1250 438940170 438940207
    0x150812042d03121107030b13080d020409020d050c07151a031009061404050a120e031b09070905091504020909130507050a080d120204080a03020604060b06030405120f 73
    0x390000302c01e11550300d5020780f40842c0c0c020004c001d0b4000d00010b00c082014030901e9600320f018603155400308641c50801d1009409502c010314480c0b4000200050070b00441d4010b0441e890143c541081240c603445040101d6124020004210005440c14040603031301c1d982c40040766814000042c1c5c0254141c00000f0b05100c4104205020381d540c1d41031020500c050307441030300c1346180c407040c0403202418692502666400050801022003030400340070080c2030f204641415a428010301160303c3c204140c140001d198000705030300d0340600c08004c0062f078414420442c1100f1240007421442180c0c40f02c039145490a01d4904c1c103141c0194007004241c1103622110881c0b40301c1c00003600c500a0126961070014140301a0794059441811089000c0c40000d0001c1201e02034804282424800802d0100003071001e4050740c2e00c815003900403888144107168000c07400c68807651040301e0410a00e00d540d4100300d000d000550b4060719950100e4818070070521090002c00c0c060a5203812141030004034150000a41d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 438942670 1250 438941420 438941423
    0xf02060904020a181502031b1903030203072c06030604110c07090c03050c04050910080f100f0c0203091003060e01230a140f0111060109150812042d03 66
    0x1c1c1c0d6491000701480a131301d110000b400343d0101d419440c1500e040001c0d03603809110000301c00603070441000c1d04816020000f0b034404400403105100c0180c020704000d002034004680c0640442c48800c2c4034000c80a8801d1101c00c0c4010511410080b055000140320858000414603a0000e64440c5422064044a030203050300a203500010401182058003140940d1465094402454104000d1264070304000381510141d550589803070020740c1d1101219240395009500c505107070f000782c4c0c1c81c181c80312802203064900695240d1090002108000f5010219018000f030322005800501500c8000e151400742551003804510340400d02e640c0300c1d40199510f0200781d001407010000d110720149200508032849100d850101d5460780074034a01050303480c1780321030102910f104009009000813144c0c0034100d260030341c0c0d02c0b1800701ca149603100ca03000c1000f8915190001420090320f140062080d800045d5000c28480c07509800b41013915207041c00e080c5041c80907910012010426400c194800078411b084d0045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 438943920 1250 438942670 438942677
    0xd090516030c06091a031305010b040c05030702160803040b090102070b0a0e010e0118060f0203130f06141e07030302160b2205060f04031707080a110405010c0f02060904020a 76
    0x551600e200505001354075800b020800c4629414000c0c101040400e60364001b14803151500c00d2070f02e07460078500411382c41404952084c5044846040c0c07550000c042e41c8501d9880d0221500044000b44032460214580710b2024240c0c020001404000e6002019158104040c01107600ca10740f54035441d1043c3d0468014400000da2f1100384000669026004207031210080c209a600c0c01e0488407102c0c150403160050b801844445481c580b9454402c1080f6000b110300d260314890001d40710f01490b4072207011403240d10002006480e0248880000c0c400711140350000c1100010741c03101251030b20129400183e000d8040c180e0a01c200049005454002c4080c18860100246241b508172290a010404c03001c18081c0c0c100c3e01103440d400540001640c4d0b801000407008005503558a1400301d8200403142d500c3c0e20110100002d0210141d0800030942c026801d15a05000d0085a9581c40e041802184509070000c2c540c490400701141020200c02c2000d070002d40f2451801d10440041400c0c2e038440031400000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 438945170 1250 438943920 438943943
    0x230d0209161403010303020d0f02031e04030b0a140403110c0a08100f060503030702042a020a0b06100f1101060305010e0c150c21070b04060914060c0d09051603 70
    0x1968445941d02c82c5110350b116030b60031941191002942c501080c107c00c028051414001c2070500c1c000c10a40c3c04001025251901140c85060280982d82051000b2543c490240b07010884010b03041c0a008402900611409903030758440c1c804070303060045d140d400e10040c010400454140d8441e0311078200074101d440e0052843e0140c41d1b10007401c030350244102c0e80d08140341020901095034044206c07560700360122000310b0b4078400f80020303d581b0840d45241d2818515980302c41c8018076004548000524014015040d1580c1d810080c4081510801810000141281003001c0001d0040b118860181d04038000064603648036555070b400c42c1e038900400031059000c01001c1d01e0700e02d4120200800c8088524000e41000d00101c0c8955076000d40760111001c80705072100e010003030000d071800e43e03003981d030402101d40c2242440c0c1001c01c0100192036080d5802840510011000b40b070006513075004441c01480f50b0b1030900b1508080c40140301c28001111640200d01d105802c05000340e0030750000e11b020b580c1c0f6050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 438946420 1250 438945170 438945211
    0x3050c15091005190f0f0f080a020f0d0609090b070914040c0201021b1609140606090d06060e06041103191a04090503091212040b07020f0d030c110109230d0209 70
    0x21519046841b0f8108010b0650034901652300100c02c64220303074446009a240d0240380e0030310015006400606078805c3c60034000040118554100045a6004002c405890b4035040c1080311038070703518000c2d01c91945d003081e0148402d0a15034400150505188001414288544c55100700d88141840b101d02c42e9010940e4001c2c0307010422030320300060a1030a4204020078058014030003500d00200715a104680128132600075031103440134800f40c60780c04101007081580b20251200541800d444190007075140000d51300e10300d0f08000440e070040340000642c6001c100040c1468001e4014407c103801c041c44008602700040d212406a0035009102e6405140c48031888420b101020581d0100c803141a40039402d404c01100f410800c48090791203081050759103540134000b2403400c2c074803a4101500410b078070030008103042c0d0100031408201c3c41004401070341030980c801110000181e0050f24a070712070f030300e00c08001501810420a241c0e031010707000b060210350903000203415420171202c0e0940e01c2c102000821 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 438947670 1250 438946420 438946427
    0x4082215050901020604060e07080307050f010b04020705063903061002010203130f1b06030b010306080313170a05030a0c33051906090603050c15091005190f 69
    0x32101003616080381026140300000356034040c061301c0642030729510304c82000c01080a00022010740401c1c1d0131a580c0313014500e4226030742c14140400314159440c1a2006410f46050700860300e10300e030414001c0580c0e49540004203109110104440d11554010601314407040c610304013230903451181d03150307551245003ca06001180840e0490034085910400030000141c041d0410f0b024055000200c105548140f031816022034022901341000884085200240f081da05400c5061100403c2c0d800740100e950714911542d0702d000da1442c9082e0030840300000c6c070081c10340c0d0130001170f440031000489400c090151103903400c0d640000b01440c0000c0700741804000740b00c240420006d01ca0a810071085041c036100712410b820349070b20612a902e858030b9002165007001641c0000c2100d203185c0d10b0801c0041d035955100e0005100500c4100c525000303c1c488200700c2c0c0f8202e040040103000c0340078858a4102400100803200d00217030001e0040c444103009950001980d880482d01050460720b17103159200c20300e400035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 438948920 1250 438947670 438947699
    0x703030807111c020d1b0203070b071b0909050c0109060203030a18020402071118010b090d060e060f01050a0803031303031112012c0622060305030c011a0901030c05010503040822 78
    0x8100c0a0941b01e0403c005803030005058044648154500d902c5000d203103000060840544a2420f5081400d0340218003880c9560000e10024403500c1190708800d100c0005440e0721019201e51005a003061000901035803480c0c000b0741d10415804209049610140e0006040741c00030380003036400090900e066011802c20b20145c0c80302e010b940026030702030341c541002c1030054490255458011515480c40c4d1040050a812900101c0500011745009103045101640b00000900c1220720030043d0540002d03034801302000b00d90054007002c20010400d001a181074024050f072081140e4812030405c018402c05400e500580d004c3e09031b030001c0404480301895600000302d140c1c800c0a118030205000d0143c240c3e1009040e241d1803d00c10540c00410a1020801d00200382941c0041d00c140000600e40e00c1c1524190302c20010700c08008400342c58903e8003018031051000c240401031110400c100c003132103e90b0141c006150300500c1041a10304c0c10740b60203110401880001c03404c81c542120680180302c0820f000191 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 438950170 1250 438948920 438948947
    0xf0705060708010b0705030313030909050f09190507120230071401081503011d0c090906010e07120f0c020c1003020f0702240c070e090703030807111c020d 68
    0x13542c00c12080e912201d450388000b0b0992442241001e01c1d00d07081501941c401d5004203506d400400c05803500f03003401c045907002140c1c0e000701809216180550042c610451a0032282c100004140d141d0a0207000402071203850020303603010bd00e550391710380b0303095402c00040c140340484007008000c04d0200c00000c2c81d04490b50001d40c0000074862500340c00d80d0344004965800758030360050061050014000c0b034010110703e4140c2c42903030030921034808901400034081c4d0912100b9a21038003142ea60145440d21070b54280949801490141d02160840348200304510300d900740d43d00700144065400b90796804642007036541d540036804c4003440582526181d101d02c00d64540500342903103400c0c041d01e0b221507070b4403070320302c0c000d01c01d20000c81c8050784d03541c102043d120003d0400b0780c403554920a20304107a46d220590310501d0b44001c10b61001410b80b03180030861000b200e80c180c0340c8a04a4503009000c0e00c64031040b00c1e0324a503a100b280e110301100f0303c3c2d60080c7e2240b1929a005040c5209803130500500010034440e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 438951420 1250 438950170 438950189
    0x7050a1511030c030604110301140111030a090b0703030b0a14130c0e040903091503060e0901060303020316050c0d0c0603060b090f151c05070e09070801030b0c0f070506070801 77
    0xc22612181074102141e6011903540800303076072a91590b0028000b804a440d00c20f418000100000c1416040610010b40a003000d03258105200b420982c8656280b045c1240d0200051104404000300e034284009032044600c01c0c1170100d190020040400d40c41c00543c2e101142030980030300d0401240c01d01035100a4041107441c3c007440f500501110103412601281c000b01e008560f14403052040c544590b800e44080c041240309120480200e16000307015051501031144001d0740000410500f0f5014410b0030200c0b0f0707040d0007860515441c513014a5818556040c1035605024130000711556a489440c49221540304d4905c5072100e41c100f80d00102120340e01c0e045043c5042080100303d01d90740e540c421180c2c020008462402c1003900c9001d40103210701604203009440c0b904200b4a41b000300498220f203210300c00b943c0d5000c200c840010200100510180c0d81d050210f0310120042c000f00d00b21503601c6501c80d5400d0055482c100b4610030b4000260711060095503075800103010301c450654043c449500400c034200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 438952670 1250 438951420 438951431
    0x4150e01020c0f01090b0301080102130609030506040206070c0b12090d0e1f050405120a0308060d030c06110f070605010306050f091e010b040606081906120201110a0807050a15 77
    0x8002035a00e040c610811403040d001c0820380750f16607109044d044003800c2c01006460700d80d43c0d00c00b0039a001c0d42000498000000d080034001c61014880c040040450ba00b003001814261500d400b80403480d446000195529440c112001c20860003060003080c5004081910754050f180c40c5203010709261901042404002118800d071600c1d42e6980418640218003507860744035068001c17001c0d1054400c983c889500320a813014505105400401c0d01500c1368001d4a90442942d20b610800c15441c041d40742c000c021640c4440d00e200451b910354010201100320740c08840c946803a680011041781c005a82c2100d070035499900600401001c4c5c0038541d0000c1c00c0781d071000d030641000c1d1402900e5100d0404d92185038003000307910000207031094109841c8910302507c1000401c0e201c8000903c2c819085a2000300d104980c03100212103c0c3c9482141c08840b22003a001104246030341c011181d43e50302d542140b40c0f612420b10280046a1f290005114191155008012007406481c107100c1c845181800a4070302403510 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 438953920 1250 438952670 438952697
    0x615050109051507121e03140c07140709020c24060111120310030506090c01020d12090602190f030509060601080915040b01140f0f0d021201050a020415 67
    0xca030641c02c0d02c8007190100c000c01002100503000c0d001c0d0603405420180e201e2076414150b074008100b80074400f081560702c602440c1c0c3c0075050f81642d2428101c595030341c00600004150031012000303442010310400c4030503041c07803a00c03490340e281001b41d802c00440315a00081c4407602103000c1103001502c4a54a2040c032107501840400d421130300005100b24140140c10002100d00542403004d9941e411071030840586900702542002401207440c00700702c42e0382c85604041244608001070040c6008816070050100c84855001200e0b0700d41f501117403a00603038a034400900002c0c4540054054a101140b61018513401800e005046010740c111000c10301d8505030612142100c04102d080c0e2090b000e08102d15952102940145003a1031a100c110906448105220400c403c0d070407541d04139403020300c4040b0340710f000f5010040100c000640e4545c0c405480320301000e0700c3c140250280d605e50f000030400702041c60340c40d03039050941e4030456090b860b96038002414008140306458443c11070700030f4a0840c010340100c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 438955170 1250 438953920 438953927
    0x10b010207080309090606041208131d010b0a0504081207030338060705060a09020108090309010914030f0a061b03020c030a0c060f021b0d08040302070605070f0c030f06150501 77
    0x100c284c454050866800019550380351402190000d04003200040c6000b038060402c1a0550820391566500d001060000186a02d00380032541b8041415000012a41d2a11f002c14a52ba8440c0780b80d4803c1c05018800011800b406100110b40c5da1031000080c2e40e120300310301c1c0040c1160b850311030b14010310724401071485844050758109524010011f0b50445540f0102c03000070840d01410900074064420360042010400182e04103007080d500c02c1e02c810019848444400380c0b603000e03a000d401c2c00281e2100080000c40540c252544030080c0180507507403500881300703e6604000b01184240c881c10b4886000c40010080490910024000ca150860400e20b4015065440c0c0c454020f01e2000c202c80c0c4240102446059409007030203443d0b154085540d1041108c2c82484541110703205c040c01c1c000c15510030121802005240d110310350550240c110030b81003007010b80c2c4d03d80000e03005072915644404441e0020f940c0a100300e01450159424015070302c000c1c0741c03407011303501c5080031103180d829112410003042c2d81 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 438956420 1250 438955170 438955177
    0x1804060b0409081e0a02030307140d020d150905240f0a0806070e0d1e020a26010e0604050303070807050c2b110c0f0d080f07021005130302010c0302010f0c05040602010b0102070803 79
    0x80c58a42030b0801400000180028020a50100c0702f040c800125803600c01566403002486210001d452102d05940c1c070160400c5540c00c80310302d003030500e0400c18103106040614960b0000304004003a800e1350145c40f0003090324201e1b00d4011040d503910a10074801604d420180c0c210f00303040c0c12a07001c40e1102c440c0d511404010008000c0986958820702e045017155201041e090181c004c000040001900400d080303510a104400340c04041d500e8013843c0d81178948007047d01c502c581d40101c0110b04d5504c1c1d4000071513616800520043c10403a0600120319003076010700010324170056100745440c2c5020800d0081c10341800e01d00305101846440e2405059011012030600c07540b10781183c0f120b603040841c20104454106403880101040700c0002c0190703420b00c803071002d000140d00941c0ea2840003021701c0015902403181041c0d40740a5114000c0810056205607000001d0601c030744004030340c4001e001080030586d0140f21143c00070074404a0180165030703091190200b007000910040c81283e1401a4442d260321 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 438957670 1250 438956420 438956431
    0x1e0105130509030d0c0504050a0b0909040b09070b1303030305090a05060a0b2101020403061401080a020904081b060103020108070329060f0307020a0c141804060b0409081e0a020303 79
    0x81d00d810000d19404018802e07900d540242d6181841111034031903000708075900601602d4402c5040a00104101e101003003600d0300140c0141424846480c0d6486080da41c0000420307880440c03050003004111713000d6480290034840400d44041841b2400d601e80070302592801410b0801a034445c1984c54046800014081d40200c2049000200d03070200c00c01041e821941c05403110001c4541c040b4094011505600a004403806284c080011513030020b0038651820080c4204005580b01c0900d5801514002c4a1143c110780b1039000340d40342c0714040f4480e656140c0411030074000f9400440040095503000034010381d01c00f141d032908200d40c0b040703805154030f07400ca0b0241180f1428598a041d007540e8807840100c4a01500110000341c803480c28440003580c0304007940c02210243c10710600000e09404005010303503800b03401404026a0448000129510350b401001500e409440305480062a100d602c600c00e0043d0090100c11b90b204240482c45020846d48038100e0200b00081000b000700a038040b0540e138101c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 438958920 1250 438957670 438957709
    0x15110a0c02040e010e070e0f01050405040305070605090718020705010b04020f0a0c080408070314010c140a080403140301090e1504021804030225031209080d050c07090608061e0105 79
    0xc0f00004403550051a043e00052170b01d1081d248081500030400c00414441d003004031080c2c00710b03038035001800117030b83c01074030000c002c64018020303100001c149801031a808201d00040f100c5c03465940c0702c408183e8440c0d51400c0c6010341e0018940c0c0c1484000e0107111620341040c4c031705514080e9044404210740c460500c15400700844102c0020401c4140c10440e40102038032800c8601d215120300b04400c4004404050306265880c00100030107982c0103e01404c03a08040354902801c0402d9408151104580204100c1c10000c4001d078580003c004900554041c11841c400000c4040c00e81c14180d14180754409245035921581081100503642e002940200071212160544641c9551809918100c002c00c840f03401e40c40d2070b03040b0100074400d054545046034015841006014925003081c0c8202800d4080c03220960080f0074940402c034010320041507401d1a120480f007049641d0303011642140c803550810107803500142c052044d0300b20326019810009180300305500c0345d94901000604241000ca41510300d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 438960170 1250 438958920 438958931
    0x913020f060c0106031a061905060406050a0e030f060a150b03010b070f0503040801051b131e05030102070809240a1202041d0601090807060e060c0309060715110a0c0204 74
    0xd541c42134008400079903100d10480e0a1081800c40b0303031341030f94080b22403501540c40d95006000084203000820211840a04001c0c541410079a080b00c1641c02100d0040034003a0100c145142e80c0c134100401c00b032500350140030741003905000c6802d0099a6000c1e43e10441c0642000040c004001090101d80c1110317045007459903200031510b0a0380d15a240ca0401800500000c02e0000d505201034000301e10846040003020081e070005c081200c00d501801012000280c1000b009001030700c00501a410700c0c40ac0c0c1814541201d640f04000303400d990110000312400c400100c2c501d8800c0c200101c3e48401511401804241407040350008807485c00340300341701010800d074180f4007000d0615650403030b005044004102c41e6504036444d0783c0179126a01340d51982c0000e03036001000482071004240c0c0000c0e10300b103655a001e10441042040f855400034920504117010821400c00b9688e641402801b0291243d0f855106080c001d41098045030480710316403105410400c880d800003648205551271095049600046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 438961420 1250 438960170 438960187
    0x309020f06031b0705010b09010b070f020904030e300307080a0c08040b07050d08060103022104020a1508090d0914090a110d0e0601081b28060c020913020f06 69
    0x10080d800f40c081e465400b6000428400b44401074001c4520b1840660390b044241c0d0303031000007801920484201902c0908000c42480c01490306001843d00140203103802c8055000040000d101f0950450000c0d072000201003c1100c8003000d00d1a5991401c0c017040030b5401d000c280d441c1e145481c441e000100c4101310985990000300503042042c0d801420540803025101c0206140481d924686a0500b4011a2041d40014000e605c20b000f11240c006041901c18110f20b1400da01e80e50404d07001e04120307070000c81c00c070740487c0140c411281e110407810f450351101400d040030f40204d414041da01c8445000c01800c0d02c0c0a010b18400c4d00c0c5a0346513113009848030a1a561400e40813030003031581444e8120000000100e41d08508450307088461544071f017105480c0242d07aa9400e00ea0740320076088202c140461481141c83d00352030300e600c4426100c18035078000c4120004400d4080c0c4117041940000010410101101065061143e441d940c8418041501c1c1502501034000491001d424200c192040d040010005d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 438962670 1250 438961420 438961441
    0x7050a08030c040f090501031b0f05101103030a140f07020d0c0f02030f031309060e0a0905030c0a12110c010207090b0f030703152012070311030703090506070309020f0603 75
    0x1402806422a01131100c1e0b00d070b2848070060070003031105031074041000e00b0100580001904072000c66600e001402101443c0c8000c0c0103501e0744006140042c0001d0001044035001c00344000d602c1040d440d80000b601329412740d068002050b005e059105050004810440295000500100c859855050007100030207103192010282a0880000303400d0701070b41344c7c07407c4c43c0500040540b56520f49000446280c07a00e030805ca108503482480b4001241602d0804a0107100c101e5028500407070084040da03250011072000c40f417134280460740072a902c08a240300310561551019695841c5d0310504050054002c0e1100002d540c1c01240c05818004c2d5604e120780c00150303949070100301d010035028090300c86060356810141824a10100b40040e442d0400c48007101300400b07480744600c4d9803a40c1c104a030410403001170303180c4084130051490b01410b42e140f40822502d100d0001651081c404c503500404c1c1c2d0801c518029081100142c54001803504059184005a1311900c109414440a0311056140d5540e89840b4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 438963920 1250 438962670 438962677
    0x30613030509040b36060d03050403022407080304060c17063001150e01060f05070512040b07050705011d2404060f090501020705010e0402030411040c050702030c0607050a08030c 78
    0x10034454000c42c12080d000900507140500e243d02c0e0804030a410354505051010340c151f04400140003480401081c0010710f020000d0a01c0042109031105c28141070005104043d4072452007a980003c000c0f00b080104104d5000d002650003007803a03c4801201e42c405450382c41c16015180f248910200d40e00c609140c3e41342000d0205200c0e103c0c4810001030000101540284031405003426414407299012464880d4070680c0c41c121aa0342d0b842031000d03000034004552a402c240700480c0d46003d5520a2144010b00101810162454a00840d030720340651401030716000d5140e20082c10f024417000c5800311614883e4400d258140140c0f100c85210f40302440fa1003a2400190207034404c0c61002c07401042c12a4030202d41c80d1100c0082d1619203d4540741d20069030764184070310559000502c10718054400c0c0c1026005035410038458031301ca619103000d4200180a0301e055103481000517a01040803c15841c3c1048060007400099406902e4440244c40b81c54032a205140c0250002200001140e501e2203d07504a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 438965170 1250 438963920 438963949
    0x1333030e0111031018050c09060a140301061d0a0509010605180301110901021614010c0f0f03080610050c1c17040b010e060418030305060607020618030613030509040b 73
    0x4056807440c2c4a84180e0900313000c0d000321000d0403680b00f00b0703500c00e140c140320340303401990522040d5062010401c1000314035070200124000f04895403d090b0202e60071440a98080e10045e211203c0c0072075644030758020b09062a008903c1200300c1e076410002601e560114a054405a16080356a500c0c5089410080f8581003107403501580303440400251030b0b01c0d41004c0c00601100340d084c1d41006401c9860809041141c0c043c1070850f400e2a0070780003483d8007814000444502c100c2d02c4091002e0140c4501803010a8001c2c00da0206942e40e04000a80c944511502100c1c03145040003804c1c107108115055a5200c5400700700078160503894000201401907000ca44221034810202c01781d407600b0300d0007403c0b5034400e1060300d00c40a800c2d00420b00d1403820303010b800024040000b040c81c0c4c03234096450440180001070700080c1c012008005410158036408003d00c01607100581d044140d803410701c145494100003d00e01300d03d040b20701c1000d1002984c0901226411141150082055041070000402d081010320a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 438966420 1250 438965170 438965201
    0x10030221040b04050105060603150108040606272004031407050622060c0203060f10120515060d1a09010609020a0e0a0b0306150c0309061333030e01 65
    0x304010401c42c01640b0b0b105500c160001d00081c0c550106201e944d000644100c132411240d1030810003907521941d401d41e4001c0c0541c601041c616076960382c0d0b1807800b41022103900000303074010806100307010f82d002d511038048840698148100388441d85211074000c1d40801088154104488070454000704010406000700522072503031080300c1c45404120680685000c1d082038100c803000610309001d420342001c01a0007401500e00c0340e483d5050103003a03843c02070000359894900c2101099005a0412805903588503000801c04928000d54206d40900001c00f8a88240368081100000035a40400c18007a040c40d41d40328005515900703992030240503242c0001c2415840030403101455584800c00f0315501d10203a848a090380d03217800710004580700c01c54000360441c001d14805120405100700502c20200d4040a50b4100540d074000103005a0044240c20361188225406001201880c003c200d400b02415100069198001c0340c40b52542018003514400d04d50b0f07032000c20f85460300a40140155001c8800d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 438967670 1250 438966420 438966487
    0x60e01050c0a0b0112060e150402040525020a02210a02011815080f07030e0613050f030f0406090801050105010903031b0c0b0d0e03070c12170d06140609100302 70
    0x300059040c02000300b01ba5100c0382040211695501d0110b9165070445004807198030b5552039400384409064013802c5d40303001854110040b5250800c0680410a04500380e000c0c10031031103903004101188a51100c0d04102c110400300c1d00039585000181c013404290b0a00705042441788800e03011124001650000680070b80c04209007040720b911802e103074484d40c02c881441d40551103451048088070742d2107403817500310350040020541c45540303d914410080c0c401c104a884107041e00c4501e50868101220490002a000c10103024170340e0011078190107040721400800c401c1d850000028201201c601c0045c1c107204484c0d03144602c50034140410301d41560481105e680056489090044a0740481d00d620216450030320f0031f200002021007120300458000500c203201e10b00b8000400740d06030070b202007103415814142c1686180c1c101d0303c3c0034200c456100500040c4076841c04c1c0c41e41e0900700c01103130180c1c4100070400020890783d482603114034601c4064503005840d000e44988410b0414215a03189181c1c0c84003c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 438968920 1250 438967670 438967679
    0xf030d24290c0a020a060203090901050609040905070b070c080609150c09040203040c030203010e07030c0b0307170f0609100b0a030e0f03070b011508010e0103081602042c0304060e01050c0a0b01 85
    0x95980f84103403003a51010301003030751400100c3c4c40340075040a090784410200010011460801d010344100c1d80020000105050582d90b55841d0845a501c0b04501001c042800014009426001d0008051003400352440c1d16295088548680d041c4000300203151040c0013081ca101c1c070711026250303d954054030440da80e04150500302e012801c42c0c481280700c1e40c01c20301a2031000d9008641001101ea000c0b0601c1555030030300322040942e8000400800400400d2001491889011b9803054001c02644202d101141818002e201030101f000f07180170310082c20b540302002060031910849544028501d00000c408104860440c140000284044081d21000c112007090040000505040301e859021192041103045015101d0150074800d5484a03800000100003013180d04d40100403840d0801580514045242d00140c00c4481a0200e19545003940c0046104040ca405a0010801c074007001181071605e0044001d01208142ca40c940c104080420040c03481c05003080480c01e44c542c000034001456850307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 438970170 1250 438968920 438968923
    0xf040504140402120111040909050f01050c07060524091f15031505010f050d150b03220b0a0b0307090e0f0706031503020d0201110f030d24290c 63
    0x69a050784034402c0b000003240c410505215050540100d1b88003a8182490120504001c00442e801540c007401065501e0139214428400ea170722450415010540712015810484100d400051001540300c41f03125842e4000d900048180c0e06592048489207005d50798080c140040c418525000460350342e8152001c184d4818980241f4148940c558082206c0c048030299454007000d14410f05001c02c0040301c0c041c2c2c51501c541c008100c942107800000c68007001c1c507400031811000c00d5012100c803e80210602551451803203c1030b80607410408515071800c09601c414290320005812903054968801c1140d110303031810302c080002051045030820140d2080c400c07040d110095881c0b4400103000300c0074003181050191085411013585956200d1019045900340004a4141081a13040c0302d1a100702070f003156010880c8415070306184003c0e50700e4028402c0e02c00d0540b811711061150000c5000000c0394120085601002141d943c1400c11000004032a90310021030f0050b044a1f800d9000001c0c00101500d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 438971420 1250 438970170 438970211
    0x90902090d0f051b04060e04030c08041211040c030221060d05100e1531051014060a0e0a11070b070918090803060d060b0604030516080613080f040504 66
    0x413180b07001d80184030490200011078500c0c0c0240c2c5440c00c8440003040109210384001c0d06450300c01c644040ca400d0305c80b0300c0c00320b1001c0b03015812258a40c03800054101e030304140c010740c0c140d1245400c00350704001840c0700b50310f94406069810300b64240d481001419503900c0d0f0388004045034000b401c2d128420074000ca404040c00308000200386d503104680c8903226126005041620660009206080420b03c500c0070f5000300100280070381d0450705020105000c52024002d141031614606000031720710018010710208400c00400141c80741d40a6001048400e408041c013a5021503440d40c0042d0101c503140d04006a8090601c010300340b0b040c40c40410012507040006841502c1860300e0350580702020384106403d4410100c0c00400b00c8000f8404079566003081f07030f0f0040500344910300105001c524a030202d400d0307811a900c150b0320b82e07000d0302e60710110038088060900900001009400b052404246644620001c420003c3c030240d000141141015400e2040d04d0207004020004c2c40818102050f8400b0843e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 438972670 1250 438971420 438971443
    0xe07090204121101020616050306011e0f020105060114040501051c090b0915100302120c0619030b0f0114071110120b0f01080727120c060807090902090d0f05 69
    0x204007103c0e03104950b00001d0001e100d1603da0401c0720300e6005803c0211826040a0401c80c180800c0c0c200600000c14801d203100300700302403030761004e02d0829070441c02030075524050403c6050080444007112880c60200403501961020708000e07136036a0b9a20b6540c08100d80c41181007115501d002c22032010020420b03c81401900c420048420a5000d2094460880c0080d20500d0030f020a418080005040101607611080001401c0d030b0300c1e0810380c0b00482c4040d40310700070b410000c0c01d203100c1000e01a501441b800d4184c10040d5101300702c0c02d99100002c1c08542c030200c03101d5030080000c221b02040005491000c12104405800050400f00481010382115040d40010001900302054542c403401d000040e03440b282016950003c0d5600c49060503102500c1c91303060b82c1180000c0036404000e142d910065000200b07109107982100b610305051400e40007040382c00200400c14200c05000040758007a03c8401a1880e40e400141c3d43c24103840010400100e85000500005116400c42e05111001c40c1c0740381d046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 438973920 1250 438972670 438972683
    0x1b030609050f0d17040218040b060a0b030c030f09070b120f130f03030209120712120215011a09030d0306030311010e480406090b030c040e0709020412 66
    0x1041032404981c9814804180c0c00000b0503583d180c0107071421100340250051b00140101e40c0d58080a030307001010410413a03050711201861020b22032b0b0340c02c2101c400700060014174405802c60901103900c070b450388030191030381e1005605280070861f044404d0105a000303003c01c140481c1c7d207c024002e45100c5d1501140c8000800012000148000d92603c01889100360300c5000b95070084540da4043c0e000f508200905c1340c200800b9202d40c2100e2000300a042e000d80440320f114041001e075440d140344810b102140780710854101c095195040c180341441d0b141582d40ca403250705004010012165154050b500135154140700d42101d110744141c0662207407041c2c81c003d5036a500001000782d4030030b0030384801c1c52031030744250b0002400d90a04c82244e00b004c4108900e6a4001848071030710809030110351600e5100d0113210712000710303501d000d103011b00c500c80050544000034080000c10b400042e40303030b18a0711601405641c0711107494910303400030700045016252541c421034441e61100f02404a20480c21070458a2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 438975170 1250 438973920 438973933
    0xa080708060d0503120403021f0f0e010902030d03050411130c090501050a0203040306021c0204060203042c131b0f0f0e040809010507060e0616030f150b071b03060905 73
    0x42e0510710400c180386500400114038000c51550040c901280090080c1d0450141c0502c80060202e140b10340003034240c01c81404030309045000c421004031207407682c501001e41e160058480040c0c4005c20140602582410002100c0e0703034904111401401c0030300e01c96801f880209120301d8811088d8015900d00c051641c50846050710b800064840b8402d4011501c00350340141b20410006915030004c05a0001e0350762841801d4030003440e020280e070030a80007400940c1000c10140090b0107211001216903d00c0740c00180710580e500c100036181034001e07060902c3c81c103031f640c080001e0202c100305240340c4039101b0081c1303205103940708645900e084841c01212107032032040e000007606002c0140c2c220302903500200c03c20b1822034840019a1a40c0c0440c604131402916041d007550160401e100c5513204038000d22105e09200c000c0b200007011540814103500010340380c210000396803400072036003806443c0ca00705859910092810100715024411a0030142d103074668101104004407500703c511024400c1045511 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 438976420 1250 438975170 438975181
    0xc15060915080f2e1d030c280803090f06091c020a150506010908030f1b0303040309030312060e0c091801080604021012090b0105032a0d170a080708 65
    0x40303070000600b0a09048981100141003009807040350302c0d100107030000000d80c0c012055400c19400045c0300ca114030681000c1a11080200d0500c080346e8804d00c6001c0004050108a4000c440645c0900001c2d28000000c00001c0c05e90b001045640c05210104040b90310901d03110081c5a61001e0b195040c0a0b00081c40500c10b0750140001034141c20b031170b400301e030f5480c0100d8015458002001c2c000c210750f041102080b40020301140500c028094040341a101d181c0e10141800301301c60381002e41d4403404640c3e20410410002c02c0e40144184182c0f0750500c3c5c108902521195241c010384401d400c140440c1c1d00c040184084003581d08000c101d8800183c0c4c80300c000c03161152038080c005209101c3c0000580040000a0052900382c40947d00101c190418a01040c05c0c1284901204c5409400303d451001940040c001c52504014001c1c080040080781c0449049130081c0300d0b20401d1264800703001e0302016800000300300c1c4d120541d2022140381100f01da04c4009540000f42000410b4960f40007144c80040801d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 438977670 1250 438976420 438976423
    0x6080102071110090e010611120c1f0f110702130204032102012018030303060105070201050c01060b0c060a060f03080f0c070902160c050406060c15060915080f 70
    0x5101c240c1003040034000e59044414040e0301004000f0f80c404008502034085148400765401e03d0107486283d5603507040d075444a00807498461001900401004107000b040c40c4641d00044207207085038042140414030720307403003c11009044108180c41d030440c01c10f46001112203460010f4448640200e07441262424040204000c0344101e01022f06400000d0100d00204014003080b00802202d40c80005000900840c040c038042c20521500e00c04194001041325400c040503180070501d0303900314065032950405200103007441c410300300f00a050100209150550348000c6d4004402004400100d0380e41d1600300d041103407916030032503c0d002e20f00e00e040f00105066400b984030f6030036030784c5c031050440c03400b0720b80c030700c0f040a68100e084100301a1013001c0c804a200000c5001516500300601110880480c81e883d01c040305e040c4a810143c090707840c2c11801c210316640304e00207a580c00c1e0880311100d078101001d40e221020701301c19001603009a0a11044860150580010001715641c0b0803d44010170008503289 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 438978920 1250 438977670 438977677
    0xf0212030f1305031303060501080f070e1501090e09011d0a020a0504020c03090a06120c021f020a0c0803010311090f070e0103051008070902070506070c0c1802090909010b030106080102 81
    0x106a2601a07100050780c141c40d00074641c070058000c1045074140041c03041340e01300e81c072181e170400c680a0351110010450101c01300103490f150000007000c0c20340c8500b451546014000002d01001c190300b01c0c0f0540703600e140d00804101001d01499030f82d43e441c03413800310100c0d40a412810310060041038818245040102c0103d1010702c01a8000d2190310441d203404200710103508404c1e1041d0303450204204c60895039658050900040040751240c0e0041e140030150360003141e40c0841ea00084d904144401c0e44d030300c00b013200d113044105000d100041e2107000080c000c071b4010205040040c12044008008800d00c00240c0106d441c0220441d070b42c40c8541c1d600c40910b4a00141951414045410454050f59a60183d040164000c83c07094880440c02c7c1d58107401072030820383da44094441d9a001400740b040c0501444659030002d201c1c1444107107a181a62410564001c5200341d00b40100ea4903003003c00c0600030340480307000c07000080c2030720414101040300703500034001d0034140c500c03a46c80c2c0440050001e1040c02507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 438980170 1250 438978920 438978931
    0xc1902030a17070e12010615090503120f040e130c050109081504080f0711040615080f040309090c0e1315050409050304171b0a03150b01110d0f021203 66
    0x7203003908007003081c50b803440c00030180001c02442601885015240c541a10080346000f44c6400868a00d25003015100120030320b14090082249500090100d51000186000c00001c0220101c0d61194030002c00142405541c122056000c044018456402410107100100a000e032451180066540c4010b40b40c01f5a40d04c180305058101090324081c0300c5c1031001e22507010b0b005d41521458400c0ca0b13000f40080d075000d0041117841c07407100d40b00c0c80c62505191280c0342c007908120740f801c10b01a600c50805004900c00074803051030510084001350030188107140740801441508801c0c0a0081264000341c282c883c0b010001e0300400c41001c103c0b0384200180500d0340f40101110140030890300b03250a0002400c4031400580307661004200000301c540026820807501c4103220040c0000051049166814507141602c0354803d0b5080360082c0040f400183d0100c0f021002d018000901074001c10040e1103494480690383d115004400401c28002e402c0050180030b200e01e0360a40da42c0122142c070000450105984 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 438981420 1250 438980170 438980177
    0xf01060315060503090a0204061d13050a620f0a0c0b0c03040c08150c0313020306070207060219080d0209060409090614090109050c011b0b0c1902030a 66
    0x1c010b1a07000307000441e0404e903600300355040e002a54002c1815141e107035000c076259886100c02d000400740d40e560125004051071001c0102c0350460340b0380c00e5035401008409028000817031030820a80c10b06095105260b907020100e102d4801e4aa0300003003c461000819a127005d00034524042240d00080701040300c0140304c00924182a10045038440380d0b0054294030060240da01d0841002c0303000000064403034a03000014030341d00d00d45858070410701251135110216907805400b030041945132941c80035a0228481e485140c03a641c4001078a01c0c0200c1e5200c0194050040200340002207034082001c33025a262902101c14140a403c5403c9508a42170000341c000102030000000c88031058004008408000308881c0c109502d507050b060450703c4c0d0100c00c44400d503881400841c02c2c0b548941e00f542c0110210001c102c0480d198550980341d01e12501c1c560f041010903140d81000d0f100e19023004142030f402c11690142e0303162041850180d039105c0000d80c81003900c08403118244d14030000071141404039695 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 438982670 1250 438981420 438981461
    0x903080a11090d0b07021e070501180b0703030209210a0201020d0f0c061119020106050102060f040308150604090e0c1906050a030203130f030c02010e150a0e0301180302060f010603 79
    0x4135400b0100b18058561011402100e2840100314070301a81104102e041201078078085141c040050a0048007000242e00410b00a4082005144e03c0054900c41501401c0c05680e81c0c3c0ca460000b4811010381d000c1d000100b201d000c490310940d10000300084454401c0e0200d980c442c00240c0150741c03002e40503a0300d600084c070000f202000034110707030001d0940117490741c5014200b69040240c03480881800c460440140c1d5124070800c0290b03810000e4a80055403200e21040034242a24001c0211400030403044411078031484515460300c90f441160020500003d04010648030342412a07120080c10802620400141d6801180d464071150480200d5041da01c0b8149060b0259005401a4000030034100451300c90940d8003003c100031854800703250f4400d1341d03982c0d1365400a02c009050800000c29850003050b00c4481910141100422200b03100c1550405d034429402a000113409000014034075044210314100c4c2c0c604064000507198010854160090010780e212030b0120b0441e800d6514100c4000c8510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 438983920 1250 438982670 438982673
    0x6030105030d0e041d03270609100c0b0c090a05040501080c100905060f120f09370c030b0108010b1807020c0a0b030108070f030f03210903080a11090d 66
    0x90450081e6000c0144c800320700c01e01044281c0e03000d5007511980d03814903000001c48500328882d884100211402140100903480304e03130030100b000e500031461250301801c2e0960802030b47c0741c020b00414943c01d52007014400640b42c44021500190049141d1501890100601268a140074000c8034180d900500041850801c1041045091422280d040040c400c0d510303400300311600d4034801018488842c651003076880700340080c21149004c0013004021143c0c521030030701c011004045403060150103901284101d0a084005003010030203946030b007105584c0074500f030b40300b040800300d8104100c034050391190000b0707a0784030710346800d980d1a07615aa41c8081d8401c01c101c00f510015150907042000d86c4101d804174200c090201e85250b441d500b240700061000b1004010000007081010083e2505641c40d1003001e00c4e40e901c00a1007000628003d003031103001d442209000719440c1c100f22000714554020b1003d05000c0c1800340117080142d85030001d17541051200c8904030380d81c500305d03480b0407009010046140e401c4e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 438985170 1250 438983920 438983927
    0x5010312032304110a05010804030212030702070e090c01030e060144100c090617130c0303080103060c090806070c08091008010f080d0f050c0c0405041101030b06030105030d 76
    0xe20600802c2104070300c0342100c6440000d201603103ea031140c1010452052241c1c00c200403460507900440c100310b0301c2000c04c80041da0200f4411410070550880a4a81d110700e50140e08000c0660018900d200c84041001011800000d084440803400e81302000490352000c8100d0301c40000740904010440d4803000c0341c40c402c000203062800b011144030344120510361a420071890307900c021703480340265101845400030400d03903205006100380c0c3c81c104000130920309a00a06006981e08208040070350800010f04440b00003200d600c04140e1055a401c03080d0349a140152a06d00280816103500d854000f5101c100c0e802000410141da00d8040102101d50325041c013126103070f10070f50701140d4000c018442c14820381c5846240d00550302d103903221805a503040a028001c002ea003680036085a038048400c2804854100940d414601c02924202d5525106480681e01d4810644d004942051405042000703101400301c0760817050500b41d80611042002008124250200b8003856606030880101072045070301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 438986420 1250 438985170 438985181
    0xa080706060b070602031e281401030308042a03021306090e0d08131e0f0209041a060315061311030a0902010f0c0b0721240501030501031203 62
    0x41000d001c11502c1e10340e00b08400301c0d00080d5048851507004002e0010f00c120800800714030400e441959a65032903c003400d80031065000c50030070000c5c580f0541001001080c2e411198202035400500011540d40e8503005010040c2110141e602140f880c0e404031014170f500c2c0e0020054010882049806d40c01d507020019012089a08019025522040018425010300980b410b030700d00c05029050810844a001d484520010010351440d1494a08800020000400600800d61000000c0c400c0c07003d81c9003294071414000800303580001c1c0d0314100400c010f40b01003840c030900004a02040300b505c41509044d500c8004115482c01e030445075000420314106100c0700800c1880082c0042194090b00c00800560b500544840c902e09440b48103d40541d6080490300010418924295454060a4403800781a0700042e016400b0010954002030440a4078410410b10a8404d801000b603440008510000c85104882d034520b032045c007840020305503000340305a50480e0f8014902d1b0b807250001c060110010f25 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 438987670 1250 438986420 438986423
    0x509010f12050108071a030112060209010c1502070c06181502030d021801020105060109030c15050910110f160b07030504030803041a010b0703050a0809190b0f090d020a0807 76
    0x38142024241c0d690150040b039001301500c0024060701414240c8400f18131012115080e0402420001000000200744a10001c250000401a00c41004400403102d085020901601d460104602070240c2c01496000707000071482940003d004070340d5034006031103c802001c403141c20241010020012501565150200d404052055034602440900002d0480c0c11910480c05c008255841417003440d6024450645c00810034201218114a56520514050103500800c200c0362200040f80c0c052500400a4a0710250024488048034412010081456580b840f103c8220300c00c1107460b02d00c1c064007160b0750990201d082801003002c0d05028851400340d01c102803c0f0100242001700001103080030026500840c421100070f0070302c4442c00f40580d451101a0402c0c4925101000524006604002107a43c0602142042c200f10b9548443c004d003800300f00c1c070440203030003040c0011400f044001e0310064030a100b060a0300d0456101c0350600780d07640305800c00341c6001d079209612100200d02c516010346040e9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 438988920 1250 438987670 438987677
    0x20604060e0f1002490906060801151a181302122509060806040e1b030f010b01020a0b190f0509010b0316050d05011103010e091c0509010f 61
    0x20030400c81400c0c6031920a007410f04a00c0d078040358041c0042d41c41050030420584011340c403101d140110881582d50702084107131030140190010b41540c1070580307402148220b608802c0410280703503921f031501d0181580110b041d240700304402c00400c1c869003d001c1e400d041030108050a00341260710034a02400c0511180069100100c103040101d030300c4141c0001c00c40340c4680d102c0140d817070402c454041c0001084615142c904020603102041130355010760f11000f21005031034411401c0e00c644011800400449061201c076004400308078120342d9030400180184030b000d40c101d2b001a020511118204c4900028450040c2c020343d11050100b83d04282d01500010b009242c1070441c0d6400080301c3c210364901450001c81901d4000f0041c4050f0203104420078008184c000d040d40300c40e420001011140640100c51046021203040d5017807040951110106201c44140555a540c445481c00c5800b03104540c2100d0f0f41c420a140400b507242034502d03005413031901c0e48400d414840c186005680d01c0b9103080304c40040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 438990170 1250 438988920 438988933
    0x3020f0d0305160c030f0606050108090c1e0418052109031002070515040308040308060306040312020a05090303160209011d0a0902060d090f0302010f0608031b0313031505070c0201020604060e 84
    0xc68006c0004410191241380c0c00144240391030005071200c2c00051810510b500040100070440c0c03149070040904841d001d020b4640070014400140c0180280900991100700d4081c2243c10050300003011940840c2102c440e0814150f50044140e4610a210720f00350141c108860a6110306442d40117481c80034030550548035054141e003103103107160100f1142940010391003001d0000303040c1c101000c1c40e08030310241c0c040d02c45e501e03281c0c4024112100c12024146190341c002414018544540c068070f820980050030340340d640f40c182c01c1c07905070582c6044041c2d1065503030b140005403814907140119071401d50440c841c0900da40f000c807550001c1c242121f050360445004c02c0321000a564502c110400303284140c41010602105050080c00c43e0910840680c88603e043c50a0207684070000035500002403521440e8508e006082c0031506501034100e50240740441104040100070043d489a102d1203540e010401855860304d40480300e8180d540340190160f0400b40209001c0b80ca6270300421074a10036041203481 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 438991420 1250 438990170 438990173
    0x309030803090c1003050408030411060c030708090f011803060b0105071401020a020606012a080d1d102007020a0b0a030209030708010b03030307050d110a0903020f0d0305160c03 78
    0x280341d4412240491550000c11940d030251500004c1c2c00301d9049213240401c882d00d019070b1110309034440680b000d445201640800103051b07880b0f40444208503544070a580c0c6030202c0345070406640e08a1010b03144240105d4810010039403051400740300101a07143d1865040d46185c441200500c0c103004014100401000200c0c0454091486080b49201342400142d5500c9202070083c2000e00141401d8100211003043d9049030600139020704080b5213000031500c1c40d45c594500007001c2e1040030046510203040c442c04403024400002816442008041512a84403100b240d0700c00b101c070540d080c0e024083c081810011591080000781c120184064822904d0584410501d10160820f040200000f0380000d4503520504040c8400c0000786120b80090068100da9000291207010051080c410014081141075035000b042e0401c85180c01441c072010350f21981e80f01c0003410100503020a0f401504008010300fa07605010300500301c1d4075095070b501410001400500712039280d01582c141c88400e0110800300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 438992670 1250 438991420 438991433
    0x2070314131a090a0f08010507090302310e0a0203160605040b03071107031511070f02191d01090c0203191b060501170c0d15050a060e090a050c04060602030405040504030903 76
    0x1005070005c900c49044052a00301c880d07080d503c2c000e0559040084900e4108016195240004140c1503e050b0f444003030103e02c1000d490046049001480d400d09084200210803000b29101081c0c070300030b40035988000741400d0903c044098900c074803c000748040104000301d80c0c2000c05903400503041e140c200e015040d00c810b00d900d003c1e0a60010384a40f9646101d91007800900d200e4881c1c40b2540c10000380c01c000440d11030150110300b440c0080d001d0f4801e1100310b044140141108030203440f51030780d87c140c0e094120880c0214503000740216401039282000d80d011190001050b2520b501070306074140c0e1181e01886044a0240d8101c0b165011680c1001d40c00d00012030b00e00580d8080c2c612081240d203c2d0400741113091038a0035021405000e01e001e0001c101c00b0842d61014202c41600c108008101612004e00302401020310342d110080102540081c002e0740200898110140c4e8012000c0b40c1090441c08200002c60307027580309800259004100404c01e83c01c06420141d4880c0c0a800e2151070315980c0d85881 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 438993920 1250 438992670 438992689
    0xf060d02031c1b020a05060a030e100509011512020f120114040512130b22030602090406091a0d06020d09150c0504030b01090216120302070314131a09 66
    0x1400b0000c045441d5240d69404030901d42c80e02c500c08000e1500c50b84a4020650600d614083e06018010002e11032182e18000e402030710003100d0503802c44000c0d20b0799445a07001007105440c0710305254201692a130a05908950090650782020400c0319220300395420051104911201e2940180082040c1c3d114001d013845020189584200103038000c5c541440d0050600300135580b05030000c034043c041d00742000344503031225060b5401d0015540c3da80c080c4252003e0058841c450049000031040401300c20050150040c20410409580c00c0c031030365071606503000654000d511601d5144085071000c0c40c040c9400c00d80d609889000307130801450054a2942901039452082095822104c168810417208009100c0d1608030440e62401030b0900e4150b0760b55222105041c42100c2209801003940d00342605c0c10810b80060035480001c0034140345030044040d0207500240800e0740456003800e0004010a1018104e80b01510704118000c202400d105204851021f0800c14071303200d00d414080d440141d02d03180c110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 438995170 1250 438993920 438993943
    0xa0b1813020f060c1c0903121d0a080d120906090b01050112051003121701090509010f0605032d060703020310060309020a030209130c15030e030c03030f060d0203 71
    0x42540c00c60035801400b50001120003114043e00041007901020072002c03c141004140a440c42030f210071410f03000b22005c40064001030704400b002e201c0c400225801112907c5d1030800c6075415205011942c081151045041c030030042140c12001c0030410540c0310b114001e5210303048500c001140d003000c1e1070350b0044515408080b43c0c034400003001440b00390b03004209400f900d26480018041d0f07141103502e17800101407920000345403102d40c2588039205400b8528110344c032403144105030299130b500c45c00c9030060030381526003880a518050701c070610541035000d0300f02a50700190080124450301c010081c9024001500032021483d80140d158402e1028022640201e0301941c0150700d0f400c0c40c2d0740401c40d5140303540c800028503107031108500050300c50382070300d1045030340480e44180700d07640784c0f4448a0070b01108070004100c80e40415000c1545d441030030882c0d0707020b83d440c3da040141899a4040035038134032601f00d018a003507105100140c12110311900d400d600c5403000e025502425110f0b400b1920305400c1031007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 438996420 1250 438995170 438995191
    0x8160b0f01030b090703030e010e0604090c02010614040b0114130803030403020c131e11040b0f040305060f07090e070e21010c141c09080a050c0c0108040b0a0b18 71
    0x401c28070541c141400c0d006900c4c1e0000d485120703e1a60040e0003550b0034005c440c140301c0c2c100300d400e80950360541500c000704018002401b042000c1d260090003000300780111000f0a0b952010020103050030320881025400c1030319141c04420028070300b008140c00104400072448038022020645a500380061802a4407a8006005038901c020070402d0400c81000f90440042c0b4000d00316000c2e00070004140100081004001928000042ea1150902c92904060001040094001840360070000204100d82c01a407d0b00d1140c0c6a4048032070a100040d5a0a000680901c904ac00b0650800100b180c004800f420306d295148003100128040206000e41e085c0e5800300031030740703d00c500d40a0140400001207403414000d118007021841629005440070100407041400d4120080c40845d0300144200d40c000c0000f903250750304848014003c0c0d00a00d50b86203240600d5202c0722180d40245800d81c01298403104610096030b0342c040c81002031200c42c1e02070340d200c643c0c07404035a84401039100b654050702c1c0102 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 438997670 1250 438996420 438996451
    0x603030f091a160f02030d09080f0105100501140d0603230d05181203031015080112020103020c0115080606041103190e030d02040605031012030c08160b 67
    0x40c09025106a5405900d04840070040c18414124034021120014054051030003410464140301135140320f1007134001d40612407800f10300030340341d000701d00c101c2162000b004403055000c0200e207850984200361160000360405030300902c007a42c0950318804205100080341800d04070441c021900ba1481076006440609501c5c5080040f00304005030b44805d2101c0b44010085040d05070401015445152170f04108071400c440901d4251345e80704e03000c1800100c0007080366200e0400c0e0303205040115040c0709030500c100701d030951433031410300950243d8101d542a1190b60109a600d40054020f54001e07a0307140310300c1d56100a42180034004090803001761803000c004201600d04039090004a82190340d00d01025001401044440203015020f8bc006007018840170a40791070241c000c9240d800f8a0481444590001c81e01140195101c0040d511405c0310122010f0442e035140200da07403041b0960005000921202203110109840740014617038000804810441e81e0510b0f141c2420b4282c0a84800d88030301c2894 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 438998920 1250 438997670 438997697
    0x50d03121b03060b07031d131407031404170f0405041a01030e070506030c07030207170d08060f06031609090e06040506071806030c0e1309033e10060303 67
    0x140324000c094040c0b0407600c3e14003c4a620080c00c0010101c3e0b1047c50810515550f07551a103e440b8a414103450500083c080201881e81850707030395400302c5000d400249480c0500100c60805035141d40180c0c0c01500101001c4240a003c00040e13018141c44520110100720000f12a1510b102e5240c10031590310410004030f0340b510004003603c0c0d444601d00c1c03980d80000c10920042e9213850031243c00071122400700d582d0f40c4d06490180d0411025500c0b1316800c001311010306207a0300c8089032645480c4515526902c00c0e607110750030422020784114409800020510020304007203240e250341d01001c00941042001c0d41c4c0c1e1240b14038203948064a01d501e1075040b01d000d100400104000c0a9042541820139403000a8507002c1088102e0706403141130101a107581c1c210701c00c240524180c0368040401b40c00d000202030200c000740041c1843c00b00072070010790030a94080d80310f10742c0c550644003c660000521184c3c03865802034201c0343c1051200000d1801807000b0310203050040e00c075080044d40b10740c07102d000c1c03040c80c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 439000170 1250 438998920 438998927
    0x1060f03050c10180603020c0a0c1206050c0406050906130e010602071e12080a09030b0c0403021002010506010914120307240204030506010b030c0c0703030e042301050d03121b 77
    0x602540900303209101c4c102d42c1c906820421040f00741e45d0a0b2500589032110490600d140a5040e100508031042e42600070800c1070084c000781190b14001c840c203219607111008008154808c610544000413001e00510865160102c0142920594036044420082d02c414807004000303020f90180025920500080003021400c46407519400402c00c0c84030241440c0c0803007030a081e1807911008108140c00240c03121502c1c010b2541c20702940d04070500f00c8607403924600b04001c5a1150000380e10840c1c10416028840d841402124410300c012385d030b00242c0ca40b5143c1080d451020020609510400340d02c8403405050040002d860064020080725150903400140108640e607024042c9410600411007440810b400003550b40c1115000701141d0754965456494905e940907801902c40c59001d8503100200f070640c0306050303010300319080328100545030403414455008000507916082c050f050070010841441c08140c500c5469020341000c0c9910721651521804807801404500c2d1500020010656015032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 439001420 1250 439000170 439000189
    0x602240c0306090c390604021320070804062a140c09130b182d0d09080d2609030906040e0403020706080708340819020f0a0c020301060f03050c 63
    0x16172005080c2500306a000f2501001000d0059402e440d01c580801d102d1070310340b195500200c00c01841142e21203401c0d1422336000d900502c507400010340800c2810000442c0c0fa00305290ba4911103542d5103000d482035440e0011983d10813260000b901035542c1404c01c540307507a2401b510800c0010000d8510510600c0c0002d0803e1029104490b0407494142d59501007070001900c04414686440b11680086054503200224130304000402c141d000f40c440c0000516048442e9000383e99141007582c0c5110b00c102000c03101e03413140003a2901c200c0c01c8a9050341c40c1c0416031618030740107841a42502d00e0500100049a07103540290f2015150110420420040c16030511090020342000c2c41c080b6020f003881200202160000b6003034030644002d0310a668901c1804000c0d02110507d4002401994048600c001d0800c0200b1100e40c14403080040145c1e01300e00c1a40300300c2d20b541800c0c02506003003004455044602c146926400c03a090345d41c481c0d003c56805204886100218030a0000b0310501c40f00d4000d0240f12038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 439002670 1250 439001420 439001527
    0x20a08061201090803130c150807091a090607060204090603151a01090e070e030d020c131413031106010306020403060c020d0f0c1a010602240c0306090c 67
    0x9143c10441c500003201941104d81004003007603c50549507030b07400c0c0710922507d580e005088444c1d102580d10b010a4100900314483e0310b0300c0d141e10000d20f59440401144440900043c201001e04000304181468a080680301d03d5000703c00050403d44c0b200760b444201ea400703800942e200e0980c44e4020011b05098003504041840504100140e408500d0001c1c1c9440214081c0560b021070410000b0107807480f80c0010a2840402400c5840401c210b0700e02a4a55a480a02c80d0144040d904030031a0401c0a0143d06903001070514500c0c05aa0ba28404407000b41206500b2000c1250405071601c80c0101000034a010718021b0744c0040c2d8071403a40c50504201c606d80702d58101990043c0356401c0007036401010f03400f560981c90074004050400c9107031009443e0203a0f421460100100390001c07603802d034006207610042c80503485201e004520b9080da410001d008442d903401346a03040000803a1030400b00902e6800034100f131410b6003454082855035414a60f40b01003ca2103144008112031403081c100c2c95801c029 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 439003920 1250 439002670 439002673
    0x606020f1b090105060c01180602130f0305060a0507050c0d031e05060d02121002030a0603020306060a082104030812040b0105100804080a020c0a14130b0d060915020a080612 76
    0x2803209000710715110014131440f8828440400e00001c0e081003900f0507504030480d6900900f007107283c1e1078500025080000082010400d000780481d4140032001307100103890700800241202d030ba9804050010342401040c01f4100b000030f002584114404000001c0c6074109a03d000c03034510075000588407000303004201917001500341014000c6a072a2001130845898040d946070882802d0401811314011b240084c01d03a940c0c0c400802c100345000180d00a109691084040d181d50342c840900b00420013085008c0c00100d600918054107090543d407030f02c44584103d01c41410f0600b9542d8030351107a1908142452000b403031074501040100013441c19040e0160208a07051409410860001400c041d4024001040c400e80040c140c40e1141c02001045c90032403000f04280035040d00c0f00d10201c180c04900c0ca176280035003002c84d811a803d6515020780c2d914808007601d00641350b61140c5508014200300d08050700c2080400b00310500310081030000b4086110b1984442c41e4505228040c80340701d200c0e103204241075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 439005170 1250 439003920 439003963
    0x5060409080706050604020906070b040215090a090c0c0212030a0905040e210c0303191415060304062405030705040c020a0f08090a06110609060610050a0e040606020f 73
    0x18503070410749901d15089640003815039141e40105000348201086a9808207010034881c04101d06a501588224801c0c0c540000c841c000d09014019405800503280c0e000d1480b40c0b0511148000b076208941c581e40620f840710f2071041580220310820a49001c03190760342c20000f41c0340213050300200c00da0010401503030100402d00d41201816101d10105099800108060b07001540c42a450020380d01013035003503025a03540381007021504625090000307400321007908021031070038200440b0a04602c643c18003091400c0400e81002008119880148110703170641ccc3d600600784103c0044428110340050f00c400302170105082c1030403d0f24041c420340c40301d48554184200304c26402e9010605101680d4000d200344500b09103407500c43d6060080008081d0441d0038071038001a8194440d0b1a981b400040e4029200f958458420981d11142c080792203581207862042d000002602c43d07401001c0c40482d515000088583c4800040c043d941d19a000c0c00040c0d200c1402c081e02c504080c0500b8041c01c4248604825 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 439006420 1250 439005170 439005173
    0x9060a05060d150f081c030203040b131407091d030c030d09020105041d01031103031305060c030d110304030f0f0f03020901050702062b0207080d0e07050a170105060409 74
    0x2642d10807150304103182911010b600300c0c204a440504000342c6105a07030100c0c0c094841e4151a640c1e03201104d0540344481819584c2c912030700910841e0301894000b2648001640c844a2221009155200c1152005224450784089001c1032040340f01804129078085842c4034596a050011201280100740580080096881c0d002000040b2540c0740080c5901050030b12480c0010780340c80c080e60303000d5118080b0480e10740150381010b481d498162845140c90409a0b10b441e0181130b81d034080c0404650640003809000c1c4914a0720b10040c0400420013400c0320700d4080c0c421a1321040c0c45c0980030f01c01c1c0a07070010050204160f0130403031100d582d02e8903180625501e01004c2009100740b0300346040d9401d15600099007006a403241c0704940c02650040d1840b83d5036401c1c601e00c2096200150400207190700c540f5000e0f441a07005008640040f07420090032820300610ba180500200012140800c0c140300f9950000307040e44600c1c80000090980961030240f1080450b400c50a4860080800d442a0b140c02039100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 439007670 1250 439006420 439006429
    0x71119081209010c0b0615030702010507141c1e0f0203090d080708040b06030709110d0c08060a031506030c0602030a0809071d18031318380d08070209060a05 69
    0x8101a081090701c481d94480002240242480b03501c40761f00218008100f08965030150490b90040405a854040c0403110680d800344601074100440003040d00c0c250075400380c040b981c000c1803224000016490390070700c00c3c0312450f0442c1c04215521940e181c020041048400d0140901241c608035800c003d940c0303180c0390400030880100144020826003030080030520b1a2401c11092003c1d00c04a4020004d40c05030b040b440909802505049413070034209000040901c1c41528424041e5a01808801409082d0354685410140060420501c00d503a000000041101001d22100030710064002d5503840032040801000580020600b907401c2c0d200308810010200003843d820810074010013904296103a0344800c410381e001d50b24403540d01d03100108940d01c6960030540c1c100304460131048001c026441c464080ca040d510210381840503001d8405025510303141e01e445045c40500b580b00d15003041020a00003402c9051004019900000040340c41411410014516604140c0071515481d81915110014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 439008920 1250 439007670 439007687
    0x160e03010f200723010b060406170a09120f030915050106080108060906130218160207171c0c05030d05010e0106020105060d080901020a0b240604030f0807111908120901 74
    0x21000c1341c0300d0007004c07010301c2e00707500a201102008141d40e96441d07aa01004080d025020b051003812a20040852001125841181c00c4154000e5406041c6441200d0a40d03408003c00003d40a1540342d0340950300040d0f2161005071440c0c0d03010000510340d414510300800004050f04400107591140c4103103c07100343c002070040e500c1030015804038800049440030408180710380207410842076000c414080f1105900c1002c0318090055400c0302c449581d103000300640d004c100c1505e4170542d0400c0c40309418204102c1d102d0781499440e41002c0068400c150f642a1546d80f1100c14040c80503a2003005101c2144004100e60040180344000c3c0010b051034000580005030120b80100303044400265040d0b164001e02140c1003203074000c44100452320304a04440080101d55100e4a20702c010008400381d50b00c0c041c0c1c10b680a0301e8010b803055140c00350942d078400d5158000c4c5000d80e04900303441d0384094580d590b443e001100205050400d035041d85020445ca19140c10b0841d0300b014910240403680540e640404503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 439010170 1250 439008920 439008953
    0xa0905121c0306030f030e03060a02120c0f1e27100c02192d0b030424090327050609220c170603060f160e03010f2007 52
    0x8038012401c10303078016002403c1a0b0700061030303600b1340c0c4505018036801c80c240c1c25903a01e00b50199105590b40f5040c410481c8186101c141c20b0761034050208507101d86502c0605000205c2e08240d03480d242000300e0b01d0a2004070095180050a000209201c2d0a00ca1a103801c214010300307180209500d00c000c0004001f646696180c008012181c88030b4001e41d91025025000302c440001e0045c4020b403504000304a4281e0301c007014a8041c170003101c0310450b000c14082e541c21a108a600d5034156207880d0355010a401041d40c080f04805240480c80341145410710810181d50701c2501c95003214070940c000205e844818000c0d8001a03003052000b04099241e02c001c23140b50305003c80700c42d841075462110311103154030010420034889241c40104001c00b60071000c90324001800c0d2150001070340d0340c2c104240c1c0c4e0f52404c5030b41015202c500b00c0810510820070000340d0400001d800c0c0440c40640c0c0720b02090845071410b01c00c40403662100b44819020540c403900e640c1c9941e03076003c19031420741e098951020f404103420300d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 439011420 1250 439010170 439010203
    0x6180317011d1504050a0609050c090114070f05120304031205010612090c080318090901020406020a030804050f100203011403030301051c020604030602040e04030806030a020306070e0a0b040b0a090512 88
    0xd42d07808012100803d0b1403070010010010350a19800705801030415000305180e00349080c000c40d4055407100242c0713440020580d01c0e503402c00000b9110b41d003650400130b011514000700714074503000220f06120283c40d090444058949900e800e04004020918a00a00780c03194903160050090507480310860f1007002a1002c0495580a40d00d09681202c0c00e661040540307000119105520001c6a1200340e2451401c940704226030322609a06030807441103102e0400564449144c00001a025007066a40310380624150703514010a440c4940c20b01c5035510101c2c10480c0d00000500654dd21045106019203081c0e00a40c00d542c10080031a454050713080e80025000401044c2c24110340d5044103e6001c0c1d58011019915659a04070b56006584203a50403800305620f1000a625402c0002d89490400c1d0000d00400003900c80321019600c10310003880303d58100300d0020000c1a00c1010400501c005c1c000c1502e015680da00d1800c0007024a4038a40085204508011a85072040c2000034a80c180840751707203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 439012670 1250 439011420 439011479
    0x3110c0c09100f080309180906371407030911091512031801050f18041b02070e0711030a0302030601030615020f07050f0a03110303070618031701 64
    0x108042030716801c0d0f200c41d0142d0314100300400c0c902c0e0003001a105190094800c450304c041d146403001c030500400c5900030219485840003484010b406c03c01d603010024003036800386d80310200300d102c08084400180440310040d1212180c0d42d00c0b10480d140d566000c1c3d00c0d85401c10544400d0f58031400079060b1501c4013807041c8004408640401d034488404011102d0041102c914105403402094503500210320301c2802d0301c03c24401360195401748044841c980c1e00143c0892405400031240462058001e20060b00b2554480c003000c4d03102c120380402040d200d8141c00609240b403400300301c0d04641d24010b141e0340800081b0329081122a0001013a10010f1429050150f225903491004070020a40b40c0c9c048044c100c15038810700c3e1019004114420341c0e85001e800da80c034071600e403402d01c0045646108000c0d080502d0500400102d000c031442c08400d070348024192494124a07840746402e4441269540b6640d40004981c5030030590095201d0000e0102d086001c0e41c1c3d98900b90043c1d00c118081124081c1e079035030b100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 439013920 1250 439012670 439012681
    0xa0b06130e0d0f031401060f1106011d0a06060503040b090a02060f1b06010b090f220b011205060306010515070512190302070b011e2403110c0c09 64
    0x11050a040c600050200101a410039099541c0c0a03801c41010116012010707020080e4400d0159a0f00c96440f028000c105034a801c01c00c54141e00c0c80789050040100c5043d60403101002444080e00805190104101000c3d0506181030b02540141544070290b02e0000200700d5541c004041d079074040e420004641990780c1c3e40c42c0c001c0c00d00c42081d0009610800000355026800b4a000c0036041b03100c0400010403030100c062007500d50700ea00a000f02da0410b44180804460791400c13118103002500d000d401040314000d442900754140448200c10352461351502c0c0c0203119561300c0700940381070b901065402c1c0302c1d0b801e01c100840c0e2203000600856000c1d080031a0510080032a04084403d195409011100449215444280070740c00207400d4420350a200000c010310303140310380243c40350140c0000414000e6482c0a2883d00701403440741e000002c00c0415000010410210118504481c004d11458016a2007400c001411506903690360320508105020a1411800004101c0d801460a4071444a5038495 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 439015170 1250 439013920 439013929
    0x16207060507080c060103200103090c05040515060c0c03010506010810090b0103110d0504020103110403030504090213080f01060503010b090121020f030a051e0d02340b0714030a020a0b06 82
    0xc550b509901c61040317000000410003c894850030080c0b03400004d040035441c050044007170b20740c2000302030030240c0a00411b000c04e1610340d00c101c1d00558015031007800700d0114000f01e00c0d1900140324240c40303500300480700d1699040a00549611079002d203840156898400c0115254000900450100968949200d00180d000346d00a0001101140d4815140c011401c401000742c0001c8400301c1c0041c5c1084a1f00d8686000c2105440030349a251300d0b92403d040c2019854402500004c0e1050042640e88000240c22401408840700c01c800100010940c642032105250039100036219060140079608010001d0502128090180c2401c0308281030009249000080741c00f8113003404103a241c001d222100d4100640011320240c0402c8a1594403d0540e100c001103072606d402c0044240980c001c03034100380b140410b00d072410001003507400b481c800c0c0310200700011039285000e80004103844000500f130b8050051030b01d24070800d1040e6000861415140100081d00c8000d84d41e001480c0244050200c1ca09944 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 439016420 1250 439015170 439015177
    0x1240920130b03040b090f060c0909100f080303011a041412011424040911011112030406020a020105180c04201306140a0801620706050708 61
    0x4500a00390f4580c10203007000700c82d1890030f881400c02445881c0d0b11681035500866454850705c0690801810642080c06015a5007401450000b407408000f0002c43c8502040f1072060151503000021612981480b8402400c04498440d00c107101c42c0034001000300051507842303102c404000b40c840070700c1c00a50094250260007100305480060007504d041042016484606405480e0110541c0100c2104d50083c402180c42c0050050400c0741c503c528a4003070350080f602c81c19034907040e1045955540c050321f40035025801c00e507800c8132191380004a1448480e4240103c40d000b05488851000ca0321003074016560751005002943d0160391100013000c1c0e03102244c0300d110100380255100c15503d0074043e01010082c00180920804110241c0c100e2070b1501007001030b18107030170650310b8001c016400d08000c0b011080014007036a2180780c1881801d0502c5d500d8101602405d8181c0106060704000049400c03021040c01a13100130098904150541c0d0600c0000c400080b9240b42c10010303a280c6050500010510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 439017670 1250 439016420 439016429
    0x521041a1204060e01060906050901050f0a03120309121110051003050f0a020312040b0406031a03031216020a05030909040507050d0b150d0b04060b01030e0124092013 73
    0x49050401043c0070960b081080000d0380d2400800030641c0380c09902003100c005004690300420342200600590600b00b484040301c94008002044080d0307a03039a404000c0719502d000400094541c0210403c1003a10811515820ba030303400d107540000800781c00b49641d45859813034199259110000b050164102188180155400c0b1094515044aa01019560785d0180754201e00910030060340c0344070501810150750980e011050014502868000102d010340340845407500040d0790210700e4101e680d010802481c00740300310600c0c984149888071485000c640503140c005c05540003800c0500c00144040101d0719101c0040361005a02d49070350426030b03c0c0c803103035821241d0060b9107100c00001f03112420740380e18850b00e02a400c00390840d080b001403100040448100408003444e000214000401980050003140c00624001480c003e40d550300707a080d100c081507200c10394030071040d0140c00b0151980061010b85240081403100003181c055204030660140741b960540540403139102c5480c01c1c80c4101078010b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 439018920 1250 439017670 439017697
    0x9020a082e0906080d08130b0c1215011d01020a060e0f03120906061e0f040b040f0609050c07020d08030712020a080a14150d0c0e0c03040521041a 64
    0x50700d40018100a10340341c000c062a40c845c0140b4000c00901c41c044441c490b161207441d00c095061181c0d50703d5035a05e005451040242414000c00d926450031451b09881001001d10008000c0503520024000000034006100010f040021000c80b90f60002211020305510940000e00c03a00d81c0901d55040031814510a40f0900001401516031265503218074001c4c9404016140c058440004104008400c031100c0801e40050800428180c9003c44403039204120240c00426020050b10002d81103900000c0682405640d9030030a00260a603841410351000345c3c9036119180000580016103003c0d041c0c80003c0072020000000b0301680e10821030798842202d0003c00399104d642603174004d040f614ac219010000c862030000c08000766059855640e0040001d50b54a11383c9400480900c4254142208240e031b00405110b4000b0b40584006466486043c44c6503030680c03a0b007880c1c50503a0501900182400c5041d80444a4150303a54009003150211903020b14565902020700103070404501913a007024961 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 439020170 1250 439018920 439019011
    0x405010501150203040518071115070e01030e0c090403051b01051602151501020304030c0e1f14010f0e1008071211090d082502090109020a08 62
    0x4004054000350305a035035122981c02d01c40c152000403a0380703009134800ca41d4060241e082510614001c5082507810818a01c6d2045041c2124400c2c0c0d440c1c1111801078000c200185c0e01004071099003c044048489024a1b00340080306185110342e039980703001015240b04106a401140425000f80e0032209a601c4040d69400034540009540e4000c1c20700312451510088814020290544041003602801929240d05080d54850694205403030300450141d6040d44020040030011400404100004040c41484c0310030703e14250104510b078a20221785011000040f81c01401842e500310034880a0b01406c1ca00341c05501410035017240c0c14020084c0c1c07250088410013000c0c61155100d2101d0703220300e103a5120030448034082d6030024101d40d411029102007a405000026281c94204100c107529401280e41230305010b4501d104803007200d10080340380046913003100200c0071800d2401c2800c2c01000d501d181182014442031009d0544040246680c1c200303690903082c5809030090722502c142c00e0707404032a02d021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 439021420 1250 439020170 439020173
    0x7030c081317150a050717041506080c10090b0406080703022502090f01080706080a09050f033a090f150e01050f010b090607050c0402030c07060b040c1e03020403080304 74
    0x1118880849480f04a4a2180001d01a56140d000785409040c040e5510321446403500454400d002c40908111940440c2c604200040350a070b0140f40d006c1c0ca07900015000c18600b40d402c0000b030381100c6c00140140304951804100025840040d43c0869080e41080a01c0360340e400c804070000d12881403098240c1030301c41c49115510030002000440300e4030907241000c141d03c5d20268040c0c00c480c24440c1c001e03580d01140052161912400c812504071190600100c2c0c40c801a40d80c00341007012028007001c850b40081510032000030b0388080c04804202c0807001c000d0017061103400500004880c0b0806100d1500d92040f1000c120011844c00840358001c4816403040d1a0018807001030404040c2d40c04540d8289804203134030442100728207040352800c05c07101c1d2620481d00c0510605801c45602950300e4041d0405e148445d841d5400214442c409141070565602c02c1450000d0072500291003060240d468900545e84c1c0c030b03030800c00ca0103081302108a101c06560305c0d450110044c0c0b1444d000141b154401200303010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 439022670 1250 439021420 439021423
    0x506040306140a0e0613020315011202031005040803071d030615040b1e010323011401030509030a08061c020612010305061614031005180f07030207030c081317 70
    0x2105242c96488010540340c814808003915405118010160804404113681c101840c14900c1301c40d20140507510034900900e100c841d440002d9100e4000024180c58840c2145000e01c0700740d0210240c00c0c02081035040544440d84a0f02004208509101c403000804802d003103601c0c410620300400804449581c0f0380126203001c80300240d4442c5000700d04040903042d0500c1c0c006204000c030a002d850300303a041803020004502400300042c0d903036001c1702da03003010a02c1d90303d80002c0103000e0040c0000a550b4070190070001400c440f001840b410081e003081c42000d10113644200041c1d08001e0494500743c40c5050690184446130841b00300035840b400001310701c0045400d01030790038101c0b4020400c0d1907003903503643c880d04821203d01480e04005044046804486150311003c0c640242c2c1e070200000c0c0e00e58442001c1125140e448000914400c800410069166960560161f000800e480c0540c284416076038054509102007400404464000c0f4400003003103040242c142c020041c480d8440f040703009116446 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 439023920 1250 439022670 439022681
    0x61206090c030f03040b0d020306011806050a021212070f11151e06060706020315040203040f060b040608030d021b070609140103020a0c110409170c1504020d0314040506040306 77
    0xc0d0083c0a082444003100d480032090310215968a402e80746424400039012000754002410b1905008047c1720480320307401c1d1000d140029190903104d9560f125807000d40a0b142401d69549101103410400568115021b0b0030041038024016040102d11001e1552055680c100d0408514845e849202e20550911b1f54501000f070069a850007244108030f41e49550050001e4212002608224100070039400a00c4c5640203691104c103150707410301324052810000307040c0d078001c3e0390544014918100c140e06000946c480c1c01d4000a0440d001c001043c5021540b648a00401d038402c2c4519a010402c40280c03070100824883c4800351a042e101810788502c0042c0800c501030062801c2041c5900c000001035020b0301c22034000b11072503180c0507508130099072030750000d80c9002129078006880b18081c0001500c400b0304840a140c003003039a20349441010104902d851014003020f001e8264010034803001d03813100190414481d030940750032406003182d400744070303005d1046901c0240c02000000e400028826290b02c076 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 439025170 1250 439023920 439023943
    0x80414010e0c1c03050a0c03020a0c0308071407030c0b21070c0302070f050303030a020a0c060f0501080c010206150108310c240509040902040207060f050c0c031206120609 75
    0x880d0341c214904090380f181422072440180410340812048620781d0007084101640c038400d1044500559582c1e940c4c270410f40607584104c1d8041400b044280400040107400215804240c0c010f1026a1071074440c16200ca0700c80c4035000106000007071010140d11901440581d03002925003034855814501d0004081481840007500140500d007404941200002c07041d804a8200600550a60300c1c0e070100000250310514140003800a219400710029046000d0750040d9071074908002409c4d85044150780c01c14591a800d18115081802080988a0145101082c0510a10300748080e50b4500c1e112083d0f41c40900c08000d80110304d4814050b241545200000b04a44180d005040e055550383c2e2140320000c002e80c47c80901d0002e007074042d0040b4410750152030500c100070008a1490b569030082001ca031b010300000e884141d1a089000f1144180780201034008215050030b80c504800e0804090b141d004054500302c003000181b0202c1c00c16540c034410350b03880030111801c3d01d000381000c1260650b24064100c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 439026420 1250 439025170 439025179
    0x10c1a01030b1312050d0e012405030309091504021308100f05040812071b14060702120f030703021e0d06060203191202160521090a06080414010e0c 65
    0x107031200100f12442110b07990090205900952690302640e140d088650764221159070b803aa0406e40e400309003d8580c424031a042085a00d05107007904422548642c5c0005010358800c00c00f2409a480e86580c55038051070150b4410686414000000d02902c500300801440c0c081e8813501240c1179202084e083c5501a645404210040c9a949210103485044134003500c0c11300180111002a0a016010390b4414070314502508a401905440f041c0420002810b031246540070040f0b8000341010003510b034111805000030814800803c2e440d60712485140d90418041002001041d40540290196400203c1c00070040d01d00038115040b12510350007032401c0484030ba04084c0005617180c00801214010400d4034a0414819041d1409603003041c1c80d0651030700708a070300308520200882c0080e50b00b48070b14483d002409859050031b0400101403002c2038042d41011040102c500c0c1d0ba40d81c410b4207000c490003810640c03c0c554490a0500107400740300086680c035420100c07034070440100481c0c1c504598030200e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 439027670 1250 439026420 439026443
    0x30703020a0308031f050d020904050106080f0a0615050d0807060e031b010f0903021e0a0b090a0510050705070b061908030307030c020a0f0314070611030a0501060507020a090b010c1a0103 82
    0x45c08040000451050941220000e400c0e500941400d800c41d03a4410300540022031050356880d043e234507003c44203880242940100305158208001c500a241040078044420164581468006040d03902050720003003082c44002804001c2142035048a641e00c0e03400015252075a91504074115480401c0c0300c0c140d280e510780802d2205d94901441074000d50b54066000f0815040e0614112580c03020403c480602c9104890941d00010340f004890b6109481f41000740c1030401c079514049261516406000494074180010415001d074000d05a5003080d03005a002d08454032110081803040c642c4581032540100b01d00404030311080000300860103030265607410080180c5218040762070f802c003004028141d92940d4580d80c04a07105d030000c0e0305a409440c0d00f0903d4001d10782d0301c0d00222405a00144ca201c01d002c4200811405140315507401404541411854000298009940181c09008600ca4a641c85901c00da45900c11a85000d10340e40c401d228000300090b4440c0b4059103d003d12049810b01082d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 439028776 1106 439027670 439027711
    0x3061a1306051602130f060e010e0c03190f1a03070e1f15020705010305060114070b0c0d0c08060f0a0308040b09010c151a0619030506030703020a030803 67
    0x15200048046c00160034000340d81c000d9000140000b25100100700114210302d001760700240b0104155904d03502d80715844c8021520203c4c8880341e924010032055000e120b5030060003940048108001c0c10000d007004c0541e105014061241b00d00c880c01e0100c0c241002c01c0d050941e0300d03500740c80707180120350304e03803082c0819030b417110981d0340050f07000e40f80400580d40c05124103074100c07a080c6482c440d02301006400310b019120782c80000342400c40440c000f42c4e03103008113400c3c0c03005800400f8090020f511840c0d402041580b05403900c81c402c200c440343e055800d01d002000c0c08201c9600c400c40900302343c03812105201076040350003000e05001c040540040003906685c6428441d10700031100044054444080320a1a03003850441401001700b0002011034030032074841181d03e42c81c1464085042d07910074012905012181d44000d410140010010040042810146119181c3c541a103410341040 = true := by decide +kernel

theorem cover : BRFrame.Cov 438848920 439028776 := by
  have h0 := BRFrame.cov_init 438848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 438848920 ≤ n) (h2 : n < 439028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
