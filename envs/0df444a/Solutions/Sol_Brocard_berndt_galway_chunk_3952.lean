-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3952
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:08:55.22073+00:00
-- url     : https://prove2.me/submissions/d695dc44-fa1a-48a2-bffb-e32026dcd7d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 710611510 ≤ n < 710791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 710612760 1250 710611510 710611547
    0x22110a1701051509070503070c2105090f010f020601032a030f12031b050c03040323070504140612120c032203020108070c1b0611010b030d090b0a 64
    0x1016085141c1c0600001c0710603031141601400030f240c150500013a524816802960345030726641e00d6040c1595411031170a82560303800206240309010315103080242d030100403151100c91b00c9008550420120b001622002c1c2c0c100000914400c1342d2030b8000800c00d06680d0701c50240302c1800001d03202c4170441c0305854010b01c800010024000f0500180c05000c3d500b880c001e100c1c0200c141c170800d8081c0e058400c0307032910b00c1c03e1482c1c0d0505e440495101d080075201d40340401041c2c9147c40c2d80c0361211142c02071000e54035900300070b41010700b940d4800b04011510081c2400c1d5014041700010001d0b00d035001030300600c0075006c2e207510b50200c0740101090240310070f00d041d841612910b652a1032220359817074108103004a50405844041d0b180654124540c03c122503059440c60f1017a0707600c1100302d03110f4005000483d00480b5111102848100381d000d028003400540c2d0f00d40142d2202c48080c01c0c00e5442d2403500e107000e03400007080c1e070b880c855100c2c0c1c51806562441680c23560b50b44504504580240c589440d00c01c2d071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 710614010 1250 710612760 710612789
    0x50a080724030905030f0901200d1103070b072012030a021b12042303030412020613140a21081c0f060504060812031302040b0d0b070822110a 62
    0x801b840000d040c0300c840c203a03517800d40f40d007016100c09056080ba141444440c0d02c020302c50a00d19205015900380c3c182074005503030074429113580b0f03441d4096054aa0701c1c0172845211b21446454a107000c00c54428030200010854018440c400902c144005084002d4440e0000347d607070103092401116402000500c011110003210b9015050303030a803c60b0003035500c05411035401c1030074560820b0401311110002000356142c6454031101c0d051121b024001280c1002061103400c5280311100c010000410f8140c507018080c0c2d1154042110304412034110902207400070103801c040d001280c01500ca5640d018440360f650b080100d824501c06c1e007460860210a0741000903582c0341d0790b09a0449801c0301e5094901348805502d44201948540940ca2103010010040c000a003a8000c403001da800d030180040e00010700c0500c0310000c070314100107030300d4203075234080790b81c03083c01340043c1c0c44240c0980c42200740c0d40000883d02d0700301140b001000e412402034001900034a044181b59210702d00080180b4504040111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 710615260 1250 710614010 710614027
    0xe060304060c020f03040518070306050d05103b211306081918060509060f0106030c12090501060803041509060302070b01030f11060f04050a08072403090503 69
    0x5050100c41c014010300442c2c90b202c4c03222000206403420350314002c4c0b40840c201001100905d91040c018081d80070075403a40e4001420340c031285490480c0d140104040c06810500b64501c1064030201d402e2026038120000361000d814286120b403007030584c00d4400c03103100a5018440d0038a48209004030303102c040310b040a014901030910b0b0050000342100e000c1030f0440c65483d401995141c4084460240c10080064550b8161100307502c4903100c00c500e9500b0342201c5074030b9100d4204440084403240541d9100d036082c04800311850007654010440da107000e10850850042c0148045401000b6070f00c0503484000d054208a02034004a01a20070360702203e4913241d030b80f0102d105200760f200f5080046042c02102282d035501c43c7c02110201034101260440992031551a040b01c0584030200703442000107031810501c17a60b02d480c010401c400102e10b48544a82c2030104101e6002d000307a00c601000ea101c20b104002c00004189004894070710420800303125110b2060940107080111b10003001400300140189 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 710616510 1250 710615260 710615273
    0x90f0f010605011403011511030c06010902040302040b040501060e132405130b030a030f050706110301170c03060708040f080c060a0605010f090b030903090a03050601080613110906010e060304 84
    0x8551090340c581441900024604819210078041c1826107d5180b18401c01d80780500340d03c044580b06c403001c0740e00e004e540710980383c10414281c10400b5803a800140800562505020350404214200c40420841d4034000300039004002201c1030901074104640340c0120020a030b4030004640880048880751080410308003000110036000e03080c802c03d928030405c140911140700d8000303020b1019005040e40e0003103440a88231011408d0b82c0c1020000104150000215940500da81006d0002c04854895041c0001500c060b04416a406200e6116400e6003e06d99000902c142d0007c0c12030400c40d98a85403800c001d40c1181c00c14078050a9040000b401d03001d02c0d5000215030388660b42a420411400d91207400454403040d0401081d400501010400e10442c550138000f140c00040d0359080380e2030450710358007080c0100600c0d40165216000040100840340060080c0760744a03415201058429040d03944d4030b61031790f5400d44a6409550702c40001111a4040c060180711201c000b0055602c070302e42843d016 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 710617760 1250 710616510 710616521
    0x5030c0a0201030e03130303120e0d09050f03030909010b1e03010611011802090610021f0603021e1e0301023f011a030a0207060c0f1b0206040302010503090f0f01 71
    0x80340000d2600320b18035909240030042d9030b400c2207144640c06c1c2c0c083c5140c504546100e2089400000d182d074070060f0001d400710800800b000003045c2d0300c1e60003409140c00104142c40f120914100c1c041e4004010024a40e03a5550195042d42d00112031542c8840c0308040c2d10700805076001051075501000400410600e0f001840811110b508200030710440500146c4024104242e041c003c3d005aa01404101c19151506410200da10b40344102d5800d514802500707a0205441a103d011075990341c0824801d50805000800c0e4a18214400d9900254524085030140700801240e400320382105030250101d5a0a40440da030031940c0b104083d00006a405411003d05588984480c4000701411008184c41c85061b42c2812100004180d01c40f44500344012061584004c00d0218465800c000c8580082c001c3d10030750002c141a50f840c18142c14014101400c3c0d03100c4082d084005000e0320300da100c0182ea90b4002c444c1541d90a00c0e1081e00d94458400303c7d807801182d401809603600405198101243c070540c4034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 710619010 1250 710617760 710617763
    0x40b0a05041a040308031801151e080f250503010c0e03010b0916050703090e0103030c12050f0711061c0f06091a10050706060605030a0b0102010e2805030c0a 69
    0x103161042ca460921124a100390320004200e03000500018001d0303154100c01264828000002054407000342c20b0029145586800c507803c0f05918981d0340c0440d08611400ba400b80412000030131084503030300e4440c0e0f03540c2110451820f00c4800e0812a404211803c0205401400090000d1003240d41c4440c0c042d01a801c20305d501c0d03010b50b20340b8601d040c10746006000c1e58016040304406c2101d0403801e241c12665030f445100240d040c490b034000700080c10182d105015000358085c1e580d10400e82c00c649420451241d5602d1800c1c2041428080c01d4030700c0c02100308560b48543e03c5540c00d1090310300c4402090a41c00f4555111044006884241c0c4e030040030303500492601465400c04000303517030712901094115505180e03d0784d0f440c000c0300b408501609100b40f4519009a06052460a02186544404c291140d075041500080d102000384070800505001d00f108074002400240300500e40712201c0b56542a201c40c0c5c00c44180040750305407a2002510f0401403170107800100b034039a14007a034400240d030380c440300c42c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 710620260 1250 710619010 710619029
    0xa050c22060b1b0c010801170a0507080102030621030a05071515050f0d080f03090109080313110604030506270a0f110d0c17031201030605040b0723070602040b0a0504 73
    0x40203d4045400300b5100314082c3c05844000c1942d00b050403580b2103561800741c5003494400d105c0c8250205400300001c4005010900c00035940e0300d426002d02c003050a0304141621a0081807804525043c6e0100644c0e503014540e01e443c503141d00a504101d101c0032010304514108034949510608e5202821032a50305440c800c0c1d0b40307102c2c51030642c414040600340c82e117406015550184076171420748170110015500015840b0011070f40c2d010036200d5000d80c1e03000385d4200244107540c1513840c0400100c0402da191503070b011110303542000c1c0303180c84942e11080014940c003c44a142c81c0040c0c0b074910301c03940d034903a2030009104a5890061900d0164500c000c401000d0f5168a81158150b5003031401d045001c650390740c0010003000c0b8a01d441c003881d40c8040f0a0410040030b00081c05807a0030851810501d50081d40035440100342d5041c03d05003c04801d4000e071902c0100108082900d114403007109138465202c04807100321b507480e40c1c2810200001c0c012604451000ca03800035101c680d02d94050003410540d840c140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 710621510 1250 710620260 710620297
    0x7020607020105071805040b0a030501020a1808060103150209180c0c010501050a06050a0f02010207150912080705091e0402030c0310060c030f08061207061e020a050c22060b 76
    0x12016a800c801210f018403171291960000c0c0400d0034a1b030000c000441010345108606a1250750302800e90300300d8210701000856036840514640310966100740280b2850002d4119941581c441c1c20110b8442e55280d8040d50700051400706913140c50000c05445500d01200894900b0030702030044466014281801e160360a050010900745070043c00c210469a950711200c1c82d1001100c8140c0c4c072481d01c43c41e404250356003800408040b82d2041c448082c200282c0100103001c4c00e0501d40940610034400e0790000300948541040b01c0e0036004005c4449841d0121103e45036120b840f980c501198108004058206001009115040d01350030061809004d04445250b520f030b40b1000c080307e40030503241000e07001440300c2e141030002c0340c014000c40c2e03045038001e4107243d20480a40903042c98184643c0c00000060b12000c2143c0803412861b1845000b5001b5101906017852103448290f0b03100d440d0240a48aa407034090f080c03102d0954080d03081d100041c03a500c1484801e80c4c1c3d00301d80c8500e03002601c50155605021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 710622760 1250 710621510 710621521
    0x90105061017180708030708280905190306020c0303040b01120c1a0f0a08060a0504090b1819030908060a0204180903140f031b03061c0204060e07020607020105 70
    0x41024541c0c2c24159102c2024a5803031070040c80c002d01d801c1c840301045000700500400d225609000174040103016015050b500c0741074100c0b1051102030201c410a865241d245200100c0d6441030501c0c04445086031503100d2221109010400f0307000307a50000704558030004400e00954400302c0074502c501c3c0224942102c42e0fa80740c82401c04800c1c2e00000074000c40d01c03410240001102c00d46070044900031100e546050207141d41d400c0300d1a0b03010459600101e40900308008180c03070b09440d024050041514140700014450351940110800680700780d04c2487e42c0011032031701d91010000008112814039203101c10300306500b0040c11543c01c90003100c80394041c003070018840403058001c0303504039150100c8883d4040503000c803100003005501002ca0030450301020055030100280d000c1d00841c840340c4000ca903070341001182e640c002c0610640c10804580700380304100240e07642010900941412480458810880388002002807603641c110101000004090206075540041c00900c10080340d002007210f40c658 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 710624010 1250 710622760 710622767
    0x140d0f0c090503121e04080105042f04111e03040b060d0c140307050a061d030714060d020d140402010e040e0c120709020a0534020d08120901050610 65
    0xc0c000c039070305a0b02180e00485004d260400034480d0301d551002d00e82c1c03071607801c6411000681c89540411080d03910307042448103015a074145099480c80388548865506050080042c03200d20a569040c4516651109005e43c0114a42150014090b80083c1c2d2868024901c001d5025002500c09403510713926980010a141407400f000c13100980c1046812030264944151000c000b58052980f0341c06010346200003034507440d0856071102400441d100d0b1038292901030740e034030f20003503d003585541700342d11103401002000041018600f03450382c00c2d58030550703d030302c3c0f0401480a8800d44c6003141c01e091500c0200c84403060358809850003035100b6607034028003018480c1000180d440c80c90840c4055000511500a00c2c6050f1605280f122219401e0300d10766592030b40100200c1c0c0000c000d18012a0300092110621802c14400c040481e1131800d041c0e0365820a580d11001800070500c0c024080d030141620360041c042c0c0e00c01603030110b8000425141051401c110420f01906055072020700616100c164004407901 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 710625260 1250 710624010 710624027
    0x1020301030c120321020c0f12041a16030314010501051e160605131a090d03050a060b031306050c1612030209100504030209070801140d03140d0f0c 65
    0x421000070440507003090600f2007030920644044080c40342c026000039440725105010b05d0314045402006031904289100b00741466860298801680c1201c10751040c0680c5032402d0301c0c2138484c41c102c9a010850428a0b00d00688911400c0c0f4403600c0a0041d403004140c0c0c56005003003200c07035032144036945176a03410041d0341d40e00880c85400c0b241403402ca0350004200e0000083c2200e050b81c80309086400c40e02c0d80310304045806c140ca100000d072804107514000d001c5039195035214401a058140c1103171800002071030300c1f01c034801100820940c440020861b45405a003204002c0c0c04040c1d0125500c0c101000c0001c600e4040400c00c0300d1080c2800300003406425890265072144440d0418880c0540d22075480e400015038413030222040c564240b1402200344c8644070041c80404107a2039090341d03241035004004c0c40d020300034204001c0000b6000144208041110010711081058401501c03c03400c91606071900021000156415200840c6d0312444100e10380000065400c4440100041c40e480300f411525811f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 710626510 1250 710625260 710625263
    0x20c090403050717041e08060c0c07031e0204061d01140109140d0f080d0f0203070c08090a0801020c0307021206040503040627120303050a0b01020d1809050c04170102030103 76
    0x2101031020f2000304244039003103168004941c995515060b25504110700341c1a000780003803074900341d894052014400401447e50490140c800841c18a515900801da1340c9180740401001d045407845049842c0c08686070659071a0b40c010000c3c4a82511081c1c45800d24041100301842e4500d0705d800000d2005000368409070001c4103a4804078050b0030b240003007019810000d072164001c40d032804940d010840012843c04131520a00c83c49035682807481c8400d06031622200396522042c07041080c0410307d600300d481004a168401d014649508103180028203140e00707a4480040c1d5400014070740001e0703801100600304107108440d90318011a4411036183e841e001103070020566070080000344480350058011545611700c00404505a5071140210800b08609502c0243e4031718a02c81040100358050240940c0b100e80075604029100c04440001e558241d00c50243c4144210100b007240c520040100241c080c2990702400c2c00b81d41071440341c1078030641c014407510110003051b41c40c03400b0704641030003101e049070f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 710627760 1250 710626510 710626517
    0x1205151e031b01050d06090e3904020d0504050105090f030f0a050f0403061b0809010c0c1101120608032101120305250c08240a0b030f0a060c020c090403 67
    0x803100b000b07184162450080303856040c0903050100300640c00ca1402600c007d0031007400081410708903d5a00b40c40c0ca00c0300340f0581048a41881040c19801915000c000350580c0c0704c01001183c4d40913400b0800a01c2032204140155080600308403e009054200742c5c0211080800c450811545500481d00c0b4043c40c2c4080a68071420060f003407049204602400000078107446075403509507079648800c02c643d4500702070100d2010800510012641011a850b449902040207100303c60b07120200030500c103c00040200421071118041a950f4484c0040c2c0701b0180707079000100415a103400035955203801000c0da400c01b075039800b0a450580321005000904803251515400240c2e0780c550b5050b2486c2e00b0412142d11080100750341e0702c990444009072007803c1401803502100550420712200d0074201306021912006070400126001091514501c660050a0742c500182d00c80344140001c5c1841c4030911003800b03071310651417a030007405003591001b62090050340840d20104e414506025004c101110080c012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 710629010 1250 710627760 710627773
    0xd02071406090f0309011b0206040e091b011b0f111206012303060f06030307080a030f0c030614040b040207060204060f080105010806090703091b06030e0708160b0a1205151e03 77
    0x7800303047c510b02d00c110307200408840c201901d4402d40e11020750200c0380009664862030840e0b000009418064032014000c0c80c024200360744020101541d106044801480240d858401c4d1090084e43c00340701071040402003c01089120752200c1c0d50343d8401c00e014010b85001c80391842c80034050361001c000e00070034010740940b42c141e9400800c03040381c40000b8105a00341c00f00308083c2c000a01148001d00f1103e40e10749001569030400c0c00749600b101c1c01609a24103040c0b0f4140d060001c1c212041d890045c0b0841101c000c40c103100d0007404280a8001d0740d50040074903001141c00710781e00d5048440074148010703036610200580e030f0f82c60046034030325006c1e80c2f01c070f030410380e01c03004a1040d034031035004110100c1c004e01c01c0c089503000c0020fa2a5040c211544000c000030303038802c488130460b202401030b6002418000000c04618007010800d4010003100e124001c0741400018040090174000c1d81d450070081e2484100700070a2420702074402a840c0100300d0706101d80116550354101c840800c1240f10610701c043d009016 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 710630260 1250 710629010 710629037
    0xc030a020106090209030a120201180c1403010903080c1e040617100605030106050901020c0a060819060b090f011701031a07050a0804151103090307121d04020d02071406090f030901 79
    0x30741c8e0703002d0084030f0455490300b60005c204d18161210554191103488505a840c1c6810005a000e5070342013a00c40c403076410301200e240407a0b0300c49a226041000c0c82580c40d034903031403400704002d030302e400826166014001280000750039070070606840d11080340d148004456503c8000500c0000b159004260200d0310038401404410310a03406000c0844040c0100c80540840000050000f52240c0c8a03400150051082010303045808402d40c100050b003e20600180b420074500c40458098620301d1400307000c0a02c00b045860784120034400403c10040b41ca4800b40d40c6038100810705100f90b14000003040c1f0407101040d40d42d8400c0d011240c0c44082c0f9070350428591070b00e0f5150016116903e011101840d102c11070358440328040c200550068190300011961800949001c6060764100e6040c0801d1009140c00b80c200c203455540044207140045800694500141e080c410003809210701c054404440c0c4101c0d204201c000080c0700d401103c0315411503c1e904040000710703075248100010305000405086c0b640e003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 710631510 1250 710630260 710630273
    0x10f06021e0d0e04021c06240e090a110a09050f100c060b040f140a150303081612090501090309050a0605040b250309060e0603100605130b0c030a020106090209030a 72
    0x20f83c0203200600251408076004284068001034500106007156070301800c10281c94911040407540f81c07401d002c61009400100301074444020601480d015000306800611405140d511480c00d0071881c00c003964854190045c01040160b960048a02448030613851110602c1c0103039603445904513543c0c3e080c5204045507102005401c0803081d451308251640805070640346240251106401c4500c5082c8003442c220700c8817020b4401e40c1022101c6045442d03c00d20100ba403000b141c7d54401d026404248001c15107c104941591020309420780e0540380c00415020401c064005c0c00700140603035030300c9408546500800103441010b10840c40800c0042104011003400e00c000b9000010400e44402c040d02c003c104142055210804101d00103042047e080c800f040e00800510300e10b040940301d09042d841c0c81014030b50803022034002da4040c4000415031a10300c1075000400b5014019894040b0b031100d4050307401c550740b40c0040909001550274101c0100c0c8243e074500c00d4541c03103a0000d0080c0107445c0c158980da03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 710632760 1250 710631510 710631527
    0x70f0c24091406070c090204270207111203040504110403031808060a09060e0105070302040e010f060503071b020d03020609121e070203031b1b030f0604030e030a0b010f06021e0d 78
    0x711000b05038100d00046c50001d0784003a0004114a081d21180d541c01001d528451100481c8107118280c03041c0043c8021403d038400c210b007080c030140d0352401c1c1e440180c0801d40c514025980815400390500c0007811701440c0d40c02c040c2c82168480e4543d00890f02c070301d1f0a0346626071400d0050181d90f42c440380c005016110f0329084a01c02e18083c040025000c904a2103044c2900d004896510120b034002408010b03484158488500400001000d8600c01d0f0400200405520025100400304030a60b04580c400c00200c202c08000035600030407980a000c21450042d4036080100d41001c140e001d2007420005200680341190f2514001224205205401c0e61400c03c0c107401071b00050781c05100034031100842080e82000e030180c0c02085c40003042504005110b50845200300e160081c02500845002d07000c0300c82c001840d41d009581828054550301003a0086464694481805484d6278130480000444c0003000750a9000e0707646603825100c1440c1006140b82002c0c000c91136030802a07106450fa1503201d172040862 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 710634010 1250 710632760 710632763
    0x12060303032404020409060e0601090605120708100b120415090b0109150e01060c0507090b0f2b0303020c0607050a020a031d0a080c03070f0b0f070f0c2409140607 71
    0x50400341c1b1084101c0445100d504800121481c000501c8200d60304031079204010071061800902e0203120000c02c104081c1c000e020310041c00901004560f10003110a01003018065501c025900c800104075034030903001c8142c0303083c0d804e43c1c00710503000c60380e14840c01110350f0b8582140c200304959123001c80c05401800340c203910482188a40347c0200d01261007100b09402014180d40302800f0340d00a0508070b0902c045640130040c1030b07144c08180c40c000d40381c0e46490041c0d00400c446a524420010848000296601c0c948442060704442c9500030181c0641c081c000702d82c80e03c02102c2442e61180c00a65152040c50340c20400f5a0114540500007403280181010845d11040859688040382c00400e4810000390080c50441e001002010854202001f43d4030050440c94501e4544918080d04581c4601c201d5610031440000020307480b081c030441e5480d840d900390740015212800c9540c0c00d07001444420000c86200c10003100819415014402c00e014800d8801003040511040340302e008006450b40117150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 710635260 1250 710634010 710634019
    0x11040b03030f030604060f12171312050c06040b040807080703080712021204060804031106010510051809040c06080c03071209021f1e0525080403120203120603030324 73
    0x1c6c0401c100c2c018a043c41c0090001041c100b000300150324040d07290f04115400c1c641c80040034000311527074140c0f15825100b216103421040c02100c00505206007040b0002207080e4012400240028034480001c0c02001141c40c00300070b80c0d0301c9685a1758060388510540c40050b0082005110030008585424001040211340d8011185040c2d20b8070342d0401250040d9204102052032501000141508038031592044200c034806012198144000584a407203410b15140402401155888081c0012003540452080040c0007420f64645032a103401070b04841c0c002c41000071403110100f802e480300401540d001e0030b00e9480b170010310a95409424000e0201007011707a4028205012490b101224442500c450b441607940d54817070303801c10f081d09002c0601e141e840c4420884100030300d80c940b803800d4600031b10f482141d1050715242031340c81c1004205070041e50009001c81182d00c500c41440c030340000c010080011503051030302d0b6985da204101a101d02044030b0a1102e035003000454181641c0400d80d12003505230050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 710636510 1250 710635260 710635271
    0x10e03070b160f1b06030b030d4d0a03170a110304060b010917060c0d0b13020403060605040e060f28060806131709010302040b0c0a11040b03030f030604 67
    0x112880d804070070400e02a134118202072120080c21104400200140040d07050a20004104071b0100760b489150705401d804000c01c07980c10b03401c2d012024a500d401c2400c910740c00303183d511410135050707610741c0ca0000c40401040042d01d40110640041102420300e074140c0c5804c02035008000911000e124002e160034140ba0340c2d81c072107164214402000c2e50180c0d009600c009000003417003002410070f035041c1e00100b0710104a250b0709040c2440010307089600224044a00b516000e0802444001d840c52011070369000d40d004280b02401e00341c7da4054401c0f64010002841110b40c1d9030103000c00c540c2d03413501030541e94100c400040d050040e41d001031500324124203820280e420b018240c2c03807112110903024121050300c1d0ac20401034140200080703038000b00e8002d0b410341ca4103140c1e40e40032903035807031080300c242c2079400402d202d8180e070b01940c1031318001d09100741c61640c0c0d80002d0880d02e03100d02c240b4008580201c203007081c0003142d08003403040744013040c0090025442c00404900c1c10116410040803035a0268840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 710637760 1250 710636510 710636513
    0x501170712080d0501090b0f030304050303090f0a1508070305070f09091e02040f05030f160312051c0204050301050709030201020d05180301140712020307090b0c0f01060806060f010e03070b16 84
    0xd11030705008001c10b5500040c031301d07c002c08010300e510301c0c0300255200c0e900a010500090341e021040b142c1c441d408942040101d0650b0002c107030810ba0507400307540907003845080000820342207400144260f280b135404010580d1850f0040d07420071203100d00800010b44642042c0554441da074030025411150a81882441201190345801d0b0ba0040e00f00380b0908580c00c0b0f081105081c2004a002101c40c0c44000e03141c1001007072283c07401d070003051101401c61000c1c40c085101480c000c1084990805550740340c943d002103154400001b0754413510880e0302075071034070b400155001e00c503814410550341c3c164042d02c000b0613004c034111182c0d084203070440d0120050501d841c1c91a50240b04110002003048656031040c5403183c0041c110240084c80c90085a00400030003000301c2e0700030106002c3d2206164031a40351415110098542100400b244190790b19166020940000019949118032002ca98900349401e04000454040c00413001320358055002c0d80c01480341208090143c07944125002070051b440a89 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 710639010 1250 710637760 710637787
    0xf090f191403220833040c080a110f030d0c060e010f0f0501030201030605060c0309010f1b0f0b0105010f120c0c1205040e0a141503071d0a050117071208 67
    0x41001c841207145283d0420483c031002031051710881041045a000100c0201c0f0034402c18503400314450001070381c92030010301005084202100941041d00c03c40711141c446280c003031401d400c3c48001a104100d400c07810581c928000490a841c01410396911351b9000c1581d8614000c0e00740d40256106654980c0d070142d41042d000c0c8160307441410540300108407540346000141c03c4231827542110b40205070402101215000010031103010341c0c2c003803030101300b19a81c040d030860f0000300000d08821004c145072004018000c003000052001c9000300741030341e8942d90300c00c010355141105c0c842c80c4011505000554440070300c2c0d0b501c08806244d090401080c0382d00c2540d00c0036111008061440c0202c4d2011600703200c56030000c100702e6400300d501ca50801170502c072205030702031005000b0011221560034480341c0b03103151024080800280309070138440300c03604141e02d07002c040c002048805014851030803000054040301c02030104451720041016000250a0448590b6403c0d0f02c8071007074408842c200605004040e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 710640260 1250 710639010 710639047
    0x120a0902062a190b2215110c0d0212090f01110c0402030c040f08070e1f030209090a0b241005041503020403050d09050f011107030501050f090f191403 66
    0xd0088031845200301307162864803800050851718180b46007202240941c03511001459040790400c0c4ca140320361100038808006442c6044e400a6a160003042210b200240010140300c4440e00707409913910101c0911241c03581d03010303c1c0e00c015400300d94202d50440d6035004800381d8400092882c156905507006002107400e90340182d80501080000080070020b080140f4503843c091318403200902a00c92500324a10f251050182202e40c2c3c28240e00d09605044010f4050344c00110f5010308a00101d1400044041e10b55240040590f15111700c5030000d04004402d001c005800480764060502c140012006d0008143d0010450414082c0130000031450305240c0320114120f41c802d83e00075136110b0451178614240944c505807182444402c0700103000d25a554405041d50320000e203050000400e1850f41145481e1081d071014100d9460a028070158144c1c25800501c40c0d04042d040341c281503882600f499031880d120458440360a15845580c0003d0081c007011100300300e800040b039062505401140845030b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 710641510 1250 710640260 710640283
    0x1140127140714030f010b030705090a18140103020307030f02030a06480809150c070309120c050105030606071e02091819050f06070302120a0902062a 66
    0x41d507100800416a07031040e000d0360900340c1e65444a055084c468003402c0907000600034595110404400100712512031403c0d20365aa000401240c01d480d44c071400342101a0420300000001424000001081c60240e0800c904036680030740207140c5503145407507980103070601c800d00320381c18017030700f280c03040800e400380103040310441d10646298842c0c981c14660307800b407035030b580091440c28507240070719020f8103140c40a1540409103003480c9024bd0b441c000524103009008091400c0030102900340007040c1403060107400128440d481d000040c6032101000c6403aa0304028004041d1203a0306428040f035449074000c5d50b00700b000641400e09009032aa03c62084605a031990528500090603020540c070f09000c007140c000117170a82c6408661240000075031100e441c06111000c02428503240c43c10440b00304020010040c0030300650341c007070618041c002d01a50110f805040ca4490360404625006018865010600d900418513860701041600503801d40d00681c6510410b0540e0030b0303030444041d405200040449 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 710642760 1250 710641510 710641541
    0x3070809071a09100203041d0613140f15040207030504050907180303030c05070804151223040f050d050a020115050109060c060b03030a0c020418020d0b0405030c030708090f0301140127 81
    0x41c81c10100b442b42c20420f07a200408660300b010381c40d036a00d1013040b020581040340708140e80c06540c2c56241d04e40d0b401c19042e10151701701d840082d0300303010b2503030020262040c2c4100b1148004217841e2880c08690709480010121222801d4a20400c000b0340603078050f4580300300e00e0600c542442d05548441a564219510581207030154a994a03420750740320300340781c0c143d100c0c13100200072004490240b80d00c5050307c1c2603c07130288028075003c80c1c280030b007499105051542c0f10301216133564641394000d00540000c02d41c1d40c09982021020080d80c0b9a40241e00309684040e514011142d1a1203012110103c00740c1081d5441591240c15428a8400388020900c0c0c80d01a00c03101a203030020310501044500184104009800c10b801c4600183e07503881d800f000c0d540d000503d110580c0c49608141e800c600c620104509144000a1502c04000b031817030180c45985030849805c00070381109070074142645c002110070444404610014803400c402500140d1300401841420008443c1c26100001110240301008001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 710644010 1250 710642760 710642819
    0x80d051602031e10111801020a020405070c0b09010504081801050904060e1b030f0f0c0c0d0e040e0c1f02010f06030605010509070c0803072303070809071a0910020304 73
    0x3548002c003c107440b00840d0b1041004102000600f0000310700680c0100a1940d1b40000402c3c2e00f40e2080219000558006104200314240b541d00a403049241180032500c034441000020458201882070300c2c8542d40100380035250110110810b40304210100c03d442c184041071200c08080d45039403240a000c1d241804001082d42000d0042402c0540c550001441043e410810054804a014042c603000601003002110341d072504608a01c05000c1c2ca00003d03400e00c2411801441540e0005051607d960290b80410a0400801d542d9403a03002040903d90060b54200208039807005580450b01d0070b601a10001941000e4940d0310420340f074107540141e403140d84941c01130001d89000c0f0b2900d40c208415080041c102800c1d6611802c0a005c02080902401011800c00011010b0f102d0102904048618100c1d80c034605104068204d10050700d4002c810310031101e02107018110b50210504080c0c411100a0a10402e0360401c00400642050801180002c0c00300151658080d5900d0303803110356a010f003401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 710645260 1250 710644010 710644063
    0x1416050109080102070317270601061412060111070f06020105090c0103140403081005040c02030c51250206040308130201031b0e0a0b04080d05160203 66
    0x50804160840682c0381d104228010000c0e400400081003024502c0d81091350340e0700e200403180c403c08591441c01e43c2040c50b565000b9649404200103040e1034460f140e200e1044015a03000e002400b07100200b155030143d000120303402d907000307400e032a9904455000b101d92040d214000031003039019990252026030b44034014405411000d000d4002d210500f0b00e41001036002c1c80c00400b880c00009000034041c015800007182d86008094181d802034103019100b88940c03501d082000703560782e0000703070320103075a02030300714810404201106660600702c00c440c0b00901840c2070310840040d03848013201c611100c4d9040110103420702c10920b290f6206d401e41c0300ea41c041d0308440c0d00581d0358920703140e10303040110b421020401002a81188886401c40d00d40000004001c40a10050f40200854101c451000c00250703200c1000640c030540521151409480704500c0c00d9a8961807040c41c0507a00071410035400c20000fa200d0903205901600e0200e0f000742e103c44200117035801090510b4103580760a401464605031510 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 710646510 1250 710645260 710645267
    0x1309050c0d0f090203102a02061b040b03040b041407141002010902030703080405012d050c0307151e05160e010c0b0a0f0506030606010e01030f060504051009060509190914160501 78
    0x1548a4006240c0c4071f00d04482100944449000300360012200c860980e241e9800206001d07580680700d84018281d9900381400d080b400e503203080300c0480d01d01c3c8044518282403030000c103c503000c480d0403440000054030741c4800c02c1030a62042032102c2c01c42d0341c3ca13104000560340421919000f54014405183c0c0c850801000505101c01202c2c00301d140c5501d01d01e040000007e404103c5880145807400c0754446156441c1c45085202d064400390200040c1500704a0700300365940441c1c0c0200d25608084c0303100003140d445005840701212103402c0241d100c800c0d018445c1c0078880080311060140760001040810b03560342c80b0302c001d05669030000c10381d84682503054075549104d000d400003011402000d80b0718007400002c1030302c16820200c0b810107440d8140c480340c41000f40c010728090440240b0034081403801c0f504048500185200b0f074100eaa080c10340001c1c0500301000340b10300800b01d01d1034885141c050801c074003001e00724282084030180510040340c138000c0011311100c035004007400c0300d03880a140b4040004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 710647760 1250 710646510 710646551
    0x1050f120f0610020c0d030915180f06020c0910121a07090b09190807080a20090a0203100b160b060a0605180d0f05031309050c0d0f09020310 62
    0x2140110114060700c00451340001790031340e500400301d441a00129070b0f850103c0d914403980d0301a0b8860b00200d10b034403201c640c0100c0c0b00070603c2980d149042c1410b9032070322544000d442a01c1280c025800c4003908003110b0034100c1206038880d0003203000d0b20780b8580c0c648413088210103191080d5402001c8648ec007a94400340c21303040d07030819820b2a201648031f0030700365000000d1107005031503840360b100c0700c00c0d0821b8105900b0342100100300310010780302610750700d0240c503480c0c44609038111120b03500c3c280a18140c80c20200e601e001c0d003001800c00c561654038811218000e5201600750f01c0c050300c030000d0004560724214000c08040160391509800303108642341072080c145024081d01c1c4120992401401450307800300980d20a85203540030500d2081c070f901c0c00306400140120004e820052089458824450004000c0c1480b00000e403031006400d9840c1c21080846009540c03d8200d54002c1101e100705000719048007460903601c500000f000300031540080d107021000306000d8011601d40f9141e10307030302540008a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 710649010 1250 710647760 710647771
    0x60c18030a0b01061b200111060c070206072f030c03280c030b010906361a1f0f03020712030e0304080f1509010b030a0b0601050f120f 59
    0x14180044103682c0c00350200340c140151030812000c1401c0310a00344204401000054000444260503c1100f03850030705100600c20060125070000702c03100b8a1400002c207288524840110242003034030540c20410542d100c0c8200f640d141c01c504120742054550041219034094465800f803181c8449901414201408043d559101c1d805c00c0c503070012100141c242201d0041ca0191054500e0b410b1841d00304022800c40e0005000881410004280361ba0294001c0003695120381c41c0283c076441d10005601c0c1418110403c2c103140c10300d01e01c0c3e540024800d811412660b2080000309001c3c5c111403001c242d0b00c180759104514186410550340300d2268200d0802c6541e18132614003946044041c2d165856503080316444001016030b00d14401c5071041080c0261009080e403201510707800da82d101c400342d9540110707803082c0b0340c81c0c0c480c2004070300000c60500c1200500340024000d0300d04404980c07030b40a10b03000000c00941c1801010030060030400107520092109040305880700c1168100000c10152040f8001d20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 710650260 1250 710649010 710649013
    0x2040c020610050f060d06080f07080a030c060507030e030304120f0228081b01090b011403061605040f17070504090804031e0c0623040f050609040e060c1803 69
    0x24410031000c9481da01d020749400740c42004d205540c000c007044552040c0b00040d00000e14000e0042500c00d4041200e0318542c07a184100c0c1d07501030301c3e50750b050346403010424001c0200c0c0f02103a088002410079000130b40d018074a4100025000001d01900d421030b4002c03103003140e0076143e081e054808940c004011038020700e02c91006000c0300c0600d000002c450000290001011025205e50307808203c4244215541c54400d41d250345516100c080140d4081e20a048003161020a02400415144408600c24010364401801400c1c0c1d511000c10180340441410f00c0d110811600700300104a56655640190040031314015181104050843c460709240c281c3d0805442141800b140b5408a54110199820b4940182c0c1080d400204000180b40b00e0100010003044501c0440c0f0009000b038110f8003540c0c5403d01b10801c40c4090100c40900302e00f5102d1402468014590b00000f8059800e02c03501908032480007800c005000d0002520381458104105d4540a400310700284000841104400b40700c0c2020041c0e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 710651510 1250 710650260 710650273
    0x906040c062c120304030308010f09051302130b0306180f06151912060c0f0c0302030d0b060409020f0405150f030f04150510052d2101020f040302040c02 67
    0x481d02d1502c0219076040075007018060002a81a90319074042400b20340e070810031203039603c0d0b40b0700e0b02900e42c980901c50740e00000001d060006001c0020b008080c4181014000300c08083d000d80c0c20040342c1000070a07003000c2c031591039075030b601c2d00d1701c00f000028041c0c43c01c10222040d81c844c1101c113a103000c10a0702c0003921504a5814040d0b5401109084828034400311961081d07090090551865400b4682c401c20b41203030416020010b000e510340c4000a580f1041d6500040c1d42075030542034030790820040c00103005034000c0103484696181c1d40d03c6200000300080089192a0b0b03282c907400241d0300700b80f250f010700080009040001e840c0014841080250340a2283c0c207001c14492121440d0100500425082101a00080070042e00ca000c2c502c4408880388104040c0c202020701d003032120400d00a0034050707812001c1d0491011100f00a503141018500e014010f80480c00b010b000040810442641180450344181da00e04082800500064000081c1c1240c9a0b80343d801040305580446850806540248 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 710652760 1250 710651510 710651537
    0x1030519090615050441160e03031204060f0b150a0207120f110409021903020103050604060e0112030507050a1406070504080d08090c280512150901140906040c06 71
    0x4007955816079206c64400c15407174215075a1000d20000300391044800740ca401c410080d20078030107501140c0040107560703002c00c051500e80074160781b0300c2501503c181040070003000500103051034202031990001080301040c010b44200c0443c4501c07242c1074011100d25400b0555940142e41004070500800500406400006058440f10800980091301400218640f2010b103110348558106a40c07540d0301600c91445544d08110070101519580400ca00090400f0302144a07443c1038000c41083d00c040c20814007080c1d10300150a0601e40e2040003c500b40329050140501089080c000c54203654007802c840059200901011400c00b40f00801c1c5200340320061000f800340013000502d05448260a0418804c2522110505850107a042e00d1040e40081040180040424503a0341d94142c841c004892800c0d403600e541c108100407618140010456201000d44488040103000342a04804aa0000581c542c800201b590054508947c0d8152592040b02403000b04420600c03000d00502403480c03c040f02c814003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 710654010 1250 710652760 710652791
    0xa0e01091104030b040f052e11040f0920030c070b01090510060e0a09020c1b06091c0c03080f04030302060a06050102070605130b0c011d0d0e010305190906150504 71
    0x241006d88081003404412003002010011125200001035103212241820162000c0300c000c40c04440c00d1a90900c02c4000c00704050f0020788080c0e4140d80c51240580341403031640c00051100410740d00700101400d034805100519040110302038014202410381e90003d50034207603600304069120000c110f02d0b080030000da031400f04e10154261032052030501c441048040000d0b0b280c0304243c205660381440090f680c2d0210310300103028000c41807540700180d0201503140820200c3e0007282103c0d80c02240b84206c00204181450040703a58a124071004e001d819140e40781c044442d0008010340d038409200003002d00a041c4c0402a465100450400a100352070405000030745940c4180f15800a014022078070f03060700d0004201500c060250214540e48801c054805603001c0c1c8400c60580d40402da00c036500c641400350100300403d400c045921001070107128400110010718004004075017200303010480515022840c0102c82201b170140d40082500003141e0110351001c1c2c0c0700e50100d44201e00c0e1000400038160f1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 710655260 1250 710654010 710654033
    0x1706070f05040b03070c14010501080d02430909060501140d120212030a0b011404080309091003120c23060613090f080a030c0e012c0a0e0109110403 65
    0xd081120b244c4944070200161202050030710300404250007003818014101056000604032019607003205c81a4038902c80582c0c4074210190301c2001e20040d1041804402c41c3c4a1391549221820305110303110074080141400c001043e40c00203280c65840f60450000e00102d40070310340c090040614000c890f0000c500015a6034003c624008245130100781c0b564808a00034802c0440c02070310007242969a20f0825410002842c158003524007041c101490000f1299002055a00352140140154586001e260030400c400c40000e104144408a094010000174141300e2514202901074660040c00c0c1024070b441c1d02c1000041e040c0380076484248210710418180003c0d4190003420540c1c0c09000c51aa03040745c04003801600c0743c003600106416070307810100b044680080c1496071890b0360400500c0f006a00c111084c1044680c001e000416070040041c1c905014800e101c0700042d0503250030541c01044000c204901229031218101d1078030b140041020a0f028000c0c010b4a600148c0d24074501030455852001140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 710656510 1250 710655260 710655269
    0x1d010c031202161401050108060405072310021b03210304080c2d010b0904030e011110060302030120071707020409080c0f070317071a011706070f0504 66
    0xc00a1110302065048a030b6030200c0c420f0070b00c1c800600b030400c813103110b52050f8520000c0d03290400004254001040d5103001d158414042d000300d03072612010710022250b40010904e107a0480c94503400ba59508550781401a909030050445c03000843e10013400c01080014040c040c1e0006280b5420940500d031a9600f41000307000c0030394498860342850b030824014107820071064401c035105070240c0d1901495010100450341c030031401d120496200b4a09880348512081d4011410001090000c0c1c0107200e6101616018541002e230021b20306d022901c0c10703005401072004c0603507078041803041d03080a00418402e1102840fa03840488211400600035104010f0094100710801c41f0909814409104450480e50002c10900451240303080c845403a5100040d001d00c507202e22440f0a40301040421908101ca0304626504020f002000c00c131105a4400081101c80d100c99103505440443e1042450b406401c1054008031191740c4000820300d0160b014007050140124020550b0041d0b620400700c0e4140d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 710657760 1250 710656510 710656517
    0x110f0606031e121b06010b0c030304020f03030d06090b0a0603051009020a050c01060e0f0f07080114040b03120c0106060915030b06190e0406050406050d06020a020a1a071d010c03 78
    0x400600c201c0c0d09111122903038819120000903403264001034502c0c2881a60b129005491259980703047c1c0080510074481d012404d40c0007440000c0252030700c1c104207074290074050142c80c030b4100c51199400407950b07186c000400369a46c0380181c0840742800720a0002810541c1410481ca042403502c1c02820034491080030082d940000340f204440348140d007030745c064140b071342d00a006540d01c0f500d4000c1100c00c1251108d921000e05000201071011400301c4a010b61080d44071a21241d080040141c0c07107540d03a4201c41c2d04036454844d80b0741d407600c0070001014098a0760040a440c6c01542001c42d094600c968040e80c10002000c10600c220710444041c840d0007581403d00150000d41c08022403204e0169020b1090000000780c2200b060301e40100c40002c000c8012901001003035210070811080301d805000d059000140701841c44001003a0303a00501c244003040c01207a42817071803039483e2800400038000d022001000c10301400301807030300059900c144031020344070494401035036000201041d4110380040d080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 710659010 1250 710657760 710657803
    0x5030615120108060108121207081012140c0f150901030f02121e0106120b030f010c1205010603090305070f060f0c0f02100b180a0e0a03110f060603 65
    0x12840444901100e0507090300c000307607034422100da10707007200b44074242e1240100210ba113485400d00c42158000504820040510341315280d007201c09107402442410402007440b00401c109480c1400708c001c580c0716860600e444c43d9004c20503420f0411085815000702c2c4200107202580d900e003407505a07002041003400d911001c01c480100c01416252590051451000803400590f10a4221940c0702d4803084441540c681042004045112024404c500020300c2c4851418101e9001da0011031503020010102c85090f064045043d0071229130142c482c020071011036103005d1240550013454010714060a0422004c090b81d1030160281c851a03400418510502002c5010800c2030b030f0182150b1040104200301c45c040b1510054511f00607501c0fa800544196800301220611074014600040f1001d0a0150f003044401104901440040d050f04007007616a0003941d540f5100b0800c0c42d4910b402a2f4643d58208100c0413500e0505008160410f5580c0243d0200310940d14005003400c00c0080c0c02100c0710a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 710660260 1250 710659010 710659039
    0xc0604030f0e06181f020715110d0806130603021c021201050910060f1a0c0307080f03061203030411120a080f12012711120910180201050306 62
    0x1900d0b0003000c0d40d65072069021070f1038140b00028a0b210505a04240c1d032502000600044860903c0001246980140e00c480c0c018043c0000d20b04919072000c080781065003038003e281da0200d040480e50b1030480700049030700341000a186000e8500781d55a0f046103804000460650b000324540400920b0320400040701c0c485407004545803515031601c58010342c4000c0205080100c051920b5442c40408100f89a0818030046600c2511280c448100c40240c2508500426003080d1980240c1100b00c11301030741c1c00b00744410384c0401c051a006007840b610316280644d9a140079020131142c1302d01c081c228015584240104000907d200900d8240300c03404032203103074002a121080601c2c0580d9200700500d0342d48003240091074a02c1e02d1025010b000d500580799805070782c9620403c0b14055440d0142400241103010010030f2000c19840b070b03860045a6030805203850180b44181c10148400c0c2c45862165100700780410f11840e4a2107600d40c90503040190214406068000038500d000c0544014880c140c440302004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 710661510 1250 710660260 710660267
    0x5100903090510020606030f01020c0c240f0703030f110a1808032b0e0d0c061b12050702241015110f0715050903011514150c0604030f 59
    0x90040400421030300f00e078028110000d48a42003502c0d800d000303104d034100c465030340f0030b046c000c4c0e9090350020350003440390b510844208400612001030800c10043e601041c02048000d01000782000f0307a01540b000d03550449450010302319640019081c002500e0314031100030400740c84049030158001490b248500c004609405000740d001303940054150f2000140400e0b02a0b51450260038254a00940304070401004c41c038102a80d01c00404038905402000c4548201402600359109850040b46c001406002d4041450120344801c00d055020070703502c0324070300000152070152690100d03152000c0c116000340310001c07540300082640304c1a003039002d600000c0e02d1000d00c0d0080711b00030b010100403d070340780c80c3e8442c0142002801c044501101d004000c06001044030010f014002c80786001c0350340e80400e9000c24100c4068102003007055055403a422004070106034030850a01401d005000d0f000f4113080e250030800c1042c0c0c04c80360811101c105100c4400450400303d0001d6201d50182000400c1c08403041c000c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 710662760 1250 710661510 710661527
    0x1050d02010e03070f0614090307051201180c0504150602100b0607170417071a0d1b02070f05010c02130926030a0501060309020a060f0e030709050a061205100903 71
    0x943d0144102080015200004014001111a42d45035104044c2d5203c3c142c06c43d40c8200300c8503c0d010391007c60100300e00e0030040c8543c8182a80d0100007d02c950f8100c8280c0c012103030703100080d154907030070503801d10092615100d010049440540c107140450f1038404041d40740c59102850800c52540c80d080c044c2d882e00c5000031107a445522a810084812580146070096001801180140341c0503504020056000160410685e08490409000c1c418a5544e0094950000c0340c4605e0a60302d64100024200031014060114a07c9070003400095041c01662a006003980c1d0100e0304000500080801580764500b41010414103a080070804140300c0c205614941c0c131501881284c00020443c0850b2074209801440c05414225410b01c07407a6070340c1004034181c0d603071640041d5005100c8041080464091600581c111501b414250031301001c40000904100707090384a080b00f91784900800914840030b105141c0a0114003c038682410380b2900c40540d205000256032501c19a500340e050300349401390012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 710664010 1250 710662760 710662787
    0xa090c0302300a0c0501080c070602030c04031a09061302060d0c030b060f13050103050c160309050d0f0b090f0a06020309030912010905151b0d02070c030b18060f01050d0201 76
    0x442018a00b4031060750b5803018851810769614881c00c40c042200d40c864a802d901800c4282952400c041490312100000c2d8000f40ca0030318514820000000020344038001403450440c0420f0209451a2095505060220050812490b00010032002d40140d0303c040a4501800007132000207060030702c188055004002c0000401e52110300462000703c0c458848004156440d511041075920654901c01541503d40640700c251024000f07000003005907500e200313622540c0d802441c06500c00755603200070036000710041c0e8065804036040d480540500c0700e00d41105400085001c01089250112159651201d05020006240301d4002021440e10030702081928080100280101c908040e0310103070a0080290b10006c85050091410342807a5200c0000914881d04803420f03000d4981d0340130803010000c0e500580120171440c1d42030000d4008942e060200c180a0b51043c80b100b801e0303040030021810110001600200e0650084040041115011020a0440300c042d192100903140c81c2c8016034030307071800310135 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 710665260 1250 710664010 710664079
    0x903160609140604062301050402180411091207030305120411180a050f041211100204030b041e02100c020d05060910060b0f07021012230a090c0302 65
    0xb070105007240c080340b50390141e80314002c100608021031307451400110030074807a130202071072210040206050617002050055121070001c181c41c822800000c2c2203800b14072104c80c00c0c00c0042490449410041103d03009801030794000d08125145540040581c4902c2c0c007609030380c00703400000c101004000180f014000c0d900070020560381d5000c11314031080c4c00007258410689414100071404561002002500980e00007030640c10705c4207482c05c10b40c0c1c884480c04010550b0b2040302c040902441003440130308040c40c8280501421820203003404001b0030f2100c130b008801c050801d07603e6030060351611800c50641007242000c180c5e8000900002c2c8034440c0c082d00240c00c0b4041c0d40700b0809410030120300c0c11a501c0514408001c0b8a0700c0c1c43e0002928003656103440700f0070604005200252600d40c2813114010f40518010304040512a016415140f00707402c1d80100443c1d4142000f413210b541d0420541c402c00101e0200080e0030a5103402501c2640ca12000e8050004141c0304400a1000a100d05a201300c016 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 710666510 1250 710665260 710665283
    0x5060412051e0c0a0501030c120e0f011b02060708070503151c0303060501140405090408221401020625110f16080c09010602030d0222031a0f0903160609 67
    0x100c3c1c5507860035a0301c074441e02010744080b600350300a1140e0a620a142d0b6606410031400c01c4501c4000d1044040b200324a11a011b00c5031250130003406882e11710404404000180c4080d680e000e894001e02800c0001401803c0c0108040a507024064a5020641940c5985070048170b9021030b0640d50780c0758601d1340d0080c0e084104014503130540c115100b00c4100380c0e40d8040c0c0280d1540e2901c050301441c014182e02c0131062010074045032001014059032500d00d411b0b417001c410403503040011030b2a50743c002c03100003120048201c621f680501c20550700c44011080d49001200e58a02c4400291000400e20103011651030b0f211440f100800456469010707000c21a10040d2981ca098200e8180501c2007095901c11803120407050305051395618102c0310076400960070000d1704c060305000303034000307007003c6901c8181b009102880000c103109080c0250702500c85001d40d4003003000b6502d58103030700811032550200c0050034405030315400000c842c3c098100d002c2c601d89031892898141e020b130045a1010380030040b880d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 710667760 1250 710666510 710666563
    0x605040507050c0f12120a18030f020105060913030503040c0b0d0e0c100c2301050a05180f19030e04060303051908061804051f050601030f0203010506041205 69
    0xc1c0100700040e8050100c56004410084282e62601043c036440c01d010414001520410714500350150000b40781e030808940800c1880c5a40b23a20b04041c001940014558100d4400042d0207202d00d40c2c0205041d94141e185241121012241d8241c4403802820480e00200190600c05141c44260241103500030003940d9030385103c40c21014115801a210040c0944c0c00120064940015030207902c0110341c07030b5105d080d516502c46148602e0070300290022415902c0500c0144902803003090320403046400006080e040c10b1402c000b01d070002ca0242161a40030f001480305080001030102c54000c44110407414a00d281d2404841600c3d00035040c50300603007400000700070036811002908000081c01c07203482c810341050380111415181610000d40048042c90070b44444c3c0128030303400c4c0d4014002c0080f01c003080060413141d980700ca00c450103200260754030000d2150b00c1d80e05000d81d01320a45000c0b0194255410b250000c0c0c498400c40c82400d4003140c0f10a071280420109000e00300c408490780e0109070141058 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 710669010 1250 710667760 710667767
    0x50a2001060f0815060607030903140d031802092802040b041406070b0105040f0212151f020303130f08040f0504150e061201020c0d181a16060605040507 67
    0x842c0942603002d0080e10010524143c000781401c00a81400200c0c0c0b403540711002481402c1c0e116040940411944000100108044031490004100248000c2500c01c0030715800404803101113280b1616000740c4130000000d1307503840b200582c11004d800b00f2001e03481c09600c51071f0345081040f43ca908240380041400103124000201500442e611904010b8020800070100300c1c2034400d075100140840c03240c40062003d81401c1d4491a1000c0c0d88031401841c00f01035a85da41c10303c1070111180d8000202050450317150782001c44059021113441d1a11b5404a0300d4088040d4a07404020000d00c0e49001e031001060601100c146081d002640080084d40c0d1503468110040310041c5a005036401036041000c004d540e14814000750080341c82c1540302c041c0c161110303010885400490b410041c115902072058011091007805003000d03044650302c601c02c0708034664050b8644040c090344882002100050b100c160501c0d03a40464498403078190702c09081080c5440c01388001d00315904200d801a16050800040b90340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 710670260 1250 710669010 710669021
    0x41b05070506090307080d1a0d0b07030b0306090c09250504150203040302010c0609020f060c03120603010b0a1701110315011709032a0303040501051f03020f01050a2001 74
    0x40040d100c05036103d0141c1c954912403400001c0030315000708003101c01030002c1d0740101c182e0304042c000306074003018100c0091404003a8400c191044034010042c050003d805100c0c845c5806010740c058989860000d14450b26a85189107aa0048400b200010707041190040000c04d210000c4c201d200800314800002090b0340c0040c00749850403102d0110200010b4000420b903803c4030350594071408100712a40d2010098480d840c412600720621529240e0321b591820054254005108010343d00c0c1c0800030381c401e500c0d010280280c0c3c02a454050403890903150010400c06484d400203035501c0c1c1071182c42c0c0b250700500c52406038001c54540403043c8a80000d16a20b00d100c120404d99449850316800d1300302c16041c1506649004581c3e000708007445d0700003000c01844460014002c2c1041c09105071080250450340210b4007141c00d80d6558081220a8090030301041e00136844554240d511410755010a15040e0310200d03142c18420701207146002c89110b1404464000048000b96050000ca113459901031b0a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 710671510 1250 710670260 710670263
    0x60106050913140709062607300f14010305030405010e220c0e040507022109060408060a1803020d14040503011503120e0a1701060806070c0203060c030115030506041b0507 75
    0x966183d201280404410171f00c03c05448051001d148030b448030707113091f031740c504174001099001d68015165040070a6a40f40444092010b00c4000c140c0105494034482200c50701641c400205c8521001400420400000d98041d5002820040c404410f100002490000492410a14113254100780d203041c80f400d4000010700051070b1038407034881d49000200815614201c036160016800030410010041105110b08a00c2000140103440c01c581c170ba0200b040381d031042c0c010812652002c000d010701d039001445081e0702100303500d0400100c1005650025101d5041449c03080070003045072002c01c02800ca8a04490041c90010020491182545544040907a042c80141d4042407a2041c8000c403600503030002081c0318000300052503e0b81080c40c0e07101620700a00c159280d9650b01c44001c50300071020003055004060070f07218841c2000e801d00c105458400028822921501c0a1004124108003c3c00e0b280d100310540c107011659a031800003050042c00c02ca0280c9900085600010502d0340e0010000e0010b50b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 710672760 1250 710671510 710671517
    0x2d020906010f080f0711030a1808030406021207020a050406090b0432041502040e0406060b04030c050d0515070c030801050306010b0f0a03060504050114090906010605091314070906 79
    0x36900c0c040151681c503400c52002c4041841e007000252074455090300d45601c8890340c280250000d00e505d101a155801100424011503001c041c20446440d034640101c0041c450b100081d0b00d000c0c2004c1f0001d403140d9500b800910500c0703000c1804021591040071071809080081c00400a0300da440100034098690548107034059403500d1100241303000e0101101c3c1442070032283c40201000240c40704668ac2030000c0056620b2440d403900080d0032955800108000d101d14400e501c11414141480800c842255010010504040004100041c1100145021204200ca85201400c41400c1040c140500a4414071500913070380200441203803c244012202c50107542c0e0501243c2e00c8a05059a0383c00c2070003074031181341d01400b5032003648403100010009886545070115a90707642d1130201d01612400e03000840100524840301006041c052a401e03441800e6074001d01442d494400040c11602c5802d980a0040380d404050803900c4000d5000000f009200c00c1d1195010f1500300c800034644411401802d000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 710674010 1250 710672760 710672779
    0x309040f0f05070c0b2403031803150f0a020304020d0c060503012d0b07020a080a05060403030f0c0909181b090501060906051804060b160b060103110d02072d02 70
    0x10035100e040f00302200396101181102c151031ba0b40302213144c010444240d83d82111003440c0070109440620243c18610400049051003003066003c041c00e00d0155446807d0403484141040107109041000c2500041034500040c2d0329100d40c000b00d0106000741d1400340c0381b00f0b5808000078015602000075812100700100c481c0b02c00210103080925040c43c01c00900320004202001d20458181800030020030348024480c0c200c1d2680e403194035041441c07a88041da2950400b40c1044245501800f0712800c1c0001c007002049941403400b070141000590f07004541206d59107101085003d0100810302d41d149401c481c9951040c0003412034204c1d0900d2034001c0c00072036414180001000c90141c40740b541514129156a420b00c4280e24507450031811910000d03178800d884402c0000c036a18030000500501000d09104a00c0f10b14a00b000e6103102409410981010319013070344c0740d0081449400341c81d0207104048026a441c039841c20031801d0a00803000040c82010744040c0030002c21034180480307601a20980d401400e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 710675260 1250 710674010 710674021
    0x140a0b0a180209040209030708010f0f0203090613330b0607020d14030912010b0301150f18110a0f12020a0806091915080613020102031b0309040f0f05 66
    0x4009610455100321240e041c0184205402e070003400103540041c1005041c240c038000043c0c0341c28031503808030301140d40d2078604440c5806a070140e02d00c0c0b5040f1103415880c0d810921012035607104000c10800d1140b0311800c0e490100081d41e0b05181110400300d1910010b2001c5552041000c0c60f094401c807401450b010b003002082c00d07d90300350764044d0f0300200404424502074035110000401c00c1054a81400104050846640e403800090480c00070790000240800c000001d041c05c56604c009620944007912034204032140c000603028055800070b655000300e413a0302010200c003920401511500400020a407205843d501c11010340300c80c07440e556071824a100f0348014101328802ea46441c0d0001c0d481e04005000d605106031400d411005800f0501c031001c214084030401c9a0004e400b030703c0842000e40c010000342404200355504400c00884d420004c40142e030001c0d40c0da1184050003114205069008100450280251452040c029006021001625220000520310512100341031880d0101040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 710676510 1250 710675260 710675269
    0xc1e0301081f0908040e0405071203050d0b09040507141f0503060a0609060c12020c100806100329010c051c0908062a0f190f05030915070909140a0b 65
    0x100f03210341100c10b003031500741481c590071040780e001442600e03a0703c100000090407114003442c6801160096491a4845960152010949580040c024030501e1000e00340030108002098050844044405050f00026801e020490b5802d400c4401c02c140800308803912008c54110008620a80c01203d40c040032a494a0050f10070000030b00481001413249404070380059501007402507102000c2c011592003102e942c00040402000c00034400010b040030050001c14200500880d10b079407441d0a05000100c1e092002810345802a848030100e200302c5041e04c5581c3e406802c014008980050540e5001d01007001c00d080a03184001c540f800190b8104800161407001040032402011052804000d071802c0c1c5a4003900051a8000590848001c1241d190034010311002030015020000013080c950200c0342000d0426a042d151600a002d8104100007002c0004501130300e01c000b801c0b07003600407500e0f010411200c459140e00240882840c0440501d00ba070705500403140314000b500d009000e061014810300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 710677760 1250 710676510 710676521
    0x1303120801030c14060c03030709050a15020a0213110403080a0e100f0c110d15050903120c070f0b04050c0f030c0102100b0301021e1c0b090c1e0301081f 67
    0x500307800b848410038030105804c5001002640e0700200840d0a00800070345075401c5900c107564020100b0b10701307182080743e41080314400c0014100c85074045220010b040b0007948030700701c4483c0244644800c244140b0500c40a034420ba00400620256540f07c2e0388030710b040c25095003e810700d40041081c0009010712071806101d120401402540c560881c5502240140d032140d44424040303818002c461b54400340d0340c840d0016034500354040c0e851043d00032814075000d0100d03400234010b104250820080780400c0d0300c0006009421070f1420222a80d214401d0400d409000302c00e420082c24001c81005000504c400090481e540600496841c031200c0a08001c25503916846060b950158201c1c1b10118a003d60b1548100fa01e2640500007614091600c509000490402984003040201c04661080c0c413070055904120554211402040580030407800210f00e213800070080310303200d400010305040c079088540d40d641031400320b003070071a0303c0756158440350340c40304a9442000307040000d070001c022007401d96001c1c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 710679010 1250 710677760 710677763
    0xe06030c070303021c110706110406050306060703050d050c07060b040b0f0112200408120c070b07032d0e1503150604030f0b01090c110d030b0a0506130312080103 71
    0x48514000c815036060f0065080040c24a08149003285902108450380c01b60241075030900411541e1a44a840d0000442e6810680114042001c1c001030090640046c201c0c2e0300302c0740480e150f507160451490304a50900c1100201500d00d400c3c001401100c80801c03015001540c0306071400d111a0041c1424081115140072450ba070140d5018101c82d4103502400b2164817000c04014007182402849078007a003030310205051102c2400e80024100b115280070300c2054046100046c2da941b40c070384000c503041d50b00c1125000c0e44041d402c000400404046c0101e00044903494000e0700400b5000f4030400a0210300e480582c25008140e442816684615169aa8100103403103071046038103503150038420b01603981d65486c0c210341004040001101040c0e4107200c41e42c44603c83d425111996041180080c283c441072101070301400003281028036030038004150f07540b4143c0c0317902c3c001540d0b40e52900003600c0081c0070303400603421902c001218540c8000201c411130a49014640c2a5010400d55a00711100e407003d100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 710680260 1250 710679010 710679031
    0xc0e030f0703030809030d0608031909060c03050d1413060f14041101022e0c08240f060c0f0c0108040c030803060d02060d0b0a1502070b0d02040f03030f0e0603 70
    0x400b440028060b0350f4403900035040804403410061409000411200b0941100000d0740c03021074003a04902031019594942405864085c8001740b600c0c1000e08407811036a0b0040c14040c021034004100d444079030003003007400004181405d690808400e40359907038000000a590403828003038002994141ca003d000807451003c1030320f607110307911034a41681d59021000c0b05411401003080780c811549141106440c0e42c1d10035404032041c1c079080030840040310444a0a1000d000804007048100810603070014038507141c803522600c9410798000050001c0458012059000c41d010510a85002e000204025a110b441040702d50141e00c0000565100400319001048821405010300004a21101454000034050100c150a61440d800500550000103101400580d145001181e520305031140c04024904000100003000d00120000e440d07007580d01a45201010010303090200b00d81d1030b8121030041440040c10003100b41c9034900100b0401030b040d5030900080c46101080440e19000048a00941e9820b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 710681510 1250 710680260 710680273
    0x1e01031a0a11161a010e0906010e04030f080612100c0801080601032d06060b0c1c09060309030908010614090703110a14070212071a04080705061e04090c0e030f 70
    0x781c001c5540a41c980e08880d4400c850309031801350b00c501102c4a010388988110280989000c03000140b030600141e001d10007800314801800007007500200070348108041883e01080e07560342d0102041500040154044041c811162150107048003503104215a880720b64808909907601c0800640d15031080c0409840864a001241e5840d0300709034105d48010003030104204441010345440701100e8140d81b00c1e0300b407c80002100c2e10340c0c42d0280b02c209004030300b010900d08030358402c65004003510341d1070081c041490742d1414008140350040120000510001000f40126030711a002054070115909540340a0144200441da4a40c02409119407001001d0042c0c0e060038042c00007203806460680d400d0391001070400040c40562100300c0400201c000c00c100401403507117001d5100b0450394a0b40e8124000640c144001e008100f00490648200d84048800c02d40b104501e83c0340390354481074a4400e040d0042c00040010704500180c0000310542601c1d200c00c1182403885040c0341e2108000140ca01d04da4002c070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 710682760 1250 710681510 710681527
    0xc0510051803070309060e04020a0e103c11032a010c0f0f030204050d061a060d0614040615080a06050301020d1a0a0b0d02031e01031a0a11 61
    0xd90203540c0c40462421203030000c010700e04803039045070700c03010090b4005014524184074464115455003820761046d0380031480c14005140c0100004481c4102c2846403817112800c64450f4400d4002c1c14801d11040208858900c00b1400b080085046490405003840711800d10282c1da0301400e100e136104140034003d1481c20003032150380c0c0e400841d2049600300564190041c0100704100f446041f14001068551102085c0c074404080d04c44910101c00b841050300420044c010740e1614107402c0302440d0700500204850f02d00340c400007103174000d80008a81090b00400d44032000103d6030004411905402d50300c00458000307506100a8800f18094941e909440940d40002c0301e2040c010341e94403a0300c210000614986410000342641d211090300e203040750f160000380c95100d400070810b0010b2241129444071507454140d6012050090034015210254040000381d0701c001542c040c1a0400410110003230550386920b40410803500900707a4401044986002407000e09052281c00c00d84445074141ca81014080c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 710684010 1250 710682760 710682793
    0x1a030607050705150106020d02060a0b030c12070e090a0b0601081302090403020a0c0902040e0610080c07062318210d09080c0604050f0607051c0b0d150605010c05 71
    0x610b804036040e00c1210f001c036890001c2d07901c01501900c03141e4090305c0c1c014080b81c0000e1078a400a8a5480c0c940e03d8005d2290913035500080013a051441980c0c0b2601408584a1050800b1a030f07034000b400d84c00d81d5008001c04070001040c5180820b20a01601803161501001100c2c24042100c044c8045420641d4900143c1740003003000c0e0384207100e1b204a035040042c0d0323601c2c000700001c60341c0008825500454284034203844018040d42c050700079640317001103401601d00241320740d0028205060a44001480c0018401c0d00d03000038030fa14004109400300c840d012001001403120461703000d168054880200c00000d0b2020800b1400400c5504c82140d040143c40c2501c0c0e001d074400750030009400d40d180c003c8800150013102914114683c40007510051a10707080050510b07510500040c400e800c4081040703111500082600c29800f00c2c5507500c0e040c018107000410052003140d00715135000f000001014204030455006955400c2101000c1c050f07a41c1d0340c0015152080c100e44000d119801a9051a005d5540c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 710685260 1250 710684010 710684017
    0x3100b07230609010e0613030503100b040e01050f040e0d03050721090b0105220209061c09031404030b0408131a040f0605042610060b0d1a03060705 65
    0xd4141420901c00c1c0203030880c03295442038aa072400ba000a420070150344030a100b2071119113865030241c4801d14101c00b440e0613103100d00c0c2d00102401000710202d480c1c4003400154034040c080500710f540c1d1307564480b2400001040d00344100c034480d02001166151504103800782003820150400204180c09002405402a0600034600c10800110040c10b1a46003094401d0b04040240c89200080c0d402c85402d26107520300781600490300030300104a422030141401d00c1001d400d90711817100161240c201e40c001600c00d00c614030280c1d031020300b400022100580b140e88800f076401d00c00d840700100200c1a080a44590040b8480540b40d07030101c500103400300e50410001c0442e12051014607010a4035079a9940203403a00d51244810310101040602100740c9082d44527000c0d1a030350500c41d040c02c1c941144840d800104400390681040202500d0700310340c0c001c014043e43c066800c08280001600c40e0344100e0b094005142c140c050364101040001032040c11100529444030203000303000180e4404109913484d0f032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 710686510 1250 710685260 710685263
    0x20a0615080c0f0112020d0b031c0206010e0405150702030a2003160c0b070b070311190c0507080718060f031a0924092103070309060209030706020a0302070b03100b07 73
    0x20120f1186010301d101745c4010004001c1040d0001001541c40d014980340159084860990348601441520b0003600062460b04480880b400200260754a1070708030300f48121006426060001101484465a000b101034a494403456452000c0078145120488903196050200b02c4107400c10000030203080d000c4017407041124020461810030a80c1e6083c0300d60290302050b41030b142c440056040c04000d584c18040e480e100d014101c2d0440c1020b00d098100ca003000c036511110402c2c054580186800c110050104d1001001c2d1007041d55a10b940d914110f034080807082252180f551301d0701d400800c0750082c0c000c140c010380b07811a8207400440b8064050814132000540550041d2040300319404411140036006245095140d054060505020003154905201649031240d569002c26010141c61804016603a0004181c600410700c91807600b0448002c0c49151645c0b90540210700003c94500d0300000c9191010344a98200d600c0315aa481c000482c071301043d225050390501c0d0407010819119058090041035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 710687760 1250 710686510 710686517
    0x9030321090607030b0f0402090f19060e03030c030f0c0f072c041101050a09080a1406180304050120030307180b04122a06020a0615080c0f01 62
    0x30080415a1a0300903094240140900210104601d10300305112a54020300c160406000da02250b100064981400790945030160780d010666024540d20842088908007018106d00788078051b00d0b541c03251b81d8015010f15804180340f100b0004030382c01c002088a000106503c003460402201c04a18042580240040c428070722460800c0141850f0a11605004000c4500f56110082c2c0140e030021841107443c16180c10f0443c41030400011620b540c03064641c04500346805941da0114840c2562845481c0e0010800b40c414030400f24101305d44241c0005640400c3d00494041c0d03528080d914094503041c258812240c0c00c144410441940581a0491081c001e140249e0040e060503c0c032a1650b00b0440d80540003912240c2d0b051400700350134034048003800b224003002e8079090800400300c106405450b0018000c005002e01c2e80e19010003114003940b100c0b41c0441c0031409640d17543c1300a54450300d4a8040d105a8070b06011540d4103581000706204450341840608503109505040001c88a000202141071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 710689010 1250 710687760 710687767
    0x5010b0c030706151e081c02060a240e040b0a02070309140a0b121509010f05090a0605060c101a01080f0a0b04020f0d060503030f091c0215071208100902090303 70
    0x55050609903803e101c812805c129130141c50314200e81d280c02040805080100c60103903110031515804200b240c0c1c40069000041103408003444014010380381c20104114802240c1c40c0071649510031800140101d0003220404103640b82c0d00c0d200412486600b01c001c0c003003400d0300b10402c0020303400c0303041d000c0c0100001c0411510310f99035000c042107580000b880701168a440403c1041200620080440b0100142da0f520060740c18106590901e100ca80102446006e03500d0028034071002d250014000740c4006801305450b00f2040c24240d81c0d4004203030b401440241402c4044030680303100001154000740507507480c000c686800d4180c02c4c041e40085c2c0441402619540c0040301c40d110350005000400c41d001003156501800c41c64082100c1a40d04054440e0f00100000c038582031b124010783e19050002c458103180303000b0071100c14001e5628128000d41100c650b40c2c8c00d02400070030304058a0420300520303002400d00e035040030403500700600b101c035454001c1070038006100426107a400b030010b5000c0941140d25 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 710690260 1250 710689010 710689019
    0x306020a05041d060609120111031303020d030c08220203010c0302091f120c02011803050306120c060a0302092b02040605120d11071a03011d10090f0f090f030305010b0c03070615 78
    0x321032b40b00700ca240d40744030f42c080c40d05010154108080203030854285010020091070040003050300c0c10180241d90503203016861544056800310102c40e005078010020000090b2001014000c3d412140d05144503265641029100c2c01050300d54030003002c030541c0d9415041b040b0540c043c0c000e0203424544401c640d41d540c1c516a5490090000c0e0002d1030180c2c035125242d1929104010741103101c041802c000303400c0b829412681d0f440c2c501c117941c00720748075080140e210464100840c905500c110043c40c201c2d81403542424088604003500240c807802510203210650f118804e0026014441813200200c0d4041a615244103105114804403415690b081d00c1c4040e94a403008000d60000003144c14500b2400001008004010f22400c101c240750801c5002d403a00c0d06049403450380c8210f11840101c281c40724543c00480c2860b920502c00c2c0c8400841c1003041104500f400c05070440d00c92800c5000c02e01c0c000000c1030100040f03050b1398015015000451030302e0351700d550341009084603140240312008002800314 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 710691510 1250 710690260 710690291
    0xb07030c030c0813150c0c030809031612170705032704090b15040606020a03261608010812071106090603040f052b180306020a05041d0606091201 64
    0x20740200b8030300e604e03050301d040039074100500020215080030322581c81c1013400018091400c110403203070412700a6486101c0c28000c40c0c1804401100d80c100400403900200744500c05010b1071440501544000c00e200c032000c81ea5441038407d40c1e00140c101c2d8010b01200724010050381c0f10042e007080340c2d00c013400300d10000c01c045019100354040c100d50b144020820080150002100545402c804560078417005140080c082d40700c0400d200d028003040000302c0d854048003d03030321100b0407101c04007000360040d252074001440c1228031800f40500044045000080c00740c40014010030340f00e04a0400c91505c10300d5900c091642d060390150a0304541d0034040c40c030b2166198006140700d14001e10032181c00f1902e502c1c1244c10415024a201e006486492005400100101c4106901c0c04507081501c00d0321034542d414a003141c19940000d110718000140101c3e030f50b50010280c800c5070407104050501520903c0205405142210650740180c400d11402c0c0e81ba190030111410012072500c000500d0805926818 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 710692760 1250 710691510 710691517
    0x709030209070309140a0c15170c190906081519030609021c030e100c020904061e060b0d090c0e01030b0708220303050601020c1905190b07030c030c08 66
    0x90b40400e566007000707428010304d0310781003849110943c05030205031000d60740e070010544a8000c0302412000340c5092a2280c0c040d82856442ca02480c403080c1c6c8d01e1801181c050a140d210b4600c60800e0141e5020400c030103030003068180d0690f42d8a440d40281999814003811038503103608406640170f0001030200301c040703003c40248405103000b01004a0395400900521035482c1c0b030a81030380484d00c1c5c010b0f0707401d0100f580614006e840307290407a0100100c0c030441c44103e03a80610324070041e5101081c42d06200c10488940c1c03110350030100002c90b80c0441c1e210540280121400362080e1041e500c0204518020711039a94004000544a410244046502c98138041c02094090b00102c07842c412403000d000040ba0403451440d81300303101c004c0144c13034040c090300f144100c0f4a10050060074140c80314042000740c0c0c0240030b126528000640000c2c403484a03101d240158501511405002b982c0c00c03400300709110030100440c400c0d1a403210380c240c41c040c0c2940c0e0865130a03440100907000c00a04081d03010002d40d204008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 710694010 1250 710692760 710692771
    0x206063f070623090a08010513050105010f05060f0a090f03030507060b0a35010c090302040501050105030705030c13180203040303111c0e01020d02040815061806090709030209 77
    0x8544501842141151900360160442d80500c01c01a1410a07011125620511004507110000e41c4514804000c1080d91002c0e40200d4540d50a00f810400711520710300301c4101d01e80c0605c0003800945d984608080c1101c04a002e440d40028080000d01c10250301900103040f14030040ca41500c05030b56842c2e000b080341c07029030401c60000d800010303200180800382c00b450820650407907031545400c0c40c003048010042d8000c42c0250200940e51110180130001842403000f110507070009000e000072001008081d05180d000491046160400100ea1544508207032842007045031950785c9503849802c80c049160b0001c020f008a0041560804030311010002d15100e0b803420480310140e124101480d01500741c490007061003120b40014843d1040c05008401880201d60350210002400d9428204250191056640000d8998000280020182c60020b05074071850b901c403a00c4130270360b00c402c0c040000d0b01000e0b903000d542c00c047d00404980340d0700d4a22442904076006080c140390360f40c1d0f29804180403d00480c0c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 710695260 1250 710694010 710694109
    0x30a05010b0c071a07062c1911010909021317030301080613050c100f0f140a12060924140a0504052a0301061206080a08070c08120715020901020606 65
    0xd850122034140071044801f00c00c0409084454080b103c0c8802d542c0c0d260801512000d51040c0b001d01036405580081c0140903454802e56a0b00c2c22801002c0c8807200501c00d280141c1d9803003940300c0c0d940340c010040c1c07416207003024007502a40d03e1f1000504051640090140c600340038407500c0d40c00e01da903010100c40d840c1c0c27103544891030148440000038010109190151047c08400319402c0180304007513040381d103180201d042100c07120700705182c00d40003048280c2001b614140381c280203483e01084003084400c50414000c800c421782c3c0d1a6032403030016604580b142d42d0041c80a0030300b40502e18168004651081c0d414412148501000010a0340d003070030045a080340c4500040103105050388182540b149000b005400d0090340d1500c405940e0724442d8001c080d00045000c030b800f10402200c4a601c40c01044240c0451389000e038032103c220499808104101d03514107041c01241c640072039600a441d5024016005000584d5032070703090180d015211000d440b80400c101390178a6250350703400c0d075500008600e1070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 710696510 1250 710695260 710695301
    0x40f09091103011509050903040b031017070f090906020903012a0e1305151002150105010c050a120201020c1b0f0307150e04021201030602030a05010b0c071a0706 71
    0x800710040c001104001d80280d050007100e403442c1a08640030340c1140d444600001d415500c1c4200c0c81d04500403608130359107144002007880b1007000808146021342c0e03403401daa000801125886180c0c1c5150030310038030150300e099200411601d0003540c8540d145901400c4058684a502c400003801c4070300410a2031007065500584c0f07007203c0e440a418210b15055070826080e095020000242801040c43d86909010380701c1c400240005018140206a401c1c040c008400154044102948a204004551003244605d4000003220361080854480240d041400b0b00003401198840400003550786a40340c2c250746d000c0129001060003004980101c820075000100c2a026600801440c20698420103100e0b40c0a144144000f44c010b0041000003213250800000c010000408100a401f0701c3e103000c2c030b03518150000001401041e4000714030610030305904003d640c0c0c030361a10108500403082150301d242d002540501400c1c0040c2280f04d42d10194102003410f1800b19a20f0006450f116104421010040c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 710697760 1250 710696510 710696513
    0x92c0408030412090b16050717060702060901090f03050a091a0702030705090c0301210f06051603060e010501051b03070809150702010e060702040f060803181f050708040f0909 77
    0x40070260f07198041443c101c2807043c60041100703c00d01403041045c41c03100e030240e400c0301081030401040c0300421008128454030003610302d03415101d0008403440000740c000d110000300c8507074041c8241103c451748031003031745c2d1104615181120b039900700c961550305200d610800403070702d0100a40c0c21300d0f141401b02c03203c0d07984d400d11f44185070801765198003090003010a80305018101c8542400e8130b0544d05074140c110b040c0c0c2c10700030403040080042003014082c2c01d081e002c1602401542d4020610030f000340c1c8200390844034070380c0080702181d0b81842008500c410100051007990b01c030314000c10026070301d4042000d440a00f290543d08540c0148402c4441a00003d11441c590424190104031942401941802e0505540000c0c107011104000c140c40b951001500304219a903a6018100503044100200320a41e201d1082d00da803070b0301440681101c1c0ea0102c544840b2803521405540d5001070848040452a000c03500948844d00142d90450300c1150600000c1030b0700c020300c1e5188005000d00c0c81d021030240b00a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 710699010 1250 710697760 710697773
    0x30b09011d0f01111602060c1c02060f060d02150f07020307090603050706051c0203130f050703030e04020c070902070606170a0c15020312070201021b0f160501092c04080304 76
    0xc80c841d0300f4940148895240c0c481c400740712625254042c0c7d21141c0c1d07410302039121420a0b03000c0340d64500d41c5260348450f100c925800103805100304580418105140c1303030748042110700c03149108000d501800744c81080e0744c92800341c1d0283c152642450b00e45030614029600181c03c016550700030380c0c1d00e107683d50020401d01204100d140014202070070150300d001c04101c01840c40b00c5040003428103c40e0004040350030085030f07034901e20311243c124910070b81d05801440c1590700c40b0324922040c0d0020303480d44c0d034040030303881d20f40308840c0011035060082c80700c0d52a0503607090194000280c00e540c035560342d500020340042d0110460119450080140403452490701c6c103201200c0150b00880e1001c001021902c11a5070004126002c04c48601e810740400da69141e0201e0184c4140200440005000c680d64645920005a40403601550800340d81e075904080300100c1c60400e00740315150001302040307400c0024480c03030510181a1600040482c012840c980e2901310700d0f14050308c00300e412050010402c41844007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 710700260 1250 710699010 710699021
    0xc0c041d0a08071209080304061d09010902030f0106080c0a08043810030206030c1b10060518061c060920010f020d020c0105160614220c030b09011d0f01 67
    0x7805d201074654106000240e490250f40124018050203141c60b0010850102925404500c02468101030b581c43e0007400700a500b050302c100760b800511100108429000d8415984140c904051140c200302000104407408070001d0405c0c1c5045c003404a18500009142c00c990400742030210345000e81074a00c1d50020900d207401403161950703554605061005a50b080d003100e400403940b8403a1501c1e68044030f4001e90024110807400c50511581c0030450501081d42c00a008441c400c0702d02407286148500c60700c0ca108021078240da80100c50324080400080d8400c10640b0407030003050000703000807250341d41038032003404025a06800c04002040641a69112124a042c81c50a20140c15103840c1c41d00040e40d1521340300c1e8502d05200d000705440380090080414420b0894000c0c0e818400c5a050004504281000351380090002d4062100c5900301d0540d20f0001100d00c0d07000b0f9080c1c00c007a01d1512000301060015140440a54842000000c1ca0000c095021040d01280018243c1000c0c0b40708140d08461 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 710701510 1250 710700260 710700293
    0xc0201050916080715051303030207081e0622060e01150603020a090e1803070f210e060304061407021f140610030207021c020f060c0c041d0a0807 64
    0x142c0800500c010350011904034100d0b074508448403100c0603100030680d0140507050004220b06400000081895400941c03c0c04841007001910750384010801129813a540c1c441821909070700c03035808947c2c0c0e038a26000c0c04094090751181304003c510a036441c8010307103500910207005e80e915050f408150b090302034800f40091540342011890300c01c0425000c3d048048620851080c000980f000802100c000764040031017141c01e0094981c2c0d0303851803404550741b004a50054808407001c00306101d10140f006082c1e0074003c2d203a02c601712203158040801049600061003112215120a101c1c110780c1d185078072140c012107054014260003d22211040e0340d440e86456901c50503414140c2103035030001a0015260045c200382c070380c03160b6048aa00d00381d01074071441c54001d401c03003c1444649070361210503000303a403658800c42e0100d10000400c0c04112107409082184905038100c4251a2428034080c0d011003104020340f14044110b282c03001c445800c048500340140c0f400c0b100007030715504210204500c0c08051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 710702760 1250 710701510 710701543
    0x40507050f010e0d0809030a03050c1c0c0b1b0a030906050f06100c051c02070303020f061905061906050d1401061b0602120c040e130b0c09060d0c02010509 68
    0x2041401c0009040524041c0014094000480d0b40c400f03004016003250b2a000e0094200d50f0b124100d0300d401080d541c000900c55129001e000454007010080d00500402c0c04101e55682094091130b45400d08040c0300580b9010500c109141c4452030f140c10074002c3c0514400e5501c0c0022840c1617070030020241e540c020121000c0c0c00204041050340c1d0745880c0c00c480055240d181c901150221442c11a00c0d015810034241d0085199020040b0002c1c1d0014401043c0e034842d030300355075044000c1100103a980c2e00694043c200e00500402e42c00304186140c2c0b0a9a00020050428010b00090000104400300507009100080c000213810760f0825202d00465128a04200c881c2e00c40d513141610040c81c440c0c019682201e000c00440400e000d100668040c1c40d0050b0700780400e0040d90920620b0f00304958410710034208441c00081c00110b2805401500049960304480f0f0520669501041000680d00c403500e00380e8400410302c10408141c110744140d00c070030b50041d00005030780d041c0f00200610f400000000b4a407403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 710704010 1250 710702760 710702779
    0xa0504020303190e030f070513060e061c12020d090e01120b040c0e070206010e0a05090d050c07030501090c080c100f1206050310140606090303040509062704050705 72
    0x141c070000202d840c1d4405000e0350f5842c4a010766000c541860302e02c22100c1e494811b00700c800b0040900824113030b00b201d00440f91403002012184102d01544c4952144041101c0030303000040080c24018a2405070200513450161100c070265070741c03800c203d0304203424001a0301070034606041d583c011140b00d000e005202203d50b959031400ea04030a46008043d4014900c2803a01c0106040011990750754000c3c2c03c2c001d40b041c201d460440f4000b940c2e001c0901c1010328140700742000c54400c003090b01c1464001c585950207007000e8110340e4001d807015480014141524400e040d40080490000c2c0310307009803107100302c100c2271800e850600c00c1460a0a0a50810301c80d511120500c00708a410180510084015041610ba0007041c459003400a0034264040c503014000d2210070484081960300134981c1450f030b00382442e040d4940300280701070ba000d00b40210741c2507481000148031515110070782961200005054448016000096140c0c041ca216100e000e494866001c0c070041007014031845020341001d841e032002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 710705260 1250 710704010 710704013
    0x50406080a02060d110f0403030816080106080708040825061a0603010e0415090302010f0608010506060f0706270c0902162402030c0904060b0a0503160c290a0504 71
    0x7014814550148400c03940c40e9019002c00c2c1c2d1741c2e0142c59107010308008403610360303580e402c0141c511113080700c0703181c41c8682c0d29985240c0d00b8000ca4109050321140e0b5140104ce6542c05415943c5040107801a2141e44040c4014441e2450403410f00c10001000b810b1036400c0c158502e0582e00f0ba80c00350040d1000300c001c01c1e50300302040d2102020b903030440e2590901d40c03859031202c4c18104200d2010101a2040e58101103c01c01419015040b00b41412100b04041195540e2500241c0c22188145c481c1540000300300400c0300d800580002504615000c3c50002851200c06540c0242e003d01e0080041d032a00520180381d820301561844030b0008001001d010b5142070403101300340e40b4402c503500d0014522181c0d2100c0800307540100c411101c651000010842d40c1c0d0818041a0090b80c1203800c406114070300b005400706a00304448103440d00b100c142e07201e03a8295110100c038110549418116034007003208003003000d00460501502d04660300c2204400c034070414003240082d0300f254001000c0e035009074140000d110 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 710706510 1250 710705260 710705269
    0x327111e010c03030b1323010b0912161508070801051c0f151d0a1104020a1e08011a1c0209010203040f0308040504180f1b1e050406080a02 61
    0x1003544400d00c1c01d82852005480d054000707040300e40710243c02100a4070100e0100e806540200c00c041415000790181413003c1e5440d002d180001d004958600c1030902000340b4605203402641e810790301940940700e1205000c000352001c03855640c04204840e01c40c120803140103802602c1c01d0b802031441e2803c035402e5814440802c444114240c0104c101d250454020700c24000c20410f11942168040314a218001805800704040c0400d0707100d038180c2e40900105040001c2e00010f104400c09d5001c0001e0300c4052424042000079000a000032052003c4c217403940d408841c0704403540e018044c103500d0320000c55050524056000074414401c1880303001c00c02c520303100ea260f9549441c0c1c0200107000301580e074644201c0101d0035030007260b0000100c07101084012040100403400f90095400c151030030000e041003a003603d43d00441c607040140c000080c555050300464074004440310020540d9a540100b29680c0c1106507101d20111060303407000394a600284101c4c6403d005150052881c08028000d4090680018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 710707760 1250 710706510 710706559
    0x6020d0e030c070b0d06240f020114060909070b040b0d06052e02010e101d03090d060509030f0a020a1b0f060e030a06020c0a0b06150d0507032711 64
    0x80c03110350b2001c00d03090304141003600240301800c407052a55403600e0701c4811011f07140e0002d41038200070404203031100442600c14840c04011141c1701a040c141c54683c80705001d900c460150881c00316000e900000b00c1ca206400005000038200354071280d544030703805483c9601b250340e55001144645001c40515440d2500300e1030450120a0119400e8000c80240c00f050780104071580c0d440c1e42501a90b0144003094407075900c62520034002896401a030440d1881140c0c03203201c1c89070755a60000041c4c002102103580c9070f02480d4410380d070710100c83c9041e20031010400c094006524007401603104600d00e0741008001c0ca00121494840541c44001d60304001d40c845010051340100701c02c1013031142c2c0750b5000e940d042007850340d03964000400b190340d1181030080c0b0361654081e0009a80c0709500c44041252400d0441140d81c04150720f0345128244011140c500000e0301e0080c0c1010100740e02c40005c244101030003003840b0403110286c3c1d8844181401da01e400210104520540703882903a5041e10408e042c072a0f201d24 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 710709010 1250 710707760 710707769
    0xf0604031e03030f0902060901030e0106030b09030403031404060203340b06190302150d150821030c09042c0304051008040f02010807110604060b120d090b1e0706020d0e030c07 77
    0xbc64280c02050480f401425280e001811042c0030b0b40038041d03510004001071003502e0290b500c003800144684c02e070080504c680e10800c0300681c41002032180309800a21501d107080e9052004505180d9030140014265240c4041030701d2104c500402d115561829002c1d021a96030801c0003980106e2844e00082c1c1441e445561489200c180002e200140a603141e010505110980020312121912601c81998a140300c5202c20b01c01c9040e041c00740f40180040382501d202e000e24207042481d042c0d000f0140406040c6080c0481d00a05c4540440201c1015000b007025030220040000c54a852421042201c407004031560f4009024410080c40045880080144111070b02801e01c100e40b512070315012176240c00324a00c4410980602d8060000f00111a00080d81050781158081c1c104000203846586560356600a680030881800040080c0c031b00e80c00141c0004050802c18010725040505882c400f40d0140104842c0e6a40c0010401e40c6c80790706104402100551a00442c1002c0201402503170b40e500a005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 710710260 1250 710709010 710709017
    0x170709020c01060e1905010501140304080a050903012a090f091104081905010506010e030d21020c0606090c031012170a0816110c0f0604031e03030f0902060901 70
    0x24201502882504044020113030602d0600702844c054610400384005c211a034050340303040c0800000c20350310610002480c0150754140d035103161a9907507002141e40c81001641c05016080c055a08541c0e02842209140d080c0e0110f88102c2100c1d00624a140c42180740c503203401c1c0319600e0401e1100d06e401c12100400d03245962400209200c0e4080308a102d40559405a032103031250385000f00b40c540c80400203c00c0f0783e1050000340219210440107552469020141c20380543c40591b06011840c41181c03100c00b80380781e040c84000075103416045042aa03000c0c0703140142e558440d105000031401c00111086c1e003d001c900a050440c03d210403405085800791040518030f200340c8085805221a030491064800307484001c4503665400244090030103401210a0500c4c0c1e058040320314000b80c0200e0742000c440301004080c00b0713215956002c102c03040b0040c190303180d042201030001100081c1c105000c4043c600d0141000b00046246190080981e88202408904603061003404001612000207a8410303c10908 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 710711510 1250 710710260 710710267
    0x30708090a030206030420010203030f071b05060106020f1216081c0513110904030801061b2907090803300406021b0303010f05060306011e051317070902 67
    0x10000760000c140790400b0f540454000240300801c8020310070449075103000364030310030640084001a40ca80c002220220350110400300001c0c2894864407041d4045422401204020002da0f100c140c0f07001e400342c1008015921a2001441c40403041100616a04540240500d4101400c01d40c07410001007a000810b0800d0104402b11400088220711802000d065402c128502d8411072822281d500f101c8203030f40310f810101c40c0d0f10b1039007030402e80c5500c00c6030076489a44169107009000c4448481d40802c4540000b200c003100c40000c3c070800c1100340f015903150780e009090f40480801d6101824041c160105016801d042001041800306c15503000402d0b2449e202041002034013807030012240c581d00e445820f24440304010420186034080d10070040f41411a48841c0701d0060559aa403201303000301480050402000c20051400308021540082c0c1858914081c600c0c4011083c01c5140e03090184000c903074003103400d0204d1128a01c910004001200200102480400f055178039100b0a00503002c4603034000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 710712760 1250 710711510 710711527
    0xa0809040c1b030e090a090f02120307080c3d1508010c21060e0423030301090b150a05092809020d15050907050309010f0c0509030f0f030708 62
    0x20100a5040760408599030341030b802ca80b5000386003805800300d442c4101c41036804100c4142aa214040c50503602021200c90301e2042e800300090410f603548820360501c42002094006860600580042c0460400420b581c040c080c00810061214803004a40c50f01004150317074181d80b0075032001e0b0000f140c0d114005894000428640115100703901304505d198200910911040d074840721010302c0710340b08010141c5c120341c1c0c0d099100c251040e500c078905800072040007060114120546960115030344001c0c4026100c49084400d0030340d0002d074402400182c2d50803120075141415080d4045048904600ea86000003a03031018019004004203035018a0a034078404441d600d400000c02894240c1c3c841982145507903a0001001e580500c0d240107815062150b5107096200e03180d41c1005441008060080c0c1d9a103500b011035290f00f008010034015900c504a61b03240040610600c03001e00c420740d0700c0540d58100300381454905210411603002d00c3c3c1c01403480c4a00b030a40441921045548400f9096490854 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 710714010 1250 710712760 710712767
    0x40605070c140d09090209010c0b090a020a0f03152a11010f0b041a01020304230612010801050f04020306060105090117010e01031a060906040b0d0c15020f0a0809040c 73
    0x2025001019020042d0100c001e00d440014900b07480d00c42583c6100d00b054a90440f0810390089401a90114503c100d0703140000c0e03110924264407400c038904480f041141500020301400c41544195101404402d0500030f001d0380030780f942d16003050b0000c00d01a503003410441c4c0050000a04406c00300b8110310030380280d81441640641c54090325600248402100034890310300520001007602d1149280c41c100900034a1300c03420004100c0d1050700650304161400c42080088518079001180320707101c00c285c6d50b403283e4514002e8002c00503940036020300e1798144440703a400c440c009401d45020341e4480d0b08100050342c0c00545a98448801e18046e0786036030000d001602c0801805542e0924985068004140400070150301030480b03004030021011800840d80500d420301098035402c0d00f003000140001c0d07550071b1581200f00528406400d02c0c1c035009403600c9580b0f0811054000040e04805850000040c1c3c0d030400044030005201d0016140404c0c4650316241e01d880346070b22aa0280d0349401802031842e00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 710715260 1250 710714010 710714027
    0x30803090a060c1206050a080a0b070c0516032901090e030d02122502060a020703140c01050709080f03070f030903120906120b03030d0b04060b1201050a0806090604060507 75
    0x42c444001d006044a0503c050040496a0001e02c501032503d003000031146800c6008408580000015129400042d200c2e1400010010000c1003842484014503000410400c50103034004948140c0da12228114600044400a521040240c1c001074103044c2c07000c04220010241101c00c440000a034900820040318118015565088203c600c00324241200d403000e440210710070805503100da11084000d401403100481e5180f100700050b44808005001905030b41c0c0100349450003820200c1035441c0d02c0099180c181e001c0090804265140d400380581d01d5044820f0300040c5c003402c8080c01c00b41070914501541c0e4011010003400d07031952003400320141805030100d84040e5030001c0d510a05015100c901401300310a500c81d4200090111035552840400ba108906540300028003845c5000068142c49020700001a4615072040d9500b5001554115440c02002c11400e03100c91214507614120030440180d80c103502c411659001981003001050004c6400c41e070040c0d026800046588a400302119080d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 710716510 1250 710715260 710715263
    0x20106051e10030605060c030c0f010c0f141c140a1e0b150708030412030b09040b07090e07090810060302100c171b010b0a050913060f06140108010b070c030803090a 72
    0x6d0000400c1044440080002d241003c100750488030f80c920076808007030880c0c42e1110f07803030000341040d064149414890f004601c0d00760b081c0d801040c1040c044018115071009010f0700c024995950704c0c0203e6041203032624180c0d0252400c0000c01041c1c01962074500501c0aa0b03048014150b941c2c0305600940d40c0e2002c4401800d604002d98030349900d403d107008820303a8000d54003641c601f0000c60103070058500c80d0042c1040143c015110018a86942d51351640e01240508010144070584001040603803e880d0708610403201e5580b140506407600320350a00b0000070049080460b81444410f202586803004010f80100091900600c00300c40e5041241703040e2014800c54605031000100c00404004c0407803490004458140200800e80d0310100300080382c080c80c402c1c40e400001c2c802c00510001d40b11180b00042c1d901841e40441c00c01e5002d034410b0100c1c1c030643c1168040707030300c100440500e03075174410b1000e03014100c00d24043e45041106d4446440006040c407001b40029030000000c0c004c860f0511003260b049 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 710717760 1250 710716510 710716519
    0xa0b040608160305070e0103020a09020304050c101d062a0f030414090c16110a0503011b0f0f1d120102130302190e0a0e0f0f0d020106051e10030605 65
    0x140c2000c81114842e50711448151143c0c450ba4001241020180810504a035402847c0d02c0010386400c09202c0031390030042084d2210f0040d08010005902c51000181480a259660b04400c2e648481c0202c07842c9500000d4901480741406403121420010303480c1c90080c00465203503a155041c80c0d05541c41d20410011401d120301000c130700007903980000ca81030303110f240c412a0225031a9481e0a0850054000d581c1c2212050340c40819000104605000e0001c40000c00b401e80100d2944840c003103401d685c500902c0c1c0d6900b41001001480d00d5500c10300b0074000445501d4082101080701000030103000704a00a04001d0016900e00c840a0351a410780f400c0c4008210000e6484d110b1505041081c0c1903c0d200c1030b03010f02c003103500d525980e0001d1a65481950340c08034411000740c9901c0c080d90020250482004981d110342800404044000c01003000000319050090601c54075001c030090954050354030407030250744224101600c0c0019071040e011045015a5441001542d45500300c01a000c1c41e88100d400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 710719010 1250 710717760 710717773
    0xc06030c0c0618080408010e010c030b0904020906120708030d0b010f0206041719111005070f031a060304050a12080f07120f021602040e030304030c20030d03020d0c0e090a0b040608 79
    0x1040c2c8190408203008c178069000700000f0001c424168243c58415941c00d900005500003c5d0040c03905a080356040103020780015003a0000304203040c5007841c41d070010b5009620104059000584502687e40050350038644507090659404004c4c4d5600030180c4001e101803000e49021a030740009905030b07800c1505103000410f0010709500c1c094a02c6a010ba03908002c1c0c0948240ca603560540c40c01143c4c002c9600f070740c5e8000c0d0480001400c40080c81c094100d0720580350f510090450b29170321a0041c6014078000d0000d0b1224600910302018404094a5010288100d0707004000050b0946030140c1c0c8c0c0446541040030000c0443c6c0000c2005101401058201d10b00c0490f03d4401c0c207400d01200e15000740b007910208000081e030f42c003080d40c0b800b04480050010b903406c90700c0d42c00210300402540d28240101441c5041c803032500c001a09161480c0d8048000079400b20b41420744481c540100000c83d803890400b4103090034490085001807100414054009480d0b0404451548031944601c004010b0341d0b050701c81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 710720260 1250 710719010 710719019
    0x160b0c302512020f16090905160303020d1b1a130b010803030105120f07090b150a18120210030e0a0803040b040506180c010e06070b130c06030c0c06180804 68
    0x190b221062880a005201d4a040003080d108001280c40c0e201e408071580252091401140b0005420100b0088840d4021400000086c044c05e00c104409140f00760081e1200b2000010001d000d501c980f50f42584050401f8245000300b40080c0001c12a4141181c980c0c0c180d43d02c201745c4002609400c00010002c0045000010701d00c02c01101843c145c035011529106002100800d50303503a4125500380a0325504891000c00c00503d243e4803811031404060950b4807480007403c040e50640e048212001c02090a030b08400c0c40c0750340036071501400b51800131540d04005110760041005160f1a84042c000d043d503c00c40c060802104120f2542e003580e00c600300c03075524034007840c01c0260782d00143d070b0032a5544100740114030300d1040107400c02c1c2d030380c8d03e0b074801000c80b600d801c00110b42103000075008a4002d00c08000360b10210308000075441c41260140e50810100300e440c0b81c50024840c0796402001007600c4c3c0000c0032503459004c9078906c0c0c034940010022902429981108011580070600102032100004000a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 710721510 1250 710720260 710720273
    0x7170f04181d0708190311060f10090218041d0307110310050903070b040828080615180a081509070e1611160b0c3025 52
    0x103000301d003141d0a90800c0400c0d411240e540f0b07954003030800350303800c82040d28000ca0740102c9000b20322400303413802044a8480f982d2040c00c040c0203a5210310391544150401c003010001002c488001c0c203840c1c40c110b18210b1140080c003c0784284200d224803c68940200c201e4140c02408010100710009064030303541c0240d441c0c004064440409000c0c000d000e03010540048102030300c503d034450184900510b2801d001603585400202e13008004686130030303051100e58040e20102032030920320445501c1091402c08071603805002c0b24401480360f4030030712518454800341500700c010707900081302068a15041c0d2a480e800200100d1580d08512810300c82c00306a20442d0903454020390041c0001400d5891f4240c80700400e4050b004201e82c54001d48044191a14076503105041126900312072030142e4a05d0440100a02d02101703440d405007407088400b04074003a00c6c800c1803203600c0f20350494811494103142e0b540c00744c0d041488483d0402f10600408629405586282141400c8080302c20040b60700c48090303480c081 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 710722760 1250 710721510 710721521
    0xe03010f020424050306060f120f07030f0b21071208120a0b0d0803042a06030f0603021320190e0609030a020f03030d0f020301091107170f0418 63
    0x700d2a030010700fa280300c0c1082401400d150a0314107640e1645155190810300141c0d034009000d60002280c10003400b80b60f41104000c9034055100e4044140c0ca500b002203008082d25800b038078180d50301d8680101d40780195951004204503070004404014a0540140241d013892003079842950030340c0303035440c00400300701d01c44006102400ca41d000d4050030b43c0351440110700320b07168102c18640042580a0900c0410390300c030301440c0d016100d50b2242070446152220710804c0d442c0500807854190040c0c030144600d0b50180128032041200355010800185550002541386a0594400000550b6248522011000a1501d003450042e4140d02542c0389c00c0d111245401540c03913960000041c942030100d980c140f910900302c0786444030042c000d25003840319401700405001070310701460345480f0070050150500514000c060841400c41c00060701e9616001c130076001d4440c445814115032900700640300025020210b50302058401c4c882c001d40b00c20b00c4281d50f0340c03a4441e07904118030401d5415451074003959a40c100c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 710724010 1250 710722760 710722769
    0x7060828060302150a0c0204050411101106091501031203111303030e09010303050702041109040911100203030f0c0310031e020a0603022a10060f061701030305030c0702010e03010f0204 81
    0x20000e400b405402903007185c1c0038100c00500002c0300c201e10f1038003610780303500140e4001d40503c0c102000c01084400050b0008201982e20001c0f8194101c160684081808056400030354107001c0c206403041c004103407402500500008040e0110352164400c124845d9100743c50450450703050559038040302c0076860320503031103103c103d00040001710b01d0103150600300d10503030480b40d041d1035203030400629900708005080b01d01d645204001707090001e054070b640e0b5402601a014003d0b8442d08000b0326400034454080d5070303195100c0541d8010000c1c08004d48841900700c0d485038075030340c0d00f50f140d403110440e0344040c0e02c05500c042c0840f02d500034004001c0310041c00f00702819108075103441c1a42d940c1c0c0e00903010b03405190882e014443d906803030340c10290381c3c40a29101d9895032105850191442c08000400c641c03494202a4540d400c4100034040c10b0340208000050b40c90504240010350325590740103029100060045ca4400404181d80f0704590040b0165040c440300200288801000300c5111402500a8400e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 710725260 1250 710724010 710724019
    0x110d1109010f031a0a17060f1e15060f0a02060601090b1602012001021b0316060e03070c27020f0f030402120a11010311030907060828060302 62
    0x4001020850441100c00c0210103071035a450689252074150010805a81016840301e40c0c40c104c001281da0310115134015044e0102d240401e0345005811510f0440014914540303d640748090044061112110300c0848c229600340c0c541699900c00d02d000501440050300b90040380106010011110141c0078240303009072682119001d6990000442d17a10a00b032190303103480071040080701403440240c084488618011b0410440000350030030521081c02c0d210305902900d0b540410000c940a18682d506041008800c000303604140251040e1007000b0f00d00c408c01451180e440480722034561003402544c400540000d42c00120070740d1a024121700500c00b140e20602c20300409240b000707a14551003520701020740c0b13032412401c09a80b5811101281e0000c1c105a03030040c0e01e2500754911450802900007128442c2e40030b0b2610703e11840014040d070796940000e440d082014801c1150074080010744030100c2e94203241415182c4c0700c00b180d00b810011399004800610b0000b015a1b030340d03e00d15800c0513007124801d45 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 710726510 1250 710725260 710725271
    0x60303280f02010c140c010b13091209030b270604031e050c0615150f0a14030f0a1109040603030e1206040803070f02030409020304051605100f03090602040801110d 72
    0x5000ca0803104c038150384401080305080f952000140d948050300950582100000c4d040d40760304002280e10040c01d903d509816140c51800e802c004d0358400400359a400c50400c00314886c11951480d403040d2005240f22034205101101c10700c0741403c007404408259841c019900c2c28146400c000f044000c803440c40310b500c1c0f1360b020b40d40c1d0390706403181040740c644480c0100900340740d07152580f90781481c60b854040d09a1090704200503150142400c4005c14212070003c0e14541c0e150b52021014040101c00700034210918018000c1024401c2c3d04200640e01404106000421021004100700540120008590468a000070100c01c02d90007041c07403e01076101300c1c0d0804926000d854040da03542c4048070001c00c0c0d00300c103002281007203010b1582c0b110581c000d03005690425454032825800ca070400c80c8c0a0300c480d03004200d4005414031510b5500e010700001d950540c0408440a00030308906105480c2e101099520f40381201441083c2c3c1c10350340039010f0500207000d00360703d40d01c020340705810449101804d1307071030076 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 710727760 1250 710726510 710726537
    0x803130204110913090606080f06010303110d1b020420070b0c0a0504031707060212150102010603081e040f031a0c1201050d0f0b010602010e010b01091a0306030328 72
    0x5040d90318502c2c0061026030f400441e6240c2c0c5026105c201d40c22201c1c0d9032601d40c00b00f0110000e2120b03e10859505004117055807450500a24581070811443c42980114510000159002d40c0440c2c0b000c094001a22481c1d08030300c08034004041e4242101800000c2d08030447e0038104410040070490700600c4950510f032030340000b03000144242c032414008035100b003100700002048000d032030140454440019083c4980b507203a800507a03004014480f444402242000b10503000c00c0d0031001c02080a1000700805801c41d91484298803c8451561aa154070031107042d04140761011a00135020760001e0300701703036071390b914017504002001d6040c42c0d0b4040d082e400051001d44088144c6407000028000c180580c0d103001c05000d48440d0303120050b1004a62500c040021030300b81480e25008141940c00044c10444101d4490f0031900406285410080c00d854200400c1c040640300e0700048221181c0195680c0342c50f000640f5508c260100340039013080781c21608000c41304011109840c00c0c840d40b08c00d070b444d8000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 710729010 1250 710727760 710727791
    0xa053a0e0304050f040e0f1002040528060e0402040f0e040302010b09040c14012601080f03070c050603130b0901020403031403012304271401020a0221070803130204 72
    0xa40c020715400042004c00d10708545095000b00392542c4054054485140c80884994140301d0482c04011001d03400150820135070518000c01c14183c56004514455404100e00c245003100b01c1d07101d14401c2001020308a0f009030f9507079040328001c02181c020300e456280ea803100da1100c1c007802c031403c1e0095440c00c0d0170314001c0d080507040c0d82e108991040794a07410070306000400c24034204004007039042065082030b00c02e400141801400e0582c401004048066152240e01ca00d40783d0303012040700540d00248104400112100441016907008451244d140c4e55144c2d034210800c02c120300d0180c1502024002d0100c50041980200160fa000780d031070046c26001d21002d5074041c4820b209020f00c400c80d040c1c84030b800078580001120311403030080c00411440659090f079100070a800d8142d291081c01100c07400c04002c4a030340c40d542e80360030490081d814040e010f54060340700c105006200036024401658038030501c3c1c2500c21506042d9000c405552282015041a1505d81c91040228000d51411440c1000b5919 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 710730260 1250 710729010 710729017
    0x50d06090b0a020a12020a1b05030c06150102071211030703031d04020a080a0504140601060e01180e0c0c07030b070e0f09010e130c05031209240a053a0e03 68
    0xd80c0c0c88075017103502c20240003002540140700c082c04004014807400601080e020201c0c0c00799024030019a154802c22100d94209800500b00e100c00001c5a10100101c1e6000b19228040f03446214020000805a007013641900411005440d03160017090340c00700405400a280c181445544442803e545055800748012032040d5245a40491510000115540c3c007980042d540980f040c070b400042103038800d108500d408020307000fa038003090034052180550359000d41c040200c244034010030000c1500e0a644202d2251001d032088180301000034040c40440c82c20040c0400035035210116058518003d20001c244081d403150649c403800941c002045039180080d4110306072110041e0003903443c0c035800e00450b0b01a1604034125403155401c900040c3d2039800b800821080d4212200b07282c0e850b05d982e81001040f0401c0c0d0b4540c840c24501c001030321810002102521411846400c1c03483e550000b003800007c030401400c1c20300405240030016000020b0b000e6841d401401203106050000300480e06d0030302e40b24003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 710731510 1250 710730260 710730277
    0x40b07080601080f090309041406040c0315030f0201050f030426031b0d090f05071a0415120612051005011a09330304050d0905101107050d06090b0a02 66
    0xc0c40180881c40c04c9041c03d181d6a0456840803c403490b1036040000328090f80e2065100c02c1004607d0410030206041c1400785d08441006071508102704000c11000200580b86400050444c249040841c411640141e0032130b0920104504400d032280f0b402e03c2c1106600a07002d5180241000ba150303094002c4c02c0b044152409521007030fa006a20080c0c4403401030315038120072910071940362140c8a030000300b140004203840032030092020b002c0650a10600c029011100c11003090310700070030441004910400e4440e01042d101c82d141c82c07110314200c10070720805401a50032944800000e1282d400410030001074050798000050802e02c41a81d17644100b007580c2c1e49290780c40c10f901d0010441c00007107160547c1e50345240c51064000d0281c0c000c1002105881c2c1004c5210026102000010b00003803280821400342030b011140b42100c012410f04001c01c105060080300702050084501e80d0a8050406000318809000041c0402c1c01710703640303800d1240c058080440c040d0b60190407400800c124031854000c6842c0c25 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 710732760 1250 710731510 710731517
    0x307031d0109030f2f0313080f300d062c150109050111010207051207111912050a02030607121d0c061e030a020405120c1c0201110d0305040b07080601 66
    0xd42d440d50f20001684480c021710f0405000c10820360221810003a90b20740580a46070042406450101c002ca00d040c3c1010600f102c81800c2500712448045140c50300c180c0c40c000801440d44881c0c06046041c007402294200c4112890304007400c403060070f51489409030500c000d100c88002502c1d020000060b08145078070b4a80003030740400c0c050040d5409051001d072482408400140707003c040752140d604000700c07204115400d150025006c82413103501161101d060380c0032a0307585100140320031220005d400746e10034240b54145e0070440100303104040c070040710390f503030058196092450706e02c0d070041403a4050301000000601d014082d41842c2115a0242098003007a801007a919220008028694021806e140300c80000307980311402c0b03101807001645c000c0e502c4502c05600c9038103103c108440603801c0d285242483d4014030a492090b622003071014100300030b04080490178401c1d130004a4480c220442030340030600c078042100c40da1a601d64000c5d48250f0142802281945580b18102c809220940307011307001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 710734010 1250 710732760 710732807
    0x40803012702120f07090f26060a0b012303010e040804080a0807020a170604020f030f03041d0f04050d081302031009150204060909020307031d0109030f 67
    0x4841d850984200300c02403095601c80081d200310100180d82c0206100e12a603511882885844001c00e40c1d4150000ca40d420940c090904244001c0034449192040c11903030a41c210318032404101c50020f0040010590096400503e804400c0d213000d00440741c440c600090040d011610041003900001c03107200407100003a0b28591900081107102d800141055800702c03010840080c640c0020030001c550389110300d5015450b00614010440400541e60202200204141e850131540c0c0012540710740c05a8105c034841c041c041e030b034004170b441c1c4810401010080d2000081c003003a664015200c104555454596503002da64440d40380390444841610b0080059100e50310b10300e1140d000b4101a688000404a6029601a0764000901c0c212440c003e0104150340e601d94041031248603280c503205020728180640c0f42500d0100002d129020302d110321000c056000c804030711550300c81d81007058480340b12008003003210074030080d0300c2c0203005140301140420721100b00070442a010340031000c02c002620740710009 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 710735260 1250 710734010 710734019
    0x21507030212011203030e030310030b0c03070f1202190804050c03010204030507141302030c070515010f180f060602030c070815010b0c0703120203040f0b03010e0c161e0201120504080301 82
    0x69000760510214103264079040d1001203081d0230800395105101d0861900320f4a85181091881144050503546a100c404c01c20418010b401800500560301c4a1400340f0741502d44c9e0228200134040c2641d6078145a40e0410742a60480d4014421030107a0301840c203a603000261102010700302c0c421440014100d4110b251b04229007541c07602166050071011300410105415011907400f20382c001ca520014214001c01e8801c1485001c01031005c1c4500600798038151941130002c081c044202d241f02e00403c481100d03102e81b20701c2c42d16810080c8410b19008043c0001911100302075207030781064988100303910030b4010020b102e020000e002d0142001030a844c20840e404c00c01c2d50041540b051500413440d100d90507000001070489204003150109542c041c40d121408c090032030038503101c140d0000d03901920520061250751880e1030030f203412404e91f0002994501d2400e5004200c040300310310107400b0003014039146444a030010f4110760218400d80c0d650110004002c068003c40f00309039406082203805200600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 710736510 1250 710735260 710735279
    0x1060f050d03050d060905180d050d11090405012d061e0c1a0a0605090f2d01081608030c10110702090a0603050d14071106070b0702150703021201 64
    0x25000e00903d410f5141c1104e0389103020a84400f5070000200c0740ea12020088100102000304108250f60400307414800e2075048000c1140c040c14504208156690f90118281c441a03822983e01000c090310074042c035070390703504c04c0138560030441d0f091008020240c0740c1400114000c20b000042d00c14a4803440d52000d140c13a00d40464050000c5001d0030301100030542c0c40444e84420025803d6400109100190300c2d001400702e040d641d1917031080d40140c0680050111115400301c00e20b503c080e0158504040400800304e0312100c0016800a207014207240c400030401701004a22004500c0810320f01e07900003030303858000d80c1da43d100741c0c1c04032041070b004070140e401e424515420820ba92a4015020380c20404280c000600089007030f40c010340d42698907501001081030511407040c0b03146032801d00a0040c050884800340501c07075114010208024100c242c40319680d45000c2c3c0d20059004144040c8501d00303140e01940d0b841402404861000c040c02c001132625119001311502e16840c03640c8807101da4a071203040d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 710737760 1250 710736510 710736529
    0x3150a03151b0f0f0c0506160210020913020304080403022d0a290f040605130e061302130308030406090b010b0408030f0306030a140d0311040f12051c02010b030f01060f05 75
    0xf00201700c080f03a804d0300800d40801046020701b8070440707030011142d001080030b803a005042c0c101c14000c074014404000d032642c900303c100c610641c9243c405a541e81c3c3c4d0345403026152146410007503201c1c01d00c40e95940003015000141d10f000303003488118815508014204031010055204128a4032040100c80081500c050442b041d06484010a83d060203524070003541c05030016040880001d901107282151000003003840d800030b0a0f40500c416840c1480e0b00810421180300790ba01c1c55041d0001842c6262030651168000290b4000d4100c40e2030b818140b4008000d00400302d02078030400b0b00180081003001c4808204c07130888902400561034641c0c884040c540ca03800c020701c2c03154580076107004480070030038601540ea9031400d810050441030b021000054202c1d04034040d02e40c542d140a001c01e1080341052070b009000d695641580300046800c901d000751800148640700c1c3c3d21011000c00032002680c05420021f00b0600450980704c2084190f0742c05800c030341e0503110b02a289884c0071320030003403402c108641 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 710739010 1250 710737760 710737787
    0x1050c0d0b012c0301200a180302090112110306161107030209010303030219090501090b0315150a14070b07110a0807030203250c050603150a03151b0f 66
    0x410f0401d500d10881e42e1201102a0482808040d0110042150700d020b1041741406581c0000d502001c0007900180d183e280202d6510030305022014541c1c03001e420041c4207050045a00908c1e10240d9a11b5440740380303211100c0c6000b2203100300189451402803801081c16881105001c00351642800c842c9802c8881030240042000300740103c00000c030141e12070340e1005010754021380b0003594510b11030700340d89650b03800402110100120340800b8020f40ea4000440c50072200c000b50126125105c03480404011210512159840100d140b0740540104440c0007074161080c01e9111802440c0442503212000d00c910711002300540b040d0f2001503040760255081c0000481071200f1038009107071941d1400f80340c2d40100c4c015005a403000c101c111454260a400d40b6820006620440324050603503150a24051240246481504040f0000c4c0ca0840d80e900300e4142d4010040c811000d00d43c0da400c2c60210101081d075000030050921071a0301c010a5406003228003030a903561109881000b50300c085501650381ca00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 710740260 1250 710739010 710739017
    0x9020a020304060f030b0d08160b09010b12070e010315020d050a0c0906030917070303020403080c0a0605072f030c100203040c09060e0c0a0203070b1608060306010b16020d2a0801050c0d0b01 83
    0xa5203002c1400c0f2b02000344150701c4075000040608110003040300065500c0e03c00e4041c0d500000d401d1201300b502e0001d2504696000005101c0024402d0701880680103010f51007000524181c10090070403801e4101d035404a031a600c2e1405007517203511084082e20a00c000140c82c124008034408030700c50070b5500070403005020b86001070415031030f07541c0c0e005543e1042c0d1200026900440c080000c2c090b0710b100710342d017005460500c0448002c0300c078001812400100b100d501060310f401c522180304141803040344e0402486078281e03540f10320030f410038000075001914191084181d1030804204030506102d41c10907600bc0301c001c1040c640d0f609111402503070010240c4000c5000070310100c80016410000a4040c40300d401c122054180e0f07011008042440040c0f1151190744040010020001c9500444110300801e029030a00200c0500200340e91094015000f042c916030f00e030381c41940c0382c032820320450500c00e0305030306e1a80b2940e0b4410b032a080c0e07081a1a0082c070320000304074150200000790700c4408041c00605 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 710741510 1250 710740260 710740297
    0xb0a05071e1209330f020c0a06050408120c120d02090904080403140c010519050408060408030720060c0307030902370f0e040c09020a020304060f030b0d08 68
    0x1d445442c1000076280200c007040450384248034180050b0055070320522000d82011409404011503000e40c0b44640d401070a20a00c0300b41003c403e80300340a550554200500300b4100c25a071500c0080c10b651081c42a0402806004000301403d000101111011340400008000001d0508028015a40a2409051070315400c111400c4e064550301040c0e80700b035016501454a491031070030014000c0700540102e02c1540c106001c1407145a8101d415030304410043d00c00182d0091407043c0a0340c052085410029007407007140104810000caa50095210700121782d5904100c01070703480035800c504410710742c034070294002e00300250268000c800a554003080c58a804520610706030040384000388002480c11800301505141d00d6112001c0c0300d84175800c404410320300242460311131071001e0308006024490503400b81c50003290034405185200c0c006042c5035a011503031034400c090084d507a640a41324810116024103034240f0002c0c001d100f44980584003414200313400c01c4c640d880031801e901580190080c1f40642 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 710742760 1250 710741510 710741513
    0x809030c060709030b072d030603060207050f070602070b0a03050a061214010501050f0603060402030a02250201090f031a0601030617100506060322060b0904030507020a0b0a05071e 79
    0x80201c42e010301d64030f8450590540c11410030646114000b04440140804206808072910603141d003036601e0710a4590340881a09221411030150140350b0018002c1070020456106001c004207060300c0e041014011110915030385d040907a21280c0601c159000c204042c0031940c1140c1c0a0741085503c020741440007e04d83c3d440300190306600d00d000500b07031120644207040c0f022409007441900c0c0909800c40d0030500b925800f2000a40520005190600030b980100100344180d040d5019523203a0041401d0350352803d4141448400b582000440580c0003907500c06001558ac4852041c00054941014001242d00101d44e011407045001410482c1010741c4c0d1140022300031107281c40e5031342e00c0304400041e00d0350b2020182c2d44019901c0c00340c54144200e80420a004403200700d13a00d1a0054a00e03884c2c0000c0381841810041c2c0240a1f012440d604010850104400c1551000082030103030301c04c40324210380c26156008484140600451000030840820a641c007007004982201c036080b4a00d1220007001415 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 710744010 1250 710742760 710742763
    0x10e01020711181e071b0516080c0d030c050c0a0308030901111201030f030e060301080f2a01120b090705030702060a0606020d050c01020c15040c080a050a060e030c010507120b010804050601060809030c 88
    0x301c403040d03034a0740107400d002c9059020303191f00c9401415010f00418403007800000140300bd0310700650090a01c00101000c008000c03052001d040014001002c1401c615aa030401103160f9008031503111f10780d443c01e4001c25010082c0700582da21070014241030301e03050b801c55550413488001038405800740107071912400481c0c1d40e404002c0d4040d1144c10041c2c07462030a06180e451802c100d0440300a8002e400320448a54061000644040580b007440c0010301d1843e00c004d44002050703007101c2d90350407000360030411181301d82181c0298080e0105908581007036650301c540b18100c82181c011200142c01c00d81030344034004d12031409842000e0511000615050345070703c0d1589007040c4400004907140711b4408200c01d1140040780303a0024545600a406221055603401c6c1d1600c160550041c411a81c07680b0641a142c020019583c00400c414000c0240d41130620015000422865012001c03605026810619501c10301c640360090f030388100103010990030403000391040c02c4002c10a80c01c41c4814011032070704180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 710745260 1250 710744010 710744057
    0x20f09030a03110f0327010c0c030308041211070501050f09092e06050f1c0504150b03120403060e0f0a08270d030c05010e01020711181e07 61
    0x801d0f1100c2c55002c0b428244642440e007010100010754009110502c4000c0446c03d441007491001202d81ca00e0440fa4001624104004407000d012800009404010550441000c42c007560281c0105945220003650448201d194201d03100000d8200d00340030481540127502130b203030120f81410928100540080850b20700d200845e0002820204c400059001500c3c1c079500c801c0020035440146089400c0140203801c506c1038116000f06c105000070505d9000391a06440d0308629020350050000b4201030030514900921003c0c503000452030682c1ea0241c43c900040d0700030003500d0100c146030403e0f2030364a80b84000e015034074511603580100c0700c4000c2c8045040c07100003101445110000c0d202c0074004040c14800c030400c0340784030480e42c4903031607204244d844802200c0d18981c50300c2c1c1595280114076050f4003420400274480d900d9800460310404008030602400c1c0f941d10b090365240c04d202c4c1d100508600c540c0c0256000d01e003801060140310b10b0766042d001c01c2507014402d400c007047c08000d20007114a4445 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 710746510 1250 710745260 710745263
    0x3063c0c020127060b0f0d030c02010903080c01050f150f01140d0912260f2701200304120c240c030f0605030d051b0a0602090a0815010504020f09030a 66
    0x541010300a82001400e10504003c9001540e6135884101c0006c0440c640e0408480080c050100d80002081107a200f003d0100145034041303240e5842c0c41c045035080d4040c25003074611001e5002e29100040390008032644043c90024000c1400f00288540c20064609011040d007039507650504000c4201484103d0150405e114420650800c5446100c000149285201040c600c40c20f44030607a201284d24040360307040d40203a007022120030b164586041e080c000061651424104600c411402c8506a0066210801840860302403881e140a1545103034103512044500506c3c2e85466058142c82a1042140340c3d40284129100c200b15021400000c001c20451240307500780c16145d8004001055142c05161182c0c46480c0060240030306200021391550b8211402c94104500800c1d50f50800800201c111803901d035a02c1600c2e02c900e91410800060b40c00741b0301030fa003c0c402c5103c00198080001901104e10901e06c00240c840e42d00380307810080030b0341c0724104091605e0801d001921b030300d039410712000800c60f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 710747760 1250 710746510 710746571
    0x70e060a35100603060e040201050903010209030708071503231b030901020702010e030f06060f0d0c0806391303060c110c03031c0f0e03030103063c0c0201 68
    0xd242c40b89615005620b150400c50416040c04010810341d01c010400300c3d007003542402c0003900c40031a500842c3c024092008034950501c075242000943c004046058001d86000e003009501c07894840200b50300342d99244103100311038946404560840ca03c80d000741074021400151001480c0000c00d080740c2990010342d440c10440c1d5002484500715078100340c0e9142d1710070054002c2d18a0010941d1084d46a4030010015402844d03000300240c0240c0e038002980d200c8641c0003031070440403903c40b102e05645403000c40e006c1c0034540d240c600690f040b082801c02d01184d0303280c80c0207001d59400c40c0c2c841000e082e00950382000846160a01c080300003207030390261546142880d82c0700c40c2e42410002d072843c50074001c400d4042c007c0c3c004000081001c1c0a58038040501000c4120103d400d1200e01001d10042c20400d1111245000c04400401041103c1e00325808010300c3e00f140280341c046904800700d42410801c0b805414281082c0c15140050440d04601d0311005039000010342543c403c0e040340c07440240c00d046030960 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 710749010 1250 710747760 710747867
    0x150f091b0403120807110d0c080c010207051f1b050903030d0612020103060902030106050f0304080c06091b040501060e330c1908070b181204030308070e060a 69
    0x3c0036805000c2c5603101d2503a15107910b100714003018007621b5100ca181c44204204d1282d82880900001c5800c450391200e50030021136079280705c3c0c00d000d51141e4030a00c4800702c150752041710400503203142c051140d03159a10314401c1240131320801c090301c4c01d80c41480c10315014003052120541d0015540f186000a04102684a0f01401ca07480010222180b6400100e8528410700040c40300304d0744007047d1040044440d206a641e0b07240d50078a1038443c0143c0207804103c0c880c4200f04001018085080560b1185400410355412070b600200b105032039090040b03400003a54820b00107034a01c0d2520a0410006003290103045942c00b8401d4440e1200c10207040446001c000a50600200001c01c00007810034502114111508843c0d42d400c50940b00720b050141440c02c4003400303e000384480301e11000a404ac51000c541481c242c0c0d01e01201d99070403d220540224801c140010302e030074082c14440c2c00240d0010045072400d0300501c401c2e5101119881800c03444680d04074060000d51801e0000141c80701d03031943c90881e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 710750260 1250 710749010 710749043
    0x315031c080609040507050d061d031b0d0e101214010602100b0306070c0534050616120908071d06120c151c050105010206150f091b0403 60
    0x80200c0c081c2c10107006105100811021601c0451000c01741c0704126040046102c48d42000800342c140034014040c2150005800b4680290000040c042910442d0035039041182c215643c0351580e06180400c00420300c0201f08440c030b40f0304000f80400b4026981488901d00000414050440740300081c443d01c0b042c0140e005001254040100100341910300200740070000e18000405e4458401070450320030b101c004003490301003210a1008042400100c0e15003850481001c1d0010004d1510501074100106841d5000c240341c2001c41c1104c504d0074501c200090401700907600c080c09440d442c031150701000145040030844d804248004030040683c0715080d21401103504400f4001000513085510840d403102e00c0083c00d94000c20503280070442101e1aa000d2009090000f05038404c00440035031440211100944400e40c945c0100c0c103944080e0b08854580d80c85801d9520030004450300d113a80403c80382d0825038103151540d100c1c1c1e40301c5207109028030003143c0386500e00300ea41c2041e04100c90908402c540346030b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 710751510 1250 710750260 710750267
    0x140c0109021309030e06030615030c04090b040932030c0609160501090b1317010c0e03190b0a0605060a0807030b0904021f02010603080408210906030c0315031c 70
    0x14181d50000c2c07001c001c4221155000350020303010f0920035000300400303c0012440e079500030b005003400200b0010203a581c549a40d0b40f812075072140c042d800c145490301c0c0c0d412040b41003a20860071500d5206c4400c40350004c0002c11a8100c071002c20f2860120300554087e252090424401781104441c030340000e016a084c802c0402d410030340c28541c0104600755001003040b00d80e90214103407003240c60100c640c80e9140342e48544140c070280507420503107085d268592031058100c41580303d8010111180d9803c58031026450800d41c8580b0b090b1300f461007810b15550603802240012804981000c654200016155a220049043c580003000343e2008600b4444c104001c842d014020419100d0303044a01c8103d6160950001d03019800000d45449070318034030030124424074001d5128002450f00948141c0e1a5941c44040039551021819200d6080c0352233004010240302d5903042d10000301004004601b1075860f020340310340580000301084800f81e44030801c0d6a9940342030005012101018042070107440103c840074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 710752760 1250 710751510 710751529
    0x24050109050409030906050a23030403030e1f0b0126010302031522060b1908010e160306270c140108130b130b0a020d0506011403040201030c140c010902 67
    0x40d4082c034106002c4800081c0d005150505488140c18129141d14032800122035413145018145c00001c808e030000f03512039064601179842a40b00e07640a01c03028181481c2152602407000800110420340d150125a1340b0050b007081e42c408206150035450384241105d105003042155096030b01e0003120b00018020740c203080c030940c9082c0003035200c425014102186880c2020304690348110007160500c0305e4030104410f03908001c1461100400842e19008104607550347c6017000d1042040231342c40d000000340d100001246c64045403d02d18021010300d461611440040c1048031600f004c81d485004e003403d2141c141c8403800c14000c1c003401072030040d5414040c102c00b50141f404080d9040c8040c0744100030403449050314049005d036014170b0759a0341d6192940020801d0030002e00007084524030750b00304110a05070798040c00d01188407810520040d100c08005680c10743c142a20306c1c45010341040080c01550107500b08940e65511450301400580c0f052492208a80103070b07d0f5005135035181c0f4001c03815407400580c43c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 710754010 1250 710752760 710752769
    0xe220213050301150b180402040504020c01140a09030c060c020724120506130b060c0d020f06100b340302010b09060132212a04090b030124050109 64
    0x1181034440c1088455502e60141c0640e1b82c014921240720401c2c540c9603601510001d100151080d901d4900b02c00405001e450740c0001950282805400502c4480480c069040c1e059016140e081040f00d40d51500005007180c91900d07403d41c41071290000d440e00c034144494207401d41030003841d019032940300300040820005115031403105007003100b40480b50741d03103158000d0501a50707440000c08480d1500810143c0c020755500c03051600031301800040054000c6509640d64880d00291001540d8042c1c000c00c0900c4a0f005212000c1010b22491003038110500035241000380c0040c0c80c8010940d0010ba10001c14418031003200141d441d410701d14070a04002c8120354014500742084810700b480d4080401c581710007502503103d0f48000c0500d02c0d160310740c42011140c2c00c0076501901c9854a0002c1040d1102c0002590480c0c07640340c010440c9400c1081d00c8146082e40035182740a2494245030560f644044c04241103205e61555803142c42c03078000041c203840c245403c030711260040115490a0005000b901c0160b20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 710755260 1250 710754010 710754041
    0x70c060201020a080601050c10060f05120a0503070b22061e050610051312140f030c0c120c030703150c030b060906031b16120e010e220213050301 64
    0xf410030703a5003081c01240d00007000e00e40ba90703ca024090a180ca4480c40a00280c045440c02c0380109130102c540c1e04401c151501a07942095100d00a02c82a0750781c11940005416900280070090010b0310844d076507a082460350f074041803068444488904441c60000c130440d0340760740e180540ca105403c0303102c4d1034941c0400754104000e1482d215011480c07031075002c1341e0902000000503141071642c04181a9a01600f4114400071029100d8684802441141c000b03015152241c8807000203c0c4100100b00c1d081d0114000181441292000a01c141203075030884042180c02852060011354a08100d200d0040d8000c282424a40c440c00c20082c0440d000100b0440805040485005003500d8400460b030a000054131030780d43da43c0d104100358001d85403902ca510148100003510701c115250360540c200c0c1840c011041c810012440e0700054407183c45074458a80894004008694245000103078514004007601b00c2d00b0300c401e2a0301c803c0741203034860758100b039061150b01d00600413402e0911440d00008100324 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 710756510 1250 710755260 710755267
    0x1090c06081003020405100803040f05030705060307050d021308101a01050c060123031b040b1c2307080604111203120402061908190c0c0201050d061a070c06020102 72
    0x70329160039080f4080640a692104086002c40d120215900c00400b441e0b001c0da42c0352500c0701c07902c181401061041c144288901c100214481c50040201c0e80624001e4803198505000341010306c2c0030390041c40f04800c040016150000790038205110048000010600008105050b410408190b0180010881c1040018000301d2a5010f0000d0480c3c15103490400d603017810400440c0b4548072030b015100e0503400d4080c000020640d01100d402d804040002290284069000b207014018030884910b64121014003d529481c04035190702000d03129002c15014940b0110840c0210901c2c000d600ea01007511940040708100a010141c0340711160a00111801d41c520b2040303c2d03000360740307018003443c050802002c100802d0031903070791008031205502810b001c2c0b40144102d080140ca010000c503a01d44100399400482585c149903842111106400c0d84c903800300c55032a40d0011500c41c0c20141e0300c11800d030307580d0f200851102e01c11049110a4044941081d030b81d403001d4507000700c07075407000c2d4424000d5a0062 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 710757760 1250 710756510 710756521
    0x3060b0417010f0c12050406060b0a090f05010309030f050c0703061a010e181602150a020301080c032a0a0302060f030402011d030703020906010215010801020a11070803160515010801090c0608 84
    0x117035010403042916000300c1c4544503414928001e00890784040340b440700020701e1440643c3c100b04401e08540d0ba620014580e81d966000543c01c1d129030b00740003000616000310801076280108082d0110303d81075012034002545955544044540740812550342d0080a42269099030380148440c401200943c0c2c00d00e054072000d072484821a07405003610000c1c8440d10440d0000038403c1000552989140002c40b03200c0c03c1c0b500c0f8010003580b080c0180320301800b40d0a40251903043c0054544580c64148100c0220103900142c40d5200911200045521032005980080580d5860000e000d555003203008660f0340b810306200240904000070380181b1681c14005015090b583c001c1601c00480c1e0301600c00c0c9042d5603a14004034100070302c400c4a0150190540000701e585001540940800e6440d41c8a026480e440c041c0c5003036558103a44a0111950300401c030401200600034443ea1966200700119401c00c11440c3d00850034003c02d80000805030744d07411105c41404070b00307103d00b0010a4603041c00c00885c100b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 710759010 1250 710757760 710757767
    0x3060927111305070914030d0819020d0e0303070905010903080d05040305250524011503090f0302030d0609020403020904020907182c06010c060c03060b0417010f0c 72
    0x400300060306a4145800d58100d580361440e5003100000c00e920104140c1c074014074050001c0030b803402100a17002141c0141d420714280007408100400782c58590285641d03c5001445e21000c0112a100c00c0d16024012480300315050301805085032000f0010310348070320741044001c080d50700d207a1145042100b035a40410100e9420300468151070001d4102007055501d5040964aa1040301d000300c00500c860b40001d00c025500100c0c802141e403150381504c3e8a080310504604605424078032510a01050034010800a02e2110700100139040e2410003280211030f43e12410000c480340c0780154056040020044011900e40c4104000b60102c01c50450034103045801081c40c800009000078025094900418101405000503010155135030500d07001c00741d140e000c5200440840005100020800c0c0e0f41d4100f08590305807103521420040e980e4116582d0b00b07481c0d1201802e051646003051691b551404102c00f485900140050070300741ea8648440b40070328016600710b60a0b10781180c0300c24503160351104850360 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 710760260 1250 710759010 710759081
    0x60b0a03050901090b0405010c20031b0a02061c05090a17030403030b060406030204080609060402180c0d0203010f05010e10140711100c020111010c080403260403030609 74
    0x1914640003560790b542545142c0105103032030740540f05605d60b03c00c200821505412500000380c131591200c00c0920003080e42c1524140d0340c405280107820501c04a0103e1110070300c0c00c05040407601c1110b610800c1900490001c4c0d200380c2c042c010800007101ca241400c02c00d40220303038008a40c0002071942908a4850b840d091441844020814000001140a140c0b0035041492254002420160350703a5a44030003a000390f0151040b04628040d00c0c00280c0b01340c1c00401e50a10513900a00b01c48518070a007a9130200c0c2c0d1000810f04002d0f02000c2c044c0740c2c115071003840038601038002508900c3c40780d0f0400001605401141060501c80c18490b0711150b072082d40301840029081c03420302200d45a0b42c0074a03160080d07591485441760407049241e044406a94001848400700e4002c4e20340d800c04802d4000c1d0f86007071310006020035020404401c0030400007482528130782c0460180040404d402c03400c1881a110422080d101900005c0c2c8400050200000e94071580f540090150010240c03c0302e000340d41c240c03c04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 710761510 1250 710760260 710760277
    0x10509010312210b0f18060d150911120109050d14070803091e07060f05070f24050901060f051509090705210420040b0d031e03060b 58
    0x41d0b0100035030300414000c15840c5685500591a2809066036030144401012031441d060300c1007115104291702c60520307586404000c1e1822441c005103585860a0000800c09a00111882001e107010000c1c80d401038070a14241ea8495404540c2c2c0b2480c901c01c02c4401650842800030300d9150003020030021310300103a01c81c070b00b00c8039041032520510f15000707200890041300070103891028000301b045105103000c50200c0170241c0c3c020541e8070800001034016522043c03401080045954503801120080c0500090520b01d44244100e182c0c01a8650302c8040703403207019200d1603408028005811f480b541d03602a1725070045046000304081840c0c9103168080f0840e600c12280940780d10382014085a0088d000c4411b2000050301e00c400c0c1c0e04101c02d00400c02e50180e050300c52940c00c811034000e002e9080180b0f59010310381141c20158070030306224842d00b00801c00041d003944540d943e41d440c03c0503203608aa200800f030080d2184035115103100040d0220004c245020030800d841c1c00c40c2800400491400d41c0c0c0d044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 710762760 1250 710761510 710761523
    0x18030304020f0616030302031605070309091104120305071103371b0f060f0807051b0712020405060a1212091a0415030504030815031504061d060105090103 68
    0x1142c80301142543c4151603054011001074006035091581640045000c2c85060b40c5510100140d49021a0540101240140000d0f001c0c88100402d0300150424442c0d00ca4501030180741980d47d10072a030001046007003c070042440469207105001c001c2409104180d001d802a01980b00e18003001540c0b02c0011040c078510f040400c41c10750340d240314800c5080f4801d078844030301000da0301540c103600c401e0078030b1303108402d51070b40701c000041485441071500209065850b1070340003850b01c0b442c0003600c481e044208001006600e01c04c80403400100ac0109c00f00800b0784040701e181207051030040c07200366100280f0842c0030312001d90080100500d01540d819045810a505006100306207100720342c0c0c4442c42c4d100d0f2000f2000d01950351070944034540140100c0f0440c00b449050034003031400680541c2c0d811a80517004c203100c0e07030009401c9900d65002e500c941d5401016a4101c0c0c81610780464820740a49003030b581c155894148103044a0a1700c0c0e0403003072568800c0142807a47c5020001480c807401400000c100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 710764010 1250 710762760 710762779
    0x9091a1e160216060339050307021f060f0509040b0705220b0306010801060e0102101e090605011e1202270f04112202130b0c0a05061803030402 63
    0xd40b4400c1c4280c0c00b0100c0241400511140d407110010050000701524050940000c1a0120740e405013613040000160303c0f010340752603007110340030a072881e4000406660a601501084150a02c59614010440080c414001503428100101c0c04a015080d80060f40101410024440411800160540c1c8002c1c6841c001c0c0d901e1a8801e50445441044664070b0b403c00309900001c10190039050155205a000780d807008581e0b80d840d0812524030040f0f9803418003682000c002d50780741021030f8000c103089c410b160740b002c981c02c0542c0002c08211580a10180d07222640c134001401141c9403841036800c80220310188404803402c0004140c441440018000d00c01c442c003d18415619655840740c1101c890701d45100c400e54a06014218a0f004003150100e60000c070524a000c01850280172801c8030032071a076001342c1520b90700307803581000354044040703a480301148003000202c4003a01c20080a03020802c0340039100c0080315281c018600003014003045078000308000d40c03c204490000980e9406601110b1503140d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 710765260 1250 710764010 710764051
    0x2120703030b030a060203040302010b090f040b0a02041a091c0206030a020304050a0b0c07050106091e02033c0a0b0906060d0f0c02010c09080307020a170709091a1e 72
    0x40800c114015054069000d04400b1710803a54095842140079030028410743c82c8030410040c00d1ba00031a0034040c0c0c102140b0100b008070300d8403090542d108900900043c070b80750b12014010400e40c5030050796501c101c00040c112519041480e144082601280c0500200803401e078002107071f40c0001045140c1040c1d0210004007809410011040602d0700700183c110641400c100c030031a148d011a100366403030341c2004000070303111681d4850b41c5c0d81102140307410200e4101c071941102c040e50019000e4940081214024014000c03030107080d0710706d00c1400e07440c08000d944400c41c50f000c10300000c1408601e94079142e0441e6060302d400000592102d001c0300c0c0d41d42c1d0740d581c100003180180406a9101c40c62481e1420091525405510021803850380b0740b101c00e0095514582e0a030382e4450340b54029086118010200701c800c018042403060f9138507140030303a0301c82c6481d0807015085505042c000e4408020701040d808181c8800025140c00080490546061080d20707014030004190141001b110601040340341d01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 710766510 1250 710765260 710765267
    0x609080633040f021810090510020703060c021c05030c0301060525201c0204020a090b190905010206040f020616150212010522051909060606110d02120703 68
    0x1c103941c0c0040c401c12220805a0b02a07000b50800341c000001004100c0260055142c0044808288001c0340c2c2d41021507400d007030030b0000c00c3c0c0601c3e4180055220382c580100c00108130b402018a0310a0300e80c01068030700214018188542c00500004003404001c02c14441003001110449040d644035040580e920464903540d01a620045244662102e140c0f07441c900c20030850002c82a0007072070b038900399180d80b0040c030104582140d10387d0841e1301c5d03061449460301c014100ba4014000000d600d0421100d181c3d40c90009501c2544010651260402444c48411405400c0407050b400740c4802e100410251a140d0b5500782140c0c0e19103000f91166801040d03805040c480c413410740d19843d130b12004120203c140090b120002e500022003551044d0307825070022402e81015200016003a482010851b070701c1c029114104000d0002611000152002d06440005120f503409102280d0340b284600060080c41d01030001c0400d060304a00e0b40a80c2c01041c41c42c0c050703030790001d207003010300c1aa80790080e501e0394245400d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 710767760 1250 710766510 710766601
    0x80604120c05030318070b120103020f0409170a020d080712050a020f0a0c11030d05070b07090504110c06010b04050a0306020c0f0106030c091505100305180105010f06090806 76
    0x40140c0320000400a45e107213005d00400340500020308441d07115440d085041024041c8822009140381404010005442c20620080f02168040d1000070000c8094813514100d900d48688000c0ca4200020409000c640c1008064001a01d80c030302441d80b8100404001d117032455035001d0300ba00ba6142c20201d411100141d0458003032240e80a11541c1d0707076002610203480d64992450540700b03405480300014980c20f021070085ca0801042c3c0e00c00703140083e139a0f80e603207180c800039082d0741c208084142e01242980f00c0c0c1c49071200000c2c0581c901a124074522403c3c130302e0b064050700003c070f104030144010001521814100411340364402c8015855014040d641403801c003850512520703960801d5000002c1c051940342100513110420014050130f04c150480f1081ca03200740c0300c0e15411800060016104e02d2181c0d00c000d4001060320540d41203560840310b5642502e20a0b001425070341d1402c0400c10185070000031820091030080040d000a1414145440c0c0c003501110070708242d5140b0741d60040000e16001d044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 710769010 1250 710767760 710767763
    0x40507050a0e0f190501090e100b0c0a05102405010206060d060b030a0b18070f0501110a0204240614070311030f040305101d0a02130f1e1401080604120c 67
    0x3461344800040c540c0c1c8a2860700361140d42d001c43c404840214000a4128000c2d100e084981c3c100080d5925054125810754400f01100d1000c2c000d030300c1b05038006007040c8a1b070003e03842d50b40004a0382461780c10b9a09840c00c9400c1c00c501c80c07101000b10811030b690300460320603407100c011103424462445600700715001e460004682a40340c00780380b25003403c202e112403029008681400242d0121f542e5822880c4e950300d058040c051a6140341c450402032580b0603c191803100381c11100303454140d001d0358042001d40b20406218012000b003400018107080c66a00c07880018a44d51410681d140110455940148a12000641041004503046d03020910400448030b01810501d80310f030340c6566074203280e51116400c14803000307031a06055202202c12a802c03140610058440003a00300251240d080240c041000d00000e004261283c042c20a070074000d02c02c0f584400c00c010ba1900740002c0c0211110700704e655070b418500301230800e14010300c03606800040481c1d01c2584107502041d0380003080e80a4540c0192000b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 710770260 1250 710769010 710769019
    0x6050310171e2b02012007021504091802010e010f0c06111905120f0105090f10090609050108120c030304121b0321060b0d02090402040b03070801030b06040507050a0e0f 74
    0x3080d80c9a603820001c00d0494606138020081c0208080040260180c0284051041e08080c80b20340007500c1d200f006106110300014255191684e1101c00d4019a0080c0d5848010504c0310700c410815540c01c05520841e800091070091150140c2c40c0e000742440d1004c10020708002d5541c1d6580e01d8511001007118a21140045501a000201000105984d0214404203403603a42003011410740301084003041d058400007407560000b583ca411440320031090040244811042d072050000300d100207807007a42e000e040b03200c501003035542c18003865502c4c1031800c5040409012040180001022002c02907907007041d40410a02802c0740e84100031140702d000c0e55507032006520000b456004054000354100300d5201c0f2680c00480700e03100c0c44071040032500640f03c0c1004a207004c0288407800940780d0b00405900400070b1005003003603214004244039810444060002c00c00b804010700c00d101007542c00a034004403c42e41805103107003940b0010620700030b401d040030601040d080000917507a1030a05004407204082c0c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 710771510 1250 710770260 710770303
    0xf250e010b22060806010e0a030b2e1a070c050901180c360815190c09030602070303020d0f063b0702120406050310171e 53
    0x151140c0c03155001d101d0301010ba6107102550115000809495401c6621a484003211079071080015100c01002e089110340c07000d103558010000900c40030045024400d1b0840110364181e000e01a003042010840e0b6001c18072503621820091550780141c14440d0481c0080c0d01e9071680014500808110010b4210b55800f58510002040001d0708003414240d043c0002010f0213000c05213074007510407005000c001d000d8031044032811200d1303446090305200c008920400c4403142e1036961003c3c500703013104d9848160101040c4d000b07200b0250700c292040183c100c40070b5403c20420000720b102038410001c4e84801842250003041400c140b6019034142c883d503041420007480301c58008075138000101942c0c0030b20600c045c04c20201c2210100700d03007e51040c0078002d01754041e098040500f10084000010300c4a01144140900c40c1580018031014000411031500d801e5242d080100141c2d60481e0305030403042e040f21078018482e6081d0800606400204201900c100300c1c01001c2601d1818010910400640c508150 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 710772760 1250 710771510 710771519
    0x616090b031e06010f09170c0d081201060f09060f200f06070c0c051c05030706060819080a080411030111070614010501020334050a060e0f250e01 64
    0x601c0902c09030746a601906080e50f1404010740d8034500241c0c44d2000640c0c0c10348140f103c1d04561085892840c00300007112080c2e60a00b0004003140e040d00022584c59070040b83c041040d0019081c07942c05800141001040c0c5000c1c40c1d001005108a440784400300045159002e01c258041c502480d42c000d40c0c1e013a0f0071082c0c0d040c3d044199880058a0621100c1c1c810800010f400c284140f9601c81c49561100007443c0c101d250000308094002c02c240844da507120210017100010b00708000a2030074600c61040420403503d410880d60514070300d0652555000c0c1003266100004110104803040c1c0500f0f0b0401d005140c03183c0c2441e9208561402001f6015071800d84030000c5184100041c1c00c07c0c6204103410703c80c0c00102d8070700c0d0200070002e10401d805a40b00f4407001c0c0141c2c5071000c0701d50800c044a4201e40c07542da445810724040098900c0250b45540042400d501400094028072681502d1306006192902c80320080c1d075603401c403c40d45e510500c9070742c19444030080b031500c03e89002070681030392500075945c65 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 710774010 1250 710772760 710772781
    0x8061801170c060c10020d020d020c0708010e010507090510210b0910030f0807080d0f02120a0b091f0b130f090b01050301060e210f100e0616090b03 65
    0x11400c412020b4030a0900c24442458000304407144500040c01070114030940810000c0a500b10554100c0083d4090061102180062002e41007040c000c00c01401018940701440d42104e08810780120305134108020044d0383c98201e04001708a27903055170381928a40020004503a40403102c10300120b540e4140c030304004035829640129141d07000880318001d090f02c071540c51002c411201c0c400240310618082c81200880c5ca0540030b40b10380f42c0a8044c1504d4094894502001c07203000e02043c100c01c590115020582045400103e60b010003818000c01c41c020342c00380040c5060200034070080000d021804041304124980d1905801400c40d400b80c0d945130051803d4100d4124242c0c0680320000034641d80001d14101c4030b00500d1894101a10b03803038030703527401c00e4022200e0b4414090b90715040200c41082c460750004039280c11a010718408040c1015420926000303081070440d4046400b10360804403022250000481d155801c41214800b0740d08403c5080b03425141001c243e88603600d100d802000300b144c85801c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 710775260 1250 710774010 710774039
    0x18020d0609021306060e011b170f04080a1101110c091b18010f0c0c060305061206070215010b090604090902121b04140f0a0b04180f0605060406060f08061801 69
    0xd454403280401c07400302004607070132442c0d0406402c81c010359108c8100440d2048121600b0b032100f042900e45000d01a078003003240d81d402a4001a55030303000321901d4090001e01403020141a00910b000c3da07049101988031540d6003074101d02e207840340040c100801c8036217900315001d03010307485200c0341991140c06076020020840340501d10903022403c01200351000fa40310b042081c402035400880821054280a002c41c001c10008041e2a046506600c3c21401c80ca001c0100c2842001d10703034020020181c4c0e42c8a81140c107101030b800f0500c074039410300c40707581c00d0760742c0d00146d8081d140320030400280016240000303601d191003042c40700301c1805100d0201400390789081006c2d503601c2e4182c8090000c15207500c0c91240d464401c0722442c500140003000714000c040316801c15412408003c001041c2508460000d0303401d03002d0080304445940070407001c401080b80c0d50203115400b200c210f030100a82032a000c005030860b001d22882e841000003440000d0229954503942508002d1007c507034500568440c03102001910 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 710776510 1250 710775260 710775269
    0x30b012105031803071208120714040306050c070807110316050a050103150b1b0607020d080f07020a05010e0a020f0d03141e0f030603010e0a020f060a02070e130b0a18020d0609021306 80
    0x60455000965060044040d90004942b04440914103451610340c44001d0401401c04481540204907407004158000080c001c1c2134001e9110081407103481d000c052505450904a07aa103000f940400c00141d51504010340c11606d00703090100d0305a07944015203059003c10b030071107074003c180410820500791041040c1221000341d01d007100c05d40d4550400580c1d84210390703070594000030b8081d400034807061129070400c0d0b0800501d004607400c81903103641c0d0b03034251070900310381404590002580fa001e41c90171200c5841191400c0c0c4120b50410240c1c2c600034000c002142180c046c0707820001e074105141070417000048840011800050700c54000a0000500d6802504c0d654829820030309030119408002c101100d420f0344c010a0012101780034001d015440d041000a01d003980580200001c00c2180b09030964403850120302e01d090403512915108041c032030050720342c1c2c045a241040300c4030030304421b401c06d0301c0468044540c0281d81402e440c0c8500600031105000b504400c50400c0590340d507035180c00050545 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 710777760 1250 710776510 710776537
    0x100606080709031110030b030105040303150501090305150402130c0203030711012d060504090c17060c04050d0807061424010c0b090a0804030b012105031803071208 72
    0x707464064084450800d607000142400604100e100303500d141030b40d040ba100806030305010401d041058000b0303085a40496041d4003082c0c4503081c1c2c4590321035082107000134010900700706410354115140c290f52018100d1a86200002000c0480c1c15035940004031407000b0104401840103105000c00292030740c00a58402c00400c0700c1803103000c1d07c56410300462480003528901d01c0d60001200034415502c401c0f4000c5600303455138811010445840d49d00800500600440c07148461901c0c0a0525510b80450451500203810040034017507a055400c084804850040307510b04005030050810b070f2a58803403980010b241602c1e0619a81000780520b800c60b2141e4403010029034103c140e40d9905a9038065032403118001005006960b0005654119903504084c00004403100c0803a10303903501030180c1c0b194005903240628040100711000c0c207a8070f03420085c414002d4440881c0c4183c0c2d5196542d020f0004500c40034103901035240341ca0b41b030402c210001020900190001e0680c5401d154209502c10f492100e1034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 710779010 1250 710777760 710777777
    0x9190f0803190507052104051207030b0f07081807170109050d0504060c06091103060711010c211a150c01111213080f0a0801090b010c0c150201090203100606 69
    0x38180258281d401c41c941010186c49541074055143e01040e00781111502000000e200105503501c075241d003401d1030380c0014020850a03007107090542004a000b050034001514100410554076804805940c10103c001000c1c204192058825030900d001e5420801c03d00303943c40c0649070440e205410a140c954010700c2501c0754244054000c40700d6120790701840e804075140c1204180010b03119030068107158006d55900c10301d0f2402c880045c1c20000103840c150000348924240982d0700c40c080c0320f02d245984440c144401508654190001440d03c180001c1001996a160004c42030407a803041c0c050f940001046070403250074070390211005805c02030320500558a00312100c9046c10142c02207518404170002c0410560f5500a44012109240304082b900036406000f001d20303e80401c0050910340c0d2640e1120843c3e0341c1808201012540c10f4280300781004900124000451154180801038030034600013079400c00340844082c3e01401000c540250144280f070101802d03900c0c40e600210585c0d29a41e141d00302d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 710780260 1250 710779010 710779057
    0xd050a0204020a09170129030312040c03030909060503070302120109050d0816230c120301030c18050609071803021f080612030909150607060c020c041109190f0803 72
    0x80781e0441d21001008100407c0c18521083c900b01d40000304071f00201100c3c40c141c2c08401c2011401c1043c2e50441c2c05100340c0f8400c0c41019005140c00c4050840030008019580c0340000003603903119076200c0070340141c90091845e02d4412080d088000b40f59007120488034002030f07080d0002e011b00e0086441c01000e1703440700040707845a88541d03684021805d040c0403140300010b21a011030a00d501280c1c150500d0710980d107010403015030707400140d4000d50240c80c0080c075481c41c00c00108d07080d100010030494503520340003c00215030b4441540d660000f00c4c83c507200c5005050b2282641d000e80c1c0680000c0d42c02880d11010f82c4c0340c0da0200034503008918807a542d40000380c8488040c021030380d902e6804540160400d101078240f0781400075035140c0c026541c10800e4203030010b54002c14002e500022003a281d150b11074080703914a82e010802c0308101d0b0025034040181002400c000000c6000d040d04981c842c01c9010f40041d406801c007040c0d80054408400b031000c40954880c1c006649078004c070394510520042e45c04906 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 710781510 1250 710780260 710780263
    0x150302040e0412031a1e120607050702011b03020a20030a05030306040e0d021507050f030c12090d0c0609060f14100803070305030106030b0a15020a0303050c09060403020d050a0204020a0917 83
    0x180741c5c0009070280c003110340c540c924454400109508030381c10110703140402d4007074101000f10500030b0f41075494441e507034200760000502c4103200d405546005160701d140d0b500005d038001060903026402601d60728200081ca07001c42116903280d02c290b03600d449180000307001d0140120003940240c0048404001c0f00c0c0a000d0042c0d103c0761450701000c0540c010540314582c084e01c004245070712409900d0442d01e09084030800e00040d030026600320450420114106000d440e00e0504583c2250154004280c02009603200810440494000502850b281d4100c0c500f00300d4950006c0c12641007004081c0402407562602c10640c100484501b546c80c41c10010014807039101008a40d0703016010b50380c01c1e14507030034240c0c10f070090045041c185c0c1e003100d000800011443c0d1108500802c5000583c0545500b04a030708004060b20300181c40c0182c00d040800c2407444e01d989031011102160303410781310355000c3c1403242003050410842001c0030350024000145018602d6001210b50180c862803104420951641c0144a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 710782760 1250 710781510 710781551
    0x80d1205070f080702070509010f080f1f0c0c05070905060a0611030a030902310b010e03030a1115040f0312050f0114030a0507171c09150302040e041203 67
    0x1101007142103410000d107503c11008142d00500c1030048500c117940d1034000c90b4050600b43c1c40007058900301003090244081c18030000c540311400800070800012040340c1291200035040071000d02a5403201c204c01118010700580120b10b8110f01941d040960f2808014060042110350900c85e05103010042071440c000c074203000080e45030301d0043d401c21180070b0060f0000c000045050703a00c000c00c080c050301c1840319844c0300b0044601304003110300e85950b4800c1403001d036841c4585a5061158001c0300000544002050b40c1c626140d51a20040d24a5607983c10340c200b08034620201e00520304201048103018100d52010a074a100341c0c3c0b40000956240c3c00c440441e041982c80c484001c030a070b00100b1058028050700070314444020140e0710104010f0f502c107460402e03154020503c00c2440180580304940a10178980010b8a111001f0303400c40464800600c074158602079003c0100c13000ca11150b0b0b0510941c180c5002d401c20160000e060306150402c3d00740070164640d0440040d05044407444114244d4101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 710784010 1250 710782760 710782771
    0x10b100512010918080d0b10020703020306041704080604030c0308100b030402090c040b0c0a021f0c0605090c040c0e030115080309010509031504031d0102060c0405101701080d1205 79
    0x1c915034204240031014010800d0f600110401c0342e4044004500c90300c0041c092a42030000029807151a00b042c000e500854507403003429900800c00410140c2c60214101c0e500c603a104181585c08940806144810f0150340c100c3e00592141310104420590044003082c200341c000d0301c80c0f0541d40e58107051050618650300440f00810814008240142084c044c01900150300d56402d07070a240e10b400c0000510303081544201085d80c880707528030b829400d00e061803c0b0880c5200b025503040400b440c0018021152611004150654030350000b00d924005000c0c05000002c000c005111048116100030039031022004094481d500e400107890206040c800a0021074011030041c5003400e12803030040d200e0b44c02101c8803e0300342c080e0301903c582002c0600c0d0980c0c4281c0c4607480d0305400c0f082e14a025403080031803009a07815507020a052051402c4014103540480d00101c4421002d0000ca10040b14400c8041001d0410745a4100003c00e17900f801240078030303a080640d0380d401443e0418012400a60342c06450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 710785260 1250 710784010 710784037
    0xf08010b1603030b01210b0406080a020f01050307090f0603020c16080c12100906020c0f0a02180403121b11030f03070305070c12030603110111060c0c0a060509010b1005 74
    0x1c80c2000901a42140e02000d40505003080d13031010141400c00411040c5408141480d80d80f92100100c0c5024440d06016100c0140140100280b82d03000c9618030302d41c00406414001c0210002e0f0a01c1d20401d0101d015041d144102405079680b608040d000e508860300015150203040d03001032813085a022400100d8070044010890300021105020a800078001503604a00603903450902c244120300500010a01c9448016a079070954003516081209034062a003c64001540030750150307070340d0002410b010a003040c07510003544032445d0135604034484120541910f0f0a210001c0c540b56585a80741c503810049842e07a00d00349440c1c05040b0344921a26142c00d581034800e00200c2c0c0340c0c034480d900296210045007000c3c0f200c068562100547c940345035042c000082d489880a0041011050402d0320f046801c0c00c00040d03030428114520703180c80e801000d11290700d2001c541b0328501d420400014003040e403c46001c00807820210f100e00c1c003811014043c1c41c0a880142200000a07100e4003c4400700140d111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 710786510 1250 710785260 710785297
    0xc07090615110a48090b010513270c0e090c1c02031803040b030a0c210e03090612010f06020601061b030905090f0708010504150e090f0d0f08010b 64
    0x4003054141d0701c003844040c0700541142284044000d07002c50070b10138600d010303e0802e0b405140c58a81400d13180120f46081c10420148241ca6144100152001c103803142c3e140c81104000c00c070000d0f1842d803c4a8000301d20041d0030039208005031900701c1428684507009856460300ea903144d002d150442d110321810002c81c040c43c415180c00c0051654061a000340782c0303011060046008100d11480c50300290040c04170310400206000b507014451040030700d113007990300304040c420b802d540c01ca8100050324800d01e907400e9103800d00030008610520845106400c010702d00d42c1c603400b0740482604e88200900030000c0000100c94046416400042d4280c121281eaa550080b4a215400e9418051030b5900c404c4051010100c0045456912262031501c100c4040100040341d01d051000142862010b03031007140507515011815214443c030001500a0b102a50098007107925030014991802e1802400c3c01075a0241940001940d940500000c1941140e135480c0710300c0381d0b21072000c58038621610490019a030141ca = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 710787760 1250 710786510 710786543
    0x60d090605180c04020310120b01080c0f0d081303061104140409080a0f05040b03010b0c061e01060e0105040807030302060f0a020a02070315022b0c0203040506040b0c07090615110a 79
    0x2900111f50100000510508072580c0700000b8881098429044507001a503800511000b2400c00c0a001c100c90101c03012541d0313204110200c4d0a000c030900f4090315001d0002888004011803245010055502c0402041009a803072103804581d04503002c0e1201c220703034207249004280751500614070f1158104244515200d151141a5008c0a4400c04c0c403003030003418840042c03000400c10166000b4525030103000e59568150190f1811b004c0d004004148001001c000e00a0b91402c84031041c0c1520198104070a2032425000165841c0c0255840f0208a204048010041623408a0094002c1581203141e100e2512841da5180a0703000d4440000010780c00040c0070030105074241c0300c0d18141031000348014a402032020800840403910a00e005008070000719100f5507104910641000750014405542000d052400244040c0f01d03500c5100000e090100b01340c110315005000550003030594031420000c4a070340d40001c070042001e8828003408110141c01c81040d0450100b254007000e81d02494101108002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 710789010 1250 710787760 710787769
    0x203060f041806050a0603140d080103030f140c07030b01170c01030930020f0102040308120603012909101421190b09010b01050403170702060d090605180c 68
    0x25a2601d28400710b07a0b0b00325002043c01442054001c1c140400b010031030900318207007000c0078002c40d181003400d60302c407264510003142c1c4a010141034940c5440c0c040700000c412340d000c542802d12140850b500507000200c55841c00400a800c0044901c10084040940c3e6200c00700c001000d00c0580c48030a03500440d207110540d610030b80c4400c000c3c0c2e100703140c0149103c2e0144420700786144c1d1705104240d03040076100a042c0c0c2c29010480c1c1041d54100ba0000e51400d801e503a40c204007070041480c0042040d60000100d61a03940a41041400c0c41c041c943c40d040d407041d03440f2584141128032560394024034041c40403ca00c01e030030230380b0703001503e0208811030301c2d14510405010700d20b5210303c0403400e20801540071320f0380e0100501c9140c2155442d003c64036003420040c01c00c6050000068070b10000c9a1500c40c0356aa1a60080140c1781204d401c0781c405000c10300540d041c041103219429009501c040009015800725840740c0c0042c824a0141c0340401c001d035641e03002c4a40304403007010385042d19070016900c000345260 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 710790260 1250 710789010 710789021
    0xb070f030c06050c0d0b04150e0c0706021315030c09120f0210094205040b1614060709270221090a080a0309210203130501030203060f04 60
    0x20a1402201c08502626034400315101038500c001d11400000c1c404003004158090031514850032102001a0032500ba600c2d0003820070361280d1f0318625100b100040194081d20300392040290000010766441400080040b0004094021010790910180c4555282482486a44180380c0c403a10384944450400d00c42d5003503109400381c115038109603442c000005882d07020070306190f01c6080e169401d11504041c244803c00c803102a81d200266402d030a0340c5081e01144080500d04c4040402c56180b021000700100c489110300d40203003031143c50002c1c03200614414101400b00550080080b092500c1c08144d405840f180160391581c001003044034148020710078072444c4582c41041c11107030450780c1e4054010009a1b00b04c070601f49000080070310b081101c0703403090007001e0b4071031500d0000e080c00805644e110341480c09230a007080c0c00c0540d241424010400003103604000c0517800f0341c0d1100000303480d0320002d50b20740c04800c0b50798940e13500380000507041d4028002c0e42d000d07260040100c01080c9086051200910 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 710791366 1106 710790260 710790263
    0x131e090f0b1302090f0103140604020702010c06060f03034509050408070209090d02070308090409061812020f1f0b10030e070605271207170d090b070f 66
    0x207051008d03240d0048044a0042e07c8e1f0b02e090004a8440141040081146150060110341c11508880f40001c0342d100b0364484048008940c40d0382e10266082c2c0a44401c036050b510022040640c01004c0402031784182002c0da4556039880d07095007070b20000c0d641036451400c0000c0c103009500b00301c603c0e00c1d88520460020030b03c0743c0e02d560303000f0f43d20903075480044e00303261010800d0760b580d41d2150014525a41c01c8013051000031466407000b1500181501c003200c50401c4004142082030000c6010802c070460807000d4095040c211500c26203012125400c03052545d81d920780341c80c065541f000801c2e0900420b030750000d070b16103810200e83d1500480e5003090040c0f1a0601890141c441307181c0c800415140940464030210b500c07407000c200100e02d030302d00341e599030702445902195044071101300017482c521150486011480400c025100c00003103010700740c7c280790200905008100c0e5807801d0860345 = true := by decide +kernel

theorem cover : BRFrame.Cov 710611510 710791366 := by
  have h0 := BRFrame.cov_init 710611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 710611510 ≤ n) (h2 : n < 710791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
