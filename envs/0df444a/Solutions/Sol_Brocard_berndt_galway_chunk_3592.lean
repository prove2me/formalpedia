-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3592
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:06:51.233755+00:00
-- url     : https://prove2.me/submissions/9bd37920-cc59-43c6-81c1-fc090bad7f81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 645863309 ≤ n < 646043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 645864559 1250 645863309 645863329
    0x11060d020910110d0e01120903110a0311070803071a04020d120306030b0f1023040218040b060f190e040c0c0210020a08041202060f0309010603110618 66
    0x250440c0c0d0030007503071145441d2004101e0940403240c41c2c50031010151089141041d1404180c03500b04502c1903104d8800ba03801020018103050a0200001c03030075214507040e12450f2818600342c00c4c070320403403010208140d448040342c0d04502d01d040035165100e54510703003141e0b24040c4510041850842013030592107080d90180c00c2d580540000c02d0442d40900d540c4800c80030003c50081080041c1c0c80303620078014015940500b035040007080d9504010703031600c810300c982e00a102e4003c1c8141c070966011105480c59402c1c165456400005000b10356500b141099041e04807181c0a215019606004441c00140340c958242c1e0300079441c0d407041601c0e03c00c207024a030000e2003a901d0200140180310100200035200d80c40740d840c050b081e0b43c65850820002e801040904042903900304215401883d8007400218030500340d0f0102c07210400c42c181038001e5880051458010314140c801860340220402100003415041041224050150200303041c20940a0100502c40e24650140c40294822219001c0c140b1107078003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 645865809 1250 645864559 645864577
    0x1d01030203160f230a120b0106110a02040f1508010f0e010b010c032709050f060f031b030c040c1d03120301030206090409080c01140a0e0604031215060801080f06041106 74
    0xc1136805084d4400507034501441d4000c10100c1403290310070b000700120621450b01511460a148601d183c002c0c8400c1da40d4030030f03644000c0c0129280d41700e0b9075420075590411550f03018040725503075000361504607ca00a0501c805001262414860850b0840700180724443c0b0200040c1c4da00131900302952020340345000703408060628902511130a181c2c0c40e480a4448018010781040401d8601304104d02c3c1d0340765000075010a10801e00319140d003a00386c0d40000d500001592890300080341c01781c210002030030640d03084003031a005400d02a03205051980607031f54000500300701681e16084160b5501345907903003060907440243d0460400042c0050b10300b04002d0300305600000d04c0496840c4003540c5852254100005010041c0c0d19000c09800c048001c400e90360f130049007104100810a0540340041c2c0d071b510b0151000d400d00110340c031301c02d491800981000501b0b01000600f16a40e90741d544000b400c001091103490800e00078100392402202012071030034015500561014a01d1080004010b51a44161342e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 645867059 1250 645865809 645865859
    0x9080f07081309020406180509150a1203050a1e08010e0903091201051905040209040201141908330108090a02130203150a081b04061d01030203160f 65
    0xc0c070003610711440400d0300a00600b94004d40c4031803402c8006070103524504400281000076880600840d1902420503a20481401c26801d8501c407480c0031401251140e00300311998010502c460b000d05070020018603140b0916610300d05a103007994840c52401220703844a100060071900100311030480f82c50225003090304402034a190084141c0059441c1645060011660b510b8804008004200141a007020210303004107100a15080c3c0c002841090010002414001c4e041c6003851540421029206998141a6940e10303d9103020b001618440b422200081800980084900041d2000f110f80c441142c44140b85c946039202a8015184600c1c000c2c01a01c15205902044c0003603558074000303540c80408200010390300e0404100c1d61400c0191100c4070741c01421806001c02111000044100c840c807030517051107802c00e6041c400140901140e60140c0c00100109103421100e040300728045049078801c40c02c55680751b410100c10100383c0c1007440b075107151449902d41009000318044070102456a240c00f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 645868309 1250 645867059 645867067
    0x110a0b1e0d060b0a031b032708040509010b03010e060d1211031e0301090c0e090f040f0f1a2d060307031a10060512060f0a053109080f0708 61
    0x580b0489a4100c0380800c0d0001361191004503042c0302160211b00d20443c1e614050112810507040700c0e51186d200c1100600346038411184005004001042c1d07405044010107507801e5583d611100705c0c4a410a0158030301560031540422210b15010002c2181141e0188910303c040d041c02c03005840d560009080601a07000802c2000050003080c0304440c04014041c0d0025129418031491000316511100c0320403c0c00914110001c055590640d256170220004a001d145660380c0c0c03601d40400400c00c080284905034195074003003040224880d00c1030301c010002246809031b6891076051204403007543c107440d241c148040d1580c100304160076203d9010002604440019a99030b440500a0b031540c01310000c3c515016041c48007101d41d0182c5080200350a1a00d141481101d0f81c1400b00598041c0885d4480c0620307071a03110031903d6600710789000f8a4014109210701c8164a0100c0c00c0c40d4490380d159800340c401e00b00c4000c0300714492007004c508503001b494403410030703103111a0103515501601c0c00f03594090041c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 645869559 1250 645868309 645868319
    0x1080403091e0e090a030e03060105030319031503080a02010c0e0f0103020a030207020603040501060303090603060b030115020a17031f0e160504080604030f08010b03152b110a0b1e0d06 81
    0x60075071030281400b04c0041001214904009120b01e0b800750a4500c60340140004120360342d8000140d45680e00046070f12031303030150a46400d0f801131101c0c0038070700d141040b4080000b007030104640281140e001030382c0003881050341c64803046500303004100000ba0b004c880c1550342007095200c1d902405400e00c241c0ac0041c50482c054000402c03a8008480c104c0702030b03448071010f004050344009910010442818188592030405400406600050080210740e201610b040b610152082000c034030390329003103d00381442c08030515004134075034412552400c01442954020304600c00b000d650400321101241040741545401d5201603500c054038034241d04100c0140030103e40f0a0061001c580a07a110f03464a41d5044810480a0241c04d1305920081d802d040038801c00100032000e02200750032001c201c8180f4603003208144955840300000e890543c074910000c0386402000004290300c00600b904035240d240712560348024002610940d02c400111203400c442d186109103611006d00000c000b01207010410b140c40b1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 645870809 1250 645869559 645869579
    0xf0b060d1502030c0909010b0901020c03030705060402090408191206050a030305070b0705070b010e041208060904020f0a150509030136060b090408090103141006050d111c060501080403091e 83
    0x388c000400000002903034280c25a0104488200300301c040c5c1c080c0d03051020548819031145030003000079000342203440000d0100310401d41240c504200d48440540441c07454607000b000401d40c12000e6410619100000c1407034a003280d07040f011254190b944900e4500e8540c5d88095085000e1710940601105010b007000061003480481e01818540103c0c3e2020f203000d04049500e00c00600d4044140805d00060111035281c0110969000d50191040012143d13454081240714045620040c0c031502e101034036442541d4010010980308100710028405510310000c0201e0031541220308401000d11080d410466600207090003c00038062800040c400c4c03281c0c1301040c1200c1301120111020000098145219a014441c030074034500803203120000303854500100101300d8176902a0400f4401c02290f001084903150300704108250001060a4442d0039190003044c4540119070f01c8009941404404209548143c219034403458069403000e40591801801d2588441c6100038102e041d0b0224002003250b14003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 645872059 1250 645870809 645870811
    0x6090a1707231209090403030b0111071d090609190606080601090b01080a050402060406030b0a050a0b030609161b0201020a02040507050c0c0616120c050a0f0b060d1502030c0909 78
    0x1d049040380c490742000e0105400d02080c00c244415000f028490340450703483d041d0a0b103a02a50608000501070341003001681c10030b0240c15800464072403114081040000202d00302a145400c0143d00341540301c0c0001c00307032034240880c3c403502c0c158400914400c015221410a200030b0340198400900035440b580c8450030310345d0036048150681d8645039401841c2d64448203072540044880420817907414142c1c0043d159100e41c2c480d541c03c0585440000e001c944d0341601c5440203001c0103204080195031002840f01c580c01c112a0103101c1c0e003c4500080d102d0030fa06c0d2441001005903500c0a2148101001800c032000743e5110581c114442e0845003001600e07244a02e03401420346403541031316404910f11841c94031546500ca98050303841880040c00b0301818810f040b5900b0b90100c580300c0391139580c00044800714643c04c006002c0e40701d94031030501031003181c0d0f40b0300300380c41d01070003900a441c0e6600040c08868040d8072001440442514486e00740003006a014540142c10701c001140b40451450004181d080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 645873309 1250 645872059 645872093
    0x60316091b031a010c0f0b1e090d0207090209450714070311010c0c020a0506090d0209060612011d01060c150e0c0307170c0301050f1501020c0d0f02100206090a1707 72
    0x3000c96a440da0141c1401200303900509c1f000040003508001078000b0348485c50b500c12403404c0341d00481d410000c1e03500d14200b8002841e100030b0800c26520707004e041c2e00d120b02e00031140140500c9183d42105e8000300281c0c1d418418a03103521605145002c8050014031075000f614280e04000c0303c80c0120104003000c1c01950a1242259500078018009004001800c911036216601c504400c1000000588510f14800c00c281d4048403000030340e80d2a100030031150b20440c40400c2c5141c0460001090420302d41411034443c20051000803543c0e03880c1c90382620014178079403001e04001c10000c00100343d1034003a0402c1000320b18801c19140c01d00141004607181c140b650b040016180b5200400801c052000c02000680342c00440c004d20071414409005101000040c1c60035941c681d40368841007069000300315000030542c001d0906c007291500c2e0308021035070000c00c0504070f214820301103100707586510000b107050080302d2403009010050415950741ea4a800d0941018580c02814015080030503500c61102038044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 645874559 1250 645873309 645873331
    0x2031009110906040203071202030c0c0723040b09060402090a03330b010c1e0804060804050f010c020606060a030e0d0201060e131a060316091b031a010c0f0b 69
    0x1c84400821030402c0740145054052031041c01006099588100f482e58070b074a10400060792078641c1003640480b44107000c1035040c148241c0c42d00042e140c41c181d0181c2c400c404841002c01c45043c0c50000c000596049800f500d600584140102d001451b1a5009102c82c000040c411080ca40e5071755503131072081e1a8042007410304180790b052200140c001c09403200c84c480f40440104090820b0100180c4100c4c0d101e00701800d200e00e000c813500c20040108034490642c5400510040d20760340c1e2450700500b198011582102d240c0505182000380c004140120182c07914290040d00c5d0301c2d954401486081e4102107110320805403242d01c4420549021b1100c07000050041e030000c5901410600440e0382c1640103010810282d480c100c40c0d40200c0d034041104156524484054481e90b202c40e80007900d0540c20141812400909400029941b0140e910442200a14440d04030480c0400c032419411039107080940d421120708980c0d508031541c4038007003010907540304002005041100d5100d10401c1c8000f210100442 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 645875809 1250 645874559 645874583
    0x31050105010f1e05030402130f0b0109080f0601170a020d050c010801080a080405090a020c010516030b0114090d020102010608030712021b03101a040905030d050a150e0402031009 78
    0x165034006040707459401c1d541009100004040b28921100f00c40d0b59900c0308014000c00410115510392109a4010341d4103402405015900e10000b801402520801404204000c1000401800101d100100380c40c03204043d0040da880d00a0f540d01880c0485aa85402e014000000d80180d680600b00590a401100203000300105000003410424040c1c004103e00c0d4000030b00f41d00051545070842d02a1201665000c0580d1035030300415007e130090f42c012502da542404e04101e8504d900d100144290b801c02c1c0d50910040c8814001968009813490042c84482d20410502e14103040903040c403030742c9900c1072000050b0556900350040c116040351100300c8412030340c030300101c1c0607903410044c59541c1c402d5590745800900c0c182c40002d40d180130004484076100d4a60310264085200e400b440981c01c5005030051218000380d1a003240c43e0350142e840a03980c60714207004240c0040355442061300010010032620043c505001900018082c0200f080b6854403404080c801e8040c00c5015481c04244101217040003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 645877059 1250 645875809 645875819
    0x20406030501261b0103090210080405060a020f040b1b06041b08011109100908120d060f05030d080a06090227030d02101104030204020c070602070b070f02310501 71
    0x460000c0d4150002104402d04002c503000000304440002d0b0300316413000351503002c80c2c4d80143d02030900410041d510201c415100162281c01c191080c1c41140305000755040390b40c601000e9812401103840d4186010340030320050050300020030040c2076954510b0700454031078810310002407603d0804c550032100c0c00107034481203a4070f5018bc0c05090180c01c0a0000b44a50a10400340c07050b1801424134042c03141003140407090171980100c0b00e91010304007a4003a40c10344c249140c1c10b00316035808560313219500d40c5011000a00c2040c1c41020b1425200002c0182035181644030301100c002c0c00150081490350350f2000d00095003140b9100410813203400c080d03003c017100383c2c5000f039402ca02440400940030342c0040032584045a80842d50303a0021088200009020f403442640e2075550080350402034100d0b1000510490040c0005180030895100e40c1c210b562050704d400d01e6552500840d0710043c1321000340031b4410700518280c0300e0329600040400140c20100e8404046e0f442007c1002102d601c02ca94440052003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 645878309 1250 645877059 645877079
    0x1b0201020c10020f07020d060e01110319050112060c0203040e01080c12030a171e0f011410050f0f1c0912140301030b1b040f261506060409020406030501 67
    0x444155403002c1181802c42c0150003118034452042c0082c0301c0c00441b0007803400c114440c2d210fa0240396404008114500200300c10309200d40c002d40d00d151a60b0302a00240340e46c0059402164183c460b00c1410340c52004031940c030b0308080e0a10007016002c0d80014003000c10000b1220040c10300902080005141d21840001840800b004c44001c1412503041044030000e8603800c040d4903441c1071001c07518449543d0f1070710f0f1003100d1420115800321007480404140805040e10000d280c2c10382d0100c900c41000300340504200507a102001b101003000c901e05100d4038441c0c61020010703100c1e9812421500307240c1146290200c18801c5801007002e41259958103080a010030250314003e8011241402c070311030310311400c98007042d001c148402401c4404000c00075030400e101020400c41004035844054480f0b031119020700b020003640c01500061031000345280004004540300c04040862030303000c2c0900701c8261407100000f540050041c0d030480b204110001e007281152000b403005000310341c5c00280a504100c1008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 645879559 1250 645878309 645878323
    0x222091202071806060516060b030316060f140a0c0c0b010612060506031e0417030108061603050c090d050a05070f0f17031c0f0203070c02122e1b0201020c 68
    0x24940d070f240603000d002051b04102210f180c7d840c540c500c5c0d01071440c5c0e49131100291581a440a030580000310b00542449204042d580d03100e0303c58070042c4540407010010400702d44191260807003c03010380b070102d622980340d5030041400c0754041c5880d0201c030f9110340b0b4901500300c00382c0c000030000300640d00a09034102c4510806010304802c48801d40b5605100807844001c8051000d4014040c001d50089001c018450040342c1504940000c071545942c3d4603c9116210102180c060b0107a48500c1061540c2e00d00c288181ca00c980762085010342400f01d0f11051152103145c0403c201c4451144040071400300c2d000b080300c0b000030720f0303441c00307240f0240e090186444559186500c0444007031142001c58030600d90100070b65100c0040307415100d220942504001001e000a84860707040d451002061200f099841602c15030024020b4074407000504106800566421903641c001507044800400c04600c0d2541e05480110703890310601c007181a1908010302824503020b038814801607940000c8035410b07044113000c0d070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 645880809 1250 645879559 645879599
    0x6190f050106051e16080406180f120519050610080f0604060b06041a030a0b0d12080c28020705030f0d0f1704060504031b022209120207 60
    0x1440194075140740a031607809200f0910034101c58a242c8941c10070580d03429920310000010f0002c148a110307041c21b620382e50290013034800090b5070060303e40802c4aa01607550441c0c8820350404041441c00ca909c62903a41c06401c00c540c240503c183c2c0420740310011903001d8040303004030050a5582000342c03072114440d18950002e2a036030405040551450070118015900c42d030401d00100d043e0b005040003a00c680701e5034212030a2807003001554400b032448900654410952a40c0400904000800700700c0d080851500040500b5030066100010300d11890540303400c400c1a0501d942001e0348044081d4014009080b0010740c0f048001c80300e0f5002e50304000940040500780c018011124608d07a0050304c511482c0981303000c2c02000200200d89901c50f40d0800c6c205c003600302c8040118100f5280ca180501007d40b0190009001c05081180d50024144c8078041d03c0d43c028000e0f24803805076400c90f29142e1034180e4440e407160f40d80541c00007042400d501110b40b0308840c4d01a05030981008191380501c0e40d00050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 645882059 1250 645880809 645880811
    0x11031005031b030604150912030f0f05041e030302090a080109020a051f141605060f10120618020402040e010801050c1305220c1107080111072306190f 66
    0x20b41d8aa51400701e003442d003003508800040c030b1151401c4070280c058200e44000911154900c04c3c3c607001194103902504504103424004d0000030300b821503134401e942c025600549000400b80c102480010700d96010304029101e8100907040c000d0b03241c00074824000a52046925944500c203950441c5010301010000c1c2c181120004401c1010b45000030700a01c5480050042c0005144811a0100c1040954000d40b01c0c2c00450788200c1c00d0b40c58402e45445007a01c81c100103012038004a450000c5d214050300540f1840703107284007507004035204c0303401400e40810440700c800040080c0201688560005102070f0101d06450b0940d545482020b80c210707100104072041e01c0c0d00c244550f8502e45180419031040743c0046a842840350104032040d0a071309124040e80c0720842c60604100b90103078000304089038900180d001d980440f507994a0790350a8500401c41400c13041c0c0c0402c10700c4002007003038070078002d2030b09070b11030444880d882c1c000201d1424805132803409240c0980a600b51894202d0b00440b0000541c03518 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 645883309 1250 645882059 645882103
    0x90b190b0f0a03060510030e0609062404200a0206010608010506040504020913050a1b1e200a110406080f0c040507030b0a170609060c07030f031103100503 68
    0x28a0340041c003561807101003680d00020a203002a210760002d401500c402081d181420505400281c0240b80ca204122424019003000540650001c030300f90303104a030301d01101e2510111000410501d10850313a0307440e41c400e03a00c50b00381d00040e4800714400314202d43c1c10b100d980d030b07000b400f040a0700d8080305030311040c204040c0750018061a11303080700751000c0701c0c002d40f409601c40150000203409810041c141244052408041004201d05900315020b42401080507170b41070340c580c00048602030048890069030605000d059202144692440112040d0003402c0b030640f0b40c10503c0143c1007000800095030400143e0b25420f10328585486644000c01d4000e006109c4041e2104003075403100200c44010b8440ca6683c000140701c10f0094001c448c2403100203000300c21080c3c03600f41c0c3c02c8410000d0020811070384581070006104280009490340282001c602050411030940d03805c480340c081c0b10118100f01030312180303103021488c4401c1c06980204411025000c80300d0824040c1803800030303030400c4c01401980c084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 645884559 1250 645883309 645883319
    0x9060705090607030e13200c070e060a0308040b0c0d050403020108070c0c05131e06060c1118010b031509070909050a020403081b150f180c030601090b19 67
    0x411640c01078001d5601c6901c8143c103040c166509524044038035040751241d01440d8011240e94411a804124042d0244406c0804c0510301560f00441180c410141d0207200103024064466001507400440100171880701a103c0d650810355130030603880710003071040100c0c54046211041c4140076070070307c00707240203400c05207580c00007001104040d04040a02c032866441c0e070300f4460201e504101a200142c0506512148000010001c04030190a14980c0b007682c00614035064040c011038080b142190703507a0101c0e0080307488101c40c8100c600b0405902001401d44600302d070a81c076165500a01121814548918052a00311800503101801c1840760385200700b0801e41c690040d40aa007951a41180041d04e0b58664000704002e11580d00042d2034900086516010307285038806900030041520140c9603100c0c02d458a00400410a030740200c0b000102c2c6002841d21650f01c00000b4003b28504200c0380d01842441c04682003071000c4c4c204500c0940c554202e6103007410504c80ca8100d0500141907200094030306 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 645885809 1250 645884559 645884567
    0x80411010224061311040305070b0304020a0b0a05070b1302013c02030405031c110d0903140307021e01030c0e0f0d0f12080f010506090907120e0a1a090607 68
    0x10078050b1210041420106607191542d81c1a04e2103885032040402481e5a11840030059405c5403104a800384200c070004103442c01080c050700d014560103045828124203101107810356070440c54540b0104030050000078041441c013920035015007080b4284d408220154000140076060442c000020004005419003102450354502101c4000d061101c0183d8a50a04200e056100310b42c0046d502d885040108002070280d21407008860109071110000c2641510440e51a0449032400e40041343e125541000800c401810342c0340c4000001c01524030701031743c5900003100076078a0003c04104245e4080910740b996018481c0400c82d40950525410038908800004e541d000c00b0501d4a0240154000417020070081c030840c0316106601c46550ba52504140754014044c07401103418070300c944201ba0000901d030800008a5a19440140c14034000d90307945442543c031703400320794840200aa48c03100b130b8442c030301400c0c4070300703602d0303074401c0c0901c00348809803104111005c04003509402541e000803013408800c40d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 645887059 1250 645885809 645885853
    0x1060e010f14090a0b090f0a0303080a0908040306020a170a0b03061303051902030a14090d06051005060a0509030105060118060804061b030e010e0127020402190804110102 75
    0x1d24501541d01c121038605a800702e0142e038020a0304950b600c40e010541c410000d015002e103550540d40d009a8051841c1007041d0090248030150105041e203010803800d224540100c0c1d0151300800d100f038034241e5aa5194030481c1d00c074404002c00900f104a542d51074a892b40c0f01d03250440400c80e401c1c000e4404000009031144070140400b200300751401c04003400c146c060415034641e000c43d61001d503442600701314040d403264042c00440d00001e00c0f010726012181c043c0801e4a240305006400c000005040c0c1e902c2800600014150b41c090b4003407040005000e6031114010401400281d403200c2c3c13200344c2081407609440000c1c2c02641070158850340c0070a204440384007501190018903001001c0d403600d00745800104031000b0b26044a054072010406a2905a00702c45038030044d042c02001480320a2003903030300702e4200044030300c1444500303c00880c401d411103010100700c50004000502d0000c184000002c4100b0009c180d01c0854035040400051050200c0524035100c000e001800c01c1d201b0058681d075503480 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 645888309 1250 645887059 645887087
    0x3020a030548031204060f081006091511101e0501030807020105130801061410021b012d0e100201060311060a030b0a0801020d0c050c030406050a02150112060501060e01 74
    0x80c000e00540320b83e4041052800440c2d441d030206075601e4441200070702c03a18052072a08085240340d000319200010041c4e18000b1100d071607588089032030a18030b094281c2030950086404001694184881083e414804841c009042c0c0000007043c0307000043c45987d0040086000a44514200c010400f0444c0c4a0445848990901e486655400100011850840d4942212086600c1c20601140d2016104229411928100c6100021980000701217a540f400642c2c03d1666109803507900c1486c3d4003030a02022a42c0c526841c3c80690440c041d49c001e0208210440f0f000003628546112020f4180340d010344803952020310090110341e0440c0c0707484251403040300311107004400001c0c2a01049102c1e42c0407403045000104014100d6560740181400303034100c042c4501800b03141c03681e02c0078250f005d08101c40b4411103500c00365042c28070700356041c0c0350b9400490101c0b080d0300814808880d44452104d601c0d018002070014602429058141041103d8058001c9004e0001080f0602d0380c0740e13040a40d50400701 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 645889559 1250 645888309 645888433
    0xa0602030612012f0a09030b090f01020d05010915030302060105150d0c020a03110d08270307060906050a05010b0909040305190804020907020c0d110a03020a0305 71
    0x744801c004114150255019030740a5440d2000390008100f580c0700200740f01c1065124a002201c4040c201d400d50301c035049040b03000c40c52401c0704000050003080000d5002418000b650360440340014401e00766800a001844155070347d500521040c00c140c451a903240f146e8140030034503103065a0300a9030720003040c01110704c40c50449525880070a1142d040340d0000c0700002d0184030415200d503019503903011a400c02c501190617201182e103890030000d0100c07101c3d056682da4504a41714201c405510054000f40005800c0050710610a140000c000400c0881d1241c0c9000410f04a42e0814008540024040c0003002c1c0c20700c001000707910086800d903400d500e0100c0d01e2031325940742c5150603038040c8503803541c01c1d0021440302e81c4240401c1c2c01c4003155124600a64440c00e10b5603402500726152058241c1095002c99440402d80206085c05555040c2c0c26010300045001600da8000800041c41c80c3e0044810b540301c0c0820350002e43c120201703039042c0c40841c442c0303114142e000c01c0b516028a1150700e21210f00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 645890809 1250 645889559 645889561
    0xf05030c030910020f091318020f061e19030204050105070201030f1e02070b010b040308031f031b0816150507020f0405010b09010206090312070e031617010b0f030a060203 75
    0x40c24050108580030700d0700b43d50465079405141842c03445e581000e140680f00d917401e1070b207020541c141c1780038088600024061055804e84d880d0f0800850f1000d5860168000009100142c8444030440c003030300b200d800003004541c81d0a644070b1007030701c101881100c000405005000c104910798000302503c050942c24240420030b2005824030600408142d0801f03040c00b1110800c11401125a5005101c1540140e641541c960f072030b54010080d51055210040c0410810000034003601303c4500c251101080c2e4020800d0032a0340c039141c02202c941032081c0f0034003240c41282d0800c40c00104100000720b60300d4880c3c144074010710300200d1908582d030400403401400700004c0e00a08542c0c91381c08a01340100c00800801841d6103600f01e50030b10744c21050200d80548654000f0541200000003502e507800b03039040c02d100343c1c3e98609200f01d072042041c0c0200e64040c41010060a1301500c4116003202400902840c0450250340c610070f1825034260611507401500c0311080007109440c0812100c0800d80c01c9040540da0f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 645892059 1250 645890809 645890821
    0x1090507030305070f0b010605040504060902070f060e1c02150604230c2a010606080408090411040305010203042f01021b012d0e1e09070e10020115060f05030c03 71
    0x5d0f20460000003001021240c1c00442e0301f603042005401500d40644080026980b5203030150104e2040c440045d000030380300000c440025400da040114000c0a9906034ac40d030cc03a626080ea545075030848a44400740e00920300c1b40e24410525070300c0c40c2d0302030021107090017000e1304010241901e0800c109034010003040000042c29580401c8202d90480e505400039181d200c05110707409006441504050300741d94240800007615601c0b500c0c400b8011600155180d02d89241b84003040002d0043d0038106103003500038000000824000c1c8041c5100f18003e12070012010842d00d4072034020300400c4251007080318142201070356664001103030021311081c46d800340c40c20b103500401a641c0040c101100c209a044d0005550b600c420a4041d505c006a0640c6450384a02080c104001c050032947c80c2c80140305200031440e086514041d10891740050060401c0e484404010740414080c1c2d500483e0303070015039102c035010810b940000a0380c000400309440d203052a41d0750940010f2813448050410000c991000c404204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 645893309 1250 645892059 645892073
    0x702131a0a0608040311011d0f010614060a050a020106030c0303030e21070f050f0a0f0302060c0306150307030f060b0c060105030303060d14100207060b090603010912031a030115030b07020109050703030507 90
    0x84001c440800da8600301c155841c0c41d40d40c54270b003041d10f422075080000004007032007045242203440d40024805e900b01080c0c0e070000c44d21500003010503800c641d212100000400c000d922800301039030013554041000401245070310300e403400c20bc0c844c0d00e0186540100c400448820029030356900d0380720215000d41811070514900d480242c8070000b0b540e005200308041000002c03503440f6125032103074007034802680d41c1e0a81d0942c80e0008a8000346c04c101c10681e01d400402e09075004540c000b905040002e1240e050044400840e10380360061040c8900000e00c42c150404100401c5004000880040d881c5141c0030020036095146190002d100354890f048607441c0240a205809092010400131915403405007403100c09000c0e00d4661f00d015150030f801040c5079080c10301031901d01c6038102c2d86031070507510f4038001140100401001000c07144048a0f014841d96820700403d400ca01c4000c544441a03420341c10000840d9001428450540e80352030428000980003007220021a50107051603915041c3c5821300300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 645894559 1250 645893309 645893321
    0x9090606130f050703050415050c040e0901021603050a030b0901050607260c1b2e0905190f1d1914090f102f0702131a0a060804031101 59
    0x60202401c1c00100040c8030307455070181f48281d008156440c0c0f2025803900781d42c12650180c851342d00d40d01d8100000c0c0500a1811a215040202a0001840d00034203100d0040503081c4001c0440001700005140b25040e0b030326005080701c0f0070046032021529403401000840b50f1144c0c1000034645440e42c5a00455660040c45607140089072007001030303683d4240c0201a4036000c40000c41c20740c006902c1c068500a041c8a5101c56207143e242034a0500154482c0d8500c1f0040444c4030b88c1820030140100101d038030745644581c50b00c00c600143c7e04041c06401c00540b1000c3c1c4c586604500140042c2d40c3d00d580f0144241003040d0340298060130105592880c000b10345020300301500030b001c0e040303042106205014000062213802d0454010946118900c9194010240d4400642114411400c1c5c50214021011020300e241c010a5804d0035501d8101242e000c200384c0310384286100c03507260362084c0c040c0e1000001d01d04050a40d030101c4030075000a00700f91015045680260010301000804a0f403205400800d500c25 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 645895809 1250 645894559 645894581
    0x20109120305030108190201080a240b040305010e03071505190504050303100510121119050c07061404180b030f0d020f03130b0c1006090b0f0909060613 67
    0x28038110361060030068501e610a100300b04581c8201484a2110043d50b000302c3c3d0b016138142d55102a586442d10010050844080f1441c4030510711502d4441d012a008240c20041c08815111a11240b95040c01421940e02d100c01119541080100d0400507180c2c481c200340c0341d82c46c19030000e200c2e02c928030020f45484800c8147c00f981ca1070032090209121000010310301c910081944044020348403401d001c0450140301030300010038070507181f00362070500b00d400000c0c24482c240c2c00c803402c00c2100d6416403103440d44c0c4148c0b180882c20011b450820003105120841c060000303414500781009540d24001300c1485284640701e81410f0b6010420300d0300c09a50818909032100504640750454249010b64031161907000100262052000364600250044181c940000310800107104c41c916144c0c490712207030b000010400b518040e800000c0e448000c6481401c0191001b0000041c24142e02818400000c4803145030511800356a03040200c041c100180541d88058262006039203024003182c7c64000c1c00c080908 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 645897059 1250 645895809 645895829
    0x3091009090f021810090b1b1b01090e131502070c2c06061204020112020c0c0f030a1203020c03120a09061b080103060c110d02070611010c09030f020109 67
    0x4074001244542d000303041030560200c940c081c8007410004001c0c0c901700100200d00403840d807510421800000328064001c030700c038424400c17800c1d4404a5010b41021010b14000e00140301c000c080040e00d580c415200c0024045941c030f4101c03142810910840101c000410040000c1c0300301070035020b03211041d01906d01e01342c0c0c0682003e0107aa02c656100515049002040c030001038040c04040050300059070a034017a010181030b0524242c419610700882000091040c2d060104984500c1c81d182268030042c071007030084002500041c0c0d5803004010340c4040125009110364009a45c11000c076001303180216a024050070010398031714003441c450782980500005100d1480d048000c2060040c034582000804074810f12003000301c607140000d0745080c44000030318200051f0125005200040b0300c0c0d07215107560403090405091055000820501c0d0006078014000180c2100c0310802c001c0f40c001b48a1960201644028005400592030003401d5204038840a456000c41e11808800d6900a40304031010b0001484c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 645898309 1250 645897059 645897071
    0x6021b120f0a2015070306030804090203151306050f010305070206071d0a180c0302310302040e010227030d1224081606080601080a0b10020f071202030309100909 71
    0x12141c03100b0800eaa1a0030f499132140c00225218840d20401007030740c0d0310070201821b007410010703200002d42004107007144d0079a94417200e070642d82d00c9803420107202c5548040070a58a0500003408040e400144c0d246043c03601341018812031a4001c00c201c2c0e403080d02860038036800c58108002d540c01c0c41040b42150307009010301c280882c2e08200601750581105584006221240c01000110204c3c1319000f140308001210759600450300140e40d0b2030b105e052410020211446071030f40c00103000c9074000d1002856aa500140000c010590204804401c02100c1140c452030080d03440429121003058404804025034000d030740d03014807505c3d800f00a09025030751602c2c06061000d00398110540442c0078501040c03081d034000303103030002002440109071070180e6500300898a41500640d00305d071019020b04403068a80d0000a515100c4d05440203500030168020071a81d04500358a9040030170760f0f00f001c41072070016008000942c0b4000b0496a14120a4807100c0b004581044104c9000c0300030b401400149003031003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 645899559 1250 645898309 645898367
    0xc040b030406111c061d241503090628090203030712273b0403030b180405060417120705040320010f0f0c0b0406021b120f0a 55
    0x450101c5030045520020001145c4510b030404071114800b46a4a210852000280441c7c020564402103c29120443c0c110380303071000c00080d0712001e603000380d1025010200030000390400c200019604007100e10f4000603102c0e00c4100140301c44030314449031401709840d02c005204541301042220680c03500980d9084004e441d07040001e01c0e0180c1c0d603c19402c0003c9198040c12590258048481290180030001e05201c81d0915901d182d2003808901203050984101d030780d42d44c080080700461003030703119a0340040c640c10840100849922107503180e250411005082200040340000c446030001e80008892214001d00029880c443c800c8203601181c5500484c1030201140e005005001a244141c240c0c05a001d904104984460f40701501240042d0302510300600c1940500440d4200300f140d4502404004500e40301c4074080b4500b5502202d02641c005940c01e00a141014a10340706004040a888429500b030130045442c0103101c000c40c6100c00000d04c0307200080c003035501500c1c46007035074640c480030003240 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 645900809 1250 645899559 645899587
    0x709060807230702010818030d110403050a0c0801150f0b031003080d0f05310203030f0f07060e03031006141207030b0307170a030507080d1d010b090c040b03040611 72
    0x210004c0b4040303441440411035041c0318000d0307004a03d1005000f10b0401c5101c0e030015020705514401c0c0c01404034204408404118240031795a58603025a440140040c03030030070507030f0071607000320070100c1a40301c003090621809100c4141271045503100720381d207910b84d101c3c0011543c2c0202e80c0d600050060000085c1d80f0b92040058100700410045210304006680e030f691848102c1d945c0c070000210070540d00020a494100c9221b243d0303004140060110b84c00c0442000224032180d1280e00840318ae40e1000c00d604081142074018869443c0d5040051800c41c00c01e40c0150000c034415010b06024480801180a01c06445106440399841d4441c0c2c0c80250b07041c008805002082d0a1803514041d002d11000031410100c1d0b207845c4101e5141020043c290a02151800c0b160358000560460700d000702000007120003107050169201c01002039018410300303402018030380d08443c1c81482141c052a6031404010212040f142950304464520101c07540d40d680714902200103149030041100c80010228801d00f1200c91 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 645902059 1250 645900809 645900817
    0x408010e060a0c0306150c0f0804080c0307080109050c1c0203010204030b0103020f030c100f030e010501030c08060f0c1819090609060b07171b06010603150e070906080723 75
    0x515002000750f2000403404600361403081c0209408410780da8400035120f4403030b07400360680c2c40c01200312034031302d05060f5201d00c01d41c1e200f940030b42515844802203840031b29052190750002c0500000030003a02100e5510b41c0d44072480c0044d0f003071080104403000c0c5d4804101044074000241d0041c002c665480d04c074030788030307a81c20030a01081c2c2c0a80007402041925003800107040c7e0034008000d0051030b0300c444050089800303800008203d030805407103851484085800b405024017030740c0b1a2070003c800b1170803c511a460a4401810a05401c0c6030700c043c40315003c540d80403a070754101001d541c4680d0101130710100340b164407030010395000d10115003000580031407154082c1e41035444011040c8202a511200590b407806011005407080200e8807061969a4540c0003d201c2c20360000303e250405070b0160041810500c003640110003194889110740350046406071400c0240c0040c04a0783c082d82840503004080f02c8c080d00402d41030003440404101b0241c010211000c17150f883c030340020390210080b0000b11031504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 645903309 1250 645902059 645902071
    0xc06040c0614211005040908030a050c04060e010509010c140705031915020d090c0909050727050c1c0207290a05040303110c0a050637020408010e06 65
    0x36055440c520128144400c444403940f0b04000603030340c1641040540350800c809070422060b9140f01000181c607880728092885818010004542c89203072061621040e0703680201240100d9070100014810b00c1e402c070741100c81d220020300e8290b845a2041006980019620300054400002c0c20f50f9412071b064006420401c0d10402d5040d00d0f038080500c0c40f0960101c500038001070640125104192841340300f94042c228248111402051580660b15054500a42900f0401406840700d84e03000078003008000c004010a00007500100302100c035464a0f12500045803961001d0751074002184d0800b600406807084241c542c500340620140d195880c40007540100b8003211114100350700341144603040030103503400e40c908040380856991003440c881d000b00320041046090569441004034002c1c41c17500540701140340e0000801460426052881c80d225004041c6001c4500b00e100040c135407918a040300e407914101282c6100000c064910407c042d0140307810a0b2559860710a0742c4100c01000115540550 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 645904559 1250 645903309 645903317
    0xb01081f0507021506030a0f0c1e1a09040920010306090b0913080f030a1e05190b040b030d03090309060c120c23010204082503170c06040c06 62
    0x644104259030985030100da5400250300a16008007a010902003580e07401503004054406602c569904e03038514003000306055602c00e45654003440383d038041a0f110705d42403240d19062940d207072400070360050400c138418850112050105a00c1200c0d222900460480d40e07011015030b1400343c14404100b2048000700581e4002400c19000040440315442404081c1c10090148035040c0d881c01560300401c803005604071113602d02040700181054203a000703107019040403030022800840c4103440c1040c0f120015012814a031038a420b201c1c00b4a0904485a182510f5803404036403100d0350f10000c0c0041424840558250040710315503508a039142d84051030452094513a50440360311a10203c600c013100080c01080203401810144c015030240c0c85081c4400d200c0c02e802280c408584a04a032007015069208101e41c1d00402c042c4001001400350000341e010804c4104242200c1d01001d404c01807251001070302650604075070200c0c00720502d0498800b02c031410200c2d0340d01c1c142813800301f0b215551407217410002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 645905809 1250 645904559 645904603
    0x70f06111e03040b060108040c08070e061008090c091003050712051e03030f0406020f0c0a050f0d050d0e0c06220b0a0c1209080f01020712180b0c0a0b0108 68
    0x15540001c2034038020382c0c2045821000b0750350080103686400c0058001d40350000e0200002424020401104002e06443c000740916070811130140418074410021020500c11b14108021404800217168000c2c94022149000144c0382c201481d540c042c415000907229008458000c1400088415500c1220380b149044802c1c441014440003038214900c0c0340407403240c008201048440049002168026024110062030440c1c5035040e80c14941c4148031511164004201c640d05000041c4070b0038044800d90400382403c2c642c8018001d001e40310741000410415035841409540d09420410f1380010080500025580d0000340302040310301c02440034900e000b901003003020034030441d40810703030307050310314584403010f828503a44d4991104040201c00c000400c01e1007900040e40d580c08110b42a40c80220794001030b60358285007020076542049113040c009005c4079010b500c01010001a807103045900d503512240e2550a506d000c207007032006414011b002c800b803080c00480c03400000310b24440e0a00c1034100b81700c16 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 645907059 1250 645905809 645905857
    0x150c0d0e0c1807080f070203270307091e0213050a17010b100f0c2a17030c0d080406090b0406020307020d020f060736060f02071208070f0611 62
    0xe00310080350030900049840c4c02250700c01c0c2c86010600d0300604240150b030709150b00c8608a00c96410b504001031317243c22441d240880d080c2018081c1201402035801d050142583ca0b0143c3c07112801c146c1d0381d0401c21580000c1c140300d400d145d10b0025001d8000108442c1c0702e03c0da01d410038200c0c2000c3e0384a0440c4d070352070034050740d103203240c0041100f42c0c0c24059183c1d1182c41c19030000584149800080503600405540c488161280d0740304913041d2106103002400742102c8c00e10342044048506503e524901d81d2041054039140c0d0000501c60b12501a5403034104402e50340d40c5802e8000d13028010000308107054150600c01007107100e8000d03521a8845a00305c17500e4110415080b030b50340b010010400c04a4004002003281c05108071090340c1c282049400080d17205600c000345d04001d04045104008c000c0102800780700041e800540b004020301a4402030604606110203491103440b101e40043c14000006880d004015205112890003504184c0401a0f2401032000c1039279036002c2014002c500100e9000000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 645908309 1250 645907059 645907099
    0x61a04050307030201030207050313060f02010f0612060509100c02030a12140612011805100e0f120a0c02060a0801030c0b2a01090c091b090602150c0d0e0c 68
    0x811540300400501015255400540080d44107500c140c030383c2c0c08100043c0c0301d407040104c0e011000301411b50300c0b0030203401700c2040282158072096a18181a060200400c500d541820f485112950094000502922a0117400303150030041100f0244080c100300d1141c090680120103010f03c4401a00c9400b800c01840c0c4011f0201d034030302c95401e080c0e004100f003c20a07504041d003ca000b040d940400028121840140128030218400740880322039110000c8044001d426004020581d0888801080524880782e45507441d0403000704402e00001021503814401c0740314600c0d032a603143e0090201035850445450040100c1400d001c103448260b08840001255807042c42202d80303d104842c0480c116131280241d4480e55105e00030000b22075904e89614402140207516440010000700d1800524445d480d2204090440e111640b0024003140150402032242c02181150180d017208a8202c2e0654034882c800b402e5014001c0742c021594079005140302c0810000070710842c0544100d6160300401c84400b84a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 645909559 1250 645908309 645908317
    0x71205130905070f0e01031112061804020108070809070312050c060f06030304030308100f0b0d06090b06030402091026070b0705070e190c0801051002011a1003090c09061a 75
    0x100213400345041c640d80c180f20358180310055005150206081204540c00c24182c2c00084001103808000c038240801c5182200c1450031000201c00c00180515154002800c82e000007401c100070302806200003501114188840409503030710203000c001124908034001d2064001c10840080c600c1010041401e44c4014216240700c1d220040082d4071b0141581e4049940d840302a00c1003044000c3d952000c64801e1070181250301074281040c0003030703d8400c2c203c110001e95100354041c07441c007850000440e100e501e96008480c1d01580503501e4120300e4450b5184411010700a510920800c14072040201d000c901000300036004d0300807034084408050304d411420303400341f0800100401e41ea002c3c400421010800b00c001560180480404c1815a003c1d401e0103001c3c0d400e02180800003480d40740050002e850000444d0300c4c0030446200030040429150004500c40036040701c1d030351050403181d01070301d6518840d4101d030749a6548015070302869a9240020300207007801d4004c500c2d0f40b031070100f4000340c00c0c00484199 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 645910809 1250 645909559 645909571
    0x507170c040603020706020c010501080114150f040905190b1e160f020a0c060801050114070c1a07051903021903020d0503150402070b01030201080105030f070302060906071205130905 80
    0x500d1409142002c103a0080d4048201184d40c00c0e028000003005403003c0c0f152a0007003203628000300e28a030000c5440156070388010425a00a011100d0700c01c41520b91605c01040013205031307000a01400c1604080d07180c00a0400c0c4085031810f00c1c40c04030104035074540014019000740c03c00202c109240061094110001c946200e48805408181c0d1085131103042920318282090040d640d0b041c1d040d468070f040102090300b05001048100004211559120564004850364002c0d1141000916542c200301c00c0703881d20480407080300b582e030302d82070311180242100d1146034818105d13850029100c40104465050039070a4026009204100e0503010300e400d803a40401b035069010706441c080c0c110090301c183d003001c0c0c1821034010303112082e82000e84407440104903043c01003803408010342c55440010f1503c04141c220b43d0290b0003a410361541c3c40c10015a00c0166541211080d440c0d2811001159960090350303400740041d282e005103648515040001412010138a000001c202511042c2c0e01c015901c044da51 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 645912059 1250 645910809 645910831
    0x40b01030603080f0a0e18040308060a05030d030e01060f081e010507080103061104051201050a0501140a0506071a180c011e0503061206070f1b0305090d050a05060a050717 75
    0x521014984d050011321011a46090004c2c10101d50000300d41c3e100c1400708541c813202148000d1001349908507800c40c1e4014011100f41920b241401c01080d02e40112050036014941c482c664a400304e0020340001000e40400023030740700416950308082d5903407444020f48804000d440c03400191460418000c041c8a0b070641c1d103404d170980c0d2940d030301e6400034009401488448442404049800c1d0b46148200c0500d004400c00403600b8240300c0000c9086840c1a030104144000c0818004030946030100d1a00440744215001a1a4501030038103107102640081001824000c40c410072107400040d5079400d2542c000c1c142160142e40e1104015120780580021840518a01010540400c1c1c46400155440200500b04060540001c00507520301501640c0e501c1c00b0504400d14404200d60103030601154052070079110005a41c2038801a01510030410302c18000c6061101e81c0d0107201081003021682c5d41d100b4200c1c2c69a180c0002104010030050b00c2d1400021542111031202c0f484001c00203001d4803c020b4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 645913309 1250 645912059 645912067
    0xd141006030f0b12010f150b1b1906140f04032a020d060219170f070e030a060501061710120224030a06050f090c1b1b04060806090d140904090f02040b0103060308 71
    0x64005940411140310556210f140c18540902400c000c1c0d02c800e481c400c80e8081410004cc5540b1030104100408000500c900c1d24104004aa484111400890390721140358401c00b0541c0714a070760740c208203140a900544450348400400c48140d000344200b101c83c444a461413510002c003240d1820000f00c5c01c2e0708000d6000c0c00306144030342c10212660070124038180ba0295030024000303c1e04044214400741c680c00d0307644004020740341e0442007e20300b4091b0380391054100d2030000490000d41c8504c2c02250080d040002d0f0302011515803140720350240d02404a45c10143c40a02040038050344106ea20001081c02c1a400141c02d00384160341c0c010036100240184140c0d9151100450290052030320540300d1405140115528001440400501083d43c420381e032104034110207200903240140c0c849010f03a0311080400010381c401003041c0c01507425900d0028035108140c22042e0660056000c01540b1600e07004000c410031510035084180148251028800c19036014015000c86500744400340c0403002c100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 645914559 1250 645913309 645913327
    0xc030b0903031003020f01050d05040c0302012a0f1a040503090a12020d02040507030f020a11190b040f03030f020c0c01020c1c03081f030302030d141006030f0b12010f150b 75
    0x107680046c4100b4107242250829a803c08484144c64040c1c909481c5441e482005000b9568070a141c59100c101c4001060304108040241c00401c0b1103001018001021500008c0c0c20412041c81c56038504010b000541d030b0724240b0b428403946952109a0191140c0171140e8001303800492014000740d000c0d0020820315584101da024840130740001082e0301c0402d80d071840c2140c85180d0920180800840c81e5648030720b40c1d031496410920b845030040e19000b200a0700700c3c0d080c000503042c244580d071180d8400f12000300c034000c03841c05a002d02541f203101d0104c00d0011403003621130030000071002ca00010907405c4810f1000d446090240c0031886e00700380112010050b1111010900404a45402000c11401110391000c4014204c84c1d181c00c80c0c0040b00180c0001030340b500110054003c881c40e44020310f0403040701d800c2c103110814001d801c40c0f0500003411f849446943c55a00c0c1c3d5401a4403044d400350801e20600e8188861500a08003428490f8585180c41e25404100d8182a40c00302540c500a402030b10304480c803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 645915809 1250 645914559 645914569
    0xf0106030e070504020c0304080606060306030d1b06050f061009080c21062a04060801050103110d0e06100b040e0403111015030c08030a0c0326040c030b090303100302 73
    0x8114400c6040c4034442c400a1503032520320082c0601110f03600a9607ca034200503506040100c090301300e40c403a1600f8028400c0f50f590210304040b2058460401b0401060300380c211180716149200d000e0000ca20b40010441c55036440026184900021141c0c03026a60300c80000349e4174400d990284502d95441010003500d5800e14800e80d59a50000c2505050f0a0014440592070000102c4044800c190300080c010744600071ba1810355411180502c0f05420141003200c01084c00c02d052145904242c0c40340740d480400e8442104a52001241d08020711240049a204550b55101920044480d003001500040d0381c400ca070040e01e094a0300700c4070030740040c0c031180c80495900304003003800c614074080e009080b6041d80d511f10420300441180c8106004480c5581081807503545140d114592940080100b4098140d01590186060380d050a00140040202c51483c01152000e036054400308018800d10040c0080c1040d01d1045038403509400400b9502d07020426100d00041d1180328079921007910500040c645 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 645917059 1250 645915809 645915821
    0xc1e03070804060509150109020406180602030f09040905060f040201020c0103090f0f0305220320010503180718020904180c0e09120307050a0f082217070305030a140f010603 76
    0x40c1c14103c0c0c1d100d004a60b006403000100303038021611035074002b404010141c0c101c0c6881503001940c00940000320310349807029442e440344800c485410940010030300c4c003513076880e44564031868000741240c00c2403401c400d48098040003500d069001d841400440000e0b9882806404516035100c0900716241025603100c200c0c1c0440b80d0011401e000c0d0a0000c00c45001b94000f982d00010300c0382c504580e05500d541000340002008407803552001800340c41280c1c0c1030f60090b040740c2d009141c901804022071758680000e410041150008040c804812a03202961183c0750050f08600604035010444c107802c04516034420f02c040340e002048622040302c20003900000c2108290f102079104151100c03001c0001d40e442c520740c01120400c2c003003040403d00b00c525a51009801c401e40d40142040ca445043c00c031940700d03140020602075900080703181254410005080b01d8000c0b100c55020000c0c1c1c41c1d031898540070340b40f500212540c50030b091400302441c41d00310560240c6401811004403100007a402c110049000c1e2003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 645918309 1250 645917059 645917071
    0x60c0201090c050a1505070512120f090610060f02010b0402030a020706050f1302090712150801141012080906030c030414010216060c3c051908040302070e0c1e030708040605 76
    0x151349c0320b000b1010840c40051400b1500c1c01c40c210a00c0c580324440c0381e8060b002511401f020380c8400d0402c104c03071130103495032401c1d03850a06103540031103c02c6000300d01501c4000781c1d49402c41d0000c418081c4401c8d041d009130101622a8100b44a1a0b0b6100d009000020301200c1ea51a00a040d00c80040036003081290190004141c0c902030394081c50000c0400f0a80b01c0918001e100c4412013401041240000c1c13050f8120400d0f0f43c51070b0001800c00c10300c0100303903013441d001d1089002c291000d02d0080003c03640445903061000341c280e584914007150341080c550001c07181a01e42a9103003005041d402018400c440c0c0542c0a511841c2d0140099203580000b825500740713420a00002226007076564080401500c3c050701404c1c01110309010305040301729000310220a2800340401402101540c500c24038840104030211324004030a99600d080403480d003101903100046401d458014008008040001031008100b59003040b440c8410612803801c680c0300c00c850441c0007038809401b040000703200d90846a0408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 645919559 1250 645918309 645918313
    0x34080321040213020c0604150b0a0510032c070b04030510020f090d0605100812040312090b0307090602070e041a18010c1806020a020d0308060d060c0201090c050a15050705 75
    0x24803d0201d0000c90f8001200a03001d40c0c044410002001031000704c401c003071410a0b00031300070007070004086894480c070744c00b655215045c9440070040051099216a1840c01208034003019800740007900711090403003140792000ca0040500105243d880c0908072400ca96221005122510100d00700c03c00039040b00080850b2110204146406692661440c00c03049010b62000030701800c280c580f1829010050344641d4844d00020050f10f9110424016502100d800c407404014280c2c420002321184030564006207482d0070040306004038a84d024500c41c0039503440d82c00303c0e041181c844101807840c0d0300403100103220700035000030f25100100c03240d580354200c040ca1420400480b502d42e002c6080d035010341d20310400034140c040348095028010045a0041205001501d0b00542ea90046190181000d0024051141c0c100210300581c550190211440d0b802003420441c81c0008040240a0805084180c42480c03200002041c0e6282800d06002200c83c0742c100700546840c07081007900c050f0040c800c180c600e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 645920809 1250 645919559 645919579
    0xb1314011202011e0f0e040b0105090d0501062601111810030e0d050c060a0516050703111501081b03030d090c050406090b011409030309010c05340803210402 69
    0x543c03003002d4403074904d51951070b41d4048022140b0002c00b12411960710521413805c00d00145070998100d0110703600f164050703480d10040700c1c0a0810501616007544034000c205270700d80e9011082c00009042c0c451400d42c04000b4407003600070401d841054092001310010b14081c5111140f05172828545600c940b031180d04010589100500c03929041100b1608105d02003180003a01200d0303e00c050080c0d0340d100d94030901c2003219007441484e4240c007201c005009030078080001444070615000358490840a0030800844940701b04101905440007801e11402a0b1403140d1101141c1641e042403101610220240c001c50400618182030000f802d070000054848184d8100c01007200d481d1070003910080c0c20a000c02040300482200010000414858200c143d42420f100e40640c41d81e001c41111440701003403802000c20000d81c1001800c04488102c85207000603001c02d0702186d0a40150150100365a900142901b030b17648204140c0c070380c842d01640c03409071040000c4a04d540b120301c0120640240c006040c910b03031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 645922059 1250 645920809 645920837
    0x506131a091c021203181504061d0a24060b04171501141318060608010c0507020310051b0a020106080c06070b04030e031903030b131401120201 63
    0x30011003952180c025411400d12070300b00702c800c031994a02d00e905070f10003401240c0e5088071480c0e0f1400007406402c0900d50034440b200c010001042044403008400d4110300701420280340145c001c2001a002c80b0f600800500851014080803d200d451607800a010074062030040d0340646980a81c81402c1d072a580d512075010801d01411401340001d0309044c08041e01e10002c643c1030a180c003052a90070400003818000501c80380382c09100c100c1c40035800360340108000c8903000400300600302c2c86000c014410100400700701400440c0c1c01c000221f600748402001a0041d218045665125008001c0d4160380440081040004540e02c000e900c42c00c2c0300ca003d081110f16080c08102c5030b000320040c0f030041c0c0d1180420301010380b0038402030010040c1260114a0160700361f4400c0c015010043c00982448111f041c0a802034500b03200042d0301080d004100101c0011506d4054010048142c03000d010303084030152021a05664480d01d010004d0b07101811803941e18045100740a0110003004138108282c00c4c0000e03070703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 645923309 1250 645922059 645922103
    0x20303151219050106080d0207120309031e06110316050c010612050304060f0f0e06030a090605090d03050a050c070f0809030633132309030c06070c050613 68
    0x40314070382c003203520356140745061007400d454050300300301540d8001500f050002500083c902e812a04191111104450a403c05545404641c0d0001c0d00c80c00c2c0303000301c440c0320140d00e2040c0941e8905c1503608003c070700030140c00c0c01c480f40000c4402c940034200002d081d031144c500920107801440404000801c1d80785d00c0c1c0c105281d980d180c800c0200d401e5440410203015194010741600c880304003d180c82c555245c035080000704107071211100180140c5000020031000c41e07035904218100c1e81c00180501441c01c1c1140704a64802c10907103900c0020345803070007107000704106015a81c050520740c2206814590b4a071583e0100800c8c40340300301c0c0c20505c1001002c5554034107004103440303402c1648a440c8070b8141c5028503040d100c0c04051440e5000310b01504142c885c0c0d41d01149000942c40c4820000e0303a018403614190070800014029042842d0210070446c240c031000004004144102e0190b50440d10703014001c1d10308404015000b496a080f00740024002c01800302c0d10031080e801200f24010b05481c00000700b07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 645924559 1250 645923309 645923323
    0xf0417060601020d0318120513060908010b0a030b1f03120306150c020907050f0c07081b09090a020f0f13270506060d030507080c010b01080a05070203031512 69
    0x2598019008011003503070180000c80030302c803040c00c050001800e031000c240d410121040006042c00d00410018803d184240141c400303c5000140b080845501c40c0b0f0b0207030a1040c00d224001c40ea60a01420f500241454140a02100d80c13086c10384219407a421130940003464548251440b40e060f040001001c1443e60b01e41410380a1300380c500084031800c050381c18404500d44518507041c041008045001038560f00346080e408445854010b48443d822100c01c00305104820810b04503225112021604c0c89000c00c400000c4a408560090100e901030f05018518004413035144140d001403041c0005070a11110181c00c10400400f410240e544250004000c0700d02e03401c0e0202070075541c80b80a440481c0d198070f012401c2d12440380008115680c0d83c3d400d9900c0600502d4603001d100c80514a1080500502c1611440e40d07210382c80c00c1e2140e8054482034024020b80d41000c1c0001c0e200c10110300411124443c0310700690a0390302461450780c8020162055010300e20351300350041d40e410340000070400f091041c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 645925809 1250 645924559 645924599
    0x715020301030b0109090803060d050c13020c06070908030a0807050708360303070f0212060705120c0f0702061c05010b0904230103260a0302031e0601140f04 69
    0x603165415820700000124050b004145141c1ca4034140401240b00d480075a507200340100e40004881045203459420403d900c13800a41000305040c05080790040c9030080c0440c01411411030b0642d5858902c00c89040380c85115a160a8104000c03107510310b4407900355a50b0004807424910719045142e0b0300d50001d9070000040c04910517500c64010500d0000410800c07411440e1482c10b002144030b80000790726445a10f00080401003e44035080442d1140b59415440703280e05010b0700c9940c0380120002d000da07440f645c000043c1851820000392540761100039a071301c04809103505810f1151550a01c01960700503944081103e040030031044c3c7d9081c85001e824007074504450f03000e072240d255000b40b1083c0e840c0300c0b910001114040e1104d2020014618a490440c2c1c0c224091002c4d00501c02030450f03560040030382c45000b05000081102c00316030036070015400b442001c00403810f0428000200d010000c5c040e240b250000384480030310b0b1080d1120001a101520441e50424a0103650b484e01180c0c1d20700204903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 645927059 1250 645925809 645925811
    0x120103140609060411100309050102070602030f391b0304080d0e030d031e0624020615130b06040305070311061306030c27080f070503061504020715 65
    0x1445400000703100c0c0c160403482c00c1c40284841d08166071140b402d6613503040c055000f50b80c01d2503840071841c400c0c2c00141040760440000c655640c014102203021b503204031040b20b2450070200206841e4104101003c8584806211030001c108400c003803607900a480d040d940c440c8020601103400e60052800700c0480e07014119004581d02d81ca45180c0740e05200e401452401401039900c0e08662545020903405c161a046280000c2c0540a001100b07140b0011082d46c2942c040c83d100e000700304611041c000d024007803540845201c1401c9060000c0782d841c0c1e02114012560807002c6011a0141005488426035564929020444001890100304640c020b90300981d2a40c3c000001041440108100c02042c0c05080d510340e45400222802440c1c031090034460f20741010303607401610258922900120440d00c0042540383c142c0d60804000e00d5030716503103000b140d0183c011050f002200460010f140c1c1704485010317010b091981c0d0b40184640e00700070240c8000e500a50200800340001e410200045a85040b8070740c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 645928309 1250 645927059 645927083
    0xc0807140d0908070906140f011b08070c0b0703021b010e040903080a1506020703030c020f060c060601031d070303050d02040e0c0712030b060304060b0a08030c01020726120408120103 80
    0xc01516026190b880105442e24010007488080400490420507c0b02a00c003001080403010048400f04d00748101000c80a440c0e60140302004202002003d00c18000c010040115840706045880c510035908014056030002060210001d00d4070782d400320425050410080d0303543c0f508041003d965001390304800240181081101c030301800d10800f01d05c101011400c281d0f42c1d00b44040039547e156a40409020300180420a40465840d10725084070f0f204017404da203441d841400c03400c646c2c2e6a025030b01710f400700f07003044800c50844111903408904041041e00815010b4a1a1803d4034154845198802171030303000c00c0003285481c1900500c50080300101d5103103544080ba820a003146085051381c501c03c040c2000719031811070340e400041d6900150400000100000c01000013240c6a10030381c80818280008241005949410f501804806000302e500c0c03010b02d01c15a0107100c800c03001d500802213201050068600414000d0907ca51046c0305201c000e2a00c082400c0e11819150309900031610001400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 645929559 1250 645928309 645928319
    0x42706031b0e0c0301290d02070f060b01170604180b131b0602030301060e0409050f06150402090a03030302070f060929190c090e0c03040b090a030c0807140d09 70
    0x403846074001c0745804003605550600c4e1014105448803491807a080014509142071903d20204a80c20700403c88411549c88009107410085031344104000d444c000d03c4d107480c403401035019501c0c2c0c5580c103807141080c02041d83c03482c1c1040020b180700041d0401c1080000a1100010342c1c68a0715800f0f01a140214107452016103400140300704c10107001100010084010003805030004103503410360700b03203007800e9200c0c000e43c9000c50f00400b01e280340a04240f0610054031071003640898110302424402e02d80785108404401031105034810030001030f400041010041000c01c1c46907020b810400d21990351180321908a413138000580d02c07003417019507984030300c413042ca0380030f924002c4410094151100c1d8070550f0716001004d0a03001c0c0d0030b009488241620760040c4100644640034080203040c00301142140ca0074824484402c0382c00484044505c0301e01400400c00811002942c804069072503502d0184401c0035640341d1085030842c0000300c0d0443c800b070144d1006040b0034400040c01411556600f0302c024508 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 645930809 1250 645929559 645929579
    0x3010b1305010c0804090b060708030a20040b0909040618050c040b0414130309170714030102090a1a0d06080c09070815010809070506041805010b042706031b 69
    0x39511080c103004441e002c61000a0406041e03408989a80701d00203031580651b008610b486c45038050060482c0000410056054119881107900920714400e0301031524036004001d03001d1066020300391200005200700d40f550302d0805802940a84107500200d10300144500a4801c212341d168229240d4106c8045001207040c5403182411101381120700b480365282c20720303881329003007800780011b0980001c040d42d4005141c040c0e40a1401019200440f007401480c44500c0f40e298162070007400c40c03525101c216070441d13103014000c0d51a46c500052142d40d0092800300b504a805044044808140a040c0440404802607203c1c1c1d2006042450240c8045000003082060000006145030280980401403141c1d18500d0300d50000c1c0a4000e0132b1582c02620b440040918280b86580000c1e8892400203000c10500b541104003503008054140c18809030b41c94210440072405680540440e09034581c0b402c55621440d030000f01450491181c0c00200280c50b5107803100c6c10048141d1840407181c0300c1100700001400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 645932059 1250 645930809 645930847
    0x303020d090e010605031b0301060903020306010e07050913060f0609090b090c0a0c02061306051c020901020607050d0207020405180c2202031806070c0c050f0a030308190203010b 78
    0xe203140401019082c40c400c4007202c64103002c0c00c0e04024021000850400340041a250880d0001d90120303165a034520004105000c5400102d01a00840000040741403c0343c5000e0300400450b11030358146958403050000511254908080c400d840304000504411088204006030407641c1d2403004460400007070100355802c2020842c0100a05d50070000c1c2e000309001541c020612504d854141c0c2021800080c0d614000c038004034444201c0060000348280c0c1180c000d106114a131350340d00d003403045010900803c03806082901030250704080002100c09110ba40100491075102c4401800c1040c16000b02d03044a000f1034030004c100c401c40c0d151242c4e144040018901c00790080b40c800c4225680310b0062000c00100c4100e0403403c40d0003102080c0c1c50340040c1c15011411410404403121440d008000400411000000b640d0003420540c000c101414114905031082d0b074043d002003860742c82d5660071120b070040101140d0013a00d81ca894401101c0d114001503000705110240d194884100290251741124 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 645933309 1250 645932059 645932083
    0xc14010b101106060103021e03090d0e0a03050604030c2306070207050303090a05061b100f050a0b3d020c03071409160302160602131e170705040204030309030302 71
    0x1285030821100c0d0b4001403040e0702441c00c3c6030261b00c4600c90106414604990540900da001c8048108a030110002074020040003a0359100c110480c00f10301804141d88071030102901e190040350008001c640101c0925800d18420b4000f015400c42024440fa60920380607086200380e0082c0007402010340d410000b510151204802440c0342c5a652030028150840610074680074920204500c0f115411a00d61503010415440550b80c4a4401c10405d00003130070121000380b020791402c0c1c0030440c000c1c8513104460311560044c04580358032011202c0150030302c644819079030b0071411248940404060140002d224840c19400428038080c011040500b05222608900c01c0710b074401003011100d07136440f07440940000c591032280c1c40c10800c0040c110040e12a125903803034108528005081000040d80c0289141e45081090103005600d0720307003000303081d0384003080051810582402440094000c4224007540301c0d600d022219000d50350004202030b41c0007a40b0680c00302d54051400c20a050f018000810031b09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 645934559 1250 645933309 645933317
    0x25050a0209010603052a1306020a0c0e0411211b040f023c030f18070513150f080601031523150a08070f090203190506010c14010b10 58
    0x100d40175565200d008010710300000c018030a038006d03945d2603444000b20b070801c9404007503450807a501e800d40a503442214550844242010010001e810b110f50792a1078052517100440b41c4801c543c0340100052607038110485040418103040e018081d0408100404031f4110300038200d050409107500b000200c0f20382e4903c07280290b00401461044290700304008000f2483c03881d118030203075000104480200b09807622402207540010500400c40c3c42141d01d140b080181040c40305400c0002c07002e06403100440d102d82500032500c0c9042c00026800c1e50066009100401c1c500c2d818160b962148203604500c070b500c0101a604280014410f10200006110045529680c1408038108854007084520702908003050846104d801092004200d040340fa21280c80060140820540351004580c80e00214803402c040c034201600f0024840f920390081e28421607442c05035074890f100d9190745101410005010904000e40b85040d4400141031600e0906c20154400002400c401e128040c0030b850170803000640144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 645935809 1250 645934559 645934561
    0x10219050a1b0e070e0f100801032307030605040317040b0606030a180606050a080d1403040203030405090403030b010e01050702060726040806060a0f05100525050a020901060305 78
    0x12410001e0300d4145980e000c020544410b0282c0610015400d50b6008014100d00e11001d00c0a00c590202518640180464449910310080c108000340b82a40082c2c042c08110484010030100d090b80000700740c500f40c80d400f60306004526601c920306100058000703e42059565051000389503100c03084100d036000c00302c8041c0060a00703882c2c084544400420103445070f8000000689518640e07008902c0310701c91421f148441503030310319000c0060140c90103414040e01c01c100d0b002400c100d0010301c561700c1d40e0181e1110212040c041c1c0c0c401c1e20301d41c4001c0040c1e80606c0304000001d440e0f1a4140140d2186000c1d03540059100341c2d1100040c88c4c801d040561b235040000034031955015235070b49002c0703442a65014800302c944602080080c049621002480c807107144000c580058107440106500e03200d000100c0d801c4103202c3d00c8000d11686919640145074212560785500c28030180a0401000c000341c00500041c04203160003d10010611070300d0041300d05401c6020702004509004030000d0140403181800d010b030f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 645937059 1250 645935809 645935813
    0x409081e0c15090304030b0408030a110a0e0103091403030f010f1202010f180e072601080a080a03090206070c0612140a15080a12110102091e1c11010219 67
    0x40d5010004207900c040b00c5103004642600001c00848000b5039103c6038201492410b41040900c540048600c2c681c258201694190081540e40c100c0d010703e222604d550030084c0071a0300440c02410b1001080351805207041d00c00d5585081003019500c01c8000748140e054035070402c8440b0b040561075501c0495030b4070000c6443c03030040c0c1e040401c5020f600d1a40c81c00c02400c0888444540c02445554440e9003d20040c0f03081c0800c03d075120351004e01000c4130449000c4542c0e03030000c100d00281d40c244142000da8200c03000d00000a0603042c01400d84901500e8081030008041e00002da05503c1410110741500d01c4010401503c1d410007060780b155000040d0030042852018185149664000e05a103001030b51406039040c10749050070b0030302c094044442180d049044514098810307004140c0c00300080341ba00e0350440c0d0219014006c48040c0340c1d001c4c1800c0b00b4034405141e4100a00e02441c061540841443c001d1545402c110461180b420b0042107404500010440064148420300d1f40080000002e40ca100c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 645938309 1250 645937059 645937063
    0x618060e0108091609020a200303040f0302070801020d0b09070c110f0102070e10050301050f0702070e1302030a110f040b06090906010e0d0b04030f030e060a0f0b0409081e0c 76
    0x40d8028007820301c1d84280e50351958103428400850305110792a49803000100e4a007186901619901c00303a600c801403651050a036001207071015600c8503071a54400c00024002940210411f21385511900480381e00548613400c3c1d50a90b0050a800720764150307901907903603840c5403c044e040d800c10070360308040d481c2e00e00303507151607030305180e1801c07500e015004101317069109920130000600140244000c07800301d42042c900c2051404001e2154a02c20341c2000080340007082203424003402844039030014080c8510b04414802c50300c5c0005c01609050401e0041500135850a201c07a40c41caa100d18020b0304a034606008001000380c400c40320074056840e0514841c241c0d284d5104407208014101e074044c035699a1000100e8600e022030b4402500301c148180340f0f40c104070021100d240603500c651500c1e5510160f0f1141101191084103414009071b100101040b9400403d41c40039041d41e8511501281b0500c1800100c1c4c1600d030035510448051a0000c0ca43e40081294000440000c175030680c00d91800d08858141031b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 645939559 1250 645938309 645938327
    0xf061911122a041202030d02030421030306050607050609061609090519090f050f0111040501230c0309011e090b031005030106030317060d0203190228061806 69
    0x2080995510b01d4181c008198494840c03410994096a0359680b241481000c0345008007040b4024410b1508000d0100d0000c81903a080d2000003100c04084010381a140101214801c825014036580300e801003a181c407920b000381140d07070241000345960b0800740c1000d49001001800d0014641e0b081c0e100700d43c1a6800000007007150030309540441c4948030b43e00540840301390311803000c0700645024070860810000c2c000f242102406001598107203c5082c80030703801c0e90020b141c03c0022150800042c09650302454a80003400012176540c140707002034040441a90f40803040c03500c100d84c008130b85400c0325a40810541c0703500304921500d84101d01c907640007501400e0030340035040480802000241040480080000062800034000e01400d41d1303e06003e41401d880081001d5400a41400210b280c10301e440810200c40e0b01070000c11b2003282076601441036221076002243e1268810907008000c09815103482c81c1e180c800c0e240b982c03010f4a07000c009005442940154026a45410820018150040414 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 645940809 1250 645939559 645939571
    0xa050609010309230d08011203170a090516150509131805120a0e01031811010c061401080f0604052d011503030e0f130209030f06191112 60
    0x4107094040e850955410301294611101300c16000101c01c51020000800810100311511180303820790701e4820041d0303100e500d000702a02040000c44040d2150791031151169000113100344c000b0700210159191402e1032040850510303055441341c01441040c44c071040e00015503409007849450142c0440204030211030496080c04c2081d9648030b0829503145441420540742c1e40b002c20b0701e211491241c0299010b8104d5040c43e000146040c00041c0154001d106035800700480c4080f480c1484050b030380d000415070280c50b03020304101100000c0740025505024050840b1031a6141a12039030510002c14a808406810b0b400345c0d5022070140400b01c1d03408103000c0001000d4460f48401d0001c5200c0f8941e2038844104c2c0c000d03582d0310b05807000441681d02c2d940c0a042c0c0b0310030b9071110b108c0524042046488423890340300301d511141e0b00305d40404020465000703225840025066446041200f030300542412812600b6038908006e0301c9e580c103502d00c018031504204141c00c00c492400c00d01e00b0082a0020b81004246d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 645942059 1250 645940809 645940811
    0x6100e0c07051e011a0a06210f0906091e08070b13081209070504020a0921080c0f0d0201060609151e0c03110a030c0f0c09050f150a0506090103 63
    0x1010a00a0038040780d2010342c4208880a403000000f1280790090010410815101200d0320078204285003100c001421240f4a0f610700d05a00e20151a03103615003554494040d4065450011569072910fa0082119150060800040c1c1951a0400d801420001d1040c0d015401028840000080680040c0d0760302d1500000c85007981d64800050101c95445580050b100300c0020074049000e40101140034440e6218409460300d0300c0e030700c409000030307801a43c09100121f2001c5a00740300218284403504a0040b0301c460318450103000f9264040198005c0305000300f2504101540c509441c001c02c810203885000340300030440240f60032001808184640900803019400030035400071980705800d07440702c640c4242e100d481d10742a80740c005420103002a0007140400c0c0303c680301542d401c40110708004100d0b05a1541030040805644050341c2540f40c001c116028400c00c0c001007001807140c80b416100e001c071048001d4841c24940c00c100e0b41514a1001c0070b1280ca902502403100340c0360300080d070360005e20a0134 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 645943309 1250 645942059 645942067
    0x1180b0403050405090a0f180302070b09010507120f090e0c070204020c100c0306051908060c071e0507050103060e25030b12030405280308180904060e06100e0c 70
    0x1a0840b441c0c420390303100c180e001c1c04040900500809607480040c01d2004c842d4104101c40114490b0075036030029502c090003503000140c0c01c000e80501c680c01802011014940b41d1700d0807145a50b80a042ca5981c40c114000461488901507815000405034024080501800300e141c6000054880c0611030800000d01603034020030129072904081150462004181c071050044018010004005150701d1040500c144191000c04a03c0300c1c40050344020758025401802041d590704100f4812540b141004540c800d482b002103000d010102c42d6441d000c644100d020f000b01070b00d0200018191000c1703800114908204000380042440415881101410080446480103c200200307400811842c40040c0c4c000c0580100c007408214040000e1040d1030303045903000010183e2001c0181100d048110440c0c1660340307070b00184040b400250103086641122001900f4503d01c89020919603141a00c046a940d505c406184031040d4040c0704903688800e500480c8929170f86000114049400081c0003e4034440d4002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 645944559 1250 645943309 645943313
    0xd050705060d091a09011b09150905150a081e13020103060f030b0f0a1b0509060f0a020a062004260109050d030608011b08360f01180b04 60
    0x38000e50740ea203802200c1064038110460407103e0540007100c01c0a502d51a040c0c501f10140d14007a00d0a400e504603550f030302c140754103004400c400c00d102001c041003407200c0307428001425035510451000d6000541e040710780f281001100900383c6080504a0008414404101c20f040088000761590001055064034040046400140c005202c245c00ca02d024044d915070110a00811a0031540540c0c0005000c03a02d903034410208608848071204003c801416000840c22418420b0303000e0303c001c9100400c0300b45014024000b14109070f005024841c0540c0000c6030795014055a8810360390611000c500e8180802c0542c000180e05208a0181c1d0034240c010300100c10380785090750b0301c2da070728400508000c003d69082c0d81482980c8a4854038803a00282c24200003054070103041c0900b12841614440c0a001540d81010503135000340300078507803141c0444050300040c00f04201400808800f61501000310304001134070742c25003410b1140f013040e2090780c140a80d25140e80402100002c5164200290300e240762914 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 645945809 1250 645944559 645944561
    0x50a06140a090f06020a05060a021207080c090604060c051009080a120e030408012c150903160b10061b1707080708040914070806100905130903020106050d050705060d 73
    0x5074004503180c041c600f01c0481c0854000540c0000b15010f0000c458a42d035880c9000310503031052005907a0482c24101c0484c101c0303406800c1d8582c00c10030a503203c030f09104120010a045070807562044c00041c0074010dc020500c0000c0c00708494000030010b0034411721019031181d4480348507a0001c8010020a01c0e0b86120800443d0b00882d284107960b020342341d5459550304c4160107060b0903c010920b540c42c0204c0502010382c0c803056654410680d402400198460079601c2d05c42410091004000f80400c22a607003d0700a40d01c4880106440b5854025003401e10b486603508501007a08032109102c0c000d1b4100b00001030004040c0941940034806950198413900c55410034040c103040200b50b69404202c01040000340f50142060b283e810038100444541509801280582541d000e80415801c4c0003040403410321420411407900035081030b842059071100890010f003208640b05103495916004902015420300032a001000101d42c0c60358825841d03103845850701c8447c0318641c030403103001134064200c44003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 645947059 1250 645945809 645945827
    0x3b060d02040914070807060c0f020103020903100c081302030c12150106030c1b021c06020f072009040b070c051f0209010201241a1e0c07050a06140a 65
    0x8040c0c0140b014000e0791400641e040c80e01c1065a8181c041c080000c540c07010001600c00807940b4541e40c10313907180e0064890442180400000307904268007009032100d45e407400c024200411500f1400020100355080b4000e0003168080c1c130324103070301511000c010056507000406040c850402c5031002d000d0f032804c1c400c451400a2040c0001000114180005170b0190144e2001e4201083c07525103007080203241101240e0906402e00c020340c01107140c260903071200d5015030064101c5100b10801880c00d640d4800c904490740003560b084850400904000340d82082e4280b241c44490400e8503042d000d41043d5580e412341c00b41c028012030801c80e2900c0220705004040040d9108890001d5100c089900e42446c1280a544410a96800742d8280621520940115909220303441c11601298956908110b04da502c40b1501d08036018016009003c0b20307000500c5040c0c0068030100041c50283e5962801e6405070801345580e1001e88155840b2904000c100e40201510710407000c100112540c0d032086201c00c0da01c01c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 645948309 1250 645947059 645947063
    0x31e030907050945010c14071403030c071b0602120a02070e0f0603150c031308040503071409010605090f0f1210050117010b0f240c01063b060d 63
    0x843c0e00500c41c2c1150f4400a11041801003600044c1204462102420f81e08901c40300d42c0021004111305140d07080040140c461144135107140300e1800b407504070541c5142c10649100b80c0000001031180c08005001c0c0205044450018082c104030386400c50194507402d03c2c502c04980441c001447c1c01c0141d209200b024050030801e0020162401c00b00703036201c1007170000c44d0024040e1040b1012600e440e9101461148221032202d8040e1a5546216000c060b400342c020085684150501010031156018409007019017400500d03202010701d00320811a0400069209506201c0e0422483e6440c3c0c5891010104a100c00c1d107c05e110100c4010100309800441152006940200303590b000e04e10f505038001c58100c031100380030701c05000d104c030301c810f8200c62644045643c0f258135003021621a00b8035180400300d071192499111072003944800004a19481864003100c00e07503440c10306102c1e91441c01e040488004190060120f103580382c0c048502e0a446041601160013441000981030f65201091001070319 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 645949559 1250 645948309 645948361
    0x50d0f080901050d09084f030b0a0b01181a09150a021c020c010509091e0c1c060e060906040e1501081e03070308060a030f05031e0309070509 62
    0xb170640d0404409941041c0c81c2c0508020b181046070125890b0304030101c03080c40e051a17072100400060b05002c4800540030340700e131000d201110400000300d8812a00300380700c0e00e0105004181340c0703560b02c001080c403580c80e00740074090b281401e4240a440d0fa00741c403407502009000009a55104400d0004018810110800441d0103000480454580d0f02150100418080c01c1e154540d40c9a13080085ea15003000c607540c94001a0180071b80038040ca48012495085510f07030109981e00313003850094082c003802c100c4520f022900005165085c001130000c1d14010803011002c104145400d240780c0c1079440d272001e402c4c244100865401304206a4841d4040b000f01c52950b811924041002d40804034651000d104581d240d0244002c042d80001c80d40101c0000100c100028628018403030751306403400c500c00b5020350740200d00c152001c00041e1112a0040d5202c0c022002141c9a074036040100d00100b4005d0550001000306000340b103541c81e0000f40500070b644080700c10071a00d03a02c2e040307150b0360700e88480d0340c140140d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 645950809 1250 645949559 645949571
    0x3207030902010302190c02120f0a0b040c05030106031214090d2003030a030605040612020612040302160609031b2301050d0614011106061f2106050406050d0f080901050d 74
    0x8507089660f41d80c801d44244d9070040f0411448d40a20344509407a41c103412244c10540c5a4000261503070a000e80c41441918404074403512900403038219007664200b1202c1c17a0700146110189504405020000354094075458980600ba60104005810b0201c004141c85e20001c1c424070b281030744a40000180c0c0b0003404580d126400300b00020050710b90380c450385000324902038001c1012402d00c04980f8166030007030b00c8a85007022810140d024004002c109074214028582c03002c03005500e6114a100802c5595200040c580c01c3d41070081c082005034170340c0c1010424024040102d1390408090000da9046840301c80410015900140e070039100d0520766203001351418101044114000140651002c0c080e41c3c1c0c50111480741600c2a51068140d03050380d4000045020031031141e10041020200811520b0411101840300c3e000000d10b602700103181100340d0702c43e202031201341054840d03040100310464100e04001100c6d20360720405001000082c086000024680400c0e0b40924201e07203420111601c04c102c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 645952059 1250 645950809 645950857
    0x4080c060c220b04060e190803071104051005060a050c070f0807050d1703070c02092e05010c1401091a06090601031a010e0102010b0406093207030902010302 69
    0x1140c1d00010240b0880e00184480700011140c0c1e00c11202070740c0601c0901881c1ca41803841c00e4070404a4413003e00c0e4000c40100d0b00301084100100c6400c010b0018000442d11340040e85414404994019aa01d005905c6d02081185107400c01140100322241541c140c3c1c0d407001020341c01c071424840d801e01c18001e40300c0d8020000e07084224802003c200c900c044196440c06884804010309903200110160044844582041c614640b2000658020240741841c19660a01340c0c0030911680c01210701a803241c050a00d560b84846164052a0602e407600700001c0c000360070080080e00b200c2c016140504280d00d9000d040c802410301758400b82c000c9400c41078080c0034031150030b03d140300f045040755520b0240240c1d50104449500030300403001002c80d4285000031204403d401103c0507000b07806614115034a0380c0302d07407005480707902c9000013405005a001c03880710b0b2510f00c1c0c0c180c0f0341d0910703030000118000402d860302c00e0030f06010584d07000515480c0200d507448082c00100e005e40580d05401e00c490310300c1044091 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 645953309 1250 645952059 645952081
    0x3020604060e0319030b010306051c0605010602070b0f13051203030114031c0e030a06020c0c01080c07050304060f0903051507020c150405060a090305070603051b090109060804080c06 80
    0x2104522a0009000b40d01c041541035489009820701e01d844996507501c400b0041e40660031010042006260024100340c0e90000a0014944000c4980c1c0b4045020320441c14000c46010b103074003420036400200f42d10740c68199084000e106601c11170041050105801d19071800694030714000b8a0001d064000b22205000030301d483c0e038404c2c45801c1c542c00e0124000520790502150840d03032102020ba01840e030140040e010780c0d8a5110f002d4103a03050045004240c00100c0703501c003030601d07204110010000180800005406071a003e080305039801010710000c80001c1c4000111030030358083c0c1c0703400405022007880a4802203e0394000401c50300421910000f5958010030745445209a9822120b082d0804010300c400362011400501d00400c08100600036400c00d040100003002c441d00d00f01410030398980303840781410350740d0300500b0000b500ca40502c10314209001c2440c1030a0030711842d083c40e0030003481c00a04020402d115508c14080182c0015081c0b2280d982910310021001c0c041c0c550030729202d2010702e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 645954559 1250 645953309 645953311
    0xe0607020a1a0c1902060d050901020c0f0304050a06031404020d0f1712010617040b07181401200309041a090708070801060527060c03040e010509011401120b0402090d030206 76
    0x2010304c55400c03181c1ca032004400a41d410b0580203040c3c986881040040100607100050070000305640070080081010000c00c24900108130410256443c1e86c1030204101d002d540d283c0c400c40406041218143d42c00d20540b00c11504194102d9500c030783d101140c0b40c080024601142d01600170003803c0c100702c0c645412200105030800c4074507004902c981e02d47e0700a4504042c2d140d0400030320907200001400250700114600d4002000d1304015a00118a501c131015200080e00651780004036103440789083e503040052110165041352251340c2d00818103074519541d004022803244500d0310344944401a030305220b1250072694015110b0081c0340b03407002001d00701c4c02059a06600055814000040e86d40c0309005481d0006102c603048100003405981c2c2d80c00150031100c540d83e11180810807518060300800042000b0b0504190160307596242008025192230b05034032039000d44d20090700b01c14140c1c0c0d110070503080502000d04002481e62480003c180280158600039400c102902903c0d402e145e0006400c07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 645955809 1250 645954559 645954577
    0x90311160503100501030809040911030d02030c01050f0403050f0901030b1e0909120717090307030b2202090106050d0b040c021e07050f090702030d061214010c0e0607020a1a 76
    0x89200328021440034013201c50920001d8040d41e000d004c440da0301d1503d82c0103842c0581c05038845e60311404a800019003400b880b1503014005d81d000003102e411050f0213018103a48040403407103400161506d614060300610414524020941c030010303001029038007a0b800341024440103040d100228000054011040449a0006218a5801c1c001402d100c0c0300040c840b5118aa603000c460800000313550301442140000117a01c000141031081c5116502c04100000003075002d03041c10480790411100004400d00310340742c9e010620105c2c0b030000c0c01507283d60746d00504480340ca14005554058420b101001801c01803116035006003499110002c1a074005200c41e019511a0403940b5801d07030703568100395500d4040c458190480c904400c815602d10340000c03640c0c0d104080340103683c6807110151040c0200c0b0000e40102401006200c0c00105000d00710145040d0802441c000700102002c0b410082e1100341c0e034107035051161320002003141c11501d942c00c1c85401000e54800805100d5040030040c0c12542001d410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 645957059 1250 645955809 645955813
    0x18080703080403140a02150c030d090f031701060915020a2117130f03110723090f010506090402040302040609020d110a0906050a0c12090e0108010605060409090311160503 75
    0x82004c0c58001c950502c01c6a4018010380343c0c1110891481010740000d54100c8842c0014044c40201485034026480d04500c540403068041d81c880c9000b03010000b50f40c98002078440c0080041c0401a0001c50110a448498040442d08008948106e203803406018009019030700c0f503941c0c140d0b0454804c410000d03081c51500c42038103d03a0342542c460f40e0030f1000c0310320f900c90941410340800403501d5003092012480c06442c2c031401a00303852442c1071a020b00781d480034180450285e504609001100001b01d0704c07081c21140c42d440c5003042c522007103905c04117001d803500c118000211030f05140d031241e0440d0011a8040e005211080d07851404000940201200000d07460802d2100f918024611044801c0b128a5403036402a80c0c0c28200b04450b40d406c490341800c03c0c45900311504e004940314010071411a42035954a0420702d081c89104502042c0681c00b601030741e81448030a000c2036603a2401e131401d40b11240c000146204240c101250800441d14883c00c03035000740801c0c6000000036503134071010340740700f981 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 645958309 1250 645957059 645957083
    0x2403030e040207030909151a030f010e040503030a0506030c1503180a1505130f05030d0b100f080c04030b010602060a11090f0f0d05011811030a030f18080703080403 72
    0x40c401a44510f81c4010002181c12506000f182050340c40103412103115420b02c0c229980361603d03080f0700422140010002c00e804001c01503401042020305026150450b071f04901401c155659903540d0001600080d589512400003411039181000141000c0c04021301c82030030b00741c3c85003141c00030b41d005403036a200c2d0441d40240e00b000c8450000e10307480c0c01a48068085007507502060b83d0070091101410400050044220040100e41141c0d07a1442160180f000303143d440741007902c408120780348644418041e494504c04400042e401074040c04070342c9100c0c20102020390312418181c0151107150401801c031546000081003242e40050f40503c2142c40e40401c100191a04914120b28041c0d0303d04c45500c40b52840d1003203218100010040f84001c009450030305151aa40d54030303400d44940010b030144030a0381414510503c941c0301c0351540b49680030781c050b00d05d0004a1300c00a20100317400f5086c00c207110580101851000d1000940300007044c0d0030003a207910b607031a813414611542c071500c0159007401c0212 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 645959559 1250 645958309 645958337
    0x1415030a0b2b05061b040315111c05180712050a0203070e10080f060105120a0c03121202040506092e0504030c0b03090c040f111305100f080a0f240303 66
    0x5c1440d06042c00001e1920300380361940e500c01c41300240c0044a03583c0940c42d422488814030740a0b000d01956074404000ca007649002c0c808400840c2d100510366803407d03010180c420014040070031590156020800e00c580c0c1c10f065810040e1801800030f1000707415201d0480c0000c1d0040c03001078240c1c000e04503441c0f074114130341d035418026507600715a00030a607258000307800401c01803800c81c56034941c0355089030980e40c01c21040c1d05d03a010103016540c42540d401c00e40c0d14061203d140e118a02c0b642d601543d80e0218101424140417030782c03601074030039220b005441c210301d0000c41c400031203403a00c0c225130715860b0910000c0704104001c0060300188411540d0544a10002c80c0d603c503180140ca03c607080805c000c20f5822203840030070015101c04200d9075201e42d078a40400100c038040f1001490421215543e6202d954500020721a0342c03100340c242801001101109002c2da5984640d41030b0300035582d600c02242c41d151800102008200445c080c145c02034203080308510780c1070303601c2c43c040131a8001c1d01c0d1044442101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 645960809 1250 645959559 645959581
    0x6030706021204140f100f08010f030c0513020705070b18040c0c0b0a1b03020316050a14091f0e03060a0501180509100507091415030a0b2b0506 63
    0x104440d007000b42d005010500c00c910100d008082019001000215686036103004502c0b0520002d8282d800a0801820001c200790000807a60040c111580903400c0d1070710b140c0301c08815421a0051600c1486400314001d80d210081e0141c1e1003043c0c10100b80c80950340c1e5401142e19550114405004414102d5180c452a281c284902400b0340c40c1d64540d502c030803120707994084141c00d0040c040841e540d503841c886108080341048607011594180c41c0141d590070440164410700b14915103000030090104542100103511800000d0304080c1c0034a1207840c0c802d0f8900249810362085003030b02181e4443c551403480c8550040703068003001000d41c1994610b44403440041e0aa8000740101c0b0541c41c2280205103100c421580450760240d006015102c5114014407140103541c0c06864440020303480590034071052007130440942281004842d20051411500485c9165003c01096110341c50f6803203c43c1901601c4102aa2190046280400350b441c10100f5101c101400d00120644062048a001074024052 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 645962059 1250 645960809 645960823
    0x180501030f030e0102160f051c110d0c0e07050307030f060803041202180f040c0b19051605012906090d060905151009270305210a050603070602 63
    0x1c440300881040c8541c80507100740155040e030604511441310b90240c1c07540403d40d16405880310040740095245007a04020400340080543c4440d0540340303440e0000140c521420318400d03003007a6180036000340b850070302204111a1780d00290020f6945010810760340e50200045219035001d45040000d2030910680701c00311200741c02800c08a81c000c000c2070111100350a5400041d03403005140c142000b0248030003c421002c2600d070f00c4010f000050500c000c0101c9103400501030041514502e00b800c8406000d2480b56102e08441d0090000c0041c45420050350014407a55042e0000000c1c020fa8007282c0031001c0d0b0481400880801021039541040c00e8a41202141d4203520000e02501c1c45468035240d00004004904003180c071841503000303030109001080940783c400c0000c80c0c1a00d451a29105010f0b00b560340314443c0d104885032054440c0585c1068280e620340309601403800a0b110203080c40380154401c0d044002800c0c101101080040f851010341209208000c01c0c1c0c10703154065911002a6a01c0c25 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 645963309 1250 645962059 645962063
    0xa090b0a060806210d0f020a031d01090905070c05010c26093409060806280e0f0c01051201120201031112100503030301080d050c030714030418050103 66
    0x100c0c551042040d507200c0c1c441180c0060f03005000f03030f950420482d090249810500218146500100407602440350428414002441c3c24000f51100943c2ca6034000d2000030800003580b12907001d516000b0103640304284410180500100821035420000030103001810341304d804881c50b41c00e19001c2d84400d8810950745a160500401c1100040305030080701e0000c250081801005115007203101c9601c5541c2c4050341200c40b00b41c0034144607074418007182c40003030040e0717040700115504240301041014400110382d58840500c0da0119000642100c43d07540d81403181168462a50800004141c4804023158401c500d03a08001158000300040c0010345140c040d010501007128240e000420400003803e01d00720603030b44145400101816140780320b14440c3c009a14541010102d00100f08201d8032100d50940546400c030300550642d85841e0101b5510765030064002c0422201091040302d614080041e103c0c116407040c201461292495100382d6a40c00ca4400ca04580321880b028031400c089a10072a4140c075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 645964559 1250 645963309 645963319
    0x30515041a0409020301020d1803030605030a0f060b03011b050d050f070c0201050f0702030304261c110a08040602011e0c050d0b01051b010e150c03040227070305060a090b 75
    0x2038840d0701008002c0c01c1159090b81c00d55003c0005101800c06403184004010002c40c07015030078211810020308030707105900424044e2b40405540000304d0b44204901c078089a00c03000105500500c1c10109025204040040c840b201d40c2d071207c03402c1c0c56002005009400d03003042041150350b4580d03600c0d0001c00c1003920344034003080e1054134410240d4132a5000b0070a002d0207a808a103407000c0d071382c082865503110380e0083d140e00310003c5100746410030070908054500c1e030b900018210285891100c4007188050f54524091100104154245440030301c402023078175802002031070f2590b81d00c40000e070280c03100c4401f45003980b0000302c213040088413501c501030600e00359550f014100602d01501d800105604180c0c541400020311098484400802180050319201000810080e900c0c14901d40340010303141800000d200b0110410694800d0340301900d82c0990102d5040c090941c0500b04450131410310395926402080180400c40c0c0c0c550150801402120b040e191f45a0b0250b403001040202c0d040b00420680c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 645965809 1250 645964559 645964601
    0xf020901021005270304030b0106050d0605030609060c0c0f0a0b0414070b0d0c170709060f0f0c0b0402150706020301060f0905060703030e0118060615030b03150417070303051504 78
    0x213600c01d40014100da60302541183c1c030b040d459854540142c40c0076840725001410016008071000014040c000042500b50010314060404c501000e845840c010700d007034581000450450b0032502c04208282440c5188030964000d10790905004840c84000c5500b542c04420f41c66030400070b144009011000c44207642c000b541800c081c0000340003d001d00c80011010828031002980011300c2190200703000d403210303882d00d4003942d1420801030207a006c649000d10911202c00720390b004c0c6903008280009103e920031204032042c0e0320303440003424070740d01860701c2081c0d4000412003004208155000314143e807910303243c009416440315800c84840c0d5541c09040e030045c80a01c803070b030b000034001d401801034422050700108201108400d59000754418200c2038800d81d072540020003000c0014501017034820301500e0140140c1001d9030201e9a9402201802058105c07150000b80510a946542c600010050643c4030f84e10170032414000c0107402d06542016078001c03c0c1100b604145028070031a6001c403108540a451 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 645967059 1250 645965809 645965851
    0x1806111c05060a1d040507080102090121090c1d06040b0607140106150c0c0b0304021c050c06071101030e15070c0311030c010e070f05090c0304020d060f020901021005 73
    0x5081d000d0201a0008458240821000342d481c2d840031300f0502503500791041c0e150909019162450715402004603901c1001034400f641d03441000c0c0350004086020f5076040b103c040c40c3c0f08008024549004e0701414400c50003007917040d804070900c0220710820100111507125502000201c9003440ca099510203010002000042ca9101000d850003444030700004d034541d554404404020315002043d0002030340002201c003042500c03403c050180c96519801819490960f012880c3c098030717803801c910b86c2d0310810b01d40010850708000224280901409944e100d40d0f080c0342001c0074a8940020a01090030050151080c1c440000d07407141208040820342030a480c0e026083e40d581113154019020048099009090000d04200403c0a008440c00018000f918075070b00390309040031a0081c0a41d10031b0801c0403c1940e0780c02100a80090498080c0d45e6241c503144001210380342c4564004240d1070900302011621015030740901000308003030b000e581c000080c0050540864400702c038140b103004840042c4c0c2a03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 645968309 1250 645967059 645967061
    0x203041a09030714041d0a140f0109150b01030c090902091311040501020111070c06050d2301080601050f1302030a02070c03060618020703020d0810091806111c 70
    0x30308054104850340c504244040400d04045054025546403840d2079400d600509051042c00011400140c40c5058000b2088041b903c03040c1984029000445800000c411141c00340998841c0d24010402040008818688040c10256400c603c2d041c0c0c03071400c2c01480c4294003038020a081032a041e0b031000302c0d0383d05144182c0000c0d044106410342204041006031a0180e0a1003070884016006540603255880c0a000900b035518080c1031105401c41030003103100282000003c3e00c240c403407a04105483d0002c0402110080006400c41000380171420500580d510303c5140d2133051798014001d50340c40c1c1c1c1c1c0352000c3c05100c009140c02030350032000c210620441d45c0c10942c0a07541155410001610300582c548603400e070b0402c2500260740d42580c03214101311010502006c0040000034410540c10110b240e00c0117034650214068110910a04c00000740041035104c50078005404114010800e55040760004004400745050803181185000480b00111040c407094440c0c460300c1d0a02003524107a8003960b14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 645969559 1250 645968309 645968339
    0xc012910030c3204060504051f17150a291804050c04090e070609051c02011110020d060f05040b09011e080604061a09040b01060c051015150302030106020304 69
    0x79100f0302010885a9180004001003000f0303c00f56071100d44441c185020060030146c2c607003003100340840c544054452140c00812a02c1705281c12140418203a540900c445407861503030340c2d0190302c10045400891010300045401c91000282c040a0b600105541020354080c8038040040e124817180c03a58002c0c1038503254102c3c5621640c0e0141850030607556186080580b040d40b50b2586c40c90b009403406100c05030340541c1c2c2c3c200504003118800c4280240c8042544910240c00c0c011741040600410324803403440c00c001c450078000303903140d0865803801d03101c40c2c0704018605801f9007510f02c42c94000004051915001e2480400401401214035034604094003000c8044090340e0f0007104210000003e0548040c40213070702c1507004a1021504844824000f080c10480c1004d11348100410428000401d03c1000158152a818100740d80315030042d0500a19109140e40035203460b07070811540c0d50780c02c05d80300b4644040780d0030b40e840026000103a1030264143e000902a0000582c0180010012540d114100f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 645970809 1250 645969559 645969617
    0xd0b010510020c0406090204060f0206071209050a0b0702030c0d02030405030d0806031608071d0907170f03040f08060708010b121305010e06060108090712080c012910030c 75
    0x3c440c01502d01c2c0100d016200c4d2940076008059000c68100071250300008000c181150600c0030305410700c0c10040c0036250803112104200c02e07a07030312940d80080050801140d0400364014545800c58502840000e41c0c0b544044802d003458011301e014000240c0c00041620140d41004018140303c03000c5c400111104480145003d42c944a503051281c15040140c2c41da50160a0200103803840c10f00702250001c0d4409250310310310300c2241e6031007007015009000c00c92009841d01100d6001d40b13081032000441c03606074500d0840e000d0303001c000f800107500c2039008403900407502d05400303441083d80c540d001510401d034248554465107001708800c0c8404141c1e4516158007000846074240c0d4290700741c5a440c00c5038824010103400b41c1c00341051007413a43e0800203060344100c100e401024028101000b81005e010300100c000c200c182e001c1222078801d0300a4201c008840a000d5072082d03541d40c40e82d1800400c03550300c0c0b4a1030059101d5030916280a1103801000c10b805004c0d100c2010000e030701c941c0744005003410945 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 645972059 1250 645970809 645970813
    0x1140307082a060708040305010501050901061e090b0c0f070e060109091e02041d0c190509060d020f04031406010f050108060409050715030f0204051008100f0303050c0105060d0b01051002 82
    0x10b614081d80d072400604000c6004240c12601c0e5030540c43c0950031148181c111900c181c02d400010045590b00413481540f003034400c0e0100500411350501554030060b80d0f00111003034480030901884072900041e858000800d08812901000d507560242c51120000343c8031103000500c1c041042c0140070094000850b0740b1b4150700503000001c0c0f0114004100e8000b9000b803a001400307403203018841200500401c0d0071203426014589010418260b0441c10440704548800348180400d07031818960341c21050380e51003a82d08070155503c001c3c21b003207045954418002216038000d410b107a44552180028801d041e2103504080d02c2069045c0760054402c40001000030b61700c140c483d805000080e005006080007002c08001c4626444c90030540a41034441001064103010301c1030004010941d151029400c0319003141c1880881030316030043c09007c50b40141c1044d03480d031918000000c20103a00030001c0802c065600c00800580c4c4070381c07040100c03842040e400079064142ca40c005105501d020140304c1c03132641040c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 645973309 1250 645972059 645972133
    0xc1e010e120c040f0c1139030102040905071d1804060f0e0d0e03030309030f07030c080c06010905010905040302251706070206071701120303060306020d050114030708 73
    0x1010748150f4056150341e645c9418004455540002c0901c014000d100301400700a084400d02e489003802d0100c482910140c046000141b0140c040741ca01e85511010b0000c3d0f40d12500c2e803102e18058142078070301078000358101380760390b0020b00355200b4103003101402840c2b00300111003c3d05c01d510108010300b0559031142da92030841c22a1031144034070a90307a030766240074055009500302c008c0c0401c1c0080194078000d0300100100120002e02104072440c150303980b070006888102c0ba003011100d401e03a0758802800c038000080c41d255007500001d0024100e5854600034019aa02d0706802801e449043e500100540d01915031124400b181e0215039951044080f410030301c03141d441030b080305070828510b03a50003d0381001050207003a1b03506200256100da4181000304000c6050030340070018203014030071035900e0403084a8420401d03100b504000d00460304a1400c9d500c51100c45c0010700180000e2280d040010308104091006084c00b240300c40858240b4000380003030265105010940300c0300b4980551845511507 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 645974559 1250 645973309 645973333
    0xb090f060913060305070801020f040918121e0e06070312021e120a0209100807030f06080318010306060203070b0c0405060a02060910060b0714010f020c0c1e010e12 72
    0xb4000b1114003495400114401e841c5042c290309042d060742054401e41d004010841c0c80ca0714050885040712001000040d141481801261405c0c8800c040207200c031880f0344080c50003551001d912a12003c403035002030b4000703244007002d80307000d503991703540681103201032101001090003007500c4120a20455405440e107407100c003a143d0940d0552110040100000ca0301062804507420708603406603954604500d4a0902c0001440c4408114160400c21898400080b02d042c441d400ca49a158a400c90600080f074445a01a07241d801c14034001d03030025016015074450398841c0c00303000c0c101c0b04c180c0c010710303e455901c1d1038412905500420f1091100320800c000290b41d12800000c008102441d4050440b50030b103040c03004e05103203020303015010107420304000748441803020044800710783e440720704807000e01104442d0300d02615412018195140c400324001d0714030340c0c5c04030307410030a4001281d1000009661000360700d0761090040103107000036801040c100f01814050303072104c0317144440c600300c400c40c0c9031306 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 645975809 1250 645974559 645974569
    0x112030815030d0f02060114030319030b0d03111522030e0a080601030b011a030711010b0d0b010611011104090b0307080109031d09040f031d09041b0b040b090f0609 72
    0x10312141c43c00a0100c040c4c04040590600c4101d024049640c00503e448484c0000031faa00e0244a0300c10380741c0d5001504591800d400703130340816001c0c4c034090001140b101d268140a0b04440d40e080161000c0d01900320317442400d04c00d910b421131090141040400d55120300070f0302c401803032078100c100301d09001c02d8440c032040c0741d5201c401810007480180c00070f1800f581940b4000000d01c8040c0d0204000c18000810440700301d0800080c1c030360014091520284038074110441e18050020f10340025004800d583e0048184600c659000b410382ea4651114040b40000355602400c0b0780c1602d25001c0315640522050040c200c41c0e0300082d5200341d0042c121003145440f02402d900f1076086010480200300c00a590070240c44882c4111003021008030b071b10301418a841e40310034a0039040088024100005542500c5111030703809410604200301400031191071429152807944103907820458800050300303003000280104c02c10111000c3d19140c8010b1030402002c2000e1082409a110901c0d0b40311009210703401d490f4032a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 645977059 1250 645975809 645975823
    0x80406200408010c02010e07060f2105070c1211060c07061e090510060312081021060b0907020a1202030405120d090b1e0d0603021f17011203081503 65
    0x220360b0002402c03d502d10b01c013a0071107103a401410002d030032006041040c0c0703400c801070b140120840d04081c1c0030b181803104030440300340000c4422404a460101400300c2da030345c00100074050754840e407018820003e010405031260b4040c80d0002c00203611030800280790f10a94000b070066188a04d20100381e503101442e155001c01c841d81e2202000c180e8a000000501c1005c12000310380c07101c101c00411141d400d507119003064030b5840d2070b081c0500c4405404030740d2520081074590b0081000d0024030000240ca0000100749002c00602642c015044c000e6004140c0303070516542d401440160001c100300d61095581d603c0301c041c2144118254001444001520384a44410340d120400d000041c05109a4040002d0031303070062a04000382c1e10605004803000303d428401082d034102c504a0b4555100c0d020201d40d0800307030446410094011030903000c40e60f0301c01d40f21960055503500301e0701e40038032084418940c1c2d50008006d10900c0d504401a0f0b000c60040380c0901c803001d801c01241c060269203c40290003007850308030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 645978309 1250 645977059 645977069
    0x1101110c1501050415090e0a02030709020414060c1e0a050601270606050315030307170421170a0201091208010807050906281e03020405070c02010804062004 69
    0xa1400c010150a880001d680500700c11141002000d50034191078107000741500030134641da5560121030040d44820416450020342c01011951602d440d07601200103508103100d0350700105017071801100c0d0ba18102d000d40e01310000101c02000a0051500c41607181101b40700b01440341e006401104011a100b070211501800310024491840c00210170349010b058081c2009644082c45d01c8402d200b1aa03210007125000548014914a0100031100103411071040a8004207031142c001245110194124050030490380a10304180b000c5110440081ba03d150104005000d005406401c4003080e115402034000d05655100000b0640020303a03031111000c40c10b54554000c111403900400c401c2904112a0025040aa8000b010340c01c0100200380304401000203029a804020103551000c510055040d004010149100201340041c03100031009503214001030380101d080100094099004000c942c41d42c55041e507804c1c200d5512a1a9400102060100c0a00018060f020302089507030100140001d84 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 645979559 1250 645978309 645978313
    0x509130e0102031e04020a03170d0e0a0611030c03070311121e2a070302030913090204050601050702060306091009020f030108070f030c1703090618042a1101110c 71
    0x82410701011002c503005601013107848440300300b0800103849000058003140e51000701105520320070107a103641c0d8001c51001c03140c03d901e020280340c000c0b00b00044008441e401003404003c0d1034030800c01c103076003440300300d940e401030a03410004581ca03030380b196100740480019101e03103074240110004c0c031000c81d0000b9504900c03a2508041c0b1070048080d0200e0a41e0020410f03002c403603040f85001071188000180a82c0f1107400140800c084003814001d01c112500000d00900200c658141c034407210009152030349007a4040c40c0780c240080d50302d5008008840a4a0700105420f04581c0e98034100815190000c00307000b0b100e0415040052520302600142090001c2090361a0b01c3c1d6041c0800180f600c803036580803199009904d4401c20108030006c062405441c030452005a0821154160700c0c0b86208160006800c08070003e600c540e6881c0c03d040751070f28080c040760184201c42100d00c0304034040015848400145c04d10510b011242c6009403003544400100c4000403036100042c032440101038000480424190f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 645980809 1250 645979559 645979561
    0xc1c02030c07210905130e0607020709050a18110102010609060b1804060509040803040f050a24064b031e03020d0305130209010b09011202040b0a0509130e010203 71
    0x200c0240414490f80c1ca506060381558031180c4000c04030303000352060b00d01a001400b100704d9800d8541d00a216801c2c4288225050f50500c02c0c0004d544401c0c5208100405d841c040c08940d60107110300508030200d000243e20007180026454103200241d00c41c40f81d5056650f10b600018009509028000041c201d502d80745071514144420410400203000601c1c0c4101e02d0706400b8005641e68100060b00f154004442c1c44d140c0e40c603842d04000e40442e43e20050101e2080070450810003030704810700f242e251140003600030782484010b40794082d42c030f03175000e11681d00e41000c1e500050249500c4150500b4404a003c051016040c01304010b4402071450417200200c0d0902000e0007400001d901110402c03030450140e0301c8003052610700945541020644600b0540c030394000c983c1b041e440115a0320190b40003041002c041d6901c9038103104940c1710212180c0030502010300c4424000c09413095034100e030b12a00303113035280680710141151917034065010140e00902c4c00309c1550300b0704814440d452100088400040c0d40e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 645982059 1250 645980809 645980813
    0x90138030303040f030e2d18060906040f060b0d15060c0314032e0503010c020f1b04060f08060702100608030702090604020f0a08040c05180c1c02030c07 67
    0x82961040558000e500030400e00000848000e0049903903905480d000520320741d200001218198003104803144d400d42c8010102c900e0540301c2401050500454080804400e200280580000116020b6500c0081400014820300b042e0f04000c01000740114009103c2e92035060300590f5070000c0d002114107036612451200001c05200d04a005020a0b040c110310115046c0e0f80140000001240310140a03c0031002c40c1082586800c800c1d41c2e4803c01c2c0840d0749120b121042d0400e0f80c4141d1040d41e02c29070800ea110211503001182007031f2121010000381140484401304800840071081c10503400036620900010182c2c6604040c03000303058000060b01d01c5043c040c400903d004000f10251640301d20780b500401440d20004112107000381c1c1510903080782d2381e070075001500034010505c0d0001482030004903030307e81c40d0340410191320540c1f10700d0140c1c0040781c4800521040504408035500c507042c85c03101040c907007074141d8090641c1c400c0b0000d45c08602000341443c2d1069800c241c83d0569000d5000ca20401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 645983309 1250 645982059 645982151
    0x3211d07051005161403120a05100906060e040513020d050f060603120a0e0301110d090201110303060d0f21170604110301061b0501050f0f0c0406170901 67
    0x62940303991900c9810b0410b6130b00c1d49202451400c0004014055070080c03040c2008061041e620340ca903103255100c5951070074035040717406000100c90340e03a09030a0007100441d18116610600050f10502c2d540e20610604100c00d0100401000d41002c200c6840c8500b610010307550b007408551007a01c158040c16143d405080058602030f0050030441c440e0700b00ca010401d5a60605040d14000d8000d445d02c0c1802c1c6401c440401d006012a000d03c203040440011402c20713454450700540c60480c800c0c1d070707481e618146181e03405031640010784803581d111244070030050201c0e10514814541900525208004d500007080510f0703000540b01200002c11071881940c20007646803c0e445602c0b110988082c02810301c81c0303d450002c1e201c140034082c148501307070b001440900c00e4808208021039010300208010b0914801042000700c00f200d100944289900004404609581c1550b0441e50326483d07114201e1000c13640c3e52182d203801001c81c5915903803500036055200c5039020051140513207500d40c00080b211070400030703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 645984559 1250 645983309 645983329
    0x908070f210e040f020c0d2307150207020a0b1914090a150306030611070203010507090803030c07030e042906040303050f0c010b0325050d03211d0705 66
    0x401001550711030100c255410000e846400c1e0401c030f6000401034910b070341d42e038003d0241031281e101d0380c4100064012816045024280d00c00c01824440b105400b8040d4031810f00d00c201d0000030311030b4407003d200c000300c421260054607120748010881348415443c0d1451980c0c80e00941155200a070b4440b0301405035a07006288009444c6c1c0c0d81c0202803924220101081c1000700301c1c407072200c80040e11400a400c9510a034840009154405000d0260046008a16a69400c40c8400ba4425440c20780840d040a0040e140a001c84800ca0f001c1c40c1182d540300344400785900030718010382c1400301094102e00217613500e20545120302c180302001348800b00c440c00b04808400404010030300482040005202080d048015030700a9030f1b51405040d51100303084c034241d0142140f0141c040d010302c248500c0940542c04802003103140400b104503224060364910401c0a010005000035001c100e44940b581c27042c0351052420701c90b403003d07501c0100b5105207985400c1420109490625205e400c238900a1240d46043c803118 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 645985809 1250 645984559 645984593
    0x140a090311040c170405010b130501140907140f09041e0e03090105180607020301140a0b010c0b1f0302120307110f0307051207030b070c0201020f07080d03020c010908070f 75
    0x10001e10154400c05083e184510844d00003034a80100041c08000c001d40007520403541c00b80482c81c0030810400b4003000340ca402c0c01080920001e0440040b414240705000e9480ba40040e03031118443c924070031454405501c440003da00040d020461000030303403150301482d1040c0426040e48200e14010000c04400c556034003002c0ba1040d00100500700650784d000702034813079010310440c40266001d4503200080a0344600d500084d0103500b481d0b842c0c1e03540082101030502c104030a20007407042e0b500e100011240c024100c00024038600d00f400100d034444880c079036030780c80c0d600d5079101c40c440044e01c80d00001c000716103e0b058101d19600c0050f0301400c00410f6031600094281c01c1c4c440c8507845001d00000b0380c0342d5400b80505c50242c1c03000c0d41c2071032140a042003100300850f0415a041ca681c04c1c42b0100408080801c08141d000d4410702160b030f1503440001035820102c2c0c924002a0003c0e8010600807006580a038049213215034035003103003d0108110400401c0c49901c00da400c22121911031414643e021501449 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 645987059 1250 645985809 645985811
    0x3031c0c0c0206220305011a0a0602070f03060b01030b030145020409080f030a06140904050d030b0301020706020f070b1b030c0f2205030615060d0c140a09031104 71
    0x950005807600010380b03140c0c980c440030104c1c1a030034042d441603240310319a101030215801c1c074060010f4480350644085030341100f40c6607040c9154449900b660b45807043e100ea0a40000c0e00e0008201144d8158001d8000da00c052602103149121100003a096882c8900e0011020a00031007040e48040768a6000145003510300c0c000243c2c000c8041c5021204501400180c0a0f1f03480e0f592800411221804451032056501c44498803814243d540000900c910f004500200e0300810484803180340c0134091a00c1a031740180200380380e05800d00101c2c098001d803c00c503030b0159001e00c42c290000300c542c0050a039880700e040095850741182d040488145201510561900c80e2034076040c80c11410810481c1da1220a000c40281c0d41c61029600e01500e2003280c0c3c0c2840c025044003868400040001300c02404c0700d80031400c913102d5868800d140b00302d4000140c246603100381d00b0401c007195008260820342403400207043c649039010172815200341e1544840c03664000034400100038000c2000380380580100b40d0303081d64 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 645988309 1250 645987059 645987077
    0x906100f05030a02040c0201060b071a06010c050d0c03050c01090602090307150c11190623161514090a06060801020a080c03101511070905060a06050d0b03031c0c 71
    0x2002c02e49960080001038040d5072a50641c0300380798009d400580003804c080100300d55406141c00c2840d00b01c08562030003c00420000003284407980f14000c540325280d0020080e01c0030b20b22026040e540542011003c0781807000610030807a0190703084c898003101c4ad00924009d07030756031b14074010541402542d0b01302c2884404000856040c0c2d680c89140b5003401076210300740d102c0d42101c24001800483c1508809130b01c20105940c0401c034554443c00c0e80c1c2d02c40310b481d1500f0351816400d401c00c005a024000b40281c0071003a107092200882c054852075141004040000030309450030448013403168208886100d03956002000c3c120411080b0b100f100c00900401000318240490028002c02101c00a880c0d02d80303c00d804000310395180303a0784000300c0042c140c441d4032031880780305004050a0300607410034149290042070400101103c0300e0148500c19000244400c500c141071042c1510503403c0f00c103e040c4400e9455190141309e0314208002c0084056050400070140c100200100c203a40b800f0019070104900c8407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 645989559 1250 645988309 645988319
    0xa08030901091424070203040b0a0c020f0406050321190c1a07140d0b0901030b07030b180105040c050c0a05060406230103081c0513050607080103080a0302031b030906100f 75
    0x404c180d08910100c004601d919101c20100301c0c40c5020f03d80207111b07084000144440040d42181000340d80c64425182c1004214003842040201c1e0f04d50700c90307903405402528014485820b4580611401c1805205050401030600326481c20014142240008942543c0500301840a09003c5908105c0708284d0b081d1280307450702c002030085402d045a84261403011070f62034551034076074010722140c88001c3c05d44001503940b401d00505d404016241000480e2400003481d4042c01d004218141d1031404400c0740102d0303440c0c08140401011550b614808022052181c408245000d000c554030a5015000070b00b068149070400c03401700c500000c4003506900d8541c0c061041001e0f40c40000341182d820902564640c040c54000030f50b50156058885080c5150004200c1004460300006240c42d00600844400381c1e076840c03056900520a02001d00f041d04184200c030601446500107540c015280c5240b40628665202c0f502c215801c203035682d56180d005401001902d109040c1214010300c001605003405070300e44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 645990809 1250 645989559 645989593
    0xa03050409050709050603040b180a050613170403120e09063115090c020f030304140703140109020111070b07021905190603140105060d0e0a080309010914 68
    0x24481c840300c260711900018000c900901d032000052901404031030356860103103000c1000350700031160b60300c50181d03c8184101d941000600d480405030710000800254503aa0480714031a02c030450211801004000c4100919000401820046104000c0d80c800c0f40d01c41003014040364080c030341c0140a9102503080109a648035110031807184074000d42cad5508440e40350074038481d5040c3c4e02080030116003002e000180345007000200400304d805006e000c1156020b5107a080381c8030075813248104195841807011802060015200c0059042080100d44045660742c0e10022201406200b541750707655984500f5003035582082c6590754401c100405000b449080a910f200c840c001c0c1c2c030010f405154002c81919941d01c804940c00c1c058030000b0114848003016020b0301d0030b994124018200040d0170192079218041180440301c0c145c03480101021b0920740d14214a80081c4510040182c0b44c0c441c5840a5020803c664001d6004010410001c20f0a150500f044442038420200c80c0c40d0f03e6004001c400304146030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 645992059 1250 645990809 645990817
    0xd031107020f01360302091006021c050d0504030f080603060603100c0302120414070e0c07120513060905040c020f06060907021203090d0305010501051c1104030b04050a140a0305 78
    0xb420400000c05808a94211084c8005010040004001450b0140c0604090040101c0380701701c8428141e0f986403045500708105a11459001d81d1103042c0360b20102c9070f40c0c181c2c0785001d030072450442d0070460a0440c45007500c1c0140d0317042c0c0c0800c41d0441d0000385103a000384029072003201a0002c124900380400481c0c0ea481f402c003840c04807195900e0710b007066580301e60112043c1c3c00c031401049109041c18145086400004076001c50640b04036000062501c5071146800e201b5803e5440850501c0629207441c18a2a244060300b402c11104000069525002e03440c4013000e0200d03a9220560503041c4410700c8200c420041520f0250761202e4040c4803103c1c00000c0c0e0f958044000d0383e42545a032074814041e0301c0c1c007151071144110000080200300c80844006865441c0003c0f541c0c05100b166a1030f401075601e80b1440032404487d0070700e25026501d80c5c0450304041c0d8020521030300c8070701e45540c0e6219640107203c02d407001c4620350450b22042060001107444c1c044880902c0000d084007050f955005411441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 645993309 1250 645992059 645992089
    0xa0803270402071a090d08040f0b10031a09010b0a0305030d24030f2d060e120d020d14101403011b0513060513091a10020d03110702 58
    0x18150000d000d4075103440e010b54007416802500b03ea56144030908004205404503000032043c8158000c0504491240d00c03514004c41e0410000c03100980580c841c001034601c003c15002d200b15039120004005881c0d40d080a015408401c24583d05003480d44125003940c481500e200d00c5110f12140c00d02c00b1403404801c44524101024000509600c40001c6400340501c00c0f400312542c407103801e0004184100b0741c0c181c240a92060031902001c588041d02200102583d0381000c1d004078520200c400012500d44c0100c040503031800807036180c0c4105030324070042a03001c4070001100503008a40c0a40c145280d0241c2c070a000030308503010b030991070310745001c08409025114403c0c0c110300104110030f498500303620414400301d080401440c124201030003d401070b03101d100c0e4100ca6005001002031428812000d1711803d000e000c140c48805450300488401500080d4640e002402e044840d0241a40d200c800c0c1503800790168026003817a082010025089945100c0400e44000040010400594441c00b10202601d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 645994559 1250 645993309 645993367
    0x3090c040b130c050406090905010f090e0a0203061003031701050108130c0f1202130902100e0102010b060406021606021b010f02010b0409060f11190c140601060e0a0803 74
    0x14154000450030040d809441e03112a01d0074010f01e2080c0e5110005100b9261141c031040b60f126510440c10080340d42c2482042d0541e00c45540900c86480c540c0c11420748190018211042411a034000905118082d14175107880c04c0355010030010103030060700c04002d0910800d07022090751714100010b80f019a0043c4140600b440d4a542181003207174034400390b809411038000c0d420a0300c0e12005140c8103041c0c01202070348200d460030180c0e80d030396181d8011045840d501030041860880c3c2d080c003e80d032603404071400c02d042d9502c50840c00159101c120140004005c1031380188800389580003070b20001e00f21504018115000442050005118600744c5c944060b02844d00c4504550a100f04a00600540300e200340c0c4203041c60729030000c0c84481d821112568000842c100720540301120f40031154414845180150055071088004c014000d522442c4868021444c2c0d01ba0545408015800c1c050240c0140010030b074030030031344091410400780207409003903d14011031034480d14820b5140d003260042c40ca903003e2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 645995809 1250 645994559 645994571
    0x10c0501141f030c0e04020d211205040210111f0b0108071b150e0102033409090b0409080f070512070305180a05030706020c03010c0801150507031b050c1503090c04 72
    0x10344a0b0035523542c8a5030070481c18110303a048816500c411050040c0ca030701c006175041600554418882c0305c4c09001e50350044c00c000d0300300d8030500103842448040d90004214000c03503003418508040c0003400804620394100001b04203040303500160a164019000074100041f03541c1188181c440c40c60300074880c507040103d500a078000001420064080324412660950000c03051180e00201d01061148000010b0045856030018620b2040404182d40d031803000035120160400c03031411a40e0003181c400101a1001c1942003254881241c16400f0040220a000f40046d091082c000144070601c40380e400032910616001036a28024414011000307590020444c1d242034a2491b03036400400d00080c00041c043e120381907941c0e60003a4030b420346440414081d5080c2140c02e201d940c401e4606605a03413048451064600090380d08950742d420001d801c5040c401100122068001015228121148607000422204189806101c0302c01891401c0c90500c102c1401031260b9000c02041c0d01eaa8080e05403400905 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 645997059 1250 645995809 645995813
    0x120602070f0f031101050c19120b0307060c0c06020c0906090a06080607050d110a1e09090204141806240f0403030503180309010e0f010c0501141f030c0e04 68
    0x2203181e14002d00b807000c1c29a1803420103410500e50703e109240c0b04020802036072501c0e065032140c441c406c0000d180c82c0d400c1030204c001c0d50040d080030b4900e01107900b0000c0e00400e0100800d2901c02e8075004000441c030250242c40c1040f010b0ba140b48050015480a0700490040310040f610314407020b40005c6c80b0b401c0d0f200000c1c4034048198040380c018010300003164920300f044680540190300401108241a007003503140c0c1e113030b0b0043d00202c910300b403c0790b0340b8664031101d2500b101850a0540c903041c82003154554000841c030340380c1c0c00504003a020391400c0c0460509408104401c55492180d100d8445014504101ea15603501c601100072400b40150a00c0001c2c0d21640000248074800c031041501c0d0020a002c07013855404006103109500410020400000101d4450381e00d00a65054078002034015850500354144441301040c070b0103043c10018410001070361000d00391900c1884c40c5d08074000b620104008200604054007810707840310318040ad020700310b88540c0c54001c4140140609003141c4808181 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 645998309 1250 645997059 645997073
    0x170a0b040209180a0320150606030403140705010605360c09091006020c031515040b130504060b0105040e130201050c03041e090501140121140406110412060207 70
    0x24201d008100b034848005551030060502e21281c0b901d0030b0702070940100000d400c1c400082d18401e121074244c020040b6508c0408000700d5500080c001c900b0404040403503103604aa21015013101c41c4650004034400781131005100b02046140036908081c602d4030289450006691304103000601c05084101c07403582e0b500c0784c883e05881180b003490741180c4802c0401a0110103508002d065a13525425150441d800c0001c15680c1c1c3d04802039140302c0f000d0100420361103031174583d280004120260020440741c003a9400100c46c84034690300100c0f00340d00c0b070082008101e4a80300c0d80184c00824203100303040500717003014031485c548011b010308092a12910540c06682c0036000703583c503d10555045964441c0c40e4125100c0c200d003204214005806207900105124019008581c180d501001d148450250700304011580e505a4644038061f100b42410442c200d44481d0144400117040075610301054207041c58004102c80035804a4002003100384001d2084003244100294081d4101d01e01503220950340c2400c803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 645999559 1250 645998309 645998341
    0x50c070f030b1b2d0a180611030a0522080307030201050c03070c030809460312150906081501080115050d060222030b0601030924020f0c0106170a0b040209 68
    0x5161102c01190017001142c4c0019048001410004040a9079a940e10281d400380038003041189640c005100141003284aa0060000710310184803c188072200002107104883c40c64200c4000c2d5040041c41d60185602400384a800101a1815620394540b9041c0103040d201159801020451144c010507070b130608c02c004011403526481a042403c41c0c080030012101e0140c00d100c0c903030038609180100c021140304020410042d4158807007400b560304407608200140034881448086034042c1c04041440d041500c00c40e4060114400100744030810224510010702050380900601c1e070400410114920a8209c1d400c1203c0b41070399030700b2245184d45000310103030061101c01508100c4c0e00c1300d0708080907a103842031400c9a0044203c3c00c0d99443c0d00c001141501d58024026020075211030140e6a0300305040d02e805c0d0522803244005061201034080b800c00741d4010100400103a45880c401d020340d001d841c0d40d47c500c02c0c05407001002618a03540c0c40703403082040144060f00c252000000181c8a12940d4141 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 646000809 1250 645999559 645999637
    0xf0610020d110c04020c0708150c040308090103140403110c0609030a1103031b07050103060b0c060f0702011118030606060a0918060b070606032d0b0403050c070f030b1b 74
    0xa54851b0385468205070380765101e218551492094100244140c030101d0320403801400207000ea14a0182143c841d405164040c801c424105035581c2c40b00140010007030341c0107001d9480781e55548802a40c048015150000307a600e00c0f840386c0c2007040300007040d503000102c140079554048013003403c03080c8a00004c6d046010300c0b20818011000f149900c0000000840e411007524003d803400c0158544914154615004940c40c28050b980520045540d0314000c5d01c02d40c0c1c1c4242c0d1403001064200706081d5480030340d042510050158014508115024a014028a6800382081e240c480c102014007100910b40980c0d8815154214a918010891082a1340066015203400c1059555030b9050b071508400400c8a84002d481c4021b00c000c01c0c0d01e440b40074200780c00344459585a100710fa0043c903110710490483c050011400d00100304240d04d03c210050003860001c05030701103980115442c1d4240481159030003040c01c07507405449141410405c02d000d090f50b0340081404410300e8804030b1105840407040740130000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 646002059 1250 646000809 646000811
    0xa060917032e120312060f0b0c0613052505060307020d090b13050105031909050f0d03020424020114101a0903061f0e0109050f0610020d110c04 63
    0x30018031500000000c40400100c041d0b031103561000481541c10348050380100c03110142640e0804010a1041044407100004c42c40005130042d9901201a5407846c00e6204807140c20700418202c038036600c00d00c1a55480100800031400e080b26641e43c0503191814000d501400350600070b07030324604001d450850005000c0243c50031781c0d0303810310310340180d5100050020000058100a0081000314001064032184c0b90300058000e40542003500540b801e4100a00c01e145050030130214a00c02101801100c034624003e4024041851045c1d0100d07060002c01c045010038103004000c100f04160f071040f03900741458800009210024104c1c00b0880c0500704140ca1011180c0183c1d05000842582c022510100d400503c0148408a860301c00f94110f401943c0301030398550080700c000b52030006504c91007116240d18000010003d501c40c4480c0b28800402e0300702c3c510781940d48081120000b00302d460b4540028081f10341000302c60030514007d533201f201c0d00000d400c11004042034580c0400c200412581c80c031f80140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 646003309 1250 646002059 646002061
    0xf0a15170a090623160e0402070b04020310060807090903120f1d070b0f09060d14061302090a05042417070f0b070611072a170a06091703 60
    0x9110701c050881c407442500e1951405507a191103a1452400301070221348100c0c00f8810b40e4507490f580042e620340030303c8401409141c00d03c00340d03030350303a10320040011500c1010405001c1c2010b005242c50b043c661040440184c0c034182d0248900e240004283c001c9034154800850b400601b45000c4400d00c0c4006201400c450401708020000820f641003502010a4041041080341680d85c40030364588140c464052012401c1162003200c1c7c12460080c00800800341515144c003044544d21b904460f1200c419410f400f20070340130f020a61600c00100d204175804070710290305141e124400107031140c83c1d500c0b81d40d20075030b41c030b0401a0340d0718100045c4c40c80707501d41300c150100101e41d10281c1e44428003000c2e605003c940a108001704032034004548000c103a0315038401050074142e0a60703a040003084503003541042d1100034044030000581035088440030f440f0403a40005500786000307400306400c98a400c501000c0d0184010450b85003800258100e05a401c40c0c0040f50301c03915410060741407008052944030b6010000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 646004559 1250 646003309 646003321
    0x62d061d270a0c030b041401090c021c02060604050105011d0f13020f0c0c0406151407080d0f060602030c2a0303160507051c0602070507080601170c0f0a1517 69
    0x1d4888542c5076604c0c2c400744410741404003000125400f0424512402080300010710104c140d503401750f0003401c032500485a0381c40741c04a140175000d00070a503043c01644a10100140c2e07007042c0c001c090040c4400c0c00e200c40c1c001907112040540d1340c00400c400740a5000443c2d04442036032826103400181c40d1804045603510458803525a160340300b20203111203403090359525009420503100b003008855010a003000403044441e01102c030a00d0f4000403403450741041c000c0d41d01040300710000701903061307030818001049800f2078854419100a03a11010540d001409400c11320700d408118082c81c0c070340c141a00340820f54075040c04580c1c1403054116540612000c5416024036406894100d9864000d038100c45003180e9520410100c0d01090207050160203171600340000142d0140c02400d01107200d881a01c0d010f50310b601c00b8a141c01800d0b4800341007078104c17404180c407150b024004400d05d6a0280c078100400220380010940360086841a00d0b400303028a403141f10800d2281405060b9052003010468141c1444c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 646005809 1250 646004559 646004561
    0x506030a06020408010f2702150906040603050603061f0b070302100207051f0b031b0f0409030e010f020f03031303051e0318060f0a02030901062d061d270a 68
    0x2250090071401d1510003184030200e81445941f4162651030004110030466509201c400c014500140070014014052182540e9034900580045e101550780000d9600d000404c0529212001d49000c081c8401c0841d1080703810751020240050303803404074115a8402d400d00d4201e15001e11035003031107100c0f840031410300b00b0040082202d00c2464407200d05464550324035100d04049039080542d481c0c0c59030261070054810300f401112b414010500401a01c0031803409004182520a00c4c00100c0c002a441146e1021941c1c0000e1002207140780c0e07100500d02000c00116941e643d03c40600312100310749034078203900101485001100c0d0185034001e8908403004103024a5070040d0000d071182814a01d020308070601c2c0080001300b45102d4968410210080e03240c18003034070001e600140c0309440b155203c0501140000094030502000c80d2740419034405c8003000c04200a005100e50088010083c101c4240d840052a029500d8550f007412110b8011610050f04d0120942000d00440e0340703141c1002040100c0d0180b2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 646007059 1250 646005809 646005821
    0xd0506060306180d080414061303021c0c0f0204110d0228050304111912150606020a17091c1103070f1a0708130303170c0d0506030a0602040801 63
    0x1007581100c1c0c8640b41c0070900e003000702c8070300f4062000d503000000c0c8540003885000f140303421038014140f055483c141c001c80642000000c4908110442c4112141810154100212030228003c0242c4805410450b040100f08150009010b410500701070901015540c40c0c3e440900c2103100d62442c00c3d603c07401c41454201a400248216840601691a0300348014281c2030707a04038070b40c096984605d50741c0d4030390f0b8100e000c107040a001c0d0340281cbe8412065840448110142c0040c06070900350000c02200c5140002c008020800e115205034186042001040e030005070000202d503010000180303031a12500c0c06d21030340c0508040e6943c4196034603014a00f0f0300540da010f05000c0c2c084d00400031492006018569501d00d14400c1d91280501d24104021802c0c030348500d030300c0f44c001c4d08003014a0f0040c40d449201250700400c0780c480c88041038103020810190030880313105403504150303014203061602c550f001050303001d40c1c0d8444509a0300c1d6000100d03544d40501024044aa221004540300c03619200264000c0803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 646008309 1250 646007059 646007071
    0x320030a180b1f0e13150c031a040216030804050f060c030115030e0607030207050c09070302040e01080706020607030f15080609070506130918172106010c200d0506 72
    0x2035204000c0780392200051100e4140c82c506003540d10a174440c90101050a520750b4019603000300310411402104140d40201350100515a401248543e24103010000f55654202d10520882c81001100c2843c180d52030384c2d81c800e81d01418400003955441c1800c03414114502070051440c041c810401141c0a00c12010314141d85a5030710b811000084014182e0840710002c00da003456510000c0002c18151003500203041c0303188100151005130410070302003401d2000c11b95076078001c80d40228040c40308207240183c0c0790040c50150000c0c0611854140060b4071110080c00c0d003020035450301c0d20701740c01c10215084002d40301800082c0d20703000b90b9501461901c42109581420003405a060002114078001c02901c6d158030840010048061415011000614080c01c0440b09282c00c25400d0300071034540d41e0400081d04030a01000d0780e45001c21086107030070195800d55161600d41c0030030300030203076403050011441643c40700140d500411080034020854111012441d4231081c1586044104217010071a980a10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 646009559 1250 646008309 646008331
    0x10051e1311161a18070e0a1401080a0512033c07110d0f0e2b03020a050105010f0e0a0b1201020a03090204060803030c03070513050d030e0108070320030a180b 69
    0x6101c5803400c94141c3c04090040c481c2e50b01040c021b00050b031200031002e41140b12a0400100c038150035a03d071071400004d86c0000c80e1030700001c20003c203000d024007041040301c2403903000d1440d620b0691550720741e42e030800c9490242c465401e078201000411682002e000030383c1e000b121055505d8021401064401c8030403060509020340c40e20725110300d0007248440e65400031903e6200781158074206010303050086070781100a03621641e042d002201d00245145202c98000e6004d00040f21a50528900b51a01a40005405c50411404200b250b0a10031242d401c01c11100001c20380100a800081d0004001076130200d45500c00103450303d2035500340d40710401482c400e88080c4000c0303075075081c03450310303804210b400d8000003034100000b5030b6262040c4000c0c10003805480100e00307050386031004030f6038800b00c0440490102e0908104000c0395078000101d10760043d80c81c030b403c5c0250321404000c034160320040716854001400110201710b40103440c1d08100c0786109200c40c0060020094100076449407015900c0140b61 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 646010809 1250 646009559 646009561
    0xc1404060803040501210b0a060c140706080703090609020a14090c090f09070c0f06050109140405030a0f0e130c1103070506151810051e1311161a 64
    0x300c0350100030b580813550140c4450b0040c0f80c1c40c03552482100d860211a11600b596040028290368071005150b02504042d56038544880951800e82c100014284512041c0d41c40000304000156000e9401d60380140c40345008160051b50b841c104028161b4840002d40c401804c40c000b207001c1701070f030142d5011110200e070640b19580713801851241ca03115100f0115001081d11449000905002400c10303009104e0340782c90800b08040382c4800c3c407071159800e000c40700582c0341c100403c4118400d0064150a081d895178042071030415580c0d543c0c0c3c0c2e216098a0b0b40900108410390103469020b005000c1d0101da014119204146d802c0c04d40d88003d00903000710101040b070001c3d10024030000041a178824981c0f040060000d80c440e401c807620003074140005580d2200b143d02c1500c00303d100e041c058900400e110304820380c00364100002c0cc4422140034880300e24005a8000e400125540c48004904007814010009407410a04070080040d215907840c034105840c3c0440c1d040c00f008241d669038a800c0d0b00c1c400c020300f0781e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 646012059 1250 646010809 646010819
    0xf020709050112021210050c0304200d03030e0f06010f091404081804020f0a080a0c021219110714190509271e060702030a0203041203030204030c140406 67
    0x21920207004451420149400c80801810040580c0c0d205d40c0645040342c408003800c0031400c081d035000b198880c2c03030614080305000800c00920602092041100301c3d401d030003903000c00801d120a2111074003404054680e028068070145c280103041100407850250703405503841d0420352800b025a44240800240f0b88800c2d4625a11500484c9010740c0d0302c209450320708080c0500c482a4001080411a1700690070401d00845558240081000000300e0f1103411191400617800d00864196860403015504102e908035040c8161408503001e24081c0380080780030010150003110f10300a07920300081140310305200454411002a4942d10030001191800ca19a13280601308103000340601c141a000701411380030825044000400c0c07080016140c0c00146c0d00154003c20614102d4800c042c02c43d40d10b600390300288507003824024180d2051850004514080404a009540703215030700c1800b50325007a0030605000c2604c25012640115009241101001c2d15250b8130b00e03044484144d80c40c400e620300704000070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 646013309 1250 646012059 646012061
    0x9050a0b0c03041a131715090a03120e06190506060a0c0206030406091713170303042301020315010338040e0613050f010b09010510021c0f020709 64
    0x8440820207002d94181460b00030350701900301d482c6440d01c80122041c0040301c03000040c14200c0005086500c42d5046ea56080c0f0304450400640e40350141140d0024010000e00180014505003c2903161400180740002e04000700e00502c0c044622654074000d02c03050081420041d10580c0c0a816280d10801407900d482c41041000e100305032a07600070414043c01100035113403040265602600804c03011503c50442c0d52294200a4100c02031a0128404150544a000e0f60a003000c050900c89049030083c19070446d1036035480c000100000d001180da41003070720801050032501e00b41802071400035500ca08140ba98049001c02d02d9203502e00081c60b0808071501030038010f10490303d803450311290421410b2080740e07480000341181c8410350415154804445c4040c008c1001600c0b802101d810682c2040e1a4900749040c1500000c11916681c1080c0d06a8140da03a0703061400c4c1110821919404c42f140c41442c188d062907920541d40507106500e200003140e603a00510508450b8289600703a07000c5c1c1e500c0e205044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 646014559 1250 646013309 646013317
    0x605040510090c0b0c1903091e120f02011202070c03030f1b0b1f1418010e011809140a0326130f0c03080d0506090108030a12180309050a0b 61
    0x64441c2d80040700130441d8500c200001c1c00304007021002c0e210640160020558038a4030300c2002c40001d41d607041c0c10481900c000300e0704c0d681c40824661100c60b891400c4056144500c000c0c0000d0720a114561061045a01510784582c1d501c50030081503480710b229080014003002c0f50f210a03000300d210800a4080584a000c800072140d50105c0a00c02c0e142894813410304c000c5000b0005036082402d4100303003801080c0c101d0904020915085225509480b440500031920a040303082e903030740c1d11b6500c018001e42c0c500740503107030544403422040f9844200070940000a07100780d410107802e41d90391052000e010a00411101491806501c0f2052042d101341a40750850030f06242c02056200030201085e14100740d8803052015034040c1403600e40343c005030388038007a0403034140d8402c588925000480d40d196941c00d00520744c0c4940704a4124000e50b140c041596168070074800d41d4020042241e200600c4000e0980c09800d091418803205508012942b4000d40901105d0090a11540780410000b5803480500308907 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 646015809 1250 646014559 646014563
    0x1b05031504110108390408100e0127020609130b040b0f0a030204090f02032b02070b070201030f140a020a1101020c070605070f2f0415120c12060504051009 68
    0x1000041620303410b10110200d1112141e00c02081c145d216016440d0300e90046d101418600002d00b017896040b011100c121070041481022607410f210510001050a441d440d003a042060420300010f84603100184641c807841035017950200000d03119a48460507584180c0c040706041e0740070003a1281910810203200f0801200c03075400300f1000814001820130344c200400c1d0300d1040c40b006110000c90760020381800462604090112840504600b0030711602903051489107050029160040c00e14201c1901c510030000041d05042e12606801740f080602e41c040704070307a80c250010030030900b4041c100c28060760004400400040b801d40185c1300c444410710803914500308200051034114503020050340c558000d0070007690030070590841c2401003442c0f00aa030407000e210707000084d003441d6422120403011002d50f103640e004501e00606038006100903200d000941b801440e004c031085e0114034000711081001d400c240c1041c401d41c13075201d040003401c0d049140143d1065080c1c1d401d6010640411040310030b06140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 646017059 1250 646015809 646015831
    0x2150d0f0f05390910080f010609080303070509061b0f0c090f0f04031209030e0a1203020c0f0a0f1e0b030403140a091203020c01081f031b05031504110108 68
    0x40d2240c103055260500701c3e81c43c81401041c0c1410404e10010701c181d4100000074020030381030020010003a203150b80f102c0c050031407814450f180340d041441e0203a0300d00004200301c00f0300a001607a503945580701410764076101d842c654418110700d042424980c4808030f41c0c159620501c0307411850811441d103100014840c07240089240020f135502c0f034002880b003501400035001c0c0601c1c14035080c00d16419000703005905000344c48111844001e4424440c0307264840d40404030600b1095020000680e000c281000c481500310360036402c00d845c0c04c000902d400d01c5540041a00060712400280b8030880c4c80030400d01e024280040b0603c42d549030404001444225001000200a10891024514000054968032190f0319201010b142c031280096058000300c0d5050b409030f48111040c081560344510140d0340144001c04503030603201c11f8412100c140f00399010082419584181015160342c40710f1201000700701c010201c4000c070640c81d84062090788103950076580c40070145c0207120f8950040c0c410500880320802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 646018309 1250 646017059 646017121
    0x50a0308070306180f09020a03050a0c090209060a031512061b05160b070519080901150501020d1101021e030403020712120e030727060e04030c02150d0f0f05 69
    0x44084002c100f6404542480c0b59121b00c4c400158440e0821003020354411070042c0f140640c6420038414118165000c05840b6004120014564503150160785440115080201b214001d0051400080da0584c101d1203d0b41d041000d21018011140c00c40e003500c0b106031182186011014508039290b10400e101c01c0c142d0b0500c10810b50000d2544134103280d0080461910078201318801e448442035002d007142c182c00250070351082c00300e44c0c2c1081c030601c0f415034281d0b540c41034414540b000107034655000c0303d20ba000303002d080f0150300000d447c03e40480f180f4041104050780301f4100062001d0298000740c2e0b040d4010f00c1003501c080342514502c001c0810280c0c1041403649411101302c8120b51404074160425010702900c4000030300c019100030304a090502185c0b441c0030800c2106910022611180d01114822650304180004290010981007005806544894001d981c0c0d0003c00f15a20541c030030200e00038030b00108000010303010b9000c24108044448140082c1d12180704801440da0030991030004601215 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 646019559 1250 646018309 646018349
    0x717011232010908071e1101030c0c06020c0f0d0201060e151908071809020a060318140d0815130b040608011409070609180f110304050a0308070306 65
    0x94010350390001c90300555107030381d5150120500703455006200f2a40d490b40440c51070208411030344200069440360076071030307180710150301c5840c0d07828003175178a46050580d2080c5540002e44250325030700d95140c00103002e42d40c030b0302800c410a5441d81500901003481c01807400c0c22120318810301400b000c41e80c10004546064451108904040041002142e80711100001d40c1240c801c5030523101c40101848400744c45551300d0100360f507100d107a0403440241c1c2c4918000400c801030f52042003c0007660b109207070000c0e00350081c02c9801013034140c007030001d0f000328000f1510290780b6000040306c441c045960f590b0407029881d91085241070ba1120404542c1c000c918541054044080e507000d1400c10400030408610340396134140f42402c540301c0d6041d80b0702e9103070b0807020090182403c00800c0001c014628009403480e00d4006030703400f8081120f403e50a4180ca841102d6610b042c00d41001440d403550394402681c0307041916246550b283c801380103d01240c00c0720001030f0158001c3c810710045500c000c12900c0c00803011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 646020809 1250 646019559 646019603
    0x303070c03140412060f0e030901080c1312060203010602010f0612110301060b040b0415081b030402040f060905060a0e09120c030c06100603061208040b070c0302040507170112 77
    0x90700d4030000c101d0501c40040e103d0551340c400c21031640a25000500794050041c00703020b440c4034070003201c100d620820210038240d81c0301c840a40e105c1c002d007442644079007031504031403c0c1e10410340c400e10070400401901d40a03c00303250f0045040341d849400804c8910f40c0d03910681c050f00c03294410401140040d0f094000400d00d02421078102d808004c000040d03007919000c3d070081941054000c6508003001107014401c45098a200d420404002e0410001c9481c04410403001150382d20303410001e141d8088003041c2151640c0d008240581031b810420311009450342c44042c01070100712a102d100c0c0149600c0041d50798035011105001d01107000103802811100c0e02c5c241215400707120403010501c000c10200820403414400705020b095107050500d2901d2500c400201990f820b604002c251903040d031828000584d02c44102ca0071101c00d04000d940320140c2d410303c00d00b003010541c0040d401c14188010040c900fa03000c0f0700b426070000d81c1d403400c10306039817200c0d42c4000e40111900001d1030300c1d10928a00079a075030305c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 646022059 1250 646020809 646020827
    0xb0a0e0a05070c12030c0e0306220314040e0403030b0f030607110a0c0b0909090f030415110d05040f12021305060d0f050d0e24090d020406080a0c080303070c03 70
    0x1542c140700340c5101260303a804040e28005100c01300080d5803089020074583c2d02075543c13100c03a00210b0042601c0d0802c2d241f20600b030f204100e03030b040e03404138107140410400d401141c0d4055030364020580a522241d5403040045031240494085000a141c034400c82118a05403101150580300075009000d180e40c4d1500550b6aa600c206407c5034621441204800045100781d45c0400303080520715150f210b411450603c50009800340100c00b0503000115080c0da00c03100081078804407004494001c031182035100007541c0c1c22510301c0071407060b400383c803148240458201c4020000c0b00c40005480d0303080c0e07a40d20703090682e81034600002503014000030100300c14083d40d5000a82c0018006007550450781480c1d440444400709c880c1d0403640f03500044441003500360018558140f0f14000e5801825203113000310b126009002d80e8103d09032003040030500c0760180e00c03480c0c1c0c0b4150595019000308a92615003c0c8070b540d80c60760002c00c4507229558000410100800700540b0700410f515180c0c80301e40962a90151600c41d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 646023309 1250 646022059 646022071
    0x10b03070905030a050109050d020a05060609180312070f020c2409100e0906090403080714090a27090b13260a09050a0639030504090b0a0e0a05 63
    0x410304001040c0d43e076042c001111032522820001400807101e207041400c007007160070040c081d50800d0130440b02140000ca40d46a100e1003c9403507160a41c1d80c041141d80f151b0781c00161000301d01c000f0544103500142800d90718018151901e945e00803140490040303aa0706100680303140c0104599001d800300001c0c0f1503560035520100a000e5040c00c518a0103e4540c1d06118002c100084048000c4103c070306040100c25003007181510700304241c2c505614050030840d806040030302000321140c94041c0c0c3e130201e0030680e424800000c1c00703200c02e550340f02c00d0541e100c1840a00060301d02c1041e00340c144940304034411008415880282c2d0342d80307030703950010b444020a600b00054464140031a0500c00015034410384000c1001d0304400030341c80b0159000d0081c44174040e50440d900900b44c8003000d011b0395400c0141c1c1c5d40300200030040b0300d0183d60600d0341010034405071071501c0004480013081800305500280504161644202d08110502c03005080127840b000502c101c5800303075460000f00b05486d5103901f000ba8404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 646024559 1250 646023309 646023317
    0xc0302070f14240c030301090f09030503130c0806010609051905090105060c030405041416090302010e04020d060b030106030c120606170622020301080705120d032307020102041502030a08010b0307 86
    0x1440c0311040f4085510503508180c02d80c000000620400c096846950003409080c0c204005860039540d010f01a8403028000d02007490030031540200308044100740f41d001c0c03d582c100b500c2c3d480d69190005808880c0500a50788107807500305142416542640d1144101c91004040300c0850b468a000d001b0641d010013a545214002048042143e4030749016141030820780d80359507813035440c043d001d08240c540304251483c200300f40c403001000903030b0744021803032568081203a00681d50a64000c8240080030340d039000d1524610701200008500d80c041e4416005ca8110f40c0b2000c01b202c0d815607500f4121021401044041002240b508a4400d20681c000d035105802601509030440c2042e220804821050021418181c00100601024005008034001010140c07a600025080000c0e002d840b2010310b4a420105691214141c90000d910707800e8250200314002e00003001d05160f20000c0c084d41c801e00500c02c2070209460103034400da10020454885000c240d41e42459a42803000100c019480039011000f00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 646025809 1250 646024559 646024609
    0x60127020307050d060509060f0103112502010908061003230a200105070f06020901020c1026090a061a120304030c12120e0415060c0302070f14 63
    0x15010600c01140104555107076151502103010310041a90b5464110301d0050a00400703020180c5c86000c04180d003070b00c0908002c510056421150640b03401080740c1a0b0b81a000712801100020990003c1c60a250003030342d4450110740c980010395910720701a41c103121034240d85c1d04100046213100b080c2080988040c031881001c614040000c9161006000b015103140b0300780c6210050a02504040149801c02805d000d81400d03c9c42e16010525544090701070300140d000203005259a10a02c40f0403581c4500405d8416039801c1c2140007480c406115040e00013401003210241000d0030700d00e00c034611480f00100244035181d0740daaa40346c090807520000700c4050301142022980356450181c20210020080015902c9524505000c0d40700442580409030b400348030601e51021030510041030721100e0781c504044024403007820104d8014044003580e103040b000790000100b000796110f640410f46600a6003116046078070340c6040800e00440f48a2075508542a1510003d030f03003098807514081218010f008660 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 646027059 1250 646025809 646025879
    0x30305090f040911040509120a180305010606050c060109090b160908101505040c0215040c03020409080403020f030f0c100e0d06020a0906020114040201050f13090204150309050601 79
    0x1a215030003c00c4a02004400c869405410648584c0e6031182c45c010003400340c01100b4400c078025200da034a030318040042075010900c2008200b03010b00001e5034000e000300b001c0c1ea030342c640c018016048194001c545000f000c0c00065a4442801042c5a80c2e0b0172100c51029a211500ac0d03000310100c0c11040e0080c0030f11100300050b007044c18003802e400c04070b12020108003010480000910301000ba04020b00c200c0c5041082c070074442c1e00050000e81000d80c401d41c3c038095100c80c2070071000c400043e0b0009501070f04050742542082941c00140044910940300607c14100d40010541c507180250f10b00301031a80910404034061401082e0800c2d00c0301581004c40c815030078000491040c0c3c0c0c8441d010340e007240d0000360345805154080031314030003010184001c0203450401038980c84254009000a4100240441c00707500c1d44100b0700403070301c07131000c0c0090040c4c07060340c0c4000542c0603401511031403100918014009100c0740c081c0c0078040400d13602038044c2c1245d0b802c12804008800a504080f071054202c4665208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 646028309 1250 646027059 646027061
    0xe1e150d0e0a03020c03010b0d0812100b0c0106050111060712180501090c061e050403110a09090c0806011205060a2703020708071a0d0c1e03091502040609030305090f04 74
    0x88070f02a902601c6941c8501c014542580c2241441c580507801c01481600410242d0064a010203403601c0416450744940c00038000d0b03070788070350000c4103041c100049036941060158004001c581007a25110100d0405081b9142c82c2d00044803010003003140c02d03648004003d00c507406110300260455041840600e04d456107421144071030000c55a04c41c044c030042c4861500400344a20602a80041c003481003c000300041c03843c012840b000b0448465003091200340d0f91410081070192400d0b540c104640c103035505160324903410328840c02c07801f405203200106880100c1907880c204950800d004004030b0b140e1071840001071282440300104036081070306c0c05001030303068404011140d01a1340140201410850220300b00407880d0701080d00111410b14180d083d11001c81170302c0302c0390340c0e082c40068000348141090310034000c0d20042c010044400398a00d000c0607010761200550a00807502c6030183c12981003064203c1c45035000300c01c0800c3d9491000c20000340300380c4c0140140e20f8003410f080350114079440410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 646029559 1250 646028309 646028323
    0x70b0a09030b06090c070f030e0d030804110604080d050f13080f0607020d1e020a21020705030d17040809030d0903150510050105070317070e1e150d0e 66
    0x2000068508a0030000d01080000640d0400b8044445500303500385410072045501c100f00f0020074850702650b500003818002d00703807035540c000040d040520b44081898010045401103800316121346000310300380e01c0781c02c114080e101a1220000241089910b102082e00ca41c0c101051070780b00382d80c0c100903482e0120003034a000001040150005c10070641098581428000003c0000046502c441821601c0f503031700407141c00c031141c0221007a100c1441c1c100e03422410700044080151224404040c000b22840e0b03031100340c40000c08940e0a07100c45640b1a0101034485840b450b440c0d00090300c400581040d1404c4040313141e04984034401c885d01d00444480480e080400140d840c40101700100c0342000ce0211026580d01c441200800400c118905180810f00300001802180d0400c41c000c1500d00c05c00d070207501c0c1c48041d000c3c3c4071942e90640c07400303590042040094030821406441c2543c07140c20380c841a402c00c0308980b0f00c01001c1c1d017440303401d1702c101d0125a000b01c089554034545403903a84060200a0100f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 646030809 1250 646029559 646029577
    0x503010506221710050f04060504080d240b090a172b260109050a0b1206100f03050601050105031012030806090912030609060402071a010f061b060905070b 68
    0x41d201c614407994509040100011030188041d082c0410851b200a02250390785c0d0040e400400040c4a84403401d00801c14010343c00e00610851522920000360300308040c0c9851030070700e0100269020b41c0c030760308400344c01d020321600c0c590050007414051103541d8005889044401c1e80104881c205071014800c1c500a142d9081d810300519500070b14001e6240c1d00444e001040c0191a480303105502e0155120a5004014401d2024090340d030000f0400f021840c2c2c2058800c118010000001030224070408c64807440e0039500c03102098501800003862081410000f02241d80240291010380e20740320054910b40e000030002c0c1c64003810031002007001d954003200d0340d0710180213940d85002480c2000c20f11043c0302c0c010b0080f02660b40a0081c0110411400d01103e82c8200213407140220341e180c80001ca0003a01658500424040308485006401c8a080e680a4100c071040809082d2031a52042d0640e960060f44216000c6110031510a001042c0c075508200c0015114804a41040781d541100e2403c0da001150703a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 646032059 1250 646030809 646030829
    0xc020c011e230a030b010815090903090a0905060418080d050705070221120c030423030607020a030806061206010e0a091d1002040e040314041206020703020f0706050301050622 77
    0x3c2258455890f10855442c03107005c0c00c1660103410301c65002100f00410b0a03940307200d5000d04c4000342c1d800b0014004d03102115405001118650380760b41c5642c0250408a600c94011071510420200d482d009100380c03030245800c0039920345090303049601d090280ca0000d1000d400e00000b000481c00680f104600c0146c42654210300d00801044e2481540c100f103101c10704151107000603c1540e5415402000b1070b806c85e4414180d0190b070101542d491102200201d0744140e160284608005820b6004030303d4070005c500c81d03a42e401d01541d680c010009a400740d01c0c071507840380c1010070000301c065000c2c0d80042c02c00d0000400b469819540c41d1840400d44200c44c55900415500c19074107400d0440402552140c0e00800d04294103190802803801e4903204d005001408014503103e000d20040b01c44406c680250a9041c0a00d45025490404102030b501c444c1e02107005100e02c50700308034190404904079080d18410b6849034a0f5074078003030422040ea000640c04c042400d5000d01d01c0005080710346981c50082104010b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 646033309 1250 646032059 646032067
    0x621091712070c080a1805130e150405061b16060606090e09060c030403050f03090d0e04050f010306050709081e150c070f060f0c080a0c020c011e23 65
    0x14260703414010b40002d050100c3d070700790034000400300c0040d607580342d80c907180c2540c40950390807038901854026070002e600821080c80710944a1107681240803121150411610340f420b100d40624182e500464019045030080400b04200300d80001400d030007030b080c906c6481d0400341c45c0e545400443c2c00b2044c080320725030b544c1e581c104600e6800800383c0c1c000b0072034469000d100c2c0c90200042034803103030002c100c440301007800000501014041c5082d210680442c81040d81c0328038003040c0003076a070b05080d40c048002c01c41c0008590701901d401e00400d44509070000001042d6444e50756414081c2c00040c0c511020310880e2000880d2200d01008484c000354416964030102c6442d44c3d4509040454651407005605209070800100c210000221800642e02ca001581d00f080c150910310018805005103056040c20504c0d10041c2d554810b1115010703200d80c200c200400502000705980c0c4101d80005580422104488060344180181407403501304418107003429080c154445a5040409202e41094040030110b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 646034559 1250 646033309 646033327
    0x3021c050f03130816051e1e0a05030a050904051003030f08061f02061e01060f0f20060405010b1c15020f030c1801030b150307180b040302041506210917 67
    0x3003810080201c41c3c801f6101ca600006009480c1c5450350012080320441072012070300d1103030400c000c40100ea08441541e40315002d80f00000e20350703489036042502c40c07824440441c0980d083c451041c0e040383d61640f64004540b02c450740940744c0c0c520091100394410301c120170b4000101e88105034481d801106502805191415640340c24014072200300c40d9003011000c00061120b80c4e0403c40f0248900c40600f05505070740c03200402221206050100c100c032000c400f01300d006031003200141b00c0340a107105030b0090045060740d01c18414100f14864586440302c2c202d00301000825190032419045c00415400585423401c0782502890a6000740c070f090131213501c00680ac2441903424100c00703480036424a42480060710120000309a0950280b1203083e204000022808450003141d60102005490180040442e038510543c2d90315085031100b43d00450405a1490301034100d0076408043d50b0f0642c449450200e140503440200114131941a68120707596100d200c0407694008907290f004008881082c3e680d0000f03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 646035809 1250 646034559 646034563
    0x2003120903070b0c0d0c1104140f0f07020d03110c060708040c09050c03010b0a0c02030f0303070f08010b03070507081201030606091a031b0f0a0305010903021c050f0313081605 77
    0x942c44003124030300c1400121040c20010440300315080103072425040c0d20a00d424800004a544060141d0127451f2a021800480b0f0a09441d031142c070300000b21130002da03200300491035421012030b030303132001078001000f003500c80ca010350310103980303114070030360b41d0342070100c651962071501d54240c404c0300110f203040c1c0411040280e170f441000b01800d00500f05001505110440c412180410702600001007400300301e0b0010b09110300603828425030000c04175958640801c45403600d1368000e4501e00c0000700212080c0500c14003440d9164121602007007a1440c0d075071100300c1120244c2004008842d907507820490b000b14814641e8055002c0c0d406510000703881841e00c103c10301121214002d803983c0040940d10321900d80d4002c0b5406284000c80484880d0000008001909031501c5c00c20981d0b000e02d9a003404020b1090560042a0244c03003502112441c0720f090403400c4200010507082d90014004000304dc00402c02c060140d50890107441d60700a00405a81d1120f00d550011142c1403019411038070060184142 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 646037059 1250 646035809 646035823
    0xe060901050c040b030604021e0706090605160c110619031a0f09040f0c05041107020a0e0606030117010f060b190302090d06151512060b090108042003120903 69
    0x88000c042c1e00d85894090314801c10300008110303510469002c1440000c00d50b880424121928a40c40d4444d520314041c030f850401840420410b44503503180c000015101020844042112200d64542803801c01065a52000003101a20001c0d0040c2041c8011400c00f004566a140c82480503100452202481e03411592411740000d012442404441c00080c0140c0360b0310b03469908690011544181c486050821103040ba103c3c4d80043d400ca86050a46641d2070400000351807014800c95030038414a40c0e070018000101c40584015078420000c1004010305207240c94400e05800000001003110400408400200c50041e0b000b042c0f4002c0008610743d019146010080180c12141800c504101c05180450049030070094024142941d610401d41302e91801c03000300c1b0007004548160405c00b16030020040c41600c05c24040d900950030a80c000c40c2c04048002519803c29042e90394089d1565a074607410981e04010a21861800c3e500703940c00415107041c4494240e0186030100c85030341c0d94032030302454a0f00807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 646038309 1250 646037059 646037071
    0x506090609062b06030804060e012001091412030f150d0b06041409031b01060305030301260d0e0d110a090c020d03090f081c020301030506190207020f09090f010e06090105 75
    0x11401350103100003007481c415103040e55042d203810309441c03401e40c3c01a190801c81800c3e030720064600040341f41d82040d054100b400c06a1003500481c40200464800d250388881c20400483c0c200000d10000e000c81d20b000100a5221105450310700b80904144041100009100c4040d1800490113003004030600300307401440b8140b89050f88020003031401e0241503407207014030200882d8001090b050075540410940000c805190400152a602e503924292810f001c19003d4582c0e08403100c2c9200b14800c5000419488885c40300b0b40c8944445904000420230300c031100b4002101c0111100716607410710384400103030030f0242001c094005425407410034003030701d4615000129400c03d41848e10400004072106401c2a00d01d51004c5201c1c6c84000c1d80303542081d68008502030040310340c80480000140000040e0301406035818506103035040c043e680c0054183e101d07031400070350004981c840650442c1403c7c40805e0b0302000c04801d90f40d190044090150940340002031001e00c66008109000d08030400780300e000c0c0c001b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 646039559 1250 646038309 646038311
    0xc0b04062f0d050d020c120901032405010c02130207030e0102061317030414060c0d0501141c060204080f030306040c18090b0303090d03030207050c0a0b040506090609062b 75
    0x54141c100c81580c0b2064401c0320402c0000110f041282c0050035019103251110b140140c42140302c00d51008620f6130408900c60f400039041c00c1c0540411140f800c40300d01c449400d000c5268011341803200540b101da4038014101d1704003070b41c5403140b407030002c051001d00301c0c3e9442540c41520b1120084002441e08002800da1a0b841c00c403a007510f030006007501a504040303d002c519050320baa5079405c15a4401024071490f116030300400b07080004d24075a01004140310b50780c8004c03c10613641c85034a0710317061610820011740c001c107007801088450300b08800c060302014490f14000d86407070380300d0740b030035003042034103e50006190b00210610405140c2400f0b070f0450b40d91503107002010459004140c1d5080c103168031036914400d81c0c43c001c80c0c009880a00848031954006030140c12425040d25000700254000481680d0b1406084108072892415600c010210303244075001da82480d0500c13041050960080040d542d10031030400c4084034179160b1501400740c1d0704519200c3da12203588400c1607071801c03a8100c0c50021072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 646040809 1250 646039559 646039637
    0x9091122061205130c03080307020708011e0b0d051609060e040b0606161a190510091122150c0519050a0c170d1e08040c0b0406 56
    0x550b0700c42000a04400500760208654550b01d005020403201c1d94000703840019803003004810b00440d1001940629001d03802ca03041c1c1665500701ca400c0741e8018000c00c01d00b00041c080f0110050081e04040c00d1002d0040c9a1b82240c038040e9611840e190841c0400e540c070350081d0303000304003601040c81800010110800d406007030780380507964140640001041a44914004151061405010560403042e00c1d4040845070759007210507070408040c10100d03460601e04404e00501148072403203000d55409100f060028203c0365041c89010005070500c220f0402c040380090012000c3c17440c8001e1820b002c0712114500c55525810f05a01203003846003000e05c0000c1c0950440c500c40003c10018102262004142e4080683c2070b09250040c00d00000d40343c06014403224640c003007038403c01003120b181908022001c4440d0040542c1003079501c030b080b468210303d41e1804041d19000e030364043d1150390b42c010b104011003200741c1d49440e1140000c0c0c0154110000050440b02801000c1e18000300c0c001460354091448140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 646042059 1250 646040809 646040819
    0x150301020f09090907030c06020a02090106030b090c030a11040b07120801030807080703050f07050c0301060f0e01031104060f061e080126010e0a03020a02090c0a1205060109091122 79
    0x10381c071542d00c8180c06281d240c1c00203003101c102400a800034551021311100703859070790035000395a1000c452069228458840c00051241e000348a80005078070007814000c1240e9480ca6481e1090b0002420205640d8a4810314014241164020400340c503950321a16201d464078100000c200010f1040302c01801600700040c00410122015140f8443d40122003035628410742c503044038180155800d0810030400441d0120400501141041620f10183c000700510742e03841e405050424903901c107101d194800b80005002051458000d008280340240c00481c1c1b4655801003040c0c5090582d02c20400900040c1240030319040804c03511080ca03041c0c0c41d00d603071030b0350401000e102c0400442e031040d500403c4403401e0f40312030003013902f2103008a0b01c2082998485501400c02135124021390004074419555440007a000002120544400310441c1d5141081217840d01c031002c000b003034060152810b100805200050b07429682c041c2c0807005100303810207621829400300d04000380a092508444084a0680c1402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 646043165 1106 646042059 646042087
    0x90f06170901180b090c0d0f050c010c02061b01151d0606032725140f1003020708130f060212031522060e15030102 51
    0x240c0c41c1d03a4110300740d08803641550108000c000060110000c50300300c906040d408407510007122110150f40f00043c10030084004c04969040000c00f140040000501281d01c4041c02030801100c00301480e0b00141c2c280c014000d44d2448a10645181e80030024250800b2158161071143c0282c21512940104083d0020381100e03240380410001150860030300b01d088034402c424251042a4000070703034055580c0065015500e1821f845091701d0300404078110fa14401e6066807220304a412546000800003a01c1da10003012071084820712200c030030f40d488045511a07070000300e240c0141d6501c820300e807100090195842ca1400d40b1039100d4007080311460302c015001900d42503000c580b843c004805000d2503a1204a954080e2194428107a24260600301d100108403414036803c0d0301d40b0741c0000e4100045403480d42c0002c2941c1c0c040405d02070082400400c8d03541903403040c0e00940c0b5204400da1258 = true := by decide +kernel

theorem cover : BRFrame.Cov 645863309 646043165 := by
  have h0 := BRFrame.cov_init 645863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 645863309 ≤ n) (h2 : n < 646043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
