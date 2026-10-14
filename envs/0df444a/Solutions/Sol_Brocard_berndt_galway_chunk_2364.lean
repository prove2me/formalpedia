-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2364
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:29:12.126977+00:00
-- url     : https://prove2.me/submissions/64b0422b-3526-484d-a4f2-384ba9f8e556

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 425000000 ≤ n < 425179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 425001250 1250 425000000 425000033
    0x501060e130b1302040f050307080a0809120705092806030b010b070206040509010803030610050405060a0309110301050124081608060a0b04080a06050a05070c060e03070b010e0f0919 80
    0x4041c3c0c140c210290800c120b03806035100101181292109014502e02403040c0401070003114014000c1c129191a041c60511440601a12034031400c80008105034040c061600200b9005001e20514608401120241445c003250303441e04030311803000e418150115229038820340c0d400c04d2110341540e09102c0464102e5010b40400d0303a1003142444009803d540344c40519018001e00c03006161641417210034051000c40c1513040c0c07000c2c88804d00c01400f40d51104815260500154940071401160b04d04000c4048412032810a070194281000131402c00025008400b038a91b0040d0300c8186800151801c6884400603215401a6120101c01190607842001c00c01d400103401407604c03407040d0b55107460207250350140c0c0c088a000d4104110312801d201c0a8860b83c2c0c0c0c00200740303c0c188a80c0c6455800104503500d0000b0042c811643ca903180c040103502002921250b0742d2040420601c1d50b102d980c2040c0c036000441da07944441c00000001000354070081405503518401c010016114501da80da907051085038441c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 425002500 1250 425001250 425001259
    0xd021203070e0306040c061707140901091e080f120403021e030d0809010b090114090c160f0c120201051206010c0b1e060f0a0303050d1104060207090501060e130b 71
    0x610300303c1d542880b1903130160340b254520540d00ca2902501800710020207440d204256503031400c01002c03941205030040c00d0640c2600d099981e1030b080c401626460015000b181603829021414420f810300880a01c05981c280802c60700c51426103400641e4804a0890010200206020400050811410b4502c840310b481c65034801c01070000c40440d1508460740c0b60303800010029018040c05840030322407021120701c02d4402004070760500c10354201c0d8118240d21640110340050009107054105400e171f0300c501170118003032000700f0402d08028204290400060711040c818200008890390b1080030704601030b506840722400c1c080040c40f8a600d000c8020685070501012400f9000055036402c1d005205440e140c3d0f03540c0b001884102d13001d901200040c0711034060a030320f148400256413206800412030742c2c10b19295aa071036190242030060301e40c4181b0810841004200484c000c0c4c3c0100b000820342e006c0000c20805aa070340c40d0201d03030000a06e9001900700000d0310414240c0707440c540180d412000090b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 425003750 1250 425002500 425002517
    0x30905010b1906030f050105010804020d03030627050c0c060403050c01020412063e0a09030203030c0105041203050705070822031b05010e0f040903110607080105040606020d02120307 80
    0x41c0400c1c407511400c15000078801441205000081d050322440c1c41e42070282408204641c10300001802e0390340003400107849038030b000c0040000c161098108001030520343c404951455000302510700750000603241c540c03c843c14200010550b02811090b900e016456030024181038485840079180e61740075264522a13550200700124081ea82401c042c60003d1041400064040030b20101c0000880202030b5001c449148440e590244800302000710400141d4601340b5a0f2008050304c1940e02d01156440250180008034001c03425402c11f43c0700610840c0034043c00240000035090403021102d04440c48400314400b800f940012905400291040c3d4082c1c150920b01c4d25060061044061925801100c044841c2062140d82c42c4010464100a10003820302d401030b40759000c00601c21040000c2134a0240380d0f00c0720480185440303200340882030b0724a4404e07580320707041c556001003100710240030307180c05181002c000098251000501e01ca40020a6011340448044001d011104d984040c0c0f0b61010840803c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 425005000 1250 425003750 425003771
    0x203130f05041b2309120c0a060c0b040b0403110307120f02030702060702091e0702010204080706140a1d1c15020702031507050f07051b04020c0c0103090501 69
    0x18054040904128202015403034034020422080e15140490407070f10044407151048400e0b00325090031000c44551050603421018100c1103c150702450b6482607200c41040c0880740f000c00081003401c1d20042c01c2e1403014009880780c02c241c44500300e005008000a10800000c0d0101e19180c0d070702034105110740f8046000c0c3c162070400c0c0303185400c00c640544407550000242000c09400c505000352512440c00076500300010381d000100107006560010f40580050300000380c0c030000c01d1100f0130b0b500c9007507a90b054450503d580024000e400900a8002d5845601c0001c0380c542d0041c090424954032107039886203001d2821004942640c40310090350542c04d030343e010345c81e02652000741c42c61100d64128200c1d03140340190b007070944814081003034481c0300d18410003404015841c0420003620301e54203924211030b00d80b596007040fa114491080404840d03030002c00c51000f044804984d100032407071403400d03654841804070f0400c4224414014440e2555204031016a0254040c3d08462042c070b000e04000070310125038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 425006250 1250 425005000 425005027
    0xd0309020a170d020105090d020714060c03220803030412050c011e02070b0f0115050310120b06011205090d0e03070506041508070203070308040303021c09050c0120060103120203 78
    0x200c1c41201160004801d0b000504d60920031244d224410310020422885580c00282d15038070076025001010040ca00060559141c550444046107032900489580701c5461900045848034091840413429050b4800a000380707002003902e0085800c80300e00b081000c85480b0584441d4400340784607a81d9526145804001703e1a00b44007621301980c1d880260780c40c05d851621074000e100c02031000c0020080f104c0140112503480440418410003420b1003581d0f512108041d0200d43c0e015803103080d0381e401d07503001141086030740b40c5514010403082c2c88990b80c4561079030444042c1c86048510b01c14030713845031001c21040d512a22400039030101c040c0680c0c800d00e03100c6010900b25800741c0c2040e09012401d02d110141d256000840643c0241584080d500784081607a000341180d0001d0f0000d010160003007070801c1c0c90100031251504981e0301c20020070040c41149815921a181104200c2c04200d42e03240700300d01000803202c44060700b003818010f45074581c00d65494480400300c1c031450341e046200c180860343d5803080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 425007500 1250 425006250 425006279
    0x309050c0a0e0a0c02060f070f0504090c05040f141e0607020607050d17130308270a05061018050405191b0603230601030e01020f040306050c03090d0309020a 69
    0x3405a4406520300d0500f203003006564021100c0421940031404100215111200c076540041c1546003614a20a50020444440c0207540141800515108481050750380101c002c100703d441d0729118094603a500e401a07024805c1c080c80c0240c00400140c840605400c038420204000040144107904258443c0c0210b50217420155003100c041d4803a00c107c140c0e05401100e1a2046250008400e03810320b0480381711070901402c2d000c010b0502040e8004980c810000c8103981c418001c42403150000c04119400042e40d50810700020354650041301c021031450f0703034690f00b02010358040703410407010b0b090140f6045004001c0140143c541e4010300720700c0940c0450390802800e9407401140c110010828a44c0c01d40e111803d194401018185407081030035080c4034043c620306d04005048401c818035940e00c001078003d022106ca108007a9440000e0303134444050b4007406001071360b01840c4104200d81d621952144148001c0e69641c1180d4080d003c0ba24206200f1340108081a102800c000e04065903020540f23100c0c0b5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 425008750 1250 425007500 425007509
    0x1002010e010c0815041b351f0f17070314030d0c020d08070c0201020a061b110c0303120c0c060a0f0b031519110301061e020615010309050c0a 62
    0x2041503084c411001903640001404203402c8400b04a9000c01400c07207598181a80426070070702001c90903006228414010940740507001c1c0940070103d0783d203006251306061003110007001703107000420042012000c20840d80240c1d00711000b03031082e850611000f079103040325943e6a10300c248503600000c0001003080c6050750303005140b0001140c444900c1c8651805940030058010115400b074000c407003215a000d5034468200c06030b410310b009655041d000403401c1c04c00005000e003845040a54141215100400000b1800b909603120407400401c6940c682c1c840d070b20f046074658154018000b070858280ea403d00d040e0003d0200301310602c2e0805407019a82020300c2201c5803a5160fa899942c0c21000d529070080442441044001d056180d00c8110142200000588002031100d42c0d520170021500c4c8136840004034a40d18070395243c4035070b92144000d0003a24035560301c400c0780b1a6000740141c1e80d0b000099590007100c100428003483c6852800450040c140c0c0d001c01da503c4d05c02c0100000719611220203200140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 425010000 1250 425008750 425008757
    0x30d0204030c05010f03090201120203041104110301050307050a0f0b0a020a1a060411031b0d2315060304120305131a0a0e030c1e0c15030403030c09141002010e010c 72
    0x25143c0400900045040c80b40541032605000070302c1c0050f03a0112541a2501c21103000584944503801d00300f070000050505190054a85010303881030130481c1010b541255000c82c00c4842640c2c6034018042c01100c1481420000400d150701482103480010241034081c61501c11150903410984410307040c5045030340c220494640c0c4506000d9035003007500410900300c0d040e8422074a1030410b030030240720b0b00300750701024402c03a0b42c003052804007042550016510f0170a9042c07050020300e00b010704007401220a40b9100d400041041c1004090300707090040e40c0c803403500455010703210b00f00d50700c0980290000074918401d900c803c4440c400090a0031002e03161103100c00c0c0d0381c140302c2c1c03070000c1c8940119800945001a1903100b07100e008000100060a41d84001503d10055a0455010f542134a4401d042c000700741d00c11122004d070a40543d800c8051403203540240d400f8099850b00080507a5001481e0140a80c82c0100206004a9017801020150510001c0c03000044440c1003200c2d8908403091540d080002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 425011250 1250 425010000 425010023
    0x801060b090d11190f0509130303050a02040b040906090b010305131106090603190506030304050f040f0902040507050a0f0e09010506070201090e07051c0b01020706080a02041d0f090c0120030d020403 87
    0x20f0017284104081d103003d45504486080000d10f44d076251803410001000c058840001600011880d01a1001043c900458989554413804c5c5100601068040e18021601e042001c510300d6109014560040441c40c4003415200f009854000102c114500342c0c40d0014003c002c40031098036807000440c4246501400d80d0b0700b610000c0710074008e4640c0581401c2c072a074020f01c801d1042d9036400f100d040d10340c0001c43e000158211444241d00140c40403481c0a540989480c3c03c00000782e42160080010a11a0341c030403010a036100380c151640c2c54080c4900d81c00016050061206041031401050041d00504100e02c82c9551012840f0788840200e07840030026401148503040d6500d152081141901d210700e041c010f4003c1840000e50303860891048008009546011400e02e880760b038100c90140002c6050a072281c400700b0b00c4529084015034030301001400110014081100200f442590742d40f05a40704505143c0c400807a503524502c000400d94a07001c200551062440c207440280019403050110060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 425012500 1250 425011250 425011259
    0x10612030e010f11120c010908191205010b1611090406200403152f09090f163921080a0f0204091e060801060b090d1119 53
    0x90f03544914000b400b4446031060804001c2c03400300e00382414010f90002a615820310194890151866600203451540005162a4991104034a180c02001c942c0c95050f0250034203581401283c0e0b091044040c004d40c240064402840000344401c5001e0140301c540b100c444045002540603e81503408848696a07404420000000b120b815a0319a0b003c0303200703d0900e49151100210543c4040d5007408140d580d200c1c2c81c41040d10307816808400c0002004803070f07640c0700d0300c04841400d601c200300303d600c55041c00300000c02145160b952940702d017880e081510704507103007040192680401009402040f40c180041081c218034241c413003c0420b00c888480d070003070201c1400d200c41440e00f05100031500c80d05128030000101c0d000030a82d5008000d0f6007000a004d10802c040d0700007401b40760000141c80d030504618080101c04011445e11081ca404410445541d4810055007290124460131110001c10b0009200f0703440d020507041c40e4140601e07100200e1001901c005090440b01c440b4219400040e6101400b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 425013750 1250 425012500 425012507
    0x403081c0e030a020a170c0d08060102060606091f050d02070809090f04050a170f0f0901020f010c0c0609020a09020c0d0f03090b01090c2015060604140909010612030e01 74
    0x18107004420051481e180c01454000d40f85e0302d04103006840001c4041e04e0309115075500b000c46034600d0080307086d01c0200625440041c1503071416154240148a54008038005282c08000c035040a44010b2801d2450b10000304118407080c03d4a42030f406104003800800318110320381c001003105501c900911a43d9905190802c02c04540c0a0003020074601c3d103008010010ba40061441c2105402c900c1034000f04000d80e8078074501c0c2c451011004451030001c5421342041e41e0241c06031040c504240c0036150725030901c030030300c4e422540d1090b800320000b08c0030103441d008505640c1c07001c25200c2c0080d000c0f04802d03840d00c07002d80036030b4080d01440000c6d82c001900d04818070f5014400c50341140940c5030910103c4d291303898551034a032060040f0050140d0300c0500311240e5010743d00f085600141500d00000c2c0040100107a0345403400c5210383c81429055400040b12880c003002200c0039100385003291404060020140300c02c00320b0042c01b54006658411020542001d100c0c0f09501c494400c0e075030011400702c01070005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 425015000 1250 425013750 425013761
    0x6160b0711010c3204121b0f260c010e0f18040c094a0607021006050d0f03020a050a0b06100302180f030a020d140610150806060403081c 60
    0x40024800807412841d51380340c4901250221503164420b143e00c0401d40c1491084016280409250108060000200f800c81000450100c400ea101c40c1c0a040130801d200203c41c4507640d918241603001015014160360140100c1c2040c000c010f4041194400c401c00440c10003401c40710040c000804c2c40041004012400420740064551a01c0902580d8001038501541001128860081030b107100003040b06807284401a00002d2011041c1c204080d4102220300c5d00e40380c00703544500c014041c10003030410100d102d0007000115040a402c3e00b020b005c0740e450380c140c2d88000c140c9c114214007480305114081041040000070071070088089022600700401004001480104a44c050500500c194208040f040c0c50041101100b91481c00c41c11482c1000a41000c00241000354402c01c00c4da034000034801c0c40f40c1d0212100002c070040350100d884508000d1841140c0e4482e03040b00e903005580c3c000b28507102d0f40b0042c0d004040940201e0a160b1030f07a65490898200b0300d0400721030381450101060195141c01070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 425016250 1250 425015000 425015057
    0x309030c0a080a030c06141005040c0f2111030c0c0705090105030c0904020f040c080906060d050d050733290d05120a050c0c06160b0711010c 62
    0x1c0825980340070041d98a0b09140c2c60040c061050100c840300602625801c512000c1002d441095828686080b0314400321001d8041c0d14000c80c50603070b003100c085003d650a070300d50580c651111071110008069020080074000200640241c661a034203001e04061000b460052200f4a0314036200e0701203400039032600c7c5543e400540f244414600401c4141c45c0800c1455401509444055580c0c0d07450010070084042c104519402c41e252174160381005501040c2640120511170989070103440e000c017001346422000700d000c1d1a9800c1081c0c400401401113008001c11352180b500c019026903018a02c2007030310a04072071411b440010546001c0b070404d561060f203040c0100c1d01482a6010242d2003400070b500001458240134906118854007444400c0200c003404200a040c0e05550b5a08405c1c010003d40000c0e81c0c00e80a032045114140d02c0e80380c103205581740c0c90340c0c8501e5801c0001840d00c50401202016040c0c000344088050f41d821a21800c0c061000ea1280c241c44491001030009800300469040012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 425017500 1250 425016250 425016259
    0x506090313090c020c120703110904050309210d0905180126100203010906030c080d020d08070314180f011107060c02071d010518090c0103150e090309030c 68
    0x216003440204248600e0a0350386501d000102203c4541050b480c00011406881d8040b501400880545000003008403d0780d104e4901801851494402d015003c2c606490040c081e4005100e05101c5092070540b08421000d42c401700d0090003610401c941c14694404a05000950321190a2115080c0242e800659100038000220f05601d080e00d4850503501000710740c2400040441c042000c01c40130010300720380c0d0080100855a95039200c00120007002c5612084951b10060040000e15140c04200081940c0c2a80c01030808042e080504441c091401080b8a0500d555403c1c0800c0380b50b050900c6c580310780019100110003900c584841d51410380b100c641d200041e8108021040c06013a45420341d4406644840045079017a0044405e0b8100304540d000001c040305182c04100390400d44054103412154191401e401072440e44004031006230003200d81030001e034084685448107510a6022000d00d06500100192a0341c4807804804006000c0d1040e141076440400e02030030600d03080c005000079900444 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 425018750 1250 425017500 425017507
    0xb12041a06010206151801080105010911041a030a0608061305010f0905030702040507090e040503040e010f12020f12010e01050109050f010303020d03111603080a0b0609060403110d06150305060903 86
    0x35544e0a00614140f030800380c160a07001140c0325050b10880c000e0302d4201c100659a1030b039030038a00a02c000d1198090361400c00307416015420340c01c0c040b141a10100c4100740c01c0034151b400622800d910150000f500760ba910756001451081c00c0c08414068159007124100017991814601c4c00e41c2c000742042c0c10401d2410082500040300041280d800c40d0f4142d03000b05280e580d210b016030310b4152651109503502d0200042004121010000b44251038440c41d0300c103001d0340c8076480d2040b00c1d030303150085010064600141d1009032034404d00c950a08000100200740342c60030114034600b9100390600702581691180c00521041c9200d000390b90740125400c1c0312170f00c10762441c0c900950310b000d200d81c96401e1507903c0e01d2618204089000b1124850341103a420302a07815107190041c04c8000c2218070350003003403034450ba02d0241e00e000012125103490040c009801c0c9801c54403081d10303403406c9240c469403188a019a42001800c0707402420303040050f4070340c4034007001c0c51401c00508280d001812202d0035041003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 425020000 1250 425018750 425018761
    0xa20160608100e070f0810051c020a091d0609121902120f0a1209080f0904060909060b031207020a142d10031808130b12041a 55
    0x4041204403100351520302455180d95007400d00c2400241c015140d0703c0d6600007000000c03034100711443c0e145840395407410090340e210700240c02c101400c0e0096584c0b110322000341c1001c0c488441400d507800c0b0b0000301080149991030144c98100d520072200e82e0103002010f20107a08101c403d106280d40510001c0c0a84406040042000c1e802e10400451102590120404c410700c544204401e0301c0c28082e202c0c01e1540c680da64145240203401c144519000101500c960324810300080c06141c4105500848590400c0c050702c49030740007174200d014101c0d002595100000f03941e0850f400380101c401e00484001a00c02d0031641807600380000c5501c1402400000c100080058984da00340900701d40780c0c11452503400f00c03000d0002e501051a0340030780d403491074000910a40710714010200604074004807003180282e40512000e90503200c0c2c0041d440100340306039001c1c5002c100600000c20191340281e80b4644002d0321a0300e03415040d08143c041c0e00034104034a04010030405c01c02e9182d00e42c010b941d0511034180c40e12 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 425021250 1250 425020000 425020033
    0x1030b090103170c030304030e09070f020601091a06040f030b090d080a0c0e04050a1505010e061812030c06040c060e0d0f08090a060c050c041e05040f080a20 69
    0x40c84010b0900203e9040b00100940c01c400399a00030318501c0a0f646c0c0c0c2d04050400400c5085101e18039403082c41004041140f1034000d00c0510101e4055401400c400c0c0c0c13800004100a0010000200b03c13084200c00300c0c0d90580d1031800902c0605869156032940d230b4154208000110f2008102c8c84680c2e0010146405281d00601c104c0e5010442c5032001c105117200d10000c13281c0c0049407d00b01d030441d0910080c0320b00d0364207640019205e130100360000051296104011030f50905e9030041c80b600401e0800100c03201c01c0b01c0c3d40c0c405951104c00342c040816110400c8810b8910b0f80004020f06507078010754107000400181c0c5088000900e10351030804000e1005000180e039194071200300034a440c203800e11500400600100b55200d0710030040031132801503074034400074040c1e0300000c1048401c0e01840a031041103140a00c114009104200c041c2c1d40c5041070401284000e00b000340090f01d1584240c4132030400036031480c0c014030004c403040d50345840b0f21500c2a0b10408502c5088014941030b0440c00c694110340302d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 425022500 1250 425021250 425021269
    0xb09010e030a05040b090f1e360a09050307050714040204050a0e072d030b040c081b040b0712030b0f0306131b06030c080c03010806072d0801060e01030b 67
    0xb4140c5c103940c0300c0b1440b000807440c1a081c081250800c45560383d4200300c906162030800007140c10b41c2c902e0401c8101d039075100100606100d94100c0348480d4001c010101071468a42c550025a88000060142844d2110342c03540e003020604540c0c0383e200e11000d0040307001c03100e441e100f80c2c1c000343d8042d81040d0520b00010300c3c9104c540034400d070a012500020b00082c0c454105486505041685150340d00391480c001000c3c00302c96060000420708001c1c25504034102031090717103400041c81d03036028000d40742c851b00078080410406411180c10400d020100d205800b42d0010f18180d0711881d103100e41d043c180c08018023900c0410701c1c0c3e02d11541c43c1e12002802510003182859200ca19039084101038055450b0800c0e03190040080c0c0c03140d65480d5040410103a82680c8800c070111724a450701e120542c0e400300b2140092000b4041c1c130005070000b5002c191101e0182c6134100400710501c02a000c00d851a0541d031200405002115000407906401080020b800c2001080410401e29045c0070348203030000421003409 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 425023750 1250 425022500 425022509
    0x1603020f0603091c0f0923040504020d0b0a060617162f0105010806010b040b070201140d0f0c0e180c0904020c0f010213120506160203160b09010e030a0504 68
    0x10000400190015400d0140e18071500c1e02000e613034600c40c000b482c020100440e00180b0341c00304142c40300c0481d42a029240c903142070500021001e411f903101e0814030018081c040e000720782001001c1c0f13003d00081d90701000684901003441002420030305d00400109000101c18040c03242c0e000707440c00e06c603150038004c1d081c171a46c14590030404036210ba04e0780707503801d0314008018003404c07040307040c2c0c00d10204a0103420a604a030300f05021141c41c0c1e41c880d22080c0440c07240d0310500e0000d0104014110040d40104120fa0b2440703051602c003030a0508400c0200c2c291200c0300501d5051507515aa0300816680202d62080c0f030950a9400176885113a01070700da00703042400342080309036400101d5104040e035140e40445e00001c0d0010107a0b0202c204402101703010b90404078000104256511300428649642040000f541d81c111008108584803da80f04655966600d0b5040441c002008000d41c4c1c103100c00395000078603100308041500d502e00109164210b50841985001940003000305490041c4d004081d941a40c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 425025000 1250 425023750 425023759
    0x803070605070e060f0403050c0f03150910090602090a0b0313033e070602240a09020a060c02130207020d02091801060e07033b0f0307050f1603020f 65
    0x1034a41d802c05542000002d003c1540c002c0001452840a54844014000f201e2068080b82c030b100480404210b110700d009080c0541590101c0039865017000c0500307060741c20503a50350580da6000004070b990000c0e1003070071009036802c41e0000340e41112424038031000c20040c40c41040340c9096007458400b04a43d0000c0c41005010070031921504401c840d040b185421110368100d804030125107420860580c07641608403020710034020380740b00107000c034000303d840c80002040381c1d1008402001004408902d400140c102e403121580c40313601000684a40d842040680120344810203100380034030411807000091085410544c3c014040500144c489492080403a5030403075425030207a60395820710084614200c52030216600b0148001001c0404845240c000e10641d42c091000c1c5860400501e1404901c02181c0c00300700c1e50700160020031000c0010329100b44900c1058550f52044508103500d1078015050507200c6403c189021000d082080001c131407004840c0c50045402d52864002414500035158624050f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 425026250 1250 425025000 425025011
    0x1206040915090804090e06010510140f0307030b130506040c1d0d080d020d09020a080604120f090806010e010f05090c0f091c050a03120b0a0b0a0c02060307050c120408030706 76
    0x100300200c42590044c0045d24010070106c0014084079507900428031038030707000d40e490103800d54103107200c0c0003c103400081e5940c0d42c502e0641d8041071000781c2c0c1d200500c103074100340d0f4480c503246255846050008154403c01e00100b22404c003041000212654a2103807000c4c4803038006000c540741da000707041e9080000c045903101d001c80454140111148902200c8070f4406100117003c0003040c0b40c1d0342c070050740d0900a07a486070690b500c03610f03415511101030ba00600482d00c6900e408465603c01c03103464901d140649489008031360b44250140c6060701c00c3e004041004605001032084442148540300180801c540700315181c18020303103000c0a1b01c100020581801800030b00d2610580b0344401600000d280d00382c0a8003108d100d410a80c4e00c50204550440c000391050500e1400103080d8020b00c410b8580c014100880b00e03140c0344000c4c0107036011400f10001d11040307844007400350b44c03644c000e035100d040581c030341031740d56040d0401c254100350700074501840c079410038041030084640000c160341a4503400800000e6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 425027500 1250 425026250 425026253
    0x1c0c020f0402030c0f040f03171204170d020408010e120f04030305180909010902040c0905100804020a030602040e01031403041202040518010507020313150e210105040305120604091509 81
    0x18803a5911000c05c1c518001800100c1d1441d800b400801c490040e80141450025a942486144a5a00c00c1c82c6080000004100030405040d201d020a044440c2031600c0c21000c02c180728183d1300554440407069644000ea0345582c0703403e001d030724441200c10240510b00480032a040500340902c0c0009810004086030101d2080311141d01d800780d112000385901c900b8984003040601810003800124080e0341490000000d06003c3d0b064107064550040010011441e030100c04c848000d40200140d901c074040d9000000456101c4c8000e102034403040b84802c550f5811820010040214202040101d504c00c000401c48403004140c0800308580c111400301d499101c0d40c4160f000c00e4603400081140b03501c2c18081c0841c1a40000007400d080c1e9101c640b450545035610036110100e0140c0d074200c000705218121047c41403030403803001e001013800c696005030750716642e007081ca084032800c9400720302080d00021200d0420424680c030543c49402203c0500c2541030f5a903c9904184030110140040b80d00c404c010070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 425028750 1250 425027500 425027521
    0x815010f0f210203340c020609040e06010608010e0c0a0c06022206181520251401020a140c0d0c0f0608040f081e0a021c0c020f040203 59
    0x44071451100b41084121a0340034814001d5100f0b9450f13940740d941c03c1c1040001c2d2140707400e01c0740c10780d04100d40141d5044514141501c52410020007242c1c0301c401040005002c1c0e0b21740c0f041c4c280711901200180140d604100c000b031f02c1c0c42e6041c0c20014800c14407a0030000c06064100444502c0c80403481c004100c0c055610b42400a4040c00c5280c0b170f6500c440c0100c0c20706e20010100140101c032816500c600c0c40d460806c0c8103100007107083c01510080c11448254291841c040d10104030400d45403510034a640c001c5c9644d00d4207080c0041041702080d1410280c0e0720501403030301c042d50b001d820b0300e060340c00900c4441d90001c1e40d9000009002010504000c0c80d9081c000002d2212000c10a00075010250180c0320740b415102d280003600510002c4503c0d01e0300440c0203441104024400c44d4440c1502200485503102c8005503001502c034550300c2e29008142d041000340401c0604035034021074004000380403130070b00407d000f5101926240704114500c219940540e40306401e07580c0e050300039100141e42e07498121004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 425030000 1250 425028750 425028767
    0x80f070618120809101e0e01140105010509010206040b0408041805060103050708092e0c050702040e12040902071b090510051e150408190605100e0402060a2a030815010f0f 75
    0x2d001d9900c2c050017400107100c1034014200e80c421f0309c007940c1426070b01c950041d1281d02503d64120b005074407501c0024000f0b14403424040c0c20a001c2d400041c2450b5076254030741e420358084071030700d1421a111018070a940d6010b002d0150469641d0800803020f261404400369590749003d080340f6181d40c0d00360f1035802c07c5091185c850502001620600150082101c082c00c25800320900702d0042e46440b2481c8525000410744c910740204025501e4689442c0003484000703908290703810b45202d1180c001c03441d000802d440f0108020145008041601e18000c0c1840310a000140e1000c2d0081020100d26104408805030802c00102c08640c51494001500c14561450085400814442c4504101300c0c80d41002da1903503410540c032441c0c1c2030025039500742200d10044403a00c6480d18503050303280440d00514158002c0c00782e04880d840c1100c02e12424010308078520f0f11806101e210140c10500c5101450317404201c6c1e40c0d11140c000c9030301000c840d000c40002d1044c0c0c00c64020404110054541181c840d1007070808 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 425031250 1250 425030000 425030051
    0x13030c09062309060111060106021b1905010807020f01090b01140d0c0504181b0e090d05070f020310110408011d03160203150403020d08060d020a03080f07061812080910 74
    0xf116001d60310745501035641c000d2f4007170410790b148800c48688024506192101901c012441c0441812803800005640f520805403030a0190f010341c21520070550800d2254401440c001c03c40781103254900340c1d8031401c1e00c0712501810b0059113070410030070100318a040041d00311a000c3e01c0004036081090f02c050f03403250401c00014800d141d01400000c0807a24228420141c03003c2d00000766854541c1441150b039003030401c0340c010200358180041e03004131b21155800c04100c3c1c0050180c032840b00d50010b15404940d4813203800d020000c1c0c080b5040c0145402445280d4500c41f81e8000603030303400324044400740c2d0703030003090103100c036542e00025480c00b152401d1000a41070448500e8440b01401c05180203920741d8008141e800c001041000003908a140000c0f0003000c160b00948940440c80c1592105101c035807050b480080c6c058420400980040c01c07a114006840e4034040c0300c0800c0103290b19005413000300402e00344040114080c1031185082d0042041d5095101c40b40000440007460845604c1b4084072070702 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 425032500 1250 425031250 425031253
    0x121504140a06031106030709031e060507030c0905150315032a09070311090d080408030d09023c04060b0a0201151a0d020c010213030c09062309060111 66
    0x5001401c0302582000003075038131a400703d412410105040c0003c5000880e10240001c2c542d43c010000301c0d05010000c9a4034059103501c1d00080301988420055a2082e40c1c544000b0780e8500195280d503501040306005800203d500712040940c070000c0c04443c1c00060640c1e1000c401c80c00e00d21600b07a40c2000904042c801094842c600c40c0340701c6808207801c00752908454000c10305040012400e0f4820b1040c0340c031000200b69140d050145100900402d0002c411040303c15880811011581075070400140603100000c0f03201150701c41041c4140708142c190310b42c81c01001d690a503c1540d40c8400c1403034241043c0842d8a86c451000c4110000801801c4140d005281d03011000070395200140d07041d00300b030115440e1240321000340b0350b481c400003040310882c3c000108518030501247e0304408480e0000e203505590000090f0a050021481170802c074442d81c400c440014180740c2c10082040c86008100081000b840c90317012400da41011040480c00e0848004d1103060303036000280e080e03030140d842540104191130 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 425033750 1250 425032500 425032541
    0x1a1309091211010603080a05070309030b1003052812030b0d2f100509151603180f0e04021801030602091309050c0d050703060507050901110102121504 66
    0x2041002002429410030000c1c2540c410b0b150860700500441d001c0303e501241d00d41c07601c0c104d000110b81c142c0001c0c1c0100e007007108442000000c0b4480000d280e004045c100b44010440340b5601d0320343c3c90320f508841c00039060440200000816143c40d1040303c1100d401c15440040361242c0c3c04110010300804503841c0e4001204981441405400c480b41a20109841c800d901c1142c09050101040c1ca288034071350394440d440c0c2c0702c500d8040b442803000e841e1202d40a00b014180d044054000140c03604900c0000c04150fa844260400b85940941c1811703a03400003403698280325040c020391400d6040c0314007031920f1800300749001c00d08540b84d4403900215954945401c00d1135507107034900070004c0d50015442500c100f241e10305a40d500030f49840b4410045500038010081c10003084184801c190b00000c05030b801d8002c0500c0000403503243c0c0511403003500590340e01a6582c2c426000500f0440c0c40026840441e0f00c1842120415045000d200c3d0304000400c19104259180380c0001d00540f882d01c0302510f0214800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 425035000 1250 425033750 425033753
    0x10f020f07090603020111010218040e071205060f010509090a0204091a04060e0f070f03060e07050d08041a0705031206030321060f0f210a02041d0d03061a130909 71
    0x183d01202c1aa4400d1703070740400030f0f60030a11140c00e03030003a012080c4c1603018003048152180b9156002c980546075903010703101c0311942d4691303201c84030100040940745500203408001d40462203c0344940580812984200302c0e0034a1810940da070b100e08034009029aa0b1000a0400c0c40b80542040e00c80c400801000303102da1529240c0324001d0194041c2203607451250401c02c2081b00d0340031800c5015910307100e90110000c2d155031100805061030491500460107080d80104c1c86403a50386a0301420350043c40290742e00d51a102c2c50752244618a40900400304080c49040c0004e04048110303141c0c0c101a4000802c01d40f01c4000090961080b8072120742218503000d00e211009036101c1c00d240c1b088400b1566259120442010300c1001c0c0391180030158095484210318010803a54440030007101c0f44c1c1000c842d000301d203640c0458100d61f0511480c0b81144016140001c24074404c01c10021000c2d118134013071007058038113017440458179800c281c501c1c10800003003103900c41040041c00030b200030039500f1000e101d0070505 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 425036250 1250 425035000 425035019
    0x220f050c01021018230102041d0601080402010c02040905120408070602010f0e0a030f0e040f1a180601030e0c090103140d051318140108060105101805010f020f07 71
    0x115046016000d6003009039000c1d042846084100010b26090115084990b541e9074091180c003010840c441040c0307810380d60318917401d10140c0060610380070a0350032440000c0786034560180045c80345040144440070000140d91000c09035240ea40d050b60089000f448614210f814050341003c81c0390b0424011800007082c85000031243c0886000b60000c06c90b46003900891020b0f102c0521102c46c041e403184403440c000030300c5070a0085030b2080c0d901d41030b110f00700e000c0005016604104082c03010903840c0d2001900400c21025003c403802d0084803404500c003000d004401c1004c0c0001d2203d81410303a42c45507580c0c0480203010f9041080e2009204030030a603124500403603810183c00440d20719105422042030114020000c0320410107103412000d00c081c2c548011010404881103540202035118114070700b01050a2651502811000c8081c294540c100018805004882c003002420010b0340220200400c04003038a041c1036403801e190800c0405804601a0720f07228102a01c1070322440b5070070000070280d18 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 425037500 1250 425036250 425036263
    0x901021309060e28060b120105013006051203040806161202030a0f020c0d0315140906010e030d020c130504030e2e021605060403030503220f05 63
    0x8408010014080d103991107001111000d004000e076940c421000305400300562413030038004000d841c8090546483d42414030081d034100303a010490003030700840c00c01902e00b01100c2642c09080c0a01c0e1101002030921600f0711024482c45006a129441c14412402c00c000c2e50818006000f0140102d40842e00c034110359583d0f036202d131045104601510000c0b13500c5002202107500b40701d07465a2890038001c2207100010003588060213000b21642d036000c520802c0c0c0c0d0240003604042c0007250160040c41c002020140a80340c2921044d000c18402c1c0405120500ca8031107174031030785c0d035003074030196115590b1600680308169511f51696040c4642c181102105a00007424552058182e540d45d4800c2c1e402d0b9070410540d407094070000c0c04a540c0e080180c19030301f0103114100822418070800040c2c2203a201d221140100065040401a00b00c02c83c1050700c0d1a044030100c005101c1a00d105140900e962401406404003810b0000b0a8199101e48480325840a0030510000d030000015200341e69a8036042c0e68600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 425038750 1250 425037500 425037517
    0xc0801060b030708040602090f090a020d0b1005040e04150504050f0106050108241906021b0d0f02190f17010b010c05120702010c170c0f030a021b060d05090102 70
    0x60a0100c0400c0c41900d003001e41c2e01800d00e940741c2c40743c1c03070b11035a03503e50182d080108020b402400d0220491003903a60340c1c000c9805004907440c01680d807602850b4413400d641000041d980604410400340001d1540001118100d410454003900e2b1601c85180510541c0086d010174182282003605205c00c0c82400326110703000055010082161654840041d111003134100c4080180b0f42e001c80d42d1031000c20403980308204142000f04002d0318540e682400b840e00003020341200c80160b00c100c020750052050380c00342010300d0408903460900e03d072290742c45182c0007140b0388009000c1d00301e100c0607010019a0700240006400309200d240071090b100e91926002044903404840550700b85500084154003d10a011001703410101600340d401800c10520350a40c00301100300c0c100704c1ca80c82090080307400102c0e00403011b0725a22a0300da4800842071b03c0d51403c2c04901030140540c0003003201c02c11031600080d03245019106440c2074000c643d60140080c40d14003c0e0404045158240f400300418510117600030301c0c079003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 425040000 1250 425038750 425038753
    0x3050c0d03150906032d14070f06080f0a11130e0a3803030906040806150a080303010e060402040306020d05040b0901021c0b031c090302011709030d0c020304120c08 72
    0x2d03070300d0200c002a143c9611002d060f11b084555180c0300700d20016106c1141c01c0d2031344c6408038800d45a03a03c03589070302125030041a01307401032401405840700c0c05484100074641468407098500380305000e01203540d009010019465642c1e81c0d403003619442007084c0d41008150800310040c1320f95480a82e1158001100d01c0c081c554640504014041300c5111200466004500060300d2010310a420540414a28100340d50622007408601166501d0301c00138000390088601805c401e08240300c1d804510711a8450b050b00c038440d40d210030300071184d000007928110361103840b4003012615403102042c001d2003150400350941b0700004803040307018010740000b0b000e2803091241d0100ca94401c9086800c0b401800c00e00d0846000428220000e90626003280003c80002010780d100b60805060001104074003440b000f0110300c104d48101b05560f009240c9514041c1d5011035810f551510a03c1d041d2240700310100344004580d108003203035080b4820403c0e14060720600c9002198540507050050b10500a032180031682d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 425041250 1250 425040000 425040041
    0x13050907050c010507110309090a150b25021008072607080105030d0e0906210a06050a051b0a020a050706020c03070b04050604180e0105160e0901050a1203050c0d03 72
    0xe0034480c0d82c600102e640060091400c00d80c0784420403105200140449032b0301c035107031500d010b02c000c9482c2d0f4035070090410307080710f0f41d585402107140c4589a03803c00c0d5000c4460060300c25100580c484825881c20440c02e8581040c0d42da48505094505401c10303448520802c603000e02a0355501551003009015030f10684982061780c1e40e0f07034109580e40201c0c800f0b00002980c0246200d00f9414603200d601c1c0c21040003042515030201071440700364154a02c3c02200078642c403040c0a641405081d126041c0c0020a460090260340341c04090001411f02246c1c41c6e0b142c881700000e290400318801c1c4002c5600c181d10600f43c410043c1c0d03400c002547c3d407107101c8500c0d00ca8040c1e184000f0700c01e001c00049800321100502600d003054600b002c091144403511000d00040341e1240740d11132051900b03120b01445070f04c0e54846040f2031500004020315402d4600301d03440c000c0441c0c0d80180220f6981d0f0a4079002c171521890200d441454520b402c0300c00380550403440901744078607082c5079007464164118030800083c03032059a48 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 425042500 1250 425041250 425041261
    0x15020720120d05040b1803030c060609150a03080706140f010602070e04051e190302010c030605060a0c06050702010b03010501030c1a12011202150a0309020405010b04030b060613050907050c0105 85
    0xb2030360b00310700c107400115600b000200501c080a9014040759240e08550440c101c2009011905642c4070000f02021340d00b0100030080b00c1d28194101320b40090114040780c10100a940108114a440340409400520042044802c00c50340e83c0000007090510302c000400c0c2e0808007130300980c0d03000a00070364003d40a001d0010500510102d0b05522498100c1c000f4041c031100c02a2841d28145c03800c6040400d4050072001d440d107174003e80011000c00c2c3c40395000054030041607000a080743c041c0c0c0c11291280c030080054038012940890f900510980007407002038a610f820f1410f90044c140c02c6607594142d401c20000205101c00032861404860740301825201e10b1035010320201d00b0340715032184644a2501040180800220054100121440a01368000729500d002011007103070040c10780800040d841d0101481107040c14092640180550703010b80e428541036542d00000420020315250184002040107507000c103c001e090001824090000110350800e0000200300d0fa03c00d24483e0202d40c20100802d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 425043750 1250 425042500 425042503
    0xc120f1106070b1605040b030106080601181410030b0d080d0b0402030103030c0305030604020d06080109150204140402090402090a1211030c01120507091809030215010e041502072012 80
    0x400035944030074076201507070340d245948501c4c0c10b05444101c204042400302003000c961000056010b00195100d110351460311800040003002400d0900104443c000c40030404858003e5070200009400c80d603200008105074402c8009000b100141540584109002000d1000380c000074642420307400000e0195444c000148010381c4000e103c0140080c1507111580c1c0480d00c07030400346410180042c00585000c0140c6150b40a48881350050501650b40c0c131601803c1011100c240340000085c02815414545082ea586d10082c28443c6018003440c1c00140d0589280c2e620344c1100c0c0b240320014000c4480c0c40c0c8032101116030303103030158007151440784c01c3c3c102d03446910300003035000580c010503901c030003850441c14600300103420040c25100030b1101c0e40f1400704a00e00a50f011060305212080001800383c01d50070000c2c608000c444644c415080604014801001003030289a441034200074089001c0d60000402c0000b4410400064020b40700d80444406a00c1c3c240c5804901003005c0380d03100c003003002040007503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 425045000 1250 425043750 425043757
    0x100b01030f090f0212030d1a0f010f020304060e040f060617090102090f04020d0e0a03050c210a051b0d03020706060605121909051609050108030703020c0105070c120f1106 75
    0x1a000c0e003d0080710000502e0b011064032004002101901e05118207650a82c2c1a1940302000a8090028402c00419420b01c065039a040d000c091811811f60102160060740342e101b18051581003044180c040039103030b103d0360401e8551512400c0100007640c3c0da1003005100b80c030200c698401841030b160228000b034605000b07641e940f000080c0901041d503001c0c0d040200a40c40070484000b82903d0b01c01c0041c64190034420143c5150094075103a0361003212100550809030a504450103041d07824540c03003040c1f090036054684019086c14500d07621609003a44204101015040c90294440c00c000c1d0000b90740d05402516240384617903010701c941034950741c2c2a175036401034020010001c440140010300341a04000e1144250303c0860340050040c1a80d240e0a080032907860210b81c0c01c0754185002c10240f13195109041c01440340c1005181800ca41d076500946070010720242a0402078080740d0081480400d5100d070b00180f210aa511554901502d0001120320a054099036a8140451060010b081c4a0201d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 425046250 1250 425045000 425045003
    0xb150103110f0a08041a090d081008060c0904020424090b0304020d0605190c0305041e030f0302180d0614060a261207081315050f030612100b01030f09 66
    0x50034400e00c01c8007198080c800400a40e100400e078810b8002d0300890180c0721f40110300c2c0c0c070b0162441c0d00301103101804020700030f000c03603d400311110400c01440a000c0303020750f003068200b2151540ea548103c0010301900075500710400b40320b200400324003103c01004200c00105440d03250f40d4400c41d61001e150400b40000c45002e50008080c039034200000d00c03103034401544103501c4040036491281103080c6500302d4041e014482c0110395900c00b808144002076006e540e0301240c584102140401036500144101400090710040c95001305030244e0450f000000e618800801800100c502051030405402426082059881c181e03000f602140b81402c04007624019240701104007614500c000060f0468000d000c007190b011400f03500003203a0701e1840c000040407260b00540441e0744a618500c8030b1202d1100640c8071080c1955103140c42e0407050b4102042d64051480b44100507100d640300b00220380502001004a01540160108148160280e5002c40f21001e001e907000c2100b02c07016102070f405c441e0030303040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 425047500 1250 425046250 425046277
    0x81f03030509011b0605011d06040203041e03030906090809330f040f060e030f0d020604030e011107080102040914010b07080c030417010c0f0215160c0b15010311 71
    0x10b0101d8950042400c1d10f0910446030740d40c1660812170b11080308403082a00202c07040043c241860003400d00302823110741c001400310380031481d5092580d1008024489288100c2000d45012141d00500d40a80d10481c4202e030041420701441520380703001c50441d808010441d1084800d070b01c0810013102c6210040e0b0385e404400500001d113080000900401740c01c8040b086082201c108004201105140246002010705071241d06504070504201418044034001c2910282d22114807903041641c001340b6960401d8241c242f048a1480d0600100e45201c00101509020320031090b0000d901c40341507008004440c0400d404220b1031000c000780f03c409440a20940c078035441e0034000768022800321001801500e40f00c1c021245020b981c0d034940c2c602800303da8003070741d0b10b03964600c495000540c02030340482201d0351610181148c81d094011103820004058031600b40d8440c810030405a45010300000d41400c1d810580c220030606c6c12041d004101e0300c4a8407042c0c002814010340a071075401d41401e072001107081c901c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 425048750 1250 425047500 425047507
    0x70501031121270105040c0b180103090206091806190311120c1009060f0e06070b0601031e020910140406110c1203030405010605060c0307020f0301020c060106081f030305 75
    0x11480b00c0400c401800b0b00d15405100b082003203514414940f08080c44008000224480c070301410841040e4070b403940040e072107038070400030030982d0a180004154421000d080008400c603545c0080f41c490301a098007550005034852030310940a0790250118461402201c11048944c4c412000c0520030301300c1c0c0b00c020701c2400650141285443c202141e400701d41540004c54007100709182c0040e030002d01c941f0800021510f00c030710501c40594010b0884100080d035040c400d4070441a81d0100d03440d8841c92070058000c1054401003001030707205e9001500741989100c05019158070111002000754020203403a07200303695003102214880d025001400b20a0845505a81000c1c40c4c0b540c152050041014005028050002d040a003030f503800d002559140c1610380195224036141c64540c0c00c4910a0b005284120000d205440b005440001141c0d0f40341d80c1900e45103110743c15840801e007e8082ea410840c29401350000110309035600480e40d51050390102d484500703a990381c0010000402460202800140080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 425050000 1250 425048750 425048797
    0x1215040b1e040216030f030f021e1b070617090d08040f051204030c090b09041e0c050d0f03020d08090c012706050c1605030604030e130203090705010311 67
    0x1e5081507080040900058a8a4058810303a00c030070b110034004401003921194000304496040c42050044240b5010451408000307800c40d03045c1d400f0350a2295050040000d45d481208020380c0308141b00c060410460303452603201c0101034444042d10085003503080c11240041c6801d0000105070000c08440d0300e40341c1c4203440b00c0d1107800c1c800d05490420340d003510800b90340c0c5070709075000d5000700001c5001340ba40312112410a20120182c6403180012442442d0140a03c40031a8101d015042613800744001c00c4202280c0f4906583c541d1080d80c420307030384000e600d45d80d2030134454101b040312555442a800d49161104284094807160b20036a0301040643c0000005d101d1540181c20001c5500d40200c042c844014400c00400c5c42d5044a421000000745c010550050303560b010000003050180300c60031544c0d000d042c0000300741c0d00c040c0204041d08101305540e010703440b500c030048051245810400150741c0c038506002800d9450280d8812280040d151002901520101d04191191490401203000d0f0041c0e80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 425051250 1250 425050000 425050039
    0xb043f0504033504090203180609071e0b030108010e060606031b0703030f0507200c150a031506020303060a231e1216050103050103051906111215040b 66
    0x50003070444002110011001403c0c0c40c5010708010301e00c5a40160b80c030f00d40341c2100e006401440c008034166a10060070b203d10f642c004203103a0705070340045482800c616100d19464078040b43c1584a0842c04400000105894030107421441e18014188100c035219100d1806012051200b01c6d83d070348600e200c0d859102c0041740c4100c0105003107400792501087ea0048030846004607481500d40740040381e40f01c0e036200c04011211080d44030110130078000e000358049840c00b048001c61100c900d20381510002503548040e40c00b9520400b056150a88a018000d489850180d9030364004d80b030141c030580d80c50030009449040400441c0c0100401d00c03804a4511900080c800708002400300001c1c403042c4c003c3d1031941c0d030b00c1c1c4580e0f10b0740010396040104030010490055460b82035441d0007150400d030a120051020070303000514001078a03152101c7c030305d00c42064100702c4002c2c40140c81c40b400c3d40c440002c003000040040411742c1d0140131045181c4240032504002c1108072100c00d0421038202e14405151400f00e5070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 425052500 1250 425051250 425051303
    0x2090102011418300705070f031a063a140703030318050a0201140f0d0e0c01020106032004140f160207030308040b043f050403 56
    0x600001c03031140c0d00c031110032004031070442e104450a06141e00349034103c10104149803402000584a084100300c441d40d11400607010030b100e400680b000143c0e0810820208041001410116113600c00e894492900b615045803104038001003d14017808940145040045d0001028907c50301c86a2a15154a10b039007400524a001c1c4581e0791903044032010030948442c1c46103170355000300500702280c05c505d406002c60b650640c40c0c41c05400b10200000014800050740c9600741c1d0242440091a800d89805040361f104045883c00070b07510108100340801c90640100c0000750220042d1048001c00300e00480c07c072105e038407000e0174200322010311882055540805110980001d403012a030702d81201d00c0c0380c0303400105550300e460881c3e05c2010451004000f2041d0b00640f0002d10141c10028a142c400a00b0601c01070005880da01c161804141041507000e400e0001800380782c0603450840c030014071a0214022814100514124641c0300f0207542d10810444068a6012581c182d0401440c4400f000d2240d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 425053750 1250 425052500 425052517
    0x290306060d14010507120f060e150303040b210f0603100b03010e0a150c05030f1b070209070e01091508130602090316030204060504021c0b0301060909110405070203040f030602 77
    0xa207842d1140c41e590380030301803640300f01040e40f100d0092010300614841190480020a141d45240010034044041c041015541200300005100003030b0fa100000681980b040e64008047c2e00000541070183c1c0c1e030064606c6500b2050310079081071036039602014a40c02c05c4105c0300c095064002549280c402c0c140c9500890810401900010741e0312003410085140600c5002d068420800c44c280b03101e0794000354003404590300c0f00c611308103045042140010314800006400030f100e080d0301d01c505461011440055909554009020100b01e062808018101d480340100340783c005040c900d0301040b1030a0544228a40002030340c3c441c00c0300d558522090300780c18142c17075040311030716000c01440907244d4080104251051080342d030300b00c075146944100802c1300e005502050150340103000f40c1c0c100c04247c40d41c054120b4000c0f032010840a8201c40020b00401031508104040303403400d0024001d100011040e001440302c1550100002d854050084c1d940c1d014511503019800304141c000d00000d0072580280c40c015 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 425055000 1250 425053750 425053763
    0x603050105031509070b0c0a2102070311061309020324012f0f1f0b06030a0506011e2a170a0201020403051509010c0e012708010609290306060d 63
    0x80d5210350034004c6e1681f04000003034895000102200c14000400c080c11440b801968803101c400d03411000180d100d0800e032102616031f80503030040c0c09071512a00100d6400b142003400107210103885826101c000d40041c1c0b00d074540c0703051080c040a00581d004110f201c0c90381c1e0503196403030603c42e1580c0e410b941000c0050031100d00c0ca500d50165450403820403c0745550b200c0d40b0b01070040e40b100b4401e00b8040c0c001951041c144103080c01409005074a03a0011241c0002b80400003045990b581030043e030300e2202e2284030301c01c01e12860482601655021341803c041884081c00e6000241004050941a20080d0b8019040400504200303021401400c000c14502e03110307000250030b00e5581d80345c2506040710780e61107940c41078083c0200000d5440a01c1025107440d01420b1aaa5049088000034000d040c070401e4540018803101111540100c2405030b00028580003001344401d60726012120b0251090059041d0307403401d0704507006107060110040c008003e0001e0010306041d501e290802400d510700c2101500c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 425056250 1250 425055000 425055013
    0x40512011b0201020403020111070303360605130b030c04060c03020a05070e06010807080f0105091801110d05240f04020702040504120f03060f15110304090e06010603050105031509 79
    0x140c954079554820965075400060b01c56141d8000517148000325040984c0c6c0e85c020388000e200103504100304082c0003600700c10045107a40c010307640340c1c1c009110700420485500860000903c5581c0039004001c1071441004d108031596031032003105010b01090795030340300081051105225162151405403810760080c81103c4400c14182c46481c181030413600a20814404101000b40b2940c010f00310f180c100c112841d14409600d0310200d020f01683d410f000d0309106500990103d5002000c0400206004002e03a0081094820030340e82501c4642c404142c1e440454205800142d821440c020f0b9030f00002d18085903483e81c207007100c1c02c0280061041e04c640f94030550900200780940c0701d038403495206512918034181c22020440d4080e04c149210444001090704205051081d4022501c0000840d40032000c1207401400c000e2050b1400c1c100c3c0603170f03800607110124000a24000581000c84c0c003031565400d651042c0d032114011020b48409004003a003650044802c1e2064a068410803940000304005030b444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 425057500 1250 425056250 425056271
    0x6110a080304170409020702041d030304060c050f1309270f020406031205030402090901021303080d0f020c07141917010e0609010c020f0d0e0105030403020f030301030606030b0601080c04051201 85
    0x41c07135001908a152000c0d4081600390840c2020710410307015071090001c2c0550800c005403126640d1100402c010955500e0740c80b0000d09500030300541d9000c1c80740124894a44600300b200e100701614a208010440b030829505a000c2048200e80c05440c0300d40d62403500014240c1d03143c00e02483d85010040b60059650034000004c00c9104905040e140d1a81c0e4640e95681400e0040120340c00f40031f00025403a900c104003400011b80101c100004503a0301501941d2506104141c6000800c2d5551081181c14000510340c6035180c0045a21b0050b075110000350421a0b4402051101d0044210400300f0321401c1d01d6418800401c0181807440780e200c0100000c1150079100a485043c00000c0e07902c80c0040c1e45904038101d07a0ba030103010545110210398000c01070311003809401001076200b010f03201d0500c00004042010b15109001c41202100c0c14000c9035507d5940e80b604000802d4a4401075909941710004079800d9071154013a40d010b2a98035080700d00b803e04013010014400300c42c800300d40d150740d40c9040441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 425058750 1250 425057500 425057543
    0x3061824051303050301210f08040815240d0b0f0603240106031a18060103060e0903090d0c090603050303060103051e27010609062c0c0304030e0d0b1006110a080304 72
    0x200300c3e4032a00f45c89488615000815240c100030203540c0c1c03002a424020800750520237107400b420359200300c0041c1e55000350500860a040e47e407903006013040c07503250100f040841c4800040d50080c00e00380c1c129006001c0040c945203220078074003070120380c01e100c0f00010442941700340c00c104110000503120307007210115a80043d8101c130345183d180408401d81803c2104560305485803000401c0d0607a0020113a10303050340f14580342d11442d11801e00c1030741301c154404140200b01f05840050b0030008400c200c000c0e00c80c10595034a800c12154503001078100000035910180c9550f410000c15034401441d045a107603a015016818200d0034100d2068074505020111032009000311002851004800a0042d062030503602d40511110083c0890000c401018002400c402001990048014008580302d8540b46011100c1e40081c40030107a0200640448030240b10b1401021070188003440c0700e40d00d8032a6540c0d4180c0300c004180d60b098000381c201e108804040b4000c2d03002503502c00d220b202911582010506c80ca07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 425060000 1250 425058750 425058773
    0x50d020f04050a1407111005040305130303031b1b170f0a03020702120c060f070f080409020c0c041b211d0f0102040f0306182405130305030121 63
    0x400c8038646680301214410010403403a45c0024a900d842d000140074001541d0341e98960b08240b8290b26a18400903041c544030300140d030035401200140c1c130666aa64180240980b050341000f600704640803a420754000c0c0940c00c00d844c122003d00320a030309080c40703842d4254000b4000001e040342480c104440b01e4500c460400600d948007098500503252401e50050181107444917410f42c5440c1c1c04884884c02540d50541070301c0c0190084240341d43e4401c058a010b4286a2086100405c201400f04e03001c2884a150303009855a0002d00c0e00325640b40c240c1d4003c0100743d5841c0e068070307280704071600700700300003d4407441d020150106a00342d558440d454920381c40c412604820003c080c0d404045a00302c0c0142d00034001044403a07810002507007000e0900c481d070700000409200003000c250350f402500a00e014400d0100b106a030f00103020f600c030a104115180e031003e160940030310a25107013000282c1110608401d90380d4035134165486600390b84c09e00c034054480d00c074482083e81c001503885807024006403000088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 425061250 1250 425060000 425060011
    0x3021b01020a11060a200a0c02030a1211060408041707030b010806010305060106052b2c0d0504150507050f07060c1a07020a0602252006070c050d020f0405 68
    0x2403407500ca401e1000750341460307000303007503040268107080c60305001c3e4036010122142d0781c410720050360343c52821480607223191403c2c3c000207415004001b000e00c01c0c440d010050303140b5110f0780e8584418520703850748150340f40d600854008044480a12050101d1120000c410107490410005c40d240783d0f4407512998407640c3c00b42d001003000c0e8080001070013002000c0c410b0a0040803541007035800c1070352003d2442001c0c0d070201100c0c18403400c03010521a6400681d00305c00501400c038202c07014510b64100003216040a000750081a920402d42101030f4948120f00300e0b4203c9a031901194800e81d40b2020403186a44801c40c01e640ba885048000354809030240b080100801860b154000801841e1030403030110048101b0142181046104001c611500071400300c00103039018074016502c212a80c45581074020145100c001d034055555203800708150140454400715542040e010000841010009984200d00c40100141031100080020b070401041c3d64001c244014100c84c0802d0341100406c0850308210303003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 425062500 1250 425061250 425061257
    0x40b03090a02120d0c021309150509251202032e0c08040807060c02010f06090b031b010915020c04020316090f0506120606070c0f1802070209060103021b01020a 70
    0x1e0080440c90403904162032446158042e0030010192000903000c3e40480070064000d5660300f21680e0300d041e03a0340c020011207034010003480c0700c000228121780041604035048040781c4500e00c1503061070414580102c0c09640c8441c4608a018140781c25100360002c035100403a0148a0481030080311081c04451840c0303000243d11842c0c5080c108a4276038181c5102510324000e201c5510103100c0890351803421650b20342c0c0c020030081504070701032808070300420a505041013034600e8400c0c04650f1503240d82001985d000228115092184070b028a00a54010f01e0192408120001e500304000341d402d45021200324214010b8070031245802000c90243ea0041303844104c05440b41035982c505942001d0004054000c50503079200203801d007404a0082c0c0b08942c0700d00c0e91450a03d001604a544440c01c0703880c5258040a41d0704580d54450020221100c14018100035018441d440088116144240d91419030003c041c440780381c50f8103005400a520a0304800c202030460081d03006041024001010408855507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 425063750 1250 425062500 425062513
    0x16060605032e090f080705161d100506160305090a12051603111c140303010e160507020609010302090d0b0a2a080613050903040905090d120f02040b0309 67
    0x440325940c0d4110302c54040d00a151500c2e07100815030015190469a034407541c0c480c1c0d10341d25401c0181c900840d814111440324240d5001040f80c0c50059843c0381c0000010100c080d550311060640003441d07406000e07803900800144071081c2501e203916110760310a4000e0501030310703000e10100070440c1d85145800944007a9071520740c2d00104103007000f22400007411003c0c00759039103080d90b40e041b043c100075503200c070b05c0749026181401c0d02c5600e0100200260354051904501403c6520f4580c0d102e4000f4400e01c00c0d01002940090901c00e4070b19400303641100a59225072800405508200e8503402071030569040507800d21040f201501c40c21b40340007d440c060f9014000d17900d8103c1149050b540031035110222050761204110ba403da80e1050403805a0766420040d000d81d80f82c0c2c0c0814240c02c0c41c58280b1b80414140400d10850110220080040d10050750f01408a0341e0b032460403e03542c0d00071014480009000d94107022032103510751b100d90101d12042c0300141c900380d540c06404010b90019981a100d40d00500c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 425065000 1250 425063750 425063803
    0x603021b01020702090c0d0e1506040608070303050f0310051c110307060503010513090206130e01060507081b0309130b100c2d0f050a0201090512031606060503 70
    0x46030012209031010020351800440e0344c0841d2150b00b018010030030104021402c075118005e5600040d0f0041a05000c8a9030309805009800c08620181d450130300440c03900c100882c54080106940040da42c058482c189070843c92540710805038002414089160140344021a00380c0d1811030106c6c4811841581c180a4583c90510301c00790050900f42e184640d00c61541000045d070000d0690381101c07030455030b110501d00c542d4400000790041c90002544040001610400a441049044107682e013560302c001181e03884660a541c80d03c0340e40400341c03514a09120014880e819414807020036002078050f00c0c20300c01c1c004081132101e0000441c036043d0a464008424607400c0003a0981095065864001c1d40c542194982c01d0408107040c00059a4100d03015084e130130425040404d09541c2d6005d102002012650304100740c461503508400c90000300240000149403420005e100071080c48a000317540340c92036001e00c55280d44501101190680c0e21207200040541d014401811004898441106842e509 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 425066250 1250 425065000 425065027
    0x302030309120301120318120309031e0b0406020a11120c100501120201050c150109050405150c0d09030e0301050403090819030806010c03030b0d120e0306090c06071506060302 77
    0x1159101c02d0391050510040000d10003114075264003a4150410311080344c4401450842e500441e000307160103442c2d0041c950105a0b0000940b02120302400390810002a151490310700303d0708a82c00500b83d82030b91404180820fa2560013814024114284241000e214030000c5060520030144018a03c0c000301e60408052002e008800110691040801c00b66040482d020900110307820042d04001022600042050003081455980381200168000039a5544984d80107000c080b40e0440b02c0f40a002e05000340500a464864015000d03940c009040c910348030903030401400c0460082c2c00304500030340b17141c400c5d84003889014004d0b4020364400d4001400c0646052030541790f4084036107034040a01070317140070a80c040c10030358206c0001d1a00820035865802c086018260a062080d84441d81c82c2c903107020000c0c1c210041c01c00c014184c40b0040032114483c02c240e04c400040703c100020381c10100c4101d403607181a2008001051050ba80d15650210416246048821540042c004a1313400110a01000361 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 425067500 1250 425066250 425066263
    0x7081605030c1f0215090a171e0a050f030c0301050a0b0c030423040e0106030201020c0f0a1202010201150801140f070f030b0a1503150902040605040b0a1b0302030309 73
    0x141c00501c52030100501060100d548090041d01000040aa150401d4428019400c00d443c482421404070f08001c603c194684488000845184004001c41c01900d003001055441a0700112003500100445180d80e55040c0c0c00368603500c040000c00c01905c030501640501644c0180400000d0540325814031043c4452500c180d000304001401c1400307a844041400011201a0345500e01c41c98078040d059540c040e26412000c4000340d0150800f041003004810552206c8102d900036801c80d840302d0949410703c03800450002c08030780c101500c00c0041c0900c0f0702c1800402121032040c40000307480b09549041a01349a2103411140703003651120a251101075011031101d4204100005451190520401c090324400c100c001301070503d502d901c44a0090742c0c0e0791404500070114800380c000c150000c0e02004008112802d00c80100b4980301e04e01042c940c10b1403080d00c0580c1da01e07464552506007000c1e040105a00550480350800409460742030070030b1a810410a0400d2003600150784a041800f551410308a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 425068750 1250 425067500 425067509
    0x1917070501111f090f050109060b09060f010503040f020d080307020601050303092b020301020d021c02070b01030f06020708040902030a050703270507081203040c0b0405130f0905070816 81
    0xb6095401400d040420701852007940d4180c142ca802c1c1558246001034040c07214007808244088a51001b8410306401100c15588120420410305800394204078810b4402c3d294a504680000501002c0d03502540c01980c206003d03954008280c0142ea0024200e00c02070391003220078103030101c00c0c08516901080b005024150441c051401c0c80b8034540070822141c4c50000394644402c190141740050074001114010064024000307550300c04420364110041d500c450800d01c14041034410b5031511400038800c3d101401e501c412203440c0d0364615143d64400a6440c40c081d1100c1c1d60810203980041d803c01c0080c07000b8108043c0142e20303450900d400700200c0d100107068006043c10000d40d039561210302c2c1d010356400d04d0000e91080d1800c0d10340c14030701d150031010b410042c2203108855150098509000c06540316502c02d81040b90100d031980801c0ca214003071031041039000112030000011480d0560050001c04119040010700b10840fa155240b43c2002071f4402680f5410003040040c1184010601c0c10260 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 425070000 1250 425068750 425068757
    0x31f0f1412070b0d020906070501090503031803120106030509160f03060506010c05120c030708040914010f0f0504110f070303060f090e070902071a091f0506011d1917070501 76
    0x30b51801000020314880d44094420040d8001112100c95942405940f9617a400500030000c420301d5140181d03490b030044c0c581084c10603035107444800d500d1000044600c200301d02c1d46010903591030404241c01420001c0c007044081d000c0c07542450300340621a400b0301c0041c411038000c0301c401841c6041031001c41d440a080c860400648a62000c040350307000901d40106c01c143e0401e01c5c1d071560700060340341c01c0d405210001010610001400949a025030308171048455140c4114003e6980c2c0d070b0910384ea001c03801d204541500c08a52000c100d245405e41c0b2000b00c1400c410f9041d450034005448410450340050011004240e454206003e909922003c0d24082c10021004000d00002c05010030743d105554451040290b40004500c410800c201e81c52805a02c1c0c64410b00c200b509114044544424800c1c042116070044207900200100d40c500581d4000c2c4010f03110711194004480034140042230707040025030403030728118050b0445510b00585c500180880407484004241051410f42003a002e40d1109041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 425071250 1250 425070000 425070013
    0x6030c05041401080c0d02040803040503010506060c0709050c09060a020607021b2b2102010c05070309030b04020301111803070e060a0506031e040b09010f11031f0f1412 74
    0x28802c03480016094100c2400e10403455030741c807520010a8403400404140c0300e400440c0c00102d1840001c058000c1d19421402408240c1d110410300609010b8428110410780c0104020482041c4960000d41c01040c202d80e4546030680e00f501091199000104100050380100c0800140b260f041c421120074903019080c203040301600c14000341d5180034480c0e00700c2c1c0180d00d0309603000c10b04904004030380b0010fa100ca0001d505100c0c01001d0200d6210909a18000d94206840d10f02c01501c0ba10403a150198140c81d05c1101501b15140c074014014024422600366689420585c50002c101d00507246a010541d04850070002c0c2c0400c5c142000d20651002e84150070950134040960b4543c44588242c0e01c00b524069240c0d41d0f0300c0e800c07020581e141e013202c500c800003600610017845818076000d032244420100030300c05200d5915000c41101d80d603020703180b0034803028408928683e502170314100c06616126000340d03055848840d0480c43e42000c0e40002c0880c00c009588900e0b50078840c520090404541015145 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 425072500 1250 425071250 425071259
    0x8060907020a0b01060e010e121c0c0512090f0406081e0f030a0804030c060608061b03131e02120303010f061107030201030b0d081611030a0818030c13050106030c0504 73
    0x1035404103006107030510104412040c11b0341d1245420010410004006805006209412540781c01040840c2d018800f9514008800d4600601c9000105548000107003010714a04e60100c81c60341000141d00e6200c8500201c2c203074aa6914066400603040d003102511025403440700100b942c0112492043c0160000a1001079084001c425a080d119090074009103503501c500d400c490340105110001c210500c1c0c643d01040303000780000c81c0c605c13492600c03414581e50310740b6500c000c6c000d00048603e11140111400c0c1c10b0001500900300c481801c2003090114a0415a81c1c000351416180e052040c80341d50003c0010000c0c05403405007400204410700345400c5500c00c0c026030070b071103003100d000103030515031039030784090241d115850f000440540010b00c29484411040c0280080540d484d0107480c070781001c1d4a0294545004070700130f030515900000461808000300002040b403003112003120760500032880e25030384903250116003482c40540800c00282960406e0005812105949004001c000c1d05120502c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 425073750 1250 425072500 425072513
    0xc0608150a030b06030a2405070c2f0307080f060c090d0f170c011e0b03030a0e0604030624090c17100801061404110a0e06030c0904050708060907020a 66
    0x20103803900310541c03c0d03a0760744000109140407180b0600400c00e032595842c51100c041414030000504802107c10320480e11002000c0325002da40766405000005110410118080b4109044440045215103943d00c10680703c0024102400c3d031340100050b40000d000c009003d80c003408407036803100d19880d94606240010000c90100c0160304401000004025594420300c039402c200e920030320102e400d040c0d80e03031205940014041c20321000c80d81c105200d491903900b45c4800b280034260a4101c090011800c082810034100c800b0702150f0065500072208001c0400420f046000e41d110504000784058003400d104003070f8580c00c400790351050240030700e0400030813842c0d58005035805000300400d454001035140c405a000d201c510130703031120712950b02c1c08000190074421403600c0300c00741c80c085030104645d40c1404000c0e4454440c4c08103402c009a44415084800d18200014540101880b25140d0501c0c9424021604649059481c50040b4100400300b00051500402d099403007911440034081c841929518078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 425075000 1250 425073750 425073769
    0x20304120f0e04091a0601020708120d060e040602210c0a08060316060e03010c08060918070308070303060f05010c031e021207140c060403031704020103020d090c060815 74
    0x182004510040708041e40d11070841e010b0107507030080c010800c00f203a510304054030754002c840c943d8840e45007500041e070941c004070344d80c412116640050708042d032500c120708026611401003800525564400421412401c1582c0303481107203e2240140d441c410504240600341d044c2420b4840024180200400c20410b4410382c2c080300c9440c108000715407520b900285c1401e404044404560842400004115500c2101010400404c2d4006c02c0300384180001103825050456503903400c080e051b008280515040341400071002e60300801da40f40c2c1d076100e80e2840c0d6254000340782540002d0f02e075481070007002030010744440200f40c2424072070340f03803400c95501500c01e6001904014408045000380040b150003880054000900d550140c6d546940307c1c0740101e0f05204812803400c65104106605800381031040c201d0741030302d816844d134003c001c0380c18400404101d40208202d042680900a0034540700d054090039031100e1041410026240c10000b0003003140c0c90084c6041801004144402c0e0305842d841100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 425076250 1250 425075000 425075033
    0x10b0f040501080c070b090d0f0c0f141203011806060306030506060405100b0f070c0f0323030f0313030e091902072a0e01151413080313030b0a020304 66
    0x41015135503030342c085144600170410060010101c900070041c801c100820303803210000858131500703030030650103030111042c044030a0010409045814584042000b40440c00117903904d440880d085949811120581034100307034030401d00c40120361002e0841401c5405807101404081c5410810689181c60313a96903010080c0240c2d0047e99140007203440c0c4d6054000e02c0020703000b809036140c2e942540c0201d0304140e9010041c141c072465030812021401d11040703103d502c12246c0001e54900d0802c0c481c001c5100c0403640c0300450050380b00c1080086252002c6c200514850090000450020701d05420302410385d00b02803420314800c8009200301b0030000072900325051159000c0e100140c540446240c0000007605041500314456034179a0f01221203260390000c941501e002000004041e6a990384c030341400212040e0b03440104042840c5400f00c3c0c02528050401c002014001b00310303450360b400201d400d40d4040303000c1d804d102601d0141882413044c0e0010140d04508030100441c99840d00c0e85030074003200c002030704 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 425077500 1250 425076250 425076257
    0xd0c14090f07051804050705040906050405060a03031202160c030311150109020a0507050727020c06130614092a03030405010f120f15090b0108041205041208040e010b0f040501 77
    0x4568100c01e04c48200300c103003c28054420803140c1040440a0942c5d085845003101d02410207201182c141000c0c0142809500301070040c581003810b656042d203144c0c9048081341c540e42d900340040031080c81e601c1d14101c240d5006460000f151400c1d414010500307040e881c000520ba0340810450750b011070b85110001d0444440641c0140c8526224000b29014130991901500e01c0c4070300d03031001c01c580c080c2e4201503007560240140001100d2007040c000c4141c2c09001c80030f8a49400240006c0c00706440e0311584011541318000003d0407241811560072401e806840302d00741613105041800f1004004100082070040d4404400a0082d6501c0002c0e924416800340c141049162015969901e015030100c0040001d5203000340941d0a100c91403100900910740054100284c26200080c0d400c15445410080001a5901c060607522502c410f050281d22520001c100101080b0000f0100c2d40e080c03015081d28401c41c24280d44515100008050103030681121840307440810072520203142d070700100c3e0102c03078080c00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 425078750 1250 425077500 425077507
    0x30e03030d02040e090115080307020108040c080d0c0c0807050603060d03020c060a030e0c22050919050606040c050c1b030703060c0e090f010f0603050606090d0c14090f0705 76
    0x1004203095004005121020702d00116000c20500745800728948500c04250081099500302c90f61020011414411080243c20401c07402e030155110700c1c6240d510a008002c203840343c0381e4520405140000003030071000041d040d4075a4104000d09a0302490082c580c0c200100281810036000807810300c0b000d03207a03910807401021070004040c000d1000c40e168010061a035501d0b10202d0001501502c039a4004852600841031441210314100070400035003036142d20180c0310305001c2d40310301c6c0040002801c4c1900718415006030385007100840000041c0e1070310507000f42c50a401d10505200545004804504c18410103001c903a49044002441c0c23910200c000550244400840c0b002c01c1c1881400c1d00b01500060924403804003058201626070201003040d40c1d14900f40e80c4400c0c0418542c2400c2c000c59402c40b100e810100541840b940207150031000080605103800710300800a00012a240812a04504880c00410003048400500c810030030081c1c0389050b00d491311200c51314003a40e0062143c01806000f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 425080000 1250 425078750 425078777
    0x5090315070f08250e03010f1121010b0426030a05130b18240409020c0c03010905100c030617071502012a0203070b010303080115091401032d2a0c03 65
    0x940140005190a13231040107841d04004e072044150f40485407100801115046c00c1d400c0e2109041010b041f101c01007929424203091003220f00349142040507810a0790121000301da0144007e0008014014075600d40903911200d4240d0322600d0795041d803100070160b009005e90510b140c61060301350824041101c02c6410084909a4011100700c541c148241101700820080b40f42040c9070700a090405480b0212002c403c40401010b00b03132806000e0040880d0021084140b02e03c403c2c0d0401c500c0942c0c2d03401d020449a40743c00c180302a000c43c3c20418052035000400402081c83c0305503d41d50194000e00c020320421a1000d0b200d000c00642c1c1090181219050490604452003801a140844d030b00468845441d43d4900b00241030340c200780220700c02c1e5110300000d464401e000f200948101c4640f410003000700307501600190f004224003417100200b584140f80b0a819500701c0c0c5000301c4000000d03030000912083c17250355400c90488101c0b040ea28240d515601108a42d000008485042d905141031450400c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 425081250 1250 425080000 425080003
    0xa030324030605040605150a0501030f0b0d0503070303140f012108070c0e0705070b180a02030703060203090c15120a180b0f130b010605090315070f08250e03 69
    0x140358280c240c115100d04044100407241d005580203600030f02c0306114603291220880004102c51410366884810304504004550180d084003280c501c0203c000518402014086049510034540031a1150400140c06041540500c9000001d480d122850300840c07070401083c0040000602807030b80605e500448404010840101e01004c26038082c0c84680c40e400b41e8a040142040180640d200c20001071002910592142040d1603c882e00080a14066203c5101000c141e80d000300e550102402000114005030710200300c4200214030510380166a403800401081c101f20403401c2c0d840c4202d143e5440640c408460034183c1c0c4082501c4021006161a42c02090b4020401110724826140c081d40320030041c03085005000d8401e80304800690320b140c1d03810840903a80a40b9010090819260800500c010b5118001a01d4192070140c11a0303061401407020003070382041101d0580000302c1c1103001d00c3c1d020342d01c0745525400129000790115a005210107001c110785a101c1250f00b04030400e00c25001e144d40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 425082500 1250 425081250 425081291
    0x70806040512192304090218040209030a031808061e01090501060c0b19050c07030801080111030f090304030c15030e0d02061303140a0903031403060a0e07170a0506040f0204080a0303 80
    0x6100c4c40303480d5140c1e031301e05051002e50002d02c078a10078400703a13900d000f0882c1040d0080315035521008020b00610142a9025034151350142c80301503035568210710119a040007000002d00030502c116441110507060180121075400581181520f5418440100030b10fa0300b08042c1c1c0303281503008400c00c4555440c400300d049070814565042d0000e5082505109066003441c00811589009035030b00f020a2b0b8079940c1d902d003a1010031030a416108010000114401c0181d00a02d81040501c420740b46007681e2502c1e02c0300c0081d9980c0040b4141507080403076005c80e50309480b42e07100e041c40000190802220303c400113515100b000349004038512590072000c003050b124000c40c10304a00111102134803440794120080080d02240400c502003840340c80454581a140790540e403140304010003034084070b0300302808070002e050f0182190007800106a10042c5440c1c1158149100b10400f02c00005c1900d04502008160780814014260302031040109000c030200c04200d41e001140c0604011a188043d00c1c0412038020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 425083750 1250 425082500 425082557
    0x110307080919140d140301050402030c07050d03060e0112020d15020409020d0606140301030804060e01260609010f0b090907050903060f0a23060d05070807080604051219 74
    0x709280070340200803060f41000e0396440344038221071400240c204180c58400c030b00380b00030030704842c2840104007a1500360011640804481c803c5410840b1030b075135a600e0000c8861081d000b00b40c9403e024012a4542040c0600410312002c411751002b24540205960b03880c840005051407584a40d00038101200d9011100100150242150343d070f00802d00c03107001445e8030300602000030400120f007640f507403a5a040d40d041c0d94010850718034091400a040c0d407082041900c907414410403500002140c148980307072055100d03c0c3e02d64183c080c42c0503410806903000581141c5c2c1d12400d0043e003840103502000c25526003d506894544280e11080d0301561140a200381d2507600d807140c0410030849120076010303203009a154020510035141040d5070a4207443d80340d140e29140f6075481b0009081854881040140c0ca4007907000e40f403649490b050020300f001250b0f000994168005030521080000030852203543d54045241c56041090404550084d0900c1c003507204108802d0540c95070901040969010b14003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 425085000 1250 425083750 425083783
    0x503061e070e0f19090e0c030d12060f080a0b062d0f030706021b031b060d27050f030403030207121b090603020f040507050d0e010f020409020702131103070809 70
    0x140926a00d01044c1000f0f0300600704a50f05207009200d400c040002da049002c6401400f0b44003e4400c0c5c0e034201c458103603200740d01e1031540d246d9100007601003000d00c02d40c0140403940068550542d031410b084038044009050b01e0300800c0c80c82d16101160420510081d052070613010703401c116038042000654500c0700380500316414000d961002504035000030308440e5800386410310300e00c210b42d40400c060700c9441001d150080149800e1060311a8680f800c010300800885200000f01c020b06841c18944441c0041c0c1c1340035440d40c5600ca81c50600804000700560f05000c0d01c0114a81810756a00945400c2c4912580740d801c1541c00a0348208044001c803124406046075040044540d919000005000c040c40140d020303440300b040070304841c14640940c610a26080d11400d00d00000c4000d0300d07004100600380582c04d9580c410034144216841d00081000b8110b801c2c001d83c4805c258010862806003610341148814036081248002d0420003058a51029072402c001c92550b581c800c0705800c1808802452284 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 425086250 1250 425085000 425085019
    0x807121509021b0d0809060403030b0111010608032502030307110102120c070f06030920010203070b041b0f030b150f040c0f180806150117010f0503061e070e0f 70
    0x91010209100001141011036650b0410f03650300b034032045d8080d40e4003c510f4000000040c0424000d4101119180e018941401c8200d6a80211402c4810540142d078043d040011f0402c00003000ca42e0100d010043c51624100d80d202d16400280e0300d104648005102c44011004503540340e000740031901900031410051030b0340e140800307601616403089005401d0300707241030b03800410010311a1048002d0194440c00c43c18449590003a1128000425920701d8110720080000c3e40001316400d030038a000d980316041c8501c01c1030740031100030720340c1d5480c1c0c100300042070240600304089008090b203140c0003c0c90043c2443c604002c44003040c00e11001c4140540c005051001803180f803030303103c003868a0540546d40c40d107003181e0929400e041020132030300c20030f440c550200e00401c0b8825160f000c0300e41c00b0300050400c04400040300c0707801c1c0d450200980c45004c261f07180000401030b074101031125a5004041c80c014000d0000c00300241c50845001500c90010000f022410b03016945a24070282500f020003400c0015 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 425087500 1250 425086250 425086267
    0x11071403090102010501090c0c0b0c0d1103220f030e0609060403030c05060a2c070e071e0806100c32070e01030809130216140d080712150902 62
    0x156580070105440c01986410000198888103100c0c801401c40b5035507074055001d026465146040401030807642c10f1180400c80101114150f20480410224a0513659260700d0400c0f0041081c1541e00401c094800c6d41030a144001740420403000403040d80350900c99000d10910700424250700580e1403082d00300800203804400c0c0741e0042c44001c0c0e058800c40031140c1541d9a607180340242c1c0c240940c41da03a074040d0600601000590034610859010103030342111101c950b540281586264180d6107080428184000081c000e0a901c0100d00000741034203002e1910708041c0f01050000011420f80000c0040b00b81020381003100d03000001c03040e10040f0340c2d84d00915a5002c104942c1400e43c040000350f601c40c1060000d442008000d181d8101d1741c22005c0c00d401c2100500034029041c003003a0320000d803d80e080080b588240d44100005a2503030107002d4285000b860541100d10b4828429092400e00c040581000320050307100e01c800244200b85440403600505020341052004103d42046202d20300121b10b808 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 425088750 1250 425087500 425087503
    0x20a081b100b040f090c1203020102070b0a0c12020304080f030c0d0504061527020309031e3a0b01182301080103030c080a0c1b0e07020c060d110714 65
    0x34400310003100c0800100214038250130403640300c0b41c030003401c01504403001c102e0510034180f901283ca010b400090310b80292a96030402c64801100c000e402c1d1652415031503080366000b4003001c40044400e00c00c51541c101500e90076813600480310415100c0c0b100000254112070004203440100448850030f00076400c25182500203000d10b50920543d6254038240025004900010503c900c4c90000140d1106210626240c0113544000c20050386d901c0200300040c48688180380c03c240c15100015402d4481232158041c288000e0101150000c00080088640040100c0501241c3d031249603000011500003080068420508054901005051005000890b034030360885e40c100e40c1080c80d5040e14891040c000544602c0000e00028001600003090880002c041000402c11b500160501da080d10b1410741e00c3e900c0078202c2c01d80c1e80c4c640c0d0780040ca007044102c40120000c3d0f000340450010700500b0700d40c80c01003015402090003010096848524074103a0302c11403011141265041519555002a10503049 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 425090000 1250 425088750 425088761
    0x9090507112d0307170d0b030d0504080c04020423190902090423071b0204180501050a270611030907060207050301050c07020609040e030d0603030908030a020a081b10 73
    0xe050030014120380b00102000801111000740d030112a40703941c010034030b500c01c00036000346810f000c500d507541c1c4504a0641d410420300c0041d61840d0b8811b5600c5003460701803810a00b03040a018000c600600041c0701d980e28000d6555004030916a1070b44000c12181300240060001da080351840e00511080482ca240f2190007c04140205850034083c941c030000b420184011103001031040b500b412808180c54521031070400c001c04030104402000c109003900002c00b1a82d101044500740d85402141004000081c050b0035400b0000410410448a0405020788105656150350052407010303115501040110b81c000a448050402c0c1d850f100d02d420a00c841d50344e881c90045901620407800001603030718050083c01e2180070300301071041c10071103554244801ca030402d01800303030b00c6a110080300798043e000300041c1500c580c681402181852a50501800c6403005801ca1221341e001042400e800640000310001e0b19940710002c0c540d240c0c00312a501d4200140350a4a44c0b05004548498141ca0099000b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 425091250 1250 425090000 425090053
    0x70c030210050a0b010216030b070c0c050405010b03060424050415080604030903140c0604050d080903151515090105090d0c08031e0306010c031805090915010509070909050711 77
    0xc54100c10a05090408507c401d0302c4006e02c80c1c0c040700e00280c0003c1c850f81c4800c038498400e05155500da52620000350a0351400d0300245046174001c01000041e29107402044a41c01036030948902c0c46003c0302d849003c8212500925000d2a1901c13120081080c2e00b05c0e15070000c1031001c050320390504003860010a200c0b4103210580b21310710004010ba00210002c540d80c9501d181c001c010514051510090040e59105503c003038803904030030f100d060440c1e241440801c00e0010007280c04611803074040c50144403505004201070041c007a40c52600303200f105031021114980ca090814a445056040020300410318000d4018152a1040c100040b100c4c1c000002c1e1a03200c00c5522141f000400080c0410034900088540134009681c84a81c4400300380108201c1c00c0350b0321a50540040140c546010804004040d10490600d0b4010008550a06180445a405028125680300d01070030305c034000a00c5101c1a006070300c05141e81d04049540ca501492000120303010450943e030002908400e202c20700d5102d1090b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 425092500 1250 425091250 425091253
    0x7050105090d0809280c0e1501021c140705070b0414030105010509060f010c140706020a06061203120c03022109072403020c0c0301022b14070c030210050a0b0102 71
    0x226404e40804551801c420f02d101030101e01172840001c101c1044141900c06440045280e48041094106185d400d80b1440948400954690030080024545424140200d01890300c0d000300c124007e40c042d5a40c0350810a07195402c2d1244030b10b080c06400c00c0b1065120100740000050000f0740121481118076201808070020451607a0711014000c14410032078503654407003100900c0c0d20240d07000f01040c203412806001300d001004014000c452130040c250b0804070261b44505843d10400c41940149009030040d240100104c000c030f960043e00100a034060f50132210786030018076074103a110f03505442c0a410281000074505000304038011081c142030b54854028061a24007155000ba10003075204480880840b0302000b42100b84101d00a40003040705100900a40c4442c2b4442e9500340081d0640c15020003c8041042084c82c4490010300c4165201200505145020201d9041c000c20709602c042207003450109501c5a14080342000f90f004c0900b400c0c02d2508040c4034240da219440007070250020380 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 425093750 1250 425092500 425092517
    0x90c19080d181203120914120c0f07060207060f0c0203011805160302030c0103150b03010b13080a0f020d020105090a26010e07090e0a05030d0c1407020315070507050105090d 76
    0x220107181c40c410001c0c0035011880e2202e1245c914a40d680c4072142007405000304d0545035403440f01d114200740608004441c0d586000c02c0c440c06004040c4004000780071210002d06c02c180c90180065110714080c13046105100108020b5084107010315040b40c806640240201301d0702c000302401070842040940143c4080c1700e8904918205410400f801c801e60760001c0040000f170744040c00440140040102030080d0240d4440300194250110020398040e21510380c41c00e84584110a002d0502900d42d80502c040e0345c0840310010103e1628281054099015034080f070400c151800142c80611503135000036080380003030000256104a82c60b0044060009207902c50154109502907400d884c8204403215040d0031011080296800325405040502c0071401515aa05015211242190030a841d980a415103404d99110940e512402186c20070003092840c50800e00c01d030b00402d82e07600120040701c0c001000e200105200354001c200703171111268820001d215915010341c070700341c8507900303401382401191008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 425095000 1250 425093750 425093759
    0xc05010302030403020703020f18160e030a030819110a030c0e0604030b06040f060308030c0a1e0807031536020909040602030c070803090c09070503090c19080d18 71
    0x7802224007807900356009002007410768003008128056405c1f0307540e0000080c42806620912180e0092080f00e22003012544000c1d0700001502400760891014860f41242c000840021f4205141c2500300c821800c40381c40c00d01031441c00c0c0d0300034020000c2c4004007103004103104100036455006a0703c0c440199942007020031190040c0440717806907000040030008550700080781800c00340d20080c42407110034804220700c0d40d40d031140d400a900a842000c0c0d4100002641c0348040d400c10021300c404883c000c00c20042070102c101c000c5c510035019100780308064036003a41c031407070176500385810000d401d0412004500100c2c0542043e10b40020345607070004002190f0040380c1c0f0990900c00d45081075405003690360a40c4d10390780e0b960001e500c010714045550f14244442804500c102010b50302c03a01d07820001b010180c01610800c228800c0081494081210420070880c0d543c0d004100710300322101c20b403080100c2420304170f106203241819070015041c1d44280075080008a510000758152200104032181e0f005484 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 425096250 1250 425095000 425095007
    0x41202010612032607050c010e030a080f0a0e03031e090102130501110118060608060603120a0f1205070503010e01080a0b161b0803011d0f011514160c0501 68
    0x1440307500b0010b5402c041c801c1c00b09004650380340d411140c20b66244610030720000034903c0c828064800c0d4000032000305120341010000d116242d040b01d4410021801c06101040041407060f000300300001000001c40814800c40c0141c003c1e092800b60784058070380320320749100d4100140348c440610490b4041c11901040c08032070180300321864445401c1040c15400e0a04006464400e0070845007041c6658407260580110320721054120024402e00c1c001c0740540c50000035501e02640501041d21a0700304102410700018110b0443e001c0b502c090800c1d450749401408103403107640018000040c464100010404402e50000c015030507120b40106a444c0b41e43c840007025540c0000d1a802000c140c2d4900c04103110b84007a040c42c2000301c850340340040301c034026213940c0ca1202041d10000c0b141d04101000521245214840c400d0702c98084464080d036500e81399203004e140d0300c01889005910044680b18280191040c0081c409140c4040380d07266403191140c145801145505c041559505c5620790301152640c403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 425097500 1250 425096250 425096261
    0xa0e06131103040f3e03010b130b060408010911010207084603020a05060c0f0f03070521041104020a0206070e1201181a06180c071a04120201 62
    0x1000003269055944a98841d4540220660b080e155412000c460076070700c0010215000d031002c00840c0d0600240c05202c0c401084800704170b01d10344aa41044460701c20b9032220072943c515101c0011001c10102400c00100e03103e4071503a0000700c82c0c0e50804e5030340001e0100d900302c40700c24050282c1c22038285582d1442c4041c0c6070651548189a00b062000514100410118410400050740b0300304a150440c4c26032107100400d2007032011005070b08604080014011f090282030350015220503030900d0f04103c06003251851260720311001d51200301201254081c1d110350113840310b068052030204c82c1012160120500b988040b501103820400603000350506060600a0710740103259500204110744414070150307000c00e25003810980000c0242e241000e44e07102401080103105003000070340714500f49800d0044902031140c3c03d844465550b201403003101c0d202c00302c00310420402603200150700e440b08429a0751622600f2005400f942d2954001c080550b12040010301a0b40705a421402e100301081090f400c1e40c1c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 425098750 1250 425097500 425097521
    0x140402030115080601090b07060c02010605090702070909050a0b0906090d17060d0f061a0406050a0b040501141e040e09060402090606090103090611130b0415030207020409020a0e0613 80
    0x3240840082c1c20034003d1222079004007050400a1249840c0c061543c0c01e40c1001c10166116511005c180091a07028418a0301500003075607010000d1605c83c00c0a560703040940b00300d19031144d86017954000e100003440140065503200c00c1d02012030814001c403954901041e83ca0110328000c1120508800e40100c001e0f004940300d8500e00a0300f0b1381c460040066201c41e030842a1041d112649503540021194030911101c10b42000307079401c1940111041c4403c5800c180c00040c042d41004c18103018035402c1001307507400c0398424079100c1302241901580034494040c40c0382c0740b10241001e10380e07103040c000382c40081c100740c1c0c81c0c00c4200c0030380b9a2102d9003207690303400c151000794002c10303440081086c901f40b07034000300b880c0c1e07038181070204100f419981c911080b21411034a4000c01346011840728200c043c000d0400004110005605050a00700710103c1300c480305400920083c0341d8001441c800319103450300102070b5580c00420582016540e90001030f0740c40c0c07080700c07528841c220306222006e40c0c80440c8200a03010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 425100000 1250 425098750 425098769
    0x607050304031e020f2b020604080712050c0307060f0507080f190e061005010807210f061d19091709010e03070807031b06022d030a0305011404020301 66
    0x4009140480c092290f140c011030304501a5600409000d5410410044820ba0708030051100341e500164407a41520340c1c00307000301150843c2c0d082c0b0001c07440718800d44d0303030f010303002260a802030050340003c3d00c451040702c0c000e005500001c1040028001d90364000c240b80010b0318020300159440d07040031910004100c52040702a00764002080d50701d0101416031030001c040440004070300e17240c0d65000d8507013441207416a0085600c10401c3c0040d5034007200d00b6130042a241001100c2c0f03282c01158910900da280110700d00720f80e82c0c600c07500041415401c004001d0040c54840514041010081d40d54140101c0f500e506102810103401c8442005110f41000386420a01e204698030441c3c0b220162680860307041c2d410015541d0030720009643c1401403200804694009000841c43c0d850300383c1c00c4241ca00785621030412485d0040004503008645100410503484984100f482d4030000c00d034054660500720703841440080341c0000b00c66007690245050b6608003594203062a0410700f040241d100034015003000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 425101250 1250 425100000 425100017
    0x901060f0506180f12031c0207080304030f2c03061b1c060f12030e0609090f0405010603050607020c04291219060203220209060d060b04021902060705030403 69
    0x6a02d0000700c1100101c0081107104c01c11066400943c0d152070030340840d1000e40000510395500c0c140800031060b003604050065041803c1c9031210096400010000b4090000d0f13041c0100c035051141e4107189240c03940a02072100d4116040d074140b400c00d5552840e6000344261f50214100c03042001a41501c5d43c0300d04801481d2441c5034000100124244044c48071080e2904004980c0e40c0c100c0d02003001500c0cac4d004110841120a0500504001740c002c100d50107887c040100c1c041a032100c41c900c561150404440718880d440300d15059004000350b610180ca10302a43e418009c0b4175902250000c49050300b00c800303208017001600405100601129a10094130b140b03540701025081101800341080001d40540d0703140e8601102640c541c021016041301c100f41d002007002a001482c440b82201030503443c218603440041d5901161250f02c0190090f4451142855903034104616a00302c0c0d200d40390094429515500c52038442e20005030751a1800c0e000d0b0113401d00040c8954800c02c149c900c520741541c0c0d441d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 425102500 1250 425101250 425101267
    0xf1b09030c090c110307142107060b0d1a010602070b040807060e01110d050904051612020d020706060b1902030a0909230f01030b010522050907030c0305060901060f0506 74
    0x10b0040c10400c100344242400018a58501170000d444841d0246c0d4006446081260441d4144068141a030500a112807980201e568061041e07640403039110b10002140701c03840000a46c0750802d240010440018100100c100c05206024181201c05503000c0701c05190b16402020b583d4021402081c0d11a448290100320403481454010000281818010703004001001e8883c1010b01074045900812800a03200c1003604082c440c043e40076110340842840000c214000070101404003105080301340d00810200541c0426604440c00c09a121204200b602e5644407410b181c0e03000104a1444400344080402e00d0900201c11600c1620386552000c5120b402d08603a01d004022187c1080c00f9500d041071196281315540642c94024580038054464039890743c64410f161990580146006a0111100003c2c0790303145104e00050350155030000c2455550000454504031480d800503003c01450720380007092010200d034050107158240020700178507842d03204c00900100750380303d4a50480701c00c009456 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 425103750 1250 425102500 425102519
    0xf1005030412050f03010b0c07120510050402060409142d0712060905010b131a04060c051204181a0d03080a0b040204060e1c03141b010f1b09030c 64
    0x4440398164206513051028001d90721425030404d0700020344070000010000d4084400b001710a0062803680d86030080006643e60303040d2540d40001360901030f01c0d140e02c0880c08541d609016034001d0001c2890801c202464560703440100034040d00c8082c035124001465282e006080710300c545680d5201d031821000c44c0c80d903c604032800c170031034102408441e0783c2c2c21011a8846a6015682c005c011408c0c0c0780e0385a2140c16034004020300254840b40c2c2c100f2001c0c03840310707002480809550464a05051004100119003841030601e01100c2482d0243d6000040105140b100c4110102c8641039111040054203c010080001c403107206182c180d01c6884041d28400191180840c031303a100d80e80c0d600100c0c010401c440864280d800980102c0c002c2402440c45a001d4104030100e000034010300d189052000401c5d03103002d44188000c0b2861940d1034400038008428620f04003130f0402014580d0000c004000702c00e040c000c000c043c060701080c01c581d04030742042d100512420010040d40d40044000344142e24080881 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 425105000 1250 425103750 425103773
    0x320331060c0822180509060a0209010309050a050102030708090c010203030c180a080d021204050a05040c090b040f050f040903080c0c010e0f030a03151202040c030b1306050f10050304 80
    0x40b03554810801140d0754800514111100103032686601101440c107009600d446003100040d0074042a00e003c040255284000a860790810140310b40140e4803081c40004074041c05c01c45401400c14821170300e22030104841540110f11076901552541c030661501400940c81d000e40101c454010fa10610114013a4104080140124420070400c00c010791269004034050b4019070384040d84036080744010400302e54050159044503a0000043e500d014200400120250042d008807406980d9845040b50101c0c0a03c00000182607041300642d291507503841545059283d50085c54021050720302c504c0c2082c200313401401d01456147c0c4601d441a82e80f010f064081d5003160540b22029034032181c803440707000c07402e2101a52082003003010350343c1d824240e1406070588a40e601144840b50072281c0400000c00105440660b1540c11a8040f0742c1d4142444110003501055000c1a071000744074010b08c100000b42d0340010121401a0741c007030840400312082194040c098843d101c042001003001600007020340041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 425106250 1250 425105000 425105003
    0xc0c0f01120c03060501030c0e090c070203032205180f0a0e0709230702070807090507021515010201050a0c120e030d022101051507320331060c 63
    0x2160744000103014001510032088012010940c0c5140600455a150062910540450820149107400078010980c1550010540407616070701023015000c42d54184207c0389000703212102c1040581214410042c0c286051007400c0c490120890b02d514051100700380d240c400e1108000c41e070b506664032405080900001c100c03c80c6503000b1100041503d10551182c9031401e240750221440326404008900c0f044c6001421400035503005c1c0004204240340001e1100640d075001c039000c1003030b440e40c0c58141c0c5030400c0307c201ea10411444200f000b0481a202c8003504050500764001d01c02c0d40c503040c64507800c0f02c54040e0044005400d00840713140c20145500000e40c0148140110b80c546680703082014100e8004032050a801d000905030f00308000000000140500340840314400180040351420059101d0610300809078214541040741c02d83e43c0c58001b0018268000e000d441626115100f01e4880d0302c40d8074880c562503800500304150400300281c0500801581a050b000f01d414260191020383c4043c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 425107500 1250 425106250 425106257
    0x90f16020106180c030501050a03080f0a090e0c0d0f060602071202030309030a060608060a0e0a02120109140f0f01020c100e160e0f010b090307300b09010608030c0c0f01 74
    0x800103c0f40c10020050000000b4504000b600d90b4040c80010142c4006030b00140c402d0032803503411301c04103c964040f2030042d0b188400c641d51b5048503000c29100340041d984010345a610540811424030103c0c0024602c0d24120001000300c0520700103108102d98042c00b90314010703800800c0500200248982880b441030004044030304103003c0000092400c0e4143d9012030300c407901d0b08000c01c40c20904000c00c40e040032442e5401d003c800c0c019080c040c0c0d520b0a18a010b44100c0410b00d540791200c0c820343c03159005642088030040b1004050204641e00d4145909020b02841804134012320080c041c400d03500c040200c00043c0201280000d1290007516601d04c2d00941e90044e007444900084c054078104005081c0107003001751629040c038800030380e04416404000480000c100803902c554020409209446561050a807200c0d203040d007200040001c02c4400404109420b13440092000d0b04038014401c030030043c001d00c9000d403070f4184580c49000d4107482103610352259082400c145442e99804181280c18035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 425108750 1250 425107500 425107511
    0x807020d0e0f0a090513020a150f050f160b040b0703090804090c090b0a180605030c070f050f03160b09030903030711040915051009020910140705150114090f160201 72
    0x749104880d001e44404030304441141e034440c00c50030805840c2000304203802c2449ca8102d41600060700368191000c1d10f2003000710004405070b074540c8810540703c0c0103403840850021014545000c400c0580140d409035008119900018980b502c81d000702c120003a031001603181010300c0d211012025000c0e0f540c016050204095021407141c581002514219002d40e45d0b445071094242003400808145801600c2001402c10800180038031000031222034030741c0140c0d03001032800e040c10640e050641603030000555010000b4602c0d4002c000c05034195125002d10420041030f02d803001c14503030301d1144041e000c0c0c141d0010721117400071410b00a00010755100280021803031014a5540c081c0c101080c101c1c420f481c60340d440501c0400303101c096103032002e03114250045141201144c002030b2110140f0003208104158403405c03294035018030003900c089941c407100725090b0309400c6103094088003013401081c10741044241c4800951030000e504a0003211255000c0d46180c80d00c0100740071464101c0c502405640d00c2c2d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 425110000 1250 425108750 425108759
    0x3120506060c030405010e18190c0504060e100e04020f1206120d0804030c1203020a0e0d031211040f09051909030903030c081605030c0d0509031207020a030f0804060807020d0e0f0a 79
    0x810590f0b01c19003284d88120b102109e210f0f001411610440301d480100842404288840e9410400c0d41146400480702c113040900c104408482040e0880126604503001007003805200d00c12101030a08045a507a80000b25079034102071200030034600e414070206034420164401900e006000b00fa0300980203141020342c400507030b102c1c0090311215500840020340d001a0b451030f41da51102c031700d8080044c1110254654901c5880003002111a101c0d450300c1d031581c0740c1b002c544200000007180c008000d450707400c106580d9180710380c900030041200c444030800c40910300c1d0f81074500c3d50711030701000d182d05032120b8081608680f4111404000c1010840e000c0c6410032124075106e100524103042d072403040c001540d603140c00f804103900309890ba40b189014820b09211407009507401140048401c0c0040f405240ca8211500009142038810f034001780100080d4080790081c044160b008209072801078807101129211448201c4c1d07a5903c4000702e100090040300c26000c241307442c2d030301e2054610004202d02d40c41c03600c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 425111250 1250 425110000 425110039
    0xa0503030c30070f03051501080c0c010509010207020405010b03010614090f120a11010c030914010c38040f11010509031912081b0901090b030403120506060c030405010e 74
    0x10302c010281100341c0203040240d910707841280341060b00104e240a100500701402c1002c01c5940390a000c82c10700004400080007840001c040d41e1601c4e40301d40081c0142d040002c4564000d5201d40b0007070b80034508107400070483c0f01c0081d0440381240c0903961290700030002c50002d403005420444600d03521804003d0080d40941d00c054045101c5141540909429801850060f25440c0101c00b12418400301010341d402182e000030000089842d0028a071216110610040302c0003030302d28000030f000c6500528040c07000600c1100d182a00c503101404404602461035607881c4498003210001c051003d07480301800000d1604c241c0c1c05003c40e06041c06400e1560000010341082d04042003410050403800513802800082c03000112880018200050341e81001d070560901c080e5600050100780c6400240d810013640700d100107100801200205940300c1c282860001c106441600f449001c203410300e400300c0c44518000080300d81e00203070b0038001c5181c18034140064034007004104072a0b520034410007d0b420803568 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 425112500 1250 425111250 425111317
    0x30a0c08160b06030615060f090d0b040b0f0603010506060a210501170c0402030c19050c071401030f06150c170c0102090111160506090d05010c030b0109080a0503030c 73
    0x81000142c0d61031800400b45440d10034028844200000d12000442e02c50320b500c803c45618511a0524035a1080d519003c0744050f4001840103104012140c00c03c4144820450110301608040740511030680b200030405091320000d45809a02582c1042407040e42070140100310510076507140850500095591944212542640502d40b0708003103100581010f4014003c43c2030402c41141c0845c00c600f40001000040c1c020746a4063704bd000103248804000d00510568002001c80401c0b40e03140c0c1d0b214886d0800190001c0020741c0030a09001c03000340000d0490146131b0555548100c0f015840280c2441154a46003001048d20007043c80c00011001d000c1c040c0084c42102019400548e0b6203401e4000141025003406161145401003011704400d409001c800360110780c412580180c0b90080b0704001140514058402440ca40c42d040c0001c0840e50981c000700d00404c1c09803640d150700ca0766190919110440c405008119401c100000b454402048001d17141c011a0035818058808040c0c91801c110380 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 425113750 1250 425112500 425112503
    0x3150305100b0301180807170d02090406081c03020a141306020c0a030c03020d06020f0a030902120a0305030609070504030c06020102030a0f0204030b16020c0a0e180c03030a0c0816 79
    0x104041e110300c951a0060049000140c026030080050110382481d40d00c410012600c0206040e8000448406000c0071040200d07070012039000503035403140901e001030025030004804030700850030428001000203020071685034000c1c2e64130020100203944101180254449030801082c004d170345c00c0728020029010302801e01d544003070890403840350901c1006850040e41000040c840c41c0406404d000003060060643e08403a41074500007a00d416072325000c4003a00404c0d0284441850101c0c1c0d808020750715400181702540280c4080645001100c2c3c0d480d200c4051401c0500071400800125405091041c0540e6020b1064986141821342b81e603500104000668004001030b034011080c0070485203144101200301e58500c2c421460549955200c1180c00801440c0c0205030030750110f2640240e00038404c0d246800c00083c0b9030100d49444586030310481b041540c003649196030f0301b0001d40f00b607840090459032000c1c00800550400503000d5003240c500d442148100c5a040050011030520300c3c0601c428a0303000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 425115000 1250 425113750 425113753
    0xc0906011e030204081615030f0605040203130210021207020f15070b10050d030e21030307120b030105010518040501091b0305011808030105060d061205030c0d080603190303150305 79
    0x142d00e4141924507140c09180a11b1400e00000d504001482011100000052250602003100b80305203a40c01c0003050142d0003c1d410900010402820904c89000160007070320886054500348071b40e171412a541e030051012007403014410004100075241c286440840e0410051410541180c0c04041c0b00b02c075080400c2c1101d5014010050100e84405070f074011010700025104103112489540340140b030800400b0b8024000c0d0b123100d684c1c10300c900200c035401c038045602c03000300c0356a404d142000900c4240071044403600d0030329024150f8907134941030060074100c0c0c00042c0321013201c0b0600c4014407040340001e08121100d43d611540240051800c1c041e102c1808810302c4251400d9255080140c03e4030201c034500341d1a00018034203200010861019241500d01c01da64180d01c440070b800b0349400070980c641102c0e4a440519021074104a000030040070140603c01c01d031044407010400541d405401070300d14980c150011090305074000513008100300d20074042c0c0b81c003041000004000300d00401940e0019100c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 425116250 1250 425115000 425115007
    0x303050f0c1c030516020a0c142d01030c030e0c01030b120106060309120c15051b04080705281e0e10050307080705030606100e1005070605010510020c0906011e0302 72
    0x54000441080e007202680b030007d0614a08150b840c5115100f56000310910170003054540101038642021680641d40d5400302c07442803880c8a0031254074401000c0b0840c2c0041c0c1041c00030101a0700c00c0c003442c0d200140c980020b140c0d103000d680c01940030f48410a5501e4110444586105e0100000d009000060080e514002a050014246102108600e01082c0280840d0600c00f800140b01051003030610101054005072a483d01d00f0084480b00c18840d508122400c04240442c5000300440c800d0700312081103a21a20445440c0182181c0c40c081079100100312040c204200321381c00940e050303a4024005610b00c0d5003002e466280103840e281e0284e513503110b8021400e00c18801c5040400c840e40c00351076480c0081c0f80580c54007002903540e000080c1001c0c016130f003007150a01c00500a013203d6980d000014140300c942e9000b448001d00c150401c1100391030882c1484000501800c2032682c6001e40420f0f81d0103045810510424015a40303006400c00d070402c107403c404c0c0042c044154011900c0d13074000d540c0144e41c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 425117500 1250 425116250 425116261
    0x60b18040c06031d0604031416050c0f042d0605040f050f0601030e070501140409050c07051b0901091e11130504150e22030507060c08010303050f0c1c0305 68
    0x211041070740340a02c0031240d210404c0380310380c002854551103680762420381502c0220100c4481d4170701411500904107024203040108102e40880c00b0040701e5810303141152110f0b8014104015207801402a0100094521603102e620070481941c40021060354000700b8596a10760100d401c6502001c90040940e40d24014000f4210089500035005030b0300b46414007a440743c0c2c0000c26290f0340507124203418024208840454120741c1c1c0c050310010704001c0c40401c01031814298451190f0303c000c00031a040e0007600d100188208824688540c3d040010700340340b290780c0c20508601c1c01070000c1034418201d1200c0341111600500300c4c0c00384000c0043c1c0500c03a1a1512820043d000012005030051440345040c40c1d280700550440c000c0f401c040300e102030004042078841e101c1e200c4000c81c03808100c21034000604055030605d50030000614055105a1007084101081041124400028000100001c004202030604e0a0040e070180c03a184580c4020769040c0140b21400380c0c410441445440301180c0c80344200300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 425118750 1250 425117500 425117507
    0x12070b07020c01030501080303060d0201120501060201150b0a080109050903070204050c040f0e061c020a08150f1602060a020c0106080118060c110a060504113705030a060b18040c06 79
    0x4040d50b030b081c20140410b5040004080e01c80c000244283d020700e01e0480014190b81c420703c801040700c3c507500410012075864500c020b000c1e2850381c18000c0b13105d88800001078602c910b5030031140d0000b03071a030b240ca40b10707400c1600f03074406400c014201c0612480280504800f695640c0b003498001d1111a1800d80e503649030959810540344941c0c4103003d1183d4500130042d90f901d0b00da0503550800071004031081614454400212030140b01d41029000d4410510200d82e4a110007043c00c3c02210503400602c0300340d94141440b0783c48002c1050420040c0c11580105480d043c5680207450a01046400800c880e070301c0d0340398203003122551407a1082c421500d8140a00740081485401022070f41440d001c0100b90000c5030b210380d02c0d0302c0c00c20018503a139911000501405204689041420030003010302c0c02030100407001d040c0650340d079207802c410101c0f4030900d840307002e5841340c04e4022240090003a201044040d160706006040003405260861080400102001c0d50a8051486117104440629034581400c4004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 425120000 1250 425118750 425118763
    0x1e06070921080c0609071e080d140f0a0203030a0609110a080a06030b070f02100b0333130c0b03010b19092304150510080912070b0702 59
    0x208148031046405001204102050404801084444202400582c5000c6040b4810803501c074602d401500144014800041003103001c54141b11520350604524100700c50280c0400d02c601150741e4400141610202d02845401d10400ca0204640c0c0c105a9086036821a41c0d00030141c4030010b800000400412090920911010748008542000f0014940c11220701d032740b061040a0080c842d0301e200140301e1003a1600040083d41d40802540c40c1c0b4181003001411900000420b000540140700c80020801e0880c415000c800e240180100725290794181c0801d00b000041d0b01964803003803291005901004813060b00e0780294404000240d85c58480e0424201001c4180c0111450540420040164141600076590007903040c0e00c455855036a2003c080c1c5403c9003030303404080c0701501d80312491800c0895200301c00300c8540076241404048a6a030100045011502031141d003d8018200c5d18079161003007000a0703201c24040101c40280c40e0351f20003902241c00184040716648410320400400e950f06120384d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 425121250 1250 425120000 425120011
    0x1e021b06100b160c0801020d0b04050916060318020a0305071508150112091a060f0301110f09240a1706010905120109020916110303040f02211e06 64
    0x940c002e06103070008842e0310810f40810a89000c5412200500890701350800040800341c00842d44c0320924052000030340180b0941d00d1180b89003038001154003a011403203074804090800d000507081d00f0410b0550040c0409050b1420000b01c489803a0010f840d90400d06c0c0103140244000d103c528034280000840640c03070b0880f03200300901c50b02403024241c1440b08204403100242410b13024a010486120700400c408040609031064004407903400c25244c0b550310b0301030403007500d007040301000302c00070b00d404d0381e020111a5007210810403e0300c000700c0c00070010303161045005161040705040250a2002d0098090100c41d43c8180000c00609460f000044040c04015200c0f01040b140f41c6203002800c141c14510035580210780302d002d02d030490807080d4002001c86600800d6850103040c041c1046000076100320780301003c141d0403c00d044c140d0b2800800c1d01d21480d88084406803241c650780c01d02500b6071b68814040c41ca490780c44e04a603410711041c032040d8039044001c20010098902e40030440e1506002a24 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 425122500 1250 425121250 425121271
    0x160521070b0105010e0409050d0309030e0f01020703150e03072a030308130311190203070501031404060b040209120c0a0b090a032a120512040f06031e021b06 69
    0x2109001807908140395045440c00d00389000c240d80341102141c054540030034010900d001c1e01038a00748088d0903902509203a0b02903a504850b4a0364202032200d1034480340b80e5180547c1c0924801c00000300c201c40022a05400c210011903500200c03010b052135030b0404482201d241c0340a4a0800e0b51400c1008002d0810b100a005c01d40b040385503490141c0004070240c0049202c0c01901c0c20101810b010343d004904884c424000c0714440c0c1030324050134aa121070040100d109014071040052958441d001d681021088000d2180d500c0e152507989a004045030003003541c005809010780841e507900c40c00900300c14101c010243c15242c4d90304040003140c020340d40001200c1c02e0140804c441c0d603184c0c0010402503c1e0712020604c2100f03021a04480160303001342d03219000f0319170050041503080c3c0491000c0e00e0700d4410f0741114018220042c0d803143c51b005a000b0410302079130f50a0208500d81c40781e08002d00001000342014410014132400100780da003c2544283e544a1ba150b400204010030840305a01400240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 425123750 1250 425122500 425122507
    0x4021303140a0c12050106050a08030d050906271510090f0626120c01020721020c1c0f05010510050f0a2d18050c0c06071202160521 58
    0x203640030458460f6000360210048020701e900c00f0072500354000000703008000c05540c41c45035950407241d501d0f03100300d0b1442c1c03501d030404021802c01800055050301840090001802c080038801000c031114000c074025013014030403110404442110b004000b4054280ca070380105205042c40d07911000c7d00c084c1400700004500d070910400003212050201560102d000b200c6404103050b00d0b070014508892580310001c078100000f4044280c010550060499a00c22901a03080c0072209e5145401c0e446400c03298030241e006604148a14581482d41c483d14690300841d40c2c1d6000c2d000e440303401c02d2404d5001c007155513030364880500004400068a000040404a03410222004aa00451741400d0f01e0700c102860751080502080210800c0c5031a0301c6045410244001070b80e50f50490b240d040c0d00441c8810518526000c04201d280d1400c0301113800680d280344c010700700c07919810022581642408089000d50340c1c00c1c40b00a850005034480aa012401100100710302d20382207142c100e0080319150006810710041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 425125000 1250 425123750 425123753
    0xa180909062a0315030b0901020c060106090e01030623040f0b011512090609150506100e0108071809060b040807210807020612070c05060117190602070204021303140a 73
    0x110031111054030b03107190206881c2450091307084034481d250402050144103100b0800c0c504015800b401003403145074200e03100341c1d84e0b074002076802d00341030b0240101d001c3c0c1c060014004640b0320703001183d1103a422400d0172465944412400d403140001d50302210a2050302e00120305220302020310501604400c00700702982400024040c1210741c40e201601c0c140c5444850a07001e10107541d202c41040c1d030b0004000305052403004002001081c007160031174400c10480790041101440382d410642c0620040e169410151078640056422082102c2c0d82100b0b904c040c040410014a5409040c0c000e1006d40d8501d81c840341003d49807401e18107650480114681000c0d50456114140307127000000941100b8443d07030702e03020b50011a9540c81913100c54801c451075801809010740c1d020001850090240003503a0aa9032110920181c08000a840444507070155060103140c100303417480844100d11800e00149014416400b18040e03801400700344944415140d001c1040c4031a0301d600304900a100c501408c0c90700d255 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 425126250 1250 425125000 425125061
    0x60501180f110702010c02040902030d08091207110609240c060a05060a032006070b010602010e0d0906110319050a020706030606051206010507020a1401260c0a18090906 74
    0x4843d0040d04100c0b00c600d0001c01e6458a9110b0050a41c001d402d4448400f07820001030032403001510b418030f2510034500800031080070102035411461380440010f0350740c0c0104040282603044042500d61001e040e0800c00c00c60240c100714001641d00d506041d5841c0d45110380704600305000100004449030508040000550fa40d458a80c1603e902100e00340c20b200300700946481181d03120326143e0b0013070b80004070740051054820f0814125074213503000344a8102c00c00001760701c901d0030113030080104485a006000c1d41e80500c0744c0011400c2580120b0742448058a088100c10041800da440032440c0000e40030001513051001d6030250030365003400d1080600d070120060440c0705046041301c5145480c00820507070382c4510100c800d1140c0003001c8805164072031415218004400c0d1089002c0380040b910048800b03280340b501c13020000c080c100100b0381d81e940c40d501e5940b13034080b190100400c048011660070540001414401604140c50000381034002c43c42d140c1c0c00c8a0f07225400c442820031040344025110305 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 425127500 1250 425126250 425126257
    0x20a0f0204021e0a0c150c0806060d0902060f0406170408040b160213050609070e0a0504270f1203060e06150c03040803030f13020117060607060501180f11 68
    0x14150340041c0e44143c02543c0006154141d16840c040401c000f51002203940d016030241c14060040e070140252082522036181215098104a40800c501a00140181c500b0401518003d1800300001c01e281660780c5c00034540703911104020341544004241401010307409000034510106010904a03a403c094a60b90014000d0f880342803120840010b454007146071040100040b0b66014000f0030020800050100141c40110342c020b0040d104140040c2240b03200780480d101c1400e0140440d41c2c085d043c1001e00c0003408903400721040b850b584580344400018455440d26109018000303102c0c107180c0520300f000c1d0300c184109060b400c26081c00002d200c46004c003000c3d1908034a0440728105031507514007800700c450145055402c850700001c03a0004000d0320100003907101d240ca100c903910302682e842d82d41040d00c070410301019001901c0080f5454180074000c0066811100040203d03080c00d100350b070340e0010768400342c22030211200000c3e52403400d6035840c0038444c1c00104150080c8580c2c5084d030400c280502 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 425128750 1250 425127500 425127503
    0xb0a0306050a0e060613090204060e010803031f180504020406120f030807031103010509100302040606050c060624070f150b03010e0a0201020d0e06120720010b1309050313081c020a0f 80
    0x9589247d008110743c1d55600c10300c008c0c900c0e040d45500540e0f50307010050b1aa0801c492a00c02c0c196108015030030030091500440641b04102840001c0d030600c1c102c058001c0c40c00030f0080380c2156803900041140c0c41c8105000701da027449802c4018903050b42e0301c0c0040011001410304014181480a0041c0b04000041071303a042d5030003a50007041c281e440800c0d82a0b10340d4a9403000c2e4015207050004100301f0340c404020044c0f800c07581c084a50b1500c42000f44001042200d103a4201018203d2510342101c09001c01002a24000c00c1c0b039514904442d10351650380004800e124404503a1400c803403509085c203004040a600550000e01443c130110f0700041d440c3e000821489040040d1000da2016980e2018140c42c1c0d202420ba412400c43d2a000310040c0124040f03c940396145481502034460324807050194040b1440040c15088855054030195800740c00040c0e400c4691340030502000920700c045511090060010200404030103080c0240d082d0111003160b513420454101041050110701ea5030391010b0502d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 425130000 1250 425128750 425128789
    0x60901090b0423091506060f130b0f0405012a26030a23090322080609010902010e030109020f06180d080d06060305090d120b0a0306050a0e0606 63
    0x71514000000c00818a460019078000d64284188250380182849584144401c4c030454450051003007600420075011180f0580c4680204480d40c000c2501d50042c2013802610810203e03030f562548001e20142d007000101000410000c10100001d42e40559601c0c0d201c146103121114624001035a449400380b84e0720054050b4010700e40c0f08000010003128004883c2010030762580300e0810000e1840500016107520303480c0c00603011048000c4c910030303210f94000d040141c01107152159081424803a400380ea09011016004404001004103051204522500c3c186000150014a13403001401c04044885000d020f60b1504078503a00503114021410760001d0210b5401d5110052014032168140005070030316003028841e1091400c0000c1403002d01004101141c043c00401c0d1503e00481c00c031082241e02c11050303801810300101203402403400740b9040045540c081400d04444021a13041c14483c0d10454401da514810044481d401d48a441170242c1c521014041d0b908141c00002c146005000002204 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 425131250 1250 425130000 425130011
    0x904020102030906130302040b40020d1509180b060609030102040e0702060c0a09030b180f0304080f07030305030f1905011212030e1027140706030506090109 69
    0x1968002c00030382d1140c0c44000c08055650031030b525044082202448100c1c000c60030101c1f00007503460300c1c480395035078051194001c052119905d00c0d501840900f040030f00c480032640d083da4418a40344c1d8001808401d065072000f003605074603070441c46003031000c5610580525142c143d5410703490120459421800e600320f409a40c003615a440024054441c81c003103598551310000380040c1e03511920040078450741054094070f110b40d0b50750031092414030030701029000280b074000d0107000081c0341c10807294000060940828034904510402443e02c440c0b0010030140d68070110f010880b500042006109280f100340c0680f022520750f5074042d01a00010f4200080c01072070400050071225046500325010900700024441540d440035040440c0c15003060550348501c02e4040410860302900480c2c1c45a10b98200401e00c00d002d079046c5400500007914502c100f0f01c02c1410400210000046884405009010034540303099108410707440c115450303110000b4035080c4020040580d07943d40900d811070380e074020040b91 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 425132500 1250 425131250 425131253
    0xb03220b0c040320101110060321031413030309060507031b110303070e1216170f07090b04020c061e180604060f060e15040f020c0307060207020a080d0815040c0e0904 73
    0x11b0072040201110304a191070800801d01c41c0062805141c91103540582d40510b94244080b01030314042e040f03540c0cc0e03214110224921402404203468501d0003441d00142c86801d980d04d480a03213400303680200000c0c0e00c4078010607120007110150310b14001c003401d24843c0218004841c0340c0724000109204244000c00d1904003280e150180350032042d142160540302c2c00ca0304203042010790304030742c000c0c90341c1c1c65000005403c0c0300500090301581c10150710010000c0f03903d40000c1074042c20484028640090f000d001d41c51412100b0040d150213001c40340c424404602c3c1a5007546c00c02d00c4010aa01040e0007000c01e00040342c24042000b94005401c604041000030030072000002505142e48102040e65800d001c0002c049800c276800240e103c800c403800e02c40e900c2400f00d88000d07401060034250f030700c3c0c04c2048031000060303540e8002c0c4500345c405004030191680d00d00c112401d000c080031f400c1000c0384d0500d040143d203912501e0440788403201100c3c02c04c030512a040008000da2203050324035001b0220107003c40e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 425133750 1250 425132500 425132503
    0x201230c0403080706020c10060806041719030501150f1e052a150105011b110307030302030a030e0a0b0103061d030a02030c0f070b03220b0c0403201011 67
    0x8002e1604020a940d0781c400d00c1c600080250701840311000c00f070244c00504c201e04005401514100c0d0b85001c02840d1985550312405a0003c001d0402d2407540301c20400e01c84200312022010150007040c0c0c84c001000c0d031400c0040d500f080244c8410508000102c030440c0c0303440350031242a441d0806c800700341143c0f1415582c000d5805119061858660a011380c0c140900f480d0104e40d0710382d043c5804000d64445011007000141610000e02815010680558204218507502561685c5d603d015401d8260040c0084010170704019494000350016000003408802141d018014406040c4e1510010b00001003aa01c1c1d000102c141800000c0c10303942c560044c0c1d640d00c0f1108a1981183c84500c00381c03607840c1041403007c1e41e00e030300c900310b040401d0242c19490850744502191035804c659010500380d1070750341ca88001ba60b4100742c120345540f18031416044100800c07100741103603200c2c014900ca4035079101d0442c20209000d0600c04880110140483c03505d81140d00c0744200d896618401c0d04120760419001c81469 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 425135000 1250 425133750 425133757
    0x150215010b07080319020909040b01051c030e190b07030807140702010c03050f0c0d020303101421031e0417011e0b01020c1201060e061504050f06070b04050c01020c010201230c 77
    0x4541c46208c050900040c0000c4002160482c0c4048608664000041342411017450203241c0c058041091855007407a507040544ca071000c0034441030440c054450720382c110428550400c50b0140c0014074804108290207400c22846d0003804020f100f01c80c1010800e0b4002001410520001403c0001c04112115500c10040907900307005207c40c2a90f40703800403c80025030329002241c2d5440000004080050460051b43e02d22440401c09400340140b4404c0c40703060038140303810400d9403601e0f00c41040340d85a5400c3d80b24100b42c82007030310140c0c2907903185455846c0210030b030045006c01c0c10f039241c00d0f94120341c0c00240d0200201040042408200d000d03042c0c00603400c1a031820501900084521006400200e040d0b02c048140c641c00d1424040d541c80e14018003000c1d002c80030b10742c0d0784100c2c100b009001614112088040b2508001c001c0f5140c98110b0340c0d0040185401d8404a500742d10243c40e40d9807940c2c050201410b4808288000c1007d0715040305c02c030601700d0660600c0544202c0c0301003c984000104002c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 425136250 1250 425135000 425135017
    0xc182a07050a05060c0a020a08030405121602010e040c0516051e01091406090601060c080405060a0f090b090604090b130c0c1407050612070306150215010b0708031902 73
    0xa1900d400301418015152003845000b00c4481c0100c000040f00e00c0d44410543c2c41e990302c075038010048048195625501c550004d8801d0701c40d80f08070000e01e6600c2104070000c0c4410704c0309400954003400c072840054420305210041c1e9100d1414800c6c40008190f01a090b514500310844d40300c01549000e080807410825010701c0d42120001101c030440c02480150030800c41039100f4124a07400240c1d417801141c80c0d4005071058030044e00075100400c4003922840c2c000003054081c0700c07100e29055a0320b000a0b00c0d58031081e1140c0108040000322040c8582003c0c00100500d100550141751a00d2040040c00d10700c164002d401e22141d0f1025641c800391602c030340001100c0e11384d803003c010382807807514040c014040f040300c1140c4e454140c15000401e00c0010801104541c80540107506090104410722003a00000700fa0004240c1d907410002141410f84a2004c0401d903603402034006900e0904080820b01416000340c024160208400000034900100300c80e80000d444100c00728411144402e10043d1158a46 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 425137500 1250 425136250 425136331
    0xe0a050a1412030a0c1424190b091803160c0e011406070f1b031202071a180315010b1306180510050702030a140c18 51
    0x10105074011155107070304018104880c10310061010040c1c26980340b10300e508010003d001c2001d00e20004e54a0320b41d00001450081c10f5484660485030318000c640b1030055402020710344d107024001520040b04450103581c91569090200c40d00040100311162000360800c04014082c2680300d40d03021301441915103858103503500070000d003801d0034000c4800000e4010981c11014100002400144080d8103124180000d401107082802030388602d0240030100038151000d90320f03084605004202260b176035000d5440380e0a41c140d91a6965070080c41e00445812200b0000c3c14030407002502031040c01518403480d01c0300348070203c0798940404170f81441404510a2000801d040010690030400409080c01401710302d40e07400da10b07540c0d140450b204d034417034541440983c0484c0020300c014144916101c0d881c11036030500600c0d013001a03000c1392504c80c0c120419280580441c0640c0082700c028840400200300c11608588803185c0c000c8003101c100d00203010200e180e2030555400c007000100801d0764440322141417 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 425138750 1250 425137500 425137519
    0x230901060f091a1903030c060b040f090308060a0501020a0209180a03050702100f0e0f0f1002010506030111041503150312021006050405130f0809030f07080d020604120e0a05 76
    0x888072000f41c00c40c002d00110400c54426969403d040040d4001e941c1c0300c1950240078540c0c03541d141500c106042600a646841e110111442141c8581c0030341c181d41801c0580c0020700ba011401c2c020030744400070f8601e62052145d940c04100030f07a40051441c3d11640c0490342c0085981702c80140b04201980f1581e080318074002d88520906050b040301c081e010080c02910001500c100e001070413240c11240c2e5071640041560590080746c00d040950a07102040303009411810020600e400003801040040c0800e0700607134507042004100d040038001c80d25610405150f150400f07040000d843c0e09928520b10701c3d41090b641340003040e006040d00310614000c41c0c100035040000c40e441d0300020744882008440b0200c190400b000088c0b9400e00e803190741c0c403d080704291500d10102544e19800310130301d000025071b0050024064005269014000840c000076008002c0035400c2c40c00c2003540c2000d50390890001990492400c110104449204c080b0a40da1189440756000203118009001c1c10030680280d90004840c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 425140000 1250 425138750 425138759
    0x50c0d0510080f0106052224170606011709070e1303110a150c0c0804121e020303090108090a0f05030406090b040b0f0f0417031c230901060f 62
    0x3400355006407202c880c2907880550324064a01e00b650324510503150019005e00701c06c031343c1a00440c00505520944103003c506105504a0005245032110041c0034540003603a040002a0040d0054502210418050304080c5400700000e450640c410b2070501c5072608140004020b4901401650054014045904014149101007030200641c64504030007048214104283e2b410000500883c00c5901c03800c4c420031140740c00d102c0300140460741c0849090002041d0b80c040000d00341c001a00c05440950803618005015007080440c0c404502107000c1030600204031070016880200460b0580d131400e0030803c4c4191510005c407482c00152500141900488140d04800c0010200040080b06d02070390b100c601c0252517180303058a510542c0305401c03640408000689030206460081d1850710000300a5a0a00b5583c0308000c2e802042d900034446160000103681c49008104003130b50390803c425140802035030080c010704421004031100c018140141040002d26032007030940040b4081c0c124000610801c90741e6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 425141250 1250 425140000 425140021
    0x403120302030703050a182006030109020702100507030c020603060a080303070f0801060e01080a1d07030602120a0204050306071202160528030503070807030f02070b0711010509070504050c0d05 85
    0x3e640000000c0c0c100404640b4921040c051a40c0f50080d100d040301706407405984140300f50800f201c0d00c401c0c240c110490745130300e561002d001c2c0d40202510381000d81d0704c000b141b041003c0102040c425a092007814000d40c004290310016901119905640c40c1341d903910761a00081c5c002c05070358001c0840d44800410000301c0360340b02042102001c0d40ea00da01c800d0383d0703c501080d03802002445a0a0002d0b41000005910f030303115800a80e400000c0704401034119070114822414294103030400e56040b900059100d103406610200d45900c603408200c01c5041c02c5c10715001944460001c0c042c01c0c10400305000c0c2c07a106031300560403141c191010500300c2a4a0b030b068644662070380b00801c818202202900040840c104030125900c0380c00d0362641e6000d246603200c000540e06000040c06201c10183d0712651510360329102c0c030040c01c5041c000d0040f480545003104009001000311150640d15074101014098800d03400229641070300c1084402140540e1882c5d070004490060060090503d8100340611144611 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 425142500 1250 425141250 425141257
    0x708070804050622060806151303050304080f0f01050c0406030b010207180903080610300203010b09030c0d0309140d0c030b06090c0a0c020d060f061403010e06090d0309080403120302 80
    0x80c185004801565070f05d0f0155178000c822204983c00c8a034105144010880c008010a04000343e180340c0c2420741c0d101d0301c4a5203150400d801201d03182c0c0c003450340749810890030081109003001200003800149004065456240514401e15080c140c4a42e07100b42581e00030701c4038074054031080c03450111801900036800301510101c1402d40c042451280403c030141840300b5045103c9104d03440c0c0c034030b00d01100c0c0d10752004110400c0340b400e1905a005020444140305c2e000843c003c126000459860301928410076050400c00d1408610030b207030403840701380001c0e08044480101c8000c2d00740424160568008210306508400340148210301300c80c404820003c403884518001c150903103280c0b801d0340e1081742801407442030701851400f142e05001a00300502d42256585a414402e241c04039452054044210a8a400307410800551844950001160400340f26446240343c4010003401541442c010300360712940c4000403101010b40b0f0b0301640080c4220807003164011540440d00b280e140105800c018006e42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 425143750 1250 425142500 425142547
    0x2b1b031e0e0a05030105062404030b070305040303140402101d1915082224140901021e07020607021003020706050a0905030a080601020c100903050f0f0307080708040506 74
    0x214001140c3d9080501c100c511500000e0004803011000b801c02c080901504009008003020400011000444404002d0301a440544000c103141c101841d001d000d6407016174a060b502c2241a0400016aa5208a42044517a50b040405d241391040c06011005400710306441d030003103409500079808114010300002251084070401d182c141c0e440e0421078680906854038403410302e040072003102140700300100550092040d0b5442d0216800446c1045280381580050904282e5640d141301600141005c5154071a240ca002149000d40614040f803002c03034440c4099491001c040b40e0304046480b4441214031513600244102d2204000d003800401940c44110701b11031443c00e00780415422290340c09001c000d158400041c5041585051040f120640010f0005046104551001440381c54003d00c040203c060755079280031040c04d40c140640ba244240201b030041350300012496030542804402c2d6400250f00c00c00e0380c4d6030340500d410032841c40c0c0520341100d80c1c00f1000150021a51084511040790103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 425145000 1250 425143750 425143759
    0x31805070801050c0313170714010504060507030509100504081308030a03150f1523090f030601120f08070605010611150708010b090a090c022b1b031e0e 67
    0x3652013000c111030360300080d64100e43ea400001c1c900700001ea0907480009000030900300d01424290b06403640d40d1801c005281880469641d4030500c024003e681c010186d01451a041c242300714140504115910008246c86008069540011804200030541102c407180754140384e07019030715255858980c0381c5d40f200b2090404a40340182c0d107003d2640c4c050290044030101702c4072410076440d0040500d40c00d800c1e00520010040406080b417403800211800022101034080220348401c00d00090024100f03060803200e10950007900104041d00001200888240d404020302d86030380c10034984413030709000e000b9001701581d040000218030250301c40f070f180d00384800843c01c440c0701d801010760400d06503000b51180d0b00040c82450041c048a003d500c01012481d070003820910405540318007440c03c9070f0303a00c1c0008005030040d03018200c449440140b10100d01042003141440b2915105018040c24510501c04036018218807e083c02d16003c3c0301c14000e03004e41009001083c3c444860f00500d044603003200c01e84a03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 425146250 1250 425145000 425145011
    0xc01090f08030304060b0d02030a0c150e0d08090d0b040b070906030e06181908040f1e1401030209030d080405010c0e090411031614030c1f0f031805070801 68
    0x40d86814084104598040300518030316103a9071a8480604084c0d903401c4d400061840d83c0000680b001c0003d602035034014034141d0300c658286000480014001e0034403c0400000a03050200c0740c0d61400d8505030150b001030b04c1c980e40c05031030010502a1048903c05454400d60300208070a01c0341c00e10b0403620548060b641d0790b4156444180c182c04440414000485d541c0c05100040c8090031034018419440000302c0c100c0d610682004aa00c0071400050030448180d00040713810002c03449055101c802900c554503d044001d4580104903080e040140f20350115820304c0312400085074040c0e8103c4803a443c024003034407000300d0310300000b91a845054908642a41c40c09041400d006d10070b1403c03a4041c0c40052440301107485548902500c2c00c2d000f480d80d42d00d0300585181000340703015040080000c0810900d06500652550100741c101280c03034290600618400c0d480130201110106411140900350800901010315294100c005003c05d001020380e440001d4444c2042c44000070f00c0c00c080301d02c0100203001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 425147500 1250 425146250 425146259
    0x51e130501050307060c1119052e0212030406150302060a02010207030e01080108070501080a1407020601090b0d15020d1d010914070b1b150a0606030b010c0b06130e010e0c0109 77
    0x30b101d406c000000d000104000402e0f580c0345031049202904104110440c032946450b0000281e680a6400041c640c05e000344501c08003a04c0e9030403c000088a140c0043d04101c140c0c290000090300c002400104003a03034807000794807400b41041d65040550f0700580565103412125601078002d50151205402081003140303070100d80e40c8102c0718517058a400501802030245054015204544041d040071400c035240c0d64519020540183c1e403d102c2c5c4103550052440c0e524001d2420111134610343c1107405464400f40705030200d25031a412200d1000c003039100503500d200003070541c00142010480e240c0a00c2010035607003c2090305401c011907e6010f4040700ca040201075550170b44d504814820100750b14018420807200c04a28600000003070181415100c6980e5000000c003140340c130403603000d0402799440400340080c540c140f182d00c40100c001e00703007007040b181c060711030f01d8100c0d000429140c0b0034100c0c2d400b04018103003241c0000103080b1411009106400c3d10507152511030186461305030015004040008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 425148750 1250 425147500 425147507
    0x30d0b011205040804060c0302030904090c0303270e04020d0b01030305030a0b0a0e18100504030215090f0a2303040f030b0f04080304020418050604030c060507030204050a051e13050105030706 84
    0xf4080c42d44104113070b140c20315152042c0d4084c81c0c1d0100a03010350005201003401c5407035500500882c2441002c900501d00d0652030050460000c0b40d200250310b0414070b20514141d00448805000d07504001e8207000c80e5a0390f0301c00030340c010130180401410036504100000805820a010303500800c0b4100d828455110a00148880c0390340d40d2050702650074142c1c0c0860600b1307040003038800070811103000741e4901d058100c48010585909550407801a40050f40200704880255550f03a042800c41c40640f51001c0c003419165600c0b90007640c080d04c548001900b8003900d04021035030000021016090b20340b156039414065448918034070060300c0d88030401000071010700301e002415100d907501000040c256240e9400340f000400440603030143d03081f09200000c0200e0b20402c1028071a51013960b07012030058140c0740001c20f85001408200078580140000d120715680c05032084107a07841500d2030901090518880442c845403e074100350480ca0a141d01d00310001e45400a6042c1c070010ba0803242040c0d03441da400ca = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 425150000 1250 425148750 425148761
    0x61b0201020601030618080f0304031404080a0228090f0608010c08010303050c032116021906021e032a0304080403080d0e0607021612030206010e1305030d0b0112 71
    0x203006030007030030061000a110781e021141144105800c182014001d0362005480d910a004090395090080208010160700601c2c5440803041064031034103080c40d045a0340c0d43e40301c10080080c810118511400c155100201c0390b160800c050a0820070800d941d440a10000c12030124002580343c00c00c03c0c042840c040c14007035484001403030b039907141050380795840c100c4594100c000b46407a50300040045846000c440a41c541c4041c01100400b045414906000d4002c0c46104903010250b402500078586030381043d00206001c02d030040002350361604820510400400410310b00e0500714408030074044100d2919815900805141010890041080b608810203000458009000d0501000240001340082c0c0207058400300310302d07021a031480081d00c9181070070b408464013070041e4480e410050840444807080401040b142004540e008242e0701e0084d00d4100c140540140e91000e00041801042c0c80ca00041c2981d4000e8252500c07520300000030b002030b0000502c80c900207804c03802c08a4221200748140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 425151250 1250 425150000 425150003
    0x90108060c070804031b0e09010c02030f0a030b040507020f060f060d2d20010809060a05090f06070504062a0209060a0b0304050a1a16030b0d02040c0306061b 69
    0x381016581c26003404000e600c5020110381c0080248000000181c0c2004250103070410403a04090250a01d4500d0850040050103e0544da061102a030f02d5141c0200803190b0310001d803280c090b69000681d0050380913012419581c2e80040c5004104a181580410181c0c0c900e02c1000c181c07192921483c0741a000c0c440156560382d48010480a044001640300ca5054810148281c120b2040e4800c140807102c02500190300351000c21a0f14844071014251001c0c03c0e86440c0700342401c407418140400d00703641d2107074001c1c00700c107e6503a82c1002c214600400c1001e100b08660003403c442d1186000071000b00b80390010711901000c205034000160014100c914641c8060540804912011095400300200018041d040c2c1e60401224500407420009840041d0f20690050004001c003c1586c42c00001082e840519030085203030303000c1132003c105400320b40c01545508500e004604101c94034005240c00c14100030080d84640340560380410150590441c40c11034030340e0344403c11000340c0c1e101c4070980a07030300400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 425152500 1250 425151250 425151253
    0x100302031905061303030e010c0f020705030a0308040f060608030705010e070906060e0d241e050105060403140c180604051f03060f3c0b1305060d0804060c11090108 72
    0x403600200c513141e141d1800e010380380200750748580340c4001f800c54000101d01000109070000d198081a01042140c1c0104002c0d0f004014120369901d0040003128040c000030244d21100f80c803071041c00660307041400584003190640369910440c3c03030300350f008040d071200c5a45540103011000402c040a0702c22441110000d03181e03803000a4581e805c002c100c40380780900b1102d50440c0c80c207100c00518a5405848040103030358000542001c6c29003000070070503c5100d040ea20f941041c00500854880c6800d540440340e0100003104084c1418400074282602424259080035001d0401010304800d001101d0003000241d40802140c2c88130303800b001042e980f01c1881c0501000900d0b0070000100150301900100000000c00511410b03880007a00c1d042200b6400000480c0c60032401c0380890b5940b007402c8034910403540d0100000744920002c0354000c4160b034880400c0f503540b480040c0d10790f120313a641c4400040c0d0210781c5a0742d032526010003819205c00441c0c191a0440001c1108600342442c5030810b059440260 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 425153750 1250 425152500 425152513
    0x1a010603110403020a031506080f030a03050906011410051c0605090a0e0d11190c03031202041a0706150f150809060a09030507060906020d0e010b0f060d0b030303100302031905 77
    0x881c0c101e04008003a000d018074903a523220002d841e0310705024421150f04900080c60b40c4641d4101700405540300500701043c10b41158004100c8540d20a803103601089081c3c0b0800c441001d0030905803124000d81c5441015480003114034181203046510039810b850382118403070300c01e480b00140030b02201d00101d0041a1135000030b00211f50703107000740c1d6418100d00c007203821901034100c1100b01c4101d14020030012500c01e40204000e0080680100001920001150045003417501e880c2c0343d10000c0074007081802044c0c00025245044c0800d07600700401c0c0e01006110415003a5583c070441c08601c0340c922400a4140d0460848000030780300750425806694008000c1407144c0358040b415000300104001142407180401125000900034041c00882c0d502440740103844002480104060300d8442c003906000f41d144c425025030a0341d0b1780008400004050b100607032520000c43e28070009010325220b00ba414400803081109202c00842c19a040e2482681664606080d4090340b038072010700060700500581192 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 425155000 1250 425153750 425153753
    0x18060c0b0601123801080411010315081e0d0302070b15010c0b0702060708070906230d09050304080c01112806020703020f06060a180e07031a010603110403020a03 71
    0x900b40000c1801c0c0b19000041e211044910058801e9480b107100500c440a0020440403521305100a400503802030828000c146400d03a91201214240509507040c16a00d00008003422007203458100907006d60300845420940c0c000c030290340d80071000d440445511440b001144914480c0c000d48002c5503200442b6130464503407924520301e10000161050401c80100e25400204590a0140e8020749203900540046d017805000103100540c014001800e02070104010041c413540b10200824448405143c21408038800014070264410400304a807024280f1a002051110210080c002c68418404840c10f44051000640e0b007901e007441e060306030b074101c10f0120b00081c0342203070500c08071007840242c2c1c040c4540b5580c0e03041c04ca0700100d50030750051b8040300d81110044810003849805c54400c54400180074a45005110814403000120010782e80740d003040380f581d42080110a025550242c0d84400158480401c41c1c40340800740f02e01800641420154541c400d9a0002c81d02079a40103000440041e003076 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 425156250 1250 425155000 425155007
    0x2090607030e191d06061603120902090a020c01060909020f09091216020117040b011205071208090312070c0b210a050a0e0c030604110d06050718060c0b0601 69
    0x105054a0707005611000b0381804490a0183d807005041ca808208000346414001262689001041103004800070441c0484039644001c0c600c200340d615180c15604400d02c040b402c8090503400b10003c2d000141c40052040800c21034014000d042d013014000c2240d0b9548000b2a000e640c03041502035003151103940d62120a040c0540e05c203500c001428215440e50310340d078507180440d40c4912501d400064000c1c400304d00315a03101e181d0744516a08421884428181a1a581e15600c010b10440c40c2d00b500c054030102c03c0140c10311500b002130451340d4040c0c0407005c003414010103a50000040a21070300841e110400f645284c201940c44a54201c2c030303801012400c00a01031525400003040390301001e600e48140c041c40f1941c00409104001d41040410181400150718065070a4001c01d041c070b0303170080c0452040716200000d8256025810140904074140400041811201c2c1610b016054a0074030081200d800d4105030507403240211601544210342c0d940c441200d80d442003601c0140b02883c0c100c0400c21541c031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 425157500 1250 425156250 425156267
    0x10e040303020703090810020a0311070236100f080607020d030b0a23011202271207090b0a2c0408040503160504060506090108010b0a030f05010303080402090a0209060703 75
    0x102e402d002c985d80d51500515850300c440d4140c090481e07500040d4000786141c0c035000301c0616042d0a00c1c0d040c10710080d0760006545103a0800c0c1c1c1c0c0050341860100445024540208085503850710034080607904181c5440d4490b09100c2c024090300c460201c0b40002d0b0000c0010300644584165405083c1742006d0b2001200034040308000294000100704000c5a05201c0c0c40101041c6e400052100141d01070b480d0015094200031000e0303961051052007242a8508041ca884030858180d04014880b002c24200040d8070481d02581e440d450f00c500c010100d4110304030fa00100900004640c0c0e800100e60710500502e00300a001c1c10f0000001d20030340324241000d6146100c43d0444d208881d10790a041d00c880c0400c5c9001d14042c0c0d25025095091070030040b40c01c2610030940905826904249418000000031b040101e041c81401002500003a80302030042c860f070f00291610048503400d02c108d507500d0800500c0300d00192030030b0f44205140380c04600c1206551084600b80c600c0036104a0134804075481c26544d506 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 425158750 1250 425157500 425157503
    0x528020c0a0c08010c0e0420071b182009010c03020c06030a02040611030f22091409060a0b1c02120d0f1101050613050a2009030c010206010e0403030207 67
    0x4201c0e030805000601c403014800103805084000503110195080041108071001c1d41540918a006c084042400e01c01e10321150288208440c1642e800707441ca00040041c0c0c2d170410080c01d6050b050000b10300490501c060740c00f400350014050106d203840110403840010965042880c003030042002e0981540540d107018281c50080c015500031100c080701040180c0d20880d04116031650028060203840d81003c00d01e80c1d0485c0150040d4148989005226800d204100c0704021101d0796018010000700c600054a002d080f10050034854140e50b0460105109801ea6a8043e0341c010440081d0768250140304002501310300502000d407800907190b9001c1e0070703444600281c1c0c01043c0d02e903d03d4046842080405410512030760b0720780d145044a04000e128a1401d5071100142e4101814000c46036260840342a04400c2d5a400180c55110500148002d15402540041d018243c0d4650070f143d14900b00544040d40c410340a969040c482d1800481e103e880034081d05010060f07405c00714010901c03a501612159 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 425160000 1250 425158750 425158753
    0x3080a2c0c09160f080105030a03031d03040305010522020a09021e0403140c0603040c0501031a03010e060a0f06030308040b040206040e040506042108040f08040b070b0a0528020c 78
    0x3040031000b0842400c4101d441c510103a5104440b20921548109441d19005441c0707004450755040000103925030070b88020240030540c0300c481d041040006607100d0540071551908603591681c1d61303e00740c2d010300f50449aa05000d0030a500d0030290414011407812550b50040c1115012414255510020f4100c030b0035403c07000800481e001401e04170f410051028600881a84415080e413803542c5e45040300320f008280c0620f40c14003d01000808141c042c00580b102400c3c041540e544802d4420007842220056950542c28803043c1c29295070045000b5015605c032040c24002070500c00c00260564000344402800501d0600004001c501c06e050749680041c8000c2c0460305d8290f991410000307880f406c1d54180c449030032203c24441004124441c02d140b00000e0b0b5100c0248918800019042c43d0000704007502c1c42e009108050100721940d01102c0250a82c0ba030220340343c90346400e04a42200085524620f814175050100c1c10b9034112524252080803042d03090049000d8020380d00010f90000d10305075005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 425161250 1250 425160000 425160013
    0xc030a0819060b0702120a020102061b090621010504110904091a010b030106081f030b0603011415130209090711070f090f0c030b1309030e060304050a03080a2c 70
    0x48807078070301880c40200b860032465134403200b0302c1c01008544200d26141506c1548070032401e20041c1d8011074515840200035080d03e1114004440141d500e120322400d03980d025000086400041c060b0550030010080445d40c000d04580e02c0740240001c403090180c940300c4c4800144006446031416800c5205264814058003800c1090201e5071140f0354401e0f0002160010080010300880b90303c01105548005075200301c5604040c14000402400600d0001401d0340b070700400001e007940c40940080d241c03a0040d502480c0700c1d1500c5d07911000320341c42c8150b8880c803030a54401041a03a650a0003583c900c2d400003029002c6170b41b10804190b8106026203c14811030060640004055002414450003491181e0002c5861001d00c612401200d0310358808500741071402108080e00e4a5007902003484002c9814001007403025800c0036a840030030f003049264040c5000041000700100441d02c04100c034429200d8211a031100c044810030b540d5103805c5814201030b042c16607801c01107103652503220401d069054805 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 425162500 1250 425161250 425161291
    0x150a05040903090602061302100302030c1b01061e08071e0b0304030c021318110103020409091a010b030903030c1602040c0314010b0c060c130b07030306080c04020c030a08 75
    0x1034070381d4080c040e00801c2c103e840410021350180029a03204903003c03007000102c1150f600260109c480300544030101903001c03000404510703c201c100c03154907505140360403003120b1000846019201c1030141d5440000060b2605600000c004481c0003a200d41101400726541040c50120248100c07204000341031515403000600c0d460703140d00840c0a1030103030f07540c40c410b020b540c01070046035128045001900741c42c221000070700028031100b4582203540041c011400c8145000100c010703020f550030001806d07141003260030410420080306040c0d180d040540204580c0d0324000c0440d2800100d4102c640c98100300000f030a40c0c140a0f000300788031541030780e040c5030909a68012030103c0b84200c0a000c0402d40c2d4042222085810025182c0100a0004d81d5850004d00290741c640b01d01010b018042240da0114103900358000d0407101d4030292141c00242c0780c55040034200200034046a2081d805640110401c0e07482ca420180202c03807140c60b50b54001c40c94041a840100d0343c1200042101c00c120741c14007a450f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 425163750 1250 425162500 425162509
    0x90302010e0d0836161202030303040f0c0f0905090d09031a0907170c040b09011202150706180308100e040f05100f200315210109030c050105100b03150a05 68
    0x50302d641d11680204000c0301183d172103803104803003908102400c00307a0b0402e900c0140e40010440354030503802007808000b41d2003443d00b0f41440042e504400509415200c020415a4443d03005030b206035081c10842c0d04110b0400029202d1260b0703030001a090744085c00c540c15100c3c0b1050189608100400200d5840665031040902440d000784042c43d800d070400011105240341900800c030030007c00316401d484c9549440684032500c101c01d00000d01a0108401201d03000b14903c090302c17107150308081e0a01c6440641c0f003480c024041119011004030b5800340104049a50807040e801c181c3e00c0d1000c0078280342c0c03130b0b5407948203115410306403c55180c455400510361034aa01c0c000d4440d0080f9048010483d44e40b4070b083d4600800d01c00744842d00244040c001c016500c00f2001c811300540600b918a907000ea0807101a03140d06c50f080d1030228071191b080803205d01c101030784084003204143c0100c00801c400d031521400074000740828442c070355096106201180151110040e0340d00e06840003044006d46030b69481c00704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 425165000 1250 425163750 425163841
    0xb03060d03050c01060312120e030a0f0e031603030810030b070c020d240c0315050118092a08040308060907020a0b0f04140a05120706060b0c01090302010e0d08 70
    0x44a907841f06951500d4003642010885220003481c0c40103210000c2484003c40d901c3c0190010941000350f540c0700800024065201092500c801900b13880040707a00428130101400c07184000c9001a441d900003c80346010f07000030000b41c2e0b078409400080e030740302c0a034101d900248030f0b0806e99002d0084416040010072544c120341e6000949050070203103060082007817040340c8040300320320149400d100040c2041c200381007101c0181c907024240019100140b0700c02c07030303000d02994108402d410300e80359070f03003108060080090f011500203054800960400245c00c45100b142603030000c011410300000720b100362410010346070703003d04c0d01d1040322802010b40d00c03814030328101500d48051484031070042c40f041c0006c503940703600c07464068002409081c40540e43c0079510b03801e85581c0d44081d80f000c0b5181042201c5074004400416007401c0700764980100212550003840c04000440c003640c038115100c40c24440c003240c0c842d41080c080e15407001d01e5942211020283c0900c81031b000d1042c6511214102d16441041c40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 425166250 1250 425165000 425165003
    0x903020106090b030706140d14090313170a0b1f121401090201020304090507031b03020909060f0a0b0903010f09080310080705150a1103041401090b040b03060d03050c010603 76
    0x414120b160900384411110101c03801c03030091700a210184400794000c01e0040c46e000340d5072441a07680b4a544245002004090364103590088a28140441388030000041c14442401400c03504800742d88150740450000780817401125074128a2280005c18204242d040c0d006c5c0c07103282080640c08070380c1c03110340514015412144840012104e5001031068061600d4100400007000b04100c00c41500042e66a005070300c100d542e000d40301c20020340301520136081048100f06002801c94228042d4401030069003110300c0e4140182d651400140700b61030315480341403441e5400760a4042e02c0b8140071560525504c501861a0590b40340c0304001d800c40b0417445620540780c0201005512420200314028007980c866000c045035501040c000e0215a031008418035811242d26081035544900200c04c2e48c018426084806180c0008140050380c5007a4003140c091b045403d1b81d407150342c6525900e5000d00350099000305c0300340c5c100c107000082050030300c100b041c48010300a00b002c0781000301c451400390a43c0c506420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 425167500 1250 425166250 425166253
    0x190c020718021801030513140d0e03010203010e0f040c03021e040c143c070b1305030a0e01020f0d050408010606110a170d1a0f04141f03080d1d030703090303050703050904090302 78
    0x80e007582142e110304d803008008ad08600943ca15407424688950b454000703003030118206801d00110701000035105090300103540c050943c090707120039101c1001e1001d440019060046c1d040c01481f00302c00784192030f5480c4c1e0341031b400318642c01c26a000c2491454145101107420700c51851800a901d10342d001683c007034900c4e802a05660383e8505078074124400034009007201841d44402224040010700110079192a041c492a02ca0a81180d0380d004034984101c00390744810702e00a03a0700316440c8a40c03200041c81511100c6009011850f40e5100880740e03407480007245466600300c0c2001c00009610031f02c0c10a80c07084000c0100d410302000c4401402210805070b03100713940070094a4540d080382401c076540c108001c003ca4041041c40e0340c000b801144a03900a020904922160a200080a1101440a01440d001030f401031310742885149000050003910021085022007804104428000004030358000d98583d881b1030000c1e282d99001c0e25030790403400b07048043c03282c18406401075445901c250841c00d0f00950 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 425168750 1250 425167500 425167513
    0x6180c0307020f06010617060402041d07030b0f090c18030d050c06010e0c07020d0c091107021206270715030f0c03020c030909190c02071802180103051314 68
    0x2003010f89000c01d1002468040d8210900400c0029003040451020b44041c481b071918540e03031000010000d110320b8110032815082d102c00084480c00c240140c40c4102d0880c0c5040200c041380004006404481030072140c1d000d05030354001141144080042c00c0384d221000c1100c14079600c050b0005c0d062200c4445040c0010384041190110024100020750042440051001150034400d5401210303200b01d00005e0700a0003404407003030410580303244010092150080410005104035023031085984480c1081e03100741c00d81075241c0384140c808900319000300c0c0c25038034180410300345d90a5420200300c41c003041201406a0380380050400001071a08044600390382d400075034021809510012109041502c004062060068114071180041154100300044840d60840d51ba14050141d43d51001181c03006401c5c10b1846000c0000c0c0c0024040003543c01d160172506840a8191a400407801a4090500c80402c40c3e102c0d1003140d40660300450700309048002c1403a4102d81500d0748030100c1ca150401001507031003030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 425170000 1250 425168750 425168761
    0xc12100f020307050d2a0e150a051b190303020a031805100e12070b090601120305041202030f0607050d1805060103060c11010c020304240801060806180c03 68
    0x910aa80d500085000210b08509020350020035a0041507030348041c0c165503000d5540c48000e807040510303c1160040c070303500c210700c41e0303d03401031a4403400c404030740c021100c1c1c2e10300c01240c505a406940c0c51415541c0d40600f0300c0d044084003864402d50a01d028460302401409100041d0000c40c2c40d0203c41c0280c90151343d444c0c02c0c50b4024100d600c01401081d0f2240a040180006200413034442c0c800100c10b40040749000c00da9200c6428501144041540a500090501c00704240d2565241c401c03101d10082d140c03140e99880000c0110b503411080140090010002881080107045080500c1c50014044610443d05440500d1800e2001e49131503002c81c401080071228404640075040c950070641100d00800c04141c0c0d110307550f801d01804001c081689a0351100c81c6984074180745c460000c660301c001d1040d41403250010b9102d034414010684510703030240c103c0080d0170a07001d03154032000f84e69a407803c1d00c3c1e01e00b0100b02c61580c0040d0905501070f118020080040600302000382c001d41c60807290070750320b0601 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 425171250 1250 425170000 425170033
    0xc0103091a15010801060e0d0209100e010801090b010503060c040b030717180c10020a060b040b0303041203031d1507030f15080d0c170711090405060a061e06030209030c12 75
    0x146e000c0410011450074842c010303291030015410803981039a90030003640391102c821646503400d4022040081365100002000f000540001650b1740c0100f01901040c0d88510505840300000c885e5142d103100d0030441003041158202c01140e00a036a46440080420080e415040c3e200044c1e03105510510200f030b200c1c00d404c8081c4a508030260040340d61460409943c01c0117900c440c031403040904684e58903d001641ca441e9504019a4400014180d80c0c4ea6502d84401802d4003041d81400d0b400070389481254500000b02003c1032400c00b032024000c204d4080e00750b21100d000100204a00201a1103202d1503c294503540150b21105a41c500c0c1501840c1c03c5c4001503150035481c254010401c400e003901400440d07a110421045440c855842e29915201800c00054110150320040d07003001e03040040200348000860ba0354001d0080641c02e2026036a2084003d03080b805030740c3c00c0c0407880803c00c410080503009034010000010081c0a40d040d112120300000d000e0415002e030030010b60001c2903061100b04c0b9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 425172500 1250 425171250 425171267
    0x2040905010902030f0745121a04210306050a08010617030a0912083006010309050c01120908070506070f0c0506360318090105030c0103091a1501 64
    0x6031443e1030101e4aa240b45a0fa82c0700034000c25a07c02101c0b944100c6420035884042c82c000c0d0180051800c1c0340f075039583c070329016032000c200d000e0300d0300c0700d401968882e04048017408900480d040900c03404000440c2d50f0702400d00c021856910300b4183d84140000d02c40c0c0307130049107500412890000150039842d01c00220602c4c941c0304804580c1d50410400c0520254101e0824400d90ba0300208100301c44100d850b10458134490b04032001030701d00348407203039043c6c02c1e001c40c0400e00501031850007190391b602d4510041d0144d9a20207002480781e084988001d02c154860140c00881d40300d82e803808102c000c080c0c2c80303510403a400361209030751a0f084071040040e100d810121980b0700340a01e03e00781c1900030305610740700c0d15000003078003044406c40d002034040c00030301c5841c8403403103000d010702e507500c2c0c4444000000c95541d51020b4200c604402100041c2c050300d1422103981812502d018001d800300100e840011070040c110391100719941580620303c3d407050141c0c410094416007401701c1705100102c0420001d00140b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 425173750 1250 425172500 425172511
    0xf02101509060f050a12050f0a05100e06070f030b031630080403110f040c0206060f03070e060f03030c0d0906091203050d0c2619020c030a1202040905010902030f 71
    0x3000e003002c010640b222041d06045940b00384036001b079424149429800e100b840304c21401c161103030412000071700c000030400060920b031102003006841032084455403600d0040b1f4020300072803401400210914065080700c8641040142950380b541c804105070380ca01c0a150700303e00c1006040d0030380c1c64031440a4001000340c0304c003019611010490036070b994030b04c103110b1804020082e035444e044002c0591258688080c1a02d002030052102c08050305e4025622041140da49204908010b01900d542c100803464000b514000c0403da40c0560b1960305000d4007515200d5216010b220030013034081d40388002d001810800350300b503482d500343c14a8030000620241c840d4004000c0d03603001070210070002e90010b0440d110700840381804a00c082d07040340241c8807505120002c0c0300104e00c240c1d543c81070402141348240706480c0400300140e403030001c1200318103d006004030000c650303000300005c0720064040c4540c60000b03009200091f29050302c5628401c1070f2802079110a0380030750003100b03001c070500c440c000844d07024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 425175000 1250 425173750 425173769
    0xe07030501031e02030a0204090809130e0a02010e0f042c03090d06051b0301081509060601020a020108090a1b08011a01021209042a091401020d0f0210150906 69
    0xa50550726402e0104020b8868403c034075a00d0720700c610854070b045c440d00c007036130380c00030400c110840082c00d104400da400681c1041c89489001c00c691007240d003034480c548400202000030705c0c1c2c00f411a401500e0030400c01c0902c0d6404092400c019074995100d008440e9109202408034455090010300d01c03022822540090781c254200780554075554681001d80c2c29019040030003c50030752250607084555401d0020350403407002c400400420402070005540310102410b07090021030b81c0e91002c0c802d48440c0b05403222801a0010054500990f21406110b900b200c0900e00b0fa401c48e808690b0780303c044484041c9401006a030124080000060a2041c165600c011200019608241000003500c03901703955520411300401040ca050f03c1e8441b94040718954442483ca1201103205e07505405400c0c140000c0312001961004002ca20a0b81c080f507020000d03201178004000076401c002082d80c0130340c00b2103403110841c0f04074034801c002060306008468050100080c1c80075076504001c00d40017542d80a41104205 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 425176250 1250 425175000 425175011
    0xf01021207051215040209030a0308060319050601050d170c16050102010e060105220213050f06040f06260711070603060b090f041e1b080103030c030e22060e0703 71
    0x2211418800141e200e400c1541138401c680043c000103000f4020100f0f0300b0b41501c03590080300c08240e008142180030311001c408a0f10160b0b00c0c101400191401110b000700719400010042145050005140d40700e907100d245040f803140e6480350701c580c69800140b4546c005a001056480c02e401200c182e19002d13260a1009009420b5555052607a454062242900a440a00d4060030b544000c000305007440c20600c81c10741d5150107006440d5001e2450780901842040c4c140c003002040c2c54044211400c035001c1d039079a680705501d442400d441c1c020f80c10301a9901e544c001e810b81d1109150500c00940300303803505c3d00d841c1000a001e000b01c1e842c2c01000d8002c1c2007494507014013804080901c0058034041c04044500540825241c0040b90143c030342500c2e14140e42040d102a10b40d40d01040d00490621a10001442840050888100c505000030f01c03003c2d01144028010300c02191040801c0a500403014040c040c200601c0d0862400d4004840610b6444c3c81d5501c0d800e00c071420002022039040395040c9418000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 425177500 1250 425176250 425176267
    0xa0314150904110d030e0301050a06050a03030806010c08040b03070201111e2805040305010b010311070816140c0102010e0703030806010f1206090204060f0906051b0f0f0102120705 79
    0x340320a08103886114a6079000080c00b040114008061090030141801d100101d5074070700540101c141c01c07030f0382d0303ca54205800181c403019a84261412214010418202149151415250580041c08007410020440358007004686910b00600080258201701e41d41d0b0b1070225002400c403500701040c41e02040c810805590b070792480c1300d102d030520403a00d9000c560310303900300020034030200c034100014100c2c83c0c41d03220400c4103503049005401181e009400030b100d8803428038011000ca4112030841c0c14010790610600c40820a180702400e02c1410402607004444429110901918516800d00c800c662012031401220350742802503456400229005003040d038210340c5d0141c0141001092917042201c800d0050340b603e88280d20300044140385110812a00c0e403542c0842010354428020b00300824094141c0900b4948580352207800c4071082d5441c181030502031070135071070a52140080740c101781c0324006100b0400001841034a0034007403820001a03450f54090342d03241010344001d214806100742440b0449 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 425178750 1250 425177500 425177521
    0x40b090c09011202071e17070317130f120e150409020f0415020705041103100b0d0b0310050f010501050f0307050304060603080a090306060b0f090d0c12080a0314 71
    0x280c100200f42003084001001c4120a0000c0c0549003000c0c06c800103041c02c828200b01e80460656589020340141e400340e1a070514100c0daa881055401400100703983c0c1500100650b1945a61300038451715560121000661030b60000e05c1500c230390a407600b0017410440e001e80c642102141c054014240c42c41c2d8446030b075a414802c0b15000e0342c4030b1008150f400041d5a49260701c03c10454001d0685000308000c05000c115000390380740c1d400c0c0030300307400f03240761041000003010341000344e9108508001c020850036082c05c510300d21a40280e80c7d041c1300b00d41c036004108000d90301409035107100200c00d0000030312480d0810082188520603841141400020010381d8441000342089035404110350a0042d0360761070324944100280803551002d02040d4010600a07912039001940e2004c0783d014200074805182c6074098a0500c4c4a2f40c840c041d0104c000300b01d5030649050214550f5901801040380c0540e0300e9070345000d42031803c0000b1003245d1501000900c81d16035600f51107200030800b004e0b8070396070a610b0000c0c8880c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 425179856 1106 425178750 425178757
    0x11030108071a090d0f0503211b0c060c16020604090914160e1005040c090914011a1e0a050d110a021e0a170306040b090c 53
    0x12010000b042a2144000010b040401c285081d940b1500b05000030032003115a4002407151501009558040c07001da01c545600c40c5005103011200113125025070040b903000914180b05509200c20000740d4540d012402c0080c16030b0f02c031420101d5044110001000030740c81a030000d00460107070381c070f40c0120b00130900c00e8025114503141032074070a8550b0f0501c520b00d000c0c41d90401d01000084c082c840155044600c00c220341c1c1400f0b0312030020a0035141071100012c0424541c6e80208860300541c80b60381c1f1508a1142407051a5040c0001c090b6194000240025420000b04516404440031420060000070650102e69281c0b0112005000d941003001310424552a080344101c0c59400380d021200c0002a5a011b003401e0745080300b20700340200507420035500702d200380c611400c0020781c011440306541a501c250580c03a89400c200700310940341d290ba00c05010b40c2d506030902c094800583e080c1d = true := by decide +kernel

theorem cover : BRFrame.Cov 425000000 425179856 := by
  have h0 := BRFrame.cov_init 425000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 425000000 ≤ n) (h2 : n < 425179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
