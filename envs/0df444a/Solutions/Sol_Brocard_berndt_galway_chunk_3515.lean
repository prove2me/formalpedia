-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3515
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:53:19.123396+00:00
-- url     : https://prove2.me/submissions/15c8f22e-33e1-443f-bb2c-443bdfd87dc8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 632014388 ≤ n < 632194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 632015638 1250 632014388 632014399
    0xc1c09080610031203022d070804230a0b03010e0a1b0f020d0306061e02031e0408241303091203020c04050112020108160228060506061602130902 64
    0x14070304402c51a2507983c0c00140c5030003a2895a90000c0b40c042e2007110b03074054080d1130498850a40541c003400418001000d036224000070400100041c488500901c0503050b0200c16807501982003010500007102a4002d0340500d4082d52705002e103000f070505903030441d00d002404010955465902402602e080303075210040181d010841c1c0402504006103051008943d800c40b203a0350794042e4114155081c9100c0c610228441024440d440d01003914090744407511401201d1800b42503520701c013543c0030382200c030900700c600103e0180300a5000b807050080303a0104050001c0c0d0140e1003042d5000c1580f003e802140f40c3c0550f10700034020180030b00c2403000140302444440407200d03030b507083c0691903015000216100340d1406c800170510b4410705c1c100300495030301a0f481203d26540d0901d80c4600400c2401e9901c190300c56000d0140c0903c210801c44003005442403100855007000d07151a6080d03c01c090b2880707206038000d02c0400c01c180d42d5007406100d00c40c0c040310500a01c7d01c915104800400146a01a4008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 632016888 1250 632015638 632015641
    0x201030b040c020c1201050c1204020406120c09050108010c0504050d0309030503040f05030606090c0901050307030605030d0c05010c09061b0215030a060303080c07030504030b0c09030a030e030d03020c1c090806 92
    0x2c64021403002079218055404085030343c20803040740d08980d011641d18615500074002c1191a0820580d0180e0043c4042c000151694482038510072248031680d00b1144503d0320101401031041a000707840c010a220f4009010b04140c94078080c0c2980a103005460260341d01a503208141803240c80c41ca002182c0150503640e03125168003100c1205600c40c06018064070400010680c00c0c28020700861140462445c0c140c104200c1c1801140c0c0d0b07501c060104400c02d603d0700000b0400d039400780005600c149168540d0b0760150340503d81182075681c550a4401402000c92080001d6a009024840c01c07034405080c200c01460b40b4400a0301007401c0c040c01e075074540808000c11000285950211003524060b4444900c0d640d240c41106100b4440ca400c0140010030601c8108009a0581c090f1500111105001818060740c074003c6460036444d1746054000404500072001141010b0109007022500c1e841c05502d044520340440783c0d61480411400411a103009403841800d208040a50250076400700b0384845 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 632018138 1250 632016888 632016911
    0x31b0f140609070f050603010504090f0507061d030d0f03020c030412050a020906060f22051309030306170303041e050d09061202070f0212281406010810090201030b04 73
    0x1224000c60b0051028410040c0100b8041ca08a503024211500102113603d180e0901041c0000761540030b108450003800d2099031000620180486000751009684001440400341c3d03842c60313481d00b00c044040c081e4001c001c0c21f81a00b07500c102c0a40d8459818100569a16003507041545184101da1020700120712400e40807080080200d050a681c0b8002c131095401d940b41c40f010000c003841980d03038810404000b003081c01e0b2001d0311400c4c40801d18204140407070020ba80d0700d0226000c5c1070200c5100312200c1e0b6442e04802010b805208140147c40c6141036100300c00e1020b03442955901c0701a001510f494016407440c90300c201c0d50703600518007035803041c192680320009076005800c89926004600110b05030f100da0f20f040c9203040c0300b81c0d4900f0390420000d11450485400b400351920411640e50894040d68101440300506452010f02251701081105c110309141d0920f14103075001c0c12030040c0c05d900311070010886aa00060f075007000d03510b6071074000f904001030b100580080004844094215007020399240c11f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 632019388 1250 632018138 632018143
    0x150203030a0f0e030d110702042c011b0c020a050613030c090c0504092f0a170f060126011706070e1f0309020306040c1e03031b0f14 58
    0x341d034401c1c420302c0704600c0d081141066a020031001c1e1450340c000d00c41d9020f000701300d80001c00d0508000e1710b418500f90554010409484d01c40d1890350b09110a501c44041003000181444140c10f1460b000700980302a11031840100b105000c19841040304680c00c52040d5980d000519005010080c60350f690744260752200c106400302c510082c0c13601070481c100040c0c00c1e100d5000700344503a03107240d0341c0c0d0f032a080c00e01c0c281d440203001c001f6920719400e007010420038107240142c81c06126011980001c903120311010b5002801c0010a110700c140d50420001401440700001c1046600003109080590001802e0300b003005001c24010822007a4a08400000071780380700361104c0c0213035140060251000b139501c61105441001a441c10280c1207203143c9440d08000c450b610403486440524640030480a0954000070718181c002d9605039003401c0401030802540d94456030411201103012000c91110340703940c85c003408421000710100c4540350b804a41c0402c0000c0040415000d5030300c0220700202c0200701c01c2456 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 632020638 1250 632019388 632019391
    0x302010e0607090f030305030702030c060709050f0402043803041505130b07030209040b131413050d0e062101050f0a260a120309020f180a110415020303 67
    0x30454050040850b10040c0700310740c54803d44420a012983e607501d56602210300b5070000b017043c811400140024980108103120241c001d849030359915110364108800c01c1140018180d215100d1481000100400c2c401c0342d86105040c01d00e184240c940364002c129103003502100c400c0a9446100001c00c22041050182d54a6044100035000300096035402d0080d0b1040f000c0c01d40080c010070550780c0007a05071803284d0000d0a120102804c00b05907690084080740d803241105580c00354242c1c17900161032030f0401c4400c1480d441104140000c1c2d803201030f601ca25407658807109040e010400405103122040d2079101c12284000000d60400c8100c10071070003030b4401d0038420b0044902c121103582c00c0c48050325000031407a082c2c4010710041c01000a1240170046170000340b00070880c1c5805194001d001080c08800b00c0ad01074940c5403004646101c144c410080d20b618108003103031281605040200c3d4403c41c1c101019441130b002c2600141c68800540894928026503001c45219602000f00e40d40f49a40813003c1c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 632021888 1250 632020638 632020661
    0x114010314010315050109230a0b0a060206041104050c0409090204021e0901020f011b03090f0204050702060a0608030403120516141f0513080a11071205100902030c0f040612030201 79
    0x10000341c2d1f200c59054007540d40059002e8244011240c2000070b135089005265041130f001140040e4a102150204c0c500e04425402507025030080b0040005000c0c02c41d0180c001c46001710f50800c110b117020883c0c20805d014a0044200c042c2c0e03a0301011741152541d40c100c0d1100b001c0b0101d130b000400602c0d02c2400007030344020100360060107032060086091070305020300340341a035045401c0084c1565140e82100148541101a01e04840242c403210240e211440fa040c042c0c0d20507405400c00d448d203a601c0b103003600c078245e1041d00c6076031013004200041481300b241720b044c825542c17030050303650b18a50480051710b45003a0b8001c1c114402000c11880040700004003071040e803880c04c603100612082e06500b1411220308a842015180d062210007000440704401403810080c681405251070b03681841291508420b500075072100402c00342003200340b02040043d03511000fa20071051014210590100343c070b1b840050100d0703000c0d00c01d41030201510b03074494010201034002c0e41e0071920409040d0070000d02a0149000f00e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 632023138 1250 632021888 632021891
    0x1704090204091404030806060f0d090602032a120c0d0c0f2c0d051204090c0e060705101e09051e1b150903010e06011802040602060114010314010315 65
    0x800312100810001842141c0603284d06d50f09a891809200c060780c40500201e442d05400c1022070340810031031003404000340c0669401600c1e8542048098117a030042110b200c4212081081080d11980c1c02c0115604000c05100380500c0c2d44401d881381a0390b0141450311a161405c0c805c2104104d54095501100f4081a54502007200b117420040c80b0340301e0b4400082c4d0540884a280724440d4208035500340000c600c240103d94020400019803851900a600504a05612001401d49031607200f480c040d1401e80031201649040001d58a0320341d100f0400d181640034644a00c840740302d104440c0c802103d800d4444405021804d00341c81d0554860f4541c0401c80510b0206c404040e101260002e4003146a50102c4041c2228850780300070491b10300e6929607803a100038803c2040b5400e070344080c085e1100311540031000f0700c0c840d4140601122164020001c1d849098410b1004004a582c0052494112103003440500c2d00b80b0b1401004802a120100c4181d5004450100020030071000f100f0949a05400840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 632024388 1250 632023138 632023151
    0x30d0201151707050f030312100303021b0607030804050f0a0602120c0f0d1505060a0c030f0f0f18030501021b011a131d0d05070203070e041707170409020409 69
    0x42c07a8068180600694260f54800e4005000f2400d08101c5e10307884c844014126814484126030041070f5807001c441940400c0383e004400c004154041094081c28903940820405c03240740d10723002c143c850180c0b0ba4050200b01d000d1002c0303024400144510b0300c4021321681a20400e01e15800c01d030f0042c3d8022103a480c2c254251303000040001485400741c801071410080c0d03507803130201d00b41c41c49005040e0240403c41800800d903000035050703503214010200030341d03a0303240c40c04080c1040c10041d00c01c1301c0301c0790b905041c04400210458000d40c040101e048415440c02e003040c102411081c0064000381d0394100906ea98030000c0d031411000700c1200182c01c2c00c0188402071010240c085103c0d18140c10036408107170465180200ea018882ea0b0f85c220305604039040d15100030b44540c4000700384c90450081c46d4080415070000c0d001b0b055080c184420b42c05800581031000680c03c5c01e94402d200d4080c04c3c90040b852440200d00c0208100c046107104d07088201c22021031351520786988414000750311038070070f4601440c60400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 632025638 1250 632024388 632024399
    0x2e0c0501180c0f0b0f0c03090d0c050102010c0c020619021002030103060b240324090c1305040b030d1107081203101d15180c030f010b0c0d050901030605030d020115 72
    0x20070030300130f0780e07801c01c1141e0809030340d5481c40b50700e46c200b000446a0760006001280031901d40d801095101801000e50b6054140381c007001a0031644811030074000c110f03006043d074002d61245002c80d42c415811240c5100d0038080c04c0c0b400c84c10922003003a0320000600001c0004140503881d048240145021598082a42d10f0314003204120480040449103243c0c0034000179800300c203010400c47d014203028640150b110030160014490860444000a180382c010810303d0340d604080d10030502501e01641c00304886100707080000d513500070780b01c0c5050421007042e1110f0303055a4144010401407541b81e040f10303810501c1400d44181500121030343c00f1407280040c00007881c0180d249203514560702c0c8000c9828551101e8202e010f0060100a1081d084210f12101140200e108540c1602c03400c1c40012407070301c906045c04000a00e02d03040c0e00401075810240404a440c2e00045040c4a1000d2103082a03503031402103600681c05081c1035071040c3e5150003410001c008032601034100802c41c5c0c26646204081a8031038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 632026888 1250 632025638 632025659
    0x1208060306040b310606060905030106050901090c030e07030609060c0f0c0f2103020c0d090810050901090b180106051002070519240801052e0c0501180c 67
    0x1210060030320b00300c44022864000300c1c4030382a0b8115410a40402404207144d0504840288480080701d00594841b8104040342c0e2001e003040c0500021802030003018908030000d00308280601624403440d990f0754010711024000c0d80403035110030140d420b5a65041d81d03800d00c0001058405000e44042e03013494415803549104449031030070300d542c68580151010792515074190981c05900c040310401c0e12804651160081c9032802c1c1c140c03001540d80543eaa2101803282810220040c07071507014001c0301103051058010201d4004000b002c07003c0c00161560b038039a502c5000d4414405c000c0c029942034018040400d400c1103032980c08180840c000e00c101a81c600074025030040e240303082001a000355100380220300e0035070036000708110034061000005440d1040744ca618850001a00c0c0441207036540d8140a94105400078010542210045800c2c1415048100521b4004c04803850110f0030b44c25a1005c1409000d90f0307072070190040c00800c5032648100050380c6c00400240c040e2a0200340d0000042c4a5000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 632028138 1250 632026888 632026891
    0x14070e18130f081b0c0a0b0a081510050901111b01050d0603050f0c19050a1a1201061101060803160807050712060f0b0415180f0501031208060306 64
    0x59588040c0c50340c0c1e858026071603461050000710394907004844100e0200354400e0142a80000c0d4000a0040d070b40660311081c40c10301002580c038080c2003401070030049020390f4015994102410b041124003942c030701c0d0703004c0c209001002c21950b0040104140385e21169022000c1c0c10748034420703210303801ca0054040440355902020901e200708254180b42090165101e03c0140101040020020652030344030f5807114288203054010001035480400303860200e00d0314080311071880d03118000c600c4006003410049900801ea9010305240c025110880444040440302259141d46200c0c2c02c1c0511035031100e000810043d041d2003051015801d0041c082881c0c0703404022100d14101902d20110050095911652580c0001009462601541c8400038000448407080c0d150244282c4002400c6e00c658641e90b0110b4000e400c0c0c0ca401b580c0340000c18004445400e028034240d64485100e00605040030000b03802030300c020010b10701c0d8603080070000410031035020102903c1000f59240d0321620355600d41456a02d040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 632029388 1250 632028138 632028169
    0xc0d05042315011401050c03070503030402040507090f050d30020f030412140109150b040606030b0d200a0807170d1709070905040308061021180614070e 67
    0x784040100845013541500652083c018100700c0d040214085c2500c3c11600041e106036000c2c1c000104000840c82c0c140320315541700030035046c00c1a456040c56a41001ea811602a89008000c01c441c82414400c003c844114030b0016034440d400742180800c002000151105000c50261140910001040740084251016103582000f0500003030005d480300415002c1c114a660100d560307400100c4c011440c6130b180b443c003603412641c0100b8031412031418030007140c000780d0200082501d408407a80007a555660305103442034000d038004208005003040105050340c40f03840d007503225100900015040c08086070075002c45840c0c0d004850861085a00e00f5298007000356410700281001c001c3c04030080c0c10b0813030b541c1c001c0440b5040740d0310907494120b0755040b04c2d403d03039095022403034920801520f407509018003000c0c02030500c0d201e98035500101c03552090300040041c01c0081922885084207100c2c42410900e09aa0004c1c014011700f00301d0510b03120011000e5031280c00207881892071140724144140b00c2d01c020308 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 632030638 1250 632029388 632029423
    0xa0e0f04110f090a0e010b040303080c0a080606031e0106180f050121021e03090606031f021605060103060c2a0f0501020d050a0b030c0415030b0c0d050423 68
    0x140080c840da00f03900c048056680201c840d5800b00701d40f80c6803145d4601910000c641d080c1d80d00c0c2141405886950b00070440c944042c81008010700d4141d001140c41d801c82c1c000d65000d6206d841f120100710b8101d00481d0140080c1203104000900d555110100006009100128909442d140c40c424540c50b15103015160229404010400031a0000603005c51101030100b40141004108440c45804600601641640340004001e0091844052011540203002140200f00704a2256034500701404180d412a09650b40482c0c0304c00c0148400c20b07041c501c20b078404140d0784590f031a881c0c03400080440c07a0b800000113003005025514049070300980800341b052100c9101504202e5542c0c40d140400aa0085803a95000e0085d143c01550b44c0c01041d0141100401c0820400c48810505281c038081d03020340b43c0328908000d03080e0207403042d1959840a9940050b8542d103166907100c80a56280b0402840000480c6031004020602114030031083c44044002058490802003140450307684c80c90341e81090180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 632031888 1250 632030638 632030647
    0x5180109031a040f1a0106110c09070509030a0506090105070e10090302150d02161103011401050904020102030405131a0a051e030f240a020f03010b0f0d020a0e0f0411 73
    0x2542c48042d54054401e00540c05048070f0f0b980d0389256202200003120500c0140b0340180091a001000c1c00001d4126a004110486071000001c0c900d1501916440074848001415030150b10705002001080d40c01030700311480b1742404203c003402000b041f200b4100156500c2c1d80183d0f1032520340050080c03100c079681d42a02d03007411902002184200c0083c080c00408040201c03030164443e60025260300c0e43c0940140403600e41508180c0e1141003a01071301c0388240d2404805411840310060b00303074103456090711001000d6031035200607860b41c881c070740045600051403000140d1015141c3c000040250004240100c40c5200f41c00384080d044590140d1640412a91120b020b81206203502c2c0060140040440d51a070a040d0002d1381480c400c01507041d010b50486002240071340185601c81d80043c03924108514002c6411003107030043c00103024501c0c0c2140005084540d5400d0807003a55188003030405d0466613401c458102400d115030b020740d80d50044504031500d21143c5428800c480401c032503520001e02c1e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 632033138 1250 632031888 632031923
    0x1503140705060a030e19120206010e0153010f060b03060112061512051003080901080703090b01091d0c03031e0c0706031e020405010e040c110d0518010903 68
    0x1e091700700e6200c40c56101d441050a0400302e514128055240551844a03100400e52802810540305801c1003582040f00b400401928125038001202c000c3c2c06101c1501035241d184098415411806038502d486000251319a8030800110004101410344002000000b411481c3d0314103944040c4204001000c2c24800902a5400340038000d492107154440040e03400d460b003280380d02e040b29881541000031011010540248941c0c400c540d045215640e819074498610b6170703a06140d20071040d483d8100015a000700f09118000d07000010a5580b0000c100e41d0380d030b120042d0000a03c0030020400e1010244488070748502e401040401d1001005005180340203035040064903c1102c075900c010500104118501c4054014403000c0060f0169a401080e40311000030130081004c1c14101007000d0610401040140340c0e0404039041d00040103840c0420b400c0c100c96026035889600a014503454000c1e0000f0f14401503208004048140041080000b0422281c1c0115081e886070f01006248000d000d4140c210b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 632034388 1250 632033138 632033141
    0x1030803130b01060509040c0c32010504050307060c0c112b0506040201091509060825030603031202040b1806090d030e0f10120905101503140705060a03 67
    0x40c000080c66200c408044542d459440c0b050099010600044010800c1444c600d000c3c02019224025407800e00c10405035078641c441e81c021a021a0050100201035400e045d020348007031070036080003080c0204500c0c509410240d80381d51000c1001ca403418a8244000c078041d0050407024072158100b20a1100e40b4103070303000d1180d5a00d82c6c0b140800c412400091905da82c0084025048560388510080e05a600b498400980b0402c4941c000203204c00e1b52030b00b407403540d41c2c0c892070700c10840d01d41d0301d002c00c041d844c0d05040f045820040f122100a5007014040f9481e400c2e0543c20150480740700359100c50500b90040c07130f040d080340a83e00445080c084204440c0080c0c4448811501210f64010300d0b561401e440c0c0000201c0140200c00300714003040480c2c40b807203040d203014080c01aa5410a442034000d811082c48020300124a040e808039505694203c0001400b2007000403400e41c10041030200b0401440d1848440c040d8950311044a02803510184904030710341c0407500e4000c49030b0140869060003a02c0304140c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 632035638 1250 632034388 632034391
    0x5010b0901180801092a03150902011826210d111908010b0901081f082e18030f140307030f05100509070f0203040f171005090601030803 60
    0x980c0841070b14010420751000c2c8204040302d0310680d48405600000310b82980e44409071410a1341040701081d00704042294681c0640b151058805e00244422180c40141d4042c0c6045030905100c40c1c40c418007054100300072500001e0078890000c1c1003100c0310704400c040c2c3c1c0c400c1c5c3c484031050b9140c070329038ac1c1d1000c689401018110007034003800081030503074042c420603009800448414807a6055410350007461a0800c940a001d0081c6600c1c691501c1c0861001034041d00016044603081030071601300e02504a942c0d1170350006880400240c03401e880e92003c001500410840030700e2003000e086801d041e80a4003d10aa41944005603121501780049072015100c503010158014280586c150282482c0828103005522031009501d0002e0414290002001107500041104d40c2000300e2a506001650702c10021544c0704640385091045100400d0b000c9045010300e502280450362902000700742c0c204004800f07101140040d045136100103801e030340102500d5041d110426141c00c180014408101902c0c000c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 632036888 1250 632035638 632035667
    0xc100e0d051e160201082212260612160312050d061d0105040504020a030206180901081c09032a0b0a0206100b09060d05101205030d0c0305010b0901 65
    0x2410b0481408141100c2079200c01d10140040910a05990842d070b00300001c540c010380b41200055412038100012450700e00e0450000c0c1440e200c0e00000b410542c41030402012065810303030380740768140141d1080c90101c8419556980710300d0417071300a2508608000340a1156864006501d03212510f103841e420009102e1852444c20404104004501803020b400742d6802000c030307100398901400c420b044880c0e0079001030300100d02c11400c00c424000907039503d54a440c1540e4049540e0750759201c4000c06c21401400c0e81c1a281d0300401600700005d8008804140c100c21880040610342c244913800e1022142120f590100410b0341c15965584000c103d1048003205000c6003c031a5600b100f626100c030342c5400c2c2c200902c1c0703400680c010010007146e03100380d0614200509403d5407050910343d1501c000b03a00b038052004022145642da80c00140c405500c4908140244001940c03250b406050342001601c0303910480070b02c3c2c900707401d00d200700e041704e4828880c0d036048581c0381d42618103100c05900119060158441e41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 632038138 1250 632036888 632036917
    0x16020a08010b06030f042a032001170709090f02030415020a1b0206090915030c120d0c0f080408070824073603060e01020c06040b04140a06020c100e0d05 67
    0x140d55500d10b8002803040c0010b4003034603131f940c420720398079084252a00447d0001c6841860728195410b0381d03040002c0d68208800c030a4200c44a030340b440d50072107124040d5840382500c103040002c075071000c0e90207500460186004820b111413032000ce2030204140d209001c0c04500040160a50a507041160081034440d13520080069103410343d278000107800c1080a60300441c07180038030003c58207180303020080c0ea4111281943c40441d1070707036040029038a90785440b10312001e10550b80b060204005075844010455940032142a40f100d846260641d900e02040c0134001f160300c07039600e02a81079281506034104045050400941955403030008541050301003076107400c00c0040481c0e84c0d4a0820a5143d02c0d42051084000900e00e46141040000e07120780c11b10500b4aa4410024130741c10707010204815500c150011556003c54480385003000303200f148850000c01a0181148000c1005080e40041a800410008441c107481801d203112007280c103920041000e81e03000140380b08a50740503e011700b4401001021 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 632039388 1250 632038138 632038163
    0x705040306151d0106140c030903070e0f0a141602030d06091a010915050c0a05030c03070303050a0c0903060c110f06060933040b0616020a08010b06030f04 68
    0x1030348002d60341d12080718410040496414045180d001c02e041e22844401c01d000c09043d403610700050701170341d80c03a40320500594002031001e001210420448010241c0030b02140c20302e07030340c4101d0180c500b8808e8a103075642e1441d0390003040d40d444d01801000565484c80a0401e11034985000301c200d06040300c503c9805500040c00b4400420505128120090200307541c0810040b035241056a41021084e6100381400030801092000c02c9003100d0000c214030550620326a00c1c2c3e0084134803441c10f04030001c014480d21000600c4d0050390004000b46c105544030392000c2c80140c54000b00a0203030f4132080800303000100317501000c20200f802500071412079402820548a0f100c07980d16164203020294940000c41d42c0a4011b100860404030405070b4090100e801e61f202c003411040000c00315800e240d461018070b40c0c10080300181035a41d940141c1c1c16082c0144416078400118490040007088004181d00c122040b91000580314030600411280842c01440703c0c4c03131a5145400142061000780c0107440d20404080d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 632040638 1250 632039388 632039393
    0x2030d05070c1b1401020f060f06030c09090304080607030605030a020103050703110d090209060117150315090f01060b04060e0402030a0905030a200106050a0308071104050c0901180f0e07050403 85
    0x8202c2d404120040004021800c000d205000f13400034036030150455008031b481c543d65840110b0165000f141b000600c1c1116110740303001070301d41101090360a500000c058140604128004018001c88070b40382c003a12410365401109030f04541d920320405070580c101124000040d84a68491907122035941800a030070490154410110380011035404c0d01980c0d610814002d615000070940e034040800d00c0c01d10a44c0d81d83d01d0300000700900180c40eaa11000d8416240085540c05100d40c94401000701c0e1065024036041c0c0040380c0c5c4001280e001c0220754a0070720041104104801200c00b503507181e4076a92006a801014040203500042072000030356902c480d89400a58144010b0004140c540c0c0e4103070320046945130350006810846034501711a8900f0701c1c1000b1035100c1c04001c00842e40c0240c0101c1d00d403031031030400c8071a0886000400c2d03031040c505010041000807110182030340110a03641c42c03031402150100080f0b04242405820303e41c04002c0010494905907100075540100c0038a01a0300f49690395 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 632041888 1250 632040638 632040653
    0x40905010c030c09050a0f0e09010b030d0c031707050301051203040504050408120f010501091401030b03060106120e1f0e03070f0b0103021203210a1d030a030501050a0602030d05070c 80
    0x9592840002e441c0d03881c5450f030302d41c8140d1300d0000c1d110813103000840300e02e02641d01c05091001c2c82408880260100004c83c400029444840e00340c4000e016035044c824405030050844403142d40450109845410904c94111000c1c0798911855040d03c2d010f02c0c590804080280880d010070465102d88010030022030180c99901446003d6031042c2010360329403c032041c100d038554000400600350042000f0041009030f030701c43c101c0f02c00c841800c5da10265400c0403400480282c40c041500c0d60b014170400c2c000150b196880340300122840c0d5107038010003c0c4031000e61103d07100d01c0c42c1d40b108016403019175404400f10380c9651124a043d840042100c3c90518655a0702c0c0110000c000d06070307284404c0c20b00410075401d00310741903030840280d03501442c0340ca4584d01414040718069182001603108800000300355400300c1d881080e400114100034803808a190f40c103140d40342e20004000d40000c2c144070000038503081c10010b0a064400d542c01542c240600d4184140060000034112000c01c0801c0e046603001c2100d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 632043138 1250 632041888 632041901
    0x306060919110306010905060703120504020a03081c0e0d0801170a052e0507021b0a09140a0b010e09070f0905040612050d02030405060d1104081207060606020319030b04090501 77
    0x24400d00b19202d1800c1c03000546100340326405540200c0080004800003a4051094070420001c0000014981c840d800403c40721803880c1c0000b80030090004c0c1ca094041e0007154071558004805005001c4103850281c0c0319112554140c4c80c00105003030701d005000020001c41c4110a00c480c440464a05c49059181c441c905008a0300c00780d070b03000c0c0003810742000016000040e0240d015203082400386d410458802507503034000c00c03100c5010308200038042243d80e584000b288000d001c511070038040352840c00203001200d5825501210384900e050701c0100d195010300d0314403466040060000c10147d40da44d409071115070450702c41c00c2c03c0161900011540d035440c5d210710006460011107001c01807150740340840c9815034070100101903500600c010000c82d81d40c1c2e02100c140a40004001c0380482044108861902494014070013600403210203580c03019170700d0050301c0c032180942001c1c4102d9649101c1a40c0340e21407401d0182207050100700c0317511350b18025040800c41800103000050b221400c0c4e154142107491 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 632044388 1250 632043138 632043161
    0x1518030c1c140d141c06090b09090105040506010e040507030b0117011a0604052403040f0210110d0309020121060914010803040302011812050c0a0902090306060919 72
    0x16805202400e1000c8402c503000000c40080c01407035450010180603111022401400700350700c0000030200b02a940d0445500c030501c1c0c6440061050b19201c80600c406005c07842021800f51504c1800900a424140991400340b5000f2010b00502d03403e00c0100c580050000700255902d01c40c030f1500100052150212034000c0002d07020074410340c0300581c4c5042c08e6800d00040001880c1c06042041c2d0079a17a0703142150220b8808581245041c0c2075640e100303200c540465042d03012030380040300700b06c2440984e440c850241c51085502c0d0410508181081d1410024107100c141158000d040303002e217050195002654003801410a045441040e01c111781c1c00460301c005210700c140c2c480800300100900782c05140c5c4c070607440e40d549689560401c02819a81e005030f01c40641002160800440700380303420038080c0e001c0c005001101e4080c00711403c00036130b1541c240400c107000b90455040003030040d0082c4203581480400a0207800c0c40d403118000c0004000c0064000c000040111481c80c121428510481d02140d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 632045638 1250 632044388 632044429
    0x912030201050612010209030d08062e0f09060c0b1b0c010f06140d0209100515040501180302060d0f2306040b10020604030503070323151518030c 64
    0xc3d124090010b40382c13649484a00a0780144126031f070664000c10302c02140d442ea0314103440942e55001c0099580b00c58245441c4e444900000e1402401442c59034882074030440da101d68405a2080a00b00c508507050b20a03400001c0c12a01030200180004a0150300813502405805824500c10511a590303840121f210b0840c1e035440181426104a41c02050010800d9903007205c00c0c00b4044012400c10014180003d00c1100c0000020310a10010403440c0050b0101810700b04802803d0903a0341324503442405400e0120740c070340d107000d0701d40901c0311803000580e503028080d01c0c20244144402e00242c25280010034041e911841012900300400f14100c1409007490120150360801c03505000441740a010713030034007445003907034454886600040d0032600309605150040d5a5603483e0000c400500da4404613080e605014240410320302c2c0c5240d8a940180b0600320403000b581104020008070031446c212080041c401840500b400254240c1032203144c08015007030758000365a43c1d00250303911600c41106183d11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 632046888 1250 632045638 632045641
    0x31718062116171e04050a0606081204270507090f0902030705160f240e0c150703032004030b071715060c01050106081506121501091203020105 63
    0xc60321030740503581000b210a0700002081c080ca2004045840c000c0483c04491001d0b00407903950501c098040000035101e9080006a080503e0043d0710b43d40c905009440d40b50421501080042000c1001c01620584207141d5151a00d000d08000d022000c203240c16581c41d80300d4038580304066460151910401d10f42d900c0503a400d082441080c110303c0c2540007208141e10500c02c04c441280c00504071603031300c4d42040958103551601d2414807824010312074014400311110886405622403481c5441c02070702c01c40018000b00840ca90090b03038503040d40c203503d580f0103140741a400004841e8401400018081c2c9400725002000401c1500b40750f100400c503c9100c0000542001031140107200f03580c000031586441e0740d410400342a0040c03104005807118902481c4540038840e9903640404443c05003041000034425582d5500002e41406801c40301c070f0411210f4035506440528004003103032400c108030b54680c04951504460210519601c2c022241882101c0e0404180c881030082c0c4c0e612018030990011409 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 632048138 1250 632046888 632046937
    0x203040f170a0b012c0408070206031902040b03160206100608070516050f0c030d140d0f0f060302091303020718020c0a08130509010308270402040f08070e0103171806 73
    0x190176500310700801050300c024400040c60300e8089034451501100c0d1152030361108080783c40e012819040c00580f441c030018000440131000e90245204030039045041c0308001c010041642c9441c1c0440305a1000d64158000340842805000c2d803940111003858607500b0300c0300d5000f0300900f540c121b810903a840e902440907010406010049a20150806d42c06031012140001e8040d06640c41454800c00c000004101d2104142050340301454101c035481d4140404904031401c0c60090a6a00044e03020307a40341c1000441c0c0c540c0031202c00254607071590080240c0e625000607c510a451714400604d11a002c01040303c2d01c003820080003c2e803c3c0245c01040e40d40d400444519910200c40e8401401160210f004002144030081582c210803000143c2c4004000140c0781ca1544d11290000140e10078400300b03000c64003074001c20342e50b4240d42e811800c58422544032450103c00b40341c01d100044c00c080c100054a0321001401c0b001d08203032195400d015110b0f140120000d815a000301140c2001111000c403080c0e0f8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 632049388 1250 632048138 632048189
    0x30f060f06050706110f070f05032b050601021b0d0f08030c1306030b0604150e06180f0904120f090509010617061009140f030706090806070203040f170a0b01 69
    0xf02203005179441c0e49000302280140d40507018444000d0311004d00e0184210a000e03003401110000720b4004646400c40c048002003219022484001e4040c2034900030000d022075000051400c540f40070b91841010801c144810050002054a4100ca4050302003040c40700140444000e18010170030710202903200c403102c49080082e01426403001c41058281201c40d0324030303120741c130854081d81d8600200e90b20610003d141982c4a1440c008800c0c3c22000020701c1c0d00c1c2d1940401a0f010305603034201c6100b078900f44950204114064141c50203094042c00103140a2014001c0401915009030390400b010900c0d030f240c001801e001402d0f8403810125030042481d0000140c2880125480a0110381011803000140710081051210340540b8070400b5560810b01080da0b1007490030751500784020b04486410f600c40c0e0005080e405036200c0c00c00d80c2d03c18074010421450012042c0da05440b0400c4600d2211454000d40d02002148510000518001c400b07030701012441c2041b002d4080e05040c04440030210502d2600f00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 632050638 1250 632049388 632049401
    0x60d0f0506190609050d0501240807080a020f2e03142a03100801090c08120f2703061501020d0903030518010e0306100f051e01030f060f06050706 64
    0x380c1490b100140443c1c1d80100d1300300107984040d92601c40812040c60f025004100740002c0c0b9920b85a5090580400750b030190184c0f00365555141601d40c2281e84900d80c83c0d41d04081c0c0e400075400003030f030f8101c0f90044c10005d080c41c0842104a81c01d003000c1e440d41444403404034400804c000080c0d11185070301100302a5031303115600060305040c6000600f0000381e00031280c4140b0040400059000004640007005402d1800302904603580200306001d064905900e803180148241b401d20702a1a004c1c0310043c0d14403064501342e5103290300716464004c58100341214040c418101e213040c0203100401e803640d03480402921b0300c40d481300315100f01c005450800191506828603044c40c100980302c0030500c0000ea00005507416486011440740c4c082c528640141c0341c00d880f082c001c5030188240410030401141c0d03500318400312164480900010780d10b940c20304c60051010b110342040e03640420f55144655119910445450041e00400501c603034a17001003000700c00287d8001c100145010440c0010b01100c0d01c00c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 632051888 1250 632050638 632050669
    0xf06050604030f11011103040902030910180b061c0503092e14041d07140403020105070803040609120f02010e2b02070b0d051503060c030a0b060d0f0506 67
    0x10390405103150307160f00d81425155002000140d0b81c0c118018242d008101e0070900d01c01440989803915151001c3d0700c001e41040310400c031070340315a1a40307840e038042c80c0c0710b182c10700c040000c1c02e0766295003d43c07070300814204050044c94120001081240c5141203c0076408c0e56280704801865450f000b02c82000852001414141e0040d101084000700195004039440f00d004550300300342d1005284c4268210441c00303107520240d0060001c0f41c86142c82000000039500c12102038813150702c0c01d0354198000c0d6550055000003400b01e0810010306021400102c00f85a000d80304600100380740c0b0b0b20f940c0d00f10005a0500004000c1900c50342c01202c1c05070203000f588a041e400900a2481c68002e0422194800d1201c2c6008980c40300c00c43c00c1c0442510a01a0001034550181c5641c1e8a0200b200404020300381120401c0c090004004805090b24021030417a020f00d40120810b415074484581c07550081180302d00c816404481000b0005445c2142c2c01800324055031043c00096529000c030901c00d02d1080d10680 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 632053138 1250 632051888 632051899
    0x2607150b03010c08012114030703140903060f06060c0d02010204080d1b031407120c03080105010503090d0e0f091504050606031b250b09010c0906050f0f04050907030f0605 75
    0x7003403c03a0340d0000e04181102c0448252400119050482410450654502401401a400b9240604d401c0000246035141c42a91030b10480400c540d100d43e900d001b00400ea0f07a041e008800810682c0d070040078181d40002c001045a450519481c038800c1c030b0080d47d0804000540d402040421800b10180603400e42c48109081c80d0b0456040c3c4103003020742030241d070401400e00c109009409458010341d016101c0a9900001c0e8140c204800030000c1c003580882c1d081140068200030010946500c2002030300c2c040d6084500070811003526000640d148072051181a070041c1303120302c100d80c41d941c0c0c9502d401c0c06240c10101201c600703481041448141c6800506441c0144400c0040c481c0300240554041024109045480c0d01c8080365502150030b00884100e085407035085114450900940e110a140540d254000804c4040303240502035904101601c908d00c0801d80511401400000c840002e10318140c002c3d01303892400f0780f580001080d03010150f60940000b40e5440720794103c8801e40c403c0c4c2010b0030702140c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 632054388 1250 632053138 632053151
    0x60f060e031005070302070209010e010f1d2403030403060608190b010e0a0603061a101805131d03041d0408040b0d06150e0109212607150b0301 63
    0x880d5030b641d81c10303412140060381c40c00040c40300d500c640d058410070f85e030007001c4540b1365030354a500c10710b078820a00415007070181480f030000350345a100000264045103d08866044d980340800380180805520407072800b003100080c441d2031580c083c80200041c61180303100240032800c4c201c6003803403c01c5628601515505020803070010809040744d8904441c101c0c05540d81c99941c0c254040e000d0034503980010801410600000040c0300000c3d0042c1461030b040d20b64110b0716060f600d0454805000d0720403214400c04001040c020350504000b110411445020045100d00070540001068030030207030390071219003000c40d05100b038003080399002d6030906000c443d00300a4140364940e11120b00c114855420313074140000e0054810006c980140d0000c0100301c1c00a600340e122044090200b0600582c042e001489004021650109141280c0312a80310051a2400641242d40c0c056081ca9400d542c121000001d02c12040a044488020300c1110301c80c84c2d9410500c1480103000055030b50803480d082c0709905012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 632055638 1250 632054388 632054417
    0x30e04021c32091f051e011a0d231b0301030312050403030e07030c0f05060315010c140a080d0c02030c060c0f0f030c120115080c0a1106070201060f06 66
    0xb442c102014449525050560b1030b81c58910b4034001144014181030f0040894144000540340d101c603200307903110004456050000d4400c1c1225030003d00900321041450129400c0b1070030703120050100007880f00800980d5510000a06203400da0f20747c002e03c00c89034a1800c018250103101d00803d0807444c480400c60455041d40d44c044d0486040c0440781c00019903071070010301414460b0b08041419400398040c0c581c60354590501407800e8800c3d008080c400405002c0c006440c0c00c0c104200c91107011400c00700d2094500001c01103410320b00400b4241c5107481040c1d172034a1140d00500410360464441c290313069031380380202c0c0001d061f00c0032400c3c02d8003950014042c2001014010a000d5406520104295136428030940820441d0058010b04260308901100300400e0f105640014a5a03ca08188402040c1e03a10f40110881c80d40300704800000982d6030012a2851213140050400c000940c10840502c0c141c202003545002401ca4840b00180c4d143c4c1c904000c40c002854180f40a0441e500d02084450441d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 632056888 1250 632055638 632055701
    0xa0c05010507120f051c0f0c091410030b0a09090302010b0616030c080f0a050711040608150a02040b0d1a0a0506040303050c0309100906020f0d1407030e04021c 70
    0x1c1043d018003065924124046100c0d40441d949107441440d681803222802824400078605155036500184ca407018202c413190241201c2c00c200c50450203441001684403050104500b02c822201041c1a1900741c601e00564928917600003070708900324001203110032428000d00f9180404403c0340240b50412500029140880141100d550541030084042d07000c1d24200d802842400b074030b8070207101c0c0884c400c45069807001c018030080c0d00948490050150101c100012100c1c0c0707104a40856100d84607001e00d0309400b002c0030358000d207180c9005003000da4440f01292242c1c07009044901c10381c1c0c0c4a642d40b246440450b41211003410503214000c1039402c18010515070301c29400b002e010b11101007520b0b14203400c10000c9802903074002d800b54890f440d124801800c2140d8500a9201501071b02d68104114840001c00d21400314050380d4400c01d04e004c80703040c045150311001081c2c0401c840d1300c0728241203455034001054030403000400c100003141c4000410b000c0320071840041c84480240d02c0c1400070b00181 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 632058138 1250 632056888 632056913
    0x140f040912032f03060d0b011e08010606080f070201150902031e0403140705030702040c050c0f01110403030c021c110a0e010503060610180602060417090a0b13170a0c05010507 77
    0x10f07619941d0faa40c5032000010100c1242c5a4020035a14200d00086880300c421080d41c003100181c600c04030516038075032590340d0070b80c2c40c81d01450000607900717000551181080e20061380c100c0710500000910364812210080c80b10380f25086071200d150000f0070311080103c0080656041084610002c8182c100f9950080108032240110f41e20710b5408038006040c48420b0080b44c0c0c040d03074000c1081000f44030098024160b43c0114101c0501c50152041c00742c0380540600400d60003031070b0030000903c0c03d03007103076810740700240800c800341c0e00043e0f08192560408860300f5051446030090a10b1155200c010741009041c42d41e90b004600340c3c0952200401150701c001039015040141210f031404884081c2404940400c0c0c0b010480b4401c0307800e100e00050315500455118060b9005450310301c2d030f404007c058001c051264002080e005a0300c00c00400c1094140f90183c01050b851240b0309000c1a51541520074a000e240c00c0009240c00070075100080104075103098000780400c3c01d12508103030b0241c55942d407070b80c41c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 632059388 1250 632058138 632058221
    0x6041a070c030243030b0609010f1e15031d1b13091e0605010e04033006090b040605150409022a010e06150307140f04091203 55
    0x4100e0642c444a65082d4102071044003020325244400c1540c00441d4444c1e41188401e0728034410481c00b040311420b02618140c10b0316511000358804602d40030204040c00c0d00a4010494021501400b14400e0100e25619001810b595004075141041c58035007030345020000450b0903d07510150760148035040100c80800200b008903042c0e07404409203880b94020f04800c0c07800500307080e041074001d8070480200c105003035481d0191204001903070300d416030080082002c0e50b0203804105012414640c81d040460010324000e40c400c00d440c04da40400a540d01070350310301e411800f400ea88030741c803803e01390030603100d0000100f0045a6820303030325183c0e1000c403040d4441c4d07010343c004040c2c001540c0121144504103a0240050b0094207441d241c02e0003420314000c1118149002c0c00c2e01400000c510b0340310301e42541001580d001000750411501d0003859040701030b841d0801540250a18100c40d00355a5a8440c6524160003880301100500000fa0001c0465500d0440ca4a03924204100010f1502c450f400f117029450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 632060638 1250 632059388 632059423
    0x609070608151207050402070309060e04140408130f0f090e030405150c0114272b1403040f031103040f0509040305120103120210020c030d09020a0806041a070c0302 72
    0x25140c048582001302c25080300d504a400010034008150344984400c0c01c485080d950301c41010000000c0006581c14034540014040300400401c011035400c20080c0001c40c0750046100a403607442038100040c3c011548201900100d03003001300700c2c0840c2400384a5641410340080d514040c108000034019080448014981c00d1020800061100d82503200c44e007200c0c0204e450807090326101049241841064400034003d0f001940c0c2446a1030303001415510b1449501600200c81162400c2c5561400d000c011076810000400600e030a042d80d400000d5016600455111540c1d60b078906000d4070020300c81181408a50080204011440341a6171140c00d644044940b106140c0790f40c1012907c41c0a09600b014200c0741c0c10380000208410440b085804200a0302a12411464484004101c0c0244046801c180c3c10800144011250760741c0300418480c402814040550b485141c0c0c58038250301243e00300c0300c12070780f090b038209045481c442c00b6901010500c0d0014680440c0c2d54001d4481900da441c0c2c3c00810b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 632061888 1250 632060638 632060659
    0x114040e070b0919120c080a0209180a0c08031b0a0507122102070807050a0b12090a051002131403300d05040b1815070c060608060907060815 62
    0x40c0d4541001e145004c29a420580e002ea8440006458248141c0d1044850b1000d5000014040c0c0c404600b810034140c000b04210056599024401500c41300322022250701e00030300c07400100041c0d0306041c21018110080045407550002d00d1052180c1c600d81745060202d41c40700000000040c4001040300030fa4100d210301c02115522468110154038444400140e0f003040d003203a0a8a0700d80c000303610401c0300c40d48002c0301d0b0b00544d55424440010b403107014070038620700704100740d9004050740b8a03059007107090382d0100c555000d43da442d82810700340b089800010351a000141e50001000080e070701400360548004103a4244a1100040e035211714051003458400040d0324080d95a032216482c0038016600b83c0f007400c4c6e85451100c82100104411103040f00c80c0360020000c00c1c0c1c4c0504034088003540e40552001041072060741c1510001d1a0b400403c44420090800038410002d079480c042c400081c101d00d00205120300340008858101040d941000c0c04000b540781c03c00c228510802020303140d07071505507200c8004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 632063138 1250 632061888 632061907
    0x4120302160806070207090c0207050105071b0b0c16061706030c100f03050c0304020d24020d09020405060405040201391b0602030f07030e061b060114040e070b 70
    0x28501c41d5056031044480c04040040e009801140d4148603048a500340c1d10f0841c1c0f5840004126074201040a0050303101c00018061540188018200d0368001e0368102680d40260b04c00e8130030292140c000a148482c0820340720050070042001a0403035074001210603145051100042c800266100700d516900350b00e001040c05034409005040054001902201010410040242000030140d03a0700000a01c1c4c1070000d034003000740e1001d0300c0c0a1a40100706100820307960b140c14084079521420b10740c0c00780ca004000700344040c4900c02040da030000c0030b50105001c0c403180100000c0f100e00400d11405035003030130b0030000180e91190311b441d134554150301c09090b100303490202c0c620031100340840203d581012a051205110720000742019104500f07941a1100361100000c81e01ca006a600d41206140180310794030000340901100303090020064245800c168202503110100d050789441c1207001c0c1c0005006202d82a90350550000c845400c0d1024888240b140d821140e50760401d2007040141703000070505401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 632064388 1250 632063138 632063143
    0x3140306120706020609100905030f130b0a020a03110c012106090f022a0307030311220812090f0906040e0d08060a3003051e130e01050604120302 64
    0x4285501000320b510007512040040c1d6256015203030f0b0f170f00a110324846105084032901900100650101c00b46081200d064911070380d03038002d101d490b201060481e01c003180c07a406003809040b030200c055000300480d00c418200603114075481d0f501144690010007501005903001280715074041500710b22258080d81c1110010000c1c001031b0883c0c5030070350501c41105103032102c9401408103c041e81c010100400b088101041441c010400030320b0703103a0024803c0c03801080c001d910204c0d41200340b5140c1440c2c04120840b13031841803160900804c000c80e0340041445071605c100300c07413100440d000000324604015440020070100c41d91852922440b1000009540381d1038581081d00241270710801c544440c1c0010310040d11000302242c0c0b25024584107400014041e070710445542505c1641c21019a940c4801c10380180b8802c0d0904c400d034240f14080201e06900090390885000e42034049030790170b450754030070300c284004420144e105a0540f40000c0c014400c17551f496040300d04440d402c4150190b0300300103150990 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 632065638 1250 632064388 632064409
    0xf040f020316090b0f01110a200a060f02120906090f030a08040b070b06030607050712020703141f110a23030109020301170a0b130201020a0b070e0a090903140306 71
    0x4020810b01da0001da09029504882800c041c00c4130844000c0070090011100101e09030f102002503801030040c50040303076410009008440e000200000039003128004144410070303d92000300016844075401c010b095040c07002c00386240720308482c2860300c5049400200c1c50701a015900740309030300c05400c0d24a59a003c200003806254072007070440d15140c0d101c240304025004a00c0070348038094240b00180c81403402084e010300c00c00d10740d142c660600809403a003184207401e901000f002d42c03017810800f0011800342501c000344c0406640c018404254480141c081c200c605610032400242881d0800c004865060f05403480110340340b030124110301c00d4100001203001c1c07003c1b041c10380e1320002001088040d40c0d41c00a5068500c3e03034034841844040c1c15205c594448181c10040d000440c00701c049148002140c181460040c0148101c0d05200c280b034484018040c800c1d0355140110751100c280d629281842c0203842c0c0100300c0d4010070031048000340c80c090700040e1a4103d9040703400c0008006906a56030030410b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 632066888 1250 632065638 632065663
    0x10f050d05070905010f052505031b07080c0909060a02130f06050334081503060a092109090b04090f0606030b150f19051206040308010e0f040f0203 65
    0x1d1007030307041c80c1001404024450140600281c41203800541a6000d101241c02611005480d6030703920103400e0104e0000c490b0200301b2505400304005007400e0498219009880000c0da0000d04403052030107144506d00a50808108d014418040c1006088240801c0b05640014070319405030303030b80101840810085c4140d800c100e4035052a100003042a981c401d014620641000740c0f050038003004002c2e0701000100c1e2407400019802c0032504100c4c240d115003c0542c12a2814a440c0f0b044282480001d04005044803e00989991140d50000f4851070300b9020100e6203080045da503104035543c00092030b206244c000c40728416224088107040352071310307400030a1590700500250b40e00c0344a0718001c0064074040c030080d40c1100084c40400c070b554007681d04074107403e40d009207207040b03125402c818081041d0402c1802d140000b0240b10000391030700c82c1d1031b8222801000b42c0180210b45850324000d010064103800c04005c14800310104070030784d08000c08443d00a0703000303440385002040501c000307482e103084204503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 632068138 1250 632066888 632066891
    0x10605060403031106060409020f13110d021908040c090e0c0a1401030e19020d06060b0f042d0501050702030f010222080a0c1206090215030f0901050103050606010f050d 74
    0x1003459480181d0404090404e425151076469000401041e106c40c070f00f019600c5501c0d00003000d280c1c81c10b4000c40c000c0342804000400c0741110641030707a507540c014041840800d50000756650759603180001440020585040c081c24501b055102d110810180b030040b011804d81d2900300003105c1b0003c000300508a000180a024a1a25290b24482942001d44c0c0d0501003402d1140c06d00d4100804100307102d1800004409030f01c096130603020800c199001d0003069403000e41d20350300419100e5440e8000d260f040d000c2c610040e9078624201c840414141140d40c9030300e030b03d0380c940c00303041c07201002034110421a80c2c2481d18039215060342c00020700b0b000b800b41c0c100f00c071580300007001848001ea2000c10011190000c0030403407100c0d6180709854a64003003841c001c10028191000780950140c650710f107000c4500420000807022502c0e4042204085088848007640303c0c04000c0144e4000002e400d503610942400080c800c951542d0f6815583e2035000c0d201a06202ca43d29802c3e20491103402526903017402c1010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 632069388 1250 632068138 632068147
    0x5091210090602041401080f071b05010c03060e07030203040c0e040519061506020a080a031503050f0610081b090601050706061d01061803080906120708420301060506 73
    0x2d044000358003503c07a8100701964280079142c03030341c020000c0c0c0d403007032180e0306c0e2442035a901c07141c04540c0f4440e00c404460750024803809880c0130a80c2481604011180794030700042d124100707888008882402801c070020140100f0402c00000da01d44901000c4442d25105038216441e94a00103061056a000c0c04408108280300f050074401d49822008200d200700c1d4003441c682d0b4482c84103e031135900800c009003e072a000c1140f21a058032030f0717000c0e1f240303882d00700c602040719900d9940d100c5c20010301c602161500c0d400501482020f5650f92510402001c0300d1000f066002d601082000841c0f2100004c10302ca1001000043c4036039010f8402c0b0f0f50f81030f500002c104490768581d9254100f54140c03140c2c441c0d00c2e048500c00842d58901a5003800d812800c084850180d680c5580d032044030551000a407550032490a10981c1d42d40f07400d0b0710003d030084103c3d440d02c0050b0b103031102011820070345e13a004058040c2400038030300d4184800c596040070001b605000e944400102503000c02c0c0500440d40c40250071840018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 632070638 1250 632069388 632069393
    0xd030b010e1903110301020909040f0302030c0d02010605011e08042006162114030a0609020f1c020f040b0c07080f0303070e09070f0804031101060801060609080106060509121009 78
    0x60215050f0780c420400c03a5001c19444043c03500b01d0180780190307a0000c00e00d07000700c7c3c04503d030b20b1380c00c1100900c03c0c41207900d000640c0302d1842c2010b444540010150b9141d610611240d0780150890001c00e00c441c00104100b00c841c40014810400548050128407034001b00101c80c1c14101721021411802500680d0744600708590311030448a0103009880d002014011900588031196505101c14031300d649001c521909030140c42121b0381b02502801350b140d594000010840c12038000b4020b00c076518a034080d140d055403e00c2400c3c4c402ca02c2003d1703480341d10410400300298605800da074240d40d0003004103078840340400d03495450306013940c001503210b11641150b00702b0014004000e40c0308002e56600d44082c0a511018404500401e0303541c0d00c04104410741042a0500c6101c1c520f50003402894212000201080c5e014211512500204040d0b5184d09040c00702a802969140040c1703005130080210610302074000b0807074016128200e00c200c0300c1030851825540700300801c582148c50070030204034040291 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 632071888 1250 632070638 632070679
    0xb370f0f1509051014131b0e0f0103140a09020a0302030f161505030109020304060906060803090103060605040b03130f053c12090409080301180605060403050d030b010e 74
    0x14890200c0d020300f440d0000f4501500c0484900460350305000f01c3c8209543c040c20008140f0050b07495803480c03651038000c031403041104c03400d00241000c540c50300401d070040e560174026a41942100141410f0402051415000040000503880310700700900141210350303440058440c214a60003c0e5140c8500503440394080304c00314001100a1100140344034483d501c030580b1306e1000340d9105c1200450340c103000402c80c0c070b25681c00541d403042c0304d01c00008903501c2d640c0c0e45000f2540580c02c0542c1da54800304405a02d942c141c0b14010281c5800d0034203034240f42c41c0c072103801c10350710004006ca040070101c070003c1010007018480c0116600d91190545090380441d00002c00400580c044003002088150001071454039221003c03a150010351016018542035242c98079581e0780f061036841d8200e50b4440c0c0f5107001c10301030000b550181c66212a01c15800c042842d100c800da88180c1c0042e803068100b00000c00009000181c078206008680c240403400b00f00890060701c0710000303100c50b01e81158180041d00004400b5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 632073138 1250 632071888 632071931
    0x70501020309060a06081609020d0209031b13060f050609220507030f06030f0605061504090516170f0c0f04060c0c091a040510030f0b370f0f 62
    0x80c8204000b0740e503096151f0f0350700300e4029041d04c01542e020081c843d03e0855001054600b5030940c0c0946801156000f081c5032003003c0141e8440d00f000303130407880321515120042181224130400140b1041e0b040c01d5040301410024890281f154800244507451600c40c5642401601001d2000b03480c11004400d68002500040741c8190020785410b80b0704591403003d214000c103980d04801d1300d815042e51591030000800300545480d9003c021202f10a0b504c840520051018080d1420b0108860414496040541d9212a000c005005801403404201e1541075103080c1e00002407030318401e0302d4807800c1d40500e40b88192025401803400026011a40a400824200c1a248070ba0380342151290b403030020100b01e40071005020121614102101520300c0d054201503000b10003092050601d50ba01d90341d41698035020391040310051618030030001245c5150070718802c0340f06403003422010f00d081020100c000181e030050421105984070110002c3c48600d520081c13811034541e5041088401d0516049150043d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 632074388 1250 632073138 632073151
    0xb0d0f151502061608060f010314130308090102090607150204030204091208070306211a010303080f0901090b0403270e162f031e0415050307080610020307050102030906 74
    0xa1600801c1d04000c00300303416441d14282d550780101c1a15106e0030003011502c0f00b80010f0402d07403145204120600d800740d22070301903101d5601d072804084d15482d02400d83c01c0010f250b41501c0c1d00c140816001d9445080c11200d10035480403400500d5011002444000d02072030700040d4000749061440d108125042c1c03411900b900c0a507e031888107948543e03048050716130302d000d60603941d40c020550458001040e83c0320f10142c2c0c498411401c08590050301038691000990060b00050080c105214000b4442240c213074101703001a0080c0803d20f2030351501810200090801801c009413542045880c03400c10601000180302201c0d6400306590303520700d1401c0c2d15826548910100506154144007a01490055226228603c1c1802c014150440318a01c0103203603404007403650204010b05580d04480d000c09070b004010480321645c450b030902901e1082c0001509240c41403250030010300c401907401444956205000705e50882c82c0b18550320b41241540149a0010802c2d030010041c4080f456000c6540d82c072410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 632075638 1250 632074388 632074393
    0xf0f1210031505151903151b0503091513060c020a0501060501110a02040f111b0106120201080f100914040b090303042604050a03080702090c040b0d0f151502 69
    0xc2d00c07004079004441c0207880c0e5041400000b401c0b216282401c02c2002021202c2c0c9000000381c607a40c0c0c95000d4912804816041c1c0c440d42d07200b418002c9200b1865020354545589002c81c207501d008800155600340c010f010000e8039100400041407622000307609400c3d20350048040c0000020124003a42d80c0f0305e922400c640a500f01400400d00d9446003c010401551071780080a04e03c15540031f00000b800302421207503010743c85070840c01985942d14010681e61040303000b1030750804001d400c05030840f101d6400601c03418080305501c40160307a0217026150041c00301600030f80e2503151041d03038220800d1980d01181c9128146028088120103e051f0313284a0b030f008a801c0400d95490b00e942c240c403403100b21001000c020140403103154120403480140c44129514103a140f40580303840014140094603441150a14000230f500004c60801501d80c0350044c554a03145070400e0300380390610b4164050358040103151607a0b03100e02d1043c0b40d6160007041c0100c00f201d00030260142c41e01071486030f03446020400000752 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 632076888 1250 632075638 632075663
    0x806060405150a06080603010b09011d100e06121f0218100503070c0f0b040c140907020706140418051b0c06060108270319090b0f0f121003 61
    0x10040b190a6440804004010000c924185541036035405005440a41c166588000840c61529440c00d0384c1d018000901820703500840b00300d0703584014440204070417650450f0030310030030261780c0711828140c2000c0e00300c4410841498601586140010319850a0b82c0c848138040220b4000d40294000e0181d0202240240395420060040c040c071442c00c24200400608200300041029201e080d10344810380c8195805844034205807200500c040c01a02c040d91076411004081103d0600c100030307800056420f5820464601e80000040e403580e205110b480144401144810b01041004040307502038844114000001120380d088900149000c03105841e17401c0074004030041c0d0388039010a481940c0035420007403081d517a65900441d800c050140021b02c801102c44018120854500b0321900b94848401c01141c83d403041e5500c01d1002c82d002040c010500001060600c103d5400c0012140740c40c49111b402581c42d40b00350140c21152240c44d84c03840b242c00c0c0e858280192300f131203143d10380200c83c003c01c042e4009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 632078138 1250 632076888 632076901
    0xd200a26122e180207080c01060b0324031e030408060a0902010206060303040b0313080d090f0507061103070605151c030e1806010e03120403061b0906140706150806060405 75
    0xb007180750103010780c081c0d12850b41040d83d5210342c004190300b030700c903070149410000714070000382c2034844039000710f10000c40120030400e1010010b540c142800d44540c807076000b40e200901c007007504c40f010301d00141e2036203085114183d11036104004613401089000116550780c54a101000c2c02800c0e610012030050281d90003043c2c061034000140d0f4141c1b40e00c640e1300781c950340700d90000c0c3c5050070300b000d0704807407214051004500506092040540050050301040345800c91480c28a0416800307410600c24800420f90200c50288000141c808541c0c2c422000a107a072074456030300c800300c1012114540d0140c500101d0900381d0180c400300c000c81d80e1081c3c6070940c0d005854070400641c8a42203400150400720140022a00c1d80b0510444010795000b40075654503a030700d03070380c8444c1b540e1007a0010783ea0703a500d07009082003511010542085041c0300e0b2501160184c18080000c02d5045900031498000d0703000304101c01400041d900c034100c0010300905504c00b0035602e4075820b45a0500300e0706e043c032603460080096031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 632079388 1250 632078138 632078221
    0x509150109170a1a190e12120f070906020a060f0e12190c02010e010503100b0f070c050d050a17040905040b06010e1807030f06080d200a2612 62
    0x2c40b50143c060400159000040c0e00030411150306d8009440f50034038404113a042c540040401021194810740189040c91040d52951000f030310f02420403000007810401c1540c0030840d80c0c54182c1c4502d01203207143c280c140c40030107095641c060403428041c881c000c00e941d14400006160141c510040e6000e1403000e1802500c0b040f01d140e4002c1c2c003041c01c4010300b00e0303150300c102c0c01541d0200c00410302600b680c1c0c0714540c0c1192504004410115100000b4120042c0700003105410010700c0308559050784c3c0f00c6603503a225158880d4000003044801d200e050f07003035914807500c10f48001c0c141f0b95004111504d07190402120040301920481d010501c01c1d01e50b0300103410058014100d4800c01e90034800541c0341d01c0e00c120010140303010060343c040d56030f100108044c0d80c1808020342d003041913900d09803812440200c10720b0550b000c0c20401904e90140000c90002a0341c4644240c28002008400301c0c070760352590404c82c01d4825540000c13000c0714080104640c00c000c8100c84002400e5421725a48028400d13508000f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 632080638 1250 632079388 632079391
    0x70801060903080d0509012904060503071a030601050c010c0903060b03030720030307050a050601030615030507030f210206270709020d060308040803070201180509150109170a1a 78
    0x82940308100604c4500d501aa00030700d030042100c100004949420490080340b0718044c4c407081400c080ca289580e03520b481c2034042c400250070124041c2500c9440d10700e00c0501d0300c94002400d840d4020200009032a03038007400030780e03203c15040c034001d0150096101005100c1300c01c41c002101c2c00d610302440690641000000e454400780e0002001044410900303195008450205200340e15100400107407001490a000d2410707414440d00007000745504514264003500c440c5a10100b4542c0103410030000b041000405d10101d030b03001444038507202d8980c113180e0050f41030302110983c021080d242d003000303403580050054422140c8020b00e408204180d03003c83d40c8140610743c0009076030300907071003403100300344039401410610070b0b02e0790005405a40b40d54070001d60b0095400444d143d00046280c1c1c0035941c004200c15541034545e01c0680056060800042d410003010b040c1020b022200584030105901442c403034070241003040b0111032881c901d603900594500552408503802460081960094402103d015 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 632081888 1250 632080638 632080643
    0x3040806132006030a2c01050a050105010311070807020a0f1e0608060a0306110c06040302100501140603040b13020405090d1404050109030b1f0e0105180f011a0c0d0305070801060903 80
    0x56185444183d02c8401500640d4000c21b242c0303144c1420707080f600140043c07010540041c140042071074509500d5110880b20140d009074141420540040d84441d0341d44101c9610719849103003552166001d001007001450150804500303501c040e03401280200e11584440340d0607803825600c20361503856180c01c031211441642c845811600c0c2c15014000621103070005804400002102410505502400361403e481503c060303025802c500c5180f02c400009010385809032001445407501024040d0100384280300081c0064261a07a001c00310b01025241c8194540003600100103005c9400c00e10841604e413519190309101150841c40d0b6a10600350b4801544e0440d41c0503103e109000345540c8902541ca0300040c000c00030050b0003c4c010900d00e0358200f081004e41144a81c0d0403c942c10b100a1022041c40180c111007000b100804202c043d660001c855410342d1f840700310000b04020603807030402d49409a26845485809020071040c1601da144d44480e11929150b81d5017203136a40d03556000c0d600b014990001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 632083138 1250 632081888 632081899
    0x60f0e1b0409020d110f0c0d0207030215091f0e0a0509061003230106021608010207050d051c0501090506040b09040309140f0d03020c0a08150105040905030408061320 73
    0x20803102c034456014001013440c10388081159020203542d40380360f9010415000c11580080391a9001d0300081203110a52081800100300d082c1c103603000135184200105041d014100700090b601101e881d000190b90400b6588040302419852209019210004141041e80944070143c0000f40c07a11780140b0060003410040e00546040d00c4448044015042d02e070140400662000c00101c081000703000b0032402801d00b5070140984182646500d40b541c42180e015030410783c0144031349000b242010411512814490030041d42d07038181014801035103c4201d03c1072500c80e1502d00000b8910606400852042da001c036020048134042d0010010080400c2d00c0140004003500414060a204400125182d000080840e200440c540000418800c4040d0040303006030401000300035641004442000a00490400303005450041d00010301040d038148509031107962100c0d50a02400818404c80e0080d059500640d046440d000030342d450610300c3c458045a1040440240002c921400c002407800104002e12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 632084388 1250 632083138 632083147
    0x1c03090f140a020a030b0610050304120e130e0106151701060e01030b04020c0d020114071403060a1706010311060a0e0607050c030609010e0c0a030503040b1309060f0e1b 74
    0xc0760301c0d0039090090701c0c08881c801d00c80044096519401920300a40c4594142c0360245405028020285c240955600034454207000b07010020b801c21101112010980c5071401110720302a00203407418407a00307401890315190a000000d0050190041001d03a00d000d184502c0002024a0485040001c40300c110515003042d00103002c003500c20030b00724001c41340524000c0340780d00329100040c0803a0b100d14074010701a880104c40d13101301c0e6028040c5a40e0001482e028118519240e40050459003215a02e18845000003002032a10b5454003000c101074049480501c1c06502607241c51030b540c000a0000781ca080c02c00b100d4017141483c1c010100c0b2101015076a940c0d01c1564102c040c8121500301600c00c8996008071581c54940c0d803010814184071b000c090002180362200c00424600b451164880580202204903082c00884c80002c00c8604494400b4646682c1c0d4050302c60003521545590400d500560400e08001441c42e849981c100c169245605050300e41d448041c1c43c1c0d121b00c1c00302101e1920122042c413 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 632085638 1250 632084388 632084393
    0x60307080c0c0102040f03030e15090f210a0c0f0819060e011103010620070521120d0e01020306030705010e040e07090905160b03040b040c03020907021c03090f 70
    0x50400d03800c6411820458280742c80d10110a0036600581c004090940315041d0030014175500140520041030701382d901500e1042c56000118441c030440241502524010010150340c1c3c0b184440203180c515100c6240108801c0e00180c103803218100c8100382d4440350350510218a000300a401502220304080041801e048002040320049952403403c1c0d403c2959505810541d05081c014010322000c86410540e6a40c1800c40140505080035080352068041d070f03a0540131460001024020364a089070304101c03400f1080740c5511021000120b00140d40110414450111664006031841c0043d0050030700c02070401c12401e9080b07000480307500c5d17170684c400348080000d03501402002c011000090404110340c0100d43d107252078502c0e2940320108a0399036500034424000240310692040c240100c042203080c2c0381c5080b01005020151000e081205000c01203010040074090a10040d03a02810031718032441c1c4140080c0d101d4800c0c0c00c1c0000380108001140401500c03c1c4551503510341c2c00345c04525846280e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 632086888 1250 632085638 632085647
    0x15031b0c0209100306020316020f010902010203033705150f1f050d0e07080c1002070e1003020901030506070207210b040c05090115030c0906090909022d1e060307 71
    0x140c103140350003203400340c01300110f141800207510075041880b2900c0e1a1001400c0280b80c0b541400c0840381d66454001a00011b0382e021040300c0d0080d483c00106080456040080d100c03501e02c0100d0464580180c030503510807454a9081b0a1040543c3d2641d4184103040750207004044a036100c5082d0f100c0180098110010401d0206d51100301c19454014240a403041c00902214840000d40100703520404e0b0401c10058104107141139007a040e40e0f48215403005c4400a07650b1590f5000d0072803416501e900041c851091140d10740011078004013812160351b541d0808a8031020103039110401401070305d1000c64403000d4045000d0245040381c50040410f9096103a5890b4040090070444444000c6540015155994842d19019010200c1d84100d407c010742c20144c1120011044c1c1c005000900f5000c1120359003141c9200202e8080d4040170440701030b035100003a1000c1d24014042e10741614026000c986844000509880d10415501a5800d900d202d0199803c10a034150300d6520403020000100820b208 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 632088138 1250 632086888 632086891
    0x9022805132c09010902030f0109080306011d0301051618030320011401030c0f1707031212111305090c030403030b0a03080408061909031205071815031b0c0209 70
    0x200e52815480c280c18030302c020880101540c40c0c4605070f44071560f55095143c203001d100c03c0c0821060013009020201d590b0184103000043c009410b12035001d5942d82d2001341404590700c0000300900820061401507080381040901c5c14031800080c03004001d4524049071741403000180c039010303159516400305a8203c000e44c80c901c048106070729501c0e180ca4210035030601c4000c0d40613620848030800d10b3307414000d010a086100b9406440c1407001340c24684071410001c038000c0c05890308618180b2030441c00d60b00c203a031a02e00c0c00d40c4507010a1b2412402d015185071010142ca20340007606040040301da560302c00c0080c3c0c800103844c0e4150480040001c540068001d901070a980000685004901556a11380f07150030740240e8081e10681e00081d04000780c0c454100d9078106407001180e402c0058080c19100140001496400c640700c03e035a990100d2802400758800c1244d80b070000702000300a5481e0705241c24040203924070880481c1c01d10f00e0a0304500f2a0b8215681d004c1400da58410014003e6000c00c00803000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 632089388 1250 632088138 632088179
    0x70f110c040b040905060c191e120e0d02070302040605030703030e06070f052a0103060e0402100908190b010e010501080a0f090b0a09051e0d11070902280513 69
    0x6131182c00c140040c005000aa206403a0143c3c8540c5a01c00c41503280740200480f00303590100701030b0180c43e00e545101800b000250010320f18081805c4000c0d071030850300410800070005014401c013007110206a034000340320f80075030303100b90780c1400351a5844007071654032009400b0040c0455001040d00c44070f400c10901800c6401d0003038880e031041e42441e0f01d89030b050034000d10003d92003090500c0e5000c0708462029510228003405e00e802c21540f407801549540300e02c0080c10091003000e00c0c01c1d140f4011449941d802015010500c10384010070b00207581c054407030f5000b240403289900000000900e89414140140c126401a100d82d204c9a0310407003d48001c042d840c1c03640c00615680d262100110b99410031083c82820040c0c0d001924a20a0a029291202007202000190b40c0201399a100200100b250811208181003002c0ca40144070005403c200d00d58015000251002c1102c02127410304c03240e180f201c56407008074403000c0386109008454a11a00090411429403000c0401446294072102c5c3c48841 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 632090638 1250 632089388 632089391
    0x20a05010206073c081807030f030c050c1e490f080c0616020d030209010e060d06210302031b010f0f1e0203040b0f091203010e070f110c040b04 63
    0x100b58200614804c10601c0b00c0c01c2c002240301040110780030880f13007030800101c0c0c2800102115441c5641d080800d005180340101000b84035401642041820000c48020100041054442d0882c00001c600d000703108035221841144080444496444030201018000310443ca006980141c0c800d0300041c046079100d04250f4140301585070340d0114200c40c1204003101c3c4610040caa0320210900400e180840c081c0c170041c0c047c1800c0d040c19580580010f20030f01404040d040141c2c59018500c0103036449805800340c02e401410005111071015a103500500559019013290344000c1c0d04030f80ea040344200382e400000c0269208000c6a001401140c1c61844d400e40d501d00003007444d450400201c015110f1440310022926154103002d0305098854604013038001821408600394a81a01c0314030701c1c00c1e4050121240c100c04540403e84901040c81910100102600c11581c3d95a41b4000403604810880d0070303c00040c0c0803012104900d1141508a0308a140d50000706000103c0c40e08000c020510465581c0c1d009 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 632091888 1250 632090638 632090717
    0x601050318010509011a220e0705090f0603150f010603020711030d090303030b0d02010c1202013206010c051b040e1f111201030b0a09020418020a0501020607 69
    0x5078424010329204580c13030000415491111402070200301c415040440c17245050030302000030034103811590300100c180300602041111019411508144164001d142c1041540040001720000300e80780c180250410307000ca400e18000300c2001500040103450002c2c00712a141c004010030707807207500a005041c3c010202c0d85958210003000902d881040c840840104803080c1c8100305141c0c0521904100d1081602c4085055100358002400b40c0200c500007409802c007006240c110fa80f00354491094000308009003448813603c580303408800007148004030210840b100c00202a5403040713200d1807020b80e0043c0203107803c4107180c0c3d0700301c400b800310f26001c0d42160b5100c00342c03800c1c05001c2011408034403800001c2e65507804680e6000017500d00c2c640c445424000d042100407465804031705503e0441760071001588441e20b440000c00d02810601360040d511508011041c0729107283c01d400c6005080c401c5850021545ea070761700590701d81c1001c41d04807020440089095000b1200d8035204003182c111030104441d0fa = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 632093138 1250 632091888 632091931
    0xa0c020f0d03120f0b151e0f0c0c0d21111e010b030c0105070201110a170a030f090c05100207090501060504081b030c012a0b1509010e06010503 63
    0x14515030140542c00621003482c140741e100024803404c0400c3c254503900784103480d400740208107280403403207071580d1004000806140030041c080c8040641c0d441d0804c083d9850080380381d00c40c091b41006a840c1468010240840307034a1030140341c0c0c4200b403a40000040204440041d0802c032064181ca03861082c08003503540903001d03010a0003203074010005100c00403455031503003071028216461417245900a600140340ca0229030b07003100c250340140d982481e10158041d070600505c2c0c208090044014140001ca420b410204070200e400342c21661100e680411000303000c10700720002ea5100c0d070006030000480b04c005200c01d09081300d088020160030700444504550b00c92850084032000d9010200140c1c1c04903046c481308a0038016510303e0303209070310080c0280c600c11000a4888481c0e410b42030503c908404102e224050800000d00030350000d42c00101142103606202d4000c107400c40710b6901003509031046100c1441c3c1a000141610740b10140c0c03880690340c0000540312a800648170941b135644040e0030001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 632094388 1250 632093138 632093149
    0x220309030f0809040e0f0c030a0f0b1009050702070303030e01051b090414100e07020a030f081003120e010f0c110d0f02060a0c020a1205031c0b032409030903030a0c020f 74
    0x5030094945c0040010f02011280ca506003003030103011074407a070000c884240c04903a0300d034031080b001c1d9040007c40400e40c5405804104c0c80700b9036030007464828148010041d1081d00440c2000440b4042d8a0520014007007000c024201d40c82250021180d0002c0e5982d91040c42c000e00150015501c054030000300c15910940307131800140c0443d12000811041d200074480400640b00315a0080c4d120b0000740440c14030b075030b00070703002c101d02003010000c1103205400604004081c451000c011604401e0241031001004002007044400100b0315000c01c0401007110000c52044900a1020342c204040426158849040100349810500240c40c210b00781102e20003d42e40783c10041074080e04a899401081b0340c0d910500500c074203144d00c145601038030051180302141003c4101c901c40040c11117000603003500306c651600201503016003980c140c4100803c40e0502105d000e114244540c05501c15a0035980c0e4040c81c65807441104601034160b0030504c20030004034041c001440c0b04130302c010481503981d1983d202141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 632095638 1250 632094388 632094401
    0x309150906020904061a0a1d10030218010f021905011410080c030d0e0f1909020c06060301020a020c0d06140c0702040c020703021c030521220309030f080904 69
    0x1d600c036600041001480c646071103910000c0c00610b0001a203901031b02103a0b401e900400141c1e4003031007000310005a0004072046080c0c40410700403c0300701c21050130b0b04000c000703411128038420030b58900ac00e8a01598016100103995036182e5004148528001c0d60b400f049280c4000122a41c0d07494160402425103049950717841208d4400b80740ca4401d14055203527142140712100c0e01c0c040d030484034404251582c000e048014074141903074041600f9070f0303c001059558000007000700c08218200c1d00400e40542039002810000403103c2159019103690302018201d1150300d09503005640400e01419a03810619007041c0400c0c01864000307081d4188201d001c108040495038404103000000c0d07044210318040c030501040d50700340c1c4002c0410b282160301086090400c00324000084003d40302c2441010f1148040720708079070040c0144a42000d4007041c090745060b0580e030690180442a00c0c60b40400c81d21300c1d01400c07890301a030300c0d40806440c6840b81c103406800e1150a40b80702c0d0013007003175000c651120302865 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 632096888 1250 632095638 632095643
    0xe010b0607060b01090911070f03021c08100503070b071106040f0305060615070b010501350105100206070509040209040608010905070302011202040b0405210f030a020d05030f0703091509 82
    0x100d000e607180e00005001708510b03003040c06500c5c5401640c481d8501c01c07070706a44c5119448180c0b0700740041c0300e0806a151584c00007001340007469014020202940c4041c01ca400380710303918003480701da54031002003588807580d500802c9c0026605000d80004039280c0341134a14503400180280d450a03407541c40e03515019080303800c15103042d07010354240070f0a4140a511102e4055a060219052001ca0f41e030b58280007806203c0c2c03034100328141344900e1201c1e9448030030810200e03410b90006002d0100810748690000244101441400020000700c060303400131407442e10441c420340d80c503864401d01c0d20800c002508101010358000d03503214070104811100b48140104180684010100b02d850b40c400100340f100c00d5440802d9260050004204001044040c0c50a4440840b01c0e04600350b00a410b554200c007240310f04060340c2c0300c0d00c000030b1103070360f0080020030b5605210341c282c92070002408002d40b13080c4019601c200c240e1200400040c0c41310702c01e81c003c2d00814441d500103e4041c800007441030540c1c1c00c82400f03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 632098138 1250 632096888 632096891
    0x1903180f030b1003150e01021318050618070305040f06061412010c0525020402030c030f070309020d110406030605011e0e0705070b0c07080703050d0507090510030e010b060706 77
    0x90040c801d1070b407405684a0700800300010901c0c01c598482c4140440e1001540003140c407400b00c40c040b64003e40548206081e4605202c0348150b132003001d03403804460000c28202c10742c0341101103049400e000000700d00090f84540b40c90542d0302c07400c408500800c00208140d82c081091108140010850b0180c200207110085904030250301807801c128070040d9540054030746d07a240400b103580351030300a0300b564440b402028050941080501e900c802ca040d050700000c0d8132500c000104000014030f00d01a501a800366401503559030f5480d1402d5080303c5003003070b001e58000950540000045c000c0300c0320713540072900a40f001c1170b8140c0d00d54520701034803401c0e00302c424010401c041c12400300030408000e00080c1494030450003d0708007403e01034001d206000010782868001750018442c0c0c0b080d0812907120075400641550b6078107590800a0440c0c1007032810000e03c0d41001c8c040790007584a09104401c1e1040100f0203c142800403074103a0051581d0201000a0b54882082c2c055903a41c54028104543c0140710 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 632099388 1250 632098138 632098169
    0x42030702060711101107050307121803020f04050408162316210f1a0a020a0210051306050c09010216062f160e01120203190318 56
    0x8000e410040c0040111003000003012141004000004001e50a03407041d40300000d503200301452581c031610070303d4001341182c0300c0044c07160704110840218606011190b5901603020f90511944601c3d20b2491001a500c1090a507140c552498241e020a81040c40b0b008801e00e4415646c10070b00c40c1c5042c00000380c8140d4a910340c002c0301040104211005002030f08050810041640c0301e86103429120b001d42d40d03d180401068241c840c0c03100900310441608018500400320b85450a0822080c84494500090307003c4000b144055042d4001e8400034091600a81400801000f1701401840010603d0010751038400035040424a184111070043d080007800998941880c000a0310308100d08561235100f40c03c121040100f00d0b44105c079801d4202c10303400c450151443c0c00e000100d2070481c1c2c21000441d4061420010b0b4407242e01e0001204440e814017450445a0381d921036800b4811003000040d405800103882d50880c1641d41904044452003401d101030050928040207251410756040a508403c1d40c5c40c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 632100638 1250 632099388 632099401
    0x140f0909072301120b0312040906150309112202120a1505150306011404090507141305011215060c06060e0c0901050a020f0f010209011107054203 64
    0x4034260a03400d40e0103040120b1046180000b01941007651248003c25907800360509150340034041070380104054a195a11243c4a002403001000203101d0320f2000c0c00e10811001c801170107401a240840d4001c1c2ca44480030b20f9030744c24000c1c6480407000f0f4080651070068803034402905071010b46800141884104943d142240c0100104c540003140e0544256000404004585c5e4007400200d5545915068940b40d03259403005039001d468041500e40d60407808100032500f18800e60015202c0c15150b40c034400b9503445000040c1c060300c501840c168100d010400d09220950040705071000c1443c0d0160000b0f407045107006000c0c1d200d0016008413000407100c210751000d001060143d4800341900c5807891002e402c101c401240070707100f21041c0b9414050081107503003425000b444a490f0050018064440d410407100711503000b0752201980741d0110341049401211980f0014002c020b4413000b03014002900e003080210b160140c10005001c191614412000481c1101c1070240107840c0802100c56032207081c1030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 632101888 1250 632100638 632100659
    0xc0305010b0408120a020c0324100e01060f120609020714120405040b03160b0a17090307170d090c0f05040e0a0b130b01030803040b01081204140f090907 67
    0x40e801200c003081d05002c244040300f00444d401c440707982040c103013030f41e9101c1d001000e03401c00030385401ca00e0b4540102000c2c04200041c0c045000486202e0000010b0545e60380726060892101c50702811500c80c030030000501284c0e01448411882217400e044c101c0c101414402c03404150752140d00f12011551300407400d83c007085415806206001c0c10314014040c1d1950207814081503000d544a100d120f00d81301c05000d44031340c900344134025248030f08540180c0c169807250300b8500140d1201a914000580e45100c9628151b219900b0034020701e6031001962800d441030321500d441c0f1501d0304107042090340401c08240c0181442c80340364045403145002c4414146818120300c604001d0f580702d207000700c0c00c01c0940c1c0311004000c901c1d1805690b115608543e152911004113020b0400b12070020009049040044144030844000d548512300c00c0c081d4030710980c9c03244000f64450f40d07801104c0154000074032081c4400c2d081146502e085a0340a0650b98001a6010000714114000d58180e08a41c000040600211000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 632103138 1250 632101888 632101891
    0x40c090509030a0507061a1002070e06040b0d1202120d0c0e01030203060310090c09063201140706020f16050f060601090915080105040b090706080c0703121508010c0305 74
    0x80c1c080c606025803064080e00521560031300800300d596401d84510b58404a102041c04540003404151140040030800303590b07020140076120f0354080710000907079203180900521508100c00b410028014145a035440058440f100c032540c150300a1514500000a41201414a010031103101040d00342071a14090003240c20011003604050040040019030317140026420000300d0302100000c3e92001a040c0a040000c4a8018036006400d0200009280401c062000800403c0b004003082c03041c1c210081c3c05015406048203804210b040c200344850348800009004080c0c001c84000d40341c40c07041040c02049500c44007801000201a40e11002801401c00210000c0400500104502d00b00f140000e0414001c510948001384d85031005c00d5080c24901c11a13900920b00f43d002844941480d250404071010101d540400b1407040c40707800510140702d0b0312124015034845032521f01d0581e071901c045615502c40c0042c822460f031202060594240d441000030000e000c104000514581d420000030140e0302d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 632104388 1250 632103138 632103151
    0x52a1b0301091a090705090c0702041113061b0605010611060f010b19090f030f0b160c020f0f030703080a17191806091115071a0c04030605040c0905 65
    0x160191038800600d4078a24103800001107542000355076030702d00c6445c0c54803205070400c41d04405a001840b1030341c000c5401409089200304d50a100359000a001d401d100c1c001c02d02c844c41d81445981c0204040c0f40903075941c441d4045244041c030301400b80354483c1e5003a52000c1e446040003807802414119102407e1003166000503209801e04900d500d07151403003c290040307210000301c014400ca00c13001c40d28080e040903001480b00c607814404140d543e0406100c50403d010003514000d202900003205641018480740a00700d164030f400d060a0415004d010303e0b40c98090b040c0340c0020720808010082d40e01000420700951180510729138a405100009010103039000110030907548050030310443c40c911b0501005052081c0350b001800304000980000c1c0d400704844017070007580c40c000089040c000724600c60b03074081e5815120341b01200d6409071110780310f110702400a0303d14098030b100c0d1244444c40711880e98200202c4e401c500d003840d4036501c6842c11108c0c01d0310110f032094044241008005802d010701c5501c440c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 632105638 1250 632104388 632104391
    0x4060e03090109060f0513080a030207080307150b0409020603090a030905180414030f0403030c0303111809040c151e112806060909020915060901052a1b0301 69
    0xa400740001e401c0403654003486061019070840d090f0081d114400340c031140004022404103640c1d640800d00d481d95103150040e00140a02c00c00450010000021204070700e51048030300a14039840400c4000034810f1807950f581c00794451401102580c0e070321010314001c044031006400011414070b0041e02d080c240382d014034052408480c81c225a80509046aa803080c0c026581403102803601010303074110711481001103001d90780410040f0901d0b40c000d002101d203070b20940b000c00008180e052120124007c5099003000c00740d1107000b0a0b481e050120803550002d01c01c122000300562680150304c1421201426800091441100c4041c03034803003000c1c074204030361250400d0355600d540755400b55110300c4480c00380f4140c05800c4850500d40e2020405038190f042c0c11000c01c0050503143c203d80b4000d8660130905a01c20700c040008106049407291000f01000360040c10203180c40718000c010740300303a0040c0007e2116051800c40130354440e144100007904004506000d40b28a8000003c00e141a078039504506010781e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 632106888 1250 632105638 632105647
    0x5040605031b0409061104090e011104090e070b0f180d02010203030402120f06070908010e06060a060e040b040e0f06070e032814070f051206060904151404060e03 71
    0x103450100354502c00007640e0b84a03104a402c1d1601040150920180007005185003c60303151085120001410603640d1065080c0b02c0700300e0b0041040d00307076046242c10b106041380401080255032420760100001104050503030790903660b01ca0707009103684c10070f04402c480a6000030702d1109031101107210f604420300071101c1c28401e100680000b5a40c0c040248000d000740244c1d0004401a401004012325140e10703442140c82502e000c900c011700180b038034410001190300f8421003001c58200440e8a901c642805800144228a032500c11a04000216070340c035006641c800f0040d4450f25207026007011700041c0402812f200858041083c9017150003003040781009403204407070480e45d9002c14141500400c482e51040d8451003480301588013842e00e680240212150325031000035400200e140c1080b14283c1500286403079468080c01800407099030010f055070049800070f0b49607c0d0880410350841c1c025a80c41c4440451104070404541440c0007588004605c8002c0100b04042c82c01401b01c503681c09000366050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 632108138 1250 632106888 632106899
    0xb040f05010e0604080a03031b030903020a02040c03110c071e06050301050f130e07170d02030304080a1418030601050d0f0605041518050c0301020301080715020a120513050406 77
    0x2020054014181081030000780d0241c03d036180c5003070707501402520b0709070b41280c89280f901400525862041443d8414520018803855020b40704c2c0c8208182c1540240031004460b500f004000c1c1070290540007070582e80c080500f882c84015020b400980744600c010601d80c2d040c61401c0030f601140c89007540c3c2c1c4a104030320500c005984102a28111442652100c0417101044000749082e058081c204401615040014484081c0090303104129003403010942652501d00510030380b21074a29502c400540d104002007400205070800825940000d031422138901c0403410380200d076642c00200c100c00e441e81c032040d003003c031f519080c0441340c010101126511031020b126070b10301010510042000d40099620400201030003c1c041c1d01c0c1c0682403aa403420083c1c600101824020801c1e4070b80280c0700e5201d40040a4440d0030144202c0c1d05030307082e140c001c040061504600d1003019926800070001c601800604100040300c10f65902e814142075241c298948014103030245410324107a10941c030030b0b030500908020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 632109388 1250 632108138 632108159
    0xb030f0f06040b01090e1b0f132301050d0323040f030303050f15120a0b181213151101020d0203070f0f0e0f06040f03050303010303080f0f1315050a050603070b04 71
    0xc0c640149640024150403000020320f5a0000b41d0600c1e8201c5149c8006444c940700560000610344940e809424149036100b00710070326a142401426041007034170340682c002c02d002d841c1007800303d0566804900034609003550880d43c2d8200780c1c0011085003581405004047c3c06010b202d0f40140704507080f0000b407612524080850034141f070703102c1c0a00f50450042100305424080e10310480c1d0040d501902d41e062502020080e0461080a0103450090451800c0100008c0e811110341e0400b8402c1d0810b03481c00d00503070b07000003080707641041d040c050105a544a0541c080c0040c00c07201d282c0500c016101c0c03070010400350005004a06c45000c21030120342d00707824182c000401c8500e0040681d50030200740740307410220320f007032059400246405111b010b001041150001c025416070703200fa0754000391900e6690a000205030203860390781401200c0800504104032080c1c440300b109005019020401b10b040000200310341090b207041d0000f540b1182080301905081001c40024126004004d01d8070b07280278004507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 632110638 1250 632109388 632109403
    0x41406040309230a060e01021b06030406111b0a0215070213110c033004050303150607020904051623100504081f110306010804060b030f0f06040b01090e 67
    0x440c50b2032100820f201c3c1044810050212100030f84543d0016071503140290902c49280326441c010310404070680e000c0c051180e00325080603406410703242140c4465803800050060071070401c401900600914201252501c0b6010440c42180c014084071151070051141c501c10b42c4d10010b0403100d04000ca8001a100d92030426a628031641c000101c0c10a809091141446038240030380580c4030110701d52500c1e00118801c60703860700a49102010407144c0c1c454604484d0b0044602401d030750010b00001e03a01705031246c130104a0050080c0034901c0c11180703500013140c07e04181c4041d540d5610075842c440d0307a4002d18841001500aa00e109070664138070880c19004141c0b40c0220501440310506441341d018000e0b002d582c05840402c00ba54030200b0f0640c81000c103000e8159030464034500303000c2e03d1121422404101c2c1e00600c81070351056001d0340d503900c809002d80030301c10005070544a107502c60032080105116801102e00114090950303428203061004030084181c000850a40c41c00300003007507107100001d000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 632111888 1250 632110638 632110649
    0xe0d030c060b10050d0c09030c06030c0513080105190e07140f09040b090c181513150812030601091e0305011109130e0601180b060d0203041406040309 66
    0x14140c0032a14112000c2d140600340035030040701c404503041030b1a0b0414068485480465020081400004011a01030400d4031001d0500c80d0020020f00c401803007500042c50340d03052801c0480c68050543c1c0342c4560141c007a4000c219503555582800b01086052103606400814604e05100040d086004036865000500c92008240a80c600850302074403a20500014010010208801d9141a05103120302010449203041ca038040e5941481325840c06406610b0b0040b4040c80721002903940c207414490002403c44055805002030f1818045003882e80200c00c0380c80c850308000018180303409807039460100c1c40200e0b070740b052106108001083e64801140d104030b4140e031180c040314030024540036018800344d82018000d9401e09002d100d0481824005114852094501d8100c50403031000300c408643e04900c0141058018400410800d11030700103c08010018517400524160680009021035000c040c4401c0f4a54000c000c100038400c1241440b0765020070500034003e1480c05a41c020f0003000a805403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 632113138 1250 632111888 632111897
    0x10090b012907080d1b1b051507020c10020604052a030a0c18060506070b06011101020c070509060108041112011d06060f031b060a12091407061b17091306050306070e0d03 74
    0xa4001e00c0010130817944400500c440340403140c05c1580c1c0081d0be90541040f900c0c050380d0440394211000d4400a5068400d40d0000082e041c1d40c01c2440150100b015180c1c0c2d1070350303181c8001058885c1c0b5035082c081100c0c0f85110340b1041e401caa1a09820350340c0d4129040d40008910315004c41001991544800c465000350712102d44c4a542d41c42c400142c802e80303043c640102d82d0758800b2401002c4403800045402c1a1030003129020610340e03800004448003001100d00602130402c03e0080c03400d0303040c030f110000c04580d40680040748042038880355a41004203941c031420780d6880744044c0040c07410441d003c40d2144078240c010b80440440d0044a00c0420150750140d409800c00141d5452007034456407a805d00c41c10400e00038080c2d44894100240780c081c5203484a201c0340070b00c20000403d14064504600f0304049190207440b03400752900e52038241040c442c0d24002800040050184075540c080c2e4820012100000020b41e0070300709424035140c040010080340511a0107442a800c0e0755901701d1124456500d03107403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 632114388 1250 632113138 632113187
    0xd0f1107020d111504030803091522140a03080115030603020d0b060d0204061d15490507060507030c06090218070c0510090b012907080d1b 61
    0x40f401380d681214107007690b00b034086408070801142e180210f0040d015501190b1110442c00061045c041040e030310404628461045107007040c0300d54800c00d4400d4040c00c140f4900040c032400181c14841d0500c4214001170820780140001d002c46002030f0310030041444c0070091542154082186103554000c090324400308080051036580c2c42e00160084154050024080c80e03644041044480400d1201180301e0003058001900900034441c9501105100030b020580842c8401209080c03916030f40003445840301240403200190b284901c440c8041c3c0c5402105c07644000b080d082c1541800712640169003000820005640440d605c03a4800010603000040003640c514140b000902802d0b8841c032020701c0402c1d1008018000c3d4120296441003802030013501c80403544080600c04940241c2d800415203928100188110200c14580e02c1a00c41010700850240002d148907101e43d0304580002c4501e007100103040303c200d02090007002c600d40701e04405070002c071210040107026140941c41900603d0315508 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 632115638 1250 632114388 632114423
    0x10b12010b13030515090d0e090a0225050d0f111209131a0a050d0b0a0e101104240f180b0d150803040605030708060f060d0f1107020d 59
    0x1002c00440d4402c08550303940d02c00c81e10641000000b06c44003c0ca5000f40703c15007109a0160440c0c0c20b0040000388544071591307428201a00039003081101c100c02000d042a4100262000090040ea050140c001000c03804400840140b0300c00510361000700304441c8140b044003520001502c522448081d030110382c2c03111048000320b109150b000742c541c24000d090041e000726022024080c8155080d050b542e4681c503544500a00c1000d00a640c2c006044021070700c0010000d4410754040081841d210064480d042000d210301029a03418404240000b90300007000c01c01c9207002c0015040111240e4032010940444034000340003010b40000b00800c0c030003da0b41c50507101002117481d2000e0700ca0300d00c60a44405e8201d8416004103500d003215031141c0f4000502140800002064404444640d99800d00e0b5039501502154115000703020f1a4210075555012a0726603950001307840400001100011a142075085020aa51102907001d02c412002c000c00d4026803600f08644040e260840041022a007541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 632116888 1250 632115638 632115667
    0xb1908150904030905040c02241003020303180102060a051312180603060f0503010216172104050706230309030c010c110f0102030709050d03030b1005040e010b12010b 73
    0x10016594041c00d9007007000209034022003040d0582d00180c400700001c64031614243e039603001c0301e00f0000320300b2591042d030565a409071850703580c03001413101019250360ba6940828a150007820f0700030210152202011a50b59040100a501c61098007060006050501e190885e04a4a080c0506400c29054845003074078051100b688a1489100101c107186940d080010003c04080c01031120054041c44002840d280500a4810030700014480c800342e8655562074842c9005900b0902c0109542840709840100800440e45c4001c0a155041030780f038505860b0440c10603a1980041c1e00b40110708610308035098880c190138121440c071500d803991725111080c1c010b00e14050070060508940c03d00c080e5404c00c036441200680010441c02c101c41002c41d00c0355040d420703808100c810200003610354100300064a04144102c0c0100d00038240060f138104006d0108050704050506000803500000b01048810911200a07006010200e10a400e102c0b038010418520001841039078540c42c40400d80c0c1e0203d9200b03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 632118138 1250 632116888 632116921
    0x50f0702063402010207080f0303130c030f060515041a0d0501020702090103030e1e0906040902010c0b0a02090f04050103020d060e072417060f1c1b030c0b1908 70
    0x207403441441c0b14040b614918150210010040b8010b000e103100000351524005291942e40078104091815917450320700340044034003c40d2040d01d411481140000105074040e0004913181d0003440c0205452608808820004429030aa140200d26220a01101c0b0105040d842d00c01e00045030b482000a00c0e5080c540d0185c01503640103075020103480000400c00d41c10006802c1042400d0715203021010138450401c5000704024080c9130059410400614946882e5100c2882d461050400300038008071922004210f680848000e502183c0c00680c81d60240f404011f20350307072440304070303005e0144d5030456000c508040b0b8207080003841079071110054600ca200a000450103090041c2507000840502e5400c2d0742c001001c042010085005940242c0080c3d5102e4205032040320081c1442c26200e00105c01c0c400341000c002014000342c1259850440002c12720117111a101e065840320740e0b02141141058110700c0d1117644a402c803108100410711282a80c1c0000c04001001824005080d076034510f03405240d100c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 632119388 1250 632118138 632118187
    0x10e040b12070911040303020a020105070f051605030f19110d2108060a0531060f080c01030b0a12020a0512010f06150c11040f14090d050f070206 64
    0x2090000c1180705407001540004981165209000881444196100901c0342d0301003e801604a800343c0d40142d40904000c104813441070401c1c10b56100c080e210241000c0401244074085403140104124a1808000d46004500350501805100800f010724100e0040c1c482e0380100300389080320f503150f03442d59805019000283c01202c00410030002c03600c2c0405089001c021000400c0702c60020070024201010300c2000e951003d060180f42d940103521050210030015640308e41c00c014551690207002c400c6c024034004001184030390a0700c5003000845801d0008481e03005040521b40718003206207030383d000d4042e03007241d2101107010502d49490021811a1000303822082d00041401401d11030488158030088003560088002c000e001c2d01d80d90166181c0c0300c40c0740078100041d0140039030404299254240740500c0c0e001040011080d4075900d40c941551200c480c40c1c080303808078008102503e041800740590413200742c034240c0d240c1900d0f94800c8031140104038000c1c1c0144004101c0d41120702510644800201 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 632120638 1250 632119388 632119399
    0x9060204030b090619060b03061e0a06050921070315020712170f0402060a0e030a053a090e07180f080111070b18100c08011410080105010e040b 63
    0x604404043da4030326058401c0c507052040b83c1da172442011010701c14002035a00c0c82c260240b443c0c682c641041900000c02c0c080001d25024245000641e0343c64010150003404981c4800c0d480b480c40a013044010880c15540010004e44600b0940a0540205480003526440f0312001c0c46240e005030f04400900800c4002000350444000e03007001035800084d101c00904601d004a0101c0d5614040090000400c2e10020740008051200104c42030280d004040300c4a40582110768060840e19110301d0140381110304040300010a1340c40e070980909245a448081c3d40318004565035041c0d240c020188070007842808180882800842d10f0f861003603000781007501c18150380d80c500c0c0d07807582102d50304c1c0301c4544203100c003030742c43c10039503c940c1447c403000d0f68520740e00841640b15a546101e0303c060202c5541036049414082d07520081030024140c45010121f601541e5101010b44c10003030980c4d4148140d12081d44a5645102c44240555000d079840d41524001e1030a002d00503070360000309003e013000b100c143d076103c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 632121888 1250 632120638 632120641
    0x7050c0d0f080c010f0606020d020c061b0a0809031501061403180303090f16050a1e1502030717030402031b130603061a0603040203070303032301080d090605040b0d09060204030b 78
    0x40320150021014001224001c00581f9585c0c03100740c0c2d54400409000300540c0001c030030300010789070030b50150a20f0076148003210f6003584013000d894180f941e050422078002034041000c4c49607041c00c001084060741070302e0b884040c550411740040d10f064400b0005039541500000060203881082011580320b14005040304d440f42040e52066880e01c0104002c24a54400c80501182d50201440180c04483c805030240c81c2213810308171038102c240c00500203101d901d0304a40700000c0800ca4205c0c0382040001c2a03010316140d0661b86090000e61180c0b1382d21605d100c17070034000d10000d40d0740031952070a070300c4203014503003403044190703012550f0821000d0555050510b41a0700206201144e00411004055503040440c45404442000036901082d14080c1d01544441c00c1800043d0180d8488040340008108211401000c072044c0c00f2034800076001343c0b6050304004900706c03103250480d003420301a21031414a14140360405520598074043d01036496407058503600c48000b40051503040314042e5410034030140c2035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 632123138 1250 632121888 632121907
    0x610090e1911091212090f032e0b0901060e0103020705071a070303051b041208040b0f0703110c0102030901141b07050901091109010c03030e010e0705030d0507050c0d0f08 75
    0x102c3d04800401070103009900382a0a8040010400040580e80260b080d400c015140c0244101d224013880c0841c0c0503c02c8440304d0b8640c0520251000340700f01c0e82c1044c00954080d0010000c2607034803240301c0724050402003006001198100c0c9080c15815004e00e401615407580d800e0251408600e64000f890741c10001a06c0c00043c0301040041103075502948050185445000d01c1c0500d40c0d01d411480c00e00100d007480306002d0490840e41d032403202c1c0d0141c0c295506150b11840b14000380d0b40112103404900000054150403d034000c051003118040840184c07422482820002c0d45038418201024100025140402005000304d015202084d01c001043c000d02c400e560301c03460ba10050b50080d107201c5c1c00420000a4461b0581c011024074241d1078401c1c0d820710b02280010b441d0b065080b0811010302d0f4950602c6d1500c00005d00c00c000782100703400d0050104600d400300749410001200b485404004080108002103440080ca40b40001400d40301c1c0300940805060011601044290040003c100014120071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 632124388 1250 632123138 632123171
    0x9020f130608042019180b09010b070f0305040e19060605130b1c0912080603060c12102106050c090f12120d091101081e070207050402120a050610090e19 67
    0x200024104e0800007507d0b4a4104607d0000910071050b0488040048400144a0036000a003d81c8242403080c242078480103103c80c40e98045640c1c480a20300040d024000000c0c3d070041c07800038040740c107080703241a80e22810300e1160147c601403d081c200d00003840d10f0a161030420750001075a83c1040c00c001e00d40581c9406110701002c4107800d40026280c3d40030422614005c00d8641c0181003d004071880c05c0810100426444401400f00d0340d075103800140050504005041310f5508100003004841003045454480d0440708050542c40041405000f0380e5120380f20420b094140c0324045070071010909862000600c1c11483c6c0f0703000841c40b103002c01c0c00080c1c1c2c091508a1070a1038820956506000700c00c00046603541c00c211800c2101c211001c0c0054180d010f03464080d9081001441a210300c2601c402c04202a0b90042490038024010b00b810446008100c0c4076980d009042243d01210548049000914100c440d00608004001c10380204400d2161031312a0107410200440900c04612100d41295 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 632125638 1250 632124388 632124419
    0x40f05061302042714041407060206160c150e030c06090a02060d1d07151b170a050c0d050d05130b070507020102010609020f130608042019 61
    0x7070007507a0486031003104940781c0c02500c050301d01004c43c03112080d034040034010160100b82c185003095681c44011495107000720040c51b10550045480c0741c003150103038500c02e182c90815800a0215002203082c04113840301c04c0d0707030400b0844a034a80341e0074041c140c0c03d01c15030001410250007a820300c0d0481044490a010001e40311009450056135a01c2d91031101982d01d9903151100254000800c00900203c120550300c00c0543c0045130300094030014030f400740c2034a0a4002c1d001541d08101556420702e449910040c25040c01c0071141211b003888007266a603040040c00c0da00112815440420f01e01c500500c2682521001600b40003121048401030001420035402000091140344c01d180019482c0920380c81c0270503802e503203c018800c1c141c0c0c0310b075011503c079004400100e04554071880000f0348000c681c000307460598104255282d807410703d03a070110142200b503449682071001850410000c58198401e210654401502d050443c940480000d040400d001640003602000c1080220f4205640b84504 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 632126888 1250 632125638 632125651
    0xe2505040c090e0903090a180e0604060f060b130b1e04090c0e180a0e160305070806071106060d0c0b1903050c04050a0504020a091706100f06050d0c0509040f05 70
    0x1143d00d41c40e403914898807132040b400410b800802e041010400c0a0a240d549114240f41250002c0c000041d12003480c02d0071001e4074241e551940b1440080049401441107000800b20705002615202520031044008a1281704946040f000850b02180354409481c001d01c11140303482d4000d945076204c2806030001c2002c1c5540d2400544081c0e04044141402c2e4050386440f0b94164120540e56076156207800601135041d440100341c083c40e001da12407120150340440c00703507104402030408a03040c01c41c200d240210042400d070410040c90b034441c0c2d114001041180c1c2240342560380080c3d200340d23424400e00e0b40c501540a004525000640040b10700c507a1070344034982e2805e84d40d06001d41e40f1954488280342c02507010b2a644004488010000c92402d40e0007890642c01c0384c2480340c40141d0f600e800703100008202650320030390307001a07040040307a03d58034505002400821016454131410010024118000c43d00c0c1d0003061076451b41c4600c21140141c00750303030a41c0c1004100340700903d40030000d0009400195103070f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 632128138 1250 632126888 632126909
    0x30e030304030b100b0711130209130f0f0b090f040507032a29031b04060207082b0807020703150b01020c1005030402150c060103030c0b07030e2505040c09 68
    0x200c5d6072150803040310322481e00500c00d000c01e1540b43d420846990301030100ba29009a080200380580d0b02e61840030300020034900300000305001c420719941c3c00c2d80d00003c8030140192410b0305e0f401340c55403206c1c2c0c22034200104026103103440c0c1e11450603030725010701600050306040c0314085503038107004400d2094102ca5508a02401c0c115600c01c0340d06440006000314034409180d00701c65241ea4505900616401603241e610a044c0381e40c003001c034601992090b0401001600103800910400c4000c00864030100390100b803031250748200c80507245000d40f046448000f0440c2540200d104148200300035009113030030a4105882c094143c2c0d103000201407404205002d80110b60b9040800c0c940480c02481c02c0070640c032900e20703583d9140d080007061840c0110b00404150144403d03e2096820480a4040e43c0700391107201c810b244508111407036030b8005001104041c10309140c1c1803260f0004c144c418603a080b0400d40c00c000c4d40f0b00c001401e00107004e0342045130824506030418441e10b600030385a4003160410f01030f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 632129388 1250 632128138 632128171
    0x141f030501090c06020d170a0209040f060f0302090106080606120405030d0e06061305101518060309020a0503010b0d08090a03050f03030403090611281a01030203060115020606060304030e030304030b 87
    0x1003661143c3ca100c0e60001c914150307c00080d6541da050b00241440303d0010000140c001d50300c01d01404a4040390003550790724518000c1882181418050980500014108850146018000544503108030f0b84160301140c006804101001010015a540ca90080c101880910004003c0590311001101e10503c54940070350940c0c42e035a890310039140960b210380c01e000341c0c0b582441c210300104084100320720200f007403a003024450180c58a482a0141c00350b59004242c0319214010030208150300c0d04210f1003645020b010183ca50f88103060224001e9003c0420358407000e4110016481c0c6040368000341443c000c0e0000005604004001107224034803a840c0c40e5401900ca0008480c000d00c80c0039116119130007025140710030200742c1007451003c0005000d540750b008031175654911202c042e02070318284212620040c0210f02d02441140e000d02a0191400c80d204003091000355a01302c0904000e008000010106003850b1081c0c00a840f07000b400b8040f659201e82c0d92078841c800b41e604448c40c03851a44ca203035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 632130638 1250 632129388 632129413
    0x60e011724061c0b0307050901080114251d0a030602070212010203100303210c08040203012708070206090a03050a050c030a02060306220f02070501050a141f030501090c0602 76
    0x40c0c40e04143e2054283c02103101803260f840c01042282845985072180107030014007070361006a50b81c041c042c0500007288a08040f807100b0f4400d02c000e084003518800c8015140402507041804850b41c1c1c00d9032030143c58800000300d006d501030361412880c5400001040c8048140890b9800030400a4800e840000048401d072a00301d00700c0c0410394562041401c400c80403c04288122500d650320901c100e91400030414020682045a003c0c0d010381012a807904104001d6290a1081201100d203ca5407440c8680f40c21000319a06640958010001000400c4000a540700e480c00c1d180c182c0005800c075680d298903030a0280c0c1d64102c0c0c181c112024440d088400d2a0380c1030204034451115030180030a0300b1500d9180411400704078140c040e140c82d08004903186004903450040c90944190ba1030010307500c04240c1081800d4846c006c0c210007403182082d0540d0760002e1002011688040e40b0292842c004009021003582c0311003da101600f95070800d2a042c0c1071100f054900e2040b580241c0031070b18114101c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 632131888 1250 632130638 632130649
    0xc140406020f121207140d050f011511060109020c0c090109021b0714091e040305030910020408190c091a04052d06040612060c020106050d0507060e011724 68
    0x31440b0000a11000310792581c6c05040c0742c444240710410030f0303414856090900700c11503408940c0d40c903071102176a004011040708880707180d054074501d241205544500c0d00b40e282d070311a07061090005540d0700203503480c0d1080f406d01c203c2440220081c945c1c1a03d5a44000075004ad4104899112210701e02140760b03036183c4000180c480484000030041d26440c0400d40400c020810011b00d1110055648480704003840c1c00110b80030701c550310a4079400c5c2c89083c00c0030781500d01180600c0143e0b8aa10403c8140100e82001902c101d01c101c000c0031240c0b109841d450841e4000180345c0c452940c046c01c003c92105d51106045180d02c04040c01d940c10880b135030700d1000d014201001880c4040c0c44100c03146c1d00d85642c0d040080301c180e20882c081d00201d1140d6a90401d1341070423051281c2610300d5680c0703890f840b0300706078280a18001000c0c12518618490401e8403000d40b500c0c841d220f42810300011403800f032090390050700107481801034196186070b1850031000d100401c424540b10782c113050401c0388109170300e031404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 632133138 1250 632131888 632131897
    0x603191b020c010e01170702010603140c0f060a020703050610031b1202040f021c0f0e0d2007150e10020d1b06110c07090c08190c140406020f12 63
    0x40d41d0091811116050054404002141c90141000f650f5900c03450340c010070000d46401640300b40c0c0002035103031850030260411f8502c078030200c9880d040f829501101e60f48914400003580030455206607540c034120400d07840c2850b15030004010740142000c07c50000c1d16103406400f1203001d28003082081214005208005c1020300a910900c1800d80c012005420301e60b00c800000d9884510051600943c21341c000d00404c50748184480d5142c8850700458500103e000320000c0c0d0345080010050040c050b034014111001c02c4032560b00044038281d0b465408981040108000c24010f18581c51000300414010325410b001c00c81e640c014191800704040b15840003401d52118419030f40c2e03003581c440c0300300801d0000c3c00501700151038884e11092812604a1204001c0181e00f0720f0b0350003040c2030361900b10300030705030791104a000741400384110400c030070000e102c0070004400c0290320001940c50000441035440c0041d1440e01c1d003180d44041008190160000340070000b003c011fa080b2401641e4182c1c18000c01e02c03c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 632134388 1250 632133138 632133191
    0x120a0506060607081b1204120201030b0411070f060216080d0c020c0901121103160302190509060409020d0c06180e0c0703031107060504050d11010507020d110309060319 74
    0x100304904001c1030803012a04c40f050103d1410359850300450900e18415030400c2d003101c24000480f0408c10219038151180c840d03000c205503408e0100e155180003515183c001d0210162052001c1210341d0700b0060301d94115010710999240658500d1400c2c2000200350b001110910b01a5280000070741480c0d000060340d10021100904022003a03081c280001e02d0071030035120858680d80040700c9406141d800384141c18003941d1140c884042c1502d1801000002c00c1d0030109861041380b1b0b9481403101e901e8240000743d0104042d140820100614030102e0058000500050042c001c00c8201003440c95104100580d1702d0800c4483d44c10b900e80b83d9188101540040c2c1d0520140081001650006402901b014409103840000380b4141692a11000c09032a4201c50840e501e03001445400e0020344c06c54114034000d2000c000802031468040d00195032041940340201c04c0c00090002e20b00f030743c00100202c039601c01000d46085c0c1c072030500204280b442d00f118107600e0798840c181496905412504a40c0c40c0d080308 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 632135638 1250 632134388 632134403
    0x50c1203180c1f0504030b010b03042d08070c09050f07092102100207080d0c050d030527010204090e06100e040c090506010e0d1505100f0308090d02120a0506060607 72
    0x16640300301d0303c5035048080c1da94010b0020600000020542ca0141d045c000e0801188042c0d50780380034500802c1a01080c00075282c100b9a00407524698000c4841040c0d130141e001d036125075500082d0600340c3e22b03a0381c20343c000150b0b20304000c1006501c11480c4140d5000b041103440c1d120215880d11180d4a400d510380040d80f00f9140300d08203038009807420b00700072001d1820340c1c010381c1c200c2d0f900c1d051050308220300340d1007800202d941030f01041d041000401809429015030324040020341029207250040000464a610f211441016205203140003941164010a0002e6041003035004408100340c41d654200e4110b03000d07500d162000120300290400311803246600082c1c500c0c2090070551524010031002e0281c0741081084a007036440750312200c0510300c0c0030380240714125811640c1e54110b81590001400c0b0400d85010070030030001200460341c40000d0f264061156a100d468a00c081079109001c1240654045905290707501d054a001c6102103441e0701034010390742d2554454050083c284a03a140081014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 632136888 1250 632135638 632135659
    0xc0219081c0608122d0307020d03060e070513080304060c021905090705032d091006141c020a0e060315060d030806030c031509010c0306050d02040903050c1203180c 72
    0xe4254200515090b91810b903400c000080d602d205030305c42d04410010384a9032a000080c88035443d01000321880c6146070b440c06200ba00c1c1018060b035074810029007520103124000c1003144016076405559400b62030b0140c1107c4d182c907520b800c014022020143c041c0c0c0a1a081610b6001c460280c0f25400140c1300043c1c441c030f00c01c0d183c05200320764592008041c0b03118100c50400d042d1079210581e011049054100d01c501182d4141141e40904040b41e52003083c154a20f404400c00c00040c0c00c00c0351030300c05c83d01215181e42104000c0140c0c060101508402903011600c418003081000c4051b000c2405158190215141280c489038030701d0035a80142d1300250320030305c1c6400c030310002131040896a60120000d020348101104881c0800d14084410403509641c045030020440c0101c001d11900341c5440007480c0170b1060601e07010210340c01e1030309908043e010320384512039001818003600460b10780203901c2c011112002d81000854000380c10564a10102000d40b200310900351400084040c4024401054070805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 632138138 1250 632136888 632136913
    0x304030509061c0b0a090c0816030e0610091b0e060f0c010e0c040c0512010e0c13080609100501180515060a090e09030c030d0c0219081c0608 62
    0x464200d510300c030741d10070403c01603001c2d000d07204804244039101041d008200c0004c0c3c1c504001ca9044960000c00c80107103842c1004039a01c1d40498400e811100a29000545200c1c0c50b6003100500410b4854480030300c204c0e014010001c170728040d502e044a043c45010840b0b4104074040d2440540d100f40c0d9400010000c401c000703440c0c074011000f011070000841c225860000400701883c00d40300c1503035103a01a50805d02010800341041d0041500e00a550704d003140c5815242c4000d000c0c81c1c0410700424010352440b00001d5036200c403040c111029180c1e1a0006501555110b070b010ba512102104d01c4042400761541c6008010b03034a00405040e161644520740300d90401c100a8001010010010030381c01c82d052440700c0d1240c4a4400a0200100ea9618607102034140b1074074801581010f00045901d5100308000000b94001100782c54130a11045000b05050b16103100c224504130080460b000c030400500c0f078080402406c0030040c22000d00080084400c9070403161010102e4010b4412805903801c9224401e01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 632139388 1250 632138138 632138147
    0xe0615010918020c0d030209220e0604080301030312050c0f07030201110d0c090b071e0809180a0506030a031b080403051005011d060f01201b01031a06030403 69
    0x12481031501c504001e584031040340d510708045810344099980050007120b031060900102c2070b03290141c1025450014120040f0300e0035407415848000144400b0b001400c04d01094110207107070300e408001c0f130b003182c1058200860b190f07000b80b00071400709083d0b80424505d60140d000305403003040300d001d089003820b040890b891240d0703014030b9085046550310440c0d15421942172014041610b000751000500c01c401c0f0380042c01c04800c40d0031000c04e0700014400c0b40c000507043d0155080440d40c44460501c0380403a480c0c05031840c052040c1155001801c100480c00c0340d10b034880c00c1445018100008c2c802d43d2138002c14541c076084010b201078000b5028441610586030b074000710b1804503210716071a618050f9652a40c9040c003101c030b02c943d0743c200d031641b004000754804074070540c80300306d401e05d0340b0782250901c0340c00900807a80940d10b0905002400c0c0c06002150b20300c215400d9030750b90030320640c1d00f42c481c4200014601d001001019003c2894509664420002c03800d2081c4071040180c840d81c5103484a03101601e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 632140638 1250 632139388 632139421
    0x12020d170408030402040e0f012c280f060e03090a050d0506011a040801151d1603050a0f050421030207081204050307080715110f120a2c010608010e06 66
    0x8548c030519030400c508250034030881008035181106441201d0000d07209134104a8028030b8800076601402c02008030b10091920958091400c000c2045484d50514103000030a2881d1030107010f0a1801000d040c1d80300000c8000c0490100464440c0031054503081004540d1884200240243e8019401442500000341400403101090340c0c502e03080698524555017910002e800502d4500c06001c810007640146c807841c400040c410a0400809280041030071000e009141c003aa0b08054a030307804140c0f400c61030f07848082c90102c2000305100501c0c1504000c9502038409100d00350100c100d03140801c085d4440d10984c1c40481e4840082894a000b5121640407510054000d58941c00100703c007074002401c0350000d1852074401c2c10b0029068400c2c0758840b04a66410384101c0d19035100300400c000c4911980200d0720701042100c0980722940702e200c5800000c0011224140c00240d11220750401c10385002415100e0860460081c01115107624242d4207a9001200e078030780e00c0c0e104c0804030701c4043c01c050860 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 632141888 1250 632140638 632140661
    0x903160b0d0b0a0f031b05030c01050d09020118141e010905120f03211605090112110406021b0a080703020111010906050106030f0f0b0105030c070f12020d17040803040204 75
    0x5156980c44d0030110300541801d90044454134280851548240c2e500107691008080480c080d103210085c01c00040c16911800100403440ca0351400c404045a0140320100603005103031100c1c0301e107a5212250207003107400c107003445485100103070304450151100ca0a0700d001c030310040c5d48030401140350200340440850421220186800b50354002480300d601000600030903200e80e4086640804042c254014040001e040441d1400c06604030312100e98201044482c0ca190a20380300e024090300d030404a00502864843c550004000200001c0032540002e07001102081000c200f0448003c4a0402011702c11900c0388540c1d94006c0b200400141d80114100000400080004240821580c1c2c9100460784240c015001195981e1480c0095408074030402c040c150f42250101300d046040000602140001042507005060004200040016440e41d40000c02e6018019a4814404c010003948030702580c00c422001610110f40300004035550034216005941045410346192070720703002e102c090310499144 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 632143138 1250 632141888 632141899
    0x12d113d06090507022103010302150a051b030c0c0f0f01030203092b1205070215100306060305030d0b030a15230709030b0c1305190503030a03020903160b0d0b 70
    0x6050106005140c4144001e45c05040409400858184941d5240b690500c3c1540c0920040c40140c6600b601080260909211103480d0840401d04861740d00c100c41c10844181c4240c401c6582504001020301036024006040e2040b81c4244410311540b04151340042d5070184d00701c110384000f94084c0d40250340255030303034050320a03e44009961001200380055400f00d580289000c0e04901a4484003a441000e003103103080c84181000d880003552481c0c1f13990111021602d103000328040000c8107603800000c1d5030081090040c84d07500e0401075102d0b00700620700a0010704003d41c2e0480b0345004256070703611550010229092040700012040104030174030405000a410080040694034540e50042c840c05003a5109403005085180610050201901c1d501c00a9418821445440c000c260540141d0300c00350748191310340c0c61300b03003a0003801900d581c000c079014000011001d0259034103400400445c5802da085940720151020144200b2003984565011480c09000b46040c003120786c0c02681481c20014407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 632144388 1250 632143138 632143151
    0x21b0117041704030b070201231501020c03010c03021207050423060405041814011a0603061516110307150e130c0e13050108030306012d113d 62
    0x2ea150b5540290400c2d1500071503001042403080c2d09002d080d0914401e11200e404410226940540c0b40300b000e808070311210544200780b05035074070030400c40c1c03c0c4600c0100280100242d80034050000e5005003c0b104040096200180c580d80c050411a001c40341c03e444184500d000e80c1c0c400c41d140048008441ea8041313810880024681d4a80c001c0014054510420303030424015458240071000c04500c54a41c00d03410b1002110b811130001d84445102041030320f049681f540c41000207007038440f0042903506401c8010031096410780074124a200380c0c610480720b1840c120004000c0503a200d55a104031201c50800007942101d01c2e102d42c1c440780c0c4180014203181548032031300040c03c068941c404107280006040d402050541d1428026a5060303a080d440100301c2c0c1c0d41803c1c1196181c0c48010841c0341402660000314001a0b410320f058582c0452859003400302400900d8018503200303900c41b41d4043e40c410074030780300d031003001070411200d0602c03401c0c1030040c1e801241080281c0079001007040d0302943e650b610 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 632145638 1250 632144388 632144423
    0x20306190608011e050f040b0c2203050d08010902040821090a032603040c0504050601180b04090e01020a020a120504081002030609010605030412030902150c0d021b011704 75
    0x30f8500b040000085a15841513501d01c400110742d001083c42000828500038040402d00b07403204180c100c115560499506d502900e0500b40c42c1c100c3c468488040200d99400205020300400e801d1800b10540d40c8014150b60f960030054203a000d140a1040305420000a46190702c01440078480404c008994450034107050000003151641ba40c1d009644500d40700491000c2c20141010b04600c00c0a14a4080e0850906442e101d1141c2c005001e041d004540d52804500c0c7d50703008040610390b1006091106c696642c079110119000e070000d21540e04000e0400102c14000e10041c0281c5000d004a54010442500d080e15a500004a004809400e0080421003c9840582071100e8002c04d0189400580d590801d04244031800070143d2010003040004d006100024000041d0408610356600d0046202c24a5000251009000e046120002c40c000500c4410144003c130721000800a541c00b510000c400f122066450440040320040c00900c0c600c0c0c091040150148000780c01900070440e803181d50b034001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 632146888 1250 632145638 632145641
    0xf0d0804112b031707030c08151f0309060b04020405090f0606040f120246090c0206041a091906020d090c230d02100c020613030b011202030619060801 66
    0x4081900090a5613001d10b4090075801d00013508002545810002c84a40c10b6000b8890300003d4510032025100100100071603941c0ca555141e240320208850000c441032000c00340041a54541c00c507081409e060451400d4502407091340c045400c0545203c3d410b941d0482c03072054080c001084594089000d000100313009802450341400342400a00100041e182401080601160071910382c1e02c13500003ca41399821b81544409201120028298010400c00c01c1d440c0784050b81107030000e0030564a03015156a81c3c81e40090070501841c01820760420380c8110344401d03c04442c08403100203a0794046290f0112800b84002041c40c0c090003030f80d0060412640110250989500c4403058a404507400418001441400e0301401e4409025200489000b481c20100b289011000d5020744141d5503a0f040305003641c000e9050090302d0350f0045c182030340c80d492072041003180c49181c00700b80c401941143c0042101035040d8401440c1a40050041804da900c0c0c220b4214a04280e550044e6000e481d1140024085402d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 632148138 1250 632146888 632146969
    0x40c140409050f1b150901110c130504020f03060c0f09120610031a0f0117010f05070513060509030a0b071b03030203041203090c05060a03110304050f0d080411 70
    0x1201404c8001082508200300c03080c0841900d10604240034259403200702d507000c480b10380200307081c6050300c609106807903403c00c888a100c42d500240018004440000b6507480180300d6842103900400070308801050582d030366011291a805180d0822a550207550320402801d40842d004003840c034500d00340861641002015580765a40000e422004e100b0070024071282c21681c0002c141050071850000e104e15031030301040c80380000e2000d4242c40c6000d00c403c20741011a9144100c50188914101070400415550202141705482c3d4400f40b40840c0483c440c0c030488440c480000d0040c40c425299494421126001500c05010300001600082c1e140300f0109484025a009842c016100d1910b414001d40d041488040322040618005150b800241142d4240b0290780c0d090320815280c10201e44190000c0a5060b011841558048108000c1040c0050080741480500c01038460554440d98140d0341d08900b91030040151120018400007418074405490107030441ea00038181010144003c0d03044501c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 632149388 1250 632148138 632148163
    0x160801061b170a0e2b02150c071403070f260f01150905010b03071101060f0f05030d05031003150912110c030f0331060203120f040c14040905 62
    0x804900014180c0c0c200720308113056601074490141100062510f1500c00913000100758100c0250403010703080d9140c40c144040100003220a40c0ea139021610a2595100000d100301c51003003000c0c3c0155065810301103603203c12200f00c00c4600000d28281030510300c0001c10084400f440c128282030403101c682080000603605450080001024131704000e1200703410751140c0000194600341401006114103190403294403080c24a4015041d40c5030300403130b5000d0146a0300030070344410102004181003001c0b03608141180c00031400c07125150030781c00065a81e030000f101d90304503080740e111007080465a41080344100e101c0b42080000c9084044c0d65102d000c015010b0000e0000305400a002c608490030460000155401c4004010283c00210815038034404c00740100000200019600313000c00031403034a001ca403684040d040052030303240e0000941e04c0e0030684107036046180e03034400702d00400d6503a0420380c06250800310041800d418290300340440c408804005030880d40c0c404107080443c80c28000c8400030803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 632150638 1250 632149388 632149433
    0x204020f030a0f0605090109050612060702032101050a0b0a1106152d0409060b0312130b0405061e072003010b030c061e0d11030f160801061b 62
    0x10164850b1007110403125540b50400d00c0c08805001c155180305065044401380f03240892a0758482c000718a600e9551080202d035441100b00b03001c0c9564000c0b014085091581104c03610125005c1c13071441c40e00d14207205143d0060059401070241a00d0700d4005c06118a09081001d044002030b10207074901401110a8910080b8651030b20701c0614101100300c80700f610305130410194400c0c1c104248607403c0318804081c071aa41e43d1543d04100503154210040405004041c2d0b000300d0b00c90f19104103254861400083c640c51101c3d804a0440360142c107407407da5401500850401943c1180c0c034208103211001e4480c0311905010030701c00110841240b488c0741c4410303804800071001c207070245401d4424000c5800c0c440c0d00315028004040c2c4644065413460380030408140728981788035411885502c10750039899051810034510490b8a606e031350040d40070b410700803070891842d56240100d03000b21508003d070100083c2d0038801003203040d11030132041c81c00e450850070111140806076600d1001e8440c1ca0984103021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 632151888 1250 632150638 632150641
    0x301033207260f070506091210050a2919050d060f0b150d0504030905030604051b0607020105030f100f080a0203160305100c03020f040815090708150a090204020f03 72
    0x301c4001810208000c0340000038800f07600c0ca4600140c852600d0300a050240c007004c10014060f030307501ca000e802c6e0803403514250b408035940aa40c82018200072183c4101c0c4a0400e00c41d6600a00c2f030b21074510310f1608251078104c0c40303481c1e00100203503810035048460352a04031680125156441030318480c0040c9c4036040000d090790000e0810000d440c01002c5951094050034100498562a00121030700c010740307540c0c0000c499039103240c191135080311904080d4044c81406c0800c800c201001600100d204100c2c89104c0c002340196040281c2c0e0311840600a00152003800401d48100c40d148100f078108891850320300d140e5484036030126078a007a80d8003000c801c0d409204007a040d41009d00c205820000003c017060301540c115210596200100a0b03580c85151340d91082d14403d9110b41c0c1a0341c2c08807002401c00ba40c8643c3c0d40002c40e80c0c2c0e051a403441c036512884c10041003200100003548000c440e0200702600b101c0c0c141002144083c0001402d0003d070076159141040103070394600c01000d1014201452544a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 632153138 1250 632151888 632151929
    0x52209060b07060c020c03030409110705030307080a0f0c1b050109080d1e05040503040527011203020c010f020d180b040e07080a1512080d09150b060301033207 70
    0x40d0751a02c4520030a64110f01d424070907d41b00481154103135410410b01260740011247d001200e48502d0304094820b01010050150050b8064191030055445800c20701010442c0400e400c200d070740b03240348080801c00354001210200e61000da810501c0d0700500001071040d04684440116500c41f4a5035144140e403102c6164840c196452030101d1650f10080c00c105038601a0b940e0b81d542d1143c0e00915200da0b03003860000201d02c0e58201520100d4101c03010119065940e030b2461202448002070131005030180301ca20707051380e501c01c030001e04a0384029802418071402c2c2d0070f411f0362444060900286030f0700320724001042c1c191034000100002c0001e403c0000d002d00c0d107031074000e18002020381456000d0303081a01c0300c050004041c04550644140e003d00842c01000744c5003018251041250300003d150034088100b091000300e181e80300e0380560464091180c00340c51020007482d44401d020007024429034501c800803650244c04103d000020a1150400701a0f42902c114544030b025130140f020307100f40d170030312214 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 632154388 1250 632153138 632153141
    0x40326012105251d06190b0a0309060b18010b090609030f03030702071502120306301006051302070609050a0f02010f080708070c0302010f0903051206030607052209060b0706 76
    0xb808030400d1010202c40113000e140302480b003c2d01082c4a8661010101811440c165001000340303d441c0300d40366600c07031290300507016004400c1c082e13504501c1d000d120061410034000044c03038020170490140782a801d00314044401d81241d6500754002e0024085c1d8862605c080042c04070164484c001181c4900d4100c0303000b490f01c00c04c0d4208040a545e541c0341036031415000201110f12100b1141c1c003a8072566000301144062400c2c0440601c56110002508080f81c0411450401143c030301050b07640d0107140c40402e0043d1180b80c4109034100c03c02d6028641c4159040e405020305510944012602c4103803500d81c240b0749007100105603403881c0280c841e0800c540c2c004482028400b00380c00d1810340c40c5403100c03018000250080000c030500421100e0401014401e620041184084070701c100100c002034180240b842e004400e0510014003014081002c2c3d1034001901c0d8880c000542d100c074a845103040040c100d1582c0118841c0500d019900045204112402202c025005944d503003a110030071741c2003c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 632155638 1250 632154388 632154463
    0x12052a1905030708070201031b05130b16080c0a0f1b05040b0f010c02120d0207050307080f0304050d0807061b0e09070206070513030b0708040326012105 67
    0x2a40c0c8031034144a50002a00441521003150700010f8050b22100c0d035000503405070000302c0c14446411040032030541110b4000019290f10341510058030100c0782c8850310400d1612400c801140e00c804914168000180118000c100c081c40b45030540d00c14008336603d010b00e00070702180c111034200065001c680000440e0076418000c1c48102c1e4184602d61071a404540c5003107100f80424104002802400159240e600900201124a00c05c8036201808660000d44810460107880c0c441d0040c05400501c3c518009151058002c20300e0145140600e00030030800b0024101001303c41c030940070301010f03001c1103082c440c142c0496100c0003468404200220f00404406040d40541d100b000c0030f000788084940e000600d6503001c81241043c95682c810404186440132003a80000c15442c0c010003040b016951000b420340c0120300c291622500d072401004c5a800b104591000c8180b44044407004010100355041c000000c030002c00d40545a03070009440ba03d0400d042c0a41803001c0d808100000b1074180781608407071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 632156888 1250 632155638 632155663
    0xf070b0a020319020304110325050901350d120b12060a0506060708072003030403050c1003020d1503150e0307080a050c0d0c030215070c12052a 63
    0xc501d5440c0c00006254071100754000308040f50350100000e8208480c8007641d80c0d0755903000b4126000c0d03186005500c2001d00c040d603000502d503500d0020000d4035040500d02c050507101c1d0701869410403c030001001d02803400048015104c004100c00308480a00d0070b1020106156090b0307911000341510104103000d03101c103c03414500502c110340f0b0024030544081002c582140003400c02003003030740301e210000b0564003414001034505d18000070486c0c2000402c0c40c0d42503000140c545200301c0270008408040d10b0340150304c409010b0381c000d5485480e952600e01e40303070100309100f41001402c1400b4100352108882181714000200c5181d80014000d114600d200c0d2002c0640314a024440a40039410240d08ca0082c540024001034020a20a41c5c8901038021f440c00c050190b0308455140031220401001d0340c075460402da000d0b0040111600c000900e0b44c1c0424880d02e00350f121410b08409990b1100810b00c0765103070304810810b0a00c0b40e2813894044014504007800c03824034101215a445c1c41c031078107000c42400d44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 632158138 1250 632156888 632156891
    0xa06050a030b0d03020c0f19080105310326010905060f06040b250b25090302010818010e07060e03121206090c040506040b22030305040513020f0f070b0a 67
    0x81c0d400017940021031079140d9406680600303a02e9075500104400c500880304018400000000c0400e60120561115105900348941204869240325024100c0c2e11b03000c51002c0740d208060b00c004082400755052000c1954800070902041d07420303e103640b07143d100a8010130142a210070a1103014545407044140440c000c80d00c40c3d1406103022050b17290b61150340c00044c140c1c0c01030242815007209d031a46954042707800c0000c001c040c1c0b919142c2c108e144611889016050700e4801c400d030001c1c0e8440d281d1002039a0313040e107a8000c1922480c2c045080a41544030441447d0741741c21909071041001c0c0910801483c0b030351140100904050200740c103001240c40410070424050081c0c4400785103c61109400a6040c3c404200c1030f2250703d0f160b6168480d982081e134220b8000100000e40c1d0310250002d00e000003400c61070a40621803d03808070050440c03440085d0001b0804e020900591030702c2c101078034080d2001c1c240180b8284014003004655004640700300307a494008551103041c8100000c4079641700482610 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 632159388 1250 632158138 632158159
    0x1314030c011d030c030d0c120903020307090b120f0c0a05030307110f060d0603111503060a05040209030a0203012c031213020109091802120a1502090a050a06050a030b 73
    0xb0680b01201812003a60b070800802100c45450900150101c1c42e0094280c5200c014452405880105a10320840d8480310041600c60b18074440c4055a0940e03900601a02080780781c0f5180c40060101300200c01da200c0c000441c50081d13107901304500d1130b000d4507803c00741203880a51020044514810351109019810822070400001c0c064040c0034000e5a085a40c603c0c400564000314105e4082c102a0030811460b1a80120030b00569030244005200b0071615014081d0920481032002e02064803d507400102102c4240701340e24054020b050a00700160807104500c440d40c0000e030035076152900e445805420f5541000c000d003820245005410f0f04034004602c0c001d158624058107480040980b00403154a0140c4002c5a215016580c000e002101c414171002c5c3e00104a10b00e080c102180c00c0748501c0e624070322103078079070b00105000ca10035070001c00c2403e9494006510402946c00518020751001a240e80401c0c140c1c2d4008428018041d1550f4007a141c408090010b000c448a05643e140b03e201c903400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 632160638 1250 632159388 632159413
    0x105030106060c230703080406022b0815011b060506090903040602060c09010c080a031a090c0a14040302031903081b1902010e060903130f050a0b031506131403 70
    0x4070554164882904501d9207084044139450400c14140c0001b40300311000a0001a0f0950019906100460b80076441ca2800440d88080200e0000a41818080f07075142c0000340b00ca07041c016800e171150b5010f0500441103003001035110540550744100302c2f0110740e2a414040f01d424a083e1640d40616482d008525007401e00001940c0c1d4a0b00070002c070380e42c080014219015901c02d0307946100741d03540300b50f1040e1100d101580150103000601c1c400100310000f002c0301c40e045d10f480342005001d6140809c07480c3c03900c008503034200c40e0002400f008041d0900c4c104000001a01c0c104010b90700303000b030aa0002103500f610301c3c2c010401c181c017501c5150200c02e05034070000e0ba581c6000407100c0613041d90f448000c0c1501495001d138054400e490014074103000d078004210210b00080000e1071180540441441c0c403a8980f0166003075501203000366504001d80e10400e101c0503545100850304210000d507581003546400c1c0000f4a00c0d8082194003001036221107080080c2c8440300381007400c1a01c1280036208401200e0f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 632161888 1250 632160638 632160653
    0x3040326091e0405100303020c18060f19030b040c09050f0f150a2408090304090209030a050109060b0a060309050c100e03030316090506070809100302210105030106060c 74
    0x821107449071081d0b103091031000000c890300360030301c040c060418402860b020348001c88140c100d00c4180c000d4022240902c80920f403d40c4511039040401c010301c0c0c000d07200d2000f44010344440e41c54040c0c00400720070150294241010021005500c164004103a40c0b40c0f52810f00100c20680d48038080b0f0390308020a00000d1080b9090159122800042800743ea07036404410318003000c0e00030406c54008000040108140700300041c0c3c10003200410150300484080d8850171101d506003128021178681003800140b0260701180c0042c8569903001741141e00010b001e4503558211a88000b00300c404c6075030b9000c0b400203420100d075008000e000ca0b040c10000c194054440c540c8030050743c00c080d44030780c20400400c8080380c041c10041e03083d410b014040b680c41b071a1150b01d003008045524608404a06110400166441c140044915090b0b02c004401c1c105020701d014426004081403030001455000c0c80408124400154002c0c0d00d002c0c50740340848154075003c185030840d80c2c142c00600802002c0c07a021804250038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 632163138 1250 632161888 632161897
    0x90412090b1608030c190206090606010f08060607030201060305070e09010b060306030d0809010608030f0c0c030604030f050309031611040501150e12032215210203190c0203040326 79
    0x10f41100e54a41c1c0b109000146880340e02c240c0c2000082c1c0402215840743d000410b0340c170410b4083d0841e800d070749903d801074400001c8105500300003241300b800501c09003042409841c005100e800041915034495480504001381904829041414082002001542405460007581c015240285181000c4010940311518445001d0a100051300400c0d003003c1c0940c4200028542c5500b43d9071101c0100140341410307405041480020700c41c06841c501c1e58038001c0f4125015a9044d102c08050100030041560140c0000702203803120b000c1403041040344401c0c0030b1068030051141c40d000302904080707001c1004035070b41070b0010103000804140d4801074603000307e946042c08800301c800c6200d11500081c21443c5202e8210708441034103080c0030103504408010030740710640311240c140c0031901000000440d0008429030b8030201d00d001c1010b94030800041680115005162800500c01c190741c0344014905030ac68000c00e043c01030b071002038200184100034003918a40d14540400b4004841c0d44500c3c071015005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 632164388 1250 632163138 632163143
    0x1b0901061202070f0204060816051e0108070c050a0b0109050901052707050409060902120307080313030314010b030115080105130c1b080403030f021603060b0f090412090b16 76
    0x2d001440c9010300a944071480801e85c0d004005000d03854035a0360168a405a04520758400780d080300c0080355a02d0300c1e4a8a4000c149400703c003504080e540c40c011125540003038200e9080c1700c82207502e540880c00a000d40340d41c19000d44e401000c55490046090101d0b00d006050400703503407610040c040304000b000d4500078540e02d40e455100540084482d41c50130400742d03601c21a4480d02d4004c44008201440c0c02401000780200c1c4c01c1e05110118200c1d4a44a10680d880140104030410000303480d01220021200c10354083c1c40c00140d07014501038988250f0b00d00f81c2000040200200041007840f80c441141005c0d080c05290003980f952401d804102c4204400305400d2082c4d881e5400c0c0c0121620541c01a0b810148a04061001d0100ca081c4000140c2c418001a80010719400710781200702e00006001825561921140c04080e207591240c0005107044140c00b030344441c28017140d9043c0d503030751501c140c010781c050881203207105819580a07182076883c1e481103042c5903042c404d10040d074400511042d071158 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 632165638 1250 632164388 632164391
    0x60f1e060a120f091a04030903020402030a0209060d0b030607020a0218180703030306050f04050106081311030f15060f030607230c0d140f04030f02041407021b09010612 74
    0x6016500703841d000c2c00328502c208481d250031403003400207040b80c01040301540201c00800d030540010143c0c1020407421640500440c0036010b003013005040ca64000d544c05112024010b0401501c0380c0007440310391103192442141c03600c0d0460b00c443c61500384400c5400021a0004040d030070126030100b40d40c0603c40a14640c02c0d550030780050600c2e0034426081095090540a80b800302d51286804cc0084c2a2070003078600640d00b41e8071082042c1058450300f8181c0e0400d8481c1421540c0b80707080029660f102c60004c46600041d8011000145c03070810020100500c500081c04104003040092041c5090080200e40300f00141041044c054402241480e0080a81e240414044800098408038045040084d141c1d0f01d10000701d40c00011804110000b400d203080e91500c13030003040c00c07600740018001c0307401403203404170100803c000007056017505400f030a101402c085140f001501c00304000d000202c2c0e250001d07802161040c00e900b0040c02020862060403644880d07c0d50400f14003e045001c04101c80c0c0645 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 632166888 1250 632165638 632165647
    0x10906121704030f0804090e150a0c0c0b010f0503010e0102030601080c0703180e18070f09200408010905071502070501031a090403110708070e1b0c010f05060f1e06 72
    0x240480840700550b40140e035682d9410011700d85021250302910400344000d20744010381c4031079031010079904881c28015410120a07103900c401000140a00d0a142c401d1140c51340541000480107032505000b0720709143c0c5d01d4142c0d440d0406041c00d542c5e29844004159104200700a01c42ea000110355803c4002d4a0007039441d991986000c0d200407070240c01d124040003010780001001810180418800c581000c0c43d0004800304c86e110650301c030180c1c00345004581001006001060383e44d4031595548010414040e01e90740611038412040d4010341000030183d440340f512005004042011000520426982002d646a5100000d407541c600d40192410540c0300e59140c40b2802400304503142d1008014220600c0d418a032a000e0b1a07080d4040041540d0700418400090708100030402104803452158507942d0359440040c03401ca140503a1303200c1240b104050028020a4400b4455900d42d11443c8400080b5800c1101c100310050421603082d0703101d010804240412040e0fa000b4150510b5015142c83d41c44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 632168138 1250 632166888 632166923
    0x1202030c070b06190902090f0d031205070e090901062c0c070309031a0f10180e010e0f01060603110c100c020c040c0c2105030708062b030801090612 65
    0x690001c03042203960b0820300401145d07840e11a0300901900c901251702c404418401004e0006802d10260050301042c1e4a5810f038101d0016500800d070302c2400b41c94402e009501c1d03000020030300841a202c080d80b0382e540305403d1104000c036440d106541426541c0e00310448040d1309840201610007032444030084c1d80403d246042600451400025590140e034440517086e000c02e10004042044a0020f20402d010f004225248070491015040da0a44e40e1060b56402484007008058002039900d01c5440d0b40e00d10450145540c00d0104c0190014040300108225140040090594100d42c2c90340c02c4c8181d08124420b540100003035070720b40d07520705403002044280e0303046410b90a048480548503045400c10b0302d2614100c1c0d019100c1020070348245d80788803800408811100c2c86403a2000b2000110310104040b4441500039810700741e20000c000c00000e6000c02030701341500139400b2780c41c0d000c0381c03a00e100882e40700301500700e40903071b001d0280080204000d07450f003c4020b1071910065000382100007485440002d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 632169388 1250 632168138 632168149
    0x1b030c050f1210090513030806031507020307050d02032a0a1b061e0e1908030409060501110a0b010918050f0708190b0610021c0e011202030c070b06 65
    0x18090460044551500907a45190300c2d0120308035038200015900c1c0c003022400c8011807142c05e001700001c2180c6000e42c142030b40d040d0b810040103845c041e4140304450701d500c00d400c40548080e100f81015030240d51544460b18007289410201401c000035034009100703070003500721245148007500050002039075907440211502410203c00c081c01400c04a40701903042002480000080200c0d020360b602c800d00d0650468855201c0d1703520b01c89100000300707000952501440c000c1d410016a102d00700e07034041803039074580302980342da0b020b507010240198540710b04105540e040050130380c4441ca8130002c3c05d412041566800c6c0b05a00500034100340c1640c0307650f010010807105000d1007101d80c0c0b010803280701d002a401c100c0d98600c03041c842c1c1d10381e41c0316502140026000c507801074156a0fa01250f00e15841e2200010402c48682000000c0114441e20a80b403d00030450803a0030380c945c03507640b204d140705101c110004248500200b03104441c02e0040051040240f540011181c0c0a6003201c50700b241922030100045 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 632170638 1250 632169388 632169397
    0x1b040c051204030f0f05120a0e100203070e01031b0c231005090106061107060f050f210c180d02040204081f05060a15030506190803070c08011b030c05 66
    0x81481c5034420400040641024000e08100e005440c0d40519048042044509125140f0140700d04070300100410242c02c0150000c80c1d002200780203492102d0300d0107907084200d800860f15a00010bc07541045c020031350b010b00c180303800e03003a088902c1c08140c1c51a060141038451000070081031240c103030340480c415014038406072052846d0801528031280e0420060005845c081e100a0000d500e010f500082d298003403459140005d00c0340020702000c0d494072000340c40c509944642e400c00c2c01002c225032001c0c098480010403143d009500880814200084d1b0020a41e40003044005850300400402d8411115841c503108002e40846880c0740d00180ba101144c0039001d26030104a00d842443c12400d1080e01c0c054003c0c01154122208202d15034070300c01000f002c407806200d489022490610b8540700e01d8480c0e000a94402d002406c0100d0303c1042060f02070400700d0b960711061007a04081221010400f41440301c00040c80c06100030b006102c0e002041c803c8400018841e03009041d520428040300900a03000c0c0ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 632171888 1250 632170638 632170657
    0xa0c0309111201150e0f16090b0c0114041a0c0c032505010903091514030c0304030e032a040504030e010503040606090203160e04050c040909060209120d0801081b040c05 74
    0x5084550750726421a507404003a1480d4820000700d00024422440181c3c00307c03060040750340c8500f00c8525140d10307106143c0c000c044c411229529065840680415807201c640603d2140d00c03440c54400c0400003010202c0030240140181a00c100880c951003a000416a182c0c069001c08140300308840061040551003c490300900c0c550074030f05280c1c2030540000b000d00459007080b40c0c00f02c405036881d00888000084080d01100e0400500104800030514006154061310a040040d56800c03040c001918203d000c0c4c21030200303020207180180146241d50541101200705560034440b504095174041c0000108039a80c0c0e04000d80400003d00f07101d443d420500081a4041085580e070810001700c40341c03074a20340c1460021441145081038103003020b214032480380280300d110314103090622900034043c0c06420016241c072a003e200b000349039600d038480500c0d844070b0b280040c500c407504100c01a1641c2e005034045101c0740c2081100c400e8421f0740303110090800000b2100000d80040e00402136540b03020783c1205 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 632173138 1250 632171888 632171921
    0x240b040e0a020a1208030121020a080105010603062403050705070b011d060904050d05090d021203070308060d08030f071b0b0402030f0f0a170702030a0b0a0c0309111201 74
    0x403003445040205400000a00942c1d0000005031648618025050f8010008003165002c10041200300c98540d803010030102210368615120805400190409a054020310040d035520f2004000c800c1d01880343c41c0091412001c69444078070011012100d1850168138942815195000140200d10036811505819804011070189586410481003030300b6091154540c0a00c5082c007088081c9040c044651146274854020042c2a401170400c40d40c0b5001491807a4010841c40317031140050b51000810b105241080c0000e40d00c8808500f00105040005442a03008074a4081c0100101c0c40e030a040340e51204280810701d5181d00c400008a4080c00c500085850a0b10450101001c02c001500c21500a5001300c04a134070004144070407036110030084600051a41c84511010009906000c1c94100b046010060320b090000d00c0e0007090174000385030822203d40340728208001d101c5200f4800d911110016281c00c11000c0100d0340c030791700002080342d02d683c031070b440e441c0c14122100c009410082c0c1c040c40e89101c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 632174388 1250 632173138 632173151
    0x240f0503120f0a1808011505090c090d0314180a061806032d09030f0206101404110408061b1903020c071a1305041b0503070215041101110604240b04 65
    0xb5145d008102059007c03458281c0c860000445140c054140d80c000c0d01d8442c1305a20380a406001c00180140d1180c04805200b48003407075a01020070b1002424000ca0180a030f8448600c0c081d040103c3ca14594000b1420f10241a50784110956560070400940707019050008003400100380700540342144803080340b00b4010b000b1851106643d950494441d19100b81c45585070f0044400060f41c5403242100c1c2042d55114000c0c2c00c101010500941125500000e007001400400b9841110321903405600300780744642c4035106114001d050001000c17440c04190350f6131030400600c6c80f00307105030409442a140401d81c020940340c3d0241c0f02400420010b01c0403410204106142141e01071590b000f0131906c240c16003128000281134241406103071030021020103180400700c24450142c3c0e03160005840300d021031140060254002d0300940c081070245004195012139106410001086440f455280129540191092100040151180c004001c0c001c031180703140790b03000401c2c84e8010500c44940e10b601c5401c089 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 632175638 1250 632174388 632174399
    0x9010204030c0f0816030b13060207060207061e0c0503010501052b0b040609050c0f030c1b061014130c0e0307030c1505030f19240f0503120f0a18 64
    0x2007000ca581903130980c0e0005002c40300c0000c8004161002501c00314003540003982c400251102030714a9031052400600f4414507850b07050803600b06090440b00e00703948040c000d01005900260790308401d8122414040300c144400020000e00043c4a90380c14803e012421a40c108826000c803150078080e104d501c407540c4290740c13140c80030309403250040340964580000822040b000b4084e451183d40000b28007482c12400c05500d6046510041104500c8481400070000c41003e03041240828017686000700b0040c1801031040390440c030700d82e0204011220b800c500a006854104a09c003010741001700000d40c410012a06681406100f404240d050040150200070071840000c45400c2d04c102c0c2ca0550305404102e4070560340c51101780c40718040381591600281d000d100e1025003103e140b1080602059160b00d818000c0c005072038881140c807290302010014080015420f1401000b0702d800c8000b13101c50507480801c1c00e05880340c03449075008120001805007649002c3e212220040ca0441301c071a0100e81d80702d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 632176888 1250 632175638 632175659
    0x40302060a06080a0b04080f0f191706091801020c120301081e15040f0b0c0d0b090c070b1f030c0f12081209070305010c020c0102150106020a0b09010204030c 69
    0x1c85007216100d140180115004000080104100703034004144003140d04c817078070391845642200d004030368005070400c003c9240668050140404000d22159009150745041b4040c16250b61605c9890408a400042150640e190150301d0f4004910081180c1c40450018083e4003a1141d001100c0c428450060035400301c07401e003c01581200d48500554468203079030b52070303c024101030b450800d10741d81c003c210380c00e400a807002c40950002d2052805481c84611940c40d40c1d0700080494400182110104244c11034101074000c8501c0b0040443d030002e401d03d414031700c8050038081e4403005042c04504a000034542440e06c0200c4e50a248043e000007104d50f034900e800f03440c0307510030f01a002c4501c101120005140d680359200c1c120040d4000203d03401c0c100c0f00503030ba0301107074801001e40d52113105161000011500070b20440902010a85c0503000c0e8001800002e4508440303040480b101d15000e5004000241d4041605403040380d115082030060b4680040786406405146c00280c101c1030039540020f04402c03407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 632178138 1250 632176888 632176891
    0xc0302060a27030e04051e01090905031e0c070e0a14010602030406140c011d1e0d0302220b1801080f0403030905070b0c07030c060206150111150109020901021510050d031704030206 79
    0x1247c0d04880d07643e803152200c3c0e040d070b40181d1009000b03600c02e0043c1c6852050580c0000750104c00d20300443d08194848000030b00e000306607800008a40c0c0380105000b4103044500070940d2048044c2ca0600031540742100003540c0e441248246010400001e145c0018805590200c03400d8541100c001d110b00d40081d14801b051414818100b00d5520580f12042d910341120510074a070f010b40030003e011801203510013540a503209007982001c004070025980c1c82c500c0303491000e0000e00b045442030342c1c0303a4207125054100d18000e54001414440c41c2d404001c4900440c0c05c40302d0744981d0615020900c0c2078645401c0345002020f410001e41c86001103a510100c09001403c90112405200c8448000743d8610041c0e85648d401c1e14003800000c44070700750340503550240280390b029014150885800d02e540303103504210074a003a0000c888068000440c50419a810004e0480186007032a0160f00340c18041440d00d0404450700c51580504d240721010800d250145a54040180c080300664182d40b0301858001d446040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 632179388 1250 632178138 632178181
    0x130090506162007051903140c1017011404090c0303120c0314040209090f010606020309040b040213032907030c020f160b1602100c0302060a27030e0405 67
    0x80c10010300015032000040140341e048020f020700006030821042c0a40c01070701c0a0003a1303400d49104c1c00000081d800e0550a40191920000740014071a9881040b800440204d00c160400c403004c6440e4076031508a000e0541110b440060f507640303414421010030013078a40e442000e80030030205000041416000158130410001c0d8140400040c420941c4c1a8103d4001d000541e100f405030703100007001400e100740055040410941100c0c695000721081600f51202ca81000c001a00007003800541820140030381328076140220307402c0d030070103044c212000340484042c44080e285001c003042030388803c400250003011414803a01070126920340b1050107000707050b240c008540184655240140424008211504220090b41001c04032030300d054906034084c1c004501c1041c800401070f00000040e940c0d0010f480034035610780c5071070794012080c0c24080e0402c031004000701105070400980d290b0350144241207140300305690807069100c080e117040c102c07030381c007001035051340c01914240c1401900013020310610140391 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 632180638 1250 632179388 632179397
    0x90e0708061009061a0a03091104051608090c0108060d0303020d060f032616060b0a031a0703230c160b1b0702130b0303070f03051206013009050616 65
    0x1585e441d4410424400560b08124005080c0410400300d40300382c0044a50b00d0103480101e01b146801c40000b400c48405a58180d18001458528560941c2081c1c8859000f20404041c10150203d100041c140100080c0058803904064840a01b0140a54195026801002c60070000f981c1c460880031f0715088a4001601c00e0749408030000007030b80100d0320240f601101001c1c2d507820149d1500d8610707100456143c0c05c03154241c8035110005d081e1a80d8648030000c5015280040145d0400f50710811825000340c0460704041c144150314224604694100a03490b036013002015007640c2e80e0b054600240180840f07101403108a5001109001c02e42d1030490140708900c18200b1084141d10000c202d81c428500d0003900854400c90403901d0903d00d5001c0c6507016000750075070f454262940d850030030700d02e402802280401e802141d04034407050341c01c000d181d012000382840b00382e00c1e8845020501807a0000d0f51210096403210a41041095a8114540d0035500c1411074a0704d04114050b024140c0280307540e2000074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 632181888 1250 632180638 632180651
    0x801050a0905060d0b1302060c01020919061e0509031c02070605040e040b0601051612090501090b12090f1207020f0a0f210f03030b01090b0310090e0708061009 70
    0x1401d19100d503d0280100400c080500903190307485d00c840710002800041640c0600c14084051780740c02c40100451901c400c0010381c1c40d248001003104280070b0381c1001c29200c80380101032120b40d0b000403603c0c030070380361103010310200e000304900c100c0c1d00c1c1c4201c00c100c40c0c050042c2d42c1c441c10000045001d0f078070316040e5a0252100c0f01e0b104c9004032054043c43c802c403c941107006001c28041342500ca080782e0400810b00d040351601d4180004001d48481c01d420480d180c10710140d4515480380e00004130800342600b4030300300d890285042103d5085003e400341005c407580301d107008180488410403120081001c0d04082c0e40c0303810034045c583c5686411446060380581102511035205103003640100056540e007200116039282040311100a1440c41c0701c2503010820b01e900e1900104108001c42c4a440c0e1080e900880c083c07500100040c900705056020595000c405d0041c00f4030311040703405040c02da0b80c181360001038070842c5140207460844254058495070240205001803801810f034030105440904030f050180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 632183138 1250 632181888 632181899
    0x4020102060117030d1508030f180904020603060402131e0f171213120b0106020118030813050c0402070506072606060d020d060e0a0e370b01060801050a 67
    0x30320f0840c03455481e001003100021184040d44142d11500180c1070310140030791940034851943d80302d0301c0c0f43d41c180d2002150004040e184a02c07101c0d5003440c261407170b5400e4189a0b004c0781c124080680060b11841d00800c150101142c001094001004c58840010b41402c5000e8040c0c0704100034050703c41c45003a89400031505078404000890b400c2103030700c000d02400c01c40c018480b04a404c01440c03100680c1c8a840005000d482524070420030350f00800340300425500d8030f000a400c440e20400c900d030501c03221007500000b0035008070343c442c1c1c08900500c0a00c406000e501d040c904000c155144d0307550061010991005002d0000b43d02403055030705449000e102d00b10303603640da019500211601e600d06403820300001c0f402c5c103007c405000c43ca2580d10f000b40c1008880c2d0b8044098800a07044030044125102c02c10101006030b0140120101425028081d003450f4200840c0b81d42e0340c0340c507618030180ca40981418202410040c80603416400c0707812a60302e9611032000424211081c0700b4036204402e0304201190 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 632184388 1250 632183138 632183159
    0x509120d2006040f080c160f060e010f171b120610090f1809050a060e060a020f09040203060d050313060f11100b010e1201050402040f06052101090204090308040201020601 75
    0x255400030440c9900748210703900c0e144507910003560100503000d6900801d1107400748003200c7c005450785100131444a42003d800030003c16030340444c00d041004000c10307440081e41000142e03816000c56a2302400c2d41d0744012034643c250b0410038081250401c009414a0740084214845006080881c0c0b51143c08401c20021034030400140078013510741d0030a00007040f50740b100e14503580e406103030340401160070301d0140c560a0824421003406d50311903850b02c2100d240f0182c14403440354440d9401c0c2085080403070100a2010b90700803090101e000350750010100e05583c2c0d4800d100d26042c0d07803000031285d82c1d80b10201e24030b4041816120300d50200e07018140750016240203c0e0000317441c0d12008000c0c02001200100c0c04003415914007020b040c80350425050701d0a482b07460b601500b4900d07010010403103041520501c02222100c00704000d41c1c6103048403d001caa5549a81042115190882d00f814400c83d82e28090062440c010029809450100e24004158106090a100d20f000740c00741d4509a0340c40d2000b28 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 632185638 1250 632184388 632184391
    0x3120423151201330503040c05120318030106061b02030a020405090a0b0601030207031b1104050901060f05030f0a030f050903010f05010e0a050103210c0b071808011107030509120d2006 81
    0xe40760725241c286460b1380b8850409941c0c824020200590855030340e502090300404a14007080da00c2c0c10025400c4480301d18100d51607805c490980c001c210561070140014800b4034000104607140c1e50300380c3e503882550750070001c0c1c3c5420340e0000d108100700d05110490a944005180d4101c0302d0701c6812000803815030183c800d6445187e0103440e070703024803c2108654800400a01f2084a0b08070700601111030b00e0b141c0744184d522030703080134000051150800948141c4040b6584c0294445c0e880004d0881c0d06140105070f002003264181070051420508200546850041c0f010968156203044901068240e80350000703412100060b13520341325601d4260034030054420901014055064020780e0710716551011400c0d1129103100c2c50003400c81d0005503130303c0c0c1600c05c1c142c2d000000214008501074000b0003911007080101240c0c00204041100390a900c01903000b05080a020702c00f0100780075405445018000e40d0f2010380e00262900514280c10182c4848210000031481c84c2e801480500e50040024885 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 632186888 1250 632185638 632185709
    0x7030203061006201c0302040f080a0f030e03030d0f140a0b0a06050306010c02030304080f0c10021c05040e04060c030608010905030315010e15030603120423151201 72
    0x8044c0d01307888052800340b0328061804050300f031045e482100030b02a15011180b14101d416030707001d80d4039803412400d2500317180c0d1500b01d0b044a0b0000c003101c800082c54024a22819541410102845410100002d081d805949200120681400081c2c80901a944d01c48880b050422034a424a17445480320713072044038611010203030041c07062a400e01180b80a2000783d680440140741640c80014198082030030740d042684001c4d0654410485150351a00c10301c1000602e176010742e5024100340c1c2c04000203550b4801c0000f100d20035000981030038041c3d44103100700d40160090070402c881a00b46450110001c00100b1900c10009203401c00c0454407950602030000819040030003141140c80310300c4805c0d503098250f0310b403d0502035040050702d0035460301001e07851100da84112040e04d80c60803406244c14407041442c2c8407d030700c1d000c100c24400b0b100700c5c001940036003060740e10b4082805445070118006809074244504010300104103550700007180151541030f220051000c100c0712801401c842c00c40c01c0c1c40c5050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 632188138 1250 632186888 632186897
    0x2010c0207090c0c1716050f070602010207080d0b060702040911010210060b09150c12040306050c0723010f0509030a09050307050a031401060518150a0303090b0a12050907030203061006 81
    0x350408a41e924403403c0e51503405e42103031854a41c600c540d00d00340c04104030007250a9000703442d00d000c803418144135510052030240020751500c1c00076510404688507220030020b1040e50384a41c004661982800d80e03440e00c0c0d0107401001050494203152841140d400c9031640148540039002e52006914041c540445408810310341c1424580400c12000400c11180d03200b420b0814004589001410490307580c8821400e6041640c850071030030010140e880c000c1005290241c02c01c40000000d080003801784515001c41400c0c1c00d224250042517001d8001803001c08075540c2040d05104003141e002c03005203041d1039140c4070751281030340e03540516456200d5440380c107a0184d1107a40800200780b4069601c2c200090000c00010900c0d00c800015044c1983d911401321150417450402603200c44c1c4a40003030181000300c6642000c2861580e0090415615000e20484681c1c0072038820742c014001c0c0c400900001030220b0500c0245848010107607518a9440140c2c400d20440020807489807000480a0545070f85030756 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 632189388 1250 632188138 632188157
    0x801061e0302010e0d060e12193902030106030b010303021203011415090301060807050a050114090409022e031a0d32060912030f070e0f19030b01080c0603061215010602010c0207090c 80
    0xc40e2b01c2144048901c4103810030122032140040c0d40038851140907510500d80d0740625411814000d00c0d2072000340500f5415802000180080e92043c0c1c08001108011111010410541080c07030b4914041c1108250b090b600701100442da04501050203c20b4a40039200100c0043d0740c0c2004480c40880c0e0700b440c90042034100a044bc0301d0034150450f04050740090142c5c0241c0c01c0c031506401c050803a481114988480c2500c000b03141c01e030b05025004c034170102c21003400355408201001451003658010001d03e00203040501d07001c0c000001c009041014107210300c41200d4614010459294082143e4410450141c040180301c80c000b1901664018000e4203040b103100d945100041d181d0b4a0711084580c3e100c9102000b5814556408006441e00f011152010017040d01c1c600e0300c20347c081e01c103030004540b0303400010501e41192240340a0740e80c00076045590480c2e440d41c002d40c5505104240300640e9881205400215036680c054008189a040c07607422200c80640d14014401151a18407243c40025280d80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 632190638 1250 632189388 632189447
    0xd02010c170709031203060503060703060b030a05100b07080711030102040305120a03020f0307030b0a0501030b031009081303082502130e010e06010801061e0302010e0d060e1219 78
    0x9141640b01d181402c0045955450740c440605180d60301c0303010000651104414409411309004540c3c01c040241005e03c80c2900300014240306000080008600c10f5840002400c10340c442c0c40c0060040407581031182e44e4010604016105a01611007903031401403000e103510080c1414821241200e0300300b400341844071401c0082e00c0e03007913000000042c1015002e1040c100c403155040300450048005440010f0710140600601c00c010300168016810716182c00407050440d05c000c150034019006038140016004800e29002c0c40c14084c0400034550220240004010002c80d070006016081e40c0b803034051f802162014502e400c94610a030029005140101c3d01074803d207954008562180750f000021174840c1148a0707042c500701b000d80c8041e45aa4450008000c55101c0016190700820707005940c0e4000d90454001074100c0105c4128103002c0d4200ca49507005020b81d0303511851707081a807102038500800c81003142c0d440304c0c0c100c0402d8050444604503550f1400f40100d805415419008200041004141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 632191888 1250 632190638 632190677
    0x9110904112a0102070c1d0f09030a1b08071b1208040306050705161b08010209030c0607020a0b0703031b0815010305071b1b0509040f11042306030d02010c 68
    0x102c040484641d000d12103840003a000c40886c0e13010307003640e503081c100c10384a41c28440d030410b10141a44020358046004c0c450804008011112012954102a200901c818016040b4880201d0001d846840b000c1090820018038400d03403c40742078400c2d00804a00d44517101102c144038203c0e00200f001404000420001c1d20a80180e0b078400014207189061030011840b40d84502c42d01002180c550051282d0301d803040138441f01d01c0000d084100c0003142000707802e10100f56120808001e85200d000b01254207401c5545e6100e1002c080c2c48410740c1e90b03499542e14174000c0c01804144580b8540801c00b5108004064450b4a5451042d8400c00d00d8900030780c40c14006400911019080728108652210060300c45002c0a1196112a00c40c4005000c0b034012003200e804800895044944101440d20601011a0001c07883c40419900549800012360800c40090000d202040c60040d402e444007500052070500308285500c074070300640560f081d082c18117a08a003240c00c0341109201041768820040c9140400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 632193138 1250 632191888 632191957
    0xa050a080604090204020d0905011803091208070c06021f020a02101d030417010b010c0213050c130b0909220f0c0e0f0907060f09031b0911090411 64
    0x2d040040c0a00311900403c06030707400448045845511948c4c000c2c10014240b00300380a003401d2450302180042c41d0350300242400c0300c1e0b1080c032405025440c0c40400f440104001c0b55812036001c2c4161407510364841c4069264588044114410040c28048811200041c021100b0403035055025000d07407003108071814010460101500f81c110404a018494040100000d01c047c3c5040d412104500c114455010300356489282554100460855510010303154100c05040002c801040400c60381d480c81d4a100b031a005800091480c24118440007402400e480c0c0105a441420303a48102543d40d25150140e440813218000110010204a19004900300c1910011031500c0341e854404406c3d61801c644003944d80581c2e820144440a10130320241110803c9105c0080040303041050005c184403070003400d030138024400a0301c0c124540705001c03080301b03090f201500030301421402007000155811038011a5001100c41798001d61518002200900303441e000d81380d150302a550712500221301000e0302c1154542 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 632194244 1106 632193138 632193151
    0xa11032106031209010c030203121602010e1609150308030c040e151f0215040c1809020307060e0604090e010b090a09020a09111c0203010501020609030a050a08 70
    0x6084250343e000c6601b401c1848501041e41026419445058601401c2d40100000c021150841ca1601038003009550f00030410604201c182030358550401001c0e8120058000d0700704840740e026041000701501d03840780b02e03901d50f0350b940d107104960b0020340d865400e806002c2000e110260300e94407955849074005c1d0308038111241c02c00c00b18501d0050a0b143c000112007841c100c056081c001c0000320075402d58103212082d603203498209010303441098011582041c604406c6206202d4242c0a4800350b550010043c18000d031510f0400c0e295500541030594001b442800b0004100665124000c03d081051001080323500780079042060301c800041c8840b02443c5485100409a00c50f051400300f999052680040c52610100d00c48420f0700442c0700d0780c9072504e59014807003d42d80d55900954100e50342038088070095100d542c1103035113a00680039248002003091110b1079150744141c420f26003050 = true := by decide +kernel

theorem cover : BRFrame.Cov 632014388 632194244 := by
  have h0 := BRFrame.cov_init 632014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 632014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 632014388 ≤ n) (h2 : n < 632194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
