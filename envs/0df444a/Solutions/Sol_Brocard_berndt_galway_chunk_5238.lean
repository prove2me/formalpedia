-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5238
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:12:09.218263+00:00
-- url     : https://prove2.me/submissions/9c393947-c713-4f0e-a9cd-2877db977818

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 941906474 ≤ n < 942086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 941907724 1250 941906474 941906479
    0x30f060b060712051b010f09050618060f070c1e0b0f010b03070c150504050c100e01050301120501091b05031b0d0f0c030b041b080105100308030603010f0f020d0b 71
    0x1000e8190b200c45034202c155200f00c0092120002e0a40034940450106002801c1008000c20441d00c00308071000203800c40b1381d0111100d0150b90001045210100e40500c0c10211900052034aa50f0301c104070050b144028141e2414044240581030003d009448000031280360407240040f4440b080c03615452040c0040c01000c40100207e0041c0710f4030f5000411349501a00901d0403020707240160418080c1c0000c1013003407641c145e09040401040c0b000000301299810029500300c1c0760701d003003140c0407213034081c0804105000038400c0004021221121a248210b940510b00019a1911580d0303078040740716a1200f0b19164005480007007045180c18003045d50500c00040380d481c2010702007000070f0381c80c41c0319003c010182540c0d0313030422061150b01c180c80009598014000b2030f05052908208001424041100111181c010340108081c0010f000d954050340001b02c2a000c41d9096a03201400d0b600010101a019941c5420b0442510000e000c0c01ca401f64103210b0069443e00e80100c92400d4800b203d90090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 941908974 1250 941907724 941907727
    0x150706050c0c030301241d220608070302030606010903051b01050f18010908070506070b04050c060301060c0c050d0203101e020f040906060807140a05040e04031805100f050d02090a030f060b06 84
    0x380000341c40d1f40034082840b0b0444080c4011030035021030b00f0200d03101d10b904c4440c0301c1c5050004610004000380c1403080d41d0033202161003d6640900443d01010907002c010495001050b07401020302c0c01c140d40c081001d01c1410400d0400c0445c0b00310344e1140c1c20400c84400f5204010040310000c0d42c0101801018141c15000741c6035441c18800420081e2098a400515014050001409014040c00210903601c4001c1425035a940d4641009101c0e00180c2c50a56001c03850b04c0340041c4030328200c46900d110039400f4026182c050401c00d070b000014910a101c650481d9984143c045038010301d4402450001c0072203128686442c1008a204102d030420f4000c00f050014450a100e05980c02082208400c000d51200075580e400c4164111542d01841d842903125203240f9040c04100f60708031040e401c1d440d081e02850020365030723034030b040001605003c0c042e100440c40c400301d40c008840c4903100600856041c001c0243c40c01400d2400b02d800f1210340ea00654050611010000401a81c1e0046038188041150076a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 941910224 1250 941908974 941908997
    0xb09011b21062d0806042006040608070e0102010e120d06080102090d080d0e12091003090b060402071b030c082e050a15090e010b150706050c0c03030124 67
    0x1a40c040c0505090600303c19101586590000c0c40d264244040c101c0c00003038072202c4c00d2501e0409090081e1084240f00480000341c0d0355410b0030018207440c100c48070f81d078401720151170b6190b007519044415003e090442d501d9029030001e510b4200940000c41c20801005036032200304003021400c50700c1540141060ba40100400d244031381e1003000d600c1140750803060141c0c1c1d0340101d103103039002007420035401645402011019001002c1084c0a400301c010141c1d55920a5840c2c41400c82c1150b042d4900202541c01318000f03e03605050a80c0a01800c511600300c00d070700e1400c20100c60443d40040e074000c984103060050b0920401a080c48646240c060000c403012000710300c1e4a4120300007500741900c0341d034a036550000400c03603005034200c22410205100c80780050740d100d0f0740d814041e220300075400350a5802c0c00004080d030309001400344211052180b2050605610740e541d800540f0b00600550800348051050070145103081c80198003e090b00903a484400c51440315050f81082c11844060070300c0301c2e40024 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 941911474 1250 941910224 941910239
    0x1e180111030103050d08060612011e150f030b0a030c0b4614070309050a0b13030b0402031e0a0303060e0f04060e1603030305090c09090a0b09011b2106 66
    0x4490210340340d410b11103420f84d44e803808500c0c01c9c010200031408904c856400051b450a0540810b4400a1132800e803119098072162051690030b023a079507010000d14080c5100d10254800c3c0c1c800c610912005200300c003429620f443e69004060300390001404801c0001da400011070041c405010800e414034004000905141800c07000c6e142c40100348844540300f03989843d400352203051810003d400e900d03043d64030341d00305080c014180001c0303002d814092a024480400c240605109440c00d012200146409040c155665186d0303424010b84100d03094481c04088044c2128111518002541407000a2203600c00da410010207841d419801142094444401e10144090b1180380503402a0465004035645450103030f89440e250036a9074000c4a20300c1c0f29004800c05606811442c003c2d461001110380702c8152108000d03124005075031814843d88401003141c001007040c0e40f1981c1c0203048038000a5141c0b0442c2c1e440c0c0328210344000e55800110900350000300c00341c0c0000100c031200359512003042524100f240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 941912724 1250 941911474 941911483
    0x15010906080604021603080f091c12060b04031b0b0f3016090f080a02011206090f021207020d0801051c060c050316020d0905091e18011103010305 64
    0x100310400003880005030b0141c907030f901252050003050009205144150500600d07061080e50405e2a1403006000304011010014088000c41000a10f12860b80f001c081e007511100b0740c608440751413070340304d0f0130016610244074040c10041d8005c1322400f41c401c0380c55100d0860843c403a007019481130014851429540044c0301501d05070814991049010581010150043c02b0050410f4002410b000c00301f200000c548104910b00100f01e4030f031a050aa15201040369164590044402c540d0015044c6400f661182d105030b41e19840f1018002643c60301e1702d00181c1a034074030b50840c06400d50001200740c40e4010a802d042c0d07101304148050000480c00b1540105141c0040c411140305061121030a0b560148003401d1011031940310004021517165808083d000d504115102c00d821100c1201542903180007091002a03464140d41e0700c41c030642801c00700100100050880340c10310a19142e00b9022040a0b0101e0f4018000c80500990300140c0c086054251108014144500202400100001400001d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 941913974 1250 941912724 941912729
    0x1203090d0207091a010e12010603123c090b0307020703171317120d09020114040e0a0c05160b0f01051504030b0408130f03020f01030c0e091017030909150109 69
    0x18000030074044d01b4001034400707240015040100e51900400104010001c1000090115183c0702c481520540c0032100d81c070381c1001d0905201b018504060352500d21081458104104036508101483c103441e411180e00f5074104640850260f84020010b00034030025070512300c05490303401c11042c034142001c00441e981c00d100744911482038103485001ca40c1d102c014440c41d100100310301d4105031107031503a010050190005c413006038003203012441101c0e51040d021040f1000d840c02245014507030b44492010030300038041e581c00602001000d0000f81d00080d0140a0002e80900401c2c0e4035950303040030707030080302c00c140d040c3d005610400780002c1c10700c00ca280710700030b0f00c0c12242c00c02040b00095a8600300103800e840b50b401d13101c0d100203c0030408940c0c102c000258000381d034020b81e14a0003014844006400b00c9070000d18150106105019a56003032034a42c240390f901504844a0aa0040ea204071840880c07a020300c03500c5880c1c10101741e14600c2d0500c255540c0c1d110404a000401d51403031003001800c11b80590 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 941915224 1250 941913974 941913977
    0x10e10030506010f03170a05092407030c02040b0f100f2307032a060e151303080f07080a05040203120a03020c190b0c0703110d030905010c0e031b031203090d0207091a01 74
    0x54070058801c284c4d8010030500340d2004a881070362f8600303902e03008108450403c0c1c124811881d103020704200c1e051640400450150107004c2415200c0c01e804195100c0348031a54080070404248010300c0701106000010840a6400c500191a00740500d400b0341862010b960080c00252a80d43e50808408500440190203820490000d00f80100321403060800c03040102d2a450400d00300e0500c92000741c100031403d1103902a60f903041154440c0905000380900030703510100000c460a003c5580882e260b07100300d801a2000b8200c2d074030017000a621b00d0103038001c0b41c804c102103580490284402c0e801488a040050950441420340080c16a507080555a003d4500350740000e001c21001c04041c0503101c042d4050084104560404e51300402c0240030f040c00c40c3e8202c0b02c0f9400d059400c14800e002d82c4d4041103294005018100362412484600f40341c1c3c0c0c4054942da0b05100c0c03007100780440e4008100440c000c0000b18040c25072a603900d18064645001035000f090141d01d4044070f01e404481401c80070038061001d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 941916474 1250 941915224 941915239
    0x1030b030c0a063204030201020d020a0b0408030702011e39030c0203070c0b0904112a01090602030405250812031e0a0b090903040509010e10030506010f03170a0509 72
    0x188840010184100c84450661110204e104444060340001d801224400d0b070884456850094049071155002c00c00102a1408200401e001510031000b07945c0c441d641d032000003000f160300c0b07040c4180b00781c1c0f038182180a03650f9004c5600f200c0d61101c1080c2140e9980001c00c001007550006411200ca6070803692408142da1403048a40303941c801e008a480304d6400265208005460794030303003440d41c1e000d242503920940c41c1c4488401000a160305661522903005010a42c618500010282c4c0c0c103031407d441c4140f55601c40c01d4000003045440550302480c082c500920251440080403040c00204042240089640160810901c0310010b200c405020040c41da80e80c40c0d0303c54000000141500c9208032003045000800c01c60446029400890b80b80c00c101c804046a0700c45010321794031381c03040d0f0280d0340d00314100c000107000e000080f100d10f9410a03141c1c145003e009613203072681810404280c01a06405c040031034100240132402e141a00507a0a101e0035038603000407640060102e01c0b40e0366510340110b0b80b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 941917724 1250 941916474 941916497
    0x130c030b030706030606030f0908090d03020321063d18033c030e060c010e070e060315060d0c17030c01110f0412050a0501061401030b030c0a06 63
    0x21a401030320314840060229504507480d0350001c0c002d070072540103d100007460207844088503c090f0180c002029045604680340c15810320900c01d40e4080490290154801041445800c00c0c03002e004421403075080e4000b003400c0c00c2020030480244104901140318480801412a07041d5030004034104130324948081c6840c900d1001c80903240e140010044200c2070031070a100200f8000700d442c41000c124000d020044401903a000082c0414401506565540d05080f5200d00060f004002c0742d10b2407600200040e0502089400c0a403d4a0f208550b101190300b1003441004048400810715401c600100c1c00307011070300345e00007081c1d100e1900103040c1840381490411440c01d029071001c0d05000780160342c0c030b19105038802c2c4030302950701d500180041d00c05629224000c19214043c070160b4a0100800030a540340c1890050b0800c46811000e9050b13500d4025046200d000542c04d03c01d220050540640440c20410804005011a101c20040500a030400c1600108664403802ca40081d0345083c2000e001d01d00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 941918974 1250 941917724 941917727
    0x1050a1e1208090414040c06030f020f04030f0302070e15040908130311180f0703090c09021c060e0f0412090512033c0901052502040608010b130c 64
    0x18555102039148407441940c00c003880000d00c0107200a800aa800344a4014000300942000000f110040c0c4003500b842000d028041c1300b500036500c90243c00f0000740c2032420004c0c0e940d2090303001d64003c03243d01d00e00001d03000030160140306a0004003c100c2030703e0401d10b40110344a8000c0c11101d080c0384203035651748108003007107440016507190610060607030100b81d031649002c4000c0c1061086803803103215000388600780d100b0307000d091900c284503d055003006c40d162110142c000d05500c0104880280601300e010600541610250100c11760f40030549941c10846e6803010700311881070b00301c800072441709401c20000c80603101107550040d40c050400607100480503001c45448500381c000c66804551941a1088218008007402e488902d01f060a8001d00001200c8a44281c0e1154103003c420381c07501d40030030080d0842c4007500d00f078901814054903080804043d8000d104410300300200e189040e03003080e019420180300745030140c42c0c090005c02161424034001014940541c6418108a803039000511285 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 941920224 1250 941918974 941919029
    0x1208071b031a06030f1f050426041503110a0e010525050d020a05150702120406021c080903160c031a070201140103120809012c120301050a 61
    0x2550407100020b82c01c81c007201100d6030070100f503448511034441d492804244071004141448000261140c0a1102162001c01e4002e0400288180c81d603006101c40403075070b541d00c4d01d550900d0548403c0c51a965604013441c035920019000710aa0402d0314140102c540c040081c011550740312071608140c1405907207100106e94510901c0c0444000c500a400100880075100e403020340070701e109405a460025000804913945e00205102810035844441110800301612481d1f0742c200f400c6206590310886401300c8560035600561101c0016401182050311903510a01e04082100a51400b00b141c3e0620854a96884c0107000102c500c0b100740d000880304010304054075000441c1d0000401604c04518004000b05d62011030380b0784c005d942400d0811101303034102c051107410b0300d5000c86815179007003088804440c826002000250199607402d03035020a4025043c000880c0c0d000042e05245000444240c0348c00c0c031200c415424050f101c2800144415550381d00320005440c9900708a4420185060841564 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 941921474 1250 941920224 941920229
    0x712260a1e021c05010b25050c091302010219032309030714090108011503080c1e0c120f0d0c08070804090203182d010e071d011208071b 60
    0x4180300042c0020111242e64030340301954a0000f08211903030781c543c90500035200c0d00c4202e02e04043d9005080914180780b02005010b00e004004550f644403217240801c0b240041602c80b420b000e10008206411582d0400003a00d07800c102c28420443c2101e165005040207401044010520140e0341c002007000740c000c0d090f1200c01d03100a0803610201e0303840481d002007206c3c260340d4502a0340100008142e504050007020030b1074042c42c400c1c010312891074503100e626411440030400e5170b00989a5111001c04100c0c05207200c00c85420241c05c810122508002003001c0c1c1c0b1944003082d401810318401940d0b00403a9400d8002d1039402c04c42d02d0032032245401882407181d1a00205900400300300807a06061708c2e805075221300c1c032801c440c4610068145030340d60b40b401c180ba00ca00c404030b480945540c0d004120008101c68440e0380e400801d0008180003c2818020301e60400b0046c52045154000c910000c850841d0050450640108010407103850f4141148920380e8003400740310024040300e07605074103140c0c1c1200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 941922724 1250 941921474 941921531
    0x90203071716300503090d031407060c021e070b03100812030114010c05030d09080408011107020f0a0f0b18040e030d140c180a0b0712260a 61
    0x196240c450910f00f5902d00d180a140000f000039140c0c206a10364660f10314010f0315000002581030111203c00c00c1619100158100d0406c04001e800c20542c4035068042c0501c0b501c510008625204040d0000380351100c612842a1880b800b00c40c688141c11001c600d4006480d0302038091960b03035542c0c4281c910500c3c06680134000c7c82c4505010301d00360307060610255069881c81a020740d099540000112604a850100036000d50800c000c0030b8480140c1ea032080068038440d80103541495039505d2068210b0781d90040d00740054100040c001e0440c0313071901c4402400d0100302c2d181c03441d40381002500c0031400003d001e54946090300140422030210b040308c0b00d980031440100184601c0085010840c2c90350803149540c0c896500300200b02c5660705640d08650f00c12201040c20034100551140d90010105c0707080030080d00400c02c000c0c0030600381040f400500b4290301842a58034100090340d00201140001d0101c4041b50140700b40361810300115202041e00840128001b140307080c03540c5908890001d11401880 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 941923974 1250 941922724 941922763
    0x102091c03090602121204050c04051e09010504080406080a090f030909050a060510031d0604030302031017060c0a030b12060109060b1806160828030902030717 70
    0xe11084000000c208644607a0325418500e0340c41c10141d94580805504c04203551040c4021581e0810000015070b01c103019004440100404c100414101c44d401e03114200009643c2d81c10b00c1d5030780741219180c1e4004080d000200035918081e1512881030040d4028541040240710110300490080e4001c80601034003e00c80c20030700c02c0075180c042c0c0800d82c18450b814802d42040b0018070035604910405007101d40290042858400c5580c0032001000303002150185c0001c008a000302400082110a1044c1c1c030a480050341e90800d00d13040c1014118540c080f6980c94840b21218150400c04652240c05c9028940d4032511084e0320001a0b0150a9000c074068205003a6075901711341c14400690345040303400c0500e0410946848080381115403040e9002c212040401c01e001540500f0078800802c22140701184031141450542d550341c10380c3d4131807500064061000c034035483d4040e9205100c09184426814100401403095001c02d0303d904061160503070700c1c140000c4e8500034410074048070107441c050f0080701 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 941925224 1250 941923974 941923999
    0x92a480604031b020f01050f0d0f0207050f1c05130b180a06030c4506090b07030e120c03030f0301080d08060307030b070323060301050f0c07060905010209 68
    0x150344800840e0103400003000c2400000d5003155800344125159000b800d4101003542c8000152034550086111f03080c100f03000c1184c150302d106a0321440c40c001c03803000d03070250b51062181040d61030640d0441102c107060700510446181d003c143c0460320305a00c0e050510742c0c3c903543d01c0c4d8103601001c01a58080c101b401c000160081c0d030512299081d0b0120b2800320707001a011502d504d801c03011144201d03901800700e88042e041d0100c0c001c0400b940e0780d1800000003400301d04800c4ea04d9611080d400c003540d0b84181c03404060144843c0750000f403600e000d44240d0109030b0910303e1584000702818100641c0b41d008403681488a4160a13040c82900c02007000917003100c4d42c0341901c4900c11520f40c42445122254018421840d503594410100a4020f00c030040080002504540710748098500250001c0c090543d5030005841e90f102c000f800c44a6680804081031151424030706050030354900030040a20707414043d080007101d01051055500d01d503040000050030842600d0110300920607151940d50042401c040d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 941926474 1250 941925224 941925367
    0x6020a051308010c0207120c120308040b090c01080a0c09050a0609180c0807051b0601060504180539040909032607030911092a 56
    0x34003039020140080003450759142c1505080f00c244400300340058000c02404c00c4244403800c60059201d000b109102000350740d0b07007200e880c0701c1c0701e000b004c60105c1e4950702003001348424800c1c5c4650001c0c60344050102d4002c4400002c0000000071310138511981d80d02c4c8080c00d11440392940c04041c11018294440f1241c60b46006800b88007507200300d001540701c40c0c103000c000c2651402000c82800440d202c12400b80c46814080c0c0b419040501c1a8040005085048100342c030104440b0307008040a458507540c80e800c1c421207030281241001d01424650401060000c4203d850564890001d040b138500d00004003d6200d0401b5030341e82c410301c0040c140300400e020641c2e103480c3d4003c03c10107219464503103810180c205201002901074114484800003100003424440c046d4124084036071040342240d00801140c000100c0e10f06081c1d995001078024140c0620b000d8104074034413000c84c13200300c500d203040130a074480d01c030806524810611400c184031101c030b01c4417500d1840c20b0100080c0854019620011840d074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 941927724 1250 941926474 941926477
    0x90a0b1009240512030d0207060b1008090c010503090f0a060e0d020d0507060b1527010219110d0f0803040308061c02040509030d090c0e06040c0512040f06020a05 71
    0x800e00079602e00034890000e4003142c07641c2e0401041d8080300108451034003003080488200b00300305180a02080204100031000b0780300801e000c601c80e02d000640703a51041b00b440301980d048504201071001c441d0a0044003913000450b00d91002d4246041a43c90303942c04100b5007000324800d464911071145050180c02c000943c0c10080440360028211400150920000c99803103000103030510200e1410800704001ca295074000000406000c1c0c00b00e001d4148200e441c51807a80000700740d015403140d40080e904005041032052040030400d100401e181000450404c42e80c12070040000e2010140f040a00c0f62500c0e4410000140794100490100a501e1410160460307441214100c0c00259900000b8025160140c02404600d0050101200c02411a801d10005060290034500548014420344805120901039098000d100710080d1310348503e040c40c0b01d0303458800503140b60301c503a0410700501481903001003540c417048c04c29440c0c1c1d01c0b10348079421716180240010700060301840c000200004916000300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 941928974 1250 941927724 941927729
    0x3050105332e051e131205010219031401090e030a0e0f060304080a08220609050a02130905060108240408040503060a020c1c0f051806030906010303081006020d0503090a0b10 76
    0x34800c01c00d6084ca102015500c0c0f05000790a001c0400b0480c061001c22194400348450034071500005182c140b40030480802e08034044864000640c5504015181300b1140e2403850040c442c40c1d00c280030310102500540c0c1c6900804606400304200c440c1d100c003c03541c038054040d6408101402150b541c2c102801c01c80342561088041c00007040c40e03540494080d01c210b40d8410340001d001420301940c01441c2e43c801001d8001e0700800c0e90f0500c140c0307803000d0169a9100042c0b0404114001c005181c0c0001d00e0301609102059201d00341580007490b000c1c03c000316803966405003908036a100a8981d88a2400e100340d40619004075800d03100e81c0d020440c101a281c1d00400e6480d080004413040d07500c00300005079191403441d01c0d480003c2c02c0f200580320741a0003480940703042651003501120510f40c03180801e00c10742044030b40c00166400b9038010400d254000208035080900ea106404e038050400310042d544110407020a02041000000501c0480e030030700c6a640300c2d50740204584240d090804c0310102d541050b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 941930224 1250 941928974 941928997
    0x1e1b0806010e060d02120f0610080403020303130302031309020a1211031501021c030c030b0306040203120a030b0d151d0312041106070506100b0a080a05040c0f03050105332e05 77
    0x203055800000d2b0103000070601c156070641c01540340d41e07241c2440c8032250b8a4402c04506602c8144800d8370b0a011018001c006044004401600c406180c480103007243c0030440e40403501c529292104401315040d5088980c00a148041c41014492060040703241148481440b1020f071918004650041d078550440050101d0380e84e81482022051002c15480300d1094800035810f90041010200c001d403080701619081e030580c2400a02806044080382c08058075280483c0c9a081c10260340380da00b0001c0c45401850015015a8594404c1c0144d1995807072164140250603d15424005020031020410b450341800c40034203c50313102e503181d16109580301c00a8440c0c6178401c072400030114580840b0800c2e241281500d40c1e07174a031103846280d00400104400b800c150f8186c2c402c84004101c101d030135034141c0000d5101e2000040c26261441a40350300001d61521000e601d449503e030300d400c681000907112805441112400009414041120704161001c1c0011440140045e008031141d41c00c480a4007c42642c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 941931474 1250 941930224 941930239
    0x1005040807120b0709151d0a030b1b0306061e04030c0305010902040e061302210111030a180b0103021c060e030a08090c030703080d1e1b0806010e060d02120f06 70
    0x10b8010a94102c60b86008071a40800c1d0340311b100d0b04840c8100351080201180e81803805200e40700b1408a003040030545c0017500e0888041c42401001e0024440f564120504085058214201803000071f4261040d104200d07010307114480707441c000707241400c2200c001755480101c2030074242d5a40b80580c017901c1d10110a130320a41c941060000a42804038080c0d06c110140411302c8180b401e140d0800c46040c07405207600c83c2d0f41940320440704108500744114540300118500b00d503120b140c58000602a11008841d00021078200c0d01c00c800000c0e40300d500c0074107503581114207091040c80c114046003035400d4040041c080707900f0043c2514100b0400700041505518940d5040300c0b40c3d0b5151100380d030300c00c0400303555a0590f105410400100310310348080c02c9101400b100c0440c00a1900f6240344034402042c040c200c1866940b50844048684a003400d50500740307905282426107030840c0080c000b1000b4184040c00352800185617000d5160960483d0440c4400007101082c07410201500410074401701d4010740680d10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 941932724 1250 941931474 941931481
    0x1b0a02221107300905040c02030d020a02010213060f201906020306040b1c2a2301081603020a0203120907170307170a0306050315060301050106030c020a021005040807120b 75
    0x400b180a282007129242c3d400304c1858a0184002401c4c03024054045001c14440600c0721542d9000900414515078009612100f0301315042c0340c0d0380880e91126043c014008030203040c664018680f03c010380c0141026000d0105018403150510440e02262100e140c0c204d03501c48208000d6034050b5002d100141c5041103481d400d441230010304505504214541c0c0c038030710f20100016924040f40391201001c3c00550554104c00415109110001e030010140320106e100340078202904080403503c3c00e2000d19010340281401d00c071f100e0244c2c50440015042580015290b1400c600800448600c1c5000c0d0241c20441d1030301040c1c0d0782c1c42e14070380c1c0584809400000141e810090b40042600d0741d990b00103810082c1c0b8810341201600ba54400da410006154990500280c5a5001d120103281003031095071005040c50024200b6084540c141c001c40285451301c140040002d03400142d00035921780c10745c1c1803c000284c0d01829a840e024640c0325080030f12850b840491050194200b0700c0c00c207072244440080e19107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 941933974 1250 941932724 941932793
    0x50a0c0b040b010602160f03140c0901030f0512160209040201050f0f03010509010920210411130204060e060f190507050c03011e1505151b0a02221107 66
    0x1100388195000c0c5621f001050010840c00908c0b08c41c5507000504584060400c04c0114004d000240e0080d12140030b0181440c06024060104a0480021092940c0f500e40c14504e00400048030302e001031f0141e62104006821039000e2802c80d00d10f645010041501d580444400008a0b0702c24010140904110000050b4240990091008403580101c82402110310040301d50440d0700704900000c4814290b61420790105454074045015030302404044019241100522140142103140140c85510402081000b503500c030800d403408120840d241603a13030301711007081d10482c0201d400e241c00000719600300e800d0581e004001407200f5403048041d50f1540040d01c04140c01c82d10445200e4075901c28000f150030007410a5400500d8100e55160781c90196522040414403c800ca6803a50210550001e20501031900c1c800044d4070710343c400350003004c0741291755000c0ba0744401c6004292010300b030501c498104444564200000e42d0507000038044d111501c60400a8100003001400e5846603050414150440c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 941935224 1250 941933974 941934013
    0x51807080a050312070225030302161a07020d05060f09100545030901090506031003060e0307140715050c060103030e150d0203060925050a0c0b040b010602 68
    0x10b4004001e9400c0034950204502e080200501e40c03011806004480c42e000c80031400f0341e0b2030a40d16620340e51013850031898042e140000f455504d0098824801e010000b01080440c8402d116a0718810f035a2600e030a0f20200780c0c00c3c00b0300c240041190242c01c0400c418204103121451060100c0422070388582080743d01d16080759019942000444c0d0382d806400581d203020f000488108204d891122400182c8040c200d010441400007059650800103803401c4542c0d003d1b040c00b0241000315096441d6082001403d0100311841c40010a000c0c1c41d80d9200c81001420310603924801d801001c020125404903081d503865030000d01545181d030aa20074880300c005c3c450b0040d0b0380c1403603031702c1c00801c2243d086850540d522100c900340316a201c90b40585c018050780c3c1e540090552242409001350f100e041c03d40c104601418018400804081180c8200c1c4610840c4018400e418506050050761428080012980c2000e06c078000340c0714842844c107010400c85034502c1141201c1c000c0e401d5900a03c03c20460340c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 941936474 1250 941935224 941935243
    0x70f0f0804020d110618100216120c0509010807090f060302330a0306050a0501050c07030b04051501030f02031b490b0c0306150a1205180708 62
    0xd09000008005052071462034003500d0080007450310715850640040c0c0144e0201510a4100f0383c184501c440b141081e0300b8403090802140003400315a00d40b40c0c40e040700d01d05240700ba80140540c0e2503a28040c030215255450140801800e406a20f45e1070307404081d511112071140c508010b207880150890010907125034000d8a07401030081d0000c41c0d54450094840c00d02000c100701e01061104002c11015540d4000d15030420300f81c0f000306020303180008022150301c05900c00c0341808810007040c01181008a0134200b83c0342d20100a4000e501c2d00e0804a181c02410800100b407003445800210a1000c0d40a46d03110480c07086040707982c0781101c58004c500b0299101c200a401c005032800c00004502c000680ac043c000c00c8030b5400c42c0800800d0313001c0c07803000c480c0300a0180119410301880305002c04000541d0307018016425440c550f0504401050683e214900403142400d408034800c240e079445609110040303141a01c051009080c2801240c03441014003c46189511408200089041020689244 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 941937724 1250 941936474 941936477
    0x211b0f1b0206030f06150301090b03070905040c12080702030303133e010c020312090a0801150b0a0e031213060e030606190314010603064b14070f0f 65
    0x10f44e00c4500c03141c00f01003c007500ba1580601001d0070001c1000c814800745000b4001e8200124092171180300780360402c00035401640e440b6040c02d00304800702d007042135920100c54881340003124903c40d40c00d08442c54002c1020080d898080001444029207503011242d51f9180503003c10712200101411410516402c0f00c0c0345500f694017000c0594142c1d4600908e12560041070410b00c800d0711030307030340000c0c141005c0401d8407041d8540417030546002d0503c12081000b410000c1e0081220b80a114455004a07074103210710742c11040009507090322a40b141c0820060901701900310390400e00d2010240c1400c0e001811300320500c0ea1508000942c5c5840740744040310540000d800340c006922101c040c011402c5201030903100000c1c0501e0300000027190700800752070417140000002052421450900d06540021321800e0030352191200040c40c1ca142444011300d89444480c2c0012031200d0854004100c4070103c0e042481285400e03c102d9180b13200c4944c00e031040c0c03019034403503101c11404501030b074041152122400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 941938974 1250 941937724 941937727
    0x180708070f380d0605130207120c352d07030801050d050f1209090f0412030f0605030706110d03060b0d180b0a0e0c03060106211b0f1b0206 61
    0x155001802d01c010040c224801c800819101e803290041204035201d0348500654650000390030f820300c1294008048026454039002c0035910498850036040041d4580c10100c13003002c1c01404516400c400a44407540c440c0c0303800140c50303845031518860708000ca031030090b200081d2030045011540341107080340c5006078141c81e40f5810347d003450240840d0151a0004594500c038103480d901095000b007043e075110076480760780c4e55036070b000900c2441038504c0301070705050780d03410545d091000041e4400c00001c82c2c2031480c40e002800c1384003001700c0c2004e03140036417040342c140c01070340008580356600c400d00c4219201020304866000714003035000c41c119002da01c100303541070a05004803400700300300350000c0c4144284003020030540d07601926010174240050340c0c0a41c280303507184000f000861051080d80600e642c1100584a95898030704050000c545150300c1305a0307080c007200481c0c441c080c1c6622081c2503110b141e0304000c603001448405490a2000e100c0303100400e11004101c032280303011208030341c02c890303015141d02d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 941940224 1250 941938974 941939069
    0x11e020f0a05031905010b0423060f3609010e0112021203040312030e06071e1115070221030402030a020d050a0b0901060906051206180708070f 63
    0x4890300d0f0405003e00070b00c0540c0b100705000010041c0282406004541c20341d0703507150311b1707c2c40c000800f10041414010100c1a01001c002c2540ca09095448014103210314039500c4a10a5040006409003540b01705c25181000c801c0d1606400541d5032030070321209440e00055039072903401011801900744114810201440d400c0001801c11000b0039000c4d03032918048038242a200c0d50f070f130727000b50f10704c620600000307540c840515030030707140803c04550041254249003416078403074002c81100c8011400b16070148440010742e111100303020000340700405504400703820310381000140251100c9291040c4200b0281c04031046a212101008590289900038010014004c0075401e004002112610588450044801c0300002c1030900c440c4a114120b298000a0107a041c818400d0448840f82c02941c080c100b8400c4001030400006000760704120082d14402005e100350b501d0390314000d11070300040b070385004c1d250001034284150300020090b03074801404e54000442e02801c9211007031090a00441600115070300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 941941474 1250 941940224 941940227
    0x10608060424120206072001030f140a0b120a05010c0e03070b0307030c050d0f270206071b03080c010606020105010e1303081b0403030e040501090b1807051b011e020f0a 74
    0x200098034030103803070142014400d80720100c0740048805550200214520310001c00d42c9e06101c0e06d850140048010403100c01b021110f50a440d42c001c0032001041d54441c6910b0941c3e9600c0c481c4030a90b1014011503542d501c43e450860701805011101c0000f050506212540e5860b000c40e085059a8400e0300041c219941d006045010386900007400f02848400c1001c8100c140c1d483c0144103070701c0180c41003c507910014003180844889014210034a14110125140040e41c4040c1110040b0b90000222440445401044000041c99074002400322400150950343e103441900440222007660f002008039a80e21030882a0301c4100312000840d171002d06e241d11000038042c00700345410075054840d0000203101d020940d440c3c1e070700c0343d00143c0205400d40c45400385031816010389405000c0f0020148055010b240100b000b80e8901ca6004400c1400364002481051050003903a4806012091b5820b4401814940a0080003004481881c100641c070b0300c480341e882207001711084204414062450a07540040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 941942724 1250 941941474 941941499
    0xf150b031f030b0f07020d0206101a0c1e06070516060213180227012a0606030c0302090f0402011b0203070f0602070608180c01030b0f0306010608060424 67
    0x100509045070180000c804115005851031150401c0354030705403181000400a031810390a003030000210340c401010015818500b9001d001250700700c1403c0c5040d101e44140c6400c0c40c2c002c1310102e204902c60032180419642400c1c40c8666020340850035070781c00361602801101d042c1f0812013481d824a276088410b0340020502c0e4010640a00401402a040381d1620300307a60007404079510070310702c0720740200b014817080f0120751681c060040312462141c80e013101ea500103450702c807464441041011f4005401450b0000580000d04c686a201e102004200c3d01c0e403074655000d1000b400700303034007030240d49000800114243c109180210780584404411904811820106074180b01b0b040360140101d50000500c15605c400490190405030041c11140c1c0c20000000c03d1036100030041049820402e03100f02c004003001c04e12455641080c40c005c102c40c407141c004640c1a13103016134510340522030310b8000500940d1002e507050195100315001c1c0059080c0c0c075480f540304000000409188250420200035501106c1c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 941943974 1250 941942724 941942761
    0x2703120c0f050f2404171804060303020303220b0723030403020a0c080c010e100306080a0524040b04060b01030e10090c060e031e0f030c011a0a1d280f150b03 69
    0x20307105510b00c500b610215040c0d803020f07403044000d8de01c0070041c0010b138082400e0035101449040042d041e10304131521118014a0043c1423602807041060b2070180000d044504840f114020840c45566828036140081d520f03503c0301c01c00c0c0c03000c5003007182c042101c00f4080307200103001d10140d4542c1d07100c000341c41c2000016141000c80200b0b041e41da00e00024180c00c00d1000c080c0150086003d4424001c00282803072803101c8044111142031600c0341000700140180111980060f040240055541010801600242a0b00004404510075215a400c003500680c21640010384200c404130000c0da95504169224030740c0034141035154205100d5500c003d01040c000900c03c070030030b004803100c1000da200d00504560042500040594540b80d0004086800300c4864515000030b030361041c2c490389000500580c030420b0030b082e45403040c1100046000c40d071000b880711310301c50420364010b0805401703040c422000384025005003c0341424104503000020442900400300d03100f541c0000d148d5660001a0581c40c0e5039038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 941945224 1250 941943974 941943997
    0x60730031b0f05090d081b0712080c0a1509111e0603130f050304060e010206060d03200f0c0405060a03120f051201062703120c0f050f240417 62
    0x6204e45800c80e6643c500f01c0c0c1d059401050b41039030f100d00c10030100c0b20034841480100e4142d80300400800450880068002021380c0080100c0d407581d40a1981c1030030b0500b248009098400c04d83c0003800101e0b15075110041140c8100208010703807810030140400e800c89112151440d02c2d035840341c03022070b0400d907009682c0850181480d0741e1600890f80c4009020f1128030050301c95510200d024841d03103821005443d02600300740020020b030300e420b400141c070380c800300003004041141040030f440c03100b042003428003907944002c02528a100034040c030f415640c03000414118071483c20040840c00f1410941d040c0c0b41070300d8006604801d9a43d6044060b14840c8a581968040000802420303504c04104a5600e001c0c1026503128019081c18591080c1ca165105c0d018500f96101c0000c10000600918000442034607e42803611600305079061480442d900700d140034200740502c4c0381031800150041840240c2c84586900e20781d040604814a041d0004200c8000380203d000034200c080d140001c001070241d89404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 941946474 1250 941945224 941945227
    0x503030f0a0e06070320010b0a090902013605120601030b070903060c03060f051903170f070606060f02160e04080d14010e0a020a1409060730031b0f05 66
    0x18a010900f00e601a0340c007540050b04050020806000d101140d0311501c800d08000c5c003030700d072100d0001003000d0717560320482c0311a6a586e002613045900488070340101e07000c10098010b40c050700300c1140580300c05e000606510494007074008513003807612401013001c2c441500d00900c031582c01c540d1a01034194000e06054140304d5858400000500980a40408628990b9000c24858941a080b40c4900b0140d00414400d56090808040d030002103480c0004030b0b60072443c02c418445000700c061117548580c44000d40e042800140c090213000301038000c80b00321409660b40b192812580502280c80b05c0c0e403004ac13001c10f0341400100700981013403824003a4205014503d41883c003070038400e010084502c09004041504c0c1040e0040000413841c0a10307907444030540c50705500d001d554240081c10070703140b5107001030800c00214400304242c071920291011a544030300300e0076010b036854170390b0712080d2851510410701b1074a02c8400208144203004161180d4102580802c44206030041a290109a2480003081000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 941947724 1250 941946474 941946497
    0xf010c020a09090b01050402040b120c0d020d05091902090a0903090b0a1805101205040f050f0a061a09040305070609080a0f18121e05010507080601020609070503030f0a 74
    0x1e4041d8080010b0a4918002401c41c9a910307019606860580c04103201da1302c1880108580201d5008940e4a5000d83d01d10031203e40d100b070002d002c0c0c0d003d20801305586070b202041420345280c0c10750015000d03152040844003242c6140150341c509031520080250422009408510342c1113050304100d41091083c280001c159480303001d1007032960004070300200040c000c100a14440030071905914094801034855000b01d0741a9440904a03000e40000241c4a0b5030312000202405500b00e5428049684001075491100c40d140303069a44004000302a6402403900000741000400c0300480840080081e1400c90a0381e582d4074241c036580c00c00c5000341d4516440d0710002001840800c0107050f951202d8440804c40719a8140003400301e00898803050780d00d405000d0900801105807401c030340d42a40404804205414035000c111006011311000b0165820701c001d0007540d03504088024400d400c03e81c01c8503030035605c0d01d514582d608940e10a01e50540c00c200301d1203005020b00c10040480c44082c0c00c00d24003094 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 941948974 1250 941947724 941947729
    0x5040302100324030b090601030506151c050304150c15050a020d060321050c060115110706020618011404060506030312010b07020a0e070f0507030905101e021504020f010c02 76
    0x1e4032640b80c0c0d20042e00c0f1810300421070f0043c402a002003600c401850198116520a40d64100280c42801c40e103250040d203070210751324a4040c10150f194410074184520582c41c10305e81d80d400134052545403c4100c40d0f142c100c0c91140c0d156510301c58000c0c0740c0d25480030140040c3c4009003809002002144d33020401600c00c0401402908000d520a82c07043c24014140908108049501400042045820000049410800241c2a054492680b010307902c80084040503a4004001c0145a42c04d005d0038030001800741e00031814503c240c450b0320009426407003a980403400c0b01d001030001681499080c010902156040d0b12440e84550050f0449141942141c0043e14001c0f09070710000701e040c8006040d074214205502004021300d48151000010f01b071002d00642810520401d1104124020581000381840b62443c10b0040901500301103c0510380ca100410814201c0c506107403092003105049081840090f4610b6011740c032802c51007564642d5420001403001c0194410304100324100c905000d80d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 941950224 1250 941948974 941949011
    0x302100f0b04180c080a080301090507090e0a060501084f050a1703100e0a0f060b070210050301120b0903091810080706090506032a09041a01050403021003 68
    0x11000141c1070f1800316010301c0c1c8180203e40d07a40041e030054109a84942c0091418410307030381561950b807000310381591440300403a84006150f101c1030401d07500005000d50260213071310040503a00c081e40c9000059403441c00c8000040708e03005014104014001c2c00300403443c8444805143e0811000140302e4901001803885a181e243d0704003650075801480c1c09404025140c003100c00c2020401120390b0940c42c2044400c42a0169480341600180880000900113a01036000a0942424100c20024591546101308807038118110813030140b40c0400d10180500c0c02141907a0485030f0340d40c0010200d600950b181d40407002d000d4451009844180188207081d03580e100e081d0440805a9402686458111482107241c04039034040d00c03ca4215450502c00250701420060540e00c0950381c25640e0780740c1480e904804070005043d1030b40950140c0c0c3c03c50700309449d50014404d00d501200c042c41240e40d80c007800745220440e26490760120f2070402082006007030101284500c803110b801c00180c1c003001d107000c02219 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 941951474 1250 941950224 941950241
    0xd08030601030b10020c270112050a050a03080403271202220b150c071203200d170c092202070b0103201518190f050105070302100f0b04 60
    0x2d60440f003814030340740c01d01a034072446107e05800c151000807000d101c42440c00e00180280c240160a0700c4903501445410810000e8143c0d012040b940c80c2c4c5154240101800c44c01e69080340000c222041c0803039500c80700c5162590b000d0340c0c00900c10000d8a401c0d490444500080c4c801c82e001134800c0b28440180c00b0141c60010140e0800c0702c080b0324407006004105c8258400c429124481e401801800d0351390000145450a451210005224041141c01c0a40700c0081c01030020030249401e81401d5407064000c92900003000d1240ca405c08035483e12101e140308414202c400c2c00c040d05003446501004d00c0d00c4c0c900109041c0100000c02c07560062000c0e000305036404918107455403414a0010030802506092190300440303008100b030740003030407480000c080c0c0d00400003420302007102240002601095120042e61000004c0003408195102840b200303403208103214038621100c10322000103103540224125660f160f4542e0240c0794605d410000e0b04000e11340034102c44d5405640d001c103d000b41d202d601c1130307100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 941952724 1250 941951474 941951477
    0x317151c060f0608060108070b09040c0e040911010e01020708250e070518010302030f0703051005060406120b040c0203030a0e0102040905090109151107080906070203010c1106060607020d08030601030b10 89
    0x40c4141000d5484d89401c806a02100717607a800100704101411103070041d1841c48500300c1e0081030181003c1e50440f040009a40100e600a140c000041d00b08200d142190990b0003080e02d40b400070501c12401681c4844540c401d000643d0070105480700030301669218030302150b03183c00d252074004e40c4410342c0100b44a001c075150000b2034400135007120018003c1071403541c240c00900c0e040d0304e5880c2041c0381d581c81d4240604940c0038107854801045d40842c0701200c000280c0000f40200741c82d0b99960764014540702c44211141c40c05898042541c80504141c002d041c2003c80030780040d451a255040450020310440040d0f1105540c00d01c00420011a14080c00d4050320201001280d10031680c2003803d914011600e0310603085290042e45000d80c040c0c2000d03544080c1e08030600070303143e04103240443d50f42c0c0700790740009605528041040507447e03000054001203010000864000d541c3d100144242480340c200040c0d03020613018400000988420001d691281341807401081e010311a0340402c039452440b100d0790b030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 941953974 1250 941952724 941952731
    0x5240c0f0d180b03070f1d04050907030201030501051801030b0c0d1508011a10030209060708030f0415020906090409050a02030607031d1603030c032003070317151c060f 74
    0x3650b0404007000792000c2c0070f1040080f4610b04007107501411130054000d803102404001811441e072800661109038000070090000c1c0301500e4405a02a200c44160000701e0205e4a8600045801d0a00c1600352650003900c001c0080c3c03d9080d500c590b0012107008061304402441005080509040e41c002e41c5a20740d041040400071724141003440d42520004030705400f40010000024890790b641d1120352007058040d00700181e550840c5404101144100036000e0580000002030254007018050075611a034000c8071032600c001858600b40d070980c41400d280700e038002d0341070040490604e484e0b80071036030941c0b00300e0407920107840761b6010906210044828a0100307a540c00032150074041149094801815900500b1141840845000c0c1175a80c80c040981001241d0403580205809214141c07079519000d6110703420a0361180e9010b23503a80c000320080303000552402c04081c40d0400c41c141140699185031a00c040c0c054010306024010240c1800030482d1072504403180040741c0c8a01c66800050080710300031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 941955224 1250 941953974 941953997
    0x6090a0810330303080c0c0f060601180f062f01051012150203041a1005040c090e0a1e0c110606030a020d0303050705070c09090b0105240c0f0d 63
    0xa10100910b4681c103500c01c00e4039044108007000c1c401020240ca40c5030030102c2c200e894000000c805030140c05010303103031b81c4100204011440400510548160340903643c0d001003c4071201d2007031010596201e12300040030b1154041c40114083e90865001c00f40054103040d0340380c5800440d03840080d2444403084165920f00911580074240000c01c0c018148003001447e410441d55901030014890207009590541c1c040041000c028007481c081d0040c104015619a89050101059841803031070301c03502e0311035490048400c0240380550b250308201d9403403418140b01c0c0c0e510b00450310090100f410f020070000c0807030700c0e000c40d0862042c0b10720401d500e45960744182117001c23203810b940390440107408070b4840c0d80004185001a035075581c034901d4055141c540408d041c1c540f09020f4489000e030000c01403505469010218003101642c0c40900c03828045e20000c0071a90340c5400b4000c030100c00804100c01924000c02d40d401e00180c050061001030b203a0b0044031110101d01000c3c5040c50b0080648000007403070102c49 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 941956474 1250 941955224 941955251
    0xc050d06181a1305040809180106090e0f04020613030512070b0f0405060403110c09010b030a05240d050a0b0a050610030b010c0b0702240117010e0a0206090a0810 71
    0x10031100200c16a5002c020030010b1001a200506040030700b0503c0d601c640000302001200c5094032107a0b00f008c0c00402c1c002142e1001c8034122031b000d004400010b00c0c600c000041d03480d5800e400c00e000315a094000e06040c0c840ba000c0c00456808030725207003512a8404c42c00400134000300106200740340c13591540d07501c880c82d5245c40758907540060940c0204000e10428031000c91804141c458015515041025441c40b00c41c00e800c2c107082000b25000d6000b048080000f076200d841800031449507054001c1000b503640d80410b0740d030046000c1c50f0b00750580580c0683c000c030141020402e00240a00900c226444040b0603036580300824002c5038215003058480003403201d50300304400342c0c82c204941810306000c944200700000f00402c0c029000604a00448070110780102e00074040d050004105498090402c07003011004107031301d5802c1c0300d210038901c0401000400d4007018400d001032658500094121451a5001c02450360041161507900807165034001480210800c0008450300802c00c1c00b044c9039484400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 941957724 1250 941956474 941956481
    0x50601030b03030c0309061b0d030504151a240304050304060824130204080f010b0306060a061202251103100e0a03230d060e0901060602100c050d0618 66
    0x141a019910904c2411903042d004002d407078002d04250740309901c1c1e543c032500d840f07101e0032850220301441c000c001a80b4990b03685900042e00ca54080d162500d007105c09002220201d999000041c0511105480286034a00d0a02c080c8107514084103d102484001000326420562054600320380d00d50002508015a0340c001002581c000b02e10794040c10411b481008800c440000c581c2c14a01c2124201b208185494250303055030090400201192912295028514000d01a0003801071091203007100145081c0b600c103912505486442da644220a408030504401940100080700d0070bc50f000e840340d0b801c207456480140c00590064481d10741280c09001858103104649840240c00d41c2042d59180c00702000040005041e6850710b8000079229004c4841d004500002c440c805100600003410300402c1c44641050069921810b441910f644078010300e07500700c0b81c49101e50000350304050381c0418507286aa100700c403402c03142d042c16483c01889600150444a0317640000300781150400d04000b40c54418403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 941958974 1250 941957724 941957741
    0xa060f0e01081e07030f1a0708190c12020c01200318070303140d0617030d1a0a120f1a1501020a210507060606020a02130c0f2f0105060103 61
    0x10340980641c110f5500080c0c807120140805400345c46100560000c01018440300f00b0541840d100c002807034208034100071300c001e800351104030310000358140c4000c0d008001e10811a03000c56548a545101450305403050294000d08200122550303103602010b011406044882000044040540c2d50b07440d00d40d0f1603054001c0c9041403103a4075070101d0004d00010350441652407201700f440321301d00d407520780c101001000780c001da030400b03101c4030841c1c0c02c50215240c002015001d85e001c600414072040303803c1c00001001c25503001c0c005600007800c00b403c00c00d543c03c0001000c00c860042c072002030035107030039183c0f074401c1e0040e000c0304c0b01580c40401c1000803e2454414410480708248003410f05031007281c9400c041d4410303860740300540c1c150080801c0340e6540602e04481d16554480018440d0f2603440310083c3d10b94a101740181e004100c410f20031324031000d582c03041030a820203940701d0b618801d6003c1400ca603250010f01c07841c20b92001d440401541c005841100c50300c2e1052440010400e0f1912000040a650f605c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 941960224 1250 941958974 941959003
    0xa03090c0609050a060503270c0a060c150b0616050601060e3a05011a0f0a0803071101050c06040c0515070b0f0603120403200604030203150a060f0e0108 67
    0x30b18140b00e1a502d11031480201c03245850101d8403070b160f0008206103640c164803a01503462001c982c80181107404201140481002c035516040380740c0d00d00007600c2e018100321005010400030302c98ac03803960050ba4060302440c1d07005003181e070409000b100d021219500303e035010b5506500200c01000800d80c0304840d01103031002541c2e029400300342810089080104006880100d1141e1064203c01c04640c6449180b41e80d0050028410b00404006190a4036124040700e4061079401400820700d0500d044620708541c0305000840c5400c500d52161910320301c0101a03941084400c002e16021500c080103214021030044141342c2c00185003008101d010824103150003c101d1051006d0004030300c0790000d8503844188d0201c221403607925807000030300b44500d462140758840c030007190201c11b02c200400c01c400c00340c0d0b1b0507500b0415500c0003007c00440780601d1100035030643c0b02c40f0810101020340c041075a000032100c1000f25020380c5480b9100e07084007051704405010b920143c0104480d1030200001200140351 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 941961474 1250 941960224 941960237
    0x3060e0c070501110f0a0f02160914070e031c020115091a011404060c15150f050105040b0702010e04090803070201090605162f06010f060f080c2d0a03090c06 69
    0x2120f01c440903070103040106c4060012031161080d86900034803841c40040051208000901d442e03c9941c002400b20900307660000322a28006640e0b10700071701e8200f0502100400401c800d80c01c0725414181003810b8500003045540700c12120036488100703680100038107515080440c00d2940703260245104400c42d41858104001c1100c100e420030b00400880e42076485030714204d001000641020400603a40b011b49050080c42c0244051003076070900d80f000195402d41c405114050b9075040116420f015900a03e000004d0030008140158001e4506c141400c0018001041000c8903840c0c491a0350400c648560142c0d444902107801c01c4164400c4a0340104040d8409100d65280c0c1c100800c203d80e0343d030400c021035000050a107408009400c2c0070f280e9480303900c02c0b035549607103a01041104806500c45c3c140812032010000c14401e0040c0c201c02c0c0700c1e42c00b088003030b414400700041950000380f040d4040102c10740150100709101e24030100601d080c0e1090740300800c2901851605103c51176582d4440c40801c00d9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 941962724 1250 941961474 941961487
    0x18034c27021e060408030c03220503030417010e0109050f0c0a080a03031d06041b06030e1c090f0902030402151201122901030c09150504020a03060e0c07050111 70
    0x4500610100301d44501020300058082c0001103802e80c0700e1a007002c4a03510001c80c050150311000002003103c5050010419091000003400d100b81e0449801009e038560014041807148035a8640345007003020303002002103102c0d61030f00001421544a0b02c070688083d048005800100700e000c000c41000c030301d42903512019a5291040c180e446e4421004020101500e810460520000440c100b030b51041c140401d550321820146001c1e10381e1181c040311908842550100081c21901903c189010540c80201901c0030310641c010404d120b10728050005d00f8003240001c0442d40d200740842c43d50180460170001aa05c2c117142c0104140c0302c078800360a80d0407550070032814900c5d40c0300e00d1003e41100c48a4070001040506450100c0141d000c0f981c8581240003283e6240140342c820300c034030034102c0740540500990f0b15190200c8909549004200320300e0000164020461400d10342d00030b00d07005400d807900103860f9446040103190360300f0540f412041140e01144100c20321800b8400e5051f02030170100c41514140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 941963974 1250 941962724 941962729
    0x314060f070f020a060c0e21010b0d1a072f01060f0501020a11010c0807120e0402030601140c030c0313030311160e0402031c0518034c2702 61
    0x48503140005d01050702c400c3c0050341d0900442640226a20082905440742031030321018088051003000d00c0510360a000d01c21a42e802c0003000103403040d40207400140c1c0c411071000700090500020b4640300c10001c1c04101001258400c60032302c00c10281506040400c031401402d17030707400d5800c6500204031022400508000507a000682c0d11400c81d8052288003402240c2e500580d000900458054110000002d0500820001249040350300c0310315250040b68101500c00d00040f400100c1d600340c0480c040e001d40c0d00301070040d45c0150600e460340340c04030b07440c1c114000c13519811504000b43c00e14001d0000d901c28004c00d608400c0c0103255000c41001058503800c8010f44a02c21010f0384200c1000352401004030303056407006d20040d42100d800307461664441d44050070042840e0300c000101c44d20201d054600e0001132074003042b1040446086d0008003800784440d0151141c103009007505e440d2000785500045441d04c00c400b0808401d45003100c0005040c141074001c0f114030219880700d50000162882c0e240c0069 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 941965224 1250 941963974 941963983
    0x21060e07050a2706031212050c030703110c0114060a0608070e1309061e0b0a080309041d010515100215070f02030f0313020307050909100f060314060f070f02 69
    0x58802c020303090066111032842c95120001d0100e01c3c01c2c5107081400100500c20385001105441e00242d4030b032915000e1840741070b0200c8506540e002404002000460382c030b188250030180001c044c42c0a01480e0002c01e00aaa084504078407200180862542c1080803c0c039262840344002e10041c20050b08070b2074905001001c40c80e5030b41d186440b48400400b1140c0150b010f6016407000c42e4454000c00c0051000250302e4050282048012541d40c1840310600b80c43c203103000d0750407c480d0220015410032040030200401b82402c04182100882c4206004e882020b09014a9000300c00c21500c00f40d075003030010148505800080380c14010340d4804051540600c8280840c4c0c1e6016880d440c2440c4c1d802c0880104a08610480c03486200c045030210500c41d66007000f01c0c1290a040c42207040b1410940d4800902102d840115840350040e040307443c00030103000d02504880e0007441006400100c0b15125611080d400d070f1300b645c140c00960700110400c80c06400c0706545075040602410319000c04078a890009544 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 941966474 1250 941965224 941965229
    0x70f050304023001061505070b06061b070306020307202e020a091d01030803180304050a090c080a1104061d0405040f03020d03050105130207030921060e07050a 70
    0x14032115490f08070209030b404410303c03120000007115440520000c08680c080d00c444c0c043d0324020314100d50312510440c095005c455809500008403141540c800c01004482d0f04100f4600c0c100c2182c408000030381620611400018610501f80140c41c4c1c24881c01c01410400341030722076142c0d20f03507500018101080000d4a00c48c40d40b0450b840302001800048810400b9004981c0341c00c0060000c120300a41c1604900b0403400e541091900301ca181400e07404e4421412028070000c0c002c101c01f00701203450071000391a8000030002d1813003280e240c0750b603840c0490704c00805a40321904060340c60b00d402c1c01165105401e29000700c00e126090000c00591520b000d210300c140d02c100c5040c4080754041010004118004a00000008000300716900e098100030b01d0804080400310700600441502c038141c0384c001d00c10681038030345c058040d842009912039038400952240310140d0030f109400d00700103400829407682840d43e40f040c00c0b03880c804892900d07081041e51000d1861690681150390309120b0740c0c9900380c40b03104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 941967724 1250 941966474 941966479
    0x70602060c0f1b1204141518120c0d060b01030b04050106020706030f06120506090f030301180b0f100e0f030c090f2205031810120b18090604030206070f05030402 71
    0x1810107000781c3c3c0c10314045400075110b03841e49011500040303807110b4601c4680020015119800c842c001c070300f5801914880c207404d00b40c3e403c2501c01854050b061110000f100440941c044a12450044000038040d030400003044500c1c6840300c0c4410465641800f503810501426034044c40b0310b5052010194407400c590095208040d0b0f01c481800031008280c01c11401840030595a46042649007040c0740c87d40740466001004c0e20582e1028413591100004403070481c3c01400e0180908101101c1100c080d081c14080700d42c0c03107a1147c0036001503540e080d000c0c00e8480055111403882007000300501c000c5828540c0c2191098001c079003c84616224119820b50203000755010a469949403c41070107081c0300881d1002d440010044a1400c2080000080407540c80c1d00550041420701c100400c05122010b699500014a040003040c0c107116180c2c0140038080801480c81c0c0ca01019200c0740c08400304d0486110910394002004d1005154050000c56041311407031400d00c1d21000002e00c054200d1002800090 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 941968974 1250 941967724 941967757
    0x5090a031e0c0b04210521040308031003110a1d040602130e0703051006020a03200f03120a09021809010603170309151e1005060408070602060c0f 64
    0x44100865410741d000281d001405108803500c949106041d44c006028420152861907500300100303011103050000c1d154840001d111100c9003040c03002c02065900416241d2074001c0c0070100c00201150b0280d03101e6101200d03040701e11031030350070110101d5a0f864103283c0518030240b130601a00021103940c45405201c003840c020661168a00f4034000d02c11400c01d5104802950380100b8004200c0b040a03000b000305603404e0005854040303840900c24101d01c00c140259200d0340303844000078014030703107100350005000d290499040644023003424030320800861501500700061004403011204141908031030114804c00c110142d44d80400d07440c611088150307180d82640400580d411500350001c0e0040d55200002c480001710344012101150002d40d150307450350180c1c103984092005003c030207a10507203112100010401d02c0c07118855001c43e014000c462244a175020101d41c03501c580c0010001490400000d10350b092404400070b042200103460000800c2c401c01c2424480c1c0d510506807490200c013003002c070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 941970224 1250 941968974 941969003
    0xf220206040905010b03010320010f1d040501120201180b04170f03040b03061008060108151c0507030b01140604030204051e0f090d170f07021f02030a0b0105090a03 72
    0x240040c0070715844014101e0420307002042a6201e040618100c0340300d50155440601e90000340a551845280c0c0c25002410781c0c030200d40010301c1040e041055084048920403880c11410218040c1c4000b60403600481e21084284800c550788010041240c0409010846072507082540503035040c811880303070f4881401c103002e208030f00a4040c00354182841e50541142e5407036544e00c00c021a560812903e0700d201e0102c0041140005008088161013030205070b480001e160388030410440c154000200c415003143c24495410b148803200088034a40d0350250004204892a500d401c10904005800801c2c402c03903280c2d0307106280c1c5c0f01d0070196816a941164042100d59402c45032100040b8582260703500041040203000128030b500500c1d601411035602500c0e142da00316102a1f940045800c0001711103c03015000400303030030b4841e90f140d0b0400803903c180c410049034014900e6281030803005004c40240d0000601042281030f10030004800000e0070903038140038180c4001138000b85a4030020300a1071180300c51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 941971474 1250 941970224 941970229
    0x509070608060a08060108010f0f0c27030c081b15030105040917070f05010605060a1220070503031f060807141912062111010c0206040e0f0f2202 64
    0x800001c1d100800449405d5a51524020301030309000c0e00b152402071070075101c1401800d86006074040c4054544403400304612a10701c641e80018901305400782c502ca54a004000180001c105400804800c03008142c480014201c0c14144071202c40c55610071a841d030715800414001e002070b40e0450b9401c50b000a09403801c3d041c000031140d4608107144a0910000d07a0328104966404102c00b0103010724000c021480c0c6504c180880e80c4646400003000c24030004407039411290740d801419502c0b444403140300044c0568400456190010b10040b103941d0030100c00c100401c10060103907001068094601d400d0240303050006040030b580500a5000c007d80d21508614403d00c03c0b0483d403c100301c03414084c282041c0094020300e0748004000c5100c0841c2880000541c00004454030440c9485442c9900e00c565090360720b040c0c5a41c80c2064880c148844c01c02d00c81c02507640e21010300000d001e070031000823140c500b042015440c0880101068550b081c890207019450a80d07244220080e1440303101203c050145000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 941972724 1250 941971474 941971489
    0x30c0b150a080f01050a0507230c0106030309031509030f0804060902120d0e03010b0f09070c150504030e040908250204050c0c0f0a0f0b0c0c0604030e13050907060806 73
    0x55034101d030010074002002040001d4060041150300001c02154584c0b00c980015120142d92140c0004d5a12503040c1c0e8180c5039071910101c5d81c8161040e10320340041d000480707007550316075401075001c941c68001c10428401c0458040c060350981e0740e02046607500301d503000342008600c80051410040e89200140070029607500034864160000c0130f00c0e0240440041569852042c0d5020341d0000d5503168186180341814020340c0c050410041c1085240c01c61281841001b40000f4680020061a40e100d0000310f0202c090001080500b044007142d149498240940039000c01e568850103149022015000300308440203660203800c0c0740c034000050240800030101603514009003e548075180000707019150507404000c0501411241c107440c00750301c000c130b4201e071141c40c442c0000e010700c20b40c8140900011505680b15900904110881e41005a000401440c1c001c086504401080d04442c04e4456450f05003000d000070401f42c402404149004460541c580d1101c1c0b04004c180150007020070b10550350b445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 941973974 1250 941972724 941972761
    0x15090d05100c090b3612161a070206070309090e1509060420040b040f020406090b070b0c310e45102304110f030c100302040f0909030c0b 60
    0x41c0303000214030301c20004036207c2c0c1080c65031742404d1825400020f20080081b03102030202d07003054a81400d1280a800303020869022a404404119a182020a80000d20310680f1035640d04100241401d04081c5260b54600c10003038940e02c0c05a00c01420880000d0104a00d068841b40380518003001d100680e011501600c078645039503600a0805805007606002580608103d800d29601d0748039541d51000900803501c41c070350003d0b003c070301c0800005500d0302d4040002e04c642118503041140c001ca44041544190b894801c9881244442aa08100246041c480b40b5000b1607400c615014402d1803610001d860402082c0103a2402c145004400503511000e2060260350111815200049024041c0b5001801c041602008000220a0f601d12080c8600159403280d5072103565002c05c1e018540401640b00f450034031865061180344500c03e000c1d2600075801100030002c0d140541c4443c14881604ca44d81c0722500414542451b084601c800b0980c8800310081640e04102c00282a17100c040301c4210038507105 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 941975224 1250 941973974 941973979
    0x3603090303070803041a0f04031803080a0c030905060309250b370c060509121b07050301090203032715120f010515090d05100c090b36 59
    0xc00c0c5407042c0f0070500010340c403683c810703030401c14504081d9256402a40c401e8034010690b0201d0300c005000a40034001032910a400c0300c0d0099030096a0340d0701c00700194002452200003c1c80c0c10090400c2542001c0c01c0030207410119161030031803418844082e0f69050030f03104401107401d840c80014841101650340c0c1c0280640d408031036507c40c100181c2e2003803c025055040c107444800f440703405480402030300400b10500c1d1550703100e442518507283c1d4409000094071070040e6000d241043c000a0710044010300e0b00c0b03050305e4241c40c82e014810070a14248042c03984000d001e42d0500158200503940032044811001c40c416101d10b00c0c40844c0b4404024021011541c0d0b041f07119981c554031284500c0d40600401c100c11400c005040d42c072402c086142c25000c2c4521a0090001080c0d00000004000a4440c110003e000540ea0300f81a440300d51601241c2c102d281d800d26502c8400d00201517100780b0a038081c1aa850210307103050648a201c080700071200d01c6c544000d90742d2605411142d40030048070f14540c00300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 941976474 1250 941975224 941975227
    0xc0e0306150111012d1d0d171b03180708060a0b01112808070c08070e040305190309021206010e160c080d0e060f0106083603090303 58
    0x400c0300319829652941106001c6480c44a0325060310105020b0301c0c03003183c1342c1251164200e0490300b0b44d900b241d0320405501e1410341c8484110341d088031038485020303240c40005c6c014a0300401202026001425016001074a40202020403072a07500d28035402d845035085030302c45590b9a40d030604600002050120841842c000c500340020004800640359001d41da0844c001c01144400c07400640300c8024001821003c1d400110303400ca062551b9a00010b803043e01a40d210f800703180d00e03507114007103540461000c0701c81110001040c820a041040702030003414074000746400328181920094407a01030b00f90340030281465000130400780c078884d4200d00707202640909540c3c4444203030301107251511000d001d00080d0346001c00c0042c8050200000039264407480c0e898551503041c1540303030b082046d44000003140031251980350041c1c1d401b10400526114881c03a01d801880c2c1d5040c20307001001c690000e00a0448265820384200462400b401160325601c003c440301681038480301422030850090100c6903505000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 941977724 1250 941976474 941976481
    0x40302010e0f180a090302071212030b0103060f0306090c061103070b0405031303111003200d060e0f0a0f200a09030b01060c1112060105130612141c0e040c0e0306 71
    0x941041c0c510350310035001e541c001600d6400e49c5040c0e45501c030300a00810603141c211501540203500441e52a0018500460ba440c0c403640e04c801014503c0d8003c03140c130781e0780320004003d200d4810500005080c4c03c0c90325401116101030920394034010035601030284952100480c0c1005000c2086500700307a415030540310300507601d0910054401401444032300654664103001c4480c1e1192280b82022104151006500b070050451a4440e41007200c400b280c86035940000309080014981c417510072901603881c4d0025281001d065800d6910040340310038014100703403003c3c0281c811a0300300c4140c0b5400884d09a00c500d404a0300311010319039a40058003441e124800441e40503400040d401051703010f21000d20705254000144440c441c0c10810f2841c85803c010010301591503e025058001c4500b008042030403910350901c000e0039184043c003290f041c0a00b031000d90342d2841c00c1c07016481d000311035841401041090b080240940a010060314030842c1d075000069405401980204a1054058225511442c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 941978974 1250 941977724 941977741
    0x60609041211010c201606030b210a02030d05030c0a03020702010216080c0a0611192306060a090c020a030e0111150403020f0601080d0c020609030a031d06040302010e0f18 75
    0x400090007201c215050304441c00c2c10b10f40080c0c6c030940350408610400411b031500310100c001304461045a40d1250001c13194411a00040e0355124990441034080c0074001100d2041524001c80b01c2c848005001c01481000310352100c81e0151007000755241800f582d540e4840c40100d003481903c2d0507240b840f0107540c0012480341000a44201c07003a2050b5000156541c03600d20a95040520b10048841c643c094401d15010340840c103200d5442c00d10404110305001962090254001510204603026a00c014100001481c06014120017054100740070000c0304040c9800030748482c41c1d040094284020840154b1007039214001700c4058811580c140c80b800002c2c401000b01190301900c040d401032250f00034035080c003007010850a0494200000500c00440c1d800815070380d254030346005903806941400206040e403024411441110321941d64881c0e8611541b500c414103100b100310703860185500380f00a10050f6008243d403189140125004030498040400050840e482c07400d0044e50303824100e042c00841d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 941980224 1250 941978974 941978987
    0x1140409230a0203070501110703140313061806090e04030c020f040608030c0d050a0c11130c030516020616030e0a02040c0804050c01020d0806040e0709061503060503060609041211010c 81
    0xc6208038140c982086d0f0b02c3c070045500114691141900d90401c000400c0080d00c010040e2100c0031284040d81e0400c10000011162a05a6131080740811040140c041e884041131142002800340e0b030a100c2d268504210100c0a003003401000103060200c2182c10030300355507404078504029400240103100e2942c035600c46170b403250131058080ca050700c00e0381c00d8141e0450080c0d0a0f03404007a4295100d01d2500105c1d2680c50819030210f0101350404000805541034007103600800900b010b0a03100400e40c2d040402100104103182c03100e11045401102c28045c0030401041b40640d11465464003191841c181d1020900700610140001d601519121010010a800000f801d1185000c1c0342a203244102c0c6e44016a20f444203240000700103400c0000190842c07805600c915040d201c110210b55440361103008a8003103170b80300e400404284041d0500c4890f0254140a03282c05004141c000d0101400c00b034004c62080c46000d84003d103401d5180143e05c008500c0b411036150f260811038002d1101c518030f040e014060 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 941981474 1250 941980224 941980243
    0x30a030606080f06031f020c0105040606060e041e090201030b0a0608040201111507050307020f0f2505060306010e1305040804140d0506180a0b0f100e0114040923 71
    0x441d0202d000501c0b100c440c11420303031041c02c010340600111201807040307441001d040c414103244154203005c40014a5024071a2034455413042c10001800b904085015002003494502148610700b00401035a01c1c84c038404521a030050000310100310860380748010303006400307041c26468000820610000c0c1242d4025041400b0398000e8903103c9207145440e107003d13201d650741c50b40c80000507514004200322500c64001140c1c030802c0351040e00c42d804041710005092200d01000142c19602080f0f416000300f010301901a040403c081404400b5483d01c40441c83c01d000040049042c01580300f0709601d41c2e180c4000c035841c800c29540c000c110300d290a251550664016000391107050040800945003804d2180c0800d072126040001480306030340c0da0000400d002c03001032402000e400313000e00078070006075442031580c02200f00380100b84103807502e0410034804a13a5580860600c2c0d40b40001000003041d10503941400c01004d1700d01255190310740c00d00c10585410220040e03458508030703840c00100c00700410000780 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 941982724 1250 941981474 941981477
    0x1a04050702070e0a1b0f020a080f3010032604080f160609080a170904180210020c011407050c2101050a05060609041505060316081303052a030a030606 66
    0x1100061305c401141c0616210b100702d8003603440202c0420101d80c03c003010300b11030041c0c18841480c0000410410b51031540080b110100ca0611400c5450034160010210754801100c200d4040c0e0039145480301d0900d00c10301940391581c107441c550a406e24144181c100d40107080c0950407075040c1000b40c0c03003c0c0c1c0c1d030b1640307030742c1894040940d05d00118400d4030075120a01110071181c000c0c06c500351f46803036080c440350620180c0c8160083c01c100b511019151401842490042103030000b5205450740140030381085ca904428045410200225101c2c5c0c4e089525544014445507030b142e1180c4540c9480c2c2d2401090000d0725500060303203a034035420040c00c040004000318111009014680302c2105003410354074180e400350390105052002c2d00d40c43c182617114030103814001c01f8a8103110340e9040403e041c0e500c10b4425440d85036072081e9541402c2e401c1596240c200b083c940c1c8403c045100d58400030814003030341e094211903110030006100d0180403a0000c000f24180c2030181e82c0e0351114007601400802080c406c900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 941983974 1250 941982724 941982761
    0x7050304150215190507030906111e0406050417010e01090c092f1602060a0e1e0603040210110f0102040609060507020a2d23041a04050702070e0a 64
    0xf142d5159280540d0050705000788100241070501d81d00809004001c2c004001c02d0780c2c803022440407580300d00406210f00c225003510341d071f00c4142c010408044d089900700150081d10400c01080341d5a407003000ca40c1200c0820391688201c0d6070740c220450151200c9408400698281080c0c8028481403481e601c04860290000f04419071041c00c03800040c0c85e19030343c43c40c41c06804041c002200709e80d541c01055104800a0400030340c0e40140d0000d1805c3d0044aa004001807015904403917600349000d4138080c055074400651402400c0000144061000400090151007544901d102c154040c07040c0140300e080180650b60a8029001114000d410900c91240012915003001440c903000300c0484280d03a4000c3c00c01c0c07540d05c2c140100000e200620001380c2440044404104041003090800440034001c200348010001c0302d00030a10761403811948050b4030491400014048504510503c420158019100414603135a0804281d0509406030310646112510904104840c3e8161b40310075800d02007400a81c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 941985224 1250 941983974 941983993
    0x91403031602221d1b130e0f010221040b010b090402250209060d320d0203040503330919060204051513030b10050604081b150403140102070503041502 66
    0x2c4d0340c0c0c002c074072481860b042060145c1d4019061031041100300e17a0f4000b00214105541c42110703450b10500016641340d60b5030200f1401050030507450b4450422814140e11101424213440d8090307040d0042c450001302401c0080d030700242d0380350380d015110710601034001103440c00080f0b5840d01007141504d00c202d1082c05d0a03000103503603284c10a069404290000c0d5114103080c519404007030b4040a10b41d4001011340300c1c07405099080401c00440f038440b20303164042c648407460401030500e840b20000c070041e00c80d45c11124400410303003540b4040401070b00c00e90404800703446e544445410003448140204641e9114244071080c81602d400400c1154410707580540c59080c92070381ea030443e002e43c01c035030a10131070041c074200041070840481940045004c81b651f0a03141c2d4420001c1c00a40c0700c0d602ca003032960403041442c482082c201c501c5140183d801d40d200200c010401c481203555100e9400000c0c0b07460400c080b100c21942c425070503034296541c001c0440342e5441c0c0750380640c100310400f809660018490131115 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 941986474 1250 941985224 941985281
    0x30a02210f0402041d1207020d1b0603060e0f1618090e10091e030908030d050a0e07050312070312020412140d080703051510080709140303160222 64
    0x9940382c0c40c45c203a02070515021844140d10340760f4401c05060368460b0f9402201c8010a82c071100c4240720844c1841c41030840c03880d200018080d1005640b0001e007140f1070504101c0704a40f086181a40a801406000c00001c0903040c150383d000f10580182920800034035020400460640c010200890240c0c00c40d0840b400e407100040607a6440d0000074112081140000c0c084507000c0d00c140710451007420110840c0c0d448400c59032443c0c00a0700b82000e09600e82c0180300ba002060b02c10301407074490707041c05004c1321401d01d1302003541d4281c4551401c11641e4000343d0310003454480c41c416080c0354181c41d4255030765503175480d0030600b441c1e8814059440c0c145408080c00c907030400203064003103600c0350745600e010f50b51182c1c0160002d000c01420200800c402c44612807060341c40c0190105424142c7d1a200e485007403010b802000300b0340704c0d0491088868001456403556a00000742c40010f13130760215402102d6554030114011403c100801c180e000c070f14444c407103408803c07600301100000d020301d480c01b9040c20400300e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 941987724 1250 941986474 941986511
    0x40501090b04031a0c0c030c01091202060403020c190801020403050f0d21020906040302130e070f0807030b060a120803090c040b2d06070b040521030a02210f040204 72
    0x3c0209150101070050000c0640a1141603102c581c40c0d050508020356207500f2410b582c0300300070318181c1f6591070746000304200200400850060a520003000c02d4a081e0fa00a5a140f044e003855502c943c0340160140050000051680068684040259101c0759286800c40c1d445c121048600346174001d440c81550070600c204080c036201c18041ea020034800408410901c029030050411300d800038010440440540c40d408151604806402800545c12030801005424060702e81c21814030f815a100c4200700300c1c040050100140e07900880d1901407900c9900c0011f82d02c05030360303011200601c0101b80d4101808026009541704801508c1920134041d185c804000c1282c0311010200d91201c0b1001ca8584411107030342064120b10a0050300840741c035418400525950403030780040300c04000311000c0008200041c80703d6082c0000b00c030309a401c034007203801c0094658000109216401940456045280f40350b10148000c0481061421a483e0410303540c001100d01c400c03101603028501303285916210401845 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 941988974 1250 941987724 941987729
    0x7080a030c15020a050414030a230d1b020f030708370213050a090c08011d03030717040c030f060b010f021b040213080d210603020f09130b010605040501090b04 70
    0xa0b84c503442d00303040c504408041c5950f847c4040e014861080c01600080c039911400321144410920004c4d10b50361b0403049882d00c40c2c0890200304000c203d034003404840504409114680d9811118500f2030001940440d2500300e46522130003581c4a80000e00014000b10300e0b00c03510021020740b13440d800c1200512690185004190000c0d006051a10f20b03150700300b002d07844075401100b08900890740c500c26441d0340c400c0c00910340200149135992010041c20b101c00442a25132110031501540c158503040780d003e0401042c0007100d90f1520b0210300007404111580440d40003455014049546080d00f9041c920300030720b4092001d50109080002c840100f80c000540362143c2c820242088400d08440ca00344000ba401c41c442c075042001c0452000318029005101900c6e45040f6655207085083c05020038014500e28070f44608461490040d090015803a012400590b41000b41d85800460702ca00f012140d4500100001600d420710b10303800820f519900000400c2158002da1b502041291a0000c4030310038030452 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 941990224 1250 941988974 941988977
    0x150312170106080c0a0203160311010c1b0809130212011706040c06030e0111040e1e1509130818150f04150201061715100803030a0504020307080a030c15020a 69
    0xc00014038010705a41c0200300018179441030300d0900c00c2c03048155001000421040b404611441c030b80b955590f90911404540d44100c1ca000c2c4118001010a18203c640000c070141c04148001001c130110b450700b410424104001000c219030b12a40c108081088441c28000d142c0e130189400e582c41823002000910368002c0b5002000c40712110b1030050190b004040304154441d0365500c46450b20014003105c1d01900c01000c001a0a02e1076240118012690300e05000030b0540302c02608060219144020098685a4000381d0310032100381c80c1d0740040c1c00003202c4404010041000001c88081ca60811401d9805140d030aa070510400312070400314030300303a0081e1028204480401e00041028020b5604242403100340c1d800006201754554040025100801d064034481b90300c40321040e4080c03015264007944c0607000c000b6142c0014105030565489100c06043c0d015900e07100c81c0820107541d001d112440041405d83c0444082c0c0941d450702806100e5000c209951413074008800c003400303200c0e6008540759000c85 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 941991474 1250 941990224 941990237
    0x16080c01030603080a030e010b130504170a3608010e06070f020a02151306050c12040b0405060d0f0c0e01031d0706052d0d0e010b0f04090204150312170106 68
    0x720004400420031032868480e15921901d40d01c003107440d140ac1d544602100c06c00040b50710705d02400d003224441010800704813044410003a03055107540c8804e01e44d00e203034021080d045c504244581d8407602500001d4656120a110200024401805501c0410342e01044c0d01611b1140d03a40010075946a41c20711060400b40c1c001d80d104c2c1c4011325042e411131010031211255541007210058040000c4a040e81043e00440c03c0010b408007016400c00c05a4802030f58101c030740d407510703007070a01190380350180d4807419015000202e803a514240668024070108a2160002c0044001402c0010710301d21040b01c0c0c150100c0d16000240e94002c1c01d000c200d000140c070280007408444e252030703000c9401e5409560346c036020440f126003a41900035114140c0c2451207030301040384d0b00d0341e001030062001c03079002007010310445e0b2500004220300d1312007850a00c091041107800240c0141ca60011030082c2509400700301110740704110101c200050500020303003899481d0b50741048141c0e80491554003000a000301d4010640 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 941992724 1250 941991474 941991487
    0x30504090f1a04050105090a0e070e090d1b0305070b15040903080601090f14091e0103030305040c06170a021803030f0a1b0b0604092a2904030f020109050316080c0103060308 76
    0x8650007189c604010b010850340788684e00d203041c041b02441650b0b0154260013030b0300703840c0402c0d901548042e481141c50741140665081039401030040d100d82a001042034600600160310380301000b48a60721303500b0140003840b904805107802005410300b247c41c103021072084080428040c80310545c0c3c1d0241c910300700310790000740c18600420503d840d000303000343c510700007400f483c40f03214800303600d624000c511945001c1158245803900344c0850308941c010324100131522401c03008102c02d044c651a00456194001a650341800f01c1d01c80c070f04500505200c0d05448005405600319030180002c144d0003c0981d5050400020a49140d00b01c5031000707406080400d09202260b4180340580c00310002d503201d4001c049205c14180c00020201040313440071440343c05041000c0100c8035140a100860743c0c4480940e2044603500d40d03905495000d5404060590703000301410208590040c80f03008040d140040031100d582010710f01418003022503004165072401400402459940a4000d11043d681c1c410304841c240345 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 941993974 1250 941992724 941992741
    0x8090f010e1b0f060d0204090b15030711160b28140f0403200405091c0e130612030f0504030c06030b040605100203091e1804030504090f1a0405010509 66
    0x51402c00e00942c0f06250041d14403032551510000d00b02003040354805a1943d142041000c101c1c0c01c00f0910501036084500c5003c0c003690514102c03580304605041214107151000281850102808100c1a01055400740800c0508080003d03203e1580425074403010400c105220105504800380c0400c0803c1e110a04950f4640d41704c4090402c0d600881011810280d49031220300001e8540800d0720b01c0390b162250006041c1c10607002e62940300105c50f0041442091b440c04030710349043e188402c4000c01000006000459a4118402518000c01c510903c50140c58405144081c540c2d01c0d0203c010405030541d076810b541c01b640c10b582c11030782c20085172040680762401c20780240c031b024042076a0046c1c2e18000440c031541c41400726004001540d004684404034482808801d0103d02030740603c5416100390380c0c81640d2031101b031403178000000111080c140c98500d01907540b8011780d040300c403000e400c2100006441006a2080600040c00320051920b181c02e5010300003202c4080c010140c1003110380c000a140ad8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 941995224 1250 941993974 941994013
    0x120c150e0c2403180a03080f100312032a090f08010c020607051b0105040c18050112060b01090e04030203030a060605090a0902090f27090f0a021903080a08090f010e 72
    0x130b012507089801d450460440c505016103400e04901041e401000d00c041e417100300c0c1c96030b40d015541c0075943c0306042c110b0f20350701069040c2d401d880c4201500d8070480002e114200c9819010180b242d216500102c10707920000c0c081400c58020b010140500060007d55184c0c14000c21042d444650013900c07003900d60070b40c2114181d00062a40c0c09000f0703200c945200d050300c01d114082c4128003681900103014204040941c0d80310001623240c0910f8201070040c8040c488a440c0c0703801d1240d000f280054140c602c0c0700180d070256019400181210440030400041c542c0100042d841840f8400c0700f002003540701c8805446d2800341d8050a50400c0c660142071180145a0b40144110000101880aa401c0e1640025040c0040c04184140e9100901c2e12081105a01d103590360001d400b030019044a0a20b4403d080d511114030340064492001d0152000c510807103080c156015540210b0210b584464a080c050004101528510b00c41c0c461081020142c0d181032064001d028050300203403940407070030b80c403d8044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 941996474 1250 941995224 941995231
    0x50d1706100e0d1208090111030a0c0318140118050a03110f030a030905010b0111030a050d290a290f0906070c0f05030613120c150e0c2403 61
    0x1d000c412401c41401e50303682807100718100c1c42080b80c07400e48504413100800b10500500788100c0381e0b0500070540183c0b031955064940c081102c910000c1d10400d900401c4010f080054483e0404140c8980c85600340884d4070701e081c0180c82240000d10040c1c03280300c03010010b0b000e2074401406a800031184c3c40002803040080880b811901412100406a2040c6050441c0d00114004011075601c51220007004001c0c010100014801d082402e206c2c0b0b01d0404003900e030b11841c5200c41c00c210001402038a01d003c580c0c403d00c0110485c6654591501140300c0e1012040c1402d420750b484ac0380c50300400910400041900d41e1050204110003510f00f58911680311a90854040d1a46414003803200d600c0702e40300c0c1c6010341207c60280a030007100c1403070141c1421203015550070090194110004000061a00003020144903501c00003011002100501c01c41c1c2000a00740e00030071410110b0034010f10031000350002204094044d0503608203c4503d0100a00c6c1c20f804075103070028082000d101100c1da0041c001841d030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 941997724 1250 941996474 941996477
    0xf0e041202011e09050c030109030503060d2621010302060a050a0201021e03010f080f030a0f1206180b06090d03030c020a0c0f0f0e270102070b1003050d170610 70
    0xb9100004501015110f10450300311000558503000386050003010419041c04203003d4000700440301d0349840c0202035110050100e80100030b003074803040400c5000e50301000e02c1044d0505641031568140c050b210f165021041c0043e10903071340035031543d00300300350420213040f01e034001c00c0b582c41c2c045112415a52500411010825554240504001c01d00e484030352540c510b040b042002d40d41e60400e00303000c09508640d00b042c0c0b100c0e4008241e840c000740e000030484080c0c4940d41002004c0c41e10302d88044811014040c55040050309000c030024201c03d65070801c0f08a82e05080091000061000502c441070042c0409541c0c01030481c001200400c4c00707503010501084052058400d007968548031100d50074160340c0b0070703446000644070802c60740c141150782c0e37005403070100881c42d17050410708509806031106096850701740740e010f0921b9902160950403a90142c0e401400c048a07450035030050011815144001d0703806004400303904078840d12641e80c0300c034420a400e046800c7d54440c0c00c10b0240d41e081003550b500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 941998974 1250 941997724 941997731
    0x406030501140d111c0b01060f1106040b131b030201021c020a0b040606030b01080309030106090c1e0203040f08031201150903060e0c0d0b041b060f030b060f070803010905010f0e04120201 82
    0x202e21617000a25016818040c99410700b195140a80081c62006010290740410a00c0020019040d07404600309400c150024246101520703070b034001820111401c0001010001c4001d8a00450340d4100d860f070302241d000740c081e211100d0718070703a0114020045410120041c0c001d56030150020706040c80c5160858058130b0002400c44e1030781d40c2c400081c4800c0c3c00982507940b01080100c2c40385002d000c2c40000c0c00c2c18071002d12890701d0740340300070380040900d151056481210362920362941d4420029200280301081c01030500b0fa81e9000c44980303940c0a46c003212a2001c0c01310021520300300034809048800d0003952182900c0d440c0d512081c000389104541d40840d4098201b4251030382e47d80c034100000142c081c150b42220b5003004c0ca8028a844041244800000f0403a40d04005042d001100f41452120341e0501041150500780010f1081c03003031414510022030042018424468240003840c141c0b48140000c000e607988560070b4141a00051156000c03022001c000640002d0000c2c9009040942034000030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 942000224 1250 941998974 941998999
    0x20f04090905010b0d2d020d021002010905060c13170a2006071104050a05150d0303090c0e041e080406050c0c0d050d0e0904020a0e040312020703050406030501140d11 73
    0x607400c0c06501d03105903444070194010786c5010040c1c80e8000f00c140f10781c4000700441601980400c0b42e074040200064810302480c02407440850003074014000d0700e90b01c001900c020b0320b0018146030003034100e000d18000d810390f14040401c036144c5582e4004400c3c401d00c001010040d00c3d568485522400004000d009001a00349800903a00e403030740a4520144200700f0200356024803070501c012500002c0080e04064240024450110303161070400c0642102540c0c018690b9500d401c3c281d000d44000c0d84000d0461024810000d24043e00500460080d0300c140c801c6520795000640781c8c0680d1825100240c0350401c00c0104202250041c00104084007030380307083e01e4401e4448000108041c100b0b440981e2039402014401d48102d501c0703004040b02c09001c648034200390406401181010200303001705000009200049000c2c58001c5060030b091040c41c40080d9070320441d81c0b60040c0660410700c64403020900b4a800403441441c4000807007080c1c40040c20302d44d44c00a05417203d0030404011500550407554803000e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 942001474 1250 942000224 942000229
    0x314120c0a170c0d02071d100303180b07080d0506180a1a030613050708011a0405040305040302100c0c06050405031b12161a040b1801020309130c080a020f04090905010b 74
    0x4607035131a0054002d0081179142c210311200c1082c250117581c8400c1402403c00000540c640003000c280c1303400d840c0c411624128185034950500c020340182d4048100440c41c2c2d81040802c00c0284040d1990000c14800368841c1828040c542034604000e40d143d4801d84005038a00c2141c1d4001d0700729004846104003176070485404641000b10607100303041d001501c9001c24051080411003c0d0040c1000402000824100d14030700d002051010000351107039444034003240034180b003141518051a0000d160b4440301c1c00c4050090140a05074104456a0b40e50850024003a070061054908494014014202000801071407444001030650210b50100802c104a499503208006000112500038040395025003041c89003940c0309108020500d40010070402480021400d01c00e90341c5181008001c0c2d082200603100507421401401090b0b40c02140705078001c030300b880140d00895102c40e41a03c8002c516190131400b20305a01c03071100300c122600400c210401c490440d580c456038035240648000100401c06d41c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 942002724 1250 942001474 942001483
    0xf0c21060903120e06061e010c08090d080a080a060e0403080a0209220f1406010e12010207020607060603140f072918090108150714090a0314120c0a170c 67
    0x40805455001104016003400e28403045144095011a503407411f04084000800c0d89000b00d100800b001c5020810301c4841d10b421b0610b44100c0d40c88105c00341c036868003610007807401c02c0896070b03c500c1c5410300000090031038144d203119001c0c58150ba1071840d29912405410060f41c407100715550000a0740d607e129220140c1200751000b00c0740c0c0100441c0241125413202c00b40c0340e000802d050840085030034040c860780c00169550001d2400d40383c1c0321100c0c503c02aa280203014511b00a904890006070840070007400342c0c064020399107d282c422120322921030100b595404e0244410f1441c0c0e000c1c2e0000c1c84034542da140c4140040e1443c414201042010243c400706903000071440d801c0c50903283c0d00d40e05191800d4003085000d03140103c01031460070300070132558901030f0000e0908414040401c45000d0140e004a086801802026010100407a07407407900b60040640840c089030b072805510480794404180300216000180c0351002084901c02c0ba884501c01420f03d620542c140f04010071086010000c1400f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 942003974 1250 942002724 942002741
    0x2208071a0c060f070306090b0303070b070915090302040509031204020f0d060f0204030606080f1507030e0307051c1b0206160506070903051c051602040f090f0c2106090312 75
    0x4039040104d00f081e82014084d584542c0001d8000384c08c0280300c164070348001080ea14a55084a16062241c458a40c1540c00d004190017404840740d00314041c41d4802d8002e0241411030b032003034804111940c2c0f8201c01da41c403805182124400342e0a0701c1c000c6030240c07415400398404050000d040c0c04030704606540d400c0c100c5054a200300300c40b60300441e00304140105481860000c01c20f28000c0c141881c0e414912540350a81c00d03583d50300c01449540818183c074802d40c485c51040da403003421280d5030010741c01e00310781d1132078043c11070022032581d40d82e07034803445100301c1049010454161500300c5020b0203908014a0f81c00601c50050103625214200700415801c202513800356003141c030350540a03411403d00c10304280258074210400b0340206500700030765138054110381701200d840100480440c2e19100007400350205419400301c01d81805511018007403032458040a1921030985003580c103940e043d070303041c00c01c05c560036100c00155060301e0240072032042d8203c00f5078a8400c1c81c1042c0b44007501c001c20b00c00c039040007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 942005224 1250 942003974 942003991
    0x20a06090507270b060f03070f03090b0702010e1006141e0405010e190b090f100b03090d2c130b04090b071101090209130c0f09022208071a0c06 63
    0x1007403202d841e2101c3e20421329140002e6550502c1c18042502c0100507120103040001080f1088100c81c240901c00d03030064100c1540a0003401076400d12000090280c50a403150100c540106d103c0800031500c13512a1004481c2004811000d4613504420800c42c1e440fa80c58101500007005161409551544642e07400303040c450008203041d0a1901c1030681e050055a642d01c085403504607213151903511811081d40c0148034881138a40c0b603580240c0586520116804002004804000d00c4004a4041420441e08580e80d85008250040d0341181c440748400744090000104801c08110350307824200f03810304500d9241d100200f501e40e00a400f20b0115170354071740281c444180c46010311000584c0182142503402c007000003406844241d40005201c0200070f42513010310801c1c0e51600e010002883c0b410302c01402184981e00d86140d6a15041002c1d500c0403890702009024800c1c090005203020000500b940c040707070000c011041c241f40740b01c280800301414040e180402405144618203041003202d1060184 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 942006474 1250 942005224 942005279
    0xc0815010f1206260f0a02011403040f02031c170f01060e010507080d060311122a0901120308090a082d13030b0603010b010e36061906020a06090507 65
    0x55021820048000c01742007880e041000d18101607a8400d0801c1745c03030121010701c00c0e900e032114580b05d805070141c04802501401101c103c400c03410301a0305210604452911406000c1032070101c403400c5944102ca00c41149544500103001180c400c1040136500601810040d240a4141d200c0c02c1980c1c00917603003078115544401c4140100104503070002c1d80a02e042c1c60700c110320b4050300c03c0542c542da45c04031440d000d040e4011502c0840c42d21041d40314001040a0101e041c1540c441002507240980c2190680c08282000045101980002500f0b1a0103400c4810141440c103010403007921044004043c0c482c20b64245840548903001400806810b06100d120040c00d504e54642120024002400f051107a4035004001c010350b6005280389552078412144055410141100d88404c0403001d0101c071103094100004889400c043c500103030045208440018010280707060406640c0c4050084000503080070901800096084d0411811a4072800607118095260a4101945a2182d10002c0030701d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 942007724 1250 942006474 942006539
    0xd0206071407122103020711151c090c06112e020c1509010b0303090607080403060203070207080111030709140a082a06031e090a06020d0c0815010f1206 67
    0x72004c15821100c10581002e40c10314040381c80e103021150312128024041e0400d047d56010789110901110243c50384150218610400d046c518002007903038810465a21805c1240403d600e8042c50032000c1e40035000c1e008200c04c4080c6a41e102c0000d00c1c0003006041c803419a003130100e456180e40050074047d0380d004028020318444007054850000080d01360311450b40341501ca000c00b5140801203c26011017941c580d80e50381800d1518190b14440c69001038801c43c13001c001d0020269000c1030707500c02ca598080080c08804041e81d04c4160502c425200d0300045a6281010008601c050045a02c00e280040000c0152543c40850505000a4019a1b00380b030f0000c500c95040c80a213580304140c1e0410664241c4d046242c415902541005d403e45610428040035000a50740c910030050442c0391980040c0c29500d9844000481c4040c01c02c405000000c0b8a02d2000506802d1b1500d020306502203050307603028204196a2026140d400c80f001064031240e454080104404020002400d0201c601080c800214134 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 942008974 1250 942007724 942007763
    0x1f050712050a0e01080c0d11090d080306090f011206050604020c010603050c13050f072003040311121f020a030207050a050a230c040f09022d0d020607140712 69
    0xa40c0109804c4c144038070401800303008506e071803d907004c142c2c1c040310000720810b81020340c6281c5e00580ca00590311800180c96081040144000346009001c251200e400f0340d01c1c3d002c26490303842d000b40140b20a0441e200326100c0400c2540d001180c0118024200500c0d25204590250944450341c0007a10b01c0e07449000c0404281c2400070000c00e540040020820250501c0a030301c183d501c130040e140c40c0800211000c4400c80c40316180050054000c203004980d40d85130303030b458000d03002031144002074418189442e0341654054041882c400000d004000d0b01501080703498024000d400c5803148c4800c040d402c0c8441d4001850800040080034015002000000310620313003c5140c610240002d004140c00a514030701d0703c500090410103004c021980070415544248642d4001d000d0020b000c0e5020382c0440511542c02c0c40d0342e040c024048400701401a2142040702404542c030036180c002904100200541404038030440d040401e4107100d1401d5540c1c25941c1e00e00d40e259844081801c1e556000390710204450781 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 942010224 1250 942008974 942008987
    0xd06060f02010207030207230a06031505060924190203030103050f0307021c03180e150121050402061204140d0201110304021e09010914060604051f050712050a 70
    0xc21951009618120456400948500203032180782c2500c0d0751001c0c80d07114101e00b101303034003258000a012400416034620004014241407002e01d000668200d00110702801c0141c201c0b540d020024212003010440c0d501e04488131450300d0405408101c0902103d800403002079401002c6180c140c0c0110b0312541541031240c100514402114a550301c01c102c0e40b00181c60b0240c4042d20b112140301003202182e9507040c1900c50300344400001d81616880ca90100360b40b00a2030545004000c81800070910705440001521020416020499450049107607880d20030201d41100d580f242c409002c0c1810200415240301e2824401d030f03021141107010703080c031403c0918204814030345400184002e10040d22220807010340c5100240029003d245400340c140d008515004005034110000b801f00c030069a51252010300921007481c0342d5040d9100f200214480e441c0404c1034805a8000400d0901c0015545814401c0d0008240820062000600c1407030b02040235243c0300c40300c0c1540f07a01c441d81d55040403040104032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 942011474 1250 942010224 942010247
    0x24b0f01110c0c01051809100e06041406130603080408070303140f03060f040b15030a060b091c03120218042a0806030109050f0f0606090c0906030606040302060d0606 73
    0x1440e03014400907a80203030014058103d10020308015507118540f5a14a0b80c4103605007925030001412010303c2480d0b0f044031040e80c00c41d0724242025455444d00e8080100352024090701c00c000d80a04e0000c02c0c2c8a1800e8501d04046441e00380c40000c10325501c1c1d03101641504198008401342d00142d00410900d43c10907400e81444030a04245072404400d4282461540000b0f88102c0c0a60884000007620380c6956104400b1a480101042d01100c2980b8824000da03004540320441241443c400152407802e803803d131100800c0080841180c83d44035803502a40103000341c811340030829246138070a503400302da10080c0302d40701c000c80002c5000360b0305400340b03c150b540340340f500f8844225400350040034003e440b09100c8403c009103001d200c2910345000003030151880c00310290184c06007241003071940b400000c0700d5225034200004d548807075455008004d05400d00300c0f0403101c250810016080d261520500560748118000c0c142c03810192039801240840d0010b0500c1e03030880340e0351328082c081c281c2c104560811 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 942012724 1250 942011474 942011501
    0x1c0b04060507140a090603020306041409011e0c0914010c14070f1202060a03050c04051e10020a020a030b0a110c030d200d0906061502100c024b0f01 65
    0x1400b108100c001702081e20b00d1090303900301540072020410300d586a030410144a015003608000c0303420201c650b580249020b00c01c400340a010310700380d81140000c40c0190a12100705840e2107800520708900c02003248001c00405041060b100c51090004a42054050520404500601840c0e00345142e00d40401c0307040c2c00400303581002c003036007000580e6800e01710340b00c044d01e030314020450780c0f100654010a400340ea0000c5522071400a100c60f4640901c000204030704404503008540c980c8000b00c16a1542207111029410071a1408180040746041821540182840b030000400304441c00c100705c9075800c0022a11b58036080024004001040c0f4003c04000c1000070b4841141d05000309911140744c8920080700320401d0304c602c1c181c4180a080e0b0701c075000404001c00c100072400181c1070020349406000d805520407620300004214094400100c0051740c400c00d45050034840b0500e40d4000e6019850010094070800035440004140c030b0f031100c3ca2055240c1c510085c20401d0701c0d07c405600f5250050540003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 942013974 1250 942012724 942012727
    0x30b01140303190c0c0f1d011212050c100c0f020105390f160b010b070b13051f05070e030a0503220e280b0d021c0b0406050714 56
    0x20500e00000c140026160010301340700a0f00041442c1455141d0290f90000d1103003440d943c000107406140360900c00b001c008000d410006030380c950b800307281c0c00f00408401070080c03841c0c1c10221221501a4000b003103840100d600321185803d91078400340a480d50b0380344400002e040c040e120616542c090150980080c18006001190400681c3d01013543c0c00b84240450f4040000c184151300c002c4000031030701c40c818510650f036a580d5060b0041008807242c02c004a56103044e090002039410b01c98400d9822303196011102c22070039207501c060b800094540d400151b41900503030001c01008101c0320214a20b1f2000c00c2c01c04515072526800180075415102010350017608080300860002e0300120403206021f000d0034142c10780d650400d152401c1c01c0c00700c1d04600008180c442c2807100f030f17804401e651070340c0078804244201d40342a44075101040e25044004103401c506501d00e02001850070510056001d20300d658108400041c2c1d40b07410a4140707040d14107035201275480b01400405a808015003150304010680075 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 942015224 1250 942013974 942013987
    0x3080301060c062f0f0c2a0109080a020f0a0905040f060f0b13021b0d02100f06051e0310020a080f010611030d0e010605040906020c01062106020c0f030301030b01140303 74
    0x10181304030a400d0a0206010000d690800054294166400c245c5604100c8001c000314440c404140382484803480702c204030748096240c1943c800c120640030769090300040d007102e0350540d084c06440d061699003607510140e40c00c4040391f83d08891040c1ca00c0fa0340106a03050300000503040102c1128000142c0050450411010342840d80ba8403141c101c1c80c1c9101030005940f0006103403883e460740241ca10256203801031400188040d940080c82c0118103006000412190701003110420854201d4451280c1214450788450b11035090361803004c03408000642507868032044d508104040340d221900407008205080c041c8045030100a0115001d0300a80c00c25200c100c01c0f0a108a580340a1001c0100c041502d400001d08002400c4d0800b0004000280091003091000d24151000e500b240100e12007135844e0280020381528990b2500b800d20a1406c51100c0220698a40e03030060f41c070040000105218010310003a200404100030340c029402000d40305215414181400004a541140707a0300c280e000b030154 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 942016474 1250 942015224 942015281
    0x504080712020a14011b0e0301020904061212030b090a0c0908070902070b010905010305030708070f1205030103060f110a0f020a08030406060815090d08150d0303150b180402031003080301060c06 85
    0x5405402140c7d0a20780214180240064060710800301c210740c11508040700000ca01ba50000481105445103010446401e601c00040b41100c0c0d0520840380d00940b048081840321880d03500c100c004004a01e0006112621059290f1812009500110216a0005140c01071000030f1003490f000d0070001c0b00912455266881b81d580c0c9004002000e00070440c001811001c02c40e101c10b101c1845035006011b0720214007880005411900248401e580841c207003660b040482d003080c89802d480321406424242080e414030002c554042e048001c020962180b83c038a140440c0c020400b0b1032146120b2000426070764104000d05003041200d035010084040c07482d091003000880400c0c8038480c070250349880c0240e9504d4000c00e88050a0140c4030035000410094a84141035064201d124510002440020180c3d9101c01001c0b05109400600010034400895160582b1b0079400035034104101b2640c8044507602ca0f10f0b82e00700c0358402c1c4d001c6008207001ca44c20000f0001103020340605018913400120301007541c07851 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 942017724 1250 942016474 942016511
    0x3060d03031d0706080708010e04050706031104080631200f06070b0916030b152101020901020709050c0a1101110c06040c09110d0504080712020a1401 66
    0x140202415121000445014a02000b01180c0b8500c00c044400c016903071039000e805c0b41415101100020081d070300100c0d01a0203e070410b40180c1d884002020800c1c44c04404074000c28540c020450400000c0100080c042420440a8003c10540750042c51004440e810958800207036070300000c1c0b1102c540041c3d40801d1070b500072000807621036200030003080003140001d001641d07090840e5a101d807010594000b0305c0025044144549010400c0303440030240c0b054543e0840183d8440102001907640005400c281102c030030390700151024003045621041030403503941c1c3c44031000c290307600c81e980855052203030f6904000c0c02d8001d06801608203c941480380010b0494450340b0400c0060080e2100c1203903040c00d0950111480a03140c003040c3d5158003d0502c030070344a100c00e80f020341303000c50603040c0810848020721032244801e4025450742c3ca0866980381030400b60038000c000b511880c034107101000114180c00140d0603522110380c0138012080c0c191400b030118181e80c08042c045a0324112050300208201c03407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 942018974 1250 942017724 942017749
    0xd080c0901090f060c12020648070302010b090c180114030108030a030f27030e0a06081609151803050d0504030201080c0304170c160b0406020c0301020306 68
    0x1500103a86404000040c0c408180583c00340c0b400d40b030810320020f6241da1000703160410612030340214282c081c003143c0c200c0e84d42c4015a102403070000010100d031a0101d0003100300d802450443c1c3c030343d54801d102c85c220700307442c41c001d40c2c0c41c540301d080c00a81001099428400d00340141c00c1220340d01c0c098200085220401c0c0a000c03084007900c03420119071304050f8000c04c405000801e406a04c10740d2982c50f0b0701c883e07860f908500007202c003080c240040c0055164240c0210160320300c070403007040d18000c1024140c0346200c030701d0441038051121200d10990640c8564500078007410f05519200c1e03244c28148041020941c005c00190108a032804040c0708150b415100c2c01009a0586001d43e03484c841210b00c0002c0d0045a840209180300b04125891841e4120010f40200c0317000f621071aa265841c410320464602c42214000d2180d4198514141c01d1070060000d4400c00614804440c1d03184030642c050303e0319110b540c11901200001007006c04c10264100301c020059002a802076003035050007408038443c0c20158 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 942020224 1250 942018974 942018991
    0x9051009060b130603030c121704051b0d110607020a180c2a060c12090c0e01050d0f02060729040b01090905100c0e060a0f031a030d0806032d06090d08 66
    0xf07404241d64274030441050701550f80d000c00c281074504141c50900e543d400b01140a09100101d00000300b5540341640c00080c0c05604a000724040c03046500c10840d240e40301d210308030380c03045018074080741d900c2c03800030003050440311410300103586900803502070411005107130083c0000381441d100c40c5180840486000c04183d201c0004154003440318070990b004014259007212851422042c1c00c20b00c4003010b8060100c2d1044103290a40e40d0700c81e400e10601003810f010240194010741d05001c01820300c0c0c4010002180640c90380072a030349000f580150b401c00c4440001d454054900e052000f07202c0035114007070051070804003c00161186030f03101038640f20131005110100f0340c4d030a00364041da800703503c4001ea8203000600d0b89c1e80e240ba000c00c000d050071481101d040c000a02d4403550030001b082c1c2c08401d039412800200200070002800c5000c540c41c01c2c3c02401582c150051034007603100034046140d040300443c3d20068940c248400c441038240b030b0001c01000b104943d0301020105034030701d0300094440d4019801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 942021474 1250 942020224 942020243
    0x120c17130c121a060f03030c01140a0b0a03030503040807081c0e1605040b0d02041b0e01050a1202070c0e091b0d0c0303050c1f02040501020c0a060e0409051009060b130603030c 77
    0x604c0f000807a0300b00349040894040c040011403078080841075104066150100203c071901d9110114804100c48040303180940100300140103002090080300907650040c403a0174030a10f4a052980c88800a0300700d031504e5078891031200c5090000450a0007110900c1038031100a04c0305881d10b0705546a03c1c501c81c420140030b80c0d950221817145807944145804815006807003444118a41d85c0440891b0720300080800010700f01d02c0d9091180e61007401203c0e91303025142d8441c68181c40aa01c0d610080d131000e04100c801e51034280c000a61021201c1425200b0f010303150180080358285401025011038080d200d03841600c5446c9100002034803801c55400b0340340c0501d0038644661a06403224503044014461080e06016024070112000c419001002a00d000703900381d40040524800b445445a4603015500200342c400d10111100c1c240f56204902c001d0080b41214505031102c2c104404136120408182e805680390b40c000e842604000c6c00c181c04001004c0c008200341072441d02d0003130507445150b0006100422 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 942022724 1250 942021474 942021481
    0xe0111090f0312070b060306010b03010605030115030e0703120f081017121305010e01030507120c02030702060d0c0e030304030807061d011b03060b0a120c17130c121a 73
    0x10304203e1140040e080500c0250750701030b281000b0141d85401c5a040348288a51030001c2501c3ca01841941e040351004e40701d00342107900702040707140608402020081055943e5041e000d600f04108040d0004501500340401500c103070b0030000700f52031b08815210040c4002c03032703040c050000029259041102c912401d485c1c0f1030300f007020400e03042c202d4913103004d403480d400801c140a0586050b40c1120032a82c1c240c0702c010340d066840c00150b081c0d843c00c986102c04103011207000c4c2492441d076005201c100010748190fa142042a50004101c1c2d0044044510220354591845d00b03100d8006581000341542107000b542450304d103640c0c802440c0300302e00700100a2901c0785001c04500c60b401c24020750702c4075080000c0c09110f68400707060f540002b640c0a000000b0342000800500c061800d002c45000701c8442d62000800c512003004a405070406030b41450030024100c040d284070360400e182a900031082e42c8526a410303000b038101010030840f640c0280d6040304400c07004800090408110a407070100383c031000405a42c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 942023974 1250 942022724 942022729
    0x6050f0f0d080403080d0b09011d070309020a090903020601090e03040e04080702040f23060f15091807080103110907200a080418180b071d0604090f0e0111090f 70
    0x290381c0002c0030b0350404140004107100c00d400c03203a21481c7c1543c1c11020f6030ba07115150110302000e4001002000300309000315424038401e4015030003150010b0041d08600340e880341c030f5800b20340e402902540145c01c020010320105415019081c1a1000f1400540c00c290405460500003240500014250712000516100715103803508001503041007440208600d08844200d1429100f03c52501450141230000080b210302d4101c0c1039101c1c0b604081d18034181c006451300d00b0055680004103060b40302d905800200c0c070f140ca00805a034403c13960303541e51201e69455840d10f64a03a005200c000c078820126401003124162744600700403807040c1c00000d88801d650106040b40c0c14081d0201000d440d079071000030081126014241503140e27104407841c080111102445c0e00d004e00540d07401c4007c2000301c030400890b45881c411819440f0f40340810500004540c080000a20300f64032903400007045a441d800c82c3c0b64400e48920982d000320186600900826109002181180c070400c510f01c1d11030204c519408000740c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 942025224 1250 942023974 942023977
    0x1031a0709030f0b07020c04060f0b0715060602011b0528030e06090d140309030d150801090309030c1707050112110d051503071a1803030703030e0106050f0f0d08 71
    0x841e008090101101d80f031341040e55500d2000c0f40d8079809131048101e0210242803c0c880d07003040b106450b2001c002d0a060420403d401d0b0b01850040e074801032651510b0201aa0921442000f0001c540000a41003940d460001004030291344980c00c0c000240306081040100100321310101014803800179044101a009900801d640380d00f4030560700ca980704000e804000080c5196206980d600d8000c500018070341104894402290701c166250810701c02240750070b1480c0c0003a01980441151000255264001c0740e08550610f030b0150001250070800b0400d00101e80203d4010388144040e10f07450b80400e00741c00d60f0340c1c40c8501c10541042030882050000084076404040780c10100c0c20a5a42c0e5107500528001805095031007004c0303105c07031041c1e01800b440d0001d02e2400303e038801041c40b184020b809a001c2c6080c0c00c0301c0100c0c050009503000c0140181d40c24001400458405d0302c00054440c000300c201c80c01c43d031207900800d020b80d24084541046664181c45c00050000465584070003014518110966 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 942026474 1250 942025224 942025229
    0x4050c0f13180b0a03080711031f050c0a020c090712060902030103050106090506101b0f080a031406010e19240f0c17070204112a030301031a0709 64
    0x68440c0458814071010080d94807804480303a5032911018a5031111030b12007140c03841100c1c0c59028183d00d104000280451010303040b068003910001a00010a0012a081c109a02c0380c0002d021302010004c0282019446802d80180d150412941000120302010390b0b40d805c0041640d02c41c540c2d480000e441c2511410022044142001c01401503a81c0c440c0800042e400a000c2196507500300500403884c04031522070725204a0700100311f0442c110410f98160b68a0010980b070301001ca5400c40407402043c1d000c1440038001d4850304502d80c1d1148086001000c9400c07800c500900040b2204c1406111b81c2d00c6001d0600e12001182c201c401c0e04004036003103503510074590080d40791038290ba90721503c02080c50314414061007540c031121b400344200d80c0210f54040c0c000400600c40b0b05030203141c44008007141c000d0414240f0283c40010425650080034000da0015040c3c0200c1030a00310031a80d4883c1c54010840020343d0003c0258299411036503504031201000d00302080070350b9071600043c502c9200d81c3c2035000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 942027724 1250 942026474 942026497
    0x40213050912040909140102030408030106110c060f0405090f040c050411070f050f0d0807091202030c0d0624080a031b0b01330c031101061e0504110c060604050c 71
    0x1501ca5890811602910707805c8804e0f900e5411280c20394030300003418021a0f2003298821f000c0d6186a0802c9400d171500c91140004402a10916851414ac0d8a51030018040031484150b03464840703203003000708148280020480340b100c5141006020005000440d0341c01992000c071404101d09007014070700709490017502c5c0041c0002d95241010070600c41c01191049660722104140c0f05051b0200006540c1400c05a40382e038001134000034108041660b450071201c046100030180c0c0c4814180c400003590040500f03506941c47c5948413441d981032090070043e80c040e580c408103e2021036140800440d140c0320000130180030711a6450701c000c20382c02107075000441d1945c0320425084558688803c2c81400c0c0000d15403031403a4829a01034005190300e4084e28410361140d503200100e100c980e42d0b0841e60f950300d0460440081d074035604e000c962202c240401e48400c82c030f5a045440030310324240800054803113883d40c180e4006420810701e45040d1022429503403000701034401007129107501290000f640700d034821164 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 942028974 1250 942027724 942027727
    0x2090105210f06060316080a0207120801060e01090b31080102070308070e030618030f0c0c040501060c08071b031502130b0f0d150b12100e040213050912 67
    0x481d030540140145000e030740074150310b28040d6215402d000312403000303440074409880880104d0742440d110b0680f40d135000f40141e00141c213200741603842151043c00058000003140340312005220403540142141264103091920002d0300c1d00d00107031400948200c070383e074102800b06520b40809500302045c154a45103036104c200241a43c0c0d0f1800a03000b50000c140c1200003545140101d40d0140c07003010701a4031400c008014100903120313107c0192825071291035051240c003091080c42c0302029031002800d0030088100203805100d07031040400c411500141c104e10144203008822401140e84c410a458405610602603004054051040e070030110903580300030000c0110051100e892102c5801602c06c0303a0f0151b5142129a0b00c03031050100314000c20400720103a07042402143c0b1060001c0e04498080c034541100403030540d40310400071401d41e10080300040010054001e0118031a54412000c009000c00b220030b43c00741c281070b4000307645003448040b40d84ca40c40c0c80d1000b02c0c800020512684800052820340c1c907 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 942030224 1250 942028974 942029017
    0x80c090d080c121c02031e04050a0506011d0f10030f0f150b09060d0512071103070602031c11090409060b0409050f011a0f100203040905010305100b010309050606010302090105 77
    0x210744e8040802c0500081010400248806080c020303640605d0012805280c2074050f050030340c1e50400d0040080d24140301b6020000042641401481e0203403181c42c045070f0b900c500803803100c0e07840c02d406880b42d4142d85942082040462651f007030b5505884d4080d034103070084140742c14595841c0500d40005001010040e12110690500b0340c8005c8990308180c88030b6030303180c3d107020070480d2848050300d02820070b4000408196000d40ca54004208192203822243c2d17060101c1c501091600300c43e600010056400011100c03048068200d01451b2865003103010b00448444000c04265406980700e02c5c2d0285840c0c0404c0d8040040b103070010000e03201c024008214900460900c2d80c1c0d14941c0c1885101c1d40c0d441d1440c6040311036101044c01400c540e016041d005210340480c140200c0301c0c50200c0d000c046010500002c1000303c907a0142038000c1d800b070750041400c2c400c41d2020748110b400140070181814075050f1110300003500815100d600c10b44c01d080040e00d408001005a40501c2101c1c0948246030900030312 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 942031474 1250 942030224 942030253
    0x230309040e030304020f040b12100911150f131e061112030c092b2d060b03010b04020d05040501050601090506040b0a140304030e010f080c090d080c 65
    0x2901422004440512080e5515412151030b8482698040d4201d8019940709455003020381008503121005001200b41114091245040c100c0584810800301d89440103507051220f010949040d85004890011404040b50182c5200c3d10413404546c502781c3e004107031039040070004442100242411107101c500d207514040d4401d042e407014007035200030914405440c403612400084400000c00440c001a1441d10340f84180e1400c1e40049081c1640b156100d501c1ca444409130280a41001c600501841c14620507413074524030a801d214441074201e903c901c50981240d00032206001413540058000a0082c41107001c80d025040001e800364200b400000c0300000310742d440c0e0040344507074054002004680c4900d0011940c0960f00c0c495258084014042030080ea507240c00100070121003400e0a9000d140c0c401c2d0100d52a800499050300402c1520004091a5802500188003150740c0d1a09407940c3c40d1541020365a800703040c2c1883c0c082e0701c5900c1820308100c505006c44140d5100c1208031804542c84106 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 942032724 1250 942031474 942031477
    0x1506030215031e100515040305010c0c0606050d02011205040501090b1311090402060703050a030902130f0b0f090121080d05160201110d020a0c0c09020316020f0c06072303 75
    0x840c40c0b152031944000f403c00c030b440389032100d00610b0700e20000c90f18070303181804001d070008070503002408080c0c0420000000513000d10030030100c0d4819880309031003106a42011411240543d0002e03000703d407050b8641d40140c2c0e008171303a04803035030411400003100d8a45040081c010010100024036141491041c01020018101900007062040d15414540381540c02030090340d0500ba68000c0d004a0706009080010340120b0180000d1006440d00185403552500080e03e0b0407400030029a42c96525030711070342011654001d0040110301a10740c80623500c0c6003004103140d000c0500c908031768943d03118880ca0b0190f803240100940c2c0c1d9040740a035600c8084011801d8010102500e0202040c80c1c00d490902c80b641c01170049201a2143c02807083c00c101050111401961160300a80c0410804034800ca000408800501010300340408005849140010302c0d401c0c080c6500c1004002c0d94444054a003402d00d000079036011180741070390b225407604c240c0e141c444e005521203640307d52422602c11041c62901c10000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 942033974 1250 942032724 942032731
    0x20a170a0b0406270c09020f0c03030a020414090f010b0a030623101814010c06020a020c010324050f0402310501030608030a0c110a3f150603021503 65
    0x111311203042d542e444844031080b41c00e0000804a04544d00104000403c50f8041d040134610003012500e000e801540f01c2c3e046074030894204400304c0e03001c1400d104a802e0006240614101641c209419051062445240010510401c680da240002e038a40955120341c220700010300d21400e00d909402101041207105188c0344596901414103031116a5540e4802c2c040164000c2551000d010300301d080c180000c2218120b9960141031240652aa20000344180300602c4501401e13030283c180482441c3c001016940641600d008a496030b083c0007809803003403d6420111101281e40884a2035400701123000303800780c10901d0388504200c04003050b04004400642e101051004810800f59440d0343c019400c5466074040d0907041d82c400c1c000782011a000d140a05030301402420702c480307855000d0780061051000e0f6000f41c1003804141c0d001c00680c1101030702c0c45c8441400e0520500200010300ea03145242c6003012006803507095000590340c03100070f195000341c0c045d41d0007034118503100b090444d2007820b560096 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 942035224 1250 942033974 942034001
    0xf090f0b0a0606140306011803030c05010e030306030c0405090a0606030f0327140a091b1e0804030513080a030f0806030a02031b0a26100603020a170a0b0406 69
    0x10000a00c0a420900c20601611150b481e411004442c0d44c0003901d443e00001d00e058140301040c0b0920316081202201000214030955030010103041a02d06103080d26521540d105080d0710901c18003605560110342d050380300e401920001041c0d070314404c105160224455019103102d29020340031041c000b50080842c1d0281c0241c8070b0380c10300840c0319400f4500c0d000003641190082c0e00342d20103200074403441ca2074101c50316008102c3c0c40581d41302d401402c1100c01300c50b29054034090091601002a8000100b07118448402c00d04025070132460b100035001c1240200f005041200c0003c001000a0902080303030040c1007031004480350b130121403070082d000310440003005c4e0115937454009401440c00042d20000b1a9010380940704181100610008d441040792a55074408110000880d400c0d14005030900041111912070b90f5507900c88a0850400c0b02d4001303054806420443c040c005602c646030711008a800704440355624090520900b401d241d06e1220080c0b00c410104280814425260042100448174 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 942036474 1250 942035224 942035243
    0xa11040b1324200a06151d04020a0b0a0c05030406020a0c0e161d03030316080105180613060b07051b120a11010314010f15140d0e010f090f 61
    0x1100e40c0c1100380a51000b8180001c040440880c03516101c1840b0464140c1d07100203c900015041d40d900c01661440407991418680882003040100154001c1003058514411030b02c807030b0304054001c01e1200f0010f016864298000080c40b0a405114001019596400c08182da44441c2c803084029100e10207400c05079007030a100c02c8040b03044401c8011250040f071814185800040800c0404e5035071207051444c3c2884514540084085a1021b1000f58421040c909440d060b045a40d003024003184810380106019140602c24994010036101d44541c100000311182c00d040c094060380358028200e030343c100310703110140403c9100400800003000c4500480340c0062600380c00c1088144465030104141c004c10541c03200b01000040340110903d4081400117240c0401d190b040002004031a81003031b4001020300c24030100c2040102002c200741040c1c96068039141c4594440400349070060b002e106240803000d50b443c508800000000d503c80b510042c0d400d2070901c0740240504245032030180c969404d6800313251 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 942037724 1250 942036474 942036509
    0x3030b06040501020d0e0411040801050105130902061611150306100f02070e041703010f15020304060801060e0117181c17151c1103010905060a11040b13 67
    0x80c000241d409440040c0c1c001c1400c226080f00c111203002150402d030760015900c1e18a00c40d00001000180f0240110070008641549401c00f8010031b10100147d00350309914001480c80141d40781c408641c81e02c140251922440c110605080c1d844604e003400d0140d02080204030103820040322070245105000440e0344450030542440d0a54800300c100f078010300180c22030082400b968212452094003d8080e0305000210300c8140030311400c036402070b00036000807159144200311000c05407000c2c80ea1360380c0341d1000d541490b24000010f8500e21060284400703004943c42075284a922a210070400801148030203107150401c1c07801c1c0d20500d64081c0801e0705a000e0302c02944071100d900c5441c01c2d1540c000380e4901c0d04083e4115600310880310301400001c40086100000c1c006660b5240a282c4001c030395582030843c4c0b00662400c01c4408111200300d13802641810b011001040001c920765921003060038021410010711032080d1070b240b0880d001045240404074404243c1c5010f80544030607180d21100c008071400c0e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 942038974 1250 942037724 942037729
    0x15030a0303061d092104050406030b10172e0f200705070608063c0301050402010c02100513080309011107241b030c060f09051515090703020703030b 65
    0x10800c54121320342d81c0c080741742c002a40010b0900c101d24420704010f03960038075859500107410743d0250351003503a0000d20b000034022803400030704480c001803405581c1001d4140303800044c9511010320b4000c00c0c6c2030040340a400786240c0440c1c3c401c2403c6402034503081044501600380040241515407000b0303c0b03044e540b003c2614251746602102c0c82c40ea000b200070b224003843c183e022141180010103c1d5088442e50380c0c03191581e1203945130220314076401c0d8800505003200c4a203101c0d424280d400c0d960310030380c140018440980d80003c28072280c1d039010b4586c107a00c0e02c0140723001c5d1003911039460000c521030310908000400d0f01c0e000c000780110341c3c001d90301c140c45607081242040c0e54143e14040c0034030659144100110505100071840642040e81c105191071a40c0e00081a00c0700e00c00c0e00c416000f2544490103041000a0f9214908040344000d804100c2802203403200c0ba034600c44910b1744030305000408041004020074207810200c103640281681071900d403107074005002c1d40010f0022000309080c0030549a051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 942040224 1250 942038974 942039029
    0x714061902120a05100b07051b1c0201030b060c1506040e1c120f02030109020309011506050405090c0708160b010f18020a09090c11060610051215030a030306 69
    0x103400c08424129152100c03c610001001d0103416003480d07050710400020240d05010141080c14000c0000e00720212061000007804a1a100114403540030b10b000d408a088890700c000c4030481d02864005000c5400b86c0201e0918445c51280d44140c0c030410b00003013102c04074210481d110301c800381c0d82072100c003480010700f9684080030345016060100111140e54628400c428401d000c82c840040846c00d04186044502280d000707070407a034103454000040040140c0240241242c0301c003501141c222107464103200130319a00032402154030902c030304000f1135280b6402c0020359150a0700101d0041d52142c031200304102d20b1130304d100701b203440c40280d100000302882c449005030f0031107120a11140c42d05a01c41d0140009502042200060209145e400318110382c44e4403840041103007546400d0150f19800400516100004040740d02c100d10b61482e8541c030316032010a4403c0c5c0d840740c50b10791102d0740f982c80011003a0b1114500d200d425205402d078a1003890b615410010443d0713840e98001800220b4000c807400c28 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 942041474 1250 942040224 942040237
    0x2e020114060a0e0c07060501030b0403020f210903030706020c06040b090d0815010c0606030318090b0f0f06040810020910050306010c080c010b030307060e0105090d020715050714061902 81
    0x6030752103504100c05400c8a01c0c0582c004c3caa4224907103041c04640d280c0341207070300070f800c29560b5540718030400c002c05804209202c1c81c1c118400042c0203100000d4805540b0080348048110001e802084d0703800380743c80400a030b0f07a409500010954a070340c01c8603901e65031550100c3c0c1c192480d449010201d0000342d808034000b40900a103554096082c0d460300104412944001710060401000001d00b0010481510a4070044e61103562a429072051a4120020b0407500b03410411016281407000e5665980e0f811881000710000d84424480740c02100016803c1c0c010ba5114130b1050040340e0f42010301800e00e81c0284840c910445024003280da00b00c80c111524041294124081851031440f00089084d0301c01815a0707440c94000400c81040d18000f00741190448001168280e032114404992082e083c060070b0b034016080d5000b01400d540000f0029516a01481002d07400d0342900c010000e410312503030481d9002508119401041d072803142803035076603407401c4815161820008003041001601030088421 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 942042724 1250 942041474 942041479
    0x60f0b190602030301060c0327060e120c0d05070e0c0712090b090f0303040b040b031501020a0f24050115031410030605060607060e0607021501232e02011406 69
    0x3182c2c06e1030025680182e100c10181c0030b000100d00040c542c0c070004010f0544000181c680004554030b41a809048165641c00c840d11407104400044e4960100084440ca1a5021680b0600042c4581007072070901e4155044100d20070b51501c100205400b02c0400ad01c2c0d030500c100605a90713040000d00071140d0f25a603000d94900c00c4810003228560740391020410204000c01030941e850640d9428054800360b201c0e502c10300b10620040204001c0d186c007001e1940c52400d00b8005800440031943d030780b404246c03d030034000b40139680e007012180424442070042014811105010021541c4460302c082411850350001c000003402c00d03410f200581a0200d1040c0545c40c9913104944082c10369640b2006084002d10454000005100b408042601070040b4008024200003421007418845002405c00001c800664190310300c0e1401040542a000440480c000800500f44074400c42540002c1400c1031669110a40441c0d4031a0098240c04042c141040e2258940080007c440c40100003050b0100849070b566 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 942043974 1250 942042724 942042727
    0x9010e01090c0e100c021f050f03130b0c0c010e0f0318060d0f1d06010501050f091908100b041b0309050709020d050a05060603040f110a03060f0b19060203 68
    0x40012940054407240d145051010310b01c3c0800c0d0104118001300f0501d0780c005095013514100b581402d036200c0b44d00c0d1607002c0300000781540d04640a4414829080301e80982240040001c810165000742002032640c0a014030300982080001e41c206504845045402c9510306404a000b61500013180d003015081c0fa8042d50501d40400c00403181a218010150f400002c10415404440028482c00581480d05207001511518881c0c140c00c1d054108003418050b584440018080d684e00a4103444008130b805010580c0d076400744000c554095036000758141d043d0800c1101052030741d40483d4051080d20440010062040032408101c103841006107041007038195440d0001207544280c0000403003501038411600d40c9030352642e0030030803070384100125241079a44e80140a920007640c00f806807c84022a01d15085041984500d42e452030301e40002003008041c40c06a040303a4503416541001560441801c01c402e9507480000000341a96403040341c0300e960201004940e1803100c10750701c026a5a11350045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 942045224 1250 942043974 942043979
    0xa08011a070c08030318120d050a02120f090c0406060806090c1902070602160605180a0506070f0210050403031e020a020d080a03050a060b25050a0f03080609010e01 72
    0x80c2402829400d84029002080080002040103600d4120007007070000011962483c00b4070003140300d1001c5410317010694010101c501c8400c040398068070a28420721000192075154480e41030024820083c8003105654a40708000502145207000c81c0b0034001e00707083c0d442c907854170010007044642a0080e000400c0d00391000c40c802e414015410ba50100410b920325290500004038074050165100c524001a80542c40c1840401d40c140f000d5800313034105041009a141c10040d000e440340c01211040d50ba080e218880c09045940ca007043d0f000101006000195151100e003440700c010508428140c0c014080c03d244504494031840485d0f0840343c0582d80d0390355a0030018100310245660501d00f004501c5646c60304005030303481421880c14980728050541e51400c00c1d43c030203403d8a400510100081d4980003003084402da0b050122070918041d0340c1c035244c0842c0c41c400f41000c040f107282009071151143c1304102040041700d13541503038114003d84400d100340e581ca00401c2280c2c042402810100c00c40013004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 942046474 1250 942045224 942045239
    0x90e12090319050d03062724180e0303040b1915060801090b03070b0d020903030d05180f16060e030316030302042306040b030402220902040c02030a0801 67
    0x280031030364001410340e1164501d900d100d03095242d0807081600c184d0014200034038013980501c1703644020f2100c01c04400e004050ba44800001142049030061120b0b02c4881c3c103031098a000d00e40c910401c496085940384582c0703a850b80070403103102c04000800d0b203140840d00d03d4160700010590303201d65840b201010f241d550350040031400044071410760000c0743c1c480f01148880203400c80c0c00d1000c0e2040e42c0d1404000d40c503006010056070755206005010b500004030601c48402d0150803121300040804000d40d03a18004030100c1c0c0346100c2e90b082d01014030b2620b8103001203480449810b1400d10301d084215210300c894645034a4807150f412203111056240c04404200c028058031960780440d80040640741020301070000780d00d05542860742180000da001a0a00c035054035400c15100140310f07060540300a14018020540a00c66030165204c92040400090b00b199594109108201d00e030140c00b051a5007498043d1002d4610524224410340c1001010890503100009036800414183e403107608503441c0c0300c030707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 942047724 1250 942046474 942046477
    0x301060f050607350703030c0f02070302090c0421060b0a0b190306081c08150303030f0c091203131d06010c230708070b040b0d050702150f060a090e12 66
    0x240c0c800544841c4004c0b00005404402100c100540518503558550501e4024100d62400307003800107103d81d0740c07080410b42d9400114182900d40c1516544000d885e101d0701704d8031600441d0b2080c0c03001c0b80708214504407400346d954500401c82c071409040c07280407003480030094030500c0b80c042c1441584040c401d00421401d00000101c0515003410001101500e400c0b540742421141e0003401890542100f02c001c1d0329620480c580d41c0310911211030044502d803040000d859100c050220813044050300081004102c1c80d03004c42e01101d00040584840c0442e05802545a82109400d10610303500c920380042d54040c00e8051140c0343e08078002c00c0e422a0703140001902c0c4400d00001c203495002d410b0031118102d1035201c9409081c1c4504800902c2034605c0d0514452400303046410079020550305110810003810301c2c01c180e640b02a80c60744041007a03922000124641681310300d021801c0c80c000004d000150300b05036a004d024410541d5511546500d80070610160341c003124140303070310f940501940b02071101c20b0380 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 942048974 1250 942047724 942047753
    0x616050a03090f060f020910450807140102031303030c0f020a0803040906140105040e1806010b040509060d150f0213240e09010506030703150e01050301060f050607 72
    0x310480c40c030f00c10607102d15045030011200a18010341c0040c601015103000c1007040c1b6148000e10b030603910740e43e0b1f02a0190751a44400740305000c56501181c0b000c5d440e00141c0d00864024160101c032a607003a031f50030342c0e207581760b120b40f003000400410b5801030a65544040111000e481c1d40100f0806401d240d40d0301100c40303120340401034400c040d032810b8440060762040c0c0081c00400c1d03500000c1d80c0321070505c903d640487d00742d136015420041c5010440b04069820609071001c0358880310b0742c2c5106556100e001d01d01e010b016502c4007558042c01e8001f192110501e40640191602070740c0849043d80d5010610080300550031010702258000744d03061401027015003110f17240342043e081c050b0a002148c000f0400c20b40c5150010860141d002c0903c110f013102c075a8210141110502e45110841c0754a00410381805041c0210b41c01800000b001a06050098001c0c4105459055900f0215992512004000744c001c3c010b8a10039401c2600001d8030350108a83c041c2601d600503d550724003d1141da40300007100840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 942050224 1250 942048974 942048983
    0x1002010b0d060606030e010203011a070201050705030304200f0d080901020f03070507030203121606230a151502031204260a17011203120f06080705030616050a0309 72
    0x60509100c56200c540032051840e201c1c00c400300c0c0d00d038200ba0000c1d050b20229a01503009070700c14401000400f0728a0a0040c10300d1840b100c10395280220b00040b01c91388a902c070050502e200000500c41040001c0c0700d11024031900310402c02032010420f0070000c0c80c901c448491540941101610400320700644014141150140121180d0401d45901b40381141c1215400f41c0c1e05070081042001503050511900b4680301e240c1240503d04400250702004105a070b60016111540e01e40c000d0b8031440200c5089000c0d02c400f5001c111003864403c034910060700440c200c00101e202c0c40400001c070100d00c0700003030008a031981c01460078460301064401041c0d800070019a10703038822600f522011070140170080c4c400010307000741d5aa034400107540078201d00000244148505069001005071403150800d501c10268503150180b008181001c204002c0c1007028201981e01e0f2800d000011410400641981103841c260203561850380e902556604401c43d0002c5000450700030400112070b0303440780d4013000e0658483c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 942051474 1250 942050224 942050231
    0x1b0a05030709020310060201050c07031b080c060702100509100911060301030305031515091c060c0f11010c020618070902030a0b1e030c010e0402070b070f09170c100201 74
    0x5440000c0d1400c2895030000028a600000f0b000081200100e410007904241c0003d010500784040288680d10a0010180401075240600f8410f0001c0d01e50080d040c1e50000c01c0262070f22480315446841d030034140c91403009841003154031012881540038075880340c050080640880300401121501074085040b08503004650396808000b240d4507a4051400b841c082e0355059102e161003201d1742c00400c801c090301031081d60350325072013824403007003404840d025034080d1000c2c4401c04a445c1440010fa072000c0000385a103051402c2000d1070b41e4018240c10380302035255905031103d1080c0c10a2400c17122241c24210068210400203220202e41b101880da0f07141000085a514030703500c100e840c040760004d03160822425190b1002a1292a1059200b0a0901d040f14000000482540000c0da50f0056218017410b0100c18807440180b50b55030741c1030f10105500004600c030a803918100c01400307581c080c40d001d0041105032802003026000f00310303c00c44680d0260010407120507564104182c4900ca150a40c0440d0748 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 942052724 1250 942051474 942051479
    0xd1d04020c1506151207050912071e060302160f14100c08070503070206180c190e1e0406020f0403051b0a06031116060b06040b0903070e0103051b0a 65
    0x104001c62541400514040440da00b800300130400b500501082c1142d60710001d003c0d4007814041c00f000f550b040109800c02c0e42c2d0311003104010a50102c1c0d007000ea100e2034051000002030b40d104014001d4ac129141d00d084a24403921110207508a0081d0852000381c00e180f03052140001c1c800240c03e801490040714240300c0916101c1016280414500d03624201d96100d41404005a800c0f139100f41e08102103052150643c500070b24000c0d5286030003442c1c081040318000201445200621900b0b0200c1000707020607900c149a00030144038003526101d0b90040701c034003e0000384891150900307009801c801811000184e103640c0c5801c4062740015600545224080000000095041103011030380301201088003002c8480b0350412440342c41c6a80000c00703140c00c01e03000342400c0c1044c0c0c00300e480c45d100318459940160540d007407040c010000043e10030b400c1200001c0128407904910090801c80e001141141d2410340c032041e03070501845d020310000341a42e1201100c00700501d0700c00841ea44180000c0c200f01101b69 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 942053974 1250 942052724 942052747
    0x302250c050924010302070515040305041701020315120d230c15060402161e05070e0a06060309020901050405040f02091305190c05010804060b0307170105090d1d0402 73
    0xc4180c034028a07a512040e46143c14109a4076614140c2c3d40900f0304508280407900d940d034550015111040b650521100010201030007403095401a0021711100c07041d0042180c4c980d8000d51080d11f8003581104000354001092030543c19142c40000c0c0e480c040e010316018900c080d25010688601c06075100300d034241070624505c3c0a0051309614101000400d40c5820112045050b00d00140c10a13000e41e004000703038840060300344070001000c0d51004078400783c3c2c1020240010700c0001c40000604ca4010060001003102c0d10754007940c012a603141040292503507801c0143e00310b80c0314203002900200c07013a004011318071b00b980c0156405401136005074006040340d800242844d108891940d0006184610ba805100d0100000c6841e1524460055005025510f452865504a1141604100003038000a003044003940107030300900c501504039401c95440d50a41c0b4040108840340142d40d40c41c0000181c40e1520008070344910b03418580318600180900b0380c40c0590100507c0980e50811380811200f903480c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 942055224 1250 942053974 942053989
    0x20c0115050f010c020f010e04020708130f0e04030e0906040915020d06051c1e0b0f06010f0f080a020d020c07120c0b0a080a020a030608030705010f0c0302250c05 71
    0x160440411011081c0c106020040c1078500c40410728100907035690340b4001600c5000c2050658402403d00741c40da4008000091302034411414024000c00c0e000c20040410f52254a00c070040c2c1e0403003005036001c144c07076480482c1c002000321401f40000e148245090002d0400d00f0382c2541005000d00042200c1009403100d07c400c0408440c801401d5500041d2a01d10612910600c4081e1604a80480034030240c00c000f03407100c4aa0590240c803103030750090003105041d0365444801460b07600508040181c0340403000d01d5091031003240c1e0640400c81150252000600c10f187d4084000300d142c4400c02151070703000c0c03480c0082d00006841c2c02032035400c01500041d10340800a6000501200304018040c100d68540f205401c0f800303611101c1140e01c00e114081445801003c0c065014004400042c2c0b03408408804074050700700d961084070b090000007620b100340070064001030905a448507051040741a000000c80c120711413114401c4840380c0c81c12a4080032002d400c5441d00c00b5001d0000810134a80b03800004048 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 942056474 1250 942055224 942055241
    0x30c20060c0d03050606040807090f0b0306010303020a21081902130e04260a0e0604090e010c0e013605040606050d0b0d0b040206090a0b0307020318030c030d050a03020c01 75
    0x2d03804404800903a40e818002c0f50361003001641c603d41058605407500e42d070307849180a03c02841da00d4841000300301d003565110368147e1000408640840d41c1d64140030351034104003001910403150f5840541c20440c807403002c03800da03d1040d9a801d809a80d5801c0034001403a0a40d006c656055000c02c4080d0411031090038180141004002c104000e003054a405a2001d006c0c4540544800c3c5036a0307035440215103103064034070754007141c1064144040c04500051482c0300d035070090b0f5902d40c600f10001d6041d010540c042041102d050711001042c903181d00054591030300000306180003a0140040d1120880403490140d0031628220030386d44219101c00c0010151651078100a001407000700e1001c44180590040c0356154801f5282280f0b403001ca9110403011110092003e40100c10001d8290400c0d211550300394000c10300d5900d050780300c1c202108002d449501c807071f588518901c07103481c00c02140e2402003030403404018018018190100c0c543d500391101e4020040b071205250f0f081c0012480100c080c05030004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 942057724 1250 942056474 942056497
    0x510030b0f09090145061512140c0916050d0e0c0a0e01050604120203150c2703030d180b0406050403110102072a1d010608010b07030c2006 61
    0xd1040000c0300c5a45035070096050b02d150380c2d5600d00380c407603a050206504200d0f41417000e01d03036944550501313110f805401220f042d4803500210603000200460032606280c2d80070300c1044038110005800e1020355032041800c0e402070340070385100f0214850603540c00000805a81a0038000c0c20010004201d004454440c41c24004035007088103118110310340280c11202916420318009100d50620010612034040d60180f4811031500d4000388003590b9040290807240e54a007005100ca528192000d0036040e001203003036804d00401554000b21803800d042240a9608001d0000c0d8200070101d000c2c0d1000c0c018000c00300404044070b86840010802e046144c81c402e074004c601c04180350070145002404440c42e00740d0308843c0d0f44180815400107114415044608111102e0a00100740c02403203000803030120b51220f0b48030400c5240c0e40001080320921281295481d80341d1444507030344c0d05081c20446c0301e500c1c0018009009864031100007004d031914070094201c649034800c1c00c43c1c410f03000b2507007580c80340d240c421 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 942058974 1250 942057724 942057731
    0x2619090b010611070f0b030c040e070e2b0609020406080a05160909080712020f0316021005090603010317070614060a050a080706080a0906021201030308010e010510030b0f090901 78
    0x1c82d50308466a40c070310060b0f15005101092130091420001d00c554003034561414000004220310824900c00d98015043c40701c2040841e0520090203031040b450141030074043d40fa00c001c08010400411806e03042801c1c5a40c0318100c00034644d0301e03600240002c007000ca0f4815903070039010603103107420001d5151a0744204003c0c0307002411740e00d8009203442d0030f40c4000d036503a00785014030001800031800c0e58400780e44926005025a0400c1040c8c0c1440c0a0714810074841c07001050fa44282121000a416064000e0710b4000c0e801000308022562031103040080307608a4010401000000d501d00a4100c045a1704000c0d181000c040307030f448c0c02c10780b00c5002e650110030f411182400094034000101c00000c00080b0b41c1901101c1c03a2100090703ca20491146174184440c2d0f0000070301c0d11f440c41d00070119169014108558881c1e85d03a40c001c0240a081c0020f4000038862030000c20007885d215902410307200c0040241d00c0c034901c0c101d011405400144407460300711843e045041200d4550400040c01044440e0011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 942060224 1250 942058974 942058979
    0x12030d0204230406031713050306192f0d0e01150e101406130506041706070503070e060a021f050a0e030711010813080d14072619090b01 60
    0x22480c95424030300d88203a180030000c10006051203003140300d8001b015040c54980803000b0300304100490796881740d0b8142c01001c0c2048580b03040701e00b10310303944109440c04211103101307ea020300c501c0f601400b4a0711000d010116402240d83c56002920900000140c04606001c9001d41da0b42556103412544840102c02042405403130003841100398040c0e0746d081c0d410b0b0918500b6042d2283c5242d01070a0318018403000a0001d050b196200c10903002d0100503002c190784035940e20450040c9000700f036082000b0b0182c1030108041d14030450449008034416a13a030781e50307449000704015403607101a11880a500c41d00d40c0402d82c01d0540d07440401c1e214001c0e00006124505407400718142e42c0da01c03080d207200b03420401c1001e001030703003541e00352818440030318048200ba0346401c244065402e0304a030140664602080c006c0c01c0c21440e0708200c4c070b42d4000310130401880d25010000d0f528295104905036045032041302c0300f20440203210b80140c0c0304004a601151441c814109039040b65904070094a0401550006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 942061474 1250 942060224 942060269
    0xc010c0f1d09071404030602030c071a15060d1d0d08010f030209180a02030604050a030320030f060307050d03050712050c0303150303090603090a0c15020c12030d0204 73
    0x44918510642040ca951100040004100b0308000f04940c00b0300c0300b1100d0100c6844400b40c25a00990b9001d94115520b0800340c1410090760040d002c100c4212500d00d2020410020030340110380542c07000f5080110410241040080c6030b040032020760381c0c0980d140c141c10441101d92080c0302e07210002c18080d00b00e1940d10070340140354071b00503080480740e600401e1041005889010020f603010100c0010201c1550b001400f02c4d040c510f406a02030340c9486000103120a0000110b014a0028800d403020040d032481c03008074802e81c90481d603110603008424400035125170100b074071040c1e020100805070344402d6280c0000035080403002e5001c0e80015008107046040001e0500200d60303801403070411508201e40340f40483d41d41d10000301b04540e15000c1d0110030545031400c00c16550102c0f0000c1a454691608488255581111450550b48907020b04000140f00c1940a1039040c1c0358801d501034a01080b040e420700110740c40007041400140300c100000125188030381b0182c40130341202d591081c81c1a198450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 942062724 1250 942061474 942061487
    0x5030a0c150c18081911030a0f0c0e010e011406031b0418112a0a06020409020903102c0a080403080a0809010b0603160c0501060303080108010e0102030f06150c010c0f 73
    0x130038071070f070f0344011038020540007240410342007960305c000064020080080402d040c05c41380b45000706890403d4070a6010002401c2061080da500010303006010703a602d418070281910207100d0440d0032040301c41c0040f070604110700116800104612103024480000342d040016521550224030100000b03806140216a1400b514200b40c0308131802c0d078102410540e0b441400b0b0050381150107280c0400d24054034503202031207030f6a0103e0700800110340f0360307030b559140c40e010394041c1800074480d010b0400c0190952580e0312603144e00c68500b444a5a92080391000e0050000031401c2d0b60300e40b03118031083c84002880c0c0100410195109403116901c51504070009003040002401d084c50503410111210065181d11090341c0c0d00c55000f5a204000e40010f05054030307040c002c110060030650074013001005140e0410405812564060002c10000c2e8161910a00303d00068810f8442c600841c00450312a01d080d0302c03480100c0c2d1280f0340f041d10b045814420542110112081000880d050003541c0390800d40106 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 942063974 1250 942062724 942062729
    0x120b030715090e091203071e170702242802070203010b0604061d130c0801030c090213090c35060108010b0313050c0d05030d110705030a0c150c18 64
    0x45400031401c203410b0b203580fa10302517001c1075056403010002a0000d44245448101c0c0502101842480d04a0940c001c3c15000b520b01c5484a15000801088a5510010b04180c0003ca09840340482d03500e5622a40620100034004500f40c1e810280354441501c6901590105000203140c016510640c0384140b5095134a1902410302c18801400100100c9401c07038100d4070b00c1d1401061450800003e440011221184d041042c1c406520f41a1041200e58202c40c803517050300d002d9203001c41c3c540e1361666040140c2c400c5007100c017240e0302100810055003246070403011004405040403008050550b8140c00c5a445075210a4184c11202c61005643c0c18410000e0b90400400e2800d4200c0d58180524a5007622014200501c15501070921505110081c0100c442641c8014223181c500b100300e00708240e8135040702209241040c41c00c01440300e40d010b0001241c103071300e521002031806c100d400340046d100e000d40d030603050764039051020b0104060845031140382c40241041d11682031100142a42d42c68503149034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 942065224 1250 942063974 942063989
    0xf0f1306020d0512040614040b040303050a1e0506180f0403090801050606091c0213020c16080a0f0c1a07140a021e01180b0415020105070c03120b03071509 68
    0x9001c02c00a071540302088914581181c40040ca154960307140c0f0000030000c804032802c4e0000000144410071641d101b00c10b006038026a8140040d0b140c1184107800c0700c0b81d18000c403001c0291442456028807903501b1940c0d0140c00100481c03280d050800661103591012103103500382a41580c104010550032500c00005403200307400807c021316000f0b02281c8903205241c060b034801c0051144505142903148503000905030f029280c40d000d440850054030294101c202d40400d03a000e40303000c0c3c885008104401c5002c441c0080c00a01c00321002c2c0c2c80f4000b466220f404180d03150300c9a0440030070b0360b0842006020000d14a00f034481e40d280503e04242d81c0740c1011400209140c1c102600c0d60025948483d090b051001c440781c3c3c800c61499000c001a80c18803554403800c4209800c2500004401310075601074004c841400c103081c413102981510403822135100300d40c0c000210300000398402c0400c0c41840100030303030004064001800b00c0d2081c00240703030040c6980640c0ca00d04041e00c45030400c82e4408040c400030110b9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 942066474 1250 942065224 942065233
    0x23130b100c170f160809120f0709020c031b06060906010e090c1804060e010e100f1e030506100f080a170c01062d0605030f1306020f0f130602 62
    0x20b960340719a00010b40420181070350700400c0e0100030500e82011107071001407503045414005110315180703070b40da004844103d103d84141150b00d428800e01280949110f08010060945030341000b8644000b500140e1f40403607184418843d40d003241103002c41240718140720700000c000c80d2500d1420865011001400a8108816003c010034607880e490015a04860741040e5961240b098420511460741000000c070381c801d0801000160111140007124180d69900301c0c1e803841c1d035403110103403460b14940c1d115284518042c100c0401c083d075403031502401d550304240c44285a00e540ca840b5503240042c2510414114004000100100010a90210000c1480e000501031414030b42e00d54070001e580703036005445207010010f1414103441007944008090b085441e06031000c00c0c03001c840001600f4000d80241c102c040c4007400452694010400d0300d02c42c11240011a5055848944400001c5140b034421550301d5000c0c40340024110303211014180c10181c4107941a00c0300f01d1004c080c10f070402140d000e030095410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 942067724 1250 942066474 942066497
    0x3020f0d17130f1401021b22090606080607090303110304030b0a020d051005010203040513181203050f010509040f1a011503060e04080a20010204090207050d140423130b10 75
    0x20046000d0b8038601d031218007150030f0f80008002c02c0c2c2000703070002c02104040c00c01408c0f0a600c5803036031101c91980d0081c40100103150301c44940958909040d0380b08004126000d00800020788901a81e004c0c5100307040a176810f09980741ea075142c0c00c4105503108001541c0100300c0c090221112320445038071007407601130081d0ba00d181c0400130b07440344554051030f8002c03c0907054076901038600b90030240065504031205200c0345000c0c07c4c5886554070050742c080009007010041620425010800c0d41030f113100400d0040d00d40c443d40d41d1440f800408510480c0e80c01d48001709100c41d0000c06142a008180400890160301c40080300101204d1450b00038440303542c101802d1102181c02007041d00c40c080c0303890401000a202880711042c1450349402ca00c039081d07000003000704500e078907a00a40742851255040b10400010343e0003d85500f021244912080c00043c8410084515103211091882001c0c5400003250154400481c40c030840c0e40f040e5a845c161a403440030031500303100c003034800483c0d26407074603111150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 942068974 1250 942067724 942067727
    0xa061109040b0109240c12080610030603020906060a1b030f020c120c04020c030c0a1109090303040f03030b180f1b0a08011a040503061504060f03020f0d17130f1401 72
    0x1103004011a619903105d603021080c890060141c10505600424529528044003100512a0408541c00c41c05400c0600107011036500a01a450540354000c1c0301d0081c1e81d0b02e90043c4049a080302ea2410b0401081810031111554902000c40c0207a010360354034000d02c0c1c1120406854017480707107043c83c0500c00d004101c12012101050180306400121009a5140b155240251a600441c440d51405c0e010704070015042210b0940d50583c08002178585d62003075910003004984900040b1405080c00340d603070909500092180c0d102d0034070f403080103041140d203102d00000f041642c031085680304201415242409180f1a62801c0744264030076405d20740707207010403454009018060600c118600c039518007410715410f034070410549000e01070243c02c40d0818589044044241e401110000d0f0040749841c00116007401c6048000003130304c0e0007a011000001204060000003001054240c2d0300204561001600c900c504004086090b43c605401210608080200c2d0303456200342d0208011410b00c407440c3d900ca9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 942070224 1250 942068974 942068999
    0x905060103021f0c020d020f12030406032a03051b07060e1002161101020a0605091608070515091804050610240f17070201020a1202130b0c0a061109040b0109 69
    0x558195180402e550791480030804000c14928031031380c271044c4000d02124680c00040034004459542e9030611006a12445406406010061801000c1e1000c04142031150180c5c010a800540150250044d4a041d100940040c1c000c510100c80c0c603034942c414800000000c0040403280804103030118a044000b00c0d20700740c003c096207401001015803820000c0140e009110160700290010402d00040c5040d0050640b80d01801d000f803610b150300c4403408030342c0600005a55007174a00c007400075007144881808128880d0005403409920480d22110041c200d0090b040d4a80103601c62801421079040c0420300002c0205150440c103080070080751041ca54102030000200800070500740b00c403104ca24030f03600b203c0c00d440408100f00781010804c01d22001540c1580186034004565480e0000184130616a205034412040d205107030811220060018021280003010601100800c40d8202e011039607030007056503460410f01d08061004540c03490705090030301641c504031409281c5116420b080c805403040c607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 942071474 1250 942070224 942070247
    0x71104060815090102250203151b0c0a0c151d06120403110a03080916051513080d0302030a0b09060d082109030a0201110a050708070609060905060103021f 68
    0x2458495012400103c400e5044170b810703007000c0605500014a2010304094081c41c400203c0c007174403803080008940140c4482c003070b000d555071803020200d40003d04818031081d00b00d81d0f088040c1e4000d0f09540b20000700c0c145c0e584c2000744504161503c441004c4200507040070030590714590300b52060040c1d43c00c5ca070307910401c9500c0e5135a1200c0f500229100c41c141164080d040c24142c2003548900041081810f8202c030300c3c42d10543d40e01003111004d0310440103202d18140588278043d04942a40840c4c50031b500c6140160464124601220b001e40340d80d940514500343c408248100801c3e800001c0c0601c5c094a400b0340000d06030103550b5103096082100118000c0f1250bc03001605554002c01c1801042070724000c000142d4010758040c0146042240c00303030b51070f0392080c0a202c02542c81c145045c008060084251401980640c548a040c041d03151038a219a5101260461b840340c5d50f202c441001402c2480ac1d1501d4900035001000e283d030540c4140040005c4000c10307030302c1400a044485c541698010206030741e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 942072724 1250 942071474 942071503
    0x1906260a0c12030c0503030f0405100c02211c060302011404083c0c190612022b0c08010806060609120a050322060c0308040b06031c050711040608 64
    0x8407102d41000c039000904560700400d18040002072043c0300c4440402c5a0003680140c080d03610390080000354404442e4800c04580c05600249040411700150780400c0380d61074000801c80c6d190400203104480d000d08220707850900607a5449090055592201650ba403001b11415110314042c01c1000b095518800b04028000d4040c1c2c10103550903039804619021084500c1d140d803500300c03060942c0caa41e12180b40480e601e0150712881011041080707100d1000040780c605454928020140440390000307588500220407e8112003484809101229019800305200064000170308009805c2c0090098406920610080c1d2144080c0109a42c800c0111503408800f258072a00024907034138200d0501c0c507807a5000e0102d01001c21207500c100080d0400c04414404c181880c0710b880c3e00c0d031009880b4040c05d504c01500082c05000001d001603501703408140c1101005044601c510148081e15403950001d1080c1000504041500805c1003400700700c0c10300220088400f4041c0701d003080c107100e0799400703800412003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 942073974 1250 942072724 942072749
    0x8061903020406090902010305102409030f030e0414070914030c090406050118020c0a06050a0917041d0411040903050f0403050105101205060f1906260a0c 68
    0x8002a15000124000d560103070041c08103595403c81030004103540c140903408641080e000038805c03501c40c2e80c0c1001786e404840c000030040191401112002010366804401d000400c01c021002ca006003a102c000701d1f2003075980e03044c00041403080c401a26001101061010502d6080c000001d8019008800b661200c2070b2000703f009c05d541c0000d1800c1d0300490b203250080c0c1c0040600c02400420340140d41603510200020188500c1011424201d1088041006890300a03540d080700041c1281c01c000c2c0c0040c66068003140301c4940f616508108000c80198582e6404002810080700e145c9081329940d5003400013842455203010340301e99000e0126000000c0c8600d60720628101010b0190058030100c0c100c103c0b119841d40e849140032402440141c9d5940c04641c0881000030300a4a603c10440100340d0200c0a440b0b2500c4001c00389040d1040506054880001801c07844182003141c0b043c1d40052600300388415005c084a403460300700c03030b40307107c14003100c0d030040c0999002050034036205c1000c440303000e88480c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 942075224 1250 942073974 942073999
    0x4091b0f0e221a010c1104090f060533090408070501290f1c06090620090901050108010b1803030d02160506060604050d02040509100603050f0606100806 67
    0x20b0301d0129507010860403002c00300c0741e0108010a54440180340c80d03c480380c0321104403090010340e400d00030940002e00d480008804c40b070799401c1a0b00038840c50340c0f288502c410401c040c1d5441f50203413841150018803411020402d03c03900c1c41f941c09101c1c0c00780c903140e06030240c640070900401e0000d600244090b1044400040207400c0000035071020403d031000c0c007032030260440300009496106052000c000d11075107910141642d18907007064942d4810110005c003400384551076a41070b018200804003a194140d80e01450102c01442004c1c845034541c0d480141503171424804100401c0c903106800090400101c140103109042c0003800b210180c1d1070580d60560303e241c100002914611550003408042d900110b4800705e0950744400d491800b5100300c081c0d4003da075440050010501452182c82c0d0701011052906015040c01d1b48240e4100700088140d941101c0d00076080011340341d25503c00c58003513005040c030030071000b4140111500100220b64200c410326004d240101900e4000d0603140c03103420b011605 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 942076474 1250 942075224 942075229
    0xa090e070e01030804170102040e1302040b061c150608040f1e2d020a17100608030406021509100b0d0b010b04050415242304091b0f0e 59
    0x554009141071000044039607140d103440065500548110f03c001d01c03408a09410441060007075405540c0941c2e595149650f840000c10320700854014160703006507480d44981e119484c0c0340020101d280b0f440001e8a100100c000606044803107609a80c4600c559602d414003456903c82c10301c03030700640c001c915207001d0071070307800d10002100800b480030740d030003000e0030992042004d001c0403103420000c170f00001c0c01201185403040380c520b400400001d6200b070000101b80940300502280400310340c02034040325801205682c032a001c45001e500900003551000c2070402500b9410400081254048413032a481401c140c0803143c0d4940e03800e003019240584840d01c1000e551907070ba4a4600c410303084000183c076541d41d50000c40c0d19074002c0c010310380a80d00701860010780364620b0200c841241c0c2d1a02d00062024544400c040c4007103094040d64007041030114030442801412844034800c11200f40e80305a46900d00f1610700304a4550303074001c3c0300c41800f141a240342c0d147c102d1065014104542480b00704001c0a000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 942077724 1250 942076474 942076483
    0x41a03040203030f0316030f0b0901180204092a05071106030c1c1b0c030815040b0a030503030a0c030605030303181006060224100b070507030c0905060a0506090a090e 73
    0x1c44c101d04010120030400400c2d0620101c0c94041942c0c2c901b0412021100072100560744007807102e94100c0001e170010032005154641080d64131500c0c010041c2030a46a6080a055a01000740900c41d9091880e0880718240f14000320b00707000382207050440c90060141e440004031503644052a200c0c910100000d02051043d03011151091a24140d00380b00c010300500300030050000c202501c040f0341e1511300341d410540c01100091031a41e0035032942c4d250356032856008141c88010100c65500329495103400712864940c1c01c038510185200b40c000e19140e03e007241003901241c0c9050800b500300341c03c0c0790040201d502c0c040100da400c2140321134480d401038844500c0c20b2030070001c0101d0b640628500000081c040b58040355441803204600d03030718415400031a645c8050780c007041e590840122444c0380d080041c00714003001003004a2144081c2c9207095a41d8840300030740602a40f102600a89600c10401c542c0b40544184024000490301d0703c1c1080030b82c0c0041000b1000307a008558200d1b503202c0c8402c8140c0d00400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 942078974 1250 942077724 942077737
    0xe06041a090a0b041b08100b09130b0d020904080c0c09240a210510020c06070f0c0804030b01051f091404020c010609020a0f020309010f0e180c0a14041a0304020303 72
    0x141c0901617155082c030082040784c0440ea141c17084e1044100100b40490500308882400b0001000d440c6181d040030003210050007952142680b100d0074034150001a10b1b0007a101c3d205a00682440f5200c540718006036007403c240150251160300c4950400ca401140005002c8810504146986030a0f44602c08552031054a421040303002ca0b511000d80c0d520340c4030790701a218103031240007030b41c101c0e041041416050380a40310004105801c44c0c030006070f81e140301e41f40400000982d440c1c903142c0709403a6155000c46501031303001956407960120060010b400d0943c440612a4002da601b105040440080100842c41a005440c40039841c48602d82e82c0755240d406440035410300100800a80b650799002c01c00940c40300d892031003c104910307071444e4010f001200344c03203480364180c58070800c840707402508032410300c2c034900d105030301007402da440081090540341c2c05803007184200c1003941c4d161032400019102c0c104406004200a004100501440000c02000c03440b14180784a5140c90391110300c00a4190700640f07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 942080224 1250 942078974 942079001
    0x90f03061a090c0d060506120f040f0b040b01050103062c0603240f06091e0601050708070309182003040f080f090406090c020c010e0301060f0e06041a090a0b04 70
    0x50140f041d102004001032600510340401040792076620001d100c0c1500aa45480f16040c40c900e0000390019040035042d42d10910032556142c804125584102d00310909490560b400d601c1c0200500155030135100d4600034100d0314035408042e0f040900801a01c0d000c502d0000002003411717022403403d03201049400c80c04024001d04100c56510020101c014490403035400040e440382201051603401c00c5101c3d58040d0703555101e1078032f00b0720702074003001900d0b00060105810044100002004903035850060070000740705e03a884503080d516010050410310061026001d0581c0782c041d1404500c0044940004250301c01d401c116203954640c02c04030010540e43c10701070040c01002405c07101402e40000208125081110100001c0f48c031059040c0c211040c0c042d100000d41c0c0704043c01c074400c0d805120181840803000300046400c1c0c0c5c80c1d401c00c01071040300b40c1c489641d50300740350b06014040ca1309020304010a0407600074160001c0001c1300040316240701819034020715540302104c0b01591540e80010341c41030080e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 942081474 1250 942080224 942080239
    0x150d0c0908031c0605012309180411040f020a0e090c0405030106031208010803070308150d020418030e0306100324060b0a20060c0c1507021c090f03061a 67
    0x2c40c0703990044803409101484490f450860003203a19802141f1091801079451160401c3c0105068644015070013403111903800b1141d0f11040001007590044148500e22403803241c408450500280410341e80c8299103a808030740184010b44020b5800782c0224403d0740212103048194551140d0000c0c01d20a5401c40e68255080c484044207001e04503c0c407000c581c1190781c40e540e1603a40c034640ba503141d001d5030600070700003024030000c500814460380744134604a0008010f0600351803254000f504584040b441d01e130009061490032818983c01003d00c58030f80d0b20940252105290191001000940c43d000003005101b02ea001c4030104411030341280203030045003100f000002c5d120540c030403050308001c1405000a5610000c0b40700a0001d00d50fa046100801d80149542d48460079402e41039000345880c401a032188203c4004011a400100ca002d209290058031860010300c10034203035900a0100748050280000c1d003041140e010b03841c40c0782100e80107100003403080f81c0318911144080310654504d510088 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 942082724 1250 942081474 942081487
    0x906040f06050d0f03091502032b140108010b0d0503031803220f1707140325050f1f0c0201030207050a0b06120c03061501050c0601090218150d0c090803 67
    0x242441380b4210580280c0720703110815590380950483d181d8014061005030400e0014810191950b14a1891001e008090540300190283c0c0c5108440d80c0500640d41e44820800400040e103083c401c901c2461015100c0080d100003e40b41c1c2542d80c400945917005044c0394002e01002c0186c02d1060301c07034000015200060210406110039a06501c1d401690024505d5075000a6065041880d4171100071011000d0030790540707001c100d8140d00d04c224107025014020010841490540d2070303607035200703080c462056260203410300c401e12140c000a01007040c0500100c100703000381842c1c071040e410001752803842c00300c0009441d8401200a40076041004001d441b582c51003a082292010745944141005c0c0c0301c4809030051410116600c0d01f80c084c025804d0b4115a010030701081107a109a4848403041c10300c00e240c031282c881090b01d0100245d100d044081d9021030300720114012002e41401110080364407006200041d00c1070303241c0e4400d54800040003640ea10140060300c0c05142c226008241e000103031b036120384 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 942083974 1250 942082724 942082733
    0x212210f0402031513020d080904020a1106060a0602061b0d0501080606011e0f1803051516230306040b0418212c0604030c15020c0906040f06050d 64
    0x1080e14202d10038081c5130024002042c00c3c50b5141e100700711206102400c4c401c580c090000252a40340141d500540822222025444900051840c00c4a6070f44030250b24410031007040c2805009000a449115510130030041c5c1d650006915402130010035a8010315010421009054400c09043c1203041c0d08000000511b00030104a241c070840f02a214031a07542d801101c0d40d51184150000b03032001c03030380c1d0411015030740d489400d01001405008581e0015680c50f9191140342403000004420010345280c20040440002c1004081c0c10000c5d040007144000d84002440070341c41311b2108400302c410084000745c0703a42e99507001110071401c06442044240c101c00843e0011205002d81a201d0020401c146000409001c4c0d1084404c0050390b030700d42c4e0340c224100001000d99003100d08004002c10548403910380b0390b030b1007000b800158810045841481e1800741c442c2c83c8000082c040c5001d540280f24850120b07218000c0780790b4030040c21500040c1400300320030500b0041917181c0006070801d0030f1080b20001c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 942085224 1250 942083974 942084001
    0x31f050a1401030c0c12050c010e0a0c060f09030b0c0901020a1a06040b03120d0c20060105090702010e071e091805011b0f030902041d01090c050301020a021221 70
    0x80c1e100780d90501074400016401d55072034850140c001c05c1c07404000e0150100c41e02c104050704180c451800041550000641a50729007158a4000d440c0c4800d40d000420075550081c03620717500400340b07040100c3d54034950348607031201c40c000602501e400c1c24000303030140740c40e032080c04102c17070850340320f00800d00c140c40401e0064100c513422108180902e107800700240f064500091460501c4102d035020f249000060b1f0606805060310828003000e000610310140006941824690301c80a42c1c02c00500c427941c5802c0802100660141280c0c0079649030003964100b4810105080b41503903400d9503207140444420442041c8103a0a900400d4420b15201784c1c890b45000da0800042d41c0c50184000340262a48070302404229080c0c0604040070511211502c01d50a0080d084820554001803000410300003030080404000e1000c2100e444595403020342c14201305044440e00013030807083e00214200003c0e030802030750b00c9001c0829070201c000c010030104031400c0120201060400328141c030074034506001080200300b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 942086330 1106 942085224 942085259
    0x2121917090622050a0f0c17061b030106020c0d050f0d1d040b030a060e010603061806050a06080307030507110a0b04060806031f1515110105090f03031f050a 69
    0x30080401c120a008c205540f02030801480c0050501d04151041040b401c3c0b205028001809807580c0010710304202001690503100301c5410f810440e141210222028200d4843c2f46107070060540d001410000300e0b1000c003c2c07100c0340c0712071030104403d90707407804038141e00766220f5140100411519001030100e0341000c1e000041c0c031612525110185d80b078849010b12150b0000c64030380104001c611800d030b40100400300c02c012450600a0190303c9204144000d403c00102050710702c20b1005060b0b08407403c400052448101c141e40303181080803034200f07119200104d100400014000d04000c5644d0300040c029852401009500184031401007095840c076800c407032110740e804109c0809400a09807200e0342529281e8944c443d2101041c25204020050f600d51b41240c00c0b2100700404c000b0039a5040b105001c215000d802585052104001d00c40c2e0282d5440845010009038800e03418025595 = true := by decide +kernel

theorem cover : BRFrame.Cov 941906474 942086330 := by
  have h0 := BRFrame.cov_init 941906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 941906474 ≤ n) (h2 : n < 942086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
