-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3462
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:43:58.999707+00:00
-- url     : https://prove2.me/submissions/9a090f4a-3f76-4f11-b5b4-1a7af87aa3df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 622482014 ≤ n < 622661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 622483264 1250 622482014 622482031
    0x11070807030803180c0f0d030c02060a0320090a0b030c0d02030a050f0906071d010207030b070216090606020705151207020d1202070c0e1b0c0c1c171e12 67
    0x611104d4a28400420340784e490103001460360201c00c01c04070920081881c1800150103008420540341d0141e1105401440e8581d5141d90003d40a00410142e006005001c44045d080d48800d200c80b0f51540c455030440c2c0b0035510390500070368880c3d95840c1d01c0e14991046050100f886c500101c140036551585801c49806002030300d104112030b076149480d4a46e81c02e42200d04900162814000241c03001d00e80900b0b120080061041d54103040c0c80f03407100c00344204c0075a01100164084860000e4082c0701c55507190107001c0e000f00a0240601d8500002c5d601d070520700916200b10110040e840803044c070001192400e6440403881e10713051030400b0780030351150000008540450103589001ca58030f04603108030342041e503100621a107440d00b040382200303801c00d0040c01e0103100e09804122090200c00440a040c591100c0d000600c02440e0582c18491003104000e00c01155000340420140020380d00d0695117146041420401d4440b00100e2512010000b840b00542240340c00140051003405180c100500c5407440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 622484514 1250 622483264 622483291
    0x3020a09090c0b090f12030c1513030e040209030a05010e1009080712050702060d09050c0109060f0c02280923010329090c0a14010f11070807030803 65
    0x450040c00107551001000500700c44036204140320440f00840604030100018000c4900b102130341c2c0100700740b00c03480802c00030300e94008984074031405020809a030501c0d02141400341141002c4c0ca40c4115601c2a22000f801d0000d090320114854480e07a042e00d20101005041700c031641400d00307105008065504d09071065002d00840300842c84000e01071114002d0740486006c0c03608040ba240c015000d44007166207001c0000030840c43d40136a80d04405040f403101d00784030000b003466851a14030b1800440d0200241070050000003040810b400c07582c0c0c4140c00c0e550781400b02c09000e00d032001035802d00d810100d103000d41c0e81c0d201c0e64810400041d02d4000580e40c0c0b10000b0440307843c0e134140007803140051103090030f03584242e00018800200c284c036920381c1304d810001c0034642c8000f0201c0c50401c010002c45140050380d200088401040c0b400c071aa050041030031254009200902c00b00003800401c2c206c0c643d44c140714568a0202e0020350400640c402000b000d4103031060913840303142584003944291084e1511558 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 622485764 1250 622484514 622484519
    0x91212050a110702010503040219030b011502150402012609011406060f0a0f030f020325080f06060a02030c07090902120f0316020303270a08060603060606130b07030903020a 76
    0x20580b1a01e00b02d030050b180030034104950390740116442c0e400103204a82007000324409c414403581c851024005184618100c48896050800c0030b03883c0381003071071850115030000d0405504009440d90711358103d0b40a1a116080b4000c1170410305440b0400e02181804040101c1000480d9506504c003c9581041643c02051a01d0f80e0040041c24000d540e000801d9480802400400e980504660a034002c0d080c00c02041e91411b0039411001c83c1c00454109010068101011080c13100d4880103881d80d65260034080018200956600c0c100000101050301601001407440d00c003e001302701b92034884819208860320300e03880e90700c01806000c04541c124000e858910119400000105000e074080e070900b0000c508180c41c54152120316028401c00340d030540001c00600e0200d42d8062180114081040c180314030601d501b034181300030700c5840d5109030240e4001d10140415a54013113000c641081040b190142c50b2002881c0e4241d0548560340b1202e401003000481408068008a00c14100c038000c84c0c03821000c96 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 622487014 1250 622485764 622485781
    0xd24080706020703200a1e05180415180605010305010608120c1b04021603030501061103070809060d180f0c0b0306060d0c050904090606050f040903200109121205 71
    0x481800000c00c00500c038540031542d02140442e901811600031328407402c42c0e80d90801c0000c01081d00c1c0c11038200c511f4000302442141010b40d1100082250081080828030f09a12540b80c03c546800018184a0f107540d1320170078080c0010218904660040d200b00300c00d5030740b8078205008107028824104140202a441d103020b641d01c07c252010b90b10340d01e014124032703c85801c1c4680c0c0d00c0c003520380b5283c0c46076090000d040009120340065140c2482510300090075410200013a200c1c03900b6900c03041040c1d204100c40f40014014005540b0160002c0e03d100b0b0316650ba0041c1ca00c040d14a50079200300d61041c1d6030a103c2800340a1600b01149401424800283e6894000032140343c803080b41e503030360002c508008580440c20a03610180346882645040c5040c4250000060207890042c181952080e403141d006102c0c070300e00035203035646000c400c807410003203803096a078050a030400702000c004081900c091102130307000080d000818107a81c0013000714100d441048001d084040d095841d15003451401c00041c0081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 622488264 1250 622487014 622487023
    0x51504080a0807020304120b0a0b040605010c0b040c12030210110301150f031508010f060b1614010b210d0c171c0603050f10110409020d2408070602 65
    0x110380100c112807074508945401c1e101078002402410442c841004005607c61401c4110003c2911034111208103040c5a81040292500204c04a10551814a0070045603800070040a145035200d071241116907960f0900f100160410b6103c80e00c0c80d660000d0040816601103a031040b10318a5200030031040d80700d0141c3d0700b010f010034011040c14914140c02c4101580c0100c0d80074540c016145004138000a0208100a80c4003055000702110780d1074551056031032065001e182e0141110016090070701002680e0ba0601d41903405c0058500380c289074091150001c01c0d00204080d40700a800941e908425980010464101c5103010000d8010504c0c03000714544144080c500950300062140b03e00c4013420080c0d20141c0c02017081c0540507206500900c00210203008070310056010f0f00160002c2c40d8a855078031f0406030b04008582c01d90785060312964000816000b610709441800e0030042c0c403803c1c600b599100a15929411075101040c0b00030030441c07004a100550141d4003100241c030351940e41c8000c141e945 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 622489514 1250 622488264 622488271
    0xf0f05040b030106121506110f1b010c02032e0501170c01050a181d070203032a07050313080c0f0d060f110301030f052b08040c170601030515 62
    0x1c1c01c100300010000035101301c1c0854092510503e0000d44002c0d62194040100d030341e80d115002084144403a442041d00c180701ca079440640d0b04016102c080b441c1d5540f60016442d0010181c1840404036500c800c0d901c0030815980c101400c4107034aa00400041c544c1d42100c1141c0102c110180e003000f00118940540030b081816403102d5100502d0ba82085c40d00541c2c1c2e640002d0140c00801c03821140071408c40c1c400107900e0000305000003a18a800040840e0324403048001404101991f004209002e454000c1c082c0d04805840f080041e10300904540c00400c44a10800c0009002440041a050b041500341522001100d080000f102d0443c1c0081d17041c0103c0750240c078103456000c01110748850100d202500200c0070094066400200c942030913802c00d80540017a0002d99980040807103c0080100800000c98290311000d0207100407411200041000440c0c680e8460070040ca56000c1003c11450480309405000d180c03044900441c0d5400071190351710b4091201343d07041d00c5007000002002c185181c07100d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 622490764 1250 622489514 622489529
    0xc15151203121f06090e09010b01080106050f121611010c0f0305041e0f1e020a06050a0315092a0905060325050703030e0619110405060a0f0f0504 64
    0x40920b404541468480c0042c003104607241c4480300c402d081c07001c004964010300302c2d0741c603210a40d07424080510f110100003044070300701c1d170b140c07003506111030703810591240c1151301c00d20f8044e64030b0540c0d41d011070305805410646807414030b01c40c007030004404011402410700c0109541e614030950b0303507845490030388401d500d244010442d83c2440565541c8680c110a40c003600405036000525042d0640743c43c0211140d4007680d4400c0c541400340200040c0a003c829121560002d4130a0058103400113415400d040c840c48050250001d51100f40034002d82000891110a0f0b148071a040d941d03802544c044c1c020048100c41d041c1c01e400d14808000c008025000c443c0301265110b0f803549050200788607540d400075015a2014641c1c202001e0407500c8003c41045c040b9036a92201d031284c40f01c0c6006010307620070700d180c41d416800c22010407410302c6035250441c00340300b4103190214204c035101000419600c55a003040390022070000b294100181c0010044200f215160303030780d000d81c0b011842c0440751130155015402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 622492014 1250 622490764 622490767
    0xc110415090b01050715090b0c0705100209010e031c2d030b150a03020d0606170402091e010b040f080d0c02240c07171b040903050c15151203 62
    0x201081e0780d68001d8020250605000745808520f480307034040116001008610360392100040401c200c50380d0102a00b001400000c2d031300f02151642da541d00c0e079801c040e00d1100c240d40443d0900c0240e200d1018074800c40700250075212a112210050815903101400600110700c0d0350f0391103000006180440c082c0e203c44240400b8200790450f0003103000d4200031400d00d038404590818005100c1c500401800da040745901c0c0103aa40c0c1d0640912804d0706d20580c4004240100d1010102c2d00300444111280c0c002d50444840f0840d603260102444100c403010681c200e060380c4100081203030019078004009540607400028452030b41c8546850342c81d807000301c94000254024520340c0040c1810007400d0baa4030100500340303507403000022803a2855009104404155480306004100007903200d144042440c4a60b0042c0461490090701d0840c4c0740030000d03080e40915030b030b607008605161292042d18100c120a10998002d42102158003200c2c074001c0e125035051015100e111001071410010f5845084550030107903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 622493264 1250 622492014 622492019
    0x1b1c09051c05030a0201050103120908030a120e19020a05040501210c0b03090c040c2c04060b030903030103050705032a012304230a0b0315030303070c110415 69
    0x2054406480d61a001003805a0701c0e40c6001440620107081440d115500004907580355003000058045814101810320003800c9090180803000f0003280c820700480d0400d40c40c40c0100311118002001d4040e00d00a8500655240c000008101b00c1c00c0320000c1d0007140c0c445581c5466004010841d45c081c4a1102d10304a21288581c000b814500450000e034020801c0e4611207607a13011a9803181e2044601041c03a800c1405803c03801d01c2d082c07282d9a0030008030724200507001044e80714040740000c0301842c0310300940048030842250303546800100242c04000c1040c0d880f814190045540c0381c00a00003240d00c3d00400701c000c00c4504000500010441c4c244003001d414500301010f104a03000d100400504100c490501d046221040c080b1101200442c401c441da511460700e04001c0354400e141c03076161140c109803444c0180e07a56500028505680b030703001e201541c03902ca09290592280030364001940502010040162190300015145070b410300801c40d03c02048000c400700400c9907001c00c94400d1801200105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 622494514 1250 622493264 622493269
    0x702030919050306010e0103030f0f0815040b0a030b1815150424080f0f150613060308090405010b1914070203100c0906050a02060606070c05061b1c0905 67
    0x1c00c0c1036070140740c5114840b038076640403900b400c80980040c409071900300c0040080582c8141c00302d40385510b0b4581100342ca845407000401c1040082c018107040c103d0441016019a15584440351202c0c0c01041d100c0c240750380b4613080d845003c0844403c41d201020080b0204084804942103011081940c1b8105566880e2100c10348101031002c102500255505021118480205104d0403185610066102c41d5850000c003903281c0181da811a000c075402220350070b906d07000c00103007500b000381c50042260300036070300d010220b00c104c0c210440740e2000e2401c01c480001401082002031940c60710584090080d0380c2c84825070600c1d4030455100440c0c0b884481c4518400511071017584001e40c510b81c00307483c50680c480c1c00280c504601425034140c4660b55401275406a0340280f500001400d1a092038bc1c24914140302c0a5114500200842e0044d8400108070782041301c48400440601030061107203480b01da43d500b0031842c4042850b440d160511414080400c40707034a004402d00241e2980d950740611a003820107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 622495764 1250 622494514 622494529
    0x10060e0a0f0e04140a030e03100b0d0b150325060e010509090406060b1308011a01050d02090609130b0102060f01141513060c0302161a0a0e06040602030405120607020309 74
    0x140d40d19030b408204100840c0e0140300c1c850545e40265152024400044101421b101124041c510071034680070752088280c4811a81280c1a0742106017200d031941c41c00c0c07200f5a098040e00c041a0b0500500c202c3d000c56030021095101000183c0030007010141d01c600082d5628110322602c070340410001d00510340c443c9081502181d00a1250b0300c080b68441e580c400380505900198161009c40441134070500c0000c009100d02115804001d00001a82080f00e001810a110b600c0da00d0341400d400095803901c0d61518011150352400c05031248413401861043d00000300222001c20340180140004100c007030401c1000c1e14162408402c0281e0b882440340108004154004800040e0701e0080c40080a04520605010b000301415203132441502920314000342440d48031202c0841c0f986040c41e0500078200000050001841840d802d16518080e401c0e0541c0d0303c041002015910400004000c182a98048040e0080701d6040e5900389507036100d0349502d40c0b203600c01c44400d00141d20500908110f40f41c90344 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 622497014 1250 622495764 622495771
    0xb03060403090e0703051510170c0c010e060c030c07030c020a0f3813091b0206010909080a08060d02040e1b040e0d0e061c051e09070303080603030f0310060e0a0f0e 72
    0x41c0401300c4401b00c100710909c58030840301c0880c6101c000c198080b6190003030140303e403400c05000c040c149510301800c0541c980d020241062105a401140603010140251440780c0520b4000304280b6105a6074031080443d45860f0054401d5a40c0b0ba01402c258010900c64407400096200d0b040582d941d00005c54580c1900694440c0341d4103c140e5000042c01c0d0f22034824005036a00384507170241c000c034000030042d04c0c040e0183e01244129240800746d40100308050291076201f0f225140c00030a64940c400018607111000c00003030741c80b5207000b40d0800540400196550340070399440314203070341000d02c0b000c00003160a00038212810f80c001800c035148452080c1c8030700700c0c041801030021741014410345110128080101003d1042599242132202c890403c43d0745224004810300004401c1c60400d940503150329807884028103010f0900c010680a41c0d050060300e110507400c05690382c80e45056150074241090506c107402c00324400380b8850040741400300904090303030340321103d03044c00703915240304006001c2c4001e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 622498264 1250 622497014 622497017
    0x9030c0b0c22030203070602190209280605031c080c0d150312180b090f13020d0b18091b0d06020c010222120b04060b03060403090e0703051510 63
    0x70031100c414000444110440c000b807155403031220a0071407060502e80704e840c4c1c02c44025548000e4880115407542400a1842c0341d0584040080351030304c0041d4814403800c580c00002000030590406c0060405a10a07000c60308220115040d4213904d94024074103c00110040e00050800000686a0188440284141d42c2d98a00001d241184210700c080f648140e038008440060403440000911036001c0c13810a5148181500b03000c0c4a850400340306000d00c80d6100c2a030280069490050705950b80214407078920001c101c0039961003811091a6009202d111440ca00c40d4410088449484107032a024600c00c20f2004005c0c1003030640d030900c0701040c24021564547c001c50341c0c070050000540a001910300410020000f5844030020301a0700005050b002150b02c810441440410002408514004c1407035003140705004903407034905110004e080b410130203036003611481d0144420180d001c60103400702e8030109400480c94480060440603600140c3e80c140350240c82035115942440c03d0046500c042155 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 622499514 1250 622498264 622498267
    0x3020c0d110a050d05040609060801230a0902034b0903040f0906060f030c0813060905010c0512070309020a0e0c19020c18160c390909030c0b0c 63
    0x10b5902e0b5440c2050f15904c503000140040360400c012500b10441c00064801e50800240355810b0047c036035010b405411440d0600c460701e44020207181c5460002c003001e445681d070199902c2c0341c00c180d900820b1001c40f88a07014594044800031005007040d0701d604220381c4141d070980e00c01c1c40c200341082020030b000d003070319034140810880000c00b010705521202c001d000d58000851000d1800c0b10260008071559142000e241c10280080344095008400e20307071111100c4290742d0b202d02c0ca420180001c041e801c41c010f20561030a02d034504e940d40c200c03025041c0d541000e481c042c1c2d5595883e9003141520074410000f500060031030014442d040003a1001640000f4001107a42003694003a07001089500c0a580c402c00768102d500c2008a80c00c02c8081c1c807500032100d0300260780b242001d001d81c01c4545000282041001100e82a000c104134030015080b401940700e21007807085000c4118202c6100c005070b866a441001c12401c000350040d030303a0241d0401540c143e1140c1101605a44605c551580300911540707485a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 622500764 1250 622499514 622499533
    0x4050f190815071704020d080a18350c1011030706052226090d03120b0a050108070e1201090c0e010812030c0705010902060a050d0c03020c0d11 63
    0x5003005204091692001d100441d030078203490103071580351520000510801c0100800000d81c40e05464241c240303520a82d02d542d501d1070320004603449858291010400d42b081a40000e545810a0f071b0180f88170b0200510140d0684c114480d40d0014015000c3c2c01016084004852514a08000c0c0080024441e0800800030584103183c1c905550004508a5002d82d8544c1403043c400507500c0e4810080c17111045501d0300c04034036107984801003116101c2c00181040d403000703070b00c00d07502000070f540c1d80c1c07000904031651850300780c07502800c01035035911550003907071506000d6000342c47d0103000e0004407041a10380080d142c55100003110181490107078030790030480b42c02400210b940d09101c1c80c2b2005010b4045020844c3c1001c03125500700030180e100e516140e00a00005411514200440360400154482c5558521076480c0080c058985984040d600c4080400c44013007142d00140146400c0e00c4e120000c00000d00074080507000c078003904015582c1c80e0300c28011441290700524043d41c0f041d13684021240b0000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 622502014 1250 622500764 622500779
    0x31a04150906020705010b0427050c030f0f0f010204061413030203061303080907030b070507050a15060302040b01031406012703080702100809060402131d0304050a0b04050f19 77
    0x7115000e003210038903400079100042c04420722690921941c2110203200c2d01c4001c04000b00e10703110080421000c191001c06041c100041000154600321019090710808600142d0035902d80b18421890101402550244182e03420b040c0308490551703d50343c8492020340d000c2040c0c115950031000031b8464030f0401680220141e07a00704096445a22140c411094001e043e1800400c070700e102801c460b54a40c405001800018840d00c5d20300d030f01101a01d050342e01c40700d01e0304240345004500e910103001c400f082c1c021000050069000f01c42581e0003078a0510001414000450440d83d10741084140ba1038030b20f001c01d15940c4100011200b501c090840c07100a60020303400c2201c0d010300303580126000c500c00070310308007141010301d0f035190001e85c18100748405e07103052110aa142c074801440248103201c5404200103024075540b200400c5036a200201c5081e140d10b8015641d69405401103501ca045040000034296000c10100c500303075140a00321184401049081c0001040340c101201030500308a000450000b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 622503264 1250 622502014 622502021
    0xb040207050f071505030609060907020a20011419050d0605031f110a0801060311041223030c070b09010201140709140f100e04060f03030201061707031a0415 69
    0x482c0000c02030482030b4a440300050300e19070380c04048424000309104008041e40c50000956102800740d0300f9180541c0d0f5400e040342852540c2100828031071100f0fa24881480588445c0750804d1000e0b01c400e640f614080083c00350500a200240024100e002e0b803032241d8600c104042e090280c1600c5010800d1a11400048d08000e4910100781124980b00342203201e00780380f401560490040180c0c180e20300300c1f1080008240c124140120b80502d82c88a00c0c03840921b015008540080c0600c0404104054052608065174a61068002c10111002d8a403854642010049601000b00e8100030448180b40c81030f41641c40e00000241410f5558070b04a50600151000400e442108a0783d00d599803582001d4800c06402540b400c118041d00300140e904901d511040c118509500742420122040700e4498000360141015400035070030303800c4102d07002041540540001040c0d0f040c02c990b00f5070410044250607501c025034130001d0600d800340542780011501c003901098000d406811541e034806103500140081c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 622504514 1250 622503264 622503283
    0x60f1c1103011104030503041217030406050f0a0b010906080912040806220309030b1902040602030c0c030d05090d060f15080d0207240210050c0403020907050a0906030b04020705 78
    0x584055000e0360456180030300c10b0b00760702c1c811000340d03a04003819a10307907075a240594000c45002c00004d03030520301484641681044045a05d0030400d6403442e061a214024007015100d1500010300d1002013100c0d2241c501558901d1601a51040300c4d003840c1ca40c084808410203442c2800c180520309140b00a201c4d0b0b50b0060000c0c100010040540b410a10603911460015901114044140c101004000b9600405007400c03681c0010800d2102d494059266400811444010580d40d1000030000340a035004009010b10450380016100200441020b2644800e0200d04000000e0801c101440382c81c0b0b80210031030b168901510000624980121004084035020408102c408880e007008224000d01017200c407204030050b101a1a031035140c00c0d0050420401e40454903204451205201e1426100700860034a40c1c203442024001740c101085940b81f81d5000b400143c1c054518103001855186c050811500741514640c0c4841c01c403032501d5800c0300241081d4440c294041e03000c006c0300b0081103041100040307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 622505764 1250 622504514 622504523
    0x110a021009021e040e071214030a0e1e03010c230418091b120b0108012a0e0d08070204110c061306060e0a0c020c0a0f050f01140414100c0803060f1c 65
    0x40c2c00380c035023001c6040c10321032200ca5400303900801c20a00e03540e5100b01801842d001c00c8c4d03001050f100412401180651240305007640540c03078003a00c606113580c8407408024540c240701601c000040b070501100340b6440b0f1402660322a01440780188100e40155100e481882d01848128809001c5000707480d60324803040d4014a4050040344648050080d800c805900400001c030003001031940003c0060400c07110b10092140c0c0243c400310b0644c56a000d6011946075202c010504201055603140c00c060f65080988285c0c003481c0303400518901200100300f02d070304103884400104901e6840d140301065844180404030340940d200c7c0000109013241e0740c0903c3c0540f44021740807502c2c40b42c048001349441003056000b032180801280c20020400e8014804083c0c5405070381c56960f0358040d800507070345003a80104400e0302c01c10000740090340d001d01d01460664080100d070004114810502d0031152040342c4580941914001c0010901c146003589d8412030640c4068042c0c0710448504c120090944200141a035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 622507014 1250 622505764 622505789
    0x170c06071b030c0801021e031302012007091b050301120f0206040902030f090f0606060901120b15180312040b07060e0f010902030105011703030127110a021009021e040e07 75
    0xe500313003081c82180300c034440c45c0000e06082d4a08081d01d061282040c4270040d060190350401c0c03c226528401406050503000001c85184550710401c00f0f0041c80c60506840b03020b89540401c51100f8842d00443e8102d82020111009a607a191180c202c480c0c1da41508a90100317081000080e500d0490004e1441017000160606040c605800d416062040c0109001d14907080a01004403580d42c01c0d090705c0310643c081c6451000040484c44810040a126104592008180a0134003510511070300600200001001030040c403042c0805050f47d034900741003505030701d4009000c140441e0381220003404078075000d48008940090840100f0342000d01c03103010f0040c181d444000440941c01d0034020640180a2118003100502c0d001d40702e0394590006015880340c0c802c044004c0d01580240380d2007a090131144180c1004010b4411201c51026802001c0000241c0681d0b020780505007030a120366040b2a4000d000400004880b582d40c1c4144400070024560041c0e40340c0680740020010004540030380781e5482d442 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 622508264 1250 622507014 622507027
    0x1a1314130e1f0222080d031401031403090d061b0206040203030306010c020102070e0901020a0f230d11030f060301061509090c0c1209170c06071b030c080102 69
    0x42060000d100050014034188103008129010025034529182c1e00c0880c41d4000381d115503903010180c4928443e61076108498898400c00050131680c1d50110b6250404440d80d038020003106400f075400c0c10160900010fa040c0c01013002c80e0080c0c2c1c051003401c0300f95040c4c0b0314084510f000a0f07241d0030740c0041528065600d80c590140190300043c0101d00c06c416000400c60340ca02940080d907248001080181002007200e025021079000300050400f030810940640c41503e0100c40e5103000b5000341110000164001da0040a11030103903240b505201c1c07040b4a01303420280c0b04603620f5080d5100c8070a1139080d968030300d400448911108055070040e960365020b80703190f040c1101050b09441d916004034444d03111084102c8007980d00500300308125440c0c4040420b03850b054507030550b00c03a0110000076280540b5440e0221000b54400d10344070503070f145071880045043c001241503950300c04418034180c00031020091000842c40500345032807041c00064221400c90303103070b03034401060044039803102110b41e4012400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 622509514 1250 622508264 622508269
    0x70227070212040f05060c01020c0a030509010306060801050102062710090b060f0d0b1003020d08030a140c0d0b06130602100b09060d140c10180807030c1a1314 70
    0x50350301042c0c07010840307080c00c3c203050106901115502c11365224140008100c81a40401e40580e0a800c0d00c0c04156035001e58141405403560784103104d2140001d01c0c00704045901805465464183d94040c0e0040040307a03164042600c4004011400f404811000d910000725003000f0402d0040044a5040104e00f0103000d1400400100e4043c0c41c8502c00d0f1505025406981c07241a2008210368102d44a6445904c0fa140b4804200200e038001942140c000041d13001072010102c0214010030490b40204170980102d090020008403e98154111441c2048081c8801a454210182c0100d001380b99a15210108076500c8500c0340e1680b014000d81c20000802101122520885440940690b5038424a282001c00a0140d400905005040d81030507019211640303800c00c0316445120018103000240403410401a100d06101c65041c6100c082242001c108041c012a0040840ba40842d071000d6050a0080081c4901008441034180c1c2009010f84140c0e0381404004900810b0a0030117a0004c10303400c0f00707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 622510764 1250 622509514 622509523
    0x5120a080901060b1e041d0609090a080306010f030e0706020604120e0f011220040f0605070c0303230723030901020615040207151a03160303050702270702 68
    0x4206a490b00380f0400c40110902c0c1216071000302c003e448090107503400e011460500854000d08030801d200025000c2c01d00540c07042a00403d03080b02e002c0b180340c0d81c14201a607650300c2c60a0003070208000740041a55540248141d000c101c600d07040120b8449590780d01286007840c182e00c4000107034460800d201c103118105805c800b40c090300c1e207000801001124081411112000c0a0604200e2000808c0b495100180c1c02120020000141075104030070000c060b08444c0c000d03004442c458065030100142c40c5014400725030129502c0800000c0040ca903032001d0b0b642101240b03182d402407685c8581d000c5020351500081c0440792013401a000407040390601c01c401052115440070f0541d0007000071103030a80c1c0000380d407680841e4200550100d01610804031b40640150340c07004003003c00c1c404030414106282d41206003050700074007142c0c0040e9501000c05940c0c0c0b40342da0182880010040c030a10100e44650010801030340080d1005498441c1d02c58002401c16542032900050100306c070605c40c5e065410720 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 622512014 1250 622510764 622510771
    0x302120d0329060a14130f080c0f060d020705030c03030406150e0a050604180501051b070c03142404020108010504021e0318030a050a03181104150305120a08 69
    0x10603400b0740ca80210089506103481000c079510819001ca914050684a080c08811414900341c1d000d0302c0d0382c0300b804a603203d1941c901038030194680003000401d200100052858507075000a0620741c8018649003440016803042d03103841c480740d0f0200510740200d80c0c10401004807010a800231940c1e850b2a081c05412030704c0c1c5000e60a07070f45040c20420403042e86214a8141c100412520014440d200c00700050002c00d100058031011220381800c3c401440410f511031842800220300000319150101e000801911991100a15a419066042c004501c0e942c5030f00404a4403001101e80010480120314005059000012101800c402c1040b08550703100c0d40890041c18241ca082d41405454080d400340080c80d00105100b81401000207a4681000a01114100c1800007543da54041c001710080c9a54001081c41000c203003003081640c03007691400076807504a03400c080391070031910f03680c0308000180400c42c01d48805010320a00c0880801c1040c482c84458440c4032080c543e8440b030003140a4002103006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 622513264 1250 622512014 622512041
    0x30606080a0b0a0f1410091a0303160302010605061303030e0d120c170309010608061302010503070c02041e02040501030b010309050d0c150c02011a0306060315100302120d03 76
    0x108000009800207040ba40008101c3e42c0418443c0748203070442d009140144005007100001420712590741e5811710318000351460361100340120300c80c0d540c519010140c540103094259004018807a400c80c680000440360700e2084c80080b4040d0390b40d00001d10380380c000d40003241a5901d0b812081003096005003003003021a03415504107140340e000340c550140010481c46800107125040c1c14204c10050707544403118440380310461035074990074025407090007080d450250801d544038030000300b80011a90000400010b0f4140e490501e9555405000c483c415550b510480c0c00c81d49030740740440315201020301c81c410700510060041c0c0350f921304170004003a50305090005042c140b414261802040000c1681e101d00100c07070411240c442511301d8000c861051007100c405100b490410021100c55064102540108032001e035030141490342001c064503020b040e1210b80d410f5001d4400c011002401410582e80310071420845036645980b82c0204142c0e15003140311340c0468004510951203039805219803818412403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 622514514 1250 622513264 622513273
    0xc0d170c0336010806060a3006050d0528080c010c180b030a1a032e0c021b0402160312050903041a09060403060c0f020f060c0403030c110904030903060608 68
    0x40b0000601852409003d582c081c1d0030010b1851101d5000e00035099030b00340900441020449080c40003044003003408010f00500d410b150b0000380707034501122003036403ca801401408031400c0d00c4040042d50407441100b030b103811403170000001c0030030f0319032001e8003004425400126615a402c40000c00c02c4000184420039024080b034180705c12100344080e40d6210104100c0021001080e40c6108c071003030245003000341d151284101049003124001102e094120140e48016903010503c0798000907242013120791001030b4008140340e5041082d01030202c500d824040c00051900c41c1002011910190340b40068003c113045031044d007540c2c6200e1041c0c46c0d100b400e0030301460030241461150b84c550700c40784811041080010551903040c2c2d4a4204490046500c400208082c0c001c10341e014101d980013046100150046a6841c240a013000c24a035100d04104907030382d890a406c540e4159882024070000b511a03600900c0f00c0d00f184d40341c130b8800700e0207180291100c140e001d00e145418025a0103a400044e4076420 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 622515764 1250 622514514 622514617
    0xd05090c10050d1b02100506030106030204060b1b030f0909130506070e0319020904080f22140d0512070606030503040608060a0f03031403060d120305060a05030c0d170c03 75
    0x5001c1078603406000001d06c003087c0c0c0c4c0c036a100000d015208540010303504c2450700c51700140c0304c0254001410201607450314800340404002c00036890740235129596040d6041004006102d1520b4254030787d01c060280c1141c2400c400d00d4441d81e1800900710b4841012480c1c0c0303000340c3d0542c40c00f000040c0140c03503d19483d02e20013426902251400001800081c80d41402245200c0341c101640300340d408801450603010f465500174905c1e1142c42031030784140780d03003940ca041c0ba09844d030812003841d40c040d40e009801410952085410f107103180d40904408d440303003a0750701d40c04800640c0600c02440242103076540d0500c40d0420000300407a81006901c0a8001204c808041002030b810a11300e18048400c518490f844e50360b2000402c3c030003941010b000f042001200d080700419509039000c980103030802c3e603603003c9007921001810361b200ea42e06c103007a5102e881203903820300241d4a40f00070b902000050302c0d80e40c2010218040300d0b1464010302c2119a981c0c400503030b0624003101c44100d1200403807119020081c07214 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 622517014 1250 622515764 622515767
    0xb04050307090c0504080d030b011403250201150e090d0c030e0603040809060c07170a050a080702010e12070518190c030623100906050d05090c10050d1b 67
    0x9020b100d8141415200c50000d040380d40036400b035070001c203400710690760000f114540080c000c06000b4406c80c041203688440690046068040d04e00c165482c1140e58100e1203900100344440003040030160442d904c44e003103445184c0049490b01c0040231140c000c0501400d0101d05a820000303444071400c00c02943d03101d4a404642e000015800905c0c05488080d52034940781031601191081c0c8401c03c1c0c00560000d940250f4920000d0104110b401c1039004980c02c0101c0041c083d100c0030030000141c040c1d4008960f02002c50300e45002000a00e2050520203000802000400c0421544000700c0090360040d440410103130400c040303005100705820f0303d020014580707800204400e01025a80d40000341e5038000d650510350203079100801810341d442c641c1a030054000400310b81800d003446403500032114003c0080c000e038000c04150055030880d445407030034895110421802804002e007000b00030b1240900702c9440e5115804d24141d00340007a174802d6a202128420352003940d88148280b5030b4070201c038501c1800e15 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 622518264 1250 622517014 622517023
    0x306050609180303010e100518061302090303092b0503030a050702010603021804020d140a0c09020304020f060c0109060632030606150405041a120303060d1e060c180b040503 76
    0x143d480c10b21080f03007034840301803540e089000d9421403900001107907074482012070003927055841032008460401c3c4c02d099a10458007070340991108150076601c00e005a042c1480c0031740d520b07100500780f0040c1d08428841c41c030306c00c0c48500720120190f0365074100005014501e656405041d50001580c002800481d1031580402c00c102c0d860707600b000043d145c2e00082002c44d07841d2180400a07680100340a4145824a04055112240c0410460700070755042e0000500102d42e00982c1e10954005199481c501c0407907040c001140d011000c025515566034400d030000405a101b110041c12240341e0a00c0250600c8042828141000d80c18000c110980140d1115555000510551220054407020b00000888420021602640d00510b5200c0c1c20b00020b428241000395160702000c601329448400c035010303203115a0b00d0f4402506c4458100081d40034040104d0044512480224070311144216104c806844200446070000314440c0040d0320301c01500f03143c00ca40c40e406030240841d10034007441c085c031389000250344 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 622519514 1250 622518264 622518269
    0x5160515010f24051c0903032403050c2b11040f1401030206090402132d06020706030207030e0603040f05060105041416170405010f050c0c032d04030605060918030301 73
    0x82010005100608001201030014845d480c404148a004481d103005000740112072141c012100d140006906507100280b070101c1140c0e0424080d001c0c04a1440a1007450f001c0c1c2101c41000c00c03030100020380300f8071503c002d400744140210245202c810582e020071007600c041c2030307a4001c12420071215608041a0341021030441c2d038101d424a507512441303004900031340911804010010075171500003c608c0082e0041030507440c0031208404900070006000d69072801d03140200d0b001a440030900b480268041d5004280c00c0b400780c208410141b29034400034880d07a0080301e0480b414000250a070b401c00008020703180c0548012102409103174440c1400c84501080107211181641c03440c451400b0541c0100006203103001c4004030310343c442c509410481d01038140c40e070501c043c0c2807500c0c002468400100301070f84d900c41411405180b030706020103a68035003103224100c4090102c2d2204691401a44510300420013548603020100d1035161000421450f0300000b018584484d09002c4841000400882101d05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 622520764 1250 622519514 622519517
    0x6030a0b0114160510062301030204270b0603130b0c0d05040b0405060112080a05030712020a020d08090a0f021c0609200f0108010605160515010f24 65
    0x1002003541004075100e80310510003104440e8000390748a50b022072584072003101405942150f4001d00c1c4113542c402114414494005441200005e174a603190049182a032918030515000d03084c2a01c401c016a00c0f042d00700011840152000103000a052041c040c280103000100e500d9400c52904101c11290031000000080452050800169486111200b40c0c0da21141d01d4400b0021468546006103100c03900f030742c00b0f03070b498400e010000503c0001c0c4000c105d04298000140307400d04400000a64850300043e00041c14480468007040384018940b0260281419550007081e07410b501007400380c03507041c1c080c041c103110390072010038007002c40c041e03032485407031964183c8100d0071105408108030300300307981001c00074881c3d0308220580c070520001e0040b015021102c04c00260a038040175042004084c00090818082905180100102e501440c083c7c114045003069820a000a40d900c25050034000c100b440c0c2042401d20045c0540c40034611a24041d2412840741e007081003191030380c200110343c600040d10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 622522014 1250 622520764 622520771
    0xe24090f030a20030f070c17100f1d030d0c02060c0405010507030203191d030105131b0f180507050a0507151d01062103050304140c09040804090605010e06030a 70
    0x3c0122a6242c040410810719040c1c0e501c0d01426503160103281d10541c03081e101350031f041101041504c29440030314030321106c4500800c2c100c42c3e00c001c901d010380b145204140d1543e6880a08100709010300340c20954007100180a1562035074240301000886440002441c2190712003c2040300c490b80d08001c4030161082405d100e903d8040b1407034200d00d14400ea155100401da174003101401603a8001c41c03640b5041c003540b0000e442a901103000d15003221000c580c10110005511808008201241c3d01300d101c4d94688005c0740c001b55110304500a03407880542c01080c07108040d407240b1918081504c9199041000c5103440751800e024880028a02c0c02a040c02405032522a50b849a102c801607008484240700700344d05e640300100446c1954000d11261261184202a1802985040e5512044050440c0d41512148d08607113880e100c0703a2441075000c0300080c0601c80c2c4400c4c6000c0d0780d20448100e12030b921034244180e482c1d04005c000d03070945030560b00c55414802500d810000981e9200141c070390141c034145001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 622523264 1250 622522014 622522037
    0x30804020609030f16050102070b16240e0c09060109150809030913020c0f070f260f070311031f2c0a0203011802090c0d0e24090f030a 59
    0x1d05100c1c130f21455103580e00c15008100e4200404404080c1105c1c0245c00703451125a036000d0390a000e101c1c40039004403030401c505191001903401c9403090303003000c141d0104010200001c0b51000448034a0180344405c0da03c4a41d00a03032601d40064110b0b8880420f20300303c403c0350b107080d048007a12102c080c07607101130001e0742d0001100306c401042680c2c58803400602c000e240d9000342030408000d5019100d000c01a000e6100c80e09114034002804500b200c810036002042a4501000d1001c080038690403a0804585c8a06103a920041044460fa040c1d0006003e010306074a90710b0240500212454030b42e00a070000b03041c00041454040c501d40c640249884042400504440c2000107406d174040f000d00f81501c0c0f151000300c11500020040d0f01e55200764020007078009482d0b40b00001d02c0c60804025444158800024100c22b940d001600c0300d00020312000c2011032240561600709841480070403004011540000070003401e18103600d42004401024055010821107625101c5c803441416100f40681d10540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 622524514 1250 622523264 622523269
    0x1701110a110c040c0807030f150510020a0b0a02040e011406071401150303111b0d02061312080a0305150d112205100f082a030d0806011803030804020609 67
    0x240150385a0080c410000b56140e200d0180241c4810b4480c6c100007480c0c040c090220800502c03511a04040001e03819a11514000c01c209414908010440840c0191030500c0002110442071038096554100056101c90401201c41107040b016484000c00c41544800c0440a403103060403120542d030010604030310b4505905406025003c0d22518040c1560400c0001041c1648480c2d8142c1e20400340c0240d42003080400d40c0c2400b101d00d41806a513000c0c204030314810051030000c3c010490300c0d07c1041415583d543e150b040050f422010341c002e48046070009080b01038164144103003684102c41168ac2a103d8075410081a21045200001480110009007003801a5690003050102d041240c0d02c8050507242007402c0d001404040d134503100c071200000e03808118140c1d0032a0441c161010080100190480809050b004440502c94480341c0c11040302c8d298440c1d02c00f0301509084004603103031000300b4140310f400142407004d03a11110a0a0811a1040c070000f03034405101500584c0460b2643d0720740040320300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 622525764 1250 622524514 622524523
    0x609050d061d0c0306150105040b0705070506040308090f01050f030a050a1d012009010f0f1e080718080c06221e060914010f1e02071701110a11 63
    0x38081200080d20030408502d0400288000220802d0301070307032007903141c050407885184a50481140803c900b8001400002610300141031024029421220740b280e4070700204c0c40355480ba80055803175007000139170101c040c100006041c813069400c0c42d0403460302d020104102d042c0c1c00050074035120305842d07070007042070320309660424000e403500b061008549103101804039000740b481c031014a00000307400403a00b60141101c0c0c1a07558004043c1c4806031a91034004c1c0888218501c2e400d8130b030600840d00030b401007081400c8a0103500c1d50300b60b00c4840890901281c050440f803210543c1246550302c00100703103c0e14070007099032041104140d980c1c6884180150700c07040e41c11491450711805000740170700050042d82500f616002c1940418000c2030503070f22a0401c4556000c45d0080d2082c0794050460143c10f940314504408040c0c00303910b407503030703c202c030100741c4080c100e43c494005001a40500b0045c0720006007003d41019104004000300003041540380950303101d01490f5071003814081034a1034003415420074030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 622527014 1250 622525764 622525781
    0xd0212030f181204060302040509010e0708062b200d0302070b0901020a150506091803181f02030c0c0102010902090109020a0512093912010e010204140f06040609050d06 74
    0x2183d15071035030b4545070024002c0d00a480b8641c801d8460a00018013101c2c15600c3c18000d018a07521012130b9640d500030300010fa03d541072901c1106042418100d40c3e21a4040c003021030134811000c0000c032900005480701c498012070040c0b0b110f4104642c0e030f6030000780c0000741e5000319240074030304d81c0d12204c10000507814440f41e074201621504032103c3c100007450007980b065102d03a8084131004401d0721030000424960340140c00c031010550003001411540c1c2c1013880e07000545040200f845880e61051605c070700504425094000c0560f10209050360001c0c400d11440640351020710003004404103d40004800c03100620848450b141d001507460802d070b01c50012985601082c84c000c0607070341001c10f401c0c0d42e078200341900022100042240144c000301f1940700c20000e2000e5180c005604ca02680030000d01c51707011001d44000d90b607179030710500303608000b80003600092004004c41c59250b003d080070720031000582c08039503108407400c000a000580c1c1103050081a00c405480002502550b03107030071070040c070018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 622528264 1250 622527014 622527043
    0x1080f01060f1206120b0f0411090a090609140607050f030a0209031c0908121603110118260a05030c160b0406020a0914010f030510090606020d0212030f18 68
    0x341e000b0581d844050031714031003144030740d18031102550ba641d040801141b0640c4c00030203488104011804a2520701801c0707130404049840043e4845007a41c520341280c1981804980106410b002402203110500c401ca45c04402c07802c04500e00901088000c039144001440f100200350701280e4007480f91810405815030b0340104030007640700c0e0313207203400505041000d104800c51445154081642e0400740d40c01d50b914450403000009002d2100c2c0d1302600d4059201c0302c0707640e080d96a05102d800314400f08108181450140c1c114200ca20754801019844102c040c40c0040d0300c40c4208104403845601008495200d048a4802c0d500d03540c2d5203100021454429101425880c02034050105010f82a402072558034582d48a02d201c031643c580e440800c0c440c031468a00d000c00c05600034a40540d000b5004a41c0c42582d0306a20f440e0f040d183e01c4000100d54603900f00b400180d211108084d181601000550089075400701d40d10b05600d0308025a4040c00c1000f0000c0f43e5120a4aa5010054408009100c49103119 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 622529514 1250 622528264 622528271
    0xf050c150c07150c0c080d090b01180515030a021c1712100b2a0f06180a17070515010b0309011a030a0303180602160c0501080f01060f12 60
    0x501e5490220350407051040d02d118181c1c1503101c440d015030340f20350b0b941080140c964100002450b01c4031111a007000185102c1c60740c88000302d9001610fa5002c06020b451900310005620060700d5820b03086034802403c5140d99980c00007000701e241d50018001031225411603d24142d44012038020754211b080e42c0c0000c01c0198240a1650350400030800303005d100006814160040e03907180e82c0720b0002030b51481a104414020800f2820020380850707800c60000140b2034104140c03074a814024540051440d00f0301041c1c00c002c0601c440c0410703000c4d00c24904000c0c1001440c64242c1d5846041a641c010026034414800c00200841000b4042c0f000b034055408503442c0c0410f0b580c0d18054070300f180e4000c55400c040c5520785a051003103100075403000c0d50f455a015006042110040e80c055009205080030400d00c0c200103c0034000140c2e443c001004907403402514481d00340c1c000d181c142000030540d00308605001c40d1504101c0074a094034107e9045945601d04034402c1c4404800c1510f410401e0f0000e494047d04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 622530764 1250 622529514 622529521
    0x41a0403260412050f09030a0605060a0b0f0d0903120906050f0718050f010513090605090f1612020d06080f060705040e151804140610060f050c15 64
    0x410a0403000308001c907001d070100c4189400d491141d00e21045038001d00c000d41c004a0100003e120310b014002c861034000031140b422a034400082e24240720340d031044034196190000c00c151400c003042c0c1c1d540103200c1c1c0641d090a0105c5010210007d0080f50b11584800350f0754801001418864554080c907032a5025040000b0b0b8034604145026000c03c591214610724180c003c107000a10500300c800111904907445424982810100404500d13400016410820180680e616040318840904020820003400080940ca05024072514078801410766245c05451010400307030454001c201150b82e13529148c502191003c4100c4840240208040c00c0e54a9141160104444100140d84003058222400302c41140d03031601c8048030248200e026540780701e985500441c41c0180350315510b1504000080009078071405803401c04c00c410382e040300c0944000102c20088031030007200b4809590080340d00c86800703007000d080401c05844500d40d20703091010403000080355520b85806010300c1c8401c030ba0600b8041101c2c00d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 622532014 1250 622530764 622530767
    0xa200f271903051612140102070f060b010e0f0105070f020d02040507020318030a0c03110a0801020d0f0f051b03040c03051605210729030906070f020d2c0d06021809040f02040203041a0403 82
    0x440cce4107103039000c280031205c1e02144d880c01440912506005035141d51411406a40d05c0d0078084840c503040380c1010b464803030107005a4031802200d1044540c2d600543c0c0342e10b0413000141107100c800c882d081c002d400105090002c5220521000d042d02c0d0405c1040d50420003003008a041c0e815240c1c00001c02d548007251a4145000b113800801460b00000000d000e14100100800304507a0242c4025104100c524000800c440d940001b44da80540034046a0403079507a640c44903404c0ca8040e149410490724498018842071815490032041d00640c00e54195244e03c9102082c0e0381d400316030080c1e0b030030703401e080c0c08000c00d00505000e0342c54006003240d4040c4d16070600489a994400003070310307245c0110340c6507000c4541e0588005007035400c40703565036a011080400c00560300040314020388003819a81c8010311f0000e81d0384800d5502d0f00c12038495140181d80325440f1600b0520401c95405092042100c80300303000104984686503035000360100e40043e40d035104c0e0b1030602c1d00645801000003940344d21398200030905 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 622533264 1250 622532014 622532021
    0x5240d110a0210050c0d05041b0303020c130e07060810030f0813080a050c0d0309030209180f010b0303031b120a200f271903051612140102070f06 64
    0x40070603021202400c100795049415550111803856100d0414040001d0607136003a00321980060003103200c401c41c111600b00c0303403070098001d03041900560711050b5040a1030500300307020300c61480005030401002801d8000592210050312401c800c005889004c91131f0000442c101100550f80581e280d102d20750107103020143d43e0444c0016151a0f0f650400000d040803002c100785400c20340c0301001c0e00504d81c18004100780780b0340301801039003040041180800107031601d0883c10700523550850800c28000d8004129880c01655600990103a4140f480b202d186442c000b00790780c0c000701030001e291121011042c0c0b5083c14019119141210103251003400740420b100d50011610301006100e418140e4040c0e011985a4480c901d107009256508108001184c2c0d141094850380c45d603401416440200a00005105040c46000c0d00d018812107003c01c1040000c02c01c00940c00042425191450740d2400403100f104800000010f024010036a107104a06102035040742c40785135201240c1350000c0070504150008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 622534514 1250 622533264 622533277
    0xa090506040501050a12062c010504061a0a290a05040305070f0e060105090f030f010f060911040614090307090903120501031509020d060e060609070905240d11 70
    0x101e00d8000049568245012074505440c0344907103d000924959494500801c400e02d28030344180b01c0d440810804d00700c00c8c84203400f1000540004643d034201340c1802c0089a81d07850300f80010a5030711100c0300050b11400070580c00c982030340c050001d195608801500b0130b40084650000803c60009550640d56085000350040d0f90003041200c01d21a25401b00c0712120a9030301503c20b901c04503000051203076118078001c01e442c01c0c001d09002140c800c942c0100380351031618012000e40b40d460703c00c0c04100862611844004001c00314040c000c2e803040340c04c00c55070b52046000310000c10501104114207064180103c50300840c1c081c00311204d06503034074044001000e044c0000c03000501404040c0460781d8040c00f505042c2ca81041141d096142c00d200782c0d0001781944501244c0140040d103051000c00d1040c42581400b40140c005132005240c20010860b00c1c07000105000148044208203011f2a100c400309034030344c0c041c0e0303441d648941d4148070700c00142400745c0c03480d00600608003040b840d240c000074005400c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 622535764 1250 622534514 622534519
    0x303240506072a1502060403020606040c030b030a08040501110304260708120403150509060129070b0108060702210315030a1202060907060c06020310050a030c140603061008150a090506 81
    0x10000304c0000120303251001a20080c0060f030200001c92a2480c0c563700050341450503060000c1d00200b500042030402d44024000c2c0c070312407400701d801c001c6543c001441d00f41c0a51888007071440e090a02c1005403404007400807107000040200181007105104200c044080c0c09154200c403020090000112916800b5000c122841c03031401c00300c508040000d0250314040c412440c0070340801d80c20400c000321060030804040502e080c3d00405e108020040d040140020785c0114032911441d814440120700c1c015001d031a0102319032201030600c0d42c04a100c2e079000c2d4080a200350890356501c9000303400c1000d80c2c40420050b1325010b00058582040004018903110b0038194096a00a075140741405481e0200340c450800460120000c1e03800203030013070b80215800030f031445041c040e140d20ba10200b80440c005800840e0507800c2e40c0401d010504100020501c080c604030381a40c614944040400c0c180042001c130441131141840c04203e205c1c0525100c175000880c09000b00908566600e401c03006000c0649445d0b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 622537014 1250 622535764 622535789
    0x60b040908030f06101718071806050a0501020f12090301022703010605090c0a0c06020d0213060320090f040e030f0d060e040203150703091e0303240506072a 69
    0x8411900039150010783c01c2201c05446c40715078640142a41140512071040017501421001040d041002c43d46d01c0c00b150607001000481c94200b1062000107070090708024190b522900b036500005600099944174050341c607030a16184c01d40c00340440c0c063300440011207030803040040b440d080040681110504440c04030024031116644005001c00d0960995005000540802800c0700340d50240c001c00303443c0b5201344001880c1c0528036040c070080f81c010710f645001c034001d40c403c104403141c2d150123001741181e0045407030b400c1110039609c0000d01d803041c0040107000c1d54603000c5550581d9296400b0401026110040d00d641d20400c001d02c004540c40301fa0100b24030782ca043c10100d580001000220300c41c95020703004000001c00102c90303000100004041000b00750b1a21401000030306840392807005214407800d1708c291404540b82c06800c1d06c4200b44020b02c0350b210440d03559100c0b04010f29803001c4400c141d03445070341e030861b43c11303c410710642026840f0540040540071031000b03030f40341440030112181c008101c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 622538264 1250 622537014 622537039
    0x803160b06100807050a0509040614100e0105070201030e2d0714130209120d050d05130f060f020d020c1b09071205060609090a0b030c01090302030a060b040908030f06 73
    0x216416012002420025140f41d0004498074085c0000700101c450710b06055082075004d070000f8054a40b40e07000900800b00b2541c800401c0e003030105850b081c15143d801c020301030079010f0340020514007490601038100350b2644000b00c0c0d40001440303d0a02034a0b610071030101203c202e11040c1281980000842c038a10511030005110041d00700440d8982d00300900011744c0006401c1840060741120801030340c84080061101c024020401110f107090029886030f40c1c4850301481c401040705c80081c40d0001d441030b10781c241400144e0601500d12000d5104800068a401409501b0700034010003115514061000481c100da090000411081e600034200c01640c40607510014010380c0c074010340c1d0300c0002c6030000d1200d01c22444140c1240d540030303001903c84c40c100500900081c51400058540a0800d903413140c40c0142070070117008045104c0400e092180302e00d0316540c0400d581384800100070707109036a01c50800305696500e4005c1504c440d0071402250322800c2810702200e0012054992620038072865098 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 622539514 1250 622538264 622538269
    0x1709061006020d020c1e0616030912030f0c050709020c031308210c010f0f1b09060c2004090308010e01061e0518100c031403090d1202040803160b06 65
    0x2003c8480d940b640940440c030214010301108203000c00300128102c01d030180e01c8440362104000b418040c000d00080c0e40911542e824080c16813840c1c1c2e0040d100d031903109041e4001090f0001410807600c00c4030304c0e003141c0941031802c245082c08156040306003424000600c00b1160040080540300c0f40990141640d00d581da5003500c0c07a6180005080f64003840010040301c101d0944110103450615004000031900c4841241c2c0c034411590b01c032030201c4d15160b50700d00007404141c003022201241c0b12141400c0d480141400c001409a45c06c0c41d00003003041442500300c0012003041c1d850301442c584054000c0c4800c05003480c000e444a4000d000c0c2d441c4261070140000f030300910540800007d10b030340c2c00c0d0091001c101064112165813020841040698503011421511348402280c41d40c2c4103115618041d0340012464000c180c0c050380358039041c100303505106010410b0f01c042648090b00000f070a203911440c040d0900c05002c0e024030b6201ea003450001007000e001d00c10a442714000c00a2103101c0c01030b0240d41c1c0208 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 622540764 1250 622539514 622539523
    0x10303050405104413080c030d02040e0a050a0c080c0a09240807020d0c02060d150305060a060504020f0921010606030b040e030a0903031209080f070b090304080a0b0403170906100602 80
    0x24034280a0025550805c08a01c00800038940e250760502924685940b84141e50309aa01980c09418452007030342c01c0000e1407140b44503142d003004c10240c0900c9400300c408801491120060b00c06034401c8400190009000c0c01400c001000b0408403035070f500d4034000071140319040304481c0e008a000c503c400c400598020b10200b4500340c912039945641104074002e40a100e0706801003528000d00e1540c4081900360381002d81c110301c3c0118400c1c4014041c0b8070f03184a00a003900c01da1343c48140201c0c0113104409000c2200e44c00c0d07441400c8262107114207192034848402d0b5048400c80f80680c0e551a04101140d03496054004615071075040d101071000050754944a5600d2141e8041d2000144000b03800380300003480392a4140424180b01350201d8074140c551074100203540310701ca0303007066164001340c3c600800c40c6406803c0d03800071b200c1024606107407030050f0594540c00041030003403204000f040020100760041c802c0000040b0780c103440d06598038016000c00da4400050350000301c00228140c0c0062920720004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 622542014 1250 622540764 622540771
    0xa200d150501060f08040b0c0c0a0606031e02060301230d08030f01050901051f021002040b07020a0b0415030905011e0b0a08010c0f08060324040b0f0103030504051044 73
    0x380c82c0317042581c540c0c940c03a80e005405002d442000308200b02d011045102003203c2c500c114015440095400e01c0d42c0b80072200c0301003201030805a100301c4001c50025984220681e411134501c14140d0007000c4c2e0b010000b03c060508182c080b9440862012008240180303040510303c10b055019070084280d807103108110b1038a10900c1540d40c003e0902000004c0140820298036a2079010b0048418010300e5010080a03030704103410041c80346102181c0d040c25464403890110003401551100d6190074140002c90b5800310b54018520b041c162201649401c0000075800120b01c0d0341d03034003030f200c510b800c05076518000703400715010740d5104000105000c83e2811040c440c051b422602511100d60300e01004609075140c0500406866040c090041d000c3e910f0007080c0c0113100043c201d0782c80c020300c901d41847c1c00745d180b074005000f400480c00814010700002c1e80000403542503c10440744084001c1d0788038004c0321440322400070744981e0342d00b0700700e80e0701c8881144000e4155009030455014140e400c0c1003a0003c41702044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 622543264 1250 622542014 622542017
    0xc0f1b12211513060803041e0509040201020c100509060708030f07020c091b0403080304060516030905060c160203070f1403161a1b0607030606030504050a200d150501060f 75
    0x1540c000091406000c03000d18540f02c0140407a945555016060868000351f0000b00101c462180610340b541d0781c0401c4401a1070216031640c41c0703044c6500002c1d612070424510500620024040c2108180907805a0780c503100024503403a40d40c06285800c00039600141d440c00b11080303d65010030310080c00400d66480140000c3d0a400f000d585001c405207445008100f040300780541040080081342c0001c0055206a000300c8021546061102d82c80e5020b400c42c03a0f8000c101407400711300c4070004101041c01c079042030b941c81c1c441c0c0d1a016510700c012130302d01c10700d080290705120b05940080d004805504100840d00c0c1c0355526206080d190003450b072500b100d501110340c81e01418405001e0006420b614428103600404201c1c24440000301610340c440e401d60140c0c01507440507007080000d983c03600440e00540a03a1605002500342692005e81c0caa80b01c00005080c0d980f090540e007021001c4596810030b0700300c000e25403840111700e81002c21070350500494072601d06042c03100201c1c0c00c3d07015a0b031404008026 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 622544514 1250 622543264 622543291
    0x2090405071b060c1205100e090d0207140411070f02040507030b0a260601031a1b09040b01020c18041a010f0911040e0702060711060c0f1b1221 63
    0x43e62000000c055600c6048207003d00f400c03d0707101c0d9018601c9004e100d20610340b0503e00160405c8103100301140001c001c440164045020380240b40c0c3d0200742d0710203c8841085030b188082030040010090a1500c1c25003601d2080480e00d541031140e181c0b5800c040a009403010800c0f40c545d6641101541d456901c4a50041030b00d68082108802034040700100d0a5195411904d0000305000f15003801000c0c4d20540d000d481c8658070710203481c0b4901c8540e03082038202554685c030050070840300d1b11602030115901e1046a40e494203204a900034080ca900140c8014050500080000859034200009940a603124600403076424001d40003291954140d80700020b00703840070303031030895184041c1129082400654406000005c0c41ca0003074a040d42c0216042c2d0068030003032400140003031400d041c00024550540c811001c0c484070703110081c11100120300180d00e6941c1c0f24549000d1080e03403c0301d100c1c100700904c940b20007080b46414500c040c011144203031070000e803512204140d00d05580c105903015114040d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 622545764 1250 622544514 622544567
    0x7020c0f010e04022b050601020312071805060301080d0206130b0f0a090204060303050c1b0a260607030203160f02060613090c0311010306080616080702030d0608010209040507 77
    0x16418403254004014000b500e402580500740181d00e102d141700c03112005a40c60342015042c4240651035004000f0f200445c10480d030071030700c3d8100c1c0c4006080302c004d01044154505500140310300d4032000d404003a201507988d507920b01c0364560364001a071081d8014020180802c6884220000b4a6500d03900884010354644486030340609955025040907000303603a4124850050703d443c0181801103009444d0692070302c030300301261030400c00c00d882c10417201d102c01ca00101d05076030b410070140d060ba4040008014910f904603070700b0b5110218011984d0041c0306507010081c40c00d0303050b00114843d81070241c607078181021941058454009000c9181e01580280e030004039a0306000751020f2000c0d04146011441000e542c07541d040d100a01c0d04141c5039a50703408a02d071340d5940c0600480d40202240001040a07141c584401c0400c445103103c94410080710780d0215900307610800541d440301610440822041e60f4a14210b4000d5006c00c2031a400355050034006a1154004c98100140d421103003c2c180d1400e5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 622547014 1250 622545764 622545767
    0xc04080f24060111070816120506040602160203070e010503120703050d0203072c040605060f03060f0424050405011a1923040e090102030106051204020409210807020c0f01 75
    0x1000245010b040081e0052002180c4c6030401003080140113150203004030301d924001c814194601074100f4042013003c0480100082d800056850b030003030304100010b03220300c640b40b108a003800301c011020798103210f18a03000c03400081520f1142d040720011011202002c2c07902c2d1112041d40106c0c100500482e20074000503002005c1c2d0b4008542c050034600d00441381350404111400070319101300c464400180d500b00e5641550078244542c3d8007420003211210308021f402c041b40340781848010480e5000b6a420300071007a02e511107810910800c09940d41000e444080d000c0c0c0b079590f107003442c400c45101d1750800700005091405201080c1d0803141d0159010328041c42c41c2c4102c0203031408502ca401c01c0000340e0700780e803c0034020750083e500f0100201040c1c83d911480c0081600307a2030005040038110364070400c0100145a0800100ca030304040002c55081565201c0c00050010801700d240a0841410060744000c040343c50011110301e01c031552a8182d45444400e1304980d504510408a03070130031440407003010150b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 622548264 1250 622547014 622547083
    0x3090f270402010203041502031c06080a021908061303020d1803080922020714030f0901180b07061d0609060604090c0b0a020a0c2c0a140c04080f 64
    0x142c01801140e142554445201c1d520305550340d0204016000400ca040d801c2c400c07200385030100040090280100d0781000350440e107410080303100174812005040450054a12140f03400001e15070b4209941c401d242c807007642c0240f200103840450040c082c00d814a4030035405840180c0c0303004040000402d10600f542c2d0740c00c0c0294818be8016521000f13030780d01d010020300c02203002150300c00080030258440c0903e02e4460b0720045140c0c03140072560000c1c02040380c0504044160741001500340791200d00a40c01400c8030140c40e0707071a0450740c5224000201d8005100c859001144c42c42e00c1803995803501000700364200d4641c0c006487d018656008080442c20a10b841e03005011740901171034035810525642c110400c5a5403080040702c000d41c01009070756081c04404164100202005141c1c424a0141c46c5c1e13500088003c00003800040090000209040c030005510001c945110341d0580c80903420043c4510351a13401c14840d0044910030f41e0b00400b4206404681c100344810350f28910061001c040450080e074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 622549514 1250 622548264 622548271
    0x70c030302070203011d100207050c041e05010305031c051e0703150e0a060b0a0503060d060608030d0b10022109030c0a060804030305060d021f050906040803090f27 72
    0x40580a2240b140580c2d0203216009640c44500aa003003404d401d02c400b1801e00e460f138010801168030620242c8040b403004111030301c207902e0407540028440b461240c0041c20079040182ca40d207591400001104015001008101c1005002642c0c0312072800e50340c800c000d82c0e10484048904900300c04002c1400d5595002d0290409124203000c11002d100d421a1842c8184560140c1c07030761005c003414004028a20702c2028090518031204a1030002c034048064403520024081e40d0242e01c20102c40d405006441e404800980108400d0300c0c0d5503000c1c40c280d207010341903016696219110100429419a00004401c1e051140310141100540b1105920303c0c035036000f506900ea01070060792815500c80e51010410760240031b098403042d0131810b050600a00300d40c0c001f411140200300503400d4101596440d8120b1581d00d54000704450300000001d4215001d00039182d103d900714a0100d40422850808400b4241212058840782c107070140380e90400c8284c4003814038421042104502e00c0d61201d0500030120b61 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 622550764 1250 622549514 622549517
    0x702030c190504140a0e0109020a2c181606020a080f0d060b0a030b0d0c05060a1106101703041d09072309070e0105030a0e011e0c0224070c03 62
    0x1079242c1d44502003010764548090103048040208100445c1608500c6280c41040c0e0060003000685c1460340030034a1140e040c0501c0915514a4552002d050302c410300310021010300c0c04854a80703017021310071510302d880e6110f81420700c6c3c01865803100c20f00b1110b00b4050304881031540201000701d1691140e84096100590700c101001c003c00441c05080901d02400004150780041103070344040b6114000c1c03c40340180d02e0a4071a100c81031004c0042031980c45002d042e42e000300c55096642e02d26400907109400352000d0340c034480c090802004018280b19040710219148000d40c0c0b040c4200724041c4c142c1702c0c032035401502c3c00500c181c22068803000c05141d10075408a0104101d03401662104581c17066599440000d060422030308151041f1030510108482e0030501a01b043c910072420346001a040d400002c16010003299216032040004c3c80075004108000c90071444110b042527840d18401c0601046030f40040580320320011802b5410704a55565001e503c00c8540880c1503e5080085a940c01d940200740c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 622552014 1250 622550764 622550809
    0x3140f070b091516151407030b040216050f01060b120c070213050112110609101803150c020105060105180f04020d0e060612010e03190225050301110702030c 69
    0x403224012200502e0602030513540284242c4192600c1c010424010422040f118100b40b810159500044d50151304002c007418041408410f80c8040307402401092514400c90480030442000e0040204d20450400000070007030000b2a01c2e004c0d49003d074800c5800708510030b02901c00003050300c0310300700c040c024042c401402515501440303140d990a40340300f030300841e5110105603481410000046901d5031016803e6640e141052400c0000902c12400940c00c5414071038020310048034121200318031005035610561200b4001c015850001c0105039000c0341e0b00140d8609004520341e980540207a44107000c05000011001c518501400041000b402603544c0041c0c00f440110040849805002c614210440080c0780710701d0960308000c0b17400039076605030380c0c284d150a419107020385010044421100550481c04814012004224034000c1c90b95042000c407000003030701c051402142e40c40002100d104400a0005420300c0d11070742d4117485120350007135040d4030107070304200b01c0e08156880402c48082003034040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 622553264 1250 622552014 622552039
    0x2702060f0408030a090906050d020f060c010906140f010f0614041a070c0b130909020a15080f0105090705031612110d050a021801350103140f070b09 65
    0x501903604190000e4a540e00f0109004000a40c0700c2280002000c4850f01031200751b1500001c1504900d02d14006402520f44036402c0c0703040e49408040b54040c150150082000742d403141042d000901c100c080c1c03440c101e2880303c04505e0741c3c118400c226040e10104a02da1a885103082c00903101002000701c003000300e032003d01002410303096240c0d0900f40d400c0203040499a40059141c00110003510303800c1444d803250f091180002a14501032420142c688261000490003028000614007174141c1d403050306000c0d0300c070b8000001190b001c40c03264017402081d4102002030341c030340e0200a20850102c1d500400130703505200044842012107096540c200042c101002210201c071002000e03140043d0241c1084080010300c070345048518400c1c0d2358403101600086082040084454126498041c0132504025101c0d1544040f04100c0840140d000040e0f030f011010450403403140010b25400348010350700045214480121050081406d21200001c000500101400c01c0084042074000244007034001603801c440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 622554514 1250 622553264 622553287
    0x30f12160c0611011407080105060a1e0504050a091a0d020d0203070b1308030403110f190f050103060501050a0824031509010b0a060e010f0c020612010e0901270206 72
    0x80001500a81d980c600850020300e071520300b501d0f408901d00e008120205c007040b00250303102e0040d60548404840103a6190b20030101254400c2c0101070715603810f903181003068034180d00000240100d80003034070034101c139560b2880e846003150110705003880c60604500550b000e5281100c0c2e080502c41c80104945480c07d40c81c1c012034506406074102e100d629000141034140d84446420001c02041410001c501e084c1c195a00c5500548110050780d0150110400c152090354402d6090403842103014a2034008641c1d882c401d401240d520b1041138040382c40c0000c0480d56510032011148840030644608619031148d16845900101c1c250030303643c2c00e01c101d010302200e682e018440080d071070341c03103002c2c0c411941011440d5a085a0341c82d20301c1d41c811030401c001040350a402c902d10803014202424030425490425105542d10383c842c94000350311540004103108400741c2290710f86c0c140c51803807280d51059951446081e0880f8903000c40b2003a004070142c10209108800030f10911021b07c0074144034103042c3da0b41503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 622555764 1250 622554514 622554533
    0x903120c0f0d05070e10021504080c1614100e090a0612030806090f010305060705031312050a0e011103180402070602070507060807021b1c0c0609060e030f1216 70
    0x415400d49454205201d030040d80410055517008007260041c40400007130b07102940c5e5050b100c400e800400d01f030000280900008905440c419028030003a5a00d00d000c3c00d403a015015020b0140380011108012029514105034030850f0304042d064a454500e0326142c410400000c1004190b5030445031101c0001c9841c1205034000f1100611a0701c1e8082030782030403c10820b0f2041c00034203882c1c11144030001000440d0340040c1d89500001c5500f881c0b5901c0d00c515511420184000001804511511ba254404580d00500410b4040c8840d543c40380d00049120045824a000c00380e500050382c03007031003500d1244c548028880c1243c0c00040c0018a400c1691f61405c00340e801c00081035819800084080058607009803815030300094a00c0a04800c8440d500855444a8800d80381030003060b003040c010008180c040707a035000c51500610103103070040c0e0fa04401803d0528a0180308002454100d441c2c0c85810300040c8940e202e40e024001d0120701b8040e078030802568000c0a40b0844008500d140c180c0859800754 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 622557014 1250 622555764 622555777
    0xb1602010c11062209020307140c121908060d05030409150e0a05011701271e052d0a0b0705070f060b090906060a030221100501031101080903120c0f 65
    0x44549802510001e44c1d44006640e90000c106070b8010070400c46141d41c003000d801031031b121100d81c00b1344038461982410724212851610700302020000034800c0d4220700c4040c0000440400d6901c00c000d03651032009014810800070001403007030344140300610210b051a08910002c541c011007a00549980c0c0c002c032440c100c0250703240c024441e610780050041d01c01c841075006501d21110001d01051040001c10103509140c00960050003958240364030400c00300810720710011075208404120303403041c0e0810720349420582c000310b100144900da4000381c85412144100f505803ea138090310900701d658546810002004162204010381000308000180092442e203401c68041e40001a07041400300a100d8071038400341250301c05522000410001d56a801850400d8aa05442c3d1840340c0071589060500d03c10040640701c264020701014903044c080a52110b412640182c0b40c00c4e007403e0555006440c4010142c4c0c0c4007209400c100300c81304102c43d0260740340e90000b03c2415400d00e40b51000b145085643c0008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 622558264 1250 622557014 622557037
    0x301090605240711060c0d121512060c18031a01170c130b0a0e09070b0f030c07020604090c08061809280b1602070b1602010c1106 57
    0xc0c20140001e041040c011060381484442d64500348102034080b0540703025040703004002e410b140c00c40381e48070380b1550f06542c20260b13000c086070308241440f41c0c054240e0799200310f800b15540c90100b80555010804144c2411201d09110800f100e5400703458100c081c100e00040340e4240108000059075122010324420002c40c00750003a070502c12035100d400740f041b43c4183c2c8000c1e00c1d030804181680e0040c0003c290000350750740171642c030480612a40b81c858050840440b6541d400410b08000068174410300154520484140701600c01194882c0b450800e14028502611240501400010111056000141580b034002801142002d50b50701c40302c0199030003295040001f404400a10042e41005c84203080303100560f040c000c01c149000009a039880c00080740114a44401d5a034000600c03507840611106203030001d1100c10545003e420012007084c0c110080030041c49060400245004268151466501c007205440485283d540044408041c00f410581c1d003002580828403050380c80304014400f0b040c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 622559514 1250 622558264 622558271
    0x1090b04080c2a010c0501062d170a170d2c21090a05030109050304050102120304031b150f06091107050706030e070f03030203070b1312050c030c03030109 68
    0x2002ca0182c1400501a02d071070301481011800c444a03074100d0704880c58441c081c80c0880341010b65042c042d0141c00282c0c0308a038a01d00b1465209611000107480341d00e070295aa00011070b0a0f500e024419610606164212142e0800721950340028008100a12030b200f540b4503543c01e22010340000012a026140360400c1c00031594a0f410540f072052042c0c0010500e035a001c1e080140210301089280c0801c000d00100655000455403403913980c0314213450207464003400030041c96409c0d00d04503540b0351090007128054400d034880300152640361400c4a100d268582d03128050b0007907034038a010002103e4641140c04451850000082402d144a2540020314610011580e03c0ca400e010400315441070b042054074074805c0100c0008200001820b1086804926001814944515501d0704144840e003111001282030366000007819400006051001d0281b82c1c2100745485048840c1408c9107100340052084141d00e00c07007d03685000b200a03000299818080e46d29001d2404001421540241c020003001584c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 622560764 1250 622559514 622559527
    0x22107080403090509190e0703051009020439050d020a020616050c070e04020105210f060a181104090c02071514030a0b010203040b0d050a0b03061e060301090b0408 72
    0x3d000d900e0b000105410340700d4a074a07051404020302100894403880e564103880d4800c1c00c3d11000c0803c400d100454204050f10358580c4801c040b44040c01d00f849007a44140c1c10242c4d407540b44441c001081d00069004404504c8175940c0c042d8190ac0784000303032080002c2c8403050092040c06002800100104402139020300018904004404a9131544508040c20004244210600b1400015a9009803851410001c0050b500d070320049816108a1000f001603c0d210f10b60170400c0b1341c485861074044c03071030381e4031403109540d1343d4081c031800314694420301032044a02c40441140541d95800554401c003005c02507444d00c1e0b01e82c20364000340c070a8038040e6801130b8822581000380d6031001481d41070540351450301a07020005609c0200442c0806004960b0707541c0d84855085050b8001c000f02d0b0003c1c1415480d080d140d07510340348a03c00405080350140c003071a00707218960305a07107004207856229145441170480340120743c0740c032110a100c00a28154040d0750b01c0466401080d02c6d090920f12652259114560303401e0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 622562014 1250 622560764 622560767
    0x904060e010c050901120513050f0609100b0f04090212011802030c0a03020a03030810150305070f09210c0b030a091401060b09040f0b040c050a030c08010f09022107080403 75
    0x5005860400c20000140003e44d49030303a0008503241909030f468030120781520343c40890340102c00740100043c00c52041c00c1a03404510b90105140c0d01c81c8019405907200000461424010307101e5021070aa03200f145010358401301d1501d0383c07042482e24000340032403c0446182e002c590859644043c0300054025076541c001c1145030405c58800d04520540c1c407580c0e4140b03180e0100d018030701907000c014184502180050394aa0119030044c1c020081c1203050031811042c04005002001c06403038460000b203403800034030031032406086444115855007801d0429640120500301c22009140c00888805440d8100020a050080003a41c09104840030000f0415050301c3d003600b13209511040d012199050103c01c01404020f8002e40f4500d41007a5008260b00b8208050180144500c0c40c81c5a803080c5003130b03580d041f00340d8020064100c400050f00c04000d410741550040c1c8040d0402d105209103a034003090244504045900580404076441803a500840900c0d264240f44140444445001071202c208000c10f05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 622563264 1250 622562014 622562021
    0x150d050705100c0f06020a050d051003030908010218060309010b0a0902090a120c05040c03090f0b06030105010801021c09050f0304030803040605061e01181701063b150904060e01 78
    0x140c2c2d00381450044020140c1c0c60900b1841c2c0303e080504401d50100c4c103249103501070300481e01740c00300402040000e4940302e00d220002002e240000d8000804250000c2601c130414400c4855452032640004031180d202810407045600091132004036540740c2c0d20490301510360300500030250003854005038030344100c1b4083c401c0100342d561201c19404400820000400e004041d0b100940b9415500402e4801c80b640c410f502500c000040148528010043c200c01c0c080e2021050f4094401107000344202d9030781d0620305090b80552a5010400400b40c0341940e04034080f0344c008581d0510540544580410b140103040c01e40e000b641c816035600070000304000c1007050300d101d0300b0752044044034490801c64001c80d070b01120710303070080c52107050040c0410740c400d041030b54590310b200402140300c07405009411603110354081d10b400d124098640485000054a100c1800360550240703400080204050140782d094403403480014000121010a80b011032206407a4161058400c9005603c0402d44604071010386084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 622564514 1250 622563264 622563289
    0x60e1906030b0703050703020708030c090907050c0c0d17031312140901120912021b040b030619021e04080c0307030b13060612060c110705060a0305150d050705 70
    0x8249419001e00024201e4502c40e07812040e02d01c1c00003070030382e00c11200350700070700c58904080c080100100410560391802001080400019219489182c5886209582501a40d9041501c94000354041d04450a101a003585518050211107044191101214400780d0040c0d42c20004d40d5403014241d02030004000101071480310b0f0b440e1250308001e4840b03c0d80c4030f80c01400000f904000e410340400400103680e40055a2440d080303001c85030010b062501c06036445003810311940700885440f038003095514151045d50032484014000d000c440d17a4801981c000d40104030b55000d00781c0c0d030034000c207100100d44402c0410300c181c800141d550b80c1c82c1402241303032030014200a6688283c4c898441400080d65150949400141000110380350024a1408001503d03650f08800c114444044905c003d10047da00405050050390f11050b03100c4018090385501c541c0c0500609810a1041088105161103a8000c0f0703841900d0440b4030030300301900c1d000501a554214400e4807123a00c4145c091003e8504130f00098036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 622565764 1250 622564514 622564561
    0x232118060c0703121e0c03021c060b040504150321110d02100e07080109150513080711120a0b100f0815100e1602070b0304020f22060e 59
    0x1005070990340204140702e40c0305213001c1c0f55120090341c400124942d200300a0b045280506211000c4000c0001740203400132244071125142545001403100f84510904080c0c07001c801000740f4180c101004d010103002c48500c090546007401e0b000101050422203082c0175401178001003081c0a100d00b00040c03117040404480c0149410194903000c40075000118003100c80e5030220042003000503100319604160341d6030721450895007814015410440d14602c03e1102c01d008000410807900c0d24025980c08440108001b410104200703d1032010610942280c503021100601184060300054552030801525000c111100f514a01c2445107498600307040002508003a103100c0c440303500e04500c1c2556070344100c1440031626241c41c04101e110a000e0b10401c060825508010307600c1c140b56104a0040c3c91482c610030040c0074915022800341c034410f040300d00680e0000c0c6420248120402001180f12048090307080300c250412150300c0307421450083d5801444641c100201c00d2030000082814142c0d82513030040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 622567014 1250 622565764 622565767
    0x5060604061e030227030709050403080c070203010908210106030b150f0c0a0507060201060f050906130e011b0e03030a050a1425060c232118060c 64
    0x860798400550701e80c2070003201000c4500b051858050300244034a0101c0c0d10306010440d0f4994482410301e22843c11184213404603142c40395034113101001c481054a0080c001030447c03001c581080500c10150aa241c002000040e000f074855585040c40ea0103500445440901480d040050401e0002c9550040003c0d090522000e81c0440000354403261524048012001c0401c00d00380d0000644150f40240c55500122540d000e8142051507640301c0030b00c9010015801c203000810301c50460b0090800303d40000d4084a52511400100509402d03004581510700d9520560000300c43c00034010f544003082c4100b0032810b800a0240c00924046078803601c54040c0e40104800140141c1c400202d40955000d80790281c0003402c2032030305403558840d00000c031000391304600c0c8881c0810500100c0c1e0351094400c00003005850701400040d2004180f02411103214200072044242980b60800202222110b8030103c000c1708000381040c50302c20605440c5c16000201c2c080c20182d000108100c500e400c50302104016 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 622568264 1250 622567014 622567019
    0xf030d090b1b0105010e250504180221010510081b0304140f0601060305090f0703080a120203010e0a0c0206240a15030c091e1e0308070807030305060604 67
    0x360401116210307000310020005110500d0358110000c0d0300d4125a0100240000d50f0340d4104da0038209030a07168007051130203000c1c1000c09a030314560b1441c40b420098554a04241c0360080e040b4504d039a29179403014107030b020020180070500404100c84074405e04081041954144405d03c10f038035498800d031400380301d850014007441d141c94403511003222103c20551603581e03a96240c680a0350b0301042c50800244644420050681004070f942d0341a03401c84d90b01085103589010610f942e507910240c090200e500700701024004036005900401308440c070b6041014180a804180004030380c8243c0c0000456100d0000344405014a4040d540c1e0142440c80200030600b041444055011804000088240400d01d568400c1d6129a0044401406c80d02110542405154000340280c000b603809a40007924140700450351a1104a80902d1408260070803402c09040c0592000318020217000243c0c0000c1800300080080d109031700800d442c920407003d9a44600042c40c010301550380107002c551241c2d8040c40107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 622569514 1250 622568264 622568267
    0xa0608010612110a030b0702030711100503071119030c0606060302040f150309060c020606010e09191802061c05060108162001061401081305031c0b100e0f030d 70
    0x2002d180c0398001c58409600c802e501c0018a03814069070004060280000c208202d02c2c0d0048040c0c040ca0f070103180c3c1005099000410441c01442803840d210203d0010710105082c01d01c20b407803a010b00b042c01000c940792032008000b1803220001c488011030006400311210010000f4501900004004c0c07070a0039030030242840c00e01d0407401c0b400e000d914030691096860f102034610940040e960035030049403c12020a445030002c0d201d0b401140d59501080764186580c000c0c0c2480d246082c0308884803843e814452080300040c80280c03111038446174440346030a0740030002d60b580d08001d04850350152110940b62017903107540001c1d03039070040c4102d0520041404008c004d200100c41020750301401d141c4062008100144482c1d60f281c590958076003903207401000305600c00d4015030305c50404000d80310304000e44e442c0d5406049800304c038071008015400c00d201c0030003100584035621001c84a028030114068091901040c0e05021104030707140001c00002c0280c00500348030812a50700c180c158007429000a42820 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 622570764 1250 622569514 622569539
    0x504060e130201050f040302060301030804090e060106081303111015120201090501050a18030804140f06041424030615090a050121020f0901020115231f080a06080106 73
    0x40c3c14810000751044000920030200c5000e543e0080245413a561242403010003a0000e00038801300c5482c2000c000b0603808006412812200d007540c4900813551021a0740008030240d80b011418002c48404c8417414810500620f020f21052010004d045810004215500329041c0c2c00701000803400f07808040941d0348800f080c01503903001e090143d55400101402c44900c8401080440c0800c8141d202008200c400c2004001300c5050b030740e4080488000f4010070159006e00d0748541e0b8480d03030410041100001800c900c0c03c030320364020000c0303081c070b01d0360880c015000c501611188101070300003082200a01e020500a0020b0086407440c40c144010a004948a0304181c04ac82d814081d2a065000103880c00c2000030384141a5000159110005522208001d810100d611800343d400c14240002c10f0500503d420300302c58200307092060600000122a03040300003148280c1e0060b030703071030000c5445e1030356055244040c1685990f114240e240c40480710040f2a0070303030400180c50341445020405510100c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 622572014 1250 622570764 622570801
    0xc1e06220f24020304031d030721080903250b0403230f01060803040305070e13030509131812090605040b0d020d060605040603050606090105070b06031e03040504060e 73
    0x21541d150201210340c11200041d1848440b8064000010001010b500140a0709062100d500c512481030310903041645800d903e00030880f05128450b90000078034007a502e8a2400b50169506501d8203041401290500c490800009441d02c031003041c5600c0d18440c104440020300d84e21310860f007414115a81c1400428110440304110f204680710420b0308101403107049110481031008004461342d48070050b440b0f4015201c2551940580d1300c0009915a08200340d61040310031103004050784809079010342d11034001c48802a0031038000b0000c0c103804c40080c49500000d84060604086207102440c4c60b02c00d0105951206041000020081080d01c1c0c00070300b40d03816203501c1810301c0c2d200c184254406000b40100c2840c0051507082000c0051116085070080050b0794141d601030143c0e0780c40d44d0502c2003e100d0401d4190004070304200101c04111100c00b0380347c101c000101035802c1c0c103011010482c0301c0e0815901c125142d0700001810005490300e0700c945c400400000044510754900002092050390106 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 622573264 1250 622572014 622572023
    0x140c060711040b0303040f0806060604031a0c0d090c030209070215130f150506100c050d08070309050105070905030c01030e06070819020406090f090905070501050c1e06220f 76
    0x807001d10340c0e6035180c00c1a40305010103070481c0d4540faa43c105e03041c1030540500c911045e03401500041426800c21004440540740c1180003928020078202e003c1c602da1100030800b07007100f0410b1005d0007041007207001d42d0329014001c080d0804a241140100701030300f10b026000e04150f5022402c100b49480e10180307003640c01040d07144444004001403c04076240703541c0040081c00d91000ca140080d03120803c0e440b46000d00d03001e40e04002400507516056585401000c2c0240142d44082075100c00c01e071141c084039601c10741d030341f801003000180340d6038081c04c0d99020f540d420040341c01c0d59400c1c0302a040402ca41c0c41441c1003440e082c00864907054105403103550250255080221130780005101002c0407500aa500f900b5200440d40e443c0e46440040180489018600140c04604800178101c2c020b80102d182c41c2e5006005414003619280c01918a40e0202d000491103010b11601061400232545460036110803484c060302e40340c0b6112202e013289a03000c0494280102805c00c60b0400b00c1c001140408a15621 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 622574514 1250 622573264 622573283
    0x30a031205060a08060408040305070803030f1b0d090f11041404060b0d0b01060314010611100b03390409080406050a03020d0c0f0914010c200913140c0607 68
    0x3860082400f050442e080301c1d0452268031305100030400002d00900403240540c0c00d4410b51511a2480c1e40c03a0310040d21051111000346000c41d00441c0d000c080030390050042c00c0c5140c82e0102c0803455105031b072444a020340c1c01041c540003080610a002211410102d07080b03404100c80c400b60700701001540c0d00940040c0c0400e598118410b4140c56030703001d000b901c0b60020503c1d981580d440f00020f01514108402c11400e10965000084042c010980d082d00c5004810142802e15480c5140c0001040070070781d615850310486119060a000b480008840708000702e038421f100010703004942410440342400940514500366041010a103c40203483c19140a86040356448190070406c601a00442e41144001441d280c52941036542020020b0803103440c41d01c17030010290791410320304440d94280581c0c070f0204524a003071000050344000181480303401321001c0000440407501194a0001c1113420510000f030403c00701040c002c03d5107a1140c100c071540d004110380d03120100401e00b24081c420004040c05030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 622575764 1250 622574514 622574521
    0x117070c0b010303030f052a03090c040e0717120a08070c06021c0e031e031009140108010b18060d0302011418070e0105030c0607140f031c0e0a1407150c11030a031205 73
    0x102806107040e242002803051105003030700c2076280d0315040cec03e2144e140034203c0c00c1c1c0c2030500d43c1c9001c500303107002c61b045218050505404450684034200c005218500704401020114006422407010b0718900380302c290428104c104070070020301111800307501c0d072080e07a00c20b214100b07a035004101e0b02922592890025034a946408420504001340c0c0c2d000451090f042130b000002e0303000011074441c1200d645200903c5044449414000e4100e00b00c40308240503810040020314a00b85015850001d038400d00c0000b514940102240d6000441078869010a081000c00080e1745e0070100000c03406040800c0e0110025490b041c002a501c051605000380120004a100424814850010800d0800750400c0c1c0b0400809044850380303950065007100f00d59481400c8508042a00c0d11a0032086182e520040c00166003580b00d40c0000d0f00e1801c2e814135188201d503404a002845900c00210400d41520390502400b0503150420040c80282c82c2076000e0f51001101101081d8009030107496003030420000900b42c2c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 622577014 1250 622575764 622575781
    0x20708070e280c020303061c0c031205130e0105190f05210616120b060d0b060702100c0b011502030702130e070f0e0a050103020117070c0b010303030f052a03 69
    0x303a07040d0303448400b00e10f080c1510440c650080001c501c580c1c0120340f1507d25042240c0030103011451018050b2020f25185401d01c0041d902d45130710103024500e418068204006800c18140f0740550390048180080c5030001001141015134490651403492420810500e0070020b00110100c081d10559119110f5003240e00d000c0c2c00c0d543c500801c1c0c9108401a1822440c00300e203020f05c804044844c2c14001003145101d10040b500610819036000c00c01090b0740d140202c0d004151024004400426a00c44c0c0c081290900582e0303100440d012484060700c074841c1c80c10150500307c46903c01640100303040c0c0083d142d6040c61a9010041b03036901581101c0c126002c90003480400020200503111a0052140c1c0c4400316188440101c004100e650b440215081513903813450010607910f0030b11000b4003240d4545000d220b03061106d45181d6000c105441c004511406580720300b040780f00203900c01e6000c240d130b0f021202c481004d140a01c070b500101040d60481c0340c9885404054204201c012030340d09030f00f4080042001407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 622578264 1250 622577014 622577071
    0x70f0b18101e0e041d10020f0d09022107031a13290a02130911030f13050616030c020c0a0504090302030c0a12020f0105060609060f091906020708070e 66
    0x640041c1080180350b01240108008805c580011a031a01c54180020f03486001383c003c5903e500000214141003070911602c0d44090300b05290126801010716111507100b1079120311801c040310350031004019032450750a10340307a07128440e411020060100d0007040700e091031b182d4994140301e034820341d08030034407196a03a41d90141c02084c0c144004821040c0602c07400c005560040d050568100340c99810082c0d9681042c001c440d820000c1489568040c400a00e000342d0341c401c5070364002d26035a5aa80118419620182001002c80d0400c0410116108002115926105090751001c1e030340010300303496003240c000450010003486003c5c8150b46604100d02098420700649504070322072012070b12844103130710b0640c0c1d24103200b8203148014442d007884080c6021050088a000351809040c492802101c641409007a5101d54540c03a08403a041210f940b068880d22541415082c0c1c0810080d151820705c54001c1c1040362546c409100303a032140d1702c14018604142034454002e50085100c070b0452200d82c404800a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 622579514 1250 622578264 622578287
    0x30402030a0231150504021b0604080a12050618060a0305060405060402040c0f090506070201030615031a060711090405120316120c050703030e070f0b18101e 69
    0xc00c0418290840f00000650714645516800c000741a1a1418000000f100d20f01e5264030320401e1205010089414181e0080c03000908406003142500c00406a0318174200007643c08a4040d03a0005982143c2980141000f03801400404144194241070000440c442100301d011442d00300d180740401c099607910541d85d40156401410348840b0304c2d207414103e46401040710103034080e9080040034030000d84180d100d000d01c1100743d12a210410704010601c44a0740000d41c080381070598941000c500c014403010084100a15030707a002c548140c0d2100f00d800444040540203004032418003e401c00945000030180e4000001e442c2c0b001c0503581e0b4204907140004a23001185e44010000c20f120313450cc4040108813800741030b40c881070095404402d06c04100c034030780980312000620511450000038401c2c0c12255105e90102c0842c0c0e5082d451b0a026991240c40da4007500528200003035070400520890580aa01e20007141c0017041003002401c06480c0d07a91101ca003100e90b42c1807148070007201e800340c0342001c003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 622580764 1250 622579514 622579519
    0xf05191d030f030c01150f03030c0303140c03070201060e070e01030213030c03121e051207090905011721070b1e130521040b1303080c030301062c0105030402030a02 72
    0x34007030b800c8281a01ea074010700101d2a203500300800182407602c2d00c00030303d0880d40007070490f103156851a2070489006030f101d0011010551107120301400071800300f00751406500b081070400c2d600d045c100c1c006421901c040d482090003130941d50400c190603801c0920396920207801c1c01d003d40d54041d004034500300034402e90001406480c50306008414003510f41d1051109003c540c0300c0d090601420807100da0303080d2002c802100001c1003005070403000d0761032800058000f003d03070421584c1a501c41690000343c80302608010a00ca10071490136103251000c11030040308a9090300385182d212440d101150061042580c043d006043da440410044000380ca041c03a00c600480388000d0140c2480c803c070781102e0140c0390083e1207600c034628104030b0507800800c02103115401e16014a00e13041c5400d0180c1003a420010a6400040d50712500001180c8208020f0040720390032000f03990f80f50304184002e800d4981d6040c489644003194040f4a00c400c50b0700300340182040d02400d2850310381ea141d100185c40c00710300d148000d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 622582014 1250 622580764 622580773
    0x60b06070501050613050f18150115021b0303030a0e03070b0c1306031a010e040905030408010c090b160b0a1e060f0501020c0307171603080405010f05191d03 69
    0x400d12906603c0540201001c41d1908910080d214100e0155001550000c00421202000c9440f43c082c0123101c811707124040090b101e1114001c65800300c040400da108510200d802201180403a60610a852555030013503a8408400ca041000c250740307003c001c200074041c81d80c85c02101c1200e1010015100c0c40c99101c9880311316441c10312141055a00903000300038018144100125810f80240660500024481d60344041311175020011201c182550b8180c42d00150b45410300400b0960500080000e4011500089069580d50740000e100781c01560064860304820701141400036040d2242d1300322603030003850f00245070312008a030000828910511071199034050100032010841e503041201103c105290007a1010358070001039858410800c01e00380c2c56001003c0501508146040107813070302e11020211017400b8041da016580070303011500103440c481c6002c01d04001d2036900203000c1ea0220311a180c55818401d041d00700ca00000c04540b003110a006030040e00b0714844c200040c1c00400b5141c01005c86 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 622583264 1250 622582014 622582027
    0x15040e030a0c20030a030804020a0902040b180910094a030414091902121006050a320d0b01030b06090a050d060f060f06020c090f06010c060b06 63
    0x6030000e288410200c032188900c69250300c010548411414079444040c0103020b17840b80d9a50200c50640f40208101d80c0003004060104540f01300d0b201500103071950842e40c5984029070140030704458443c1003900d108400a80c204035103c00021450400c03a4154040800c0b0700d16050350503684841c42031200540410340f90b4079503203184031100d410066501e11942051000352209070f400e4880c49907000b284840100e80d50300500034200040400d40c440d843d105616120307410084400d041c3c6e44400b02c0b20054040c101e051001e6160304002c481c00601480c14894605072101002514074030310315001050b2920040c1240031728819022540d0701100802050b1903072460507094010040c441540c107140043d01d0300c0da140702141003103022120000e00091100302414541010132022480e001000c54019403900c0b5180c020078034a0003030f00c0203000c00c0c82e8549200c0d402d005000b0b103031102010f5a10f1068100506024040c510b58144c02d4200b1028a4120503d640a0909002800400103890b420900014a9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 622584514 1250 622583264 622583267
    0x4050c03060f0a0e061b1e030717130b040822032406230604090204091d0a030905040b031608010203090f0706050409151502010506040f0e0615040e030a 67
    0xc51141004560400800540a22580d0b580302c04503001c103003c016146d101d1702e040090070b02070005224518962210402c1d403400d142025001600c04c01c01041060701035201504442c801d85074014400d00003040c410380152540c0400e03481c00b800142017002c0008041d89400c2c0b00c2e4281c81c003404d040f1048603914035501d00d801606403240521002901c600108105004211070080108980208074500300380e000c080144003080700b031202820352088040000091000060018100030400c00d4030019000c9003d03000120003444040b02d202e9642c00403840400040d4010000e001520f6054a0016000c00f40c3c101103403401310150303e20200da17455a0750010340c40105400070b512590b0840142c0e1011701201e56015a10300150003902c0c04290180f005100780050396001c15040720342511903042d429170b2944c0c8140f0721545034001c0c40c0180d44a9042041d603040c2806400041016050100070303680103521865200c1d107001e840740c3c11a0500410f442801d42d210b4010441140901050341d640d42c1c52a00c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 622585764 1250 622584514 622584541
    0x20d0509041109090412030f0b060f0c0102091e090709060815030309061614070510110109080d14070e030703031d030f15070201060e07050c0106080d090e01050418030804050c0306 79
    0x1b180002410100a48000c3d80b19001c0c4400880c0041c01281c1015000182c0010a80111002040a66003440b081200d6a590200c0c00142c5941d84c00e107000041c002c40510901c132000030805014083c580404100c0541c0c08200355510541c400c608183e0a940c0708000703429442100c2d0001d0344101c1c0852000013450300482d050507010b200d201014181d0008401d80d5480702010720410fa440700016a03050b02c014005d000082603200460000502803141e59103a115541202c02e000f14450754481c2d07056241c00d15007a4840c2c0091082c208018412500c0001075550a103d00004040040320300b08503500c8050150840b00f2140c00030241e9441140c008562942d071042a20145030002c1154041620b45006100d0541500e840300201c0c0700e540d482c54815101c950110840380348643d84e6580c0011542004d2101054071400e980e2100d50b081e150034a40b545010060704050302c191301d84042c079200202c4d1042c41d401000d0b45030400900560b00e80c2000c82c14526112482501401440c0800a84004550b03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 622587014 1250 622585764 622585793
    0xc0a0c23030f060402100c0c03140c0111071401020a08031321021005060315010b040f090204050d23030706020702040c180308130801060b0910020d05090411090904 72
    0x440180050444500701035480c1c154140840d515042800401c016040c480028880210642800180250340342e5a41c00355100580c81510f40441c46440c010130044144814100b0640074030701566405d81041e01c094440089201d6400001c4c081c3c484100641d0003030103000d10090304022184e4403860b11b00e1300c03a841c482005c001143c1c3c2100082402603540100003205101c45007035801031820f034181d44071540040c04042c0c240c941c144103070f241c00c0c21452204a41c0360f0290120000440d21103192401042440350603400005250340107200610130790300d8581d034201981d0780120b0100803032050100c5000c1b2440703142d0300b04141408002807100500146030000e104861017602d0811030300303000280c2240c0100ca0701103000301d0031031101d80c208089075849024000e40055170000d8600c45607581e00e21801c40e1101c2e400141a8040404c0008441c541a01d10782020400390000d850195000b540007040b2384901c200161240303584e4642c85440340d601c101907900030780000d018200c0368200b600f0000101c15003031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 622588264 1250 622587014 622587059
    0x100e0115090c08011d0f0c09031f050c0f07230a060b100504123002010608070b07080a030c0c080706050a0b030706051615230c040e07050c0a0c 63
    0x2000050071a169500704685d514954901c0c000d25100d0681c1b04040b00d00162205400390024407864806681c00d014110070b10a8542c804500422002c903044140e61006106400d410010b2258404000150040b261a69030017402080509000c244d640c0407075000c0101100b1030320640844070704200d46903101e480c600301c2c12200ca1601000c2c8c55030446141c40341e07010b101045443e440700c86000900114a06081000341e105004c444a109020512952440d0360800010b0303443d00b504004191040c04070780c01500c01c1e241d0503807170042e13a44c698541610035080b1650400d95246040d1800c0c0f032003180d0303014181e603101e000e565a810040c00d100024150a60b90f07168002c1ca0050b04540624001480000f00d46150b01c07101c0c1440d00210310b08903a403841250030340b0b00c0c44101480c7c40d1201418856070b454001c083c90202d007103005110340a03105000041207103012840c1080b0900c0242083d550745036012103d413070600c1d034810302c584149041032042d0744010181c6503018404a2032000e00c3d4241421441203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 622589514 1250 622588264 622588277
    0x50c09061222051b0a0b092202130e0c0a2703050105040c0e100602100b15210705030f011701290f0402070c05040e120a02030a0e03010c02100e0115090c 67
    0x44d1400c000542509104100c103800d01041303684011700b00348015102403101450300c600d420b4180061202603900070562015206003c9400b030010341075032003215070042c1c6860a40ca08000c11840013034211840d0b011070440102e9142002400790707045044080295038010003c4c0981d050500d4000b90144181c054282d924005100003104c10540e501701c8822135407503070300400c0c200100c2585c440043c00391081d561b802081e132440154080300040d005000300c8500302540626160100d0840d110b0810241902042100c01c1040c48101d0f079080503054151241e4030f412501120302c101d61580117280c0701c072601c0c3d840c20303200d0002607441f42d180314190312a0806440c09582c81c01a8810401280314035a0b0003418481010400d01290415510005040c030040f412100f59600885c482c0060b900240e24240040c0c0c40010072000c0d85134009828202a0b00981c02031084451381c0c600652118400440030100d02d558100600400302c0c250010800c41007038086e52050b40381c0350032040c17001e0242010f001012452 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 622590764 1250 622589514 622589563
    0x10e010c0f140106092301050109033c031808150c0703020c19090609050c03060f01090f060801050a060806010f1b0b0c0706050c0906122205 62
    0x2422260369415440980e11800400c1580d0300c01c105140b81d52026201c0d941c910010070320354403070f200700465805141020501d00c10310340d1601c001850142c00c01410080007c030102700107094003d1089281c202440c006661a1242c52901410100d48106150400030120400103241d002103410380b03da9100c0c501e00c2c000540701c4d61410355401c0c020032810142e160391070005030311540d21006462451b00c244180c030304070b900c0100000c007021800c3d4100044191041c00804c0546c003240b0562006000c0290f06002e2454200303500d82050100078120744c000e607140e8050749100d0b0301c01e4041030081d04c504c04103c0c3d40c03180c5030750f4014007440090003102d0280b440048007103549805041c20500c500c0e416543c9200c4141842003c950061600410143d00b141d0318007084000b07800c0108687c4105c0c20560060388454142c180b450a40e400601200a00c4600700044140c6480345022904001020f036680300050f140d01d0402e1200d1461038920044000c0207019a1080001c0465802e40d42086815809031100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 622592014 1250 622590764 622590767
    0x40612060e0f28020a230f0a0e0403090510170c1603110f01140402010e0f030601051219050f0709051005150c0109110307080601030b06060702061e09010e01 69
    0xb03944030a129640c010200c0d48540035032040c00d0030350b400c01110300e07080c2120303254041034200c003035a00071002c0c00c444401444094020460454030a900c2110b0344448201d070440400c2c1e8030080c2e40100c003a94040b001c0058149405900000020070001e00303202180162510010003005c03465207a108007401d8800481c4100c04500142c445e1481e44454032803080c0199a420794013204980d4104a1501441550740076581c0c0a2085903524121990000241d18141c0300040915142c00f8115100d4141410394104541300000c03103d040d00c0042e40c00e41001d45040400f1031414240d06c01c280584550032060104020000c44e0340c2040304881c40c115070400752030340358070000e6030317004c8511055030302c00420200401e1038502c2c3d00403d1841c103803280a20b001d18484600e425920b81c0c590556491000315201a41c1d0f003400c001c203400600562000d0003055040d030340c0301c00b2005809004548203030f40100741c2e032041d9601c002c06c48890b1b0008814150600345c10950b44d0301c094100c008a1780c00714500e1b00f080b025a5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 622593264 1250 622592014 622592023
    0x310020c0309040203041403040305012a090612020c010e0d0e061e030a02070b04050c010914090a11040e07080103151107020d230303090c042c0a02040612060e 70
    0x480e00440076605181007803003400000c0d0001041074800d820300410000e0880c0007400140017440c01140045400ea81e50300800201030824410307610704280b90014035420586c0300c8415000d5507413525002010009003140e4101038054801240002d500c2c0c0741c0581841d810004040c0840d003d47e44410080c80c4003007040050301d0103071072078244034940e40d808040403140302d00740110307400030103001c00500b0030740c1c1a2188190000205c5044a03140e000f002c85c1e01096270489010001000303810320400210310400041038140c0000303030030304905030303243c00c0f070844004411000d032405016082c15800c1c1c0c92801d00c000801140c0b0a110682e202034403000c00c040340c14024014640c0019284041e00d2600310b1550a000c0580514101503c55002500740c0d81001c1200d01281401118203038015a16401c0102113607040813990201ca40c40366140000307000ca0605490080c400005042046007000840c52011a090081800d0002e6000f842c008007c200500521548100103000f56410000c0710a0010200c2c0d64 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 622594514 1250 622593264 622593277
    0xe061b060a1401090c05120106050c12090f060d0615020703110d02010c03080a0e010e0f07090b010215090f01050a022d030a0b011b030f021606080c0901020a020d030806031002 77
    0x2c84450030052040c01201d4004c1d80c801101d52901501c0e041c0005c0c0305100c0c440b82a005100020390014125052600800c000c4002c0820140701c103191803035170f900050140d0320003d8018020071001c1903883c1d981400343d11800c002c2c542541581c14145281000a44944481c08201c482d8071400321140450f05001a01c0c0ca180d90f41a15800c10b161038945007922008401000051007075221103c1082804080c06071505021002005203503044030342c5107145c1800002d03040200c10516103488403c660b0b90005d01c0701c04001e01d030401042d043e100c84941c54100000c0004004080d82080148180c29400b90f00034103559451003244440100542a8281204883e41d071421440e001480400c1c18080c2952044842004c14105000e16100095092600044011055000c10765058130122031a4040c08601c10302380002c07070030135030040c1800000b800010b80901210080d0b000402c40300400c0e40204220218030790004c0c0007243c401c10f2850010043d402c2190b01750300070b0090704109600380519009440c00d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 622595764 1250 622594514 622594541
    0xf0a14060c0901030b19080d03060b090307090e03040f24020303060d031b150905060705030403020a0602030601140c060103060b0a0f0506030403050f19090e060f010305070e061b060a 80
    0x6404980c2c00110080c1502107002944480301d0244030421002c03481c5590001e12540f03016010410403444090708850080d071001c1c1d240c0e40d00700080300315581c02248500c150341d0b80742000100030116404461650049410104030902c4e400c0012802508081910f45402d1400c941d180030003542c0601241c80b404180d0b1616000184810303d040040c0c001c0410903858106c07042c10541401c00da483d069240d004000002401968603001e200a1040034040701c0d80c00b014504049155041030381c1c0080d5140b031415009883c066001c80491016846240341c041402041d490042d1030300390856102d601e9900a2100302c0b01145040b0265030729050040c400c000301c400301036811118078900010300c41185d00c0140304904001c010041200d0241102018001c104c00150106500221410000d0729030b1400c0d0700481c010750b4a0101704402c0e5562242c6008100100b03280114450305c4141d01178401d0030500e0100ba0344a54081021f2034498266441c0c104c5100500c4111001a2140d8219200311003030400c0030364 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 622597014 1250 622595764 622595767
    0x3031e0e0613061104060c02040b0105030402030a06051509010305160608060f0909070f080703120306030b041b03060e030d0b0d0c031202031e04080c0a05220209030f0a14060c 77
    0x22010602d0716580700119009080104001d100040d00302c10950290b0024004241d82d40b1401c419410280304e192000e0400b07080051075820310b03800095070b40d00d05203070084c5a00d4440e000203080c4401240b40701c080303203009010440156113911303182d80c0f101481c01b4092402880307a000041d48a11070030b0a10300070b01001e8103002c035a2682038240102218010a40340c4c003480b0300c07103000a0721020b82c24580300910844020300011420752500500007490102031100b01401d200e801d02c042807011500f9600994402031088600c000321008001c1c041c500d6001134511464040b80303112120f804401442c4030010340f0410089121848104140400c0806014105070b03801c403800d000080280300541c03800013041c01124281040601440040540e40c076040300f01300300c042000c02046204008001000a040340d600d00c120703062002040850244c490383c1e592231140d40b0034055a040c403940c1100d410840240c20780d030b0080801e8840d10b5869558000448055031030170b0303004121038404a241d5008040254003c3d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 622598264 1250 622597014 622597021
    0xa03050706050a111b031605030712020d120c0e03060c03011e0b090d170309030d06051e0112061214150709120c0902030a0506030705040e031c0e0303010303031e0e06 73
    0x100c40b07064492200c5c55040c4010440340d040482c00364100b03400240700b48025590340602d803074a034109042c8242107000390350146001951060708121b16041c0300c00c402e4400594040701083c112900c3d4220001c294060040d501440240380c0d4480045040e514211186d5200c1004901d4440c0f4008a0f40308100380c90405200c00c40c041c0c07074850140c0ba07420340600c0c0c0411018034220b6801c00c80c1c1e401968604c18035400060f6903e40d00c1038501690700200310440300784100b61424402d1180101a9035001810800010355800c40001d080d80200060b040321030b00500c681c604c81c6000100f240848a00e00341911503000e064546102015880340b281e403003030750380e41d07105c9207011290a0b0070008150b08803481c0b0622600410b054619101a40c0310760210440480d00f400d101d404d05050a2064203c0c500031070411052064400c0300004a03040c540b0008104903180c80010b910f1001081c90030150503880c00000000802e040e8150003071318240c1010401180340503400c8250104a804100ca000c03415040307031001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 622599514 1250 622598264 622598287
    0x90d020703110906040615030902030c0f030d03050a06090f0207020405060a0501050706050915132a03080d090503190906080613090201110601170f031e07050a050a03050706050a11 79
    0x9a40e0044d2004e031001c111181c40c0c410380060080d560a0345000295259800c40a40c50100410000c0304016607104540b4050440800e1311051100448810700d5140d9000c6854204140e02403801007442c0b001c10800300c40320491840103540031007801c0c2c0c8120708000105446207000024101252030507101c00e46440d030140d1f9528007502c002020500315028150350f10030406c45480e040c611984032100d41c1d8000d0907051504002002c0410868040050f000205400344d0000c440c600c01034a401544543d203603590089844041d000d10340005003540004202c20100c42c824a008610305000d640711b0020094452400f1216410225209a840440171003500603050980d4001d4080500601d02952600204407000740f0700700d004e03800036001070f6882485054555060201c404e444000340060740c80e124400510f100032410074040d84c003040d00d00290b154100030701040309035540d1342e000043c2c1d800d40d01a801c0c0a0095003001000f515030500308800120f0310403c5120708179840f8403242505c2d0403d80d80102 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 622600764 1250 622599514 622599529
    0x40e01060f0e130b040c03110a05180a0b030f070c1703070507020918010e060903030708180601060e12030c0a1205070b040f110105040e1303050f030906090d02070311 73
    0x90a07002e2140421071812140c80360078009504051202000ca50020301205000403078040710041340805207401c1002c0c01c110b48207000c07200e6111345468420303211021032180d0b48480e03400070801d982c00240c1100001c0c0c0040700401540c40b80c5d540c4203407290340d5640d540054401c0031410000801740401380e40e0203500c58001034090350300b01c1d41c68030f8110f0038044541e011030754506003074502c040740100c210410002c0c0c43c401d0242c2074810301000080e10240c10b000010300c1e5680805003603031051003928400128405004210a201c203420b201c111001c40d603440001810b200390101c2d0705805160703609480301803650000102ea9290300d07120020000e04417991500c10300c01f4090003c120400604024002c0032403003d40b041750095018240d2116545603500e0300401510322400481d05000041c0001c101040c089964954070148074812440b00f2901c070b00d401ca40c584030b044000c1800d8103003c0300b481110303500015654880c07580d640c1100ca60640ba410706903a80c4010b440001c1841841c07410000c100c1c1000760 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 622602014 1250 622600764 622600787
    0x9070216120303112a0a170c030919081606080f060307090c03141b1602180412020609070b0a110a050102040b071a01060c0f230c0a0b040e0106 63
    0x10300020901c071260740840b401c2d40a0034020040c400260250b50a542005c4000d6180d680310710014405c3c000556180b510341607002806942014010460361550b5a0510480c0c07070500b0002d000e503214410321030801c2c0d05104140034503080348c42416080101006031451880a68071aa1181c054035955800803038800e00000f000c07107400d401800300010301e1092034098680d46400684000c2804201c5101e00401450300400740e403241001c3c3c42200024903111000c8a6840c20781e19410342c441002170010403001050040d642d1800000c000070403040c86191041c03d034006046500703452440d11400043c83d82c035050390181040c40002003081801107800b40d140e00b80d24030b4540c81078070320300a400e81381c40e42240c0182e4042058100001250b4041104a68005407800c03842011405c0e02d50421200820b203c0c26403000600ca58000e01c2e00c5d00c10720120909200c003040054465800030320360722b134103e0788500c46a001c0300d02941b8040c1d00802c010b02c00314150b5050703900c40d903804035850f80b82410031224000d812 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 622603264 1250 622602014 622602017
    0xd0c2309010c080307030e0c040c0905010c0f0f11030c010c050606040b0109092c0102190e01110703030905010f05070203121b010c0309031709210405031b090702161203 74
    0x128281c00008038020090341c42101c25850001f01c03004900541c44c00c1c458094400b0344168034201d902101c0035000b05025040c1c41080c640160010b508cc0380181a50700295006010500340b0310f40c4904011652540e440340e04019011381e40041c01380c0b001500c8002c541c40004105070001c0b03000516a0800358010300d02c1000514004e50010303030741c061040032126036151810516485407502001e01440300f544804c0030200780c008500c0c00118100c49401d810603400203200b04280750210b542c2c140c2c468441c80e1480140a0b042d0f40c012a40c80c60090074291041c03050a007c12020b8800c1e00605018409a84c81190080d000c1c080b841742c806002d10541d0700440c4813040755000d2100b90038420b40244030301c0d10042d0060f200050001002d040182420360a0040805444204030801103000760200f00c0808104802118811840b1041d50b100828040c80d08800d4040c85070500d010030300328a800617034808041c20796410281d6100c0c41c8049031a005001d501c02c0d0315001042c0100009000d42c5c0c56821502c1c001d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 622604514 1250 622603264 622603277
    0x2208040e101a25020a0e06031f0905070f06020307060b220b0108070306080a08030703140411212d0a06060911130b03040602090a08030307140c0c0f04060909080d0c230901 75
    0x1a009c0d0101041404595982081d55100c420003005804c00c0400f01074088403070351060440c60403e000b51b8a1190400040286803102c1000c2c44c41c0c0c031481d80018410008844910800c1d030303005c000302c0080050286071400198030302c0209245a00912804050701d0080303001e826090300c5c94540014652010700b010003015520006c00413801490030010b401075101740380c0040e149440400300441000035448504060b9109103030a4030342d030310000e0b505c2c0401c1c00c4c1060505e08990341e0700680207111615414280c4500500a40d4010000c460340860285c87c6d06100c10403540c038200c080b104c21781c02602d80030954520a20300a200c488242405542c0c27081c41103801524094518000c141150b01d0740d808a0401da201106004c1c440380c015a18040800c00303141c03450f0030a03006c0302c50103030369810403032045000c1e4001044d92a01307a00c954004a0160084401c20301035805503207022074043c1d115005011403079140c031140701c006500c41d44540b4442c1c01c009074031100c0301840c1070743c0764660380c407600a140c103000c3c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 622605764 1250 622604514 622604533
    0x100203100906080706020d05090108010e07121e150f0e1906060302091f0f1407140d140901020705010e06212208040e101a25020a0e0603 60
    0x140c9014450103040010701804c004c070315140c0044d00c0c11034543c41c00c0e01032150900525005036806120541154282c8501408544a85c80203491140d040c040c01d0512600b00b4040249007400c58103880c5070b503504500c2c20480d5914140300d00f11341c80058016040b0a0014003820040f40c0c8840c100c3e40e400036016106c480358000030900003021140b00c1d6000310042a00810701200902d4007804084071b40340c4001c80442e401e400c1c020000c1100e900162410140f001c14640b40301340001c8801520b5901c2e80c440e4000303c03a00e07103d800850740c0341d0324851036800144512171880e80c08403514054031b598540c180c0081041e542003c0064440d1a24500e040b50480b10610000034550206007000200e801440e44006a500b051501c241c01c0c4a02c125128021a11511038003001580c42d000f1a07003158850070415040e51030340007103002c2002c41c0e980444241c0e0050700350a491909605e00402c5114648840e40c246510b01d40b1800426100001d0080c2d400591880b0401c042d00c070400f24139074040c90040645400c9923 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 622607014 1250 622605764 622605779
    0x30503120c040f0e040605010512120c03130f151706010c020103020d0513030e0303070f110d020a15021e060a0b01050c07140405010e0f0705070303090803130302070b0306010210020310 81
    0x100382e58003d13079130034003480d0070700c010700800b445054054031007980d40e20460002c62012a0380c41a10900030008032100141034031380f0701380500955185400119000800c01c1d6104440c03500ca40b040d0003402c200301544915800c0041c043c2407200b06104c18000000419603031800159012082c2c403100764141034003040724120040d1148145441520b4070485404002881d00300148014520301805001e6402005a100130524580343c0001c200e0b4001440c645031202c800106591203a0600c000303420464900012840144801c184402d0085a034200c4445041c1c81054482a024a2140c0c0d0300d950480300218a046c1c030582c0010021074418100207207095407941e1210f103044000d9001c410314001d0520b17080740900d0701e400781c1c60041280254144c5541040c40c030003149114080c01c034074140140094041c08041c0642c1028001d1608101980d841e483c01c1c41c410000d25101c81c00460050203500c001040c00380754081508e01410341a401000c80c000c03e4000000258400f619905c0068240800040c095 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 622608264 1250 622607014 622607039
    0x170d090303050f01050102240a0b061216090f1421010b0102120c030a0804050c030723101e09080604030201020901090b120621012a09030503120c04 65
    0x1034441ea40000d418545025004001c0506030071450440d00040304141184d0003034002081c1001012564462030340b60448020024800c00642c01c1e00b0542c04641700c0c95200a03d02504d110b100b29001d01041e540c00c18108660000070b5005034100780410807424800c0101034a40d01000b00310140000d0401002d948403000501d10003e8a6095603445119114465034180055034980c40c8100384182001d407242c03181d58881c001e112182d800c008802e0001001d0250400c00c6200c03004000d81a581074540310313880112103c80c10440481c0040d0040174031a103904104140807d0809d03203540d02c201201d081424103c62001ca141d6640810401c0c80c0003190109080c020640114400e03000103a0301c0c0c02c2c0d0800980030180540c407544d00c941050241c1c20030811850000b83d8815400c90301440e001c01c42101100c41c1c03e010391214134042d0f00e0015507030944483c104201c4804565500c0940c071203068280d044a0b104945e0200a09a400601c41c0c02000c2440710701c0340760080204044181410340755050300300d02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 622609514 1250 622608264 622608281
    0x5071505010905160503040c2714010614090d030e0f04062d060f0e060715050a0b06072f2e032c010b0406180b030c030a170d 55
    0x74076661014000c484c444c51030800c800c9030759410110300b0f500c1c1a85680520b1882c0d8401e0155400e80c8078400030340e4550b11041040c0c40c91031701d401085003015003490203500c0d14003400b5100200d920416211541d140d6030040e0303000f445000745403440c1d0f018076680490702c10840038007841e00308000a80380d03041540c89000d154003506d510b178040740041020024900303038016812003c03020f9803c0481c0910026901400c4102041e11a041440f138005481000c240d80f8800c110001d04140381503030740c0a045603240e400850054030500418000e44940d038041100e40d120f116001814a280072104004d4040100c100030358804c0c800d43d0401500e41d00d200444c8968002c03a0780028100003200f0241c4030290a00e02102e13003c851450100400342d86911001c503842c02d11109078841d0303440096128104071003500017034012500600f05000170f50390707806400c3c0303491040c0090745412402c0443c0c1d10740b2403c0008002002a40c014001c0034410040d803642c0d906000d00745000310800c1c804100d000c1e1400c8460080009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 622610764 1250 622609514 622609529
    0x50d0c050903010f09170c03040b0415090e190b030c0a08060915040c030f050c03030c0f0f12040e04031106070e180712020c07050a1d011409070507150501 68
    0x607262000400c0500316000315450303a14961500220b440482c03072050105040104420800d581c0c0e43c8454203c42c55809554403050701c042c070006011400320021580700d10008815151800c03215211020100f45440c2102c0a0401400d882c410802c01400c6820480300e52201900350b075002c0c0c20400c049840c2d0b012980169031142d200c0e000b44501864104155144d40001640041c41818950340d1501414118880501040c202022040c1409024400c1c8851010014112030b559070701a030f40c10791540b0308030f0403030011805440e07002c151200d00400c808aa80c2d60a1029a213070604040c0e910342c00d40c0c4094070580c00c105058400c2c0c01c41c0e03c1c2c10400c2c28000d403215202c0040c41500801000203e041e2910b0700307840040ca01d0140442550000081c16001c1400100541c4625521000510303090640c0d000340ea10008008000942c0712030281c00303465004078110018500d030707201d00090449184421007140c001e0b201000041c103030b603c179001030403603940704801c4a494180e64103080030030749074203810885 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 622612014 1250 622610764 622610767
    0x40b04021306080a0210020f0a050706120e03030408070c09060308040311060c0d12090213050901151d100b12060f040b1c020a0b0a0207050a0906050906040c050d0c05 73
    0x25460140c000794045001d4280c107001c100c1c10704030001d49400c4070081c000d002e0150003031032160b400c2c024000140404175a00c112090780c2c2c49030034000d07a5600d07184152004603101e284a8200201c0901410680765503010003949940c48a96407141c050380902e0059030741a00c100341c00300300e18a05019800040d802042d08640751130841c1060894020070350710305445075600300070800035040c001c281c3e81c004013421708115081b078200e00c0000340034101c0b404000b03501ca034030400515001c0c00143d101d20b0003121600001c107c44010711540002003100360080d001610714120034446051103a419482c0c0c011005c46022517519a240c90808160304240301c1c40388034100e554200f10450510018018035950308071000e101c1d0101c41d070b0100d022049410a4091940031482e02202591659085040180491070445980e0307212008006d44600e221700555218036001721001411090a020301c800b03603040101154100d4a4580404c00242103d0070644140501488580c840f0f031042d20070192480300645416 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 622613264 1250 622612014 622612021
    0x60901061401050c1b0f03030d0e1b010c061119020d030b01090f0506070602091f02060906010f140109030618051504170c031909060f0305040308070c020612040b 71
    0x80003080c0d00c41c44528104a4240316960007800c0000c0d0448000d9018600c1140702d50303a64001c01c0308000400401600f501c00081c0090761803480354407000d071020f200402c3e1024841d44881b5025042000b495071070001d0085a41500418030a40c04041c1885028504500d003200e1681c11303000441c02075a4103405a04940110f82d0f5080d09405652003002003441c1c40c10401d4200300c00072590380d0042c001c480c01040003042c0001000047c0d03040354032010004205c0203001c1c40d1380041110200310520724800501590000c6007908000240aa0503140426030b80c035a0346d4200300200c4103003460b038200760b410801120720000c0411440d103c1c00c40b01421501014074101e41908000f85803010403600a00c0b440c0044042001060969000701491500ea11480382e032740e56010502850b501410051101e02210240d04011480e00f00000e070302259855140c0040c1c4400b42c8405400300c1300d04850140108108800150f41c541c80307180c00c01d5019100400d00e9003050001401400541c400f02c8046a05183c50000e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 622614514 1250 622613264 622613279
    0xd060b040303030c1e0c0c0302090408030618070f110c0a0308031602120a141e1308030c0601050108060a030510060f0f0b25050d021c05130b09010203040806090106 72
    0x90410f54050b50412508480d42085d19054202a54108208210394010607100708500012900020b54000700100058241400c201c0303c0e0b544299000d81c401d0240305040a00c0e0704441410b42d10400c01600c464144010481e426030302986150070b80c006500076204102850382d0340c00807403c05035000b20320380c64a81c038019401c00d4180c983d41e00c40d41c0565208141c9444075860240c100d0b184640c140c038142c40d1220900c444c0f50175900a0140c004244440348601042d401e03200f05c0130700074081d01403051403145c039a41c812440d128822401607502c1600b02c0001404554011490720b904044007903d9410310716503035142c03103052508001e08a0301c005c0c0c96980810040c5803015088002d070110203400da1040b0300e04051002d592003611a2032402047c0f0008850408042007280c00e1407a420134255005541d083c1d600a440d540590101a03040c00c01003590091039100700140c0f020314020100740144181000b0000c805034005a0616046200070040860501c50500116009962038000030800c039050541 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 622615764 1250 622614514 622614521
    0x414010c020c030309040e1c03020703030516121e1a1f08040b070306030218160801050d0f05010f0c0206100b0304031d040638040e0408030c0d060b04030303 69
    0x84040c215031210401811541e0301100b101c590403c2100c000411170a1002c010341070802340302c0383c00009082c0c8114035903165059002410824401d60b010040c60340c800f10580c0b0700702d110035140030000701c419110604446855000d88044240300e588040b1106065a105082d141c014441c81d0ba0003450000710500d80c10716202d25030880302c0640c6414006d40d04050000c00c0c00350300400103000c07140c500d40841e0005000754041c0c805150090a145121071840311f9064403c5000e5400781003003000ca03540564090b11a2840a043e200020b10300102e10030661180c003100030804006035615540c4034852981054980300e4400d04000c1a0081c0550b4039000301c03410746400b0154080c1201c00c50070410000084c0d0321480a9143c402144050f031028844580494000c0c2602d822891012040c4500e0360300a00d0b80d01c0e648003d1081118060280c001040d403040d61500852160070444000a0040742c0050218005181c0c840002040d9034208800c120104040c0d030003660010484030400241801410b92600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 622617014 1250 622615764 622615781
    0x40911060f0403150608030a1b0203060403030507120525030204120b0907060201150302090403051b010204080f280201170a06050117070c11010203070510020d060f081203130605041401 81
    0xc004c102040c84c1c040c40036100e12940e0000d23410800b28424004038404a422058007250700542116414509490080c00502044d82c4010204400345841103010519010b03d61144101c00c0103100d21100f0700a8501c01000d040e42c0200030305409010209100848034120103c0b18001c0010300442d007400c1404e1420090345401600c210b9051100c0948140350211541d0308803a03058500c06019500c46c10102c40700d00402d00c500b07192107031000e080e4004500540192040d00c002da4281c540080074440c4466075a11031605001c03002c41210341d445494000900a0080c41313006060410302400c0c1d40c54150b01d282000c544075420240e40b0031050025503400001440c0380c070840d00e20350700d10307040022014042c0403071014010007007508803d130807807940d20034000d50b4503459002c01110200d0034100b6076103001e9005040c03203010b024900340001840309600109482141c2019000e01448580200d00c16444c0e8001030020346240411003030a80080c0030352041a1195000350003a4111464800749c00c0d080d140ca08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 622618264 1250 622617014 622617053
    0x1181b080307060b0a0b0a0e10120203040f050f0321100308121914130302010b040608060105090a1b05070606051002011508070b0a030e07080a0302031b0714040911060f0403 76
    0x902c803c020443c0c010071241c8c01a0b2044a01d243e4030919070608030f442e01c414400d030000441c0040144005c00580e103205100c0d2074419401c2d907003141c0c3d2120f0762a1ba64001c40b5070700000c0c17590485007580e01000e16804030750446811031480035055240d44800745a58800c000901408d000e000400402703008604020707402a0003508180080342c141946c590707010002400315160070749200b00c1e140404d8000d6005410806000c2e00030b0205ca56039140a0362504024400d050051111200044100c28140304d44480d100840412401803c4101c0c012982c50308034040466040387d56610100b00c0342e40345416906210880c2e400410a80c9640b102c41d035070400b0b2588041100d0344141004e1000390f840f0301c02d07640b2280c041d04d07000500303c1c2120500c03032500c1c0c5680d0025001d4003480400d00306040d804002401c200c0d0b40302c072441c800b440d01208007076900c2d9128800d26241e075110070344568881c0703000e400c010700444c0a00502102030900d9400140183d12804050f030a0a100103410004c0043c6102010503000c2403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 622619514 1250 622618264 622618267
    0x1b1e0c05030a0f031d130603050c0306160c11090c03070e150418090c2607030209010308090d1208090705041506030209060f030c120901181b080307060b0a0b 69
    0x82e80e2640c80b480d9210f6001028020000180d8035401c0056807151120000100381102c500403684c0760500400c201c0c0400d032041d0282d00400070180c103001411038040c0302526982d05010004034001c03500106c2101007101c103400c0e030149040c550307038488010038000e03060101c4140c2c2c0ca003405040581519641d400c0c0c1c600a2503000d1400c0102c48514013958200e41c0c50141103080c141d0040501c500a0100c480014002c1d0407002c2c0c00700703c16084a00022080418846072059403110f82241991054207200c0254400045001400020b40e6403002d80480c00018284902303003002d640e00e41c07907007808904405001944210030008504410480e460082105a40400c5140b20001000c8003000d85801000241500040e40700440d440350011210303969800c40510b40c0703a003003454401407240c0c17141c5170283d4040c00442c003240d513042062007201e215021007145a8a00842a590558500d4035884038111150751000c0c001f40d1240301f40014641b0500c60035000503000256410070800c0500c94001ca5039500c030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 622620764 1250 622619514 622619533
    0x905091303030c03020c100b03010c111b0f1c0c060c0b060609011701090b1306081f0b03010608060906070503160522120b0f13031b1e0c0503 62
    0x110148400c655805150115640c00c3d41030007a8041d03c140c17009009103201d68454071207818015441203600d080200c00034460085054002c448600b042d0542421b240c100203a080c88d040b00c40040f00e001c030700001d4405c200c10406800000c0384844098007504641c2d0081103110100030a00003684017074126802d03c8400140385440d040c490010040010b4019000003403081196806480c10501c0ea43d440f00c0104610760f100c01d141809803040c44217103030103110705a1600c4441c01d058050202503c2d0800d005040184840ca0580285109001201c074100c0c0c2d103410300b041545003070003604041e0420100414030390800589451801724014180c0301080400d00034400f42c1e41c049903094040041074680241c0300c1420620340700013105501e814030045041c0400c001600b410b44080c040a07036024400e0031046a40d9a0508032a603c0212140c0340340380c60303903441d00c03002034011101c1c038800080700f18003002221082e540341e401100100070045000c07103540c51b07c20100f101c030501e40c00c00f608099002d06032084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 622622014 1250 622620764 622620781
    0x231f0807051321020916081e0a1d0318030f030c071a0d050112060c030603021c050c030a051501060c170f0c1f0c0206010302060730080601090509 64
    0x1412809041220603c0f2003804200c0503800e10720800309a0010018800c1e0b0030807200c4c4021032065400f03101d0108115034000b0b590103010007200c1c0640d100d500b50403e0300795500940c2d94000c040641c00c0100141c0c0b4100a001c0d0480e041001c2c01100c4041a82198004244420507150240081c40d80c050340d44100070503881548007042c444111082d03161682102e00c12090220618080d4000301c525417032408000060014406400c00c006c18001e403004c003c60810303180114143c07510760002940000800100c4208048610301181d0754500400c140e486031560280000e0615010410646003648894005000b0034500b00041d40101490701b4407003001c4655503039042001d00e07214412068a4008182c88100d610800304443c525601c410070313100b09000d10302e0b1000c5044501050030f074800d840c01c41c05594441c00010f0f014143c0e07800030300407800c00744030b0780d02c024080d0b402c82040001001e449150800042d15100714200f0094039440703241c481c0c030b03011000604246440c0c1c09035108940d050180031001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 622623264 1250 622622014 622622047
    0x9150b010e040b1f020a0f1b05060a1e0c0b0c120c0c060a050c071a090105160c020f0604030c0902040510140711120a0c09050f0601020304231f080705 66
    0x4207001c0342068402958613800d03820f00c10300380805460554580c20a00402040d81e613100095016821910079264840d001d1150b1070084502c018007140601001074045481c1c0354101c0522451890000c00c5103a050743e9041c90b00b003060ba01d0f0128808046503021070010f80c5012258051904240241040c4920320032a66414000d412030074016656408511621100011142517680018620f0b400d107251000e680c241c210100c03031600d02c41d480d00c004180f5040141c0200510400241e0300c400520303030709400b000480d10105c0d46c3d069100c00304000c00800101002c2443c2c006192203e001600c1d507141406210a17046644400b004000c05c22003c200924081406c0d9000e031908905403005580c42c1c800841c0717800c511030480c024240b00b60355407a820480d10540901c15992082400d0100391107844e00703641015070583d07020340940c0050005103d0700c2c48c00d0910700250180034800c0d62058110b48080b40c000c0446141320311084407200d140303000f00341d0010680c5401c4074880c608180382002c03180141c0e900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 622624514 1250 622623264 622623289
    0x30d0512180303041212020a02060915060f09092503030207090203010b07150b090901150503121903020909041104050709180c090e09060f070810090f09150b010e040b 73
    0x418120501d90303000384921b40101485124000441d500e0030007031000ba64a00007100c0800300c81c0b01c2c900303240c4581e8100300103031401a14040d041c0e20494034180e042283c8444020800d02d0240320311410000c0400003c10082c400b82e40d03000d41c0d000050f0840c2002420000780e90417070075825004000400c110581c250031140550380006e02590b45c040e03d104908080d000e80c0c81c1556100703641e40c050064070300301940155280701c0c4c0c1103012612103659805140d01c49051410700c1e824240300348180d60201c020140f180c010f10075249401450f2103050400038842400a80b800e17a42400b02c0442c078071841c00e05200e07494001c0d09034280041d0b030921381410000801c1194110b06075158461500c0d900060060040b40054510300c40b0a003c02e180c00a00f450f540e003c1101c00320600b000c00c1002c103c0d058050a2000e0090181c4095495854245145c1c48080e081402e500203079541d0f1010340c2400318504003d907a042c00c0000c2004114040d0030f100040420384141e0031f4510840c90300300040c02c196580420405d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 622625764 1250 622624514 622624523
    0xc08030a0b1c0b060103061a0a05160c060804060507170406020a050906040909020a0501170705031305061008010c0f02190206090d060917070b04060911030d051218030304 75
    0x8210a507400030864840921400c8000c0c8014140d4050030000b1100303e440c441c510030b071b82c01c0210507540c2c2c000800c900014458004190f80070002c003071a4510400c02000d80202c4030000300b0200d20b450391102d802423015032081001a58480502041103614020640c0010300d62130580c00c8030818109081da032050250000f003406600141c3c0e148840c0c0a40c00780e54480c0e0008081540315952031f02070300003a01070326104a1150848040118680d806070103120280d103105400107070b2650f5041c0c015110380d48041c1090100703110726402d03400081e00c204200ea11401050041c80340d95031400412070300b552000705189013440314201c1d001440a038002818541c0b27441400b100090a051030000c01c82a2141c242c495800c90031001d2440280480e5403c038451942c80f442010380840040200d0801c80e0080c101d0051084007900c0204021401a420940e03801c1e01410700d40040002d6600064505107800c485080801c07000b0400120388851500c4069000d00d1903614040c1c01d144501141d6100c1c40010801030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 622627014 1250 622625764 622625771
    0x603091e0f0d05090a0806010e04061802060c030a0206070f02250503070f0819021309020a09023f010b0c030d0603030c02032e020a03020c010f0506030d0c08030a 71
    0x4114030400c8140c9000300a001519800c07109000c004165074003a40400780150218030002a044500080080c1292070390f6610141a80b5180c1e1400d024200003c0d5004d41290f600300d840d809a43c1d02001484440004001590341d80c11021020b07042c460000c00c1001071004445489103060b030041641c1c0c0206a070b840c20402c00d042c42c070b080ba4003510303030759040140c0500c03900102007200801941090251400241151041268184545040000008020b400442d000400c0400000a80000c822244020142000b05444202c801b04a070003100080340c3c82c6044200850b0000f40c2040b000040c10040400000d90750a03aa00d8210231034018403444541080000b0004540704041c002d60f0740101402e00c00788010365490034010f03d00c020040c0c1c1070388207001d01c080c00070f00c0c802480f0080d1b941d5020003014034858a41c03500c42c038000750055800b0000b0b164003005030703c0103e4000c0c403504100140007040000c1c1410614203051808408100c010144081c40010402054800e4141e07648000c2083e0b010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 622628264 1250 622627014 622627063
    0xb0a03170f2206140c0a140c040c0305010914011a03060a0b040801060905070206061018050a0e0103060e06090a0b13050105070908010c1404050d0618050703050606060309 75
    0x8009612416240451201018082c100c040d141e02c0e0038101200d20719914202c81c02d80120b0008041e1081030320000d0280e1200c0d030303c200001c04521081906000c03102c05e0750401400240420240c2d071410f401000020ba5a000501c03d00c00240308220352804507a111150960410035020286084c03140328030101700000c000a25286d03513074441c8402604008100703e444507945c2403581c2c0689035501400b020541017078002480148000341403803103654001c0410490840000040d036550035110041e40441e403a9500106050300c0b03200c00440242403509240e00d5035031460400004941c00c8000c2c040300c9030010414400311100004102d209950000440c00b840d44600300c821403a00d0011030014860b500340001c0000942c0c0000301101201d2003031000f17004102c005c0310202c4080b9004003c051000320140014010790806d00900c0e4403035481181d0015151100301c079040c085c10003014080315964881a004c0c01000018014160003042c15620541141072a52585480761480586080e4000040c141e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 622629514 1250 622628264 622628287
    0x3060607050115060302070203010513081b10020408030c060f01050d081c05070c0c0605031911210a0f050c040e0a090b0106090e06150a08090f01050c09040b0a0317 72
    0x1e10f080f0014200d10f240165503030760302070081d4000d90400d900c20f500c0c001c009091000c0107541c1c0360000f80d20013092450242d0600080ca002202500050454882c154000c040c2d00d00034801400a8118a0000c5803980d40071000c1510304039009002048031003a91004201d0f5032500c0440940c015400300d1000c1d200c550000541d0b205500010300030144d01e04107400d1000c01500400d5070448103000307009041403280c0750441924281b03c103603810f0482030041000c20140d044581d0011281e020180320300b916100d080746030310744c84450300320140c01840c40910500031401c50500c944a00c2d407080c07078020300c144d1400e016627904034007852107101c010034540780000e8000c03045680f1004031182c3c171070a485c02c20f50f10342c0001006580c00d801008c0c91440d5480100c0c0c2645070003003800d02003c800a28061a26207403040803602d00d0b20140401c0e009101d240e004e004904001c6c05802e02c20702c2990640d50301c8241d1403041106480c0203000740c5006000d0130700244082400d4410003188400004a041e41d00d0100114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 622630764 1250 622629514 622629521
    0x204050a2304021819061409012708060f040206160201210c030605030105130201030c09090e0114180c0915041401050324072313170c06030606070501 66
    0x700581c054030008041c0b001001c1d02c0d040c00200c10050b6103000c002c03040000d1100c048850f0f030061a0109040b101e00c001805c99000007003403d60010725045a0100303940102400010b030004010b20101c454200c1070044071401c104041e0310005043d5101034500f45034000c03032170034400c3d40c0b82c2c0e841c01e40f100010b24007035900803200c9410301c04a84c07880c1c940910440d14004010302401c108500024240200050b0300c2c50140140717400b80c600b00100140c10747c1d0580c0154000c1c200c28406105101140c03a00080b9015184075640345450044008600c48940305200d00044100034941c442880c0c49403803880260b40d0000342112030310801d0b80c2040040d01c4450b0342400b080c501810b042d40c03003803d0204201c5010001004d081c103d40d003d404641c91070921480154412501006810303a51014500254020340b0410288140301c8010405205c3d488030840c1d440c206a11420283c4048150101e0070003003c100c112030307454150454030180101c0c1c4036400000d14144070140c0719030720490b0701041c01001c4c40340a51 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 622632014 1250 622630764 622630829
    0xc030609070905131a01090f14040e060708010317070f200d06060e01050108040b13081c0b0307050102030a0f110f0d0c030822020112090b070c0507090204050a 70
    0x140120310540d132080b00301025020190301d94003d99404111040d0950244448a040c0c0305800d44404545040440094603402403d4907264015202d4041c0060440d050003164000c030015555050550b045003082d5100c092848000c00c040b0340d0402840c400724181400312045c0b1a80149550900d214000c001054100e0400d00d4552042c80c0300e0821080194a60240e01100c036082c0400d48240c1e03a420041d91000000c46000d448213071040002419400025215607881c0c0c03046150a0500161680d00e000903112041c50306900381c0d40d210480c0e402d1404104400007400c0901c0294944500580000c03c1780c100104000306002e0381c3d107074060180704c051013481050000001201c100113141000245041c480702019004120160f01094440d8440f0303c86078a182840c145000a0b1201d9900441e150b0b402c0704900310666a5900030500010106c0304198000c2d101980c5200d0412800d040440c1812610382c0010081403040000300495140c092394941100d900d64031460701080000243e5190003c087c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 622633264 1250 622632014 622632019
    0x90a0b041203080604060501020706120906020f04143307050a03020d0f02010213031e0210030b101b0b060105040e0109050a140603100e030405090103050a020907080c030609070905 79
    0x124022612195800c1d400c1680ea019a80e6a0a076856810074481107402034040d050051700841402c3c0308080c068807805024000000700090748200e41c0d11850100c0c0c000d01d2041c0021000000c003049184040c6140d44000d0200b1200281a000300740c040d558043c8484180c141408142c00441001c0313090001526240c91b0401d065940c00c0006140082d02c452514041402007a03800c1e40741c0400074414030a594680c3c2d4040900460f8604648907500342000103003031060300440c03002c03500c0010b8468840c002040b007010340700802e225070b912040013056034060a5080810140048540b003510896130110f2402d07802400307011107a103c49004a0721403080e0740115a00c81520740000500040701e6001c58450110308104104640b10713100c0608102c001911810340c540d00c0b03061140c0705489030fa4040340c041183c00381168501590742c0c011a0414400743d00c142c8850f00135a5040f425810140d40e1281d1200c190310b82070340c640c0b03080001113869020161465010b0b65141e4009016140510400700141800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 622634514 1250 622633264 622633267
    0x180306150915050a0e04050a030806060405100c03140702090a020c010b060a08090606090f0601080606040f0801060513020705030d090519080307031109150c010b0901060804050615090408090a0b 85
    0xa0348105812041144205400340300345410018802401790021405039a2250203490008002e4804464004001d07011a5000004000001d80c560382c080091111114546030001551030a0402130840041072130060340003c000c026807001a600c240b050356008812100c01070f00c5420140300c840c0146206031866410400009480d840b00b50003014103071041450030b00f00c40e0700d41c0d10a0140050414113a80900307000030350b0000315440703600901000340d0000001e80340c6810310380c0c0e400603411040c045c2e44c81401d6507552240140300506025689120210410909502d06201030b640d0301da03a0300c03404a0307400c5c00c59a40c0c440300b03007003140601180d51104c51354080b85c01940d910342424101d5a03c15510807000c02e10b0601040080d5a55205444410302c00600181405030a525144456480381e949a15695621031240d0305613600d411b081e034083d2049941e031104030b1401d07143c000d16122025103018080e00e880c001128503a40c4841660b680302e80d0281e20b4684540300c450203d00c0891702c40c1c100b201c2a100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 622635764 1250 622634514 622634531
    0x70602121c060b1c0e0109151d101406060c060103020d0f1b14030c030c0d030c0b0705030106090f0506090607080724150e16021c0e040c1803061509 65
    0x44c0da07450b1142c4584501e604219540c504640d040c2205d40c83c041c020b00d1030380740741c20944000c1606d90040303004621010504010a4544801ca424142800418a880c0742d442001202c2c20b0360102e205035101d20140e400c10301c2e0180308041d09903140c0e41440000e1251100004113020004661200046168060503451051120140c04614540325000f0010007500094a2502501d030018841400500140207000c0789500b0300c2c180700c64280c140805800780481c800074040000c02c140310741c0748601c0148c0e951075142d50500380c1c0203105143c558000a4410852030090029544501c221a005801222f140369a18800e1800c0700309802151400f40017800c1106042440305110b8003901c45403855036900f040012140307145c5020320b14882c001d0b15484541c10700040d120364164040550070000c1801101c581e0305000d842a405c0e2440c0c0380b0b0300b000051202103180710500306402903c401102d1801c144c5c1c0440403151440b2800006440040e00494841c5e04140740c60415026507400351039907800c00d104004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 622637014 1250 622635764 622635787
    0x1b090c030f34030507030b09010312140d0605090105090c12040c0b271c0f02060702090702031c11161110031509020421060605120f070602121c060b 65
    0x2641ca20142c80824140303070009040c0340c401e1158481010004104003410390840d100d40e0580701c0d0a075448402d224020f866411541c0554018045c0c0309010704d000b1482500340828452816010303488640109002d000b40684d0395410410707540740740787c0c1c444203510316030725410070100c1650306a226a250000000b0103501e6010000803980c9190203d081088117030003520140400015030b15000b003005100c405040c0e000403803840c04504164001090181800312940004049290694230800964400a5128482000b11030030004205c00100100301201e60302c1c5401c1e006100e40e0400b205161001c003844001c00c8141c2c080350080d40805851650040e400313541c050300070705100c0700c111520345840a0020342c441c250b00840e014ad4805400f0381c010310340480e14400c400100c00d03800301c0e0034035210000441c00d500c44031036804201e410700005141860200c14030505008160300020119040b807444520101040f200f255072102c144007505020020124050005000940204c10018400a500000e04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 622638264 1250 622637014 622637101
    0x2010e1206090106151407021314150d020a140a0e070507020a0e04030e0d05030f030f34050a0e1c0b0109090f02060903100e1b090c030f 60
    0x100b039908020030405466800c6420404d01c004101c500054038001c81652050ba11000f51003042d00c040c10309007041d403107030000105440160f4115580711015804000000403c0b001c006034a100035a01e0f400d480f4859000f1840d419402e0146007042c006028a4101c40e4403400c400c0d00c001c101c41d003002012814144002080d50f4450501644541c500030b0000ca216019241c3c41d901907689038943c0d0f1941000d040074090054880300e42958140000e118011001e503440c5e008520a82c00d070f010a840c01c0c42c02d40720201e400340000901000840d140306600c2001380403032603a0b840c0c00b08130b400c1864642c0d6070100c04881d050b55030728040c0d400190040e08143c00442b41c1103a15200c61040504088907078035003c40c0c404035400550081c20401204c0720440141c20308100400024201805440c1c0c0e08d44004041000d80d0302c216010746c0d8a81c008451140802d40c0c0c0d60b140c059070f80c0c080328090003034200517181c5071342e5020180c00c880b00c8002410106240003803000c00000a6540e01c50510b00c100c203c51034180d00c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 622639514 1250 622638264 622638271
    0x9160c0c0305070f06050c0d030e0a050a050d030e010b090c160609150c05030c09010c060f1806050702010e0a150b120615060325090b0f131d070c02010e1206 69
    0xe13514402d80214810b03002e10240c458150b0103100130b005c00461010200d000e44001450701c3c84501841580c0d001044080c0903d0501e98000c0300101800301180c14014100c0d450b0300089001c0c3c2c0d140410455456a4440130b481c2c104c42e007920442d446585034001105480400c02e0020691450458a8420086620342080014820640c208518910134400750f4541c401211508100c0d4000c01ca481225070048482c50310303440c010000005d0144d0708078951401c0350b0201680c060b0120144000e64204200b034001e60790b02c40520310003884106c41505011b6900d145030b01001302900e010b500000990640f507404595000f100510400b03c0c0c4031400c1884da25808254ad080c01d248103032508403107003400c20304222800b400003640c0640480700380b0030280210401200b0880d00300003940c0d400140d007a0000002d860380c3c10070101e140d40c4d580c0000c400c1e10440c10440c0d0100c6250346099030280c104c000b240e16020390198440c10001241b860900c012213107609140491075001c40541e2070900d85040004000c1d11 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 622640764 1250 622639514 622639529
    0xf06130c021e030406020a0b1f08100f0e0a06051e0f07080f06010807030207060f020f0903150705040e090304031b091404052a03010905010902030d090509160c0c030507 74
    0x104002c948450b1203103d40d000e25009680100c05400000f040310020755801503500c8150209011007516001942e03260707501c00c032019440230310700c0c0070114502d04c54060058000c0000300101d942c80d40d00251140c40c1c91700301615050740d40c00041c0744049009030032403581c0c1c18090102c07100c0c90b0488071405929010b1320741d40d000406401c00910100310f0f400304540a032505840e00341071603881d120102c004e50f000c001c003104c03807540303408040041c1c010900182400001c0c41c904030744ca40c2c0b800400c1c54a010000c801c811050203203841403044880d0004121010748524000d20001651000095450741c421a440200016101038046a501c0e0311120402c0030344480301c0d0140407206250302302440c411380580d030140c11500940f0500070340e120004940c00e403000440741141483c01c0c428002034211002004d0684245c1d4590800c0340851809202c6a0085c058905020042500306808603000c0300004000524520342d40f100b600c2414000d164000d5010390191070262260785a00e00140c030f48006100340d03503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 622642014 1250 622640764 622640803
    0x6111e070f08010b0604150e0a0323060f07030c09031502070c05030a050d05090102210a03110307090603020331210e0f15040320100203030f06130c02 66
    0x910078811301410b02c898200500e054101401c00c8108205c3c411184c0c004800c2c007000d12243c0302e0949810403030000440c02407400001d149040102103d011031200c01043c1daa40000c800c20809501e00d0000b2508034117a8680014044244401034408036440c0c0c101601a10080203201340b20440c0c1e07001440da05110b0780250702a00c0da00e00a140e981d840c4030900030119042181d0141c00b0600c184042d000142c2c0c1441200c1e60151202c3d10718005121481c2518a001c83c0001e09900580c0c0501405404250415640c0d02e98500014024810203083c0120010142c002000c54088040d000c6070301e0348104942191001840d1900c01c0700d01c00350101b40115902c0c0c02450700100b204074115070511100b41180c6030210302e10703510380030040e54146003006154018224030100c40c0a461010151020b103209902c4403000035502103282c8001d0644000061080105640708502c1c960b001c02500c2d00304103148400c000320340f24540000c1d0f41000b09240d40d15110725191003c0d581690014500c0c501031100360106 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 622643264 1250 622642014 622642019
    0xa03111603090509010501120f1805060a0c0c05030f0d111908101a0702060408011e05060f0a0306020a1103130f05040e070303230d050601080f09060106111e070f 71
    0x2c402c5139024400c150101d10728001c0c11140c13400030380002c01a0103061b2000288501140b6800b4441e4918500641d1035a0103102040081380441c894030400003418100052010f41965900b40e4034800c0c02040001d11501240104100616402c10300101c00712891031500c9091552015154034195410b1600140c1018003042d001540d035160641651a252000c02003003880d00c2450000c0d40c0202005c9801031010000010a16800e22900c803407000c03180030280d04169111498020f031040500828464034010004110a60382d495000d0110390348040701584941c10820292a0305030340001d050b00c9408001036241c90b5462408804044e110800fa0110f202138483c01480200c41c0c624a82101ea548115020b00c0809d000e9004c00280030b0700c00c00c50249070000211107180301d401408000c190541c40d442480500d41c1c022140c16400241c0071070786055460840030590b60360006218200c188a12a81a02c0400d8014001c1d42c000c6c162550003101110b4207081082d5403010076105081244180c2c0e04003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 622644514 1250 622643264 622643269
    0xd0b040b07170604020708040f060804021003050f0f0919080307030609020c0d1b0f050705120c10031806020309330403030b040e30120c0a031116030905 67
    0x3440051400300180441a42e83c3c00c044c84004d510082040d16405801e020000d1b032450848503000103400710b982c401d0464142072040c410034200c5905400c042c541010b0410495540d50405030780c0c0705107006102036064407003046281c05e20400c0907070145160b0031700d03044c6000d101000e80154010390990340c082007140c0d516032210040f80120321545130184c210400182c81d0611603030f43c00115108041c445803900c140e0303070f4514000c00c560840c110b0b0031750400a001c000c0740c0380800139203508a0792680a00030006250700000c4031445001a49010f065a0312111801d004900783e6441d02254010001c6580f4248203d20683e2405140c5800d0342c0080e05240c0c203850810006e04844817040c40411040054441d5501a40a40100020f09401030f540d500c000c110b0365400c02c00482d1030b10280c013122040440501507074015104000101024400c00c20510250480c0b88110725404001103803001d4980c10810002c4000d030080d00184000e10030003090354030403007081ea500746800070300c01e45500b0b21072681c480a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 622645764 1250 622644514 622644527
    0x501080109171914120a0c180f05060307111c02010c09240504120b0f010614040603020901020a06111206040509120705010b0306010f0608090a15090302010f050903130902040302060304021e0d0b040b07 88
    0x9400100e2600b1076080205007045d201954006482e81014ee0817104850021450681888030001030300700743c001500c816580a10840c030a81081d4580309120504000c40d0a05011005804042060340c018441d40003501c114140c501402c245d0310040281550750411106090707003903c0c02401511090000100c140c02058843c1004101e601c2e65400c2501c0c0581c00c5d002034100f020840e065004004042000454a2103886405007100400a4540c3d0440524441c1000000c050038003e034900010b101028500003509036607500e42c203810641c0d5560398174043d40501410218546c15201d900004105040d9240b6000141d4020340d444a071290380300d209407550350318040c2d806401040f24483c140c214400a400100e900c41c080d000114124003001e41c21012039408541022a98002040c00b03c40c1c009080003002c01410322030020b5051501f0740d00054182e21000d070000b8400c43c00c2040f2140b03800f242d40340901d0a810010a40e03e04400b0b241410800014200c80031201e00c6c080c41c00041d0030038000c1c2d9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 622647014 1250 622645764 622645769
    0xe1221041d160f0903080301030b0703152d1701060501120926091e01201203130b0a0212250e0a090501080109171914120a0c18 56
    0xd076541d6001075180c0095a03c0c4804450007010068050008070200d60300000442c02184a190104c020b440c00300d03401000c85080c2c403001c10188401c3c0c0030400aa045001101d410704e048101482c40f6180400c0c2e003d0101320147d0702109180c003c0c070307040549030b60040d840350f812541e003a02c4420100c941d62031494111030304100024100220860310a00000080046103080151b400d1158904003242d00080c82042d04011841441800000740c174805503401045410820151207401c040c000100c125562203480700c00085036a5030380031001405801a0401c6010200c0d0015109000ca081035209039000e5409030080c00108114007000c568188400444400b401c3c4000e080203400389008030045a58101c2103280942c0030a80720400300b5040d500d40f058034000e04c0030030000940801e4a161002c0300c05510040e15001000600100e844410550440c9a03c40414034081e020004171a240101d6802040320442c40b110300c0c0820442001c14560010f08000c0e080c1e140c0002150400b241d22008440a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 622648264 1250 622647014 622647031
    0x1c0501080a0606121a04080919080d0c0f2012100c08040f17090a06170702030a0522030c08030a080121020114120f011a0405010e1221041d 61
    0x160901c505c0d18040354603075001031040c1c10091074505900b000561040070614a003200f0b1207031f407404000050b4100206007181045041c0603541030200d4940c4000c0c9202024090300700020520310107801c0100c0310302c281c0c0d81040200020320310042000f8140c0d40340c0c102e50145220038500030891107298000c84907584034907440b006405c0e1400a9075917180e00340705190807100c0d030081e00740001181a079541c404480605029914000303d00301c0c0c3c1e209032030b1508014002ca019500100140300030b084d40b0100311407101054548080c401400303010f41c845240300c140e10180a4000c400c5000c00c041d034010000348240d03c1182ea844a560340c80c4d10380f0508440031b0302134510b4501d510703001240065006100a440704c00e52505400d0402c44200e04021102c00f04071800d4420041080040c0011384d8261130701e030b10607205820284d06040c14800040c02c4030955980e070b14800c03466107000030a02c02040041800c45006900c428101c10301c41c030038002e0740d90440d015031185081c1002101d448940c000c04418483d0007503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 622649514 1250 622648264 622648283
    0xe100e06030a12030e0109140f0c09150907020309130b0108060a06080114040b0a03060e0f0d0f0c060e16090f0912031104080f0a060c1110021c0501080a060612 70
    0xc5030f00035402002d851051840e00d540f00c900800c00b04110070b0401004216040151050001501c0c8082c246400c0e000308074401c640c48401d22180c1c41c489501d2718400d40054540c0c10040d01c5450f420f03865801600318040e07120190480c0f4403800b0800360407620003200280c0b241d009503100c4d40300b04208500c850285a0004481c070004100b02c0101c00800d07030504501500c001001c8000d03a011800c80c0c00703960416078005446115003030202d401001613000d903c007042d0180404407282c0ba001000da400c042e0540042155440740c0d1014003200380d001c540c142c0d00e02d1088035501d0300c00300318820141e41c86216006440b0726148020305200c100b07016041280b548008442c07600c2c440040150000d241d03445200c0c80e04641844003207607101003000380c070343c42e840248020800124180741040944e9000030759042040140196101603c000058086000c0c64090000d621001d9072a09a10003800740c03484c12403c3d90a10000242a41010541501d803e00030041400800d8a44540160075401c2d0301009265050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 622650764 1250 622649514 622649543
    0xb0c1b010f0c0b0601140714070e010806040f0201030b030312040308061203040b070f0f200a0501020607031d1213080d02060a0b0103110d14010f08030703030b03070e100e06030a 78
    0x40101410358407044c141001d03412285c02c440601e03d1504103010803103c1500e00c03480700030720340f004001e4800103003408866042d00e9810300030119122940a0801050358400201b00030071603011343c11401c0c0b51070020341165125211b03410510328101d015642900400d003480b0201d81c02e07081c200e5000710300317259160056240c0780c40c290486001e54002d48040d501301140800704e000182100c1580008039015221208854501d01e20f60b80840000b0441e583c0b00e01403c0a0420036a60041030b580d50204140c1000075072146079401808650b08030307007807148090151041120341044480d000d0007446080480c455402501d841c03c6541d00e0000c079641302c0c0503070b2000b0f00052050700c1a40015101010624000c59039004e8452a0615034210303241248549484281c4a014514a81c4000303006000d03a840c445002803604441d0303a12445160380107400c05480754030303c1c101600d040000d0300081c17080c1000d11f2a249000115140c80641c140680c400142d09034010640d07603c0c001074070711040c03600300c0301e0100220b2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 622652014 1250 622650764 622650773
    0x504051f0b09160c11030309030a03120501140a0302091b0a21020414060c07090c0804050c1008180a0c030308040311011a10122901090b180a0b0c1b010f0c 68
    0x9102c034042c25810307c020412222140c030f0500c221420f15102c1d0710713802c1d24010002a0381007554816008030102d070500d411494410b82d5450120006c40f6016a010491500c4068001e40c022500c60b030790181d01400024800c3e40c032a80036451482e41c40c00b0110300d040060380c144001042c0d22561141780d081031209064140740d8501400100500c42c2020100c0e0281942c601c034603820344014201c0b01c0c002c5441c9030104400c0c46401e00800803078150440e00b0701e011074000840901444005406009a91180c440084070300608001403800765400503010314440d039072860024106039007110220005502240300d94039005c814042d40d2008a050103105c070845242c0070034440c1409010008404120300d038040d00b07107641607510917400d510142c0390900703182d80082b43c0c00b070184944030240365042040110b0200300c60000e401c161400e00448915481d041101000000c03580715064002048240780002c81a85942e000201800001020303a4000102c0341c841c00150381000d905803d031001f04090740603420015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 622653264 1250 622652014 622652033
    0x4080403080f0d050109060f0b0c10230c0d1d0a02010f0c0605100e18120a030e100906050105060c0318040608030a0507050f010b130504051f0b09160c 66
    0x6406840ca02e07080c140842884019100280e00140074160743d01000c0c00542c3e03084040300080d00780d0000d801e281c441d03914030040e030368442a1030001d1603d50b50800b003152680b24220030042c5003c104054a00c50400c15820603090b4008402c0603459403402c0720268050142c000b040c60f0031038100014050145040c4c005541442ca0741c0d643c002040101c1c5400400502903208450180700714801c001c4240303007808801841d00310083c12407404c1340d003405e030200c01038a00090300c81c4250300d2500303043c0d448268031407041e0b000d419804146a40e6000395080590301d07542a40c087c0f400030340950300c14855660b8440900c80d144c841c124101041e6002080850111f2140c0c0c2880f010400740070300006240c50380d039100b290542c0c10600920000520016101d0705000c401c1001600510066008000c810040ca00042c508060a08d600c0411519100085c090050900c036001040c621a64a180390010418000000741a0f4420b41c41c8a40042004100440e50390080b030403030f4091580318103440d110151651000e0303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 622654514 1250 622653264 622653277
    0x3302010e07090902130617010b060331060606050a02011505090606071a0c091f0806150c0a2409020108130503041214120708122a0a03140408040308 65
    0x406001d038110b103030103c0c182c0300e00002061512502d000740b9140105a84c00d440700c02c149c4a01c540030600901803480c141c20080c02401c403208204103640328040c228500c0c0710840304800f500161903d907000400c690041c4c0140102c4c00c82e64020080f01040140251956006016650300319a0450000707603d41060300040410f00c0c00750759900d8140040126081e1690412541c500700d03c000803504a103d418206800034400f00c0d041d0061078941c0802e400240740000040195128007180c0100c0c0300780c802a00111050344140b07600f5503d80d144c4034288001030043c0800c80030a0f070080b00c918940c2a03c56446100c500342e41c160740e000100d84030041c1d9158050007492081d102c41c001000001030840118600f0781d01a4424194189800f0000c0081703414441500907401d06501d0400032140025003540444807402d09880550281e81c54005048200205440b2440d611014032406402001c0003080074062441d6560740a010b258205820a180502c05840007403040e4401c0c0f2080c00002e0420015242 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 622655764 1250 622654514 622654519
    0x30f0506010f2402100c0f18050904060b011206150815090106030209010509030724170c0a0c050613110406030314031b03040b010e0604020705060a0e073302010e07090902 75
    0x3017407034403540c80d402c40314903110103000f04070400c0500d020305400c084810366000107500c0b10b2003c107203400003140f40b28000500040076a41d40e100707040d0607a80102c40d103913261001c6d00c404000362503c502032007448010034020700b0041120400026811160800c1e030251100d03024040035090391900304180d0103904507840041c1413100500400001e524201311140051540764840f130852988001149904030402c0005410002610100d800004083c0c1d042c0d900004c41480c2541d66016100c011502290340d000020481d01940c01032003a005640c40c0003004280c01241e0840030302182c1001c103c00c41e030b000d110080100e882d66010b03255103001003001e594011040070003080d11b00381825814190b030b8801c07075044886850b80300050101d18900845070f90700440a881c111714100441e1203030784c0d40e200010810000e00c3e84500250280720f800b4840070300200944542c00c000d2460b1044808207010360340b4201152983c121945a03400c0344140140d0328500c1410001e08060780c241240000a0700d8810002e0b43c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 622657014 1250 622655764 622655773
    0x10510080c040816051f090303110102130905100906050307030f0519030215060103050f04060b03011d030d2a180f03151410210b01030f0506010f2402 66
    0x43d4000c42800034400764010308100e0307500c440c20001000b00b11000c40261540b075450030040c520389160002072040c1030700d805080151030080c09a50340350280c4a80d000c041c1c5500703c0c0c2d6400043c1041a80c12450280313064007020001103031214418001c407041441110b42c1584001410070200f000701201c608654000c4065403c4004601c0005142c20801d0343c040340164801011020f4501803042e2040d001202403034140502c3c24101e0100450240203040600250754540081f00c0c541e40c00d5120110082c0c2c08409a81b0740102c014800b0f86070780242c6850650b250a0421200c0f40c012040c110030414101901e10a0b50716001803001c540981005050010304000190046400d00f4031149c1003000310f00c03d01d1020f4403210075032a4801910b411040e00c8068040314801d0150700004a0300081c1511248400b4100d0500e0125521010081c82c500181c0100b414000100030300c50321088c2e01d054a0b02a4040311f005076070320b0503000030700d00c418451070786a201886c00d10b00401800b612110142c100314030455 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 622658264 1250 622657014 622657019
    0x3041e03050111211006050a02010e15011a12040b060d050307121205060f06090a05040603060207030207080f15190e011a01050a05160303020c03040303050c100203010510080c04 78
    0x10b0b003156520003582450389804101e80511020742008004c0d400741030300c014080c5050044031890509458000d08041c0100442c0340e0800324402d40c0301c652800e03803000803aa800e2544100c00d0740449000c0c0149621040240740713000d05600e8080844101152242625400d5551a1079440c4030010141076076602c40c113000349d81c00c0454401c2018143d0079000b650002519000710034080e180000d82c010721281182000100102a81c940321010301c1440191045a91280b0013800681054140d411140d813051404801000340000c96014154440c800c2d000c480384140ca07a40e101d41d89081d00c4d01d81543c140d0141d900c180344050f216500300e030400036880da40c8803090b000c1000e2a003900c0c0381864000041e0b548454195085258141007118000282080343c40d260389a80c004006114050b0b0320856a00c2140e00001014800c0d81201d03628900301040d42d8903140c492070018442c0c5c0c8040d002c9110380c402d850b030611414103a4401c4904840c030080c100100f50604900c2a176030740b00300404440d0f45001c1407100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 622659514 1250 622658264 622658273
    0x20c030418050703060f081009140712050d02031c0f110a031a06090112110d020f0409050601090e06100c0c060e09160e060d020d090804061e0203041e03 67
    0x90401d6070400100200d41407030305010042c1192040e900c081d6110309a294100700c0d464001c920055080c0b145003001c140780a4034108120390307024207c4647c201d4402c0c40700004d034a1040d4030009030120701c00c2d401d990040c0b18010080340d89000d5020444040806050b1000034516103521021520b4221500400c4450754007506100d55000207554030003181e280c000c0d01c0c4502030640000100c220b4120355245c10401704000003800211901c54022801f0781d1030202c04040c203000c3c0c0594903044410f540655503003000d101810750300c2d0001d110301000b040c20072011840c030358010a4040141ca03020242da51495030b50b41c08101e004a030780d51018040c0100c0c1c08070203000c00c081c0548840609072035103c080c00940309c00d0070701c000513100a1442e001542280044c549190303102c8a01c0000c864111681780d100d80c6070384205002841035000c0000c0e0940b610308184104503144000e4411140c0d1074031451002e01000d1100324482c4c00380000d940060300100030600244408400003101c0342080d590b0f41511680ba580c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 622660764 1250 622659514 622659539
    0x5011e020a050d08160201140a09061103090d140f07030c080d050a0509151509071209240e06010608180304090b030c0a15050a03110310051309080904020c0304 70
    0x1450340051007134010444050309280388116020110700c000c00c08a616444598000074001c1c11040c0803588900400091100d160401a000305400d4100381d643e09081e80710603aa00100000000890001d1400c00d03243d0005400b03490000355566030b83c61824060b1780d01140d112441c2ca0040350f203110180107400c920300c8580b207550f00c941d100050019503802c000303c50a24103064407002528448103c7c04005100145d20214030042c0700694a41109444103002661500300d2501c2c4410002c0c0352048080038400c101e411a410032001c856240c1180306210b100348103030380098480340b00c541e001c10b0041110a2080f80d10716842480c1021400f04140703649461800c0d640164450126591038907888149460300b4000f82c0300d40107044401c014081e141188001d281c0d0003841210301808004030301d014086000ea08509201050003000554a14022140719980095030042500460a6100c1a01c036865984150085e09421583d424209600102008080c0d403011065001e180001d20000890511010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 622661870 1106 622660764 622660783
    0xc03060a110904051b121609080318010210020d09060c0c050d0c02042c0d02030f162d0b15010909022d09030f030405011e020a05 57
    0x920000702d025145d00ca140341c410300083c00d6032003034900c2c9800a128941161480700d1092804108460f86600c900805000398401c21030040d000040300c608400f071a00500c103d0320400c00248502c41a42c014801e051071280c0c446205e5402c2111034021111180c001c0d180c42c1418440390f4031155038981c008000a024480f119151000395103454000884a040d4032084403880803101000c402a08036540301c3d0a175500544030079080d04c40c400300407506030800f00b581090822525840000d070100a2082c21203c01c0c40c2c40d900d1030220251980b00c901c40d075016401b8081c070099107051403506140b0003030101d1000303011040c001c42c40e80c0e004007020042d1040c2c80780c016107401254803800d82800e41108606810600303240d4280b80509800002c000300401a02170ba12070b84c114000d181d59a0255002e0306000c29004200c2c4090000500b0703043e0700140301031046607044401919190f05184419 = true := by decide +kernel

theorem cover : BRFrame.Cov 622482014 622661870 := by
  have h0 := BRFrame.cov_init 622482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 622482014 ≤ n) (h2 : n < 622661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
