-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2021
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:27:59.580308+00:00
-- url     : https://prove2.me/submissions/2268dbc2-cb6d-4778-8cc9-0fc2319e43e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 363309352 ≤ n < 363489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 363310602 1250 363309352 363309371
    0x9080a0204021b070609030b01061404051311031005030f0c0609011d06070809040b1203030c070c0e0108070e07030e0717030d0c0914090c120c160302240601080604 72
    0x43c00d540d0240c812103400c0d2400141c444e503000b848590148410b0311400c3d01000002501805424100c40c00c84030091028074041c2454244034010f1440d030642001517540c3d1803880140c2c1205400f1394010009140000300c0a4500401c05103004000408141107070070034011314489644041c03c442c0703142803e0801c03140309140c100700c0c514105900e03424550400700020303046003048281d20080c0f0008004403010448820f094080c0241c81c1c6400c031407000b403903000f000072a500c881c0100140000b60311404095a00e035444240100d02c03010b00303070f022030515400300600b40490303004010001c0d1b00510701d1600f045810101a030065540405100d10f49007181d4941000481c03010910460315480c00c03d00e01841000c1c007024004100360f0040c482c05010103e04c180840c0176141150401e40a14141c01c200b030304200d01d1484003051020050911300b0400420014910115516103280c4410f80c0030f9006404e4144c40000e40009a00210322145140c4e066101004003507070308000300542004007501c0c00500b01d04e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 363311852 1250 363310602 363310627
    0x270b010917070509070e01090308030a0b0a0305070801061211100c060504030806010206061008151809030304031409010f0c05030c0115030213050c16020f0a140f0109080a020402 78
    0x14039002001d0500c0c6008011403180d2002500400300c0d102502d19904998804074202ca07020b140a24942c0005c11020040001c21034680203503801019501c400110540c09d000050340a210642c02122103401082080180d00c10a2041c03400904080148407040100c0381c0d079000800e0040340d509881032001110b41140603124100013882140c1c410320403c07450400d8103018080840c126040d07401031084900041041c100000900c803c039104da2585c0304a501d0b4141003203201800c0303501d4643c100c0300690b504008a500c6c181c0c6c0500690604010319524141400c0003490302c020400f410400100401a855859a0203800981c10030090b2501d402203450a14056056104231116114250b003448000d1241c0c1071605500011684200d6025030114000760182054800480b1440030301325062100e4000d152040204d02042d520062000c0e0003200000d00045481e60250081c044960750b01d0b080c24060300740b18003610032680c82420f0240d201d03464040099900d0401000c001c1c0503507000724880c4171110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 363313102 1250 363311852 363311867
    0x614030a0b090f10060e0f0f031002030c0c100b0609100903050d02031c050106021207210f1206051003020708070803040602090108010f06050301030204110c0a1407270b01 75
    0x24010882c019034103000d0151020345000740e8400d0718100b040d00000607580d0241c501142505400780650100303030305144c2000380d110300311901141c040c000c2c155036403600061480110b1040703c004020944940b002417410b03140c04c0d0030080108181e0f14084892155645d00019075a00c1002217a10003d40414800308407240e0fa000e80c00204148146c845105100340c000c00604103030301c620080e2040c00242c2c9110380c01079550a10441c0090b0300129042101d0a03004070082108034019002080b19840b5002901d1904503186003050010303002010103500e035980aa07078131400c2078400c0700c144222130a010002e400820315030f416005240e40051100704002514050340c14003504840b03910703102d01e85410315101a501c225940c600080c0202d0012958512a820501c141c4216680e0315043d0b80c00c542c2400000c01b0043c10100c00f1a40034405042008400c100b20503c2900c0781850b08903070b10f82020780f20300d015455000400b02d40100e865a24000d24058100000418003c2c00402c032030b2440401a5481c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 363314352 1250 363313102 363313121
    0x207060f020a1205060609062b0903080a0903200c030303100f050307080a0201080709052e02010b090c0702040615090e0106080c07020103052820040614030a 69
    0x11030800000086504159000d420714a0041d12030f000c1440054440c0780454500b11003103a071007003061104441ca800e00c0310242c610801070344000b0002142580d80c45d950305820111090040d0344400000080650052000c2e810007201142448010060364007e07240e078050030001c012032407900c4281010000100000700300420003070160781c1c0e6070824050382103440c1514019000c800c5414400014103041c0012044120703080034002e070048444641c01142c804a002e08900100040e56001080e41e43e14024207020800380c810515403005079055000100d0f0300c03d0805131040d640341c02d5850b01c1c2c5807200d1003074542c080c02e0021903d6403840039100044c01015070350482a0031a01c1180c020107982e03041a500000c0e01c1980214642582e640c130030844000008482c0a401c2307000c1405084010b5000303412840c0c104500c16202d82410441400d44440c9030b040c03c0b0030084075900c0c1d000107444020250b48041c069003540410b5803501d41854001340026411051490365207100100040b21484558010941c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 363315602 1250 363314352 363314363
    0x60507080a08063006071707030c0306050a08030d0c0e1e0a0e01081615051213080a0f1b05030304150b0301090602072001080c1305060c06010e0f01030b0414010207 72
    0x508100c3c01038209a00a6003100070b91031712034600400c00540c02400101c6604134240042c03c4a60380380d400c1180540a1110301c003081c5929103201040540d10f298031140075086040042d80c44460000303444040d14641d1031000144801c221075070245403120307840860703d0310308502c00c0d402003008100810100e030b54541c40585490b84520022a00710387c0862004a05503902c080017481680319a28400a1510184843c0100314100507800c8000c04504255600c412240ca602003183c10b0b50b1a9900c2e03981c48a0808000105c90705910400c290300030301420900142c0d0080703020701ca0015a21643d882c8000342c4054402d203a01005911020386541012486020207002880b50307070741c2464400013075044054219209548020402800303004400d0082000702e059440c14041e0f01c402c03500c4025039206260403070310104a041e0216094580d10f00601c07071246030f03e00503c0990700d00700d4180002c14014110110740e81c82c440041000c50301849102c2d070880d4101040d25130700400c3d1440c0a00912900c40300425 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 363316852 1250 363315602 363315649
    0x1101060e01050111060108031812010606020705120f0c090903070f0c0302040509160605130807030c0f0806040b1f08060907060f02030f04030f06090209010b04060306060507080a0806 80
    0x14000c0158000504940382a25810380548030121880e454100034040d01e1141d40c41807104202218560420300d072007000c058001203659000d02c076081e0a5503501d07004a0096805000100218100610b50000818442001c2c10841d443d0f800c4007130700d400c2030160306840f81031198089400c6001c1031080f1200e8690201c0500030442c1c003490406000012848180d00c1249481700282c44030001107119803003040450040c0c030855041240c1500c01d604607140a10b100c8010450100b6081401c000b2203000d5030250400d401124507201004540c14401e0300900101d401000c24000000c001000c0e25801544910b03606052082502c2c0d1060010340301d40c041c803054800c040c00d21020404c00b1800c141070f520715941391482440c0302182a03a50344501c103520f0383e400c0070801c82000030442d000303030b800e0003144500340201340101d103a0000f961804c0c003a00582d091800020b82048110740500c035800050200d401c2940c20510b164aa9020718080c0849040621440a0004580d0340c1c440b0f0701c04d106161221030214 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 363318102 1250 363316852 363316859
    0xf0a090512060103020f040504030f0807022802150a09060e04090b01090e01050f0112140c0424050a050603010b0d0b04110901020c152d07060504060b040b090c0703110106 75
    0x10b584034820320003a40250042c250002140c00c2501405100d150180c40c1d20b6900d0040349000c481d5441c004040c10110300510b245000194680c50704240281c0c3e078680301205545090040100d110215840c10012604c10014401255000001c102c100c0d141400d02d5021407400c2400718000d050707442c0004100402c0303003001181442281c0e000040301001d1500801159071035008544090361300f070003210300030f8840c3d92542001814050352001c2c00c0700d802081c2c4030f04401000201d000d0310060303044403000c00700c5494602c81824400710214020881105d4032050945031501041161006000f801e200c01300004600d010141c00e50440225181c014204001880304501c1c8200d403504110304580c01030060303481c101c245180041e51003240c0407241f90400d1810058019640700c00070040c0c9900c40d0403085d0030710401049141c0380900042070040c1e8002ca04c41c9010b2402c13004880741d00e90824801d03443d0071462402c90310b03841c100341c0c2d0054102c00580d544802c1810155440c14034170084012640c00d041c00803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 363319352 1250 363318102 363318139
    0x30303050a0f060e160507060c02030c210706020c0c090420090606120403020a0b010b040603141513060e0903090102011d032b02030708150a06050f0a0905 68
    0x11449503040758010000700c521079502d00241c41080c8140000e0809920200e03540390080020090010b0039402d00614100c00c0703a07980300a88505500504c0943c1010031b0002c402d04c0c0500c5200d07103a10400c0120744044022503506481801464006414594040380c03d034907045080280e0651114020610388062402d032600e004098502c0b5803440011580c0c184c0300c4503905042d20b100d8084d0000401300c90400c40141501a403507580140160111321810307900304c004c5800c5102c054080d0100202c60b641c0e80e4144400541600c1c40740480101d40d0284c5001c11211000c0904810100d410403100d4000d034015140501d03001d0000c6030011410071001509100d507468002000b004400000e070005c0c0f1802c503100b94089080010a51086c560b500100109449500707496042c106403100c46100300d0b68084a089040104e030000c40710100801c1d070b01414441c000308001e100424080e8201e94107a90581401002040c5018409048081b0000800e10360301d01c1d4041c562400180c01d0140041100001c0340c041c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 363320602 1250 363319352 363319361
    0xa0309150c0207050d0c0e04061104140a050d0f0b0903090301060f0305190312270803090c0312040b03100b0f0409180c05090411040501150e060a020c131401030303 72
    0x7950050f01c107a00340054142070202030320004a810048101e011031410700450400300e4010801c84150750354681168503800b41d040908054035810715940d50601c100810b010008505e9000030384107014012846001038500c18a421391640d22056501e0f0715140c03450910b2a5005507404181d05500740f200c0484e000041c54030030b00c1224018000c427544d1a11038500c004c291514060050001140040c0d44440309040d50007101e044110400040401000321141e040710b041411400c40e9580000000d200328854100051030b1b000d00e046024100d40310f1030f512803c00f45d2140384a01540c84e41c001c00000d04030081c8000034401130001680b01079031501c40944500d0194814064088810b190550480c0f00300d00804280b02400d0b80f000e034882405040008010407503030300400c11035200380385407240034013925103000d018002d081d08440120004090000508041001400b042c0107403018003104410b540e0014010400303000c2660140c1c0c07107160904102001d41000c0c0407480810542400000c02c05915600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 363321852 1250 363320602 363320621
    0x80421060e0309041410170a0204060303120c08061e010e0303160c0e0402030c1201091403041404050f0f04030c06090302070e0a021315030216080a08100e0c0a030915 73
    0x1810015403000303200b05c0301d02050989244c40c200d07165490078043d241e8050b0a0181000c1032204480b1b0780346aa50020702941d482c3d4004400003040003030410140f60050144441a108a06084146107486408980741c1003400c0082a188540c2d02500d460030703405250652200c5002400342c0341d41d00c428100001e0720900a220445400c051080002281302203501c000f40143d600030050b203a0454014108004050001414004c40d540e070300b01e22001500c08800381c041d5020401c040d41d1070381e14010b81400c101100c0f246050081d82810204140c08402c4403c680d03101d280700c000242d4648441c2030440354003022500080c075152802048038145500040c0c40c10440c0c0c407102000e1004c0c1d403803510080a034000c2540c441c100e00c490740c20512220503008a41800e4105a00c0d00500342000042c0ba640c84800010054840c22000902c800b4a10b80c05211558010440301b0f80c250f0b02d5140c9a00c0d590000c03030040c103c404207007020540c00d0340c4600c6504000140d58002902c0b5200042c6030403004c000701110346 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 363323102 1250 363321852 363321859
    0x40806150f030d050d050c04051306030501050a0b0105070215070503030702030720090406050711030427060b040e0c090406260f0c010806041103042a03080421060e0309 74
    0x20700895107071038005401c00402040b50b5030241441d4a21030710101500003d40050b0741001c1c140b0010541d6114082c4100101d40d500030003040b0b003450b6017801400c40c0e201034242d02781981846915500c5036040400c40f0b541e40e9051f80d4030006029100314078842e034008c0c240010040d000000c03c1c080601e6000000e0f007030250190400340800c0c90008400081160304441c0c290700001c0c088001004030302540c0c4002c0d4414610f003000c61451428081150035a4081e41155000e0740e00100140b0000d1701e1980804601c041940d4104034440c244130010713207103019510903410807010400001e10300e0080081540d08224020300107100c030a49500703d0020807141243c0010958070700341012190300d00009681c00203a40610013030041c62840400441e5041c00c000c00c000d400c1511051894035011107034009604c0307107021750745001c0ca200426603520309114005010301c95052510030305202240f04103040710300701d410b013038141c1510300e061201174200114888409042d95140c0170004004003804001014a400f088 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 363324352 1250 363323102 363323119
    0x9080f030306100e0d080c0d0210110919260606011e0e18040302031b0313051c0b010905010918231e010209010e0d12031104080615 58
    0x101440350340740400c5078001d030710001064a1084084c02020728401048001d08881c03030a81035500d070040c1c03c0c5e120544107920b82d07121a0701a00d0a43d0705211800d0b008143c07050a002e564080140e080300c0b4011600c0091003500c54000c80d000412140840c5001000c10304590201000743ca030b6140d84403020640c080701d16004400c0020b001d584152211200203075111040425070003038240c00c954461845d40b41541002c250006010a80c0c4030400315031085100f64025036079003c600c520820390030808110082d0319441032002e0600e1401d1141c401d8140d0b10160707043c01c080040751019a02d840d884940182220103840c0c004a011354103500903d060b00c10b404e20601c04081108021444860011000b03400d8070f0b01c40303500e01c401c068003400d0700c00c2c2064488201c6080020000264407600d4407031050303252a070b600040d5040c0e503580101801540c208101d070784810170603894850700c1c4c0b42d03200c18000a04140d0380c1c034248103c44100400b41c402070050a02102c00034071b043c0d42d0903a24003410701070140c420403a6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 363325602 1250 363324352 363324373
    0xc0c06051c1a0108062e0e0306130507050a0f270e161d041101140d0c09050d11010c03020322031505011d040c03060e031b1603110303070807030908 65
    0x5560305204403280381b0b440c0c0c00e610100c00032000683c86c80d41001005054141441c03a03940802c1924001c41d9203808054000b260b45c0340c10740c60720346030703a0181e4060140e070f0104200c01080283e0040445a15038909070489940c4981d0003140c0722030181d80da90302d0749010f51800034040c00291241064054a889014039616444846000e003820040700c0501e8003248006000030f4049088541c1c1e848040c181038501031030b00c284600040c5c0000807022103040da0b5413130002da00c1741d01c65401001002d050f101c0388001003a07a00c4031194142460b17407090502c00c11800701000c142c401c1003162413030b54024084840c0907504060301e580c002098441621100c1940010001c00700040c0b16042c104c800140c4414819005201d0b801c0c05c14070010b1054400c00a607013000004500385000d0301c040c45070300308042c40d5100403803140c011884144223650301c4240d01604012180161010100c429641c0001c00ca4501c4034500001038510700c110b941c001c01c28400070412104060b00036402005a400040075154015003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 363326852 1250 363325602 363325609
    0x3120106090810091e0b1605030705030609041a16020c0a0506120703060305100506031b21010f3b070e0c0d0617010c0c0c06051c1a010806 61
    0x45014030b124980106141211074085548000000f82c81811070144408038a50710b2035640c4480c2e141038a4a41044042001c94a28508201c940818030b09080e400c60070100030007082c1d404020000c0780204030200203e810301c0140c0c071002001c004c20500c03c021750b02d422440e050080e40521b909070094480c1508a0301545859142c0201f03658000d040344c1d04010320b019500e0700d160f00250119003810340d5024040040744060141c2120402403020210b0107051880034103291100e10b00407240382d2075901640d15060398030135001c16030b0080c0808000c0f41c943c0e044c408041c01000411a10480c0320310304090581c940c1d10f0380d003088074079114010100f5107504403050600c003d10201055440c441c0c101c1d58003405103081c0c1e20801d5800c60322500d281800c0c20300004030103003120465040010300e620b41842050f0680002d01403c000c00c041c500d080310250103550b681c513940014900400c4d0a101020503c0c00400d12148960461507421880500c0a40c02210913904d02c1192141103a0000d000300380041c590b8107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 363328102 1250 363326852 363326867
    0x2090f0d02151b0a110108250e060f0d0b030f1f11091305010906050d1e050f0a0f06060b0a0c02010c0602090d0b10050d030c0602030a06050607030203120106 69
    0x980291180300084a009401442d90f4440d8045a81890302c00c180400ca0308030030048480828450f4030030f11043c3c0c0301c1e400050440d840050500c11305030b10402e4070304c0980703840358004601410581000704d1070011020003d00d190080a40826008902003122440d424a40d000003061007420750a8661a2030180f80d042e44401c1c3d02c00200140300802465032030b580045030b0003103540200f600300b098140007004c000182800d40400c0c2e46000c0700d8a0304014095120030b072041e0001001e0840d8070090340780700c0340c1c0c9030741c2e107012607a03072440c40100e07003003c07200503c032042c8a07a1740401d6a803c01d58201d0103891404c04c0c581d50f50f1b0340007501c000d8178151001c140020140203c0340c9040b40c0d0388074440e40d0201c40e03004441006107030504540540e0240105520341c1c079800d80c0901d50030b00c0381c2000c05151030580101e850740071640d409948100801485100801d820036040d50b0115008000581d41c0c2d0740f08070030b8101402003940708940080f800100c44090641c044090300080b46044c03e5108240d030b071070300101c8100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 363329352 1250 363328102 363328129
    0x2c1c020316030e0102070317030603010605030c01020a060b0d05010207032105040c051c121d0402030c1e0705120904140411040e25080609060705030114030c030a0602090f 75
    0x81c40410031050110340541d0802001d0181441114103080e105d035038400240724000685004240080180f05c11071400380a000040d00c001d400804034960340c1c6000030356034201d6070400750102d6581c1c820301e185522810481401207400100035940d4070568540100034644240407980c0b00c19550740194601003460046d00d010b83c1e00252418089401c101c1080303070400742c01e11148091660340c7c124100181034408a4140c80703410361640344e00c0205402c070380491403489510691083d4410420010f080386410140c424000421061512549512124000902c61180050400c1c890340e1a20b22400c800040141f22010042e603092061720354010660310140001c0c0c0c0c000303080b81040405011982044c0d40b080071044c5800049542e181110040e00c5645e05a549510318a1140b251041c407155100b0003a05070805042e000404c4a850014070050035404103001e8000c07211a1a82080015603003004140541000102500c42c0f100c1e0381c0c58200c000794031440d003081c000c1c0070f10f4a40e080c4910700901c000070b05 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 363330602 1250 363329352 363329377
    0x51c0204030c061b0f050c4e0f031c0c020a061104090e060402150f0702011b1b030c080a080910021e070911030402030c042c1c0203 58
    0x80b941020003d460342d0703642c8038116048103046009003020a5840d0703010040240070700e0141c5040d01255050010707680c007807698000c03858120759078034541100d8008400a00a0002050356440c101c50049800b0800700e840e01003c0e1784240300c802d0030900004001845944000d00010103d02411010507003642c00c1c600a00300035800242940b000700355507802ca01051946180d50794076107500c44e01c1c0501114480035051607254400d104010440c01c001d007680c40b81451080f481c90a21000d03051100191040c01402410866600e0044196100d040074141c0110782c007841002c15a8401c44220b00d6030001d62100713469030114003c0024071070a0108440000c2904901c400f0316105544090043d038000d0003945004501c42c5d0104030062801c100c03148004810200302030042c20b460101c44c6070564101c1e0640c041c0c40b034410000d03c030060b940085c00c009002e1044d100070039110491401c04182159032620703000c01d40142080498400000700d070f030350f803400c2c603e4607800612007000301d04982c2e03402116500442c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 363331852 1250 363330602 363330623
    0x510020d02010f110a08071103070305030103060510030203071715090307170a140304020d020306070f09150e09040302010e0601090b01020f0106050d080304051f1a01021614040912051c020403 84
    0x30900c50310010782d00100310305142348035841da0110b2901d5a40460025000280040700510030000c5500078036800601005040f416903003144c0000e5150704842c440c2010840400851205010003031140d0b034103060300a008102c280c50f010641e00c0d2260700c50b031812103019205044001101c1e2507582541c001c0d8100350b86100703440c3c0769052030010b00d900141c01030368010020f03c0c801c1d005940030800c8501c40c0d14a90384d07140583d0880c05002d0203607600b50304a1280201d42c0f07070b03030580542e91091044030881d40407502d904140d1180e0030164010034201100404a004503000840d4107000d0b074100301c69189082e0301303c9599201c201c158500302c4015024090b440003016019201041610380030b0b603080b50103042680c00074201c410304070404140403003c0d01d039515180c03042c002c1120b0802d100c11420001c00e0001c0c00e041c015a0100c07903030752042809045401008480001c0d0942c0711588542c0405034800e030345035410003200c0c102820030f4110300c40112291260850308001c140d0707203000355021250302004802 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 363333102 1250 363331852 363331867
    0x301061209060903020706080109050f0c1b011b11030c0715050408160f05010203030712021e04030803041704080a080a141201030b010902310510020d02010f11 70
    0x1648054940004003000da203508001d070104520b440380da002d0901c03e40042290900d0401d024226000583c0441d086528040c1008a0003140500301903111040803551076035241d54884003010301c0000030fa04009036207000900c00780f00d443e2140340b011140c02a2240008581d500c51726a641c2d12405240500d685c0007a201040105001115000d4400650500074241501d4286040c03410f11302c02540c3c0c00059107440200000400e040060015080a00c0918998034242402800c5003c001c0d0407003c010b540014040006111281c1500c1041c0202c11003641d66030b980d052240c8075400130b54003980d2800c00010400e8900302050106d50480d003820002d40b00418603503c8a49460f0031410800302404060010039075048000301c0200414199505881c4840d410750a0440e003014058200c030074128410001071000e60721080e542c52145141c00105400c2c22612404111905400d43c0007640107114581c51040081d008900c5950b0580c850303008100d0a0015202103003035a0001d40c011945440402010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 363334352 1250 363333102 363333107
    0x706090303020f07060e2802100c050d0906170106080f06041811210d180513020c0d021603062304051b060406080712060305070602340e091006030f050c1203030106 72
    0x1c5008460a080c5000ac00c101c0c0c1c2c80701800c16024030160340c00030795880018410746800140c0c080a800d1041a07060641d070401030b0180a040c009030038181e5085440e000540203a4850f085500340302500c031840726038004140b604142c040038203034a02d0b1064911240301c45411a0071461100c6046810000f4024003103081010303180070400f60184d9000040c0b918010500d030b2a40c02307050f5416200103070010381d19841e001c81d4a08110180f81070100319045408640c0c0c1d051080015a000d8a401c69400a00245904084c0441c481c074a079030003441c403210710100300900a0204089003004101060281c10089603005c1000e5403003580178407408070b0341840208210901c11014880e44450b14a800905c940d00c81c0c4a9a00c0c081a9034010b000513401800c4d03000941c440c0a26801c01c1072210240304006624080800042081d60300070310507140001c100142241c070081140d2203007001065810072a69449080100c0041c0516a00b80d44074842d5171aa003440707091901e1801c800458400c00b8604590800204 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 363335602 1250 363334352 363334369
    0xf0905010b1207140424020f0d050d0e030702100305041203020403120806190306020415110714031906150605090f0f06090402030a0b1f050706090303020f07060e2802 73
    0xf0b03420841310500c00030903101130044c40e440700701c0c80c2d0380700403100904031420080c13404200206d03400d4190480359140b480b0b9500801582c1d140380040b00045208040c0c88401403443c0680d60004e0352001d0400310092803907030076500c0203018a004200088500c40001400d50591055210040082c00d401e05d4071791040340f15600064010310001d0281c1d019000300e01619441d12002e0704140d64041c1c4c0001c0c20001d405c4024650a4001568100541d13030104107985a62a03041c079106440400742c003a2204100c2e41d40034010844205800340c041d00e2100251708210004000e0515402c5a4021001c4041003135405131040d522150001010112403141410902ca9000640c0c03e41070340141003440004150740d42d03400030f18841c0c0c05070000003503105040010440034a007014040a05411001c0c0b0707220034107a00c00c0c220f920203034103c440400e002c501490214002d01c40c1165119031040701140000421034a80c115140000c1010211041610701d0308404004845406c010412300900c1c2042d10010f0410741c40d03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 363336852 1250 363335602 363335627
    0x5130309051005031f080a14010b040e101d0706090801060f0509060d0606260d14030a0c05090d2f030d0c080d0501080f060c0f0306090a0609060f0905010b1207 70
    0x64411106da82c1e070b4041e032410002000c02c4645801c0480d01302e80c40c031404d12403450010004c407414041880340720003054407400c0004484003410348480c0201e40304003801c0104041c080c0740b042101d801d503136100001070000d4194000e00640703508241001a00c003e070810b404054610080042000e80c80740700820400808416040394025111840014881403001609d4180f101410b031592a04201780c038560b04100d0340b18802020f010280216910303e200403000e880d8088609c2d072001948080c000025a00c1d40a40c1d40030075400b050881c49041081b090859002c00c1c10510340c0c0d00d00300c10240750002a5030f9424041c0180d010350000e12004c10040c481c102440d0307140c0c0109019442c0514140001d01a9013090300300000e03d43c8045c4280b00411810441254440c2160407040d0804113030103143c55040c84050301c3d5a100d120740001142048449501840081c200a1002c00013180c0c0c0348001d03c107034003080c032601000c546008000a41c6440a204031011348030341100300603aa0352640010b5170b6070030ba8540c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 363338102 1250 363336852 363336901
    0xd050709180c090f090902120318010507050a1b081b10270e01210c1403100e210702060f0715020d09020f030d0206041103100513030905100503 63
    0x410000e958040c41d000380380504400032010070981e03c07e0042c45081141440c201c0959441000f61408585044048400b01442480c10030f69070b11141c105589800150b51000d801180f42005401d2401b02c841d0901c4210b450030400d64010004d040510303d40240e006101a030030110900882c405640700300c0c3c05e98043c8100340e185150710401c2004a030801d4119401020859030780600510a0842150100d0032805c04140056000f4550380d4a00300b219009110788841034034148100600750b82c2c148a546101025001c007008400d203003040c55a03661100c00c801d0076001c4070391414182d01001c0c405c112031b20190041c2100340742c0f0000026124841c2c0c40584103071141808410401080d081e5400100b09020002c000410b520045004220440d02c3c00d00b4864440c0d445180c51034030043d008140c0d9540715402200d020403c0751140c1c042420a901510303055201483c00d010847c10010350307103444030040e009554548990752180140500b01240c010010b01040c401d200103507105c1004900c0941182070351 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 363339352 1250 363338102 363338117
    0x14091f0807090213050a0b041503020903010f0c09050d02030a11040b060a0e040b09040b0a0b0f06040603060e0105090f0a051b04080c090f0c09011d090c0d050709180c 73
    0x3210300d81e040910380d4101c40c401c1500003600300e00084000408001401c403c8411481240c80c0406885451160348541d0408000031060590024000d605440c0d5541001e4003d01900c10f011009100034141900100d02054111401107130b2820501300c640c0e507981d40075000f482070044a40301d14001e4020041d10a074800d807211900350301d40c0c840b000a032565a02c25201c101e10401500304200c241e5104016160054040e0001c03c40800d03a03048183e034001052070400110083c040000c80c10003030189406680080d40060000f460503815409442224820340080340c469032200100030550000780d0744141402030410104034111280e0340000d4010000c4007602e009190843e4051903a030300710f0b074000409034012b18001c1c80142407500701658032240c10f00c50204507141c03043c100d65007400364004460400c1ba40041040c20062010300c6810309020080001c48a0301d42109a101e0325448603161504113410240400c800c0d5028001200590f20527807000501444000b500e4002040304420300780c100f0500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 363340602 1250 363339352 363339359
    0x6051501051210030c08032106010f03020c0a020a12170f1b0a0c09050108010e070e010b2b05071b0203060103020d031e020c0a120510052a1314091f 65
    0x4a14000c0c000700090b01c003030341d101c641d401880711401003044290031840b000c8c0c608001d03d9a03801590b211088049040c0186c0302c010701c0424503d402c00c404c0000b0b4100c5280080414124544012940e81610608070002d810074803001a65041c002c203a940b4100e1041800340c8903030307a1070a842c68485070190700304981c89043d0300c1e11080c03559041e0781d0240007100c3c2e540c1e00600c040c0200b8010459900c2d1f644004024042c40c1c01c0080d410110148120014842d001c92203905c082c003001400300701d200b51451404407641a44000b08010b0000303550f6a00030642c050b040f1124142451024040b880e001406801ca6a1840d02404008011101d00300d0401c00300b05003044a03051018040c0001040075802000285050024480c40d0341850b0015070130b01c00303141c0f8918009480040c01d0f1622042c42c03030b008203164486040800c0e410042184d841403100149410402045049020f85004040420745001c600e50f036841640312108020b03c3d00e504806808002141641158410540680c0404000c2c07001c0381d8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 363341852 1250 363340602 363340613
    0x815060d1406040b0a0506060a0c12050c1b01020d0c0c05221d06130803010b09010507050304030b190509030313020307120b0603011a010203040603091e0f0605150105121003 76
    0x801c44003113503c0313022101800b81c44000c074420b8075401182510b081c0d04c1e106008034041e140150000c0010005507a0791034600e0a00c0c032400684445400c220102c0f41003001402400444100240086006102c0c095048400320302c01c906054540d90045205c994150515050100304010054504492407414445908421b1039200e80004455500c58007240c0400000300141004000380030321080c40d045440d443c01089411049904542080c6000da60780c0040c240140c9450207134001c00340240c0804200001400002d10445109110420b55810301c901c896011070300300c1d00700f030b074460196910610001e00041c800441034180305000034209c4081a90345c42114044440001003140c200117180c2c103101c01d44c1001d014804000c450321203e14944041c1c0c20000f0769074042d51080c0020952a420000d05214107000e40f00e0a1800411400b03500202c2c4ec14101620080c0d05002c171195031a000c009801c66044895039988204141d485034501103100020103050517020b055142051030a150001c0000d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 363343102 1250 363341852 363341863
    0x3141005160815090c070c05040b010f080613060f18140a09140d120506040504050a12030e030a03060314210c100515030708060112030c1b08160815060d14 68
    0x5207000b6005e95a81c000785000401840d44d98041d5010b14103003078013000240c0c0c01200c101c039251903d2901c10526594440061024160280c213842043c0c03510001280c4141d480c00c1c8542a2902120b200d01d100c440e04040304122420b642c80d10742e50305003010104560b800c41d0b4004015880c001d203200c00204000b07811081c18060140390141c085400c48412203003800c064081c03d0381c001e10484042205140607110319480301c42d90300700140381c4d040b425002c45145010b07500c0700c1c18480f1000d0032039450303005005001e001401326020940e44440500c0792a03c40d4240011800c94204050356041d6030608070b40318802c810b0b0010181a55030340102500b4a141002c41d100c0c1e02c0c4980d21402103192045181d03801d05003046100c0c0c00c20781c1c0b690040360050203100fa04003a4826000d42c5071810823001d41d42030410a40c180f0ba00c021410000c0340d000c00001c0c256000040d20012514003141c200300659448000035940d40f00ca41c10140880c0b40c6034006070192a1400b40001141d00407024510030728400b003070190418 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 363344352 1250 363343102 363343111
    0x20604050d12201914030f06010c0c030b040201080a0e0d031a06070c0311060a090302060a030f050f0118060e010b0705280b0106050702010e090a0b0a0314100516081509 74
    0x128002c644071521030050942a08144c4c503c0c00d25100e40c82c103070214003589210081c440940760905001182603a48581c0030500701a07002aa81d40406403070f07180003e1010b60035502039000508103004146034031070910541c0c415038071000c01080c014210322800e41c040c03d1600018000880c1801040049896010040445501c503d039109000d600b1403900120b00890855000d006071014450b2000007600822000c058940480381151158555001107000c2d02c4801540c00c0c0036800c20044c851030304160309415041c1c40481810030042c08080b080c401c01c48543c0d10800c0510454140104241d41c000710041c4011401207064800c00a542c0700d819010844030909010003084550700350003403008070250180508020302e48285403008c01d4000034203c41201c00000e1203483c00303a011501044080d40000311182000d410804500d6903414921603101c0c1d60811102140520800800b018085100e0070f4440c8d1a100084442104211408c4481c82c0c1c004140f1900b17000c4080d00c1c0c590039a50200028401c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 363345602 1250 363344352 363344411
    0x7050c070f15050708070b04060f020f07030f0806010c02090a140106081503060f0a0f090213151a03042a030c0312140306041116060c020d020604050d12 67
    0x840b80707400e0380070614400c5198004200b1805001040008110000700c40507290040c0c4400340584580c2010780080c040024031500755840001da181981c0d111001800c490360080c4c07505295040104403d66a0260450382c1c20f000681441c00000149003000b541e0780c00003242503000a40217002000c0d810300010030f03000324001c503101104011480d1144c5032006103480090f00500080d0400028800d20440c015100104484e12036100740000c0b5044d0744110401d83e0002c014071303107150501180320001c2c0201d1044001c2342e00320400c0480c40d0b41d960400103001c541c21184c080d20310741d2182c03991030134150624101c622084080d449124000c03100c0c6d19520195026141110340e682c6580b4228007401c00107000328040c01040d50003140302c00311160560b40e00c64000d0b207011400313441801e1041c45520425070692001c0010b08004400d0003820741c00126016925001c85500c84020b02c400d81e6902e508030780007040303944030304054038809200d941111422000c28a01040c403020410301015980c1d03107804580507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 363346852 1250 363345602 363345629
    0x160f050601090b031204060509010305070c020d03080a15050310090c030f051005090c0a06140403020301020d0617060108030a0c06061d1b0c03090f060f030a0207020406050f1807050c07 81
    0x900e45000d0241c0d00500c4800c003c01480c00f0324140c7c002c0c0c8036000d8a8030351810b0503540ca0015a1181c01288010f104030760040201402c84c109143c007401c0c1040640b10380c0b001c02d140081101040111025100c1516001001004500c1c0b2894110303020b8400c41000b10781070744000500200043c1c2c0d042100072060700c2a0040c0420000206500b0100d92004041c900303503601c0340000b915152115003128069030f200d441c11500c0717101003624002403441141d0009405620020741d1a02c0070030203501c1041507410b010b04038030401c064543e4540d80d5980030700a00f10141c00800c484079a243c090048281558820040803c003d40c2d18600c0c11588020b0307144209264043c4010400d0301d0311010481e806c0c04125280c41801d05003002c0e8034582c2da0083c0c131280760103504180c4015115071785140650b0560407140410b181d807442c00c1104900a9008448201d00540c207144000c156481c0000343e01408040c003030728075082010100c0301e80320310f80800390100342408010807c95509100501804014203c00700b41c080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 363348102 1250 363346852 363346871
    0x1e1b0810050a050f0712060b0a0806040f0c09140a0b0705030a11160603050a11041205010b040b010828321b1b07090e0c010e06160f05060109 62
    0x41d030360000c002c420310600d00f100300001e40003072900340340d0000400d05d0168480621512071000800c40341c2c100720520b0f8004a492850183d100c000301d03219440c156001d000007a401400c800c01c0e00e280c3d01c1c000780800c0d802030044c0014410f50715000000800146040141035440c0c90f6105280d100c10410303138540c1c01c0003034034103095500101101003803c4034034001d0a64400b0403015070940c0c103044c0621400c00d42c40301c010480c12070f229040702d13002e00e4031300208681d200d64506e610881c013100080c00300c500b5420f2803c2c0506c03038581740c865500101c1040c1c44021090ba03411445501c8603107100da85c604100c500104814601d010382c81034241c2c1003030a20b8013181e01c02c981010a880c10490000c52130400205d20304000d2003002a2490500020781c00316034949400703805540886d903141e400d0030f0f8109031140000002d000f2486030007080106206c0304c1501c10041c0102d0045507861080f031141604444200511b1401c01d005000e040181805901003502400d1192744075414010283d01134407440b03840d0803502 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 363349352 1250 363348102 363348133
    0x30614090601051005090105070b070c051002030c07020f0103090f060e1009120e010207080a030210050105010203180f150c0c010905090f160c061b020607020a1e1b08 73
    0x15810080c0c990003000c080d8034180c001009114504000000c202020506c081e050340104240d0b901c90790320a50441d114500301c070008107918100941512603106e041c6008120003102e10031280600b0b01456241c0c5425080d07024013690f507451540c814100765444a011010659505082c511107200f000003103800b11a0f81021490141c5641c007000d2070a207090030030b04c00640019400d20341c840490421060805000c00141e041c20199441841d09000d9040b40104059011405900340c400c00241001030340d0702c42004998a000701d00d07488607112240e4100c03203203901e4188580d20503c5002000d1084103507549194510b00e0b0025100801654040e07200200150780010440e00074000580750600e641c502070101840c02c90300500744e01d8a4100129100e10360900c10072048408c142c108000740102c2c0302c0741c80c0780420089150402401030017840d0200b44640d10101d021a030154101c00c100480b6010109842900c001c03505080315401780b000c100201070400c0405c110018500d00c80900104134001c07040307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 363350602 1250 363349352 363349391
    0x122d030306080106211a0103050307051605100c061b12051303050d090629120f07170c04060e01080105010603020301121401110d0c0210020c0303010b030c0f03010306 73
    0x40120307410700009010594000090329400c0d80513005c1e4801100d0141444100185003140491100300424008005c0c0000000100341c0240300300c00304c0701741454401141c1c1010010703001d0746a200c1103000034105501c0c400c039018400b460181e600042ca07541c47c90020b41c01010f004445001254030220f2402c0074640c41d1160b10b41c802d450340b10100c0d05000720f540007041445865903c1000326510008003060003003540c440d802c60404014559960441e09143d071840ca80501d1140e44101300c0b6509014002c0c1001c9882854207910b800140714107800c1c0405515440d014a2000900707116002200c1e01d00d40d0fa50107038800400f540003402016504100d01c460a444058100f03070306240c01000100704084e01003d03400540d030b4102510152481c42c07600c0d2203000d410803c0b03180d208a24041110304404002e5132107910030000c1e41c1c00711340280b45440402c00503030145041c101455081403004101c085c2c4007000655000d6000d0b6400b030b284c07945040c043d420315002a001903a01c0c96135000c2c190f4085400200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 363351852 1250 363350602 363350609
    0x3206010e090d0f0504030b0705030a0c3020070309091a01141309050910090b06280308041505070b0601140c010204031101081f122d030306 61
    0x1014109280001d241c0d550b5440500b4000c0070420000c04000c5524454416100134591140700d082460804031002032031034000b621140a9a0300e8940d00c515864001d0a402c1c062443c1791045000ea0300462040c01600f10801c00c09462442d12881c2011a22500d04000c1c00004469007001d5110212800d00408180309030300928600e91070704070082120403040504186280c024600690306078500c149040d110700914034403054036100380a0104d00c9180f00d81001d41b00d20400005c442d41001c42c1001c5030155200e100000c0c1a03d00740c440407a4140c2044410000341011180e03411514010701050201c0344d010076813080e2403060700440d042c03119130fa501138240500c1c40c5601e403e500f001f801d80c403100e00118001e018075040c42140c1294101000c004001d0b10500b1125100031503e49a8038140700325511060340d620380c001581c80001545101c20030010030f41c030042c001c103000341c540c0c00c2039080307000c656507940240c501c032110151a40341d00d603c0c101c508502940c0c5c4110301d51100c80350310303010303064505907013 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 363353102 1250 363351852 363351869
    0x603070b270111060a091505040507030b060604050105120603070b0c151303020319021603030305010f06110706080402190909120206090d14070606030503030103150b010f0c320601 79
    0xd20755104a0b00141c0c441d0820711750700c000520b180192801854050035101d0880f003060070702007000b013480380101d074200490740500480304142c4e80304410440144a14003c0318080342080c03010802c3d0204060f00d05903c464060704840c001c94840d800306400c0d8001d00c04403d040c0d1300411048005240c0850300640000c0680420341c9110031030f1f07601075260f02882090703101d040340c5441c0c40700390390b03100b0080c3c009109a407070450300c0082e0700c0e0b04005003d000f0900521b0070040d04624000740551055515079902c1d0790072800380c5889410502d0890b0441c10141040e0b9200d1342c0b1806500b10002c07440ca110f0000e0017840b070001510080d91404211840544200300d0964010034100300710200d001c6442c4004100600c1e0041200c002105d0000c01c502a0101c094009880c18202100b0080000011416240601c400740445002219060159200c4034503003400252030004c0c0c1503068ac042d1041c030030864807650080c1c41c0354a4942c2121400040081c00c401c200701202c20044040105112440c017500011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 363354352 1250 363353102 363353117
    0xf010911070b150102070e090307030305010e1324060909030f081501201522030203070201030507030b0301050a05070f0203090f12030c0102030f0109110a0207030b0603070b2701 78
    0x191603110822800800d444040380103041c1144944e031081c03003c08044c10144803424140c2c10f00c030300c01c103940b03800080c000c60120349048004201d025091012520682d02000d41c1000c1d000c03507a4804115a08154076180610ba8540c80c090281c0c07080c0c0152409496032800026421341681070040c903082c41009100203000c514814094034000486806405520a00f400b01d0b2903200c8075a40300c0300c0c4030f05094801c1e00b07010344005450700ca440c84092030b000d5034801c20154100a10315a00b030b8804406a000200564010440074006501076081035030301c607005042c0062011413420100f0709541007120070212403a941c10400000640100c400000822248011424445139002060303508d0904070003035101c1c034002c990502e103a030010011682c09004110082d5101e0600078280c1000d60400e002d4038180354103040b02105240346c2034003501e420448a90051130002e140d502d542441c0e02000d0807464050040d920301050740080d400013452208841404442840040c2240001c4964104501c9041101c203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 363355602 1250 363354352 363354367
    0x411091503060f04020d020a0315060207060327050a0605130803040b13140a020913230f12120108071d27340303260f010911 55
    0x400e50880e00c001a498150307a9661580400207000a28000e54140d0003800000c1d0030002c000c10303030040e1624564640b070504c08034a21200e50300300b51200b4010080184d2008030304124807031080d08a1440e075a40401142280d42c2c1c1c00c18111070000d4060b100381c0d002d5200490070f00410586108566010990420040c0061520740d1a0070851001600181c000c91120010414903685080d0044001d64010510410040c0074812a07454220031042030380300b003007500c00041503050004100b809082c0d00100941c0c45401c0c8031606042c6100100c0b8a0380c45100300c920620f8110300412004c7c0d40d0b4103d100c2829140c0d603240040b1858400140c1041500f9008000c00308640072a6122585d03528a140e0100305150769a054000b1818004188141e8051a0191844a600400b2070601004056102040311002da440c00e0f900c0c0384100d2601c3c00140700c022003010800f1034030a060b01f0250301c000c0c0d44a04c094540450241201c004203070b60b5400d440400d1070042051800612556200c40480e04299040120 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 363356852 1250 363355602 363355609
    0x3160305070e091b160b0c070206041203020f030c03040905060f01080708071404030b0f06030616050903070810061d040201020c15160818090f0628090b041109 70
    0x2c0c0c9101d41405090f01e100491100c0c00520800c41c80c0e00400355406440729182d250b1070b8100d541521042d6904034062000c2200800c40e001242c10300360300034002500d03240c40c007040000c4080001c1c0c0260214020601c840c0d107074038802c7c40209510615a0300560300c650030004130404030340020b40050302c00c81680c00e503805680d0b042850968086010304000f80e46035214202661100c4c0080c14906030350400240110030040300c44007081c0501052805170081d07940749000e06a4802e0140d035402200400c615404510350700ca4070007040000c01c05002c1d54651545c94581d640307048070b0000702c940b90702c0e01d03510240300c3c00404485c288106a040170941c02d582c00c054002039240c80b00d07520914010140045503548605031b2208551300703000000c0d051500c0c0c01c0d8905150095401c0b0349101801c0440c8400201841e14006501e14003031550450701c500c45880704000c001d408404616155261541441c0748500549210f03440401020000c2001c19002200402c11084036000002c461503c80103000d00c04481d00e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 363358102 1250 363356852 363356867
    0x6091a030604030e01021e0d0305011e15020a0b01030f1208070e0402030a0b0603090607030e010c020c1c0b070809150129090301020403110a1502030319060e0a020316030507 76
    0x3e0b00350816102006102e40100d0401e020003070107101c113104003003402522410004641f803488001e6030b402c00c400c0c0d0301d900802485c82e40240c1e005200c0f004558040c042d04d03038003804002c5110624011101804181c0c0d90b40c40828109a105807118800c8a902d03030140a6602084054040701d03142240349450071250280849285101160041d50701100252a4010561054644060050145d512032a03c0800d851340c2e0f039011500c00340020300304a40040c069405008003012101c0580180142e00c4821050100030141c040901500c03d41100003100402e01000780e0f5401160a555043c20600c0c004800d18076043c2c0003002140c9031203040004003c00030b41e0002c42031500041c2c0c0e1010103c40800b0007541e0160040b030005039850b501c0001e001080180818400d200c2900c02c0d0392448515613102c400729000469000c0c0c03000540c104200094001d101484490341105078240001010740e112007a9009843c8100d80ca41341035a0700005226040704e501c0b010465a0003546000c1c0100d103000c6100074043c6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 363359352 1250 363358102 363358111
    0x2030106140a3005030a030f02040b1204020616030512071b0b060321070521070f05011b050d0b0d03021f06080d030b19030209010b0f120a06091a0306 66
    0x4140e18031204440c0c0d60070042c83c0e03d840380d542100303580086541c1043c540b1703940901c0d21200402d203030900c21104040c11340207860032200a03d50890502081c05440c0040400060040303a11120401c6070150108060014030f500c24000d60782c0c15140e41d10221030251220025007083c0a00007020f02004605240d85909400690f201c1e074420b100e5160103000c43d2a0015030b801e0664500e040c2c201080031220308a000d80038041c010f5046680c501401e100400290b40b00e1711041c00c418500300100300c0454150122115040d01c540d0001a074170316055520300100d0130304c4000500240c0005000281c0012740e020300f64a50b0411a15403080c10426680070f55a01c001031000c00f14071442024044c031a54aa0303000c080145007400950b01020080000217004080c55501644100c44081e014608120035080c0281a80e9010b008405075900381110f15050b5040002001940d010412a1594054002001a000d802c9580012a00600f0000c00301d027540c0a15020407285a200e0079900174a42d0001402c5401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 363360602 1250 363359352 363359369
    0x100609050a03080a030b0a3005070e040804031703060f03030309151e180f1c18120b0412020a0f02040f0b0a060903150b01020c041e060e0402030106140a 67
    0xd40f008044c068019002d480710b079641c00001c914002981c0c134684c0442140100d98030700070325168040c40030b0f8010701940b68030700902303554000308007401000c0049030007a40090250b5241030500b81e4a5452812403503071200103400c00c0c10040240041130502d00d207500c0090700b00303e019500710318107846401e035910101840706030704800c203c000c2030241000360907001d06501030840d031202030315000d00c003075401e1401184584018070442001400c1600c011408440c0b6500840000c185180c2952040b00c1103a1a60300c1d603944010694030002c1d80020544600c074445100e204e40001074503050402841144403504854255001a490800041c1c065030500c18400e0b41210006441c1041200d10f02c0180a802c3c0c180390407026481010401c40d03004102041100c5c400e040c08101d801ea0700d2000340540d4450b08210740544e02034400b11000c0d02d070907000703207400800e44d61495061001003810f0300103464040d0b01402d080d070206014032055060038015234000e01401241101d08902d180b000c1004500c0710300c0342086 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 363361852 1250 363360602 363360607
    0x30803060d020a1d01080d050a14031905090c030d02030306030c090a1506020f16030f061a0603010f030c05030102281101020a090816030213020901031d06100609050a0308 75
    0x4540d54824480054130b020034840c0f65030845141000401c2d2001e025a000700d200360707401c0001207880341040740ca200802e695900a038081e01594007000d50005420381001c40107440c2c4400c800c1860b803040b0740c402c40e6104010088994407205040c10003184403100011900304008005594800244421041406583c902030a80c1d40b4000e42e001481404500ca4883c4200d540000c0c03140e6001a811a4080010040e0740c00000d04261701c403043e0106120080c400d0701056800000300e10f1a901c4880185000c203101e800c2c1c00003180004440f64001d030000c0700150a4043d0601c1800240303110200038000540c006c510b0050740c495600380f50300c41100750b90450306c000c61400c0340d454440c1c02035005070040c81d802591205092030303000e01803240a0203140000d2150113042101140503010000460b50050500f805690300012080040d5004c20ba41905050b103c0710145484c01c040082c000c050b601c01c0d006000c807400c2030f2048409840c2c0130f1f444a4100222200140401d50703401c155a0100c0750300c0f140f11035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 363363102 1250 363361852 363361879
    0x10f06110c030604080a110a03080105041e051602070b13030609080c0d05120a050f270f03030108010b0102071a0904060314070e06031911010903080705151003080306 73
    0x20718040e5034480c840d400d40111400e010030040203c010717103041303007041c0c03140c2c441c4031881142c0d940d80c4e0341038a2024000600d000c0041240d824035510402d03180d101c68088060003807601c2d50400a0b110300790b80e80080e411180c10440d2455a040c0401c0c0c029016400100b8608510350503c186000182c4c04050032442d5254050f02c100045601120303165103520023a1110515506005011500500d1414200c001c02c1800a41420400e12a2030f2060105006680140d11403a92000c00b1094441011707014a41c00030700e085031910304010f0b03c03140c495040c00031aa00e6041200e841d080d00c074840c114038150360000c0000d004034401141c20341905260328540f1512400000000303400360901d54070240115100c0c004032070710040d012410200f130b107002c030b0001c15094540009250351215026500002150314051840000e0503411030100a0b401c14544541c03520348945034500c241d4440001210b0039070008890704118050003003c681c0c428070f580f0603c59a81c4c590b0310750110a100050402d03200359500b41d281c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 363364352 1250 363363102 363363137
    0x50705040e0c400f0c03090803130c18150504050609040f030203040905150109050906060412060e0607020706110c0d06050601090b130602100b18040515040f0b0f010f06 74
    0x560f80000c0c2118104401c051100301c11000309400d20000b04076506003489203584030700900078084400d134070001d0f09145955002c00c0e000d00c4020058115414071282c000007410034204082840e4014050790b0004117001107203000c2000c0d244690110780514205002c0200c0d030f82c0c0d150354040d4855009400c605003500203142c104d040d8411600a0f040d106e01d00000d01051060740680121540c03403e0f203680d0401ca0311002080202d210440b03046a219800308030501807000e6950000700c045100b4400803482c540c5200441e030424804450000050340441e20030040240c0c00035101d116131186c3c40c050300c804200709010134100f200300340700608070350388500c0446c005910510340340c03004105107403110f074951001c0c044002c0d802d0028420030005103e11280e91503041218807420004c0c041c000c0134000c402540300c0c560395108000420075220350041f000400794035485584d00e14400c5104050b01c280c40c15080c036044035048005081d01c810031142e000140320b000104c10302c0301c3c150340c11414003450520551075071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 363365602 1250 363364352 363364429
    0x905030906341b05090105150706090b041a010509060d02030a0c090c18050d1202120c0a02101115060d0813050f0d051009140307050705040e0c 63
    0x1128041054651480000300000b5802010038070848480d481000c01003a140000ca5650148942c0064070b2001003040c3d2500942d0291a62851a22581414515219681190f0101000761452140303a02000100404d502c102030600503010295403a80d418100030403280c00c8003d01c4107020b8011407440d4070655804100c40c03a055075100c40509002d58948030700b10050000410303031a01151006800906500c4d03580c440d4429610050004054202103881d0580c1c07200c032130070000055000e917505d01180284c200008000ca0b0403d40300034031481495105010700441c0500d00307982002060040c281c602e000c041040c0c40e80c1d04140030484015101d8400044030304550240041080f4030001d6400c40d281d012079000350840e00111610b102d2581c1042c01d020380700c10700c81801030954001c69260703030040205a0084c102d1078003e01410b42c01401d100702107850741d400321405940c654400b90042000d490f290049501000d90640902a41c80742e8802051064400c0d400b030006140781e5104050045980210b03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 363366852 1250 363365602 363365647
    0xc07020f04020d1a0109060c0f0812072712020d1e06140903030f181c120c032304050c0d03080f0703020a08011806030b0901140a0905030906 62
    0x100b10350341e650100704040248800d03034804a40d403141d451249101c3d0b001710058000c54405032a029071010b100d54800c118100b00f0441154609070a11484a400b1001450740d48070742410703121640342080c4214410084024141010103d0310701180600c2503d526007269a6140c2d030540e140d180301149c903c2d00041c0c43c00e07008810355462061110141c03c1c0040394110b03020380c418000402403641c542420942e10391004a0b4541ca200c00e038600800c43c0300342c0c1071055a440d078000e034081ea48480c3c104c541404100550040c00e0b40060755000d014000684c1c01c2c850468040100c1c2000c1160300c100c1c95080015400a111010b0360b80d01950008003840003e000c41d00c03030008002c2015403d14001d10740688942005c1d1000000c0c1c11141c000202d00601030301c01c450099840e61940540344e03181144420300c00e002c012044110301e40350440040090342d442a514020340300354002080d507004c0d0400d0520070242c01404004110f080a545402240c004400c440c1c030aa82601d8240d5211710504400d12036600c6c9a8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 363368102 1250 363366852 363366859
    0x3141225030c1b050406080607020a0210020c03160311120d030209040f0f020a020f01050c030103060c050c06090607111212040309180902090a05060a150c140106050f060708030c07020f 81
    0xa02c0c15903100840503500f0300fa00c908403010400e094a40c410369542d82c000f168803d015a201541d00300252a1100034000302d030000d031044034200041040800d0402c1c149032501c08038109241c10510030482c514aa644c031450042e030f0b8451114598024080e620003685e909030080c16800140c0c21040d48031a008620301c81d0200f4010b21a4140e022280c50007036001c0444000180641d5404040243e41030244a0051841b06001030440c1d00310b840f108010f00c419014001409410418030040c45410f000c10751162000301c003e803a142c07409020203020782c00f088071140a65045049004680c10400096400c034540966108585580320f00e0240c1d08091241c100c030500d600c00c1100740042481680058204038401d1315142181e880301941d20f001d032001511826400911041e040c0b00c1c2d0021310310500e8035000b007490660300788001070319001080740944207240300340d0b51103c0c401e21050134280400001d100c81981c1c80da2600d040c03034550041d1400041c0020149031000507020080d580e82d116806101030005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 363369352 1250 363368102 363368123
    0xf18030d02040803040303021908070209180105091c090f0e060103110c0f0709050c07020f0114040821071a040303060306060612050604022704090b0103141225030c 72
    0xc00f92a5600d4120f0322040740148260032445501c00d4054102c81c48882d880400e0b141005450380c20805403107001030800e50086540304251810100902135075000d40c0300c0801a101070b4281c0341e1a450440150640c5806225842c4c50400a6001401d014800c6451405045505407a0400100d02509aa900c14000600085030306211040c01081520b6058488022118070702d035a6203d4200b600c00849201d06000400d0103004091700b01900c000b480ba9005251809014034640099409600030707400008056120940354078400e4500c00118100044600800f410300c441540c0302c4200300c904440f609205241c0070086002c240c02030300540040c651061050010985503540204242c0d0651180910700c1d0505001c5000f5081038800c8a41000c3e22404200001d8001200c1901c200c05601031f0913082941c0e100150042000320307240d54040c5101d828501030040c410308501c0e240544240361481c0035070003041600307503402031802d440700d03900100c50f807803e031014250406507164000114041c0c00030700403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 363370602 1250 363369352 363369359
    0x3011503030801141f031a060409020d06082b050c01110a0816020c06070f081303020102060a02042102120f061605040b0901140408150612060f18030d0204 68
    0x10782c0441c141c031014101800081c0b1003400f001100361960007403800080000c00b41c2c801261003500300c10002c00340400c0049080321004003241c2668000ea101c0e16000c0c3d40880c0441c3d0207013907401400d00800040d0000c10000604038080c1a141004042911110804060341083c0e20b00460594000100980082040c1009880b148446031f1011000713900045800c8001100340d10700040e00840e224541c0d00411403520b0346001d00c960fa40c402c0e171003030300c10240604948001402d540010840d0000a06500303812a180d440068a0050b0103000301c501680144002d011910b07a02c107202e604114011442c00c841e410a0010845100714102c81802c07e0003420201c0c001d20000140081c0100c00e185003904000741d150300c00700e40c9801075014203141514100700003821584610b111505e64201c00714400d00d45655555003918024960f0f518500030b6012408000721464848454100103044401414181c070b09141800d50380c52000301400115a81040512941c00c410410b0303842e0301003010800c569907501c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 363371852 1250 363370602 363370607
    0x3090303110607020d0311040807031407060c05030d020a17040b04020109050406060203160501020903100504060f02070807060507120e07050a0614030a0b031c0e040e0106060f0e0301150303 83
    0x405000503404641d2048041c509071000050755840f40c041580030b41150124031a040340a00f000c100c0030190030105020214229009124030002507106d1b0f00101250700e01040041e0400c034a590011741400102c3c18048045113000c0211510032140250050352103014650641d80f00f58104034608064039403004020401c0840c0615502980c000d03200c14500742e80c4e810802c070076240540988001600140001c441d80da0140c0d0078000800d10400c009402d202090003c00c1c82c1c20500900860380d00e4860052200307003d071911840000f4401d401c0e0075403030040c15403903480d035601c80c174200140320603911000654524810032844511824200d4244440340e140310138281d40d0001c90007594800c0d0080070001032140c0c05640d000540d013100201c5141140e845031002c074010621070380c40c1c0c0d41500036541d0125a6020500441c0c1542c0d81301d890381c8041c4400542440300b119040503902842c0da2408034240402904480d00e80c41038603552405606244451010a01401000c800c642070701800c060013004054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 363373102 1250 363371852 363371867
    0xf040306150909050303071413050108040f0206030c04060e0f100e0409080301080703031101090209010e100902040e1f0f0b0714030a03020c060f04030f051b0a05010c030e01020405060d0b01120903 86
    0x1200755038008c0d03c00b08612040b042d512400319455a8100030000402c0b85502070300c9502d501a00401040419601903008524107500849130580c0d0f5400000d41840070540252a460002e0302c2030f141c00005d00110301c045204120a00001020b0221001c1542420750f2076030800b0380040e6104071059100e5070b4a40c102c681e0342003140030441c04a00c030f03031410100314001445400c1c030990300241400341d16460400c401140c01d40142841c694200da01c0408120081240020401051009000d01c2c0c02d01d4010030403001b07128145007403c2c0d0361148440402030392442030070510a0310300c4034040e03507522189031909540040c11f07040001494000821008151605980540800305003d0203076891691114100032090f0011030380100401c8041a03403000300d5205102a103405c8005c1c2403608076064011761014a81066000d048030240e44a6070006101649805400618038404000b035051509110014406000760004020010741d9201842c1c0560311645d41290700d410381f041c081200c44d20700d080051510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 363374352 1250 363373102 363373111
    0x3030e01030b12100506030f06010e15030d0e01050306061c06030308010e0705070f1406090a06060f120204180f06050a050c1c1505061c0509030f040306150909050303 73
    0x79141240a40550802da450310300011400e1000d01444600c004040009040c0074285070b800d4814003038503140014013009441e000c0d0032082d801e401c5030b00c1c1c03c0303007035440f000d039908621802a0442402c03109400c0d000341188a0f02e0f0403d007400c0d40c40e07603255004107031140106040b068031414000f03488401001ca65224405990003a40d8488003a80c0322501c00900517002e6030702d080010010007c6002013412442c0000c0003d1003821452428510760104070300d0a90300b0740340c1511036005840108200412072280318000c1515142c0032903c185403c80c1079070034910696020b0f000d19101e8220581c0f00b04a51000c4608990000090136030840d43d0418030014982180c014940c50326040200d200b018200041e00e074604d11580c80b00092030403048003070740980340800c10b04081032030303000e0042a50303507860700a044a4411007280301c82911490a408080c2d64000c1d040d0955500104217441d550840d0804940c10780740c00510225100c00201d201c103099000300d40c01058500e03d080c1150081150100085008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 363375602 1250 363374352 363374357
    0x12030703050c0d03110304080d020f0408030a0e0a1409270a050706030203040b070c0609050601080a0218010303080414070f0f0e060a23040e0a0503040e010b0c07090e0a0c03030e01 79
    0x43d00c3d44004250300300c070841c3d100c0241c042c02c11302c00100091602e0300100802d962030311000d410907103404112091a081604070228581003c1404e0344107170b50050741480020f108645e104403562810341d4102c0d0326460400c8090141322980006141c18041d1810041d03030380c0c82d68412003480745501c0b4580d605c03140780e40e000716064086c24000040c0303d0310030b00035640030356003024030800c1c1622403400560b40550030200494603152a071404801051042c00402d0090108030301a001118151041207031180804021030320010080c0c0042c004250300c042c465600c50340c003c2c4d640030041c0c202c038112407415100d070b808114103400070752000c214011580407520494091480d20482a1551401c1280d07040c1e06009081c4414084e080541100300c880f592200440e0000d0f00c0003030301700d011542041c1402e055100517071b900da10008003041202d18450071a4014010403502d5803d01c07160319a1a5155102485070302820364490f40c102403036180601051221641c80344c2400c45050b9203150280c84804441071a502 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 363376852 1250 363375602 363375613
    0x30f0503010e010b0912070e1f080c06130f1e080312040221070902180306010305060a0207031403040b090c060703020307021003060506041d010b0c0c0f12030703050c 73
    0x1002402141501e05903801014501210380c20700a416a1940140c2032a40c1c1c01803400007100f14011040c007020001e0300004201c908035181600d1080301500441d0380d1800e0a46420404020080000c200e9100e400b400721032541c0c0c1c501e210342041c00500c1c8150411040c031203180c10002281c0044004102401c04000d884881c400d5444800c25140e0040300c951050881c116000030300145450707007094410352498a0f00002404d20600b805151011541094641a03800182241c19a000011035448000c0c02c4004004541c11139842c1c5856100180440440b1034005c82e03100101801030350a107a8807686c00d801d2684910b0203040c000411740003941c040701ea07409080300c51131042c10080d007101c2d60140c15400035842c200596080c0880e085010400300101551035101040c01c4e500d43c0d0050004100c1c105044128580242200708040f07010790021305818403c21a984800c540801c8118184000302d407c90200d0340c5180105006070710380806c48405000010700c283c101500175010b0914880203030122030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 363378102 1250 363376852 363376877
    0xa090302010c031a220f0f06050306010803160503041d040b0603010c1710090c0f080c03061f140309010c030b03070522020c0703080c10060b0f3403 65
    0x1821142288146584000d01446810309418902c0f048500302844509081e903105c80d080030501225031100200d01440d84540450250403a01c0c0a600c028280c11000381503194504041e90b0781da4070400540b001c001664001603030034440144241c0d0003c1c440c8001e021020110841c0d4900c400c0780440e4225105004400420198141403007141900c12082d21040500c100041603030842d1000280040c00c1e12082083c013054508290081a00c0c1c64000e8a86201c8000090303005080b111004110900184041c02081465034418241201600c0720128400b4081000305007200c0310f08203200040c2c005100081404003401b41540300842c40b91060344c0c00c0040d0b0078404101910f80901d480360781c5d400081031454600e640c161803000780004e10841001407400c0502d1a03040d0134510300358401c1d1001040890340640e4848207002000c98006080c4080003403034104000010b1030b00030004201c005d04004100c41802804140e08181a00300d0445501d0850501d80c070f211074913204580085000980000d2080d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 363379352 1250 363378102 363378107
    0x405011b050d11010902030f060613020a120209010521063115030507081c0507230309040204030506010303030b09090606040c05040506130806071706150c060a090302010c 75
    0x60545680700029142070801040200d0740d542101c11a020300e55aa6140c1d6001643d08002c2c002d40b018681c40508101e103402801c0006c00b1b031680410038491401000b0200f2815407040c040c1c0c0c0b480f46203810040c0c032005c8200c0100e80500541002540184814020040340041406201d21542c01180c8103c107801001603580211112000100700c008608059921080500d401001e55080d01c0c01d500074186680c1d0b01c519180079103a901216240d0007580700c0110800f03c410304002c4426460400f00c4c0392070495a110881801881d018007102d038001035a0f011424001e0084620540c00200705546458a9090a0382c45650070300c42103000c03a01e4040c4100319802e1a00302180704000c0030000d0309441c2d0b03034041840040d1540808010401008020100e0f8a80e20354001c3c048034210300840c0700609080c09061407030400b018040b034060002c031800b0075040044054240703922101c25906c0d40003c984048440446000320342c85000d0074040c00040105070200e43d070100300ca8a001e0b034000d2082d401c9401c0107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 363380602 1250 363379352 363379397
    0x20a110c030102040f05090a1107060c081602060412050d0f0204090506180f0603100f1508030c211e0a02060604150b03040f02090a151509120c08030f040501 69
    0x110703100c3c007581078006c12152030300090b680d41c0200b00303030404501e45c01c284000000650101ea0304943c81540c40541429455108858507844808018040580ea050ba44042d40d1128001d00040488100803048203445100f40d0541d8140400c4c1d100030b0100c01e2110b5101d001942080c081c20310300a2800d000210545000c981c124005850340ca010042c45d01d4845007250344c510001d00c1c168140c0700305007076505a090f25100b407564010450740b002541e0007150780c0c607401c1d224056000c4003c40d441845444030800000c1844204882500c071048031711a059408600305002c5c0c0780081203500448540000020144c0c0010036201009a0940c1d006030b845c442080202c03684101440300c0d60040d8201401184001001950443d0066940c80c941c0301c00c0c2c0e8005120142e0131105206250f0b25090012070360a003074880500505407861440d41b00300d00720f603002002e1500c0c41c400c26407800d0941c2a060705018202c0001c0c805440745800307480e62803880c0002910140d00602c03d00380014151041201c501e03080d40030303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 363381852 1250 363380602 363380609
    0x10f08150f1602071809020f030a080a030b01020a020901060c0b07140a081314010e0c03030702060702220203330f0927010902010201050709030c0303080a0f020a110c03010204 77
    0x607109a1102160031003071100301d400880561081e8040801d503c01380c028080c1c07580e444860701240c4001c0f1807061183c000309001555000351320030980c138130000300d00b541583e904124030728001481d20703030b1100100d141020042e0040c3d0001c0144002084480d80008000212070051400042d203444904049540340d001d58036200d14101e081c05044040c80c4a481c245400c410091807001c4001309a40300c2d40c14001d9140310602550b035460b582803002000600c100c040402049000e141044050b130041031003031181da4002441001507680300900c0307844c1500c0403452560420700840d12071608104250106c0ea040d02c102445000c4000000e20011a00c1c15506d40f03910007800196404030303114181b1403030050141c070b1954191001d03181003139502041d03800200040300190010540344280d000190858201500d40c0b410842c08101c1840420155495141101d1b81031820140b00d640f001c05060090045105512600d03000049035443c4039440201e4400c3c0321809800d4811178070529081500301d104030711 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 363383102 1250 363381852 363381871
    0x1a1219060e01060801120303110a02160f03030e0906031f0b0a05102c060a0206010f0603050c0f0d02121e101d06040f050108060708060d11060a0e0405010f0815 70
    0x10700602001d0b6106c0b0316807501d10b2080c10042140e403209486030115421a108200050b84030b03080140703503104040300080007003c4221451017098117540b802000311150185690040c040d0300089041d1751800c01c24000040408501055848101c60007440540441078441d80702e030550307075004581c510b010020721408001c00d03150310245e4200c600424801c941192050b0340d05104030196400c65813031fa140241421a40c070380c0503000f02e40c10800c0e0081110166044181007502e09001c00c0500f0760f03154111650380400442003a140c03840360305500041c0c4560749140003c14010320511044200340e10400c00c800141602e400020703a10b41080c0c00208103d4401c0014001701e0300000050030035802c0072150001c0c000b820200c0d15441b800349400558200f80d00c020a281d12420800c04403a0703019500d540c00c0f00d0201d9803946443e100e912650385640c124182c06200c0e8000007110f900b2a8084c2ca40d0601142d40a0400e0000e580c0d192018003001040e03210b0440d090017011064100c10760001c1d5003d100d2010301 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 363384352 1250 363383102 363383117
    0x803120a051e0a0903020a0c0605070302191e110409060207151406040b1206011410140414180403030209030123160207030b0108030a0e0111071a1219060e0106 70
    0x100c0c1043d014102012064080d4055103100c4004503528403443c0c00500015250543c1c1d4446c40d00d0000c1c64201c2e0800751490710b804030350904000501d44580c00c0240070504100310904412410a0f080c0031914040d901d5102c1d1030303c0c00a05c100100c54015190190044508040002c2c07160310380c60907500781000324403c042101001a00c00d20385039004000a1344040c080d4500c1e0f513441d41085240280c00e070001007101401d910500308503e8841d4224403581c40d54a480358407079503001c2d0019102c3c000e90090301a080012500c111460301d90808001803108a1800d00e4804d04003070174050001e601541c3d803103009509100903001e41c0514540b01520030013544441240031340c3c90058020362500060fa08a046018660000011850002d60540604000d502559456210345c0f009003420b011080000d0501c4070398654a12440004501c600031108007015011040741d42450640c05440b031226010420122241801200050031640c401c082c0d400f407008201c980c0c2c0b07139079602000c41070034440e60700000c401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 363385602 1250 363384352 363384361
    0xb0105032e05090a2406020a0b07032d0506061201151403070f122d06051c0605060904050703030c06021e0304020103050a02160f05070803120a051e 65
    0x503070301100491000000c0801565100c00008110310010741e1002285038032000364032036280b00354002007020010408850229840c0c0300002e5140c032a000c5019240c4c1d1203210000d100e140c0a6013004101100580c1569468507044004103500c2d0b4100e20394000580c83c04002a500e030802c0011200b012003802c100500a0380f91124410799a100c900c000c0302001081101d6800340b8482c0d4024500803103003614ac502040410035001440000d21003201030245003004010208803000ca1b1518034054010b10082d034182100050a001401996020b290090b601c171200340001d8074080303400f449161040400b4441a10b41000b04900035100b5100034005c3c0c0c0140702d041000a000c0c2c5890b92960b4420f000140c10140803086000341581d554121145003200002004210f692520800c1d0b880b1103803000850800000d80d8540c48040e40c4040018481100309800c201445010000000108001e604403542c4104695240f2040707142a1441d520490510001c1040310301007401d1200e140032450321890b01c590b1f8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 363386852 1250 363385602 363385651
    0x30f0702040b04020f0403060b010c0c03060b031501090b0406140303030705070609021305060f0103092001050f0408010209120604020625060501030809011b080a0c05031c0605040b010503 82
    0x800320392142ea51003400d011500c55001078402641d56202c25522580396041a00994800f400c419040010b0b07202c800c0c0000b110f5000c603800b5203406c0100043d89000c01c0001c641780c200742d00c0d11100303141041c80000640d03c1441c0c10044458100b658180090b1350b464217a0010510015005c03603154101740001507503e0f2152014244081c020500824209440d8020415860004d80004070349030311541005401e0802c40000c049002c02864200904001034803810190b444040c42a8130000900e25201c1150307201d041034503461a0040303032650b9102d03030317800005000b5845034649900030440d403404a44c0c02480810134034481c1e600904814900305c018201404c1c50340c203815001c0524040000c509003c41c0d140c1c800e15000e5442a090255654007000024012903c0440c400051404c0080c510f0001a10401502c655084609050440314124500142140a602e5602d14084c024861002d0070503156040801220000e9600704204015100115000d100807125007540d08000c10400f4030425 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 363388102 1250 363386852 363386857
    0xd05030c0a031e0606020a1e020a0b0a050f0d060806090615040c030603060213030201091205150c0c060f061302040b09010c050309130b04050a0c08040b06041d0109031d03030f 77
    0x16008040700342e52141d00f40c588011601d1030b4101d940181e00a080640401c10a0303864000d0781014681c001c0140130559000a140051034069120790000100e01d00000c1c0d40180b00380c40b0b0b00c15068201907294211000c1d200010510342c800d4100501c10f90000c80c000301030101d40180140252100d0001c040003803414000508066018003041640d80d800000105086102030012a00d060302010510351031070000620030b0320350303401443e4800c0c1c0d204040c2c00003660021340c0c103da050201c4550403403a55482c21072810703030050301e078003076520301076030342082111011180c405115141c111080041d001154003214101e026a0195101d0003400b004800c0596010f149150705880c400c0e42200d00d4203041ea8040303205854101d240010040e218901042d0500c0c0500580d0381c40b851010003002030f4500d00c0001090f04002800c0580304661010115600351960f0300501404605101a16202da100c490310500808500f007041d8009051030103c0040181103400035a903640b40280154200302040003100e4076139 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 363389352 1250 363388102 363388121
    0x21315030b01080d0905010906020307020f0d0813090f0605010c0f02031e01060302131a01201b0310050c190e0a0f080601080a0b0408090102010b03011a01020d05030c0a03 75
    0x100920000c0040e24502031203010309070f508040c00310820002c20143c604841c5400481c14060803a606000d41e0b40e00005840000d070f01201d000b8501c01d120800700d8082c01015401510b80c00300040e42082c0790712200e04100c00c4680c01d580801c060484540560101c81d218002c041c0003616515020012503100820301043c81d0004064880c150031400c1400e204418021480c40d240c1d46a031020000d500d080194001505001da00a01c2202c0320012250040d1569401c41b40c103000b84000d0701c45000c00c3c80c3d0080c1c0b1040302c1c29130880e80115444920040c803540d902c504948a842880300940c400d80c0c1c503020b00c9001c2d019030303d896404c0030100d0f150051000e41c607a2512003003080d81859106540d40d00000400103100000d91100d1150811039240d003000070580004c00542c2c0700d4201000010800d54503298441d40002003191265160ba004034050312041d00125410343c02d00c1f05561040304142200344503607070300760211908000341c1401903406001c210343d03d8030f2031030381840f00d000407074000d81251112 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 363390602 1250 363389352 363389381
    0x6020a1713091d0105040302010b13151703070b040302060f010915090f020904060e06030f070605030c090d0b040b180d0c120309050604081806041401110111070f050c010c0213 77
    0x1500030f8110a2421a0400c44007540142e4441c5a45001030609080404544480180501c803140300041410300214803072040044001c3e420b081a0703110751052003582c1010b075001c3c20500d024202814025070710b203030644070303490003681440002441078600d226200d0380350704032554030407000d02c1e1401e0100104240e400c020050741e000c2000d0034603a5620720414018100113404510a8141a01410310304844a041001c0c960b000036000d100854114059070307400540e0500d4035a030303801143c02050300b1100c0794000422203102141840108a07180c0255481403c000d100b040c0090110081541e80b0540c1050450114243c1400d11011802414141d10044203500340400c0441c202d43c1d5003460f0100c125000d580041b40824400b000741c8000605004d440b108480344c1d400c1c030b41803081a4025001b01c07921103041c0003070300c0c0c0034030100c40c000e41041c00442c071a0250350341c17241c140d030620b4001190218021075840c058031149142035802100c1a202d043c2e0090480f0300c560f08005c06200050a00d101c080c0e02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 363391852 1250 363390602 363390641
    0xb010504080d08040605070f1403040204140108010207140303011208071109040b150312030604090309053303040c0b03040507120f0308060f03031c020d0606020a171309 74
    0x604601c20000c14403516081c3d5504003540c41c4c075080000440703101800c56000c0060300c08013041d2055120301c0101c10b204080e001a0307929169440054011b14105222248090005000003120407042d805401c085000700c040031030070300800c0174954a03031009004104d11039281c11041004680c44034090010740b4810400c0340c580091002c0022400441204e0481d40ba81600d800c022400707441c0c8046401c00304081e00200141d8940b8640900036020041041d8051550350b468001030500c1008098004d050280c80f08090041e18940149050412031403034081ca001003200300c400b002c400341140c0c4641e0b00003200f80411814000062480e40c00540305441c1ca2165903800b242118280c43d00075030107481041002481071346440c000e0844940109028071401815440e41e07213944011040352044c01c100990f8480c0564160701500082c040c4480840c03105190200106800c0c3d0001071900e00e81e405501c000342628220f10b100650f42c8503d8500610b00c0d44a03d6040103518941c0d000380b00c001607030411a14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 363393102 1250 363391852 363391859
    0x2307080304080618010e15060f3304080a032001060e0f06060c101503050f1e030c0a110a03081c050a0b010c0b0711071d0a020712030b010504 62
    0x1869508075401182c01604a0424080d0301ea800c43e038004402051400280300c1d0b0030000411545901e107080720506040042c1000130390607640c2e005c10201c0340c0c90040c4000a02c0e288020380c0a04004d445648140318100d09025400103414003096074206c40b006001000c6411240d5011920041984039001d0302105064000382902001e0140c80003921700c0041818092400c1c011500004130003402d01402100204030800d0341c00000708a01d0000000040c01141c1c1e11810200800038140c26030000c0c02c40d00030740f064003a98110114800420150100802c4228140300344030340d0700c0344615283d1200a6018065001c0050360100c0b004007195402440301c02ca940c1d0301e0321001c035158007401e031200109081c04401c98440006104042d0001c2c40c24804001058030000040d241c0100702074040c20041d1840001004503114960f1030450300007180584d0314140e1765a0000d1401105420741103041e10780d9900040c80100d4601c00c1e101c2842d000145105030000f120b40c1600103007100d40d0503a042200401010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 363394352 1250 363393102 363393119
    0xa08160b010e0603070b090907031d01060602160501020607080a0e010b04090f020910060e0d02030a0212070e160f080a0e010204140102060a02040308040e072a140a2307 74
    0x40c0c001d20b00d0040a014500c1c0c084101404c0100c550440030a00b035080c8094202501d038569905d610802030f0400060074551032507070700010706080703046060542c24900b020400580c08202c2500c0b0184560041c000681c035503005986402d0112801c2c0001814900010404009034001550980201c000010244005004107085d00e07080c00c0f00b0340b840014100d00700c0031818108002076000e07800c5180341c0d50040c10540000c084000010445119440581d4082c1c02e6503070500c8207041e4960300400b4028005840e65440752103500030b1007101060301c002c0000130300b64002e5084c44003243c146541c600b424415a0030701a2440c03c0041c0610070401e6803009004000c00c1c091000740301520300c4809d2956603030710003000240ba00304000d042085007401440304100007406d4106490542d07800d2b030350380d40c00c994640008503140b0300c0f01c0365220410003120308620442d401890301160454001d2202c0c0c0c00502e0350081290381c42840c10001044681c2d1082643c1640225113882700b40e0002c85802d40e864159140e030304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 363395602 1250 363394352 363394373
    0xc21020303310b06090f06030c010c020a050301020d0605030d09030809010507240510050f150304022e090506030f01060809070801020c0705090601020a0506041211010510150507050a0816 82
    0x4548496040051012030315003045c4c015400b13503054120340c0051801601103501c17100907090380d5040c030030340710400401c550301c0b104072401416024000715115045c0e49200c6000d40640c1c460b650207809144440a003885c4620760010503650401003d4780740c40440300045074141e01101069a51505c507944440c00d100f49441c19042c25414240c001c241401c0c0040608502d05466028510038442c42540c40d03102e80311100c5540180030f0260703400c2d4503076443c1d00100d10b03d03606c0d2000b0542460ba04108118807210451f0361000d0402c240d40d502d5449a40311414040f1900c005c0d074a6500c00b0541b60010082144560070b110750040d804020f07906d000b41c0d650541c2c4d007640c0150301820705642001809204a00385040c982c1d074413003c03d02c000d00701000720751521500c036080a00060030100c0f00d002038004040c015511115003d4019000701318500e44a03854044007141030003828030208095106c3e0107000d1080060301c0d00c17190060040c1c070f03400303000355030350729046d44450b0030201d00e03d100c180f0308030110758601003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 363396852 1250 363395602 363395701
    0x302010504021c0c09090c0e13061b0c0605070306181a0613060518150a02060c13090e100510080c0d0b0a0c1404060c21020303 56
    0x1040e181030900c10055101c0301c1e5446a4481604071200c18042511180181e0454155600002e140f42542c1002003480e0020341050490388403000520880000320207111405a001e11001c02203440442c1064100001c0540720b00001004900741201264850744015009182401c00280c81e6603902968103078000e00340c0408030303002d40c0c0c2d03d0003d1400003061001216980d048071490700d000303a807115002141486000701d00800801059400c16000303400011100b40400070310180c0100900341d03012060f640510045801030007698003080c01c028022003036440c04040c42010706002410071104074000c01035800d03000098420381181c403980300c1140c80b810380210300a010f210291410481c1e16460302c11844520381c05100300300d01210200303129440380b03030b040004041c0110b00000c1c488000c5503040701c06100c2004c00300c3d000800040ca15000142c100c98203100d0b460851161030701100c059040ca80b0444a100560801c000003100c820141e6000c42030000350300c881882041c203005d03460540c00400310 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 363398102 1250 363396852 363396857
    0xc0301050c0408190b040308040615030b01080c1e060f2709130f060e0f070602060603100911010e01050c010e010203010614070507030b060a031a040309080d05040b160f03 75
    0x741400905010f10080f07200c4400b0600c1300803084c0e9140d44800f5180c070010005010000b200e03010030200074131030300040010b503030034031440321181c0d01da080044a03840284101d19061042c980d00c0f03200c40c240401d40314031100603512012280c2840800303102256000340320309001018100f200e01c0c0f04e29803402d03070405141d000c1070f2045041800d880a0000c406006070108040200f50440500000e20811044110f142e004c039011075450108038001d480c107a05140300ea0118055501c001c98000c2d40019061710607803080341100c8031120002d03440c0003162404038001d000c2061000380c00090354000c468000440c5c90601d8240d2801880154480c216400707241d400280b6500000100034403503001c04040c815585001959150a01551ba52607a900e024403005010245403400252103507510550301c001160001d1300010900c00d101c180b00c0010004980450200e1107900c808109003000050b025035078010360315214a000e017400b40344450b40c0c0007803001007003d12405a44a0003c1c4200348200000c40c401d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 363399352 1250 363398102 363398107
    0x4090204170d05120112060b0d210f0801031202070f030f020102060c030105130f0b03030d0e070e0126010915050609010b0a170a091a07030606091401050c0c0301050c 73
    0x1881c41c9080c0001e031000300d020014140400c80b114510700140f11304440304450511450019840c00030301628801c009281d01004448110080c080c0c083c86812030140b00c48c02040f072800501c1025210329020906140025046a0061001541c050003001007040140104d13075002d0350302c1e02c50b000107180e10b800803105818201000000c55804001e0550071482410301c4508642c10200480e50443c107903082c20b030509817244082d0543c0c00466000511041000d01540d9441860400d0740d4040d11440d000c3c58036070301c01c500000902e0010000d11a058804c0c0404034102204118070614040303401e045807601555a4420000008114101051110714140800705180c0340c0003081101d02c043c1603019448902d4104031440301c2c1644000b0076000450300120300421500d98040070340040100040040c1514103031038446030110159140390388a14001e9a041c045503407200c0701200c00700358034801c403140068004000c0c030041d80244003400700100c1a604642c02a40c102d40040e0030344205441104000c01e00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 363400602 1250 363399352 363399389
    0x307110c03030412020405040c030615050a09020a1b1a0f1906050105030a0221090105040b0a020424111015060311040501080606070f06050f340504090204 68
    0x388001952448101c000c0d600301490300300c1c8880070710448407009115555550006040029003d0841c0240d500501c6c1007040668000d5007071004000e50041c03900c1400c100d5000501c40006000b210000340e001d5403545402c2c0744000507a807080c0241181160150700d00800250000c0415a44c03520034000d000c40d42c1c0c01d908041c0d030344da40d124110f03c00715001c8500702501800780b80d0f0010222600b0107801c20006035100800980d682d080341910541001c038191030024000326000c1500b00d10300490048001c440b090300c4d040c05507800c03403095100300c50b00c15070001442c88003422100031224001e440c908000d01540d5543c014181410404487c0051850b40d4010b11048550380064540142043e0b080400c07005a030704c902c15605d4021171045904008890000501c592502c0f000d8070b24242c6d200410079241c143da880d0550281c0303811180000d18640b00c00000342d658641d84007096411101404400b0510071001000b1b8403030014403010010f011007007100150000862008000502d1203452400b84d2200b03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 363401852 1250 363400602 363400637
    0x50103020a060206070c080c0c040f0603050c060c0c150712090e060a1818080403030c0b060906010c150e0706020c150f040b090a09021b01050a020f07260307 69
    0x14541c200b003045511010801044c1a00900c10400d0a0b8100c0645078550026454292030141c40c500c8054125090400408242c411900010305aa100301c00380c3c1c9070b1020840074080c4a0050148000a5511140702c046460400e0210b02000b90010b1080ba85024019180c0c1c1c2ea0780300d1303030380d10220004201c00390806c121030031007450b6900208121410812176281203115500098072075980789030182d55200c000c180f1040d108440c1c00c0203502c0140c064440e5664240909400c4450b03a040d50501c10b60305c0050007034030780508581d00ca290140c641c400011801d40701d164000d04010036070314000d596055000000081009103000421480c1d000384a0b00c0200f209200240d511001480140031052080e599045c2d210002c1d241a54108030805840320414000078640c00d04903406112032901c00182219140304200850f8814807031a4002c2c0078949406e40c00034102e1244624401c0c41c40d00c140203210000d0f410312a019904c09500c3e8040c603191101c0c55045c040d030761050f503000c0013061501c65054010003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 363403102 1250 363401852 363401869
    0x504050f0d05090d0b0c070606080d090f05100503130b0108100b060901090e0a09080f0a0f0c0503090d05010b1507050712051e1011041d0103020d0807080f0c0105010302 74
    0x8550b854600d0406100d034020441c1c1c0c0790a020003e000d40c410701d001800c11300405007540c1400b0b4000e0010300c070b030307954511070036490f4038030b8203021000101c610346c02040d02c0150320546801c03a00c0285c150751020940b040c084550f9040580000e00d0945c2d850210300110b800d000e103c2d40030305a280060869881804445001c8030030174519140140030900410311680c0e045080201100c02d41440c0d010302c4e42d5040d0840004041074103000b04005070100750020804c82c510043c046449907a21880e0104032048402d0743c012150583c0206542d00030007140c00781b0b080070201501c0c0c0038480c0f000440c0c07a111090000c0d8000f00001007c5241c90307008640ca0090087c1040b8820082c5403071000b103142d002041c1c6406441c0d16100b0500d468441c0c140170801d541c00000c00c041c41512501c000d080041c01c20203030a080d565400b520030268021286c1411250f9801d800013120704030ba07030040011100b01d00c1a03940064070b030490f000036140011706101c40403e04820a0051804041d454000a402d604600c100000c20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 363404352 1250 363403102 363403123
    0x603060609080a0b090a050109060b0a052202210a0c0905060f0406050f0c1b0901080102122d0109021905030f04110f031204091d0d0c030507060504050f 67
    0x1801c410005000b02045520344142c00000003403207030350343c0120245070682013000202551310301440c003420304c4050780c8844007212040321105040c580d104100280900b012254015296242c1d1029910011035030007801502c0300e0601f0520000501b566180c00c0d080212604140c16031140e000341c01495011034030f8005428100c40c26400c200c40381790049061f01590046001303110700090000142c0d461031065981404c0c0722421220900c10240c0158002c4003803120140c0030342010310002c02c0d842010f00a544c9142e04c80e41c0c0c4150260788000196098820301c44825440300454440185a45c109004c258040c2100440250b5501d03041d4890485125204640d41c0801c0024030510406c4988814100e40094201030440b111a0b210300003e0281c0c03030400e501c1a03141c03150031401d10301d020030030000d001254a1043c1c10810407a010b11000202800140d001c0000e8003d9051491483c0c0034071044001140a8a445400c21466903208800c4480a92b403d4070640d22030342d51180c15010408c0700c108070307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 363405602 1250 363404352 363404357
    0x204090506030709090c230d0f0203010507081501080c0c0d09080c060403030801050105071506091a030d0c02011808030703050909060a0501050f0a02010f150f0e010320010c06060b0406030606 84
    0x1011043e80340c1c0410005d403030081d1000c100c24266590301d05640c0a9802000107c010014440500700d490703c100c02c031004042c100c0c041d5090030001000c007405035514034031400c4101c2d01806070402d401c00440700540000d142040a43c0240310710fa200f6481000408006602c9442c1c0c0e405441c100389009260a01d05035001c1d1042c1e20410050002a50021410381141c00a080035600c8095602c3c00040c3e11041544500c0301070b1402030005007040081c1c015010501d0303070301c005031300c070f06900c10a00d44c842240c11818004668500500c00045d4800d90501e0760324000840da1185440d02e0b40783c01400c5920101c42a40082c001003030060140c1340403459981c111a00f21440c84400e86840d0019095000700c0010310540c0c9004180440881d00070b40000d0404140020100491112800581c014190390300030382110100c0c480c0080748060545549a040c1e0b900714035030002e4104403191203507007a90b00c06ca815042000e9050580c0c0010314038015400039110000b400d5840700c1c1464030007400c940c05503011108 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 363406852 1250 363405602 363405611
    0xd060e18030d0f0f0906060519030b0601080c0705010c180603020309070b0a03140f0a060b071a060111150f0907030206070b28020301030b061002060f04030e040204090506030709 78
    0x94100001290700402e660391020076240410f2a0701c1c80148403030760007002114140039005d0100603940d40480141d4400700c60846a440015030442015841c500008080207400800301d401c40d80a40510b6a2200003840b40ba4a8030146585803400c0d501122528404910300300d8640419090a10802c009003e03585000c5080d841c12407082691760071548103080c401e41c000560030030114840d4002509424854604030500d041070042010801e10031501c00d50458580a00810360301c009008940c0b4644d0010740301c8261510640070300c19464005400c5a06010701129042e6803803d043c42501031076020b0305440241440c2c0b400c110014210010210001030304201000d0005030351304000d072540c642d00b240c100115591000403001215484450b00600025058594004800c00760010744c142d034418109070200e43c88040c02d0007030307010301c409401001d60003001c0010041208905c40991040c0685480c0340030100541c0418201c0c3c3c800c3c0c20180d4500e44070401c020142c2000c1000070024107100c101000b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 363408102 1250 363406852 363406891
    0x6050304050c0f0d0f03110f030c010e030a14090a09060602100b190b31170a02063009070f14060a084f08160302010905030d060e 57
    0x43c80c104c010a00200701c551000c0101d0141841110904640522141106c46403c054844550b0301d422440c502100ca40c20007110a04032007000c0199940001c032038944500d1503240d8100d608864210300b950980166500000003200c881501401006100383d80241107608c089a90940c00d8170101120340d40107032500c0a01d0b03050360360884401c008844000000548407072407941d00660307114004400072803e40c00c070791101c000004118411811124810801650040303070800c0d00c1e45810102038040e50240041c0403200010b01a01c01190015103200204660004412254600c001d0240c842d0521684158001d02145c1c0c520340c50000540b02403202c10030300c1c103060000201d451052403042d1040195480218100004158084041d03503400b20104010180312114000301403c400045e01e912100307100c01010082c2c0f00c5e41700e294800c1d0004600340ca4141c0e010030b01e6801c034040c06412170442d035031121000c0100b04d007800a000b00c02d50101c0b0200ba20f900c4c000041c00915806405820810070988806 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 363409352 1250 363408102 363408109
    0xe070801090302030a080a020f030a060501170601091512090309080f0c10110309040603030801080d02070b0702010c0507080a120f030506030a0809060d0518010507050f0904050c0d1508160305060109091b06050304050c0f 96
    0x4e81113c9119003070b030a00b0280c410b022504002d2150681180c41d05203c408401c0540102102c030941e1640001c4618072000c1202d07441d80c4820301541c00e500024500c5080d00f106200c1d092422443d81000304481c0380481080101e4119042d0f0b61041c1c00241400005000700300007030003621a00000c0e44001c2031510b0514035a14003510810b40300905000b40c0c01040030400c903050214a00030501c0100365501c00105003811414801c800715a0f40003d41150700105030103010348580381c00780ca000f5004154070036865507880c040c1d501c070380030b210b03405803003440140d080402900809106201494600e850001d42c1985542521000303003001e01841000c1c41020151031410b01541e4003401e0032100400c007511040e410030340320311810001302d0195007090880e46116400aa081040b50444001c5a41c02506200e1610124416000040c4580c00038030041150400d40d400003800d20340035404604544000c03269400d0911050781c48480801c5000c0300708003c0c460b0a001403003101e0001d45640380c0c120f0044000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 363410602 1250 363409352 363409367
    0x1011040b0d09060b0a080a0c240804061b0e0406050103110f0d0f1b0f0206061311040528120f0803130203100e070801090302030a080a020f030a060501170601 69
    0x6074401070b40d52075100007030068a8000300c8008001400c1c1244507500d134050300b5203072288441e0503684058040000a007902075030300b07002a040021038021850802924045403020406072069a03070076180c1031103c4d6600410026200e000c60541c4901c85c488200c1810300050f98226804503050501e00f10b101c1c841d0300700210842d002c0c01030140f83d4641c1e403403014003403000030140055035420081c03800c0601c4007a40c110600d0036a805121b070311030285542e458034003282d88032401c46d80c1503049047c000034421130510070382011201c0040300350107070305154907100814040b441b00580701c031807004c003100b20348000f0040f0722480c001b0301105d419403500c4910b142c8811440070b4400340020300806c0300000064a5045007140c00807090380c0102600d000c03842120035100034007a0310f2201802ca0103a41e50006100c0c01c1403003040c2d41c403503058010310700b400c00229041d107617418000d02e4405447d408011130811102818000c42c481c003d100c030001003c9040600061964a070400d0304c003582c800d40030500400380e030003210 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 363411852 1250 363410602 363410617
    0x71e060903230303040311060f1501030911150a090603060f03030e04150312021e0c1c050d020102031504020702150a0c0501020f03070f09030b0402010e0607050f1011040b 75
    0x110782c030307420724000794840b40500c01c8030014090380000701c00d0104042d4040343e01100c05001c4402c031425030729101180380d1084401d032026001c88992242c03950396940282c20100715a8060341c1e00c86150324210001c00d42d4100b4544c44425041800503000c0801a042007503100649403610b010425a4140382c0d2100c0c1e80e101a00000e824880704110180c640c0da643d400401d1a0400030b170031000c0b12903a900e0300002c03421100c100c42015005420307030320420301801a4031240250000d0001e0441103c244280300c40c0290122a084158030300342001c2021882c200b040c000000711640c00144c1d44e240c48000301001e9003641745017a1140740100940304c0941c0d1000c4c1f00d070b061489014181c81d42d420b11140c081d10011240f4000405550000c02e00502c03123102c2d400a58810f03c00d42d00c86c1b034680c10700410120340725002404010406030004002c940903500c0b400c16928403180190040d4a4200251281c900c0c040f00c1d081900c6840d80040e41004100f019409998a00c03d018442c9a080c00d06000c1a0703113843c00b5000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 363413102 1250 363411852 363411863
    0x90609060c081608100b0705010e0111091e0312031e0f0105010f030c031803091e18020702010c0614071202031005060c070e041a090c09070302031003060509071e060903 74
    0x41920310707417a00c044000804010441c650350b10781602d803c0340a000265013880455103231668820450503c401280c032101d400520300700e074820001710307d00c50071001282015014800d21020075a1600d1910085020f0000c00c10140307460011021034003036850b4000d0000344c0b007550480041015176003108070303d4080261410007140503d400a4218020140c40348880030035001da1501c02c06168007c1c007541c050b00c014115580e450450031010001020340c42c49942804070320213a07650030b03080d03203640a030010307910500d00105200100d80300d0200303440032441e0300301c410719280c428407010320342140d100c0c884510803038415410340c9480388105807011828407905006805c0004c02c81c200207001d0129030084e00030040403000f6418181800c10a148000c40c0000070441c3c43c01c0440c81c090400140562003643c01024035000c2e80c0c0d130340c01c03c4019400150003490803494900001c0700043e03450040c0c910549241d002040080c2c503003500890003070401c10600d4582080008203100c45607000740510f0540340c000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 363414352 1250 363413102 363413117
    0x801090b0609090c0303210108191520180108071b0309030803070305010806070201020c07030210030212090c190807170a0c08010504060b100c0321090609060c0816 72
    0x40341c1c03d81405401d6a480d035050100082c62002e84082148440c0c442c802d5050304607407aa00c8030840c2d42d0f10701e000c0c004c200340d04402190240c005030310750300608845045903101140e500311a448801d00d600072803500019004010071000c0204105841840c42030909207082015030501400180054016a204080c49010410031300103050003041c03800002d6a01039451a0b076807501030b80c014010031082c05000310501407040801ca00c18414002d49040c807035078101808115245900304100c0c4001c0d0842c54042c103400f400503c030660404907000f40701d903000c8005411540c0007a01003005031868420b00031440240c16800303000300c0303100050210a81c1c41401003840d6611161000318a0440d50070001840d0b180328071404600410306420603030046101c0d41c0d041c00301900100030001340400300400c60001402c003041000109124549004140380c080400304a103084022020b419200b400d4000d440803522005824200445440b518286a010345011049824810300392050142195861000c21459 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 363415602 1250 363414352 363414361
    0x3090a03080f1209160f0332030d0609150b1e270a0b1810030e0307110a08060705041a090418050d030b031f0213120605010801090b0609 60
    0x40b0100c0740034045161184140f49041d45546030b56070360b130802101c2c40c420750b404006042130b03c925411059a601568082602940c00e224903034000c0800482c0c03843c6450681d002003801c00500042c90f034407820200110340f040c1041044c03425100500540c055042040078100301240380607007580c504000900d2002e05500c0b00d50780c003503003d004207008200c440201040c02a804031100140710b0310100191642c4003015500c00e82d41c202405015407880a00000d8600795000d4035085121520148090500082190380484d400e803031074126403001c40b00c4240300400410720386402114a80281282c038002c20b218940004010018016031103504c000c1110400814003071002401628010800640308110f07100745070001080c01041004150f03200d0040700c5980002d940320707015402e06100301600422038170401c03200202c1d000c50a10424800158284240b032840f600a02c0000d00a01d001307100600e4030210307410304c82c046400680c00300c8002d82c0340040303117000168103010b125802082196601e800b980d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 363416852 1250 363415602 363415627
    0x8060a050405062b0606060305100e06030f010e030c010b0a061b0f170d0e0d09120602070507120c080106030f061a03120c0f12030c1c0501060e01080903090a0308 71
    0x24408608240c14002040255038613000100c04100343d000e28400d00000e96151030590482e0816104441c40c4140000c0c144031100b80406042e810503400f41c101ca510007000c826031401c46090b0b039900e51003034000064404000b07000f4003441076000c00490701d00c9078403407802d03e000e0094015642c4240031042201c0300c0c2800d00403007450014100c1e400c00008413610f0750108180c5035a40c49140c03107000d1075252800000a0900c00280a82e040200c3d403650f01c0f0300303070415800114450b6a088201c079055000c000802c0061003c0c8040c600900055800c0f244012080c5070a2075801640d41010310b840e8034000007040480e81d1000c114191903007009000410000c0030b21030700c0b01203441e00e02d03c0307406202e00c550641480304a00000c003e4404072106480320700c4d04a1030615228102041d4040c100d180038008640446400d03401080b00211102d030886c01c0d6500002c000701960b009078001d10108544144009117560003046040e1300540c084069882e01102c1d000085158a071800007410108021500305500c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 363418102 1250 363416852 363416869
    0x90c1710152d1e08060a0603140402010e0409020604080601050114270f03010e2a30150a050f0c030a0b0301020903010f09060b060406020d081015020105070306050108060a05040506 79
    0x102d031010f4146107010307455015191201c11354443d4001c0c22a441c0c009210b51081c412418000d17200142080c05490701e0300115009c0041a070f035140e11980e00c1e0011001641d9003c028002081e640005d030105601d044005008641e140c071030160b041808100750f8902c0d84445d480318080040002703d03024011441c402040100c00745120707a40d015031034985c0109000000184200711005201941c4284000c40c1000c241a2112140c00a4000d852808103911080e1544d620349108003580e11030940c003040814105143c180e100700d0004102e20369900344940980140034041d40104903103001095420b003240c559109200061500d4441c83c0d580c505226107079402c0d01190783c2190020028031081c03042c400c5003402020150012036101d403501c0300b0b4010608207041501d046a2040e000340025410406c42030b1000c06000345064100080900003040d140c1d580e1a122107403000d01c3d800024039141000e0041c0442c1c0340b541240c1e0500c0940010401c0035500e030b542d1a81074450544000c01c6540b592004101d684 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 363419352 1250 363418102 363418127
    0x2060103170d02030103060b0901140109050108060402190c0b070c030804140703200f04060e010506073f030603080301170f03071227090c1710152d 65
    0x50300004c000014001150481514000100ca076601c480e45e840303c500001600040c0e826000c6a4030004c20402c035030040c0000350740b1071400741c0090301e450880308198520034040710840002c00d40900b114014098000003ea074050343c2030800c0c2c00c000c41d176602d003d08611002040142511802c11490480c03c000384441002140c1c001280e4a541c0d445113101d01c005111800111701400600703500c9040d924040c010740089138910000c0d41c035280d0030030b403d000701540018410b4680410306080c0d0800c16a903451040e007820034142c2414000c4164072400c030415094041381a040608202003440070036201c1e02264116680c12010140345e003603141c0c44a040900303881044205020100c1e05009010400030004a044245d965440049000101d03a00011404280b9680c01c492280340900196005602031181c070110742c00c021224002403490004208001c17a0240c94120104000300450860881185003809a0341481d03116207980901c60950441074110030418040d4440b002c912803405140c054010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 363420602 1250 363419352 363419377
    0x90a030b0c12010602060118021305090c070c03030e0f09060f1003060e1006140a0c061e150e280f0b0a030c0303020d030c050a08063613030206010317 66
    0x140c2d03031354010194496000b440381d800002e80718408500115150702c2102d00030320024505106481c10a420710042c900014648810321030100005c1c1c011581c03000e901c40040d8030954950840801601c180720b8541c0c1400036481c0186080d4050010990700d615403110194819903004d0401030000c43c04070090103c5d54044001c90120707400f4010000b9001d2042400e07101c46448843e003000f08100801c070b9038031580c40400000b420303a6824800040d440c0d001064003010400c5031400d080c004103071170b034212804806060345c1c10384000d808101108035043c2c030700d0f8010340c02d4400764802c401c18003801d61080c11032402d50307481c02e6880c4010034401d02c00d98000121800e001c5d00119a058407407401e9080c240c0355000a41c007501c03e2646030404140300e0b015200b001d44160b640c25051000340710702602c0110010380a5035102007500074a49103000e00c40218901010011044050f058004550341103952002e003003c000e1960000e9004040784d00081c3c070504607a4040b1405020f041c640180d4242801812410b850 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 363421852 1250 363420602 363420637
    0x911040608030315060309061b0d020f07020307080f0309091801051306150f0513060b03070507062318031e030105030c0a0e07030e0a020303070515010b090a030b0c 72
    0x7101100000a140b0590340304a6010403218803004100541c0000c9410044a605c83c0002030000441403d00401d148401e100302400e21170a03032410340036600715610510f8a8100400c000d820f5250800c09000141511000703061801a80c6003019140e10071203801c01c0c000c07010000423803808450300c000c02d001c1c4510900200501c0c188003000c04142c00041100b950698207144140c208001d03411904411a140903400741c0c2030f203190606015036880f03e0314070049101d680e0b54001810180420042d44034190581d0f07111365a4080749007240c100c034104501d440038917103e0540803c1c180b101c200c440c2d421035055010090a54941c1c0803442c41c501c15440401151b01008042c559104920400345068600031030a0741e05c00d0076203109101654139180720b040d8039001341002040c5868040d41c0f00c2c01d400c0c0c00070780954003200350640110349554800d00040760158462042c1c1d00c003070b1034811091070240c10b8585070f681c0752a00902c00586108200e00000d00b0140001c00840e03181c6403460202d80e0780301c0d21403d0610 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 363423102 1250 363421852 363421859
    0x515010311030a021b07060503040b15090103141005010e060a061701170325140c030a0b090a0c12120f140a0c0212070509180a0b100e010803180a03031209110406 71
    0xc8c8075400c240c07800c440e0360f20103074041182e0480c0c0c0000b806d603054014141c0c0d821680b858076a011084072a921200c1c90380034103000043e962600c1e000380c902901544450320340c0350800400340310b40c02d00160301900800c183c907000e05952084010340c103070440720301c9400c500360b44905060560440c803c900c01c1040458001c1e60744000045079041c0741200328080d4134030382c03100c01b02052400e07110088151600c1d419004041c0c1e0100040011515a8000410b60215540c0d603030070f43d603611034054164000c4030128508a4651082141401c1c800703601c180245400019100328002c0035028480368503900f04011404112180e41c1403290050300300054000344040701c14440300c01c050703864a400c0c1c06000c1c09030f000307000000c0215010003000001d14001c00002c00740d00e1150348803c00c4084020303050940d980300c20300b40011811403003040c05000e4460040510394540c2c2c440400da180003941140c55009480f090410404290405080c0100310a00c00d40803070000d055103810710a07203154082107070b80180344c81d0010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 363424352 1250 363423102 363423107
    0xf14070f060915052a031306030504060c02010905030712050f160b060a050a050607060f0509070f082a010e060c0c1518060a0201090c090515010311030a021b0706 71
    0x40040b00d405158603203070755043c03940859507032162038190007810010708080359490500f0711000001a00141c1601d051054040f1040f12440c000d511240002c0c0d03e030410321040c813500d4070466070403003600c1c00204000126651200d80f030303000e00000074046841c1900b01c0e2103818001d50850b0110780407425030942e070b10000390b50152106800c0314140c0f41650024002911410001c00c240241c0b50000e040503812843c010801625030f02a000032201c0725122480301707040704098021103000f052840041c1003004d09050107503540d0304840d40102c84540c01100940c4050b1082c1000f080003650780e40901e05e00011020043c1d0384135040355221504108002402150704030082158003001c14102d40c401c40f00130344005003410764007075070b0920b82c11140b10100880403440c001000344000c40c2d850002040c24640d40c1c8400461500c5944080b040c0740e100c00801c541010006c1180c94400c0090a0404c04401c5846500d0450b020050500b202964000f5202e003200e03075914000409000c01c00220f58805440e003d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 363425602 1250 363424352 363424367
    0x7020c030a0f14010e030d02220e09100204140105030403170405240421090308030a020304060b01020d0207090b010903020910060801120f0326040302060f070201090f14070f06 77
    0x152403078142c1c007100b000c010303006020300e0344c0300421040111f05001029582034020351000f022030b02842c03414003400303c2d1030640012100007011981405511441c1215140e400d10020782e00d514491481044144604042c66044681c0381034280380c003d4403580e4034a01628100c0104299410f56043c2c40b08101c1001700c0041c52141c2d10081245503000d241d600081c6034000482a074008050780d2800c112040544100f00081141c1010ba11300700c1e003403503038030744801086078815030b660800a07070004100414840c0717500801054032001c2c4001c011040c0405d00080d2204580d0180344c0c1e01d40d80b90f07080e07440d090b80b01792044001f850700100344103540d091900c181c2d121058140b0884020852007000010843c110341c59601d110b941009501700e402340c403940d0440f81c1707004c4c8418411000c0410140200420098048030748264403036001404076060114105444020040c07103141107a04010309000000c00707030544c5c8051141e00400140ca08280c0070101802e110690700300040c0a0302c1c00000140c40b541c84100c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 363426852 1250 363425602 363425633
    0x15030703020d27051c0203040504151205070920070609050c06120a0b010207050117071e0c0b063c03062509031a04060b10050a090f0e06060307020c030a 67
    0x116201403540f415002001031071714510401580050004002a0500e90449000510400b107140230b40d980321503140d1411814010144d9450f40401d106020307240b0180700c0c0d04d92401c001d03602c40108690b2400102d07517510030544014140d5481e04040c0c000c0280400c4548080c4030010005501d51002084000400c8000c40d242d400c02424101c5030119540042164015242c06079104d04044c41c0450580c0c1e01da201c0039101c2c070100204070210f1580c1051405000082d82e92030b9840c00c0da07010050a00c4846038401900303480c0300d03403030311b44400309011194400b4800709a9420313440c030803c000f44c2c03003100b4031070080c5183d040c2c040c015082082140b8200c90036040c1c20800c03078503515241341506441116001f0f00d23030000820082c0280c02d4070101500e00b14131507911611441004c204161071002040006400c0c24580f008500003140d9002043e4000e2000d0015112880000a2403407512000071018000540f406015030000400f0404040c800e00c0411031002c1c0c05030880d03204900f107281c2604040c80ca600c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 363428102 1250 363426852 363426863
    0x2040603120c050c0621040c05060a03020a03050f0108190602041701050415020304020303030103020108041401090303060906091506050a12091110020a020a061101021c0c090515030703020d27 84
    0x2c01d0251a4a0b1245c10384903c071040420f0601035010041486140f020301501c01d440e8040ca030b03480081c040d56864010043d000e2903a401685801c0c283c0d80c06410390320301602c10081401d510b4014000c071040020160806500082c05a102405038113040000f4803854010568a40d4442c07921034500e0310541107140610301c0380850341c4803c40d89207108030407404280c4000b075040e0000c00040015610806d1802d400038080c0400101898051551908541c9050009c40101b41c440c80100140c0c00f0350303c200d600400050509002d0012020387d04018249240200c0040c03103808903110843d20b204d0540c0038468600740108110180c8a0704010f8814103500c0c4000348a00c043c2002c2c001540d10200e41c260500394060301e60340e406810400d06582c0700300d5954007520199802c0c00a094943c059444011112030241000500c410314103800400c92021a0400b03801403540801c2071140d80410800c9a601c00000c0ca00141c1f10000035042101500590002154010001500041c011035117440880e840e0320a1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 363429352 1250 363428102 363428113
    0x1506220f1d010b0301030b07170f04290a020315031902040b011706130b03010c080103050709050115080a0228080f101e091113080303010f090902040603120c05 70
    0x20380d118441e25000d000b030100e0342909000410001c0d40001c24140c1200c42428110440091000410b0303101500300e60003280352050f0740a1000348451959003021060204210900058101c1c201d840030b204058002c10001c4e900100007109164000c5403510010b4008083e10b0f04400100700b10007070f1160039282644142c0c940f9140c41541e60103864200c801c001c603646000460790320602040643d01440c0343d214480ea807664400c500d240e0f0280b150000816154079a000d4035415420198038103035042e04260502440c3c0001408030810412012010390070615021000d03039a9507204c14040e000765400100350309840303814404400d0f07004c541002440d0072581c4251507555024022103c40d0300559a102c088107240300240400000d0146010749800c0d020b4100c0c203c55070b500c504800b2985080f090401c50900807400b11321091012100100610110300258203650400480341035004007407050600c1310382d0701c109a00840d155900400011a00140c81e145582d1407e103020348044003580b0120f5090094 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 363430602 1250 363429352 363429389
    0x60f0e041d031e04030c060813021c0b090f1504050307170406020105060d020a09110405060301090e160312050c15010816060305040803040b0c270a05091506220f 71
    0x11031041d1821a03400c9101b815105190042c00d1304c00c1c0c02d01030300d10850002e5058001000d0703140c500c10300005000701004801c1d60b0405007043d0b02d00c1680640b44e000590015100400022000900702c00c12180001c400e02ca152100c0c60920319620801c80002c183ca01051002242c10301c0110181080b50b17815002880241e9580081107101c00f901070000f580031070b01402c00d01c040d0050794000840005000d4145140030348400016003a50000d80c00600303050b440b1009102c19600c10b100c2e0312404054040400905411507890f03a08041c2c041810900304030020448801d40a020410103a100b00001e003c0d00055849600050329030368011003d90130980c0b117450004283d4440d1061510481c8c01180030307400d6444940e2070240900d030260080c1d1480106109a84459584121541171800c0c8140ba440003210700c02d0500810f0001a84510710800c0e820041085001e40c44020403420001103840554a00c10340041c0101e60301d616010020200740c000c0b01003005801080e8120035640100ca01c54811590b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 363431852 1250 363430602 363430657
    0xc080403081e070e04112d03090a060513020622060203040614031807090506040b370f0b070506090c1c0302100216020a0b04060f0e041d03 61
    0x41410344050b4200b44600059800b44554440c4107014002840070414488508402090b41c000b0300c55030300c0007484600300c801d50107091280341401c01c0b01750701c00a00f5031030300001254803042d000c040688403589480c002400c01180d049030f030302d85a5000b841c494a80300315000420800441c0175188040da048400c0c0411124000000c4d05c0071219140e40e6141c42d26001200b0300e03500c0d000980002241000c10003402155001070080c0005040d048100040c3ea02d004000c1009030340d1440529405151442000fa0b41c4e04404404078407101e10744e00120040d442c1700c00d6448480d484580c080401100700e94070208410941c200141003980c0a081112000d445001d12582c0b80d203101203114ac0d002c0510700a4000d01e03008801c050703440038028010b440c58007032030000c0030051f81e004a45462012400c99205805c5103010400c0b00051b000c0fa500d2a400c00341001b001a00e00c120b806d00b09404d103c0c51054458861360340d038000410080d5403142041c003203103100c90300580ea6003200707201c40b1020484503506901c7c0311 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 363433102 1250 363431852 363431881
    0x4021c1a0a030f1509080316030c0512130501050705090f06090a0509180d0504150201050417070816032001180201120b040912140324030304090c08040308 68
    0x10010824000203185650f4994032030503580003180c03c04c1c0c600c5226181d66006100b0740c90b05030700038164140c0c1e905e40036680d50500c811080016040c903280a42016003542d101058545004290111900c0f54a4012440e0304c1d10130741c040010702035030810040005496003c03014040c40310065031480341904510082042500540800b643c002504450400803483c20f09249900200981c0d141004071503d1090035080c0502400d1000110310b00140c104070080c2503403008406030a0b90700c000c0002c0e0071b003595110301e207121a40d410030005102140701c005101601c81200c4d400841c4001c0b685010342e0703a20340506040104411010744104c0c040d04071840c040180542500780c1b4242015200c464015070040d60110142440031b204655034210480840c1c44a106102c10240900c0c4403020003840008020a206500c801c15041c040c0280240144000243c90b00d10041406080700316102c01c0c00004280b0754081c81d8082400076084c41c003000050745c0c1110f001030140d0302954078007010759034140c003109044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 363434352 1250 363433102 363433151
    0xe0a050603040521070503070c140414070f090503010e0d03050609090c011404050405040f12050a0c141c09050406091119021c080118050c0d02030a020904021c 70
    0x341c01c01300d06116041410000304507200d0403c0400d40c00c2003d0b81e02c615186402c4602d0031140988944018407492595078010120110304035001d000c0061144408088907030080c12780400d01146040c0b00b1100e90041804d6070180c20042d0003007110b506840b100a50742c507110300c001e1010134a403a011410720305140110a10070b40c0e1200003030460404801c011140c80121032400d030351140d01400041a07503039a901a4900807070107402000030100190816540e4903006008213000e0100410032281c800e070b04000509401c9030804040b100c8060324800d182d090811801190380300300c01b40c404d014011500903034040151901580d0401c48107450703003103110444005682c00081d044c01031142051082d1511246040c1d040a072040d40c1c90a000b10f105400c01c0d8503c4000017012550200040c8601c031400490f8080d4203501403402d009509241002a40a10403499041d9260341c00000150300740c0341d6901164000340014000b155550351040208503407091042000107044c1c00c0c021703a0011000c1c602440700c0c1c5c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 363435602 1250 363434352 363434363
    0x504020909040807060b060415030c020115030b1306050c03040c08030f03011202040f0606030b28030f060605090a091a0708011202030109020907050a02160b1206060d0c0e0a05060304 80
    0x8a490b079888402d000d8000003000c480c480c0d21469070020b0f40c1c4a21000d400185044205460401d106003c0901542e100c50188021689401142400002d078000b401c0104e91700300d4a64082c83e15000c0f12080600050701e0302078605800c220a00c80e0910b20b007030055101d1401544254070486d1a892401d4480c0709400316201184800c1c0b0051110b00090380e043c0303102078801000003400898100c038160030750381240c3c8068080307995920f01400c281400c00b49881c0c03280403000390681190f525600f449000845000207014440711056490270041300d0390001c406440020610000c03840c002102002030112024200c400100c4880790400c4a00f036802220f001e80b405440c1c46015a007004d58006821216107010390341903407109010005601c1d15070446014600c5c2c0d07500c0c280e135103000541c040e1800840d130b081c96920106a20040040c001d5100a03140c4407501903090384419200c02c2e0008003603028a030384415803035141401189060781c00040c0d80d14074800680d0b6204c0e11a40c1c0321304111540c00101c801416 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 363436852 1250 363435602 363435619
    0x9070f0b0912010e0109052d060103080313140303070f08092a060f1b0f0a0b071103220506040f0b0708041e0612050403020a0201110708010207110a05040209 69
    0x1245030000d00c406041c0409000080c0f0700004c4402e0a0942e00310351800e0f1802e400c101310780d020b0034881c06888482e00c240208668040055252099902d140511019080710b42c00f00110707400300c4c0d461280300413983c1c00c903031000d41c81c00222603540e460303030300645401c40031640e02c1c240e0038805409219aa4442c0f141500940321098aa5007003800d0410600340100c12001c1c44002d40480d6a04e10010741112440100401d4648940040d22403800c01040c440190940c0700e0629001140c01c00031f80f44480c2a40121551196220302c0c070b081d11100f240e123000880a01001c10311260070718010b42c05580103501c00d4074030900740d03588070207110040c4500d01030300b283d01d008504140f05030724070070f4000c00b15948992907480ca01a581c0e01c00c03d03005041640211800740c09500c0400039a988408003a20307000381c0501c02c021034103007660007a51318600c03842e0007418401c05040102c020b0030144030080052419100175903030382000e072a00f0071100d00c2d8060700c0f51040020b05000b01c0d20741403501c01e40d801030401500c0380a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 363438102 1250 363436852 363436867
    0x101e06081003210201020c070e1e090a060f090209070507060506090114190f03031808030a17090a0605090c03150f18010f090303020d05060d2105070807030809070f0b 73
    0x1005061041480c001390364082000066070807003007050300004c101800c038903006410205503288110081181c108442c074005401e2000d4070700042000d5420940c02540050300c84151607a030790240c0303e82071000c0d600c07002c6882044425a0094001c1c5840d41c4203440420865a4100400842010038002c40c05010b41e80c0049800c1030802403e000d405c5030301c41502c400341c07699071b54140d2041042500210000b45140700c522000e00070183c104c901509044024605100075450003d1556071041e50a50030b5003280004a407042000380142074140f42c003c08180220710302015160340d10a01000d119010f0b100d1422410507481c1c00c181e005020702581c0382941820f4030344d024032205a0840e40089641556a81551025040c1c188500c5421070702c2030b00c000d6180c00c1c1d5030710315038100c0f280103083c603010f43d00340401c2c000080c8410220188001001d4904084016500342c2122540074595004107803603030005025082c1038009040c03030b00caa1111001c07a842143c940158041000803480761608080381405201c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 363439352 1250 363438102 363438143
    0xd050f090c010f03140c070201080108030c060c0a0302070506010603150602011a0409170307020109150203090a031404030f0c0801060501110601091d1f0b01050f090603101e06081003 80
    0xf821048030340c6130120b5421040c815501e203c81c3c2c2900c0170344045000160708011940c00c46016401800d00402440c14620183c1c0215207580300100039203001a800505151002e00035412b44001c180c00904407000c2d580c48850240003403604400050030315880d013100140982c814006c0c000c500e60040c11400c00910180140809400d000c02c1c11a02c0754030001c006620001000d001c1c41c8114050b90000c10300350058100741c01c80c1c10102e0180d0a80380d0041040203908080046d445c070040d076243c44c1c00042003c2c14002c03040c030f41c01260401850a110072a9a0040c44042d41402095622000003000358550343d070015542420050602401a001a00100003010507580f02d03400c0c2d00c140b011102c8100c2402d0345c203241442c3c03202c440381814110b91a40f0030080d031092f10580307039484420700f130030f92401490146401040c003c4143e1648070301e20000001c0c021806c0f0b01d40c80d000802d100c08101c03640d101118021241d0f2070050040340002042c5000042521103110710b65800c0fa904090a020f40c603000c003000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 363440602 1250 363439352 363439367
    0x120e0a0f0837050d08060d030e0907050d090c0e0a180803060303070611030901060605030603121b030c030c15010f03200915151201060c0f0206030c0d050f090c01 71
    0x92015095260390140c9082c000403000b07440c0c1071080d00038089009001c14060002c00015080038050710310440104002a000030204013501c6086030305d00e035a60b9503420100c4447c4146000c0500c41818801007000704141c8501c1c0f10156502020200302c9591000041c0c800c071030700400740791400b940d41300d000404211524000d642141018043c1e074a01040341d21b40a066443c410124010501c0000404c026840c0078402c40016120904d425440d50a1038800240d5a071526118516490300c00a41f00c062100401114003640c010941603a494851080b9440d4803a0003c0102c8070407070080100002142142c060050f069034003010103c0036445c103603200c90306003801c292001020f40100e541d5100c00c95031840d001c1481000c2d0032180a41c402461014001c2c3d1000c0150211b83c004d00922080010004801c081ca042d2000e6180c20302140959052940700c0c8034030304078041c3d0055000004e20192580403030090100c0c9650b1034040c051600c0c0c01140030000a01100d0880030703908200b804441a6100c1d00c0b6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 363441852 1250 363440602 363440653
    0x2011101062601050a20090a15020a0c0f05010c1101121514061819150528020705060a11060109020d0e061e13120e0a0f08 54
    0x1c40d603488115a0b4920301190300900c00001d8050000800084240540c540c0b14400b254144000303018903141407480c55160b003a680d40e00501081e18820364a60101c030b50000c1125018506a0703244d02c01c0f010707440e04c144100c19510908041000700711140404808000c468046c4c0d5001c400d402c943d225400064a40601281044441c08090139039261601a000440750101c54064005203004d110342401900d480c03c040c0148401e2029a049540c40502007030a224107481c04107115001410300041140300e50411800e81849010742c2007000d81c050080d01003034040c54108800303402c01c07100840c1241d6020340d070640180e00100091103542441400b6108299a609010884403000ea1000b401c1c403109801c00c071485640407600e013400e584a0b009070460012034101400c0a41401214180e0500420f007492061200d40f06c00f03343d2900d9010303d03014000c2d4021681205010301144000e10038001208410711070506040302149100c480c10340c06040382c0311040149a0502d080340031140d11450b180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 363443102 1250 363441852 363441887
    0x5040606081b040506040b0d0b06030c060c06070f05030108030d0e0709060803190e0d060b0d020d03080f0603071d0901060807030302030403031214070e0415080a020a09180201 77
    0x2100099107031042115034103801d081d55200c1803403101d041c1800102c0d10005c10310751007035040c403c48004544424584000d201e805c80540e4646580741000700703113080b1001d039415403c110b0014452034003010216004d8010007860f030301d0b10b40c2b0203000311080f10140000c1c01101c10681003008030080260203940300c0140c07585190180c658980e40d85a26030101d03071042d4440e482ca03404c0042d448080305540c0300e1000117014603080100b141c401c40808181c4000c2180c500400041d40c604074000c0507502e0ba260b8101081c3d0007000814006a00d00d0000c0c032900c0141e40e86035802000714046010342c600400c060f0306540c150080410200030400500c851218040c18182d0195a03810300859152401e01c08034014600a400656440d0f156140c0100042081c444c158001032604243e0703280c601c5160240ca41206192500422202045000a004100c054007002101c5001600000c000d080410500000e6001f1640c454a071070b07441c66001c09403045202c0d5804001040b810100040d0b00500c0c1d0490900c00b8013 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 363444352 1250 363443102 363443111
    0xb06040b0d2a02011d0106081e15010b0403031b05100c05130b120a0903091404150e0106110312160903050102160212031804020904020705060103060203151e04050406 73
    0x4038080c110352282d100d210740044c1d445135440c2d084041d40c104494002c15400c0c008204591600004584a88190300d4010314000b5a444c10310b50200c1c100300480440100f501800529695048500e1103940584401c40105075648011042c00c562045245041c98000303001d014140d03a10f4034040c0041100d16040818042c6c144501d9285c40c0d40c02d540c4102800c10342e008a80e8501001c0551110008014a2250080c0c1061881c00000b0742c0180301030100d170101c11103181d80782d440c0d6000602038003d840d161601d0401100c0000741c0c60b05052240f50403030300750f915001c481c5608a80820f850380314032048110444251004500303018000e0351108040782072481c0201000b41c5a5440300c3c01c0e60f0250400c501e000802810030020b51520185403401c4004100040d4917160b4105044940780504104261007142c5c04680d0b00301c0d035252a0102c40b82654000b060354034660b12071800f40000d400507903a401d2801d0a080c2c44042c6820010310400b485840800c140e4500c4181c401004007500300100104c0b1135075183c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 363445602 1250 363444352 363444401
    0x11b110a0b13030b010b1c020a0e0301140f0703061410030209100807020c060a020c01080405030903030c01050114030d050301120f1a070315062f070e010305010b06040b0d 75
    0x50801402c04000c407482c500d00b03090301d1400c0100407403c0680241725807070b00810143c3c850b150141010740c4103002c0d40c000562503001900d007e0b03a6200c00c01070125003550138040b0520590f80c0400c565840b4008003048140c20343c0307540d00101c00700d40960003900240e12401d84030088905d4a000c119460000e00d14015152a001d0f6000c5014900c3c0d00412001045020050102e969014020000303a80e105580b041d041c01080c8400a6032510001505414880c40300c001c98240304060040b50380007000907040341e0b034034068207082c20300138a003d20038020300c107034140a101601c0c0ba0106903010081d105551342400d60b400c2400c2c0000c0c0c0c0360070810849425805c60b02000004900c0c43c030b8892040d0500802d008107142000300903043d150044020950320188081c2402a1900105c10003031076600c0704520640c4548040c860b102d00a8880711440340ca100d890000103a41103200c4049043e6072081c002441955010000e1103a17078007130b070b0140c058404d0050194100f00e801d107030f1042400c100c402d103800c54032082 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 363446852 1250 363445602 363445619
    0x6061e070c03080c07090203161b05010507110c040b010c0308070507050a060504021f020607050d06081204080d020105060d0b04050c040c0f0e0a030213020c030f0307030603020f011b110a 82
    0x2210b034001c545558000c030742d80000f0300d0240031020081444240c1945185000d1409003421905031988006001800300b201d46101522650800c819510800030015414a550040c1c0040c1195800341c60300c0c400c4000704a040e00b4a070054518000c81070319981403c0c2d0540d5401c2d02c031b07403034000e0480003000000c0c003140d40400c00030025400c12a000b1980040c1d10b050500601c9228198018040d070030b4041181d2182066070b0001d10203611011a180c010b0316504101c0e11200a1314041d8801c0b0854424450f02e00c0e80054007a00800c01c54071420110b504100c8030080907401d8600486200c0e83c8000e00505100107d0005c000d141e9126110f102611510466140018200e480500703070500022180c022404206030061200720f50315408649035040c4920703507400030f24094004201842c13103a8000c04d01903100407040096030356028624090310b0322442d06050080c010070507403000380c1c451402440610080e5004070500c019140f00440300f810105841d803210490000b03000525600014142c400191844 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 363448102 1250 363446852 363446873
    0x4120809011218021503040b04060b0f0603010305010b011107181104080d02010c08060f030a121b0b0603060c0c0a02010e03070801060905010f090c080f0603010b100807020f0606061e07 81
    0x3c1e84500401030405840c0107100a207001c0c50701d4000080c07010001c0c00045901101007603030040c2e104001281400c12840420f050f100f00c0e100c05500110080004401c01106400100700100d0030b9032414940c0584035030043e40ca0301548501407422040116001d20009070f1341007000002100f90402d0b140966504449182416802c1c81500507551a4000c401d42580402115000074044458601c800a40c0d070003c1c1c0c545880c44030041c0702c12610160241c1c0039003d100c0c000b030207815042e03010200d64a282000c000d501011a04144640a024005a5096480019201810b5402c0000c241c8a19242d0040d80d0303411034100003aa062052180000300040240207000203800d80d42000300c2e080d40740414044080900ea0800e9003890f04103241c005089500c41c078a07540c010314400030341403180c8500000ca4010056980002e401000500c18a000c00f90040e00041c09000c180d070817180d4015000c2d09442e2600c0c4140e990951042c0c0400440c260041c5102c0303030b8200c0c0d6942c0091507103407040036079411817000e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 363449352 1250 363448102 363448121
    0xb0d2a080c01030f0b100e0d020a0f0306181e152c0606010e090a06090237020c060703020129010809060c030117030c121e041208090112 60
    0x207030300410744211156818040d51050312801d0380c0030300a4607056000640030301c0c4009108010081900d407001c03416540c03120b1090207143c0190081d0f51050311454081c20348002030005075102800c0480b02e0442108010300640e6030f5410469801d1a441d03040f11139524460016070a071818078a031003610100942c1d82c400c0f084589864588030008101c0c00c01c03038913100c00326046250500c0d0040001c1050598003c840e2010b803a03412658100300d60b172001040c1004002c41d0f00720040e5180301054482480c140054491345952011880d200856031808001c0c00800c40c0300345480c01a00000e64072111070030710b400a030003041d100c5e00001c0b4a64410b903c8151050200390000c503001c40085180680301e50300028420341240c09007010340094540007d60240e20712044c402e6218016041c942514102c0083c4140d42e5a4403034070041c2d502045400348640c105030445540000320315001000043c910703006101b00c41c215542e814500f030b58002d0a490703254058004030001414060000800c4440312a03a20840900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 363450602 1250 363449352 363449369
    0xc1608010c020c010203040e0621060901020a11010c092c0f010603052a0f04180609060f05010206042010030204060e091509040303060506120a050603010b0d2a 70
    0x8914146600030303d800341a0007418150f400820081c030011901203405c681c00302c01541c1c11352035600c5c4080100e60316040210780807103e01030310007400821141034004111440702ca5480c403100c1c0b0788940c102402c80d8215070700c0b4000724140b20300800081e5503030307140d10007000100c0080a03080881c00340c2151000c817084840001101c010001444007942510403a40c101110362080980088401088800c24185585540c00754101180b0003070b01c2c0c071101b0202da0152840550341ca010162444813080a4403060088558190800c8800b080b000034000c1d4690444030142d0044c0301588544c1c880b40da00021120f14211034449140303071040103032102488200c0e11049590010380e524980740d4014507500200601510a03002003051011110301003440c0300f5402c8048600341d406d5180d030f10301540205026030019401c1500440d40307000301c02d09191894810865803c050000707a54450826003218200151164007851440009022030310310786c4151681a440070307040400f0030a901442c0b00442c400e03800303040b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 363451852 1250 363450602 363450611
    0x11090409050a0b090f0a0809061306030e150c040b0f07170715090312020a021515010e15040b130503010f0e010b0109240203071502030f010e1003080c160801 69
    0x8114030700b0012a413102c41d03031020f0540140d1150b0340f151121800d50020302580c10100b035000280c2d99082c22246140c032502000400f1990b40e1001130080d01c4079136031020340c40c0100c5504e00c03082040c000e034803407040040b811030503d41760600001c088103411207035000c200003105012071800102c40e002d1046094400644807500c900051900401d4504100c1a2a0820382001c8446000a07000000000030321030b4042c000d030310b410038100c08034600813001c1c244030600c200d50b109000708802c81441c13040e44610207030b0704c0d03210351900c0e401400080c070901700054100000400c0100011500c01c805403582421088040210650b103a00003425501c120a40f441540e80e144000c1d540072609201c0c83e040d0501c2820036107100d51400f0080118030090840317a01c0114042490303403580d988244110389180e540032142020481c0400000c00003500111070301102503420b0400464204001d440003842090805026841c071810356036401d2298102c0070701d5249a111b1024210040340c0c000c2c4852000d403e0b0000000b5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 363453102 1250 363451852 363451873
    0x403151d070305070303050304020d05071e06090e07030b0d050604031701120201020a02011211030c03010f0e190b04110c010e01051e1b070f2a06080a1109040905 71
    0x30880c000000544009500c40c20341040080d40c04505541103a8040c249a80c50f96118004516081024580148140180c5902081d0100c40c400b03084444001c503410b0803045616800c0c20348000c4403901035804101c1055000034030340da2198008410802c0080c0c0300c1301c141501c9a4ac0c4506d40131b82540c1c22004103100d03080c1e0380c1903100148101401404e50080a0200b0030442d00041d4a56208040180c104900401042c503114619000301920555181e0b1083d52440c000314140281d400c28029048000000f140000b04140d0114410b4003580300b2036040b0103988090b4049400818101d2030160300a52200c82c009100201c4001074204003d501c2c0001c920306000c15076a07400c680004101e21214041d816505103c2c0d0184035007a50300541e100d0850444a42d054032401c0180501c4a00034104803442e0346001c00c03c000c0301c4488881001c0d1500c031084c80b01c0b48640c10720200c0c2c140c0c01090001110361000850b1728109800100d01c5101c08aa00b9181208a80104041c3d6440f861700343e82942c00088042c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 363454352 1250 363453102 363453131
    0x2010e06101802031620120c0708070503060c0a0e04110c010b101704080706180b070c0f0305030721150e06030c120c0301020307030912020f0c011103040315 69
    0x902d40082c403000310301e580b030304140180144a91480c40c00401204040801c0100d0401d6820015525540200c07440c2d00200d02d89925698482d10000e1581d0080000025045400041880c1525001400b40003242d0740c0b0178245107190880302030901004a109030201458407280b04042c058000b1685241d40c0c0c1c5511b115075800c1d91000404030780a00b103881c000721036a9074002c01143d5009100542d19025441e5800c10900358002d00714050842450401001c0d901c46407c1c00e500081c1c1e1150141e2000c56440c04025116100d180e8800303050100800d42d60f00010388a03800950b072104807402c1a020241c41e5001c0d4007500020345d02d5600c606991801e10400e50140008418002d001c0303405440420324009010945900d13a51034024002d01141c00444440c12060001542c100005002151a4a041c0000401074406003005552440541c030411010031720106100f880a16800000c1182852a4004490840440c0114000e901040c440400010801901001d074030005201c00f145400490405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 363455602 1250 363454352 363454379
    0x10b04090807260d0b060f040e010503240a020a0c0f1202100209060a0c290403030506040209011710170d09080a0f200904030c120309020901030b0702010e0610 70
    0x940903e40c044040d80c681031401401c845810180c24008102e507400032012891602070401340c8100c0010110700410051140c00c83c160480c1c0301102103030223103000450240d4261240310390f0074050b070011100190000f1003903002058404118900300802903407a8031080b10210180c0000c80c0e1400e040e410185e5020740c10040e103520b020a0b8001103281035400400200310b03104203030111040c00800d200050520211401403000e4450b06100801c207030302640803403202c0d0f010458003100841c2c90040842e02c1400c00b84240c4003401c1040e12a12103290289001c000007540040118401800503000441c003601c6640382100502110001441c480810700170240103081c1e0b40d0040c244a0b8011000b0102107203011515242007500b0000403403090b48980e00030060440c4001c1e4184d00301d0150b1045c4020154401c0284490602070925034400f526416401c805440c0c54840c080d40c842d100c10010b1011808128145400c51003900002030101c1340300a00909101c0b08407940c001c4000108010440003c06001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 363456852 1250 363455602 363455633
    0x16080325090501120c02010e06180d0e0f21030711030d050f1c0207020a0621050603070b0c03070209070c030f090f090203090c13090309082b02010b04090807 69
    0x104010341c5410100000c00400d111682016400c0d15200c000f81924000c1d4886900c0810650a0340c00d01d03d808003d0421a070f0300e0320750380d11307041c400c0d00081c0c0d08841c811501051101802040c403503d01e00280c041120041005142001c0010201104540504204000d02031079100d502110b45014011f0100b6040c8090000a42c0c2404001c100100c1841010003c03901d82410340070081411200702c1704100000e01035000025080500c20b2000304215402030b84501d00c1601c1044100318510740000d03041c040d1b0340c00b91440c60b0141d2002c00c0c103004030210100541542900f2404490502c4a00d4000030300000080c6d44100100e09495480c03018560b0100c80815500a54113088040c14a003c00a0326602c14621a000c00140d000c80855101070080c0403c0c02c0141000703102d02c402128968840d0024131040308100d000c00c50a9800007075900c00820f00700010101281342d80d45030014010381c00c4000442d40c0350321085540c0e901494606584520a02d01014007400006880e1502840d0116010003600f5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 363458102 1250 363456852 363456857
    0x100b0307050d0807121e120f0e191b03140f030c030313080c011a04060906031203110708390a0809010c0507080a06060501110c010516080325 62
    0x91007034040f40781d11007103958180e400003c07400444520541207861030f005080398020002d1801c42c15043d554004514801c0030650703a001c010025000c6500707030440c1c10350038449005400c545c2c50b401081c50442024080a4040c0203c56140703942c1c85040c40d03000c1d0306034001b210000100403900440403410048842c071140414001c500d4648140b40361503481c000244148a0169000c0c1401c0802c2896400c0d41c640a81d644001e000301c500d010359402806104082203800740745080400030f40d50640c2d02400d0200c0e608071801c0c01c00b006003020210040c3c20840002c2c403c1c00d0040010b13500203030700d141c01000390703201c000c000c4070102c8103120154034106043e0300d0300c001c42c9038440b02001e850b1201141d255651a48034140554540d041c8c0c0c0145c07001e086c50b030005421401040d000003030204c804141d003405144107100400881c1d44407401919110051b00340d0030702a52110001e00125401342d801400c81c0800441e0044041d0070315074461103140d0044401441c5207803400e0750301a480b59a845c03022000221030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 363459352 1250 363458102 363458119
    0x306080f010f0c09030b04060f020903150105090c04030c090f0207120e090c03040816150e0c03060a05040302030d1a120102070b0c04050618040e0d050a08010806010e04080a0908100b030705 83
    0x60310750b00c041c16405000600b82eaa55270f10245450005030741254003404011b0b0582d884808012136400700c82c1c80910446028801003030018900200c907004031015250f002e0008100581040040e0f0b0040440c524680c00d100e07401c221600119005685002100600e030751484403000c0c040d0305110b01000040d00c4411618024003e010024901034207845010984100082105a41e420000c00d0300c20303d0001d110274145400c440044103071011482c599061070039030803103d09440c0d003080041156411034024005800038000c110800c1820f801c010703c4c1c01c000400c2d02c0b130202c400f031340012103544619554105985d40028003c2c10800400c004503032001c10710f500e043c03e041c40d04010460622500200042144502c5c08541580d641c5a004198a0a006040350713100180d42d00c000d01540e100200381c00124204e0f40000500000000b4118160341520715500c0c065247e036590881c6580100d04580240301c00d41c0d01c00b042d0144200310032a20703c02c440700c02288041c4030109150034070440380c01241c01401c10303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 363460602 1250 363459352 363459359
    0x5010525171e27011205090a0309210b28020d15080714181008160f1208220501091a03010b0c0708010203010312030605010e011403070306080f010f0c09 67
    0x70802800805070600e00a00c040f490708401250121401017200350a10b1804080c420301c0c00c40000c1c00c040883c86629007002140d00c410740c1c803100714020030780b09032001503c800810000300e0003061942c110307a114294408010407500c075250341e584004244400258045055402d9844501804070b5003192581043c4109041070750035500d4012034002e0b00408080030f0f41400781c0b030310340300e507004402440c181c1d6081c0301e4184030004000840181c4110090341c03042c50520400d13058400c941c2d80c00c4913050960002040e00d03015034841c0c2c2610390b290603501207505100c042da0381c00c0c0920910b00110380c55440301145030305280001d0300c807201031b400014a401d10130078148101d40340e00080301e06503081c40003120707100c1000b003281c0c500c2c0030f226802c00c070291350010000004012103403001d0382452031191000c0c0842d6465900441c2e00e42c0300500c089000600705581b10280f404510300a6400dc0070615004c41e40c5525140d005140481d0b0000b100300c140e6441d5041e0000131014852070404861601e4418581482e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 363461852 1250 363460602 363460627
    0x5120105090403200703150209030d1403071202090301020304140d0513050f040b06040e07170f13030302130b0403050d0801050a0902250b04060b01050405010525171e 73
    0x184131040103c0200e900e241030f02003600c00c103d0303c001103610042d4280300005034500324000e50846140607000f4444d480c030600c5014003e0b40705100325001b4034402d0381541c0e100001201d048203401201071000703508000440180d1001c0c0001c41c4114003c050004806826504640c90082002142810010700344600705030803415090402c00c4034811141168105000f500180c01050844507107079100100080000d100d65881c02104d01c40c034895229040c03540d85950030004041d20032101d004580e4144000503103003d5180d50400c80c03240c02440c00506021803188420741c0f41e00309401a8010507400b0030100200076041180410100e200c0ca07220070194035007070202d46190030700c1c000e000d1003540120340061030603051030090711881c400354400300f07182401341030180300070900340e5096615600f440340c61080365008104480c02c540341030751400c1c035283c031013542c41100d40311021411240d5101e01e01c81d0400308000d0068442d122000d01880c969400c1e288540803440c070320101801c810741e0428400c2c0064100b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 363463102 1250 363461852 363461867
    0x504020c100509070503070314011104051f030f1814070f030201050c030c031801020d020106062a05060109021c0e06010308180a0906092706020903120a05120105090403 74
    0x18901d840403030380380c503a4020759040240642019805100b50350000041c002940700ca4114000071200030020000311040c0408030344940e01647d6041105800551121200d030b1240000b100380c40e02e0009940c604c1c140c1c41100b56a00f0114079904903002484000500000c0e252501c00380c0c9284000309842c030702d00f0890038103414a5100c060305108001c240e6203c41c04041c0700f02e071a941050800c3e6951241482e2101e080c00c07401600d200d00503c14a540c1c2d421076070051190209541003910b4841c0b542a001d5080c01c4224006101e0142504c1c1c01c039600c800048080004130b020701000c41015807103616900405614080d08030464030118140b02c4003180050000c210141502c0c0c10000081e521841c16540d440701c0c9480c840110341005100720002085d1105902003819140d41c2d113004e009500907100d10400004558040a200e2000c0000600000ba403e90090403010f00c040c0c01d031054111241141a03c03508581c041e0380102e103001850642c801c80c074005690240100b00c030149090306064400038800d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 363464352 1250 363463102 363463123
    0x3304050a060b0102033c07051f090602030f010326030708130f110a08010b0901090905070803030a02070204060501050f030708061c060e06070507050d0302070f150509070504020c 78
    0xa9900c482c020b00a074802d000325204c03001c581101c0500d0680000807489414030000fa1071104100040100b0700b42901c1000321410250404001c019154003810510440c00580c61070885159642c51924005801f500141d40f0400c01504013001643c51810100e0240c0010146104841103004010701009101019170307401401c1840c100c01c9035070391665100d030041c3c40410054111f100d030b03981c42000c02040030401030b411b1805507a1034041a69400b6120300f41e0740580040741d4008031010042c0300745502540250300490060b02100c100955801d08917013554026514440801d4001865800b9801d0034090b020041c0020710b419440c181c0d40781641c1c0307501c0c003000e089003003000486d03804030b203281c0c0d6407804800c2c140782c44d2001007444408501e0540024450422400c0440c0600d40c0042c0c9080e0041090741c51064010020380381c181c407050421002540001004c139070f10040420840081001103540b44003a200310f078000221410040d030410b140000c90f60101d4070950040110724101e40c07000c188441d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 363465602 1250 363464352 363464363
    0x31b0c06011809230c0301060833010e1609060e040f0902040f2306180a0f09080a031a01052d160215210703020c3304050a 54
    0x11420b807500000079020241014200030000d098019480205000c03001440120500b100e000c8820031090500b62812807003088002d401001940101c03da0004102603a03020034001412807120002107031190200c20f8000c038400303200000030031180642400c0820040110341c145829030303e1400e0f10040464032107072610350090740c48011202000425800090450354000c0043c00013004103240440140000c1d0700d0a540207841c1217050007010507010ba19801101c005c0c02145016030f4540f08405d207440042c042441d0655a00c501f00900c06c80c034411480000d1041e241555a800507800040a03903101303c00b005154000401408526038110040b075000380402410143c9916401c0304440d1804046103108051030703400241d01d0f01803001102016030052084034662003640451160303d03824042d016160031001440300300c0503511910321537200d5124a980c940985051400b00c3c4540c10000115a00324604404008240001c0020101d046080e590044048030b2440d154442568070302c0c01002c00b411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 363466852 1250 363465602 363465629
    0x40c0e15060d0e0d050a121b0e1216050117151c05010213050418120503270105070917100209010207030c2c0903122703031b0c0601 58
    0x20400460f41082045075142015104020400d4802a00c039600011003880040c540100c0060001130301d20800005103486804900c01e42020300c0243c8450520510040d0f1040340da00546d01448000c000c3d030320141800540721003c2030301d0103001601d4618010a03440c0406543ca04000c1c80c10b103c030140140c204002c465400704501034280ca160442e0b442c00e4040c0442d400001c0d45803500408034003032012140f066a0810103011550501030805905510003402e00511078103404900b48a0800340d500410700c00b0302c020402c17171040c3d0a0120500300100082caaa51142c081090994019515030000c1c840d285c2c00d45044140c18840e19250314651142c514001e40c003080e02c80c8103920802140b80a10340c011a020340c1c144d10b8810301d056504034000700307441107a9180c0549091002000c961070088500b42c0080d4140740d501000d803200e00780d000301480c81110216611100d5032814000800705044d03404003844d600d08000c12080c018a0f0176650440812904100900c0c8044000520604444003040d5028 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 363468102 1250 363466852 363466867
    0x51b0607030f141e04081002030603030a0e030c060c06190b0609040e0102090907020708062211130c050706150e0c0a020f0307060c030f060b030c0903030c0f0105040c0e1506 76
    0x355580a1002c1310132000282a445016860002c0000d00560368120101c0e8442d08100340b985040e44000c0306c0c0e040e01908280520000a07008070120b031070071140101500c0410742c5080100c1c11a400140e84140e00f540544240f200106204600d68100c10188409120f4450498042400f610900c0500c2d80100e0782e80b1890a0101c1c030030741c10340d0700c40c00c0300800101080c00c0040000703650744514040c5442c98002c11000c03e00b0500f00140328525151025826071401000303850b541540d00f0540c00345a00204c0b00e10031804841c0407441800031005042c1c54654841050f4240041101d4881d0a581038a0310303016402d105014000c400c95a004101c880d032a5a10350138104202d040c04101e1819049602c4003140c040100201500070001c1c89466035001c0083e908a121214140c0e00107128140d45003108201260b15001401c00800e16440060202d9144c400386414907413528100e81c1c0341d01b001e42d5652060100b00114815448000c2c04100c041071800c0c00c11901c0c2c01602e0480c030790400d208450025660 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 363469352 1250 363468102 363468137
    0xc1e080a1101090c0e0711030406020703110111070303031a15090f031608011b0519050315090a050a05070c0809010e010909020a1716080a090606080a051b0607030f 72
    0x1d1644503800310300510b8550b95604181445e20b01070300c400001c161242c0300c08901010010555048503030650040210074995141d0340321007901600c1041c100100e440201969440070860724000310b100340c0e0001001141154040d040c1040c0d41c0307206211307501100e011005040003205880300c00d2021030fa142400354800000034a80082da034403500c80507141850015035140e0641c841135100b0010034aa0001d59804e4000b00d402d88035120034035898205100102044600c140c024550203150219240760394545080044c800303080460f450802039894100b0801034000758081d242d04140c1074145102124095615075080740202c446d40c50400c140803100c1081c80c1c0c4948102c1d40141a2000110340e507007602d9030010134907552008402074032900348021592142520000125810440d074414003031341c50305c01d42c1c14090319181000396807181d01c586002c0b403009402e20030310b04610f2003000144009a4a1851390200c40242a00903226010520a100109411480c8201418014503100f009864080781c42d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 363470602 1250 363469352 363469361
    0x901031b0f080d0206010509060102030313141b0f03010203220c0e090109050c120a030e0f0a08150a05040b0708070c06020406030c0908030310060503070c02030d0c1e080a1101 77
    0xe1550071001050004001c8000316140e1210b4040e5400d541542e80c035031091008107442a600e0900680c01040000c0300da4081c0c101c00140144645100c4400fa10340c118218070f802d0444103002d10241840000c02c2e514a0a049000100a000e070020340c214a042d1400f1858403203910000c4080002040b903540411050207000d0010b8182d031340d1145030605002041318003c050078101102c2030301c14000340e41c0c2c1c14507260f05020031100d0760740010003a0041c071365011a00d40b45100d0100f90081003400c2101c40c02d580d4050210003a201c0344004002d0104514540c1c500201e000e841c80d81c601e8542070500000c540d003104e102c1e5000e042c1d401d0610303082d102c10500321022110410003420b564800318003c103145615811091892800303680798002c2030f13125454943c580c801038410415980042104002c91400f582c081e50f171050903800c02d00d00c2d000e61900801d0400040400d01ca00007200068501c04000c0e8410f0381c0c2c00320030002c0118000c00805c1d03550344401c40c850310507504140040c980186542d11000d410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 363471852 1250 363470602 363470609
    0x10602190311070f081605130c0201180f0b0109051b0901051309020d1410060c05161d0106020319030f0605130c02010e24040606090e0d020c0402090901031b 69
    0x11a00d882e0764404d110880f090031401045c4180c0104410340ca501c000040c9030b40181ca2004280d0840341010309501c0005090324618601555200c640c160b460101c0300442c101418042c6401e4000c2c1c1d03901d880e00400183c0140c000c9840e96103004213101034142d0fa50010240c001712003007055582c605000041e01c00740100b0004800c0740c1da1116000c203039166503401030050426500ba003404007400d0b1440004419608484088546c8460303201040038a2284410080140c09801510354148610048441c180c1d507903006440401c0382e082c0b9032300c0c51450001f000741c010302551010714240020303199000c4110803400100010151540a90f01001e8102d0707104400400f001420300e02240e104c90480d10140034150003140141d4038000e0100700c0e11001142c3d8a80c1d110398001500068002c4200d00b003058040a40141c0e8010744d504404110049540b040f8043d4030441c00080440302201ca4000345042d121012aa0040d130040c4140709854413402e2249041da80d000703c01e010502910004480356014550 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 363473102 1250 363471852 363471887
    0x71e05030a140610030206070204050402040b0607031d220c02010f0914070e01030210030f090b0f040b160219170a09090f02040e010e0a0b041b12050106021903 70
    0x109031040101d0740c0e140d00070b440c164605403041c0d5503405407125034080070351001941100c0c0c204803400051030268409544188001c10000c2c0c10314143c0080740e1180c0290303c044000c500c00e5851803000315444074140c0103c20085400380e000a04842e00701410119107241c40000986a00c04121542e000703402030344148001c00b10402a94002c0d040c500040c9400c806091014090307010003041903400c2240d0b0381d050f243c001d00300201e8510706000440c01040e000700310342582135440c1840400194104901c5000da002500e959425080c54107160b201c02c100603114050200c46006440c40d00d90700800d0b00c3c0c84c209911044402d4540d001d090800351003420000c805410100000d201e5460347d085031042044e9201c813001004100c64406082c0c1c200d02c580d0148500d4940840e004200c41c1d520300d100301d80d20948082c0007107943d01e05600424180d4a0350b070310b4200306451840344450505d5000710715142c0444403c50612075545041806034a0308001d00c0c103401c172042400d034a0020706000b014841080d4a000c1f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 363474352 1250 363473102 363473113
    0x10b040b0f010309052b110105010803071712100302030f013602040606050408190201020309100509090420010c0b0c030727140613060e0a090204030501090302150405071e0503 77
    0x306142c0c0c81b80c05036010480221341c41101c40303d505501403044506807030001c0000c6d4070b89a6a0f8840010f90045208128002003003003041406408500702154050007288401e0400c0d581188105400c00810a12003201c60385440d1039101103001400b004550b180e600c170a10710000c001c001075000a1500140d0180d00b09051000005a042d131040c010821180c0300000e90311140860300b043c203010111880043d005a209100440291400c0b006200c0c54181d2400c200d498090888080380707803000d003254240d43c002c45540b034007006251403505c59074843e502444c0c20000a111a82d40c3c03040e003080581004174525010000403281400384082c0d542d4600d070035500792075501d031100548210103810701407030300c4042d10034034084100c0c10410f09842d4020900301c011508103080c85c2d02121981c0010304400e5204010740c0c00000e13061054401440914012000850041310303070705002c2d24151104030f0307180051054104100114802181c810285c80c000302c103021200c1c030070000d46003e2580d83d40020703a140c041d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 363475602 1250 363474352 363474403
    0x109031b0803030f220503041a04081005010609060c0503040b0c25060909021c0b01091a030a051b030a020705031902030a0210020a270306021605010b040b0f01030905 73
    0x12002614401c0c07007a00506050f00410392411031200668071710040075a070007840280842c0741864401c21034504490200d90605550381d8102e45806070901e1010b1460307035100018080c4d0750748001072030050038140c00c0c4189824540c3d41c5140da2846a072080c08142c54010805911110050014141080d0007490034006003241d684004040c02e036501c01e10020648060000030090340714029a10f1100c8030b40e4400600c03450f0040080081c00842d0320a034100000104c0100d0a00035414074040d04208448001e5224900085003204540d1301500407100014034200701400c001081c8100c03a03202c00701510143e120710441c64001e10350300800d05102d031280854a03802111542c000050104a1455401c42d50961a4030b1944422441402e80c0f080005060012452200071550900c2e83c03041c90500001c0e59040c1d407520b60808a80000c4a41401c086c6c0400410041c00000d008a012888080300e080212007102d0000503440039105203524145511601e00d0002c0c00000c0c42181068690503515600071600e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 363476852 1250 363475602 363475621
    0xb0a050304020a0b04030b0a061e060e010903050d05120c040302100c0f08030408030412030b0f21010606020f1e06070c11090c030a1808120405030c0706030212150109031b080303 78
    0x304881018500b4604040010180303881309250031050ac80e0203c00c0b04160903d101110001c040b401d64506102040c4000400604104400c03803100380207a0301c00703442d031015240400b07001c035000d00380c2107007054240301c1880907a580c400358042d18112424212300c01c14952814801c1040d040001034440380011082205100a403c000c5104600c203096103005614585400c2d42140e801188403038010f41d40c49501c182070f0502d0176110080d40784201408054400000946096500b103070002401600060030000c14500100054280e51040314442000a049a00e040d5510400100048104107401100800703200700901803c001c1100a04032000924000d134070140b00d54005c1d81d040300e4241c6028140d03200c030805100104110395100e01e07120701c0d100e51003ea8400c0c00310050401d807031600040080c41c00d1041e0400003032008041e1524007607220340035400c0344c0c62900f000804c1c0a07181c00c40c0f0075030900e040c0e80c0200e4050649500048070400720b54803840540b802007550704142c06900c4000188004000e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 363478102 1250 363476852 363476873
    0x30a02030304060f090506040b1906080a0b070f05030a050403031107032001020a08010314030408070e06150a02101a03011d120405030a290a02030703150b0a050304020a0b0403 77
    0x500800c010300015070320101341412128048009481500180b01040c0098403c0c03000e0354124003401412601c54524100c0c80080352310541c0102801e0b40928545000c11080c070301d2040c3d004007181030101d124071420348090005e00c0028140d015450b80c44001408240c040c3d4400752941240010054446002c0c0c40d01030100a0b0300075180004455000d885003c41c00305008130b46245900303950350b0646074078503070750b5030080c0d1300c8040e5542c8280003c1c40f010070b001c2000c00c5441c0c01801d00030040d8400b42003000502403070003070042c0480d02c91841000b42c010150740008404d03811000d14000060703045041980c4148464024500c150f00d9420001d0390017640c091001c00f10080a000c00a031002c00710f0504a8440e80d01c00d5126454241c1c00c4207002101003440094030503844104c110600f18104c464184078240c24400300c07601d20a180d03000c014001010742c14031640341c1d0303c904204d8082c0b8050410003000c0440c082c1380c1c5007404015000000030115160720b0111002407818862140d1690788030701d04402100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 363479352 1250 363478102 363478111
    0xc06060816140a0608060a0306110a0e03011416120c180b04052404030506010e07020607020d120e0309060f070213050103020109090c1e0518030a02060307031d030a020303 75
    0x1c469090703012a600c1160780000410720402800d25540c00d180850550349914001c1446138002ca0154000001c036115000b08076100c01c02401031551403511140c0502130607200d4004902903850b19034158024102c942d07000b5000307943c41440f42000c0b1050f1000700e864440304c59041202a042012056000c2e0b0031070920341400080188100c243ca0710340c140864980954480d0350303804814000b40303107243e25030b400c0c10701c1c102c00d05040400c4c0f42c03a440c0d480f41450200280c0c041c0141c010380d50104440715605101c807507004591031000c1c1c0020001785000802a2008000c1c8820441d0394481c5404050410001c071a40c8100103801d030380e120000f40459507000e400680c000c0c5e025400384510011510140c0c070520f4141c0e40c4c16180c100b1201d05220148004100194904003403128400204014004a01e1321129918165641513698005205040200111145241e000358448001030300140c1d10001034075400142498000f6206c465102600360740019610f00c25214040000c084170190750200046114 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 363480602 1250 363479352 363479383
    0x130609060b03070e0c03070c0f24110a080612070302041505040c020d02060c090a0e0421030c050f0c15040302032203050a1401020f0f030402090a050402100e010c060608 74
    0xf115690b040d001342c010422202c14406210401c00124064010902d20700681e000703c2a18004c442d0300d07a031380a0f540b80d2010440301c0d64010f000c641d00d00c1c0038540c0183c140480100701c465007494041000500501400f8100034840c1640b882c0c84903100e1740400c501070042d074000340140034440e82c0ca8401d0a408896009003405141042894907240c1d000254002c084103560b40100081d40e12503003410f0311b607000b00351043c0c8c3c03064614100140343c461401829005034010401d40001d070308601d84007542d22141c0382d09001854241562500300c9500541602c080c0b0300c00000c0380c0d5a40701c0d005030381380c00c07c0350043e811114106444144030038180d000010b460420914810411400d42030004158014000e210061155005944890000f14080107856000c000303a40090f003003540c003040344c0009410807010400b08502c04010001940341001c810ba40003002c118040016041540105000d140381d0006c4e1030070b0061103900030115034482c20003a1119500543d08001790380d00c0300c200e10746800c01034402480 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 363481852 1250 363480602 363480613
    0x1d06012321090106080a030e04060e18011512110a08030313050706020c0604170c060d200307171008010c030507110d0f030b06090604090203010815130209130609060b03 74
    0x350b914140308001c00c4c0c3d000b00c1c009281d2000140d0b0304841c20b4103a80e5a403504151180b80c00901207082100c024060000d5184080300064404060b40c00c5580d0382c43c00c84503102d01072108101881190780c2030b81c1120b0304030f4100b904003084100820080d0a69501140c1c0d2032100008020310500d107142070708149403107202a12034180d91900101e03a9030780c2c0c10002070390025040100304030440d0150a20760814010f4401c0e50300100804002034210b03080100e42040194441c403005074494170203800e03000d0f08088400803506605007040002e041c16061805c1411100e03001380400c8024941c0d01c845402401e80700700a10011610140040103003000f590700301c02041e03011a07420078040020810100c3c800b400d652368401000c1a170000c030003402d180d208603900510200051521622220010b00140040b01000340c1e40b94034114030030b403406001641590308251100c0074031990b0012072041c040720b90f0301250045040e48410040780e8902e9544d1000410742c45c42c0c01c0c1917004212564200500002045095030b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 363483102 1250 363481852 363481861
    0xf020a1409010b0403050705010c0f0215090a0f0f060e18011d0112150536070503160501080415091a01050312031815041109011d06012321 61
    0x10054007403030200030280d420013402130255511403e110004ae6010b914103d01a00315900855a02c204a1403049004100041d0080013030419007200e4000300700c1e0b4584000558500041c0c0c0403408554020007003000380c20041c03407000c0c1d40c645540103155511b41c403210384a5650b40d100300407000e404640078444110b07050000600b0f45040000c040903107030410b00c403d0460342b001500030014007004161440c00c80e03000e2051b0b000050030917580c2078909450540000c0c003411603404586484090781c00030313129600101c103a0150381c558000c5002110000c3c28030241d640c0311450312608160380761840d452018030705400b050604c6251142d4040c2d003d2140300381d280d02d0b600c41052585401080c60051002ca00400c00b0500340d085a0410aa00c4000c0900303441111090800422080710140c03030a480a41d00e2100110301883c101c0c08040c0100481c0342ca000310b0b211005181c80c000440106081e0501a9104100050480300000d004019800700e1382c2d5030340d6036200340741c90700c40100243d10000070212110001c0e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 363484352 1250 363483102 363483119
    0x1d160506070203060f040203100207030201050901150302100809010b10031a030607170c04030f03080901051608071809020408070609090e06010e070c050313031b140d0f020a140901 79
    0x44074a81d8018000d00200d5440040201e40c2820242080b40c0610034094104c001007400c0c40540b4075984694004111408c1c00f83c0110709486069003110000c5a0301102000103035905201c080c540952170804c48a99500d25070400e0041642404603500038400d4030340406195851b038060145011f11040e41d41220b130024003030590305c5030110740003030120304901c2004550a45044400382d1107001d098049141c1134a81d03071100041101e60201f00d000c03650b820309101310054203024a690240e84000408100c00441c2d0005000140282c40c13107082c8201c4800d02412a900040080041c08402905544d1981e452040f03d035564010b2289200140707a2500204500489000d10307040a0307001d40081c42035900340142e41c6500d210107003504040c000b880c0800400a00240090014507008001c28240945036041450084600e0020b1190ba003600303d50034061a040c60090000c01c0f80143c2d50440300d041140303441d40b5081000180a98401c960100001d00c248509844804000c0140d810720442d90707843c40301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 363485602 1250 363484352 363484357
    0x3050106020618010e030a17011203020a0b072f010b01020f0d0e06300105030c0d0b090a05030706050114150316030b04090f1e021e0102011d160506 65
    0x88500582005000c20b1055008040600f4103210719000082c0400c04103040f18910350041ca07420000c2000f040013040c00e000c40300e48aa0041c074079044024035003c46a98025107074000654010000c1100d0000300e07007a90f1091a0b12928048041e031030048042c0100c08000c006445080d04548660901110001130751000c1001e6003000c40b03500091080140e42e80058035103100040c401c642201c0d06026032880c03040004060550000f440c4400074111003c14084004000c050304042e002c0d0313005101c009040d031160f0410000362600f003000001a40c4619a60b5030820b501450064614800881c0840130301503507138006c604888403203035020038001d5130f0fa041c406520300c00040751119290030700c0002c44560005521900384686860300140141e4510001401c0300ca078440107075012040e0360400020080d1940620310031000f0b040c480e8480c00320a40c0022050308043d815202d2a0034502e5100245900035000380075101140c07000703d50b4034151800070903690f8100c0da1500c0308400034004001200d080c003504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 363486852 1250 363485602 363485609
    0x4061409011109060c1c030204031104060302180405011b03020405090106020706050315040f060b0306040605090603031e1201081609090b0112030207030b010b180306060d030c0c0f0308030a0c030501 87
    0x1c141c03c000115007000401d40104090101c2070141c06225080030200e0740348205941c149460042c4c442d400c5042004140c41140d0605009501d041001d1025030346202280740404001150840642c5d83d614006000d01406c5100301161403400c0907501146400d50041c0c015904240c4405030f0613a61a4002c82e61401c1920820001c541308002084080709424480000400c0181000c035a500707100d0492002c0b10b00f5640110310507900030043c0100380c40c25001d03041c0202000c543c0f00103076081c2080060f80364804c01c0440c0e540c505039114048066070f0803100b40ca258420b242c0900d03180390703511080d85440e8210242e03035070301c1454422008165107a0f11321038a002d060300a40c4044550307007499004074a0154500050381548a0030300000000f900d80303c122400b030008011041d07104c030031a40108000c6007040d80498800d80040e401c000f040e0310741c00d5404410760741604d02481030760014200128041041e1300321042e02c41c03a4210210a104151004501890810030100041d0004010440c12100e0a01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 363488102 1250 363486852 363486881
    0xb030c090402100807020c030d41070f0c0806060114071110121d010f0e030901030209130f0c080a0504020d020f0402040b042402030a020c010305100801050406140901 73
    0xc0b45200300d510441013aa032020440c01142ca03034a50480002e490030403480703101d0001429001d84244458150407420244680303105192903da04003906104400c05409449a074864001c5581d03c2030001419210030300035080107841a00075211520b0980340d904c08c903040790104100000810100c00490f0482d840d45800080c05410400120100201d5100301d071030700c1d0200036481c0300900010b0094460fa480b0405401050400d000310702c40c00a00b56a03002c0b2044091511b8900148042c68000c01112000002440e0050b0b50343c090f000010290f4104003045070806150800805408405501c40c2d020305203981c40b4602240e071102c1c45801502c2080703400a403c1140c0303030410401030070015603100d00c0f0340d002040036007044d0300e41c2d061600f20381056000355402c1c00c0314503154006100344286080f4940251015501e8606095400b0b541c0e030205034075aa04040e560f90000d0009070a0131803610140503281d0007404079040600b0800050038492500c0070300f1344003400c0070502d0003405210300c07120f2280c0d08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 363489208 1106 363488102 363488119
    0x702180412020327010519050c010b0a03051c05161115040f0b0c0a0b0c0918160302210115020106080303070503040f020109050604090b030c090402 65
    0x611040295001003100d943c10002c07000d00e9102c980c6109000d02c800102c00740040b140d0b03201c0c00143d44410144032011f00d04169200d03000f0030010030000c0c000d100c160700910410000140e948401082680300044000c0000245180700244111b10704045040802c1e188034050350420b40101212900c60f58100c01506103042d035124011405502009800c01d800d01404d04050f06140c020980d40b2500800c00041280c010130a000711039034403d02164280c10305c00e408045580294075000d226440504003a050750ba070b0304c1c0c2c046100d9549001142c0782d00070100000e41c002c0d403084404d07458132401e4807242059010a03044040c000c00726050014a030415044000b42110840d4004d44c04030b400030402d110400358040c054a0300503410103c42e01d5100c01d10310050301c0c00309040d8071a542040c0c02107000030b590101c0351303c02a645002a01980c000311b00440400001000843d03000b075102020 = true := by decide +kernel

theorem cover : BRFrame.Cov 363309352 363489208 := by
  have h0 := BRFrame.cov_init 363309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 363309352 ≤ n) (h2 : n < 363489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
