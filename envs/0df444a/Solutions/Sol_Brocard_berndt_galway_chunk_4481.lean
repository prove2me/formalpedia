-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4481
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:45:40.458405+00:00
-- url     : https://prove2.me/submissions/49718245-556d-4b01-b74c-71df6a247360

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 805755395 ≤ n < 805935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 805756645 1250 805755395 805755397
    0x50d15030b07110f1f0b0a0b03100f050109063c02070306060e0411090703060e04080c0d0305090c0d020a0512010c0818210705070b030a0c05090315070203 68
    0x1421a240400400c00d00030382c0203440c0740f440b000c8030b010750300b195240801d019955500309441c01c0e000159200704038903a44059010502c0c2810041440166554500007131160791701c00d483c09101124000d205000400f40d03211000000c110031f1a082880c2841d10400400300c4207220301480c40280f00d80300c1d42100320880325a0107100e810249206075100b0722014080c0d0b031660507120843c1c1c41410711000144c070003909000c03244500d41144003800511645000c110399030000501c02d4050682d85e00c0085440c1840c2d40b44c551040c0e04c9540c8860f40e807092002c1091411a214502e0005c1604020800c10a00c5000c5100480c058058803460491000c03480011001031141d001282c01184034070260030381c2141500006504071458a601c0055201c40701d0400d0000b541c0918805e440e440002e0100070114000f00381070b04c0e0900c100c4140e0a105641e5191030505d00f01741c0c841e00300020044140842c8290318412440106840c0c00d12078034116440c0c0200e03480340340b108821643d0000007400540540c1c0284 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 805757895 1250 805756645 805756649
    0x80f15030a14010b0406060c0b04061d032704021e0a02010f18121106040b060f0d1214070c030b070509060706090c33020c0a0303030605040e0d050d15 66
    0x500c07001030404a1502d90b80201144180d0900c03660400c8400103100c2d001d0a14a41d8850304070402900b107176240e032a5003000d406410041200c506500001304013091040c005000ba44641d07a0091800342000c2032000781030040c1c1640180706510400040c1c8840e20341c003410081d1071000401d4203403900d440b80800c1e0300400c10140414001c07400d245c11040c080340e602c40411051845140403491801c02e00c0000c4490a010030103842855208002040200e00c1142c000d41d840300005046049030f44810020484501d41507070204e6848a080115410180d00407030505501c9010b05800c2d0f00300403142d02c0d0140080200c0c403000e05482d100c50082408142301c0e41c100d4092071000707010240c0c0d07014986001c9005000400c000c1e21012003402002c0340300f405440880d80b40c000b40820006040e018101e00790344da07010f250340318425403280300c20700c2900c0d07100c001255004502980700044c1c030301c4c5801e0601059039260151041c854000b211501300554200003070b2406890984000a64960030300041c1c4603901c416 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 805759145 1250 805757895 805757903
    0x8030403060510080f0d121803080403020706020d0e04050c040e10090515060307030c1709031b0d0f0f0903080f0702030c030a0b071209060f0b010f080f15030a 70
    0x24011090003040d07000503005400c0d02440269581d074543c58642c40d0030b50300780041490b41012261030a03040c400e1544040d00058268001200442d250824601d0304031140100c000c00e620390100170071305806200c100e0003031001e80083c0c050000040307001004c46020180842c8129940e6011a14091501080d10043c06008220340c01c28280312003551143d03050b92158a002c241884000782003a966000000311500c0d014202605580700d2900c25405000c60004010800600b49142031040e40220045405070280d6005940d4400844490080ea1210a48c10000300e60000038020b60503030380000c003460392040e5841c00c3c1c905240d00b4881200e00807010790014001600205284c00b0b07100d056001409502d208404032004400104141621290541006002c802d02900010f6140303010341d100e00d000c003420150010340031071256101da00b10340302d00c90038500c103655030b201d000e13003550b00700340c40c400c002d101800c0c212030a16101c0d140050400c001003408145407440464807465440401c0703007105490380 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 805760395 1250 805759145 805759147
    0x3070c0c15020a170405010806040902040b33070206030c0a18030b1617061002010213030c0e06060408061b09040c210b0a0e090715080405011508031806040803 70
    0x80c0503009564180703c04090b10414541c4a8034081002c0c448101c074111803040e116000c036559054200310040890002c20b0745c000d074036481010010b9032903180c0c02d00590b499007042e00100541102c0310f000080c3d13a09500414440070040da001503502c1c030f03042e20790103214800f0b01070b91619000350844c0d0b902c0d12515055030800241e130000c000c0184040415104640d0008080b107141a4490203d400c0c5d203440c55050490b4440c41e0100d8080d04203001c41c58001c00300c9000140c0b42c801102c11140745881c2ca5403007070711140c01c401000e008100441d40140d404c00c9044a58504040c18041695240c0e14090407110101482052105ca00300503074041d15071102d4010010803c8e8018a8000b400980107502070065007649809800795000b40c52166620611000c2c0007a1152400c10209071903483d409031070a5090712420000040c90f8440148019142c03034141e54820603030809180c018255003582c100117908900d14801070003080800419500b001070b00407801c81004c3d005201050461059800c44178036408 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 805761645 1250 805760395 805760429
    0x902130f0b1936110f0414030c010f02100c0c0b070e0108090d050f1c05090a06151a160c090902180f070507080408073803070c0c 57
    0x4024070800481c0c1c0d0040c00070b000c0d40e0803904035605040302c02c40800c00b1082c50f81d0107085200100c3c1d000841d10a90410b8052400a21200180d1942c2065000b000c07035000c2141d600741103007001d03c4100c0baa84828205208801061200603495121070700d900710302c243e40c806c64000803d00c1503500c001000e8101e0100000c43c01c154400603d1640030b007681e01c1c003040003500070440c3d00c1400201c0c0c000e07520055480301d003424042050f403038466100848250000d00c0905079141072219511840b80201001401022240c02d9498a00d090b200c0c441121440c80d00700c0d805c108002215681c03074498a005a51010b9501c6040304410f0750000c80c54100500044640d031000700d02c41181342d02014106008079554240c410b90300d07054680d010411980c0b01a492020008100c07020b00541c05070022510503004c460800f070726a0100c500d0300d09194420351001d080c805590480c3d12009400a284561014003410241c1182c110030307120b448017a01110070041c4050b100001d101c80c503a81e10000d07022200490f09441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 805762895 1250 805761645 805761679
    0x40b03040312140a05100609140d02040e0705010207090b06252f04112d180a090b03060c160b1f060801060e0d0311010f1a01030902130f0b 61
    0x20302182d42070403130b62404000c50300c0b4501c1e00c0c1e480000c46980b0350703a5400d007a040000030204c12040c0003505400600304000c060042e07035940100500c50001800404256180c8000240307401d280b03a00c4003804514100d17030036105407511b604403940018040c201910a0142484045142c103503080043c1c03444000c100c2040c1c0d8180610002080c42c04c1000707505d000c406884c010001102c1503e034106401c014100016500000c00341821f4071600456171402c07450400c2c200340d40010360700101c143c0c58680969852880945008031044010303103131503101000802da60b1004290342e4030020702203807014076000c00c610b0101c40d0445a1400f185520400140c403038249142086034485280f400048080034001010413214480c0e00094100d80b260b543c1e144500810354103020b48034014041c15010005401c030492079440e401d015441040400f00400281e00403c1900540121310460199041504101c48400583c0c0c0e954000641c0c62107148000504520400307490740109045940030f5000080384803000000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 805764145 1250 805762895 805762931
    0x218010f060f0c02040507050c15190e060a0902240301090f0b011d040917130504110406031e05010303020307061b091215021b0709090305040b03040312 67
    0x8515031240001855100c040c10b861464840c00d800e00094068000d03038001d450b05400040c0c01070b01d81d041051a10200b1441c00e420301c40162181d40309002c2e40e8040c452001e4106d100c40c9140100c00c001004500d0864244c81e4881001502d5010429190380d118020f654400b18003003000405041816200100804821843e410034807410303003214500a214940d82d0518022805001030594454020440010341400d038801900c0340c094100342d554135510002000041c2100f00f078074484000c1394803808031200803842c049541d00b109004505049818064a23402029a1f081c0e40481c20041950754910003890951107140d8403520030541000b00001c103154011000b0900c00d07000d02d00500c505100098611840c010449295002030000401084a0611112492081c0c0d12542e25100c0040105580009981200d030f80004111140040304d00da08900308640002491402c00620413038106450260050185114160105400000082c205446101d41104c0307015041c0e0100282d14102c8018490 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 805765395 1250 805764145 805764149
    0x11030a030b0a05090114121c030614030d02030301062007090b091f0504020a0c05011407021501050a120203030d2a0206063f0d02010b0a0b04150c021801 67
    0xc4442e2203000c1080c0c2000c1c5a101d0507580104400f020325840d550900080380d4440300001414041c030030301144101150b54280490089135039000c01d0305828214400c3c40440000141ca120780d001920305001250003200b41d0f13044a10a08000074202000e4010b10040240e402c0340040034022b942020559111b581d0154034415010307101420340e41c1e01d54960f03035201404210901b4480603404001c01a0386401e80040c00000d209103414030802403166115429140c0440344492101000003c200410381e0400a41800030160650b00300c0070351400f03012a5200f250342c06601c10358081c0000d000c0030f6403000c204898102075840703020010070707000c2029500c418000e0b82e07040e45407966a0030421201ba10000740d060081380000e0541c40c3d6030300001d5605404101007900e03002c4181040c0644244009008001c9108555404c06000c40490007000242107440900000307205464001080c02040b2400c4103440c184d84003425071205007045010261003000359100c009502072201000070986000030301b032440c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 805766645 1250 805765395 805765399
    0xf0304030b0a0e0d141308060f09010c0c03090b030402010903081204150b1011010b151801021f0504170715050601030b010e191e0f0b16110111030a030b 67
    0xc0121540f440322500c9035003064243c03001980e00e4096060502d01d040081c81d4034580342c201c014004c2d9945515508000c0104c540400700b140070020080701d48420b0107400b080c2403840c604188080b6996a02a2a004a6021340c4a440c0030100004007164050101d020103190071150007034544101c01c01e00001c5020482d411181e680c403140840015541900130700c04840002003020700320016448040303411303180e02455003489649a403d1278202d0741f03070405c0400c04c00040c3c182c204d540d090300e680c403d03000130003161b500c1d070456004091498029803000141028420101d201190315182c80c1020950002e101802031031111000944900b0402d00000c4420200c00000b0140104c2c0d0f101c00041d0201c4103004c1c1180e010601000d07110785a450410300c1c42c5501e240724001c48003503648405078054182e900302d940e809081c8044100b801140241c5606400414403903008516042000d040c00030070705e80101004244142c3c1e118000116030240150b8110351184400b01c82d00d844032848010007074080c00e02494 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 805767895 1250 805766645 805766651
    0x7060e1e0d050f0d092702030a09080406120506061608031305060f01150906090b130906030c2402120c010e0a05073002010c080d09080322050c0907020f0304030b0a 72
    0x1410080310120100b0400740340300400b10304507580c40d803c8003030748c401401020300541e01c0c19000000303414040644090104c0795964808046281c40c0c0d04111000604070600c03036a800d10071400c0040411410b00c00d2a41e0107030b813090700d0b07880700e500741405003815520043c00c0e03002e54010404151081011141240c51002c450030456511980a8403d50307124040c02001405165061056540d644010407200080c20a4415099914882e500896407281c00c02c503402c4032404030030030040701c81d8040681900d40070701601240c0c039150407000e961420a9010300f806030030007046d4401d81c4d203003e41c0050005100b64007600c0400006180403a114021800380c0d4503e20074083c13a09984003002548904203d200c1d07840250710003525001907904142046085882100801840407009158000c40c2e224912030000107890341403440c241202008030032108108000d200c00b00e60081080081c0854400c00151030b031100c1c544504800324100b60042c1b035441c0301484001800410809130940451090090f16010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 805769145 1250 805767895 805767899
    0x20f0a0e12070e09070306150f0b1303020108100909050a060c110303040609050309060406030603030e0d020607170f071110080c0403060c0e04110c07060e1e0d050f0d09 74
    0x101c4091100801409a120800522403682a00a1030390005203410464042d50390307a03600d04003a190426036000702d1304801e1700b0800041c000751500202502e1501034150900c0d0000f80205407400303445c030019040101800200f01e0302170740c2c4505440a0040e401003801400701e1820180e54a05010000b2a05030f854040c125154921807001c0d450000303c8075000d5031035078585403200806004c2241c0240c4950008000324070007592060000e00040041e51404220310f07203036090281441c1444141031b03000d00301c0100c0c40380041c0d6495040340c80c22079000b0380ca20011804100c1f2650140102c03810044810400600341052010001840b81400000c175890352501508150807140d202040d1040c10700780005000c00e00005806410640542505140110b65084180700090036128603c14002c0b445000003200c0303802d881c05005034030240c411802e0581585074484085201180201c0c0b49424014968000c47c46070394459020302c00d4941c1020403100303e00b8105981d161a40301191820010a02c1c0c4240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 805770395 1250 805769145 805769149
    0x3021e070c140d0b18010510170312012304020a05090a0f08030909130b16120b0f060d0209120f071d040228080709061a0a03110409020f0a0e 62
    0x4845a106009090441c24040355581c1c2c0420b00310140c0a154402e43d5a400c61132800345c24441d8a114030340048250300304514100c01001c40c031b070812009802d2a001048540e00748109c0e01d900c61704440c0c00c4144051080400b030b40260001c44200c2c0f5056201e4000a160600d40b54018068003480e10210f454040d482c2c0c0c2c48101d0315246d10b980c0301b60003141d04180881e0700d062a01481140d882070b082014011408466521103049800440c0c0c12414484641e400a40f00755200401b22800081c82d0b004202d250083c1c0300007403290040303a0000348241c80c001410084411545c05a07200c0c454003030500d200c0002c0c0405026202c0410408124852061890015024880e1074041c10b14000c0000c4a060031f84130380c3c0a0008040300e6807150354050b4039420300c1009405500410000810742100039158440c02c0c65070610581c3d80300d07409090302c4101c40705801040f19048044480f42c4c05c130380c100060020481664542c203070203658004009a4404100018a01001c030300402444030340744c0d00c0500740642242 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 805771645 1250 805770395 805770419
    0xa0e060403050a020f19031212090b18030906270a0623041706070f02120d270b040201080109110306040e010e100b1f14030703021e070c 60
    0x1c0040e0459101030306040241c00c02e0503000d0f40740280a450b5420481180c014981803141c503a108480c04804900c0d2101d503258007415100314180707074001c140a982c10030345170940d12507405042008507548050f110000244200111200c240c8058801c685900454040702100100c0301071801e405042c90300801118500003694206071543d9803148600001e078080d0000800c82200300c1c0400f0346000300300c0030450660342c0410200c0842504d00406003840c0c5200020a6200403900b80c409650082c071a1f00e0300039510605a4184164102e40000c0460080024802004030740c80b1b02140a440501c40c40b050100d0a101e45100c0d40c002e88642800341d0742c8240201c1105c18a5802a05540c02030020510500e4076800c600c2407481007030004101004640901410290b40700340d44242140d0f80e100d41c00d141d040030b071503c01c040d5410061851403082880409000086070009501c04002c0c004006000e0f60301a03419562950040c04000744000440c002071070040d03201d407009454211841500081403103c0503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 805772895 1250 805771645 805771649
    0x1b1908220f030303020d060b36010c0204050402030712030203070501050105030c0a090902010201091b030203070b0a3903090905130203190609050616140a1727030a0e0604 75
    0xc40d1000301c061450b00d00710000d4109910207506582c80d1080042c0b00d203200c10180c100300f88240d0388500400000001c125061900030312001d1a01ca0070350800c802c6a0300044c00400750b6406840110b0190358901c0000d0601410340c00000ca00000c0040f48818103030300201401420703210300001c0242d0790b2203504042c1d80303060f6203180c242e2100c0e9000d0148031100c059000046000d106000118400701a07a82d14050f120104800000c030101400003001986001c000c80e40040403400280b41c0303440100783c002000c0c0180c44144040807895015002004521161a1080d1b0941800382150340b004500d401450200c0710300c518403640f42010007207035507009080b1000480d2540200202032100c1e032030310001200070780c1840a80f405a92030141401045051092a108000030200300c0444c0c1071980c4003502800829824285041c03081c00440f81f00e6030000c40c01c03003441162083c0a122035039064020b207078468040c6592540c04000c501074100004001024007a01c4585407103110403401a4070500c505070080d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 805774145 1250 805772895 805772909
    0x9060903020603010303030218150d060b0f04031e050318150306100f0903080d0506010305010b040e010e1b0a09080c1002061f050a08030405241b190822 67
    0xf0001000002e010b41d0091003100050315040b03484184400000e02e84010381e8400d001d43da81c0c000740c103001a02e001c0c4511005400006201c600780312000b02f04904601031800000c01c0060b41d01d14101041e1980304032240307070507401004c5a80d9190000003c403049889000790038000c05001458844648002055038400c500c0a4613008014aa842040750300c0d2102c0c48000d0b041c003000003804408901c1c1c001c01000000825140400c0c0c90074014001002c44030143c2c0901c1c00070760140010b001e085a03031842d080c1100e40d512401d001035211100701d600380c04200c003c8240d6460000543e026801e8004403c0800c03964200181d880e24051710301030110a2208055090050301301d40e0004400d402030040c840401e080ca103014030725064440c404110040034580142690b60300100e010019031801c000d007011000c00001107121007621001d411070303090181c040703040144071000144900c8850b003008581d030b640b0322101001c40e84600c02d050086040d4412005209800101541008041d60742c1e80607404071816 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 805775395 1250 805774145 805774147
    0x31104180f0f02011806051206100903030e0609060403060f0f0209010f03090c03050a2d03050f071518050c03010c020d210501091d0a12031d060a020a090609030206 72
    0x619900d040103040d01c0b1400301d040c0441e2540044000c400044c840d406846181c07141651041070082c14070411b90000d00040c420441d61103030501d000c0e0300c01954001c42c1d1741428100384500084000407442d0080c805402d0300000046000001d03c40c054022007814030714170408000c030301000040401640301e42005280800c0340000c611900034403951000222500401c5940da0326926a601d850420710350010a6039070401c003003d000e00782d0400414041010881040203034007200240d4024040740210144441480f60115240f03080c0050780c114070541c004d28040402c09265540202c0460b803180090907211440348440e44a800e00f014032654036000c40c1600105455030f074070442201c2c00103200d464400106095a0300c01c0340a00a07000311406040c0b40301c4041170b20031081000c400c0c1c101e44503240300701503880100940c020540d001c5036070382091994a0003048003803810021010500444013407502c503100b08810090404116400761144c2034440d0fa800d9001603641400701c3e00c90100380400b039801b0300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 805776645 1250 805775395 805775423
    0x1e080f0703090302040905010219020a05060138040f0e060603130f0b07210203041a06030312010f170312011211030a0311060c0c070b07020402070c03110418 69
    0x90194050300c0d41520a107011030b900c41c1c890340820240c82e100300045540341e4001c6034611100001ca190b415200c4000d1005141112103501c031159244011300c84c42c0b500204945208464401058a4885558940c000035036005549a1016812790041c81042e41040c682c43c0041102c2c11042c0501e4041d0b00002c0240c1d00350340303c4544000e1100c0e100031040f0b9030210410800780000306200d104500c64000c0352160620550112443c0f6201182c80c0d07090384240c1d10400c00c020008440c5024201d42014103d04821144d5490020134950f104220001e10342a5440e0700000b6881040b551403c02d590030400302481c4070156040203a66400b410a415041001c940d0050180003081c0d2896180d95024618104811a1f40b401090404100b030318254002041c441100c1e044000401029070000d04440f229880e1082c454810b070340703640b054010000a14000030314a000e56071240c05441c811078020740b05000450f601e14105000424551456000e03a08107001400c03140b03008031141d000349800c00b0381711261075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 805777895 1250 805776645 805776667
    0x10b0d020d02280b120708070c12020304050a0308032d0f0601090905013f02090a060f06052101030803150d050304120203070f06170a0e010510031e08 66
    0x300d0403000108002421000001c03000d007030f281c003410080ca10751140c01d6640041c3d0b5842c00540710001e02110034022000c0502680079806814a100c1c40d800c1801c041900c0a2401c040b421403107190700441c4e010542e5100442408130103c011400741c0b20b10000d8100c3d5200c924a4000200040561441c14100e17401c0042e411000b0034035050740c0030605150024409403155a01c00894200383c104884001402038080c55200d51102055000c03282402d4201d00788000b4001005804034485000b8007c00d4048086012400ca13504000c01520b8100f111f018899100c3e90010541c1d008040151100311090301d00900d0401d043c00303164181d90b0130050aa14503540c0138046140920440c03403a940000f095402d6a01194040c4080c00103804880c12100149009004162400c9002e412001000301d1100c030400102d504175000c40c0c59502040c0b6049042d0b9501c4102c4401000a03102c16501542000b040155021310724100c4015248030341254054107054100b51641100030200080c00308000300292400f031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 805779145 1250 805777895 805777909
    0x72001060603180f14011503030e0103050601030e03091e06160209160906030216050f01020d1a10030902241209031306051606090609050616080c070f0807050f010b0d020d02 76
    0x5c581c20010410f003420301110800c0d280140d20903000204081c4100c0540e607850f008507500140c00f4130b0207004c2180c000c05003d84921604e540c00d0700c0360200701e00100da0108c02000240ca2010003c0c461902d50b07801a0800b40c1ca88020141284541032a100203000b510303404100d41242c0001c1e90754035040070b09242c0309a00941c0f0020311907003081c83c2103c200002070020806e03c188200454009621146580214001c0c2e4000102440c82211000c42d450310945803103031818244051031030080781580890002c5480020740d81318440c81031038410111002811070700d00910022121000b200f0b155a108490302d40c170b030301604810450010081000300030440c442c0024000000110700c2e840342c9080f5950700e6104880ea0000101c40481c2ca40c8030031001d10500b800390950001c0a01201c0d8040d52101c10001c043c618000c01000ba00500406d0350818804075840e05c0512a03440b01203913580d901c00381440c540d04d100040c1d000505608001b1766143c02d04101031260901a0b000d0240c501c409641d034204004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 805780395 1250 805779145 805779173
    0x50303011208040302061317070b072d120e060a020c0d0201111603050c0d030203030a110706020706050f06030c0f040203042a06020f010c050f03072001060603180f 72
    0x8000340902004c40541d0390341004001d0f04c0c1c1101c00a2000c0e0b8540041d1020b46003001003a4555604111703020007401c841c200c01c81c1e60301da5124121041c0c0140d00410030103d00940640302c0a4014003000110030040400700042c4000d00644444410f04a5481003080d0781c8500415040160031204284645003003164440c50841c1c41410700d018030841075030100f440c066200c0046040741d4064902042407003414025004e101900ba564000c0703010103510081c0d5039200140c008001d80351b50b02000e83e0500303d18801c0e06c3c940d0342c1c040419591041d0f10b04100028081c20341d041000700380c040e00441c05174900018003042452024002c100a48440c0c810007009410040090f0381080d544030009001c804941c1c0740c1c1c502c426030f202c00344aa09040c000c0c028a01000c02424900c0c9070f1603c441010700c941c000040d10308540030f401380c00d50f890350b42000880c0e001200001e500e0015122801806400506401c0441640c070250350401c044500c01080d40000c0280d00c80c05407128a07500c18010206041203604c0c00c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 805781645 1250 805780395 805780403
    0x362b08130f0f0f02190f080f0c0126010605031e010302011b021c1b09020a0804120507051203091029180103030c0b0603010506031f060b0706061a070503030112 70
    0x41803141c000c85d828200c0450342040f48030350321000340f003000030b44600c02c0301034140d006c020140903040c3c1d0850b5540e031403000c040505004000c0443d525405055644003c9051100d10000255075100e030068101d0b0019500694a2040300140c80c0302000c12642060484c1e4050356010680000e818440034080b0010310b0680c3c002c0b400c0c500d404840303012000f019070402d01c6070540e808034081900a918407100d1030303001904040d00400110801650201166401c00c1e0008080c0d04180001c807019141d41c86211401013240c044c038080d51250010310303c065445004d4240030b940d4680285004102104c104401c60403050b410300e861913106003508100200b00e08000b910b28050340444080464086400368003c41c00110854812010000840341c21904500d05130300031300c010305085002984414086072502440340c118010b2180c80f0342150407100040100000459841c400c0381484006803d1302e002d100c03e0080b91050302c1d035240050100704d41107150031070042c40c116420811490a03c09002000761 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 805782895 1250 805781645 805781663
    0x30506150315030f1605010e2b1b18021803060405010506030d1707080a021308030405031c0c0b31030305362b08130f0f 53
    0x50900c040030008500510b501d1104141d01d150070b4041600d8500c881c00d6201c11a08040c050540d030001c0401507034140c0d203090818070464082c10000c514200100c1c104080603000503203c1e80d00920070b40c0318880f40355000d09116060344d0602d2501220603001c501c01c0a150b0082c542511104005a41c007522440c12041101602010050002403400b4020341c5d00b030307600f65136034010302040340390410030203a0361081c6080101c5240032601484002010062900381801540c40c0000d016a03c40e0303048440700c0d10030610a5004a4071000c0c20380e50798100b4001e26000e482074688003050010001040342c0b4844483e542c1d41c40a250a584c0c08003c40720144c58a0055190b00041150900039140320030000c600c480382042900308241801410b480000c0e2801c2c21040302401c9440480c80d803030f0b0200c01c080f441103101041c1c07144405c41040c0f9101d864048048000402c03d189000014076200c01c11451106548410300b43d00e519058100120320100001d017034030902110000050a0b04002c002e03c0c6001c1c807504 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 805784145 1250 805782895 805782919
    0x106081b04181802060a080712090b0a05070915050403050f010b030606310218010c051009020a050a0e0f07020d0f030e2103060307080a08090d0206130308040e01170706030506 77
    0x110303405d80c001441c4400400c51340400c0143d49940120340030031890520742e040c005508641c899a04038913000d40030401c4140c541002800c1240182c0305280106100c00c0c2c04a001c0d00c1a010003007940c0c11a000459050049121101e440d4005024540c401c410083c0a88900d403506010444158001600c100b810b80404080940e03c2080810b940440c02c80090003503034504450030105003144144140718140b0602d40d10300400319000040301211001400701c006070ba80703018000500c1000781741d40400e512011155021500440440d100c07400b07113081d8680414181c842600030391703c5544080c040740010383c03100401d4100e941700344c119004802c81c100c2a95204020200340e4100c002d080600c1d410400320020038000d50741800c22541005100c8440507000b0061039640d0000d42c0c0c414071b0080c5100361807640c85c0c1c8c0e0543d695401150040a1030800b101042c1d9034070b25264065410512401c07408059042c000038052600200210b80c48003088090080c080c1040b4065005107000741280350012541c0b440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 805785395 1250 805784145 805784149
    0x1110a050601150f020d0f03110d050a0c020115030f03050a03110d1505011d09060301021209010b03010b010507150c05130b0c07140d150b090106081b04181802 70
    0x1c5010303089414a0200c0b006000401505408000c0c0141c0119881150000314155125012901e0920f091071b012401024200c1c000c00d203805545030441940d4909001c0c841240000d0340003240c01030b138940017032000c01d819000c2500030005504c03024100e285046080400244900d000386020b4140d41000100402507400790215a0824003440005540da04da07401c00314508280e410004000074a450403d041008042d211040810b00400e400740d00f5400200c1c0c0d481e50203406480b1501c00310b000d00c004501d000300859000e0304080e490305001794a0311050780318075440384003140c0906400511201c10b01c840c801041c001050102800001c005050286940309036000b004240104000c02031035440705040d8401c171342480415400400509648001185141c440b20f0300b02c40803076000721054490021640301d00e405813420420b1035a10022210010034a150018145409148141c7e00c2c036243c91412249a607051241e402208084181502000182c0585400c0b40000f500188040d403101040340d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 805786645 1250 805785395 805785403
    0x30c0c0a200103051f06031a1804140a02090c09030a0803011e0b0702010c080c0102160f060507020a21021504060506011214041e1b140102150601110a05 67
    0x40a440046040c0801c001642c0c0c10b0082e1500032280610303846403812107030945000345d040707442040180761f1503140c11704e41c1103404a40104070300f002800d440c0c050380341e0351081816588115000c0751045104510703030004910019829141c9640904801c2c85511348441c1a1065008441402d5040c07141041560021b507024001d18020480089080d0769403c140446001c80c50503500180b00c071b1041400150003503a2b020540613820b54102c5043e5a03980d1000e1011070181c030620340000d1400191031901010400848114071004d40640d10030001500d40f00360032038030340e00c0301341024100e1403410446006c940c94804a0041d0300364a40100d40e11180410001741e00c00c10122015103101b43d846c01044a956088071003550888120b20040211203202048070b1070014000e000640800e114261402001468008440c0800e07003018a02d80180210f42c8200818011030266800403140d900198003d9400005d40030000101000301000c9036507000c00456001d01c0c400d14880c158071540c041040426404c0c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 805787895 1250 805786645 805786673
    0x60e07030320150a021b120a0e1905041a19060809030309030d1e1a0a14090406020f1b0715050a08060d080c1501090501090908030c0c0a 60
    0x5214641681c5030050030701c03460182d0326903508140c0c00c2080901808000d6a4010f0b60012103043c0c01a00c030134003c00c1450f64034950840b0160f040c4501e02040800f0030240014003040405940d03040360b2182e2040500c412510540f00c81350740e000c20000148442e2400340c200502ea00310000a40400d0223801c0300081e6190052159402e1603086000184003c6501214255104212000441c03075400c1c00c170550b46e943d100f1b124007940b03141d507600c2c04850819081e100303095060784001c0b424821403040c002900c407200c118681903403140c0c4488800046c2184903400c4480000310007840c06078a0b03512070f16094007960214a01e0144410100460b0000001c010301d9120030100d12402400414104500011110083c240480a105060240340c607000e40c800c40290740103805540e4441698024030b003581f164018a015014075001b07000e86240540011541e1604940ca0588284090703607030307042c40c0d00072030708603807005880322108000103074842d44150000c280800c0c0b44005c1319040c5c2d6880d1900a20440c0c60 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 805789145 1250 805787895 805787897
    0xc1302040807060f170916170d02012d06120c0e071701030212152e05010203070b07050403020303040f08010b101d01031112071205040f0f060e070303 66
    0x8141400071590800821002e043c1604041d6400070103200f001d0312000810b400c510100c90b0b0a000120925003d0058040e8182034600b070300720454940031200d202c1101c0c21030b241032610860200710b103054414064504000310010b20710750880170401034181e029120100ca00d2015442d400000303144245100c90318a142d005003041c1350390509100d84281c801c00094802d4041200594450121001240307505045981c1294100c1e45003542a1015050481c540440b180c48103100c400c00c00d0001d441d440c10504016045840c840d510720544808500c0e0b030031809501d00580c014000c0709c0006602e440500c0c0c0042007030a0081c02c007a81c941c00640341d54010b801000c011081c3c0c1d1000c0001c514240126840c01c4011a1414410298204c00901800c425419047c11078211172200d81164020ba00c850350700c0700c02e160302e070b951070580301c02c4d94100301415558800082c84003281403d42070990f01ca0980600c0d400191590394140035215105800003040c01519000d40e544601400404104840c100552103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 805790395 1250 805789145 805789147
    0x9050f0f0c030708011e0507020f161d011203050325031b110a030e010e130914030c19081c050708060f0918010e0f0a021311030a09050c1302 62
    0x3110342890f04155150b8041c4645130704013542420001703581031142d149500c1007680000d09a4400c2d03001c0b860031003089000690390141c24603030700099000c505044240d81a070f00b21248034410034003002540007000d108001c440e4103000320500001e403007403000795005604188003010b082c2072509180003444064480d4400700b03996140c958080c4a40004040fa0004107041004258145448542d00c0b8001200c0007070420209043c1280700e07030700880410480d10740240003000407c4075070607110000c1c030641d101510152a450305240c8689400011a01602d2400d00a88845051034000e10003840c20008204c40404060040141c1030201c0c07240300c210380d00840c8011a0b00d003003641d40506003440241c60103000d0f001c6045191041d840d520240760300304110080e0040006005c8813a0b6004082440061b245030160075203d805005001401c82c06541c000c952265070b4440f040120801c07a0404600702d90151000cbc000520424002d522000360b003402082541c0309901a040003441d0461440d0726800c0e090b40c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 805791645 1250 805790395 805790413
    0x9080a090e0106110a3302030a050f220c03021203030601120b010509060f13120303050703180b0a060e01080709150e0112060221070206060f010801050409050f0f 71
    0x61100720750051039241801002620640b8a890301c0e00064000640b10000a0741328216610000340c9078025580d0010710300c0c50030a80fa04142c8084c1d070058400560040c10a00030820400260b8515402040e10ba15072000011160a61a6000d8401300c02500c010307a0345c01d00000035803600f480c103120f65003018020355501c1ca4010000b502c04400c650500e0307500d6140c045005543d9800100702c0e490710604950031fa4a0f1001084a40140d01c07030b41e070b207900300d820380c1c41c00015417105d4104000010178425203060042d0768075468120119030401a00051035100040160003090001d0442c5400c1140c1c0c07900424102c1e01c50400003131910302030340040c0241c0d001000411101400e840f40000e110304001800c00b4003842e1420f03001d90b042060040b14031403100c5030324074400c000b01e0794112158608091406c3d01c0d0644034100340400340b070341100c040d000350083c072001802038601000b0b810a2810140c60700c06050342002c040c000201001c2500311414070600c2c52030a010b0f0020810007105005090081050704 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 805792895 1250 805791645 805791659
    0x1223010f1d0c060406050913150810050c0706020f0c01050f16090305060c0906070b010b1b031306030b010201090501090b01080d110c150409020a090e07050a0509090a09080a09 77
    0x200206001032156000308500b20070960303c040480c0d0464003a0700d0310980341c540c8000011400f04480d40c407807540ca46000e180710350044000300803100300c6d40c0701c0b000e5440c1c0555440595003682c0c805c40f400502c22904010392000184503030302620001c129000418204010106510700f1030380e065420740c0340105a2401c21242260030326a00b02070b204c0601d041c0c1e90861955550f580d48140107801c4000702c80f00030450300080d0b1508411381e204540c2000a80c0c40c256510b604452007540310380441552a00150001e0418500020446181380c4180c0548048145820804c42c000d0446050950465483e01000e0300403807402d0084901241c061404001194504450b0601d401c0c01e07941c44a040c420a880c500d00913030720200d40313142030682c159520900d000c030760818600d1610542c0c02c10f0000350703c003080e020801c3c3d80c0311910100b91001624044800d072140002666180030300c5440e0341c00100100f2039000503013450b403000d9811000383c02002c10303c01c1e103d0307071805040d8008500500000301c1e1007200700110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 805794145 1250 805792895 805792931
    0xc14160b010617010e0912030c0903070909080a0804080d06140910050d1e0803090109051e030d090206121603060f0b072004051302040e03041223010f 66
    0x186940c1c00c001281400500c0d2500f44210305103c1e0f00f031001c50010009106007001c0c02982510f01c1c64411913980c03442c10341d0034404140c206184481c06842141400b00f55480203201c1c0190440d000340000c0c0c00d2450080c403c41c2c40c520014001c8440a006225500440b606405039902412241442d0416002c1c01c0007800700c1c0740030041c0100342c85075002100b00855250752100c0451680c01080c5a510104898420b0b4600030112000400700310b000001c001c1c00c2c0c3c806500c4044a24032490a40300050101180c1894410803040e012502e500200002c0d900748200794452003181d44042d0a003030802ca03030308809144160040701c4150a80040d140b0b444007080d41807017028060b02c40c00144800c15414041500564001c041000b444054614141c503401040c411032280d50f450001e0041c403ca00e84510010480142d141c0704074000c1d401c00c0c0071805034030000b000359802d41d140c90809003c400d16a07180c2e240d0100c01e280c020003200c40820114100d8035001e00a44113000c0706000c011416090590080c484 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 805795395 1250 805794145 805794149
    0xf091703010b040b070f0b15190602030331050d090b030705040902090105091e0a0602010e030927041109071d101b151b050901030c14160b01 62
    0x2644010030040c41003007840c105aa040e10600d151443d00c844261925007410100044080c00407100c5404200140d07116044400c0d0a042c02d4616110b20b20b0f01d40a10b00301c0707001f0745c020b00d0090f17081440000c80064110b003010103a1251000800445400b622a0000039024070000303840f01d030803c81d460305205030403e90000c000c1c200610303200e20350f280441b00102140038501900003503e030005109040c5a1142041d601c80c0c03a001400c032601d52814012100c48102c03c10121800799048801c009a054010722900302d0250307403640510300d4010400c0421154820001c01c0405644100c4900c440503040c110546c2c5c4180d108280da124040260003c00c03800b00d0004040504002e4410203d90107194510761240c00150255190f003d0710303200304000d0b520180003580003864107074820000d4003032002841465807c404894010412504021110a403500c0c13041141804242c0030400843c4070f5100b80d02c860300318012441e0040e0b005140c40f402d003543d507102c0000c4a19844101d40304400340702040c820361380 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 805796645 1250 805795395 805795433
    0x1030506011406070b0a0902120312090c0f010801140103021308071a04060f0305061f031a0405010b0a11120f120105010912060e0703051c0206092a0a08010f09 70
    0xb050044c07550b110ba1001000a1084801e00d403540c41000c00c54485403025828414003906580d100c007000140f0003185901120200014491940da00180303003060503034581882410394410700c40da820301903180450601c01c0c8d0414105642003003200400d5444d00502c8028206440251100714500340401402808203131902d003403000100020041c45070044110003100c20030341800304441e131301c80000800002042c64100c145440045c0502c02841d81640309081a91000821003880030000d0140b2049a50034041e03001d401c90100b0442003114090014a5100d410803411030701d020369800d5008a03190004004103850726000308074031058841d180e065070b0241200b0b1800d041305510b4036418203915221580c01a080303540c1d846600180050034031451000e550840c04541e0207a19801030035450300c0c41c3e038040b88010b0113100d021a40400012410303a0301035410b285094122003a10480700506480c12020503444200384c240083c07042000c0c010b003025500c1f0b0040001e1044d085080c824020a083c9180c1c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 805797895 1250 805796645 805796647
    0x30b0123040e1c0306090e030909010e0a02091c05010f1e020a020c281401080703020a1b150b030118032601090b040b010f17100e01030506011406 64
    0x80c664100840606011200031500455503407000d40c01d40341054092096088800c03500c01020844030b030541c10900031205d407200c0c20445030546518040d01c03800360400243c2d02c02000f1004120407054922150303042810740500500d806500400288542a101424020f030082c1c7c407510401c0c130601788a01005004500001d00c040105840700c200403d82c201d940c50502640800c096042d13030301c200051100c081c00070b04940303d01c0001c0c0e00806071008103d04861000100e9540104542c00c0c0501c49000e00c0d1410f0f11806110740740d00a083d0007a4000d0400b100801082103007003009d2440710000c7e0320205015540a41803610f40a500c401540c0340582d84d1030090703050140b4000a1080c0d000791415194143c9001e072a292549122940d207103140c150b514400b14080e0001044010080d40034000d9100708a5041011240c908010750f110008884800c1c04660415022038240001020781075006586884a0743d01c43d4403400341a81549003a0002e41d042d074440342c01401b40d0a4254009000300108a92039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 805799145 1250 805797895 805797929
    0x40c061b050703022101020d060503011b2a0b0a0e07060e03070506130806240a05061e041503050412020304030c06140904090305030907090e1b0d05010213030b01 71
    0x842d5540c00b41e10000303000f0f0700701d880303164a0b441410012981041c1820b00a540c0c1d82c0d00161100c0c040c0c0000c3c0640c0f8400c0d40703069809100c00f144032509001c59000758941041003507403040341920101921000b00707004803207030710103100007000222007a108984240700014000003583c65686843d880b0741140c030a2008001c50176400d9500080d0b00e000300d0300100c520380d907650450030044142e00c00c540e102c10481d10031041840030321122030196005d081c00004002e13840c80d40d0340342040107540c0d85101d07490b0007a4081003c11031040840c640000c04480c4006150b1034560784640d1104c0c0b8103000c2c000e010010356034006003c104101d0381603040c0c220b25144011404c013810368460076200d0400e8403070315042c4400d0300601e08521b40c8000580c1c500e904c0060080050743c54500b800390041d4030444400d15a802082c070046101c102a11658818102c18401000700c601801908542030180c05121940b00c0d480d4034881d00029424001000741142c000d040c68490741c910320f081100410103030070a08a42c2000303c12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 805800395 1250 805799145 805799153
    0x306010b040506030a0e07240e221b0306030510060518091c0503150a030c0504020a1b23030c06150f1504080c0102010e1b0a090203040c061b 62
    0x16202034910407030f010f80c0d4a4407908010700041c00f4170038510890303002d50700b4005405032a90b21040c1d000c4172034a8244010700031510086902081030000d840d40081629150400c1108024110b6446200700d04001040030031b0428035880381600d0850040004d446190500070080240700b17540c11540e0201044c0401d074106000211002440e1a00702c074401d043d03100160048108002620f1040555501490a180e40708030007030041d801200d401446111901004000e420011001c2c01201e40080300100302605140421019621514441c0704200d918511072a90158000440d02030300d1003440e049446517100d040440800e104000b20914070f400c2030040c10711811010900035804003059040510315a4400005030322101004c1120b41c000c489011240c00011040780103000f55101c40c01118400c0c0035050049090f40c00034140c107c3d40d038200c0d0419180300041c2d20040450320200410800c000e503261903032003040760400c035000c0e9620000340b10104103244d00441c102002d500038080c10a9404440c2e22 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 805801645 1250 805800395 805800397
    0xe160909081608120901020a09051917070503070803040918030503160915030501050103151a03061f02030d0f0506030a2307060804050607170a09020d0f080304060b0306010b 76
    0x80304845404030001e0381d0040040000c101d4134a00300041c0c0940c2e80d0300308041312078000d4102d000b44034017081c40d40c80042031515241c014044079000d81c6d91083d1955080c41101c4090742d4481d03030600010301c1120320101300d9a8040c00f400c4043e100c0c0d48002c5031560b260104031015600c100c04071040400c0f4211141000c00d90240440354002c00e9400703801c80d45100c00b20210707000001984041c0c0c6000d0012020140750354180c101c9030485500f40d800b4044640600004034004003e442082440c80b601448800e00c00c5c000c9014540c080001803003000c0203812007c469035401c11010304070380140c1002801c03041c4c2c81094403600543e40503100040001e441c00d50046581c559040001400d81c0c50750054095901d140100c0300800c0058441c1520340c020b0380c07420003030b010f100140c03002c80700c90007444009401c1502c40d195545071400d0a41c03086480d43c5400000ca13009004003d0140e030002411030030807010501d44080d60360010303c9407a5240c0d0340e24180c1814011981d41c0900184607401050041004400002c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 805802895 1250 805801645 805801657
    0x60804122c0117040803060a0e061e0f090405030715020a0f050c0a02040e160e04030903030f1106070518030d02030306060f0d0c031e0912140d0e16090908 68
    0x425505114901070068901c4908025104003000408041004000b41d1502440c010201a03800d041c50b10340b6031280c0840b54404031040c58000b0703044580d0360084c031030600716040b074000d01a0080d10100059008242c44c58001c131010b544a80c4002503e81c100304008622000c1d08a1001c4118105503803004010000e4440030103002c208034001c0740342e50030304401b4018402260b60050042100039090032029881d205e16042040141d2007c120029014a005214a20950b490f5584100490543c0d030103980c0b21269032145820000011001c510030401044074030702854058031055210329030700340b80e05090840c16032654025081490408080390b0000107132604010100c60464890714180303c0c0c1100ca0180015031031901d41071a8104615a80603440b02104038070201955a10051412076103060304d241880042804a124082144241c420505902680301d0007030741a00c2c14002c3e844010a070303540c0ea205200140c1142000b00404000307040d0031401400f00c400c0c103000d405216240c00646000704 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 805804145 1250 805802895 805802957
    0x111204030b070e04050403030b040b090c0d0203190e0c12031c02030a1104030b0114060711012312060109081609050408041509090f02250501021306080412 68
    0x480041604980220400e441c40f10300640704100f685064180200034080701c1034503034040c41c981200c049040c02e00c91801c03880745080c01034152600e90120040e500075031000b045526040c1e03006040d40c03440e0380640147c0b1021040c3c50020300c00c0d07120301401c10140907120104030040d03a00401010380c10031a003850700100201c48400c010b0f00c0c0c0c0c0d40c032a802c202400c40d0f41e4068410910000b40401080004920301b810f8810240b403c4403440311550601480d0300c00c009014042c0d00848500c0c41c1698400e170444601c149c508101100725500200c5521100d03000010010100800d290810109580c001e94510051011400a043e1740d046006100c0e00401c007030082c2803942d9291000a01400580c0301194010040c903800000b0000b05010001e00e10075490240c1c1c0b00980c10b110040c4401c03800c0d80281c65148080420307200c90300e8001641c42c54024524030003155295024840c603100300850182d8400206117940f40d00001d45450310302000c80c0c003800082c81c3c0c18082c0c200e903c902c816846403071b4000f080b049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 805805395 1250 805804145 805804163
    0x50a060905220309082d0706020a0605040203030f0c0d081f0303140714060a0605041a040f0e010f09030e09090a030809120415030c0e010219020a080613020111120403 73
    0x41030034215940e80d110741100110307204d0100b01c1410a618011142850700d01c1800420786e0307100900c0c900741c80308031911034880164008101e02000c280d0680c40b25801500c000c08582c602402d56081b42c3d026044004401c9241c1c000805021a051704559941c0c0c0c070100481c0224038691403028015401e0050b4000502040a485003640c110705c2d080003110305892300807440f2030712440c03496208e5945000071101080700034101000019141002d0041a1600812145003100f801c1d80700c0602009204034900c43c8400ca840b404000c0c403058007031088880f00200301d000404c22048908014101001e032200c018010113002c0100600d03880c0214841c0105580342c985104507803140001c2c24035003050049840301034800002c00044140a05041d0309806415450030300a0b0009003e0984509036000d1419016801400b4281c1442c0304205500300d50f944000d10f03072070001d612082203514100c0304803648541100d2054040003903603044504031890307519038001084440300c40505e810980c0110700c4014681c0340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 805806645 1250 805805395 805805461
    0x902090406090207060615090b030c0c01021905091801050f0d080d020c0a0210030c09090e07240315030302070303081509090c040e0f1207060608070306050a060905 72
    0x388981005005041c0c00d10150b44941d020709040c070060080780710b00e24a05c000303032140e0082a40225044001c442c20840c043d0f0455850040d01707420396000d0101c071022075500700013140c040c10010030b81c028800c82a5030b486031a003143c0024015985417001000c1d40004840c80104010751350030400303040f0b5140540d41580103204610303024056000e901a8000b119002007411018041c000680081d068021542ca09102c0d41154003603085800302c1c104007000039503e16052103130031641d410182e0302d54101012950841d0740e6244980d041250014030480401c0356456400c01107034036015070383e0324020a00168618610b150b902950b580b0503803100800303000040c4000381c43c1c0303040d4040441c00502d000c0e0114055107080b0078605d0322824000f022078030540c50144100822500002c44d602c800c0c1c0356000401248001c0940300200382c01040d81181c0058441d07501181c2d0340c01c24011000110300c62100031805081c01209001a5285a004518032a15150401842c1c0114141da03070f11499041a114034042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 805807895 1250 805806645 805806649
    0x5040e030f09040603300e0d0b040203030d0603030314010b0a0f030504020a26120307090b0f1e040f0e0f180c0a080a0b09010509151503010f090525090209 68
    0x42003550001c1d0000412114403081b2044580400c0b540c6d94101034070f00c02125640c50203844a281310103030a60007000202d4140d0009c0c0b91540c0064101e80010112800c009203056010103581e1180c01c110002a2102c000da00311810203101507025064440400d4144000c0c51001400300291107421405c0580f142c01040c15900c80e122000082c084021404403400c8a41c00c3d100a030400c15188018588121080301c80f281c2c408205aa0041155907104000c032491300000c0d4101d50080c003007003454114100702a016500d841400c0c0700c048021480900c0d03e95150040c4500121110350207107401080700300800440d42d11083c10258060015110010b8070b0300d0301d043c41c516104900100d41d40110f01100040b07105803000482c07a1065101d030179050255950700a2407400d030303070301a038008030148d0002e900d0707804214000c000640d02ca155420083c010100d1400040e080d00d04200840e81070503a41d8444405000c0141314080d070621180c0410107182c074412001c45002103072441a14003840c0e020030100701c0b41d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 805809145 1250 805807895 805807901
    0x50603270c2805060a050a0e01030e06280213051203280201090506040b01090f02040f03081b01050f07090b13060318020303131d010806071b05030a170105040e030f0904 74
    0x3e003101600e0503440e00344002015005600c0302c0c0e080c02c0072401c121280071496100b40a8103074810303280740c0600259202c0c003030400200144403903520400712104486505103003180c0f002c0c0400541d241d602c448003a151105020080100e00c0d031082503a0410440085401c2242026080c0c03480d0b0700c04107208500181d10700300d0040003084001025030040741c0c00c0c4028444000320380d84c1600c500c4c01e820002c000008114808038031451203294400c0303040c000300700302040001c40907000700b84100346560001e02e406c0644034215002110000c452070342007030070300441580c001c0768403000e022064116440c20b0004441f001c0c0c500024410401059100c081d03000306542c0040300e0000565015044a4607015007040d0302030108161300520403031280080e03450500400c00c0030240d0498030101d02030a0b1343e403a0450101d604410074103421b082c0e06540400d030000a101000108066030b00c5544940700221002d0035403a810300103038455441982010151150148044204c13001d91688009480d0760b2047c59002c40c011f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 805810395 1250 805809145 805809149
    0x27050f060910020d02060c040513150510050703081003024603050c1005121b0f18010305011809142e15030210020106050603270c28 58
    0xb03900b03588281e10382a000141509010f89070303001d03a8926a612401413803280501d02c00e040c0e215020f007c804902d42002c0d840303070100b20810602c58800d103888102080070b10038480d04400001e14005803407802d01d079200c2e040ba03030005a00402d00105a20b03580001e04c415030f070900c0c40341142c080c4045013810280e84082c511203032001d11280c10f488004407040c040310200540320a903440c2c015010340050a00d0224201811a2034a84525003002c1c00480c081c25003c01c000c094060801000c00f00c1c2e07921380c042030007800f03007913800c0c200b041d9541400100079440b00314804e034a2810701d030500b00140300c0b074840902041001c0600100004800042e42441500c00d003040f24461040d0240000d5540e0890039043c00824000c0403142451b400380c4488459011a02000140c01c080c3c1c1c1024000e20062620b111450302c078481074400420a0b07030306c50000800079441501c0c0d802c03001241d81c82041c0400020040382c500345030000064a2552280341c0071400915071050403010510641d056900c118910440100c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 805811645 1250 805810395 805810399
    0x60b0a0b0712020606223b0f010c08180a15050601200714011209030906020f0c0d1101022104081b0306040f14060f0403090e1612020918040327050f0609 67
    0xc1fa08102c0c081520b0503003c02c000036800d802880c2201c4807400050042c1e80f520040e035510a00e01e980e83c24081c0c07030028211507507040c442c05043c80c03410106a4030707103e1080c1d4082d100e81c00101801d00d1400900700c042c650120400000d40b643c6d8084200501050080c00c49450b0550081600d0300100121400c00c174152040350410f28004424042c50f5204c0c1958045d80c80d241c080795040c45070b030390107607076606541465145c0c481d5005181400146441c40030141603401801140d511040c803042d91440021100b82c1c802d16020007003030400c44000c0c1004a0754003018901c207404512105500402e0300c0d001c00620290800c0d081e04400c0042042c0d440300c0003420452602a00c03031070300300507100d5005800e00f500e081d000208048000f007800081a0310315809895031042c070801800200744107980c0d045054480c03142c1c0350b500b446041503d4807030b205c882a4805000d00c04007183e1410746006010541d040080c030105403401050b0000b0b04416207040c60542d4000c40c0c07a41c0001d080700c3c00240e0347c0d01c180040c4903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 805812895 1250 805811645 805811711
    0x260709030203030d09060b030f1b210a060f111b030c070806071e0203030402010305040302120705100c02010b012a060e06040309050616060b0a0b071202060622 70
    0x188141e040342d02007008140310361b4090040c0701c24074042540e113450380840030b10107800031410124194801d0f8840c0c031400360007500f103460800c225503002c00c890750800010310301500507008203410801c2d10303c41da0300441c908101c00c01c4624403601615101c4d0041032101920b404100f4030052128004005840702e0159881c02c0f2048661600e4402d61a20780035209000030a04800c0384002404210800d886102c125038015030466485400440290001500c20b82c04d500600700d1000d000d20542c0010400c0c1070180c8002e1100c05901c0e134820044940f03185000e021649407421240f0660707403100c041d502d0151100c070321088550202003003100c220075000004016910748210305048400125015100d18000c0d214208840d50342c0c014889a0f11a807402c2c050718000d100000c50004410303138440030344260083c05119820362501144035031035205010603181440748000810026070704002141c0e00204c1aa24109808040b4849020880b81c00c0c00d0160304688410990030000b680300035243c103c04c0107080e00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 805814145 1250 805812895 805812907
    0x50c0a060c09060e0405130326280b010504290406081906140103150e040506010e07110d0305040201032408070608090c040b030a0f03020705040c26070903020303 71
    0x6004101640300d02c0021074401c2c9960840c52405c0d1141a1090009a0015001c0f220700d035001c85d12400403405100e0412548518103208214014100d03205090b41000480c841c41d40f64001d2081b400c1c51200305004d00d080524885051743c0c0082034804030351242c2c3c80440c503a03a00d804038046516103c220a08841c4002c600014016030006c01340740603980341d0204100c1d08000c0d0040105555150140c1400d410041c800b142c1e155200780c1c8080c7c4002d1a04e01e40d0079203c0d48a0340540d420311000d07a4240c0e045d82c060001800161020299140c10000710f04060800e0800e51103101e840b8041981640203040e5594001019a4040c0d000032001440c0704207286806007403c07000c803044d110340303000307440191103165000706915002d40c5e41d0300d006400c00d00c000c09d84070f181441000041c1500b04209509801442e5610300020752200c090314040b403294004d461b4075401c0200b4403088440c7c0c00032000412a011207584000007120f03000d440201e0b22071034900030075a034060081c6d442540c9648001e405103c0041c030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 805815395 1250 805814145 805814147
    0x390d050316021008040f11030705030a080d050906221a0405160b18060f070f0605011505040302100f051b0313050604080706030b0d0b0703092105040501050c0a060c 72
    0x140c84103540308440d40011050322000481e14901c4c200d4004203002d4982ca80c0d078011a0751240b40303000c0080003c048500e05130300d403c0032908180842c80700311070000c8007062851150101e80541c1ea0310a031440c0c000d14081c503020381d41c100c0f15424105014021514441132106014881110610751b0521180c1e01c40302d4141880d109a880141008510907040c1c029004207004c1c2511044814032424407026241c441c61480412581e03602810405440080030441000000c0010550459141c0584e0340024590b140c0342140c801403900c2072880040210400c010300040e0341e14a4440054205461b03c04041c04140c00d05469a20a4145004001c4030454550414101c00001070100002e00390118143c1c541e00e0090003420b0085004126880e0058030081c0680c600c258401c1801140c011700f5110441d655071139800ca80f140a030b032042c000070380354041201070000c0d4114042c6c0c401c00c41c507240c220107600345000915a005a01400f4100103001400026200c0200280005160401c204000c4000c0090b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 805816645 1250 805815395 805815427
    0x1030902120c10090b0906161a09060f010b030a0c090e16110d0e0d0309120c031a060619020a0501060b040e0c0a0203041a07060e0d02390d0503 63
    0x10300d60344500e075907841c4500f0191003160f092040301c444008240c10900300c0c500300300c050b40000d01100801c02958030500040b40c0702d0320201803181d25038a044071090402ea1501400d003200100031902020121004000180134442102d0b80040d40000c001004401d0300801c9500d070ba802e0f4441c2042030300310030900a2081c401001070840614a4031103010a92200e4115074407164011842008a0a207003031701441e5041010214080c68846d01d0700c0009a516403050f1042c00b400402c00340c49510209000303004124890041030000c041040081f4030360318184001a54a115125400b55000f01c95140803c0a500801107507000c560300c07400a00409855071050380d2241c0052003019039500404004c40c2010f20120220f90303624a403540038501c1d190414002d12052101a000302c4104071081107000b0101e03695108496000700420068039031003880910003880c00d00003001c840030358060300f000d00703060750300103d40b0000c3d4503039844402e62080c8030a0001041e81360349840180c0140030019000e1105040740c5c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 805817895 1250 805816645 805816663
    0x3051b0708030d0f05010302062b0c02011b0503100302060f120c0d0b0105030c0301030b06280920192c09070c1a0415150504050604050915060103090212 67
    0x50010401d640c3c801342050141d079004c3c44042c7d0082c03402c126200c88e5030940c40c40c1a004100741c00c021b26a89900d90440400c640745800d006005035500d94601c031700682d0034040d6080340c1d002c51515509605040700681009801403000074400e400005411301c440740420262059043d40b14028001403500c1d41018909034405801a22110f20308802e245040d030140c0103aa005045651100b400c6a081d55108103952a010303000340d074032031401c0703000111014044404001c0030079881081040c0324030300210078003650310300900c186409000c0f0001e150300e0105907041d202c40b511481d1a501d9401003040302503a0940042961040860382c2a900c041d8014030241401c0c2802d10580710240e259461a104540308080c20500800d034003928494501c000c0d103000c1d04150090f00640e8940114a90340d51038004890004c0a000c6100300c0c0300c0f030204400d203003d1003503580c0a42c0a550a024501d8102c010321b0f2100003615401c801500104045446644203030f00181c0980c0e80600724026100903c24990f41d40e00b410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 805819145 1250 805817895 805817917
    0x31305070815100e13150b10120506062502060706020417100c0c060504050c06031e060d03020c012703061a0103200a1e050901091d0403051b070803 65
    0x78030303502c2c0d00007501d10031841c1c2c502031090540309079038800c1400c041c44040ba812644451840c0210307a100b01c4144044070540e00e40300d22060089c4c0c418800d449000301400c0c452241401404040281d110000c1c02c1c0c5518040000d04045036440041c045010742900900b0f40783c13011501042c0000c6031441100c81d840e55004030b500302c1814421440680b86042c141c900040d40c901000e00000305103801041c1c000c1d100700b080d03130004011a401b240c6607420440f400c0110301041008a01c40e14110822182c1041041c0d4040700c0e2031059440c040d598450030f04102e4100444218280b401c0c2c4810742280300c840e20034040031080e41d592410440050b0440c2131035040e0344042807445024642c000e1061680e40c00c4d000c460740300507151004c5c014100744c002d40200e4061001b5030660f80303da00c0f00340c104030600c40d03150340700c0c5610f601d400400141907007002e410000c1f05007800c814030b8414a14442c082c0f50b1041d458981103582d80d029513501645001c2c00d11549031103228038034001c40c001d200480a002c01c2c4202c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 805820395 1250 805819145 805819171
    0x30f070c08060c0301270f090b160509091609120602030f01090b1311070f0b041208071e20060f0c04030f0209060105090d0b04021503010803031305070815 68
    0x3880c820390f0350503c800c2c0314107100c034601d1007241168080d90f04001403894104500c0003031700700100140142614050700b000c45c4c50058030390810055800d508407581410340c1c54601181040d0280b00464031140028088030f9041801c82841c20481d4450441180540031006610301c4a50302807401030040e4005443d01e110540c0d0001c008102c00348107105122000f28000e1441e0200d213141d0450400503c1001654114420204241e10104c3c0d0102c401c4034907503220341440a424a083c0c100722214103040c060b14000c0041c14014403041e9540a03036207464222107250b8980380240031480945890149141c13480e81440c11500c1643c01d81400300714140300d01030420f0404c610740d9458070400c0c800e1141b804010702c07560414064601504051980652211060500d0391030103081d100003c3c91074001c04800c48405820008000843c10207032416664081501402c600f1941401c28075a22400300511030050200843c0745c810030701100300509002040140d080c0e60038034025801065440c0c104440784001424 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 805821645 1250 805820395 805820401
    0xe130b0607200f0310050405030f0408150919140c040e0105150a1508061801080a030212160f0c2102040e0a02030a080c070918050606090403020303060111030f070c0806 74
    0x3490f54086641c0703240140a003170f5a00207040c5944c010301d400340c01030755588030a200b007c107884180b40050028140b035500070700000e4070480500ea50700c60018480042d030740003052205005c0c80d0034000000d071294001ca090703004c54110500140b401c58600100f9a0080c203268101d41514019406103000754210743c18220500d203e07409100b850310380d0f886034000010040b42d842c410300380305002e140e410040c000c007128141c80a4081c1031001388000c0c0c11410341500700c65403800400d501000301c000240c00002d1000d0400140110a03030b02e81036028005040c10710001080010000000e00003001707048405c00182d48075481c01d03c0310a030b0034080c680807030089103400d458034203080000451488843d401002411003444590300d03560746400000140031548111000440d000780d085c001c052103801825010310390238030385003080c42c6002005080903000701c400300103000101b0f0740801220351101d001c2c00c1c10b41c020610807580d00c1c514840c0b043e42e00e40c21a40032504038100912203102c0400c480d104000c4034034030b031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 805822895 1250 805821645 805821649
    0x7030210141e0403052b020a030e1b100309020d050105091b0402040812070305072001080a1e05100e040f0218090a021c08070f060c050a0e130b060720 66
    0x240b06a4014000c04d4050145640400d04000d4915421441180e1001840c40d00c00c0148140d0b0004018040801d8031070080806080c401c004d00b46001032040907191640c0f82c204040b5000d49076a03250f4104250f2503022940a41d100d2100244050364803000811a03858818541c6840740020000c2106d0014100b580b41c000e0329042c02a00c0903a03616501510400303d00c21035540075548a00c030114288407041c0b12440124400c008805403105020000701a03151015000512821006201c4020b40f03280103100b02d42006d0700d070b0520080c9140e120380041c864913290300c20083e040c2e40b980102d48142014003080100141c0c6003000107124030039500302ca45000e01490844403541d0480e1840030591004101d0b038050f00d001401c0c2200451040310035200d088194448540a921101050300e00001c103481600070000340384200a40c41003985020341c204080100028511110280068811168241003941e2078210350301c40070400400401c038a5580007036285c4240c0101f590503489017140380d81c0b41c22000d14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 805824145 1250 805822895 805822951
    0x207080f0705040902010c150203061c081903020c011d16032a0b1216030608073b0412020703022805060c0a11180402060703021014 58
    0x3440e0080140c003605040800340401008032070026410449003200400c0402c44542e40e84e0360103070741c0c11000350303a0345400750030300204840c52880c4030240c96a0802003804070701920155030100070b01006580341d81c0131041d011006402402c40c95803c652078500c682c00c180d5035858002a03030036280d42c2520038241501d1a9034640c040644000b80008088a103007000b18041c000d0340d600c145a800f00a0b080c019124001c4605e03e0b0400d001c20300140c81208203000b4002c080075600e14015003540750900240d41885e090702c1d102c0c0310620501c20104520b1340c02550303400da41031082100c92041c43c580038001030311948000040303005440aa031402e4081101c05100b80c808100c0009a80d00a0148440044c0907001070340f91801080c40d82c0a2071803201c0b0041107980d90517000386110101000140300102c00350034001c0c805162800414812001400100149034018403540c0d0b000780c040f01d00c1c50f1129450f0a0aa0404080390b407801280c906c0d0040390b8408465180c415806000200ea250b201400d81c0c59500c484 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 805825395 1250 805824145 805824163
    0x1008070b041d10060c05250e160e130b06030f060a120807020d020f0d08031b13031403120106092103020a02040b04090b0c070b07050a1d010302070f05060403020708 72
    0x1203c50a80140441030080c0c0381c01542c9441902101c000340550181010003040320710b8241240c0c1d20041080041c42c09403403045070440e614940c132000310320784c006025244000e541005405510415144444003070903a000c0310302d07803030007520144d504e01c2c02c010f12130501081200da03184100761114001ca05006200b06100800ba031041d890307840c01442d5020801d4448202c4801c03a840380b041d1128505907210041c088524503c9a492a030301c038203040d1001960415030303c42d10320f0014014031440c507680c4502c1750798204880c1c00040d051313105415820110305500c9032030300b40d031441042900000ba030300d54802000c508442500e8500f01c7c1c0380009050310308406205680260050340840b03200d0700541f03002d60025400950007000021070240d25940ca040040b01110b00d41002c2c4004a25002808185441140cbc000c03218035019151048168029040c0703551110743c1e003040c1451035000d001c641d003e541151641900403c0c943d281c50300c04d10b440303a41c440c07049504030014007446000240c103503030000b40c0d481 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 805826645 1250 805825395 805825411
    0x3002041d01230f040b190e060607031e051308060712050705030a0e010e0a0308180105040c0e0408040b070807020114030606070605130f0506010e070c020a0303081008070b041d 77
    0x2a040c4442c2c0c08120700c0600d4800403c1e07105503160301c0310b00540e0b15141c0306802503000080ba484003a2030b000904429500041c00300c0d000702d000b045000c0000394810740882c3c2001000100b403c3c040000c000403074031800365410101da41032a0b003002080b1aa0001201c52017180295107008040c030b520110507003a0703141941c1a1001ca0024404aa80c420007904040d8003106160000156030841c910801c1c40e100540d4003d40124040070103000b21108116800035070410003000902c01c50a290352000821000751280d040302d111824040380c05c02913007200711401005003143c0c013502d4404900f06074078941d104210483c0070944c0c072000da103494800c0b602901e201c0d0100401d03080c00c160a80d101c0c18042d010082030058007584a400c5640014240381d0920010380c0144001d242642c188546c0e1920310001a00c2c072000c1c405850300c0400107a481c000e0003015650302d485d184c0200d0311043c0c5840c0a01581d0340210400d8082c554000ca035425070f6002920440750650342d0b982d29000040000046020140e82c500c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 805827895 1250 805826645 805826699
    0x31911121f06260109052a04050403020a0816053306010801090f0204051003020909130503160201180e0a2f1e1c1a013002041d01 57
    0x1040d10039041da03c603070b40d014120300220704202569507072414006080141001c20309001a401c804d00710307209190410340000d40b0104040e042c10388003e1750320180c0d008001c10400c2c00003251400800e10001c4401000c2d8030400b01c42000c00c090254240c6c50b010303000d05940c8866a11a003140182c0c00c818820701a01d4181c440b000c071070f400c040381034000c1c0c0500b05040070050317000c010000300e945442d50152004403045e580180c5900091013000b411030400341c00141513000f22546040031800110031106030350524030840c0c100d68064030041c7c5004030061004c242c0c5c00130a58000031b60280b003070001032141404400410103006c600c40c2162204207945030340c100f6a9400141c55590005a0700246003c0056010350342041321640e038403d40c943d2154858201c2e01e001c8007400d24131510180a02580c07901c52000311116071040e040000d10144900e420140b00802c00e40544a009040d0000c3c0d00c040440800d041d5511600d44c0002118022407520f24403114108100001b0165946d9642802d2f1150482401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 805829145 1250 805827895 805827929
    0x3030b0d0b04120201230601020c0108070f051806030a1a0d0312020c0327090609070c06050415020d0204080601060503040308010b0901092102040c030506031911121f06 74
    0x507184803241400c8842550b46c0c81d10401c01507100000c105900c804020360740780c228a0300100090810340720070480e5041c0900c0c5411b1081a03608104500c0001d20145030454880c03052403648804800c0c1c07444003582000c000401e001b444030041d0410758008503a94500640d40460301e09106415082c0385015000403803180c05d800103420300d500106690b44000048a00341011243d18012059401c03404e441c00c00060329016186003801185c0961040e003c81c4c00341964501340d00060580071041c80c2c0100303126a124001004c1180980500320088410001152143c0c6034002c0c401c020340c41070203003526a20941c400000c0c650300c0703041284c1c8102d40c90350354019039074a0001201d00c960486420941441407144012411090a40c0e58214180181e044039001d800380b0700610088541d8003502d9400c05013040104155910005803411452882d111014400705807410a1102c00e01e40d082c4103603104078014244030b40c440300054034820880074a000d110100d0348440224040394840c1c401d820b01421040c6031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 805830395 1250 805829145 805829153
    0x1305120c130b031c08010803030f060d020d06020d02120a201305091e06040b01020718020906030901050103031b1203051f150e0312070b0c070b010806010303030b0d0b04 74
    0x400c0c103000d81d540c90108001c0c200c0b600090802410300418240400d5690010700d40d1688140194014600700019500d14140003080040c0f282c0010705460240004500c0c81c1c0840d125042c038403100682201085444020341010301d0080d50040d1078001c18021070001141c441030b00c0384a141c90280040c100d64031662a49401021103070814616100ea811401304001ba143c0c075919800b603c5600445c0580e03a0300d0300755030844da5a9210240020b806140740100d0000581d0300010010309903a00d0300039015410440000382c070f0103403264030b500640002e0048203002d040c0c801500014182c030b100b80c0b41e5040ea090100005d0f0601c1120f42c60141540e1840304040340e40394026840303503401c0300c940a170001806404406404200d04c041d0700000c031201115049940641c2c0c00304100b02341c004210007900c00106400d0511420740162076014010403445004030766030f87d0508084609055000e004d02180390b07546c070100c2e0740b6400248410f5020034104021309015141846d03114081a9118403088020b84994603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 805831645 1250 805830395 805830409
    0x4050405031b010f05011223011104030c05011106070903060b0d02090709261c02160806220803070818030427050c040b03040312111305120c 62
    0x4026145070004002c40300074940345440d500814000b070030010079980c240c001d000d4102c40e016485840b4410300380c061140000c0d001800c124042072041044034008108042440c010452492020400100040d0000411001f02c010344100c540907220803416055041950742c69420840d200c200142c9070361014800140e2030381c040700c0c1c1d4100c042c041c0d4000151a9007c5030a11105581401c042540c0300c0e000c10a420341c65642980c109034422500c0c2e0000303008440c0c996030f4001c1070101003c43c04900030381d0040620070403459629000201084501c00d541c1e1b012191a00c4054070f1035030038000350008043c1c2881c450314161100d5a8064003407450342c0d0341c1040c11200010080d0030600c0c0003010003803550701042c1c1003001d00050224001030005444d00d030703a01d10140214101c10707400454180030130001044502d900703540844900d0352090350b49a54500c0c084902c20b04890072241580d15140c12200070020389070141481d51240381d042d4421944500402c1018541c4000000503a0701c05400c0c0c038050705144c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 805832895 1250 805831645 805831651
    0x60503010614210123011115060d0c030c0312020c01090902090103060e011806080f0a03140d0219030f06050603130c03080f07021c030e064803040509060405 69
    0x4070340280c0c0800f46221040300c000081e80800d240b040300b08515100e0b4051602ea07620100350074204005c8011540302d5103612a0440e00540c01d0350044080002c01c01e071242d034140708100f98004204070202c0c2e1245040c41e5104950b000507640a1051881301c80d00500004440d28030810507180c0b0305a01e131601e4a00006076000c008407038105521441b0010386419005109400303003510500319100403809114060031a1081d91102030907501c03045e085002c0a00205454130519054505070a04120007420601244100400e141d24144005021000c0c0e0800381c0c412004811a0369082c41581100216003040e554540105540408200b02051915116205108699216101e50061141d0b00c1c1c0700d818003900f04040510354050005446411494078000000700a40703070703000103000614503483c01803851440d9111103005044c00100072201006070750341581c1010301d80384135100d007510f842e045d0798404401d002a10440326800d170081a40100101c00d440a541018052240396540d0300d0411000e01005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 805834145 1250 805832895 805832917
    0x3140f04140604050c01120b0f0d08040b0a051b0d080f0a0902120604031b0507030807080f0c010e0706170f070512070c11091303030b06040f0618060503010614 70
    0x2155034011040060000b94401e50203440a40707501042c1c000054840c0c07c03949080d4104524119030361b2169907070b90903034010001d070550348043c42c00c00030314100b035451140760060280c0c0d0034045640c01c06c4a03803040050621400ca082aa540300280058040c0e440c0301401c49640420382d060300188107405020010382d8008121071000c0380590880e004140c0e4401c025600d0380160f040542044103254015081442c3d010305c1c03101110350f015107070319403d880c2d40d02400010314081000a080d0103000c18003043d074000068502c01e0560391940f2a1a542c002c14403143d0a0050740100800040d002d40650a10485007400001c01480d5580c2d83c80c10921504d8003c14010600406000d00e04807008210940d500c103840c40d490b401d80b0014075041c016482004143c41d1441910110204012142c480b0f10741092282d16007008030700003003034030001072a500132070700011940008a0800140316034000290f14858002d017043d040910f40781c91007225644424040c800100e218100c60f500014450710081000c5000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 805835395 1250 805834145 805834163
    0x81e0c1002160e01082e021606020c031c02090f01200307050d0801050316090b040605120307061107020f06031b1b0115060e0d0f050607051903140f04 66
    0x50541c0340b520110094010140d1850141c0041c4000e1604000c060500c40490003a0b81c1c408810683d019400721340d0503106096560007082c00310042c10f04140c0c41c0c2140d82d006200355200c04400010507541e8102506803806030800f02c5004c507d406452007200c82e80000030740381500b031031404401541c0c0900d0700c04d81d081028140c4218900a000d007400a030100901c104050300316003001510007400904184c104501c81e410881485140440340d00b0084200d6400ca8004540054080300060050186031711058204070405460070100202100504d40d90f44550340420100d008188404000d0240c18802900400f114003100c80f9454920040c40d4000502c2c00715000d80456070448200e903421400b0007141d003000e4019000c41000003801010450400d902c000051a4500b40b4010301c00306c200d4940070300038079490074100240140c0788003c201d0950010219140e034100400020043c4c0c0c80482e2080181a0380050748006500c40d00030303090f8084940b85800c3c003d84920f4550111203401410884071068 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 805836645 1250 805835395 805835413
    0x10e030609010c021b060304060507051c0501080d0c0203031e07051006030c0504051006030e121207031401080709020f39030a0c080c25081e0c1002 65
    0x60204200c6104401040010070324044041000c0c0c60000034031490b641d15000c0ca504090b980d1104400e5a0b40242c0012003c503c0d511900b206454511400030b4200c0449801060706c071361071180380c000b90b04848058080b243c40c218140c3e0107d9190a00d220000d51503001089552411504103a0101e405652040310030300e04030103903690a00d010070703c0c00310000441d00da007010000d10060401c61070040c40e00340d80030300c080d20b498040c1110702e22a50260009045e82da051003110444108540000001c80034144d55884200d0110018000300803a501030001e400c0c01d00a50702da0400f20b031168100d035880d400904480b4140950a4042c0d0007460b00344074030b0f000502c250506030f000303504202c0700c1405544444940464041c1070b01c014200141230081107610400018614175801300b00c0c0102103802068403a21209000307200350a042d4114180c06410060307444a2805c41c4274683c11004a0340700108880b801c040c201c0380c0000801300441e103441d40b81c01044910b941c03400c042c04040c00205582c07060790f031111 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 805837895 1250 805836645 805836649
    0x60207060f1b11120d08070804050616210617010b09010b032203050901020d0306150c0204150b181c02010509300609060124120c1713020f040b010e 65
    0x83d020801c00f20704d41e000008188150342c20030702054100f0030910301071895250a494007079950361f010b0106082d8841c01c4504030300c020703c02c2d1001e11501040e00d248100c0150742d6000900900441e00030804d148410403a03403006118140f00320b901c0d050028049000310780c85c0240451460300018003400a240c00032101005002038400c2003502c6502c20b0f112541c40c0d11280c4002441c01c018084c1702410b141c50802d00744803400ac4007802140c0c0034410f00d0072000824041c404036000e0001c8884142001e5400000890240020006080040401e811011840201d58200100c40506000504500c642c84900d400554401d9000380190000540f0a41d15250312200919200424000910768982035044001e4a00c01c18018075412000e030a00034030407541000300559000e00b8409108005001441c082e1061a0003100300c2420302002e03083c1040240f040010140c24402603130505941c1c114043c000404c40205445400302e02034000d440200700c80040d10078480207100c400015410703c5040c13007060b6516 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 805839145 1250 805837895 805837909
    0xc010f06030b10030b0a020702011116051309030e061612020d090f0302031005070909091112011b03020c0a06090602091014091003090b0405010501060207060f1b11 72
    0x400462840010440e15504042901c600042c240c0390a9943d44402040400d58002e080f9412a00300303040140c0d11a01c0d44010f039510040003101802c5070040342d10803c600611503501070121041910a01d400c1010889100200c40940c40300034041048412881ca441c00c10300c015180100808044000240d901d445000340c0e8400b844203400140d0000b4006d401c403070780c8040c0f020001d0000100508120341540d0011b512503071031144000751160b548001941a070320629802d0300074034090508000201d82400e02c491040b00e0b0400c018011150b04400806911052040c011044440c420f01c00d02c04100c2e0130b040b400380d0300040134012035124000710b00c804203149200c4c25401a204010040c1d68070280401c2c800082c403483d404000b8000b00781030855124080c1c2007110b009400c02c980c0070700c4800b003440043d4020002070350f0180503c801c140c200001c0020551181e8182d44c4217400702d0b854241d90f07840c103e0758241400025000030b1800c0002000840d0210020b0740d0032841000d41100014200300400c4203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 805840395 1250 805839145 805839161
    0xf100504150f320a02160f0303060303031a221b02010b0a0608041e081e27031504062d0c020a0c05060c1c05040801051e1b0c01 56
    0x340b5900d1078a1070241007241c25040d8103900003ca80030b600400d4000e51050200018044640e075500040d0708400001494804000a54402c40c8441409a50f05008000303003038500080340403d00e010400032413848405107042d007000c00103211080005440545003549580e1808540032980c0340e24141c008008540e0282c0e0000096038000078040304a0b204108584100d580325906016141050201107240782d4480c00082d01981c00c0295142038614150a0038400c3d01e4000c2d04502075540740c101c0b9035640c0c000800c00706064001400040c0407041c081595681c0d000c0100347d15504c01213002e4144c540c504074565015016000005c7c00d4490300d03840c0750804000e60a2803480c0e40c0d08050b2035202e5400c610840b040d182c0b0610081809010647d1801c00c40e000314002d4600c5171034080f0380000001c0c41040344400452080044410000c00c50030060200d803c07501607280c107942001d0000340b5000030501c8420042003042100e800031303161070784000c0d0004925202a01d102504001000c02000c0901443d4a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 805841645 1250 805840395 805840421
    0x50603040f024e190c0b04030602030609150f04090602091009030309080f031b21090a060302071208130803040803041a1b0903032107030b030f10050415 67
    0x75280c04020a4004182608150b030307414116074441d0403502910014036110313035001d1801d480c003e1168905143c00380c0c5055500043e244100020003100b00080c54000e140680f42c1a075403000e10303880c2c05546d01d07802c2411521068203c5507082a809171450a50440c050f10f80c0203440040c80c00307280a001c18281c2a50301d010001103031035580c0410402da07000d50048000c20030030015081540c80d84541e40d86901c1814909941d0300600d03408940307003c13018442c105d041d284420207030200c21310b118007107410f9801c00404244036003002e09001410320302074000c88600075401407803c8000403007508155444540a403155003144910015000040d903000300035400ba07070103000d02944915061900c0202c060115242036440c10288083c4041e483c40b42143c00c105000b04159552034066590209281d13002d0700d80405103000203050350940f0031f2154107105000f016103070350038844042907006142d0b8408418964803032a82c04401080b01c00f048680c0050f400600c0340f1051000144800d565009035100012611 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 805842895 1250 805841645 805841719
    0x9060d0203010e04050f280212030a11011104262a031006050117150409030e0324150114030a0209030c010905030706030209030c040e0304030c0f050603040f02 70
    0x4400c0c805c04128104140b81080c0007450401035081010980d044042c40b041001d0741241203443c115912503240001c855415400c030380e2100c03c0070a0042640d030315580d040c0081d5182a0250b502d06810104480a032042c0c102003800c040c068042d21500002229140c0400e402981d0384068014040c046e0324141e0101d46000382d05c4900e4a00802d4200005100d503080214035001003044140d8210790103446d0320072f00901900d45aa43c0500110000c600080c1c81c903401454030644504054206030152410729040e011601d02c2b0108601d8900b208a652540240c019400800610744101c0346103101d1145006140c01541040c0403504207410380c0099903146507207600416100740f80d04042007c1c0c01c0307048091914401140c90720011945460b024000e1108050300000c10060340d460400c004401038a02800c00c01c245000009015181c1e08140801c4070760781d1868200090f0880c503901d400c403e554004045500d151600da84408550318001c41c01c980201c5011070124080e110540c4900b0001c1c0031031050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 805844145 1250 805842895 805842901
    0x260607051305031b010e01171303080f1b0c12040f09200d09050715030507020f0d0f0c0f0213020a030b030a0f0609051207030314180a020609060d0203010e 68
    0x60000710607504800d01030340c0b101000d00e075405405140c03131040d42c00a003000c400070701c2100700417038103884191801c000190440c4140442c80d0142c06c00c000040d4001d60b00c0c03412036141e42100e955861002e0321942a02000c2d40c02d40080c50b00c09200030700b003410b85142125240740c14900700a00c0d5801680c061410b214104001304180f400728040c00003401c0c0100040c42e4150810841307103143d80914215032050513540d032101c01c20440704002d41d0014051502030948643d9a951004001e0907044915000502980c4181c0b2188440081c2d038070f20300c079100d44441c00c51049920781151801c040d54401d80760301c041030b10440c1c00742c0c54014020501c403000e0600566a5006c03224040c040d6a10041554001c1d40103140010201c0d21044036200d03040c1e400100400c0241280c00c11500e400700e40c480b1a014414001000420190550f22800710760b100d1801a900a03a074040d8108a0754586501022503034022154000051901030300420250782c0003003966007080340384884e10089800c240c0014a1303d80c00341c0b00b8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 805845395 1250 805844145 805844167
    0x20304081510050f240405030f1c08071e1b03020a0b1b120a02040e09010e0d0f050a030e0102300c04051f0311031e01060f0926060705 59
    0x28002410064804c545142007000c00b0800c950300710407800102640030503a6039140b5200e00c1c00c5070000e060040442e016201c90003040ca80702c501040c41e1900101080d400720807c1401a81024440d82c0d0b07076126000c91010043e1a00d008581c1ca003504010041014103c1058140700403151206c10b000703034011321159216203055070071008040d20722092650b90850250740d03900b001040346c49200000400c07044c00d0f21841d000c0d50190249820521020f01070508114001d1415400001c0c070030a440d04030760110300c56207000da502d89800364450000610030040c2c501014003d4008440104000c0f00051034011500300c1d69010161046090160342c5490400c035002e85103805000ea080250049160b281ca0f2400340001c0740701040c10800ca02c48807000e1031502906000e907100c1542601042c1c0115500d240011082c02107003000b00e403501500c0341010010684511414401c03520070816194440944c1c10900b12040040440c030143c4280300d00741213410240301b001d00c041400b4800a480b40d076218072141207 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 805846645 1250 805845395 805845421
    0x424020d05030c130b0a0f0203130b0c011103040b0a05011a0d0c0c2405060613050d03021f06030201120911120c131b0f020a230a0302061603050603070b0a0203040815 73
    0x11a047c21540140403280c03442070200529021162091005581c036090060480c1c0501095201c407200208040100300c01d012603441d04510813180051b04200300d030713215821403c0e1407809940488204205008416206c5510ba01290b4001e0181c2003a100312642e5139950030b400804841141c030311038510740c0d444480030b0480c01010340140044401a06048040c60315581c8861300388141031142401e9800f40050500900c04105010003410f0200307038401e440740080001e4859444200d0003d102da60f002c6203550054032502c51051351042e03c03000c24003075040810589808220014407507000701624140e50f46d65101c107429802000d04004038180d500c3d00180c00030040301014100030b20030002d5600c5046980410080c1e483c1e540304480107119581d070001500c046001c0e16164106119404116040c0f64000802521500e17084811040d15608100708a041d528207440c400c0d0076520180b002e00203480e030000035084049451040340c1c10180d40d80190f40c60030041c5d01007a421205603405012845103d50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 805847895 1250 805846645 805846667
    0x60b040b01090e0402040903090915150201140f0601030f02120a051305060a11040503031602100e030307230709140a14150102071a0424020d05030c130b0a 68
    0x42449080306180007070b24849407200130802403080d66120030400030140124814005400e01250400140308031001c10207256006004808407040c1082c055400d140c4140900999050b001da4a0b1040740c5845100042614000c2c003003e0615448119882c66100c0b207202a0040f0073700c4001c010014200107003010210b038405043c8404850b2072051110105200040060300680d015400041a07800c80904c0410350103140c100c00da15000015a1200c5403401a80d14070706140201c604683d141400d0f031064584100c0001100e8144d0800d00010707005c035100c9850306620000301c1351141d444016080185041003265000034600760740e40c001089910001c02700c066804011840d0810155000d00800390728848014951080c18201450402c01648203200ba800140b440236050241c2c0201142469a180c010b400f40c9d109070707040c1c90480c040d002400c82021001080580180141d60b114140407210b56200904120710b445042105000354005460040011f1007601603242e2144c10048004002004070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 805849145 1250 805847895 805847897
    0x3070f3510091a130807020a0302130212100602120f0904020f0c070602060c071103100515010305150d12030b030601030f0302011b020d0c0c150503060a060201050106050703051c09060b040b01 84
    0x2003004c220300e00e49000540201140c100086644680c250302c0011a030380c3c003542000350004841c645007041000181c000e4401202c0c00c0508990503a0749a05407400d00c1400e03c9100d006a10039401640d001509600420900059140c032915203040580460b069a10080340d80c4400900040c3c010081c0038140008400ba014500c06004141010381c82007070346014401d03000d80f000155480a8100f60380403c001d829a40c0d030008144011f181804543c0c803029003016007075010074101000600803c41c03d6490402c851001020000300c000141c0341c460307640c20140e0000d03050650b03031030300c0c42d01d1a50100003d41c002d41c417881c401c0000400d01c2c038009082d40e020031303451191407981c004100c0c1a103030003107440300884001d45441c181d4040942400e43e01a51150b0005949071503046c136901e00d80b94084000c6210700402d40d9260711655541d2401c03400c07564244200c0300054002d00110300082d100c2c0004003011080646143c03c0c2c83d172415542c13022103085001c12602c584e43d0340c84000d803504103400f030303503000c1802 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 805850395 1250 805849145 805849193
    0x50d0c1e03031706120604050610050d0b040b060d06060e07090e060f06090f04180b0c040308030601030c0c060c03090b100806041e0b07080603070f351009 68
    0x5140d80203040d00c0b221a0440c0c0c000f841800016205403980110301070070164080440b0400c5c101820701030707181c4a042d10340d820040c90b00c502c00b08103403c2c401d41503140990310403485101c5503101d840e4a414004054925640704c101c00078103601150705405410f01400ba0418103842504149002810030101a448011100d405c24100040e681d0744d8000b00c0a038801c00d48000e81d0300e501640c0041c1c0d0b58040f5110349688645846000008411482583c036402489540b07404840e489031606140d281c05644802486410304000240b5594840e4200e00401040c1d810141c503541800e030b451500361030320241e000000039504d03070210040c40b820509003904449510850116141041c88040d11201c0040000d0f11141490048980e41200c8400c8202c025420206214130741c01c140c04010040d40c015541c1c03c0c40f070300c100c92700403c42290540308a070442e06607850881c0080c015280b0503e00954440030303021800e0081c6c41101183c0c070284101585032401103c002020182890a6041806000d01c40101d201c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 805851645 1250 805850395 805850399
    0x80a060e010602030904090516090615020109020904060905030409020406030c0f090609030b0411041d2803111606050a11191704051c05061305190c050d0c1e 69
    0x83c01004440c3c4416098801040020b05814a41e00d807894000c2001006444540300041480003940644145c9403006c1a07039080001c0700c44100c0c20380b112881e0103580b0125080c0407500152090303100340442e902c11003c3d40e007444c1e034030224081283c005500c10070110380c80e1000f0101c1c072907210204e0703c44100c15080c5005000d00780b60000b042c078039550100506040302c140215040c4542c038140e00c1c4241c3d000410078001c000b01e15140b03680000814030352089074400c01e0042184510983e0101c00a04040c0352800480d01c607584044035170700035001c030400160184501280701045040540000341909031681907603803440c03801c0240741d54500d10000306640c0104200844ca181c1a081c0183e915030022610840841403040c00c100c148500d62010740e01c01003041042c10f0700400136144402c0745000e802a1006545c9110040d4004050000003c1180d08550b58030741c9405401c0321100265401040480c401c0340d1a00081201442c40070010780b0001c3c0c80c0032041050348001801c52150900d80c03c6c80301c20700340c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 805852895 1250 805851645 805851647
    0x50408010b1f0509010507050307110316030f062a090503122109100207150e0313050603101205030306190b25020310090204060504060501020606091008060403080a060e0106 76
    0x14540410715081210004c0e80000c1c9a20400954000d15007040c10b4907601c0819181c00344005031040900d500a000e83c500303501c1c2c0c00760301d03d42c0041200d0308020b0b10781d0f031519656030ba9030081034901e00c0b21030100d00d1232051070f1500704240070500341a819511605446400d19041602d0500c0040d00600d544c0c4042200516001c0b40320851540710022802201844c0c90318a181400c04003036600764801c0600c0403554000b030011818a00f074801074840c81c2000b201e12a00c006507100e210303180000c445e80c1c2d00480108501c3c20603900550784800d40e131440e40e51103034039415419402d00640c0e100fa07030658004020300142d03140070565648010910007140041506e498400d0701c0c18010f50361403070003034402d007007625803e809486001c0114941c01000e680c070394032000700600010302ca03001c4164082c5c0d181c01004226810203100368010740700140c000701115691041084200c4800170034081060304030042c0010141010000540a40c0c82525142241d1602c00d4440003183c2c07640d84208407006008004001032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 805854145 1250 805852895 805852939
    0x705100c060b010e030312072a0b060a08030c0c18010806070f120e1f111c0219050a110a0b060907170106030c03050a11120a0615050408010b 62
    0x245074041400324081100100584080702e00003012074044c000050300100d842070440c0050311035601a20b078031f80e015000c40300d4900346140c0c54100c800c4d00c42002d0964004542d0103141f050b40240300030804031280f900c901100d411130f00b15100111403a489003000d9621440c10410b1180d100380d20180c0000c0e5503140c5140f10b030359030340041d00c5c500a208648500d074100c0e41c81441d400c0846814428103111001a0741d403039640d130709005041440c150300c82c000c0030201c00169010380d00300358007880c5880d800d0840e8808800f003070342c2c0500c8482d89000d50800082416202ca11030b03002e07103c003403900c4051701c0e045072543c09002d01950450240182d0041000c1c0300000794001c000b00c1c0c1142064942c00b000b5524014142e5007140030780c030060344c1840290000505a503054021062444240d94140090b0320740c1c1522909030346c9400c811269444040c801c07520048110b4035003a50042c0404e0b004164a0b55035800c0d400346100b40380241c0001103000800b4860030030240900828035a00341d0358003e44400d0380e0321030902 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 805855395 1250 805854145 805854167
    0x90f120203150a02070506040308091608030f090105210711070f06050a02010b0910090e0f0a0f2103050631181401060e010b1c0f0612060e070510 64
    0x310010404500300103010313810343e1012075002d0300b2074505090604015060003c1100c0305002c9224403480d4503c00b00c08444294219040180114180514442e800c0d0720382e0092640c1c1810001e040c82145002c103222000e0401c0500f508800000c0ca0030310980090901004240d503480e1a4448403007041044811464030048540d107103049901d40c0b6190388200d01401c000784609500c0b5001038107200da61844d0505203001c440d0042d004001101c0b000c1001a00c49005000c00e00ca030760008500000494040d03510701c4000c030720a44120b8113403d13001082c142c402c030031070620600083e5602c04100d61401c0c92550303040d000b120502220741181615070960b40b072240449040768095211000c480441200c80308003000b1960007203d2010003c110103809000700424414000084501400090151145c000310f0b00312448001c00ca40ea51111040e02d040a0088614220492a0b840c00c1c005002d1030420b01c040d400c40e00c501c001041811040060340d285c0343c1130760401d41c8100546842d803800103030400c281c101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 805856645 1250 805855395 805855423
    0x601020708030d0b060418060608060a050d0b060a030b0708010824060f03010209120105040204060e060a030305070510020f0a08011406070f020d17030a0e0604030c06051312090f120203 81
    0x11139a0842d4081007103801b0700c0c2d0000c0030f030021700340010450040c3c5030849401da0b00703107a8030055103076100c104110441e08a031040035000341e210030615002c030300d052040030b0340400b0140010448954a03940e00301c0c0701200701c50250010300d2110042c00070540a000300581400303c0c003a4000f0841c4800174000d40700101810a0380704442840007403042e52401e4055480c4014010940d040c0358440030700f403902910003245c0403481030f440c201c0c01050701d6035060146406a00003410f0300b1040e50850754140d90903400004181d5051090100209240c6041d00050007882e601d1486a5190000400003404600c01a0003c1c000c151804c042e09800c2d0b1100c000b900d000580000c1c40b25402d401c0307400070605440039142c01403e4164004490015485400c00460284c21114420044a070304540b00940320502500c009000079040300c00750010504507040300c1d401648a1031280901c101c1982d8000c201d42e200780d00400400e5102c0300410000ea0315208242c01002521072051040c1c1e40340d40025114403c1c202c03680 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 805857895 1250 805856645 805856651
    0x303030106090618151205010b0f12071b0f031d460e090a0b070509040b100206010f0f140d031421181c0203070b0c030108060601020708030d 62
    0xc0b13a10b50b841c03500ca0051160110043c0451030750000200110b1441440c00e200c40d04280000420030340c00d900b110b04503001e04801c1d5043c100b00c1424501403a0b4041c0124040001c0090034403520300c05142c1201c103d91050310f8513500001c00b480c000d00061742c03d00401c050400004060142c4d81c4582c4044520407040882d2524500111403000c0a0b621240c503201d81e006101c0410854608030f0700d144a0b09503000003004d05840d80c0d0f00c80e4540e54589640354000d014100359408104140e000b04090311205400510200304ca105510100700e0b0390f00b0701341c49000181d0010004000742c90402e500803024250140040c68540d0030030034001890000c0d40b82c07403070040503000061000c0c1031054a00301103111690341d040d50380302c2c44810303c0c81291000d10b50a1410103100380206280c212106203503080450824050300900011104102c1524030a4030a0015800100f080000003080901007501c03428900300842d03102e5040124851520708002c080a05640c004d0b0024019040e0000c2928004204070f9004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 805859145 1250 805857895 805857917
    0x40902240c06090f19030905040207170711010e0d051507050f04030f0b01090209130b210601032001052203020d060507020105220609081605150603030301060906 71
    0x80d031054440c04042850300c0c003070042408103008011503100c0388283d5500841d0001c258071401c08060284801d4000d0102d9007205081040d07040c17503005085205d01912031503a05003c2200444200e5210290440f40707128040c418001c0d03981c210b01954180c1d4000e40341d080820710039550fa0355840190488401c05072041000003014548034408a400c003041d00f080c1b41d9111681d9150103c51010302807801c603200041c01001050414051084d2000340e0401804e400104a41803160720092541c9040b5980008010492000c15002c0c1280e1100700c00c010b01c010041503145041c01c0c0c0400b8818010b201819200b88070b0200315a82c0a420348018110410300b0411500098250001040c4290b0009401080028003d02030140e80e60106204071000c0d0000d020b80d640d50b81002d00d0000805142541080c10841a10040343c41540305201142c072410100d4600714800450034000240058101e506501503846844480718172000c440d000001500294155414048043e154400f24000d40342008012100c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 805860395 1250 805859145 805859209
    0x140106060c060e0f0a050f0625110705041d1605010f050c010e06070c0b18030a1101061a2109070504090305070624060c11060a0c0c14040b040902 64
    0x780c130000044a00840310040700c9442c00680301d4110820800b0f01d8010200000d21207465052501110b00c03007180300b2080c84143c03140c2a291009144c00d034280b148a1a00e011440d0344651045aa028028038020141c818007244058500040303001012403c040d10f40042040f030740c00050030000305409041c40398403a0300030618a4010039282ea140d00c0c0d203120350024803104542115443e030000b4003400540c0740390741d640300301003080311301440d0710380d0455108020902956100d000300481d08240d042c00424165500d4034050f00166421030021518000003d0b41d82c0c50000c00703c46400c8201e1010228881841c0110076580c0b1815a4800c2c44d0245440c0c01420b000c0510841c2280c0005070b11035030810080300d0000a01101c40d0368046000d13000c8041702c0740402e2440c003890020340708540c00452134440e01035040a002c000e82102148100340601005403000180102690b40c020f881d245114a82c011061810001a01c021200840c0100e10b40030801c2c002d40c449561030b40300c501064030405521610301d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 805861645 1250 805860395 805860403
    0xb06030a060203150a05030f0706050d0b0603040510050f040803040b04030e04020a0305090705010e0303180102010b0607080702010305010b04210206091e0f061c050606091804140106060c060e 84
    0xc00340c42c40042002407290289850090000003038412201c102d85420906944400803600500194020181001058031800007001d0b4041c0c154004200d4048160200f0380540066408640c0364000504c61650960940700f1a50300c4014124070001c1401c03d600c07000b1446c4070107040a40441480c00c0003409160261a40c0154400d02500c01c543c0c81c2e1404c0c074000c00810059078004044d01841c1000200d6602c610034441468034020080e51518070322130640d4100da1003103c0340c281595290801140580d4903140601000c60140d01d503d80c1c0e0340c1d1142b00040807980c0582001e00070072401d00060041c0d050304100500c0081140984c0000d101036400040d01034044c02d410640d000780ca070503010307150a00040c101012264207442100c001900403003000314038000d0b001d0003144801c18503504c42c01e110f11600841d4101002a10140c80c1c1031a0101040030703003200d06914041c446070700040c04200002070b8407041040038074030000c208503030030310000610031001100d0152141c3d855415034400e51100380 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 805862895 1250 805861645 805861663
    0x30906041e1220090c1218031c0c030603080904091703240402190c0f05060406020910030c1e1106011715060102060103020d061b051903180b0603 64
    0x10314400c0300302c1c48a2901c907000d043d0481801d0300e26043c0e01e0080c1032500302840c505000b0140741304076038140a5030f42c4071000300441c014800400801d041c040c00c10000c00070300c001d140104508045201803448804c054003612403800780901050701d4203d04001040601c1c047d2100c0d14403c84011403413003e03605021003000300e800214110181c000050000451500300c08010204064440e00021441c940c100000c0340610030320190f020b00a070000381700c09841083d201d20752038400c0070090780010711038039041d140c6a81120111406580000c1c4c4100f80d00d0100201500301d02e65280074094080c640301c008102441c031a03942501d800f95088040e56990241c140c180c10304034940204c03034a9613035580f00c100e9501c0030300c034680e0703001c0c050004440803500300c100300c07a842141c0680082c1030b103900e107a0038000f0b1511202000d40b4807550710822487c9151140f010030440407200d40d903003922802100840c951000c4001100001d1618013400d0303182d807800400c0c120006681008000038a1381e40c100c0400c1c00c0107008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 805864145 1250 805862895 805862909
    0x503090a08160b040f0e180f060406050f070909022d040504110c060115200c120f0c0f040b1c0c090605060d110c070b0301090509030906041e 62
    0x44040420030700700c00034054810700c0c5a00341000000355941004021440b5900800d181d01d820410f0500121008514560b00292680d1480c505101e40701040f5040071351b08500204540c2000040c00140842070040a07080000a6200601c1c1d061480002c2c00100f41449a0502c80ba004505018000b240840030604c201026106511440b101d409210059004d4090b0740e200d50310b0040c40e100c581201c80190790020f130864000304110313401c01034420358001d1002074403001c00004c122250f82100500402c075240158080c01005000d1084003080415000f62031180390560001d00040c40540c0c0000d010482500282c40320303088101c1d84804603025000c0c040c121900030000c060340c2002006260b41c16400e5900400d095801d0701d44800c0c1950542d400b6120f9660300a00074444400d64a40961094488236025034802e0b15028922485a041052550003202044804001081040302c2d50146c01c0c0e01c8035544015602e443d145000051680c01a4001c8122180100c11100300b85010399034010003400c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 805865395 1250 805864145 805864159
    0x18020a020319030e3c0a061e02040801020703030f0c0507060b030703020a030c06030c02191e05012d0509070303050a0201061d01050118080705010e040b0d030521040809010c050309 79
    0x503500052400b101100e50b20f11510305c5081030301c03504440c01e00b00081410b260101030241003c95440b507502400c6c2e90034528040d00c803180350540c0081400e200401c000d102080c000750b21794440b400e0141c1200ca1440d0380c0d07002c1b107091040018003194030130100c2e054203600510005810254802183c0b8050641d00001d4002d45101030200520102d84c3c40710044480980d001d01180c02c11440880e01c405c01084032401544100b04907100284104103040300d007180844004074010381c107071070301800e50b0302440710709843c10f18280d040c0c20f61900c0d031400c880d881001c403078007800035040003001c441da640c04c60f20001d410000e002c50450282c610030341001000b422408001c400e04d001091220001030000e2051902103085d10202c0c421a040b40c0c03202408442c1c0c01009084218a404015140b0071080d401890344030380e5801b91213505590349031012140ca0301035035a260700d03144038210300505140c1001d2120080d0f48118200b00014240404640c007022003860425290002483d00c00d00d14080c4880c850390101d9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 805866645 1250 805865395 805865413
    0x319020f10140d0e28080a020f0109120e0607110d031205071d1008160302160b0411031216060f0509211323130618020a020319030e 58
    0x802e1303030060101074070500c040c0d500c03d06a0440240100d000c0310707030304810309052501950200b01d0f101d01502030b0300c034140107664a13a24040e4006003112001c200484030000c407120b0f2124043d07840000b0142c000b90543d21549448101e842d031404008942403014414080402c01500b05032141404031494002113200b4842e03401c2ca0800a821080c60f40c459401c1900b22102c1c0c1c1910f482c05000c8021a82c80f1500c0c0c0010b0307611540400b01e0754000da803040c0c00a140c1c0070002035201554415060490b14012001c2140a003464502044038601362041c0c41c2c0700e40d00c00c01c50f120707d844050040b14101c1c1200401c060381c1d5032032407510030049c00491106624081c0b810042140940020030450b0099000300b0f110402d07440450050800c601802e489024021020941070107500549806a03140301c1d03181c030010010000c0c900029070f00390154101a0080b80e2100420446560460b40341050502c141c1b00640c1801e036030701c400a40e00d001d80c011415550711070580c2c0c5102c281c043e92100e103054003030000b5128001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 805867895 1250 805866645 805866667
    0xc080f07060b0906092e060206090c010c0c35210c071703071220010612061e0204080c030601091a130b030601060306050319020f1014 59
    0x9040440c0035100c0d01d00b004500b004510b0140740051198100a1002c0181d868029403102128481e04030850300100401d40748001c41d4032050904000c103c254010840d620b0280b0046081c02c2e1447c81d120b0501103c002940009004982c100d410307603180705000c40700f2101e1010104003603400c139510789040d0007a03403036404c2c20101c0129102c240c00c2c2c000c040030000c1100c441e558020521800c81506601d4104060074081818024000d0303c2242c80001143d0030108561120300c20840c2588894003c00d103004645202000b804030f110b880d0300042802000300c1407910300150000c0f4489400204020b07528650513850300f4105151070412101103e0440d01c0351348510b81e90791b032040000a4076210384038070000012035010350700031386900f0204144800c001414100510030400190140d60400c00d07250345243c000b80d00e040000500804503076030b010885034034143c285810035001c080f42c040e01115041022001d03842d007009403174000740b040e1410302d02400c2805040b03603288100311003881030340d0000800b0706101e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 805869145 1250 805867895 805867897
    0x211403130b07050d09050906010e041d0106150507051f1509020d06050603060612060637030b0904020118050402070f0516060e0904061103040b090705060c0a0f030c080f 74
    0x2d94410400c542d000402400d003918815090710586500c10402400620103511408410807880c40190020071504500498400f2110b1644034082c0680c0d0f48ac00100a02d81012140c0b01c0000403a0400c02e26012090312001c0e25078603100c5801c4840450745442c0708003101a64000c0190f10500c01025150383c1c0c0b100c1c4420042d601c030a00162000d400c0c80c0b400302c9c05107800c00c1100d0003220010170031850082d803044c101040c8100140540d9020000b17025110141d240c42801c200301c09400d11503031110740d95014460741d00900d400c20b00801c161624203504060344501450716000b80d02420b144e0341100394450342000c000ea03150071041c1c01070700100f502c00c00c00001c8004814414824402e8501514500c4540200b0108a202d45800a044d080d01364105080003074406030054001d9070041402200d025961541d9032051b1412901009400b0410180680a0180101034001240d005240c0103542050a903a100c850304007502421040302894200741c0180b50142110b588503010070703140c80e41c4020040903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 805870395 1250 805869145 805869157
    0x14061504060501030b01170a09050703030e01120c0c02010e040e0f0307050706030e03030f040602040306020a020a1a0c0d0e0c09040309090b090717040302010603051c0306211403130b 80
    0xa90611402044560081c080c5c00c0d9400b0040c0d58602c13410200d290000caa184010742202ca105a5407441040820414060000910f0194441010903810300000410450345500e06c107a0007894005d1400d60b142d80300c1c95008286409203010550725070703080d0024006201384100584944219035548940c007002002500c03401707024009036600280d41f4041541a512280c03000c50342c5400030000a01c0c4607220081e0540c2080c0031f07260041c10580c490f030b1100304a0b440f45900c900941e11115a850400c030700c1059180c0b4424214441000508098502003800d005240c102c04103580c8840e140d42c02103104210880c80d41c8002082807140b42400d0030003911641140c081c00f6032590900a00c1c02d11402c0c5900018018000341c2c8e1350400b4a0046605080a614040c10880855480c0c0d240000032840801a00d00349400c503d2089012003400440903045030856032103034a48401c0f0244850840740855031001840750000d90007003504605882d124103500c90112003001a001410380890100030180c05052 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 805871645 1250 805870395 805870399
    0x314091008190612170711090a1b1d040c09060507020102030d090b0f0108030c03032e06030e10090b0a0e0715120501090b0d0219030b01030501090209070c080d09140615 74
    0x356102004c090740e4550706c60017002a00318a01c0c0100c0000904100c66015441040860001303103481c02000f090900141c0441c1001c001745c084100080101003000d030801b49a08111410440c3c000c14403070203000c4444621800b01408030200390001564000d02c21683d4030700c8a804100100c140915085420003010759070070841da0300070400807510f00710020490b41007922000086042d561850b05503803031154041ca50380c905030120003104038070b0402c0d0034400000c0c20302603c000c5a100c0081c641e1502e460710b01c000364004a424441c1e4880403070901d0011580002c0384010118200380d001e030301c40d07151411551014480f00e481c0d804104e41240d10540b0b440b08071041400600440c1d985011480c240d55030445030780e900c4924105070751300500e014048561241d0b0340c0113440744c0c043e980e9114011305030800d80c4142c0700342c4d445022070411072a0410116510100c1410f180000c440c1c162642d0380180650011011069030f0b500b2620280f0800162580302640c1c2c007800c07602645005080201d480d0303110b0340824 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 805872895 1250 805871645 805871663
    0xf0801020711012a0c0312020a0516030c1a0c0d02010f0c0e06030a050a06050d0c080d08131e0b07440613090f0314091008190612 57
    0x10302c0f036204003002032582c006a0001542d40e00b01ca14141109007440307004841c0010140000000110100b814007440b046680282681c0ba410707040180c108400c0d8070100800440592060001404030300780c0c542a03c1c500441102c020418102000c1144150704110940e48a06e0000c2e00d80703e40d05400c00e103040740e103100d024003010307050070030940300c8081061080307034000300c1400021001461944030a42c400480d10000c2200c99441c000300360380c0c0503c44001d42d001e0380c0340403041c0450790b020411100248040c2c50445042d00d0b180030100c0c401d0341002c100402c901c0344600c124002d440c010502501070340d0448a08601800d02d5000035048a009286101c44111120080c08640404d05c0c0300403011894018040902c0d81d003181824000030b0300400c100d03800120900032690001040c410304c032026103d5180c125020255043c0545024404000c00708165000c00c803201c15901e030409080561041c50400340030b1134036403040701c00141d0a2072080d41c10040c40c3c10000140310101052b02010540125021 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 805874145 1250 805872895 805872923
    0xf05160905150a030b0a050411071a01050604030f050f01020d0b19080d121103040615090e070504092907030b040e0c010c0f060c0e0f1002060c03100f08010207 70
    0x40071200881040c030b820346490500440207043d009400c0310350302d0b480003415800c110703403100c001400712444000c110520b01000701c0e21504100602100da4500c0300f04107140482c42d890400050740790b10646c000203015040b90820501005010802e201240e2400310080d03445810103801c0d000101040321050344520540b42132040a4140710904205481c1c482014003401c54264102342c950000c0403000100903035549602c1001100d214001e140101d02c10300c004580c0c40007000034030341c010300603403c0840103514041000303082c1785000070383c0c42c219002603401162050941c1405101c0001a40e02002404a01011032824005001d500c5e0305c520182d813020000c403001e05c41404100e641208203504554041c030070114503517024514070711966114090706805040595241420754030000e0032400496642d207640c0307002c0c0c90301c05d020380341c04601a10a41142946608001d585600c054882c22085c2d5000000c41c100b04c04100203000600942038600002940d41d41a19000350302941041e28180200008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 805875395 1250 805874145 805874149
    0x3060603051003080c071d04110a120b220c08010608070e1302150f0904060e0403080406110d090503270a230915091b0a030209040f05160905 62
    0x2910b00400401c40c41203500c5007140c0e01c06038203601800c81c00b42944211940016210215112003101d0003801d40085034900309460000c2038180e00707480380ca10a04000300180030301004401040107568000360282d0307542d20ac2c0c0c4a1181c0c1d80d03881440000703a05080b20320120503c13201466050845d031006000b040001e070741e542e416840c0e210700c0c0106c4d42c01e030070064041600030382100388141455000900e2400a44040a0303101c0341c50340840b011440c40100450003008034607003803046a00400e05403110900901c1c0c80c1e03070010203110004100411f030b070791b443d03000d4000d00010b030302919101c01e00c104d0208950002410080e80c0d98010b40203040c100143c240c2c1019142a02c1c51b0141501c0c40064803050703585e401c10750741500c01e0040c000c0c0800da281400d2690000c40d5034042c49140500c00c0701c006c4020145800302070020310303400189042c44580202075441c210120b0141280c4119156280050311001008005006803034280108010705041c842408251111020414462116500c4030084c659548003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 805876645 1250 805875395 805875401
    0x4051e0706050f180604121a010e16140d020d05010f1511012304022107050d020a0e09010b03061608070e01031d0c030d0203030f041412040b0a03060603 67
    0x2040c1c00200c0901c0100c020301011006020b0f200c2031901918690100700c404a0115000b6a0001c0b034032026104000d401d111038507141155459500988407429810324901040b00350300600350300010185403030204146032068041901c4103280d111802c0d504c0e0700007218103001c1c0d040000246121864240002000d05a00d000039040b01c511111442e4400f03401641a02c454920086101080d521191388000203c144001e0403200c4103060014a004d0515005110903420a581d001c0e01080d40140b1810f180c80c0d0006907501214800c50710a80010b00510100d0042500b540c001c102c100030300800c2c00300403030042d0464084d00700180d080f00c1856840211150b184803114442d64003013164980414070340d61190f140c440307440b80b040c1008556032003070840221081240580e10325468100c00341c1e40c0000e203402c1c490500c00c0e1a540c4021030841c10030711100801240040c0c001000981c00102c100c80380701081c4008a1203c101c502150349450b1b4840000089600415608000030b290036004100035000c3c0c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 805877895 1250 805876645 805876649
    0xc0816081c050c030c0105130c05030105062407021e090c19050d0603050a0c05040c14091011100c17190c03020f0403080d1416050a09050904051e07 65
    0x9164111821441c180a80c0c043c0d00c02050075205010030070032106554024042d545c01842c508138054900150350508400c4880a034100900c80e90404e0103005d05a0384c0c1c407c60103c1750310f000c1240454558414070b805d0061007604030094101d0180d0110580320541e0085e000e0344208180c50608071035582400084452090400700b0b82c9411540403000c0360b0740c1c403c2020b4003100d80030010000d04503440c1e4070b40030701d806c2040ca01216600d15081e400e100b1800c041c001c2e020084128242600400d400d4036008003640940f408841c040c07035441e2522041e0707500c40c0ca04910501c2d540d805446d540d447c60640380740074045121408022817828195541c0368120401c2c010b124402e681601400c070040301d40c80b0400b403c00c4035528402c05409103c640e50090743d50004100862003441942d680301c40b00401c203000d840400c0303401c0e03062030b118100b0800d02880c0804640704005052500d96a43c0100a80c19141c0d4400354001c03640050701c0d00100010480300103428042e00b075040960342580000204040e41e00d201038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 805879145 1250 805877895 805877923
    0x5010e090403050304021c0f05010b040c0504061421040524150f03060c040501021c05040509040f050109111c050706050a020a0515061c03090506030402030a0c081608 73
    0x40c800140209200e9005560410702c001e042c541010110155502c0d01e400c100d40643e44261040411020444c0911032018040c40c10b0310b06101d86001c6180c0503144d802141700d42d0b0184454400d1072030f2800e84440455607a00600c1100b24181000e0141c840710842040354111011310405103804609601810800360364880c510a5558a80c0c03055041441c49040c008059040704014203030022070340c3c0c28466a1b01c80c1654900703050700c1750700e0400020f15041c0d1091864240ba00d58440c845c05c0240d00100b02c5081d14001e9525010580362460312001d050301252001c0c041e946400624020841120308440d8910000ca4101940c000c2102c1c0001241d00e010400401c15070246904000751402603001c0d00e023400060054030401e160944230241841151810b030850240d1020030007070709182060360601044401068440002ca0b030f40d8001d80703048111702941c3c0c81100c001c80001e04648c2e0800c1142d031441d50222100c0388580d980d0b129a40d80fa20204050b0035a10001e0307001040100c0005a261060196 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 805880395 1250 805879145 805879159
    0x20301082a0604090e030c1203220503071101020f120a0e04050f01170a14010606020601060503040b01050d0213090b0114150910051918090219030c0e0a030c030c05010e 74
    0x513090b04040103240142c1281030601083c00750a1a82c0800d0160000b4116006806a80c0340b4098030b4628140e052400742009221903462904041100002655040c1ea8004003400b207034a49200141e14000000450704805e126610302e00301c20051600190840e07201d13648a488500381d0400401056840441d6042d10458404004001100702e0f150000306507400b100540d101444a87c07903c0380300c2d02e00b0000044141e91144010410641c0c10044240185154580740b400c501f8580d4400c4d043d18010710625104107402580d50b415540e841d242d16104401d00c0350200034822480c500314590038424442c10102e101c01542071003090400514080c1060100e603980d80ca4024413408200e940801d601000341000414400d007844ca444035044251850700703580755012120002c155a496407041a08000c1c4100d0050050030400c175030516800e040304400d4203021030094130402044800e0f001a8400360361000d964000002070020703030041c41c001e59019200e6070f80d1040e01c1c0c030015a04e002c600000c164009030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 805881645 1250 805880395 805880399
    0xc0c0406030218220803220201020a03181d09070501020c030307061805010525031811032506170709030b09010b090103240b01120c030b04020301082a0604 68
    0x3982280c0c0c05031032407660282e40084207091000d1a180348034203c400c1c0600009101f09032810004240711090040780320038003213041d580000d4a1f00b920280007001e1025820780b420880d18210303440c80c0a404000380c40003074540901d218455043c0c050703645500c81d01400001203119440401e2035060504050011407511280c0d0b61400700900440781903a010804a2403001d002800a0040a020f1242001d07070b4001c2030000d507000e410080c00c14207414145498004070303185246042c81b0743c0d4009a00200d0600402000303c011078240801c0c0c00f04408007942580303941e640403003032a02c1101a1119070380c0d868070040000e201c002051606031001400309041000c10000180c08040d20303640300c0b00c008008140283c00a0100c1c16021080c0c204440510500201509509046114500c0340141c09401c0c4100d0449800180008032078442e0302c80340640711403100003035034020f07040803040c000040c03c115070382d41e036800d0090713206d0111040b52415104880600c242021070f030708050f0b4a40340010107031032521b8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 805882895 1250 805881645 805881679
    0xf0108120901140a020708251a07060615022a0607031710050114070210030b0415140103060b190c21030501170a05102309030c0c04060302 61
    0x14000019080c10418580c3e21a0a6100307034002415101800350000d102907070410211600303002140710241b001c2d20110381070601395810544007808650070007103000000c1c1c50701d1024a00e20b100300700015142a05140d8006540618040001310002c015401c0c1e60f401581002070410303d030012005582d50f000c090301282c1c150300d403080050031001d20a040c110180a21107642c007801880490b10710128014000080005d5600480140c50300740c0314901507031822a075580003403c0846a07190150806da603e580810300c1e5100ca0780007190324021000340c120304c181c0d0340c2503415075000311084940c0001e041503400206014a0300c180e42000d10010303049072030282925012200c0b0b03007100740d09903070148505a0a0040650840d60401c00510594020440b9810007400c460402c03036080b504841d90b40300d0781c2d005010580100d41200a902a1000411300407007030385001201c0000605180e46598074201840702e1046e000004002811490b41952440b80c03101c401c220460380c45201c007941014081c4140b860031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 805884145 1250 805882895 805882897
    0x1031d06090c0607080301140a05150d0b060405092a07050714060901140d0603060e0307060b030f1009020a080f100b100e01180b0316020105090106030c030b04052b080f010812 77
    0x1023140a8101c8107583d80d50310029031501c2540182c140f164400103410804419075029541c5412380c2074034081d2411345000e02140c0170b520002d02038112012145111000ea1007200e0700b109400041d651402e46442d903c0c180320352076a0140c4140e0389924518501500a81000416600710900585840da002c0155010703090259009030910f410482d03540001100089076807003400403640722000115261031b1985002c100b00c900c06200c5ca48aa0700c0b50881c01d001002c002903110010b03480c4000816180c0c89440426040502d075041aa114010142a0034042030300041661800f0700e1200107110240082091010050300c0d090000d00040d20314101450700e5006524011885142110b42507040e0760b034010304d004940081d02c3e810700f1a000380d180b0920180c0d09004194120542000030401146180e8413250710280c148001010340b101000004c0501c8418030020315171000c0340e00740b41451500804002c034a81109101b2101168481002c26050113040300380034181d6801e13400400c003000740003103c0191 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 805885395 1250 805884145 805884179
    0x1401060503071b140d080108100e01090b070c0213090809010305060619020717060115110f0a081905030618060a12060c03110a0e090601031d06090c0607080301 70
    0x5103c5008040b0035020000d4401c40c1e072031805410040200318081030303190b06118110b2120030404c030903075005000854000c11140e414210205c40007401580001c02c0c3ca001d010745440207800b0340c5d001410085541d810501113448180300301c56500ea14002e25100c081140c108890144c03200384c00b0700c50310a1550095025030b8001c90001c000c1d60a1103105211405c10b408442078020041c2c0051208221001c0d50f20f460360701c00c3c03190740050420356041100e13440040d0000c011482c02c010700f065201034106024850905030808601c1a111809601c3c28070703000b154028180f10500c42824150400e000348240c00740d0b409000004d000202c2128011170300e115500c0c020784425841800c0301400510b41d03510410000103113210380c0b40800d807800002d60160880c0d00b88503074050a00020080140c07240c0e0b2109044004007c2141d1a803030f01e89400004030010800d108c0c120700ba00352541c13050766000c800040e015100b01d644404882191580800b13005281c001c0c40c00c010b00301903051005200d540030490400d64 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 805886645 1250 805885395 805885397
    0x619030b1302130501032708090a0807080d0f030c1d060903150406050906060a0603020705120c1c0f200109060203071709030301030f03030b01030e1002120a140106050307 75
    0x4603490250089412a4012500440c0c03e5100c1c41081041d5605800380c10101e1200040c0d203012191210f024001c42e44000d140103042c000c0000d200007950f5a101640c0000d41034040c00c0310b13a030a072a840700554840d40040c5c40e60206160080303030104e06104c5d0049941d003810f10340c1c44000d90302c3e048030007000d0440202952980640c0502070f140035510200010740e18168440d04040c240d042030b04044085502c060030108480d04075000b00a95034460b4241b04048444a242c01607407402c1d14240316080c000070b1002001e483c3c80004040c01c90001c00540b038240c4103010030303000e200856a12810f8402541000c5000085503210104c58040d03010403500340d03880314a800010880d00d15030355508040340d004403240c0000c030700d19003a001c142900180301e490b4841c4a5100852540d4110b440d410402c030005900241055254203a100176a4072a0b0070145400310806c088400709010591300c100a5080103041d4010344500c2000a1520940350190403807031001e00240070304603424071504580c243c0c40100888 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 805887895 1250 805886645 805886659
    0x1d0f0f0d02130516122c01110307030207020103060e070c0210050403060c0e13151e030501060323031804020c0c131a01030207120507052803080112030807030b0f120303010807050619030b 82
    0x1c2c0000c0d64241c003e500c4ac0010761b0300140c2d10701d103510000d021104a074014000d02c042e03260411400640081d1259034803034040307130f440c9601c1613517480444a600c51078000074217071410030f5503581c11150003c41c500c40009040300d004118150040c0340f03c0803507002101c40007403040b005404102c100c00200d9484004c403d03003071078090a0707600c0740c403a00d00b075404940c03003101c042c42c030a00301c848035050700340d02c0c10360b00d02072080a03515003103440815a0900e05a001100d21450303000502e00c0b1720701002c112013000c440c4064250b0000c5d80299510100800e1103c080700700c9000e80004022103588a4402c07242440d038001c01c00b24030580c807003000300c0719600440c1d41201c05104c0c0900c0320003080030040300280c201d002080600030452040c0340c001c1c50345030182d0118005040c5102401b001035080041d45500003100c4ca0000303852a1920001800b03400304140550300200c042c401010907500120013541a9000c04080340c400c17a0381c40c402e024151098030642c482888216940507259482600140226080107040c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 805889145 1250 805887895 805887911
    0xc232e050c03180a29030c0403020d0b040204200708030903040f0308090f040606120b1f030b0f151213080a1d0f0f0d02130516122c01 59
    0x114035650102d0240c40b070301683c80426a10501d80651100060980c40001890214820b807031503110007216481802c440d84080001100c107080780b0160b030000e5400600d80c1c0008034417414035080c0da440c03d0b1801da00490902d400f8982c009000540d5100f80104060101e140200c6903d80b4030310b54101a01142d81c5000c01c01c000252103070a1030000c2d02035802110116503613903038203040100200340605224040c80c02e24600708070154102c440740c0c5035000c03000307030100d02c602600b40000e00040544c2d504a04d0340d6000d1020010303550b4181d0282400c4281034580410703000904081010702043d5040351440b2900400c40613040c407400c0d0b104150840009400e5131030407042c40d510741c4c00a42148450b131000804d0758504141004503500c207004408000d440c290480c042d07900c049100101043e034194025128000900215111401c21030408641084204402e080c10084080404840c003241d80c0000e203000482c0300d410905108046480c00e50388210f440c0500a411390400741032480b900088036560303412803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 805890395 1250 805889145 805889167
    0x30c0412080c1e0601081617210d0b03120f0a020a0c06111504051218040f0902010f0e010e0904080d090803010504180b071b0c232e05 59
    0x808410107a0010f034240b0044622815146401c1050380b15943c2a031001e841c28495408075030050080e122080e00c1c4100c1520000341c914034101a01c0385603224421420080348004800300c01a18407100384040600c0b642d03c129041503a554401c04c0c1c0390295410800112112040b00001060034905ca8010380c2c1c8a002c0030f480360000441e2540c824008124101424040c903c01480501d054050301c80c200c1c0030905054a078140d5940c0200303600380001e00001040c012041c40b00b403280c403405c03000074030a0150300800c840c01e101500707990004901003101d10603002304007401640c038854a801c042e5241e4609034024010007034000d070040c01c155800e440c20040c0c841c14001c00c0c02554007032401035125544c1c0303514010a02044800300a080401c030215040c2800c0090a002841d07904801c40d450f00c400d0100000e481d9600000381000020b0144200d000000707101d49051641110503508181c05034600b05040e41400160301a11810000a00c41da10300007002c8000500711008081c05803611506111241c0c5c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 805891645 1250 805890395 805890403
    0x40915050903030a0e0d20161d0903120606030c0408010c030603020307080307051c050424081510120b0a1d0112080409020d0b2211030c0412080c 64
    0x228800c040c1c200004005a244042c0600e45c2e143c80321a000341000d4081c11401883c200a111203800da090065190141c900000c21041165151511450401c00d6032201c401d000b048030100f410303e1200c030703090006810710004010303500b0003141c17a030100d01e644d52803004014840e400289200083c00c000c0c800440c2c0b0740824032403411030820503203000400604500401d4074040095024003001d600402401000450104100c0c61001c10015641410108000151054003031a00300301034804240e00c043d070600107448500d034007481e400d44a074415902c03000b0b424007030310400b25680c03900001c2c1c03411041400d51040343c1c5001c5600e06c2c3c04000602c0c099203c0003d80180302e6500c2540c20f802c800e90074403007910421044900402009034a0262009030703603606d0758103014510a02600b03a9022888000d0b18000307405c100c0100400606070741804840c49036124102000c0d1050f902040d01d05422070350040d03001404c45e4004c01c0352034041e44c18240b030101c180340c110800a1046074070410030701034140c0e5058100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 805892895 1250 805891645 805891651
    0x619110d050f060f1c111c081201090216081317010609050c090d031419030203090c010e010210020a12020c0102041706060a0e040609051608070e010b03010504091505 73
    0x1d2401c6002e0300b40340c410400c8101d19540840d2180420701c07410301c02490a4001020070583c4130075049000c2600600048401e00e00d88074000c0000000f04a540c1000024030042c40c515000240703100c15a40c940318054103d008035804881101c00c89007030000813904080c00350841d2201c191409849a403100500d003c4406a400c0c24030841e0345400c4240807030078090003541da0000110090a007004803590014001d1920204050280401c01380780e040d0144407031084a00f407403507900300c000d000340803414020000c1d03100700c0302480c0d24000d030811802d1943c4503040c14219118164014441d152038494000025840401c03900103001d4002d400c51600d22140c0090411120404001604c8929011640f09000310218403509990001801c100341c9950380b14601080d610305c0d4440c0489903580f86030085c014941007030003074001e20484480700c000c030340c1116103142a00d14030820b581d9026a40e003c0010800c4083c000e08003101d038103000520141c209603000c001c0c40c600403e049070300b540b15880c20310200c9100fa = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 805894145 1250 805892895 805892911
    0x71e1e060e011b021225140f0c0909030309060103081c09140601062d1412101703040510031e050a05061c020108070e210f0619110d05 59
    0x41e032031105881c0c040c01048050722041c003030141b515410740450200c000604003007185890090b40030605100065609030400d50318041102d50149142d81d40d0ba41d140b480e040035912503401c1000003041010040b0a80c0d0154040000401131a42541d86400c05130b04805440011890148660144c540e81405141c0a03607000302442164a450341055908001c8141c1248003801200c07401d0701c2c1910048080c1c03400c2d55140a00c6d40400742100b03841241d034801128000c4414aa022400b0700503010024a91070244144540c45100c181c0d5410507030240d52985880103816030000d2008005504020207510640081481c0009440e24103607001c4503000750b0304101641d0281d413402000703060f00e081c0c42825007140e0120b40030f456242c602a0441c514003182200241000344a0300403c180303134019410103100030f50003490b43d035410700d00c55030001072181c50b00e001c00c45d01d114072200b1000c3c0c075802241c554000c000321a03049400c400182480006040203107410743d1405d80401010304104410300c0f94500813580 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 805895395 1250 805894145 805894181
    0x40c0e0324060f18040f2103050a15030308180d02060f0604020f0d0c090b04170114040308071b0506010b0307180e060103180c0b071e1e060e01 63
    0x481c0c2808806104001e203880d014001d40303500030300103a0320a00c04038805441400c800205546520340801460403407030f001440c6506594100b03140401e840c00d00030011030641d80411099640818110903100c00041c0c47c10180c4040b407060001c00e20804255034010000d000c003d05101c28540f403a8a00070350a034082c1c00580040b02444491010001c40700c0d008041186d00b54189524012012030034481d0300b0790212002c1d6100f822089483c011101c02e00148654000c850710f482c0d0b00c540c41030300300f0803504413010030b5460040c44062250406002e207005680643e64821b0a5480035004d403028005208480c68500c0c8160807180011410403843d07010b0100034100036282d05165501602a41110070f0000744903a00c200c00740600454020748541c404000d190200d0b501000c00d50310360481c10407000245c100c4070501804030300b0402240c010080700d446580709203501c1c54128140310189505101c0186400c5144006450000700710403c089228020040000d070a0001e03a42103085480c2c42031100d00100c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 805896645 1250 805895395 805895443
    0x6050d06060302031506010f0503090a02130e24010509060102031306020115051e04150f0806011d070905040504060b04090506040308070905060306040e01090c0b03010302031902060306040c0e03 85
    0x4085c000c8504480380010038208506080002811014403924800304000000c40001c42c0b4200c10003002d50048d40182c5070b501d44100c0264040d024110000c02c40010f48180341e034210070044030000207410344192070783d440241e07403e00c2c00704155920003402c640c0c110320091001d0944d02e480404014010880764000251074851004c04440d09100c1c3d034805442212048510603081c000c400010148a104860004d040e03010208900d810120941041e52131004040c008070709504001001c42c1603945250800340300a200c0012020346110403204000082c3e1a401c0030400c0e4145030f003205030000c0c8100c41c082051b44812000c6401c640f090300050350554499403d0100740740d0030524641c0c1100d010700e440340041d0700309008240c0030310001c0c0c5003501480e0756222100100c20294481c0303542503408900a1803850b074403107054486030428041030b4424090455011140185a030900c080c0c2a0302401e8a4255a199403c00c00240a8600139005000c04d200b00c000305907405008c401e5030300c000540242030602d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 805897895 1250 805896645 805896649
    0xa0e100b0a0e01180f06050d0f09020102030d0c0c08030405212a1507020708160f03060207020a03050d021b090601050f07030302090607150b0a0b091306050d06060302 73
    0x1459a0100e00c04010800858000320781c445194440d441007030030040703018441c6007062000703010294400312440d0001d21010440c9035001004041d0010340071424081110b000b19008100e0303004c2400240540d0081080148542240d0010180c050b11420011090710705034440b10f106510894003120b0301c0e00700d01101c40d41c00c940407120340000702001d4415410101d601c40d145014080e000181c050b5a070b01000c000410000402c403407015850300d40074031505800c00801c0603580d40c4680c0180b1a41e408cc3c00303508008140c480110404440c0d80c446481e51f8640f80d610351030300a61000b88140e801051641001c070114404009000c5600c018ac1d001300002002d60a68104c000461004144200180004d002c042e0ba2b10400355400e41008061403951b030746c0580780c203500030b104000c603141e040203000c45c2d13503c10310034204086007070003514600c10300690300014204480328505000300e4007030250510002000d41032205a540049041031800206507882e0740002e02005242c400c100c0e461500c4000600c118 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 805899145 1250 805897895 805897921
    0xd140708040e1f180908090303160203101401120201031d0c0a0e090a030e120607050d05091504060c0c0501240501090321090e13060c020307170304050a020a0e 70
    0x81840c4070041e0550b01d0030a04c0000301e120142d000c00103501e440b0040740061164140c100c6002c00c600a080b00d6880002c1d82d07401d20007c4c03032a1800e900c40d008100d03040c80c00d1103090190442518032840c0c0342e103540c2c0c01c0c030042c180045a041026410559204a01c00c43c0840025140d1300c0d030a49a8000c20b078000101c000c018602055070440320181c4c45140901c42c00d80000174001a0303640e85406c00600030072201c80450321140d04040310003482d20800b028403d0030350300315004040d00c01c030300711007030050b5550b142c2056660441c0100380c003031314504040041d0100301075034019200300d101c40c90714011882c0144c81d024251081c0074400002d010307a0400152010303035280c1102008007401e08207010542d20390f03100d601548482c041d10000300405800420207407480780c40c40c18080c28144111392402d0605142000303042e0151a4111006440c2541825603507000005692500740c2c051883c01d8102450500f1074125080034004640c0c61064154000c01a86d610550001414101000800e90b1a040b1070010314 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 805900395 1250 805899145 805899181
    0x3100f0e070308040b0a03020909040803010e13020d02011215090203090705030105070f030b0d020d030206040209060910170f01110c10150512120a0e1f020d140708040e 74
    0x456441500100b0000c0d001c02c0a560445045800903070f00c2d2011032505501904c07407400110f9000c440c46c020081003201c114090b505a8403e40c0c100c110558440a018a02e0a01d04001952140308104040010362040321a213043d40004c440125400a00222051500b41c0c01e401140d207058021003007040d002d400704811001403900314024856414003600183c400317243c102c41d280415450380c0d504000c0d9241c50320742e0285c541d806000d0300c00e800214140291508815039040380304200181c0841d6541c60211800f80c050703695010781c070262314075000c881013502412501a00c1c3c00d019100300c4084807002071040c1c4080000b03a1050555441741e0b0300c0164100b13a000010080001c0c648210300200d0340400140c02c09540301a50005408000c01342c00510b0a101c7d0040207440c2e040008000802c00d91110309125a4201a10004c00d4a26045180d1940326035803510702d130040e80700d600c2c680314952081015608480c0080b01451810380c0940701c0c0d1980364815040616516005818031004045214040700c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 805901645 1250 805900395 805900421
    0xc0711101710030b0708090a051501030b060a0806130501150e0405060a18060c050c0105070509030f010603020d081e0c07032114090a05180124020705150903100f 71
    0x1c0114195a1348444d4540d0160014003040818000100300c401c0070000100c440343c0040032102a0004880400320a1100340400c0b10f440c41c040d40450520708183c15280306484100000e400c050f50380b01c00040130000b150324159030541d04c41d03032440c219031100c03007264000e40744219900c0443c1c9424140780380307000005001400000d2400584088040d80c1003408821954803800116117060900001c50b2030b40102c100b500029413920083c440c0c001e0b0400700400300101c098003541c5000382511001c03800c0312a580302c0030390810101e0850100144581009002c4205c14503c03040160600b119850385540007022608035680c44454140103210038112603141050b8000b445580d0110880e50051041103407001c1c03d03031000302c04501038526551b05d00350140500350140c48407074000c5050783c0c100341c0b07200c00307205075001c010800d04440d041800f0b01300741c124040d250b50004c0c11994902000d1051400b220000d84180c860240300500c01136130140003941284400340f0020400c55040040c0400720340000420007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 805902895 1250 805901645 805901671
    0xb0403030513150f050c04150e011101020a02010c0908010e03090f06070507030605090115210c0909060609050903043b0c07051501121e020d05030310050f090c07111017 74
    0x800c00c0c522044140d502315841c100d41c01c20326403401a108582103000401c01e9500105190001030b505511100d0558010364800e9003a0faa01d400803400c86094030b880c41c6081c3c1082007a00d006040081c2051846ca038003521451610429450f09418210290821181039880c0c000f401181c2209018950419420f2143c8020f214a0b1a104404c90318031000c0f02255504054590000c0c803840c2d00d03481c0014a039046061140007018605500103108900481500314036207c00b240300364138000705036810340ea40b8030f10442c55030810300c46140b5030081140100d20301c607a0b1031000100301d41140c040140200c0d00901c4881d107590341ca150032414800075040c051494842d01300100205101003000c44200f64000904030782c1250041c1c2d51541099182001a400486d2a07050300700300328000000358440d02805400d00710241e158810807200c801c00c00c1ca078591108000000c40d4646142100411a06119019240c10f0400a001003554114001544004180342045840d51000070316045a0300000e0035080c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 805904145 1250 805902895 805902899
    0x7050604030b010e1608060904110a0b091201110a050c010608010216061a0f0d06090f0f030206100609050402160c0b04080f160e07050d05010306020d0b04090b0403030513150f050c04 80
    0x104201c0000301548d1007803081d2004507081c080742450801c820800500700032883c94868040307001981c820090355002e8103041005010380901885040314400c100c950031494000c40c02030886007a045500d025205550301c600008928400f4402084d401d81d24001c4004448010b082030b4048a0303002e06040000344140b2940c0c4003d50f11080c904c505940103c400070401041810800000d040f5078900901d011401e030302c0745090000400e4040c644a210750308440d0180e80703c0c80581e25071206407207107001046c0e070301c3e0b414005403034990050031400300d400f04441000491a21850840b4000e648840034595001030280100401409103901800083d401480b05450034241d200760340c50710f40f0440b50044000804129818401c50480300d10140c80d010920043d610303801c1c150001d521540700c00b55424035014884209003000c0c0126842660040d40818030390396940c0b401d901030900209030080d202c080030588000a64040c41080d03500c1040c03c0300040044030100d03024101c50000d00450059103041c442 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 805905395 1250 805904145 805904147
    0x1701060905100201050723070b1302030601211212150509100302090402060a030b06133b10080a08030916030804090b0f060406020d02060609011d0907050604030b010e16 74
    0x20b000148041505403107e10408075924080b00c1c0200c20f0001e122101030300c144040300c00b00512504005008800750303001c03070340d03105410a4a021010a0502e030103180d40f0768580420300c2d40c0c00442c0c40d600c46040000c048400882040c045900468101c8103c001041d424001410001c0845a210311450800103803030b81540c00041c9141c20040000344200e800086141c01e007846500006403480001c1c0c401912070010502c0000054843d000b80201c011002c0540d0420000c0c060000001d07400c419014100320600401000d1400300042c04210541c4440b640043c1d00700c0c04002d001e00490081400c5500e0342400302c080c6083c034111586440d003038161101c0a00c08100b6140403182160588400094243c034000041a61000f5081e00658400030110740011943d801141c20100d00c441a07090b10410760b03030582000300b0031000380039103192443c3e030010a00c0c456011500c9190440d001c0c0c000c80d24926521800648207078480c2e00100ea1420071480104902c2e00b9820840c0d0b00302a1400f0341110500541c0d034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 805906645 1250 805905395 805905407
    0x60c1a060f0402090a05090f0f0c07170a030e0f0127050304150e130b04050a05071209150203011719050d0c0f0f080c1014010509060117010609051002010507 69
    0x440288100c0c2c0c00a2801c8040c1c5d680d0b00100001c000290030103100345441001c00c110700c001240c1c0761944440c2d090019003c1400e841c11500303001d0344036002441e8684008031842264000e07854200a05035a604420100d0703a04004403148828150004550003a1550403801c1e081800030350343c1c40040a44c0a01d200080003c0103613000c4c0c8111803905541e5180781c2008884121944031000c0c0c12004511909800b032120750041203400c0015076050016486010b1f500c1d040740c03030446101e0001941d20840c402d054070260098104c1c03501507c032880701c40b8245000881207074820f9006a56203810300c001040015010300450500038250a03155106094036103031140c0f81d44940c140001003000010b0b811040051380501c071582580c000c12844510703042480c0a00066000d50041c003103c0c85020046280c2e81200e000e5402c0c16042c00b1100c192591900c4180715a248000e0324040c140600c00e0035005408404c0011980204001d64440194034a0841800b4500c61260300d10b60442e41000204407200303410031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 805907895 1250 805906645 805906669
    0xe0c0303040608071b030e150a0905090c22030b1f0308130803071104060b0c0a0809060906031515040b0a0c050309040c02070e010f06091e0e01060c1a06 67
    0x10800300d005544131002160428003c60200f0006010101ca00701410343c07092441002c420145d4854800d000c03003204101081c0280442c07000024108401030103d414081d0381d480d040007020509500300002d0f418280182c0e1080724500e60300e9403080d01c0030428010b50994054001c40710070900d19131f00c0c006200ca0028225180400340c580760300041d06080d404103007100328000342034032001c2d6522580740d403030300b040307184da40004562081e82880c2d00840c440886004076003c190b189802001c50308000d070f44103c910340010048540c44501884118070546410006612a002c1c044030489402070000c10480c2d014151446900400c100b400184034401103d0125601c46585082c51040210700e85022440c503c02d1403601c135001400c2c919029910794000580c00d0540e0414148421903a80b641c0c40740501c0c6856114400015800c079400300501c0c00003002207035100c00603880c0480c0b05070f1a100c0c00d403006042a44001c0002d21001d8548041c002e4420340ca900d00503441d007080b0b2881c1848000a0b440120130 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 805909145 1250 805907895 805907897
    0x605060a1d06090d11150f03070e010e0f09040c0509040c0612020304110d050a1514090c0f10052101032f100207030b0a0c110a050303150303090306190e0c03030406 72
    0xa20030300c2c1c0c0c00c0c1d640c440d0044107000002c04c1e640d40e41c001f41c1c80d51124517001540c059002c2090030410341d40760340c000c03a016810002d01405002e050917500b0100300b4802c00181044c0e032002091540031a040c0c4a803050a403049018010145181d4074000008240308800c1803103034440380c814020701c0002003c2c0406654014030444030f00c9c0000c0201d0074450304068120300c000381405a401d080c1c549600c400e0300040c108100070303c0044065980c0b00d8841c4c4e1a900c0342c030700e1113074441c0c889440c104241c50406115044c95800b4500345042c1003201ea035a10407405c00c4c400d0302200c00b40c1d1100400801600da421071111400301c06440e030380d02c188007020f104210445600725101d8981e115407101468402c22942d0001c50b042924400a401e1000b86031000704840c0c0d103c0c0001507900c40b8804102900001d0548100790300500a40c9165503101002c800655954100b96043c041001040300c160303030800655029038020400d5071064000380b4400700031500c0040e008a0603401c24010b00010741c0e0b000c07003503030119021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 805910395 1250 805909145 805909163
    0x903031b03060321110105250c020306071103040f06020a0b06190314100204140118030809040504060209030318040b040c08060d060209030a08030601090914070c060605060a1d06090d 80
    0x10614107170703418500140070040340d41ca000100040c18598401c204400700d040c2c044c08008070078809040322020f480e0b02d0080d41641c0900301181c0c0052150080050340a90f420075a410b007511400d80304040e180c0c95006900503407080c403500042c08071a407051a00031404660400810401a580202c1001280b0028004106401155803110024008410f000342240011540d43c0e88855150001d800010380d07050020b6000c5055440f900500c91807a02520b130058821381c2080d03411010400a0080200100c60b080c2d000d00c2820004c1c0c504001800c0101c81b0441c0015003142403401740800c031101402c00b00d10860421801d41110341d08240040c1d003144068032101100b89079800c0490182c800c00c07404541612407000341d080ce01c0206d00255010344026600c000c8040d540d480d0700b8045d65640100360049550f0341002c41c0c00c00c0e0165020460907441990003007102c40e598000180150806c5e00c01c20049500d1200007014a88010001b0031888400c907191402c040290000c584000ea64090040070f40d0a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 805911645 1250 805910395 805910453
    0xa0f05031e06040222031406070507171902370b04080c06010308030405160533030c07050106080a0c170c060a050705060a0b011b06020d0903031b030603 67
    0x1610b804030b03a4100c0c5c0b540b51001ea4004a2082400c00020310704c0242ea800c0c030107060328004d41c0740110f05d1501a030625550307181040c40b20780310020212040f08a210351014104120f54000908205022455450360050221010189621818910305000300c0ea441d40600c0303001075407110398042034035041c2d42010304040607a40e1440e1070f00c03013403250000c4401d092081100001c01c0204e542c00643c800d512610070b40d0f660010600a80c4840c2c0d0160151a62004c2409001d600341011560b40c00040744042400141c48090b0000102165105a660440f11203001800f80d050000034018034000b000020020b101c01c0078561228020300d0158025440b8041400390040440307034041007900030080004082e141d4540d56054090001d90090328115464010040010310401d400e01ca103007400003040e190b6281e01101505000291035500c0341c100d0b0381d03e500384003290724050284146251030340f00f610300240b461250540f5a01121061420204060800c5401c3c800180c03001007424031010481200c14400d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 805912895 1250 805911645 805911649
    0x126060c16080d052e050f13090311070807030c1a040f080a020418050d1b1406010303090e0112020d020a0825060311090d020a05090403050a0f05031e06 67
    0x1c6901800b034100c100200c0c2691803081107a1049000340310b011404004e5202d1001038111503c56032242166040f01080100304d2420302c10b1590661040051110b100035076414502421124140810343c0007800354003162038000e000f0004c0002a00440005007a034500e1035030742c00810b00c158000c80304001c1000d810700c1c0040407113200f40c0d4050f1240340032202001e81c9511403160359a402c0c0c6400c0e4451070800b22048014480c0c505000c031180e4000028000c0380b01184000d0714103129907500005903e2101c918040420040103000c286103514a010f8000c9500d5810020f0120f10950841140080712200410000302c3d444841045683d041d00c1190b0b00c81e502c0d000040c40e0600302e62202d0700d01c1c005d00b6882c56405800c480751445d0340204400403403945032a41402c40131180b080540c2184024108480401403402c000c0c0c040520707200810003109030b5140e10100e04c642409841c1140801c4002c00c00504040e00170712100c0e802d0b089460031320300f18500441521600c0040c0c80b02c140c0401240350100d4070b29 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 805914145 1250 805912895 805912927
    0x80c27010908100509010513080a0e0a080d0504031205030609180a0c26030405030c090a15060503070806190b030703060f0807080c060f0403121101140126060c 70
    0x2c044000c01e5a840384601403614002e400c0881302c00d5465440c0c000081c0300705000d85454000341c0c0e0040410360400c003406200381c1d040185402c0a640c041c40400380010342c20b030108a0130701d800c0801c1d41d030a0b403507615614166501150310070400c0700b031050238010800b003600e84a01c00307907100750390007400c0b0000d2900c013031141c0c00c08012042c0a00305006200340410b14031080072a105000d44010340d4900c0c0100c400301629101d0190303000b01030b81a04400d11320880c03454460a0a0740208016000180510503040b00200d685420303032142002c90004820020f126410407030455104a0550303000407400c01d1403011442d41c603001e00881414000110109013228400d5000501404510740b60711452a04d8082c1e00d41e40d0110362169802c188035440c01c0b4009801e00c030066465036007240d07640d18180340c1035540312480b4803070002c001d208004a42103400e0043e482400307042c10803120a100d041165041c00c16a404807000c200c0009400c20704102017944901001070711583c820200c1c00b4040d00c0f020103c1219a43e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 805915395 1250 805914145 805914149
    0xc0313030e10031d0106081b03010e01020301033801090203070203120403090503100e0a020d02120106090504060e030a0c02060307090b0d05160c0f2006070b07080c270109 75
    0xc00c9503a82640c038a07416904c90812415460003c100342d96001c5801400d8039102d0190070f00316003221481240b0207a0100e1500800311006001081c070048101c40f60b03007241c000740d005407a8802c0340c0254000c1c102c0030002280002c204c80c0c0c0008502e00b500c8806d04103007041031092443c0d651740080040c01062091040e01c030b400090244890311801c0c1420f00904450b110301850b48280213114000d5450442e621590a03062011400f40c103149010340c08001806a0f9002d040c0d8101340d00c40c0015827020030a00c26000a000c5c90034000038242010704240c0100e441000607240d0716030080148044181c1c00c03042030030a180d81114105c1d5242c0d91108102c494104c50341c440028404e0129035804032480c6030f0400740c481d00c901080190411041c01c800c40d41d07000c0070403014180e074000008402c040b521680c40b581200304030001e00b0100e0021600855001c4d44108400d4402c00f070301c0001d00003070303da0012045401202140d411801c100c00001184003502c0007840c502a40c03c04074050a056034060812400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 805916645 1250 805915395 805915399
    0xc051507051608060c0a0c0209180d020d021218090408040911190c0c06031109060a110106050a140d020d140312010501050f04150c061e0501050402030c0313030e 71
    0x100d1040751540b1001c000040d0f015005039400754500003015201408103451654242e685c8041150115400780401660060710f41450395840d07105420401008114100c110f00903a80100400b800409000b810210461000308a00340104800c11045000003099440140308aa0b9918103403514035024070300f0b106d40d0744000100d505080c81c80c00946102c4000e440c240074020035031841106460412200d09440820040400c90460003d100b82c0c0d110b40d00981d0089010040c2c1d0f8941520100068140d4100010741c3c800100d800c414072108034401e0017210010a010740b01c0801c0d1904156402607003542c0071000038028942c84207440c0a5640d04104070903034a030400d90b8a500e22010115031501d80e400206460440c0b02000000501075100740101c500744018000402c0c2418200640320b00103102103001d490401c001101d20101244c0c4d54491081411480c011030220029800f03819010355405078403c031310481c418810410248940300480764442c0300408a0a001425864140c4140800300c040035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 805917895 1250 805916645 805916653
    0x8010e0c0d09020a0b0417010501060c17070501110901030f0c020d0c0f0219051005040b12250513080102090a211506030218160806032a1009030c05150705 68
    0x145d109140c10040041c0e031400c8405003101250305046500ba01d20a102e003000240401400c0d4000c20420701c0c800500601c44d0b4412031400e0015190942501c2500316030710313620400065600c40540c2c162090440205804505004082d0000400b0352610002d40301c0e00d043c800040c00340310402408052280425a0042031104111074034103401d001c0c030109000d264000c9800c2c40710300500038081c10a48044030035001990380fa10007002403004030600041d00e0001d403c0d040e0042d01c011500240540b00c1892090740d5196210030b00a004010702031318543c8802c0c035a17481000b50030815144d5400700000d0310704480804079034243c440010350356031004503070107403801250034028640541c8641201044030300031a10b80c201900c0b000090707407010070155407114a200000800920701c41c0140c1c04507a0200300107080d20700a59024030000003c11f2203041c5120400b0300750300350415500d09552001c0c90b19070645403a0444034115654402e01e040140229889590800325503d868982e9008858010380e00c84152 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 805919145 1250 805917895 805917899
    0x15030a0207030318120c0c0803160201080a090203250803040303050703030b04050601120c1e03090b0f1009110d061211060c07050d060e0106030f0c0608010e0c0d09020a 74
    0x454001d421640040340064140344400544180034843d55001540240d01c072045048104419545a59280421640c1519100c0001140141071010f40042801c000031464252128800144503140c01400743e88181d262102260140c2c03800201802025031800c40d2740d0603001d80b40881c0800d10010350242e2514800000d000c1704050340540074041141c4240c07002e100e048c2c0c10008010554030210350700780c005406031303000c0c2140220580140d40540040d0030121004001084000072011b55030301502c020a44800b100c6040100d105091603104054008503032160410410846c44030840c5e100380d400040d1542c003042c0840e00c54004842c040110070300d08025036940c40c071411111f03100c40841521244052003401955047c008200c80c0d29941d80401b5020381c07818241000343c029182a02511001e56410703050429204c240f040801841c09451200e112400c2c614010750141b840760801c10400c802280100b00400b21403240c06e8102031a050103d803608001e4502c3c0c4000c200031000a54010814100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 805920395 1250 805919145 805919161
    0xa05010b04061b060e0a1502030f0c0703031401090e12040506090d051216050f01050106050919050402070609051c0503060907110d0905040c0e0d0204090311030f030a1a0a03020f1503 80
    0x946c414248a003c1d1240448100d140d000f00701d00045408000280705500090840e4140708001c000e40c1e8400c0c1400502c1d03c0c03441c03464071000002600800b100302d82e00c0103020100041041140300800302206458913150402c2d010420a000304609103009006170786d001410400c00b80500f000900404c3c0300380c0c1d00c80030f84003058110010b2411f4143c4846c041e07403010340100032042c0100360589001c1e85400e454444240140b1440180c0c04510611240c24000c012401e90b40c0d50005154482c040c03400401c071700c1e010381001410601c0f00003510005602c49000702c56140d412070241c82c1c0c012802c0712400e045a40e004800d407041c1c40074803083d901d98056110071460894010320f1000a48402303407010800380090340e600741c51480c024200d240d4003042ca8010b050040ca0250031483ea000d22900d0407c1070b58182404452640e0029004900d1485012041003142000c602c68441c080246501e540c507009810801700c0c5100703186000c003a0040400210810050300e504820004400003204859524071301800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 805921645 1250 805920395 805920403
    0x806061603030c0f0809064c05030a0f080304030c051507030510030503030a0c1e120f11031503121b0c030123100b0a0201050f0a05010b04061b060e 65
    0x4901c901007a1300c0442907210b10300c030f407181c0b074401ca61400082075140c490070401740c00c0e5110140d410b034082c0d80313140152007400c03020f2034091009440c041c0b21100e000e0300a9141c00c01102e1907080180039074009022000400d88202503050f41c0c640080d0700139a2a00c46041c00c950040c0c1070400500b080c40343c42d501d4881640d024030403030302c0b032800390740c04100a4403100400c192155061201802c2c0f40c0c0300380b000c50617141c0d180c1d005048110550400d00400010401c041080c20004d050102c085100c001c0d200008034011301852551840c082d00801c414a411280b400c03890101402d9100d0000000322010243d46040000403609070000c20702e04d888859129a028090320344020b1302e200d50103078034440b00c1142414000d25158070308440301e00c03c0032280c000010501c1d400041040d0302c0b0880c001000203a0b84400001001101c03003990000c6920310b045485104040000ba014021281c40e2000402c2241070b205d007030340c00351403071882c00d80c500c0000000c8030000c051041ca8050451072800d404582c400d40002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 805922895 1250 805921645 805921661
    0x9050103150b0a05060f39010509030901170a0b120307020411180111100501030804140315010909020402090a08060603101a06030702150106110705091501080606160303 74
    0x1000500010b10303400144a8011001d11030150031200500060b102803180c0300c003511a0807410529a40181400b501100d4900c013000c00ca40c00001d69034224078107006080c01441c0e07001d010300700114641140300300000e04501d18803030382c030910b201741c000071a1502d1099000071041100040404c0070100724159030715100e9111100803841149420b810448038150074041d02c5030180d0310301007420111440e0300159100b050300c000b008500d018955825030203654507c03c03a03019501170802c040d01c8a0a280060b030040e062003410903c40d0303028040e8002c280c0803504031141564a40344010172031041d079101060107030081d21030441e0301001603000801c00d0000096064030480c8201d003154404102c02c146242117414401c0e20000b10107a51610780b4a5082200045412001c2d901c1205d40441c40b008210b4030044c001e070402d034001a000c1481c83e2180004010341400751000300e80da08024103000c240c410003c0343c1c541d5601d05106012000440e82e640345010381c2c030350001d0f080d00c03051407502d18500100100010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 805924145 1250 805922895 805922933
    0x60609060f18030204020a0203120f1b090d120e041a0102070609030803042d1218140f01030603020604151b022d0a030f0b09190809010909050103 64
    0x500c042154621071505040e0040841c1240142c550a640a010296124001403400c1d80310810041481c032100002282c4241180c403090f802d82c1c200340e4400116031012010304000810103000310307140c5580d00c40100b184298080d442c64030030025854181c0b04c0a50000400e035009241c96400c1600354010030414040700000d9090ba0302098440d002034134400c9080c000900909018400900005c9088040e40980c020750910a00f0007503100d149040301408240040703441c00c0c8401803522007d6000290440994510b560242c007403414001c90111001d1030000c200c1c0704058516064a082e4004c1d40503134003442d0040e20f11559140c498064200d041045125000000c0c04d006a00104480c110800c0030120b078000c0101140049802d5500303504110701000d05885d840d9401e01e26407503510000303102d00644c07013892131154480c46c9040c24a541d0303e0081400c052a003244003045032500c150451112203da01801c07039030312080c001004032007c0800ba0840d20320249424008802e00545031480d121098417 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 805925395 1250 805924145 805924157
    0x160f09050703020a140703020313031101110615091302121515150d060f12150204030b06090c0d1401150f020304090f0902100c03081f050103050a020c0106060906 71
    0x1d1607011403c07441805a02c50014080c40c04040702c0ba60b02034004c10f22103029204807801c105006040c841c0c0c01810b0f60040760b550703501001d9000d82d960001e80f0420040101c0000e80401e00c1c00c07101d0300c0c00b14103d11403403603c640210320000f00076144003d2000722068014100e0821006007101e1655500003054500302d1000c02710000982c1c1c00000d8620200d10710010f031440c240c200110f402515035400008034000c1454a4450215110140741100c0d0005e01d1440e110100741111402d0080340c1c00c0e044100d104c00540100801d00214085e45000d941000081d640c0c15a50780d43d8202c4c604841c0281d01e0100246401d100345481648040c802c01816200016103004d50b0000486003503519490401101002d40c0041c07004100800155101e2623500d0764611020030504e10590004281d080c5c01d42c070000c040f43c00f036031400083c1940010302c1584144524940b080c503d2040d0400b04881d181c40c464030b0b04258075080003410913030705034040d00d41140c0810001d02c040c0d5150301c006001d4503258060b010000701 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 805926645 1250 805925395 805925401
    0xc0309072106021b0a06240b03012c3d05040b03010905060c130b030112110607051e0f0d1b0206041e050306060105030c0a11160f0905 59
    0x42900c4103491012040d03020302481d10341d40d50b40701c0180d00004420307046084688a4640501001e01241d1340e400d124220000c3c4000c01100d0000c22815414120001c00c1102170051126504007811241540e45045542e0700d01c0b000740307884c16250f00342c4241d44c1c01406050002e0003626070442c001641c6500b00d80c520700c03203115105d2807051140c00c10310516204006940504000d00e0902d035100c0401420083e0021480808030307100d00785891800c1d035440c64500000a6191000baa0125030880680401c0d00c2a903e19494500180301d03042188101030032088a400500f80e882d500e803000c542d415648101550520104516070780924241c41c0142c0d04140519140c140b44481e02080c000c20402c401c3d00e17508000301c4021001d0b5404101d0400403030304803804201c01f0610085801c160401c80410481e81d01606003000103242c01c00c1805000141880b20500a0000c51400e80c000e58910126510748064100503c220062a020440c8625030319580b0401c0f0101d45000012040c00940d0000e0714180940d403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 805927895 1250 805926645 805926659
    0x20a0f06020111090607020907021c08060a06030c170604141e06190b030c0c0f101a0906010c15020a110c09060306010b030705190327081905120c030907 67
    0x4800d08003600d0717020320204084d00040c68040b600940028070b510481c0c0381c51480d1401c041c0d240c2030002015012a14030401c0003444d04e000e0300002d001d0303c0039260500c10406c3c21803000d48489840840c4141444150700041c50303903201d682c03080c2c28116285144801c14140140310030100002041051520315800001814905011200d00c49008403030140011a6142a140d03140a80018100b2034a122040140405183c0204001c080e46503001000d440100d0301c0c0310144040b01d944000c0507006000300303517940c0142e95500d905030750b10010078206005800084c0c5000800b20414240441d0064808200c0c01483d0703a100100200740c41c460740031500480300c11130401041540803a03025525501090040c0701c64066030003c0d540255060802c1400e01c4004481c0740d200301841114100040d6035804034039151003260a400c06460801c04041d8501b990548035201a4494800c8401c1409801031191001c548100100e440c119808002a089402c04ca640c4c8050380d481911031074050311401c01c0100e161 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 805929145 1250 805927895 805927897
    0x5091909050f0402090a0e0f0303070f020d0903030f0e21010b0411071110110a0812160e0f01090b0d0e010b090f0604320103031b030207030803040f020a0f06020111 72
    0x141d400919050071555548046c5014001514480b4032600900703801d05407540342000518060001034580941ca81d44622000349000840b0008108100003401d0400202c1d41040030b14203d01454070340101052011000b02c1c150f8140186124400101480400e007911810351060301480c00c111010701c94031503c03880345241e5000c1d400e03025201281c202010021032a0800c02c1c4803881078681811070050b04140034050404155030700030f075480c00d400034030741d6128012100c035258082240060000140760442004200c1504c858615000e007489450000c856030064013001c0c00ae00caa258616a0303400d40041e0301c0040c1ca403150a1101d29070a20300906103920b084840140f1400b50300e03110025658030b07202080007406040000c208560301d1300303803083c50060580d00b0701c3c1d00b00d50440e60180c0c52545586002000c40e0411807090000c1484e001c2c40c2d50009601041c4241280d82002d16240c413a00d403410902259120030301d00940c0416400d1000507007048031201030040360001c1c1c008001983d00c0d60b84010103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 805930395 1250 805929145 805929151
    0x5040c0c0c05130e030c060412110613080c01060803070c0605270f060406030504150506010e011101020910020a03020d0e2101090605071701050315011505091909050f 73
    0x200010718809005604181141c8400e04100708030116264640810081c1168042400350034284c100070200000c1c0203c4140301c0d0038600207490405c0c04c0c84012a09103031103810203081300c0030500c45400c5280c148401c1b0019940140c2002e4004c105d21a51070f80c41a40d81d5001101c1120044498040007600b94082c406032544103107814031a6100b15030150301c01e01d1040803001c0b5250300006042c00680c154840e00302030005045d05840010b503d08082c03c100e008440d0016038404018242810000142d0307000220340f003030240c00c0c00c19104203458841e60b24060b01441070980e400201c0798070074800081d80010b04044040c0a5002da444c2e1000b0248100c130500030a03d44660040581c440d281103020724036607001014809040002144050340c3e480600f520419541500010140d503101540380024181407401003108400802c4030303015200300620402d405100e217502c1c840040074207600c0d0501401c21112105030013042c4400380c10000180000c1c0515030300802d11090318040001d080d64001414880c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 805931645 1250 805930395 805930403
    0x16050f120d05030405030d0203070e0405090a0c180e1516030c081504021c0605040b0d170306120706091d040c051e09040b0901050705070f020f06190905040c0c 70
    0x4074521418405440d90390001d03004a50a11040204040c5100f03140b002e50300a2440396070f900d0000005a08020075984042d10b82c21040d000156a400000c100003403101c11074207a020303070881c2c2034424588080140420104002d0314007895403080c02c3c0128203a2994407a48000007424100d0000d248102c00308e500d142100b03c00f103503e807000310b0385a2000d150224a2202d0080016240c5035202109104c1c020700c802c03c822080380c0312081072101d49040d008002ca4100f007a00c50014090064031030070409a509031800034200d40000100311591a40303445c0042000341001191009640c0301c1c3d00030042170643c425811820101c5d480c0150b02e104081001d030240d41c10020b0841d601e0b08080401070024a1542e0039080c03c070703140825640e83d0301c07003140e4036100798040c0031007841d45d2400030b90260035130744010400400c20000300300c1480012600001104050b4056401903a4064240c002c51250b1050340c100c44080c0b0300b20001024000e50100e00442078600695041c40440032642e4140d41551150074014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 805932895 1250 805931645 805931653
    0x206040f08010e1c12060b0a082a03012c01060c0b060906012f0d021c050a09030807050312040609060b150d0510030614090d0503010b04140d0516050f12 67
    0x104d0680e1250580d0f1407a0b280040c0e0010b442c50b0755088199207a8468500748020800407010480c0c00b2501a002c080c2c0454030703034032158010403203403080349080c4414002c02426000d40c12864002664500250180301c011680c6d90000d942c44d04001b6000866010003121105c0c21040000c3c182c2c1080c4150fa8011035040c0c464003880d6102d028880d580b05042210001d0502c0f641c400130311024820407900000d0401c80c0c002c0c000d80c0d00081d0790b40c1214900c842e0b410341823043c2040300c400d46680c080000000c0300e0f088a022a00c80c10286049410741c81800740324040302c80b041040c4424020540c0c0b00d40c1c091071180070100301103e1a103041c00101c51862006180134041485a5001001d20ba00324960100c8a411002286512503907500101d8091000c021183c40c0027004020706480704018102841021341411415585000744d80100c0b4404c0e130140d100c0c03d0b000c0c000d803419103884010400421a50001c03c0c4c0d0340c141441e0400c081481000e110340c5104403221b20028290b0304102102400c92403038a800b034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 805934145 1250 805932895 805932943
    0x90216060b03070e0a02031801060b071a01050a0b1c140f06100f0c2402070b1005030d0c06140f100504180b07230301150203180f040204030206040f08010e 68
    0x100b0001d4000805140003101400c040542307402c1e00788125005070128105813a1116828145107410041d01d0310442600704412005110903520b280d205d0040b03403c902805561640345588409000050082d4194a20b0070803029105011050920f103108940d50728040200d5524281001a02d408180c421000300300c003414078010940c03240b4084a00c0741d00403007a04d40c0c03640c40100210104020340100780710300f0398089052400c01410300741c819002060718610450280c240000039484910408484052010170b90310b2504100c2560040034000d105c0e641000381500d0007605101c5040002c0b9990190100d416101141529042c03082030740200c251007075070040c16151341c0c4503441342501a02e100140300c00198184200c1c078452541c007440000c1011090b4417545825942c40b42640784521240c01e54209102c1c0541600e8100d0541515a03011a50001a0011800450021b119a03000a90020300024010500034900c0704038208076034494008104100c460008a80c0741c0781018107554401a0040300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 805935251 1106 805934145 805934161
    0xc03072d1d22030c0b0105010f140309120f071e02061c0b030d0e090106050f04063005090609010c020c0603090106090216060b03070e 59
    0x2454144074281481c1100c109060904000032815010004100000c404072424502481a0010703802081e18100245442400f802c19540c21000ba400011039520504041100c0c1d1419038910000f0540010303002c0fa607510280003500345216440400340b900c5611002080711314908800c40c1c1d030b224401d2070020b13810890070480b0111030020070341640c090f03102c5600300c5074000d4508840031208481000585c0c018212049480c0d0540f2030360b146200d030150844005043c1d40b00807a001070280ea0b07548400c0318a032154041c0d610f03402a0030b000170042d05010303c500042d800c2001300d1200c0082610006456802c0080d00405880350301c6031b0900010078001c1c0446a0480a1b58000b8000407058420196039400308000040c0a00c03c0000028078024003035109502030200108207550321040c4030200121a68034403004e035206860305003482424030300003c8102c120303a4905003d076410b03035550b5a = true := by decide +kernel

theorem cover : BRFrame.Cov 805755395 805935251 := by
  have h0 := BRFrame.cov_init 805755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 805755395 ≤ n) (h2 : n < 805935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
