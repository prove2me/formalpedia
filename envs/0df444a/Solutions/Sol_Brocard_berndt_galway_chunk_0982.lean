-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0982
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:38:16.415469+00:00
-- url     : https://prove2.me/submissions/d369e2c5-e40c-4150-bc65-94b53eaf8b36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 176438848 ≤ n < 176618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 176440098 1250 176438848 176438879
    0x103060509070f0f1a070c03081b070b0a0f09090e03070c080303061f0311030408131703090103021602060a090305060709060c0b06030c06120103020108010b0c0c0d05030c0304090501 80
    0xc2c0c2c0e10703ca0020707081c1080c64a603c02d8501c60a01c04043c14044001040b09540a4440040d0f1118442411a46a01e480c41c0c054114428500441044010300281048002010030442e00c0201c5901c2c03800303405110866141210403110380910888010019016110f445485d41c01d02c031060146032a80410314003c0310050300750740403102680c01813090020a54507507001520304850707040388021402c0b024502b0b4001c0d080c0c3c0c1e0010340001001004000c00e1110200003000700b41d040c1681100507680350031405111006c486401515a4001e1003000c003154003c2d4001c140701720724044000c400c2241603000032150b60144401c40d0004214040400401204014550b0820384608008501c503041610041c0001000d07140904490805800b0450584081c004261800740150030103136130b2500003003888060702082c0310884c0025400c4c000026100c408105032070081d0070b150003425886e42800100441d04040c41d03003d031450f02040000e08042c600800c0100010080500c000c00e82e903142c40700e86001c110f003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 176441348 1250 176440098 176440109
    0xa0201020613050c0108040231060b0f040b0702030106050a0305150703050106020c2101111803010203010506071407090c090504061703030103150e0109030302031909051c0512010306050907 83
    0x2c96070400c00001d98041a0510100d41c20310f0134101903500c170300014054240001c2100000e50000003804501111091001c141d0070703500700e060003030350380d0b5518042e010b1180c40e003d000640c100b40b00c2813101001050040090600040c00465040e44071000074440045943c811034080d031001e039030ba8091002c485c140070740c800c80038182001b040d854050069200c1d96410170b118840c80756030080700c0072464010b0301c010b40e030300030540204a07040400980108030f82c0048134044603503503090f0034072980d80740500840341a02e0002c8c0106092907015035610610325140c00100c1124058440c1c00300d40e41039103100b01d101d00060b981d95458406e00c0c080c2800126007403a0080c1050841030004c800d0110f0300082183d04590303204440103059440840c072000140320a80026903a54207000b005024550b03d40c004d14010b1800002c2440000304130118038040307a80040004121350082c51200303801c0010741844036456034071402e00500d050004080d003143c40c1000d800444040d551107081c040a001d007004240003401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 176442598 1250 176441348 176441371
    0xe0406030b0c0d090605090f070807060530040327140f0102190302010903080c0903070603020904140405011409061302040504020a030203010903030e0111040b0904020d060510020a02010206 83
    0x5040d5259460707440e200608100c84000006140302e00d42c00300364802e001140e00b0a100f000380d82450000141c46a40c5d8020101d074134451614045420a40440c80804441864450b240b40c120401c2900089080241c29822280120a20188501e181d100301900c10343c4a560ba00241c502081e413460b0114035410212050100500014002840c0e4000d01240b044001c0b0707010030541d905000100c0c0303803425807081401052019510f23201095015003101c81d0142c0b003500e4101d030355540c80da01d8582c14018081c445074143d000d10f200700219070007035008000220001d0404201038401c142c11003000201a134045546a46d501e15144e598000610703641c0c0c02c2440031000c1d18090404241030b0f07880781c183c02000b0703101e90b0f9118041803c541c0c610040200540e4064002d019001c06414050300030001c003d11407005509080800d2001901c1c0310895050310540f000c11410107281e401070000a401c40f0071601c5000d6a102d0000ca03a5130b451141d40e5030100c07819030007131801902c1880020f0400c40060000740818 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 176443848 1250 176442598 176442611
    0x601140c0109030923040e030903070b03153304080706110601060302040e0c03060f040e0307031116030618170403031722031e0914030331080318010e04 67
    0x1c0c812081985c1001c0300031103011032401764603a48181544524144160300d807090003000200c2d42095405076108852404030250380d40722a8092040302c0d440340c0e0000e41920402c449941030100c80c8450540c159204205107801c0c0364860002616180e510741000e008070700707058650990030800b009020302528091a0075818145006101049040090304074004458040005003854903003598101000000810601001078400c80c00303500c9034044007043e000580100c8415900420010300c00c40245844107501d5440761650700e032500180100c03c03e440d0400c41030304003407001c40d02c0c617a8112005030710640c00300c2d5150702d94500034105200d1100110125107050b401c0212280444e041c25451041441c0f01101940041c60b0484016141e050083c0040c18200e1180540950250780042a20454418811840e0000c01015030300e0065240403d801b0000b40d40d520303e292a610001180d42c0c5c95000114841074590000c1410b6407c1b0b0240d854025184080c09806903030300001c0040140f03400d65042108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 176445098 1250 176443848 176443889
    0xc1b0302090a0c0903080c120715050601020c09160309080f0406110109030c0303020c03090d05010b01030608060f060103090507080607020d030c110a02061608070b0109320601140c01090309 83
    0x945184400b1b0704000c0007148030540101c2c01d004060100704401c0d0620707076840320ba14140411700030307801c4840b2031246404002146d6500001d550304138130800515401e03265940035070b00c04440c40302c0b10a5800701521003e403200010010070140414415a0310496150386c104003000300f000c10a9080020a84e0401c2444404a41c02882c000700b4150545030150f03640d031030b542c00c051552248800307098010030003040c918140a03040d8008a04210241d800344960b031364446100742d03610b806803003001c0201e0040000c03c919600a0f440207203a0351085050300c00203a9190030316401c241003103d04401680004a07182c00b002c2d07152152180268443c100050303c4024104060b507503641c60705001b4040c020014810000032044520100d1250380b01d02c62554900300c0b464045441007003845807203629418034821a411540451030700008042c940a8038480c0007803c080b0b2614048040d0495060051401100907000d004400a00d1009038000c008601e140303e5250040c941c4240f5070080540e4a03090320b18460 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 176446348 1250 176445098 176445107
    0xd061a032a032a0d0f0609090c0b0c0a0803181203130311010608030a0504030b010e01050d0605070302090a060c0309050102030f2a0d0206071407030c030503070c1b0302090a0c 77
    0x4010b8207454070000c0b40c1240b48148000d110f48016003404a280100d149400000d183e0007441d41000428401e0103919a1003940c4020b8600f4030b6002040c101c07484006109020070900940201c001c51407c48180c110b80c0d4688250590007660601c14154010541aa40d201c040000041c0c01c0c04640c1050300c0c1d460950f03844902c03448480d00080c1008a655000708105c0d43c250444030140a204061b25900d0401d003002a0150b4030500c0f0403285804003000025010505441060403a50090024540c200b03180e55030000518005040b04140f640c2840850b01c1912800043e9028207110740333443d0440344d40c03030030044d0070360b0803646c842030455200300812650310780414240d075209a1030010f6050010315503112428080c0f641d6000311241d104519010100550002c0c0303031401154183c40318a004034a480701e1210a01c2000000b1707000c1150b0002d8900003a100740000c42d40002546007450100c509590b40c01040602c2084803034810300711036018015490300015440d088203044500b0007200700401000703030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 176447598 1250 176446348 176446351
    0x507050f07020f0d140f1c09031e06060f0503060609091930081e0c07030e09070e040b0303030f040b0601050f0a0306380d061a032a03 59
    0xd004412241c110310182d01c072452213068665015407501038200062030925500c0c2180c200403040351240071070074218080a0350400032848510b0f5075040106066882e5805c1c230345a6881004266100003810001280300c80c42001c01800609054250051902d0b040514004010b40140e104682142c180402e840e80007880788039145158140842049440c1441340c503d0400e080c0c00385417044041d441145030380000ca60004030400755181e40209031102c40f089881d4140501031520b0b0040780b135010501c280c441c54054032270a880f03894a0100c510000340030a04500007503d04402103550701c21a50b82e6881c2a0103000c0005200760000c50452801c03c00f1510001400b41014004508480214a10782d108070102c40c1040840104075648240003038006000f0190b500c03441300e6440c0c0d4490311410b080c07410000802c1c005001149009845100044039842d50710244128032007503640d820002c0d820018120702218034401c0c81c84507441c0d02e0402c840c9070388040e003a1070400c818212a5590104500d900d8281ca = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 176448848 1250 176447598 176447603
    0x2071203030c031a010c0b0a0608060a060f0b0a090303180503030c01090c120f0204020c1c021f050408031f0801090309030c08030a020d050a020c040e0a12020f030d020c0c1c060507050f07 82
    0x7c500300d85606180c40300801450b080804030b4001c0b502000110452600124110307000480304c0d105040c4d803040b05074010b01a58000000007240e1035020800319229444c6802c8070000c00291b1403446581e4030000b483c540c0a65203c1d85241d441e500124180801c2134650070040643c88100c0080102c65610340190107401400207200b55808503e03170500280400140050b29403480c14451b030004140c201958400002103020b8100d40d40ba440c0f0321283c502c0b070150502407584081c0990450302c5154804014001c4401c050021902958000410140074020f400b001d034003d03110150001c0c21810106490400d40d004003e8641c400c2250b004a10360004000005034082d2402c00d403174070b00192003281401d08018816502a081c50f1b040c64101c00c011800e981520b1148984c221100c0c0c1d641c0040e80c880d0300203a2000c1e450340060019051581e00e40d0014440d04000b8010b441900c2c03003041c0064080c0312803e14410303a01000040c803a040010522905401c003c203803c140b81400119010000c19103d5030100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 176450098 1250 176448848 176448863
    0x50102030d15050910090b0103020910030903020a290903091c0602040308030708090c0a060206130203120a091805010b03270607021c0918050702071203030c031a010c 73
    0x45006030020344070480b02a1400600811950814042d031a5001c003a50061340c000b1850320300e44118540c041d2007100c03175510300034152158580c0710840a07801071500340c100707070300303500a00c414000000c0c02c40f030103490700c0d501c52095008441410300c50039000c1c04e00104031400c194400c201c640c5848e52503040650811684042c3c00d4000222454500040e0050f644020000c50b008028040f000350046203062060341408110307119400031804008080760180704420140e0803c101092036811000240c5004c280007904403400b0061482903100355500c1030042100042403010280f25004159a44403103211501d1824041c0e941010005a410320015081f02c0e0300081407a00b20880b076055020030b4801da500903080d981d5a10b40030fa006910742d0108584c00020b4022901031540c0c50b400b071241c850a0700c4500d5101c020a0038612a110004c000c098420380039407040100c0080c1c0c03410340e40748241a4522a640100d00c00580d017502400341c401c08161080b08807481c03a540e500c0d50364807115a0144503000300e41e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 176451348 1250 176450098 176450111
    0x40f030b0c0403080d06090b010e0a05131107050606011e02060a05130b040b010e1b090f0406030b090d0206100506031303090b0409021206180c180a0603150609050102030d 75
    0x6160314442d5a0000300310503001706070382e140a18945d005604031181030406200c1104000011180c414400b45030f2944800780040501c031604000010303500b01c902c401000104244042c1044030950011b14080321560b20400070000c3e2540e011070382400020100c40701c144c50081040b0041d449550080c4040c8005a507400050103042d00e406010f00155000402d0b5000d50501d82009021501e0034001e1a03850b5069002280c15030240441c4903400c1a11a514039040004d03000400c88812034600c015680181c50784d80100c04901965907040c011444880100510703d50038030b010b8100000280000c0341941a180d080001d52034080440394040c0d8180420b4400709518078041e203a9030000d80154202d0107001c04c01145c33120380c0341c1c0107107064003400003001d010fa902c2130100224404054900c00390052420041610340f00480d0281c603030000e9040d01850300c449010081540d020315580002d0000752140034003a054ad0503410000081c0040c0e240c440d50180c28600040d5481c031602c0710b072040d00e40c0c0d200d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 176452598 1250 176451348 176451361
    0x30b0a060c08192f030a050d02090613150e0a05100314090d0908070515030a0e0a06141b19020f071214030a0c060e0a021005031803040f030b 62
    0xc12128000c11541614509031144000140b6010000c2d881c1451000342e03401001d66070074140440740e80c05069500442c03a01e045254215410307040323071042c0300b501c40c0c007400550104d42e0784c107000d4014009403200144500745000c6c00e2001d000704100c0c1c2e44080c0b042c64807800030b043d00e84bd058441a140241d4140140d51003042c0c0403030090640c15004003c040c00c40d814000301c0a00800e10a42c21402c81c0c0d11200d03081c1c2c84d018080d0f103905452081980c480000840d010605516102469104040d0000015881542c05072181041d00b50101111000d503034032224a42c2c40219086560020110910071a42d410720030000cec038444c03294484202c071409442e50a1603c04c0c0c42040345840350780708070080d69020399442c811811207400f40340c0e0840e0000c0504809035450200042a51144e410300d50710380751000745030780390358008045001401c01e450041d080349a01503100c41d042c4401c6040380d941d0745540da1034646100c284d80c11141940d440300740c10400040000d0344098100a050300d42101c0389941d01c3d100d40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 176453848 1250 176452598 176452613
    0xf2306040b0612071e1a0406110f0601060504091103070f0e031e0c090708090303070e010504031e11010c0503030f072708060c25020102070504090606080706030b0a060c 74
    0x20051103110310540700081904001425410080041c55940301d00181d110b40f0100e1155210307400305403442400340002c118840c0702c9d02c59181d00c414000240e070b0f201c5010404103801c00303109800c5030b030100d100010108a00d003c00e10802c2440e00c021544c23a811401c20b100d00034448245404082c0810010000500603668203100311500f000007242013213858400f446103a40c89400d45461507114027040c0c400039400c0d83c0100c1c02d503485032202c940910b103107940741e81c01911850104009541003140c00d1001200040e02e1084000200082804400c0c05403143e00e84074280e10861204c45040103149441400000c00c00001d4980040c4403501450031940d840c03008980b0b000101000d5548120540446000080d103518041c080e40e448000743d551503500c0c480e01d84860704ca03007014000c4990081d2510701c0c0c441240b02405411a1052060b01c3c0c1e622fa941c0001030686589001c252003c40c0d680f807041040e800100610002003a5504050000f0034080c0000b074404d154500c524400e1080a019450070080b04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 176455098 1250 176453848 176453869
    0x105061c050627041104060f18021e031b091305090a0b1f06080105010c0f060b0613140d11060307050904110910230904060801090f2306040b06 63
    0x50103d40041050b000ca482c0701408001e5030141c03040752071a000c0340701030700749401044142d0f88541000c10320300c1c0c907140c8850f000050383d042d002c048950174801d0741040c100d0111200c02c03404440501c07a4503400e102d180315000000b9000e000b2820042000b5a034a9501c501c0b0029205864110300001d1940c1d843d501c043c1041c5809030010441c03440c40c2c1c01c000640140082044070082c0340c49004100d40d8070762500340c4845000303014050104100c000d00c540082c5070408460b086a100702c1c07000ca1290040f0000c21250b400c4221020740311816143c040c00074014040d015942e0440c11a0300c000d50106607100c00307510346110703446e841c0600400400114410f01078401c50300c071041c0107082009000d000d59156a5590002e5031104e12030a60703219445401c600c9143c400c10640c04044c0c2240304064030300c1c0074104603442010200e1f04652124400a02c041082c42a0050f0a0041a1070100800140b903c011107118444078421500242c51400003010b0000880a500a5220102c104603844e840c0c000340041c0300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 176456348 1250 176455098 176455129
    0x8240f04060f090c081608220209010e011502010b09010b0703091a07062f0c0c120303102304020901050715151a090405130203070611060105061c0506 66
    0x10007402c00259a02c0c140e2054081c0d5101ea034900e002d42c0c50b440b1901850224404002c400504110701085400320201c0c154207400c0c42d55034901907100360550109407143c0c4243e11046041c24014010446448085940c4040e00c5541c4001c111806442d00000c0203c88180102c03840c0c01004107410081500444000703002d042a003141c1c003024640d10300610382036403000808844039401d00e500080080409203d600c4410702a003000134a000210724504180d42110380791407003502c00c0818181a82d10360158004212490030040c41c1d90340f07003400c805c4e62190650762141c10040342c0200030200e905010220848003141c211400759544e000480104d40c2400345031070181c40703c0055400702c40c00022981c0100d500d5444a059091029540e20801805074a0a01050b24011040100d80b050b4a41940016032042160001d40280c00c1c1940102e0300c1e190454000c40081110300400c0070001400b04100d90040c01c00b01e9040b85401c04090791480102c0940d400c1011090310b07040810119910345000c80d00425 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 176457598 1250 176456348 176456369
    0x803040c0b0f090a050105090102100b0f0607060b040b0d05060c0a030204210b0a0203071d040e030705150903030415020904090501021303030905272503050708240f0406 74
    0xb0000700d85007059101030354040c4030300020440007820303502601c140e61a03528160082e082d0030021110003400740ca8251211a84921604d1440e00540d4840002d4900c03140500c000045c40711120003800100d950b800303003551096404400580000d2400144540d105000f5400c030341d200c23565000250040e003e03a401446000c04032450b01c5441e44010b0701d60568841c06604a480c0c19204c4042c1c0ea070481c03001707486d044000f816010f60f880d0f0ad1151304904e04501d88028000055224610011a055401c941003c0303030640c214503404401c10407050000e60300a11504090351450a10b56602c0807039a8442007100141074011800844c1d80e5590b501c840022900301000359650006103207491403800d110701040b008a8a100c10114050a00304c4a410400391501c0a0002a4480c110b4010700e180004040090303a01c641d201c2949241c84000d6907c444c881d05031808101d41c00c0c0301c0c1001e05007244c02880304c2c98588100a90301a00942c00d004a003603400c041c0e8401140403004c2000c600584502d801c03a8081c407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 176458848 1250 176457598 176457607
    0x110a0b060310140a0c271706010b0304030c02030a02180a150b040302010e0303041a04050909010b0f040c05090d0507090b010903050d080709090905101802010206040803040c0b 77
    0x954441988109412000d6403010768940d075a00c2c0c11982224140c001540f529800520f0b900910380c0502d101507a681000c00b41140356449540002d541c81101c1d410840c2044800c1117170107884d00b10756554418203409090380b036040c0301c178220741c0c0d01008002501f007040f82000741c3c2c19502c0601c190f0706280d8010348555203800c00021303071500301c0c1e6080d42c4100b040f500d0b01000040949941a1075001ea0310344e4a80580303008c0c9180c0044401e00580804694140400c000c002070107200c0c00c1c00904003804612034541c4841c03401c000c1141c8030400810111a603410000115440ea4802c80c0b14234421ba03044500084509524204841c0e9001d26140c0607003280e907818499091001c0000c4040483d10300c2c140a1190350440e40c01164220780d43d10005000303502941d610700420b4020420141d1100d81c0386481441e00d0340d1610860f003560240c2105a80c141c2011220310100e8049021748a0480d400b0300c001144400c180d40002c2d80d58100501c050501c0f900130000c03408020840704104010414005103907160b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 176460098 1250 176458848 176458853
    0x5090d020601061d040c0201060503060405100c090b031f080d0201050406060605090108071b0f080a02070605190311090901080d020c0a03150c030e01180b060301090b16110a 76
    0x8a412414110016206103000015018031035492032090301c040800041151442405003c00307400704040d60380c15952a9440400c1f661010001581b2983c010002003c00ac01005500c104aa681050000801025590500c840d81c1c403030046a410102e01c5100008030341c81c0d00941301000f041501300340c80c0d5006201c061041786505402030b5029034090002000b102c1e07582c1000340d13914800c0060080c08a01c4c2c000010308400e00a074034030341c0c010388940ea40080c605560350b9107041003040e00c4e804440d14038002c2900408550f0401190b8007030810b80c100a842d0200d903041c000006008141210708241c2c4491196000c0344000f0700f52480c1c807078007030000412540c40d010036a403520712981071100144121184a1014988590803074210b80d0095941e8a01e800040383e4034020f0311080700b00e1020700d9103603031019000b13503005d10405201c0740c603c510700e03004441c99191000c5084800340c100b61080c0e0400348100c01099554141981000460941d80e450015504013640d01c4c0105100c00981c500856244805 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 176461348 1250 176460098 176460103
    0x80a0201060b0f120115080708130c030308090606040c2705062d0a08060411090a030c0f06020a150b1206010803040e0606070b0c0d020c01020408010c032d1a03010509 73
    0x40107002c1300200410303a0b80f21040e85a101450003d210b000694103000721704907a01501807141c2100d03400440060f044110b88801c0c003103610660086001948000c2044103c01c4203100468100004076018840e4a50320710700200100481009001c6808428881518000ba030092113001010050b210310f807a502d40510300c41d24501010799484c90090404507002c550b01c1024111960005282c5800e45540c46041c01d010040149900f47c4046c0401001a811a40e032100319600040d803150096002503070406038007500105144e03000000750b40c0140840c60008080c0320628490502e034503800246180120006008074400ca04120f00c00d000354000895245c20200042c0203981c8101d01d5025240c40e4002441102d02c681c0d50080d251101040100e0f4410f070300d4500400100e5558140035042170103106015089900540c4112040c2c1e544141c60f02d2603d4060040b45a4202d00f0b201d54190741d0099980c801a040010022418040d0382e54103040000543c02c25440d8003480240007007000d8034220444a0703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 176462598 1250 176461348 176461357
    0x30916080a0317010e04110f0d140d171605130f03050607080402030309010e1912140106033302040b121005010905010e030c030a05030403061406010c080a0201060b0f 73
    0x42c0069140c0400103e84000241c6a80c100c80e084072881e03407141d03155101e03c502d52400c0c5070800d91001d0121134140e41030352400034043c40680180c8170307410b400f18030091843ca40741703500009200303204038503030342c5403c40d202218203503808142ea06044c507080d00e001804855078421310b010030000c0e005510010405001800d2980d080c2c91003007040b101940c03583c59058032010b0040301d000b50315030f004004010313407544a55049444003001602001201251561500b280b600c550001003510500b051641c1c14800c8a0031031102150a03d030007001001d0454903092801030000d68000561501c454646a045050700c0060300b400c240350800315200d58660001c00780b00c0c1d2100c031a01461031031724000700d0392142e14180708030129041612000340c078501d4100190b840161300400c5680c0b43c0101d5000b10850b4034280720044041d44a400070310303580c0e070551800f03d00700c48080c0c80440001a00f4010044540d0300030b0101201150420501d588035030201500700d014003c1c07600510000c0c0c002144441f110740380f110140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 176463848 1250 176462598 176462603
    0x10501140d06081e3702031e1f02120610020a050102030408120601020c030304260d030c08070f020601060c1415011703090a03022b0b160e0f010302030916080a 70
    0x585024401c2d240c2288015038090f414200b0178040d101100900b1002c20141090600c09002c0d41e400d008040d559900080746004070080d070b5000f0300e29486011106034443c0080c1d0f240c02000314103001e082d40e42250540c000400c445d004958403034512184c98001c2001030341c681c1d4850000d56984c2341c5403603c45020303000100c01301d000f014800081141c41d0300109003803060a50103030095080514000081911b140120986500800c400c0704903c0a00d000340400a0000310a480114908800d90002010104000d05280401140701001014240c0c0400d4003411100b45103005600581c0c1801c0c40c000f09000c1c01501807062203140e40c3c1040c0c1c2d00e42035010904880e10404001880301074604015203d1007031900c210f41c011000e940610040c46c00391114202802c0000f106040028004038880c800034102a06030345a125000c02c00030310301102c4c5100704080c0c6513849c0501c0804048804210202a0078001078180740d000300000740542420083c0151100c1080d0064003081d03542d41100780c503400f203850107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 176465098 1250 176463848 176463853
    0x70c0e0610170606040305070e1f080627030a08060f060a080a150305030c0709060b04050120010f0612020901090b030303040f0305040f0e0f0708010501140d06081e 72
    0x4405150404160034030302070075110101c1810070000c8490302c030380d0b00801c42644800148004000304100304600700107460114049400e5051104102d000440905400243c1108800061040300c10124a05401c00402c038500650810007104842913640c0c25a2825094030002c5051080c456000c100e50b40245070946404d0305800b004c0c000c3c0f164030321034940c9460118118100fc518000c02c03c0d0700142c1000a03a08801c04925100e645c1c82d4255804049800110740c0a800244209441403154000408080f00c1513440d040c40c0c00000b901c07086400b0840340c03039240e10b0180000308820a41003194500c8402c0810800e8a40302c10089070b1066028005a018480c5040003240000701441245d00c80a002001941541d5580d030369240c1c0d01146400413000c1240511001844d092010101005000881c584454900e032401c4d0a82d200c0c1c2c0c0003080f00c4100401000104816600006116220b40e4a100100e9844256a1400b4060314055008123650311450403481042d610040061038085165400d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 176466348 1250 176465098 176465101
    0xa0807030204120503131509050909150702060f0903070f03030f0f0e10150e0112050307050709020304140a030f05070215030c0a1806170711060a0209030d030603080306040b0d08070c0e 81
    0x10311f10b460034090300d403110103c1d4448106101a1a0107540103502c20760712412569010403100400d1b804980943d070071000341c1e0101082c0b040104404c4a40f0350300040060045040218503280c8075a00d03800d80d0409001e2643e51040076210b1038075078101c510000d0002c003050119041d2500c0440d13030f0358407030079800e40a2441c0034074034000103080148880403184000d03940540d607400d0903a02c600e051065041100c107807008005020001c0d03014440c103401400b10100c0140c8038601800c0031503240b008801161920b401110b55100040d0f00031307911012000030b07840c1050b2540014404540d02c100560021004d07040040200404400c8820042510600991b01d50011010211088071401014041e03840820b200b00480c00390400d540e844103510070401d1620100f4510346102c3c4a04104064400001080d0001600e10560030104008140150301785410030a9901d1a2226aa6404041c050500c141e4a404010b0b011755038000000480d80d420607040e5507120030510f03000d050f215040c86900c2c02000710381e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 176467598 1250 176466348 176466359
    0xa0605010302120c090303070b0a090b01241d04090804090608070b0403020405130f0c030201091d010b070c0b1b01060603020909131403040603020417010c050a080703020412050313 79
    0x70769000581d110051a82a00c0c0e480c180c4000c0d0300000c2402d60103110511680c8c001c1480b8428036405900380350b00c0004c60403d01d090920220f10160440f0642568031818138120051041518a050751300e8a8585040590644100c45500d0f8440d40294413070304041d0264184080c11000304101e03103c1c82e03000c02c1030a9035400c444c1e417692203074420b039242180c0030f00040001d4140303504500c7d4006c52000300c002800c0e00c3ea07510031714030300e40c0f002090f100b440200c0420710031543c02454000160090246081da4a4103e03001504209d105000708980b000012612408004c08004030700040c014040d5200d07283d03c49401002203c410b0b02100b01c0c000c0d03003014800200c00e4001c1c8219800c0079000b03001540141d807400c02049030f0408402040f00c07408070038013020000781c6007800a0800790096980141e5074915122901042c0d00c0106403060340303a450100502c0000c1d07003000494540d1901400d0000b125910200180d0090041c2e512080310042d084c110902044000300080003030402030302c1c40c03003445911407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 176468848 1250 176467598 176467601
    0x1060f0e090c1309030c0803040f061a24040305010606050c070b0a1b0507170109020103050615031b1204080705011505090604020c030d14070f0509030303240d0b0a06050103 76
    0x4403064100294980203c0c40207003541054964a0080c00c140560b0883c9640e1a04103900482d42034508442240348601000780c513000300201102c86c80840040344090f90000780d81e120f00341d841c00140c91400c46686105d80c502c60250340056030403c0082050964a80c4040c11703590180081c0c1d04240260070021030b1202c3e001e820303224030240594500d8291540e042c01c402d09100c0803030058031248111480007445c0c010300c2c05c6080d082102c031130005c10003000610000d020341d50083c05691103892000014010140985c0c2500d034410004032007200b00d01c40d000000030036072082c1044a45448a0b040801c010b1128440041103558031580081101da1a484a807560300805406000d5000510b040072601c41d1801d0340103005036148001c2600d1902907c1000142114008285191540080300402c804150010750760a141d1000c0e08000d4644021000082c2d11391000800031302c4600300c441c110090b44070840340c00c0c4585810240031149804842d08140d0601d0f00c00700c505c001c145040000205065110f0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 176470098 1250 176468848 176468863
    0xf090506010b190f030b090106030c031d0c0402030612121e0306090a02181309020f01050f09040221040f051006050303040e0a150b0304030e010f050d0b010203040801060f0e09 77
    0x1924070003d403c4500c1c840c01c9400741c0c00c0013500703410582c60310004581076a40014860080540e07450006a008070300f14007900740c80f510300c51f00c240d000505580c410312020200b03040311500422640141d80740e4581c40010001c0f503d41c01c00c1c8045108a03000624100c10400040495050360142e400c000c11842920b48a0781c80f08444264200721820081003080c0d0064010301840b50100d80184810300314480070034040440681301c1c0e03602e661121007100542c00e01041d1a0f616690a1070690301d012030706404110079100d80350004d801554001350780310807102550701d04d25804178900c0054000d41000d08010540001c81c40d004c2d6906d0158428045811031a03101c0c0c54122480070f009142000e1030100021001100100741c502400d40354a04280f01c2c24044400d0005040c00112094603410b141c203008118000e00c1d00894103100c1c5030764080c10100c0c1c012090303620320461080c001c40c0361b00d224030040f410b41c0a02c1d8050f860560a16a020130000036412040d0107403107504859121680e55290141e85d54100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 176471348 1250 176470098 176470117
    0xd0908060a02160f022b11030609030414040902040e16050102010501050d031107080a0507030302070603020301030c0b160210090302011716080c0f0d09050105130503030c0a020a05010f090506010b 86
    0x14202603020000c0c820a500101e072a0001b0f0090030b034201b140540340d034030b80c00c422514071000a4624102c0100b000c0c0e05194010032400782e000346024607202c0c890641d28401c60282040641441412a949a541b038011403d40c0303902030014400e14040d00891303982d40303100806000320001100400306243d44144943d82c1210001025924440740035203045d11440310f40c2c0c0c100a45070041c0240840c100034200203000b88070b03210302e00515400d455070900034100b00054118504042c0100010000320340c1788036030030094451466880755120340d51a81c4040301211090002c1d00303c110700042807091504102e4120440b4002c3e260200c0710280d904801010180848504c0c00440001000c1640d4602c903252843e030091040001a1521284441c5a10395030864980101d40e183ca9090050400001f8001d407a040034043c070072501d07512810f0b900e098490000a014242c80e0002080c000041442044400c0756a60090006c00000d40416088000352660200541d414440d0100000f07146c4100c0084511805 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 176472598 1250 176471348 176471377
    0x70209130302030a0f05040312091701060b040303030c020f010617371a01030b1803270a05090906071e050d090f0203061501030e070608060405040c080d0908060a02 72
    0x5034044c00c10703110001c1c5042e090341040011b02c03021000441207000c1b0400c14056849070764a00d80b0304100f04050090f50b0300d0904150341030000c01c11412406009640650703a0508002c0342ca01da2062040f407070100c00c489252000c0d03080a100150003044d10f400c00d18001034010503100c20b2004000280030002684492049408680c0240d0071b100d24103890301e560032446040c0c03070801c0a8034210184a00d800a800c160f880781d58000500003403121040340144c03440c0340c010107182090144480b645560b5552240541600046c51000300b4542c1c418011001900c0000c0c596001414610850b954448003210280045040c41100030010b4612007991428a60f036030b80e61501c1c060702b02040a000d000c07101c00458500036210382d071000598062102610905460440150500280300010241d894801504610b41c2041d041807218960007084d0550080042e980450a0b44071860301f15500345060740402010b00800c1000c0301007030340c0308030b028003100c1e01401240c0c8075803181d078603d004a115006d0b03d64480d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 176473848 1250 176472598 176472607
    0xb0d0203030d0906020c06240114091306080304060c050d0e1c030c02060a050904141e18010204030f0b011e030b190f060503240606030916030807020913030203 70
    0x6001c1e80c103d2a40e451040320054185a84c0c2d407110341c5003810558141059051540095040d10184000c80d0094031007442c02841e201200f09060402e8400c0d10740c01d034000d45000c5a81c1002d409603800c2800245800c00407255950350b02d07a030061200341078a5045566005d07040b05103444c14030030901940c010b1070080c030100005202244008004c2000c103070440c10310481c840c003007003d0780d2440041e040ba8004c07074640507664840d907c100000c442d403003840030190800c40028041031440c92204c20122140401c1181c0700d5842c1d41c00d410002828503410130030150b00006011042000c07020f01921014882c1c04940b0040e40c0307c440086884c40861002c02c1145614242003011441c80a981c40d044031240242e0806000a01d86401c00c0c0c03903e40c000246141c0e04ca40b010031860608001e5000ba80c1a04501540401c409503030341411548090a864410354000c80403954018060100c50464400700400d0f4400d1652072801c0c10319070700050001d80c42581050001001492100b0103401c110781d042d4040d5181 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 176475098 1250 176473848 176473867
    0x5090705070201031506021f110a0504090e0a050d11120304080a0906050c100b270910050402101115040614010602211605030304050318010f23120f0a0b0d020303 71
    0x202c8142192000c415031103d11880004006400030b000e0000c2b03a684047c0d5982c14282020240d90b140e24024996604c168100f101080300801c00c940340c0401881d0140d180001e0081180c9410f0041d428140b98940000501c4100050000101502070580d102c0004185e9545010f840a00540704813984582089607000c8171003d6590114101031801800107400b071500c450301c00200c03515540c480c1400b28005050041e4400100004160496444410701942c60203501140c0103041100c1c0702c0081c060b030390301e0390b1a4003403050000c0f0104952a0000d84901c0ca0103007444c4c0003900798590707840c800044840000c2507051000c41c6440c10a5148803071070946a200000b00342e038a901551002940046035041100002e40500c003c1d4042e80c0600c00554075040301c03000140281100c40d88103810b000380b1448162600341c001e107180c0390802c0300203c03103030602035043c0ca04c0c01603105005420603100004400c110000540410850041c0c400200402c41110000148290741500303c1d4040e5042d48113100c008503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 176476348 1250 176475098 176475133
    0x17130204020f04091a0103061215020a1b030f091d190b04020705031206040902090705071b150215071706040603060c02030a080a1103011e0509070507020103150602 72
    0x10a0b0b821206024540f0340c0d030b0a200011036000700002031000d0814a0500303c15030b40b50203800d0151118070085940c00080340c6d42c11f1002d044141202c4180c2d9008901c03104518003400c950b00d01701110b070f922080b204600b498010600840f1116080200342a60300100e0b13403202e245000072141c10b413a032002219807207010071600b000da00703961962980c58a400700e80c41c40751114000740108500c940002e5440b0944071703442070710b140401064a40158130f0502090090382c4c07100d0809401c00d8450824a07500d090a04001c0d412600307041d1a502940300002c0c0015500b003030021001901034041e403d41d0464000140d00c085885420358454002880c603608000ca24101c1c001c819030030000040c00042c600303903607075116000c0d6145112841d0150300702181410100e50032404003170b807154904104002003000550340e01d000740018050314044005140c03008045601041c00c01028020061440b100c41c42c150100400c1e59100c0c200032800241000440e036100c82128221806440880e009070000400f564411030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 176477598 1250 176476348 176476357
    0x4030b1b0307111e0d02010b1207031b030611070317071d0604081b1e03061303050d0e01020306010e0d0c0e06190f061707020d050310030b010806071713020402 70
    0x10041c02190326030488600100300c20080100411301031300050050410107402c50724a509100e005032181222564040e00110304401540d521124100c1c0ca00c041340100c19014071130f908000c100300c2c42d01075503c203450720100161900b01d00c41e0782c8110307181c20b6500c4400303040c55080e039081d0041000b00d12080703a412500307080001e000c00058001070802c0c2daa000300c5894105082081905000510382480240c14406100407107602c11144130ba20005922010075035541000700156078210003c110f8104042c0b041c0100e5801601c1a5014444006d824030258000d5009403541030109000d080c1803080380c2002d040408099030003101c90482540b41200c101044030b0000c100319030000c00d07500064400010b0803801c0000d010044214205241802800b41c02d40b10107803411025000704804010a0b41d0f4000713080e0862030918a403c07516034544214001158040350001807002003601c0021070422800600740380b0907c0c2c15500c0c644050350b46d400c1120011410345600c40403441e040301110143c100340e001403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 176478848 1250 176477598 176477627
    0x2010b0f210a0602030901110304050d03051306020a0807090501090b0f03130f0605071803260f0a12050109090c090525020d02010509030405240903010204060504030b1b0307 76
    0x28401d49040c9801c050a1118041c01260010b90100501805c45001d110360424030100400715031550400b034883c40e945010250107407041540300c034005080e003031000c001d85100035070005040d511244540c5d0060300c0758204442c0403000230b403581e00009a43d031140000e8001ca503036801c4480c1c81c017903d0a40c2c03182e25900c010400a0300c2201c40804400103042c20290200041c005d2500061500b0501e000401040c03c803941043c1d048a258410300101d040700410400c120300840034a00c00144c1c2c16607001a0340030381040304034182030200300c00c48490307007001320002e034942c8804007000b90ba03032100042c50460b00030b18005461059814000d101d5a10f040c0e11440e0080e1000c0350b0b140c408940920010540c1801c00d11503c0160000302c20b03464040d8090280640011f0310001450529003003501043c0c03120364070b01074001a45103100f2013440d40c84802d001c440071160058000e43d03440340c5801c00501300c5ea0113803200b2192010242c000480c80d4400812040080c140145018599158072404503562507031503024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 176480098 1250 176478848 176478889
    0x1e0c0b06061303140105070305150d051e01020a0207090c020601062105040305090f0301141902040902030c040312030506010806090a14090c0310050c03072703080702090702010b0f 79
    0xd1000b140301182002544035250f400c0481000c02d90b03a600391400684400181810041400035012220303d00c070056a406550901081c2c40d03a003405864140c05c070020034458040405d00a9117040190001d140740200c41d000c40d080296900c4011045035030440c0820016006440184031491040302d4010300c0b410f0350741005100d81076290650007141c1d82514114049003000900030301d10304010901c80040c0c20f0807002004024043e1001c901400c900625250500403008500300480d059030341903c0c003601e40710b08115101c3c0f0f0202c0540c22260b000b03007c16203084919150100000d846402614403450040e5900d14160b141c1c0c1003480032007907015103a9078980c2e884003d144072084158140c0c61040d80244024101d200d1542c0c24113061a044420302100d840c02d12003000040c01d102003c803a004105481c00168000490889800d1011a54014051802d04020000c1840600005011440d00882d0b0b45030f242d80340c451040e82260419041d83d6003081003405403031241c0c0340c4594090200075078841c9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 176481348 1250 176480098 176480107
    0x1503090a140304030605070e0a03031b1b1410020729070c060905030307050c0f03190c0317040806070c05211b0a0f06090c0b04030f031e0c0b0606 64
    0x300c0700d08809404211041a9101107020010300606004a6070890440c0c103109140f4030f08070340803440c91183c0740009818011170840300703040b982a8400d50070001d50008208080b02d04480306000d000190340c450348003c0350340015114441d1400c05002e6180c101290002d064040ca440f804c4100f03041d003000d104c41c45044e54041c0c1444445504010044c0d18451207202c25007070700788076000d4007041480d000700340a42d00030721610001950000c1d003050414800c440401d8108115400031385443d08903010100748c405020350a504101d40d50301c80c1000c0da440baa81d0020b008860031250000360140b0300c116a11342d800400810003003030094600d001ea4174060303015a58684c0761140040b40009038503048984624000880100905081400c07a013906850340140c1050f030084d480b000001245858050301403035884808070208143c1c01d03001c800a201c0d90b078030a41c03141d43da402d2001400090440a401003030362180903446c51302003400161002e407165104d1055072440c0f602e5518400a00914480d0480d10800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 176482598 1250 176481348 176481353
    0x601060c1a0a020a0206220f0807020a0e07120203101205070905010b1315270f09090204050f0403090b0c030c061f06021504060f090b040501050a0b0603061503090a 72
    0x20030310380b2032010007401680e607840c801c000924101005140e2500704403119001080f001841d00d10010068005050040e641d009081096041c40b440788003d600c03091103000000d440d241145428800c0c60395032240b60308004008803207020323840300300c0e910185003034803903c1407110f607525a032040400390240c01190b00e1292198440400c544003a0800e0052090218070100d40c0345502e910340000e00300d02100400c2c448040344014100340f000c000c107100c01c407409000013050301d11040343c4200100070103805240459692144040244190366050b4003403400c7c01c000580380954025035902403685036070348103052032406403c504550061940009240003c1221215002d003c000c0d00b4012645c41d404840156410404084400a15480a0290742006900440d910b02c068805a4803503000b0344082110a447c0c04c0440052965450041c41c1662440600050200550140f07128107640b4804000500840c170030003200b4001200d0095010a401d43c004c18040c0115010b90f0708803078400112190401c00c3d9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 176483848 1250 176482598 176482643
    0x20c01090516091134080a0305150f0f0402070609080309073c030602030709050915030c0d110303030702010207060f02030c160318090605030607050c0601060c 70
    0x100c0d040d54180d02120b11801e40c12104501a001816000c6007080416140681c000c01405503c0088885030301120600b410b515108240a1110058052010501c001ea00d0a40c106400c44986900000c0c40c02d000201030300012003d0815000d0010200c11002511004000300390b4080079445810580901020707001403024003070f00300c01c281304a02007500da142650b900c40c604051680032008000084441607030f400a159850496039120540c01140030444500c5030282965a03400180740038800030801041c0b41d40700061806507482100d9003002522184040407541c141c50b0015a4560050555200b035440e01d0012400e400d032007865078403001450000024210b4204861480260f50002070030ba04210143c07055901680b0701c840c0441c15410200200d80043c05801528002c0d01038464103201418047c00b04102d5400c80c5c080ba0407200341e1079028140240500344a410b0191192402203008180102d003941c804800c5c18004000603031a001049440c10010713030f0b00761b4007001e00d81074482104114 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 176485098 1250 176483848 176483861
    0x20d0311010e03030610030212040b100f18060b03091510080a031d041407030c020f010513020312070807020d030908030a0504050f030d0923031b1e06030103020607030201020c01 78
    0x510010f141c4919040040c404081c1c1c40314071007003c0520400c000340500344607001c80c0b0381264104110700d54a0b501c042e0011032200b15174102040401040c100055201c03c0da00d010240e04020220a01032942c1e9140d1003031180c0003c2d03458015540003804c80242d05502d41c01da141d403100c1410100080d42e43c1d90b2503030340d00340340c1d01d0b250940008045007803010401c242019a00f1121030241c82c100011640c81c0154000035001515040401d03807101610110f0a108000c2420388801c00402004142022401c0760001c04054000300d001740904a546508001820281e686d000d07045445140b62007601c0e401c0244140d8503035021818010810702c08550100204090318034084240c50303130b03590380b41030400700318103d9240c5251512a5004000102400354049110400c0742c030b200c8811000300c40b600004180c4a1504107080c0d4041c0304500b00d00d60812590318540000140550360101c50b41005141c00580080c1c10400c01d410890401c0104014100301d0000c00c0894068400103080601c42140142915079 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 176486348 1250 176485098 176485121
    0x2010e1002011d0601030f020609040e011a04110903070302100908010207200603061305090f160e0906070c02090c1b0703020a1e031101111c0212070807020d031101 72
    0x15580d08030b004808180d0340b841c52003d2100010b00c01036266070340e0b00c6640391703200710001d00845d4007044004140c1c031a0b07080344141132000002480391210114503101c0c0d080d90034000a1050781032000b81d0300f01015070000c540103250094003a001c4a0b0654083c400d0410460b20000100001c02c03d001440c040c081c409000b80c00e05c03407480d2030b8650110801c05a8100c003a600c80da84a084100144140c039601c03201c4009061003049404641581c1d084031542c2001d5108501548a0040105464140c00090b905d04182c542000d0504000c0d1201046141d90b00411140e18001c80c0c90560014003519200e002c190f440300040010038944800100203011b141440445a544c070340c4111003d20071441c3c000c800002600c412803101d80280d811840c00c10201c400c610011384603020101065801e40d01c10407001034019900344c2210360002e030303440c40c00b8044103000345c0e0700c0014014080d580070788041141c1100c0301a600601102d090450f25001c00c551004816411010310426188141014000307014134140021b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 176487598 1250 176486348 176486351
    0x307050d020604050c06040608131104020403030806090a0c0c03030504110d03020d1227061805061f0b040e0a15120b011d0106050c010b130902210d0c02010e100201 72
    0x102480c004d031038980340703c01040c45482c00f80014045240c0c000e03142940000c00c4101c003219400142000320030065811402c03a0081d000140c00700615400003000c5010f0442079030012050341e0b03200841130031a0710a886e03860001d22400070207404039101340c2160346c0245c01034048003044a0044001a03103482e04e01c50881c0513030040040e441030280c200c034a10713840c40340c0d4503c01d01074102c80350410182290103400c00e00380340180b05407000605c90340f81d021518020b1304c0c03861101031101f00c0c00c1c2186e88260031101c4800c5c490034480154100820310600710200d550841d121030605003007561841c9070030780040035500166030326010484d09403602c0352030000400803021804000000c0d030800c80c0d45447c058110340f00a08440c6500f07051641c0450360720f411515989030954071203002c20881405802800d10f9180c3c0851011600900b4104030b50048200500c02c8510643c20016000c080030340c2c2814807040001600140b100c00001d5005892035545c140c81490301e000d1651f081ca00003284204038091040050313 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 176488848 1250 176487598 176487601
    0x7060b1017180601060c0f0b130213060503060703022d0a0e060301050d14072c090c03060a1802030601030602030108010c09120f03140315040c05041a0304050307050d0206 75
    0x40e01580760302908080311820445101d14024942541d4203418414038081200159584c01405014000e050f01281d00c1030b0911401c1c00d142050103a01d43d00307113030180c0c840c20a03801c0c480b40e80c180d144180001c445002d40030305940d43d60303220181c1c000d401210020b0440c1243c070f0010001032140480c4080b1b0074250420203911071000380c41c000c01c0145407038801806104e0420040c011030340c0c0c03a1203400102e80c5c0007130002d1004400d0b0f440b10303040c902d05520170700c41034441c2c0b80080700015401010304001400c1141d608016a1252200c0c2d640394031b01c161140d0507030014004034419600c81e400c19440341560a51401d05101c0d1070307010a282c14000d0303005460710f940c084010702804500380608500c003002e5241401c111410000310b110818016807005048100b240541c0c401c01d801110100b17406041c402da0140c40340782042d291580c00074441c008521981c41c28828141d407a004800755402d8400c03140500f41502e0070400d0b41c080962000d4001e4507548410b201c8000094002c10080c03090804590141559 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 176490098 1250 176488848 176488877
    0x2060d0f060f05180a150f08102309010b0319050601050603040c2907050303070e0909030a03091502070c061403040305030601030906090615031a130807060b10 70
    0xc07104903420210061044200402080d40c400c201002007440a8201020540765510000d00500507103031114081205600c000420901c1000440c040b02c2401c400c0d05c0103400204000350499041140c0440003440001503401e00c0c1180c0001c031a8070841080001a290100e10002803804c1560001007201040c64049901040000d09c051401800b043e02d00c00d00303600305540c07003c0b84184c00d40a0450b055500c014140500c0c0801c0000821300c4516034480c56542d12182855901c0c2c0d4011150100890720125180c0d00a0801140d828800c6801030041c6091180c8258100d024001f0200182e454602020941041948610003031074550320a08036207005916180019200743c80c034036160341100000740204008039800104881e0b11080900c3c000070300100d01d250200c0140100342d40a468a4a070850420100045424903000c3d40c5c050501c20441d90b4800302d408e10100c0741250351000f094103041d440c000240e42800a41071141c400c03140812440380c20f0b80407401001c0314012240004004003a465071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 176491348 1250 176490098 176490101
    0x20f0705070e15090a1e02071412090f0102030d0614120312010608040503070c151407020307092d0204090e0a1205131703090f0319030c0c0302060d0f 66
    0x1484030b465a640700c0e281c040f408000340c1040a000701d000b000c407480040c400e51125488040016510b240c9801070101c40c0142800942103004100d80903d00480c41d40307000480003174040c107500c18a400b814030300f044081c00d11010840c00c2d101141036100034003280e0b40c40d84a0340101e501509407440320011411110f0b040055651282c454804960000c0007850501c032480c40703029056584604141d9030f95105c40c604070782703540300d108005403501550400c041035080c002c4006e1504400b0550b501c0200c04903032902ba100b5482003140007581980b0040c02001810a60b0704071161901180c5d6901181c003070081c01e07400403019a400700c030100d554001030a1166850074400d04580c022500000d03c10401207a5136100a00921034507001484808500e9030520124001d414024100071003089201480d2071114a0307582d004040707054850032074000c5130041130400081c11010800c01582461207030180b0785054444007400201680c9821426001002603100d1500410300c580c0716940c000340c0c15145802160 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 176492598 1250 176491348 176491363
    0x120d02130b071e0c030f020d0b16080c04060c060f0e12030108010c110a03271e06020313090506010504031a040c0b1812010b090118050106080c07060b13020f0705 71
    0x143c120051660800100740c1c5102c850082d60307440400e196440c109400050200040400300824001d5028100b0110f8000b100454814010341d40305c4880d00d0311048095080c81c010b40c020000064510251030001c14002d8000c20036680e11800002940702c503075038880e414910100e0711703800403032070000c0100982c0070700b4410400c1458031781c9090300c0c1d40c8000502c0300352540400100075040200000b900c0204003414031504e130700d0014160001e042e01d03540b0301400700c15200c44940c0110310400c0c010000381440c0040112140c02159001c8925990308100743c40c401042c1c041d00c52030411100b444080001032001c1c1106401e04c040c5445075044c0d00d810300e40800701121a03044000851424000500402010800d05100d8481162942c004500182d0791500529035140900d40c040c07509000095840c6c20181400c5c41032042d9003092004d80e8903042c0c2a158044140c550f403200070010441341020542e1544407441100c0b0041450510f8001551440142e07040380241d1001d08200060341000c02800300f1414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 176493848 1250 176492598 176492633
    0x108460902010504031101031d0106080105010e07090614070501050a0f0c030b1c0213021902060703050403023a0810060305010806060d21050306120f120d02130b07 72
    0x2403059604590000b0824011403100400950202550b0b1030240c0c00780d003000c0c101c00c85d03c402444900d44d4440002e030203070049200d84441946070100200b1034107007541500f4880c1503203441e410709140c40c1c83c0d0b0031200080c610b240406500c000f40320700301c0094002c0c01031500a48000101048132034400d1070007011039441e400d0711402e0510f003482c24042d0361204600d42010000f0450361019452890020408000711007160680f4688005508d1180c01c0284421141400706a0f08413402603940780810b4044800c151800f6000d81d00402d4801c21202160b02060070a0002c0042400b51041c070225051000c025034a9400204848804000d4420442c10340d00000301503a02c1c042c052035140c604256211140a4510f50084001c1104c1105010394040c44507001e07002c04004c4400c03030198801c020556002902c0c001d00c6090000c800c4080c8110020300fa88007a4181d0014202015140101d490071340d0003000c15040d01703602442409003081c10a04407000030a010100310355201ca091400038071011500d2001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 176495098 1250 176493848 176493851
    0x2040302010908190b09030906040305070312090311060f071a040311070b04050904060905070e060415180e070f0b09120d0914030a0209010909020a0b18010846 70
    0x1920041089031107841020b98021500c5003951b00e5016038070b8210301c6420784650300400b00003400810008001072400031a80203840009030344240810444240516110180c503040003620300a0441c54040020701c8500980031500b072400e1000d0350350300e1090240a0711964804003010410040c5500030325054100420b80014061076400c12034004524011405800d001e400e6a00016013005a9680502c01203600402203802c01661103001807840710301100e001d4000d80c00d203058400000d16002142098800049184401c040000c0c0754200810159411350002d20039414005480c01104440801500a1406040e6035a041005021707181c071010a54004c16400700d148950102ea01810352400da400c2c541d907800407506d440300064a0a4a6068003a5100c0d000304000120707502103030f12038802c072482034401001c865690500c80d0545d020b1803134502440c20b03030341c050f070441588141c031101d81c0700d501c0601110007503015025284280742c1ca0b100c0000c51004101d443d1128000400246002280300e690 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 176496348 1250 176495098 176495113
    0x9090d020a0f08130e07110a080a0c031206060c0302010e0303040203070302120106030501050f15010903020306010504090c080a03031401081f1d0a110a060305040f170f030a02040302010908 83
    0x600a5444401000182c0070b0b00e1110103000400c14035204039071219403504504079500b03445200d407131130700d54050704c550010031088208086007030720204a01c81c24603004074880381031000c80b00c5c0c103841c100661401242084894442d038000034003039105001c06040d050f0b07280081450b851401a0854043e814055100d9005008100c0103980010702401981d6064900010940e04803081c1c601401c0700d6000240f072035080600f0441185149642d0724450f1010440c0089203403a05001912046458003020b50560400ca00510003410140c015a451074490260340c060785a603001910b081009100003100003230b03200da011486201400c02c1c17190141648602510710b1441107050380829003e004842a0703c4c544800042d101d0100c2c6a1541d43c0c40d00e10784040c5c030449a044d20b48040f0210000890612440310b040c2c01003203a0344a880b44520950340b02003480c0307003420b03140c4640800781d00c014404100c1c041c00308105190560030340003541c0200c03160000541c0740ca08500c00940350175081e400c070602d250301042 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 176497598 1250 176496348 176496373
    0x6020310061404090c02031204063206100903020310090b0f010602030304030e0a09240602010b010c021201060305070324020901080609041b03080d0b03060118050907030b090c0909 79
    0x102c3d012202c08075400a0120340a000590071402804d05d480c10480070070041105001550f001180020a8183c4d411500300c22110004241104403190040d000318180000c0c04e2410700d00390075030218005040448015641f540046e292801030211100304548604040003000b02e03143388944c1010702c4040c403001070341c14900020758900004001804200314287c140066480e0b102408014002044083c0501c0c0e43d45070620703899801c182400c8aa54403003110000d042841031080000200059444008032200d03074080003c298008c0321504803a5694074800000502d08000e15402140312346202c40620001d100c003140301c203034a4601c40e06082d004004011203a03a1200b051036020804842c00445a252424032112007402003140444651203400d000c0305026a8201800d101001c0703205c03d120b268220b00c04d01da2988001c1c814030850205481d214810682e00d43c0100c0d80c40036040b02181c00c0740ba41c0740c0303514803240710a6445444503000080910500e04240003819801a8481e000700f28101022 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 176498848 1250 176497598 176497637
    0x5010c02010210020307050708030c0c0f06221704060804031b0f1401090c140a050d08070b04111507050d0906050d0c0509040e0d0206070c02012003090d0602031006 72
    0x83c1914101d500100040c1854007601c00e0740c51141c2c000616548900e044d02c1510415440809041054406c021103640713612000503010f4800c1c0c0707104a0510007031020118001814018070380440e81a00c590440d045250952000b510007408e07503030307541c46040c02c0c24240a0400100d100300741c80d00f20301c118001c2020400c03030b0451f10091ba502400c08001031100071000c3d4018107200741c0090007046034540001d10002004206080c0081c21101c01d401159520200030001c5092034006000704800e0103801c0100f2444a00c0b103074400d0040c0d05a079018000c41001810400d417800760600c07850740c040b44100034000d0420546003035105509110b07000500f4804054201d004020502004e41d031220103039116544901c040e600c40804c007a005220102000d41c41e5a220540b241c0309c10300522030000050b071803605c25020800e42c3c0d50180c4074600740180c40c5900440c05a2540050411031108002c0e01510342c84030701c01c4080c0c03d1700800c2c0058503414803001860f982c0c07800798400c0d07081010f203521030390015010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 176500098 1250 176498848 176498863
    0x705010908010c1e1b0c21052112010b072f041d1014060618010c02040e160e01060c020303090f03010603020607080711060a081b0903030705150105010c020102 70
    0x1810180000000e00822610354003103a900c2c0320702c001c80103104410400000f42e03000654038429800381d00e00600300500c0250060041f005411607000d41d9181c0703a40314514802950a1140c400358a1030103640746c48100d8511000c0e03020040b032110000704030090084000d03015080c921b09032401800401091088840490001d140d24861503449004095201d0360740e800d840d160145a05603030014485c0c3c10060024250100344200200102c4000b40c402e250407801c4808012596146907040e2801d1001101e0592106100301c0c0c00c82c0e5205940f4211030410882c3c820442820b0809504042c2800f02a1800b49010ba01480910400e608600010b9401005550130b020b01500d6642004c01c0320344c0007a02420b8203a0000e0b400260004050041c040508014611207014680c100c20124030007061004510446281c0c0e40055140c41c0466803102e0780e804070100301d241c800a481c0c1880c0304040001e0441e80140f03012030ba07507071005500691500c10021501d0040c035090070300072300d48895500083c0d2501d80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 176501348 1250 176500098 176500127
    0x105041508091e0303090106050a0806010311060403060501270e120d0b12100b190e04060b060a050a02070b030105060a051c09080909130c090903030f0507020705010908010c 76
    0x416000070b60140d002c100400111040b25125804415240a02ca44903401500e02c00b5680d401c120011486040c8175584100704c3c1c2d00070001b005240c1c40c60300c0d0380100d80d0001400e0b0b54014001c010000104d04074ac090503010300b4100d200c8450211083c80700c40040428101c144118900b4082c4840a0550119401d001385100c12a46a0f0f1120030300c038018010701050800d030380d00034146c001031443e906001034141c0104c88070032020482d005a0b0020051400c411420b980c0d20384020304002c0c0b00011804903a0758100744590b0012039072030700d2903002030000d81090b01c4060000702e011610000c00c0c3d0741000404000c04812240c41d00e55410312001c195188034003500c1806022000036400351903201d50b4030a008404042c90100040d18841c54103102d10b03840f03500114828007102022030700525a01a0342c0340e900394040c4c040300f10180341c143c040c0301a09800340c0c00e87c1850b540310609182141980a070702d02c2808150301420742c0d00d040c5000501280c195030401030040e8900066401c0c55508080a0702c032412 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 176502598 1250 176501348 176501357
    0x2003060c0301120302031b0a0c0e09030a0f021f0203160c053301180605030d0207141305010905060103051308180609060c210f070803060d0c03050c0f01050415 70
    0xf401c1d424240e2031807040c0c008034200c00e41c910340c01502c0e48101040030041d203803103101c0e511041a1303903c903003582401e0181c40320011a0020442e170f10065000e42d6444442c600303580182c50032103681c40c1103c500f0700282d000b101b60160300042017202091041c50301c0380300c0c00c03e1170608050920f0252115952001c48850203840e40c0d5103082010b000001c44440060f02c010581310300211f035030311103200840d0340388689607401000d0b041c8240428285070201340d00c0d1a8000d41da004000c15480c0403203544085100d180d0142c1c004000070341d401ca52030490301800340039001c210340c08101414100300040c01c842c0300401c18240041c0c04080000090800001c590f100c40a40030f00005a4440300005a041c2c85003c914a03444003001a0780448500e000c6224141042c038115501410490710f0585d80c070500c1086034001000400704940d01c00141c00c80080c0d500b040d000f070044012152140e80d404100c0c505604162140d40c08015044024942400d500c00201000c1c41c03d40c0c01c06240146d120104802c1c80001c10500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 176503848 1250 176502598 176502629
    0xe0a02030a09080d0c120b010f0f11010903020c12010506061219020c15070f051c06080f030706050606040e0601030504030c0501020d0b0901120803130302010b0901032003060c0301 79
    0x4068100c00c540715040b12415507191302c0b07840030400803c01c0034403207000f00b1041500321380d000c2c070749110700e29200c00185c44e100690104014121003140e02820344006200410351700f655240000d100c0d8140091281c2c0003081b85003c0c2d1001c00102d441c1030030f51030146a0410040080c80d48862041d102001c1003d801030301c06407141a442544e290040703c07840e80003403012980088c04003001410244501008400d440c080e02da510f81283d1000031090501d0208400300101550384c0c44451851401d0380c40c0300e00000e240b540700d807400c6007400081441d0b40b010342d101190072010300905218803904220100c512900c0d180c5041d90304e01201c00001c0c01c950615a88500207018035000743e42401140760300000071980c582d0f24081140042c8460352425005007d81c90020805034075000d2624500d942018000e41160b8880e40d109480c1580f0350710031400c55489411040f03c40e100c05040030302070341c0b040c10980c448400c00e01106071740548600103984a540700380244060502a141103c1c1511000740d03480d40c0d03a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 176505098 1250 176503848 176503861
    0x30112031407050a0309091401030809190f0902030f0c09010f0f0c0f06020a020705010c0218060118031104050a0b0a05060d0b0303070b0f0f0702060f1308030a05060112060e0a0203 79
    0x1c60203900800340140c095000000205035100ca250804d4400c002c0040003941c0d481c21003020024800d01000303040034410001011140380020102c0c0c1c00c109440f14041c052070726120840c100c10f045901c06417003107401005004d054182008034551041c80c4940c40e500f030000306000205601600c1c108401400502e00c1d070782d07148034840d0107200d140c1074020b0001030b9495940d1170310800030b50006004000501401201007165807058000400040d0000c082c00c0340c1d20031909071585504000360407941440701c08000416140003840c0030030004c60250501c000103c1020b4140800d80c0c00007884070003090719102101d0300070f03501c1c1e11b01d940070740b00d05585030360f00c9070a078042c07010081c06020091945031002141c100100043d088550b4442e140d034115109460302c80340c0c1d50020141d400d45188016811000004030300500ca903444e039901c1134826281505103011500e4080c069402500c2844259882c3e41c20000d0950700b001104000f000c4c0c81c44100011b0349402032400a040c40544122040c4d80c00001080c2e2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 176506348 1250 176505098 176505137
    0x4060609020307090608070f080c032503060503060115230c030409060503012a030e162303030a09060302030c0f03090706030f06060c0602030a0621150203011203 71
    0x180903040303421940d0303003050700019018040c98803c210006060800166490384540907501e001c8400d03480d680c84940f1100c520090030380006095023081004a050702d044c4012203040340c2e43c02801500c0001e001c4d814207040c10300b802016003140c003650142c6c19030480d4107548140528040800b012070000d00280d420700c1c1c42c659201724414400e003844085800304040019030300c40000c462046000304903151021458001c40036a000195038122615182c0d00d0ba46802600040c648062400070b4401c136084200c0d06c0c0d0303000c0406401040819422109091503000b400c0249507040300c0450007981410440d01c0018881c20f102d001d03c800b00b54010010801d50820601a100b021824000d580d4980c5000c8100c0f5640d083e03d44948000681031000d1042008007522a00c0d00343e880c2a501c0c412000b815407100c9010b5440641628159542e400c80003609a44251400750310070182a84400c2c10b4080c1d040804403500d0700e01140f50018410001000f0360902c951450f0340d0554181402100d40c10090380501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 176507598 1250 176506348 176506361
    0x9070e0a0509090f011a2b0803040c03050f06090705011b020a1712040308070f0809090405010519020412230f0303040c080303090615040209120114010501140702090406 74
    0x80d001000401400f56081d00403a240000c600b449000704240c441c0e111641260094410040343c0068243c0d00f91040b803001285190580d568604409082500725030311156517901c01c403015102ca021451007802081400e10100d0040c0c0004802008141000d04001b501d902c2c0038811a8140084400903c5015418480d52400150010105002e590740e8011461700b070180110002d91030b0040f1800c40c207100794148291811340350401442c0d41002100d030b0352510b1000c1038110a0380c14904c00d002a040343d565507207815205a1003040007250f181000b41e080440ca40342103200d41e480714014042071210344410003020070b00d540c201a800d1340d42070604101040d03091a922108500e4000d80c01d8030348000310300000031802588035144410805594505154903030206889550440c0c000501260048122001107500890000d01c0185064092000110014440351000c280d03651500103c0d07101c04401c0c10401d00401d402c1c01c100c90f80c25038a54001ca210b114040c0c00030311826000d00418103024560b407250 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 176508848 1250 176507598 176507609
    0xf09100815010806010b070c090203070c052a01030e03030a1107020a091e0e061b0c070914010509060604090504080d180c06090609030f020607020a0b0408010501090b09070e0a 77
    0x2148000500029081d00c184240600200d03882804000110394141c03004855040f50041842c505103404d10340a0000707940080c01140400032508400b00208105000d9041181c24806803c818084001d1500034001c540305030160600d8500300b104002104040112980000d40c100b00203030343c0e00c1c40103e084150064450194102c01d1200001c1134280c480d2b88400400c410400b020903074030240580d0b200a43d451640c440305140c200001050a4030029505840d9075240f09e03000d58200a501c070305262400415504c5202c20b5a200c0a2903406001c2d8a280e4501603c400d603000042450020040707070341d5100c1d51142301407150342c460020301070000761002d84a0411861800f44800041900f81c0c0b0405403400409680d091a9284006050f6000d65245c7c400c481035034403102d00e01c5184d034640416816a4520590300140100320f007100680d40d40780158060118084034030b440c1d6041c421340d142110b10580021215624026501c1403e075583d03548203074003400c940303410080f00c400000402d402808a900a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 176510098 1250 176508848 176508853
    0x8090610081e122209090f20130606110106060f0c0305090901060903110108040b010b07060e15041b05060f07060b03010c0201020a020d210207030216060c150203060f091008 76
    0x20040c252500d24a112140c0803115511030300c07507151058401150b0421b200100203c941002c2c0d20300090076041ca0051440e40e90000c0e044944c412408102c0048407480300100c1b00d9903900c0c05000054010109807456449200200700f61410000090b01a4001200380c00a01802410359401c01d8844c0040711165100900558000e5a5500015280d05280d0108446840d40da83d8880e940323511400081d48180d8101501e8000760f464080514000d03030004100740d40d606d071944098044000e0420400305070400103200c588041c40c1900300142c0001e0515290042c1e41c448410030090b594800303098a29030941c0742583c940d1100185080c3d0006c1840141c410740650900d17241001064040d4040c10070b00c07929409032096845121011154540300e90070b02c016010103940c0c0802d210309a07a0117481c14dd4401e004507042400365070038181c0700400da070b80040c0000701658001c0302041106011003021491200c8158110300300240001d00d86d000c50355601e4050702c504000250107070990740e184401840c00e4003d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 176511348 1250 176510098 176510107
    0x140316030e011205040c050105090f03010204080d08090601180c120c0305010911090102070902070305070215070c0905010e061302130e010f050f01120c020c1008090610081e12 77
    0x3000380a0907400900070380800c060342e0642098411600480303109613800f004041c9110700301401901d07150003070955590041b1035000400d2003074800344000c1026110700300040c1920300b1045001040d4050040040b1a2034000702e00400c4494072005d0f201d0800c0f40903034800700d18618110021265038400d4070b144d640243c240580c0e6030500740c040d4801d1b4169400490300344100b60b4a1408101148500000740740140e12a0b04100110b4440d64003600c8020320034903140d031a04205400003400031003250200d00c401d43d00041c8070010015a601c0490040007606001e020a40c0340203960107240d00010300c1640200c81030408241411503590440c1e1b16041010888a50580c4a03406a0150f80090003111105141c52001043e2440d29945600400c0301c140e660500f9800c0b80310514001c2d0081d07450700415881546564882c0b41c3e10401c07280340d02c1c1602c0d07845141910b04815090f28004018052203160300c0210380612003c540400c20449490301000d12001329800401c05521785840d006a01004650214 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 176512598 1250 176511348 176511353
    0xd0912021914010306090b0a032003030c0601080105090115122a0501110606060322060207060b190b1902210910020c13050a0b030d02060a15050a03140316 68
    0x1040b42c0c142c00c000781d80800c00940c071102100211201d40d05203c0d880f00c10300c0070400005101e0078a50084441195002080c041c84002003895a00110700d110b516400100050007046024852aa0b01004650007844410f078611810b030b0080d0343d10300521742180414520041803105040c0403454400610705010324807070b644c0c09142c540b041d44d401420b001400c49003541d6104031002955034051807006255a1440c0c42e501043c1000025050280300c0814140c41c0340404200c0c02d00c003070078050740148001301d0301c1403103541040540d500035810140c01280841c81441400000c03401d491514018081094001c8443c2c10103a180002085e0320891228070300424042a100110203401ea0394002c0d0b500210380300103400240e0300c806814500c560440c054152402d4141c4a0381c00554010400b214005003285000000c2420b0020b09180714002d40c2c0000280102d0b140644100d9101c0ca402600c409041410304000070802902440050610074428040782c8641400780301300c0c0da000d0511201c06190b00c1051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 176513848 1250 176512598 176512619
    0xe0402130602010e250e18120a030b060c060105010305070210090f0c0b04081207060b0612010302030c010e01020307080706060b12010305010b0103020c0309040c020304170c03060106020d09120219 86
    0x1c13106030099000300082081c1c40940e07003400300c0c006802850945612800c000c010320454800a00040f01c4c40d5000b07145068200b003c0c0488034100380070400f860f56500020401a0a49060304182400b0300010072240c90076900124507581510300903e0301145039110960300724681540d06401592451501f0110303420003904880b0301c0b8907580300c1c880c0354000030ba0744d500c1c000f01401188140310458210101c08070384010311600500919114a20010304451a2000300b6a00d4000b84405145c28550038014800d500c2c0c01c01840e2010755007440c0ca10b507140c000400003505d900445000a15040d4046418070030003c094001d90040e0584004044d1140d544041c546002c5a0a11040d00d16510f0900015101e5120b8002c503445030301050021450914507809110013482e4405420046010501002c9461061141d485440c0310148005040b154505010142003500c181d00410075984004225411590400051810ad480015103909101d00e0750012031152405680f11111000c084440890b280361603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 176515098 1250 176513848 176513861
    0x60618090203010c0302091c030c06020301082508070e1003021005031806040c03150b19060e0904030818030d0c0f083301030612060605240a0e040213060201 69
    0x3140213100d0107142d80c9050f07080380300d440c03400c0360408505e111403c1c0100c43c5030107640c0c03503d10903d401000305c00a03488110480e0000e8000400c1d5400079229103280315035007a007041c8101c00038141048100c1c40c00c1c0000d595084144641c1401040b26000078101d00186110000199005414407001c013485c8400100341d94401c03208030104c0d200c58280741107180344c0010454441c903400800382000c80e0071340e21059200c00300d1380480d000e09600d03640340e4481c0f80c545203c038200b1080801858a205800d08030050b11404080e5542400780c0c40034800c00c030200e980000c4458000321000410400102103001050030b51254048442c59035082c55050250142d101c00142c04005050390707030b00784588803489210554a0040c030b0031410b000c41c503081001d00c3d440e51041c4080c0f001e014140002d941da078072003420090030307200b0000796880b5684074401c102c141054084a103248d95940b01c10089512840423a25980c02154900350420090290060503510345904a440600c10303601040e003126503d01d07000b4041d204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 176516348 1250 176515098 176515103
    0x3160206061009260303040c0f0f0302030c0112291806090c130b0a0801051f0806040e1f05040b0601050a050f090d0b0901050901110708180102120307051314030a0b0406061809 77
    0x440e945c0004c50980342b0303032642c0c16254020084d00705142c0d00fa004480283c401d000c082c408a644030504a04c01000c2d600040c00142c04040444034241d000081049901c1c00c20703030303034188071550310104541c076694403403816032044c80c1400d01034442141401e4041c01c6541d40d00100b98203100054180b044542048010f030403180121403d80010200031f0700f440c0c6128580e07103e0404942d074940071444d5031034580c00c0309070014201c1c070882d040c2c00f241c00d4600041488500c00401c110f40d41e88103200034005e01c0c520044d803111003070a06500d4040c0307000c0000d040e403140101602031640d0200345a112a81d5107101303030300e2140e04104407c4140c104104420300815041c0c0b403205856181c800d1403240b8034809010780d46990b41150009040007259091641e1031000180b0260460080651544406400d00044e50141e800c0707a40742074503444907030200d04041c40c4581016100390a488102c5002d40c1c0d00280200f4540d0344030364441410344035482d100c40648000e80282c482c40a1114403580a440c0690111640c10b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 176517598 1250 176516348 176516369
    0x31a13050609060a18050318150a18060926011107120305070320090a030f12020d0206060901090f0e0d020c0103051503070302011407060203160206061009260303040c 73
    0x880315040300040305a010b00034600d4009005440d5200041c0071190711601000c0c0c07050341000325030920700c1c1582c0d000ac8045000f081c1700548080a00708108002009070819041402c265810607450071545406107210001e4480c0c1fa03a100101c0c0fa000f0341201044080e461461515581c452070031901d41000c00758480d0000b441d03c07000070000361080c00340d1170300702420528000c03200d900343e071501995521501e1322680150000c240080003031005001103c4045c0505403001c4503190642c00242400401c82d6084d0856003c072050000700d40d1200000c40c110351000c43c00044042c0f890000030060012084410858040d02883c5490180c020560707040300381d801d90b000c100b155586c400072004649007501054055020340001e000550240104004620390f004031a41005000e5a0b06d03c241d82c802c46184240f4158143c05410f0290104000e0341c0241c0c085070910300d1650b800e000104845460f01c1505d140e000140c3c0303034041184015001e403000c07414010035a0f0307482c5041d04210f006c0e501d07184100798022 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 176518848 1250 176517598 176517611
    0x20a03170d05160f140301050103020c010e032803091208151305070f0903080f030603070b030a1a01020109030804020f06120c030907270c0e091005030d0306031a13050609060a 77
    0x114814418444217400e0003420900310b900384401100203420005039011a51740e0340041ea0620345040000e003c0e40415480485a900403181074801c103165818114814541801080000101c2c5484a02d00c1240c0920f003800050b61107482031025024106502500b100320789a0f5001c2d42003540d0001c40c85047c45403103118a90a803000c5c100e9500340188009000c8080500440f405200b028005640000000701190500364403062410301c180d1050300c14940ca036540d8158520248040031a10701e00b00001d0008000740c0c00581c8010b0458540140024402c42c2c10303480e83d07402e40c0d480c0e6040c0e0f4500308114030900983d1030031801a40c01caa0003034803161020700c5200c000064940300000e1010007070110705031280d009d01d0212001005401070300f410030140483c900c00c041207a126070700da030380c840c54140c1c8210280d0b40c60701c402d240c2400c1d01c4166007004c00d0b04100050000c1418030500110701c4504110003803566803100842c0c0702001410500400602583c01400744088000a11030301500200724108140c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 176520098 1250 176518848 176518877
    0x1e0504060c1d060f18060301090606080f0402010813020123130b0a140d0204051f0e04020f0f1c0e0604150516050903070504020c0102040315020403020a03170d0516 72
    0x52010304110f0380900100520451200c00342c1c06000825803d8030400340301c140310740000300c0c56002600640e5116a440c1d00c1000341380d5000303803900d401107082014145203041c2030300001e04590300244100d60010720400850704591242842e0f4441c4000d442300a1844104418a07a0300b130b80c4682c2c8002e0708012042004125898074500b11014068070741c850038036400d0b13100b20600d20764000403030b1000d401e9800d100000d407603242c85290b2070119124027581e20720011001d17006049948102d580c20b0180b4030520425500411407400c0b502c0d41c80d4160001501c400700280c04c0e9010b0b0700e0f00f0503266902401d0109d1812030280000311503019621500f080ca0160300c055a040040396001c0701c035100300c501d21801ca0441c80f8011801841000000703420781c2c100503203441c08101664000c180070011170b0340c000360410a008084040e01584580a5800d40c5010711f142c000540c1004a0f01019203107032180700903604811100c10031540440340c02c180c18000c0746482003031020302c01d0150fa4618003082d080da010214 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 176521348 1250 176520098 176520137
    0xa08010203150904061e09060f0501062111040e01080f0604030512070203070515060a06020a0f110105071209030201030b0619111e0a020102070b19031e0504060c 71
    0x3182c0120942030010401800070801c0d2010301802c20343e000c660b20020050002184421304002244803040414048410b141400858844501d07069200b46000014003065a00c40c5040700c45200d0000030141c044040d08040700140bc440c2c03804101000c0000d0001124204200d20354100d9030f080f402e8500c50000d91032055100c14003150000c00180040015404800110100d540c00c0002441168105905075450030b1070001c8403207994804001d071208200640c9881141107002d0411072014000a1302e595840200001120303600805c1001049a0000706900c00d4050340d0115800000b40200c041c5240009000c52542d40410381c0000e080c590002440d00b4403004540d110f101000011120390401d080031241001c4502c1c68250b6030040206847c245900c400048000074480c50141541e08460301c00646420080c5d400512546810302140c04504500c0541d0340039040981008604034280c01800c0405071030000d10060f410340380c10144400e0000903808112049002d80300d0080e9120303081001e41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 176522598 1250 176521348 176521351
    0x90105180105090a0e2b020703151a0a0b0304060501060504030b13020f04060303031407080103050706080601090312080717061309020a05030601080d02010c171f0503030f090a08010203 81
    0x3036680149100400c40341c18809038041e4801c450f40000115070890030a05410401c0118880000e00210700360b540c501002c03601244002c805500080040d6890741d43e41c010700c4c101c080e4400c2c18590f82d880d8440c03034982c0703800000092034400410040c40662502440c04054000703450030340704546024000b003003039030140341114140c0e5000f4841040980c1c0f040c1c0500da0000041d2800c82e085000501c1c014a10f0711940138010240d846501c010502c0354a4075042c1e5400c441c0204000104807404004001040021031282c080e80c400d89072242869031002c00582d410720745035000808084145450024150740203010b2409141d032030b907800320801c41c06a40309200900070748440750b00c4605013030a000800529441802c0491010308003040180e40c6000080c10854241e100c0002600158001900d1035420f1154014400c00c0f41030134a82c3d1084005880000500101440c1d13142c03a05070020709a078410100d0620061400804481e07403a01e248034034400c1d0f0707040312510f1402001c030050702240b0b000301802546e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 176523848 1250 176522598 176522629
    0x90103050a050d0507020a0b09180a09060e0c0f010804080c0a03030506010806030c101b020a06050a0210051501050f131e0503030309060703110d09060227030706050f040f030c0302090105 82
    0x10801f00d00f4084420b22562282c1c840c55840546807819441018590b940709125880e031500000c1c101075641007010a54410b0b5051103001d41001000c030075250741d00c80b9940e030240001e180080c4280e6032860445014458850b120310180300c2c0c064218101541900110711406081e83e580d1001d8440d84241a42c624130710310307000c0d808030445000c00e04491294003003910000e210070006c003503d05260041062040b1b180c0240d000140c0004100d543c590b0104400e4441c00d00f035820801c05458551501150328107842525410480300248041805074041e00b0303100c0081007094051a0340d44d503900c50b615407940d19114062021074403540001d1500d804802d41c0e1081083e00090641959042d8049004160020001310395481c1801700d0000c0064500c82e0f00242c0d40700b00c200580d10342c022200c14890100420160303c0000f00a1090055614042060303012110f4a0603c2501c5074511340e06458140641c3d040300d034041400d15400024443c0c5081c4000450340240c40c0d51184d0390300d034014007082c000e018084 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 176525098 1250 176523848 176523859
    0xe01020406030b1f030519020c07080c0d17090409080d0b0a0503030703080109110705030f030103061b0507030305060a0504231506041505360102010203060d08031005090103050a050d050702 83
    0x20341c4c0002c0e0194128a5104503e020410340d44e02c440700820040703030000c501014280c1d018100c1804400410406081c40c01812184005080d41c0d40c0d90700c00340c41500c45000204131f24041a0900103460306c2d00440760741a03201c203086031504201349084008100c04003c85114031221900044c00b800c4c0030088802080e003613954081581c3c00c01046c000601072889141c1e141043c00c1110802165062028280304d0721f0320703500703169a54550705140040d02c0000b402d00b0b080d400440c0501c5180c40d048400c4540c03541d410708020070942e4070880001c80c04403050b48500e41240c140300800001c402401d00900c14103400d811013403810348030582c0101d003080d0f103282129009041040700740084d040c8038440640c512030524100c0e2500440d18619006410b420412400c00c06191490140e1148050941e4002c1d0000384001c5080d440d0900c00500554902c10340a4448900040071440702d508030385c0100041c290191413155956501d1920302c0e036500c80b07884251094081c070f003107040c9980e12030000c880c0284c0d0020038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 176526348 1250 176525098 176525149
    0x150206180312060d0c0f090608070e160306080d0c050f010506150d110a0801081c0206150402070b040b220c050111010e0106091b080606070b10090e01020406030b 71
    0x10b07550701694000d0f00c0c055001d8190f00300d1308001180048601c024140299005110a15191341c440680e40350340c000710860b80110405010f241d40540c0807940c02034450584a94040710f03c4400ea00412454010b807007c3c3c052200c21010075600004070144d51803052080f1440404005a4107003207500a403681070b0300c03420310801410f4540e901c00280c85103000d56900043c407107a0019004200354403001400002c580c5900041007107038018460304000c0e104455400500ba00c00200003502c0717800c000d00302c50b200b64203400c8003c03c03522198161002aa4032451144ca281042d0400c090184801c492034120344003007496480d035954400000421180e4001091400c2d03074102030040d92003924992a510156603114500000700c0300901940f8014020110300003040b10703d00b1720b051040c4404a0100c3d00340100c042c24030165807101801c0700d015a411840c080c109407100c5001031034680c84d46c4d01a460540c203186000442500641c003c2088441c9501d040100600c4a0b0a10003240f4241c4c6200585010600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 176527598 1250 176526348 176526367
    0x6050a0b09030f060f06100302070b07110705041802120a03090608042f1504060c0f02030307020901030c0e0f0705070b040c08030c012310060507050a06061502061803 73
    0x805044006001000d94088800d0f10410500c0c14908a0392004c01032050020310003942026004406c81c1d00207490103500d40841d6454500d464070002e4104001c1007032001e000c010015052001e18081c180c0140107112011401084135802011413000340e01c5080c1c0c9002c1c6246500c0c00248254003281d1545404900c2c80c03078140c055603640c1008009880014000562700201c9200c2ca000003541c42040105410b40b800d40d505001c1d040043c1c20104040740820001400025000044080b105a100c41f2010f040100d510201c0d04600640300001e4010302e1810011007044400703c00b00c006d490000006d2141603a40d007804c070300c1501c1c05a8200c0c0c0401c0341044610081000d80b501742d0390050280c2810403100f95034801e0a89143e205461005181e5941c01283e442c007102c0b5445090300c65111642110700d800c14102080d4950a144a4034080c07010003d81242000b4007400306043d8240c21010810490b5561480c580705580c0154002c001405440001201d00c0b041060551100040c00c00030b40c02e112070310 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 176528848 1250 176527598 176527619
    0x5040e041104021303051f0b030c0910150f020c040203060d03030216020306190501050d0809120c03010f020c0120030a090309030b090a0b070e310f0e070906050a 71
    0xd01d40d550055000c00c401c1101e101c040603403074011403242e00180a19010102c4500354400f000b17191400b030714140306180d50b4a41d00080c20500090044070039410645403148884e085400b258884a55644000ca2815105820032000d9114007019025101c0300c1c0006030801c012403004503003039503201c001c07901e01e400031900c01d078094850103041d041100c0c620310f03068000034030781541100c028510344070040d1480780c4041280070311401805c00b0f903080500f101c3c0d981c1d04d9210500810341e1171030007002641c41c40f200102e4200f10300c82c460803003e002002408074610010010b5481004400392070360a0103004a0443c08142e140b550603052403200c039040d500c61101d00d4002d000882002c1d41002085200071000c20b29010059005d900d00314003c2286010519004079400f80042c150300a02080c100404840d4880e820a8480c001f1801c80c0461050381e00d002c8100c3d45c15040b0151058549028082c1d40050341c0fa80c802c081c4000908119640c1c40d0344d915242c2e050701c42c94015545c10048001080240341c1c0309 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 176530098 1250 176528848 176528873
    0x4081b01050c0a050721080f13120302060610020c010c02010f050f121e070e060d0608101e11180f091009110a0f0e0a090204080c0405060105040e04 65
    0x1450140c1c079100c1d0301420075140c10141c880a59164001c513008020114480100454450581041541003170440e118941079005206542d000a62300040300c0706143c00100030039020b810f494106010b0b842490030025030b80c00d4110707100c40c012805d03030819a01641c0001180030001030165682428100e0075801150f03010089074005040c068140100d01032009003030042d0a011644c5000d204003840e001034a9264080e00440001c3c50183c5001800710f0f49034059401c1c031f00000150b810503910800096520028240ba601190081c05441e410f01511051a04045070064500ba9440c2d00089482c1c1140210759410342a0959008101f00cdc3c0c0d5130048141000389500e000041200c0803202042010902c807902c221a0340c9098541c0740c5d000e100d001e03980c1c46031051a0325001390040c01c04508803005440061a41d4800091003680314481180750307a520103280251410b01400c0d91110b9961345401d50b604400700e81c4521803801d101c00518194807c10980b07045854540c2030794121b407070b03646070401380054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 176531348 1250 176530098 176530153
    0x40b15010306090e0f07050901050a0923010303020d030e010e100e030d090f120906090909050f030a03020405040e0a0203060403080705070203010c05070501382b0b0c0408 75
    0x440e91000180612988102c8000a40b00f4020b091700d1420b0102890a0820540003070388905000401404140c4660b901981903c5410000203060342103441080d5540e505450322080780058440007004050340400c04507001403054800b40281c03000c140020307098175a4000f000060342d010303108400f10a8095044003000510006c161781c9460007141658065480c8150305a9945859900d808100a0703101200c02085a6902d05903600750308241d402000300d01c0070311580c0309407621958a00103008051001d8060b0708010310840340c0e10684840090041c0d000340c1302d502e104a1500302c855103c0640421102c0304c555004000d4010b55135283c0c5d080e100c084016100c41d0800c41e0621490005071000d110b070080c14540c2e42c55413512510907161150070342c1c0b699481e40048140c0100d200c4c440304842084150081c82c03202e003100c5c0c415400004150201440d030710b541c01c500031a903282c0030481e201400403007503980a0350015005e81d4407040000414812881848010741c0402411002054650490a400c2c00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 176532598 1250 176531348 176531351
    0x1150210021c2a0c1104051807060206070909020a050909150a0506030405102309060f0606090d080d090206070c09050106020312150a032f01110303130804031a0f0f040b150103 77
    0x800c5c01007401c84004446c1903c50130100e10494a07045410401e507002008148010011440e006000070502c440131300c140d03604507401044100009000c1c02c00d030b98030703003c010341400d03054039040c2c050304186004244414041c8116080208240c1003503001c0301d10440d040310052a4a176141540c20000780b0b6001001d002c181d002c2d1074259200503405003502d010b1036403000100103504000c030341a05107000150505200b04c13400c00c100d000d81c0e10303220641c0c0f038840d8009140329215490040b91001505403001c00035806800064501c1c100000401400182c800880c800c008580e01e40c0420781e0b9a21031013416800103409000080d070700d0424074407412200040076046003181a038a62340c40701c482c810b504044171100c419681c1f16804001c03c60650280c0a0300746003c6290401074003900303882c3d00c0081c0c0b0341110012901e0341c0038140f08507030044070020742d80b000505803194110440c005001000361004c41d4200710f8100821004441306480b60301540d001804004a41c035995130302400c90724400703080c4d410b05 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 176533848 1250 176532598 176532623
    0x12020601142d03161512090b0402090421020102042103120510090903030203070f020705060703032a020303100522020a0210020310030c150801150210021c2a0c 70
    0x500c83e400304c1c4801080000c5c0d01e004010701c00d440c040c2020b00381c4d0040d45116850304261a01141d0f01e4051950001d4050740c42c1c01007511207040c0079104000c00c54840c03031814180d2102105241e81540100101c8900002ea201e4920001090401810a00c074018000903058005845801d86580c0441d40115114440b00d1465503100c00e902c007598624001a400b00f50f01004100410350000e0290201ea445840517003903c41c1000001149070045450103010142e41c1d030000f1f08007551500341001040084000050700100c0384e413000b5581d5000700c49901404051180000325400c00d005c0804183e940380c0780f460712080e080d020305402908000c1d03030581148106800002480c00c10720003107014009103841031960300e04609080700c2c808110361090300d2411503c0300c500103c9500c0034119041d2031080700802841c08003c10102d280c5200c0c04140d0b030342c561002030703942e01d00031003501c0e0541c00d1403022106001c0030002940340c0840c0325000c8006505044010304658050344244c078459659446411204001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 176535098 1250 176533848 176533873
    0x30405120a02040f020c100504120e01020c060f040f140109090c020109021801090b0f0609090601020f060a0b0a080c0315071404090606110307030207030b060d12020601142d03 77
    0x94844002c5800206a40080c42e030386c070381c0d000744442ca4605160b014240030754109a0b44002e000300003541c85208000e90100c05000e2a03100707005a8007410001410f240d00c8030620180b503e07840d400340c4a0341c001420810b46c0021340c01d132990400a130b6514140c4034525014913001c4a80080c0101c90582c40840d540d5814000051341c90402c49000307991031020115132581014603640c115000d03461814403c002140e0000c01c103641383c20454007242000e5a001c081e83d103d036001030f40303070852415034200070340202d600304080750045a00445001c03030111151250a43d44915452b01c802c04440480d826401c1032001007206129001d20507041040d514250354812601c52080b02c80e50400d0308048421a1503880401c91640c1c4075106040f1066145c014502e000c009580180d514103c070b03c4000d11918400700001c141d5910906006500c50308079200100100200400944030242409443c008461032682c0303003010f09003158034100d5655105481c0003001c81d103407070346503184d804007400d16814858210380090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 176536348 1250 176535098 176535101
    0x50a030b0406022b0f0e03040b0405060702010905030307080306040c3b1201020913050f0106080702031b0c12010615030504060b0301090b10140105030703020a020709050702031201090509030405120a0204 89
    0xf03507400c4401c0001540e1401c032076208203840240d1b1511400d640140000d014011500301120b00301c40d02120111f907a118035100503a503815217903001c154580008114613050021900c019440b03150111005c00034100b400c07000351072040c4c00d0b00c15a40400c22020313107402c1924840304078400780070b0b2200c07000c0030704c083c110300064404140020190380b0b030350013050f0401c10342013810b00031001070001e1906000c0d0b890b00070360010300084c0500c207420030070440401085016001740b04448003400e4203040c100115840c00100d90362080b030b4110540c06000e0340440802440ca06103e41c03000c0d1424400d003502107066031b480450241101500c29100e00d41c0c2c0302c00302c40fa2690244158818a8401c84000040b80307400c0814855802c541d502c0410050041c0c00a02c4403680c0c03105c00c581d40050941001600d0384030103542245084400d42140d29940d01d4141030000280d0004060301040017455030303c800f07c0c0c0e01d030301104042c1c4405585450280e030082c0700a019a01c4c0549076071111705210002c480114203203800050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 176537598 1250 176536348 176536417
    0x2040902091609050a12150b0406030c082e1e0504030e1c03080109020f070b09031b0304030506010b030711030a09050f01030b0904030305100902070b10050a030b040602 74
    0x5400003180e40b18842071034126503001c00418044130491001c9160100e448141d5081d800000c00032030400e0255421064254800c1036840c1001c0c2040084548034904003c84075445e010f13000c2c15102c5c641ea21002007004d80400700089003d01180900c40009503081c501a0078015181d00000500c0d01600000300428407035144568000c2d60344070307100c0040005106088407170010041308000325108c5a0040381e0400c800c83c5c110341c0b02201c01030f030324540c000b10f1500c039001e03c0307074010304140800040c4442e41400101400404003091400c460301070580c080c2594900c100d100c0100282c00050040003082c4208014541c0075000d420800910808035441e1421544080c1d83d50340443d81201c801c1c0702e1030820746213580d0294030070300702044501340c0000001c1c1e0141c0002c1005040503220300005071288420600c000082031085419500c80055150a4500e03100c00c40b0a00c64030459200006141d04c2c1024501d401c403500881d4000045e1103e81300d0034040e502c460460b80b50f04a2101241031540300140b000d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 176538848 1250 176537598 176537611
    0x17010f140406050c0703080106120912180b04030b190b03070f080606040519090303021b0c04141003080703020c0a270606140c01061d15180a090204090209 68
    0x101440d1800c0e1600000312640980700da1200281840382000080e0410b0300c845c196880c6041c004000a0168114402f411410324001c0a8450218940001503040481000d0790310100da130042c4e040b0788808160040d03009500c00580180442c0e0007007241007044805688a8403c00032001c0388020401c0040f80ca82685a88403000c1c81d21b001c2d00400910906011403034202d01c045400b8040703410040c40c0a10350105460746403000c03c0d5102d4580c0b003054041c2c1d048070b905040d948280703201122104000d03904c07007601c0300f043c034051420301c84400c6c40041c40906262056003101048002242540c4031101c040d040003034110103600c00c104a410542d5a079410080090480103001c155078220319149001c030702d017144210940740d403c05100f4410303503030007520544150228001da60b4644500312180c501414450740011400b40058500ca40302040d0308054520813050b440080045148180522840d01c911075580c8032741a000780c02007800b40c00d0390b40200350100d000070000b103540311b09074001844044041d20340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 176540098 1250 176538848 176538881
    0xd090c0f030b1b03070e19090f0b04051006020a0f0c090203040b07110a051b01180e04020102120304030e010305090f0d05091008060d081e030c04030c0902070c17010f 73
    0x2001483e00e00c080d40a0030603104122024103500300710030301508075003418003014425040584070b42c4107100c54515850040400070410310500040c0302c583c000a16540804c107004a00b0240040d40791880141c040d400c441f0a1b600404102030f25485020f901c4400d0101107861059010340011b42d289180041c5024a00801400c940ca0900d50009031940030103550500d62078100b0300c00c0c407002c9000400c0104c0d40300b6170307080308000c3d20321080c004132280c0c40d6801800c0c034000c000600100e916544c2000892046200781c0031100e500c152104251100e01040720014001100c0d60341d914032951083c0c21a0360040c401e08115140f410a0201c1c2c6810104402c5047c000103202140c0e41d03001d8a010042131900300700d2814504203600f020340110341214035000c4064441000000c4281c1c0d017669020000e409000c480e10307074944a00b4100c0700380382160302070321082d02d2107003151001150340c02c1e55200b141c00c0b080e88600e40e070500382d01d020504000301d00643d100c07003c25540e640407544040c1e014001c48a841001d12513 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 176541348 1250 176540098 176540101
    0x815091207030810060e0a0303050a110f01050603150f1b040305150712020c030d0b01050705070b04180209090a110d020a0309050111190e0a0f08011401090c02030d090c0f030b 77
    0x9095120481e25481170040000c00c0580710340c1c03515580e50503000d682d0546801559000a90070039076041400403c10505231045804940a001040d8811070081c030b001c030251941480d09403400c0c3c01d0f000048e5090944610200003040f1400c59100f40c1010749565040001d003080e640e6211903080042600f0081c040300e540300304012240e540b2030121503c20420400450800c07400240c410381d240183c051407080581e4403081c0f01200ea0044040c4c03031441e6409800c85059644a001c08101604103208401c0001c2440d1210fa110301c02c60700a880c1e28941c0070780b4060311aa60b20603800007810701210005c40d500c0701041480e0240865000038120b000d51600d0204842846182c00b60850750040001c05001e1400d00c40c583d4240d942e24200340b29800c0a15041c40b48900c82030001d031600c61a40c0c003130020222001000604a0740c190001140300400103901d225603a660070700641a5183e4032803810040c1c10400c1400d46040281d40007800c0340340a9501241201d07158541d0461104a035003054998018000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 176542598 1250 176541348 176541361
    0x4051f05100506040b090402070f060501171b0d03080709180911060c070b1305040203041103011a060d0c050f0d0902100212090913020907050c0d0908150912070308 72
    0xc01c4000141420303900c0510386807070021841c15a0180d4851030748201c3c2c0025070340007031140c00c1181c910800d0b00140104560350f514a6403402200b005544442e550180b5102040000300c03215403000c04440c0500204081219030307404840c02407000346950705002c85100041402058050205045e542c00310000a640c0c036142424820410290600b5200d202d041140c10800c40380802e400040f140150000764456405017208a030303005054200d95005032010040205010100c0001580028103a000700103030114201ca1200540d00304511035003212040020000785640e60780310b8158243c0034030b001420304d00905000e09090340301c55108241d0b0b907199100a802d61500100e4111a0103042c001000d54542450318003a6a0241002c010b03c100d0102002401245c14403400100b440c1d8024039160107071604a0000e0305642040c3c829551034411114450b0115004541f40000c2d501000000c20000c120481c034145010001005000c2e14050000d416254040b41030240980038444c2d00c4a41c0b2510300340 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 176543848 1250 176542598 176542621
    0xe04090f0b010816031101030e030f0c060109050112030e0108090304030b190501210219030204020d1a01050708030a020304020d08030103140c0105040506090d1e0804090c020d050a0804051f05 84
    0x80000f070209525000801c00508401b541045801d001c1c03c01140c3c408000c030400d42103014400c103a1800304c00005d1100b18041010440074147c86a600040000381d8880c02a038021801d00b103001030104c2e5031540c50320620340c000c20349258410030500c1100d00e02a100d944100142005584d120748000c004005201040d0440c00341c1409800c0050007034220090448122055096403c0c010703000d1980078408080c1026600360600107903402410030f543da6900c680500c00207002202800c00040110010324515600c42c2003141e6515030442a420304640391030700000e00a500240040364040344210340b01001a0b002070255000b14007504003c05490709480d5644c0c02d0030320740303100d6130304100c01000309100640c0e031181602c45c140015681240b9502c014a081541c1403c40010509041c076440301403410005135200800668041030310070300002c0e1680200b0799941552400d2200401d13002d101c225240c512900450750312601450495103000000c034124000800041000e1501984800400c45800e400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 176545098 1250 176543848 176543863
    0xc0c020907030504051b1516060b010f02070b25080a0e030114010605032e030203010b06070b010e0408120a09110307180b2806120902030703030e04090f0b0108 70
    0x10381414421450180d172003544402a01084040e04100c1051800c0a510f0784000c540b01840343c900060743e10f9440800318001c103071110f14229071301801c0c2082c0071825480390f403c910a650b070a800401000d810310284030115049142e1088544100c0590310401d014003001c1020864007550b41c41d50365803904e020041c101100c5956003402a07042c502c1038450321030b880095034110b0f695458000c0d204d454103400c1150300711000030300d40c0201584c0d01c024035403104061400802c4078401c40080000c1440c0100380b01040c0034110b0701604441d0208010480d420301841c0c856809071045a42c139203002c190307075440d000d044c0d0141c0d10000c0c00c0d5900d11030201003140411068140d0344c2c0c11001000010300e040700c002c00085c0d2032602c4080351910b40300c1d80e08039511103400703e034400d0305002c00f081c01d5103494280242000a4a2007150700090700d040c82c103844c00301a40f140d07120058024005e425951b0460300c043d542103070188152504140d41e03842d101c0108140d062081d000c148030f440210b609515191009203080304 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 176546348 1250 176545098 176545111
    0x30b090708040201110c0303030f0619030b010501170c0403030e010c0b0a02040e07020a051b0111030c010905060609010f0501030c21061412030d0c11100b03120a08040f0c05040c0c0209 81
    0x148440c40700d07e58001054070350100916030341d0006a540d5101041c140e51700b99461210419108501004215610744140d041e25000c2c4e03500c88054894a54400d4040344c280c0c1d003001290010017062020038410840703681c0243e018100b5010382005695480900402150544c108a6000c1011b001081d00e0304001508000329100a1403004c0c40c1e0b0312016180c2078601e4030300400801c000800300040e40150040703c4801c84100903070740c42e0742d46440042e02a20034203604071003078010400007441501d0f000984505032074490421105403802c2ca030041d801410308031511002e01c9090750803140f00d00100000e800101c01003240128441c0d03d42051095103064140e80349100e10107007818a44088400015102040c1030381d0808038400f1500c131000da07039800c01c0002d121100c0c00342c90f0849403082269004100202d50990403030340e03281b0420001c2c2c009809400c10610010768001e0106020455000d40c40300094050317405840003554440014040701c5d084605036011034138400310350303040d4901440e180c0ea0111 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 176547598 1250 176546348 176546353
    0x7050105090105031f080a0b06030607020d0f0c03050405040c0c0c050f010c0f06060e040503130b07080307081f06020a030305010e0906041514010e0103140a0b0c0a030b09070804020111 81
    0x500c2000030f801e9000060640201c050b440ca2081180c40040200100800080c4140e03400b201c0c2c84d081542484408032122404ae20401c800f103910306100140041c504840343d51403121080f00054100c640c14589007087e41040010310002c1055a91071041d207030600900d854a40d5080454500341c0340710030565101c3c6110710016403002c200b83e40c211502e0012103a1111150b5107034905031178150001c05090304480960b28407501040100308000000f003107001100381c11000b07803558415214031b15109061005026000500104080c1d501400c1d03056000443c0d070211404100c009580a000c104071a4002070040e401003009000349074040c4100303400350881c11030b41065441e1821704207980741809423006003a480700c0e0401040c55401c80c2d020503001500c80380300c89003650f5541c1001c0003460080c0410b48400f0f0034405001c0d020f48001456003006940924508216a21009407100c143c000e0f0020500780741c0c0b82c88001d0241c0c1d8901a599208000f41e44030300c022400c00d400010074200c0070003402c40099 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 176548848 1250 176547598 176547607
    0x11206150f0815060112020c0f07140312030103170a020f0a081e090a12020303070c0f0501030506030105070905190b0408030316020a080304060c051204030c120c0308040209040204140a0b0307050105 87
    0x1170340d110401c0d529001d056800940c0e0740b54117001040c513226030305441d08800e000d0808003145040d41052100790b030b07840c04c8044800103020140c2265891000780300042c0380504506802416401150181c1a2010540142c03105004122092030520100503000c0f24036510020703e18194180052654100344002e40c6201d041000fa080411801d038154080d92082a801c1c1841004540d00cc00c21140c11641c45038015010a9460701c1724100c0488a000346030200e401c000000b03816003414401c59100d07080f140d8400c80070a2400d401d00803608003c840540c20481030250109100c0030100c01040217080000095a0300d207491514020500e2012203040d0440d0407035410308001c0f440369401e03030741c215030080301c0000c0c4841c45510580c0c03544107800f415101000c019040005141d00906c00070380d842d01481034040e42924940040f5240400c3c08401000b160801c80420050f0030301030070035030340948054000950540740500b110500e5030100c03902c900c0151608900b12460905000c1c3c44c00400083c24040d080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 176550098 1250 176548848 176548861
    0x3050603071e05090c0405030d020f0d14090405181501092a0e04151d06060f0a0c08070f0f140102030c0d1a060a02010b09150603011206150f0815 64
    0x191400f4400c03940300b035070380c0c0000c00c103c0743c3c0e020704941c01400020115900d000e02c084000e0b4a6100715010030340d49004000d842c503c017501448810800340400c2d088a032601c0c44101c1000028580a04466420103404202010341312081140042c241c4034a101c058480d890120717028140d5486624040c040706003e003191240103030803641d000c2d1004140c1030800100c0001c0300031500a00c0d0350010030503c01c9800100081042102104000d82061000d100c00c0035500c00c8140038051241c6a05001038110803c00503600c1031141000c040c9035849006003510300a540e8030340780300060300c1c2c85c4290344207000640c8010401100422508000383c00600950451804500522150003400c405084407916495086402070614034084204800201b07000e407a03101d04003000b8000c05050007694024000c001c08229100100401c00c22075000c014500c130300d56820a403060211a0310014111111529415000d03494aa080c13242005001d0890350034820f607180c01b040c24680300800202c441c07000741d45e0050052 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 176551348 1250 176550098 176550149
    0x20f0307120206160b01030606180e0304090b04060e01150f0e0d0b091e0102090a05040225031701060806040c0804020306011e03060609090c17031606021204030305060307 75
    0xd4142d01150344640303c1d2015541d10103030844501000300390b8003001001008020495111a055844818884240402c481041c80423561040c086c010142d01c00e1004101c1039007903030082d000300f0304082c2c000301d682036540e40582462502070f000720f010103a8103140d20f01d0580c0e00001c2c941e43c0c03c88615255070f0282c1e052000c82c00341140303880c0242c0412003c000140d0811b004102e424120b0080503044050503030708403c403500035008103c484c1d200c0c0d0031000d00007071913141600a56002d043c0381103001c4030885980b1200d24494080c03050840500189080441c030044e1418090b0b0f000700441d44030301c022894403070100011140080164024020040c09110251f200014240d0558190403890141600e140280b0000c40030f42e42c0c0000c25141c2010004502c1420b2138000340d100f58031820091480b00e4651001c40d05c0c50554507002880c692003417141501a501d014111801180220345c014a040b070380249000b1240401c131419030210f901c1c0d100f031040c0f5080400c00b000090031402e0a4580c0c0c10556800c00c1c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 176552598 1250 176551348 176551379
    0x8030723071a0f070b070801060e101e0c02060a03270f060b01020c030a050f060c03040302060f15060403030819054b0a06090c050301050607050a05060112020f0307 72
    0x40148001040b040003c0540710101d43e8410f4002c001c068107464030750001011403038240201c0c000913130403c542016606003141000b4502c0c0c0c0c652201c00c0c1c82d40403000c54611148000b01c4290410007820314039400760310b94400900c00b5020710b82d404106030360b00d204000c01702c01c1c001142c030342d11707585000480c400305804921903440700740d20200105100784a000100e240107880d428095240c0140304600081001c00507107620800191341c284d96441d6210600810342c0c1c0030440c0e0240241c2c00103000941c00c140000c202e00e5000c0c0e40c04070f240240030300000118030b00c0d0b001600700b1008240301000303000398407081655201410001010600442c42c050031142c4425042211500c400d5280704904680314240750f00b0713030841d44442c4003003055030014401080160b0100fa205003081c140342c0880401c41910901600b074402415850782031840e4a000c05001c2c881d0b109103804d0350180503183d09500018004c1c0070f441e00071b085074000042d1600041c010441e5050092091521960045030704001040c014035100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 176553848 1250 176552598 176552639
    0x903060f09080301080d1205040507060804210809010513080a0309021305090a1a010f0b0702040e010c120b0a0806060906031203040302030a08011e0302090c040803072307 75
    0x82800380c2400c0da9440509001a00100305110120020510b020009003550140b1820740e100c0d200107800e41c20000481e45c0580e806009a04003240034005207010b42c11068000c1d200b460000c01d4690b001c48480164903840842100191006040c02854802405000c0c0c00105083c9102d5445000303580b41a007902c40c5400c000705050b1100850f006543d03421161011100065405000504e811202d41d621044911000c842400503015072403030482e09482d00c58160390703900c0000e448441c2804000603094006a000320703400394039010312002903d028080c011076809661601440c103a014812074042d100c02c3c01900d8010034089004005146000034019003000040d10482d5194403480046410241c0c10603546401581c000144410183e00000403e03404100d0b944207e00b590302d0b50541c00109012a40300000c0b0314040c1c0b0148094904030301109d811821340130b50986401e950b81502411900200b8003590110031029400c041c4540c0d40301754030b840300004005840c8003401c000e481403a003480d11494 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 176555098 1250 176553848 176553851
    0x90501020d080f1302030f0a020415030b0a050c0f0706060f0801020c030306060f0c0304030c030309090515042a081e061c0201020c0405010e0a0c0912080c1524010f090306 75
    0xb05044e1000c4404008034183c014058481d01895400901d07035600544400300d01a503e0440301d11001f03039805410030240c0c0d50107980841d045e101d0f494402d01601016150001d1700e40c04221200c82452040014080144030720790100c6c0140c03400c6200035000240e40c0c8040e940e40d0042020b00c160510120849500040841e1290b481c0c1c1c102d00000d400c1c034090020b4024a071f10000401100384044115120f084038070a0703039402d035101c0e2107415035401d940302038409640d0003000046c41540c80c40e15802220012040d82d0001c41600603810070400c005110f190f0399004641100144001844010582c006200c4140403c26080c1007070804103a00d101294501d40300a003204040108580c42030107001040360008001f0700895842d0303e4100c1218106840c00400103141c07240040390075000309841c84c12034180c02e049420510032611140c0d4141d010400c1c80350036018501c00e1502000d1741e034407600d000c0c0d1540030300b0082c9000007195400030b000c003e055140c10700c07008191609103668410035020a0b40c1d0301410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 176556348 1250 176555098 176555101
    0x30e010e031e0405090408130b130b09010e03030d0905100c0912030507081207030e0105040c060e0f0607060c02060106021b040f140117150408040302040b01021c0206040201090501020d080f 83
    0x58042d0750303000b250051a40102410180004c0c0442032000e00740d5484200858214207648181c1d1880510903c8601070241e000028200544140c0c00302529900034181400303011707020824002415903200c0303800510610b6440a03d1010700c8410403207104041c1560004101c40f08070032101604114261141c032614418500040040511a038151600258420b440548a8036a1051501031240407610900024508414041074034814018580560382180c004080182412000c8449296040040e50050341c10603d00455403510401441e5007405884002001846158000c1c140407060b40700c0c604641c4040b030b082d541000f10b006c8800c0404400c03100020b000d05014008005400c1100c0801c0c0044212800050301000301881101c0b405440d000b0790701a0104a507091501c0101654040c0115006120a00c010f05050b40810741c034400500440381d42c00610302c0103964491024a4480050708010244000c40d40c03c0582c000103040300740040d00a40c0b20301c0c10003c100c05d00040a200b5029041c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 176557598 1250 176556348 176556397
    0xf0f010f020909041e0602030906150904030e0405130c090605040b060a080a0f29030106060f0203070f080c06010f0302040c110c040906200408060601092409050d06090201030e010e03 80
    0x1980c5d8002c03680310ba02951649442514035441d61000c840c00c1e8055410820710010a10b010342c41548030344d5040c3c6800d20403c17008002d000044c00010030780440700c0e4000744080d000c103000c51140401480c86280215070039080c407050009445003007604901400c803d028507141070750403068050340120030290001f0a940050001c0d80540b501d1942a106509411b00c85080c01000c2d551240f8044010760003840b900390740c0c8034203c8a1003180020b01d40143c00600008002440904044690b030f40034540c0c060070003a8509502d420a00c080e4818803600c2c00c48881002181041c0c0112650402c15040c040c86201900c11065110a00004661b218a940d115008204240c6038082a03503c80c0d0a01416424900305030032421551050064180c1c911038080014495803044680c00159140749001c0410004440d01c0800344170101c3c24061b0038820398103c045050344a0101550740b450007007802040820703850001408a030090045d040d5140d0501069070004500001102e241ba941100240103080b50300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 176558848 1250 176557598 176557643
    0x70f0c060603060203070f0504060c0f080712110d0305130201030b1504120519030e060c01022206081605040b070302030c03030f040b01060c020a090506120f0f010f02090904 76
    0x1404010304a9181840101c140805980030398030403c9103031150303d49201d84400544640c001c0348034440c009000c10354485d000400c0580074845031881801d4040c1444607594a4a20720a001a02c0c4070005e0314401c907040300d40804005242e6504102d050070455411300b48450f0140601d5180041c0c1415120280c1c0318407615030b01d841c4d0680101c0c0c034080545498440e40d030b0011044c94200705603114894800341030b506004070018110a41c0d0306483d0046000d84590034000550006c801500040d50f0a10070303020040c601900c0310450030840c8109044141c1800c6004d4105a0060162100301c1240d41e24001d0294201048405031044103c0440c1c4500081ca8200d1171803007282540c025902010042c06101a8440401c80c01180700300307200089030fa225501101c040c03e4000000c2c1d48000b10000801c0025010340c02250000b40140c0302c06051251582200c3c90600c0b8404802081d80c0000020700107160288035204400a01003400d61030000d4000010300c0f0705001900240c814810f44010354000d4090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 176560098 1250 176558848 176558867
    0x6080a0e03120a02040512010506181807030507050a08010b090a1104051903060606020d080c3015040c0c11010302090a2309040203060406050c1303080c0c06070308070f 74
    0x60549650303192800d11483c0c00650002e1140a000304402c920030b0305018418003c2500c035040141a0200c003071018410894001400307400322402ea4036143c0380c0041c4c04001d008220181d4002c400820080c1e14060a2004645050744480c0342c80e494400900080e03a2a0440281c0009103854041540079061080070b84d240b10326130102d81d1218219442020701511900d88408807401140100b194030f0303407900c0990701c58040142c1c110001e554603000a0760f00025002901300f00400d51085048030380c45c000110005c0c02c9031121b14260204038010444ea180f144081030b1072413141590240001c0554401c003800c600380940000b40610308040c2c1c00d81c00c0d03901c6030307040d6911884020403c0707217010365a040200b200c4242500103180c00c0e801c4180104a4241a400b03c0d01856024005004594650f00c50000805018013500082d80c1c0800c041064405a20800c01c0914040c2010325656040704052603c1d001281c104180201c030140b001d680840c0e00500b031194803440d42c0c01c0c0500b0200041c00c0480301082d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 176561348 1250 176560098 176560117
    0x80c10030f0606030f06080c03030f0309010b0d03110d03060b0409020f0c0313150801050f0607030903210206060a15050a0309080403060515010c0210030e0a05010204060c0c0e0106080a0e03 83
    0x1802d4000161580e05030012800200780c80d82c01c00510341c1750061641c6603544807141e241c040d032040111030f48440d6640001c40d80034403480000501a00c01100103031285590000680002d0810f280500207954284410100c107a12800c040220380d10b4a000c12202d8004ea2040314802c95000c02e07030380c0c005429102122209040581543d99800c048102c0018800d003e0107107070090b80c0c015030184032a502900416050302c500904010040720180d082202650084208808015127007400200045030700a071001640a148030318901c0000030b0070003e2174458000c000900c6008141c004002e140301410344c0c0c403050802440c0442e41c94112001c1940a0f0100143c01480000002070000600115500540c06030400300398581500d40c44c4401196028045003029501c41d0201701b40620150007035000003407188000041d501140c0294951600320380083d4004c20200b0501d9803800700b040b03090b441102c0a42050104201c0e00d5040c25001826280b0042102c0007082d5141901e03810100704100742c0b01c0400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 176562598 1250 176561348 176561351
    0x161202160507031506051e03010f0c030218010201060e06040b0d0b04050601170307050706050d090f05060f0606070822030807030f080a0e1c031b0c0b060a080c10030f 73
    0x860a1500759500c040341c3c4002d0b980511803151141035078869019450803910024454010001540741c000d8009010800300c551540d80e81401c0e030324008440c0a0420200300940b4010707150181c02400341c0715075103031103859411640b61010a1190301810400c02c3e8000d982510005065038640001c02c543c4400c1030800f901c442c081401304002c2180000d8024103980006e0345d02041c03800e40f4032403035981c3d000c0c0c050700801a811102041c004184504060001070380c1c60381d400325680f0400d03100c12501035030204055030150400010040300c00c098103015038000074281c480e2480c0c50381a80761450307640121a03081c3c2e02c0d54441c11030001659900503403103025542040c0b60b50303a1036103245009800101c0482214020801c2c22000887c42401441440401c450040180034001807007105440c0510040030008141a030346c01031543d0707813058401d40000a5941d604c601404401c182800b0104144c0100f046106000b1200e0501440d4000300c3c01081c506015a80e10302c9402503560103401821000c5400a1440d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 176563848 1250 176562598 176562637
    0x106030c1e1a0c030c0303190501060e0415270506031501140102011b0210050106050a090303030b19060206150405040f0213110a17010e010f120317040303020a17161202 74
    0x45c00c0100c019070152001914100140415405283c2903441c00d12071580494294040007e941c101900040740d070311403403000c0362a015280c6d00c0c158003100350f49068900e000010280d21003c0716680c40b0340c642011044004007182c1070340102841300c0b041c0501030b946c0c407002c4984407804d023079000b50004102e508031401a440800810180203680e4504819000d00c00c60130711000160135801041140d01e54030083c1e44281c0c4160861f10198040c108082020390130072014000c12101c07015800300d500142405501419041c200006013504041900c2101d903c00c0d454541440005034900c4000b40c01303030740e042c1d81c10403200b250381000c3e00c000c00b42d402e1940640c13900090b0100c01c1d581d01c0310104c403100140c0c0502d500140d80703032211142c0855003400742c0e0b00c0c941034008090060b0000814541c141600c246840180041c1501c0c851602603419502140420b03004102400c6d1150048128140720440008502051501710b00781c400d0840c1819100d410302000300f1405000c407021f43c04079101c03c40c1c22052107510303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 176565098 1250 176563848 176563867
    0x1080a140f011107060c080601050f09150406110f030a02030913090f14010c0512150d05100203060a053a0206030103050a140303071e0504080f0106030c1e1a0c03 71
    0x45611200d13045402610302025150300301c1c00303030201034054030042c1d45190901c0125045400345501820f01503910140a0b44da1143c8446607100400141015035509030305d100700180d6081c50444580c0f4007940940040c003010100b140d0000941b00700c04011200102015224404d800003868201800b400c0242c0343c1d080348092200c0c044280c052080100e0007005030342a1000d003224280205120405205801070100300c5000503120908016080204400c6070f003140e980e50a4603165504d004541500e4001c020407549142c829440001007034266030841031a5000018000a402c41c5002c03840d00c070b81c0c00c85071994945003110311340e0040d603405031407155256100d0402c0c9945541c501801c4600c12000b5000184003140401668010605a141d0404100245400d0b03603100641c0c00005040000a00002a004000b004003200c80e0a58200010fa07460a50621401403100368109030310b603d207181503080c40b60f800403900e0411242007a0f100041c51b10700c20b0040c0310ba446a000c0100c07040c400030520350ba4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 176566348 1250 176565098 176565131
    0x11b0b1b0309010c0e0109120204050a110c071a03040b07080c04080a03090e1b0a0e0112050112030e060a020c0609041401081510060f0302031f0f0501120501080a140f01 74
    0x501240176154214541554001107500038914007078441e20841d140c02c484018189900a03035003009184401080240382d22160313a0094200707000c0c0300c61380c5e8000c4008001000c030381061040b0b810428000b4624524241d01d891f4100c0c80050f00c01010040c1140000e075500c0084015200505001400d40e0030074802400d00030012402c9000306c8030100c407403002040094a41d017030500240d080d203210341810301c000c0b8001034070b4079642d1104150500155944400c043c21a40c03040c40d020b848400e01201070002c050034020942d40c1601c0c00c0b40c1c000c40c01040042d1710709400080b0028031150072162260780d0f40d000c038007140242c003c22103583c0030100d0101c004134162001058907101c0b0310782000784118070307943d042d04880d00c817856108120119940070f0307500e2201446a002140e011008405044040d1240e0442807001c0e0300551007a8860104503030b09116640c0d2100c2d4094004078400343c24440ca5060072103194484e80c860718022710b110900d520120901c1c44c1444084841d00c1140d000b04100c0e5003030701410b078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 176567598 1250 176566348 176566361
    0x7080102120a06210f1e03081b04051918050f07020c0a09020f0c1b12012309150f06041b020706081008070b0a0e011b0b1b030901 57
    0x4115101e4040000c111007507910401d0225624212041203d5160004044034003250b41c000760350b0803005c080f070000482c0b1041c040d69548500c80403100340220f8141001840004003821381010099911121014402e0081c00d80d03060302d204480381054100340c080366030f841604a50010140304940305410801d8071060344400d00c80c8103402c1443e59150740d0035500f2a282c80c0b8480c01d540c1d124501410901506259a000c2c0070b8450511120610303021046981c2d0380f0380390b40881442040c40009001c01024105401e05030021a5000c2c0280b0190101d0041d13008030300000c0f0511003d03000000002441a0410000b1410300c1003041d01c1c85a0508148031010038a5100f02d601a00490601600d01204400c00008041c0c41200b68058001c0c14205141100c2110015100c451081034080e07010650f00b03000c0c007402c001407081084480da120310481c4041c4c1500719668101c0e06000c07440b01c01082040b0b056404210031503105020312110758410700348003c4a5001d80b034881c2e118901004220030010305501c4035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 176568848 1250 176567598 176567617
    0x9030a0f0c0302030c0d03050f0901030608010212060a090213030b150a0e090706113c010902120309150706180506040501061e210b040c030c060c0209070807030e07080102 75
    0x12500c80c5e41c10020f02002010b04032006000410801c214100c28180c00041c01c0003420500d0045480d95403000070b142640c1101d4500321040c03540806120307003403078442c41c0000108104070782541410312030b1200c1c03180d15085110213003462a8a00000d00344450041e001461020010600821661181c0c131050080204031113241e598424140003188843c0140c00c43d840ca000e800009110149844100d404991314401800003030010403c0403204d40c00c60a0407814152003a80000503841107980100200c17a00c138020307580c40c50781003080140707000e0f103d5510020306041c502903560790302d8405241c080020485280440c0b100141d2542c241d00b04000070a8407401940990028040300e5114002c80d00c0d0812250160301c0c842c9608402084505001c208070a213040c071204901032444120b44032080c400e001124110741880000106000700442c0341600c002902c0b192034a4484903a0507400f0820050001d0205014880b5000004184902c650041113001c00e00c0300036110441c4d520a0307198048e40204008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 176570098 1250 176568848 176568853
    0x60501050607110f0f1203120105060702102003070f050115240306080d09151412090309030d0e010e150403060519150303030b0f010c020609030a0f0c030203 69
    0x800c0d2074100306440d1080d07048520036000008110800c00a07200ca05001c80e042125013500b9001e580d1a8124078850101060203190b50b06032412542d181800c050704082d10507207081c40750601680302c1d01e042400c40f1080e42011404aa50035a141d40820b0746c2d40c01d030800510000800e41c1c01c10141c11120030800d8800c50090040343c14403032820400689900501d0351140304410082c403500340c403110090005440e0b003000107100761180402810410f004040c43c1c08201e40000822020445420310004001107181c00000e40c841c010140345280b00315052540c0d804801c0001c188442c07024005ca4610308001011200c001c850b08a000d48401041d0800038045100214242c1da6814240303018007285140c1d80078149072900f5a5103010050001401d544072080100c01d100c00519543d11405a2007107a694010110b0f40c90762030002d09407034448030103901460003080f907034015074cc00901036424140c1c1118496100c40070800030034a03040f170445c030240c0035484054942d4240100098114190b9009405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 176571348 1250 176570098 176570101
    0x80d030606051c0b04090203060a06060e0a0b1c1407030f0609020901080420030f070f06030e030910030e070605070c1a030403030504170d0e100c020a030c1a01120605 73
    0x181c5583c020801e902c041c05005000a510341e142c036074001e1103603000042c40003982c04582d8010a1400e80229040284165201d0052104582104644140380d408070340c1e40b02002c0c2401c7c030120280c014a00005c82d448003c1420b8405084150020702c0307a00d10001c0e800c0036500e005040103000e00100040f22030a14039209021072003481034000c60b01e40d8a0181c44500c0c440c1c44559541d00710310b54045440017485003114503c0c410340d81c2404a4800746e00303500000c100340341c01c00e60010b403480c0d41c40d0300c0700d4181454210001031b44d182c00b0080d03460013101145c61b40f80304da01c442c0c401e0b400740c803610b0b0180056014404000c0790998011010388400303801000158802c0d5180e1441c640c50780800518020320620034800100001d03c00e810603544280b20f0140c50140c0301e03070902c1d60340340340e0040c20100f0505034450720780c00f400c002d040080b1206004603800138002c00c1e440702406503d8551002009d010041c00c034079240c0078000c0c00a80350314038010000040005603900c1540c080074032000c1d44101e844504000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 176572598 1250 176571348 176571359
    0x30612030408150c070602030103080301081507090e0709180204091503020d1403040f0e1608160c170c0c150a0509060901030e011b02010605121507090f080d0306 71
    0xc19141524028401444414560195034420020013811070a07105404c000160000b411400510f0003144650b52190300d075414a1b46080c1482e9008a0310301490290004110f04650701107000c00444100c419902050340700c3c2c00e022240355200750080c080141c00f0746802d038040d105540c0208110703100ba40b420040103510031091205200180f102942c0b02d1424400c1801042d400c040c1800c0c4801000116484c0030340d2406400013000c501e0f4414482c4101401c104030180c1c0c07003450b910800e06094a00003801e46002d0b00c079000c0000076074a90300104584600402c04002004544c02505c02910381031a442e940c4403181c00e40c3c1d038911041454020016404500d540c0b02d18142170f0341100c0c209864544c1000204418010325070452000d840c10541c88a9444115000070310480740c0507024281c00c1c2c5002ca0b032a10b001b9095804a502481c05078015a42a07a0400d201141000c00400c2000340340c0c240c4d450381d10f07003103541c51019003240708041241300c0002805400000c0c4031050844581f4140036056490 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 176573848 1250 176572598 176572603
    0x51510060f05090a170c0306150103020c0307060c0903140a210203040909140f15040206090d0602030f04060605270405070305030a031407080c1e130f0302090f0c0706050606041a030612 81
    0x10769910310030440d2703c0e00d0010250300a0b0050207180003908c0c2100e050541e035484140a1f41c00001c042008140344190900074031110b1541144250340a90007011007503036a585950b030080300c1798600c00a000100c400c0050844c800e200300e90003070541817014400ca0700282030117030305407500940c084d10301e1080040c480c10000300030034070902b00f02900e85000000e80d900d800717112507503110340046a801040e0501e40c10010f800c910145000e80100365481909107040d2510030101d9507160040c1d8800c5506c54405080007640701e0340c1c20b09042c058845e11510740c645103031182c5080c545030801403032800041070810718154036038040040b0000381107484041d51500c403015034803034006a60886580000f007000e21000b20007009401c0041030080c540518119500b465285482101c7e0070010050950440800641c5004013105030419460b2600c0702041c103144081000d14854000018099900c405c00030780d0640d240400d44000f0440c5850140340b40d581c0881c1c0301156402101e110b48a8be2240e1082034285000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 176575098 1250 176573848 176573851
    0x1030b010605030c0d0513111c020f1212120a05010302090403050c070806100603320912130501020d0e060a030f0b0409050a051510060f05090a170c0306 67
    0x2918240c0d0800c01d048856510003001a04080001c0054642e040d0051151901c501340d805854080da1081b071030710100c400148056141310302c4200041c3c400d801c41801068002550496050203140c03100304c086070500014640e12201405403040044000c480d00000f000131000410012000d5500c00440c8411118280400fa403c410307000d0000d00040d0040700140380c82d0201c2001c80d20a181d0310100549440b801315446a001d110f51001000f11036058000c501002003035240c00703002c0400d11441c0d4000181420382c840e041b54442c50100c2c14801092003102c1805031401100c0b507441145c0b005400004819104aa00500c904a1214011351041c04002e40b65000146500d150070401306d4101e02420b504295484443d644269599055031240b003480807452198002d000f801101d030902a00b00510f40511880040e81f10040294956051440c1c4094560030700340349194107968142141d8502559400d2a00803d8940c1c0c0800d001240750070398950883d002044136205000301d13041c507490b03000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 176576348 1250 176575098 176575103
    0x6070203040b071a090c01140f09040c090909030c02210c0420130f1502070303030f060b2206020a0515040201180b0903100605090f040212120c0f060103 67
    0x8244000e000200c401c90040402d14000d0131a000c04101030714042c508880c2c00c1d6486070856008520441146d43c02c1415030040117100456203080010000d00c44015106410a040c4225620b80201800c54013a10f200c9003d451103c10820046202d40307005403151008017402c0e44121650768405803a102c1041544100c6035800d805484112618420320014004004401048894000700d40007105080009080d588070004640510b0318a8100d000d180500710b50080c16400300c0c0f00315550700d181c1c0c00103401070440381d05150024550b1502403008000304044d40140e014000000b600c0e40710407080c0245000040e08900002040355903500c1300b41c2e40c54480305401031454014081c2d42603c40101542c15a00ca070040c10088100418149100075195103600a8881861b011460b1941c5040c00c0204203107809096408014407800e00700042c8841d60014140c05001840300002421901c0303000c07940c0e210180750001c845c044901c0d001d40d94101d0300605d16101c032030320035002e0303540010b000003900504898 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 176577598 1250 176576348 176576353
    0x1806180e0d0c080c03270f100c03050d0504030f020c030303070c02120c1f030b0f1f02010e01021c0b0d08070b13020a060e12060103030e010c0f0605010b0a0809060702 73
    0x204001090711800c00590b03040d141100305001c1c00000c00b5050004100c0794141685100b51501200381240c222035065503014040c1e03041008640d003a4031000e2020075240303441c0c00c05050790449d601e012a041d110b52650442580e05003014401015081250b011016071070381c00b610398010495060680c1ca005c04c075800d10009008000d000007500b480070441880401540a4802150145000c81c45212402a404c1100301441c03c52403400c030b074144245486031004455150031040c0a1000646a4904d11101401028008080c0c080c0718000d51003021081481c0e0000e41d111400c90703528040c2300c414003201d904901d09100aa81040c5001895985201ea00104890030305280b61a08003407004020811034401551104041c0580c0d206004400100200d83c0c40d45030302110001480000b14032400c3e000d04947c0480e00500010340c0041513905806800c0ca014528201d8a06101811069000d8054181807800c800401c0d0a0205402004402d007545c8481149444026406070b030340320200c5032400180c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 176578848 1250 176577598 176577613
    0x30d02060903180402070602131802071104020a0e0904030203040609091b030209010c08120a0606020d020604060b030304090e030421030e100306081005040212031815041806180e 78
    0x40064500808580f01c0980300508264140c2e403000c00320384c812486000e0310964502c0070003035032a1504c10404610a2a401542451300ca65280d2140000c3ca10030144141e4000c22100020342c46540c11b800c080f81e005000214030b06060401030340b0780e4820b00030a070000714018408105d0800c1c60041c1c5030807016541005074407004425044009420440c1890304002410b5040c50220b00c500000d01944111218443e100d030510158080440c1d0295100c0420742d00103c11604001d80c000c208039031706c503410240210780c11140b200001e082d40304541002006a180034107140d072104001010780305451040c035901000c1390a44400e41404080000c0040029a400794142344608149221103205071107800c4c089442038480009904000d11509100c40713555684040106520780001510743c0045014003461034000c1520b850090108107100d41801003140402034847c201054040740d0040c2178030f00790710440c2520200038801074105031041c0203071040c000c03800a414513220711910780300300c0c4408002c1254 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 176580098 1250 176578848 176578867
    0x3050303040f1a010305010e0105061509090c190e150702030303011a0f07050604020a050103060f170c0307060c1505100909050a05060a0213170604140709061202030d02060903 77
    0x7980b01c1e51800300c41c00340032003070340c110a40c21403000e040c0030754804c600119010401d0300d203160031500b0081840b842502a00c0540480ca0346040466170f071054207680404669481e80d660440c0b51180032454200e550300001c8555200e0b5000c0e44010140c0c10480c3c4400707260f070301410460300034040c0006c06545074100700010040030500180e000d21450a0012190a14103040311035120f58228100a450340d42000c010003045280a42000e07026103000d007420044903041036900120321542d80500b12001c462495180c508084c2004a58100300000b002c07106100d4440c1c400514809d101801201c5a0320355418405035001140035851141c034041d1402c80e08580703408a283d000c3c02041c142614280900342100c4003003201070101c24810a01b100c00503a40e801802111049089194040060405032a0070f03404501404510030340c0268002d04400e445034545c000c1c50742043c0c45640b000384003620708400000d000c4101c11524000031300031015640742443c0c00c08140c0c1c5511048a070032480e90001c0008050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 176581348 1250 176580098 176580113
    0xb090607030c020d06020712030507020d03090501091b03051c080412050d06030809030f010603021c0c0f030c060806011e050309030c19110d0f0f0f060c0f02010509070305030304 78
    0x10868000d02d480010b4070b5050b000704032520301c4644140c800540009202c4140108c00c442c1e0306807429545820031480c50060402500e079280c403100e1604140c0c640b001b41041c1b10702500304141d9940c01c001110110402040d4841000b016444100c1b15400350202440a411000e000728680444586800000b0740e126a10356801511026441007031000030720030818490b080780b0981c00514410404640e4400a41d41094548800d024642170103a040c10b03010320058039030000301c20204001501c1020f88001a140506082031700760054200140300110002c14060403030700c0701e000c81d04241c950a00c1c079282c4e40c0c01103c0000c845262020420b10011000140d035100301c004603481864030701030b13a080c10301d00100c2a0814039400340105032418180580c0c4103000035401c0034200180101c031040551031031943d030740400501d02d08000c1c065030400130740070080c01281c003102031006520034010860000000f070b010b801d00781d0aa0081d00190f01e07210000c0c024410024000040c0c9030400c0080d030031035540d07594611 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 176582598 1250 176581348 176581357
    0x10609030f261602090108160911040503120406030f0e031209011b0809120c060c070213380a0506090a0302040606170c030f040303200d02120f010b0906 67
    0x405100c00444110121190b0405410340080d008418900c4021500400000b10b506030407186460f00f09298902242c1c100b000020708650030342c1c101040d01d0046014020003409207611a075018040e400526054010040090041d145940c40800c070380c5044020000c00c544032404400d00303c4d4020000d940c03454070b0800c0890742c003444940c004980c0119001c1e120303140104203c3c0c0c203404245020f0902c0744402c4140186003064040c84082070805c1c01c11100e44e0340c0c500303000e40b101030b0766540040d4138415900c54820813004000315001c1440032201c420721901c0000c080c40003600081c09a00f543e92131165690280100040b4010003683c6040d08040411041d07500c40c01e83d850380021200c0c1e00000507150b81c080c20000b0449510f841c00107000300c03141c090495030300a1413035108143c01c03c1001524030786900b100d80c002d5007624001031210880c018050f03168a10000241038003002185100440b0415001840c5825202011280c6a20b441c06142482402805030010582061024942034107080e005071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 176583848 1250 176582598 176582633
    0x1c050f0d15090903080108030703092705010e07031d03041a130305030309060c070f110622081902060304060e03191d09090a1502091306050108010609030f 68
    0x9056908420401c5205155070700006000740c030f4003901020306400c00e0040d4018021400514540070242e0340060516903240250055003100b8051085005803151200704004a5002e0400155848000c41c0108500c11a00c078000a07007011250b2100c5000102c851140e40b403020015030800d0b00303021103008110310707a02c00c80c8002c500900c10310005201003125100114040c40280da0b507402c007500307940d0406100802c82d2454200c200500d0000032240c4a044407403e400400c1c003440c420001000400c58802c80b0124111485c100c41c80340710081d81c00d88000202c0b03028404035610003205070000c0300051265030000e50b000030b040c000540030948503080011071918850070340f8a020100992a40301000b0b0202440010ba500030759120345c16810580004400c3d01240e54181914003c03242507550361400354002c000f056800764580c00c0d030700603805039140540018405043d0312294071411008141512031240000c80348400010300c90300541c00d040603627400c060f03185d00000b000e07200c3c03440924400901 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 176585098 1250 176583848 176583851
    0x100b011412040b0123010503180105090c240d0c0e100f0909091e02010302090a06080604060b031014060d0906020702030c0a05100e03120403080c1c050f0d 68
    0x3459120920800030300d036541824490803124102810310000610303058011445101642500d901c01600c0f012650101c10000d1910070b07525981c092039010150100202c0d5101c0350b080c042840031030640403801c20010a0184c80404402c0041d29581214114290601e90700d00020400c5020040f8660000c0e2030864032070401d4441a43d004c1d001c1070040d40b44aa4010028102da5604001d40d81c0c8000e05c1d1004210014043c072030f94240382c403901d54010500521280042c0e1a580d80411640683c064030403800002b0540c03400d1980d2000060000c00d404c4880500c03c920b050408038040c0501804c0e640140460303007035200b486003031001c03803242c40056064843d4061410b1021090184071801048180c80c0306207001b42e2100071301d105041c50200040b42c40c9100d104c0003038040c8905d0310f640b900281d1200c49850804084400c242c0400d08042d1250a481c040c90400280441030005c8080100080d050000480d0060368800400300c0056080448420001c0c1003000f41403100b080b19400381c882900031000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 176586348 1250 176585098 176585117
    0x241208040e070215090c0105030f060114030702010e06060301090b0f040305040b18040b0102010b37030506090f0a020612070302091906180b0301050d03050c060a09060b12100b01 78
    0xc4580007490308803111401a0701c9000c07140e924003c501d0005400004010040c0030300034001e0000ba00034080140445c0d212074207480007609036072181144491403911482c0032035403130404090003400b0f03105c2134000c50b10034820503010840504052144240440c1c0100b140c0066071a401442400044090000d804200d000e000c0450800c0102d8000c11001020510403036030f90f21602e0600040c1c0e1200380103181035901d00110640c1c00e0b2500d0914026400f0010a490040781e480f0680f84803042140096032240e4000301008010044006040e6000c0e8241c8001c0ba01800d00348600b4690310744120134003d40101c0244072040198071a11081c03500b04403030381030140c28002c0150100e504030320807521303807009040c00720303010410a900072034103043c2070085024040d0040e003080c94500701440103208282c000c400700d129070380a162080050782c510203603100c19100310341040c03d40070028016103c0d00303035a0103150400b050414034011400d00c29880001001d08614003521000304000c000540299040c02030b60407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 176587598 1250 176586348 176586359
    0x10c0914010e030f061003030912030e060306011b050c150f0d0216052d0f070b0d090206130302041b0c03110f10060e0105031204120503071403070624120804 69
    0x5c400c5104118160604510b14035604000780480c0b21507025003c1d0011205502e40402d5000125025480b802d80d00d0310340c0c030b44480c00101c40404000c40f040c0d0000940130151010410049210306000c0070803505208041c0c115007296003240300d0b000e40c012030b1070b000300f00464180c580764014101000c00c00e40c64000c610705c42d48515050580e130101d500350f0300034040e00c0903048041d1108941c403056141001070000640f0b86c81c2181ea1001c460003005011003011550074520f424540003084040d6002d8841c0b034603201188900c00d03000c3c809000c200d00c80c0303051070f08184101403041c800c0e005c83c1d1065510040d416000703440658110301c0b44905100d40d8040c01400035a6104208018000519040b8000801626003000e0301d1b24540182c00c0f0b103100f0340118110b0034079804030703000396401e48803640724000030100c8615180c2e10b5441000001030501c141c0950150240b070740400900151405020240111000110b006e82d88015030481c55852540f004c10a120141d4003051110f83e0501c0b41c000c1515140d12507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 176588848 1250 176587598 176587603
    0x5090a150905250206070c0b060303040915090e06041106030a06080d052106010503040308090f0703060b03100b150705010f021201060f020307020102120d0b0d060b03010c0914010e030f 81
    0x1214000e0040c2841c1c0820f149003221014194020030882c40a00210304141400411a1000407005480e240318079022580c03036501841200d0050110200411100b07051045c8079031701005501c0355001461034002ca0218a18000c501c0300d210300d50003015202010302240c100030894201801c282c220a90310300004c0b0b030304c0600b0402032104403c00e40740d181e22401420586200d41344c001074000c2407400240c0c1401042e9030031100350390b0020b500d402e1810301560b46d0302ca91031401c508104d41440c03c0c450540008140030540e441000c500700141c0c2a07179054a1070020720340c01d481e4034009003900441840b10f808549a5124045c1c4400f41c0700c0c0d00085600500c40800d2016a088441a5850315068900400c02281c0180c1c200c0d4968810b40055410080e03546c0010b5291000b42040c440c10074030002e422840d08815505c01c9604180040103403803122210f061150091200340320650081d842d04284a000c2d500860102040360751802c0b09040e00700740400110352807100c0d094426014030544d00c1020600c5020f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 176590098 1250 176588848 176588851
    0x3090a0807050f120604030c1a010b0301050a15021b011b2009011404050402012105041e020619022803090e06011d0f03161e05090a150905 61
    0x3828000c00c0d800342000104010440900c1259102d00d032010145a548000407a10503407194040c188200c602005051600d0640c000144410b82800040000310350300c480300b030141d81a1602624482402915000600c8614281e10450390259010140c01261181d8070030910154600600d010001c2d0180944070140324070306828201c5440c1015181c482e407054950358101e4501c2011200e20285524113082204000190104580119240c0740028156401038056601020203800d031804800e85d040d031800018141510100c0e0b0020824640c4526840d050804c040e81c5a0001c2034107142c030309520040340d800c0307000e41d842c6410360086c0c151940340003007100c00c406081c1031949c2051f60100090302c4c008280b60300c15040b00820803808030600c06507907407142c00c0440c140c81c51000c90402240303140c001001410450002c80e814403035400740841850340094810120740340e4036020b006140106900d403071301260380c0c0a91034122000d20005002026075030407440c5000501c007260528103890b0109441910b00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 176591348 1250 176590098 176590109
    0x2120a1406041a0f19062613060b030a1205070c090c1b05070b0406050406020c0105180d02031c0906200607121806050106080709050f0f040222050a06020105070e09040503090a 77
    0xc040c00045c800c0880c0c2039a1010001001200840c01c1c5460a07400d0502001c1c10307400340c0466a1000c2b405041e0710208907016203140c009241094485564a0050090740b0014040b2a080021400051a000e0b140074001481117203480300d008108540074903050300607585405540303c0c81480000030301e0860510040001d000c29550b215511030601a010340b41c40090306403141000744c03c01064007a540710f01d1140c507025108403140d8001c8000ca000283ca0140e0304d1003800130302c03400d043c1c0c80d007002034200c9034080c102c8035641c8840d4503c017960511207241d50349402c9a083d01d034100c000020001032040240d0841d951881c080012250340c0d502c0c60b180b03881c4504200302c86a6a55070010f014994001582c80c1d0b10811915140e00c0c41401c013004500c00d40320b683c2001f409401ca00c4082400d070769903901600e10380100700b542d5080c940c8804070b007098180c405c0d201d1640071b0b0f651020702180d0075106000303241c030612064850300b281000c00d00c103002050300020b1082c0e40300d001c1400350800c00e54032080c0e180c0c000c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 176592598 1250 176591348 176591357
    0x3818130507240f0203040e16050c070f0f060e330a02061b03160f090b0c030a080603030f120c0405211c0212030a02120a1406041a0f1906 60
    0x390b680e400351054010a0150342958001c0c0000c2140c1007120030229449192860a444a005202c10903a0030740140c110001441c020b01c480803480f0503aa000510446014019800500384c0e40d04007959200c94000845400100a080c8080139008000c070310f00319603040103a480b00c0c40382d1013030400300d40390040d000c4400143c100c6014031102c3c040503070001000604404410b45181021100b40300102000880403051100004400e5401c41c000d07207000c8010b0100082c01075840d100c41d900b00d41c4a81c8113408686c0071801000104045081c00411f440c01c0560000109240c00c0d8815229404801e00030550341d0340e8141004040b5840c4c071202c40d0820340b100014403000b4403c2d0b600d0092030502071078030454400400a201c0c03100720b41317038000346182c0203070940c104042d0b0360303241e12100802074450550480720f2607030480c09100c0304000315440380040801c00d1506855580328903080000392004000600d04640600500c8920352504000300b1030f8601000346048e07482c1c105c51804043c8203511707900800109 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 176593848 1250 176592598 176592659
    0x303040209010f06051b0f030c1015180e101d0f03030601050703080a06030210020307050d0801050a0e0601030b030f0a0201021e0303070c063818130507 67
    0x5081c00500c1c140508200400e018040d0700302040100307035001703141e11004910641e111040451609000e42120101c018007501d0340c03049074505a0380d0700c0702c04068081c541464110205a205071001501050b10b803015108015045225610001f41000610940d42c500030720099129195082c480c0c506100180800340c208020517066950822250709502141074004000f0000c45030780c8070044a8200d6450309200100e80c981d48240801010340d43c00c000e41102c91a00d55180c8582c001001d01001881a0200d50b0490388010084591101c01e100c2c0c50380080640100307110400c1d00c00c003440d82c01030040c9000074549034030100092601c4880d43c1602402c0d0012034810080d943d06000041c10002c04003504184000b04050b071541d644801006902040030100b0349078108591703504207004026290755280c41c1601001440e101c514071903448000075540581e00c000c031a043c411080c190341c0080e80d4508010b036484510349a0080450b030701c101e883c1c0c0281d48000c01c00300160144040e02d0180e40a094210 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 176595098 1250 176593848 176593853
    0x6030614060301110a030e0c060a03241206050a0906110a2715021f05100602010e070303140714010504050129010c06090803090f1207030c08091c0302030304 69
    0x10980302400c0305020b64144000505100c00000c01c44400c0c009528000484800540c685402c0a54110301103600001c0001c1d406101030789900060204118544020b20320281c1540b03c0d0381604861144159103040b00e1660390100710560b00032a404000c6150129180200b5a103582c210b034010300b078100e4001c0300400c0c208a810ba1008246844042c41a60240903004555130305090000c1d138454030105261450411070524801c5c001502c030310003180c94511a00080c5064940a442e044590380d0100c6d61040c0c0c0018054414001e12841c41c583c0c1300604001c40c1151012a07020343c0980a0300d44520040000c03800040b69412040c15510440c400041c0741d04052a01c9401e440c1d00e00c040300304100382045c1e180d400c0d61480a448031003910034200400c0311045491711001400702728502400c2004088100212417101081010300d074482a82a0780392550030f00c00711071450049880203400600ca104217400050700703d00003080da00340e00904000d50700c00780204101241032503590850042c0c00110a0004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 176596348 1250 176595098 176595131
    0x41d061311030c090c03070504030506040b151c140c060a0201050406060504020720010c02060307020c090a20031005060f0d15180c0e0307062006060d02100e0301060306 74
    0x40301c800c4001c0c107a002c2d5404000303451580082d101c40c0c44444004046083d00b4045c100700c4000f5075000d02594020b0be45404e00a80c2481d040342e01131a0003268094824441c548014195000c0590f035490381d4a40c0d0741511452003052520640300341611402013000030a50311a0040c1880e01d9136540041194a45407400d08241c6a141e03100502884c014401d010002d6007414001c107900800709207003001c2c03200c901c0040303640c810740c06000381d00040000700303015000c0d80c0452304c8018000c0683e01981c0c16218600c00c203049401080c22b82101c000350a034041040300750b480007150404c1501a1301d400c000d80b500b0000e040b40c1d01070042401c0032000010404454280e5009856072a007007020002d2000386004442c852074491075100b00c02c2c0c0b55440d2840506d03103010f90748080481c1ca024045400d00f98841002400c0c440119914640800914408598002c40000c24910070072026041c0444000e0390f50031b004d150000e0120900900404c0c07166443e20b42c400340304050043d40108008102000c00248154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 176597598 1250 176596348 176596373
    0x60b0d1a0a05010e060c0304120606080f060c030a150314030c1006050a0501080a091203020405031002040f03020d150c050901030c030903021203060a030804091a031506041d0613 78
    0x41c040c1214a904200d80c0c1e810500850644009440043d620b141c06030350340742103209540100341004a81d040e160244100b07944044150b800f1442143c031030103800300a0907a10b001c11104c083d090b400420010700342072555000005140c0c0e4408140c0d03046503d03941d445030440e901486904c0c6990000c0b900580000042000c002c4c80901c01c0800c2280d5030516001c280403144030700070b60381404086c0010400c6903031554000f40e4130302c0c0c000380008028560780700010701a6119214440c440c6c8500c100d40d00b040d5513903100b11421201a4035205001c2d0b440c507400e21007801c013032440603202607049403d5403030004002d001d2040440c2495031016902c504820006d811640c0c00c00300403003007501c4d0200080000c1e4001818445100580303004a03103d0b5240d80024031102e43d6038200034408280803d00103051891030300315205294820641c12846d28075041407550710b043c2054203580e0000305502240c4d86080552207458100b6003200c401c1d55103c1d100f00d00515140d010303103401d00154800803401e014401c0711101c11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 176598848 1250 176597598 176597651
    0x705010c08010e0403230904021206010e0103020c0c0d1a09160605040e0f0c0904020c030304060609140705071e1101080a020a050a2106030f05101b030b0301060b0d 72
    0x11182d04140c0c0b00104607a0705184010039090700400c06d04403626070601030741c1d90b01e42c00030410b5507900811440e2042d10407080c1d445501059500401030440c2d8068000e48030100381c4080103020000d0031000304aa0300c50400c0d0151126610a50301408049a0300c2002c1c0c464000480140450103d100c101100c59031030381d001302c042241c140824000a88488003664101c003035100c00704035689032000c95080c54402d1001180c0e000c4d00c0003071a00c00303240c000310103148241c2c024002003250680e91064002079410340c410500741001d450700041c64040c0503e000e01030f00740c01480186000503c00d1303115030f0040c140b51800e0302d112408000c01400c0b580c0c0055042e47c400e041d50402d5082c0044c441e03010b4001d010b04140d01f018424480d182d03110383c412201c1341080380290014107200705556401d0800650a01a070192424000d84001c00000c0d41d040c010124411805241d080ca441e402d048224002c2854200d0a5490354071000002502c581e1302c0094203402001c1580081c0506400a0981b800107a25400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 176600098 1250 176598848 176598869
    0xe0703051504080415180f0504060506070b0c030a02040e010b07140106080d0e120106150f0e0906010e030a02031e010e151f08070305070302011101150902160203030705010c0801 78
    0x400c40000d56010588080f81c0e031382503000d6101ca0410806684010b001075418400501a1b440000c0308003049008408440c030a607000c10a15440703005120041c8102c000151030344804002041400c00504010340e4020700e51440181882d84401c03030b08c0c010b1902a0703c89800b9150200d0300c002800520703500d500540c090312008101c05890b00d18404d40740d661000300c170014091040d84542880e1100c1d0701131258400047e00030031525440342144d41000285080c4400001e040c141c90313080580c05040d08510f03244000300280503a035120401100c0c80011111542d402d400340300000001614101300028400b1203114015034210a400029421650601702c004010f900203e486c28803d07a9107038240360403030014039400c0650118015581114030745948444200d1203200340010620401145141c1540d100340c1e43d040340c84502e1541542600c010209070030303001035058400c200441e02e560003051102010405c64080d40e5446c0c002034190781100030180e900b07944a00c52001c4442d0702141250140a81441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 176601348 1250 176600098 176600101
    0xc1d060c0d0e040f0e0f07050114030105090703090b0406050609061c0f020103020408060f010306140114041d070308040503010c0309030f050a3606030506060f090a090e07030515 78
    0x9690310118107030101d080c425a00d941e500592100c0e040101540740600c0240300c032060440343d150b0b5604a0901a000600401d10046229803040d40310070304103951032810b28116400c00080041d10000500840c1c00d250b0b13680c1c50500002d005003007170f5110354040c42001601d40b40480a104d040c0364000c01c60341c4590700303501ca845100c01c204000070524a0700000e4400c00c0540e60b100590003880b85400281c2180710b80d408008481002c1e089840c180da100c2d05007440702a070f007a10003c07401c0c4802c2c00f03401840d031510003000d4601c2c201503100204481c0541100118070300c00000032030604509800c184c42c4d01c2c20001d024006400c00b400b4000000c901072500700700c48546900c0041034580d40e005401c3c200040081d82c80403161040444180204615000aa03403001c80c04404801052801e1000c8109802c1400041e1090081c85910b100384d1025010b1407510440c0f4800c21659400903901c03030340c4441c039484045411f800300d00c40d5251341003010008143c400c0c02c5040c01880c2103522030480c058441042c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 176602598 1250 176601348 176601367
    0x91b01090501090618030f0f1a1b1c05011202040e0c0f0111120a0c02120607091502010213080c090c07030c02060a0509100f030c110303040b0711010c1d06 68
    0xe4001200c0705882d01c42484d91782034194003c07501c03081c0e00c09800001c040e8004820b00c040c0d0901d40c0005031190040b08a5882081340c4020913860440d41503107403072407601d100c94a5500c100e00a128a842d42e00c0029402c2c1000d84182003150000e801408150b0420728007001141450310521810412490007030503248120700c00103183e0044680c0660410460072a01c0454804c20451900d46101c4001f2454554402000041102d050b40005034130603c003c1d589803d2100e00403940c1405518a640e40c103110509143c60b580d00c00749508440d408540d0300300030459006c40c6841400000e80298000381500700146000c0007001e0700c014045800301081003004400094000011f00c3e07000754107444854403802a03103002d5505001c0e0302c103400d40080c0c00000c0070403079592261210304503010329201004600c941c042c040710302030141d490403000c0f035000b04040341c0454040352990b039001c1041e01c4d15940d00d0305c0c1000c1160960340008400e80119144801041c1020408081554152001e0790098184001507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 176603848 1250 176602598 176602607
    0x105070618060b01141e160501050403030209130504020a0510020a02090f0402010f090b03060f0105070501180605090d0507060e0106030c0608012102030a0311030d0e0c09130807120e09091b01090501 87
    0x42d43c0200040340c0004087d0284145030158a441c0303500140200700c981b502d402c0c0a03010b580801a0588210207000760701c0b03c642a14071070240240d4018104280ba0ba00300030902000a061019140941c803500b00744d003006944501115100d03010a03000d1040b9802c05100140030308400b0505e01c814040c000909022008008042d01d503c281c0484541c544942c481c8010307501032140010181295080c400514402d0101219100704a413140c10100007903501d80341d1681d2a03600054110700010000c105682c040755054000b0204140002d0000404950700d580740035580c0c80641c41140030800040040100701c107627070300e01844801440c1c00d00604c6007441c0d0009480340d6107018010103002d025a08265441010801d403403070b484015000b080038039440303440e042e50b80b01014081c80c4524510400900644484411048040c0d0b02c802000d04018151f40c1e0b4200c6000d40d165245d0411420808a00f541d640300010306010748000005410116000c28204400c1c00c20900c11034107104148004010b180da10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 176605098 1250 176603848 176603887
    0x5030d020c2106070e01090312030b0f010302030c0901030b150c0604030908011515121d060105310f0903090e100503030301150203070204090b0919080301050105070618060b0114 78
    0x2c0ca01007145c1e6540381c0050316000c400f6000648845924907910360940e170164040110300c50b044a103440119042401102a13100440d20708000c01818040b40f00b803940030b6003100381380320750007002c2c0c04220807a02da058007582c02c400380340015907000409100603d03400c00c2c0100e0182c81c1ea8002032001500c4000c4506005280303200304480d540508803245806803042450f0700010390701800c1408042c203010060340000040f000c501c1c4160103004000a41450090010340c2002040140340d021400310508016503140310160030301242c0d4803201003140910b0030784520340a40f40310361100481942802c9850504040c020115020482800001d01443c0d90020980c3d04588001c08091040007040100b24254001c1d684000e40080c206650f5070704000c280440207100d0125035089440300110240d04a00b0760400d810f026024440401c010300182d440341d070082c402d480c045c600118056058a0b00d040046c0c070314401c2a10899910401c1081035a806036400d5601d00b41e03818481e0400101c1c2e03141e104408071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 176606348 1250 176605098 176605111
    0x50a20030301051e09070e01090608060904141221010504050f0c090a05130515010216030303020a031e0b091e01090e0a0b0106080a23070806040605030d020c2106 71
    0x2020108001c44c020311072403207600c904040c0852101c2d041c2500c0140c00032264204050220b070443c200820854804c204191048200814004407625180ca130152a445109441505402100d1800e100d034001d00000307015014404e440000b1041c03520074101200c1c141a040144142c0c284002d10405070440e540043c8c00c068140300f2141d4400d603c5001403041c1c0300b82e5022503003008d10141c6004d00c004090740322900c164100c118901180b44601d004988a042620020655150541c2c05101180c441da026104144160500240141a8800c0741030340c5100c056051441503247e0110559500f03151144642251a031030351046d01e004600c1500d51100014094508440e55421078404022070811105c2c0304682c02110719501541c60300e030000c1c00c048080300c0701c5c1ca1032400c1c40c00c900800303101003020394400043d09909000545801c4001c1314500000750003141d00684950011589a600344081100a40369400902e020800d8000380004640d00301c1c0000c01c0c1501751020300d6061400403410503071000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 176607598 1250 176606348 176606359
    0xd17070206061e040e010902040b0102010c080f150d050a0501320406021605030705160b1c0914070e010b0f1606020c0601060c03110105090c0103090c15050a2003030105 74
    0x843d1000320340d07a03248040340590391180c01c2181550f032429041d4448403e42d0b00a071014050701660400588c02d91720002c050000043d55440010010a41030100b99000301070780d00440da00e0301d0000000350010030b61400594040c1c01048854040090900ca04500540f407100e41c821802d410040782d0104003510030000c490800d8810000b0104019507040f148440070382d03524025040414100181d03241c0000004032210702c1502d203030038050300380d410b2400c080703e089420040c900080300300186620701c411001070291f103494814000004881c0e843c8655242054002000721034a4001c62410202041e0311488500004204c01040025200b040765460000390107d880c0e40c011902d4a4002803280c030600311464000c660001c01c0b15a0700c83c05070505039000b03946518012a060295508840e825561220306a002010307000b8954082e030421114503000344c500c1105190380e011144010b040c4034859000003500000c00314641b9030410f2030718078003030f510402c4240500204043d03640d80b403106006451040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 176608848 1250 176607598 176607619
    0x270815071d030a0f0305070b0a05011202120c3604020f040506030a06090b04020112150312090305031b190b01180e030c2802010c020f150c0d1707020606 67
    0xb0345040001800495000d80101034410250800600c3d5820991040745c81080400101d16400ea0501905042c0e920154070f041490080740c0c00c000c080f84440c6000e0344a80942c04003000e903a910b04030701c0b50a220031030074130030070b00400300d07034080741c00061091425603408070300d0b05120160302c6094030401041d0058a00084944501d00000c1c503000d0030180092025081c0b05101c0c080083c09200e06018601c00e03224408015480b00740902a5060b903400c40100000150003000400e0643c0c00074440c4204038149050f00c44c0d165140c4504551040101c175808044908017201c90782030400071030580d012800003022408100b41d4400e100c4000c103100707829205105503090102001640d10117103a949480381120394540d80440015110400c6030100030006040020114840310000051401c40f0740c140e5a0b048243c60603030812181d00030100816400110030f143c0c861000d0a080000c10503030100900030021201c4120340200180184041e200310644032506011550382c00149490b0415011501d10340c09 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 176610098 1250 176608848 176608907
    0x6021c0302040512010209011202040b0306090601110313080606010e06070809010504050a060804121404210503030103030c0b070906050a050703140406090302150301080a0b0727081507 81
    0x1e4007850b0070580e4440d4002c80d044041c038605500501e4082420b0321085484800c1101d80001c1780614403132100c48440800000700c0c10300c1c1c0164055449a0141040c07400540382030a002d00c0d541280e5000c0c40910b000c0002401030240401009034446001d207030000c840c481c09070104802c0d0103200001440d1100100b00c13500307683e003e1426034000d41405414070070042d81c1e442000b080d2043c2600e05a81250b0081c00311b246c2c592054003012220360300040a1450645003420342c410840d015000e008180030041d4514000603414801107001f5070103540c45d010b510400b42414080900b000d400c1c801400400001004181d4000c4107541c00b032070305400e12a4441c070a038103007681c08064855240248190005011a03490703048464030081d6030085c0c42d0b01c40440c04680d041d034031a100038000c500990f40300c5050100094100c004142d800312803840d20701c0003d8079105e82c001c0c100000041c00302041c1c1e0840310900a00004205005509480a40a03001400e00b2540a014054400060894a280618011003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 176611348 1250 176610098 176610101
    0x70507090614061617030a0e0d090b13030803010b09030601091a0f1305190605010908060105102d110616050c1e0709060605040f060c0f0803090a0302010506010906021c03 75
    0xc0c003034000c3c1768602c180c110503942140c1580210b51007000c1a16043c601c081d1000000745e244c0100f002510350740816070901031504103a4001010100c514044940f0100010f1244c001560092100c0884030f03898240c40c4040500349041604140c01c100c0c038080102140c1a80d006080c2c10704e0106a501c210801d084402282d0182d0300406005203013400c01090144411005007442400c0d11410300070020f10f43caa2004503849443c4e84240c980c55802080140100e02c0c0c002840c1c00c0215403400c01800500c3e0300e4440403448175402d8541c107041034200c1e08411006402c640441240c01c0c5400140a0a1404a00d8440046d01d120b0311001048408034113141c40c0c1c8000c0114115005404100c2029520208003c1d03036030b00e40c41e000325040542800740000e03c0703c1c040d0064030203450b440705140d07032414100b000403114410300c600143e4481512703040b0400401c036a000214002e10841e40504501d1406090280c2916000340400d4100646000100250340e80456000c450444c26560400c58203a4400b0440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 176612598 1250 176611348 176611387
    0x303020f071a0105031908090a081506190e0a09050309030712140106060f03150e011508090c060409050a0e010c0903030f080c090607020d051207050709061406 70
    0x80c0004002040c003003040340711001d249201c44000ea942c2c1c0c90302e0034540c481840c1480345891402e03950882e000103462802078091100301401d020f00469590312030034500403c07100c01d0f4081514a000307000260030305a80900e02c2c06a29002031290915007944080c00060003001520340e90b0b620006c20003001000e0049844500300282107031985600c4e0b000340000384103440b41c2244d011803505038004101d48c06000b03c0007180d455458581180140311025005080c50300b01600c101c010512011811904194034107029040464619085504000740505149006042e00002d0f80c48105091103913030303c41d42164140c4100c0840440c19498480e8104003910000011803942e50801c41d80d4000346078811000005c581c02595a0082042002001d8525030b90075a03040c00100d008221500e0075003010b41c020201c1c244050801c07100080c6940b6618180802d00300d810314581d400040340c1051100c00c00c003140242150034010018180b9080c28901100c000c0d004003400340d6030219000c56050100d420380c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 176613848 1250 176612598 176612617
    0x1e0501050903010605130e06060319170408030d0b030606010c02030d050708040305120a140901091401020a050607110708061005010309020a0b12060108070c0201090501080903280806091e04030302 86
    0x22906c1c8008194000040c1107081628540ca11940c40081c07464900003c6454040c10042c035580e05961242c0c5aa641205107484e045180903000c10001655210420040464912214001a46c00701d40410541031200c05820305040003080010f00c4c0140e0b0340480d0841e0b10f82e00b54284141d035a4041c0c94017514a00840d400505103001e1441204a0410054000d103007050303041c0d8a00442c0c81d03551481195900a0200c1140050208441804000700d588005030081c24140121140d406c07243c0c1d540341c5000c0b0100c5428002900c0f1125205c40c1140030030035240074218580180429203491500503c01822620500c0c1c10103481c0d0070010255211340b1a0b9501030720003100020350b030781c40400030f5100c02c0000303950b02400100d643d00028a5a071240d83c9203030720254160748101d480c80c0b0380300046446990107041d5040c00e0004120001c1e0441301a40c503041c1c000503620b248003080d0310405c4042c00c0400700420140c0201c40c06800c000098644850304174418000c40030b070200940725030908600074002c1c1c0d16007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 176615098 1250 176613848 176613859
    0xa0e01020d0902090117070b0702041404030201060e01060309110904060e0304080109020a0504020a050306090403090f181d120715060b27011b1703010315061e0501050903010605 78
    0x751038100049812201e8214000c2c1c45860786a613030382c0a007000608000c90300d1000ca0304580024032148100100500085000070404111000c2d031707480c50b5402d83c1081c6c070200c0141c0c0d541e80c5e0030003109400103031143c010070359810b080240343e4507038540011078842000003a02c9000d51000180070800d240e072180d02e41d06800302c1125112519181e02a00800c40c2c28400c2c0d01c96005100b00240c103150500880b161030303002e80d541a05503203542c0148078005c080604202c0a1000d2a4400b0841c400310041c007500900d0080b00039291003044980c11301c121152007000f902c1400e5030003d5880701c0c1c90002100e00003440142851039542500e428560031201d1030140c0208064100000040c203a1824009005050142c81110080200141c030741070104040b070300c0b0a40400c1c0d850000d0038100c1c81900c6403800300e50088003440101003e00700b03604003503072098004695050500012014140403449074502402501c48090f0411000c5c1c1e84600c0c41e0502c910601d410004009016103403030310b0030f4000c80c0050102410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 176616348 1250 176615098 176615107
    0x1020403030504081b0a0e040f20040f09020a03030c170406120b010c1214040305070e0708070e0117041a0a0b0f0406141516050109031d0a0e0a0e0102 66
    0x140240954414440c901503441103407001c1142c1e00c0842c17070854803a80003e01020481c2e2800f15401d01900000b00256401102c10f02d4280c0400d81d62203101d202e040038030018000d841c5a480c2000201d400748403a481d5054901a02080161150f0202c0d0081c0e1f90075050403214203030707640b50090034000612260803400d200400c0c0001c6454102d070303944034443d81d00b45042c0001c1880d980111165603801401400c050420400c002600340106414a41c10640070310551800780c680c1c03505854004244c1c00044180c01080c01c100c0f8150b8009501e03504840c00f81382c4954590100c0e03000800c1e41c5000030103030a415070108041070800505840403070304600c0322201d1501034a42a03113880c00410090180030f015000045461542e840d00d80300e8841078440e40c007006100d001d1145d0a00150115000c200140c0300c1c41040841c000528106280130440d20610000c5500005480c00501c51900b088a151003d40d101d8003080d1680e981d40d9107603040d80c40c01070f081c004a6550000300009429014403070f00c4079510001c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 176617598 1250 176616348 176616353
    0x90607021216090912021b04020d06030203031306030501080303040c03150204030b04150f0612080c070b030c0408010b06030705160618030207030b0105010c0804182307030b04150e09070801020403 86
    0x30010078146009001985c01032400d03071410398652200da402800107038025140c228030340c9000d86c040c0240b400b42440000c4d0340e0f03440b079011a09d1036005150001d28480406c108016056250007100c2c090312809006c0c40c00e50a044d0340e940f1070400d080c00014820401c401e0070001d281500c1c0c0c1030790019608101e400c1c1e403d00301420b0907001c0e0078003050002e90440c207200151000d41194011750044074050640f07135244034255261540c0c980c00c40c121002082c0182074002504600c1d40f409507025100030300700141d84924000e809404c5907400d10340c150040009204016403590841c058550022040d0605a184242c601d0300700000c0001c1181d40c4144080030003c1414154001070481c1543d11440340303e0180e0740c84100646201420780e50080807c10100018050306081203034002c20031034024000b05007201130040d03008001c000000703000402c2d14690204400158175000d40f400c6208203480801c602800090301105a422038010380c0310452240010524492040040400030000d40c0021134039a0b4491 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 176618705 1107 176617598 176617601
    0xf0d0c3c0806040f0c091d06011709120c010f05010f0b0a0f021c0518101e050403060c020a0c0b0309210d0c09090f0209060702121609 59
    0x642164101c0084c81c020b076000d0782c07020b4039031070825401d08543d8851104418605442d1501031018046240d0b0030681091609002c4034290300b9940d20080e20910f0004484000c01c200e110005955600c550194444660b14050440c00d0040d81d988218509580640780510110800108000304806000b0506560004810b005480b030320301c20901c40b0709004071900006404928006a12020750314900e9a44422a80031030721540c50b0036441100610f07501c002c86081489640c100c00c88002030340200c06641c011644040c00340526003400300d0003521040104003c90b50000840400b080c01c0500301d050320b02c20721400c3c00074403410011060f2142e2107140c000301920100c0302008020040c80303480c0100040e004031511414041443c0121203800ca035500c0a45508052040c0141e5505075a0103080302c8080350122418200c06a659601c142056408104803460000c003501c0002d103403403d07 = true := by decide +kernel

theorem cover : BRFrame.Cov 176438848 176618705 := by
  have h0 := BRFrame.cov_init 176438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 176438848 ≤ n) (h2 : n < 176618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
