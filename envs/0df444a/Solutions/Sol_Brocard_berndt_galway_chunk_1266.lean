-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1266
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:04:30.123217+00:00
-- url     : https://prove2.me/submissions/fc3ce25f-e1d7-4418-b308-451d5ab4c4a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 227517985 ≤ n < 227697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 227519235 1250 227517985 227517991
    0x1b031b0c0c0108011508010e1b030403051b060606030a0c092c0702031905030601020f150a0b180604020715180b0112030206180a021525050d0f110a0302070806 70
    0x5c1c0e040c2c11041c001107030341c080c1c045030440741301030001c044a84170040c281d9560304058095200f2802e00105000c2096400710041809044e0f00700c0c1d036424031241c4c41419407101ca00740d400951102d003d01c0458403509450b0b2101020ba811400c0800f901d540e40d01c402580302010840322550007015400001c10401c250b0103196110329603201440c684031a2000d2144a4100d0f204841b08020300800000d22503402041507000000090003100d401301030380c10283d0b540200844001c1000e81c1002c407500c2c80360500700e04103080303850300c5005610700c0c2c2e4840381400002c2d00070701c8055a4004600010b06030a12003481480340c91803501c4142a503901c403030b003840740ca01201a40f05007031010300c0010040100e503012480c983c0101c110903c1807007000300b00d010342e440e00d07221f04d0020b9407000c03c100240e62010400001800e00c0e040400c54002c06582103500742e41c01840240b40500f040e08652511400c83d88a024081da0402440c208002c800002196140c90640380d44011000760740540f50a0002020030020f41d54 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 227520485 1250 227519235 227519249
    0x504050c0307030f1b1d040302190305040302040504080f0c013603030e030c070b030114040b03030a0513090c12050a0204060f08090a060c02031c051b031b0c0c010801 73
    0x610b552542d0313203007243e07107902c001c01924404002000c2820f110031200c4140060410034108000c00c182c01c0034565401d041a5001c030054418820801c407074890151404400b1030b0580c035030504051654081c4800707030100500490303107d641040490aa20841e81c09403041e80c5e4508000150011000403054942c844140e421072001c2511807030040c520310f82d40150440b1a454079010615101c40c860365442c5004010441409004000c0c0108900d503a040165040300c680c0f4081c500050790210034081215820540369401d03070001c1207082031090141000b0003004840001d4000441e94a4249004a0760109069000651300601c11140c045c0503025590700a003010a0451030309150403006050748003050500c006001d0a0400198481004d011541c112600103070140078a15001d81c000b0b40780da100040a1220920040e4003406102491017150301c5520a15040c000340115a82030080a03000140041070b8041000703202145c02900902900000499200030302c0310100c40000500200c2058008034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 227521735 1250 227520485 227520493
    0x1302040e040c090e190f050c040c02010b010e0f030715020703120306062304051003110316080c040b0d0b0f030d02060105270705070f0501090b0703050108010516050f09130504050c03 80
    0x648200c04641c0030302000740d201c0c28106c0321040c0c6140c00c0381082c0d40139440503030052501610266080e0190845a03080c9402d07600d00b54200341c03040401010f0600c01d28541c0e0980d0241105020042e205030440c0700d211080e00445045903038070b81c1c47c84c1c0880b00d080c3c813450010741c40366410060740e5040b60750903810020303504a6180060480c0000d03038550140b031166a106902d4a4846460381e400f13507200440d0075a248040ea941c3c1e10f4401c42c0d1400c2c81c80283c01e0000010340c2d040024802ca000c0005680940c0c0c22b500d5a0ba03c0d124208070200040c0400d8640b107036100c01c0c50ba0321014990340800c00001615200c0d0081c00003585440100044038074000c0c207040c0d50266205100240782030400d04254404401e00f801d039220a524202404d500c004907034004d0240d840c0c50f400c402800f01045142d40304210684e0144420703031325121414203880013a140c08000410700315012010383e0003a0f0140021500c0704851034104140d07032000900065a82c0c881707a041c1e0b035482c0240300038400144100c104c141415070040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 227522985 1250 227521735 227521753
    0x207090608190305031315150b032a0903010f0501080d020106030b060d0f0b010e09100204120b1902121005010309030203040b0f04050a06031d070f051302040e040c090e 74
    0x48202c4924007030002c007080f41c000002410450650f0100f035031707250004030840103140303215081d1000300740040030b000100194081c002809030240301100d04c1031540303049032148203218580075050b03c2e0a400c00480a100140041071803500c00b407050306080906c90310085407552401403082e0422000d00048021641004003c0c004240da11500d03d0b044401560b544200500a083c28140303403007080ac005010548020002690703160008101d8000e04110043d07400f0340c414040d04104a100e07500c1142c100b40b940300c3d8104003041104034000c0d480740c2c8680c1e00704401c410026281c400c0340d01c500710540b07485442406019902c2c2008805201030b00e401c0c20100405482c40d2400f9589005038841c010031402e0000c4c2406000c03440b1800c2e100101009003c40e801d441c8c031020080c001c2c04840045110341c004d1003500c19995480011040219110103008907402130802c0140320f81c9041d00c001e2200000c4c0c0070000011005101c0c03040a21585c00385507112100b904100b9003038181e540003d106c40340343e0b00c4a021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 227524235 1250 227522985 227523013
    0xe10050105091006051605010c05040905103005010e0d11030a020705090a090204050a0c0806031606033206030607030e1b040b03160503160b03040b0601020a080a0207090608 76
    0x20f4000c0d0349050605985980103110020311412245400038115400c01c001c10800c1ca40080181080e100104801c1c860380c1d5400c0842c0b50000c44502c00c030741e02c01c507680307251016414a03d920300d031b00784000c0c0b4034802c0c1440c21500d4090075200c20384900c04196200c40c036810315841d44000030311545800ca0300514031300500b4000003581d8000394050503110308501004102c0c0314046901c14203205902034410305c001d20b02880a0340041c0700c034044d6400421440301c00200c492034041482c22150b8442c01000403540d003007020447c000c141c00c00c0350081806c0b9002c0840d0103036500c15004511240c0070101411603280c046c05060503c100076004c0c80c02d1504280e21600c91460201d4142c100404002a0707c1c40d61002c00300180151070034031b104d5601406115040c0385840781007200002900d400b5070864046409413401c04100305014400c0c030301c110005001140002e03800141c0d442c0c0100c0b0510456280c203142d0344420050758052010800940d20180c1e0421407038289004050042c080c1c64080c1001e001c80c0c20b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 227525485 1250 227524235 227524261
    0x61205060a060f11011b0311130612020d061403010b01050a080c03040f14212b0b0901060f081015181505070204050606131203020c040e1005010509 65
    0x1d18000c0c055444201e5103d0340c8030740110040c41003080001d0011800c00c42e281c0001034422003c0200180c14075403041811000381d002c445c00042c030000200c4078240341445c01c1710121011441c2180b52030b001c006140040590340101d802a140100c0741c491403010190405084071008014141030190910601348020341100405034010400080c6030740e80c1c0d5540c940180300184c3c0940c010903444803d80540000c10002950765504c01658801c4c2c0d080c1120401052614094074501c007119040154192881c024504002c0080322544003010902c00341c2c4200045601c0e85c00d03000000000c1203c12a001c0c416030142c1941d40001841056145ca1030030507401040c20481148500244a10302c460060070391411801c0302c0013805051001c2c6020f2034403100050061b481442c051340319a05000119800f440c100c01100e00e4910f0f070007180c0b0012450000d0480c08558000c0e0140c3c250b0180302004802d94071140540103613005128050848131018080440444406070480360080c441d2508024484001e40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 227526735 1250 227525485 227525489
    0x703090803182b080709081e101b0e04090b060603040c0302030f0a1506060905210105040f051605030303181f060e13030c0f0303090b0f01061205060a 66
    0x4150407211202001545007883c0c0400006426180d02c038481d80021114400400a0f60540e94014a0742c64800c011203202029000d641c0303164010f800301814001004084418000800c4180c0c4d10b0101039141181c2100c031054860410040c400000e80461540b0200e50410340380d04940800942695884a9904400c001d14440c0131b00e40020118090102040111004540c001c00301c2d00910b020b05442e40c3ca40303184401c220f4640407402081c10080307075940640001ea07801992552300b0207141000700100111140d100866150807c1180c40c0b29440c2030103030798481c41c044c0700e007e9800e840314a0403501d89020701e00b4411804802542c1030099a801004507600407c142120944018002c800e06040040841f804510144d11004602c070040752074000741c088a07009105030b0f03034658a41030740035004514a500200010210525000000e40d41075044030814041e1a0000c4c429078103503214003004c032040d0b9180d001d04440d2401000241d510003030103a01c14075100070501c201c0c240107000c078094910794 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 227527985 1250 227526735 227526751
    0x10609030c0504090201052b29090c07151a011b0b06030c180601020d08130213110a180b04181d1c08010e0126030c030703020705090703090803 63
    0x104101020340e0b104000752346030b00c3e68590300c1126103d404200380c18102d2030896038481e900d0400914140c4041c1540c800000304030b89c2d1200b290360316010010001c452800508480c0103d8085c0a054003040e1310546446000f0354802c03001a202110a1000c24040c1c13801070860304020300e4440c800c000596246405251300c0d80610b5014241d1101c20000742003110001c1c07007a420803c0824030011341c0a80c3c1040078014802a0280c52555851074030441d0902c004880c502800c541030780d203400040c10200084a10303804035450004070404e0380e000820b000d03071201c5101800928003000f4840c0b10451800d140004061286115280504d402034500005500040d106211541c50740c04200502c009050390780c500d40d885090fa0394a840b2865180b5955010010142c00102580b001103100e88401d1213280c140c40100c03117640c2c225030010681c040c0e800c140b40740036003107408203008040b05582c0c00c101914103684642c02524541d410201802460307500142140c003014189070603c0003260745542180c1e088402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 227529235 1250 227527985 227527991
    0xd05030904090510181703010518060103060302041e0c03061203140c060c130501050a141303021f3c05041e030203010f110d0915090605060108010609030c0504 70
    0x2107003085030803c4410030b803600341c21703042081c04402001c0d00d10402c4015803244c2c10510550061002c5c07140c460109004041d0080c1c07142c40141440744004000300c1e031207481450045000e549a502180c00d4413400700449801011201000511030350314090011a0066403908000d0380346012500701000c6031a2034060240704120442d95400f40c000c10440e6001c2e840c3c5022100c007410031150110a9901a0500b01a62000ea00012909600c42c0c01160b030b80d80502c0c1c0d6052254562280000d01c40d0340400c0100d030308001d07002c80000041c1c03030b80100c0315901c540324404803026425510000e090b94580c0c24113200300b0704a090f19403048a10107025034420b807035400c0c102c0c0e280071a1882c007a03030144201e410800c500640c00030a00c04480d518000e03c42a41d01c20380003440303484401006c4a00381c5140d81c04850790a8000c0c0401c14846009903c0030003c140035448019080c07101c03540c030b00304840b041c102c26510305444404025407540c0010501d4010a610300d0440c0744607146841d0281c0003c9070b4010035201d036031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 227530485 1250 227529235 227529251
    0x606010e0409140304031e0803041e0606030312060f050604031415280b0f0616060905010c170c030a05070509040c0936020903011d0c010e0d05030904 66
    0x7038641c0091000c651140c000c4495114103205943d4941107440308a0f01e6410288501072081101419610455401503005082d902c40d031b99000b04451141000480b516159100080820400c1c01004015130098541c6504400c000c1c1d400340a13181d46030007140030040b85510400817034075481c01b140c0803250000c21740c2c0000040344002c0340c1007000c5c40089085c940091800d0181810a00004400800d50300800e001c007010505d2030142a58403015500d5444448401c802d0480e0074a00028000060501314038403861846070b0311002122009841641c0300d030340d140d4160a02c190488460701034408034800041d018039020b4108a19031100030b00c03084c0d00c00c1d1560f01282c1ca132030040d0306540c4180300081091000324000c1e480202001c0003403150007070100640756480c16117186081004007031340d00040521100703482c00f4101c00280d0b112055081d0150340e20b40d41c0344031a00d4400000031000c001000a0700701c00e4004c0e00010031000309614403030310958140d1104000184000308072014000b050780e010038030803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 227531735 1250 227530485 227530489
    0x204061d03150103080a2604020d0206160803010e100b0f072d030306060503070c032a0503071202010c050405091005060c010b0108010b0c150c0c030a030905060a0e0606010e 76
    0x181e40c00c56641200c2c10420010007001040ba01a188443c456074901200c08844006a8290110fa54a1504004100c404200941090003584e61618000345c009860300741850080322800301e84a00a507804800400144061080002c583d0781000b0814a104000c41c00d02c04200103c4c4100444141d60341000100c00c1c0030480c6890700c86000e640144845c8003d1814561003100025105a04900282c64020042552800342c01501d0180585d07640760389414445036010781e445808261852014403100030030304156444a90020003051194001e15100e86080c42d224200c40140381a10341503904003a440309481d684141a1811102c0855102c450342e00c0746019802c4c00c801940100c1d4000f88005840402200150404000c11f02c0070303030700c030682c0341e80e103010f49003950049407820901a0809528032030001d040a00ba02d410010045010345809191030141d840c5902c10441d0001094603112042c044c084284030903648400d0030745081c0040e150255030300391900307401040541400445003200d40c042e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 227532985 1250 227531735 227531743
    0x11070b120a0b0402120711010912110111041502060c0301051e060702330309070911040b0a0f0e12060f0a14010305010b12030f0f0a110a0c03020906040204061d03 71
    0x5060141c001c40d95040614509800d05d50200c0300030020850821000c006a1070501c5154005130b003101000c10070040000c0215241d8504244d41d40c8559200c1100050324400b9200410041c01138104d81c455030b40c110709020381800e0008007005d2485805200406c25a1114000072018194250105500e44e100c10005407860140c075078065080401c45a41d8090103155416014045020440b543e110312410640034100344411106009150400301c010010f02c90540c02420403803040c195014100707911780b00c3c1580d00780c000c14030b100e000600b80d0b582203000e550040d03c103900da01c40030382d541c8410006c401000c0380c1c0c5060181c11100c0a05031080040c0c4010800c0d4000c500300c01e01405482015696410040d01030200525900d204d1041c41e550382d08411000021568480c1c80c00b4030940c206400040140c01035004290000140443e02c5071440c0013442c144500303001103104c0c0d41c12101150450040c4200200b00600940c0950302c10002445444d070400c1002048500301a04c00400305850b00c0842c0c20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 227534235 1250 227532985 227533001
    0x31704080105040c1e061e0c0506070309060b040203130f080409020c0f1c0207140112050c0307020c030f10090609141b01180b0c0708071511070b120a 66
    0x465480c02c1c1c107110800503110036100441c4d06080e03040c107010000c0c82c108100c44419202e0039010402c035024007680c0c2d0328403c41a501e0b150340c9041900401455846890034800708990840c00a075507980c1c0c0d1010840c0c40c0c400c0d11011b03203064404605514104c540c0c1c0c00b114500000140c684841c01170080c082007010400c80300901100e10043d901c840380c07011030680c0d03101344208041c40350056265060340101d443c969600c0901040c5c1c020010103141081004007c0e20b4a01154102304c0c0c5d041e022a0141c4040c01003900070f01280949954130321b44480020f00381441482c00074402e8000540a00a400c3c0018100080c03c0c0e0104000420401d280b034200020803e102d070041221650707a1143c1c00014000c680142041c01d44404841001c0c800401140e0517035000300c82d0f4242202081d802d001000d0110058951030b4105811101c0303040e01d40d03401c64541512644503d1800a5860301c0e02c40031a80202943c000711101d40090444500b010507030101c0b03019040317156908075084000118908042c0c1c00c41e1907 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 227535485 1250 227534235 227534249
    0x2010e130615030e070b03070e06130e191404031d0105071a010e010b04050a060503070309050f061519090c020a060c0804020f120c150912060a200301031704 69
    0x102c2d15031076202034003038005828510200d01402e10005100ca10b400d040f07030b2046490b41d880120545440c010801c0642126104600ba240007800125540201901960060107252044181d00040044810580e41c001071400030342032540062000090f080b1000d01f00040404220100000440004a80074051054054070400801c1606401105038a030501d040ea5480340300060b1a0ba218500c010985c031652003810f0b01300c1150501040040e104d00084c43d0030880350b04e80810000ca03140c0350703189048000740380224650041d00911400390005c00c60002000d01c2520160151100100c0307500341e0740880c1c40780300221900e60500c1100d9030710a20000c0001507200380100098501d02000402c9050212000c074000c18140c124a009840d0480000c81c0d09908100104503541090b014032008440c1d0440f1703000240d0040c0025900799030b461021495080022004210f0f07442c0040599041d41e46a003003200d0058816030025051035004021241540e40201d01c0c2680841c010084e0700591040d580409 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 227536735 1250 227535485 227535509
    0x7020a0206030f0f0106020f0a0b041a0f0106110111070215120106020319030207020d060903030204080a050c13020717090a030c12050f0d122a12051302010e1306 71
    0x490151200d03400c1c060520134031640c09070381e00c44400782c4e61022410600040e175401140350000090032000703003a9026101e24141c4159601e00c8260798800c2c2c90982d44c10716402c24640060104c198441c510451005400c0300a0011503001d000c091007074403410502a0280f60502150688004c407002140c15404400500500640c2d41d0768009459404c6025040d909101103520250218401d000341c0700f0082d0000d1144600c440c2968031000289000803044003031540900001581ca501803003d4038000e07008001801116210f001007081443c0c651a0507560684140000c20100f440c0d0342d1050700c0c2c0000d142000da0f0312849000003540e0034034643d0000384504e01e40d910110b000c00e4001c0c0c0c034001d40c030710032001c5071a0303c0c0c0700e07220041d2507100c1e5442c0c0500042161421052151107604414145a0144090480000c852400600400400102c00c0c04501e03030300c000041140c014407520364822104106480c002c650390f40000e0107000f103c861144104413aa40010b030a5485621071700080c140d0740024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 227537985 1250 227536735 227536741
    0x20402131d0f10030803070e040905010e070f1a031303020c030318130c020d030f0b090403020303011a03070e0105070302010f1a040f0e030702220614040b060a1707020a020603 77
    0x240840c441190741d400500b03a48004940401d10402901050380e90014241e81107035110b40e0201c030f01c00c104400c450351150320340c0c0c060004a0400e2158401c06d00c1801c02510700c0d80d060280081225035607a11008a4140c264500300c1ea240d4402c081e02d82040440103441103d58281c18202d04c0c2c415072180156040c00001010581c20031103036100aa205004d44046c059030342a03650110455080c0000480540c000c0643e10869071300c20b501030130400081c4440002c1c07032b644003004109206000c0707408401680c4004018440c0c044120a404c2c0308a001d0030f0020320313515000e0300050800c1110fa0300207040c070001080325002c15000f034010154600113017004001500b0b016401198031262582003500036407820302e484440c4442b500405103501c40d0360000318907109540c0d007802100f810310070b40170140c104503500001c0382d80300da0701402c0002d01c40d07a42c40c2201c0000801c04c100c11644603507181c9110301010014881c0701d0f900030780c000088420345040c140e49544c5482e001c2e0706001980c3c400a5000100000b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 227539235 1250 227537985 227538029
    0x8070b090c0a0801051006030c1101090803070801050d111e06030403020703020915150702030a0b01080d020705040516120b12010f06090606020303180c04050126010501060c02040213 80
    0x2801c6600000700c2d2900d00059440721454200c54054681d0000040055002c4c0b0929000360080c04035a82035280c60620641880726650840d00c020404a940700e2000081c032545da1381c0b241c0079902404c0700304c2d100b0b1030541d00d0740d480780c070b0829603a100706003c2c0c20410106081c0c0e58011000446041c0041c2c40746030790345070614009440e9112400104e10072050307100410144606081c2c003108480d00584041c4284e41800c04107e00ea400149040f0391510540c002e400010781c076480110300a0018000074403824000403000380c18410036800c101e006030f00d04410490f507416400416840101a42000050f1500300300c4290040c0c000864529001800c0e034200c2401001e05500840082c919888100111074482c3c08580a60f8124409c0c2001a80240040b512482c0620740348070b403ca45190444130b844200300c3c003107025a40c0981c002355485e0001c1109610390301580b007000103c2c0c144e110003004190f040c0003016010030032240010b4042d940c0890000781c0c5e0219031107000042c1c03080e0440300041c1c2c1c008a41e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 227540485 1250 227539235 227539243
    0x9041805070902040807050d32070603090b1f031b031401060503120f0706050c07031227050331060c0b0406090303140702070f0812070f08070b09 64
    0x2004884910440303500082c4208144203842c141c40d41c001c05001890b2520007008450019010280e80d40f410010745101c0d514441c281c48001603a00d5503200d0b0341c5683d2011b009050046690003007050500348142c000001c1c030031101c1c00e40c0c081816030044215494074000c4901d00c50070358000034000b81d1005041203a4500180d003000407644030b1251080040702c4100041d0a80c2e900e44540c5070142e200c0b110001000740580054101207003a442801e00304034107502c0f44419544140c40100c2e100d500000e03018281623204121a843d070b070000c40c00344101024900340c108082c054880d40c0504031002104e600800c441030085456a4091140220074209199203070b5818000c0942c46020f40404220300003004c6c0e009045402003250032800c1d03503c2c540c1d030fa900c51401410100004404143d9100151600c08081e80300c40e90143c841d135030061260a06040c034501c540c1c0c8240d0015905a07015030000c010720310300300e0101d41c0c4407680304900784540c0b5254608a1164012444000c00401410b0100054620009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 227541735 1250 227540485 227540531
    0x30403050304061112012402030403022b0812190b1005030a090605090c0a15050403080708072a1a0d0e07080a06020d050708060f0910050d03050306040e030f0d110904 73
    0x1502c07c200121011405a82c1c074400c0d480029000f05500c3d9014180c0015140050a000380301410403008030042d503260306140c2d0041e4804200c019a40c001d0284085a1810340110000417400c10080704040200050040c1000d0340e44000300140040042d4400718150040806194000c4090025041c0590155200c0204200d942c0c019001e0050011b0410100d9150b0303000014544c5401d841d150854a07042e005600801d4242c981500800100d130004013027520400c5091101c80454004c0380e0405c022403260b29a03a4040c4988440c0b1001c0f81a404407004200d0301e400c4640c1c000043c80d03500c400881400d00e0141da00110340742c010217a143e81400003e4005080f045441c580410255680c0340043d40c0350042a6034903600702d80c850e085401c9078181001c00c95086554001268015507903040082c0201a10780000c0b0001500401031213110304150180520311030b262001781d0300388410040141e00750b00035800004103c03910354024000c0740014104840060102600a015503007000c40d58602905d034031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 227542985 1250 227541735 227541779
    0x15020c011a01230a0509060d090b091605040203090f070f061e050a050903120307030f06050607031b030c0512030411030106030c0b0d0f021207020609010203040305030406111201 78
    0x41c4541c40300642c030580302480c9048030820001250a650300044140d60044038030003042c403804003c8140070382e40d40c0e800340c40408076441d808225081103207000c9100d518041c040410541c004101032540ba00c1549400013543d809441c0140c03282d950404403881d2000344208184580a02040451440101e15004080d20501c4d1a185640e2961ba004110402d1035180030b0b10004405101441c0c6580c0b04000408a5110003001ca55400305d00c000d400725185d100781c40c0d1a000c44e075201d18403524046a8001c41c4010142117408600b8014907460203409e41c03040c40d5030101001c141499010030140a81398a0545036081401c40342d0507041e02a000d84158402c1c1ca081d1003a0104ca6404091440c05003c0e4600340c0368000f031144d400b145010200c43c0c15800c00141c4030b46254a42001c02c5901d00688058104414542541041c80c00e1007200641414000f4044d00e006900401c01c000c00720750810202c81c0c04c2580b200000500f810103440309099400f48200c40d1000c81c1c4048000a41c040360708070100a09a0341d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 227544235 1250 227542985 227543021
    0x5040905060708090316080d0f11091011060a090507030b010e070912030e060307110a050c0a0806070504030807020a051207031b06120b030102160606030317010b09090415020c01 78
    0x204d681d00c0e5524016107015a0700700a0042540002600c40c0340030f09003041240c10045800528a00e404007a9400380d581c00541040105200c01d041c64842c108844100032401d0100b03511800001441e12403200030b1182c010300303840b44035000c10010204500d500a64100b600c44019585418401400031029a002c10020303684000209000c80304c8031551884540c075403554160b40c01481c0c240980c0340c20080004061041402c8030300340e0480c00303102e0405c5080c403507806404044600000c10042d50002c0d0490343c56680508100038403140c015084405a0341c10191090b2100c03a18800191840402d402c183e400201600000b83d102c800040e001d000e9a1040c2c042e480320b401e200102071461980313071181030300007601000c4426103d40c2071f130320000fa0940060009481c0013242100541000c4c1c01e003004840ca41d82c2c0c0c400800c20f1551000640680d0003031188410b000d54035201d40c082c850300586a03807070300c40c80380c15005c0340c1001124004d0b8109981201070a640315000405040c0c024140c42030721041d140c0c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 227545485 1250 227544235 227544241
    0xf101a25050d05181e09062b05060708012105190809030c061602210a0b090609010501031a0702010f1805060f0c0a08090709060e09011d060105011805040905060708 72
    0xb42419030205c0c60f1510043c01040c0d0320380201004800d0002415054202041c202a4854a1801040d400800d0450413902000c540704d807402d6850580001d155004100600c0018006030400d65030034003030310440c611100040c0056061050a00e40c1205120500c1d007070440b076220812080902400c000a003c0b000c0e51b031881500010311460348036220600c0310800040101c50018545116114100701d088219002c00300328844001f868510b98500036541000542d080105070b6004025041d80900c10200a0002e03500d903a07100e020700c82040c8403080340403c0b0003000404180c402d43c0810242e041615003440015541990804030a9200d0b00550781c9000790000100109281d00886018070841c200c458035080d916842282c001c130000e08454185d014842c00000d03c3c135018007031100640390040c160b404500301410b0840c01c45c0c1c00458144a07250840d2442d5450403404101a41151000e080940c00c4034504080c0080720780c590341100380d006240100e00030a0240025080d0300c69890707515200c8003a1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 227546735 1250 227545485 227545489
    0x20f0703110105070602091201090c0f050907030c1701060f0f03052a040e0a02030115020610060315081009031824030b04050f101a25050d0518 63
    0x340005081030824048125141d44950002c00241d03005040042c00d10b0004c800003186810040385080d000c3c0e464060752030612800a20b907200504005000340c0c0303613a02e4200401c0034040c00a1008040c90380d00c43d0308a0155002c0c110b5030744400445000c0005039038440d1406010a01100304407000101300410a000450281c8100d0f1f010f40350900b407030320b80d0700d12500c0600700340c00740400301c2c0c0700080d03041c40300148500010a09500071030700d55902585941c102000400320416500501085500940c00d12544540441113102514443e19010588018103501c009502440e40e120f000144201424011150b03050303400b402ea00c0e8440c0d902c021340d4103100e003150044052540031b00d10a070320207421603001c030124680004160b258541400710b9190902000102103540441e0841c0041c0146000c22a0020000740f5481c09029040503010740c81d0303001d40d0381040e00d01420440254810040094500951400395000c120942c460121190b080e2894801000c54020b400c18504910030b4500c800054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 227547985 1250 227546735 227546743
    0x10305071e09061103090d0f020d0206030f0f0a060303120510080a06090507080703171602041b0e060315010806030709110a030510030b4003080c071e0314120403020f 73
    0x70407000340347d02d0540865859a40b9a41e90f030000072a449015100c6000058460380f018501c00c4081c00341610710340c80c0802c0b203040c04032030061000382c0c07007407070b0500500c00283c01a1194411282100000845590f100b084400e00300558200e48014450b00040508101050300311a00c414401c100b901c01483d42c1d20781d0703982e50f9425400028500200748101e00d64507402c40303014000c07403a888a01f00312704407515000310b030850f0784d40d801c0e4100924800410740d460a0f00b004089542e041c041d28500c0c9140782802c00d400244603000070045c10000307110089420b03a5401c201a8000e000c008408018a203200c1c65085180c0d071100c060000424284000208007085d1104501e00716600b05022169564651040e854010741d04c0410200416200200d10300a140c3c02e001c03451a0261043c1000045040f4100a4454072004080c801400c50402114002462007844203c540d901d6602c1c4d140c01507001c1c42e0a03100345205031036456890074045405280031202040441c000c50080d000d840d8028600d0700000d8503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 227549235 1250 227547985 227547997
    0x5063114060d020607062d0e06010608060d0f05010e07051002030408071403160b1e040503031e0705030703030614091006050a0203131e051e010305071e09061103 71
    0x101c0b19a2549190150410000038040244a05d4001440c0c92024a10340d40000d4148151118010b00b04640b8042813010310aa99941071407500404042d8944800100700c410300030001400384801403400c0c010800d00f1031030349034080d5010000380701c49004500c403156110058442d5922074102241c022400a0000c000c030b605940310100500161030511060b6040700018044540d01f512540303801c1c2200b90307140510341d40a0070030108119522413004207101d014440385003d04200410400c810801e6a50000803200d034070711100c1c2300311030b18880c000103406039002e91701c0090701a0000054400030950705600c15400c3d10155190303200840ca819043c40030304031040701c3c450f07559030b4007642c02e0000601420180072440c0580c81101e14182c4a91070002c1f154202d43d000b02e060340b0140d00d400d610f440301e031680c2001902c1d0030341e100c125949a089030340000d0801400c0907410b02d0b698601041d4854828125a0030050034543c91079944100c50701d00400c002c0a0380b2480b40058424856001581000f10803181 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 227550485 1250 227549235 227549239
    0x705011d0606092e050d060c030b0111031206030a0c080106030501110f0a18051009050f0303070c09050402151c1a01020c011419050c0c03060601120506311406 70
    0x1a104040c03489051301203c1c81d58646121280c1e2140000d2a035151202064824805c1c0da0201e041081a480602912803141315941441100400048c1c030f20000829a640c4000301486c62445840b0a800f290510a00e1103010344010f407800341c0841da060054005104036441800204504100302d140741440e402741491031011544200004100c99228a0741003a400500c114480444c554580001c0c0459152126020205030380e074104000604d4007500c020807045c01034028516050407540c0c0d008458189001d000543c5030ba52002c1015900c8010038891051000401140e460703521117581000b065031034021584541c10b0160400d007402c403031001000358490680003400d80000c10700c0150344000444601115841040c021105142c460f044548050006500c0d020742d1484030031351003070410b8400200b29010b030b84060280051664041c481884030203466500140946484000403000d500109621442601040880302e0218a040c0391010381c55920004100d200c418a03078011065004540040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 227551735 1250 227550485 227550511
    0x2090a1e1a0f070302012a09080304121401060308070f1b08060105040b0f0306070c12020f0c041806090302030301060e04050f042d0b0402090f190b01050705011d060609 74
    0x1844440700318003034400f0503c00c0c00049209104c41120301c090501d041015034a440700701000946640d0044081da01500c0c0302d10145107030509041d2010441140c00380c0c010064544900c0c2d100c0000420b41c01840a90f5229540c1603441d02141080c40507440c4505080c0e0300c5803000300b40d0750020f00d1800108400c980c402c10240a035070703180104100080c00c1c0c2109194002519281084413540c0030702c07280344189901d883d00d445e844014203000342501400e07245a01907610400d0002e000542c0041e04040142c401c440111b03c1c2d00c14000c806907500350b0085e00800040c100081c40c2c080617000300180d03058660669a140520009004210a0b1803054451003640a208004a8080303620045810000040c401c0454030411407000e12200c0c0c0c0030403030b005507455828903090004601d07004210310b410980010081503541072515456109044c21041a40e501c1c0d511890103003107900030001c0d580040d410070b00800c00d040400c0c07020440d83c1d41e02075140342c86014090003c0c4840c80c1040000c0d008051424240c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 227552985 1250 227551735 227551747
    0x30424020709021c020c0d020c031605041508010c09080c03160311061c0605032a1207181e020a0f050306060d020a200c030a0b0a02090a1e1a 62
    0x81c03000f54404a01301c41290604100400440d82c180000d180c00308900303005002c600c1911300002d00f0b0601ca00d104510940040c500d010490380c503c00400700380d420440f40010982128200c1c031954100381d40c4a0b10b030319400c0c4142200002c0e00018014215400d100950380040e13418420552622101200340d02c1344490a2001c0c0081016070011101a003005098a4039280c40705601d01c0f40e400640e843c03020525240c840074403481c281444001100c03150340000180040c2020008141e01c0049000d40c1d0040010700d2107064106010050301d002001c213240b040d40c4c1c000788079000001810f02c0b810b440050b010f0481100401d040700d80f00f140d4032820150345100c2c8101a04038102d0b0b45a03c06040d059100000b44600d02c0c807940c2c82e200800617542d658480c0000880d045402490250202c003c042543d088545074203190b07100132491032091030b4800d00e143c99a80c2c850900600030700503451080d4100c2000783d4003290040d1203441c4101c9601d04012401121981c60101c1e41c1b0160a07150304a02d074110078080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 227554235 1250 227552985 227552999
    0x60608030c0d1803021507060b2d030a060c4808040503121b0708060a0c03021218070b09060f0d0b04090602090a060c050a08130e07020304240207 64
    0x480b41c03c0f007081e043c54442c042c2e69070000303880066158408507413107000084007420421030703108165815005940000800c0108403682601c6000d2a4620309042450006280241d40a000c0c034050264402800c200702c440345807008040c0c2c0c101c980c01d65914001442d81601140300000300200340485070780202c0064171f1880c032a0302c1f030010981c0101c070b00160601012801ea9002d0000341000c5440f01109503d6030b9010032042e41c11201e0050110340758100c22014003980c08049019a4404031203000030541080c015001c030028840e0a80705000201e4201c2885520a40000c41c40507260039079080f15145501c65048039802c1c4940350510703034000c01c00c00406503409001009070203001e01030f80d8006010480c110215058441c80c0c0c10444440703500146555040c41c1510302d030310140c901803502011001180da2090381d1540b41c95070180c51540c1c040340c90690507203550101c0d03010380350042002a040c1441400a0350b26000f6000d8205151000100100d4003a8002940140c41055500030035070342d454044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 227555485 1250 227554235 227554247
    0xf03060f01120203070f06031e0c0f1b170405100513060c03030908280314040b04080903031204120c082d270102010b010c06020c0102160f060608030c0d 67
    0x1040340c245c0a03020000130240040301c00480106650f46012401040c00c50400b000d40c041d481140039074915092091007106c2e4800300b40d010982c841c2c1841c9211030902d8130005444030606800800c402440c1d01b11740e260640e940003810403a8405da1700110300006113078082c0c4a44c00780c0100812144034002040021a20854400364068080d0800150001403070300d50450b20341c082041c82c050610008007030703981c460400305c0c145a01c200d503203020044d0a48034400c10503401d030040e0024040d040c0000102e018003034003a04561206400408a99444204442011040c04111000d0f80c0740308400055900d000d008440140480742e010b00c80c20f180580d05200340e00c844d440c0340c000d1f14007841c00740d410a104a022074001c000d5410340300d800711044825091164114030b01404500d04590601480c42c05070303600f181d20780300e00d603500c4100940c03900c458007280c0380240907065200c1141c10000d20290207101302400400c031780d180142018800710f0b8450144582c1d80c0304072881d04c0304940c0440710440445100796 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 227556735 1250 227555485 227555519
    0x222050901050d171207030e0c01050406021005060f06030112170906030a150503070b04032105070326011412010506150904060509010914090706090b030702190605060f03060f01 78
    0x164180c01c01c2e0400d03081d0145c02a040750703400e000c2951898030000c0c8840400c5000d90744817091034000e00c0c10703040074030083d107490071210307000d6504e80c4036004103c0541c0c03440320580c00c042c405094592031390303501d40510405070002d520a80b4951014130186000010103000c0f00d00311030002e8442440c40d1280d4189800520544642819035a00380401064668090262200a0604c180c90b940c8803400c50400b100b0034609a083c581403040400b41450926400c00d0580302c0b41c0390181040b022482d4142d00c0d181c80d00410522285070ba014240010036200e110703e001501c1c43e0301c01e80707421003100014050070b4201d4001783e900c0e5030b1005003032990b01c200c03040d60f20041690480191001c03c000390f44101003039a0b200c082c2c0240c2c3c40ca5880716040064241c60004480e1700a10510081843c00e1030401c026100141038000c883e541c000001c0001e00030b50007004041c0c5054044449a225027199080080c018039040d00c0b00343c421034881d511000d0502d800189a80540c84145000070036910303003055404034410031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 227557985 1250 227556735 227556773
    0x7150f0e030105090606040f05160c0201051b010614030d0c1b09090b04020102010b31110307121a01140703140310080114090a14010e010222050901050d 67
    0x3400800c0c546840a006541c01881104020009030808404000685050182c6900c04c80d2a01c1d003045007805803146004034140311812300c01d49a10309030004a40d81e108070f150042c0c01c40d0036010395a0031034030154007460889020802103c248110441050b071030314284010324002805003140c440c04a40c0d1982d280790300300d40081a41c940325564807404421755410001c00d44149560100300b00a550f020302520400c170344116600703c0c490f2030030a5000400c02c90500103442c404100c80360540321000c40c0e485120018120040c140e240d10b00348800808052000028a4089003016002c20020030201a4100d030720380141c54080e1040e2000020f05003a4004010580801104c02c21002e040e624000041d800340443c0b00301600c266003007600e6142554414401e05100414000030058616004115070000b0303603108804540d418560040f2502519000b00000351652000811900c1220f400844406114881c84002000c41e80c0b4020050104801d11031141c001c03421401100c00619041c404218008817 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 227559235 1250 227557985 227557997
    0x7080403110a050126180109110901080a050706030b04090212030d06170a06020c0c060307090f0806011508041b060507050705030a1e030c0602030406020306010e0909071203090308070506061207150f 87
    0x4014420b003950340e2254242c95000c0c02c204509c1a80c24a01c000502400044c80104082c030b11950302c85a44481c00d103d410704042e43c404c4083c2e01982c0703640000080c3c640061003203c490a8802100e0f840f0751000d0b110070310162801c003000401b01c40038800d441010541034080e0000d9285500c4060295000802c20595402140d200c0042651200007079402501d56688244c491130910013110082c4801c1d40210195500c8030700100030065031000d003181951454a0f010140d629940b41489045450001e02c6203224011072000c12956071000107003200f18011401c030f071400c5a0b24424541c40d248840c0700940104031100034110b440c49541d59050f40c0c3da200e0300e800010760741710740c94410480e04265402c8503800d40000034005a076030b000c00d51103088101160382c44c0382410108400750b550951480703060040780e10310070007005050050003441c4c001c4d074200708061707074500c40c51800503100c070310440e1400cec0b00d00b4000e0104079001d40001904010750f40c400381500180900c0e4141a55507070343c2c804100c002c000d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 227560485 1250 227559235 227559271
    0x60c030216060503040c0b030907050103020702060d092f0901030807080d0e0d0306091802040b010e040e010f060815010b130503010c0309120314040b0a0207080403110a050126 77
    0xc070410700c0c00c002c0003140d55841d202c0c1000e20703200e00c01c8004d603407180844290510901540784404100c14003255002d00700182d44d00346902c0030824600601c10209861450407406406000c42c0b5840d000b4800301c0460307d01c403948000c0b0071501034052504422901f0066140040c000540b8100080c40d5150050181509103014402e042007542c0c40300d2510085500550315940c0310307d405024601c0544120300d014070030ba00454034041c034103090600c000385c42241c4641c00c00205034021000da000b0310001410520411400701c40c4c03103000c2c021400b000c416051400b1000902c4110200c1c1d089a9144172844401460340303401c90601c00d0342c103d901c01500418124000040503a0248036603001400d15860200d6130b00024140744003501f44004005041c9403d120250f21034041c408111540190303c84031815854a9032001c0100034003500c400140a41c0c000a0048140041c40080071451101142e0042c90307140c0390801100c03a0340340070501324044004240014100301c07005691f19072102c400d180c6031340400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 227561735 1250 227560485 227560513
    0xc0306050d050a0302060705030702030a0c0602040801020f031509070804290a150b0a050417070e0910050702011a090402120304090b090108070e13032c03011410060c0302 75
    0x2411140040b1980d5001c0c010a0702010f805000082e8894140e061941c11881d003400042d440c0d2040050f01400c00c40100b0709001084110303130548002d0300800c0000c6444103415503400c0502d2348261601c0c008043c4102e00340f180da14050101511604081d40c4491160b10340d55100980464000c000304044c0040c150705600041107141c2c40c0b8482c1815810102d0107010624040072805115040f699040100b0011842c400d030304030f400c8908982030940c464200e00f01c086070250410045802000304420482c003800102c1200003901042d641d0156001c0005441b503500c103038200d0340803580c1441135031306803c1403402514164081d5544140040c00d0420302c4c0c810038118605582c0143c001d03091103076039016042541d0074a09622409001401c0c0200052070814502d50920070004090808200442c03c60700f041501c60410750401c0d00c24048101d03405191601c2215068a48201042c025841c007850300c7c1c001d404091050b40248420348000109034140b26085941200030036046c0c3c250f01c620034201442c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 227562985 1250 227561735 227561749
    0xd06090f0b0610090305060712020f04150f03090c030204020c0102071704080c01081b030912120604051e0f072a11010203040b190e03160515120a0c030605 68
    0xe544200660003180c58080104150780200e2000c0d082080822102800003d10004940d0b030060018103100c0402c03100d15003403070081c2c410504202c0010340e012800145031080c082608204107200e48510004404801c2e044080310340301c2c14040c100100c00242003000d0705240d40107045080f0b6080001d40382400584548203224102c680180074114001030400c008142071040107480002460000740700d00b0500e91030000f0001103d0f0b05290508000042880c4200c04c00402d92840c80102d9929150000700c625041c06000495045005904180005180081d50a802a00080070401440054840e0100f2191b440700040824050104040d815082d8404004180411158032001301c400007855103451800061141e00d0079041d5413041c8810300c21100d150742507038111000807546071405480c20004403240c58a607907001c0d1b054002c4c5217410050328a10200c0300140c0d24107592085a035010034074003038918800e11840080c0740503004042003003140590045034070081c8500e00410300d10f480300e0010b404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 227564235 1250 227562985 227563013
    0xe03030a11010e0d020a150b0a171005070c0f0602040f03050a020f01020309031b0609090108010c08010506130e04020402090a0e041106071e0c0f0f260c0d0609 70
    0xc10198009241001002d00070310303d20008800141900b9004ca10010350341d80c50406008000000e002103200080c00690b00c002c001f020014480c503031150360f070101220a041500807502c218007420780d800f00702c0152030103490b000f50810b07600d440d810031881e101c0c02c412070f030342e02d00445101c1c0d000c03c000a10901c0101544c0c024501036009850004412310401c40c1d00c800400c815815500240691840e69802044911250001010718100e07140d84034000b4045118125001e603110103070800219140380158010f281001003915001c1d400d91700c900403c0a07900907910000c1c8800003094041c070081540b101d005800c07500c040c10243c2407095a90014034210900c1c3c000c124288180c004120a0044002d101c00040a040c1c41c03203031500542d500d48240050040500c52001d1003171440300d40c20041706a604400a0401019140a06489000000c4800d911348240b0100784c44840c0c0071100901e5071001c017103101a2081c010260300c0780d2141444110944134205488040d9100c1c41d03800800c40000b40806 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 227565485 1250 227564235 227564237
    0x10915030f050711010605040b06031602010f020a050702030606011103030a0f020c031206190311120307060e011d061e09120a03060306230c090a03240509030310030f030e03030a 78
    0x145207140c44e041e103084130000d03808a407040342403405d0500d140d200d0303008070394002184500241c403103440144141d0240c000024402100307480000c01e041070690040c050023040b40300710241c450f07603129400115903401e100c01c50b5203ca07400c2080803506100c3c1d258002da20741071001030058181031850b01c0c42400c642241e20b00034030b04103020f010060180360441c1040001c0202c000350a0b0300d80d04649442a2903400d4268660007045088100c06403a1001c0042c0d413042640000d05024104851250fa4064059484030036900c5c0100c11003230080c01e0f40414540e11030b00319440242c19070120103042c034402003800b4054940501440c080101064041e00c01400980816180419207034614035004044901c0c0504514404402401c222680700004050300d40180c0715000c8552140b45500010f03900b070740c0c10b501c0208104c1c11010441b00303807000b10200141c07000307195404010b181d503071b6a43d02e600c80c032003150800303d000340800d0240000341006000c655158040d24001540400f1007001c41e2031a07202120400c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 227566735 1250 227565485 227565497
    0x100509210403050c010207080a08090a090e010c0305010501021f050714030405060712090f1205130806060405060a080a03080907030b09062a072604030f0c0501020705010915030f0507 80
    0x10003880380800000140f003030207100424102d40340c00041a2150700505008014060004800d18280d4548156001030a482c1e44100590010311001ced078001c0240000e103502107410500005900e42c004a070841c1030555244060030190040702005000707010003010b042c2401036400e140500891150041c45c803441c49030000b0810f506000d90098041d0500c03100d840c40403410710310a00001101c052507031b0040c661041900c0c19118448030261400d0052503000015458900b80c0010f0429000a000b17004100550b0100555205c01051080d140f51501400e26641c0c40880e003c80080e106e050080d43c0204a4810f0742c5031a6200d9031070031070f00c0b001074a030001c0310790040c0c0601c10002e10300f10385608010501e40400d5481c0181016072001401090005010b0a03ea4403064240348010301010024007091901c160b95191240f400c40303202160141c3c20b55041500070f001040c00e5000040090980720141c540201030b5150905103441000411f0300e0100305911051940d03202210340c09030a008051030b407a80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 227567985 1250 227566735 227566739
    0xf150c0f0f12041212140c0703170c060c160203070905090d08040c060f0314010605030f01080309031e010b030109082d16020d080406080103170c1005092104 69
    0x19203030408001d0299107505080004016a000f40000740e5502a40072112000317840c000b0748141c48024144185c000c2c0b0040010320040031980102d51842030301e02c285440d4408503051005910703540120000c003003450780407201007202c50030039002a140c400160f541402c034061312540402d04107450b0350302c6980300644920a22800d20014413041b160181c65141c181c01e1460240c8525155802906c115000d000e9500c00340d101e2079100390055001d9050040304204c8950350340d40c004207154030464500984e00c1c141d10010542e107030040101c0f40f19580050082c40c0c1180150b129620040c44a0361702101590b0392704a112031038400b8000c440b03415005500d52520b4800c20840364101c080303010041c00b018000e121900b01318080003020ba07046811000d030b00d9004001c01d440460150a01c000000e41076890200b000610035600403416410382c0d118407151130304c40301c24180d000881d008600d4134040740c0d0401140f5607400046a403150b640031040c503048400b8420f00341a042482010032010121040b800101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 227569235 1250 227567985 227568013
    0x70809041109030a35090a0609060509040203180f0708010c03020a080f070c0506010f0302100503012105070b161407080a062a03020a0215060f150c0f 66
    0x1070780d48241441849a460428440002502c0d4140e09800500c02c0c40c0c501400d421030040030041d5202c401e8000b1110b500d13543e080342c008660f0303007160442c0381c800c04054074003040c10b500c10105e00307007100e02c940c4485062445d84400c100294100078036800e0300310001c10280000d8481080400030460b1404040c0910383d0a02072483d080d035010030154014580100606150075920142240d03114050a11091041e101d442c8215030144040402601500c240800030480104000412045901c00c42c1c900c0d084034031141c81a03400b0701092260524048030300c44000e4400c0c81c103194803c201c92085082c0d0b280207498154514076600100e409160015890700e04404110521002c0185040c020700103042c00c52500c0080c1d030395580c5016004100e1a290101c800001d030300703105242e034034a005c3ca108d00c2c022108040001d0094020503541e00c01841051401c880c1038030010702d068052603007d000d05800c0036a240510140c10000c079402091a102080b03048510001800380c0002d104484015000e542c3d60702070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 227570485 1250 227569235 227569241
    0xc0a061802100318030e0f090412020c04060605040509040516090209040506030c03070302210a0308040b0f010b040611190f1a06030312040609050607081b0306060a2307080904 77
    0x41c81003e040c034041d02c09071500c4006000d0046254580741c60404850201e000c541001c1d840900b25801c105003005101c10040c44140d1078507010346503402c68003209801c200f040290342d80c138402d003800f1032003c10050141e4101104000c1d4400c0c011000ca803441403080300c100880751065404400416404150070f842c1d40b0780b5004403500840d0843c0144925941d00001030385507151480002c0c17046c0c1080410460341074110380642000c0500d001a2844901d1a05010f0a00d00b0304070346c03c541c04256000040d5800004000340d40c1a0f601818a403400d060414a090b071b101c000304168200c40d0f01c00c41041c02da1148002c401803c400d072140301511060311032840d0039240c0218908104a0b4080841d0401506803000403d40c0e41d040000311040c61152a54181003000744500c0303401030010b00965041100c019000007006024a60083e1403c8410420b1000e03445640400d036040759020a0801c9440e1300e2500c244d2034036020082041400000d00001c2032440f45580c001d08046444c040c005c9003504580c60244 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 227571735 1250 227570485 227570509
    0xc0501020106141c020a03150903030b061603050d09080301091b0206070c0807060e0d0314070306060219050c09071701060507110907020f0307030503090c06040b030c0c0a061802 78
    0x1010403502603003441c0007403842c859882c540404500404141310a5550f41041c1400450300f001c3e001c0c0090f0f002810800c082c1400030400d4020a061660f25552810700740d0440f0100c0c01c0c20070381d00d166140c0a9400302e4030b6600070818201d065440c2c02d01130000c1120040107600030540e001e00015040c15944070f119509851407482c000f0754112404002580b0b070000803000c4000ea200001d0307541c0742c03520b14094000b45503100340c9031941e21581c155100c09540660001c11090b01f041c00c0c5411642c2c40003003c13019a025070040f00d0043e0401c410700c0b80b100c080440e18211144c490000e8030180307036000d0041901003000312440c0340042d080038050120b15a000003424090013880c60b01c0d624003001900c600c1c203e4401c15a0b650b005030f032000001130419100f03100801b8603000e0402901d688042c241001002c0ba08140d5040e41e0034040c1c6981380c0400c0c5044c40450701211810500c050640d40c403000f400701540c001107020f03441030040884000010f0105c1c07140c02d03105016000d000702030308070600500101140c07078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 227572985 1250 227571735 227571749
    0x80613230a02030403090b0307140d0c03060503030408070b070204021219060608060901260102040f0512070302010c1b0e042910150917030a0f050319090206160c0501020106 76
    0x10030900020a51004183d007d0f210340f6400560f0b6038640701412030301001c41c031075a082110f1012980000c050419004030101035240e42e414807881c0e40794410183c8a2140d4401d4955a038041c0a0070803032088500040d11203035000900040c10900d11120b21003902c84103d81f6811200000d202d0140f1002d210b03c51080641098644048a4503007503020403010700041c09100d24844001d03103101c400c0a00d0f003406100d0740302d03490300954840d99200d45040300c02c10b0502a051140c50403164450a610000030400d04484d0141d44442c40c15075161100a00c500e51001c2440e03403181004000301c3c01070700c0b2440d8a8011441032101a11021160752200d43c130301c83e40d407960382c00c9840002c184800740706460030100594441601c812007a1508000680710108264412680a40800182c0000c0f540100207052030b0901a20780503c03005194208842c9403104880221080d141444071302400426035111801451024180c0341c41c01e0104401205a5640040e0446070b0310b01c0034400b4012568207000701002090301e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 227574235 1250 227572985 227572987
    0x804060210021905071b090b131b0e13050115030c020d020709020c0709090606090c050a080c2b0510050a080a060c090b180418050a03080613230a02 65
    0xa10071000c204000e80290300100480170490038144205c21440340400e585030791044141503691040300e8042c0c07045034480e5200e80c4c0e034100b10b000511014000c8490b0803841c01095900c400f9602000d840048004ae0042d0304541403d45401002a445c8100e0303020f84410010240c000407403180040a944045001408642102d80d40c0c80001d070b0001031030419100089405a22152851092032915044e64400d003050750070150008180b12080c1c0c0403400703541100b03174144540c05180304156540d2240b209180002a03c0d10005071a640c1d00c01c0160000c043c10942c0000b0010031842490102141c84540440080e525420b0140581ea0b141096000f004156454014903180c140d94a84034015200c006c1c0040e0748425442c400d052107034a051020305150a0b06a071120f035000c802e4580c0c2d00120807101d00492418040d10020360300700044042030b662150040910402d01c2d036045614a0000e4070142c0c00c000b02c1c0304c0349c802e400d28078055503144114422001c0c01e1801c065a51101c1000090310720491684 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 227575485 1250 227574235 227574247
    0x140706020c061e0c121b0915130918110402040f14040c0e0d030305060f030304030b10081f020c0a080414040f0506031c12050a060503011b1211070b04080406021002 72
    0x5d240000254402c0414101d000e4103040c801c0004418415003e840760f00c01d4920032a11414504180030b811040760510744c695210380c80301d08400845012100c10013459500003904000104155101e0200800150000d0309040e92a94100701c2010b01e50000700c086010070101c1001405d051140f00074840003450100030561510b4040340120359014400b50070561140e00041a64030b4a88619100c004058116551103903a8100023101d807405858100c59507602104c000b820090009000010051901903e40c4205c407103490308000354031104070f00301a806030b6a0081d01041c801c501400003401a04200078000004c8000c01007284c00e10f00300781201074980401e010564900040c03c020320000704d1442042c62800d58070503a1041c02c2c5041e00c0249030305100c1080b5503c865504080f0403543e0a4000740801120040c5030700c415500100050005025584031401c10760030790f04a141c502e07070401c80051400449450780c2500c4002150251030001c4002810044150704012a090901e0260320850a003c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 227576735 1250 227575485 227575507
    0x30e0c0a1404021308060103140601080c091611010c0e01410409020f09041a09160c0206040e0121052109060304050120040303140706020c061e0c 64
    0x42422001ca50046602003500c40040700741e503403050003900d550400c45415603540c0c505610080e040483c20111030061500008031000c0001c0c0a0348171000042c40079440356200040303c1d0340e24602d0f00b001810002041101c035140c0c0703001c0c070840300f60b0342869030348101d290080e03400075061103050220f4143c10076030400c00e841507980d0300d41c1407802e031640b12005d400c0e200076400381d28001d8084c94200030700302d81c030014031314032014182d00c01440105070a9070180034004803640b8500302006035110064100b84540000381c5101404c504114600f100e904225107182000c1d00422400d03009a0002c100000e00d0707100502400e4800503c1805400c7e00102c0c0101480482d9a29925820481d5136071340ca041140035901841c00c1500284c3c0d412030301c007070011741c0c82c3d00d402d08005020345a51603900e49d83c62045c01e00015120001c81c200d905481c1c05072601704a446104010003000c1e404540281c451940c01d0089005038141400a1070082151045004541c0c1c003a00740c034800340758040d060950000d010041c5510503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 227577985 1250 227576735 227576759
    0xf0504030908070f260a150504020319020108040f02010315060c050609070819030905090a0911040e15040c050d05030307030606030c0f05090a170d0219110d03050403060c030e0c0a 79
    0x15030400001d05c40c50031824945546405035152004004181c88a14078004051a41c4003901c07540c0220308507490041c1101040840500c0038601038000307414000040c01145481108900c0140f0614001904035010f082d101140280794001000150b60000d049082c400300308040360b0401a45400b8208003454031030001d41e5942015191208904019110001d050240b09440010700b0050400d40241c5803ea00c1d00009224440e0200c510000c003204413001ca0503d4440c218134000c96000038008009120544400144002c0c011500c07801e212a0120301c5455001e07016240790b100700c000f07640328285008090103542c919082401014509000a550150b105041030134058490030b100d9681c18602c808110254082c3d00003c43d201d0800d203040c103490f0300004040318010b880c1d5080c1e039294111242c86903c44185944080e15003401800e41203000c5c500900840411440703801c00b00d1409640350b0f81d4a0680b0284540c200c0403a80e180358016405400303110809e1181d404a440c01c211038100b40107a131139 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 227579235 1250 227577985 227578019
    0x303220e130f0501060b03070f02101e0e0a02040903020a0b011d0708070c1b08070e010b12180f07031505040302060a0b010905090406150807140906040f0504030908070f 74
    0x402c03180801e0400c1880400c0d030180340a42601c50b03005a403854440320182c40746d0704181d09040140705520f804c000864861140f4071030002100500c01d40e8200036242c510103821059070f901c0c907a024400780c0c580169510303c82c0c40d0095100342c01801c000c1e200c50034011110081603204803181003088443c500c10703980628242d40c0c0144281400f10301500c4044044a02c1514070200801c00c025000060860303070500e0310103008440161086803945ca48400c0402c920070400c0c480c2c0d0084600603c41100080c8800780c5135980325188003a032410444100080d41e2415003054401e00060700181c1c0144140100b02d02250070a83c0c02c1c03007040c410742c20b01c0d0344c0c003e65401004004e106016965104400702d60301c00c1e50008001c2000034201440c034107050400d8030080031f0010900c0095289240001450000441c4078411108046d400c4070154000005111000d00b0045c07403180e0140d555280d0713800300c40007880307240e0246000b652400c502c5814100e04500d810a41e802c0160005988182040341c0100d581070804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 227580485 1250 227579235 227579243
    0xd0912060921030905060127090302150a06080105010603050c030708070905030d0201020c1902030a060203040f170c010c05040f061223040c0e160509030c0303220e13 73
    0x4031045507007850011030140700b20544194844038004082c0c2940b6800c8101154000c80c01e850a50340e13502290100d5032000c500080354200d54107221900100f01c0e920000800340a4010f80701100018036000b83c1e0024222820603d5070350360102803003600f800348a41409803400c0c0c10108035900b400c0c10401c03d68000205008200022a000500014460303120040100005800c0f900d0921550300044d01035007041d00106224441c00040c120000300010301d85038501d401802030b000104568840001a40c40140240c0e14a503111032060000760f03200390761242880320a41900d44910303034000314500351040034510a0801c002841701b0301c685002800428115800d03410890300c0c2441804910002d0800d54036080c0700f1042ea00600651111600521446544550480781001d620388401034540300c401d5842d00340301004000070080ca103000700c00524480100604503141290361100080c5544d00000448004024110050070030005080544000e00001c0f00e0006252805030986960011841c1c0050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 227581735 1250 227580485 227580491
    0xc290d0b031e07060806190b0d0b060a030603020f1807030903110d0e030d050301030302030a031d060108030414060c10180609050309100e1e0a0b0d0e0d091206 70
    0x6990100300c10907440030522035508880301c4140002d40c40307a006101d1328002c103040c0800102c2c2d518050409248000c0103410100300c2c2030030840c600c06142c01907007041a1a40d5105a0008259585806003002d00c0b510782e03011030003505610502c07456128038501c4900651400c0f01000d0035036181903165500c078100d860000303200c11040c14211602000c50100075441c0c0116212003420651004aa04100ba0158111080c441d009407084516101c02d1201800580040c402c4004261083d0056400803001c85c841c54290050116640d041200c00e0f48403a186900005040001e100900c01103015050100d5405040c03804000e4591b0303d900c244e003002010590341f0700c000824a0000d4907001d003590741080d010401e010942c40d10f150b40f0340c002901140f00d4000c2c0070740c10020901c10402d0f11040071000e001001c064004c0214007104d1000705000d02d40c024000800030070202c1e01e01c030180080030b0100e0400300d0201817407032815081c012100014000c010310a8818450300c0400e940c16000160700801c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 227582985 1250 227581735 227581751
    0x304050a111302030f0a0b0915152b06050307180c03060b12060915100f050d0c030b0a0801050106020d0806040902060a0c0b070e01021015090501030c290d 68
    0x150b074640300440d040e5200e8804020310104ca0404030845219000c00b002c1000440e07149000c10039007180443d41b00c91001c40c440c0f400c22040c2020600d1101e08020041703d02d0528018001d001c8540003079054a0082100481c40001c480102d40289801040d00381c01a201050600940c8007001580c11000404151202c0d000f40040d40700c4d034803050040101c000f51645421aa4010b007555250031740e0b03154480c04815000c1803c022001c6c0101f141c50368020000c01c0b043c01c460b00f007a100802411060018080203021180003140300c4c0c010680f400300c0a03900003071034009503803c1100c2d9251640094a2503031400c07006000f000e8001440060b00303c014208103107141c4d5201e00040c0541200702c00203403c108081014004030390020403d40c01244600440300195641290844044541000c980d0059002e2600707403c0368a1507510500b420202072502c5501aa210589407040d10b00a0b4002c032240c01213810100088c2c0d6400860b5103002d02a909501c0d600f010700d00140f02a40282c05c02c0041d115681c4030a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 227584235 1250 227582985 227582989
    0x50a050c1c020601030c05040b06250b3105030a05070c0f03060c0305090a12210606020c09010b0a080411120706110709020f1204050a08030412030c050304050a11 71
    0x101c0440c0720a076803007203a0014141000207484010a00c000c03900105a680b0106031481c07d130181001d00c600180c003190a00300b03001c10510710200081c500b8501039500040e01d101113070010f21040d2160780d400e0f800d1041000c0d4030300040304209800c5841f81a00164000003000110080201c03070700041945001602c45006090030280f1141e950711001c185031038840000104100e40e000700500841c5c5440820403070352184401921078400c05002009021020254058607000d03c41485824200e03054030a4001c405110403400c0780c8044c1c0100c001346e40065040096482c0070350a85002d440d1608080742041d0300d250010380800d03000383c0010a00004c841400001f511740c03080d80c21044c030241045500840c0d0f5000c01a02080c03040c03562000740d000700706011400064a008490901580d86102454846c10b81c40d100b5030701c50060000c581074010090044042421907024501031401280c44201006592038042c084800715480b41003803060a000304800306401244162400d600505030700c2c442280400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 227585485 1250 227584235 227584243
    0x91005040312052401030c0e1e090f0406051303090b070204020c030a0c1e030507020f040216050303060f040501080606040c09090612060b0a030206030c0c071502010e0c10050a050c 79
    0x10101c1c500345010104038030301328400ca10007800d030b03900c1e407502402a001070011400d40c2c02011144011034010b1407a00c2481c14125030b5119010b184c050981c1b025140d0800041c1004403e4840314500140300043c4000d20a840c4103298000001c0301380e40000c1512940c014009d240710303200c0d065100d10089506003e6445070b804848a0591541c2502c1e80c5e44d101071405416146180c1040c0d81c0a0440b000f00c034501d03598036200c0c141d41600741d1180780c281017540c0c1c2040010361030082e4190704190240124095503140754090070000b4441c0c4080d60f00c03841e129003800b841d00d280003511880380b81020300400c54403c0c00301c5d1694021405890200d01c400c1d4000054400c03441c558429100686003500001d1009038880b106403580e4460341083c4448c00c07840c01002140001400082d41c090420800310b0f0a03a420b0f0401004c60742d06180035601015541e489002d8458003d1072102c001d84d44070038031600541001e102070341c03040d44102c1d0703070341030014040c000144240a4004000184200000c202041c400100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 227586735 1250 227585485 227585507
    0x902180405030708030103030804050d030614090405010b03060906040b09280203071e0306060b0301080d12060503060c0309060901060305120904090210020d110f120304030e18011a030910050403 85
    0x9004d050f82c950b500e240c020980d4000712010380d480d0288504150a1620900841040742c2c86000c0c40d10010701c001c001c00c40c40150140080b00c1c25035980146070860b03141407014034410b40800002d840c580c41c03d81032810188a00030105070701a08810161034031104860400b41002d240050308000740e940c0c603c040381ca41259504803480d107000c4404090880c2c028035042a05503881260244401a500e04642340c02e40004c0c066000160800141240018454440810010b640740c20102da0f140c1d90780c0103e4208203050714604000707200001009200300040200701d801256071740080000900d16290385486840720b00e110380d1003620005403485142d96070340142000540080c9a010100845031010b035580040c8003e07140070424040503041c8908021070105480b00a403c098400d180714090355000d254030091040342880f081000780c0394203407103084a20a9003180500f1401043d414800b401141103120481010004802c1040011040020811142d202c001e0030340400d05890342e140607542c1c00044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 227587985 1250 227586735 227586743
    0x7060e04020d0509010e0d020c0a15020717030a0e030a0203060106031a0306010915060804120309030324050306010902071e02150f0703030507081e1506070b011809021804050307 78
    0xf100784240c50106501c1040018010821034083ea5140d040a07600c0e20060310141e0360002c114070041200141c0910410b0003003105105407136140e40ca6080182201d4440c04903001142d001254a00400382c2180d00c03051b40c81000c80041c49556203580c0000d98944050168001b0503031911101140e1400c103000f4010f403403400138140d4005684548290780108144001c03440008910b910000d091070141c40a40e0013541c11a05801e419680d640c0142e02411030401c040301090b560710000e001082e91052100038203051412a00e0310680341c0420185000c0042e0032042d90188104034000c00207035407021161840d114000748042c4034500e030002540c94054520307101c0c0c00500c00200c84e98420703100001080ca003403003500e080005803a80344048030307401e2080f100c2940c50304030300440804060014403c5540b10005120150310b001c1c915000c1381c0c00d0b8201c00c07002c94015403400d005000d031030540f800250400d01200001c004200e540d40001d10307134000e03a004682d080e02d40d01021a040c404140222980c413030300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 227589235 1250 227587985 227587991
    0xa080d12110d051009020c0a060c09030c030b06030601061103220911030a050106050a0c0303021b1c02100504020109150c0c140102010f15051002030903070b1903020c07060e04020d 79
    0x40d41ca81000034040845048800c03252411303010655107420701c2a51083d18400004001900003551030400070116090500e080c0040401c0000c006100180200040e5209580e1128a030030301c02c00b4907141485c1038000764248142c92407010044c103000010f44480c626a104600b0703180600c024016420440d6401583d0924100100540000c542070010b5008511034a0104082e0f03030307a0b99080320b441c02695170038400204420181d2010920035009000e1080390100044400d004c5203886a107004a240700030031000840c0179400100a80620401c4900c0003410418001490543d000900b80d450b540134040c072500e00300340340a0707002d03110b1100b00301407a60080b03185584039201e2140000240b04100c0003030056080105048190340103024403101400180101101d0700c8c00c010030444103640c40043d4108600c424271809825a90401c841e100504003049050382d06c01c481000e45421081021a08040c54010083c8804102e000954030003112414501504003641800016010780306c1d40d2825440c480c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 227590485 1250 227589235 227589247
    0x20307020d020f060906060d05100e0d020f0105040b040209091006081006091505060c010b060d200304050d031806021306020615060301052407050a110a080d1211 71
    0x1400007690280001c254084420082c25035070082c0e0790384003c03940c210b41600048081a564204142e860b8480740c0700c0c0d429030385000d0070460390b54200c81c004c20000c550ba610441e00a46555014440d296982d001100280418581030711030340b6180c440a0320003801003c484000440c4542c041c8134060000d001d600e01803001d190b41c2c0310a540d13100482e102c81206a4a404d0740003800c02140d11919007402c3c00391554071034003031038502007102d41d4104e8441d8840303035500d81c4020307074150b5240c1005080281e540384001884d2102c102410f01c0910003103e20382c584480420510010410014205400440b140b501103121301207840d070300c404008811002084680045641080d0306c41e10140b010554819070708607502640d565400242401c2c4695a4940192042005020505040002501c4038001c1e2849020401c03030803651b10034a0f817002c00c0030760701500240c50b034108000407603c43c1081e4003000c50701d90043c1400e1110203526440090004001e0216400740301d02d8014044d001a22040382802d0080e072114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 227591735 1250 227590485 227590487
    0xc0b010b0d051608060d02040b150705010b0402040303080c0c0a0b010602011d1629130905010518010509130b1e10030f08130f1d1302031f020c01020307 67
    0x180080681d1003141d802d0900284000c040da90100742011100e6480c148261561403c1c000001e10149042c1e0b0003548a00c10701c1800c1d168092448040ba00709030615603100344a06005084484000c405032107075004001c1000070952104d00c064000409420030b580c3d443c0c14100043c50b12180030401440441114000105942c0644c0b0100007107041407214403d421648450355240d1340c080c1c4001c068194106014000b0500802400c4071010440c00300c20381140c540529592180c0148400110b0313800404820b0018175024050b05004110a136211100000590b805800c103d0f01409402e00400740c00c0001450098940000516103070801960800b604140065034051610001d1800100e48181c0c08610000a0380e01010101e0360406142c01d0400c0040d99030054540c07145d034120382c58100d200004034201c0c103000020401092041c05400030000f040c1c410021480c0002c100c1d01404140021f81c00141c1c902113040300740c0802c0500700b0b10540000e801410300900400316003103ca98804000c001c10b07d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 227592985 1250 227591735 227591737
    0x1020705070b0c1b150c1f06060f0c02010801090b0325080c0306041a0702030d0e010b011b0c0501201501050109121a06040b0409050c0a150c02060306010c0b010b 71
    0x10210078040c2e034010404c4034001005503036900005038108512541c1002d0041003200604120450107003a90701802a040c0c0d41d03100c000c1000c00c01038217503548440400c00039403c61140184145c0b14141288201981d400190a0510500c140d5608940324000700c6c0440e0f1b8140402003142d100c0c0990014481a0000106000d04560142c03900c50710a0100301485441c002031102d00c80c0c3d900c2980c09202c401c0c0300b0404400000b0241a200c15488240304120028500e030043c00c0c100c5000100005003402200001030800c43ca040504a41d030300703035645110210700c090440324280c0d9000e0038800507840707a0000100070490200740c0c0e00d44031b0050300380079104440301c900781604840d401d1703031248000b036103c1d40342e041410840c2e01c004001d5480d400890b1400041111065408040107000158182b1311750046030548208900840d00c40c3c00483c0e01e9001441c0a072641c101030602100c03036401484030700d030004d40426001c0002a105400200010300140e10604180c039045901c40d0714ac52265135500e2070501c036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 227594235 1250 227592985 227592997
    0xe1003050a05060105040311240a120c030207030509010f050409061205010506060901021b0613090213150c0206090409060213080c0f09150307170a110604030512030901020705070b 79
    0x80794140300c0030549540c42803054800b07507900003d1140c41d00301d160081021188003840b25072a061020081d8000001d494405050080d20301d0b01c0c0c011010000800e600d0840d0945041002494411300c601c42c00300e540582910301d45142824038000490103c10f0513036040c05950f100c0c08005052600c0440d189180d40c06406903944030304003c1c0210b89459041000e180a01c41150f17005074454422010026140e40762624400b07030182000d454118100742088020941340c0001c1001500090300301502e0340c0d1944417100900d0380c2c5118004808100b81e008124140c901d10292041c1c0b004203080b03150740e40301d5001003269644014115a5074280100d11700b11300080e481462500e01030382d0005001c80c10720108621814100030003100446e40c501c1c032010030002e02c0c418015014810a4030205001580c0c00c0c006000e0b000f038000804050039035203040c0000c0360b40001c4041c000d01e000e200c00c0001840015001810030555403142d0f85030354070022000e00900680b64090710318402c0400005064030080300400d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 227595485 1250 227594235 227594251
    0x605120a0203010e0d1e09080109030305040515040201141e18091302030705041805060103110a06020708030d020304080f03040f1109090a0b10080f07091b1b030e100305 74
    0x860105611300440e03c40d80c0c010700c50700119859407050100c4442440b070b252160007460410502007516009080e00f110350701c92045020942d14014001441010030001042c02c458890b0580f40b4641755000074101450602c031518a2140070410341c9041102611030320891351500d18090f118a5061038110806418072504d600804118010800c000c00b00c866098059401074001c1040510785400c0c00010a6a40c0307030b2040d000194a00b402c00030340184802d0f030085020b4a1444001c0c101d15007044020303005a4844000d5501800081010130f0300402917489080400720016103a13074072400c14035807030710071244400c403c4800042000108111280344107605030040020032844086001030044240042e034100300103030301c000c00d11000200e0138042c56500c030315007440410340103a0390480c26240400c1d903042d80c91140c002040500400320701740b254088185000343e138031281a46c0c0010140130800c00c0c40f20380002d034500707180c2401858001c001803c0105009802040303203d100c1d004c0200102015540c0074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 227596735 1250 227595485 227595491
    0x305010503060405070e040c030b18070b091c03020312161d010219060e030711130207020a0605090625060c02070f1205150f0415090c060f030605120a020301 69
    0x318241c1400a100c0740f080d54004002d0500604040c052902464020b0007111142500c00020000070f07800412240501d130551316a40b0595099682d2070308180345a00440d160302000e01c0440070517590141041c070012403400103410b5202c55410100d00f14411000c0d040e110445c50024800407000c01d0a249184400c0c42e074421109030003086c02440c40ca1030082160380140e0040086030301c141c0c01c2120398240a4400c2c40d0002d00c0050001c0700c40e0071908001c07820344500b00c007202041c0003402e200c4162290308460303c9003149030118583c0045c0341010749005400800074007003a0340c001612014101d644a0a16204a40c2c2e044502c0081c025901d030030b100d04440c07141c200052081d4a03800050601c0070740d022290380004250a001e9400700c1c0c40d080b960280c41a100c1e521202c02242c1c108044280071710031480c007244491038141000010f2500c46600345849500e04140311002c25083e60090f0203403400c900e0a04648005e003801140a0000b035040558400500802960540000180ca46646201350000c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 227597985 1250 227596735 227596739
    0x70506010f0803031608060103060f23150403200a0e220b0705070317072003120402040b04140c042603040302150c0d08040c08010507020a0605060406081606030501 72
    0xb56100d001c1038030403000340c4085044040c091030190f01c01c030f07500039810b00d000604156140e401c81006110b560160300c50a104110000340320710741e401905510001034540d0448005d00440e5105288154800905107608820303070360001e2104885446120300300100f40c02220b60b2034102d0030b40326074003d03640015948009102114054184100c241c52141c101c6a8800c003562032400035a019449000100c0401c00380c003899039020000c881500d40a03044070740e142048006204100404003e64005415151740248034030705012003189502c1d076000f9030503100407850003940c030003080203051032401d1054001c0980c010000d03d4141000a0700c00c845140c1d00340305c0900d075411024031140b0010866009240c10800060003d070900341414091041e1080c4110316103100ba00c021800c1803010b510300400600d181040c0030510040f41d210300003900c7c01740000c01c030600700b404010f96200070b0800300901c20341d241d40000340150345540c0850001c040c40c9050364035429070302c41d004200c2c08080c041c080100b4502000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 227599235 1250 227597985 227597999
    0x1c200306060d03080c070c0311040b0303180103090807060905010f110a09030b0c040b0406020106030c051c030806130e03130602071d0c1c021c110715060902070506010f 74
    0xc0c0c03401010081c152140d8400c2c140c0341101c006600500410200504100d45d2002844410844000f54003441b1481c050f505c1c508104015142140d01e890302c40e80c0284414841d400390710040000c030342d50034240003e100c161450845210f00031440c0161800d0324008940041c054103401c0151900b940803010000781c4003100e80542640900c440710030001e1111002400021852020190007181001c0c032982001d0b1b580380550100e501a0700503a0060351550801c200f0031403804450400b03407004980a0400504603050714036041c2510304d000c0c0402c2000e80100d400e6440c0e03908c0800305c024070040c003440b01501da920b02e6503513548460385035140c60258501c00a000340c8003141035016940c45481c08901c1f00b03104200c000390003134060b10751807081400704000b01c0510242e42001840c401a86009071b109e20341c030f4035403280d442c6134800c4c00b16030310b0b0904001520182480044a1929500009881c0f1a0a1114001000302541e4001800c0c00344001002e1301803000c0060014122450103042e5204a5107a242e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 227600485 1250 227599235 227599243
    0x201060609080a290405150a02040b030601120608120909010e060306010b21010f090c020d05030105041523030601090207050c0603040204180b09011a0f0f1c2003 71
    0x440d0426681228000300f0018040e0b110129548030003025500c44540c00d04c00501e50007500b039400704c0701c50380b20500815111050200055100000b92400c5091a152044655452100920039810802c1e04058040903222540c0301c0800303400600206c60701d0700c030b48032035040d410381c414605284502503240001440501005c20203110f00c5000c0c000d44110b91a040303500300650040c14180c0380ca9241c607041c4e0a405a00201154000e0060890f4409403515040c0e54600329040c070058502150407a64081031181c2d0418101d90460740e0599000507000d10807881e4011201064004602e0110100b8601c0300380e40700304401d401402c0c41102511950790341d400078a1b0880c490b6400080490300800c820707140f54074012014580c810f0003d880401c0301e1001c822103103980c58001c00c040f140c0c0c2c2011020300484031800d11035144680b86c000c2c030714229030104c0c0c400140010441d103034a51060300c101070700d45426114903c0700b4030402801958841da0301040e107415012485480210807280d9004245000f01d494009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 227601735 1250 227600485 227600489
    0xf0603080403080a050c01020a030c08130c030b090a0b16090803030709030b061215070f03150e0a060e04050c01030b0604050d1524140d0201140a03110a030c0201060609 74
    0x510348034036140c61070395070300c0858000140039014040284070b0300f501c041d401c0c0020601881103980008002e6002240504151030107840118030080f811440d02c0040c28884c40c0405403034001c0e034898030035618016031605c2c005040c1801421140c101041c0940c95000094500c0680c0b2242c40f0407030159103910580755640401c8070f4201c00500c411108001007032100c0307072154115501508500f4130020f00c8649a207014058028440994034100401c854140d1040780d01545041c5450240041c036114040a0340a20040c000c04000705045000300303140c0442d981c01007008026401001d803152500b82045512441000c0c541400f05c1d04104106143d842c0040480f002d550005040c0b03d24540b5a481c0c8411070020120301c50101d50344c03696216036214078480c00c84002c8020011000405081240d4070107a100d0400b05076010364610000d0b0740040c0e82103c0c03c0c2c0c001c941e00400007521030348810340c00c40160170010344020402c280050030030055a4140c101c03400d00c03003594009019a0350b8480046074000c81038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 227602985 1250 227601735 227601743
    0xe07081c0f080106080613050103030804031119081303020d050708071d071d360403020a0201050c070b0706060306050603070b0a0e01030617060f0f06060a14070c0303120f0603 77
    0x8070050200301c5c010040c080c1c0080000e098820501c0a81c04072004444081e0025000710300da01d02040205648401c040c4120303c0003002501c5040e04031820b80500f03200f00d5000604914010401c070314403c6076201701c40c2c02190010090711250925041c50b07500c43d080380c05030380d038140654000810080c3c080942d0b044c960b86089640e071032076a01d50608851071290b00301d99040c43ea01040c070031140c0da5035200722502401141c91015969180c9102c015910900d148420000b8100b504200000700e032b00881c3d440046502803d00380e43c0e950005213420b05103680c6130000074502401040e40e609000795130784201d0035a03201b003004000c1d0761107481c101030395465144660443d0400c03c01c090740e0203e11465400000f4101030402040712921801e00c1c0220030800301250b80281c0c03040b410041100702114810b0f4000038402e2040c0240d042c2113010604c1c522802d018281400070300808107a090101c00100c4200d660440381080c0c1b0a078803880c00802001c0e00c25060200c060514139103049204152048408032680 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 227604235 1250 227602985 227602997
    0x406020a02060a030213061812050703032d050304120c0b0c130b0c0a170f030a0c05070b070c0201020705060f03042a090e070f081902040e07081c0f 65
    0x1c0e820440305500a40498080507003d0002c164100e128102d0704010301000d84070850740c20791956040c2c0000403103910100000311020035120106401203140c00c2031725054600318030f00b800d0380d0442481c94480040d203102800240d0f480e0301c80c66036224012f0342c0214400c0d003054a030745405010481d0b0726204a80c0140491050401044a0f0038440d00185024610784074182c01c00350396090802001d41005840b400d454000e40d01d030780c00700000ba8059000302e100c00803150b42080110004207640e0f01001305103001c039a5864907140c042034042d10545070502e510000030380043c5002c6000800800030417500301d0151044010115075480c00c1c006441d113480d008110f160540e03499440307160342001079507a440f010302c1c0c0c6000e405103454204801c0c200074094643c0080f549260801100e45090a103a00078030108149480c00d0162100200b008007440904401800c0305000c0d40c00040d00502055803a242107124103040002d10040c0801d2800c13094200f9100c085118a0768502a28508204014480040c41c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 227605485 1250 227604235 227604253
    0x90601020619061a1903060e070e010207090f0b0a0b211308040e040308010603020f070f11060c0c1e101103040302220e010603021c1403030a0603021203040602 70
    0x71550781035050480c10716034041422641e400180d13400000b11301c80b94090b940b002030b134034541c1c05058904403021380c000e180030401e00c2d140034260000349402601503000c02108402030581a8402c000300005442c050b03900f004003100c254501001000100410741c006c040008001450308000d4083d14944d00e400f2242003280e00941da003100d402c18006065104c40c10328000450085040311001c0c1016200b042860380c1c0b14102414050312400c0140d0080d401c05004002605c00066075605075162503500041c4801d102c03041d46014804000c03400c0c00c5c00d4201c0301c041400c040d01c1e00005140e24615409031001504220b181784004039424601320074940040b481c48042d000e041c401e070400520601100c0c2503c2c1820740b01d0f4001010031421140d41013480012419606a900c003a00c210610324030b40070000c000c0d851652740410100c0321288404441c420103082c0c0341d402e2181c14842c012488034050141c0350b4920700100e210005201501090340140829265100c1059000041750241c0304150002c00d5592 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 227606735 1250 227605485 227605501
    0x70606180b01080105130e01020408060f06120c030a06020a17090c0a050406030b151309030c060b01020303070206180c0a0305210c03041a09090a0b010f0f0801151e02030a0801050906010206 83
    0x3090306007c101c6598200070000f03000b20207000260003807242403001211824400d041050b0203011440c100d915030050812109a0f66002a010b42400d601c0200962181d200013020740c1d0718902c00f07000140c030360f41c0c0383c003040303480b40d404a0b010780d82c04800c4403410b40e07003030300d46080c40f0448409000c0100550410808903568000e42c1d9440403411000410224800448420500c20303180000021000700e40310702c6030340c0700708040e90182c112a24020302c011811468001d030003e59510014019152802d04010407401c4400188080844140f01501503030716075940f0f02e0400c0c3d44040f5501022103144902c01c0700000340c80c2c3c1d14200c0300f0380d0140030002c600341420b000c2c4c3d004442808503042803881101f002210903988580d05030f80d114205014000504205101c00075242c0e4006500701002c0048607000c4d0619550410225030651b90547c0d03480c4e80500840f40260784546802180185122240080e9081d80b98000700030f040440099440c0b58503641d80d0010b0004200d829504140540c00000008420f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 227607985 1250 227606735 227606741
    0x601080f1b06160203030412020a0e0c07060e010e070803030a0501060e010210050a020403060f050907060318030305040206040b070c060f0212030c0706060f090c140c06010e0903070606180b0108010513 88
    0x1180380b9200e5040040b0b944d50020345180e0240e406000d0020315000a202586012041140100140ba0b2692201d143c5481d8500e40d038032942000601c26079852092090000095000ca4401052031007100c0a042d1101e001c165240c000311902d0241c0d904200000c184a845009078008088060b0014041c0e5541c18800e10080e00000303010072191035081c000000414041d01541ca00185407a5001070340382403c80103182402c2841d00300105050402140300104010040c90b405e0840d050300e0001003a4a0303034400120540705035808503105090108084043c004040a5582200d01a031116030076407a030260281c0e02d50003807c001c0c000451003032002500035420301e0010200e6a2084400007040ca8542800d840c590704141c001c200081e80da50060f00b48641c0041c1e000300b40090102c051410710000c03c58840d541c400500880b2807184000300401c3c4450410800d45451652001c0305100680d00cae42413003002c16810a51080d51039080184c000802d50191803554160792020b030036140d01410207180c14000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 227609235 1250 227607985 227607997
    0x30706210908040302010e040903080a0b0d120801050a120c180216030e030d0309020d0320060708060a06080910050c07020301150504060f0b0415120e0601080f1b06 72
    0x3425020422003400a500380c400c9215032442050308603103480c11800018402d91203074030b01034041c0d45440e42c5400401e820260043d80004e000201182d50100b6501140c20b030044110024445000540c440b107a868001c01341c80d041e24010340d900002d00f40c0c1c0340034000c841c5807205806080325954000500008580c02c00041c8031004881015240c41d92281c00c0800d400e101c41e1050b40050819410300d0f17801e250038080c0042d07803461480e05010300a0540c0004100034681c000041c248010341048011326980480311818110081c41954290310300b0203000b070003000c4104c81d09442108081c001154480c010b030990b0b8017915945000700070280c1c00c6400b401c014140a00743d4403292405100e1100142c4d0240562001844c0008020b40c0d030352724210a010135240c194200801e413640c1540217000740c00f007081c1990120f41070800c130039184100352003042e14605001d402c04232101d802e1881c031000d40c0b130001880d54100d0303903003104850b600704200b40070076101c4100c0c07007400c201c80303600207a014110f240c0034000e400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 227610485 1250 227609235 227609267
    0x60c030a0b2206031103010605031c02071208030906180c0d03020f010c09050a0503030405010f0e130f1d060717100e0106110c09060f0607050111040602010b0f040605030706 76
    0xa50714602c0324824109590780054035040b40c03103880038410401030310342d610000f20058000b0701c01641003100007900d81c004082c0703200e100c03080803040c80785591082203c5001040c10f250190100c034003e00341100c85a00c125144056807144401003402454003d006952030180500074120090001d0100040d8000c521419811440394008002c441c010038441d5080801303041d1128001c035031915042c422000e181c1d074429403094009000410450740c200324995070580552600b0b05040c1c0c3c0d0000010360146a4400d0021424506410030580d41d005900020308003111444c03601c4140540213803555949401c80c0c0d00400500c81d00080c22469080c100020f80203a01c0b100401074072030b01d60442d000d903003c0c240e200100080741034101318000201402807603003240d0141e8a200540c64020701055104000001c40e40c040d510009a070341c1440001c1d802201080b0000d4156660340c0d9960b18001e000c0c06940c251140304031005d154072441840c05100f12030031550081d0141500914103007003a2114944261914 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 227611735 1250 227610485 227610499
    0x60e06070606080318091006021c0221070b0a0b0609040c050f1908070f020606090402030309030f010f0f140402100c0605010b1b0c091b09090a0f0509060c030a0b 71
    0x442c1050f0184045c0c07011a4403a5000300c10790003480100941d405028007512624041103205109965002c00d0a1801c950745e011444600e540c00b1008918001c0418401c040120788001007402e005902c1c0c0091034040e00569400340d00c0d8851542000440f12003000c1c50794428401c200394076090919400041011944d42410341c207046010707000002c80e03401480c415104440c4210790800d2a90130018280d0003001d1450100000764804c04003943c1c99002030640c40c8034520000000d001c65904208450003148003806544650700e50380b0300c0a0191075895a00303a24103080c4581810400b00d1841007600d140c1180c0c0c0c203890161940d03000d00211103481a5031204110070b451002006c80c1c114081d140c024208451040d9172042c4042c4042c4071a01d0300000b1003050340000718450703010390f2240e051981041083d00340034906482a09452064444d41d0301c0242c000000300304000d14104154400c541d0700f0b403d540e0600c0b0565030840b10a403503020848444080c0c038424808160420100c1c1c0c0900c228000c00b500701 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 227612985 1250 227611735 227611739
    0x30b0d08031302010201110f0706110c0a030315171002071e08040e06040504020d110619050c01110a020318031005010905181f0207080f040b0c120301060e06070606 72
    0x31690350741c012621500904031140c4400304550b42403103161844042c51450904226040400452500c01d0000180c02171b40c40e102d405128141581c200c604400100040740c0d03940c0030901d0050040c001c1c1c034021480e500502400040c1603941101400311801245014004024403aa03020000f500241415507180020a10580c0b2400c2e8040308407940502401e055600d9600c1d0101600400a000b40f401c0c0c01241880c06000058440035000f88540d039101d14000000b29140c030204205010752200c001e1592590328149520a0300000203201520f548402404030030a540031a59041c0b16690303180b4010307401040150050034020030070a00400c0020141c40c054084124440240c1d0401c1e00041401035035001407100801403006103005400e00c0c5405401c003404022284001c1d4102d0b20741450032690002000402c000d203480403505550003c0c61500d48550702c2d100492100c4c2c0080301581003601c10780c4d040d015810341c0e00c400d0341c0c100c0e102951101184850142444501d800001c003c60b9065111840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 227614235 1250 227612985 227612993
    0x714070308070b010f05010c0c15030e0102031003140307082208010911041505130b0609040603030206010e0903030c030115110703110a170c040c020a050d03021207030c020d030b0d 79
    0x1401a28010f054074211035060010410388003070306501c00c03418414401035481c00039401840309821581240f83c100d540b0000c0b0720054001e040302d064080c00651000042001001c80c2241d82001d40340100c0b04101d00d40500ca142c0c81d5a442087d0015080400034080b40d003039440065541d0814000e076202442d400d81c0c0d02c091560949004c0b03601101c100c1808490410b0a08003840386e1608007180301c150607012890318010441d6481ca101115410380d4481406e070095407115412103404800140c001c001d001e0352800c0003501d40c03000303008007180c103480704002c124240e0001003174038000d420089041d0b1441e40380c8100130403032040211074030b8180454490058221038080c004140114020b00b0f00d00e4044041404002d41030b03c181d000240000940d0311100e02c2070038001070f407601c111070585000820b000140401d030b140c0590080020064491a000040981c0d4541c02034a0b2424a800d03c0c00b0f05034541e10000d8094840b03014200340140c0c028410390001601c2500800c000b0074000d020410700c01d486440d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 227615485 1250 227614235 227614237
    0x9020a0e010311042c04150f090b1609081209090601020304030302060f04020406030816020103110f0d0b060c1f060e0402061c0e0d030e0709090c17340f0b0714070308 73
    0xc0c082e00d403110003d47c030845d002054000c11803107046801c4100306062040c0c0d10760304201c4000d00214070710400780080c11601406280e800024000c0e403800c0b100c80600b100c5541000d40d000011483c0030742200c00118070705500000949041d03a03032540241005a4950181100d91040140166481170712240004040307514a801841804102101001c642c0700500000d01940c20007a10366040f0f8004020340c140c204e07051000c1da04000d4242c000815950f035281d001465600580311944c45600454080000442007001c0380c4036024100c4205102160751000d50b40c0510004450280d0007140c100100076000385594006804003243d5080007805650071300300701c0d142100d034020322008a40c1c4d0b010b0011201d441041100700a03e2150f1092105d4001952030012040303152003138500d0004032140e200d220010504c294800115120792110981001d0404894070360a40f039514a4180340c0048e01095054104401c04c040e2092424860f140210700c3d5698144040001440d00e43c90040e014044000323000700c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 227616735 1250 227615485 227615491
    0xc070f1e03110d30050a02120d062c010f051305091c020a0507090507050a0c0c0506070303140f041716020a030c0f060306080d050c010b04050109020a0e010311042c 72
    0x90701c00c0c184c9580c02d42c1480c240300c002880f90414800c00313004840000768001180d0300e241100e881c1543c0c0340d00390015550080c18158000d000100103031071041d074406035100c03a0000c43c07003411001040c0c40d90740d9000721301011655001307035078000c1d4680380c220628550700d0b0042c035040a0303040101d40039070100344040c16031841020140300045e00a5440c40003031100420105000d012245020400da00701014013038801e00c5a001c4960901281c0101001030166000c0c5100061401905030355503800c0c00c0c80c000340100080246414000a10404515195400e14079544079070b81c45070000100501c1c1d50703d054120341243d00c2011401d180c1e001c1010068450a440800451040012064450500c44d80d400101d007a42c11480415180c50000c126070003001908028006503824010750b50340000304014050320040c1c480c20340150401000107001d110310350060054020a41c0c0322881d51b018400110241c61110040200510090105001a040d00481601c0260113101914100c00002200c001c81c04070807 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 227617985 1250 227616735 227616773
    0xd110714010c06062304060f030b0603030403080a09030213050720010e10020d0606020d020c13330b0a1403071b0501090308130308070e0a0b0c070f1e03110d 69
    0x10814020341c44151503501d05d1450221818080203052140d214814042c030711020f00358031f07010004180943c4052007104d01440d00009000d03903418550102a0003180188022801101222950346541905101d0580904140d50740c100400b402200c0740741101c2004032020607155600e641d010780c00e01017000305c29480668a000581c440c20350205e00411520140e10034410341d08460b2a41920541c086000f4a071000d081740c2c0680b070101c0440401004004040001c00035040628400d40a80f4141c40f940324035442282c61080038940302c03600c0344014040d688038540840e19440740215001c0d0140e0186030300031354070b01d03000c104503011203402403900307000c1350301690310f65561504a018194024400f982c040742d040c0151010f603c0e00d42d0024090390b8014284010040765040c10f07111640c507200a50000d0004403c0070f6142c00e11640381d187c465a992060310300501038182c001a020700058803440054490f4846d4102586c55238692408a845030720405600009446c80e40e03002400c0d0b041c03441c00500107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 227619235 1250 227617985 227618009
    0x21507030c0c08031c11072411090609121603080d06050d030e09040c0302132702060a120b0918011404080307031107060c030e0d110714010c0606 64
    0x301d0b0420762540c040782c0d000b55450380c208108080e110210710488414003420040000f4080c0080400c42209000360030008000003004013070070003240c03060460300c242c0300765020b000c024201480c000e40907180f1510544640164041c03008503501d02d000c10700688024111b0068331b410400c04000158030407081c0c3c00480784900041a0942803102d644141000b0b02020342d03041c062203156407006040c0c085030719030f06485248100d0005040000c1342600000555002d0400078075500e0203101c2501400746650115080802520108040014203129000e140d8016059518190004c0c0f001ca54030080342e1010000181c9500c21081c40f6280c003103015121708011074002040d01d200c004481e09448260058114080d03030942030101003003030041242d80114050500003102030b20742d800c0c442c0070b009036072014240c10b180610303102e82c0681503000709640e8150641900c0041c14242c1042da0440c02a0240d0100340d8031441e418849000c45080e00020194141030224030044039a0b03940e001c0d5003c82c0c01644603071003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 227620485 1250 227619235 227619257
    0x115050c0a060f1508060c0f03060d061e0f0917130e01090f0506102709050a0504020907090f0e0601090b0c0a02030d0306030b13080c07030b0708010f06051602150703 73
    0xb05203140078001e1703c00413015220720300380b040101150303000f0307002e80110a0f1000008502203a481300860200e0651100c0c0c2800700115620f9040d0000c0086184945100e0030300048403040758051042c110103d07401240c4942c11040c0500314070013600b00071911440c00e420203902140d81ca4030752207024020203211202103482050390000354240c5002600007070080c1100b1420b0380519400180c20014100e108440c455070044224083c40300a02a6015981d407a01d880b050010000440d00036038810341c02905c400303000351650742d412030b00004248a80350107120b403c1001c0c401c11405904198000c0d80c1490901d460544071803003c62690b2144440300c1481d070111000320110700301403200d04a043c8003810100041ea02d952070b40098031100404451988c58090708503c2040318420035034003040c54101c2120380b969144d2401e460440003d807009030101d000c2000015a040711f040c01c20003594895038400c5e050545142d4000b0b00b8075000c1b401240d100c3c0707500d2201440702c2d000c100548a4140690f0391000b6510b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 227621735 1250 227620485 227620511
    0x2070819050427110301050913060b100507111512070201060509131203050907050d060f11030a060e040f030818010e0d03110a020a022e03020901030f050115050c0a060f 74
    0x42c0c0300b5144222400c0007170004109540c2c03806000e550080540c480e14016145618006004107144d00c08035134441d6001841e41c0044e80d104e0064414075104400c9403030b00007403081c100700c0b503655813420300680001304104002c48480350240036500501a400007046080d122000160038a100301c0744035090b224140284400d00c0109807010b840241c05080420250500010840c0c41d40e086000b280c1c00f420030444020304100243d4844400c51054200801811326030409c203078a0751340103480d8503101d9403c0020200d80c5c07450f19000240030310703401548088210400e90301590b0219009000c010100d01c80e848644c03040c0300030b0003017106503c12030016100c012107145020302155004054590b009406100400d05213070001115414650100ca0b04000404e40d4032280440c0044140b96050000c040c40c0421b81c51a0140c0280031118000d03207040c003c01806140900403540244507030095a00108138103900c02c0c0c003d01c0200303007078101c00007981c5014a030ac0d110001503428840d9001300d001d688015001002d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 227622985 1250 227621735 227621741
    0x1107080910090509070f0e09130212070e04060504062d060f0e010b130312080a05070e030607030b0d1b03120212040b0a030905010510090b0402070819050427 69
    0x3a041400d1001d640b60400d4049804080000c280409101d01c000c5d001e8100d074010060008003c00042401401d45060807100d100b02c0c1880034200d020310384c100300001d01c002c408a0138000341c6041048803100b07a40d07503031a4003010b4100a842aa00540c5da02100c4411010b00c011884861441d8054151030740404010312080b01d916038405100781d180380780b0500200f1000100241101c1d049100c90341c41d9403d0045000401d4440e030300003014081814032100c0415080680c0f01e00c1000540030401c01d5564407042a2001300080041c8ca03410341202001562860107030303001a007001c8000c0c003a078491441e542e99100d07074003007d8000d405050488290820400400b1128080c83c0d00300c40c8080c0c0801080783c50b908860340a00d0154540000003c150060b0440c4294800c580040c1c020000748854104082d0443e0000c0050082442050a042c103800c0c1d241010300031940790340d50205419162109410741202080c0c800507000c0e040140030000010302d000700a102d0703115001000113602103102810408412 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 227624235 1250 227622985 227623009
    0x170709050a080a03051b0f15102301080c0904090c03051e0604110d06020d050703060902090102030d11280e0f0904021017010b180a03020901061211070809 68
    0x35503110f8421100002d0b0301c4815039481c101b840b98600e00d03034040540350604040060000c4074643c0b0458000f00c4c01161070707134110f50040651441c0d89203219255203010341c80301c0701e801c1e100382c0b07403402c01807411665442580b40c181d10056290f850b80c10f202d00b00d4005408e9603125081921940d10f100028403d001c0c0500c4404103801c107032081c1070002c8008910143e00c61500034406419101c0d00248541d55880714003803440115031041045607158104003002c801413405030b8840c8006450040c0120340405944211005a58142c0056003480d5011100c4009171080b15070105840a0074008060000c040e0a900250403448240400c3d90a00c8280014003000754504070610900c1074a901602685a0105c0950000e0301620302c11401c8011660594020b41c410139022041e4000c00000507444015501810201c84600342100c178410600701041540b04803800041d40c48060b44004000450060302c0301c511014110101040f00c1c4000414641580c218500c01e0f501804001520b61440c80c20380d0007400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 227625485 1250 227624235 227624249
    0xe031009210f200c10091e0f1206020708070309090b01020609120d06080d020109020306340c0c030b060109060215010e040f0c060302030601030608030304030c08030604020405090112060e03120c0a170709050a 91
    0x400e850103807400d0914988c0d10440380301c0404140050b0911102d60102c031141904203ca01d40c0d2054a40780c014034101d0f0920442140c1c0c0c0c0381400f00c03410340d0b1011900d140900b10700d80003803100d034421459090213a4484203448814036919400054140d10501c000c0c540b1000e10340001800300c101d40181401e1280c0180000040b203000984807828600e20543e4090865010f101442c002c0b21007030b000c4d40d03c035442640142c0703132203500b030f4000042040c030170002d0b4805c1500f03a984400c140e130b030741c042a80e640407090300301e05079400c02c2e10042c07022071000f400440d80309000c0c50110010428540781e00901407616000100041d400000300a01c80d40c05d4010000180303d401c000750700d540707410f0310000d00c0c0c02c1458000404244d00000461fa10b0382e0707540c040c0d0b4098800208009201d5a584100040c6414403101c1195030078180b180081ca0410007200352900c130411000075407103903520900814002e034024010340090001c040c05140619100d15040c0d0310828054403060f130518140010840c2c00720300c50b40229 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 227626735 1250 227625485 227625539
    0xf0a20090112171233030a0b07090b030906090c1509040f11040906081e150903070804060e030c03030c0d0e031009210f200c1009 57
    0xc080804500c6040581c1042e040801c40f0054041c0c1c207858400c8a0158141c1d407038000601011081c4496004584440305800c1250240740402c402d1410502c1889960315400c6a240d01d0045020114035650102c000d01d8001000e94903400882c4a41e00141c0d003c0c0416440101001903110041142c5020500c007107444400040b408045580c9510400c072400f070041d502c0c1c001c0440b80403d0313a0003402c1e40318883c01e0800c2d01c40b40c0340c4221500510051185070271610550508140c03000380c1ca55002c1d8680741040c041c064000c10800a0a6600409400e030503252104000c80404a141d106c0603201412465803420880403640c000c0510b840c18150384035100303410821003400d02001c0040c95030300d0700c4102c1c207004c113400200e40700081c2892481202002c2660400300f01c04104603140700c5442c0c071043d48041981c06824542c80490340b0703074504030600c008240048108500b96003400039a02c2e04c000e50a084680c080503100105010000303400d03030740d408925a242e05105142410000e40c082020100400c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 227627985 1250 227626735 227626739
    0x30d0c021603030f11031c050a0501240e032406030d08070f020a020406031109090a080409111b0313140310020903250e16120b01020f0a200901 63
    0x38901c034080b44001414031a0014110b03000a0048409041c03041741481540d40b201c40070602e105a481c43d01203c0003484d40317410002002d441d000e11038241660103803032041590700b00b50f14045000000d18503060080c002840c2081440c0c1c0d404200304030810356800142d5a120a0080c081c52000c00701803d824800d0704000340e40d9180c6a80011480d5006469103840900090540420307030030302d01c1c00345010750850f080c00340103c1030100089a0000c04142640c01c070315140d13206210107841300a00720004004010030002006a12516045080c04e51040c03403119150444880b1041201c2c5c4602d0b004009035000450b80c00843d60141e441c0304010820041050b1800c2c42000019403101d11613858815445d9020800e14920f0303c1c100300740d0309013400080402003604d10040f04042c00000341c0c4111220070b031051001902240140d4000381400c14903441d00d2442c96103c0b10a0400307098440c41c014114403880600b004112070070050f01c0780990003555500540000c02c0d0701c1c000313000d6032240b0080c0514608401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 227629235 1250 227627985 227628013
    0x609020315041805011d0d09031a1e09060f150a0b0a05040b0a02011506210506030f031803010c080c0301090203041703150a05030c0f040902040204090905030d0c02 72
    0x7081e01c200112000502d1500d44214103052100b0820090b14035071030103104481e01d84840310b40c42d10081e019002c40c1d00b030802c0070004032215403041c040100182d41e50082c80d9042109118040d40001624078014040001a6905c1c00e06010403280001c07280d00c41c10500280110111150f40c01c20b40e40d15001c100000c01401084a04055100b0a2800100040d05044a03403062007a1000b410940354083c2e69180b101d1f1000340645002510000d808020010000d20702e800398000c901075000c20004440300740c0901c0d0781c40004140c01002203801d4000e8480501e02e142081c0018000510f09400b11600868070009142c212032565401005010000c130500c05c2e05241401904d044809051000d03a4940c1d80340b80c85183e00c954111000003441d0080184a01a48180864041c07030000381c4032201891307a1071040541e550b0040380b1060300038030708290f140b4071418943c000014503800a040946090f555004503011604012416600d6804c00f20343d184100244d03004aa01440c07080c40208840350720146 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 227630485 1250 227629235 227629261
    0x203240303090904020f03030c160e15120a1407060306090204061b0309150e09150f06090d0b01090603051203010501140a021c08010911040b09010f090906080102070606090203 77
    0x1503e1003406582c00003811075171501091042080c02400f46c0c1d45540c4844040c070360340c84d2410740d0340030410040c16002c175600d440c8031a01440f80c10300d049444c0e0100c03007010a000c244110705031030709400e008841c0024041440c030211040792503e090010003556280c8440181100c10a82200e00c1e4140100030070003099034000c004030311590020101c140c43d04c2d440c1c58155503240003a480000208c0c0b412a03c2176a55400042650040000303a03040380c400d555420480003c012031070071079603100341d203003010b105a1304000001d006004406410b0b0000c4140c9900c450844c00000d030301c405030498440d0700034010814288031400441009044290541d410907002808558080070b05040444020441b900b86034801c00540c1a65030000105640d400000e040c01401040309006d0b0641043c24043d0790100c0c82d141c03004450031516100802e5040c084c40000450ba03920659404204000101d04003082c2c21840340304c2d000050668070001a600e0050b0724081007070ba100da500c80d030039652041c4208050384031098 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 227631735 1250 227630485 227630497
    0x304030c0915090f090b07020312010b0c100509030717040f05061c0216050d0f0504030813170705100804150506060f0c01020403022e08091903030203240303 69
    0x1000126a00700342c040e40481c1120198081c22400b0b00f050608030002806a00c0a204140190b2402c1034945d034070711060b070f924424003903002d446844183c0100864200d01c0d0182c040f0200c46001e50307600c64032882c24901541ca0555051180e5040002c0d41001c00c030030303245132039030b420ba83d4202c050600c0e180490241e60403126115050181800080700081300240030204030040d44214011911203d5850440107007009074081150644210300e400f15a03917010386009440484140c1da0f80d46000d0a640d01c10a06803c8400c1c0b503100c488001f60040381e180c00c0700c5011060303594018010589545404c01708020407402203031140a000c1c044007400042511044580789180d80d902006c5800e4590802013081c5d442502c1c1c440105400c0810720512000064006004590007201c0381240c0b280020b401c01c50040c00c0030403000d41c6a41003101650054040c2c104558490000b10568022000140d000d803d00a4900c4c01280003a074000100f20407004103403042d004680d05914880022511440801c2d0703248106 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 227632985 1250 227631735 227631749
    0x1110303070c030306170a03030b0a0f0b090a0f0e160f091e0b0f18180f04051c261014151603080a0911012601030803090d020304030c 59
    0x42c0c41104240b6001c1c0e040b01d00101b1791000300303124040d80082031940307940c21004200c00203800d04841e80d884e403520fa1410f0040e40c00e1210720602492038451510090303809200c5998201528240000d1654411080c10307005000c0c2c01407120347c0d840c20304c848003c403060941a0805010f00000c04600d03440d4401490000d40d0041d504020f0b0390510005180d001042a17407042446250000c1c2c2204550225070282803074490a12080116400407170410414078040f134149090006c0c12400900e40c1242204600d4000c1d00400550303468400c90500c51804a640792030340808100c410400450202e5590030310545205c03440411003d90414a07204048a5600e11400310100300d084031000150350303010b444c4000025050b0143c1e9841c03801580101c180d024041054020480141c00074100c80f846010300910381c1da0240101c1c1881c1d5601300192081a82505514031302030a20081e80d010304100d41505003c0c0d4060fa0489469141c03060f2800d1074038a61a11050442d08203000c2007002030203074200d0205032001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 227634235 1250 227632985 227632997
    0x321020a030522061107050a0305060c032d040c062d12060305100c05040b0702060304140607030516020d0903060222060e01021b030616120c020f07050111030307 71
    0x81c10701c3d07a450303031401484802c1441142c9000000d00d40d0700901045071000003c003c0e5442c0640e40d50421180003558030025265401080004681c030207400300840d4800303007224000c905045105106210b01e18808407800d81000440c0038001440122402e19006000f07500c2d000c0324002409032540f0019040c0c580003000705031008011441c0314002e940749910400c0661027080001d550703050080c2e80d00d0034402404141c03032400c80c0200300980310f002120281c03980c06880303500e020410340c28085c4950000740180d980e64600903512110540911003140500344664010400d401c2a26003407003242c0c004440d02d8195072144039182000b075001480c0030120382c1c00c844016101d050f200b03210079034901c41e074107442c98140103104082044d51704101c60304115202039007111248814000f19900c2d06100703804aa5142c0d00c80d000240440280c00030900c0305249a142200d61030f0b026402a40c150350f036030f000c0031026070400307000040c06032410080c4030010442441d100301100b001440751a16484003900319000c0142c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 227635485 1250 227634235 227634247
    0x5040309051219140d05031b0a0c0f02010302040b030705090a140f04090219080d0206090304060c02090712020c0106051302070f170c07030c0e131523100321020a0305 73
    0x18040ca03001e0b4601c1013040c02d603014244517a100034000d5204561180600716946049080c105412003a1100c8042036156000301c20029151002d802e40310303203003c07410190200700104400103c500554050360b01030700c5c1c0c1c1d83c40da400f9000300005910541c1003403580b81c0c4400d000c0011655040c6103040c002c1d509071000076941e0300381e002003407000345906401c110000c92404001090540001c08020101e059402c6e52415140d822000c1d4881c4103902c42c500c0012607103034840016150501c07140e0b1704900b107400c1c035458080c907000305401607811a25810490381d5541c24100070741e0400003e034102c04030511000f146040344990700c00d0302c5014a104060b224805050785c003521181200c04031030280c0c094004445401c5c0d900e240459041d25a03000340181c0040c520041150f4a010460750001503900c2087e00081c99800441d01c40203100200c07603002c03081c054880c42080c9032400c119044c013400e02032000010b4541181045650841c10070903c02110340b80e618520080742c0d01140d1404050f81c10320700340760303109 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 227636735 1250 227635485 227635493
    0xf1d040f020f04030b06030f010506131e05040c060e01022116080c0105010303110606010801230d051014220320070e01090c02100e0f0a050105040309051219 69
    0x801012410348089800140200a2141038000b1521855048041354074408489002072700780c4009603000c940003460542109400c030647e400030202500414017220500030a074060388180c1c0d00640301a601c50085180078030220307901140c881c1203184280000c20503030b01c803030038003078084803240f22040074850740419400d80c0b0401d0003220601c0b0a4010900580f9064030b0070206000704020300c4107e002c2003211000da848500c0102ea1315204000507110074125a2802c41407840421440402c40c5010348041101d0342d483e6240b46100840b02d00600080400020080c002012180046500225032200408202c1850b6079241d01b98501c00b003050000c403440354940341c10341c1c0854030101401900c00440e510503001803000a114402c0310001c0307501c1101e42c2da80c0e8405004840c130616550006030401590140307012034942015109801c0d41040311030343e0040040c11814113004903800c036a030f81d46603004d0105265001c0080c00140c001103440c034070b11090710100d05a131200301e1071400713615513043d803080e000380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 227637985 1250 227636735 227636737
    0x41703090901140907140a030b1216030b0f10030602071712040b060603060d0204150504050403051c06121b03080d0906150305060f040804080304060509010f1d040f02 73
    0x40316000d0454481961603032140702d4548981d070800c50084080c100010702c0c041c4183c80d17081454015681c0d0602d8050428400c43c050060002c01c6a0007424214038039049150401c0502d807052031303080600542c04c1c21440c000b0b82c0110042e10303001c1c07254500024480c40385da0039001036045079404500141c1d544010b1030440f01d018901104816030b80c1340400d040404e2101402a07610881c81407a11201c990780d0700c020880ea60106498060300301c800502e2200042c1081e0340010ba0146035580032510442d52600000c05440c0700701e40840020300c020070000384049468000c000c905c80c2c014070500503e82001c1d86a580c40300300120281054540b40d10200210b9400c08180f400707940c22181d8143c3e50102040400054800e1007c2207032160303e803036408440c0680c18030f250b0045d80d03488000340110340c95a144105080c00301500c00d5404104c20040054031030310400052000706941d48500307864860310380000d4441d000012203a018030400703a145200584c0043c048510901e400c90300000c0a0030640034071002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 227639235 1250 227637985 227637997
    0x913050c060316020607080f010b1b0d1e0905310606020106050f0f0a060c0318030606030c0801050f010b0310050a0f090e0d050a080402010e1c02040e070803041703 72
    0xc00403c1c81015183c0364601054041035030210b5003140c641d110211100c000c21500301005000000c014081601ca210091001c07004d5510070360681441d0030301c01400c5c2145503050f0404122400d1045644403400c0005003203036803490500009051070500450301012003104001d102100c00000010443d808500200c0c048078180010000c1c0b0741c43c0c00d4064005c100c2c90080034495091841d074140c80b458612954004181d0240c0a0402c8501d0008142ea440195110480c00d0141c4802e0f0540e01c0501000e029000314000c45001c00c0302c501e18101062983e6254201244607410b00082045da4a0f91411031411140490303082942ca07600c900c1c8100d101459900200c2d440380b0081400180d070303500c00700180181c4103209420400c12444807030160790b82c0742040440000c10014015062041c0c020550307160b205006040c0300e0091000d80d0300080e0f2050f00003400110424450109000b94200303841105090001d0381d0050841c02c2c20298103650381c3c025842160440c002e19520185801001c3c026030302e03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 227640485 1250 227639235 227639239
    0x3060103140f07031a0a23190509010b03130215090307080105060f100903030c0809101e0813020f0607230f0c09010501032c0f06060f0913050c 63
    0x1159050000148482da02e0035200c000000f414522100700710164808140a2100c00606001001c1d15021842c2c2588101c0034689401034900034a030042a112809400800c40b071140d0003c4501d402c142c1080141c0c0410b0f0044403c607141442000300e030504107560350342400e404a40514a82405102450081c4a040006505809000344c006107620054000d5402054201c800420800000040c0034840103001990000103404003400c0011034000c118003c01c540c0690201e51808a418011581e4415a854000006004204035403881c1c1703034040d800340d89500d05241844181c100203204403401c410702500070780304028401c030b9842603540300c0c4115a08141d102980700c59031002124044240314052200341140e0146103404061b034440412801c01c0c2d0356005040b454240d0034400114001d02c0c066100240700703402c90303080301801c1c04641454029010b0710401000526084100b150030404050b00d5a401a0b2007011803030002c4da6441d421035442410915602e00145980c240985040c2d003800b0015 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 227641735 1250 227640485 227640521
    0x13060213240e090c03071103190c330c02030c01050103050601030c0602010c09381c020c15090709050103080301090c0509010903150f060e0a05060108070804020603060103 75
    0x101014404076030801c0141101d85a03080c031004003000b44242c11004071691a1291030800000349000d019252100000011004030b074140071a0482c0e83c40c1c0360203442c03241004600718003001d104100c07800c0d4202540c0c00c102100441c0d500c4920050543c0740500c03400304400540c9451070389403c0c500c204103540292191600034400c07541c1d01d05016468802c01e01060f00e000300c0750000402d503940140200d0b40664000da40b440009454075190907512030070a5065008000c5d1012284501e010314941e034038241c0703200d0421607a02d0f5081c10660744100218801502d9a500501090080381c8010480c550f0455028004844a58030016010300705407180c2c00c84d207000d81c0f501c40084184280711000d18181c540d40b03441001002c0310150141c17014020070001500050b060750b41407001911800b48a142d0004c410b0000c1144400316100e9015115250410122a14001c3c10040e0f11040743c003800e600b0140a080c161480d0500104c001c1013404000e0000c1e0081a000011800ca03920980c0803510b5084505641 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 227642985 1250 227641735 227641769
    0x1404091a0604140115140f03010603090f05030c010f0b04110d0c09080d050903010c2d0504080f0309040c09080a06021c0606110601050a120b0a020405040c090314030313060213 77
    0x222402005c451348000907034145d04080d0320310340f1400f1a0f40d8a203104842908680c6058012805092451411a010044031400e08000788080000d48030b0003540c0300c00401c140c25048200000c41c0c1a8209030b911860412252062a01c00e100c1221050240b668005c142c0000c001c600365441b080c40da000c440a44211000b169015034404041c10409204070001d02c03003e18183c00446244983c1071500450300c510022a0002c0b0324000c521154640950425608050707503803100070306191002204050507000020810503600d0140320b500450209424405c1800d400e00c10010707a622024030000744100e41c001503811a40070b000c42004500c1742540810b00005d6200c0d81e008003682141d0100c0740c242c2c41003500100e0b803480c0600814042d00c1d03c114641c00c4501d0540c440540c4254081c1184921070390804c0042519240d80c040c6400c41205a15454113103403440c078200541d02c40404904600e60024014004a01000d02ca070300101c40c0c00060140e200c4565004141806a050748135010a04c10f500d18 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 227644235 1250 227642985 227642999
    0x5010c03082a03070e041103010b07030e040e011a040c0504050108041106030712050a05010302061e0d090507050a08010c081306020c010c08160305130b101503061404091a06041401 79
    0x8510561392940c4032211512050280401c2c3c900c212003288607880180010f00182d500c039809812a2400b03458424200c0002001040031280403203c642e20a1b5120100700561a000115401c042d00042d41c00300141c00c40010003c01d02d02843c05414104481c00c0003141c1440103d82d0f4103103d5103c0144407035528100349002034444900910098250b904020000d11301120500c0307200e0480f9005450140b61514003402d030401d0543c03a50070410351260501540245488601c58554003d1060006001140c10803003040402c80f201d620078140e0385c1c1001000c00e2056030281180390401488060304e01c084c0c1035464644064020507420b001903618140303a15990719841340341d0070f02581c1400b06113400d90380000011010b0b900c04580701010348540e50001c0f80017030410180076070b009035461740f41607203680c585820f5440d8020ba00ca84c000060f40b03441d028402080000c03a48140d654084408020703041b102c0d82d03942a80c05600f001c4c820740c80b42c010700098060300ca5801c1040001c2904400440541c0c590503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 227645485 1250 227644235 227644237
    0x3050f0a020d080105060a0206010b090d0f050102030612030a09121a1306060909020904020f030102070507060e18010e061003020d0e070e0a050f04060c05040b03041208070905010c03082a 82
    0x11420003d0300c044000030f82401d001d422643d0500d03456001d001c00e60308200300d201445d40003800540e0030030054140d08002c2402004600c082500c04c000160b41d03803c0000400c1080c0c9540d2080b034a0607002003000c00c08980d0041c4001c0c00311200000c4980c5543c081e400c0404d02002e1982d044544a01510204280d004c3d00d1000d02e88001d1003a00b08104190310b42a02d80e0442c2c0c040240290040c01840c00310303000d49032588040004403c010005071501015075290f5090600307980c00f402c041000c411515100e071400c001c0c04682d450507064035545d40d601d002d020080400001e003000e80180c040030070310303031030340d032003901117407003031605014140701c50302c0d45547c1c00341c2e2050980305505407091242c010500040c900e0140034098a18041a01443d840b02e4840c1c400414038500c5410500008000002c2c0182c4404082e52046029810301c00600e0810000500020002800e201c104120f00704140603d03a0032407045007500c1d42520b060f02c0c0d552781c2d003070500608017960803284d03200d070310301c940f82400700a8818 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 227646735 1250 227645485 227645503
    0x11040e0a0f020c0a1203021804090c0f0303020d0801081903110a02031b120105090c130f050705030105120609031611030a08130b1603030e01090b0415110306130903050f0a02 76
    0x324005e100e41e0b0300710b0124224010100d6489041075180c000240c00c2c0351540200441d40d00035030180f03006907542c54501c0300206003544110b0150700f003084400002900114a80d0050024001030301c80032340c00c1c1d00200c030100085000101402030101500fa02020200041d02c1c046501a045600c00500809101401d8032881d114902c5522400c00c0303040d0904040c050103000e22400f20003400c100b1083c0040041c18130340070b41502107035a5152000c030005091801124004c0c03100d925660b54950410f0144520207065080c0c02c0041c0d4030140c14002000700c00030403030342032140d464540380b0307d048146410314a191100c103115078036124480c218400e11a011004006900039403070705074003013551040c050480c1d00a6800b4015101c0480031002c011034000c1d0027509038040000000168042c01d6507614003a40f0b000d503000e58400e8403000340d0302001d910328410b40c401620000001030642c54110000303041441501c282420981e101d0090808060040d01510582d054050005850b0b03181e04030000d640e40c02403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 227647985 1250 227646735 227646743
    0x3050708160c1701091106220b090418051203150a0e06030c0d030905090a020c0a03170603030403210309050f0a0219030b0a0e0708030c030c07060311040e0a0f020c0a 73
    0x2e039035454a0450512640d41840d621001400340d207846c0300100041a0000380041c0c200c1c3e810482024129070b40002d0b40000383c6954210a81c40320300740c20900c011116a01120f01440b40c0c4080503501103a0005541102452908003032596940c2c0c00c4560803e00c1c80c3c0d90005a00002d01c1c10012a0151243c480244643c00980403902124002010042c2d07035510716502402041c0516014402c0c0c3c14032240c0c19500010182e0013520b072615107066103180492805041d400a2562000d94080240d4843c00d036402a0080b0015401c1a04641341c00004107019040034801d80c083c1070301c03990a280030f42c01a0303a4043d00401601ca19540112032252640d0344508220301c41c000d140f051404110901a0380400d882e000312010a15540c0d00e2000700c0100403032540c00d03c492140850015000004000800d215401c03070000d0340d00d6074580d04d4424503040490308100107040c00c2842c1c0343e41c800420b4040d0f508403040c0010a03041902c074880e0002c002c00007070802015041c00010001014280041d641c40c0d480d202d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 227649235 1250 227647985 227648009
    0x30204031a0c0d0c091203020307260d15120f1101021b06090a031506081902030d05130902040f030201021005070f0f020c040213050a2103050708160c 66
    0x40c40e1a220714100084490900d030250903c10484018581e5100000e10b5503a410314000d090f40b299a40b110f00041e491044005900000d500400c12403400400c0e03c506c0d8a4405407800710f0020714620180d4040c00000c407910917030300c05014424410400d500340c020b0170145100b21002106040130010050b41030000e0341c3e240e0056401e0842944005903842c00c082000221030f00b04e480550400403075600c1480c041e0360240c160031001c2b000c1044042c9030145415164000202c0d81d203421182424100c41c02c001e1481403030051240790260f180402c00d0b00e04585180f414030781d40c0071840003e0305508141d03080201140d20101e40419000342021030401643e001f40c0817500c000640381242026604203c406100080507003002e1007205005428084c4100031500543d04511f180101140c126005801c4010b000001501c040000c0d0034845514009880340031050000f4040c00c0c40c40c0111518035082c02400c00c540040c015080c4216002929070001c42202c1c241c0542c000d5060041c006406401144a00c0036 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 227650485 1250 227649235 227649263
    0x1f091a160e0a0e060f0405090c030106080f1207080d0203090a0204060b0a0c0b07090302030a0c050411031311060d0207030c200a09021e040603061d070e09060f0a030303020403 77
    0x20048a030000c00d01001400303540380c2c0f414411100e0481501400032a0412a80300b82d00000d40d4440c06a64840c6004000074181040400c00305425a402e0fa8064a429044010030500708800410119161644859090b43d58580d603d0085698030901400e150705901c0803051261020000c078075285d140e802180d0034080c017501d0b40d100c0010345c0705405030200810408084000054503130b0900c0d0354040000d082c42c1c250144d60360007190503c0034003d001c80395002968070501c03080c602441400c2c0d0403e43e03c81a1401c515010700c00301e40c44615210007806000302c1c000810000d6554600311022201d01240a41d00d8191510b006400f101310300c6012a511244c00014403043e58940e102460403040007040f0028851514409a0081d0300c0700503100e40e6011000045508144440014402841250380c0003840b503107080700c90002c00288100d0080c90f92101424418001c1d0f009140c00c070108011980e65220344c5481001941c00210724505c80e42000e1429000820f06800d62b0142080740d00449000d10304803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 227651735 1250 227650485 227650487
    0x30504030512041a09061c0209060409050f090726070f0611120a09231206040c060203070804060305092b03060b0922020702060f0a0e04050402031f091a16 68
    0x1026105c201d60300a8001e2114120005841d40840c0200a080300c00502c0c004140000c0389040e407090708000002a1110144014640e25203415a8040d4000018261813400d114044035034024118200941d6000f9400c80151480c082c4840c1c1c0061500081030201c042d514440035103010201000c0103400d000b09460711110040000c02c64141148940c3c0c0c55181e0f50030103030b00104032020020b140d441010f000d640402961141d0081c030701e5a8043c2c00040c11280b90a2034806075803a901e4100104541040c040100081d803208161000e454041c03c011a8558543c0304c094078004500040c0c61148804034400c0e030f04a04ad40504000f419055035060040580b16408447c0901c84e52218541021280c5d1852402065000103950121300e058800352400c0500d07000a202a0071120100c908904009013185c0d207140c0000513211821420f407002c2c00107240c076800081c2c840c0e9a104c81d000780001d004c81d45c101642c00d594022402d15034881c19503030030342c02c610440307422107002215040801c5401040c008940c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 227652985 1250 227651735 227651737
    0x807030f050c10270609060c15110405130b0603040b090109050a0305040503010b19090e07091a04050a0504050714150301080a0b090f0c10030e190c14010e0409030504030512041a 78
    0x45d40c0203448002c070851a041c1c00b01c450319143c01c4152a4064400b841c0003881d1580e019030180111007060b01d07629541000c080060361024054000e2141c0d01e01003800c405600c0d16800d40c0e62160f08415410200d5a4000d1010f01514001000070f0039806800000410950000d000c1c00c20b44000764000c10201010750700f07100c040c2d03400c03c080790640064900308200c45c0380c071174000144030745080d405d80e40c4882e0741e00020304c143c601c1d40403c07408840d242c4084140c242424460300d640401c4040c418001410a9102c035500d4980e20f014001202240c4a0600103507211420741c001105540c0421a6696940b03410090321402d6204040b1501038510005c92910040051036043c60031181d4042c001900a590401800300041e141e12000d040c3c41e58985600b075501808101240340b60410b44028020052401c882129540d400c4841d66410111641c1d04a9900410400c030800040e140011559060306044c0c50301e010303507480240144500b441c4e02100c1440790002c0c2c07084410064811404c0b100c0f0b51054045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 227654235 1250 227652985 227652989
    0xd060e03280c08070609020406030b0115080601090320040b060f0702040b030105040206190210021809091c0e0402120115080c03061509180a06050a0803040807030f050c1027 76
    0x4060400e020103400f05c1c14591112501c02d01c000e1001803030039a00d544114200b0000d0744030040340328402030481150791300000c00640c08542480d010044604503a5644000c0403410121401c01c60b40040041158840c4e034801030440703900178005611004810780419040d4003540c0102d0080b81014401c04050405004060285d680100f0752810f220207020891212144902d03088114410b94014541d480070a1000b800d60045820b0340001c41418078040c814180b03000b40c07420160390710040c0940c080352a22145010784001ca480e2200e02d1245600024003e030081030080d004000409000061042caa00c18905005100ba02e80320025034540c3c124582c40d0000b1144190000008041c003a40b040031140288401c00b801070180005091171b0701540313041d210455543c41034903a44c0307909110070328007148000001d09801c0700541c501401c18081e05e445160030700c002881101602c11040c1080400c2c000d0400c8071101802e81080402e10520040c09484d00807410240c1d80040102c04001242d80035100c81 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 227655485 1250 227654235 227654243
    0xd0f0f0e0f01060f05150904180506070c121b02060409060608010f0f050108091912020c04061415070813031416230307080607020d02030301080c0d060e03280c 70
    0x616241106001c401b1440e80b24580c0003c004010001c02c07075649214a40384000030411280e12144075140540c80c080c0c01030000b0050150000007540000c0c4402200c1808041c80c0c904511400051401150038a9840600030b611680120340401e41170310a41c8040115406580c80c05501d99070348541754400c801e14020709008640041043c0301c154007071070041d40c101c154241126440ca0070b041d04c99800228404045038030a40506e03030360310043c3d810052113042031021981000481c0c40e040c001c0ca18803290010050003450200f400d2901458644107076400b042e0041c8429559984507000a0303450f035120300044500e00c0f4121108440c1841c00210304103d842000340c80e070480d03800d04c000403003480c0e001d10110250408008110f00c2d2a00c06000120041c004440184442c1c1071501c400303801c022040541d10110b43c002c2c8010440506c00040c11899000c007500c0140c09a5654245200a003086451502051000245201c0c05000701c1c44a502c5199200c1c8134000c110800c00030440300c500e01b40350003034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 227656735 1250 227655485 227655509
    0x1116030807120c0c0b18041d0715020c0906011e03020913141f050a03030c051903080403180914090c0103020c030403060f06030b070203070b0a060e07050d0f0f0e0f0106 74
    0x2012117003c0c500240140030324407200c250b0011406001800740c07031301035203a00500d01d40e41c81c0b6104250010007850b0090f088540e19829030315000340000b9a01d90b006a110f501c0f440bc40780100e10142d000d0111000e12020001c902800001c6801e0040c010b58010380c4803d00802c46108044003248031032095010310a40541268034645a501c4601c00303a004044c3c24a00390701d400c0b80c0006941d80c50303200c2e0000641c400d40310358001001e1030a04c20b091003102c0180070301020880500c20b00181d8003541496200c4ea0504110b000103042480c880d0300880c8c02c1e01701600d0303240b810b00c52070f2041d410b120700507114038000000c4401843c5002d004500342d004015019145a10a00c010300004034030b03400a0b07504000b201400a850390350703501e4a911001d000c0d100c0c000982c0000403010b00b800b40c425840740d07210300c1403601480058a04048a44003640c000c0c911010010003250f18000079903aa00402c400341001d40b400d102004000090800a04040310031b001c10380300319400201c0c2c0b101706019403000c0f507104071140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 227657985 1250 227656735 227656739
    0x806010e04030e130f2306030a080d0b040c030e190c090c0507050a031709030c1209010201090b0711071703071209080d0905040501051e011116030807120c0c 69
    0x40d6500c0c00c0310444154003543d80e04d10882030002500c595001d0301940c902c0440d000749401d0304c480c5141c2a41601c0c030b03004c042c4c0c4010007569441c0005c0040543e540404d049a50380c0440040320000c0c0940e855080d809401d2604d90381c401079058015540462106055603290b031007910f40c0b8503608240c1a801480489128001c02000741e071070b1700074421980e41c5e00b05603182168039520706e81060281722088001c00e041c015034a0b0511a40944554000060001140341c0508064195a558444041310004c50710002c1c56032040d034400e412a005141c1e11a0030040141403465020309122050380700d203d0f55105880c1c000035560b01d418580c0e100658405c2c051490103a4548030201e25600e103400c02d60500010150020742c64108100340c1011805075511800f11b14207210800c0251039041c0c3c4041d1050110700412101b01c10807900d02003001400b405c10865066049504038180f0601201241000d1901180041846004002001918400c004450b180001440151401d075910a0042e0400803607183c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 227659235 1250 227657985 227657987
    0xd110109020f011103040e010e10080a0b010b031503011a0f01030b0a03020918150a110705060708100b04080c040c020f03031b0d0507020d090501030c050d021c091a010806010e0403 79
    0x181d41d010080130001e992500351100b03602c810a02083e803210300850105420450014107034646c0d4005004084003410310381000c1c1d10b901590800600a0003840d920000100d06000c1300c1da55405194a40a4024072030440804804a82c0020720f40c60580680c0700550711020940c800d00c034200c50f42c40f000304046c0701c2e1410354090044600c8000c01d02101038440a0b214083c0d110100200e00e0107001c4082c2955141c9082244801542e07400b8016510409040c401103000990200f40700c1d903c4641c500e001c0c92a55107821800084600584c04124068000140441c8d500c4d004101d641d680c25050701c05001c80710544108070394420344034a8641240d00140049030708503034005508607900d1070400d03805052500c1d0481d0282191000d44801016a005e00300f8150030390b401491060041c08242801c0001500381203001d00316118006417104210760000d2003094107912610a01152081040104005052072511507010070040a101c040310b080ea000006800c640050780c141078500001c60140740d03481d9564 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 227660485 1250 227659235 227659247
    0x70e010816120906050127020f0f0918090a1b030c030201050d0e011104172a010504030507031b080307030e010818060a0606180506041a1b0d110109020f01 68
    0x10007841c0d030350f84804254001c500b6500440c1c0c06448600c1c80c2451703940c83c1000e03554005801c61848502c1038018403c04502c1202030055400d00c24004244130b540e002d2010004042c1d0200782622441d10880d1018815400400124440014800c0d0034240d0a140e490140721250741c0f03248402400301440a0081c001948600e001d411144a002404503490205000031420b680d1014216603416401040820241c1e021416030f5040840e00c6024010780d40e80e6840101d501c015081140b550b29002c210754441c4c0f64890003c60f00156040000c6d00d400948a2410030400825400894411603020402180d40c1078048200c603c503691545410341d050390080b0056034103070f00003480c0141c02c242f0100c2902e54060b00780180c52044c4000c5900040c0c2a08021002d4500084500c2d02002020b104000303010b42e0310345004803401c2e143c10400442c1030408070002400c5a1040901e440d07840340c50030b50b42d402d032500d0001e0543c281d10741c542c449080200c0303003270106422aa10f03c3d10280d40702d14159140c8503654003440f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 227661735 1250 227660485 227660507
    0x61505150d1e05010602061b070f03181d040309081614040e2b0e03030403140c03030d060810110306090702071a040807080c011232070e010816 63
    0x204040320b075400e820703148003100c40036840a809a0000c1c8100700b44045800e120b0074000e54a04012800e0141ea5110f00b81c41c1e2084180c020300b4007014a0444818640a211400003800030491a5281d03540700351480c201c50340282c0381200031560140c00800c10202c0803e1079080007442165070100ca9142074801c042030205580a03a40069844c000290041c405020b200d00b00b205110180c80301e04108007003100104030485411003080070742a00108680c1d40030088404882d040065240c040da00910750508000350403440d10707030604c40011100c040a003280c0005045402e4001038914215554040d041541c1d510216942c880000700b00040b601c1c075146a4480d00b0140501c120b5104545490444140d01c4c4003240004078407a0106081000c048100904030140c8488405040e101c0c540c03900103070408800c81054280744d80c0b43e810540c40301100c8421841c108040d2000f54031009920a900b0b200c40b0819541d400c0021180c0d1a05201d55001e20141405204511b244000440302680c1c1210880009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 227662985 1250 227661735 227661761
    0x912030402190b070209010504060807030303111603080403110106180c032c070b040b0a120e060a061e0305030f0a2c0108011d0411180103061505150d 66
    0xb4041001c855410514060103488500140b6545540e140100322203c01c0503444140f18038200401070207c0603000c5646411613a05050220300c0a0b41150460090f000d0b081c80c034580e000322600c00348107141c0d02c10181130041c2e003e83c030307414241d08111842ea03003621481e016a040c40e06801013452035001142c0c4c0520290b50f42498000b0300384e007488032030407103211040032081310040550f807080c410107000784680002001c05829442c981441d1030681e681034040e10341460700f48120526910040d100300d8000c0700108000800750740003460100102d01c000d00490060a00d030070f0b10242d0005910140158130402e607030b0028011030030400c229900c1c900d0b540c085100842041180569000c04111851181f0491a60a081080000340f80c600050030001c059001c0d070004455003000300795030026070a800741c102d5001500d5a114000340e1010903400d80c240039500e003d48220340000800c0c09510390000c401b03032002945e00310b0029501c8080045000081c2c00c03004100c14100203000e450b00069000b0344400c014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 227664235 1250 227662985 227662999
    0x121b030915070317100609080114060d05030408060712050601030b011715150a0305160903230303090106050102010b24090307170f0d1d0d211d0303030912030402 71
    0xa1081380e4920140c2a51201c42d4202c903080184070040d00710900b4400341c205100204000800c00001035440c08002d0851405035a80b40c2c061802d20000380101c8000d0724400003103820341d05040500600320327002e1074100000546800701182a5600c41c2c051b081e06131005039510b40840c2c3c007110035803040d020058842c1038401710820940c3c0907521045480500680381003040b94941d421080d02406640b802006041c00181c0d4881c1140c1e0190095020001d803a003202945817083c407600443c810066241c0c40c422143e11001c0104076440308150843c80640e071081c2d000380207903c022000e01040074540420204200541d48440b44e20a02d40800360403680c40c020115100c56075036220104902a503c82c801d2445d8000130201404c01e48200601100d1004929028026101804012040b040a200407500c145004802c040038000040c8401180c85002da1800d079800020400c050251109040c40d158140725611022285140c08416640b04c0c2500e01c1c060504641495803c031401c0d400100200e0340460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 227665485 1250 227664235 227664257
    0x210030b0d05101104180207050114040f02030d0206161d06130f0605090a090b0a1a251a18030703110c120d050708040503121b0309150703 61
    0x10380c100000210300d004801521140e90300700304000c20344403400d013078002d1604100810000d801b010381c2005006507200800585a00039807800e24050301c203000c080246000c0200c188400e02580ca040d074a0b1707c034421811116500500719069880303c2c0125030304c901d425802040c0001d11400340c50b803400c050b15048540d5103c240035070002681508545a64081c5100488060002c0180200210080c15035030030200e0401c00b815001030341692082c0a01441603445100303a85294984050705c0c0d01810104040f0f144460408010240341c0c1c01c03080c3d90f0901d0f5140e048034500e4580c1000040c072000b0fa08140c050350001c04d0840c840c0c00302d007800340903040c0e07101c0b101250b15208142400036214192003507407030f044d021084100351071400400511143c0b141800201c0805030030400904104c00d98494180a41c031020203051003451409140c1c4225014014550144401e110749001130140040c90510000400c902200c00c96507802650b4030346810003940001a198003080344083c00c0303082c1c880c0c641000c40e04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 227666735 1250 227665485 227665489
    0x917031308010b101107061202120114031011070b0c190c0c15020d080a020f0403050f07060903080a05090f04090b18010c0519090e090c010806090705070210030b 71
    0x810964801d480d1650740d29914910761924003260040000c40e40790525004001d00040360300c5250034400d400502200c0310700c025020460b5015100a80303001078450150b50795501f406000b845100582c83d00c01d00a0701640018410580320300c4162402d0a400c00b0706040b401c2d95208468400600b10046c00c42092042c0710481e2000142c44071442c0c8650744d404041a4a440c05d14960140c9810076180749446500741c2c01441da0026040312400c04915202c82c0940b10301d00040020302c921203005810302d4000034007005214000588194951804d0212440140e071618222142880c41c00300a0400f4070070071003808042c0c0704074007a24a0303840c020300140781002810000390488807204d8044a0b9201c0d43c200300b0a6031510316042c08482000a0001c1c0701401000100618071322070360418070700020700c07141c010a10f188210070610150080d0781002d001420302c0106a0b80c1d4500449a0500080720300f400142207080030245c4070301680041d00e4090805901d0f80c200204000c909281d5010966948440380c503603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 227667985 1250 227666735 227666767
    0x30201023c15041a07080702030307032409090b0f0c0a030b0a0e04060b040507030b101412010303180602190605060f03161d042a08010204060504080c010f091703 71
    0x114400c108101c0362041c80011103076130300d6000381701c2410701040108005860340c001c81206e50003078503858001070811ba03232004084080340c107840d01c41c0104400d00c8042112900ba03844841502d0081b030000400303a07940500103a21040450782c1c203103221000d128034440c5030b0080d0402d4030428001051000720795161a1100d900c20310446042e22103688400060f006407c080c412150400b0f0146007d000840e50070f0045803041456120745002c0000c41b002001e5144045400d40f0000c1098a108940d40c1d60f403410001d1000c0380e03841411045400380d6100046840c000103e0303003441102c0412080a01c04180c0b43d000061070300810258025405600c0c41800c6e58040c060740080e6588080615071150808081455207101e600ca07030704e001c886100c2444080b41c42020100d40e03007800008103403030f120032071891440104515444111558000b03e00402e8854100001e007051b50215400c4a102c0000704004487c0726100380c1d0030501040c9001c1c000e2080800b51301c40d0311b00110500c1e0442c0d207880b1054503964030b2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 227669235 1250 227667985 227667991
    0x10c03020721140d05090d02010905090703060305070609030c060f3b09010810020a02030d14070807021c0509030106050603130605060603040305030a0b0a031a01030201023c15 77
    0x502102c902484040005202c0101c40e0224420b0040c5a003049142020340140324010a00d0b2185001012081c1103a125043d86400f820000e0251210f5062482004d00684a103000c110391501a905000c03840d80d1040c08208100c80d00492040c1443d40b80c4501903900c405d07550500400c028001c3d100d070300d402c6c1c6040c0f07402c1c80100510202c003058092188901c1c0d00c1280c00c4511601c038416204c0108050341d00080c00303041000c03101d10016516030039114181d140d88180080e0070105801d100c10200b210803501c426a100740e445880b00c501c1580c1d034002c203d031251901342402c1e40225540103282f400900c42e4001e00220700015000044941e29500021b01c140c008903000a251050560032508020f5030b40215a0016802d681403811820b0980e0043c05074080140179241650341d610b10b1050550b10681c2c5000215040003580caa928001000c03010060401d000030f90240c13103804130f001b180d090100c0800f140030301c0b100d003c0900c0303181c00304520f1002100b800b040e04003413141d04451680d8042d21580140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 227670485 1250 227669235 227669279
    0x1805030f0a06050106020f0a02060c0a02190303080f0603030307140417060a06050102120301030305130906060e0f090105030703081b06070207080c060415030b0a030b072f0c010c030207 81
    0x1445401600e0102d080d50742c141c0050045400150b4071050781c00001441101e0181e040741c2242c1c5404506602c81d140050300c2c04040c2d807003105518425034404c0702c40ca0240640740a40e41d000620703500d44d09480659030040d5001c503095030080000941c890310801c2c0e48104a1414005e035803030660758810b0382c00d000083d207244141c40d402c91410700c0700c1142d1074402d2900600003800a82820500d0844822150005100103000c2c08400568121881051800303035010304080842003200c1511250008c0400303020f00c56660007916116103000e95443c04c1d2200314106e8074010000c2204600b140e40b001040d41001e00d40b000004403100003410801028840c080c4900c855a00500700c40e03240c01110743ca00504d01d081e550091604000078070901010100350b040e290b11070305020030511443d901044600401c0c0d0310250481a8600c06d010f8010f902006000e0034038000c03195400c01452031080000308030b08600100d921580641800045540117020708400540280103852110741d0ba040b048000e1888260899 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 227671735 1250 227670485 227670493
    0xf0f0303030a150e040b01060807020705061315090e0112080c0613021807080f07050d06031b09050910090519120801060e0307050f030115180b03120304031805030f 72
    0x30361500f20600344900401e0040402c2d00142031a80f104c81d0303046810300468042114500004003110f0003041a403008101c01b41c0b005540e081d038040d019020704150300540702c01422841d14402200d1181d09a58152280805402c816900c0e00b90280c089030700c911011201200140302d45180b00406100c0c5030301c240400c070101c0280e0485441007180054244501d051140310342d50920840079400300003c1d41c000c041c0c1c44980140d44a01800351140d00030301030200b00081c1010404800c01c90002003039520b04243c2021408500d44414980c419203604440c00c500c5648449480501c442c2c0c00c1c0c00c41c00100d0300031002d03903440704114003c80c0c5240700c004805807a82034100c1d03c02c0c0d84880d44003200318010111480c10b4041b0303914034400283c41c2c40c80e40c03040f14412014000c0c415000c0c0d800394407055840c000d813000c40204607a50500c42c1007240c0e0720b01c120031156140080036801c1d4180440ca10344580303880c0c200c4e149142d4942d0f07002d41d40c0c1441c2405080060301107070404110741d2401c00412a00e13014a000070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 227672985 1250 227671735 227671751
    0x11030c04050a060f1d0a030503031501030509010b010c0210090f06091503020903190602040902042306091021060801151a1c0e03031807050114090f0f0303030a 70
    0xc00010012544001c0c20094050340c90010260b00159170b61400e5032280011242c00340000001d6002040d54101800310300002003070004002000441540412003a02c0902099403126181c1d401c0b904501c60243c04265454000001403034041c1070000c2440b01800c0a1400c00e40380c08042d08400801d81001000c9500c9080c140b0914140200b41e421045907440c041d89050105004240c03904100500e0700044003491614108000c82d07070301664081d1980c80421901d4540d520b5a490400300d0704408042144403082d1901d14505266048030701888010742154195245004111082a1031040541007504508000c4412100d10700407400141550000456a14105800440410b885901c6041d605003d0310300d407100300b40124103481c248118400da03c95034482d401d0140e00070b00785540c481a0300d40000410440380003003d42c00b4001d00b0381c03d08100c4003a0750f1078400544000c240c0b41840c41c00350609100303c4850f0702c7d0040b0400b25090000d42916007501029010a01d5500213907074000b0107548032102 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 227674235 1250 227672985 227672989
    0x2d050703020c0418020603040512180111010203071707050705060c07140109030905011206050405040c170c0303030621070f14030601120305032502061e1509070311030c0405 76
    0x42c0d9007a81c0c0085904108031510300e514800d0183c0e0050307000f4001c801c04030003c2d0038800c041c001440781d00002034940b56614000c803402e00303180a80300c00c086d000c40e106446110300303c0d80500c01c0d00c2c130409060b199410310303008001c022a1000b00050224042040400c0385a0000c0e0003808260300440e076140c2016210030b50391070403143e07240c3c42a0070f001a40e0701d40800b83c0c01199212100b030040f81c0302800d0000700c00c2c880709143ca018000541015411606001c01d010800c041201a10215a540c841c402085e50580742966121010030302115810b07407042c404240396140091780c0400e81c0c04400440c80c614900c3c40e010760300b8100d440d80000d00340c807030940040200c6200a46603d480034001c0380a081c10398107088100250041c200800b034200a40800000d400607840804020081b1000c4ca40752030003810600002d6589204680c5010030020541e5462078a8440190140c020204481000e601c1580d41e01441030410006086204041e110000074861442c108021401900b1800b0072070307604d42c10182 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 227675485 1250 227674235 227674243
    0xb03100f05072006070e01111b03060705070b040201050a120c0306050a0603020405130906180609030207051002030a120b130f0b0d0804030f0501021e0309060708162d05070302 77
    0x18104880d402039079445003c0360b0b404580b160707000806040501c0c4002e00040100c841c0304001c08407100314464002545041039050b0742042e80290120200c445035598540211083e000b0041c0041c400c09000d07010500660007240901010540307407414001c8402d1400c1808141d60a9071450307400b1a584003800d20243c1400880c61015008900301903180506d0300c0e0100d0381030050140341d4000c0a84d50440e03203003004001d421544600303c41d011101034000a81c01c0c80300c014003181c0006c802500c075080000803141000882505c41c000250091410700301340b0142550241c18000d51045a50707510384410308030395141d80c18105080080c80c00000c02003503e151304012503030070041941c82507807140605070019510348203d4050f45c1d0b0060054079050031600c0d016003e230043d08800101203030f46030b0302088000510009544140401c0e421200c140e02ca020f41070b03c801d0800c1c0c620300c443e03003008940016880d00a043e00c0351618582188800c1100d60016036101102480f441c5600180300015088241a4100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 227676735 1250 227675485 227675507
    0x4090c1410050c153d0905011409060117011202010809010b031c0c02100309110901050f100905100207080f06220f0b01030501290a090b03100f0507 65
    0x801c1480ca02035550b289240d981c2c58185140c41440c0741380b000107840030f4030020152011400ca0170f0f840400e00d644901905a000c80e502c0c40100c101c00034900042c403074250300445040b500036440d2506d413040302134103002000500038241030502851304140da00d81040048420300900d1500c050304401c10041c0700042020802070300a25490b81404420341d0306035408100c0004116151040b8490007224503400d440b51588010003035800b21b0000b44400107160190008484180706811f0030000f00320f01006c0160b1b540d428010690084005010b090b0349003000e440c400d015440c42d05140d0185aa500000340e404040740e0b000b100140c00035a000c21000700c0800c00810004111000b610701403910046d1480409600301503000c40c81f04030f100890a0180801803149c0c01500016111417568581c241702d8042c000d04480c2060b00104440e0200342116601e08280051034001e0080c49074038039209605c800303460b48940d0180d150040314055108017120788119203060101d20404109464a08000350945d0009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 227677985 1250 227676735 227676737
    0xc0109030c0510020a1505010f090c09060509030f1f230a020715090f0b06030a020108040213021b010e1e06072d0203030f150d08030604090c1410 64
    0x1042440051110001907040d030340c090700d900f083c090f141d1004902e04034260300e016001070b803107117808249140942c11190580c0c151503441c50340d8903514241401114003c180810000e88014028003945114400074015803900504a68221180302d400383d062020308019a014080d044600c000f46003568082c800040851401c00c19080d50450295100341000130300c1c1182c69940051131000f005500b08440040442c82d0300308102c821214500102034805480050b00d0510b5a00d00140e158500091003003000b0382c0c1a9a00101c03070f2156801c2c0003200704406031200d15683c081c007001d40416840528211341000100011038070141c46024a03040c2003004c00f6000780c500390280c0c0340708100000588660007403020720b4901c80d1142003904030760b103248402c0400800a8000301413140070700e40c0007003d0350245445400079a40f03a107400000980c80002d08440d250409000e6003420049170306030000c0e40c0d0015000c3d00c0400c0c1d00d0f10aa450343e0168a0640000c80041c039403401c1c41645003048911078140d0005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 227679235 1250 227677985 227677997
    0x10b151309060b03130515070c03120e0a020409020307092c2b0201110c0313050a150503090102130e07020c04051014030c15090909010902100507061409060106020c01 73
    0x703150400c8400c2c072000b48502805c140000c000001c00000b000403202ca00c039280e541d40315a06110400509101000d0f605900143d0440b842d840409118440c0018410440c002007071500c1d581e81c00d00025000804099904d40240100060704030018001d800000012000f2081803512140d001c04d0a0148401209055400341746100355502d0300b0005d41119501103814040f4172170320f011040340034040a071381071025910040362404250100001400500081a142c89440c0380c80e1030501a030480c03180b040080301e500e028101c610a81c05413000750b03041200240090301d0118030380c0e0f040300080f18541c480305494101d4800c00c001c0550520819030342e40421501030280f42803111340303070b00984003502070bc003409a500c8080e00d04a940400403a44201005440e20800c52880030030f0000c030360440d8131414015000d0f000054001017062042c4102c0581c000d04800c020000031008a0716500308200c101c1d87c55135100c0450004e0103040140030310640707695000f003503150306104000f82020441100d41d410f1000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 227680485 1250 227679235 227679239
    0x13060305090a080702061614010c0e0d12180b1c020909041506050d06050403080f0403120b040b0607060504060c03200c01020708130f0b0c0c090405010b15130906 71
    0x41a02c4120640100c9000d480300510b000255041c46030740f05440031040702d6100b03041048900140d050316803424000810045007030503c01c3d101c80481c84001944901d25825940c0042c039050b03002059400d452a10381410f9126a825032668609a04280c1e50508085000380702920b05405d0200780eaa500c540c00d504004690011400307010001e4401840440c0d020851001c40150b54041e80041100819842c400041402d10400400742074905030700160760900003804801c6044107560189600d03594620a40c5c107002542c400500c007202d4015030250b10ba40d02454147e884502424845014840c0000c180c00c151402d407040302e80c082d40d41014142000f20782810000001940c088450388010901d541e01524046180240318440e001010701202281e15044010f42400d0003040d541c07116008504107071500001c8000d400b41059415495010922087c09818200b01e0140c10a2260b0000b04121544500241c84950401d00c0301074202c50202d4806500209040394000514100000304002c038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 227681735 1250 227680485 227680501
    0x50106110a030f0e031f0c0206010302100c020415060809160b07030809010204090e1b0105030c04120c030203060711010b040605060306221a010e2d01050705030a0513060305 76
    0x76090740280900c400d00508050702402103030300c2d5404440c01004e66220f12009410f0782ca504440340c0c0740442d1249004040440306000207000e5058a80041c000c0c500d1074494482282c1302da07041c40040740c0246c1c50384107403001c0e00d24108c9070501515040c0c0300d2007402d1802000c0e01e0315058507000c0b00040482002d5007000310b031031228121007410b601450072643d40d03074401180c240079205550203900114581650211204404903840312420104090100d005180c0382c0119000d020649450010000c10041044140c0c18156134980c41071149206d40c0c513190740c0c0d40010b402c0c107a0442d501c03c0030800400803078106000a10031400f401804031010014141004003003a281d0000602e040c2c0207000440509405540031840c070082c12640b05014451011039005a41407290444036081c0401c40e01c442c0c40205140c00c240b003480c140c2c0344c2e1182d0300d0b030300d42c1100951011a122900040c1813003000c02000e40031420a1005100102050b01c3d030780c2da114414401e8910100103030b800f03041094941000c0c007101d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 227682985 1250 227681735 227681743
    0xe010f080a020711030f150901050f0604090f02030d03020d0b03030301182007060603060506120a03030222120c0e0c03071409100c03080a14010e130506040b0a05010611 74
    0x70700c055401600c0d4149441d201d03081660381800c1070307814801c500c03070b02100c242e002840754203400c044844085180c07180204c007802d0364010f40f02803044c0c0b94560000343d8182801c0c0d0298039214000c01c1d40440c05070540e0042410040700034007400c0007030303000101070020308040d0203040201a0150000d510359850070000415440d8811042c8401d19100c0b20796141342007006080300c00804000070015901d60042c40c040b4002c3c420b85c4000c407940ca04204c0022402d1901d01c155441d510140e80140c41c0c01e1010b42c0e8120020f61291917004003041c038201ca207000c402c6540f0740d0030000c2c141c0400d100c6101d0b416401c0248050703090b648880c002c50103400c2000211041c0c001660f07008041410900d811044503600001c85008146945821510b001c510343c1c1011352050b9074400c0c190007600c0d0000c00f82c03920003c020940d02c03440580c803840c2480b00010841ca00446903102e0388412001e40111071a00035039142820b2460949099650115500910031b041d6558803c1600500302820000c8010032011616500c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 227684235 1250 227682985 227682991
    0x705040803030c0a200d02152a04120f1e02010c0f020a050904060c090b2104021206040506040b2d0709090c180509012d030203011406010e010f08 64
    0x320200418a558014090100040703c170201200303010301c05a220502c1d507503c0c40705544480c01841050a8a581e100c11000b866004a03045140d49031360340c4002c8000c900100058401041c0c2040070000003c420201103101521944940d00d281b50000150a00300b0035040c80c81944201c1da055000d9090050780c1009550811903440f00c4040b13a20540d81c00003840c5141c059100c603401020301000c00c03040028071743c421140c080250300c90f44001a20351170b03041c00b86d0052401303502500422403055080d4081c41e00c8441e41c003a20007040400c2c00f0000e40302050401ca42650222840c1e0311030000d0204101d01236510380c4e40166062022030812841a840c0d211407580c8040801d0000c49210104000038400c01641003d0040d0060510180842d260014480034000201104e80510854041024a001081141240c4d81604410b03407510122410740c2030000290740c1065064081000040140c80a000307000800300c85000040940c03500700005007019920002e081d0400142c401c00786100c940000840f0f0b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 227685485 1250 227684235 227684251
    0x90e09010218130608010f020309060f0403210f090803090d0e0a0b07062301050f0915010503090f07030b040209010e090703230a230d0c03050d020d23070504080303 72
    0x50f08030034902440000d1880342c0080490f54202403020004107401d400660250b8080411252140d40d100350700d5032841c03000c0d200140095800a0760020100c00c440c6038801c501c40303214000400e0403001101c0300c00c968020104603003010020040203000c06046c0862001189141003040101144d00c002408522941c080c00301c10300ca01140d2001400850f6200c8042500c8403840000c40c03096000250007110400d2040601c070340e6400301c0315000ba050119040d1301503803003c50341142290020b001034540390001401403404e48159101c410001c60200001070046020310b0101445040900510480030016007284004407181400d0000c010302c00613900c0b08580c3c001401901c003441803581c0c101c04004441041d00f0a11130b040400081c00042503107026507450004100e00361700300801c40c1549502f234400800000c1150344444001103805403000b02944106c4020041c50410000340700b60031103031082070316080c44441c8006508040c07500c0c002d0f26042070180c1000c50809150054040e524880100541 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 227686735 1250 227685485 227685499
    0x303040303021504110d0b040b090a030e04050c130e01050a0621240b030901151d09031e0304030210060b070f050309090118050a0605010c0308070915090e09010218 72
    0x241841741c0024807070b05a510003000d403160324020f801c1203100031078180d4098600c0c0e14440081129000d0005050750074942c10388982c0e80e100760700302c204801003200130b048000c2d142d410444c8049294195041d080a0700c5803001c1c66245506100601401c501c032178000100b44084014043d1192142c960007030340d4440c2c0384102154034000001c8180620042013010140515507040c007003080d52403000618424200702d402008117020664041a4001440c4212503c00080501d0030308204480e07243c2c5548500d80800312403400c00c2d054a0590951005011914240700c0401400101541441000c01640d60840140900b0342800310901140c03155240003040460800380c00810007600b40152120450020300e4440151380d92900300c0f00d40d5900c0180e01c5107092420000072000c549604c030304415102c040c0d468040c40061980c081d903062802a14503802d000301c2c1c2a00041c1c40300c8400121004059641c3d40300241403402c07800b200d000700040c000c0317680c0da401408900c1038188001c2140844a104407458 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 227687985 1250 227686735 227686741
    0x302030403060506030c090a15090606030e0c06070f080d090503122508010b07020f04060305010501030b2a0702030c0d050d023a0c05100b0f03031806031e090a1103030403030215 78
    0x49c1c01441107a60112049508042000507100c0d05075020040c0c0c0e01d4428203860a8030942010003c05200d4400024003000c1d800c400d0501143c04000a4000305014100000c0c20700c401c2c1d220185150400708402103807154450802200d108205250260307403400010a40c1040081c140c0500b41000502039404201c50109420042d541c1d502c0d0407107158400a4020010182c4906100c0c0c0682030074003050380e83c1194803000c51006026503082140c0e416442000c2c07025949180380c1c691041e07000b42820b0382d05200700030040040f80d4841e0031a80840748680c0040210100001700a4200f0003d01d262485100d0903a0743c2280b4050b100341c00e070114406104c1c021100e00076001054403002d0764404050941c0c400c1c040c01071210042940000c10610040b10070002400c100400c1594030b01c50410584252003070200e00860b03c0c00e1080296404c160007880301d1200d1400d007030742440130400440d50110f890780b14078a100d0510801300c100e0b5510381001c0d0051450942180c0340030b995601120381c040e803802c08540c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 227689235 1250 227687985 227688011
    0x13050f0a1e030f060b040b010f050906070201121508010b0402040f12021f020703020312030702100b030c04020c03220609120c0f030303091104051306020913090302030403060506030c090a 82
    0x144102441e48071500b00d80790380e00360804d0710042502d00c0409001d00d140c0020b110096000e1106000d000445940b241e2070702980200740111500144012070510501c1ea51601c02a4020f00034071070300c1c401803196900d0103803a0010807825107414010b284d0107980304003c01d000d151030031140f1406075080043c11511542062020680c1c0d507540784400b24100f040303c2202255664081060310449008904681519542c1120000b4510050380d540002da44600d82c0c9400703401c42e0b90454208014007c0a8030114007a010214040c0d03444a43c40324005d800005100c0070140101c20074104440350104940c0c00e46e0b040041c081d21042c03043c054407506074000c20112040042500381c8002419a500c240c0e240156240785c09009403541030811120002602d010190038105482038601c00d40422400702102c01d041d860324002988003080da0360b00140201e400590462044c046c0c1409980b10f40c0c01980c0d0b80c0e146080503805c40d54082e050b180f003900402d5240c01203035030301000c5036000140380c900003c1c2031500b400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 227690485 1250 227689235 227689289
    0x30c0421050706260c160609021203120109090b0f0408041d1806070f12020906031003050d03050403021e0c030609100b01020105010506040605030c1c0213050f0a 71
    0x4000c0d1207401c82c04144958416a03520b4a0307000403118407410710a00e01002041e41e4203d92001c807140d410b000344610b0700c0c029112010100d010342c0c80041d040316580c0201e00c000d0350701641d4040c29400080c00803000540d00103040c3c010701c0c40450810a04020350f607500c082c1c10740600380d11280c0c420a00420b060140c401c00300d070018440e858008110181c0e0041724a04c40700104c40c0030b00000700c040c004240401000c11914480e1074255a4082c3e020003235441600c2294240c058941002c0d0309000005150312064021802803010b201c034802c0f4246549001441c01070098002d004050608092200203a000111034000030300089090903c0703001c0211092a000c40300c0308680c2d1600c6001d082c819044008101104407043d8000c05100f802206070043e03003680c2084c41420341001d400c00c01000194455005507811036020f4052511b42282e4101804d56454140180d00d907003540058246030841025020000a15003510092600308001000a20401080c810300c8c07850007440041700b0316114080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 227691735 1250 227690485 227690549
    0x4020304030513081e06040b07260c03100b04030510020d09121106070c030804080a0201060e10050901050d020d1104110a0e03060c03010302061b1c030f0f02030c04 72
    0xc0540140f9995500801e41c0c901030660205400c10880a00c4000b2031008244d492003260055445035503038440b407004030b0700c403000f0f0050000c12070050959101d0042582d540d050054420f100040d85a0030801c2c1c2c07181600302141c0c030800c3d01003800c1004100080c80864402c484ad0400707100180c96100065020025049240f0000d1204009017003400301c1c1ca4000016084c1d500350902210b21070344e15203c06a9071380500c2d41014010601e11400a400540c244009006512040c80046800e0b80c1e566072100c005c8030240d6600c450f11004070130600a604105020f2030040404480030360300500c0c250080395002304081ca000d4030690020b101f00130f175915150040f10750310b88500c50007980c1e001204da0051001c0700c0308007654461b00440b0040b8962050f2201568142e9070010440b9107408014401680003039031101601c01d0074040c0b858058401c0700b000346001000c44031134401203444000c4460110855948080d62038042b8410310900260708000c000b560180c40c9242003030700710130108074404c481c0d0b40600c2e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 227692985 1250 227691735 227691757
    0xa020601260619090f061e06060210020c191410050c1803120f040e09030306031c11030a05040303030509060115050f091c02031506100e1f0f0f02160302040203040305 73
    0x52101c3ca4104034680e0300480a450790702807ca0b004901180700c00c020f40c0d40c180b06007401603000400c859000c8500346d00929901c0001750031600c03082c814a100000358550b980d419650100307002c1240702c0a41c010320814001c0000d40000300860315002500042c03a000c1c440211080000041c00c80300076807000c0000301e22000c0340090a54036590390004251450f8003034010b540e1307030500320401300e50480000000d59000340390090241103158410001103402e4204000c501d020004c3d85003040b0520302c01071004000c2d603c40f580da00359940d401c6040140694401404011559020000401580f40f41661948d109002c17440c11a030f5035950352082c410703035025441074035a108601d4070150680310000800c1c1e90100e8420740a640c4a0f1443e451000c10340107085503416042135103044204150707403240e58602645d10b4014025030409880401410301340409950a40200f0a09074040c00d80f942c121414bc2c0300b03c0c20f10310043c50300c03006e00003201d0800183c03440020f004503000310109041600420543e000c10b404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 227694235 1250 227692985 227693003
    0x212010609020d1a0603131a04060515030a0b010b030703020d050c09040b030607050910050706140a1b02120a140d050114060408060f0406110a02060126061909 70
    0x200d407241070095001004484580307107840a8501c46420071031810480079401000715095580d40d020142100e48416801c90b940c2c058003900c0400300302041c003114021406000c0c0020b040c503100710075005d14101d14a000f4170035407011004200041001c080e15041d540702e181d4094690b203844ac001e402a014203140c40e05024101010400014100c1020344214081204c1c1403000c41c803100141034070b8540995101000540401a0a40a0520f2010980b60704003d01c0c0a42c6480055260102111800f1000e02e280c00805c01c00e00800e07170802d005000c0e0110f203c07075204107035211082d0302a40c1d4200e42079441274a11808540c0c100b1240c0200ca440b86001c02c40b0661a5071000d0500c0180000e1100340166488602186001c00c50f81c105034040d00c003542d10000c0101045e4950b84807101c204140100101d0b64180c4a1a03903001645015000c4c014604003500108810350604800d5214620b400300d85921815030f400130304481010010f110b64001d440b12a00403000d06011010030046c240c0550040d0504813 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 227695485 1250 227694235 227694239
    0x3030e030c071206150e0a0905280515070509010809011b020a15020f09010e1909090c090b060301050d08072405070c05070501030c030e0609070806180a03080402120106 74
    0x1101003d10000d42d01c10002004403000300440c0565114080c00340d680c9403403400000030861402a80040e050900640c00c0b1401100c1d0044078041444400581c0d10b0419400100f810400c01e0800c1031900f01500008054500c1c9800030001305240142c5040d641001440d07008601144003e50010524008040c42116100d0301070f00701960726014014125100d81e503070035100d506d006043c420366850156018000303140c65403010044a05d075003003021490303001d4580711000c544003d00c03c9100008041c00704000c5084041c03401c3c2910407004580c452550705003000410786140d541c0d9001c90381940e4045031050b02140c1182400012401030120050102135180c0501c105000b002c01e90380c1c07a00090040a0090780c0d9580400c49107800070309001022580000400d000750341c01b941281d0810180f61a0005c1c4842007000264540b41050322950041d0700a26814000d81400f446403030b6121a45000300280c001188006a544944d01c0c80040c0030011001c012404647d0f03a11602c24405194100070301c2075903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 227696735 1250 227695485 227695499
    0x203160f0533010b07082203120306050109210503041508060f0f01020a0b0612070e1b0304150207020117090715170105090703020c030415030f0902060703030e030c07 73
    0x81d5042c0e032042072100004502810381103980400905803032000e401c1c181003400035070300c40c02c0303681204480d075010704103402c0b425501004021110000b10701071101c00c0590803281c2006001c84050381c000c28100031301e0050600c0300b9810120354103070b641c8404642100c1d45100e814081d00f54001d40d007209120070143c0044440a070341c840e0150b070060804569000070101c0d1001007200030701c0c0e009141e80c0542c000c40300d01000300d00d070248038541c4003030040d003034640c01f0303084011040c10207000780c11a40350180008103200b07100d51140384420300b10f05240101481c40c1425190003990354110440b4000790b603000034200045910178071080c054006114281e50140c18000e14040d26513105000e00c0764015080254140528810313110201d0000c60251176000707607400c1400380612507030010702e44428035400700500c2c0b10010b420030003080100009092441c11500408005080c0c441082c50640320a0410710b01c0001340e51444102c6001543c035040029401401d080d485003107001c1d4400e1070043d4060102e0000b080c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 227697841 1106 227696735 227696773
    0xa140708040f140304080102130f052b082803021918030206040605030115052803090606080109110301020c0715022514010f0203160f05 60
    0x4500d42c070107081c4c610381c015808261240c2d1b00083c04040d81407141d075480c016110440c074602d0602d150200003158800401c000184d0840740c2d000303009010704051000c0c1d5001d43d11151103a240c0180e22401c0e16043c11050707840c076071403003071100c04400c6911901c00c40ba403081522285500039082000b003112140c0e401d9858121400c12210040050703581d00b000341006001c035a65550703480d810000e0010402204180e414207021041c081c40038802e0241c40361504849514010010701550210110090401500d000d000a8038160020070f015031706400c16409640120840b4490b21481000d05080703110360540d23002c4c6500184000d11425800b0801c01121400a1044644d41d100140303a0750320219006080c0083c51801503404c100007200d0310060208440242014985c0c5548408081d45912406155580c9008150f8100e0708010b4a108132640d10740d001400c07a4a90031076140d0301108 = true := by decide +kernel

theorem cover : BRFrame.Cov 227517985 227697841 := by
  have h0 := BRFrame.cov_init 227517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 227517985 ≤ n) (h2 : n < 227697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
