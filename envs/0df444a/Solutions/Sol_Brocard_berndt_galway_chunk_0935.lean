-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0935
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:06:14.534438+00:00
-- url     : https://prove2.me/submissions/b3512dba-c07f-454d-a61a-e46d4b8b9c4e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 167985611 ≤ n < 168165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 167986861 1250 167985611 167985617
    0x60616021203090a08010203100501030e060a0f06090c0203091011070308070203120a05030603012717071a1603060311060309070f0b09011d060304080304110405040c052809020a 78
    0x44020968480314540d005c1c208800015031030303003440100e04000c0951600840c0c1131608080e202980da00700015130f40d600105030b046c00704001c50420344400003003080b03402c5000c485041c81400511240c001001b0003c0160560f403044000900205c1116849101107200c90302c0e030040503040002c06c0200c4c0241042e00d00080503114a8088081c400c1c00951100c0181400304001000f0003086280038401c8030a01c0b9500034413007808030340814000104206d4001c0050203c0300e13a000888006600c2c0040e20800c507880003520020312080d0740480d40e501c104270344116030001d00c01c144a40280c4a4000d40044990100712960b1016074403040002c1d5410051040b0800e2083c06400514100002810801056094a0701d43d81d02c02c02d6000605c4042c07810300440d80302401042e8000710b52a048222540160001101603d980b2180b403e00408204c90800c41c1d0b00c00e05003424481403080c1c0d0b0500c40102c0d00119089074020820f0111f000721400f08240e084883c2407040000c01c4101c2e0b45800801805000785 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 167988111 1250 167986861 167986867
    0x24120702010b0a090911190612091b030b090706210b040606050c01060f0806011502190b011409060d0201051e0d140702030403050a020126041a060616021203 69
    0x105030f540040c0d9104400d61600c482c1403106009509030310906081c0705031251210440a126195004400761181d9401c0040320a500440c00f5500e91020343c04035880704180203000c001c0c41c03900d0030700e852070700098480b22041404200c80403000035146044132040c0e115140c030240300300760012850913011049025a62a030200d080e0301d503a03604c83d20014100e140c6846032141218211542150540d8000c0c501004a0200174862904000b03020f0781160500905039a42d8840054102d0a241c80c111140309000450501d12040003140084103060710040b4650341e010300440001c020000001f9203038507800c2460281e0060140d48620000c5c603141c81610603200581200e0440c4154561184112054040d0395a07000c02c1c0c82c10b240906103802041c10300c011410701c0e01b0341e15100c3e241c40703e04078000d050282d0600198004c80090040d20303480f4200f92003840d014a030904010000c41030580c040880480780900103030f06490010700780e4030f0303107810100d8000d80c148460307003840040800040c13100d002d44024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 167989361 1250 167988111 167988131
    0x60f040608060a0518010e06010b030711030f0405040b010914130e492102040815060102070b070f0c03022101050c0306060307031d1204052412070201 66
    0x10002c550107075003480d0000074113142c40d02c200d0340c007000b2071148400310740d0400d50b2500c0d0b05072000500a0544c0d14003101903603030344c8520710f00751581814101d0154442c000403904640c01c52006025208861058806100c00718115004403404400c40c0a00e07021703005030894000c01800d200248100030b0002c0400014502e9000c0195441c0003204182048046000c4602d0903002d15251441d2881000081d4a100340302400c01081542c0055542c800c410424116015a50805200c02c00c00e111092501c0840d5140d4850070119252800701594040100010f03012580c0c1e5440050900c007264151044c40742801d0f901d039580c810f616a905416120511603040120242c0e03036185034801b070001130480400001e17402031019401d4680c0213014401110051080001988904084030743c00a55480c0019a910908040d015001003521040c07200e442400f2522247e42d102400500a80d10101d0388103c24041150b003404404080c940c03810350401041c05030194000c00c3d402643d8125280340000f09255290f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 167990611 1250 167989361 167989363
    0x51305031204090b040207050a02060d061511010c09060e120f030f040e070306060e09131a2205070905040c030b09071a18240d0c0206090d0206060f040608 68
    0x2201d80c1e103a2031000002800c000349000c51103442060313501036800350305010b80e6454050321603e18600c0070b802050b00090711030b4000c005501c510041c164503d1b40013503070f14404d100141002c41e411480843c80d86011140220640141d1100045a1143e515005601010000d0101c0d081005030031101902c9550686000c42c2401e201500d1440c4146180c80e0b111440e0001e401640400544404181442c01341c0900045501074900c0203401c0d020342e440b40c3c0a8a803600955000b400c036000152048249640c00b424140300140c0b1a401000364021009240703842094040c03e80701007540041c4190b02c50001040145101d40096030301901903040b0b220180e035292a14107094030111440000c94104260501456030f40c1c20406101100450b902818201d00b0445103d00911140807135116064100014000c1da2040410380c02d810300141041d900d81e180e07141d584000c0c2c15000010005402003070001510b240b4001f900034003189895005140380c0e150031003480061200d001c0c1c0c0641181e21040c0208036460 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 167991861 1250 167990611 167990623
    0xf060d1b0e0108010903180612050615070f050105060114030414010e0619141512010b130902030f03071203020d09020d030203031e0c0f0d0b100c050d08010e010605130503 75
    0x1200c400042400c01742450700800b0303c0080310800181e00152082400100c1c3e02c1880741d101030f6013070100000c213600c411000408104080e002c0c00c10707003140018468204400305040c1c3d00d100788600020f00a544818005540026107142007091035082800000c002c100030f0740b5000300c100403070400040d18240e0710b401c0d2030906600321590843e42010300700b0015210154492003e0074140300480d1032031400c2000e80210312400509a8038440c4040c0980b9a0220030294815150980e0080000b0348179600740011402820030070105a100740070f15090028400e80200443d032050f03a00010748a2520007008017a0001d405c690b001e0a0700950303810f00507005032640513150744080d00a40041d603c1e450850140340102c0c4003009a0615050002c040c40232080400091714a1954441e0020340c440d01021061801009044803140d8009112a0011003868208020000d02d81c0690192586154040c0090b28031280038030801c00039113000c800400ca4540310b070300a0310104100441e090007050755040024507102d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 167993111 1250 167991861 167991869
    0xb0f0313061d06070311030115121a12030403020105030f130812090f07060e01030207060b0406031b080c01020c040e030c070e010f23040c0507120207030b0f060d1b0e01 74
    0x4650107000c245140c1c401c00100e6403103070b01e501c0c080c030046c10004200102400180b04615036624440c00c502c00880c01125000c4500b01b110800304500040080403440c4151034030182c1c0c0c0243c020040801180300048115416207030180c461a18503101c15081c00d4580c0d2008041d000c035140c20200c048001050342e401880880044400304c1d9441c24851195070400302e00482c05040303644000400c02c030703213034020760180385612007401c0050301e6808901300395016040c6100200d40c028a4020b001c8200500c50f030034021000300300300150603402c1d1a100e01503620340070041c1413405079014100c4a8101c1c50690406000701c0303041e50a8030304040001c14424a00321241e0418003840d900303d80140300e0440c019108070014080760220519142e00701000000c0410700030390850045846c1c041c5281118050000c0310003d503400300034002007242e01580251120310a0000b100c6004c280c001103005a1169000140105c1c40146442c0e00c5007a5641d8600318020005950207480000b0500003a011100501c014020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 167994361 1250 167993111 167993141
    0xd0f0503090109060c050604061109130c030b0102061b03060a05042309070f0e0c0705030d05060f0904120e1c03091a070c06050a17040312050a0203010b0f031306 71
    0xda107103800140100420f41c000f841000702d41c18214000c120000741c416009500940001080021180c42803040d1042420303c6412058101c104094003000750701180d82c0c80f1466408000c607c07a40001262a40b00c29038103016080240c90603180c041c01400011074000e07070000d02c1c80d0b070920780e42c0c004242640c1851406072001c0220b000740102083d59240800d500086040181c42a03a04006040300071000c2402240410391040000503480c1000b00c0c02c44202c150001c040365211501a01024082c0030308807042d5010b00c520000442e80c500b4079024007401103a100c207003004502160b0354101c0307074521000b40b010780c440e03882c0507504044002d1900d85418603010b6504c4405803401e01820b00e140c60f801750801c1c000c0c030310308204960100b420300d081e107030550b0317028641240d03140740e0302d1000c0300c9900300091420300c03541113501400209a003210b0500d0b9040e1503000309010b1580c6212201c1c00301d0200b441881c0c01c0400401c92200b60024101c015a80084140c0181303856207425100c020131110300740c100b0742e00c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 167995611 1250 167994361 167994367
    0x606031f090908030402090109021905030a140103140106080304060f050901021f0605210a12090b03010b030f07020f1002070305040801020304060203061801080d0e041b030606120204030c12020d0f0503 88
    0x40d1f00f800104a405030403032220a40c688505030001c41c0c1d50180f401c0f50001008000b0001c500d02910395040090703c2c0c0130075510601039507101c5c20890640c1d00004c054506940c42c0c00c1e80012940303004401d803400c07039840b07460741c024010050100351a2a4030085020381140509983d070030302101101e032101d005007807508001403039034104801c0c440101488010500b9940a101c417074002d0690018008007120b900401840d40201c40180c2074a8a45082d0000c0500300b80200012072346565203c090f6200c0d50041c4104141030300c030200c040c4d84a080c8005420015003001c42071580050442e0024001c035072082c505280b406588001c13040c00c98100f0344040b9030091700082409101c0c034120b1000c020500c40300302a09820b51614030b103296204c1c0c20700d07512400c3c170145840c0c035511551070b6400350000c0c940000004d0486103210341d00800403d0b00c1d004110114140d1400c0380030b402942d100741c03402d07264000f05d008140ca082c603004082c43d0b040c40408a0340701b45600203a00c00145250b83c2941020b20410096407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 167996861 1250 167995611 167995613
    0x20c0a06150603050f010308090a080303090a0b060607030c261303051203090607030c0c02030d080105090901020705120d09020d05010213090e0c01030e070f060503010314060606031f0909080304 85
    0x40c001110b6000c0400c1600705000d000e10402d034507542ea03044a600040c001e07070382c0c1c003402c02180942c5900d80c03109002c0d00000c070030040c4109003c02c080704502d214404040d059602e40041203028003440d00080d00082112203a03000140241d8401559842d0784018144c032180d080c0d4916034a640710050000d158240c000d0b082041001c00c0040f142e903811080703000c40c11440d0002d40b10b903841e00c00804007020961900240c00d545c3d801111120269500603082d5426245482c2c0040c108440c203200d03a81c02020700c0303c00500200e07418804c1e13840859001000d80f884180107228085a50410390f019802c050751078860000503900e04031b00d051554421400940c41e0191844114042c201c00e500040505007001103540104078003154004040c00c00b42000035000d4102c100407440c100454010100101061001103111604400074504891103004041c80e000d6030102d026440f0003094440315007109052001c6951001d070840c000652500c80880b55944039919a208002d60b02d94003c00c2d100300000105001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 167998111 1250 167996861 167996891
    0x1204090f0501150c031d131d0f0a030309020a0905070f08090a0309090906110408070509060d030e0621010905090d1d0103020d0902030304090209100e1c030201020c0a06 74
    0x42e0040051091011001d02d1040000c4d00c0038040090050410110b104140440208403041000507035001d80803039203030304405040350010a51410307052a80040e4650b040f2018a000959200403501e204c0034041401641c1c0d419000341103281412a800302c00c0d9000403520ba185031240c1841403c49683c1c1c000001500140039210041c003800201d1947c0122884001094003c20351030120b6242080019400b01c550410000801004826100780b4000103000030f100c2d100001c104066440c2101c01d584182c403482d04100d220038407800000d0100b403981407040001c0c41c3c940c01508800c007601d00d00c01070801c0000c445d850005400d81008000235964401c1c40041c0c0c50401001c8101205410800d11f0900307140610801d19424001d214100b51f00014144582c03880f5800800a00358054102d030345803030300c0d6000900a500007050a0340a00d0b10310b4a17000c0114861200b2075402000a05201a40702049188499407180c41e0401e40556408001c141d55000d0b0070407000a013940200c5000030b00d42e082002c14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 167999361 1250 167998111 167998121
    0x7020f0a030c0b0f09270f0105180c090409060605030c09130b280c0e01050c060c0306010c0b13111c020603040c0302031906050a0209011b0302150709080d050c1c021204090f 76
    0xc00c40b50400400500040c4c850ad541c03050544010040c080d010360b9020000300c400d204e00c881e007a03042401c00140c0c104005c0140c018809503003040b010b80c1d4100d09070b034080c08003500c01103602c89100360180d100342002c0303002120a2030704030b2480e41d4502c1028922411848100f10b04c0d40000703908a41ea10754040c041d550042c80040703204c0d070900e0554540071000e814141d8a54000e0503060b040c60001000c00e989070302542e003604110303500119401e15494869941d4285480403502914030f0a40750700f81002600d4600040742110a1030685400101856000e21055810040c8111070183c525913003c405664200114805041e08000180455070649840b60590320702070000682c0c1401880030180a82c2c0052210007202000b000c01140c0c03c0c0c84e410120314100c00504050003d018400900500c954842c40c140c00752810383c000c542440c0b52030041165603114a0310309210903003002844943c29404121b0003240d0040510490340e03c40041c0c0f420810b158005e43c80198615503c1a100b0b202c903c4078014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 168000611 1250 167999361 167999371
    0x10e07030b01050d05060f150c160b03010612091505180601060c02090a141f05060f030121050105090d0207050a060c03050a210207020f0a030c0b0f0927 67
    0x520105107000e00103003640c0503003100700380155256400101700352a41da0366820500801000c00500d001254040545544100e51018050003144860b204450706404100100c4015403419072841c0c1c030302001141c180250300c08610301c598031440d185020440404103842c040716100c0303000480d42000102e40c181c16114440c16080ca8029000401c04a03800c10544000c4c5901520440d025688000e0104000c02c05204100240010071052003d400c52000c2c11200e0703400600c840103074058a503010080c42d0302030300c000640c46490400040c8402801e845d513420200f03607500b5500340365000c03030fa80316030a4440403240c5903269400040144031082c0c0c1040710038000d00055841078a0941070020007408400c0e9518040c003800b600103007101e0800d1040f00d4404081c913400842c3c4e007481e002481c007640654006e41c8140d00c1000f0009801c441031034906828400c0341d6110b600000c040b40303828842001a0402403201c06030700300610060803942c49001d4260f03c141d018800f1130302d070400403181a040390280682 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 168001861 1250 168000611 168000617
    0x72d060305150d1709060c0714090a02040308090103020f1921020708041a21041202030a0903060b0301150311150712030203060a03230f0d050403021521010e07 70
    0x4103400700e100c040d480912044d58000c4a56203645805c0480c0b410302ca841003054582c0b10310880013410781621103101c416203d0407901d82e0065100e409240090f070080d0300010340072100420444010b58001d0b8002c1c491301c5d48150505003881c662411881d210040c0346600404186c005482c4c010b8118510329401f68055107a4045003040303041e4540b40b006000f1030160414044400d51007203d5000300c4130a94010b03000b4004261000942100c409203001002d64088585404500e5002000360011064034240c10107036a40090581c034644401c0013a0002c01c0344a40c055590340d0048074810072645e85800958001c4680d814022211028419039008119500c054401e0a2201c030340002c40128007030081005a24025880b034550030700281044a86520040484010f42c1400300c9005440440e4000c06924a041e1480f018203900c4c919113aa810440400015404120510042c6000c030700480d0340c41c41c079001c200d041c03d400110741d8101012502000303071040c118100403c00701c44001c4407260302500c945 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 168003111 1250 168001861 168001879
    0xe060103090f080d02040e012312060609040606090e0703022b03030203060418120305220b0c0417070906080d05090904060905250806010503072d06030515 68
    0x91180b8009141c1400002c0c82d01c400000c0c4103030140b45580513100500b0b02e002c0007190650b5186040e000741e80341c0e044c000d92080c040c4160828a4900301c04192012040040608015694030b010840b003141d0003001100d5542c0d030349801040500720761081c0302090020400411741282103004120000002c0000c4620006261038082402a1010111403006034107007400350b12a11350700000b602034002080008001c0c600030b0000340510036000300004003590075850402c11030302c4200b600a41946144600340c034641e80c0c2c01035240041e403040310042d441000110140d0506889006402c4100da0a0141d62440e902c41c0e0307018044404c440c807a1030000e084003401407994007101324020780240604400c2501c500d68100020341402360780c0c1c01a0090715807103401d8a80701c10810912071025008145001c403c0400c0020120380c0f800005007090590b03c00078000c1c0012440c2800c451002c440782103c0c41c008004031100b01f0f030301d490015410b80c003404964402003014070b040b000080480c12080361082c8118001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 168004361 1250 168003111 168003113
    0x15030a060819110d15151415090112090210020f100b0a03020d11030d05030910140426030c07060b300304031b05150c03090919090c0e06010309 63
    0x885000c00c43c411040c2c5003d48249500e0900041c1200d00d216550010350901c00c0380080143c041c0d40c0101500c102e00784480e4800300c034a060146103c08404014520001044810095802071041c1804003070f40078004501c8810030390218107801011402d460241c0e00034004080e4000040c041040c00040c4900d0800482003000005151081d5034807000e03004400207a03a81e414003107100b51100140d20090111050042e4900c0018501d0340102d8001f05c45000303101311101c2000c500e020700004d1405180c6090129240e5840781809004540b0b60312580120360030381c58001c1e041000145d841550590116900c814040c144142901d12040d15144103507616042d020000448030b0070f42400c0342c0c401318204003000d40d80391040d2441c460f42d000035124601c4d550081c03c121001070a90415034005403110bc480075003490050382c44e40070390001c082440c1c1003030080c0c2027141480e01c0c120358004828004600c0d5507810a5003e030442c2c081c94826601130788000e001344042c181082c00c95410160a00e403c10011400b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 168005611 1250 168004361 168004373
    0x18060302040e0f07060c06020c01021207030b01050a1418090a020307080a060e040b0901020409020c0304081002040e0a050408090915010e030d090b0903010906020a050a0212070c060e15030a060819 86
    0x14000c0500b81b0212007001c0080c030620394191448914080021035690a4040000c64403400841d003100002c0d0800703141d100e00b944030300280c44070004036454034803010390071400c01c6007681c010030850000101d0001c1903c030950f4543c0440b074003941d880b8800580e20f041241c0010185080104405851800c08404001c3c0c8003010070060b501503044904000d09494940526000e0710603540400055400800d040101003004001071007151100310480b0341001e01c0140c0302e003e03800750f4816030a1040000c0006580080ba517000140d025105072082031420f01d00c8000240700c54400d0760280d00c094113401c004041d558010700c3c400c48180c001c400821291070f05030b4004061640900130300810000102d82001c8544094103c0c08400d540500700350f444a401610017055900641c00c034000600c20100c50860055002d821100701c99040422003201505000341500c50b1041c0100b501d40240103149100c0403280300901450203a091001c01081181c43e0005e12468141c0c801015562038030520148000184 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 168006861 1250 168005611 168005623
    0x80d0608030708120426091e03030f0c0a060c0908010506010305040b060103090201020f1212010b0301031505060105072001120b0d11030a0b040b060405070f080f060a18060302040e0f 80
    0xd100c58840b01a03881d49000d07000121007140780e0500400e400020303501e02c1c2506d000361403800d00a881080211014081e041100303580d12407081d4154000300110003411003000700400306138160b4402c840542d10241c0e1100101d440c0c5400c0940090f070b400304140114103080c000c8a800c0b030f009280501860605850311014204046d120328141030740c40d0410401c40e4000c0c0b00d09001007641106a40e00141d4010030b110160348400d984404000b000380002c80c20591480c1540d060f40e4000001904050030000e00000611020380080d040c04001d2249000140003996035416001c403042d50005130f050b0840015148400503568021841d00f045240541616010b00c0026504d812040040301c60342e40c1000b20742005c9622101404a190810411051103400d1243c5030140c0810784080009580d5024226001e64008041c040021b0303507140851319000c0000140c54200400905401d1030941d241e441c1189484e00a80401e40a62161002c1040d46891f102d84180c24038000d000d0000150b1503962542c66003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 168008111 1250 168006861 168006877
    0x203120c07150e28030b0a0b090907031109040303020409051f060f0503060d0204061a0309060c27040e0712050105010b0408100f090606090506030d05041406031909080d0608030708 79
    0x3000e42c081502e1601d0308541002c2c01540c1001b481c1e14142400c58485000d8101681d203180070300d03e0180429018a4001640710440340c120f0400110700aa88081014009000c1d00580406400f03000100302d06038248a00e80c05106a50b00d6031b802804446101040180780354090000c0c000c920040050300c54108046a611000880c2d0035000a00d03284000340080400390080c240f026240d00701c024581d2070030f03c000c50141c3e190f002100c040e82c5e288141c0d40201c0c410788040d030210441c0062102d0041c081124440c0076490010004074611f001c80061518000080c1e1000020309000f20240040c00300c2842010301410140358018685400c04003210b03920a40350300344100070380d9a501c15148109040d88210802c5901c05014070003a0b941e54080d4002e028240d03038052003401a000c60b200d100c3c0c05274085400701c640090941b044550700c0c800f00310700c540000740001c0c1468101224894080c4540c4600c5801034800d030310080c2c4a8440d000d1006c1103d05e070380c01060b015481040b016010401c6a400c0c0d03560f00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 168009361 1250 168008111 168008149
    0x18090d08070807270803030c040305070806070e10031d1506100207060f03020909041401050a140a09020303040b070501020307120227060c01050a0b030f0c0d0b040203120c07150e 78
    0x306051a00b00c13500c1e00d0154000c4c0d6490002100307010140c1c20102c01042201e009400b141c0d400340d1608185501c552040d00d03982c001c91500b08652101c1e0030044e146240121080c180021000610080700c6000c0014244000c450f07005400c006c103080b00158140703508040107840c000c480d5100712201a43d6a14640151024010101c036640c4c1101d00c290104c5640300ca0142403031006082c64903164000d40311940b240a50780d42800c00151215100d0310503001d201d51014100001c5460300c0a16500820540d43e099070140000c11001c42c515980000070070740903110320700050780c030b00c0d203014010807000d40140c10780c098900411812408421142d13a0207682c1d807085c10141d0600b03e6910014078a8402c540120485500744030400c11581d4465001041881055091f540c0304a0406207c0c4d0703c1e03007c1001400e80c0941d07861004030120b034001400725405403000e0210342c1d5000b00d26440180d6904040c8982d0105e900148080c0a8040380d0004040a02c03031508006140312500000180604144201c41d132070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 168010611 1250 168009361 168009407
    0x91404022d0702040b040513020f010201020c190209060a0b03150d050d030c031109030a0f0204020c1603050d0c080a0e0a180f06051c03050918090d08070807 69
    0x40c00c050840064405080e404020040d00721414001182c0c0c20071942648110b2402c4000011820b01d8001c291282850311480f1044500907400c00c8a4039001d480c04a04640d400c0c040900d011000704416006280045859034035890075104001c2e030884024076050051600030010040a403494043c1d036000b010000a480001129401140303c05200304c0010300640b2071480d0300d06546402d42d1124481c9201550103028032612400c1c2a0000d11510a0841c2c06a1100c40c47c0808504c00503440901103100910151074042c51030001441c1449401030081d03a04500c0d101001000801c00c960303140c80c5d0711070902038140f54040d21903040c039001d050b40300c1c1d050001645090389035580c0c03006031402600000020520012080300240018003003000001040c07032800002041c6031138003f000c00c0066103e03c00f0842c040401d40e80880b0785070003804415030860b11340c20b9544d10303100b0090f02c410700c18100c105c021b060308144100003e04a50010b01a601484205400c5c0030000d42e01039070f41c0148900500740240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 168011861 1250 168010611 168010627
    0x30308160c081c0b090703050a0c020c0f040b0406030c081501050d0b06010f020a12050909060a0b07080a0e1f12090201021b010c06111308070b16061d010e01060609140402 75
    0x1000c4c110181c2d03000e502c0000071080004064040d480280208031406082003050740c03403201a641e0300c00c1d1507070305580000010700036105840d02d80c02c01500c01d0005440130900035079940c0c070400940314941025060b40c108070500c50b0081880301d080c9005220445010311504040d03140e0482d403020142413181000850b08101d4251402000784000d11907000c1c149225241c80c4400c028401d400007150540b00b540510046070743c2d490100011001da13584c0d8148945886147d56549440307502081241040c04018080c007104c5685030044005c2d4510035006a0000a0300c1910040c98003010140c00d04109182030383d802c0150b44d00255030210000f000c1d0032107561a085000507561180900e60007030a5a04101103842c4c80c1d0706c008042c10254041c4a03007040559112050315440c5e92890107070034102513060140e02e140c400024503898580e40141000100300c0c2a1904481d1350003840c0324481c14030713911140340c011301510920038003009064a1400304425414104051048a9442c0c8542c0c4980d8010901d44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 168013111 1250 168011861 168011917
    0x60106050714030909040c140d050615010207152303040c03061a092509060f08151f112803050c150406060e091c0207050307030308160c08 61
    0xd001d00380c4c001d02c0c1d01da90b8035161400c1c0c00c1c41c400d6806010002c1000390780c003100754100340303a0f008d4540f1b0b4000d014101640e03c0c03a980b4540307103840c000807504520400400294076050250b03c00c02c00038565036414081d4121003c80313000c2c9200d05040d0000c240c0100100408202e803a00404162130344000007055a041c140031052a060000e2200da50105400b0300340305c03409034198442070750014401074041c25400354180c1604d54240c14072400010690700c0a5a54145204581003540000003c001e10900a0094003103901012407281c0664690b44410304d030842260003d00382c0460740c07000c0e00101400340c0403001e60310608100a605240d4811a110200e00709400b810070f54402d07041c0002246d82d200c114500e40501e009064800780c5001c1d00d00400800e00b030000707000d424403644d0101c00910403880900820124034141c07550032811800b40c074001041079030713052020b00b004600a41d14115142000c01580301c10b90340d5010700074103000d80d203030310b1a0010349a130b42510301c0304410704281000c0c0700c4012010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 168014361 1250 168013111 168013117
    0xc0702150f040b03040c08010207020a12030903080a0807110102180108060a0506030c070611121503100e03041404140118021c090605090a0b0a0213050301061d070206010605071403 79
    0x1c010741040200b0003003031682c0804040c502c10307405030b110382d01d0b05655040d80c1c03800c0b845441c00203234102c504180f091205100d0080c190041d103210b4907000078040c4e90780e01c072006590003020138079000400140a201805900c240c0903074030110040c0007141742111014241c0c1006413080e603160f05000a200008256503a440c05070300040c013004c0e003010350302c2c07403c20143c0160ba0f00c000030465099140010f203440300345050003600d6948440101c010000c0c0c4560145d1100000410307012039151160380790300d00108859004400706404440002c0d82c0380c07420711008580b070743c680c1000d01d40a94034014040042610200000b811100c00707000e1460444982101d21010344505586041710410901c03400c240e031800d030b03480689803a0080038104040c0c2c03035000800e500c0e80e00003080a0940c0c2080c0d0041030410b6031580c02864603000100d011164155918082400e64016610040501a2510350f058001008003401940041284090000d075030411b2405020b03400b84000140080721412250b2204035010022 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 168015611 1250 168014361 168014377
    0x90601151409041815060305060117031c1e2a0207031b05010e040b0a0303030c03090501060810050c0c030f0a0e0d0606090f11030408090a05130c030506090c070215 72
    0x2032204441c14680a2040c500310042203403507108032211750268032030521843c01a213034448007504050340b80c008000075024030f041c01e4030031500082203900b4441d800c0c2e07103d18507070780b98454002c41d640780404100c00c1c00c80c1061400303101369410314900c03c0410003e061040c0c40000e980b42d6021410504540c201e1406205030401881c8051445070741c10f00d1043c014907241100d400f6a81ea4051030406820f20054910340440c0e01d03084403e480c01800040d000e034020000d24051450001030741d9259440c0d4a081d0754050380007045030307003000342c10111480300d81c011140e10003c1070308100e20740400c4800280d920701c00c440c18002d1121010803446602e0f840350030000d1502c00c00910f484403031a41c5041c0303c4002d041030310034000c2e2a0711781041c000024009005040b05c850840c8410350031681c0740e4890b000d4a5020100f5541c1c0000c00602c04030b40f50790740910741402400c000c00d0000314003e0040002e411124060501d5201d24040e1040100114030303a0201e5400c0ca90543c1c0c5288542d1350010703800a540a0445 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 168016861 1250 168015611 168015619
    0xf090a0b0103140c100c0b06063006030109022b080417070f0501020c09060402120106020312060901030c0302010302221203081302060915040b0d090209090601151409 73
    0x100380070040110540344159401504d0011240c00104007000c00c0d944400000300380d40c03016074004558600603c0e507002c038014045ca0b01e4056644001410804040000d422020030b0b03c41c10805482030700403030343c1e101c0010350080011425a4000805041c1c2104000c2e81e540c0e00d000001c403060030040e0b1020070880c3d210060544a076240d14807131410458032914000c15105100e800a1100000300e021422260103070050104c952602c01132000040c3c0040c241343c3c100f0380070000c6030f09003030140d4140c90003407541d07601454440344001040003940401521300c611900080b801440403400701800902181c0e82420010b81e0b880182c984004265241d07140001743d845040b100152600c000400140601d1290350303407180319a01c0d026010491103280c00e0207134200000b80103c044038200b203c040d640c2480850826410f05070fa840310a2403e52103034082c1d9850603114000e5401310304007050b040d41c202e05c4e140042e122560404041c207203010301c1c1c811b010741003088050290301c011080d00110740030300002030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 168018111 1250 168016861 168016883
    0xf1103010207061d1506100c150902011103031b180406080c0406081504030e01090b0d06050a050f0f0105180312030103050708070605041208040b1602040501120206030f090a 76
    0xc00c0010041c500072000c124130840040d07100100340b9011913410752125030700b0582c1d0100d40f60700301480005001c81c44407006100d80e120198000c514403031068100c0000e400741c08a410038903880010480c441094410030a544107000b40003520101014101e10482940700080d00c40552022410b200034404400720340062601401203001540443d002c0d8051200b682e041c05004d40d218030315036490000100c802d4085130340d90041800a84074003401c0145610515012038102e85402d604221988040d0303083e1140d070703034481c001c22441c14040010300c0209011110241c0d118103800c045100c81031401c881c503041140000e004a04010f0721000039520304005411607403980c1d80c90107203c0840d8028041590184604140010407070400168041502e030103559050805103086082c120b45c0640100071980e2240c02e220114410340311801a0031403950b1006c05101c0c000081c0144070498406802c4410542003260344140940c4882c0c0c00c0f40c1d0041110307010b40306280d4910340c1c000d0400042c0c03040103109403610 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 168019361 1250 168018111 168018113
    0x3030e010e1008040b091908030702071707080c06070305030403080406060b04060309110a061e02030d05042f0604030b13120804061a010f030510090c02070f0f050a030f1103010207 79
    0x4000a1083d845142c0c8000e1725150380b42107543d6203007061004001040c0303010304440002c040c2c2c006141c00848030700403600d485485803418115044094900c000c9684041001c00200b40d040140d146220400d5801d41c0c41c20070b55840040480c0b00040c0050140002c0002207400c0141c10340c0450020058200032944031381c1c4500d80180a0310f46548140c0ba000c10344ac03420f4141c0d1a0030248a0121442c5407240309400520b00f212504259080c0703a10380a501090007007602003510350040611071446103e5514400c101d11120390b1074501e0b203d0b40e40f142c25100c0c2124002d1078484c2400c1304c0940b90494460401a80c0740d12030800c048014610050405500c0c2c02c418142c0e0707800c00015030049109041c20f200c0c0c0c0e2201d41455440494104529000403440f40d15015400e000f60321190300b00e26410303e2015a5601e818401c0c2c02c2c0c440400f102401640004002c001c40702030320308040c016040315690b08007100e2826000407044202800060725403a01801018100450405142d5000b80040c000355150151 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 168020611 1250 168019361 168019367
    0x31015140307171806060d08070b04080a02060a0e0303150d0203030d0501030b0906060907030f090b0f010f06030902061918090c0801080a050d0f020c040f020a020f030403080403030e010e10 83
    0x14840c0c0f0500d814030000030a204511000d84105083c031070200504003070391080c08002c020701e4054015640c83d00100041e1000c0760030404400d04c03517400b60f070401c1d5803401810300c001d02e40280104038440842c40c0a101c0c644a03075000c01102e810500b005507818200f64140700280200f0004000294144400203a0740c0c2c0b07e000c0b0341c1103030b41200c2c06007140c07440d1036607070030041038443e041250455405210240081c4646000703901c10003c000d10f0341d00014045007240c0d20082c04900c1900c0c0303101c0d40e520300c4004002ca5400c02008a0103400c051030140004403d5a010443c00d008018201d1000d02c88050b907920754a100d11040d810300015801c0b0041d200d9603610700800100340c02d0309a00d0005034480e0000c100c90400150080310b0a60000051100e0268030008403504001c020013801140141c280c107452541d15402184529a900803005039603008018010785810580f040c0c0d20481d8100340400c00c04106140c040e1011030780c040c207240d400a0003980040391903641409141d03602c80c41a00715222200e81c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 168021861 1250 168020611 168020627
    0x11151b0d0b01141224061204140a0503090607030e030a030f030f0504020105090d03111e1608061506040b12060a05010525290702070902031015140307 66
    0x420307211412035186045514a4502c20300c06440550194000801c545082c142070717842c4512102c0c1400410900c80d600050342950010748025078400e10b46041c031042c003111110003041280c0300002801611641e644194590080f025031a12910020802600713040c0112014801d0320801005c1c1c80c00f40009107000307454858114000c100080c07521100342c05201c0e01c1c0c4a45406070f50140c645030f0420703d01c881006003151a0041c01c504002e0055960300044a08005584210b0f22845082d10280d0140180601c0d00e8040c2e010810581003180c1c08005114000c41d0103a085881406008028800034000c03403400d200350b5004420040c1c0000f070800c000d1480c0c83e0b405c0c1c002c0c0b504903007511036030343e6403801110180140c0c0414402411100400915400d003810032011092040b0b480c01d031070404091340b0580045401c0d01b00c4030f0340080482040850341d0706000070000f80c031075040d046045041103540c4031175010702c038001d218503603000042c0781d44200c0c003580f25144004040f50215039645010b0000402e002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 168023111 1250 168021861 168021881
    0x2114070c031101020f030402060724020417030a05030402060a17010605030103050c0a051c020406030b0c310312050706090309060f09050f0409140d02061611151b0d 72
    0x1c0340550007218070702044c0211038109130150056801c42d10740b9000c000b680d6104140c00c403018070307140c200009071003083c019000c1001d20301440140c455143c90142954208082960340c00d0ba002000040b4420341c02206a80e04039805403085034a4810701c80c0c041d12241c14402040034152004c200005000d6803180045058900c5401174490b001d181401380980c1110ba802407075030000811001d07007980c2c01c42e43c1541c154140011b001003a42d581e283c80f141810303541915980f521650001c1d40032503040c01d006c946402480144000540c4521142820082c0700003404002d180c000c4d450650a0800c0c800e034192281c2d60340100f0100b24175602440d01400c642d0f00d9210364801306800c5010703102c9880c014520032040b1040908500000baa95001308030082800b0102150b40410502c0020500e200410552303200c9111500185103508146124a4800c004505440b04100044010300f90782c030008500a001c2861544070001282c83e84504a60000031920900f9122800802c42c81d40e44046504551402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 168024361 1250 168023111 168023117
    0xf0d020c010213120507032409080a0e0d1e06060312020106060f02070f15030e150603010b040e0a0308041e0b161e08040c0504020705030702120c012114070c03 70
    0x9203070364150381d1403221300320503014049400809042000c101d0065000f0040d500c00840031883c203040c46419011a10306030302c2941c480b40081000005a0b820070744001d51582c0403101c1416898503a80c0d000c05180381003001c8048882c0c120010420090306070080c0c409036030300194451441c00c2121001b4000c003280d22910740010a640060890380d030010900005542038800450341716400c004110003040034140c1e41a0806a40b1154099611814002055240110707802940e85041c500c04050070355501c852114802c9141c503410002d032007000a81468010340c1401c205029954a003840300d0b0b6001c071104450010124001140c0c1003203000e2440c98800d03503114030b6844814581c4036040340c1881108800b5000d20707042d18580b4141900030000f80c0d03030042c81100d4101c10309440700c003c6000d90304100c1e411515076002003103090461404504480290326480b00414400c2081e40008010780800740f400d45881850a80c500014081904200070f00c1500c0b1000702c030981044a0014404c2040c10419800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 168025611 1250 168024361 168024397
    0x313121106040506160c05090106090609060e060403110a0504051302131802150705100626060a020f1201030807021201050105010f0e060c0601140109090603080d020f0d020c0102 78
    0x100c1c90100165010b4840141507103041c000480c410603502900c001050391080008030300014155036185500740170700941d07a6a40c0001c1d01d03140010389610b480b5000501802000714525055441701c405403001c403a001110212190440e40110742142c8081e00001c0c9c0207030400040110140d01040d4a1036024800e54a401c8148100c00440d400c5400480c05000c24044084a240c003510780340c00c41c1450300c50300e8440b0303078500022030f910345250275010243e05240f50380f81c0360200308042990303680201c00d000c030440070807020413900c0380e0300d446003002850360560560109140d0310000500081e07070300080103c03801c00340c2035840e410f04822581001004034840c0c44098000c02a203041802a18121601a12141521000040c1c01c4c0c0700e07858250b8429421000c1800421146001005414000d2104203982c0c0b2140002000051031403400d5041000800d0818200f01300150801d0115a0700c00958100141c4a44010320300c900f180c880c45d201c44000600104644041c0744041d4003c3c44030030000b00c0d904003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 168026861 1250 168025611 168025643
    0x807080f07050f060306060d02070f0c050306070f050a0c05010e03030a06060518010305060105070b0403080f100e0f0405072409090b01080a0b0109350f06070507020102031312 77
    0x15840c1d0340d070701895401c191011006007090520b1009560800401000541800300c0b042e00ea00c101c0e004160f055461f815114100c1c403c4c81a03002c4008003030041500582540c2c40c010708050080640a98400204113000a031600e807244500c03d903401c200d900400910050302c10580380341da82d802c15940442c1042c6070480c00141240680c08403000140c2000240240522060041d401000003c1c040743c140300301017001d400090100d84070300d4801c0303120f5111810b803404e1041210701c410780010300c0c2d01c0700480030703000a00c000c0208500c400e602c8004000108400e82c2e561401a0801c2f22550003034203611294154082c065a001400d0051442e0310b580c0ca001a9541c1c4c80000155641e4100f0607012450030008203209400c20f4003c098a02018103100001640d111a10b6820400160644d20450398402100c207024503801ca0740e00c5113803c1c2c003004044101c0b00b003030115120400a00442c0c00d0040000e554821a4001e0013921103100000840c5100c8941d102f0000d42d03010858078040701c0c418078002c103000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 168028111 1250 168026861 168026863
    0x21c20090106021207050c0909010c14030606160c03060e07140411030c0334030506030607081305151005030c1e010e0301090c060c1b0312050a03020d060807080f 71
    0x81d040359800d81c02407000003642e0704100c4260b4000c2d00f080d141ca005003220701c0304c5500d50601050003a610b400000032800a0b440000700100741d01075031444400c0c2c080050000e250380c0c142c01d40742000c0880780900b483c1100352602088a41d107550005003600d00302520800f10b0f0788085035050443d10042200c01c402d9002204000803074000c070781408410103003072001c00c805821560180d0781c03080400900501350f60141d107110b1005810405005441404880c0b440402517140c01074a40120302a00244242d040a50018000300c100800206c1001c0043c6a0102400420011104e1021408801e0b54070350402007801030806205010300e9019103c1c041c8841d0542c05c00c0c49940c5038945205035118090a0903200464a6500420103907516640329000b18010840314a8820014003058032140042941840e189030b00007017803020f80f060042c0001e8100013081c9030141710f41c3d8101c414508569038900c003102c103030024051400c010510610744640424004000100d070401c0e104c002003143d00c1800d52801031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 168029361 1250 168028111 168028129
    0x40909052d0601031104150314011109030607050a201509031809060f030709050402010e0a03080d0902120109030e0109150e12030c0303040c05040f020403110d021c20 73
    0x103070003503070300410041000c40c007080011280103e00800c046102150709041031030007885c80d0003d4803142410740090811107024460808400343d4841140d040c40300141c0029140c1d04000d1040c0240b200002d550038800340320f114508603541240d4040a2840c00d03107601707596120041c0102701c010003e240003003600b2101c00004d40e038801c100c056100c1864040308050215a0501401d01604000405a50320f0182d0301840154080c2c5541200004d13203141600004003600d000381040b9001e0802c0c0c51040c00810b541100b2030f1041d0340461404201d240587c030114903a00900c20005006510b001216030425a2000540021034400d80c0c030349030b140c4d44070484071800ca070203140f1031b1020680070200d0011504040d20314072505280c0b5825203040603551070b1500d01707642c021a0100e0304290a48010302946c98140704644445807203482c00c604103425555084201000e0041c0e4605c82c40e4001c401504650f200c1641c440082c0c0484507208042d0081c1c078111031282c59000000c86030300313403018002c07025007010078a03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 168030611 1250 168029361 168029443
    0xf0e06030c2b11030109050c0301060f05030a03081e0412021005100e0c04080f03041a03040c05190810140603010c02070b07080f030106050c0f0a11100504090905 71
    0x200e400c0d40d050761003140200c2d12050049600c54a0b07100583c3c43e994007841150940380c0070b4000362024030344080803d400c490903034108003034411480e2020300c503a0701c00150301c401059142c140202c00352603481140f106101c50b02c1d140000c4416134010442082030720100038488035525000c460145001d42e5031748041e07400407291207500d0000941e0030442e803c00e80d0009604410517058052074036499403c0c2d182030001c64202c1c0030b001d46c8006420808403180c40c5524040380b41d8403400b28210700b415030b2560700c408050310510313205400b4130b69031221200035800c401004004030030449008800d401440000303802c1d5808a182c83c18802c00000d01103003010300404080b05600d6001e060040d091500d510b6098000007001e0702c4220091140082011080d402140600640d468644d101c640702e0514510340000034400018540160740ea02002424000200d5404001155010080d032810041100c16019a07403000031141d0400a40105201c40896605400c20b0ba9412211902811103501c0c03411202c4100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 168031861 1250 168030611 168030649
    0x40f05040515101b020a0801060e09060403021f2a1403090a1e05010e0a02040c1b020609010c021c060506091e1b03040c0e1b04090905070f0e06030c 65
    0x400f0780405031040d00540401100b00d41c5080d901c109540100b07103110141e03003244030305a544007130900039000c030011607962000c409002880c091600d540d0080d100c00c3d90f5403660122500c0420b8000321041c0f0f90b0000000e99988102401c840380f40e040c07412a405071030f0f00060020640c24100d1050080c501000c81c2d100b0301004c0020218404980d07a81121043c030120242a8602201106000120280203c5042c180850000d121419850041004846000565074184076107100d0020750b00681c022409030250701111825220091000140d542c1116150002e50246e00d46011800c150081c3c4035483c0f045000d0f8004006542e5942c0c14071881d03078800d46205c95400d011820b035081001d10a03003800e07842510348a010a142843c4104171220b9001034600302c40c00c0f03550b000c05100582d54411001c0e4070134601c1c0d40804494480340d0700c0c20014821402002d840940b00c1c0c065a00340803007004142d0042034040624505a59624210001c900007903c5203842402100b40354121441c1003140c1d2071400d12240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 168033111 1250 168031861 168031879
    0x609060e090a1410060810050906090612010c11010606090b16050a0b010303030b030607020c0d0b041a1609060f05090f04110c0703140307030206011503060506040f05040515 76
    0x103010806065002041d001c0c2c02c82c0c0f80e4640d080c0820289864a020341c002e006071000c013500b484805084400020003010f001d81c81c00c441000715a56200c0556000ba10aa40c62015031711050089000701c003c2c065085140c0d800c1050b2080ea440e44450410003410000008100c101d884003821581e00c034051042c070020200a11521210840d40300c82256000d102d542100d200d0525666031884500090b80240c010130ba40c1d41c454a185e040c01d00140ea44200f02784007a101017400c4800103011443c0c90720015102010071030000d4104034106c4504003000c89410b80011346490580f02003800412042c0656002a01c03500001071154011700349480f54441c940c41e15370900350b202052141080241140907401070301d0304150740b0a2064000141100c0c1f007454090581c05095040001c00d0a40070505e09460764020040580840e601060b003074155840541d0b03141c6001c40c01c0000300e016180940002c0c0c1c0c00400058002140c0c2c00240071802103440c16a01884a55641004614046c80f003804c4503810021803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 168034361 1250 168033111 168033137
    0x20c04020f0a050a0201061a03060f030105070912020415080706090e0f010b0f0d050c03011703031902160804080703150c3005040503251a060a03020603040c0f060906 73
    0x43d50113131400708510302c0006800c685d50003146c2054061001a00f005c290001700b44681c5082c601003a50000f0f10a4001381b05030f04100ca002004040c2600c07034202c8082140030180e086503501d4201743d681c0c0d484c0740c4080200c1516211002e491704c00c68070582001ca171100500044040c8a501e0491041881c181200c56a80c6024408911a800a200d03903085040811075246104854810980501c440b02e002c01c0d02c81d8181b4040e600040d1504450a401340c0c018001c129407079200d4204c0a100090418015031203043d15147c4041514030304000030b01c0070700003260103e1460300004035601141d02890000f180403040100d40000ca400e080d26050000d00000103411041d10403000b064081404004600701030a2404404812102d081e0780846468000081950620f4420102040700b00040e100e5440e4154150b42c5260080b0301014007001100c08110014072240d5406100500554014009550303d01d458540650500214020b030900300ca244100170034042e00c1650541c0a0309c1c0540c642017148069 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 168035611 1250 168034361 168034367
    0xb0f04090e0f0d0c0c030b0f0105030106050607082703030c01151401050910110d0314070906050d050c04120609050706050931020a0c03030f020f0315030f0d0f020c04020f0a 76
    0x402107099070340080b174100000c0002c40d401d4140b0711030010340038840d07620350401d01014255860365100342d1140c4010701a40000c204048111910031114a46401c000c40410308140c1c00e800c607000b80e299060002240c017580c10041074000c070310000001007030041591b40780c80c0c0c000c2d40b2102a0fa081e40c00034000b441032150504104007011105655421f29814440121100510346a43c05c810280003a454400009501c2056042c2e10f402100c00c0c2080c2180034140340c4000c2c4540100103007003985503110804503425801d110104c501801860f1140c1e241f4116a00342200a014064022145031080d4000000c500740704109a4002140c01031201303074610380342480c01c9100750441c0d20110002c0300c1281455805030044c801040c05656030341310780080f19214100034080310300041d51151410700402c50117407400d80c1d0004881c1c0c00a040c0c850b9804281384030300401d192100c100c80c0790000b40b00300100e241c816038200003080100146c80d400c40305007031100400d010980c004c03543c1001c04031741c00380200d04c420341c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 168036861 1250 168035611 168035627
    0x2041401030e1501080a02091b0f0d0e010203070507020906150a0c021c05010e0715020a0201030f0b0405101809020a050108070212071109060102010209030c1005040b0f04090e0f0d 79
    0x10040c81250300c40e44005045008448017039000e1091a480800c0800c114100101016807002d0402081550186a5400e0001c54440c545041d5400040016446441a03c0380e0042021b00c182600840d1a4980b0940c0589281c0c080340b4180d1040c128040091a28600101300c200c0f200000d844550500c00980015900d100011104a91102201d009002078a2122540c1a4224090000441d00d1261f0750103950401d48507402c50166504a581c0800328103400091000d41c1d95428030380094855812a00c9100600040010541c060b0512040c00f4070305400b9007908064980d00c4800c00c03004901107503e54120b030140e1500a4000d400c9101c100601d42c0140c0c0c03030301c1d44171071140180c0d90a035204803c8984568840c08007180c841c06a00d89541e45030614881c001d038000700c2030000f140782c50820340000740d131004c02072411481440303c6804019103900c04d900740c400825070300170050340340c2c8014021045d003038106c0d00030304a180349092450100d128002034090300400b43c1d0701c0034155020b100281156100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 168038111 1250 168036861 168036881
    0x81e0c031f0b030a0b06040608150c03190216060609150b0711030f03030f1303020a170d0c02030403170f0a0806011e030e0f060c040501050c0a020409050318040204140103 75
    0x341c0c0e903205500043d10203000a0f40d45504c0b40100000d40e103041c80070001241c03e16004110250722410030300c41c5000c1c0140d034554001846414031916943c030703007414642800300f02c0c90f200c45140c000714109801e1551404080401da01c50481409102e8442407140205c0750202a90b812501c201c07a410095504d0b00b03001090240e000b21045400c03001e001d00820701e00f4681000d582500d0784004200880506183d2100b40c1141c511003000c0c0c980b070303450344000b5601d4208041c0a00401400ca5148000f4448841154901e4096071414410401c0f607036070103503d0fa005480152500201c05a5056240840c20100c403072903450708070a541000c3d260401210f449400811b6281804140413000e000f504840b04105103c0445560224049500560042c00d00c8540c4802400660140c0f052148074074588040e075003561420303e000f9444002c4010345901e000c14030900650401e1405d030b0f6503c180000031008110042c0180303078488c00c40740721405010891040e482108542e81b01003c55606c81e40c071a03005048d01c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 168039361 1250 168038111 168038173
    0x20607140105010b030121110402030717070f200d0809070302040203010b0d1407020d140f030703320a09210203180105071e050a0606081e0c03 63
    0x9003800d5a4215042a040303041c8994011004100d00e01d10866044c1111400007000804035000b80c0c0c8085458144a81d260312641c0c0210000d0000d91042206040002e01d640c017001d00c13801c00c00000f8000743d84100329880014078000108007a01100300d2489c1050400030001d22803080e00150858810601034030341d031400c0c0210000040075075a280080c40c06416400100380c3c0d90007403610040103d075040d2140740014103e0404000485401080c1c400d2240c01c0c2d401d00781400400c03e0700145240c07240340354081c119400441401075030756042e44050752196616100714100d5008441e0080f101486019004401e1007200000d00c001d01250011a000c511030243d515191041211488070404400236440c0103a1010420740135090a030310f8103151602003800c0542c501142c0d6141c030100304c2d40c007030700ac4118220b0046000c403c001c010051841c032144c0265042194a48541115880d10342c0c4901c852000c14101001b00401c035000b0801450b040740007402807907803c58810320180d031000c000701c43c0509 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 168040611 1250 168039361 168039383
    0x10b0a1209051f15091a0d080403020102060603120d0f02070f0b0601121503080304050a050d02060105030d0302250204020f0a080121081602030106030c06080a0f0e0a020607 76
    0x35811140108014240b1038400b614402d40760b4402810070107501d00d190900641001e103040c0024502d00f1800b4184d400d030f084040b81c54100f0f050754481003180c1443e0550820200528603081c000c421020344103991007607003a218a522803104142e80c500c07003110321011034502081500c07060321241c0d00921078240301410140c280034041d00ca601d40b0411140080e25039034121402c0014940c1c1c803000c1c1d0b0841224041e0100060510610044a02605800003c01c1901d00001150900604004900311540c5c030108492103181c12100080d1a000e0138070900c2d003c0d1141d00f0040d030b0500d02032700959822034024081540c10200045403402d09030003d07502a80c201f0740c03c100620340d845000b8014040401143c80302417136940340152a2950041900c004210000816500c400040d4102d0031a01492410b0910700310303821241c00000e0041c01c690f40010010002c43e54005081600068428030908050804100842070080804291a0000c0604426030032001e055001854044040d00843d405180283c0b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 168041861 1250 168040611 168040637
    0x240e09040303090b0109062913080a11030a150b0f03030315120109030509090c09030a0b010302010f090303020c21010627020703210e1b030c03070e010b0a 68
    0x4012800e503001c0c1e002035202d041e075074103020704520a0f6004090541c0200181c61a2806103030350400c40500040c060907800e111402541c80803015144144054075240a0641d92081d54503500c10a50808599940030900060074a1a010511110340750b004003c84d030700c40410b000703001c0041c03a004040c958401d855016524542e1810005580300d600455000c001d005185020000c0e070189030450203820343e040c21000c0c0700007544070094800509003514442d81c1c0e81c07a030350145c0342680074200c030041d0035104040841013030181c0c403402c1e00d040381d000b0f0705d07280302c01d08003050110703031a035854000074006d60b0202c039030785000d401d08061029240100078034054071034014070001800d4a81c00d9100c1c4003921100c1e089006020803040308203180c501180c0c0c2c21441d122991342c000d40300c501c202d1041d4518941e0142200c807000d145401441d0203074461003e440320204d2510f04118007901d0016802e01030300c40c8440d04d8446050004580c42075030b10142c510344c0c142e8a0320703620f080241c0c4840c111104200c0d106400790 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 168043111 1250 168041861 168041869
    0x160b1801050412140c07140a0306110406031103040b0c0a050912212104030c06050a14100e04061119020a05010f05061c03110a1a0105030304240e 64
    0xe030085202d1084030f008020481401040c10001d0110b401219008105900d0341038000581081201c8040d04a0a201013149000400011017988040d10b400d050074425660b522000e0010402d40715180c804208903907000301d503400b080c0000c4030001d042c58030711004101015203210203007050707201c9841c01518181d510030114040416110103102c69602050100a6903042c10701407080405030110744074142500b20361001000424140c0010b4404030540100e01418494000400d0245d0020130500c0f003810541d44042c02003403070115001c4601c01000207e49058080450503003242d500b690a24650344031074440304001c051010380005c0c10141001503850400c003d01d0855004000c0b5000341c00e480440741817603802d4888112042c21080e01d44030410040b507451044203070b038070700e0f11a03004d4000c07142c0d900d002c0d108069003030070b4190f49200d590304039420094540303024802d039200240ba2101590740c1314180340c1d03240a503000f014200c00740b144010291042c1544503c0c41400e292070110480c41d0814085 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 168044361 1250 168043111 168043121
    0x30405060408030903120f0a140904050702060a0b03030a020a0803100f080d0807020a1a09210703020705090403050f160f030e0f0d0809010c080d0f0b03060705160b1801 74
    0xb01015030000309641805207020720031540c40c5a03101c144145400010044000c1d54404e800c0ca0a00b84810428200c0241a0748819290002e0005d401001703542800300c000b0390740c4d0704100d914007a8641000d0a1604a050120a0f265004040c0d001803a81c40602d948091050b00000c0002110101d910000240c025020000c40001c0030303154060700500140704c00c02003010200610f85415907008a550b9000078240209125101000c007803c44455202e404a1500b815401c00d1015a102544010300300240d0101005080d41446902100d20f00350b5103400303105041070f0403600603000c5001400a20742760402c00c0c00601252000140c54005800140d4403000c030400702550590000d0308291001503207003040c5501e0318504d2001c8410b000c101e1141e984807511813003050105410055103024004c00c115080066a0400e00c03400401c0c840c0d840c0740b0903420000d05c03450300c03040d201303104490100305a1070140d011500c0e801043d0340c07038450802c4c09440e000103020700a000402d101402e44c9081030030500030301c20 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 168045611 1250 168044361 168044369
    0x140d320a0c0e0a0506030706030b1309030f02150c12060a030b010e0403080c090a06030e070906030b0703050c04060e010e0604090504200a18050405010e03030a0e120412060902030304050604 83
    0x50b08182e01e28054000007458000c1162500c0c0501980d944d0003c0e4480807181d0902d0007141d00310006002c990a4024081511503460400c160401010341103549001000c82d5582281c145101c0c403507100c0101c0d44161001044200108103c50000d8090f8110b10752182d00540f9905c200c80d965a604003500780243d2203040e01030a003d042c0b0081542c0034407810742241c01c010710141440c28450000313003003103160b00c103840505585941d000480d01d005d20803200200495401001050b0303603418804c0c5856011503100c00002d107070a0018403020f550100303aa054440300c1d520001c60300402d00040d81c000b6540b4482ca94414818400061140094003401d0701c15403150481c1c50000b0307151b900202101d0b001c0b144c1c440c41141000b00074410780400903610840025002d2002c40d079a119810041d004040d00448503d45010000400c00c0760300300c03a0410315803580c21408a4813881c40c070789040f003003501440c021145003e418901510115580d9041050401c1c0001c0c1524034095641d40007a50960090380 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 168046861 1250 168045611 168045623
    0x3010801050f0c0c062703040905090c0405133c030230220303081501030903170a06181505181f0504020f04140d320a 52
    0x30030100c030302040002070304800c0f032a401074100394030050800e1300c940000f05103554503e040c1d1408452000001d48050340c06e02d001003a070307076115120b100ca44041d082c00c60b0b519a0078810925003d2041c1070601c2800d1080c05540036403080c01002e80c0d00c05c0c032800010701c0581c54107180d01401d4a141007004046981c107079800745038814003100724a00a818510146041c0c110a6802010b03884420200000c07040610108210715070b503071030031095104500021050b002e021003100c0e40c02200301134000d052a40100c00042041700340d008080011026540070500041c0000e030400301044011203060003041c0c10042c260302c0440c5103030b02d9804500040441c810400c04040d10340c00c100108121403141040a801300352102e1030015680400a440c6810251040004c0d2401401c4d100012240400c00409080300510556a800c8140f80b04000c1e9001401030302c890880c00802d4240520740604d144102540c0448050b0180c0b8460209540d1341c040b0b03c01444015501401c861000380007440b40c0503809100d44 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 168048111 1250 168046861 168046871
    0x72c0109060e0603010501060e060d09120306061b05070e0403300f05010b0703050705100507080f0903070b04021c14012304081206010c020904111302070209010306050709030803010801 81
    0x1840d000d0b5000d8003030186800f03645003c00500c030310b541c840c00c8030241c4c0009550082e0b660301481010401012440b201824400c840c1c0140a9640c2c0d054002108807a09681d40b9880c0903032480c2e940d54400b080c1880200711741d000402c2000200d802c1c209141c0d2190180c10701d43d41944840551003d480f800d00c101c0309001080d42035101400e0030900c58580f10a030740100402c910f40c10420398071003e108007240501844004aa41400c00c0b10030071045519184885080c0320034104200d01030240b0006580b050195050b400006e9181003000040d00c42c1d0320b400c098004040d40722602401042100110043d0b00d0780710800302000800d030028801900540e540c0d00008481c0c170008050700480b01c008200109518a0b4018800841d881d8003c0d01d61035800042c4c10703c00768aa80006941c000d210050003508440c480b401c010a02001d52503404d40d001040e20400c490001e110884402c03441641402036001c10711a0040c4080380d10b41d0302c030301e92024550409413401a1a42c55806080e0005d912030456a0345070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 168049361 1250 168048111 168048119
    0x305090105070c02030613060915090201031d03160516030f060b0f180c1b0c030106081204030b06040b031510050f06040303120b04020a050a14030108072c010906 71
    0x744a450b41c03005041c41c0101e00d4040c664006a03e61034080c1c0f0100742001c5a102c0300050004c503030300900810f940040b00c600c03110056580200603101601b41031303020a244c01c0c07041e412011b200030707154041550303a0090f515000d48000f100340b1490000d1000c0c2c0e80d501c01d00007501c1c200c84110240401031400f900221600f00d00500d0844260b0324403c0c16903010302a244265030a0f5200e50084044085040c40314648a17950020b15851601910602139450184545040a61900451b81307414000c0190020322483c0c1c1c4079183d250760348050641015007035100304801c001080c000400190030240041c0082800500d00700001e20b001004544c01e200b40e40c00000b40510003501c007900a00034001620b000346980848030000703d81c0d0049101c0542405003080700c807100400c042d44000701246008108548900c0c5114005000307070048034895001c03c40c4541c000702a0500741007501e0480360980c00030008141403401d020300c50040041c07404811340500e400400e082503034520303140c081c140e0004000741207454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 168050611 1250 168049361 168049363
    0x7050a15030f0b15091e0619020c090c0405130b010206070e03010f050103111002010603030c06020a1116060e0316120515040803041208041505090304030827060c03090d0201030b0301020a030509 85
    0x401d188000e01c0010035021070403183c9661003a11a100021808c2c000b5080160a0a0b030420b2a1082c200d88d02c000803800f0410084190000f070415240c0942d040d02c00d07811036100b4801203818050b411070140c2c0c0414001807007640700b0401d200202401400108a0250401545080d54070a800848000b606622404880e003032105c0d00b030015007410710003071044038950340b80982001c0600401420090b0002003007030940303015101e07001d110781e40a0b04548084246001030207480071540a0140061000e580c21302e0146070018034107410b040c0d1424440e0075185000282141000c002c0b008880e24000c0c01040005a08411182ca20460050342200d42e01d240500e010100200305001580c2403003150f43c00c0c800810801483c560000c1c0c030806000406480303002ca22880c6018070f90000700790702400a940e040009480400c181c00700c60081071622071451f0041007001a0084c07449100c0307158030600250301986001d00d1752001a90041c14001022406100031909a074031010050020944a9050050303d00b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 168051861 1250 168050611 168050629
    0x20c1005041202060f0606070602120910150302090f090111070804030506070507081207270e090c030d1803021804020316080c060d02160f0507050a15030f0b1509 71
    0x110600c090075851405e80d00351500030070b0141c01e150080030082a06410000c065045400d0440b841426900c02c2c074051007646c1d034480380c040d00200c0060408500c00e501901d007400d40d8040e25802000c0c2001503590b09010f08a22030003c1070814959210600981da104021000f000300c2801441c02039992825414080e00e0b0007070181140c010803008001410120303c0250a0341c06403410052414003d03107828a0458880f8451260310b05801d606aa541d81c0752010340169004136039454085c0c524a071307510810b5035298000303510030940503004401c031807011b14851480d40040d04403900b09503000c640c5a8001c02c140031810400c0b124400d080c0d4003070000f5880d080110714080d01d102c50061405d0390410b50314548822402d00036501500c0086001280d0100c250140e03a48608111b01c200301200c031508280c04845a07c12050b5000d004698021445081c11030349242500c0d201180070513003d20030740c4118014400f1111600005541742c00d001803a641c1d00c83e1090910800c0c09140f600c41044504000c8070700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 168053111 1250 168051861 168051893
    0xc0b03100602031c02070c0810060801050105030f0618071802071103060c04121a04050307120e18180a110427020103090f0b010f03030305060103020307021f020c100504 74
    0xf42c03003441307201103002c194000702071840050080503803150140d01d041444a00103402c03002403809000380000b034914031a48940f040ba0b41c0c0f60020b220a90380c0d50103264031a0107803140340f14580c09c810001945010103415100c1d1800c0c80e0303011165130302d80d1426424407091501c0c80300c2d258203800044031b4003401110b855922240d10300700e01814a50801020410b0f00d0b2155125440c1e94540d201d41d5503041c04150200d2412020308950000d8030741c0303018a4000d440c0c0d07106080c1180d0303040c801443c10034003c0c4510495148120040d1078016011005c608003185140002c1503000340d42c40304180b281c190300060001e0411580729501c80040405404100019201100c803c85a840481e944816003150301010100c9590b0b020b00380017900880504013980a41c00c0c1c5840a0301e0071011070b000103a040040341011f000c8a00a075010850364036400c004409a10041e150f90005030b0162884a084841500c0000903002d4800300c01803070240462803081c01c0903001e80c1440c6c2110360361801c10041c45003074108501c5d12 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 168054361 1250 168053111 168053113
    0x903030227130507140309160e04080403080708040302040e0c011116030b0702010b18060f0108010e0f06220e0c03011103070507030e15090103060506340c0b03100602 73
    0x7014008010400700403a0700001d51815840e880480d100502404070840c1442c0c80c0302e1243d0340ca182c92002e242c1c0d690307207040c000004092828000540708500031004d030300490388641e40b1803a06103035499111954004a205130340c5804c3c05c10000005076142d1299100b030704514406071400743d181c0e20003d0180303c8914054411500305040c0348026482440d201d00680f940412000700c29190110101d0041440e009403d4004c079915444180015000b00d40301c0c880d110850b1140b01104100c0700445120400f8802c070342113010020b0204a00042034005180e01001c050030340607100c00681c40b40c2a240c3c0d228450084090b40c0c698083e280d01006001c0050740395000e40c0244502035800746014418400200302c042000b002044200030107204050203520a00f0040880c1e80151a24082c1025503105c5805c5a020074546100002c0c142414001d0f1810004450200c0109010503d110ac3c400782c89581100740964480f02502c00007030090f6110340261042c031041c10703264506081c00d84542c180d250480d0080d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 168055611 1250 168054361 168054427
    0x70e030c120a0b10051206040b06100903110102150c04050301050c090a2616140d120f0c060501060203210105030a030c1506080102090f0103020c07171009030302 71
    0x4060300009081d00c00b56032000c2049010f690702c82c20042100145c0d00b01d581c1c005203d21089002880014445005a008007207219490321040300300814483c0c0c925003a0042102034000b000811002d01c19440941c00600584904201c80c10720400304480032520300f2080c43c1c0210381482141003d10885074404150134545203400142c80c0007840005880c810203e000910702c003801544c0c042d900380c03600311500d15030403034035400d01c05031646c83c6402450081d1800400e80c042c0c201150700d4920322182c002a00608181c2c5541240d85007102ca40e6160640d02040c0b1826480420008109116042c003c040d184d01850b11800001825240a40020400d580c107010040c0103106540e00070440100c40e40d41418208100c6805180652003001d0b02c0f01000d02061030f00c074002851705010f40041082e040f040f28203040c119060001135040307000e211030302d01d402d5000701e0080c086c0c4400c404203021020340240c2140c0303800c05c0d1034506809a4261041c1240082d8011031008098410720a030700602011070300030480 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 168056861 1250 168055611 168055639
    0xf060f0e090f070207030b0a0b15120115090b12100b03040b19110a021c03090809090912041503050109020c03031609050a031a01061806030c030b0405070e030c 70
    0x1c1a14000b81c0a0b444102210300071524107402000010700555001500d9102480d107150740d00001c0140c020010b00545e9400c406c2009115030504548000c07100b2110f01e0390903420402c0c0c40d01d0002c040c80c3c8a405006007614085809440c04024010210450380b0034041d524040c924943c0025240d40711800d550010b10511001409207008250300c81701c2c21002a00003d000241000500446100d900140174005890700286601003603000031041054030003155400100000c03402c07201c480d03030302070304482045c00000362038540800c40c1e5800800aa0844070728482c0c101c100e502039030043c1d01c919210b060452a07025011342600803940140304002c021410054603500032034a1b40302c000c1a0740050f00000b641c402c581070083d40141c0203840041d15050141c0c0e103e14090140300744050800444000e4400000f038064482d0302c1020080140c801d02a45551420b081500a0454003403080c00749600d86039180c455844611900707118803920368490700c0905101d024107042001d580002801200f80c2e8003941 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 168058111 1250 168056861 168056869
    0x2028020d05040e06010212070506070215070f1d06130e01052d190b090319020d0201050703030e0d0807031d0718090606030302010b03190201080601030c12060f060f0e 73
    0x41c0484800380783c0d0b50026910600106d06040320000d43d0040f040000c40d09205006000030494860070098088842a040120340a6500d0108450392000100c40700c01c0400000c0c810056050001c034202805035403011174600007042030b000088440e001105044003040f5074081703d1040382c0101400e0f02c503200103000385103641c45d461002003240c001125034040c02944c551552503010307108022000300d8100346512a10001c00f56441105028840e204440d1072100c00c109213105804420b81c01061103044005541c0192915000351009500380340d503959450045510900c60310940142c5659800118900407001074100c0312032401c903070f068002c0001c43d0407001e8800150070042e508034a94140c110a900840d1002414034003d00038a800e042150020406805400a005014040b02566903441d070303c500da5008140405000ba0000302c0c0007020030f800354080d5000301800c24031880c0c50f60360400f02140c58016941d40d0303030020904a101c01c00401880d5440036a0241d418803610307006131801000800a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 168059361 1250 168058111 168058117
    0x21305060a080f0112080f250602211009110c06040302070303080903121503010e0109080318060c07080a0e1906111605100c1a06040506040e03030403032028020d05 72
    0x701f070300c0520004011811030301c04c450641000040c0b1450199080440c941240070750807083e00d02507290507011382402c0181414802911a0101d644041c0c091071501480c28064800711881d041046410040c20341c040c01c003804602d1159020303400078130f081351961500510030000242074001d940c005110303142d09080000c588a40010070018201c80c030702031010000b801401d61042001956203400c0c0e03808200859107001c0c40c41a10a6000983c440205541071a103d00d803c645103015114100f08280c00103000f040548647d003024a800c1c42401c0d071190108041104400f8102e0b0528940d074010401c00e83d010300d41c401c181c501c040240140c520a44d10880e290941401180c0c45040c4500203103402910a900c03250240350456190211111217403e09034600d18291100d5004604281c00501c5a0a15003e540401b10b001e1005601e15500c1c2d46040380200f82d455070030314410f031141c072500104081c0c882c054607100f81c01ca41e15000c1da40c403010820000d40614025901035401400855a20580200507 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 168060611 1250 168059361 168059377
    0x120e1008130302030c1b1201020702091f090614040c0504060207060c0204142502030910030906090203030d02120604050f040b090102040509070e0f040b13021305060a080f011208 78
    0x400e44560100b4942642180a10071820509110380500108448915a44a8480d540945101c240342010500b100e09034030801c00044c0d00b10310713660086000700305140220070640d4107640c90741d0800782d2100040c0007680d4456001c0540325441820312070790780c50240708422400085050440c40d1a02d031403406034682456204a038203011310340041d10b081d0345541d040800480708010721130b01140380401008044400341c01120003084a1110b0306840103000000300d4414600040014180d0310001c94114083c040c80d00303044803015151061000103072420400b504111501c2c0801585803400d900c9006505000100158800d43c100020320400c10344c841c3d07800350029044090006165100c0303d81030701a22a035402144c110040c0402c0064003a032056600e0001101240c1e80312020b1001c0040105581c4540001907102004401010008103558028807507406084403040541d6035480004505800844e405800b18407200100300f030078000c808220b03001d0004403883c4241d201003074840c089580107201d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 168061861 1250 168060611 168060631
    0x3050717012a03180f0f050607030606051e1b061f0b0a0e01020313030c0e07030209130f090c091d0604051507090308160605090a02130b0103020412120e1008 69
    0x1600b11010710004c81180340190000520b42e0540003600c2c2008035840030a0083c0e501d40913100c041420f10744203001d0b88003200c03001d50322242000716207040408064803001450304112303000c020b8609004400f6500c090014032402c080e00c41403800d10389114600700c0002d0018002c14050300f007032003049450700c191036041240b441c001d01480702110050f0701d548200700c0006444500130500004000e00d04100405842141000c0b01490b15410010380c01d80c0140c9480740d0303015039140f0380d030381d522001d5a10810b40c060850b44040f44682c101d4a50880c03658443e0042021182c86400100ba10035001c0000c05500003224024075141c84d03e520f0342600c1d0784800c984910000e40e1040410140c6100f484400301079500101e0b09545c03407c3d1018041c4031520f000004840d91800c040000d0800e02d13000c00d05150040d005002e66100c4d21030031881500900c402042181855824800400c80c0c0360108000030410707216046d128030380644c02e40c4c080c0c01240c030303400b51503c143d40280d04043d003203620520807608401c49031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 168063111 1250 168061861 168061871
    0x3180402071a07020d0807020d0f03021e03090d02030418020705010204051f03060f12020607060e03071209050a03020f0906040f23010806040803041b03050717012a03 73
    0x1400900039110741500036110000c6200440d200d14003410311603020354425000c6642c00e40d1140000c0c0d480b02c01c01c9542c1800758000032040c000482c000e0801011071030581c6001440d241c40028135a0700c410b07004440300c070308480100800c00040c80812400703040300143d000031402c0c0340c90a16202034514000c0300040b0f04903004034070881086070075010754025190040007810004d000140c44107240216807071010000e41407100004400b40d00030b0746102544c0c0c0e1702803003044508940e02441865402401c5c201d1310305546660b5000b030110300344084c100507072007480f03440f0081c050260024103820305500b01c24071503d65840100016520010710f010040c0d0203403104492076852800240c01030558a00d44807105c0d04000c480d040c02030700c1002c050301c079803c0b1390b2020619903250784505a84407400c4070000d00e140c070100007040224001c06c0c4803032070081444d00814200358072669500c0c1480c20940c050311b0800a0003d84000c0e00800b03003d80140c103820460240990f071940d2043c02c0c40030b0b1240c2c2c01407042c95581c1e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 168064361 1250 168063111 168063157
    0x2120c13050c1e04030b0a0b01170906060d050f011b110609060402120a050a0605060411030f0c0705070305120a120b0d020f0102010b04050408030405060105090915070908101a010905010203 83
    0x220709039002903806c40311004407480c02c1800e60303000c0d000b45500c0b9030020381480b1424a4002c0b1440c0c0c41030140340400010502565035009209001c80580c605070345a04c19482c0001004030240510160a01c0d11541c07202c044045c0003018000d034101d07a241e6501c98100b2800c000702240001002a402501124001a1001d10902d4a4100081002c010b842800b03211102c1b02403140c00d821043c003070074082c1c1d020410140d44042c5c801c40c070f000a4400941044407100410036550120000c0d0804038000d0003590403041e030760f0343c42ca46082c04601c980002c0b078001140f040341241c1c10203003d402c2402c401302c040c440c0320740c00340008040c443c51020081c030416034002c0c0301e0701c20f9200f58820881c000340038004004074182400d11440c141c0040f5021102c0e0700c150000412a41402e2401034017588020000b4614044120021810304070000c110b80704001142400140211040100f800b04c0b0110b110002415595000c0b03a241d1000907002c1d06d03061000001d0704106690b800011a00500c1e21190030301405094 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 168065611 1250 168064361 168064417
    0x61b170c04031b0611010204030c090b0a0b0703030507030b010e01022e0609060509090c0d0602090f1804060506060406020d05030c0705010e030d32040f02120c13050c 73
    0x150b038102500d180e107014082500349401c42008000e550315071302c0f000342c0592080c040c54240d10076400010440522200f0410605802e40c00074800001d0040c154501280c4901d842512900078050640002c0e45410070b100e44c490f007501c114411010280391400c100700860380080c1d41d880e001c80c00c21a11050040248500c0c4600c10750010350020105e10a1000595505409000c1c01c140c0c040c10b4448c2c084000891060603000031110800c000103441c1012120281e10b840b402900300d40c28440c0c0041100b10301c00c0c265910756541403c500480e0289001d10700b000e0505104803000107000e58081c204c1000b041c854217400246500041e9087c0c900682d481d0380e4040d02e80440d0150003401041582452440f407807181021028280513510124104007880c0000400e010b4107503152812415803202039105105000c0d06035106074000c0c054101c107080d40149601080648904200c09581600030750341440c502d28101c1007134000680f1800c0281304506100c40403803040d20880c41c400c440343e00074055650034524 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 168066861 1250 168065611 168065617
    0x11030c0a12091212050c0a0816020a050312090f060c030a0e071806290406052d0301060e03150609040f05030a03020405090115120b0105071e061b170c 66
    0x10f84008803904200c842c03031015010300d1034001c61340502402c00001901030140b00c0c090b10250245540d8070400c54444991002c0a10540e00f070020031405a0032484000c100100002e1901110b0714400c200613282c40d00c403c6081c0a6012404040b5400c05418003440c0d0303a00e1804c2d80d40114a0713810004400400450301403030040940e0049061071403000240d24441401d5201004884000c0d804000400740b00f0155540400f00448021402605010500116100d8000b42a006a14204010b2408440c0e480c01c090071500030710b01c005d4000000018048964040c41042c610032007a8010b200400f8120240444800c004007101d0081040c0d8000030103001c00f06401c400e1603500502520b907100c04403180100a98070a0050900a010100c00040e0311020300f5644030107000ca941e10041650003128480014100c4140103504103e010f00c2940003150a490396100500361840825102e031455141410541c1e091003c14501d141c41240c803030800c10703041300d8525000b64694690550320ba86054040000340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 168068111 1250 168066861 168066863
    0x206060f12061303030606090b191b1b0f0b0906280207030b0f04050607080727030605010605070b1501021006231e041a0306041511030c0a1209 63
    0x2c49240d05214102c90440384514445000c0c1e64207000458440109a41c0b41c1c1ca41c0c403a04d8803125040101040001c08010310003441c22062814070041d00c8040400a5200780340e4405a0f0110324001c4a03848003184507454500401d41d059400c01114030704000118540502d0b10468040c0900181c1d000310082031554032070041511004814604510072000dd50700c03245d5000849020340f100001c50b14440103032094601c200c1d03000000308050ba90f0381004642400020f000c80c010b014100001030303002194100300ba010819a41071100c84545075042600603900107a0080d01800700c00c01c42c0802241e500d2000550010280c15882e0140400340300407071074100606603406a03140b4003c0c0200b40240b6450002c14040c21011902e00021390b50b0040000006820240d1206601d400c8800d0303c841c00e00b6000070088113074161401c1001c01d00c90001c0384c1040821603045681d04840800a84000b110384034a04800911a4802c1e085207000507038010309201d412120014030543c080320072841c441c80d0300b00d0000f80b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 168069361 1250 168068111 168068113
    0x51003080903030d021201080c0d0807060b0d150f110a02030a08151306032604090e100e0313090c08060103052503060503190203120f0d020a0e0a0909030206060f12 72
    0x5080342000030b515406c000c2c050210070303008811240e156860b249078545d901c41e802c0002140f508880341d489100801300a000341c0d0704050701303102280c0451502c01c019805094031400100740c1c902900d11110440f00304030400800040280644901c496000041d11307460f460908000d0b04503100d031041d44203010845041940d202040141100c4a51420382140c0200c0788500032540410781140d051006007080c0c03c1c1f041c008940706202c10002d007407043d00604501180c50b01614240c48ac1c26844606940e501d0040b255142e00c00500d04210201c140204002000d512100300140f4503600f03801026004054806410991505c0103d82000c5c0401d50b40841d00c0012030030320b140ca036010354019000d003106104240c07090165892000e0b00720740100f480880b05074000c003c1c24a02007005641e4500f900b10781e90380701c0c0105080c04158a404114801130501d480d154440d8800c811400042160f0b2070f03202e03044035004030308109404000076000600c01e604000c2c111038100b11424070b44040740c41d40382c90302c02d90862 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 168070611 1250 168069361 168069367
    0x705091e0c07200d080d0b0301050c090901060f091503060b1b060a0b0604052b210504080c090615070308010509010e01060903080703020c0904030f03050a051003080903030d02 77
    0x8607203009001410079601c21281d104051000c40c08014640980381c0f1001d4100700311101d2480001c0b0128028150a00d100000103858080403010a08503041100d51070a4000001101c110924007014a540103140d80d180c0070101e16406500105448414465606c0149049004046150084c0c0116001e030502c018200c1d103406621814181d200421041555240501d03404036a10360a180140326001c038000d880c1d94075291405041c0300442188c6559000b00741814000c15101161102e1440c0b1141e00465a5174001086003001811200a40207000c0c1401800c00c4200031007000030031780c041e243c6d4088518246036600e51000c03c2e0090304500d00b480d88140d000500c101050303001444141625000d84103200261b80381c10004402800a000b1a030214048600800c0080c14880081c090130b4820710503591041c031424041012400c055800700c1c0482c0e07030340b80e007664901d9240c800c0700e9111440020501c4107041204400d2540d540300d000c0a4000d43c00012a0080c0751410030403910424501842155 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 168071861 1250 168070611 168070621
    0x6090611070602270a031e061107060509060f24090a02130902070c0b03040f06020a0e030606090124020a051516020703080d0b0315070201020307020c0a03050705091e 73
    0xa5111500c4e0b5280741460541900761140190b4a4184110b000b07094450b202d41541c40e0400e0b031540141c12a0072500c031b08017070306002407858002c0f0081d00764417800c00d40e02e40201c0d00d00304c0245e1340000d00850003603000d0000c1101180343c141a55402c55078203404408900701e051030081a070809405001e400181100a00004601036030040c00d440c020703007000041041c1c0b02c0016034160f2241b404041c1ca8a284c4580602102070b4940065802901c640d101c812005c45c00c1e55107100307a8104000030000f040c9800c03034404150400713001f0158045012a51040c4c2581804ac0b401c1c04006901d000008548404010442144c007c0140c841600d0304041101c000d035100b175251f07071480c0b00300700c1321855a80c40e00d0807008412400022b80c074040d240d2001b03520381420003100c4e4103c020090000c00590510403030642885000712207518502886441e4005a80d0740740092700a45040d510390741444c011002c00000b0008110003003030308026503c044a850a142d25010848a00e05419180c1e0315051111402804 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 168073111 1250 168071861 168071873
    0x40204020706150614130b030702070f0e06040b01180e13050a05011d03070b1b040e04060b1207080c06090414011401020d031116050f010c090f170a0609061107 70
    0x800c8680715950a04043c4101400d00014021a134156a0049071b290042c00040d0104020f1369000040c1c0c4111600ea030703a50761101c08140785552142410004030030510400c2e05003400703000001142803d20114685100c0c0500c10464101d104040440546030003140d9407030600301c00c2c02c3d54a5000400c80700c9043d450306015008203400c000080c8641684141851104030100680d58519009040c2d0f180c00d5880400000304003010000b0b2000301c00080001280850b0240c0f01d40d4041d80c050103000175043c00c04010b0020400c002c103400c8032141e00c600010031000c14000b510442c03021050b00c419880b03c1070715000c14040c0c080d8628a130310b0b5414088c00441d4060860501e4591004241d0882e244c4070310b07028040c2d04840a90403d81c429050422810404009050007507040380d20031001c6960a442c0000c60b02d00f110f441000340000154142d00401c4188401c00b5484d0152000741c80c406c5014074846840340da92075100000800e1243c44846103424010164040484000036550003540e13407820349004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 168074361 1250 168073111 168073151
    0x30c21060d02120709020c011406100c060c02120307080601030c0207140f1504180c0302030708010b0702011103031f080f191109011409130804050424030501140906040209040b040204020706 83
    0x7001e40030448002030300c00c1c9004bc1c84184060081d460b00c441010044d182c000280500400040c154801d689900341035021440c02940700b020b20b40d4940c83c490500e40001020340381203551030421940496000d20440b104212292a110703001c07a5014622030101e0003041c4000d00b8081180100c1c1d102180014105005100000c40700003010020005036103441c01c190105e00007520803000064400e8014400801554000c1054500504003000c2c0e03d4003544101e80365a10446840031a40402541a906d50440b01c14040242a0a00c0500501c03005082c49036501d140800e28141043c10040484040c8010041410396a56001d4480200c0c1c0da141e20380c00c0788200714900194060800318002803031802401441a10aa9004030742515052a020820000e0720340c054101c0d001f401c0300a0003811442929070720ba40114480e400205a0f03210307a03c01240c00f0040144014180e4100004100041e900c0c601903a81c0b2a5000e4648a01920359002150003400b0306c00000b015289401203081c80301d015090340e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 168075611 1250 168074361 168074381
    0x7090608060103050d11030a0e04020d0603030f02100207110906010908070803090901050301050402031b06130f03050f070e0703020d02160c090c02030f0d20030c21060d02120709020c01 81
    0x3220924200b40a0803124420000d1b513641c56500107000020019104204225a0420003440035082c1030031500c0e49000c59009900442c04034a80c041c2107140142c0500c606019800c4040046003030000503240c15440201c0e0700c3c28070344109425030005101c0c2c0e004204010240c554203044400242e100c00302140e80760b000009007407003035030140c00020b070918050103400c3c415035020700584100109a40001917030703002908460781c032000610103c04007044805200c002441b001d500d10340325604d117050031824407140091400c1c40c1e030003040b414040910710300e00b095082003491030700503565501c1001c01c0000380540c038440210ba103481e0380b0110a03c4414034900d020f94001081c2041602e9003010240e94a200320401c07802d0b5864184034480460304943d1000501409030341a40c001804040c00781d5846500c100c0b4090107580c004951128810a0300b500c1040343c01e4003500007066802d0110025500600012000b03108100415419442c0da405020010060262450035503d5080c0009a280a8264160 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 168076861 1250 168075611 168075613
    0x4060203070207140117041127090a0b0f06040912020a03020c120c010809151e0a15090e15070e0112150b131d010302010206060108010b040b0c0709060806010305 71
    0x1802058456144504401d820416100e19684009440340c04180c40801041a41c1c10700d4235160014254980d03c080000015200100304042119a002e08441c1036010348041101d0740014289400941d052600b180c200300f0a9031150803d41d51400014068520200300802c0c4405005076441019000513401c070005200e9000d40301030603050030600c490502082c481100503407202000e0380640d4001e2451540050ba181c066072a11205840703169880401542c1416016240303041a15108907441301d140d4005c84420010b01c0101f002080a10000c8030b14011707001a2a610390704c0c1004007008120060300c6009100145116207461840609002c25202003240881c2000030281807642c0c8500c01c0410b4900718640101c1c2c003d0402c03600720b885401c4607520740303900b0a0480300400d1443d100802c0d80f030200d001190305003c960442c4002410b004001d003042e07060000c1c50005005545a607400c0d281a14003401c8040e4a4202070740307080389000d2141d4081442c032460200003003641a00410201c3c184d1780070310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 168078111 1250 168076861 168076873
    0xb06010f080405030f09060706140f0c07020306010905070e04050f01050301060b0c0601060f5711180406060303020705011107060302070206040506030a0507020f0d021c05040e040602030702 83
    0xd5000d4aa0240803580100740f40c204000c50030744082408090542520701500722400e102c0d995559904946160004500004020b0708118240d1403107000250b1007c01d08900e5401c207451a40800d545074018003d900752191600001801c141c0700f18082c2d5083c01c00104148030509242d240400304240a0040501950070032802045120500048956446c3c4445c000c00703882c2e180040803580c803986500744908001c1c1034004110502810b10346641126281e05d801079241c450409401000c038000d030340da0b0350030b00b10719407400302149010000844815008080b042a05141500103a900c24401205440390300c4103000340000c0c0021640502e0580e8804d400315a011611100103541e40103c1300000c4000340d111203403d04c40580300750060007805102400c0c450810b9100c2000031a00d402c200c498040ca240c0c3d030703410081410345c10030564643da04000007400b9401c2400c14025100c1d4040800510a00c00350324925505500c50000c5600501c409500b91030301e07061034a0316002039801aa030b000014440c0c1c5d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 168079361 1250 168078111 168078137
    0x70807020a0c03020603062403060307050406060c060f0e150a050a0b031207051203090a03030c0e01050d1a04180c08120307080a0b1005040302180112140102070c030b0601 75
    0x407001c409582104401c03810740d2640e4200704813517000a02590b00242e21218030130f90040d000301d094420000300300e111078076407a00000f41460403040b0f52000c3e00c150b0412031f0400074143c005520140e43c9400c0040810009051901c68000d454070301440c0c800c0d40f0891039051400030015159034010014001c05000945130007040070241d41c0c0510700c0070b915403c20042c00d00c00d812020002d041c0103118030165000703040d012410041c503410444808501c0c0e00680405070405504d846900c0803203e00341400d001030311404000a00390f0080304000203a856959500d00d040415140c0d01d800440320040c4240f203c021402403c10101408000481d0b4079540c3d51404601400003169500c1d146c060f0000c0c0c03030305607550380804844100740a00a1418540d03503000c02c001c544c071140800e5849040b56190240e9441c9140306002410b94440307420016165850010b12020801d0000405116000302c04c3d5802c01e0a102c0e0301074024032a0704c3c801003403c1691800082040b02100c0c5075841500c00362078005200f02030f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 168080611 1250 168079361 168079363
    0x2a0a08060105060a120b0d030905103b03060c07021c02010f0c11280807031a04053d0b0307050103110702130e06070c080904050a09060504060507080702 67
    0x401e0042c1c41d8400424803588130103c0c4181111800700d05c42990100b240355100000c102e0b41110b5410940008441400138055400c00c2c1a22080c1e01c941840c10948490002e8404007004800c611a40005040000e040c41a4421540c1440150704000d00341c0303000781070040640c4a81c1e440400308a015689000b6143c030380ca00c44080d9114901e8040e16600d16521080c0c004a41e041c880d0139044a400282c4000c4407000e8840345502c55000c00b10420081040d1120f1030b4060415406a200f952298410802840002c6410b460a00300d0501400450840e4946241880c106004050980039100d14495541e00c20420100c007450f11000d01032041840044020041c8191030001e2480c1e0b070158007108007004654442d030712507e04000d24100080c10020142e0000340c1f10845002c1c41840591a40503290f003110041c464103820074054140b109003010142d4524034140a140c15040c403507540d0300005010080c40c0e400c00f01c2a50390000080216190030301d0104010482692080000703030030400040c4042d80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 168081861 1250 168080611 168080623
    0x240a0c09030308063d030b04090312020c0f0d0320030609062e03050103051504050703170702060c0a1502030c0409090212070f181b050901022a0a08 65
    0xd05039070fa8030700a94130b0714244075880704075070224400300e84c50249041102103440446610300711100320f02203060301100002002d40700c40c6000584598544048400081e801c008c1c00c07a038584ac031800140c1c490452020590034a8644007602800c0e000e0300d6007000c40194180c0c000c00360f1400750341d90341d400d10020344000310b00342c0000c6400c0350300802c10301d012135998588941e0b030302c420560900c11155111481030340c0503017001740350040300c003c65100d5005104100b01031102170200c0000c881810494605600e5a40d030710300030340c40007500181040b155404122001400c942601d80c0240c10607a8407010b8040d916550f40c1c5081e07040c1d410b0040d582c4d14200d80003180c001c690081c2c1d40d0b00d1049007071500b0f10024000910261108a0b48170b0a08540b400d0791203810310403000140b5400ca2a005400d203091020b0300d50b5034818244107480351500411800c005100c1c3c0034045c1040903445c15645840a260050386840c20000c2064904200310011508080030b44800312100300c01610420b080550f241c082030340d169 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 168083111 1250 168081861 168081863
    0x30c150c09090216060f0614030c2101140c030a0b0108010320060403020916020f060705030f1e0903030601020c011106011a1201081b090601080f0702240a0c0903 71
    0x20342888010042ea40d0950040c12001c40160000702c0091080c0e0765150031940c032914000c0215456800800035030303440a207580000c5106501034094001d070a400550034804c10084010f021070300200d4064200c2d000d40c0b10004401011690030181d044c9001e442a564204a5010300001c0c18002845081d51003000d070581203d1f4000800884140c40301100250100d02036051604000140400405070780d407003041c10b01444440240520a610b08100242082d56801443e40e003544110184100c1c031358000100d0754040000020000c03192584513a03034000090941c00b480b090110a42801150000480214000c0e402602190f41c90100f0b04019100c100c0c400c441c10909e504050010004060409415240a03049001c010711308a20151003001025080c0c01071040c90340300090884241c1951550f00703400003411103581c14135291210008000e81c2c8000c0004103c54408400715034000e000300440c80c8810700031003c030b42d50b818002c0c8004005850446c0d100c1040b40c1003c1d0f01340175880c0140b01c2c8400707036 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 168084361 1250 168083111 168083117
    0x7030e0a081c050c0c0303040b13051504090b01030e060f07081e0c180303040806040209010e0c090d15020d150501080405030d1104030c0303020307062016020301021303030c150c 78
    0x140020100b40e41070340101402c161240a85d02e10403089a60520040000d009048042501c41098002c2180c040480f80c001030f003d00710b05008101d585903004103840496030042004211011041d00407000b0f04150700040ca020702c00d14003031100e01e000001c1e43d2031003038505075a0804941d8640d501644400315100103202c601c3c401c800462448044640101614070080c2c44403814040400b011a24585c040d07840780741c89402ca04103200031031401e109040c0c018003502024180b2420500f100785800e100c0c0350301480c4949185040c020401456284d020783d501110340c003c5440754564203c00000e040305600c031480c00c4030300e4640403403158042d10312a030040f904031b0001c40c18480c0720307140f6500400b0304802c01e64144505002c000002403110b0441380195109030301a50310b4110b14036000054510f04613070004144010380000d1002881c10b4182d0b88840c426802038004c0210a001281c02403141c141240c0380390030103840c0030091542081603605d54520641060241c1c07001c0400001c03c60340342c04012800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 168085611 1250 168084361 168084403
    0x309020f040204180e150c0c010b06090609010507020114040f05040b040926041503020c190203031801270302030d02030403020306070c0501141f0e06060a080408040b07030e0a08 78
    0x41c4e28507540207078001400d01c42242e03003107500e083d80342c01ca513542100c920040480008003265520401c2c0121070110700c003a19543e0800c02540c000404074020703850f4080c10040e011a10300c00b0340e841805150100d8540440300c42d0f84544513000317607a044c0c0050040901540c2801540045800d02e4810311303480b5a0030284041c60a840c9064041c03c5c4410508440c41c1c9030410710010590b1804074140c196540ca4a07140145d4601c0315004c031034100a005200710740d114640310140009a00d000c4202e404142c00651203c01021502006903039000040e4040c0c503440c100c0d061545c0d0140c508d100001d06403402201203560000320444101d17a02d108030700000b905504402c010446150082002030201c9115400200f08a031900d4014015604210707200c82c100404c0410b140c1440b000c20850801170001e58401480d0340c9000000318582d440740c044c0100401040800041c1480403040554000d02280c0b0600795450f031180c1001407402c010100114401c0740400d40c0090703001070001303030440c0c030760655003001503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 168086861 1250 168085611 168085649
    0x1504060f2c040605190c020303010303080106110a061e020403110a05150f03041401020a08040209060604030506011203021e100f0c0c12030f1d01240b0f0f0a0309020f040204 76
    0x40130b0a0060b005190409107110140d0841800d40107501a010281d0300454403580b441c1802040b00206a02000500c10741030700580c2501400f09030075100a4102001155007070140d000320341e071103d005901043c1175102040104c03c000d40040b401e1000d18045440c0d000030351311101000001e0020301c400040c05041000b000405040403006941d000b03000700700740351f5540e0040507581c1c00e90344412010340020b9441c1041104619000c034140d5000101035410b107080c58103580c2c4030b40d9500e406010b0506c810402405000c2094800c100010600d00762600002c0c00001c62242195079032200c0345026800c17800c01c00350700b02115a9201d107041614042d503031000c0ba00010340320605603000c4400c1101c01c05803560100581601580500b60b07032200001c08080114003081c030a03d00711122098542080031254590820508441c1d52070010354000034cc109954400a01c544441d03840f41220b07030b03900300300e011903191420b0f0703095444210994001e40703105c0030701c400030b000304000c0b4403640c012804000180702c40c4c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 168088111 1250 168086861 168086873
    0xf0c020d08090109080304050c100302091003050414030703090f08010b06092e0f030e0c010c1707120c1401060f06140702030703050a02190f0e1504060f2c04 69
    0x142c00c00700d0300e0000076821203141c40700383c0c49038803c540c1518070340d2240c0c5200c6d900f414558030001c1054414641142030021340000100614220719541c1c04140d11440454288003102ca003003412441c0c89030032a9a540400d01d0086c0c81c0031514842d0418082c8414400141035006004400c0700080041c03002e85003070650003c000061a41c0c004c820480d05e0410340d40d20429510026100441e002500d42d0b4038802215000103003507464100011407a60010f0842480c3c590300900914490355000780f01c000b41c00300708a4030092030f000c2d0070806018031021041041840d5001544503100500520007401e5162580b84101e003030740c3e65403050803108000300340c04214141c4503040e0425030600c0d40810034600250f03a000640303030a039541c109403065003040b81c1041c00c51030106820304003824502c900c590b07264a007918107401507503540b0864032403003800000122200000074000340d0300440208104600383c0c031200407520a5010b40a5070602e400c0c0d1040c6110304030051401004164150500710400340d580755281 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 168089361 1250 168088111 168088127
    0x914090c1803010608010522050d050a051908061c15020a110307080d150303050307052a100507030b061c0204080607080402030601050f090406090c120c03060f0c020d 73
    0x10440039040884180c01694013070203484000c0644200100d81030400c0c0c81d0304000d004c5020411625a00c48442000000c4c001113603003440c020141c14500d403201c0c0c0d560f1058510b80302d02d408007211413111009481d6000d0304034040902a820a80f0000e003000c070001400c656071035641c2d002900d500c002d2860300d1643c0085400810351961a441d00c000c04d480002c94603899500310480480b02c200001c101d8081900035803161207105031b10703603050039030107451914054410701c40900580100708001403025846801d8445411a440d503000070b843d08090b4101780152030b016a480d811640b2410302010a017850704c2400ba810400c100101350900d811310500b5034202d003480e81c0080c0c050240d000c1c0000a540c00b0140142441840c01d9120340c0c3c2946083e104150405c0c9058000d45d115454031949124961a24011264003607800030001484989505005010001c998002003c440440100e07104000c0700443d0310007220b22510050041d141c008008209039072004107094010ba000e0384034580d81078070030505 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 168090611 1250 168089361 168089377
    0x110615060417071502070e01031e02060703030e0606010f020c060c010603050607050a020708150a090203010f0227040501060e060703050405060414120c1c170d0c0914090c 75
    0x8028a442da48911110b100507504407a220180c000c42c0040005202d5001c9a1101c403d281c07015107282400e04c10700b22411841804050401141800c4c20702c1c038500850303001d40402ea0024510b40d10384c07560f458014064035000602e92228018100440d069501480050410fa0130640290401c0d103440d10520006c1d8000c080da100181d034031000004082442480030500404641e91a517654400c1401c0280c584105c1f42c1c80202598001c0d612601c40c00a03182c4d580e50081c1c2c1345000455090514000603000d841955504550244001a5941c00f86140900c40030845000b001600154804808000840740240300b811b012540410124640d450000018034581d44607042c0b40381016110000700d03401d070b0455000110000c9481c50155698504498110a07070110f450090012a0104020030380d50035280414071a54251020250200100381e2800b5807402c07000e040742501c5003000314180e0081d0030009150800300d00d8000c400b00c2c110780301c0c0445084441d4040d1000ca0b003a00c030b01184604552120314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 168091861 1250 168090611 168090619
    0x80303060418080403051608120301090c0519021b0d0b04021504031e0201031410032301050406150b0a0e0105090d08070506090c0418020d060902060c0a0b07110615 72
    0x402e00b0014842c04043c0014500840051440070012800c2d294021015040007d960f8003040980b08080c000608032415998000d801165001d0400303000c1d50320f030055000b45242081e0f4001c2e00c0440c076174002500c0004031800c40259240081120070300440a02000c40540120b00c000002405403d040348a1701c240030306142c81078a8a69280c448540d21070084682c0b2411200442c180310540da030500943e500e4000001101c420f9003805016402850440d02c0014107500c001c142000c02c83c0c1c00f400e804550110810024042c5180a1070b0410040095600e10300002054041c00704041c000b40080c2c0d06400e00d1a210907640802d141c0042d20341c0d4010300f19159018891080e04000191407038013510b003891041004000c01e0404013802c50412504000c03480c0504c5c603102c12002d440040d48880b00900350161455940e01ca01410100050b0514010103034000c0c07000a42d11040e49400203402d00001d0080c01c18402035182d603903081f20407001d88502030381150f0103480803c41c29243e8000050102400030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 168093111 1250 168091861 168091901
    0x14101a0304260c06041a090604020f010504170303041e0201021515120c03061b0714070503030708070b0601080f010b1b0d0302120c030f0117010b130606180803030604 73
    0x550b8001c542c0d40414104203554200105120800590f9040d84000402d0980301e040c41d8540b4221050ba9014010806403144c904403c6000680c0d0140c011140581110645e41c2d0180203040704c041d41d40d40c02613500700c43c2e03100f110488220200072960115615641680030307090300d6140e0784c00102d00400150032aa803042009203011410703542d290540304000e0851000d41131801c0c42e102014184800181141380421004000c60700c0350440000b1074141c250701401d018070a15400510b0b5203080100d40003103400d4800050340d0000c1c03011590180c47c0140c0324245182180d074402004541c0d0132400e5903441d0781080c543c4014401d014805000e00003402244016408034004d020000d403801d4010740111010982c000b40c1c0e0903400c80388482d11944000c000203082d00d107007070024014129450501c00c45010260031855684074440079049000d090348001d05582c10400290607443c01003015100b150046941580e280110b041901c0646c1d084800c030201131800e40d40d900c030901020307050584103850300110f62 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 168094361 1250 168093111 168093173
    0xa0f030615080103150e1207030507050f03040302091501091a2a070801020c0a030305131b0e01090c140313020405041b0b0304210905030114101a0304 66
    0x56240c800c041e16540c42d0019491400d26040c20030740e001007003c038203060004400a91400003541c11400920411a036900c00460604441b90700038000000c1050007a000e40d0400b0035000000f03481524000c50f007564403911200e0088500d075004881040c0810a12035040200200c80403130968900c0380c4800c540d10300b1060110803c00c0501a01140422100d900c800500c03240c0708110501c080c019040085241803009000b0954900384c240c0010101904d4500203014030301c4801d00c55844a03406010303500109244d003282c28444145001d9420300000200c000100e081040c000c03000c6d102803903100e616081c0001ca50414040d40014924604a0f030350110030710060300d9070311130301c4c1c8614066800d000002c00c03007113818095051144d00c410100300b002d00a00002c210024006600c07102c102e2050101c21503c401c00b52030309841035028581c0340d40b81c025020182c000202c00f0900c2016121070669a140d00da0000720944940e42d03040e511000030074400140010b51642c1c5401d0380a0703244c00101c00410307103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 168095611 1250 168094361 168094379
    0x30b0702060a0b01020f030702090c09060409230115080a02190e030c0123090307050d0f0201080603030c0d0e06040f06260402180a0b040510030314030c0a0f0306 71
    0x29506100164000d0040141403445441400e00c907400910140c2030000c50824174a54a02400c43d01a220312941004902d4a80ca20011240400d0002c0d240940740c50b603c080e18001014032901c0c0792040500b0130452425203444014440c180c03894a03400d5016448850b0703085135171403802011613110960800c080d0840d000074180300c4111600640d00d861810320310b603050604010084014506010385002100c68201700c540c0c1440c011820003810740d8a600d020000240340c88402e9000c1a001206500c03081c0910402c851100300c018000c2e2100c48003902d848082c5540c178442d905191226811261003518810b20540c10b891070254024602c0e4101910fa10041400e224182c0c04034000c62001490212060080150544135850800e1184440e140c66004911121307115111b48845a00c044001005000c090b403000142910103002000360340b51000754848001100d00090340402c8812000924035240d00040f00c0c03090700268603090074031a80200a0b21552840000c000500d522203c01280d8541 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 168096861 1250 168095611 168095633
    0x30e0f0901080709150f0506160c06051b06011a18031c09060905031e011401080d0201060801020906070308040312050a02190201020703080610260109050705031510030603 75
    0x182140140040b04d01c1c2040240459040700d04d40080c0c8082c0c07010401a4403600801d403401c4a006580d01543c1d2100c5140e1100086401e100080942600f8500802d60070360102c003810940d000e0001c0e07580f90188450100f80c0d5550240325130006407000e020403002240320000a0f10680da08030a402603410603c20000e07080c00a0804028540755041d04504005944401414000c10560801808480c100703000701c2d0321090600000c102198034015040b6142c00f096002e01107103403002ca0350720003550315146072544440d40b01ca4030100541c02d194000c100303400180300301c84c00e94600908252824500369000d96090200806c2581800703252200c40e0440c0d1840e001d407901c241201d00c00180d0b1640701000000303510b83e01048903c01c40e8414042c0d000042d0f004038003103401100c12552400a01040310040304c2602460189032002040c80c40d20489140910895905958114a01380290b541c0c40d01c013150140011190070b1505c0b00800007030b06c07260814017903c41901101d40f07070210303103141c5946511020341 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 168098111 1250 168096861 168096869
    0xc0b03040605101d190903090603050601090612110403170702091003030503040303150b0a050304020301050a110403033b01110f07060e0406030516180204030201050304030e0f0901 79
    0x11000000300020400c1a00c611980098000e0a4100b038900b80101034000d401142c1101d4803007204240403c0c201c04012160400322407040e601030140003034500d0000c0ca0704040344518004039084c0404140a90700079114541a0340c420f03a1201842c25101b814240a0150b024045d00e805800300b0022000c188400d02176002c824280038619030fa04602d01c1401141c00004003503441f0b0300400795040c00044e80c010b0480e81c2142d0035190102c0c2c07201d44900c080c2055481503201c2581c081c400280010003d42140285103e117008a00811036960380d400d00c43c0948403001e1940310029003c000074800280681d14000d081c44074120802600060218912007000150214030080350700c0e1111810b507503901c123604c00c803e10060300251154404001d8441d070307505503074081d03441403050800408005454691118000f1070b000422607004c10016881d035007203507081d8010090030b05030300542410b5080c554021103045a5040c3d44840c5195180c0c0c5007141c103072500483d030075071150800811001b181d03075410105003e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 168099361 1250 168098111 168098129
    0x6060312050715090308040201080601021f0608011103090304171f061503270219060305250801060e180403030b010e0307050a05010509120312101e050103020f070c 72
    0x2e5619041146090b488001000c10b01402e03e030552001a501103003080d00142c0c28208254142c48000060381840d074000582c0114035188005504070092a800030000c488511008000300c0a208020480f01d201c102c03002100ca6004002c01c005208056004400707070303103c140503038200202526009101d02d62010307200303210a4507020240810f403c8001200b11800c09403d041190401410302200d84410911840e26041c032251a40c5003951141707190310740003000010400d80c2994035100003400400013902e0380001d44100b03c0c180070302144461001541110305449080c03041c0e00e07112044070404c5020100c6504482420a00086400348003120781c0a14426100031403018132280004240d0381c0b0503145244a075015000030040ca8450340c4140080d0352081c030b0801d0340d9140040104002410010b40600e940c4070000d04a03207010302000c81180900a0071408041640c1e5842c1d5825031165407103403107403404000d22410042c1c0e40c0654001c0407240300c40c0e1406424504d0f15190241b07004890b0303200040c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 168100611 1250 168099361 168099367
    0x60726010605090901140120030403080f0c1501030c180e01020a1d0613050405060f030d02071d040b1f08070305030706050108061608070e0418020108070f0203160606031205 76
    0x10601d40b40d0350145c058040c1ca48002c81c4015907000080c015090040d200c200000c1c1d00100c501011014011100616044000e6941c1c070400c000e4045150741c01240c00c604240201c0428000e001048904c40d0f0489403c00baa83c00914140180c0c1032180349001c0c1171915803980d8480240b0900c0003030000d810a45119102d001c20107001c0b1941c6440000b80006081c4103450420003a40d264103400c41040c1615425240010140d8900001c911001c91040210740d244c0f103461040f8046a9000501d901520f03005103c010400290752501c4200420994004080110100000e0185801c103900f800314009903040700f0502c1540c543c111800d02a50350010784403508002440c0c010311800e809282d0042540303200503d070920b4461704030b200d006119141e02d001c10000d88007060301c1500ca0034a40000000c020030030420800b50072842c40d58444514000c9000c510070b18009880207024000c10420300050b90042c40c6800003622101c0481411310f58200c803030964606022002c580c05100f070400e030303000701c0e240c00c1d81e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 168101861 1250 168100611 168100627
    0x901021f021902030301080709050a0f1103010f0506031608060102070308211305070302060a05040f14010e1806370f17120f0d0e0303101205060726010605 68
    0x1d46a0b0440181e1019984200010046032800003150003c03104204000201c5840d558503c1b0054811040c43e1a20a420b001082070124041e0008504031a105822101c0040d960000d10040d800704445148000e9a99605007285030300507201142c0c04003051040c0c449031900d0303a851071216002000d07010f50640300c00008a4504094100407600301c4401446103030601500d60714035648a4040c00005d026190224848050a000e4000d440290243c3d4031224012a2220808021483c10407090750002d8560404c111250a24690742c1d010a0101450601c00741d0b03e1409010240981b100d030010354080100c4001a41c14a08118035140c12401c1c4440503400c0c0303040d410095054040e0040307014210102c404007401c5d90300041030802244010310702c80e12410b21100251450080d4040b5501480c14081c0462800c03801200441c072a040060b415201d641d12003a6086100d100306d000180070f03030304c16804102c10a00402040303e04071407111148031506002d2500358041802a03001401245c80412580 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 168103111 1250 168101861 168101887
    0x5040507150221090a0b040801091208090703140a0b0a06060905060c030405040515040903210b18090f0d0f0f031107110406092406030c12020901021f02 67
    0x3440310007a2004008807008104401e4581840041400d122980080c205016460b002141801494940c101607144c0e540c42c4012070207020580380032982d2842c0400c99518031070080c407003240510f6a00000f095000c1c2503903101c0004448180c41c0003181d03ca112010307400202140001c40c40f58400740300205005290800162600103141c00c00c41c481d039005e020302e015410300081510100c034011900070815455004003059400034103c40300e500300d070820501c80141500403104d40c0c0004103102c002c0303100d07890140e4040d00715006500103661199010345034200050540300303d0f60700250701c0d60503607804101c4490286d2030541508100310100f8075100307c8200c0300d604039540300c00d10304050500b40300c1001481038815051103401001800d19600e0206500aa11564000405485610760801080704001803200e02142401171003114408440c402042c05071290181c0030501a80ba191500d0003240c9090780c102039000a10401d0440c400c46c00b0042548d00c08202101d8014141003006a0387c2122545034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 168104361 1250 168103111 168103139
    0xe0a0909061d06090a061505090903190e01050d09110904030215070215060d0606150201090203100204051c110405010e061f05030c0a120203010b090a0905070c080a1205040507 77
    0x11090355007119040001e298400b10b650f80328a0341c046c100051110195000713048051b401c0d00590b070802900420803e901000100070308424a00800f03074150150008d000f100c000050343c90b21400940240052001c81c001d82d0400c04000d84103141001e00d0420403000b180c40c00c001104c3c143c0040e40300303a0500806a201a040d41d800c00701e988080c040045280148440000c00a0811030041184000b5a010712040e82d1146000d0711500403400040c458030031000307020b000b200905070b1090144100c4048085807600c05c40c1c08486001c0c012002d200b6039501d41445440d00408107aa800e100d402100725240d03200c2c41460b0182414010b22040c0c0c0c280780c1b05204504440b84048948107412603405042244c00400b07495114050740c54056880f580040100c5468464010200240b4008400440c543c0545805809003000a032260f01d0070030303500c8200320141c2c2c00139208000841d9000f0001c201003072a8400908030b002c0d10303080040c1c1001c0d1006216044440c03c0b142070b9070036000004188101e13088803944c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 168105611 1250 168104361 168104411
    0x903090f12020d2409140c0a03380a09170306130510120b0f16090605090607050a06050103050f01090221011b0305220809010e0a090906 60
    0x284085020141d0209000d00712542002e00f4580300001a5403034034000c02c462001c07034081d680d01800b24401902c1c06c50706103009100300c43c1c454054807020498038240040c18008803a0001c00311100c1e012252940b2072144580d228450a44013401c2e44901c141c45120800d41c02001c481e900000d90181c0f03818518039a01d4081c1d00300354600000c2040c0b01a60307035034072010f41e0038040400e000a001d4a0380c1030189800303021075110b13000c0c0310f0422146405002c0d0401405100d00d030b440718092010b680b010010300c2c1e0b5640820800010a440d14021311406204070040c004111015000300d28001044e280d151521041581c2240d03423a86138030040c0300b081401d0100c002c1500e05080244107840041d4005607a411215450b107600400c200c036000e00c110400d41041c0000c0c80391440311014121500c0b070007806010120791982e00c68107440e01a19542603843c8100d50080c1d04442c00c1400c00c1c4944004540d0340903000c0b48294050f00c00100803801040e14891352058520601c1c1c00160700000840c408400070700031403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 168106861 1250 168105611 168105629
    0xd0206060604031208070509041e1d1e030f030a020c01110a0912050a020409080a09050a0302090601050c010e061303020f161a0c16050301050f1b0d0608010903090f 72
    0x3007000540070180d021141100c5e00340321a055444920850701e600440414542c01030034840010a86410526000010301c180c1600b805a04941040c1c00d2484501c014100e0b060b510015031004061042d081c00031000441c02d0031b8a18080110440e0340a80d0400e0768000505c1d80e0005805101002c24480e000e09500145426030528240882c09000b000f01d07407041c0410100d007050101c0c10003009000c10290300d40d000b4000c206d15201e9080165554100b1f981600c0800e0015201048920317081006170700702d0394001e00c02030982d41c1d1300d0011030702900012556442903481e00d11007011b0320420f0044600ca0441c03884240010000350600914003e05980e01c02115084044500c0d06102a8a400e006840700c2021a51000d00c2c100070a0b115480755603800c08103802040c5c071500c00d0040728621340040390800c030000d012030313100c00101c2009004291000b0a005d485001402404108080501352440d01c0100020f031107551240d2039801e40d403c504088001640e1124140003500c83d89041c1005001485 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 168108111 1250 168106861 168106867
    0x14040e061c081b0c2e11010203011413050405070b0c0f071e0605030c0405010309030915091d070e01080a14040506040506160207050d021c0b0114060a0504051507020a03050d02060606 80
    0x5071490400c029940c00032a0345240030250170210360040b20481442650240215600c0d07039510320000c6500da64100c5103200b00d51604800d000d1603000d004542c01150002c02034401e0514000c60240507601011205906004810181ca0521070070300400d0010101a00b185081844440c014407034a0801d400c02c1c02800014000d2000f490f10403420384060722002e09000070038904504098481c1040c035401801030100440c4601d0300c56502c41c00c103108452081c103592265103448800900000002c0b650040000c0c81900d03003201943c03190000c10f802c4001d074200050b40a410040303144a01c04e00315070a5403554025420710040000400c9800d0b4080302e200148040a18224402515080c0d2446040d00c100b01003140d800c15903440c0c6240d919120306901058003000c400f80f030310116886091003810b5007a568041000780301d00b041c00407a1085011551180d00e000c0c00c040030403500d0001c003041150700d230109104440060701d03a4003038030019600071002420b21b044a484000d1138268000c0800e0302815041c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 168109361 1250 168108111 168108139
    0x3210f05240d05031e0a02010f0c020a0b0c13080a02031608120705010b041a03010b0a0f120503070512030a0b0105040e0a0c111002070314040e061c081b0c 68
    0x10001c031651120200c8249045030401d0800d5803441c050001d0480c01000d00c8958800c1503000f03400102210b400b542c0003801040c952121420403100001d011001580100c041100003a50b07016500d03901c6080a40b40720b09052101500c0005101d05801ca1816503000307400103404d41c541003002c860546582c5100704801420284c0c1103071101400050600e0f280d0300461f2083c10000c1c29045003028050180c030400041d00347c1c0b01280110583d98042ca4000c0d4600020f4a00ca03051001c01d980560f00b0020300426154500100080c8564803014103035041d0000b80041d000190003030103e0640001c190003581d8803802c003103448008440440600d41d041c0142000200a11440018241e500c054600400176068803442c0d01541c1c07800a06904101034018520341c10402c0d1a50f501a000050082d99440075000c5070300300c40803440c4614081c0140c0c0f20070000004880c1d00c0c0050a0410408841c42d444540b403c0f02d64440d2095003085a10002d013844403124080a10020400080b08034401c44040b80d8202507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 168110611 1250 168109361 168109411
    0x40611060403051207020a0501110304021207060503070c0c030b15090709180b031606050d06050a03020a030b0c1b0601050108070206040209041214030103080405040b12030a030903210f05 82
    0x14138245a491200f991001410f00c80c0288901c601c03198100c0c0080c09540e41d20008100d843e4401c4a0482c401d1001d603550040c107410006d04641560029143c0510f962112601914400d0300380e00111001c02c2003800110000703c002412502602c01401c03400b040b4007076401041042e2100504120070080090740811640070403880401c02088802c1c07000a0210440002ca41090704d2a103540200401544002886580c030000030b04144070140420810300e525402008140075140c800a0760003030710001c1c02e00c0402c840c0c0c06200d03001071710a8a4145000408503005041c1044510a40195003145c1c004104da075803c442c0c035660049040c8080e11062900340d0004088200c050b10140c40c581c200b150382c09260b802810000c0e00c0c2c1d0b4048440648030341c2d480c41c000109a1090203002c1c000c0d403c012161446080003034210014030b10010186050440850b0210014651800103800308121424000440024140005401c0c40342417000f060781d00542d444241556400303040c04036280307186080d207a0041c00d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 168111861 1250 168110611 168110617
    0x3030c080f040b132001110106080c040c02010e0d0e0306060103060e19180b160f1403060109090207031101060b090f0f0328140601030803010e0a0609050c04061106040305 75
    0x290104140c3c80945071080140c010080b007000040c41c42145694443d000241e80d990416012030076680c0006409940c003065082e251144151411503000004000c26481c03e600900c11210300c51000003100c41c01324425519110703c10002030081429a918102e080c1014052240d21400038282441070901d0402d0380e84500d1001859481c08010b207602c81c807208211508403546142032903900c180b116010b810400350b0300c8400c0d904008a12042440c1c40b02c402d0050700a1280d418580e10350580c1c46148000c845201c0d4002170816041124000c8003050081881c4050301029003e542c901d02d075481000155400c54009420516105c2424025800d00381e131800030100140806481810f0b44a0440700401d10b131000c0c0080010851007030080024031100c0701c508544881c0e0145503200b005102401c240c0303403600820b01001e8444001000140300101c624a00117070840101140000c0700c40d6103080c20021140d06441552507088001020011142c0c400c10800f941d0024402508035410a5640603100344 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 168113111 1250 168111861 168111863
    0xc06020102130b0d090813090f0e0303061c0b0109020301090b0d080406050705030d0e0606030d0806090711190308061318030305100f03030210050a0c0c0b0c0c011803030c080f04 78
    0x81d0f0020303c0b9010051560449102c0f90b034810b144540344c8100c8500b08400302c01c1d501a0412080c0f41555400240100d8000c0c0f0b644d0100c520040d41c034540302d60081c42010120b019580c1c0050000018101c00289091507190003040c445000680f0780d418400348505540748000c001d80b26004146560000c0b40404040720105c1d5a60b00342581d444c2d140349451415070080c4100600420710f441060f107400d00020982c18030401089040c1d0f000c030a18010700307a0351440c00707913085600400c00c20f0000702b24a00131135100b680403c4542c112401710701d00054450031820f103d0700850029101600340112030078001d403441e2440d01002c00c107000041c0030160302d4001c050302c035038050105500c6a01050103da1a04045405000c8443e400b080a03034403130801a50700c400000d44000d01314a0100011a6004644100800600702d659410b87d400125118821110000703001d50921030010031201c0c0c1d03035100074440d110040700c810107208518500342c00c0150403215510403070014040340c0010446c080c075928034125802 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 168114361 1250 168113111 168113129
    0xb010e06030a060503060c04060e0603040b01090c11010c09050301060b04030512031f0b030f0604020c0c010e0111070e010e0906010305030a1103070f06020702190b07030311250c0602010213 83
    0x3542c071080080041c2c00c2c02e40c402505802000280050745290000400c2650701607142d0141030fa0000d0103100c0c030b0340304c01c0b14094488152400140b0225081d6081288500708a1808292540341c4018a5086600c000c86041c0400c07581c03001042036040a0080e40010300924480324205071860700c0b9140ca07101d060f14080c01603280040002c004001c411586a81d04030521507031038201e512540034001c26441501c040400502c000009a0a40303400e008442045002c1c01c0a480e034541000019201d000c0c04034600b03414000c4901c1c0c154400d01e800c0003c100101001342d4080c0c03040d454414240310002d006420304009403c03910041c8041880081203a859051034030b409405004411081802d500858000a2203556001005000d00610b0740241074054004c403500700c09207044a58817920400240310381055084140301c0c00010034001d5100020318910310304100d103807882e01407003912018010101400070003110002e00e070134844864440390240140380000c51034854500074000c91054030348540303000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 168115611 1250 168114361 168114367
    0x160602070c0f08030a1d061c090b0a060f05120a0311030d02270a030c0b09010e0402030108071503020c0c1c060e06090d08150609030a0b07050901120b010e06 69
    0x4110720000c99600a01441c4250030003180c0b030b00d5000da240d903c9031009800085100c4500c030400300444c02c0d64003c008004020900d801401218100050800a02d2915440da02e100c1d007800b203044c00c207400d0320600d0b502100007105410100d138068000f045410482c0244030800c920141c010000605100440e0903040074101110301c250f18134614030441c3d414521003400440d00314032581d05114803041c0e0904e096013000350040c40c882803210791a800d10001e07001c2454080c0030004409880018820040c062400007040c9090348045026a4000c1e8403e04844d030042c80108011080102c40440300304d2a890254600019480d00300d9a80391482c0307030b29100d1a04588840e85804003e0100c0800315485901840724000c060680ca80703807101107400070824004d5203800e8501521400c0000e01c20705c44401400c11f0036840c00d05109013130b0426140d240d0035109a60103100860f80f81074215101d00c55547d05c403655024610001016091002078000d1520708101074000e140e81c00442c0108410317010380780746403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 168116861 1250 168115611 168115613
    0x109230106050904020d0f080f09010305090c01120209030102071e17070b011401050c010516080603120d09050c030708030d06050603130204090501020d06060c141c1206030816020307080316060207 86
    0xc7c2a081c04100180103030070004040ba203465410340506405c4109880c1005550307540c000c1da540766540c803210a4001000d0f031500130880c4030720f40d001c2e2006120150006003003d00569a10f02210150051006400c5032000c0180c01c11072941703229051820a000040e00707080c0580d03180b42050b80103000300300108070011030300c58031648618181c0b25a070769800002c0c842030a10700da504d0031650018108800003110440003a8a0f402d0004281c65043e14049400f440c191504580d070009221b0088200e82c02d00481168111507581002200f02401c181c401031651074025455120480d64258001030150b00c0600800c881d00741000c5520b0180d42e01580c02144d548031a252a900a10803004c000594034a00040422041e500103040d00c10548201c0000c2e00d140d40401e100c03590344114030008035004080c58140200c603441612801c00c06540c0f80f4002c40c4d01901c2e82d40b014510342020b08140117034141c0d03001c11425840d0420150005246410265141200c0300312072032282c00c40444090304070340c0c0000341a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 168118111 1250 168116861 168116873
    0x6140109020c1b1302071103060a0b011704080904060303090807060201061d04060b091e090303060d080a090b0f0a17011401030e030409141801050906010e04060b030109230106050904020d 82
    0x1300d07000b41c1c2c96000319a00c41e905e01e40300c9030005600c0e1109000f482000c3c0042e503010010f2165042c080c4050711a900303070520a046001c402d00c001031080760452070900541c01e054a803402294081c52080c1c440d81c002d50304002c44c403442c00c03003140e003c0c02c00c5a0508500f0000c401c50a12101101e08083c070340165150768506050300500205113030a5040490340d4200b20700c0c85c51b80e00800700040008141207206898201c9001d03500d020513075010b035010101007a1000000d074002e0040c1040c01c0d0380e081c60140c050341c40307200b0213107600b000845107003900f80041c544000302c0d071100c604400c480030000840c141c1e50400d0300c481c141c40261042a0305040c2d4030f4035180d00c140e40070000e0b10010012903c080c4078814000064900500098844400ca05480c04002c401024103014040c80307040b0074401407542c1d0b072900004003144040a0310540b40d650362001e4a04581d2021301a40424034013a1200c80d0404041c4082001d525810501034220b0341d161000c2440325980702a02207401940490b040131003000d042c1088 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 168119361 1250 168118111 168118129
    0x10206100b0d020901021f0c03140c0f030402210c1011120d0b0a0305071a07031e090e1608150312220e0103060b010f0807030c02071206140109020c1b 66
    0x344010b2502d47c6800800c0031981c0200071561070b41d80e0240581140c000450484d0309050310103d2402c1d00c03d01c50300c2c92035165840550b40c0107000500e03950703024500e02007104d5600620801b4040f2030b0440500c41c151130130503920b022045003031850030303888807240310b0202c40e22101c9070040c0c1c2c1c42800e40050308000e2808203070032050740d48900034910750b00c0c140c0e07d00d07101d41d5907401407041103112240c21100b403441c1c02c0c404094660081d01a121580e00402c14401c0286540c0152030101c20700050704000705010344907101d541e11401710340c24510450492040d01424626008048030000204040b440c0020b440220301d1080717081d1040003d44d02d500c842400440314a0520941c0000c100301d1240000340c001d42c004109040b0790040c4401c010040012004440c071080c07440822020480d0b5001268116100b07030301c20b00c0d0000740341c8140c600b81c0e902d0348200805442030002c140c9113161107100d1155075000e0049802d0051200032411031a001e6512041511111004c1502c4401000c00718000c00c9611f5981d84 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 168120611 1250 168119361 168119383
    0x2b021201080a062d09022403150303070209011206060b0c030c100204050123070b10031205030601081503012d141012030302090901090609050f011410020a0203011802010206100b0d02090102 83
    0xf0159113039059900b80c00840c2c208989c41d0b045181c009803a80041d0501104036030307882d5009003142c1c91681c03c2c40210b034882103240c002214207a60329a00006d00d4451030008e09002c408200180d6076032501c20760140d1600c0b460240d00001c0900c100010003441c0c0c0c204019007c042c458041449044451802a03140f50050000c084e003403200100c00c103c03149002c003039440c0c262071060000003203605c1a05001c681601045812030b02280e80780001c911100140c4454032210900107002054040c205481e400c0740c0c0e03a076200d1100350102c000800d5501043e0902902c418400041c0404020f8a02402c1d00e9680c019188200041c840240c2030282c14036201e50120307070701800c02404009240d40e640d950b040c000c016a00c5142c00c00c91504012601502c0c0031a84107040f1007000780c03181991403070f00c020041d030566514400c505600c106051840141c03401c1c0a210181081e080c81120300450a0001908065004162104503010900140070601c0c1c40402e480da0900d0300040180c88100b2140180c0c41e081050380 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 168121861 1250 168120611 168120649
    0xd1506080606030709060e13060e0a030302090f0603090a060903050c0f06040204061d240d0b010f0510020a110a0b0c160b2b021201080a062d0902 64
    0x49042800000c03214055041601202c0b04d56a403050290304a441078080d111081400b540450580305034800e140d00e1050103070100060001d102403a080c60700c0003054040340070a80100d1100d05034601014801754107803080d00c01c1c5240d85010308482d83c4801048000410641e61043e0301c00501d4410340c20745203210020b404a881c2101c0600c0110f03956127048500f00d201d203060210110321000240d1101082c501801c2c0441d00c540ca400740e0840200035000d030391162001380b043c400680381c0e890400003885a4012a40010f95504002d00003400422a802582c0542c2e50900b00c220002d41c00203021108941004006482d4401040041c900e003095600c100030110010814007500d00020518440060308451a001626500c8078220b040b1b02824030b0100590000408030031858411442c910082c14110400500d072035040c07240e840e00c1950a030400c65881c0d000c21180410415030b485080000c8100040d8081c074160451815030f121044400c19451043d1142051811912005450041a82c03004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 168123111 1250 168121861 168121871
    0xd091104020c07085d120a090f0209090f0102040e04060b090c0f03040203030409141807060f0c1505010b0c01060518010b0d0e0102030a0b010216030201020d050c10060b2a0c0d15 78
    0x8503001e611b504944851514010040c000c6002e50b21380740700780114a540003142c4402044e0540030004507840082c5021a0b50280c10141400c641c82031000304060318024510b0026418141011000ca0f003558213814002c00c8164188a010ba0203601611045c071b01010300c160390790344c991020078154001c5a10460460703041080f148811140755404510a5500c03040c0c51080c015131041080e520031141c455140450300c50760010707010500c103200d1141441d0244181061340c03214088403800300e92090707024175030341c440c0460340e0496044c0c213000740802090102c604802e5001c102081d42c08004040c45a600056000940180030280b10b8100440ca1381c0500000c5440b03150081c641030140caa0682160300500071554420003007004a070b01c190503681c041c1d00801070300034138040984a82c2d00c6407450304920f10508110510f04042e034041c01020300146518140c548250810103c40369055125440c40c140038143c8241c01e640e80003a80b0841004201c42540500ca01c6d070030072240c642e00400241240c90b0a013 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 168124361 1250 168123111 168123283
    0x405041401170105040b06011202040e0702030703080a05090303060409110306070e04060803030c0a200708071502031c0b06070b0c03060108070c03050d091104020c0708 74
    0x1209429040b11036040503080d100c001d840a0034200d50044800404641440d004601e10754401c030051325554401d8400140b510b0346410030640021012182c0070010b0340b00103404410107600116254101940400030301490618804103030f00c0c0d020003000d5a02840c4e40710080030034020984040c50203801d01405403a9241402c0400520f1a0145003c82d030040341030101c0040e5050002007102e11800a28124500b00b100024048500031400c004002442e5400c510568803282c00340007100042051070000d00241e80781030310341864104016800010764000340100b02c5003046502c1c280c4a0300c50704110005000107110002071180c001c5400240c1854000000c21040c20300c0200198017400090f00d8004c0350ba074801004a400c0d0464050050020b40203000c1c00b120800c4c903130400c40c2107a124040401d414113407880450100c0e040080c440240380d204c0b0f031080282002c140310303215192aa01a0420504603209016160a9070101d20014000558688039030110908810140c103e058079259a18001c58 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 168125611 1250 168124361 168124391
    0x20d0206070b0a0506040c18090b0303090307060f080f0105030a140f072c10090c050904020c100c02060c04170a020d08030405010b010903021003020304030c021f1b0c05060d02040504 80
    0x200b00c4000b40101c0ca400021280c3c50b00032501092066085e5110b080c0d0708e420802c140b00641641d25116400d8841440007040541d0300380007000203001680c0d20b582c030ba5500114001c0103040c4c0a0402d090059220005110315180070842181c684d0700909600c1080d080d0400c5903281018254042420380161040451820141801c0c2401c0410b0030420349600303445007203c809520b03c2528040135000e030302e030000c0114403259049402c04c0240750910b1400e007210100894103076445040d41800329008a03943c9104404d1511038143c8105161004200074940402c0707180b828440c9000d913254182561250001600d01041801c10807036000d445241103c1c01482d04690301d80003541c086a155090000380e0700c0e079500c01d41030001200d4000300142402c24102205030000d50018009400b0060440028409625030110003495200e0380161640f890603012030080c03400c10600b00d030007556000c405c00f070004109051440010745600300da000b030b618800121a00000e12550b8000e541181c00d0221004010300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 168126861 1250 168125611 168125621
    0x60703200613061104050922080a2703023708010501030c06050310050105070203150c0d0c080903070204050603070e072c01090312050c030c0102041409040c03020d0206070b0a 77
    0x4840c050030f204d515410709841e0881d021740c2c0501d5810008440000c0ca090040e40102c0c40000c038035039a034480701001da460b800e8069106400d03030800b00705900d00e03051105600e03000c800c19090300c5100c2102c0341400c59002511400310b10b02c041e01301584100780e658502039001110034400114080c034540c4030f135030744008a018000900c800d40700310404000c00603045001d20102d0f48290f422206079040070f800c000065445400c0164113907010702c0390f83c20000d008010390038101d01800391104c0454030303030b09400986000c4ea0080e03261a000c010b056414041d003141c001003640c6240b541164045240c2e9101c2000c6450210503500c5010700c0e001c60424080340c0f42c1c1000c0903140103141c0c98002010002901001400c006d100014207000a20030f15040020445000c1c10006141d06440d116107000d003404a00391031608030f03128a9840e65400103082100c906070705030040385400c0a03500007600385010f894411110700c262101a015990f440d41c1c2034110f523503560450783c50580c403d0001c005420300c60b00b40b8005203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 168128111 1250 168126861 168126863
    0xc180d0614010f08030306040c051c14090d0525020d080307020105060a23150a020718060e0c030705070f12090806102112080f0a050402060703200613 66
    0x20306580300100300320350745600c090f05445500c0d000b580b8645850040c07200400800d00204c041103010320078240c4140d000c1140056110541d03001041e405542d401003403860740060108085584031001c0f0766601c54114094030038040416040c0344480c6c4e4034400d00c04030030f00f280b20002d51100403607140104101c0410090742c0a002c4030b5008000039a16901400016031040c01001003804a1003d81c0c80b02514001d0301d004131880c0501242c0b444407248070542082c7c6c01c10700c00c60000da000000c0074440c01c1d09125102c0d05d404c000b5a400c0c42003a14020760501480009428034400040000014190501400c00c640b0b4966100c48948480009070030700d80c0245045a010000081c030422000a004800042d014014003c0450102d042450301103480c0c03c1c801b030000e102a40d40d55969565000c07a0040409a40d645044c0d11540c4c0c10745445502e4100c1000c0c010211208185460144009600d5000c241c61620390305042018501121300510003d030150144030b581284038883c01c001001584100e00301090b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 168129361 1250 168128111 168128141
    0x304090603030c0b0901091e0606050303040f081b010c0209040303060b0f040503061501020309100215040602031b0406050f0304060902040606050a0e010201060509060621070906120507080c180d06 86
    0x41c0c070f42c040d00030301f0b84112000181c214086034100403d4807003002c004010091003010300043c8281d640300420b00703541103540310001c44100800200b000400c281b005030b128122001425140700c6080c0c0010b02080c1601501a010340700302400102014060b0f40540c1c00390040d00c091644420090b4107900d0568080d002d82d600900900010900402314400c4030b09858405070080c41c01c0c416040140010300130071598040c1180704030f401384815804a20740c0280618010140984e481c07030090b410341420003150300e558090340d00c100001c1007421350010903641d280383e10044140d41ca40b200d04200c0c0c0030704031594020758040c1c900100040c2045d0000001c09115026480300a4856102d40059088904a200c0c13550400322080014070b192410700018080541e1104002c00070320b010521000061034200c1d665004240c6000d81072111a8222201404151258406212618040000514100014082221001000c01e801c4044c00c20300004d00c020000141c401c4480001506040014040c011501048 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 168130611 1250 168129361 168129383
    0x150703050f07081e031905060301060b0d050103030f020d09060e010c05010e06150d02060d0c140406020d1404140405092a090604020a08010612020d06030b070315050d03050c0304090603030c 83
    0x104c3d10740050384d00c104000050044100c0f04183c6917030117810f004024035899513071042e0124002000b60003400c03541034404c000050a44c150f24000e071010203c41c44d10425540712403943d4140f503a10803111340c166841441c104e40d0701d811100c0140c40986110070014403d5081441710b58075028009143ca2140400350b6102c8442074041082c00040001550003035000481081803404401d600d4000700746d0640c031468000051844210008a950081d801210050304141c506116569010104e030034201c1e5241c0125140a2400c3c485050124080c5581402280c4400c0007035046a41482901d41d8000c0b181c000c260b03ea2000035009145040d8034128601c1001500c0c045003c0782080d20958102ca130321615605000d07420300f0019504802ca68998000b84c580030421014000703447d00402c2c0042d4424001a081d908000320b02038103907038030020304141c03e48002c4130410081e561080028001a00341c00c0c555500e81d8a080d41c10f0451180350400c80116091040001c10190b1080100207440c1c0540704100c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 168131861 1250 168130611 168130657
    0x180f11010e06070b040503070b0c0301061715100c021f03051608073005010302030c01020a12140d0c0c02100201020c0304170102090a03030807030e010902150703050f0708 75
    0x28500710328103009030004020b1060030000340880c400d041e00140600e0481e405c049a580d2041c281890444030b480300080e011004001c444d402c040d030740441104c4034011440038907041d08404030b80e100d801c0100784605100c42c40b1622090042e80e0303c0902980150024aa00c1e50f403555040781c103131890003100d000900e810005103810000c86c140c400030004070380d15035030f068940c1a4225102c0d8510801500c92070f80080340c0368194070044484012100d039a400105413589940105400c1080a845440c155001154201c2c002a1110304001070240c0d103040010a507100750b42c030304405004032810803245914048942210b5070f00103048260b103038421034201800b1081c40c2004c90a0b805040300e2810107500c03d11003848004000540103406003058000103050071822000a1035466003648181d000c51410003d10841581c14051500309011007c0280b140d069a0760102d901022895082043c4510100d008001c2521400498022900d0f17400020b0b11880c2904000005070301140160000d0342d15a80e00c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 168133111 1250 168131861 168131867
    0x5070503070f020c0901091d01020c01090b0f0405070512010209030106080609061008030d0c17070f120c090e0709031227080309040b190906050a0503010b091306180f1101 75
    0x112003441c0245c0000c815918041c81d00300601740040e026001501000342d08600114240f000e070007440c038080b002017100e400c241029484400098100601100c40300c00b004089400002d0b8003003104d10507110070b5200d06041f0807443c0240a40350760719506500b0b20000140b001d0000036001e002d40f00300e00698269458003040991f24000b40e10510a01d90400d0100003003c10955200990360381c0c0c10305019090b90359501400341e58000450745a0007160201010300680e86d40004900190205100e04001f640c00040001e00940308510907040b5440d8104001019103215540f0301d8011075000408200c00440c888020b81807900461400b10001d00322810701c500292031008500480e2046d4002e9032801d0404000e0002401074132800079002051000c08440c40121103005400804405e0f42c0000d40a0902c410004840d42c40d6020900c00d1381082d00c03407046da984d40e0300180d030820707942100c4c0c0b0301d9048107244c01e1015100480141c204064900501003c0c441c14011400c8203911400303200103c822504015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 168134361 1250 168133111 168133123
    0x20f120120120a05040519030302030703110a020307020d0204060b040303090303030e060601081512030a020106080c0d020a170a050109030302070510060e180f1905120307050f0f0d05070503070f02 86
    0x1116007500b442d00810110030855000c5500300d40150203858902c000881d041040701610041100000d81c008100443c48d5410b1003250400780d462074601c0c0c9032240e5050000e41c1c0780034030a03002c0d01c20b01042c42001c00f15940c036884000208102c1400070340341c994a0a01030701c502990310041d030100c3d0030006101d0648001013500c91240005860724003181c2c844049805605951083c226003200071003803a401180c0042002d000312460390343c0045030745400e015005d0306041a5152081c001c4004180c500011b03078400d8520802d50310064440045145c0542c00546441c46020307026215520b0101c0c0d01c81810361603001003c1150040046076008550301f0084e85c00c0310303441d1254200c0100c414000c9100030305040c0640c0395507004d00d01200d044042e0050f000d820901e103905100c0365030030303c18004020020305024039002c4840e50a0054290710305850701401c64800c1c40c04246e51070703a00282c800005100e00c01034511100c3c1b01c2d01d0410480c0392040e009406540151081c0b004200c00510040007a8070010300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 168135611 1250 168134361 168134377
    0xc051014030c07050f010e0c0f090c0a0c020102120d05040201030e0d020607120b0a0e011502060c19090312080906220204020c0703020306090723010c0f020f120120 72
    0x1e25507500c400540800d0381200000300c0c0d050041892920600e0400d0090350084c00512025001e681003800c2082410000300840a000e1340b4180e00708804120251305503250401e444c03c15011226542c40102d040100c036001300000d546010883c803400348080d40c8014440c52003a03c040044288415089560713020142500005a00ca1800240424402d000c0b92f8a04200e80030302050300544a00040c0c0c40098a40024000a0888004000d82a580c008a0380e102a035800907207070a0030a01078600503842a450680040c24055030700c0030103144a107400500941c1c00c014070080c00c8030440401400765405841340d85041c1f00e40c1d4081000c40002c032010501035000818a180405010381c20b00010390040f454440c0341d80540383c000009078406120741d510030f0110801070005035081032403010241c0000786003204110030103026444142d030482074810001d40c0028085a5012503480040d0204030450601c07a00542641da20740120041504a0b117984074a0f040a041d01380402d079401021402030141e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 168136861 1250 168135611 168135647
    0x50c061005100309060209180a05060402070b010b0c030d181a0105101103040506030108031309141801060803040f050a0b03040305030f18060411010e220f090f0c0510 73
    0x1030581c2c40503011354040c440f100d00c510809800c10001000060100d1401001410803003505410401d000501d80709d5280d100004540860800015468616503614140100b21020f9000905140b2440c410402e480c0764545481d0103002540408817007000340085050112214a010111000c142d038074510103070b041e2500a445005030f0082d0580c101d070840760007230b00540940010007001c640d64856000442c003800e101002990b550010203501204c09103103621a003c42440e1412011611807010f2006d038118840c000305040d0000a0700c01140100400d034000c2d44e0910000400141c1d94131018013040c110b900840c0c00c42d01161740d40c2c0501c0d01700e10040b00c005001139010000980b03400741c0ca407002d6030032115844010b0b50120200f1551841c044040d82c1c19180c7d03a10050069a040d039100945441c8684141c0720b000754500800c0050385103c000d09148402640c89140840007203d0580c09100c4007900080c10650a822307509210380301c24100d010b03140c010680e9500b00c0c181c00d4050708841c510343e8442d803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 168138111 1250 168136861 168136879
    0x203010e31140d030e2d0304080c090c0a0c06020a0302090d0308060a301e060203010335090f03070f0e060a06120207020f0d05150a09051b0d02030a03050c061005 71
    0x806c003110303103140040c0041d6103000003d05286100404002910242202da070080c504003003010b0400c4900c820007010b503000341404000c40401e10358880c019100107035100f40c0268441d1614071007900640945040c15801c0214505200c040c1640003803600d00070b00082e1013101015031500c8103c0da05d1801380b182c50500c2480c0c0500f456203500c084d0000b101050181d04001940c0d99400041c4540002400050b00e0064001c401070040c818200c00041000811280c41c4c801030030116100800c001081c0c400754152000850041e4058654030704464170714030000d041c1d5503030301e85a00c8071900c031080d58010038020003409030004002e4203220200c14191801601c4009603200b00b80e265030080c1d07100c240200c4c0c1043c0364580074401c1d80c8894070926803a0b8410005090054841d0740d24035516800207240f04181c030700340114440882c2010441c41100d4134041d11003044004040701181d1b01d4454442c000f5054401d0002c8c1c1c2060550040181905059410035582103498218000c50607564901845501508407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 168139361 1250 168138111 168138133
    0xb010c0203190201050f030901050105030706111e03040803040b0c010507030c02100c03021209010b13060b0405150f13060305060d081902280302100203010e31140d030e 74
    0x282e80360b0850a40305241031071401c68444040c14503030f0010b8601602c0b61303440d80018002850280305074406405103240140c0c0c1a07111144071691120724078082d4070388c080f82c40c006a44008082c0101c07000342c5000000c807551030b6a20030a4001c036a201c85004500740d40f80101040221f03100b0300651841c6140e0380d00810000001c800084014128810320106050b17080007088000721611403014800d1f02d0140001809e0304600301400030f1100840c0c921440303207260040900c20484814240e8040c0c481c1981c000008610700100301d9142d01c02d02c3c2800109500202e040b40c64a4070f40d50110003a10000c1c1d5050005841c1c0c20140928108104070092070580c0c144092203500c0050421100030414510449403c1d0300354107500034601e200190203840519038004500c0c14160104400d0b04100801c4c40d086155603d0242140e03c800d41c0506850b0032041d500502c030051780e408040710000c24441c01d40280b0180038a02e02001d6825402261000d035011700001031016900a00c207508800403220081c0180c0381d90303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 168140611 1250 168139361 168139393
    0x7080f300a0f0e090c091311030a020d06050405150307090e0a060b0415030302010e1501180b0d08031009050c0a0905011b080315010201110412020108060d0209070305040201030b010c0203 82
    0x2454041c03000c02140030700b080181e6440e4140c0a0041700303002e02c416038038002c1405000080b00000ba40c00d42d09420325456000b2006483c013220342c00f8505500c016140c00c842e00046000e400d10354821980281402c05002e501c422000503814180740c11400c03079042c4d0f81d5070300e042c01c180c1e01010309c42495608010307003000100b803441e04a021268070003440010540b0f45c41b003000120785110341082c0c0c0143c0d540c48030300c1200c070010000c4041340000030360036501640c9015482c2c102c2c00703203680000c4209034072007140e03407403544842040403801c1e64040d000d40d890f440e00b011003c6012149204203c0054104030110300210240400c8541801c060350b603da104504010054a8600c4c649240309207000d141203c0358003044031103002d54040d20251001d29000c179289000242918201742a034180c40341c0c01c01c81001a080351500c6030004aa0a08141c6001da4860000400c100a000d8000c0d40100f82a0200240c003649680458440d034400d03201080355501101c01160400140e01e00250540d100100106090803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 168141861 1250 168140611 168140627
    0xb030112080d020d1d0106122904060e06060d0201050d0902030f100603060b06030112120e060711100e030a080304081306020f070902071509020307080f300a 69
    0x1001d00040e0b450401c6004800040741d000b0061a0301c0c040d035808803078101660300000514118401d40c000c0c81003134207082240c0c1204540c802c00402060089034211815050394038000030200d07100b003000880c3d10701810441c020345800400300c0a00d0195000182d903a03e00070412074916030b01030355518140440441002c001340507a407400c1e40c0c14451040710040c103400402c00c03c0c000e801d00407008540c4c0352441c07900005650b105160300788103007001d2005009025903042150003583d00054030744032041c000c61068440d00e0350100c90f2500700600040c000d0501958009800c00028192514403030720341500e40841d040c520700384a00d980754100741d208901043d0040f01654001d40100b080b503140c410318004604824505601c1103003d41c00004010341d1514050041e00001c012080c0190b00e402042e0780c40c488540c52007082c141c5000d0f0340c1c1c001502551020480080948105806c5840603480555410750314100d0208220310050341c1c003240104042c40309030440134104035080180c1010304007901039039689 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 168143111 1250 168141861 168141863
    0x61a09010e0d0c06210b01021c11070e070e150a030e150412020601140607021210050c0306040f06050603060103020901120c0507060b01260601020a0b090607090e010b030112 76
    0x26140e100802c0c04640c0c0d0f01150402070616858a584550001940d100d601010425602c24186840781c82c100a03600450382e800f08041840d25450110385410b41541c442c100c1c0c07101840240310308207000c5034146e4141d140350700400c6191620b21604e80c0d09000c00c41d244620012185d00b101d03003403110707118542c040e411466074076100034155031080249050b50001007104443c00d40b0745402503180c0e41c01d0300780c043c003007a4098401503668003028101840400e600384a8100001e0190020000d80c20041c0810301604244800c100c0040c4054240403860076003d400079103006124902c0c1245207404c8566030310841045983c00351006045a60b20401503000f504600b090b54188014030202070700c1d04219100e2008214115110302d41c03107003507a0030540100c8020784107450600503248800b05454103031145081000042403802e10b03c965a500c0100d040034000d0200a00079104041805244000421500e116801075a2914203880d0744503035104001030301f84185c03006e140041006204070011030b44c00a40c0c1d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 168144361 1250 168143111 168143119
    0xc080c0f0313030201080c0307090519090c0207061107180f0902060a090918080904050a1104081b01140a050c070b030106081f1401030e1618061a09010e 67
    0x5120141034107607401002d1501c084080340714103008540e00601290b810010654009003103207890310020703001403085d00071a0b215030031000b0119111080005404090824280180b0100504a4020356184001d024113408240311661842c07178000001944401c031903903150300303481070740322801c40000804140305503501c4262101c200c440540c80c6e88008004400c0340381d980c0319044e803401e07400c02d04940484081500f089803082c4110007041060b025981c000c0b104403800101038540030303280c1c2d005044c0301c90580c240a40109001810b2040442da11181c40c000d801d00c0400030701100e00440c2c644202810244040c00107001005240d48504040c044c50345c4440100c0781c52903120380307035516550800d070b00000000303050004005156045c25140014079039a0106c609034581001000d0700700e0f070701e840105810150317188440100c840b0200b00400c1e50041fa500030103005074843c0000c110781045080d042412a04080b000100c2c034280c1702d410009201440c12042c10a108000112248a0359000c2217030700c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 168145611 1250 168144361 168144373
    0x40513050a030c03120908180f04060810050906360319020118030206010501050f040b0f0703020d0203090a030b060102031e0a03110403050c010305091014040b15010c080c 75
    0x200c0c104181403426000c0d4660f01c940c03418510f4010441c44c10869400c81103804c0c00c40600010380c9180540310701e01480c002c1d084074180000003059041c144c208032640e0160502900051080c4082002d401441526405104590390041442e50f100c00c141e41000e282c80c15010302c1d185000302058046042d8074550000900102c00300101482d40c2c20a2407141030312903101c15030b2409250244030701d807106002d20409a81806450700c0203512014148542030501a00141406514000d1011503014000c0c200300c142c4c883da400c030030102103a0400d9104602503c60034001021040c0000151074550400a22000c005815980e440940c41c60140c60340303044d0f12082c414201c1d0301c82004050714003105c0c1c7c0721046072103c00c0100d008007a510074041c48a0510b0007000140302090300418100207031042030a011409803140c0540c54580a2502c0200d400a490700308201500d00400302210b00581c01000c42d00065115940d0700440802c80742520382c00708848228900000c0c1e03441d00540702007400c000580e00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 168146861 1250 168145611 168145613
    0x120c0b0310090c09050108150a0b0318010603060c030c08010b0904020a030f0e011b0908060f040c03020909030405040f060b0a08042603010515090303070f02030a02061209010b010f0c02040513 84
    0x42030f95901a04240400c0d03550009120701e581c0f09541c19406031040d00903402c48884000411901d8413140291180e6450020002e8101750160f40c1c102c0c41100648020040540e490a1841c018951040d8901c0007030b051840191300e461082e007040d03041c0e5800f981308900e031110210420000358855105102415100c101c00100d1188a100d1011240310b00800407540e40920000c0340d0142c160b40b005081402415401802400d100040792503005c1c40c4030550401396291400c22803401d920650000754003011810800c13101c10000301c0a0700c1298821307241800032070984100300003501e4084c0a03008560300700f803100c5101d40d0b2180454071b40050260a0701c103031040400001c0d60030008140603004c00f04400000420242c1044004501000000c064450a2125400000351240301c0c20001610130382000c1d107000f05650b001d02950b117915500601142d07842000c0781034811200022a0035107000d510300140f40605500404406030900316503984c00c22440c48036820080142409000704810489400c031442c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 168148111 1250 168146861 168146879
    0xc0f0632030112020111010c05040e060d0c0b13060f0e0607030e1c0203060903040509010501050f2104060c031b2604030e0306130b070c1103060705040906120c0b0310 73
    0x140a02a4600000022401400050502c486e40d41a0031610f030700d44002c0072410b43d40030041c0c80940b4981a44061151948400603480c9550f51802400c441080d200015550080c10003e04034148511a980f00d1980d1307270103081e110740c0d07241414500400c0c4420146000ca180a100030603502d4401e0070850180d84625001c203410708031201442c030044210320171400c1940303020054985d100800700c004620b042c2c148004180855818440c980c14000c002c502c4d00c9441101d1000e8642100004a4404100b44d101c40d420716019010b8030107840ca54600704140f2816442401800c00182e45405c50080391003100e2070448498000000350f110b403a0a2060010782c0510207000c1901490080e980c10035122506810542000009099407a9116441800e82c00252404000360350061043c2405542c0d4603040c20b0400c0404036040304a60f150044d00d0410030b003650040050070545159000800c0019150b03050388042109814019040e01c1e80803000304007080da0748005561001111a110131210341c0d0392015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 168149361 1250 168148111 168148117
    0x1e050901050c0706020304090b091611030d050708150405100b03060609040905101407090603050604020c0a0c03061b2001090506190f05060609010e03120409090c0f0632 74
    0x613001600005030030481c2078054000d5041c003c0d41202c0c070005904107003550740c0b03044100d0040e18003400403c18213908034170410f0040d9000581361a03024002d0780f50141000309044811251441c443d01689025091420940b00300f601c540340c0c0d5440020103908048222045401c024900755001c64104440356098480740a14803529103c3ca0043c100a01c055540205070b400440d40c0100b244440820020707a281e00c8510101107a10b89d0500250513143c1d44040740280c810a104914244030f01181d1500f0002d1001c4402e04490040c01c04100e8110342641389014002c0d01c007000b40001e40502040045291080400c0d580d0340d140c40c00025803011a5582d00e410107504032403603a805a0b4500d8050f042c542c540c01091200040c5010820062616100062030340c042c20306007034100804c400704044680c408111000210fa00d00170710790b458594036041c00001c4c01d50014111a9165501400500301000c0c40d64481552000c0e22030000c1507000d100380104c0c0d81c48070700d240d01704d40040f404154001240c480003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 168150611 1250 168149361 168149369
    0x2031b0a091d011a0a0e0a02040f060807030f020c0c060310031202030316031806090614130201110609060f0718060504090c021518010603050105251e050901050c07 72
    0x18002c0c00d1151403550308644048142c10f0182544130071034070360341c0d64640c150001e4410203240701c000c686805229200034002d9402915030a103100d00085001900401058800c041c1560103118480026800c0400e901800c20110002d0340b00710303a20780340c43c6003110140d60b0080c04e490100c1056623880c2c42c1c0301ca20205c0c280984015030800000c0c0403107518075070314007480d80490b41401e101100c48039004c22144500c1e040c024103426070382c0b8805030811205400060b13200e8406040e9102508203102d99800604180f003040f804a07002001651100402040d007610403d501c502900c00355075142e4001c802001e0080c0000f0800208500c40540b014035070700003c029001d1990340b10b86860818244074215a000102c0c981035600622070110340707d00d02e4030200c4d440220195040d004481103010140540f83c540c00060030b55003030200304804610348000c8502c0c40318040141040b510900310094034a5142d48801d4007808000c0c860080d221400b81006103075485040c5040c92500c808440654241051908 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 168151861 1250 168150611 168150641
    0xb04020d05061002150a05040303090b01060306051201050f011406041e060f020616050c0a0609060e01050c0a08130f1509060f020f18030a0f0b09150402031b0a09 71
    0x705105141c108900011081c50440c001000da40a4805040404160040c4245000e0f5240c1000804251003900072840c410f0f80032044017515612080c024024104c50300860340140d000705502070381004140180c40c012003550030305080590909421905628841800a40208041100140c21848108070750900c0d0355143c902030b04181440710003090300800b002c001c41158880317803c1c800b00f103107002851341e074030585420055030301c6100c4c02c1c2440c00d00c1c11201c409800d4500e171036079010030320541d508059000a400c0d0020810b03561511001015805034070880700006840350006442c03044041722881c9400d00581d480c0034a0140d0342e40300070040b05054034100e541e9855450000401031540110800e05d031003420158201081d10b032000354030340036040b00c03e50007031085100c0c0b126a403018003d540780a90071000701420030460b4245031040e09001e564088003031085003050346008211a444c0c9008990040103081c2110385c006088440c0005c1207400d0741d11060503000050110303414800c000103da4104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 168153111 1250 168151861 168151871
    0x904060e040501050105272e0b04031205031303081504242304050a061a07030206010b0301120602030402040b1e03060c03040203030a14070507091b090323010b04020d 73
    0x4011f0140282e0300c05188442050610710441401c8941d0505030340c040382c04540d804070300910442d54002007600e40900951880098004515204110014403e40e8041c408072030800c0e58101c412100740c4070403105400c1c440c0344d85000c00b000070300c40d650311074000843e101ca200000024100060803520303000c0c850544c0e000c603001c0303c480d901c00c0f0803c85001080c0c1500722003819042e0a006031481c01d48503208511469441c03000801a0406910560140618201c241149152102045076950001500380d02500c2a5000020160848070460303059424904581c45261442d5990101075000904200d9000744c0700e88003829191074844000001c1c001040b04207a490702c0701d42c18182031035405403103840c048108200700005a10004120341124a9503d01906e890036100003003d0b82c1e000f2184000d04900034100c000800b054544c20003c5c10300d4080d007207003071034400c528016900d1180c0e03840000d0002c0f213010407907a00c0207852400d003043c84e2540c00c004180f07c001c44002404a81c8020114445030ba40c030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 168154361 1250 168153111 168153119
    0x1903060308190e040e1f060e0c0c070b0316030b062101090e031e0c0717030a030b040209010207050f0103090f0f03020712030210050403140304050f01200306060904060e0405010501 79
    0x203e41c030034210b10140c3d410081000765840c0180c4580074260148240320380b0201080b01c640312a0b20400c01403901c00c14800e01420242c0709441c0f550700041544119101300400071603090030120449000d401101c0380d80c44c0503031451100b9000341c0400303110707103078070036000d2040c44512002052690608050080c12100d650b060699171400c0300d900400101c8182d0007030010f0b11050130000c50021f450ba80c0884540c0d1114005c0d10070b10b180481c03036041450a00782245003460702017030005c080d01184500d52010302840310000d00f400101e0099250f82d50059100000800c201e00b40b8a9040005c0c00040c580403c03100565252040d24078100385044445d90040008c40c410f1650601c01c040150001c1301c2411700d0341580d610000d580c0d8407101c0c10920f545a80754003040401d8014120f46d01090700d50031074181c90785414100749440b413140645c401500d500300758088444188100681314400c4032455281e045480790000d0010702d411421095800c541d41d001c1c00300e004900c2e801481e01c42c0784510000f28881d814 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 168155611 1250 168154361 168154367
    0x1d070215280c0212040506040509040c050a06030902041a0904260c0705180f180319020604060c090f0e06191712090a090e0a0b0109060303081803190306030819 70
    0x21130713480001d070420f100c1071107244c1e40e900c12201210f1085034182e49a131181d0070807105141d240d9110a610403c00240095160f0701a04540441802100e0802142101c01010183c501024000d0f65000c20300c40e000600080c0024291140317a214001002a48003280500704170640c805034280082e41d000b404108442c0ca4658402420503940c282144801d04083e0748401c280480504005400c170502003c41c9441c100800584920144800e554191081c84110194a8800c1520141c4505092419034a030140c00b440801d000c84079501ca40c561278500c5c040341031103c0030001d4042ca602200c80080704007010796140c0d603000600b0b00020b100d50700f0010750103418544075940c0606407030030606110301486580d0301c1501104444180d003000c240003502866950808064510050a5180c268000309400d0700f00ea01c88070a491003500c925a403521100c03c601401d4268100c4d00d851a441004144030211040c450903040740600c1c200131520315260350f164645a04003145001000b07029520610030280c2c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 168156861 1250 168155611 168155623
    0x3050d0e030105090706080c070f050102040306051801111801030e0d0305070f09060903030c05010914070513091e0c0807080114010510080406051509010f1d070215280c02 75
    0x103000c800800d5121b10b441030151069000420340b012804000c0343c16000d001107102c0700040c0c00d074410000c640d11a26860900b00a0030152010340c108540fa0081a01240301482008900501c0b200300380d05054170140c590000200d01114181015264403500ea13601d0000c0007a40020704603510041440d02c0c0040c401040004014458420001640310402400d50006d01400c103494040c0340800c11b2007018284070f0f0142c2100c040041804101c1c1078424042a4041119026504100c0d00c7d545141c400c0203512056840d40d100141c100200541c0580c2446980000e124956101c2e030300609082e590340030810700b41103955025000d940d4542c0c40c22040c800300c0c41c03440c1d4050207040b200c0c0d00307601031142c0e0b0003400c007400100010051a5610b01165070b85582111800e00d0000040c447d005568480316042d48603100392288184100d8904a010140000040d00d244a40520b900401c03140743c8281c25551400c102404400090501c0b40c0b0303543e41261010b200e401171a0a051001c201044007030402440d2074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 168158111 1250 168156861 168156871
    0x1d0d0f050f0d0c080702040c03061e030312060b0f031302030f0f01230f0c041a0c1009020312180a0e0f060a062705030102030f0403030f1a0402031003050d0e030105 72
    0x2e00103244005503101045e01c03500e035010744000650f0b4001542c2540101429004120702c4603840d500d90281d10100d40070101500c0c429610345500f81c2000080308180d0f60207001d1001340c003005010400c2d81035001d6018503848509521181120f42e215008a400c1442d00da088021076040601d0103180c0f05002d005620b400d1450705491a0108100c0308080091400503229409400100b0b000c13a4070010841c1c10b80d000b5000e02d185841c44c065840940c9036503980311141e102000e0141c8044400176843c0c61180780d6026402a002c2c028007151034400400e00d50101d4281c2c9060014030080c0c1d04c49840e003c2030200504504034882e211810a6101c010b4502c2004160710b1003802148401c1c044694400c072440038400070f4400b0344801c00c4200c1c030f010030100f5003074100540561000c020000c0c400e0903c0c1890340502e002e43c800704040e1b002d900c0d9540555440000d0301d24103020845104080d802c140c0c0c019640000d0510201c440e00340c03a541d440b400c003002c142c0c0c0da5002680603020b802e00c03464280303d416000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 168159361 1250 168158111 168158117
    0x1090b010806280e01060903150507090513060b0d0f0b100f110a050d031e09020108070f03180303020406020f07120813080d080403110d1d0d0f050f0d 66
    0x80ca070107000640c464aa00d1280b520420f6440c20704806540c107202c0c0100a00203080c0e002c40344d50313151040103001546c0c521081c2c40404020802e44001d92541c4a07280c000c207202c6e6904c440d00e50821040c410110719800ca1101d282c4c1d6200c01c0010080c07020405003100000020000c00c451000345418010b403503400c09010302c80d000c2018143c041c15000500f4500007040340c03e10300054004800100e05081d1180d04c0540036000c0c03482e00ca070301c4541c03581c00090a41c070015100300740020582a4102101c1c0002c0c0001c2c0411003038000300384400d01a030440b103c520502c0c0b8000ca980c2c2e040c079014012510a041303045010940224007441115018400c0b1350f0382e140d45500501120303184ca441c0c4070f0150307e05107014291610001c2c00b0023140303c1112011019041c4801182e4030040c481000910042e07003150150b00080298003d9800070b50007098143d00c2500c69034070540c06501068010f00a0400301e8803003076008030202000c200043c80c00703028616041c00b0307001070010040c48030003c03401e28005140900c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 168160611 1250 168159361 168159377
    0xc031109130c0e04090b070809070b180f0d0605010e070c081803030f031807060302030906070f12090804090e03070203100e03040f030f060606020f0a0303020717030f01090b01 77
    0x209844020746515100c41c042008074001c0d00100c816a0000fa44500b280e800030b08042c0980180149403480c180208026611075900b41d94864000380c8645080c0108107000c03100300510750386101090408151008014600302c1a00b22220006101078442042200c0c6691540010807240c0006d4410780e03448075090500c21031402c01a92010154816861255903620440f440340d04a0348081050b1105030a60000c11584d80c02d25022510005c1a548141280d501c603003400032640340e100b030098a0107081c20308010030b0181c60700082540c1a1240d040341d50104090540301000c1c00115000742c48c2c44500500d121f941d1079042c94541b50580b104444c20f801e256104008803801a2400102c0000003a02070300000b8003202d41c50241d50652007154065014150700c58408401c1c0042800c20700a0580320b40b108010056550406a844200c4000c03980301c160840c59034040407034040c3c0c006100c681c2c410340003180c3c52400400d02e004160800d40f6840d50f01550240103000980c0c45110f240400003003400d008003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 168161861 1250 168160611 168160627
    0x4030206150103052701060504020708030a060801020712030c020a060c030b1f091e09090303050a05150306070f02210406020d05090a0b090d050d021f0e0601051011030d0c0311 77
    0x5c0c00d07000001840c1000940d0b09902410840a502c6030015041c001d109540d5100329051410503030b081a1021050a0319000c40019079600520850325500e50000d40b10020340307206e05080d0020802c0b54084810740c001c000520000600d103210754200040d003078800003071100c80e03c0244040d0420040c0d10050b03140c4200410681c55420860b003204844405445100301c030518440c449420945038030540300b103800d0199800030160903810492141e82403100800c4a41d40362600c1d00c0c2600e9002c8420b54040e006000450303101440390240c1411000a401124a920315801d00030f90b04454824590000c900701180c1480b079294140001e450040d420318205007003170200380c0041c0a00c400f81c030656016101c0003551440c9502c0304500411030581110690780200d078036110184d203513000c1d00d0b07010402c03100d00c01c5100100d2441d4030911451002060040a40343c0c200300030311000c45841c0100748107100d4a420300280c14101000140841580a1340204450300c0420010b0144e8150b03840903020110140603e074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 168163111 1250 168161861 168161881
    0x40209031f2c1b0604030f150b0d0c0506160510050103020306070c03121512050610051e040e03070203070b070203010f181b0902070c050f0103061206020307170403020615010305 78
    0x420fa02d100583e144900c0c01c07200040c1c01882103510040c0250400081641441807454040b0741006041e02c080c0460401c0808000da56143d8800040541c042c1550910032070501c2000b0b0071202c0e11a41e44507031100c10589034130303180c00003194040a00c06c1e200c038010b0003141024030405401010b581400e84c0d1707400860350081d00c1d16819091446038165102000d414500c003014030302008102e000340c4184000d105081c0b41e900c50408517400240080244c200003003d09001c40006a0007006940c40307004044044104000303000010040f48480c4400d0200b0005a0703020301c0810b000744072031142950798448901c1407500b5505410000c0c544585040c291440800c000740034804200d1740680e80c400e0703600e541c00f10744d24160025080001d0b924030218458040107000500321007510740480e000c0c0c5c4c10b07800101c011000e5441c3d500410000c80c0766041030344006007041e0041c6401c881c150420a08044185031000080d100c00c176400e800580c4104140b200c0d6007120010003081482c03e213028011454030880d58 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 168164361 1250 168163111 168163123
    0xb031b03070c1704090c110c030304081207080d0e0a060e0a0b04020108040f080316031b1b0c0e0c07060c020a0506190b090c070b0907050f040209031f2c 67
    0xa000c3e40303108841c2100c65940002101c0207044850810001d803410b4480080040791840140d150512a41d40300b181246030002c192012038245c1130003807092070303001950054260040001115503120034020f1401071101d900604005c1d1102c507000f404504004d081c964103444060706001c4064022904c0300012890070503031207920540a0804001c25100c900d84001c55554004018000302404014808688c201a403070428800c0380d076506001548407480031920b9014121429000319992090016120000300c003030314411030049528004942c3c0e00c0c01e2001e00a201120703441114000050143c0800403180304000c10b0b40441d00c024440d10105a580b25511403002d0603410410000c0031101c61600915084504010000340140b400d0b4207109080d800190414034044903658104030000b4003012001507401c0c111a4020114001d00d590201400000d40c84031804a402d800340116040c0501ca070f8482c0884101c1e143c090010303810f014540503501c400f14100c00c1030f00b129100c080f4004009400200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 168165467 1106 168164361 168164363
    0x6140f09190504080706020301031112010e060402040f0228080106080f010b0a0e040525090602030304080c1e01060e160518040f060b031b03070c 64
    0x8000d6216801c940c181d6120405290044a003076080d0461504180995a040d10f02403054884038160f0b4402d03082170702c0e1104070600c00e50030340c10400c031040f440c0c2300000020018641012011611143c02a0010b840749490f140b40b0711100e03120760f0465003078241c000d0000c042080741d20041c444282034051b0120200b110040000341c0107000d12040b500ca1414070a05100c160f003800b404200c075800941c01c0f00100b01c941d211000807600c8500c501805140054081034803a0f00d0b2411501c0c1d01c4001c50010401c02250510400c0500d8002081e030f0f4100303902c115842e49403007180c50300601c0c000003c0740600c035051100389030401764071040d4000d509454004045c06030580e1000128180f22840110741000034204020341d1006a9038000c60700f9025000510102c0c0020303e1211fa00300f0b450407a040740d19094000800d01c9243e02001454610b080c00c0200800d040d840d04240240581080300b030 = true := by decide +kernel

theorem cover : BRFrame.Cov 167985611 168165467 := by
  have h0 := BRFrame.cov_init 167985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 167985611 ≤ n) (h2 : n < 168165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
