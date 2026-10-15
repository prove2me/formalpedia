-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3874
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:55:53.608977+00:00
-- url     : https://prove2.me/submissions/0fb5d510-746e-4da7-8016-eb901cf8206e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 696582733 ≤ n < 696762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 696583983 1250 696582733 696582739
    0x312060e060f040b012304030b16050d090203151306050105010f1715060f030103030f0f090608101e060201050c0c06010509041b181b120b0f060f070312060303080105 73
    0x141c004e8200d078801e640a0350036801c0c040710410403120f40e41000300c0c140d0140c0001d807200151100880c00000d042c0840090304003140c0c1e1a5818000318445010180580010030380c0e151050000b02603901036030400340e030701444041e0b0100b940b07424249410429620305034030903030602c001e410000b400107400000304410003400000340c02c0d00b0707a580401d0303401114854000c990003074400f10302055000d0010005505036402a20380c0240002c8214048910070329032003641c1c00041c8841000c0100350b0044240c0b030703000f00c0c064161580c0c05495148440807c440c0d1040710820ac0351070f50040140ba0f80a200f01a0400320a69880c4d1a04810440700c40d0f40300c4040c0300d40e6001c0d02c0b0140000341403003820002d6610001d542c03241c01c440560f49031180d03c0d40c03022000c1c4070421189040d850f603060450b040f550000c100c0480d08c80404440100038140e00512005c0c001030340069140a0000b901d994401c01000910300c1051446d8590107030303041c004c0185080400d0007001c285402402e0001c43c0d00b00d240300d0b0440d2022 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 696585233 1250 696583983 696583991
    0x60309071a040b040e061009060e010507021203030c03041a010605040902031e0a0b0112051b070c08030721111f060b070b01030b1807030f0f0803130308060d1a06120a0312060e060f04 80
    0x51000c42e09034804080122014000841844407007052e800096000c2d82c01001c20802031030700704005101c80e0f4400e2103020040340b4200010405410142c01840e44080811140803a55800747c5410315850411250f154800d079a03840c401da0550b0b008000003031a4881d019040010740707040b0442951201301c85502c1e0f5621503001c241da004111083c0c501c0800f5201c0d180540791509000d2600b16040300e444040c1d081e06510254036201d81610844411102c3e400401c000d04600303420318207200458003c00340003201540c460102207400b4170020014502148903491100c81e1358034605018003c80400303043c05103a60401e8041101e0b801c0700040039002d480c0c101e01001440c44a40c582003004290801d0020820103012041001c100d03990850480a1406621919480d9403504100034a111400c04018405605044048840100e1591403580000080d0528242d42c585011052a05500440407000a15404060f10b4112458002c41c0003e04203c0c01c500c070f0504124000492020078524668044d69039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 696586483 1250 696585233 696585247
    0x20f0906090604030203030a210e1b011e090911070c061b06110d060501211e050c131401050d05040606170a0b06060309071a040b040e061009060e0105 66
    0xc1c10b04403001181d0040403681d840e43c1c40f000c041c0241a1001e409284e1010b26085450014118004e111100c420f0380c000d451074000080000d00f506042d0001c2c2c5d0b04200804905c81c1d400c402c5401c00c02d00071081b41d120000b10034505240a41a15000507500403210300c00e200a0001a40c002154800d0324030328100b0350342e03401000419007403131401000041d08050400c0c500c450348400d6100100b609a064410505c403041d220300054420884840c00c04040781e4091392000541506540103001075101003829152000d00607400c081542d40c1540c1d0001c0d0540e000529521703203152400c903840200303a0a030601e41468051000608a0700075401d0aa40c8aa2282d00180800c2150b6001c0009442e0260544000b40082072215940781505841222a0700d43c880229103e03107484401c0e41e1041d000040280482030503c03500019401400c0e00c003001e0010b0030b20010131807220060141010b403801244051851510340b04100c1e0000c0d503984031034140303c1412824051607031721841502c2511800e00784503980c0c0e10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 696587733 1250 696586483 696586489
    0x10513142811100906031a0618040e0f1e0d080c0313020d05010506030c09160e01020a08030a0504020108160e09060112090b01060e060412020904140a0c0f09020f090609 74
    0x840c0461140d20103e0080b00c0796680360000140c100352109540c08102d030b9040091401d8404004a5000c0d42c410014000c40350900360541910614000181c408528200303c684c41c1c900c0c060403800308083c1c41d0440c08460550207183c0340d402a002c248170004000d0171b08182c101403c0b84002424920300c00b1800400070b0b01c06811a21246d401d154040c007403000112050608134000e01003a40c8043c844d0060368600d0309a890306140340c0c0e008000c0481c88010000070f0f807800381c414401e28000903055000b480401c802003200100514031614031070201140c80c1c0707400d10004010340c1c1c1c001d00a01582c0300b490b404449655208410b51700030f650644000d1075543b14400181e039038040c0e66a241c0290303414448000c003005050001c95040307130380a490340c60202d6044402c004207405603001d42c81100b0500c2600d0800f5243c010300041d00280501d1414250701a141d1150703003030208055040c1d078018440310741002502000742c0303850001c0035441421030500446040c1001148100d9400d980f0503440450034041e156 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 696588983 1250 696587733 696587753
    0x7210f0c0f0221071a0f16020a180510170c04051b1305270f070504051c03021006061b150519060b03070c02040e0705030105131428 58
    0x601c11900e14000c429103884035503186500d00403514010240350140040c0500602500c1b4131110781c049050404c1190000010000440b0001b40d900114909000071010a420b003a8041e04a1044011849280040c8480540074407507000145401141030005c0c0d80441c045807034000e1840c1103801046513201d102000200811540468584040001c4d075400003c090300c03008800c48a003512400c01c81c0003c400040304c1044400513031303807101650000280030341c08000a543c2e0302c01d0340d03403c0043c20039859002181c200140716800e00c00012102c04400e05040c0c0410404000c10030240040c06498280385000708000214010303c56100203100c244810041081008144040501c2c000c028601e401c1881503400c0c1b0846c0c60b280492440c000000c260780a04108036072149402e83c48140d440c003201c1d402d0000800d4601d404040a01800034085071035038080c000d0b14003a180c1c1c4508012395030158102031460401541d42c40c0c00c03580c0003490302c0c2c02d00c64100c1825900e46080e0b402120480c107c070f0034488054 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 696590233 1250 696588983 696589009
    0x1142701140705120f010b03010e10080d0504083702031f051b3a060b1b150103060b0307172a0108010302060d0f0207210f0c0f02 57
    0xc00101c020030801c568024080c080d07002c44144682c41e00c1c1c07030301301c0c101140110a000d800c0190b101003005000e1106011050741c2c1011a03a000c81403c0360341e4074903880c2000000b01c20003001860018080100550401120030384050041140e11200146003407840403040c10240411303c11705840200d401d540c3e041c03040d0003005040c0c1903640381d241c078000000001018125aa40221026168004030555400b010380d42c0a003943d000304003440f140c65140c5001c5402c4040910070241d01c0c0006a03149100f14050308000b07111442080c0d440d00c607013001030010030b4007075103d482e01e0b580035036108039800e058a4001ea04403034001c0e800044111016010074240403554014540500d1803180d0540e8035180012200701c0c1d145086c061800c4a0442c02c180d0030030602c40c2d0881ea000404510040c000b602c0c044c002403420b10400c82d0001400e030451900300040c2e03041a64103803400c101083c01c28042c02c07007141c0d04031403e0b520761501d50405207d000000e049a5142c2401510300c40400c03101c44115100ca01072384480b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 696591483 1250 696590233 696590261
    0x506010f12091a0121053a020d080a0b0d060b040212091515090f06061306030917030f150301140c0903010b0307050d0311030d0c0f0201142701 63
    0x1e07001003c8800d40b202000b88503417240c40c0c41810362000d020103454440340c0515808030151800248070000d01c100f241c4a088210102c1c0581994403082d420329642a070300034030031a00074203c1c048140802500249005008101980c140820b6181640d900b55240000d01e500c031000180044c0282c000c60000e0258513001824810410700740414808009101d1070b44402606204101d59920010010600780c4000309540020001c1c001c9800c55980d1406580e1000c2e000d45480d0070410140d14840003c001e55001d03101180da914148000d001e000029003c0c032080c0300c1800c510718206103107529401c460051112400300320307801c0281c0701a80e0a41144000180c0c60041031140e040c4840506455840502c00d184258a030000303110007418081042c1c812208001c005003040c220684040d1428540500e40710307000c2c081040321440e2103030300e072040502c00090795480c0d042000c1c9149c4040d084a24420549000b5230060080040c01c03c0c14070031645c0c400c5032840d4400621669200264050429403200c100d0f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 696592733 1250 696591483 696591503
    0xc0f181801030507050d0206040501051803060a1d0d1403100308041805090a1104090c05100509010f05040b160609050106242105100e100e0702010506010f1209 70
    0x50060a0100e001d068a020f041030f03501c059650010062000345003c0700035000682400100304541c06880a020203001c00c0121107034019944000a080003821161400031656400d03d507000d030302c811481c03000401c403108001d0902c0e004800e0050b2010401c400b000c62042c5000001030390740290b140c8440021548604015152901c48050110850207203038103040041c80c100c0015645600000c0300d840349a0403040c44454015045d0900c0042c1c10400c800b0b680c401c803c5400059240c0b2595103800c0b40001d29a280c9494000c1500010034417540b101860040113010301090007092a100b0484a580b041e2400003c65500c4602d48200a484201c4029005501c0d0202c002443c44810450410703168034501c20010b010150035044c0c1d62070002c2ca50840c101282e510a81c1c4846030981d02080c0c021441c183c05080c110b40e5082202c4504204403500d4000c0c40c0c0350207080004103900540c4981210080c0000d2200e40b4101000070005031340c0d240c10004025010300040e178909a00d070300102c041504a40b140c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 696593983 1250 696592733 696592759
    0x141509010515011b033203010305010b090103030f080402041d0615030a05060103020d0c4e0303240303110606010924090b030a1505090c0f18 62
    0x26000305000c8841c81e4000b1007031100700b8a01c0d03224129903004086888554080f80710141c400320307410020f100c06515120b403501c9041011101c11103802c42884214035100d0354035070442c9402d6094810309410340c4d004e21410001840001e4000354002d00d50241d1386050000c550322400020090101c403944114030700050f4040000254010403001d2180e95100700c050744028168080c19625803d103030f0007800c81e170020340060006103007000c1c6080f13196001c0c0d030f000c0c9280d40d02c40c0303030944030700c1040504401480410301e000003200101210150b01c0c12100313104051038120301c103000c210007200c00d50000c04159481c020701a46000010002100d039a0028104254540320f140c013030722800c2c10000700415071040d6400141c0f1036216400d1041520070032402d500c1201030030004604252403002d402c034140704200102258100c0c2a0000d1407052882d0480401d00340e081d0102441c0d80c2070310344c000c0d50040010a00f04150681450111980d1101d441020f80d40c0310070305059110741340c1044c14040d510040f800051 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 696595233 1250 696593983 696594001
    0xd1a060412030906020f1f02070503040810051b251209030501050c041a0f04030602030a0912021c0f0e0603181e0703200a0b0c0f06131415 61
    0x4110664800d843c0d8507446a2682001d9030f840c18024500c0d181e6a005800340511800b0340302c4401100380d2084409030074124607583d103e040d0380164012040b44d500c008105541c054542c002e4035042003200d80030b5800e1102c00d030511412441400407820707044005013002158040c0c2c42c10705c03502c01d5030090100c0c3c0c0c4e90030f45a84007c1c224541031005a5040d802e080100d0f0740054000304030740c05c40c1c00d4401004255440c00d40e40c4541a0002e1800c0602c0c06001e120000100d03e0900041d0300c0341c2e10040001a51009515001c420303200040207000856020108a01504403000c006a2441c135080c148106180007091086034070740003219007030b5007040c0301205100c0340c20f1866150500400600302503840b0301c0b071501d00d828407501000004080a61242130200041191241e102e1a5071030000794014645041c0004111400b80540c03041c044480009040503d901003032000f85c00e604510005071140e4200303409003113800349441d440503100011509402144800c108000505010b03001842e101a00e0081d806c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 696596483 1250 696595233 696595259
    0x20606040506121507200c0d170f0d0606030209031f06080a050114090d050a05030406060806090c010e031b090a060e07020703020f0105030613270c0f09060302060d1a0604 75
    0x17440d0003007074821070301c520405407003241d002c82076400346c0007013401c11a003008000040c00717010000e59100d001110b001029244080050070050508410300c5e94032260246000111130741544038800301481030101200e01d41c1e000c030751034800300c802d07603c44583c80303d440c11000020704a039403140310b1a00c50107080030108081904088101178060070350520319036800d0201c0b07840e4481ca00055000501c108040c102d0140a0009560400e014020019000e500ca0600c10316200098505280543c441c015501721580d0211214034503190071b801a21109040f10103914030f41400600313141c411240704001801d1115039511100c01810b50700626080e5080650700139480e18041d0000b0307401752902c0c5c24052800c1d40a001140d00586d000340840911444159001005203da49a0001c1c0328080346041c07000864401082030540c0c1c050050007043c54507101ca001d0260020746d10101c0700d1810a001040580e68210540359500003032903001c00c0600e42e03d5182403c0d82c2101e100551300c2030000c600400c0c182d8210304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 696597733 1250 696596483 696596491
    0x503030a0c021302030601091802040f0b03040203060114210a020a030c170a0f0b130203030417070f03050706050703021510060e090c030106031e0c2307030206060405061215 76
    0x40c40341c200c807000f0100102a40b10840303203a8041856042c0401404050001a6005200070703a0010306094036540c0c00c1101c0c0450b40c0c0030541e03d89011083c00705514003440310b1401440015406c40300810b508010401590a1000c60060350000000080b52410284420303401203500070114591152607290645061459001d00c50401480d64031007040380e10300152400b0790640050702408240003030351310780c0030042c001890f10b2507103110b482c0c4c2c490040c0c90401c0944007802440074030340184440c940c8054600f1107258048044001c103000e003040411004613071300d0241d603011301d00b190382c44409050591814200e0000e49207034a00820401800f503640c00c030a0819141c136581d0701949155580200001d20600b43d0b5040c846100402c0100040c5019078450040204880304103c1100f42410504049071803e506500101e48041c0e10989013078115650300a0303590b06541c03614100006500c009584540c0100854040c0750384070301003962643d640050307010300040c0d0380c03c0701d0140c1c5850308000d10001c4152 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 696598983 1250 696597733 696597739
    0xf060830030402130b130b2d06070c0f0602100501050d031709071214061f090515100903050d09050303030f06010c1203060302101103090909070503030a0c02 69
    0x640e018010300e4101100412051020006070305644483c1c0800094180303400f030640001d580c4000000c40e6440d840d01a84940a0010001031442c00d400148800c0c41c20045251403038924403104060b000307030581f4400b581c240c0e044e0b40b0030f81c0310026894170208003601c580064a01c0a441403001800c564009031940301f421124406001a03681e450610521601c40d8034000e0108690802c800340108100e81c0090b40400301d842100e80255590600c12800c01c0e1418054405211002c42e100b0074450030001990011055042d14607002d01403203801d142007645000700030510391540085900c15460b07001a10a813100245a0005032040b0034026004c00254403048445000742d10104080502a154440444501038055451030b41c6407101c541845100030041418440d03071307907010310204e0b16100700c0c01c1840c0c003e82c80c00101c25003140100400d804140041504102c6030440d10303240e02da00070080c0e034a00704041e1130301d1800d6168000f8042c2083c003150446a0148404524007424540c0020141d4001e4002c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 696600233 1250 696598983 696599023
    0xa0201090b0c0c0111070f260d120504170d02120c0c07030303050603010f1b030509010209010e120c1018090603020312070f12030507020c09040c05010507060f0608 72
    0x9007051180c1801603008424060f0490040f4603165401940b070110034078024001e403207003d82c40c3c6004100185c40b5401000ca0100820b000003501003043d203908400c822a00018840300e1030101e0028404500445500420ba4540d0b0106040083c01450240d050950118042c1c54004804082c40250008042c1240101c00c8001080740c41d00c0901c00c4030b03806501d540140c60114250b4601703a015041c094041c2e41c00d0b40d81c0300f51b4106d88042502c5121881440e8018500c002d006072040103042d1200904941e481c2d920420101c4626038202e4000940c003101a542140251680c2d541c41e4101442d49030250740214845103c4420582d014507010001501c03040b0200c46140c40d029106c003218081e0000941581c04100310380c1c866081c80c0040c00c0090310620a68034891115030300c0c81c545a10050042010035150400d0042c0c5030340502c00c90701900c005841c65081481d16072102021b6000c1480b03a141400400181001405401d41141680165203001441190fa850b000340f036613112480d84c0007001440c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 696601483 1250 696600233 696600239
    0x11040e09101e0c020c210709022d09100e1009050d0b09120408070905010e040b0a0b060f0705150601020a0302030f0f0c013803031b010207020d050a020109 68
    0x16a1140b480c00510341d801d40d480200591200c00d0040c1a880400402d41c81441c01120032592a4480b110700e60700d0b100c2480720140703d907406076454603c46812080c14140148100d00000802903400b001c0c03202100d461800c1401c00d007024418521075a0441c6070000855078086c10320781e03000400c04a5089095a032401c0450001004603a8034003103018040d0703c00c0303a881c0b005020404030f4401c540c00c005001c0590f15069582c20b00c40d00582d00c90b50007042c0a821004003004081c1c514414503004103048050303c0d0301071600b0b507a8424100ba00511f40e4502581d110540f070000c3d02c030f80341075825001501c2c4400d90b45e01c0c203c1c00d0040e500d002d404a4110010031210000340113502c007080c03480c1800e40c10340046062110001c0b011496070802904182c0c08070f000e01c10001d103140c0074020036010280414560b0100208801110140c0766443d1140d0303a6180d81c5c51046043d51030000442d032540340c191960b440c41c0601c0c03030001d601900c1810b00c0a075018901070012403c0c404045104466580b01b6200c100803555 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 696602733 1250 696601483 696601513
    0x30515030106030b0c1e030415060e160809120c100c210c0512010b0c010e07050616020a030206270102070e0115090b0a020106050307050402030c04061211040e09 71
    0x3d0200401a5102c130011800c500b110001600010a912506805410b040c90b41d0b4091500100c8040c2c03456409804c0c00580e8074524450703200a801c410a140166240c4071070321007a00c0000d60403000410820000240c1c04240900c18500c41b01c10030801290389203105100c0c3d5540741030703015041034468580303d80a48464016040c2000c81c9211548802000481d401c0f648020701c480c980740c20070300508100f1500001281c05005004e001c9044460303807600209041142103d8102c507074251310f580106014805a0341d007105540c0d444108220840c071420f0b40e88086114407555600094200c540070481c6200c1c0340750b80b903000c0081c1e0300d408c1c42d62214007443e1004aaa84003248500b0307140c04805001130010900709034403004020282d00b0064030165803500300e4071269000c447c080005035901c0c4170a000514017030003844c00803c422039041d811030800d4441c0a0040c8200e104038428880200b80500f1074149540041c01c20300c0b0300d215502d032216914000c1d046002c81c02c6400e0582030060b5640c80c01410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 696603983 1250 696602733 696602741
    0x7082d0102181c060203040c03050c01020c1509040e01020a030c0f03180f0206120a2003010305060c030912070c210515090f0f03070201020618120a031103070305150301 74
    0x5200340c580914482081410b00c0241101c0000740e60f00300344002c0b00c1c0c40108045000440c001c520481c0f9003d8803034a581815828607900c19090350445d0041074250034030307a407210741141c403188246008580c0e950310400020003c180b500c200f01115400403400030000d540543c8152003104140d05ea510452480394070441c111800702c24800607032a0001001004510507030750074602d451019024518102c14440029400c1c0030880c0d80801003600c40ca83c0c050003400a0b140101d001a034034040c2400d650440d5140d584884000b00a00c0c20070402000181d07060f034040254002d07588103001d802e42d03140c0350380c2021414070255000c2d0b00d00c0c001140c00da5002141940c504e03880d00c9034000c6c02030820f803c10740e0b10114008201034048419841841c2070105240c50900201d2029030544000f55641c110a00c00a410140004c21241740341c01c0c9580408004403010549900651200710002e58403100c014080d00204111250096119004010800d0b8181c060707101d98020408441d1050540c9480301c1018203036 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 696605233 1250 696603983 696603997
    0xf05010c18080703080f040e0f010302030f010b060706180b01030c0509150d0611040b16110f0a1401050d021605120405331603032004150207082d0102 66
    0xba9225107001c0000c120340b0301c09042c10059000c41c2c0c034074095a03a030303a0078000b510584040c41940f444034010803c41c41d00b000601801110341000340b01c50445100040c96a01411b42e01500302d0352100d916010480c0360311100c52605502440f41c19407545c40b03081000d03140d000d900645001e01e0030040803420f820843d1a4004e07403034800602030024009143d0391030b4081c10040144150b050810300020641e010b400001d41128241ca03030042460309514184480800b502501c41400f9002c401f00c07a030b6003600d548690a0666210f2842138080440690049803a441601c00b81100240b010680c02c012100e25110802214025401c03a210381c8548482c140c41407081d44a4241e20219584000e444070141c00d6a0050722984200c841c500e4808640d0711446582c00b192500c42403010344600d01c03080641512803403a81c442a40c082c640400550a2000600e04c9103000d1018404413240c90311400d40d108020490140c40208103490900c05025400700c1e41801c00c00194185c840ea440c49858019014400c0d213a103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 696606483 1250 696605233 696605249
    0x6050105010912060f0902100309020324011208162102070e07030f020c01150314060105060406050702121204060201060b030906060118031205040302040c05070f1e0f05010c18 77
    0x250f03500b295141001403e40480c20002c1948410070b000141e40c0319110200c1d00c0300140c802103805111303403042605010501946c051380310082540101a9201c006032181550414082a201d84009040c0440c1c280241000d02c0703007101c64501403400f0041445001107610f441c8205805644035250b009a03120707400d0b070107221011107e039400540c425119030800000b2510805006282c959440803050030b48035a10501004130224140820410003210401c201c51240701002d00b44a50524001038064407841c4148000c01c28040341c40015591686403290001c2c0340481140c519141070395001030140c01c244030300030140d460f085c0001840e04440f01102e10800000000d480555600b000560300e59514000303031140c00018140220014440340c1e8400070340b40300d03501d80d0740c1c49910b948100030503200c00c41304c48000c202d428411140043d0300381151190310b40d8030072206400c1009808e10540e0a90f61001d020313001c40080b007020014003a066100c0401e0200983da400b20310301707500d840840e00c01c54520568070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 696607733 1250 696606483 696606509
    0xf0614071704110a05031605010f180317090402030a050f0c0909190615021c03060305060a0504061e0516091d150a031b0e270a02060f07060501050109 66
    0x600440c0151070b20f8800140030031400394580020138900101d4481000f032014000384240550768001c1d042e00300c0c0d080c80749000b903081c043e1207402242203242440300500003070410400090701031031302080c0c401400340984110749034a4250b9003240540020f8624001d500003941c00b003104010048200d8450580c05448e0807140e495001e54502d0020740144082a12961041e0108150200c0008007132614023550042107850f0107092000042c415940302c8005040c83c00404200148003c50402e40c05a020350340080c040d980c50900d40f000c0c04038400ca80754203202841205440740b20310b520440c042d01c02a41144500d016100098078007078180d005280802d5107103402d01d1210308000c030120ba4000103034000038506410120100e01c4101180c0c20456a5424200000c090500208140e8000749918210b8034103d04020170034410107c0ca00504c4078820b80d80600c041c01c0b41c0700412000e04c02030f5010f824a565074100380442881c0344c1260710308032181030400f0000a00d40d8403420895058850740001c40c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 696608983 1250 696607733 696607741
    0x1206090509120f0705061303110102031006031d030a090f090209010e090a09050a0b0406050a0c051b0102130f030203070f0602100504050a050a050d03110310030303050907030f06140717 81
    0x88020b4000a000800400b0f0810180f000114188042070041d1148600c854100516242c0900300f003c9008581044c0da1060003001390702c1e0000c89901c0c003100c6460600040600c51500b410140d400c0408465030203220004140f950350f41d2002c284070803038151070340503a4595150b0f07941c582039100f05c0301c00900240b03444200300401c0c80c0001403107400c03c041e5000010b1156080d0341d660309001c540c00c01580c410041c1743c100030600105000309603001418807000c200345a071400c4060071310b0261822842003c0c44400074a4146070703096040b5004003140c0b600d400990395840714400e44900780c0380000c031b000b802444400284c0e8820140c0c4031050740c01c00e40203031414101e100d01d841c00400340280705450034840c0c138003041c2c0840c03401d0007185046d038015400350240d40c000380b401401761003074102c00300fa41820400402c82c56010040300d480680794145008940e0303854030400a841c000c100d4001810119400e0607040400500b40d10012000390455850f150030398600d1805e03540196402449106031080100207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 696610233 1250 696608983 696609013
    0x1a191d0f030f090f19030609120503061f030e010e07060f02060114091005060703020a0c0510023018130204060507020d170a021b06031603050a060b07031206090509 72
    0x1180c0c824010f4211050b52014095040b4040811b5100351820f6580d0a0381742c0c140915001e443c42c442000781070031032031070410703030003103518200b0041681000103050001e1071111442a000641c2215504000380240411500da49844260b10b10030000800c444d6103584107501c0c0081030188c12941c045841d00742e511214414481d00003401070003c04c0a40c012140441c0d01d039554005800c4c0d060291380208145401c0c4e26011480720000c0e00160b10074020300c1004101d05a000441401d154100c0d1950765991018000720015482150180050325101080b039400e0f0348131020654034258000c41d40c1481ba5012070012a040b4804e074040c50000034001c22020300503050008501e03142612421080f144807a0b5000ea4074441d0b00000052030050b0042d000c0518503140a03100002d032814201c0d90240785061034480b03640341c80b003081e50000074180c440001410f00321180e88003030002c0441752501a076039500b614000706003540304040b840c0020700d06400442d260455105940c4540710309402010003141c5aa16 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 696611483 1250 696610233 696610249
    0x905390a0617040503070212060708010803030126161229060409150f0603150e280c0e042303040b090303040f0306060806010905041a191d0f030f09 65
    0xc1601c5a210030044100103031504200c8c0b800c000184005000d41d420540703002015800180d2089105a006100501512464404155103e82c0c1c00800428046180300c185023008400400814402844c40c1e0004074087c654900142319449840340408014480d041500081054050101c0c490040f00c0041d000f401e16600561a80c0e02070714510351f54241c2c030400d60080e9131482d4181c0903101d44424041040020891105400061150040c845a544070002c59074414081000300110b4866512a01e208a0810003000025400401402501d5140c08090341180c900b6076044035240701c080c00c510f075200540c00c000c024111300d1401a501c1c00d41740041c200c07000c3e004070169a034540010000011842098500c070301c0154031850011910a01c3e02101a040c080f05910696040e81400304000019100070000321014511401080c856101d241455a41c0c2587c89030802c00e841c5489124140c0d2024459080b10800d9090110f81c0720401900764170ba01c07402500704250300ea000034400d0014178604014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 696612733 1250 696611483 696611491
    0x309060a06150c02180c0405030706020a170304140a06020a0908010509071505270319080301050d0309080a0b1b0f07060b03211201140907030905390a0617 68
    0x61034405140341c908014a6105c1175454040b00c13a0001002c000c182010301456000701803074005004600313607544408160401d58401c0c0c0e141e00c84000b000804000c50b2440301600307645800c0454088031420700d4010025803011740f0150110b1000c2c040047e818405000703041c4202c401d003000c0d207141c902d040459840b0206001000c001d1200520108140c0c0f00030f81306203078150080104000d543d5064000345820203186041c00d60000d0403125443c0301203804541100d0444074151012551642107060440300e07806207420115960040c4500f0740b05124a1040c1d07140200101d151961090504030751800c07662180d0b0341440802c080074400140410781582c0941049a030140964140a0040c25180c04003101702c1c00c000c01d0b00c000844c1c00302d0391507500744080e4050103000d685803492200c00b000052008100411035403c164403a400070080280611011024400f00c4081a0003140c05e0240d14005080006003045031014849990301549080041d100032541151a9100c403c0d88140115011a200030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 696613983 1250 696612733 696612739
    0x306050105151e040815191b0e010e1c050d2102070606080d09080f010c0e06131a041a16120207030f0809120703030906030207030c15020309060a06150c02 68
    0x101c000614501706100045039441e603c000840030b8034188030000500b051035a9400c050500c2c0c0310304d981d01008440440c2c191201e03642400e08a44481c5c00040314580d0f12004400d4025030240e810710050041c218070780060390300c10400d658102601c10b03c11506944207095a1121111010f00c02800c103506500078170300b1074040d0f5804034003181c442c091a45000318460960700090702000c01000700886c1400208411880716000788403009030b41f030009256260100c1102c1c8281da0008040301240b01c0c08480c90020000c3c00e608507181c0210b904c0c5c000040e0000e10403004c000449811401c2c07001451000c89a500e1456041e80c01000c0494440491f03032079060a551082d849048400300216a01c004ca0004803807043d044a640d6400036403d00821155440184c1c0081e0700c0000d0074000641c000d807403034042e21142d24006807260110700f4201d440b0000007402400d400b0741c001c200865001c080d002036206040e00c604643c69512803032b000c5002c96090380b03d40341d0015215540710f81614450092112070a00003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 696615233 1250 696613983 696613987
    0xe030604110621041b1a0a03020f130b09040b091e04080706140403030c050a201006030606030512070819030f14010509090106030302060c0309030708040b03010306050105151e 77
    0x3049980306040056034241e404a01990b0200d0014042c4114803000e02000e0307000c040303074030800180081b0310300414003503a00f8941c021505c1000e0b1030036101541d421a1011000c40d51850b50340001844035800139400c0c500850070320074041118200f42c00c01d5401018481354401858a42c01303c00784403840040d000b00c0d90040200005404924070307001e0040800c0c0c0c080d0000000f81400e2a001d0308642a206c5003505010040c00b5081d1444c1c0c0081c0d840e81c0d44800c1c5800c2000d80065141030908140301c020700642c4e02c600d81000803042c801c1c01d5002409480c810021680e502e621103c200030a030003100401800200c0030000401d10810b40c040c04000c0c4581030401261894408251500751070f0381d00c0c0c2245228420000412588c40c02c01040c40d080125000204012425502c00a44480006002c02d2503188000042240300500b00100d0340100d8206502c503450320b80304c1e04256200d0f48284020f481d06c0342844008a550302c3c2040095041c020300740802c510b4800030350064003a4003108a0150081070003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 696616483 1250 696615233 696615277
    0x90b011110020d061a03060f041e06080f07180f0f050c18040c1b0f05030309070f14090f062b1a2205030c030a0309030e0306041106 58
    0x81040040910981c4400760b200c4410841140444078282d00c00712409459107070340707109501848101d0b0380105083d07032101da014500c100032602074070880644200c0c911507848400440c58561b4404400c0c2d40000b81510414028002000ea5a02040c02031020b03103400c0c0400c003054141a44d1116450000040011481c403843c1e415600c1100c2040318800d00c4114001a507403006c81d001d065142104604603010407114005500003004c824003180c4034810a50709a0500d001d010780c03e034030802102d501c40c080700e50b00d00d4004c200030385502c981d20808414070100c120204804403c810a000c807810003805c20810303a80d4060105520300c802904e03040d08500030231040c2d11120440b001c40079070140c0001c030b0168030f240d1a190584002d0f00d81407070307141200c0b480390a10440411151130450010000c8040340140401c40c2002c500350301c00c20218031043d200000d6102680343d01034210001c190b010b42c0702d00281200001c00c0c185c0f01c40080f5001003e512001701202820300d09a00540700b2051018258059001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 696617733 1250 696616483 696616517
    0x5150603090c04050403030b040b010903031b0203030f07121409010c1101031517120c0c04110c0d181710020c0c04111e070308070e0f0925020c030304090b01 69
    0x34042c5d4050300001d444000c0d07000207003001d02451041c02000e00c0d20920340380ca9620020003c1001303092103c3c0c01c1806102e400d00b50b513401c0042d02c0c0450000800c00344c2c0c40c4d5082c6000c2e00e8580f40c400c140070209624052924410540c401035440d480e4060310380500000c01944d03900c4132401000440740c14183e880082c406400840600300707015044200d480c250f41242140194640b011074420400382050810945550b01000b15400203030318020390380400d52030881ea084160074018031003400c2252040040300001554043ca810710050b904030803d17000c50380c83e40610040700d80801c1400340d460b40100b0b00404046d4495006040302d40d6520705855a00c0c05280010b403c3d50074030f18801040007404905401e81a4000e140c01c4c0c60901c0070400b5902d09a4070766030103019018014402414480103450031500da407500819915150401071034007a00e8a003800c041400c9128021100da0002c08400223003442c207000040380c0701d2011000b4011410585424074a001420300401e0441c108211511401c00c114 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 696618983 1250 696617733 696617741
    0x2130b030f042f060f09060f070201030b1519020c100201060e090109120509010c060c020d020609071a0f070b0c04090b030a03090e0907080607020309031005150603090c04 75
    0x720028144480604280c14401c0c20080d00e8110030200300c02014070031007007480140c0340c02030003003050321340f01d407141d1001d08581d5540c00b40141d0aa0801c4000803c0c41d0100a4500249403d5100b620100001da103904107015000e25611004a080c0c823041140940b0384940f4042c0f01c036003030503e00c11141c000c0003100c00f003070104087c0001003016070b44030642401415002c1d440350380c2c480c0750a00200400da8650b103d03001c4803c00c0024001c180f180009100e00e13141d208444c0c00c4d020540124041c0081095000002c1d40ca84150b46041c0046c012000883e09844010405031f0403030b00c1c0c00e0200d26252003088001c17101c69100000b800483c03007040000e14001255040182c0c45201d131448aa900c5034a420038080a88600041e014820340080c0d0f422000030380c10000c0c010555002d281d80350001e176110703030155107800007a8002c180035120307690820901a80c000003e00e90080b041d400d40300d800c0a0400d10000307070f600548503c8101e03c0d19000807403103414040007561b40140008101c030968640300001c18115 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 696620233 1250 696618983 696618991
    0x1b0b0414040207060b1228020306071b0204060e091014010611011e06030b0a050103080d0902030c0d0804170304150305130f0c060f2d0c05070f050307240302130b03 72
    0x81d0084005003641c401f81580c42e1640a4210b00c003291803091590000b6201d181c0100b04c08148103080581e80e12042581d90640786182d40034108006154550310791101c0702004441c2c03e011407113049582e00001065029840c0c034540c81c0b0304242016401c041d070a4071558410400d981c03e545d40d55003091145203402c0f0307040060002007a0001140c900b1402d0030300601c40020030000c0f031141010300400000e072480703084440031a450100020034290500c0002c1c10810340c48207165101c3c00c5102e0750014490508024000c403210000c0101c0540051003070151280581e21645c00c082099950564040c3c0c0240c000961000c600742e050081c42e4056510003100362680c00d0159403200c1100400e0040940204089648110b1414500c0d10f00d41600d60011300d1711000b842404103020700450440d003a5001c0c8034000c0d4899400030585003030f40c0d1905d00c42c0352070b000030f40304040c4280b04020300060003c1c42c1c1441fa80c140100c2640180c07004a10f1a4290041e51222202020702d100d512000504450143c1c051806 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 696621483 1250 696620233 696620269
    0x120a080319060e040212161a07050a0c050f0103090c0312050903030a0905010807030b030627121e040501020703080f0d0f02130905150127031b0b0414040207060b 71
    0x40e40c2094014040006c013903401c0840568444000300d16068403202c984d900b120340d41010912080c03d01c0741e81d55864081c10304010a988941090304c8100407901e01c1d05c5095880079031707001d038104202d000110207903003075020040d01d0361005280600108043c0441141610000e04040d468041c205000c245507a200c0d04210002030f010100031300056a001c80e02580294880c46d0038010304840300c001030303260900508210011103486c00b107880f507040f409020a01010400043e601c225003201600261030780035a08144c070140b140f2000c0480d084040d01038806461042c2d0040120905590350034001d070b804544602060001809180e012032a54000e1120b414080c90f00035850b9100046072021080150304041e5519042034108403404400749409000034001b480e00e540e0a1183e503641c0102603011000c8030b401041140790100c01c4c401c0c0003880c2001c948895001ca400e0030340c1d84620304820b0185004804001044585005062a0503009007201f940160700c0020316202d00c1000540c800303a40421301c14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 696622733 1250 696621483 696621509
    0x20405060703180906150e130216021521071101020a03060e0a0c0e0112090f05030a140c1b130504060501080c12060c070f140303010e06120a08031906 66
    0x2100008400f800d001041c45080a000c00d1307040000e01405402c00381e1500c1c0400085031320064456840b243c0d0701c20003c100101c01c541ea5650005c0b51803d1401c003d605074001e076440c82d10403410803445402c07148400300d01c0d0010700d841100d400a60000756005000f55042086500500560350400e10080c400000703182c500103480e5203420030310145405c004144603021860101c803100c1d000c0d040f405140d10303a0303000d18000e107202c1d03000482c0c1c02c020540010003802d151001ca0b00c44080020010041080e02d10035101c40c0d08445900311108064468038681124030b4000410003480e442e03024210400500307004002041c0951090040701c1215002c46051300c10365180c100404c1070035030600c0706000400c0240c42070082000040002c82c1c1e240005050b410310302d00005400010300600c0d010010b40103a10094001e02c0c0c000141105070359403c280101400340080c180410120701c5c00800341258a060540034290b45881511141290b400042c8840d8460700d00590350550302d0400c0c03080d00042d00c100e220400e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 696623983 1250 696622733 696622757
    0x1005011503060501050901080c0307091706070e1e0d080c06160905030c0319060209060f03060108062b1112011407080c0f160b0f09060601022e020405060703 69
    0xc00b41c5500ea400039041c044100a009070303c0c3d901601180c0d10109164059940c2d0301c5240c000c6401c1c03860f0350b01c02030701807031003a042d9460201d0120f0164050000c5546e00101821406d040050600000450000301ca100308400640d40c00c143c881d41c01100d008400840c105400000c0280c100f0800b160a200244102e40c0c05145aa8000500c403018000a400901b0000300c2c01c0b0110742e0305c0d02907048a85100d1100c4c101001046180c4e011101c200328003404440d1902c501d2004403a0310b030030075586180800d59040000c1c0581c10407070702151075500c0034900c1201d00c40410f007984c5c1c400302c00880d0648216400e541041c28503141c604c2d0341981c82041400000d4120724403a02800c2d4044098554420001898140805070740070b00e058400702c408180303905550302c100091403407510b00101002024801101c0422401c0030311440e500748900c1007841901d029a8584004980322000e4011044441c207145c610000f220001c41028101400321080c0145402c2c1c840c000501c0386d40240000300d001403241041a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 696625233 1250 696623983 696623987
    0x108010609080d18030507030308040b06031203040b06030f1902031e0307140c041517010c080c09040612050102070507060207120618061e20041710050115 68
    0x1280101410300e8280145800d141c2c1654866074a040c072101000840009120b012080c0c20700d100065a010044030410796507407502414042048070140c0e803108500c80025000d05022607110f8645100d805081d21710740c0c1c2c9940c1e03070454201c060841900b511074500700028031201081143c1c62014106642191040035204042c03a21400034100c41c141c1c41c070145400010640001525901d030b500100d28090014036400c1503241c8181442c08075800380c14072800802c840f800d138000710103485161480c00c00406400c06424240d40c003641c1484000344607440081d08844080e8040d08039034900800100380301e40d980c0e03400601c01c0c0c000e45094400d6540000c1c1c0e5002c00108022110003040e40e800a0001c0034a4507006000c00e5a40b00d00c0505030790740b11400d00000c03241203505500b582d40d016004000f92110710b8103080000110028042e0441c0c645148000f69841700c5002000c2c808031908038078903090429a55035400c240079110800340d44207500c42014409058083c0f2406400f14000f80078616840c6500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 696626483 1250 696625233 696625247
    0x20702031b040c031a21010f0506100201050403090509060a0506071a011509060815063105130207020f060703030b03010b06070b0f06061e03160302030915090a080a0e01 74
    0x60f0205141c5030418800c1034110140820080b00300c04c407409101070400c552002440020204001015464100044410f0103d41d100d54003403641a90354002942e4050800d03401c030341d402d86003d004035001c030340308020b940b8000c0c92003a80314902411201e1203d03500c1c0b010921039040050102c8500c4010f410110b45c0c01140e251030760040c0701d20820045030400d140800382c00c001d05030080004004590780000e4a008070b0050690980d400509641c0d070355120600201807054a2a001400d5000a084a04800c000380300801c829a0001484901d000605100b414001d500200c400c070b800a0002820107001d6940b03501a269480c002c0c2c81c00700f1b50030529001c05086800000c040f0b803040005004c0c42010952248507160710902994480c45141c6407040008d8050040710700e00c901e08070105049503003415040000c0e40c010018444141241d04030344100740c0a900080b1744400e01a4080d40d580d040e0b07407500c503589940158580081d01c80c042c603140c55070342440e401154804046041d81a160f48507582c0210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 696627733 1250 696626483 696626501
    0x506120105010b0a0305090a020a062106051e040e0313030b01060201110d0e070806070207031718100905041a0f011121132402010606080f0703020702031b04 69
    0x80140d90f06200d2044164084d240c4248101692003002a1800c0700801841d2070a5800074000c3e8400c80da00d220080041c3c1c6212001019003030b468442c40c01062182c0103000540383c00400e1040c0f2520800d0440e4a4201045001036000f03403141c0c2039000041d010720041050012180392041058214140240a500103910650071a807426001d01411004402601c030b003480507400100311071300c0f240310580c03410001c3c2e00b102909028060a004c0c00701d8000589400300c070300c1110030310340001580f41861024045e8520580441500d001e80d15414900300074406000081030800403007680c1c4800100d012518014a10031030031303000308541c1807245841812141d043c1c00034038090311350f10160b182031030721140c200300909040b65001605041010b02d00f815a41c0f40d07072401080c020b01a96804000990194034a8220310705081c03146152602c500c107004107016100184c031203e5594840f0451015140001025001055824041d98005130790074480d002c02d080c1258265032040305484108011512040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 696628983 1250 696627733 696627769
    0x1020d0c02030d080903071202031c060b0901050c03040b1317011806020a030207050307060f0c09080303010b0a1b0c0503010c2c0103181407050103062304110703030506 74
    0x1a00000681e0009900c408240d8513207000c04164480e0702c0c660345036000e40c80000302800540460110f013290b000000d003c035111080400803103134181403850390880702c1901400003050420481d60b0441d502800c0280b42c4012032608032440d003030b900c0c4240c0c2c0b8550860140350088001d000760421060482c041010b14039541c000003004540d4140529031025224070030024026500407a08407903540c0298152134403240c00c0400e9a603240c840349040c500030500000480c0b0039910b42500004220300c642d03d40c030709441200000314996400c01640070015045030303418108005601058130b800311074071803841c00014031a99a181c20701e400d0604050030b69500c5410503040000442c01440350000a411288204881c4c1d102107943c0008980100c02600c002d40300d40b9000821070b03821000704449002900e030060405016101d216484500450517203101d440b9442e03c000f031008044100e4550013101c0030a403c40100006034401d5010000c02c0c189d04400010b0300031030f07602d030204030b03607400c0070302d1400002d04003c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 696630233 1250 696628983 696628997
    0xf080105100b032703120901060b0304020102060c0c011b0f020706030b0303070b09010f1506090b070b18100e1e0a0f0b100b040906150c0b070c0203070f120201020d 72
    0x101e25081c940c00024241d104c0c00c007400059625503044d62004144010028003a680d83c1c4a409540466032401601c480c4095031a018001840081000179680607a40c140e018203c245c5403204040c0864000c4904401c0c3d655940c0240c1006900b41000ca0780515516203d1700000e1103c0700020741021243c0c0d10110a050800c200c03002c0c255400f10454400c44c0d841400d00350641c66a000b21030040061080d46000d00b441d0175a11401c00305000d05201c111442940d404001d070303032182c406801e140140708008080007034150115900e602c1c0784405208460141c03003100c10b4211501c1c1c8560940700e400360112950307040b011180d4121000c05038641011114071004006081c856541c2c05150880714101422540390000402d00c182c800c202c0703410080441e8110705465540b14024080144190b20640e104400d080313440b1075010380110b102d10016604820b0501c9141d4038003a061b500021210b00c104d925001d06440820040da2214690000c2e140d04090041180d0252001910b40017070000a230b800c1c8128 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 696631483 1250 696630233 696630239
    0x1081003031e030e06010308070c0605040302010912030302190e24030f07090801020c03130e040b0403031e060f06090602060411010c030c020409030e0418020609090c0903070f08010510 81
    0x44030082c442903056401003600e804003500202c0c02001001d0030001c0d40d000d00c000010a001c1c403003000d04217040c0260045207500e5601e10003591688580d00c0f00034003140e2264400c200c006035401440fa00180642000b5162205910038480da111510540c81d01040ea071200c2480340b400c00c86611713541306030f50520060f00075901b84c40c001518000103000c80c000c0a0144000385040e446440100c000b417040e840255110710f5011492902c80d0000c0040c03600d42c04c84440001081044103008601440c0c02c0740203044e040e222030320210050165245100c16091103656011200e11786445900700500c80f01c805d00d442141403200c010003d00d0f0303d85c030074011035100c2420320000c1501d44091300800a024208100c140c4600c0c40c0984851002000c040c1d40a460b2400c05428142c010036a04d1118008880800c009107000c2165690540c034005c02940280090100540a0408860854100e4000c1c40b4107400c01680300006481d0045942000142c50b002510402081400740107058000222403101c3e221581 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 696632733 1250 696631483 696631487
    0x806130510150e09070303030f021602040506060f04080601051314071b0b0a0b030d0306060e0402030a06050d0524040b062701090b01180b03071206090603030e0108100303 75
    0x1110901940065030b03000d40c0c0b800e101c103001802c001480c00c0c0750150320a15203801444d0312020244002e80100e0b0800c1c020303800c400142d00c2261000d2090f1100c2071448032542c1c00780001004d0041141d03420117020025a01790047e030038094001000300720002d044640c10601409a800d4240d200c3c1d9100c40d007000004661180340110305540081180b50200c81d00f070400e900252091107003100540040d40403030070710000c00c0da65001000046c60a5044030540c1c0c0f00f414048084030318a01c1014005180425039042c0c0e0324181c4c0086801c40c41c546000320707805440e600000c0d120101404100e4056021803007024201710345880f0040044190100c1c0011803400f03884503551090020026403156a00c015138240343da0740040c884005400c5030000c03890b60340e1aa2510002809003081c0c030790200315090151180845050b00d16010b542040c0c003084d0640c2c42e004000e40710061009058a180c9840e100041041646441007800840c041da50b00d84003410781000141800314003600044240e85080c5051000c01e03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 696633983 1250 696632733 696632743
    0x11042603160c0e0c1c140a2405010203030114030f0319141206061b0d0e0112051909031101020d0209040506120a0803060402090a030804060921080a0504180608061305 73
    0x85001c050101c0580301040f50000800d0701c0204214261107000c07d0149243c00e076400011440c481c40c7e0803480085092408201c0c031035880c45001c1c010707481000184804440c200e81d085204d14003800700d0304468001060346007190411010003075031a0440001002040e801007410301141d84d00041580f03421b4804225882400c0018000f500810000400712046804803840e40d039491001400e80342a00d0085d140200342c4d0240e4074203030307001a8502c103545940c01a248101c40c003035101c0403a02c2106071161080c0b000509403d060079000e01c041000c440860000c20300040040d20100e44005030740c1c1403076008202c100d60300039041c1405042c4044920411642c0001c0c040a9140c110b040c07079469a40f140006400b03031051080040e00421069400400c200281e8081e005662464542c01106512054404210b9444d0104280b90395240700003080440d2548004141c00900c6240c2545007544900300d184901d20206034419840b65510010030141c6010710141c0d40083c00c1d160614005040790b21200d50310 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 696635233 1250 696633983 696633997
    0x100b030717070e060315040605120a0f11060c010605010315050f192304050601030504030206130f0605090a0204060b0307270305070806160311042603160c0e0c 70
    0x7501c0e80002262040c1d00829415498020090a041d030320b1504500782024404104000d078001c60400380040344620b00420a140789400c08c200602010780a0b0326030080640560380103590b000700c035101c504001c3c0c0382c40c40180425403180340041400ca01d4540011f0840f00300ea27032f8512608806080600c40c542d602035031182d040350115500c110f0009100d221a00499a41d841078807420b182951042450714030351580e24203a40304a40400041d500c0d40c005500307490742194018010380220001507010b00040807080072035801940e0040d130244d1640d848008440c03042d115001d0903441425000110b152500828021300b4100030b5450860610010142c441d034251104480d1010001240c1c5c0c449102c03c520380c0c001160018200e80c2150b0303885000340d1702e42d5000c0d00c003035120310481c541c0580100d01a026140c90f40c080c0d00007061920b864003c461007980303082024620f1949910420110248041014220414425010420410091819244881140d80112284411038041004413100c5109079088 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 696636483 1250 696635233 696635267
    0x6010b12070e010306090204080a020114070503031303020c03160e0a15050d061e02031807061706130606082e140d08040609030204050a141824100b0307 67
    0x2800d0b0002c0060b07024010a810080d8a0380c808a000100460f000811850315070003078a5440c500c040d04a480e044604c1003000140040d441003000c10088064900801030660281c410384807010750b1040080e04004000c0c075460401403802c2414850140110802e40e00121406c02c04c02c041c9661903256841880c0342d204481c40740158400d80014000300c0c0d001040c15a00c0c1d580711800c961041c1000304001d400907a09840703041c00703411204c0d0804a00149540903144103440b40e207829040c0c21038441410a00911141d000000c0c1c0c4001c0040410901414024113080c0e00c0c0c919903498011529130700900b5680c0d2001a40001220b035010741c4040011202c252241d80105005540c900d00100e9021100d40400034140705000800069190380f1500003030540344200e400b40400c0e1036180b0b4000507281d241d1301d995820f8070110f0100c1e03100210160000c00d40302d210015103000c25040c804100d80002c11a0401c0c818040520800c480c450781a2003050107066608144d501f54100100c009014600e80016044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 696637733 1250 696636483 696636497
    0x30212040e1044010e03180a03050312040c09020a1d010921020a030804090509010605100e19051e040e010c1407170a0c0303060f140409060b09040c0806010b1207 71
    0x541c07500c01000e0075403103400078005d0107110f00c6030641c29942d41c802459941d28100301031840344140b5181d280181140e8106c0000c5080c68030142c5044481040504210380d2032070b0f2101d001038010658005880b070091180c03201c01c05015480001c0078003424281030300c1d0400048034024800c0c00340c21840b249040111314809140c440c50340c80480c80003105600080c04540011500185400304c6030409482400000003d2200d80d40d1142809403401d00c060b108400b04040c5007180c159418030452200d01114204102000650303524049039a156089840c2c004c40c6ea092154140c83e800c26002c0c01601c12283d000030000010720110083c415001c03d140000c2d18403000540c0001c1c0310400b4640c064000d011000196221342c800d01c00b4045421030745040700800d0410b0380c0002c02d0180d800301c2d88100d40c100c46804400c20204e0080200410507118100c6285a071041110000d484210055228520685490f14120b042401140c40c140b03050380180c90103401084800d01e52256003c42903041200c60811030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 696638983 1250 696637733 696637829
    0x80a0f020402070606151115061009090c0f0311030103080306150c120309010c0e061903020c1509060f0601120203060d021201020a11070305030a0c030212040e10 71
    0x40180c42101809041c00f814172101080180c441c266890540d0529250400c9101560003c1d54035440c1c1007082010300c03207862000903d0303814a00f80b001d0310a0b805140c40c2031210307101c580e072004543d4001e402800040742d488529888507014464080c90011048817075007158075650322502c50388002400540601c40e46c4480700c464540c000140e41c48040c114069618082a280001030241c00481e01351107150b003000c50451540d8028402d00b055900042d111038075004003c0506a0301d042c494001c141099400c02c81040301d0002802180040201c3c00c0c0304844c94100754500600d0030001529074402440c00303806001e080da801020088000c0300d485009030b101d0b0340e1100010344c19007006501030f40100062001100840040d4010441d25890713071600000000c016035401d80e500f1050000800340c0c0d008115521030303640070b240c056403440d1192045641000d04a800800c1d280c22a13413048003011a51800d00110945444000c0c01a013200c110302e1000d020407100200c2c07440c1c2014078440c0c2804c401400b072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 696640233 1250 696638983 696638989
    0x110a0609030c080f030402130c17060a0f080109060e0303070c03081005030a05010915091a0907121b140f1225240903120201021e03041a01080a0f02 65
    0x80b101500120004c0d12050254020740c2154403c41d0100d12400a910700048007410f54468040998007690390f0f002c0f20000c010000c4000e0b80044c03d02c03980700c100c1c081c00007180320000c0c9000c80034080b40d900201d002c42d09803a09100f60750740c440d003829091700b013801004070150740160310100058040c5840107158880034182810080b00d50000c1d031305400342020640a0003030540240255a11921130405050700e1046c0c140c2c121516910028071030034880d040c0c1070541e0224040c80790010000c0303066030140340d0307141220080b61600300012185410000300400b65400b540101c1d0000702081009414109104000203050030f1103c2c5d80a4410f903904260030030101c0003002611010000c09001605280b4200c4003606a00045c0c070401c0c20000207402a11489240d03070003004880c10f119103640d85c03d42d003940d03034461144840c0e807542011994240328013200c2c010035a41085011400c1c04503507690f17003030078100f00c2d01198003202034058030110315004001841c000a04229030365040a01401151450300c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 696641483 1250 696640233 696640247
    0x7142506060803070b01050306070203122215060603060e040f031403240406050105070b04030e060706090308151507061401090506030f010b0a03031d03010e100c110a060903 76
    0x5404680740210100e02e240c0c00100806000703001d00022290b5a0382c1d04201595400110340701030050b00184070148140c8817460040ea00041c0d50f0400740074401c0210001e6450700440740094070700700c0304270380a401030b100035101f0f07000507091070706d400e000c0542800400b185803e4040e1000b0314810007509840d007810b00c50003209040490705070b80d4542c3c90414902c0340750400e05080c0d40c80c01d01031145440030a986010300c02c400464206031274050605c0004e84414640b000024400e8081c00b11103284200c0c1e0b66a100000c3c48001e10038000000c15030820f0074014161200180006210501c001d08501199a4000150310010341d42c011560740c1d103810301c0c002003d0072041d0000c2035104031000000c129000e41d504418491a070640c1100e01541020ac070842c00c0e510309064454000300c0520091012030311454a03042250f40703d078141080344010001180c02c40310100300103d03032030701300c810b040050304000d000318288160b441c50001c0750001e00c0d403023941c0c03691a011001490a030b51402d0340c408040c00380207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 696642733 1250 696641483 696641557
    0xf06062015040f0b0f060a050105130521060c13140d120908030d0c080907030f061d0a141e03030f0703090c031202071a19140705010b090714 62
    0xc4c80c0641d42405503a103000000d0030b03030303c440c85407107540004541d9501c10740958003c1c0400040d9516100c0c50f100522441900501c000c6103852401113004101c2c8100f00f0809004401221150f43d03103403402c0035140c603c41d02e940c101131801c03050720101801a41e40e142003030003501d030007214a0180c1c424001003a20300354030a9000034210b020104e0040100c51182d440345643c0c1c5041c2c1c49400c02c90707840c0000c4039101c42c154000284031a007400080000f24600d41e10002c6121141c0c880425100a880d01952405400540850f078855600c80d1540b00c0303c40500280341a03154403412900c1c1c01d110b4201040c0ca070b0000030303c3c0d40c4640048600003000c003442a04541c840c0f035040b1141d06802e03500c90a00200c901400020107015104410307000075103040c50a65401a19003600040b41080403042c22030030300070045c807104400c100059140741e21808110008050a07446400005250f6200c0720a102c4000402060f03a0288228102000c81e141c541e20b0407108603500300c05c000900701c2104400e54200c1c0000c95 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 696643983 1250 696642733 696642743
    0x3100c02100c0e0405010f0509042402042705070e0402070609020d05070305070f060c020d020f0a0b070209060907023d0501090f1b140d0f06062015040f 67
    0x20440d41c50781034000390b044120f40020740341401242c3c0c070780b01d0041c80c1e40598030030140c01881c10000540490840d040c1800182084070341038568007040440341d4182c2e005a0068051442c4000040c1c0e82c41e06084103c0344c0040d0001d4090115140001c80640f9090200c501540210f130001088010440b03143d120300001d550050048100c0d25860604941d255042d0004407017511400c00080780000ca1719104a04807813403075a07800d844461540c2486030540700031508a0b080100407004c10f40e560785154440e006010280600c5488250f035004011080a0180015014100060510040c940d000c50361080b07280c440102c440380590900c405000500004070f007800001180c1c4032852004640b0b8014504803501c0e40c3e81440100c485080b00021505982c09821301071181c85401b0400303601641200c18140c0c46901c000e4202950b0854250546030004540000140e8880040c8441500300b08403020700300c850045007038a01603800b0344540c2e4a119083c05000d5111200c0002d080000d28180c2d101c02c1ca42c45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 696645233 1250 696643983 696643991
    0x10905070b0910030515120f100c021203042117070801090605030c130f1d160605160303090222051602120301140604030c15090f0503100c0210 63
    0x3940d0401882d0b0822000b00d8442c03551940c000ba1082c3c46030103124041c1c2c80308450400401911002c102c039030f41a1032100e0160340500085000309001c2440110035a0400000c046030750810144000c0c200b4080022002000b4001c0c003e0201003034841100710644d00500c1c16250903c0c4281106954050107200c04040c21b0101404002c4400c0c1d0210245040f03d1402d0720a22120707031030700708040d243d00803a04003e80110840846042030340a5800c00d80510b036101e040029003550003100d0049503010f8502c208201d0b84900003031036580307002c000414000e0810780342c882d08207089220300c0410809400b0b4003504241e1100d5a000c195501c403c1d00b02c80d9000482204d5400d200840707004009840c00300c0c1c5c1211074150000301e01d60903500100700500d40d0180561001d01e145e00b810460850ac0410811080d0482000c0c0404400250841600380150040c1c40f602104115141d40040c00d42038182c0001000c1ca14119080101d07481c0018404d08805840801050108a9600403894440b080d0f0516501500f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 696646483 1250 696645233 696645239
    0x30204080a0303090b07140a080a0e03070303060e060d050d0f02011112160203031608090a0b0c030a0b03030901050306090406090b070905040b0d0b0601051e0f1b0109020f060c01090507 81
    0x60b441000600e100340c1402005546c0c03507005548035800740701c4031201c0c0d5404000e92000c2c0362050411035030140f1000d60014403003155102c494a590002e20044011030758a140601c0080c05080703c1340e42c4014100c0348249104055603c050f1248c1c100006ea5090110b496403200d40b590007074014040714480c482c82191106203801d03440b00000802d8071500c0d441d05071054240315461000c400c43c0c2c03080c46002040e07a03c505014404403940c22000f002c5401502503442e5800026000d4a9224011080c0551150b00ca040c12074420702103680d000384c0d580c46a4020801c41c88641d0300714007505c1d0700240889000c1c40580c3d460a106003e406044402404902d120701003000e2190000a4501950b80c1610100041800c003414440e2042000001420f48021600010706030361241c0700904401c5811440f901c6500301c6e040307030145140c024450114088002094802d80039203c004084420102180244044000364010071040b030760901e0114083c007000074a81501c40300940003100307c1c5901c2401c841d08255 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 696647733 1250 696646483 696646487
    0x309050114120705090f09100b0d1d0a140a031e020a0609200411040312110703030e0108060607150b0f1e1903330c170108031315030204080a03 63
    0x1000c21052849010101d00440342407c100081070b02c100c0b201401001c445003005c540b0300b0340790030003403203081825150420b00c0080c201414003a024101d80000034285a483c071724104184400d05102079420740e024000070307400300340c0c02020381c20710a0011043e00c0c00c1414a9008a00381208560701504040c2458008020060440e6041903541c48050500f9400300198042000b40d03001c1d0180714a01c50800d010600224a40c9408290021280d08054544048000034141048410741c41a0042003403040c1510070340d40c01c064034950000d821103819181100c2551102c4003e01d85150440c00301759624150103070781c0c440d24074201c20b00030001e01403281d002c00c4010340b617003040c1c50030035041c043c8001203200c40d00d0130340745108130f03058960001c15540b6282145800800c2e0456030240902c4d01c0c601001c1400c0341c0d510510030108000d80782d90703500c4504807144a6a44c4002c0c0184d0050440b40d0040104648091180c0400b00c161400c02042c4000205000740841c0030740a2900082c1013800f03030480000c1015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 696648983 1250 696647733 696647737
    0x90f06100c0516090b27070e0d050106030618030203270303040f091b0813020a1205030a110f07050d02040e0303090d09050f151b1f0501050306040309050114120705 72
    0x7205801d00384524641301c0140074140f401e194080300c24050315005403040c1b030b000341d041d41e83c0704007541707410340004a08000240d8161340400e410f0310241d65420090050100d80d00654036206084003000b40c0c24000c50340d0080d50b078801c40c5490002740c421004131048204d0701007454940300d0742c01412240c40d103880d4006200b03141c00340d21070406014500801c040009000300404500300c0301a485900c855038070213040b022072201801089034800c2000e0004900041403140d40d60541c0d0080c0e0066848004111014100010003403c041c501da011010200440100107900d0080c0c5da4241c400401071080da101107405001e182202a4080c0000b000304402c0180000d581c8111008943d98880c1c0c07030b56100c0c140503010001252031900200d406002041d000c14401c02055100103c1ca002c2201d158401015070801d0540042c114000c114105041c030328550500807280585000c40c058246410560b4018000d20403034840c02c1e0510414a4086070045030b54420303661000d00120100d8135601d00708000400d40c6d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 696650233 1250 696648983 696648989
    0xb0d080d141003030503010b0a02120a03051501090302030c010507030509130e1002040f0b030402031c0e150306060334200115140a030204020f04050a05090f06100c0516 74
    0x440ca550000d4a0702d94500c041c0e10880b50941c5865107140d0810740100a154080041002540b281c40b510981320f0501138010100300c0c2160b0383c00102414002c10003e007403861001560b040001e80340007840503a0703022682240011003420181d90b620712618060325203009022221ba07102000b00c107802c1503203019130482054600164103aa4051218412040032400f490090498407034112509016a10444d001550800d00050885d018080f516003000d01101c1030079040300025140044c44126824008244014003100b0704103030b82589040404110700c0d000c014001841d8440c2c8100844999007048140204840c0d41300c04641a070300080300240c04445440d2000c5603030214820220390f0450103120b00c0c0070a02c000c106410744a480c0c1200c84c4803280d100d42699034001d5009600000503951413009203c0c440303c070140c0d1070f01c482ca44410002c0c84810b6a1060b40549018010044614045808035034040c00071218642c1c03405440e034040b0307648041940c000b441c51040c2c1c000580d103201481584411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 696651483 1250 696650233 696650261
    0xe030d27050d0515090319030504020f040c170105060a023406030e0d05030103021e01030e0706120b0405041502030c07151407140a270f03110a0b0d0b0d080d 69
    0x11300d03200d9903200c50342c1c1d00c5030900c218103511119130030041c658480d0b080180c01c140010a84040320414000203000c99001900306008602d07091040c0b070404003c0c40c141c81c01000c0440d6001c3c1801e420007400713501c408200c1660800c00f441c0d1301c4140340000304a07030308005d50a080c10390a401d50b5100d25010300101800e220509003031194400764400d451168080324140c981c060a8030700705c0400c132b000e10800e00f6903101866043c076881e1301504601020402013000203240301c1e034403d0300b40c40740a0103080460b00b0300d81c08103000c5c6040000300b201040360001419007110b0303111001696641c074103038100001d01130584020412500c01d1a000900300c80c540091440c2c1940c4942c1d400c2039241c030038050b20b10408000b20543c00110034401b43ca0918002c90109691102c81d040404810300e07410342800b103142e143d4214031110400e0f100180b0a04c4031502c81c118089409a0300c07503140c0307410003040f401c16000d041e03444034286031075240c1c00d007903615181d20f69030701c107030344411002c0d100c0500140c440080c2a114810140c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 696652733 1250 696651483 696651523
    0x130501090c03200a0b1b0115050f0904050c010c0c0f0f061101051b090406170a030f03140a09020d0203011109040b0f060d0203090a0803090d0e030d27050d05 69
    0x1070b180703414001e4140590024007841d44c40d0324105040000d03400c41e445404180310001e800b4203122400b8011041e40b07141d80c0349103482441c00c100400c07802d0301005a42501a400010030040000c3d000512601114024200454081c400e803030040c4041099030030100ea815501e0400166100c0d000b8241c02c10303111952108100955148040c0c0c0c220740702206c40721744010450b2a003022442c200d1008103c074042c00b4101060550710340752012070107600101c0c0c0484903402211800203040d03001c10106242c0e80d4a21341402040340c3d035008603000d4503018000c005034603a2204400b00319070794401c0318040380d82d025000b4000c00c2d000314002920358110383c2c0600e00035030030009331010a1510224030240c42c0d90080c292801c09000d020740000a4200030244192440789091540104100001452007405020001d200614010a00902500481c40c40d203001c1d41c0501c40100d10240c10030b01801c1f84080a0031540c0015890f44440307414170026900a50300100d00310000f406000d000f01e82940c403100341d500409 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 696653983 1250 696652733 696652763
    0x80106030e0c010804110418050a1b271b09060207051c080c0a0807080913090302060f04170d06090501210807050a020405160e09010605070b130501090c03 68
    0x10b62180c01c0c0c4a410350000c0e101c4400540002c00804500007448409400025600001c0d10b0483c1d203501e01c0b403800c0d9010f510001c0d09000300412507a0305013401c03044282280b070140c9050398156107000040d94800215940c002d2000305050258007800481400314200078080891b140058007441d41070090318014021408040313014204102c00060410b0524880e60454009803a01c8c0165045030b4103d03001800307010b0f00000071035440c0300034001c11f07405030240c1540d50588508001d01404180203210b0841e04150504000c0b03038011135904c0e440440c5100c0c4800682e541d2800d000d805004011040c02c00b00082400310f0420040d902642c10340d0780483c020070160b40c0360480801c040c004d2101400780b000e500d0002c4000202c0103c0940552449031085428102c0c0550000b403d90308102c403010340745400750892907161648080600344c00c0f0419a0f081d01594140900100640b280d104003a102542c140e000c91800700c1c0c4030844500f03c1340c114008000b074181c03e10309540d0181c0507120680c0c2000e82c000c102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 696655233 1250 696653983 696654011
    0x12150a1b210c09060809010212010612240303050d140c13080708120d061208090f0d051209030a0206040603020319020a050d0506130f1d030f0403060914010c08010603 73
    0x1202034142070b10350840003450001c04440200c07000305906c410b035400307020004014500c091701902900c0c491301d81482520f00550400212503680f6044048031440d0074501e404503d040d4050070a0701d4240c90140d50f84d41c51103401c10050210a4240c2110354020b4041110000c5640040c1401c100e054807000340c00b543c1c80300302c25690141e502170b15250307804c030301c9854003040f00441c01018042808031011500541d10080000758911030882540d04c0300001660242910786003520500c150030444004401c1100741d00c1e442d0340d0f9292026a40c12064001561340e0302e6980401c0f44c1400c499000304403e507516121030004005e50030a4901d0026180306401014141c4c0c014020750b010558595602d90600c2c08010500018240291841e40c004064081ca145410700c3d900400b40b42e80307102640030800d480400b0006503481d0007801e400d185504240452550010020700b1541101e030098804203c04801c0d040944d111144180c507140c0542c80e0441c1c02c000d40741c114603030358120b0318903460402003a44007a405d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 696656483 1250 696655233 696655241
    0x21801090c0f0503150d0f0501020c070504060e0906010b1821010b0307060f0c06021b0a0c0501020106031e0204140708090705090603030a230a0e0306010512150a1b21 73
    0x1041d0034561803140f590002e03042c680b00000d86140201f07100f28202c902c907210702d401ca0f40000c5146540b03400c0070b8400d00560815004500051030b003080341c1040c1d842c081c46030a448843c180141c9011040000c1c0e01c20300c4c3c170100d032540f0139412001403400c9800c4100c0040c5212008480025540c0c55003030540103402d600d40402c1b80000c41d40c4984403050002d01907101254684020081250b01359824130100704150010303c510a000c0c0c2c21a4000c0041050505104c0c00200041d440f4604580c1001c1081c00021260140002021118852a5072610b824170000b80584a01e0a11010086103032081101c0d00d5489036801e40280c04000540b060030b52140288080c10100301c500640551040040119a0344181c009481240c68079080c004240d004100d1000281e1120ba84180003484403501d20115180520165004040448000340c0f4502c800f142c80d62100c100c980c1ca00f044441a6000070703020b40320390b040682010001803400d06000d8520601038040c4552064034490100c000103400028641c41c89 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 696657733 1250 696656483 696656491
    0x6101809021b0d14160b040f0302010f0e0a1506120b0f07090b030430110c0d021f02240a0f11031b09061206010210110702010c021801090c0f0503 64
    0x5144c140c90441225851210f80c0103030100d052998420844a02041140c96994065403144100300e506041c103040007801d5400182e40c41032058642040090401000920a03c203154460160440342ca12542f00d50000c2503c0d03444400d135240401d104c40f08000507080c120707100d49481c032514802500c41c41c0c0d040f11401402e0041e6003a10908102280c08904520b16420400c00c4900140812184040c20480070350f041083d60000f0441007007600341c4601060059051003070050320b40103250125038000440c1e0140b201a2480f00304595907070494860320030b010070090024204062542c0507542010070010700e50032680700d21340a160515600403501c0b00d0142c0314171040c031140128150349403420b4000b4104081815031581c02401c0249030360036291580500241460520440d007140348c000700182c100200b100b82e1044152500221207212403030001500c480f96020f20303007450307001200d00c0446c1410259040f4020500c680100016032800c2c1500030138040310095807905082802d054095809004c02c3d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 696658983 1250 696657733 696657737
    0xf0302160b04150615030b01020c09040b0907150207320f010909150305010b120a03050d020906120103021e031b0f0907180b030f06101809021b0d 64
    0x10500c200440c0410318015041401140120302011800c0031400403102103901044000c02100c070203406083c2c1510030103245100030b00107000c00182e04d4000904648006200a001301c003808041031174000204000006071603000c848003405c4084100195030b5845600c182030040d5042480203444c032124084406160901c0703103140d0486e0782c0820030070051100307080e55641004828400003070150268000c190b000700362140c2c010b189506509015096962801e00240184041988006481000248014616050701c0c043d922002c0c0c8080c840d004e8813030843d07103541c0308202150b801e0300d4005043d40740c0c0c1264405ca913034900c110080d15904850480c10000c580e80f40d0442d0403c0d164400a0704080d40c1c1e1010001c00585a09425100003401043c003502e58900007240e28511010540b20858528064a00c3d8a0000d003113150010b07820003501c45c0205018000d00d58086091107042c003030302d40302840b070314400c480c462242c0c0c031410090b000f908020001541074800c0344403900145004101442d4503100c43e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 696660233 1250 696658983 696659017
    0x30912040b1b010b1c0c080d02060c090a15030f0c03051009090c0b040b040e09010908090415090e0d0306440709020301090510081c050c0d05030105010f0302 69
    0x803003040b07451001d42040c181c503107548400c90402c0c90b585103a00c201c110340f0032000f030f8034a295560800c040e50a0352900015800d601080f524513503907400080b443e50203001007802503a61403500010514551240c0c1c85045201d07109241c5900b1160141c0040040021103d810481881002c900320243c82d0143d81004955501801c18041043c050b00094506402113030b02c1c0c11500e0741d41c042c284541c1d01c0ba90169a004001050600c45404d040c1c00e0660899202402031150301d403580c40f15200c46c403820500d54070a943d40c0b542e00c18081d62081486000b1710003264104407082100c0c1105071101d104c40c01c0840000d20b4140081202c80320316549910070072003800019001a010810860071611500090140c540c013203401880c003c800300f1200d4060105001c02580703c0d40f500207000c017139441c094201020300404680503c0b925000082010310f1850b030750404c17039407c104120265810300c10070a00d4407060003004201c080f096000300041d03040301d20070f9035030403840b5a203031401310304074001c09290000351048 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 696661483 1250 696660233 696660247
    0x15090403051902120f0901091d010509060d02040f060602010c0809070611100c0905040c0c0506071b080c15010509161d090405100f02120a05071b030203030912040b 72
    0x1c0781c4401d07110408500440340541131080070f6800750b0300075400b440541c400c0000d02da402540d00c0024040104a000e0310001d0340c0101c01000b64a4034014002c0078019040d660005590742c0e20055000d41803500904100a16001d00c80b280010300030038051a0090340c208107520410f6486049240d10a94000d00175082280c1407640840e5948140c059506c40783c1306002104c0e0710b0348103511030f05100c240c158540544151422040c8425240010405420710281007402400302d140822660b921841c145020103000e40d210700c082019140c11040500b00600220300102140c41c00074051040d40b095a0907080207a0340c034810410502070803103103054454004800c28046d503024100b2100008400d0302e9500c2c203155004041a050315040700c0c01e46050784103c120a031500e480d84100445035407039000070752810210b900b5403421040050045003100381e0300c000052010b48110441800302102d86000c0b10a10045e0600075903039003040c1d4105585000300c0d034a8140c0c0703000402c203c50440340090003890a0a030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 696662733 1250 696661483 696661507
    0x912030e0105091b09090c10050a090504110910021207060b180603070303110705100e0906120304140a1a0406030b06091c0212010e010e010b030f1207060902030d081509040305 77
    0x340146c1001414070030004040007a80d510004003c03e8640c5035101c5448441416008008489541c451402245030039141c41d80c082400c03045030205081580c100449841440d800c0745014600b0305800201540412103004108181d088440f0346082201ca40d400b015000b43e0000503690152032007a40f41d400b800c001c200081c0201032000004d000401501c02c00d980c1d03070020030207074400ea80d03101c80003130031384240c0e5147ca140184901343c01803415500c0d2040d281c02080c1c1030b0399a01c01da01601c181401c0c645100b0300b4903564014140c002c3c00545040c20840d1900d011041000d4105014007400b01c0d05051000201c0d003480c0095850003d002401e0402d080c03513600741d05a42041604059800507a64441c003000607209001da118454191000020850f209805031421580360011a51003034000b00910b01c50480000346460120511003122903a4039818541500101b6108500940600801d6a174a4241c0d80000407580703d000c0303d40c6071009600b000300402c50315410442e401000b0030000d2100c08140c0d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 696663983 1250 696662733 696662749
    0x30e0c0a1404390323061c0209012105010e010e12030624090a1e0506030c0a140d0903050a08220605070216030b0402240304060f0912030e0105091b 65
    0x852400d0010f51240c5803840c000035100354420605c1c1c040d00800078001ca03030901c0c0180c5520044075155100304200f040d03001900c440c0c0180f18401e0410319520b01c01c080080d040e40d400740103542c00002000400d0f00c81c0886d501070700c184414111680581c01c0780c2400580341030200c0344506401441c13042e94000040501c1d440342d0074500c4042000c5804d10a440d11505d508441e1400b419030a94103580641180020f0815071205802c01805080300f13200b030041694140d01a0350101409003410b03c2c249940e8400315849001c2c1103505a0544d0415046605140d0080001c2882c0c00d0705681c1d505059441500d80140800d055807a120500c000c698044045802640b180d600510f03584180d035900c1c01d07800c864110b9101190029036006400c4818407003145400340c0c180304a141080c0c0412961090403002c41d0f418000108042c000c162180a400c4103a9a030740e0280c54400ea01920700c90b410001d810001b80100305c2c905a5a00661070503000c110b12050000708034540898022604d4210000c84007400051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 696665233 1250 696663983 696664091
    0xd0f0609031413050301050901090c0e060d0812060102010522060510050d030201050a1803140c1005010605031812040b0f0c0304060c1b0b0a030e0c0a1404 68
    0x70251101c09410102c050082c020240210841d1854504080c00c050031180007820008490b8076000c0d002740060640c0d40d48e007048464190301d411050341c4200100e10a4452604001c068072400541000a40e80148065006582c282c1c000c02040c0d443c90401e12034192070400034000c11100c6c049803070000382240c21150f0300444a410038010140d0b900c1c08103070a0701200d45c2c00c901603511801001828100b92084e18940e104145486001d154107440c040c0038005000380d07071040c400001440310a00b203810130500d40c031108841e100304401c0d0f0b915100200503410507585070a031b0464803180d900422100080386011500c1050342c641c81d00749000818078040d403101201c02d24801040c40b03601c480204c01c2c4050320040c40e0540304c8070007404161419030302001024105403c12114901d0901c51740404c01300755401c44110b4180040d40500300d100d03061a01c42c40500d2a980081000303004a440b2041913072004a9410a540500c8880c55075200001c00030b11741400204d500c60200f05001450044040d00c44c3c86c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 696666483 1250 696665233 696665237
    0x903120201061e0810020325030b0d0b061206010b0306060d090f050115080304120f0f3e090411010c08030a1a120a0210031107120306050d0f060903 65
    0x20380d569491604034680c0c038210303039402d500a4a01c0304102d034036030610101720744441581c0c045142d46040321030207400b101078810024083d46110b40107072100780281e101c1c0890035030003411001d6100103407a080440e580207c4c5c1290040719110200c0d8804003000039164140c40d80c44910508666030a81031021581102ca54460160b454a01c01c2001c16034007100154898051400440c0702d201e00008085041d145a000f044281c0c0108400c002c143d406080d0704441c0c0307070b00c145400303484201d40c00c0c9001c40e2000d608000c1d02c40c09804130047c402035004800c0300b008007020060425a074a01d141c1c0c40c409600d034008003640222400d8002070010b80030b480d81000320030301410413190706001515840b5258000701c072030218680c1e0380d03450809181000300c082100500d04803511405040200401da031146407000000303014040400c0b44c80f20050003032308a04030102240300310580310b0507207090030034507804410003082c0420b02d0a500440c981c01c0004400380d015800801d4203206040c0c698824009021000382a0700f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 696667733 1250 696666483 696666491
    0x4110f030309090c2a030a031107080d0608060a06051f0215071215050102102a1806030603081608250201021b0d140a02090c0a030c0f0903120201 64
    0x580d655101c40b82400750200492103915811780f03103510075501d140120308601240c050042410030701e03400004c59403040e140345408510030403040d20100f100c2c003a40303400a11100d00458210780403d072640c0400c04890880c6e0480307901d40c9960000004aa1480c01041e420403281803c09080000f90b04817000b0350b0680d4811240c0601003a451307490440e109072003207030014110701302210090109010380c0e109a5139040d00c0c82500d03031404002075582c200485541c0c007a10f80300d40e0b482c00a040085111000e0220052131420390580e841001020f0010384003070068000581a00443d40038442d00c11441541c0d4480104c6241440c204c0c070601c00304040f1807045a10071000c01210315441c2000ca640741c59400401103403015801a840061300340815200304c0c0c070712014880541d0509039144c040c405245074202c00d001402c48407640350345082c902d03070405c0690080308440c01c3c004010440001481d00a00607a003c0050261881e000c44541c400d007031902c00000d4203402d060000c00c1060b005038a02c08201c1c00005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 696668983 1250 696667733 696667747
    0xa02060f130f150203241f1b0203250f0e13060e0111070303050702010509030301150e0a120203060703021602060c010b12100f0b061902070e042904110f0303 69
    0x48180d9100f120207480602840c20306a1b100c040c20170080302c03000c2d011180c24800258203034400c0400000d480103481041000d41c0001e06104141c028801c0e13141d0080c0540d0036001c58102d800404401d014900d4424044101300002c102140c0d4201e9400d9819444400045441d104200c0081500446c03059507100c1d500d68820780813080910894800074441c000d425100d0895003006021140b004040ea406e59062008000d04e143c0c002c8112410340304c0c9c24401c0141c3c4000c00100b11100b0f48081189500129a03003004602e00c0340c2300c2c2e01004014400c50480300259241d500c120141e006518030f0036850000f218641006241a00190010301106400003c82000100c00038202c10141d544458031500900380380e1001e0031503401100c51409040000340a600c08480201d1030034480d08034840444100001b210b5440c61081c40204001c0040c064015040e00341810f1079080401d0402d10028880300d03100c10011480da4000d19a0b101c2ca400101071b0000387c00c61300a11458030409850b090341404100125 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 696670233 1250 696668983 696669023
    0x6150604080c06211302040c020c01020d2001060b040911120105010e06091c021e13020d06081c02150705030f07020102041706040c05030c150d0f0606050a02060f130f 73
    0x11441017241c02200480b1100e0741c018042200c220a01c0f82045420185040d100d0343d0b00000c00304240c241c0c41c500024021400401e40e0850040d003617044115500309040000e11403a0f40001e4825100305c0c10080184035a480e101050394841c6110021412000900420556000302840640040041c045501e4454948006441002c0001003400b04414661080003981011141c030302040d0114091000000f80c91400030300401449084890f401e0f4000404941800381604110300074840002121070042c92036402031424050300143c200144641c1581c4543c5200300e58a00d4003800040d29024035580742c0400011600c2001405501599001c010005030f62458400f00c2c03240c1c909160140480d401c3c18030b424140c0a05640c0f00301c0c4254081201e400f441d5481480c1d803e204240401d00301d079610000309060019120710328006d00c1d1a440c1c00c00000724640c00c01c008080c4d00c1016426150b83c0d54880c0c20041c84450242c407034a008041c0440b101c0b0001e0601c4035412480d5002d080d1804c060742e01d1982c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 696671483 1250 696670233 696670297
    0x30528080a030c080603160e0c1201121a0f0c0d090803011d010e010e0c0304050703050607031d060c0d0903122a020607050a0f110f06150604080c06 65
    0x41c1c00010340c2c0c403070204484542c0101e103240c01c41012800b07030446e600c0b456040c40304401c0034081c040c02a50401d0101d05800a0001100c82000300884200c0309503075140c0440e05807961242c4140d0711100044042084081d090310701502c20341c2c0c2c881c82c903a029204c1411211498020700300380304807541e4904018002c90f81000144d030003407412009012100385040a102e5031200d041c1e10034010b00b00d0440041c0600429800065840142d0170112902da968a080103407503c241039002605500800c006e00c84943e5158110315501011304000080c1041401d0400d561800c04813107010440200f8045038084c04044c0d00400c96413806898001541140d00351403130101c030380b0a1001c200346195480c9000030480843d0a154241000b4000f070318007450801c4014000384280c4020b1020042001040780c610f0703000301403055002c1100d20032542d00c601a80541c603594402540d40c0402c0e0900c80060110074901a4101d07001d50b08602c0140c664100c40b0740900007036030007059841600b01642070303158400101e8511 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 696672733 1250 696671483 696671497
    0x91a030f2d1512070b0706020f0d020c060703060501170703051f08070504140c09130908070501050906060a08100225060c030b01081e1b040e0906060102010603052808 73
    0x30b034046002000314104001d0507620f854608207034004400810814502d07609581c070a81d00043c02590f911940740c00d045441c4281c081541d8182c2c404509040a244001906403140c0c459880800820382c42302c0042d40c503802c40003e40180700303c0004c0010500c51007504010380000c0c003a60746000143c0300d40c2207040003150326040450355a01c8144200407618060140c48585101054000c9050800902c4130312680f160a007103a000381d510300d801c542900d140780e000041c4160050107007038a810040c5416800381c032017035034808001d00c00d85010414501d0010300c03e508841000c0010441d0100030000d0701c01070740203500c440034030744500d03140c9910b4942d9403082403046501c582c40000c6e01d0141003038040e00701ea000c503113064100010a03003003051848828081a1802e46400c60602007682c031121464074400c107070b0f40e80c0c1c04010408074000960100d440f6650f070080304a1010750b1781540e9040012404c0703814078130003e07016910400f1050030000d00144241d01c00049402c041d1044a0103807259036141e804a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 696673983 1250 696672733 696672751
    0x9070f02070801140f0709051f0c060603150609061503090212060c030702010f110702120a1e0605060f0319210f0e01020c010210020f0415091a030f2d 66
    0x1303003000600c29010b842c1c180d0081242c200021660b003800082a10200042c0026a105031500b1001c0951030051070250340d01a840350062081070788030f05d0100070007144905800811030501e1004914800c0a0064500361403814261522440e01008210094041c2e0fa90507a00211001c500c1d100000080c002c00d0f1140c50780414050f42c03428030a0009003103580703280000340071510f0090303800100001001145c1803181c040724041d40c03c01808403814108101e0980040403d0000d1052080f1280c0d00031041c10418040c51007048582d50714014030101900200c2c4140e490341140303804074140c0c1c07180b81064908078010704415111045407541d00403071031610308a4070040b170808e075035458400381d00c1504040d0f0210284003405002d651000040e60300e1402d07000c60307036810b5000304026a5080c03104c02528010b200c40031034074030000608100175104400300e020344203035100320356889106503880348100d9004540f1900d540106035240039981502c0c545280d00c0721181c2c0440100210386110900c01d4500490000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 696675233 1250 696673983 696674021
    0x24090203160c02030c040c1e0207051c0209010524130f1d0c030c0702040f241a09011b051c02070303050409051b0c01060603110909070f02070801 64
    0x1005030600400c4000007031010000700666002c010784011540c3c00c1c6981041e40d010980b1100c0080685643c40218660420380e480440710b810f10640c0014950308866003580c04070102e0a01002c03a450224403071501941091b50070b401044282003610b40070900c8800d000c880c40d079a6464a04108003036000c10300000503002c0380c1c0414058840700d40e48080003001588001e40b00c5034042c040d10354813060020070701c01003924080005152801440700710f41d90341c1c0c1e009000300400c04d00f0403040b400600101c5903c0b0f030241540b40701c4a800512008189080d140241403d101c80503050480841c10707804140586d0412007004103018510400c80c0000042c18400c0000d8038130050001c840c0100500c0c010005005c540c405842000404d03000300c125000d44d102c4500205d1b83c0d5442500c222040941035590740490503000400500c400c0065002e8410b0f0740c0569000e1214414681000010b4001d9003007443d8008c84907004034150900903511568620002d0054aa00507500c400341821101001840e911100e02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 696676483 1250 696675233 696675241
    0x308010302040b01030902010e010e0a1a070c1a040b0706060e010e04051209210f060405060f010902120f0402120d02070315020703090308130317180a030308070324090203 75
    0x800c0c000d00f2060703682032078204160806500002c2070102098001c1e0305110880180c0500d9807901e10755240603041c40b040c000c00e03403005001c584d189580304440c10b584030409054041030002c0600300c80088200343e01007140c10a810301c2d04a01d00e03a4400c00048858560718180001e190100d9818613000701400b500c0d2491a1519051003170919000c3e1010050011080081021595400700410a82103103e602d01400c50700d0481014a0720312041c13000003c0d0704c10142000200100004d04511030451348480c00c6150743e0305c0d1701e000e060b80104c0a60058100c503030740c00519000200030905902c5800142001d61060405420b2414102c076205a000141c21854060082c460030190b02082c110b11410308518101c0313242c40040881d40c40f400020003507640001c80b5000c46a18410420286400c940091043c0120740c0c1801d2007907104008000441094580c8000d162070064003200469415031a40030069546c2c0c0005c4000701100c4840c0c041542039a9100c03001c148103e2125006000c0c0100b0043c5d407424 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 696677733 1250 696676483 696676489
    0x11a0d09030c110102010c0915030b0316031e080307030b01020a1b061b050a080c0f010c0201050f060105030f01090506030307050a11040e060907030f020604152c0603160302090d0308010302 83
    0xc40200f202d0540e07042801d01c18080f0b601c9140038084480504c5d403070200d00c0012400324040c01c5010020760b414441c0708400f10070700780c070013410800b00c80c86020070307803c8000ca0140c00083c101502c0c501410440d02403000601c0980640c01c41c403c1d518052058541900d4240e441c44400800c0301c000c2e6007040040d80040c0716081d00700b02c045120190b440001d03e00030246550355039a840c40708000515500011440d00740400c02000240071440c9440003d01c8003151041c0001d0081c0b504440820140000e40d011a09a500840484e402082000e0349411642e007801d4200d4060900031303141c142c25110410410011070b81c24080c0002e614469103004200703101200030001035425000622910740c1010f014803040c0d280008007602104c4c0d0101c1709072090011800014858000c0740c1c4035141022102114501c580c0d4040617040058030800c0e19040c0f0f110200c094600d40c4458403405503000b40040010a80c03040b0b010f101210b0f42c00c40c91502518011074980803800c141d0841e08101e01050603d401032003145 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 696678983 1250 696677733 696677753
    0x309080a03110f010b0312070606180e0606040c08070e03070b0c011a33040320031c09060806060417102f07060b060301080313050d030503011a0d09030c 67
    0x400944000e010301c201d1200025191f003031440d0b030510941e400040c030340100903e40d040900180250005554004031014281700a0682e02043d14100d0017904001080c40c981440b64801d5002700341d036032100c1940c50f144180d075021064601365925100304640014100606ca00030310b42c0da405600081000224409120204c03488a09018410f044403034014081f00901c04400083c01d0001d13081010001200700144240e204070340029121030401c103e2412039030405440c020b0001e8054084540326a4172528500a0002d0b03440480c000a058840c10021a44961076003500301c1c500810540c0760980d9200f27900c030000c4d901c0c00c107000d954104010118a1944520451410302c0300700352041d504625840742680196100030071040c1c2031002040d80001e10030703035a02810506030043c007042d5030303541c50708845076481d003246019002c2400708802c0403d007410300f0300c0c800100c103a254a8440c01c50b42000c501040381032800641d1070b100041840007080001e044e00980c1c2000d40a81c940c00e0040841e410151001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 696680233 1250 696678983 696679003
    0x608060906090303040b101e0303020c01140406031a04050f040203070807030305040501030c030209031501051e09010e0919030f110d1d0609150d140106050304020108040309080a0311 80
    0xc0e800040400000420210031a0b900a40c801141122a591011000b146503100e4010030a002452100054040c3c0c1290150003524020b4003141c844817100d030011101000800c21055060304203020412100d0b009802003887c0e607603901c00c070080584803071010404882045035410030303244545084c001541002d002143c06840c11201909650b4115140a065403059103c0e0b2410036070750f8440c0c820510b101e54159454404003d00360f483c00d21595420302d070550700a000b6544a0324988080c0785882840214100c0120707005808064141e18090900000501c010104480c0d40180c015064001c211040c03d40d100f2803003030f100c640c0002c0100700002d000c964116041b0000754041c1c940380d1807203a040007041d072a84283c02243c0b100702000c840407411900440703841d141c02100e6554003401c0c10800402400c2100d41202c0c0c01c021442082030703155000c1c0428410b10300422010008540954807a6031215440340c008c6c204902c1080d03840c4c1603d8540301040380190001800160040c446440500600c032070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 696681483 1250 696680233 696680251
    0xd05070906110a0210120207120306090e1f0e030406090905070e0f100201020f2d0901050d0b0a030b191d0304090e070e0709141c0809010c120201060806 67
    0x31000b090110982d00c070b00201c40a48207041080381018510321404200b5003580010000b50340754103c5151417148116100103440109050800214407140580b080c0c07504505144002c240c2054079900c0c010003801844010010740d41c4480e002c200100d01040203000802c0c10740ea5a200252400d03041904840c0040c000c60100f26803c801c04c1840e9440300b600326000360381210800c07818002807509a009106041c0c00e070032a0038011600000e880c50f8041c070302c0b0080d10441070450309818010b10340c03c5244503164010303010400c00d200c40d502c0324209038044642c2420180148100301d40f282c98408003031108480d001e5a070401441302e41c0f60b40c4880e00403010729074406110380c1c0d20800c0c5450840e4613400349000d04006617541d1540240e003440d0030490b06008060303004020b0340c1c0c0d08003100000c02c4a6030381d019207100c0300740001e0242c4007410b103480c11211007200d1030f6214902d4031981c4c0e225142d0380e018802c1141004102e02d0300c800800d01d40050000c5040d171540000400c02d01c0c000085003400c4e001052005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 696682733 1250 696681483 696681497
    0xc0706030513080702093318040503160602070b010b091e03121303060c0807021c0e01050f130605040f0b030f04081e1207030f0209010e06130504020d05070906 70
    0x400984414156030406904a031540016035a0111000d6040c1e52000c102d21043d6086900c40360380101f1011046490405031840d05a44030b4440200e040c008091703400902c60350003001040d8181e5019040c0f00101482101c1c003503c1c140180e260040690780a0b04464070700d0100190410852400b00b103600c03d89820a28012105c48610340000d49503240c5000c5051103120001d26002c049405500610143d5440703801081600050302c00140b5440c0122520780162140c1c4100845c011140c000380000400140e4070401e8403200d601c0116590742020f07803200042c5100348030403035103805501178a0b00541034540e696521146802407142a00400740d0102521450400500001c103101d5001c0b0f030760240d0095540e950b54918403207007a0030b02e00600c8030403c4040001c12a007030740703c045d6021140950034a540070b0160b1150151003504038464010403a0205101c01142e0038a070078000f01405820601030038082203260f4035008203041e80d0103103014500a9a4a404100040d904040c80e10b01401680c0b0b4005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 696683983 1250 696682733 696682771
    0x806040e070501051c1802040e030424030e0f0604030e040e0c0f0a0803040603020a02012d0c021f021207080708180a080f09040e031903180501020c07060305 69
    0x2503103070741e00ca006440c1000400120400f1713003120201004040502d1050410410001d8150500c900851000c101d00c40d81c103100004203000000410342d415511211080d402301540c0225441d1100004e518810606441c1c0244500509061000c03026102242d00645690314041c680246501200001c407071082d8540711000f10f500c4400960701c000404c0c10380307544a041d02c0034000280e0548590f8003000d880c3c2300004000c00c8540d4960043d0800d41081d40003405100000e9070b0b02125040300702c40c0107662101c0000c00a1040fa0a50426040d40900e4010348800742c080c00e14030a104403112800882250300010280902128102c40d25800849440e000c0f85a041046004050080251612403010512205a4100344041c44504a140c0e442a001c3d80d84240c1d00902c0070b8942c01058445106600d04903082c81c1208001c0704a42040142c0301c0e21030b10042c6107038815001000701100c3c40d00c80001d40c1541c0400100709100a1032100720482c0205012840d06200034250351001f080e10f100c10794080e03003e03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 696685233 1250 696683983 696684011
    0xe15100b0909060a080f10050a0203010e0f0709050405010b04170c0a060f110d0908010e0105040b13050c0d05011416090605070218010f09060602010e1e030708030408030106080604 79
    0x380300c45480c11150600b5030b80300c0f02e000800220b60368005581034001c54510118013040003540e4000d003120f0711400e10059031100300c00d40881c0800d02c038134000109604000341d40100041c9440d94403a000b401c1030400a61203102040440300300360010300c85070364001800d00c010509003c65500c040e9095006040f201e2810002c545580d52034071414060003400e41e04040c004e4003544408200810080c03c44041e920b00b035400034040e91040c820340303003254070b06a02c014210340706003d41c62045801c00c1440c41c182e218544006881c2ca1780c4107040d5054001c0c1c9507201c05d155180c46803001c01e00d00907400460386d01c4200d03800c0e00307005402410002c0e007040104100c46815400c02c4164080320101d0a0054403000d09001089940f80407510611440e03416000120b50b0341c144031884025201240402c00040e0b8403104280c0c225030a001041600da404801c000080840c12684034003131010702c81c00d8034200315642d91141d4841d081928226650324001c0b0052003900c3c1e0090440fa8420310071034003030002064072441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 696686483 1250 696685233 696685237
    0x702130920040203010f12020d060e07050f01020d090506031305010509010b1c1a0a020d0903090e24090c0c030d05071d06180301180609050d140409050402010309060e15100b 76
    0x840015000051f0101d055689000c030102049403c44014000c40082d0541c443d280e4586d4020203210f8205a0360480840d44005444030140316951585a103070341c2000700b04078858000801d0700ac1002803122521000038420301500c0d020b419441c0010951039944000c00410b21608510f111442181a5035900450040c103600b40b03c01c841441540000c0d1601401a0701a205412040f0741b0942040d8090b02059800003200044545a5000f05159110341c2d4050a40d043d642c0c80c2c1d016900c00f804100481c82c076005c1040780e01310360f403501040c0c904901120b8450454108180300304a07169a8030070850400e8000d8a000c20200c46c0c80d0940201034002e900065a034001d1440c4d5040c1c5201012031381501d0b480950220072070303804520028030f03441858038045014203040c020445650003061660100b403402880300c8442c00b01004800c9040c1410200524000d150082080e41010b40ba080d241d000b00b820f0340301e00e0603440030070000b405012710700d18140010794002801700e91951603500b00410601d105801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 696687733 1250 696686483 696686489
    0x503040611070c1a070b070804030f090b180607050d110607030b060d051e240f011b1115030106020d210902010203040b12060306130f06020702130920040203010f 71
    0x4289550b80200a42c281d401745200040000380b5840030b0103072058108411504c614440e50341c00881e202c680800301c4000e4800c0c80381101d50081841040c039103810502d1010400003011b000359003865425110a0710700316000b4000310200c1d500c40a200c955680074401c040d0b00001d0717803c0501035002510003040b6148164460044501d540d80c0201c0e1440c40c00b03104628800b01d0a1004c02c2946c00c2100b06c92481c0c0c0442d50300c2c00380301c504286114915080510445401c42c034140c4880890030402c040e59025001c4030b14045414080e80c5c850b0030790540c0c0f0b01070b0415142428112054681d170510070080c4c40c00240701c03d10b03418006501420381442c9a28403242c121680c5800005c901d030203142c80180d16502940c2c1000002000c089005030000c614146194403a001c2101203400b02d803185031a030440746100f90000740c0b681c8a4904001c02141e101d8009040c06840908403905402e64089404c08031a55403000b15011520101d04407104906000303c1d1007403520807a030451455252080000c42c6100d148 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 696688983 1250 696687733 696687749
    0x51e030c0d05010f0c030b0414130305030702120d090213020304020901180b040504050c0114030405030f0a0903020d050a022d150702030303100f060f08070e1f0503040611070c 77
    0x403201000300316083d01300d004d043c15418800d10040c508090090f01420420b608280100d1420904070707a541d2080008a0086040d134008202d101103d07142114a544010032250642c400c60102400c10003120000b000200104100040c0b40d4005104010740d1859081d10504054010700901000d84d90b4004403a044442114800301d02c40c000e455580003034209007242552042ca0304c402c000134013030b000c030b030b8400c02031307000da07212000340030381e00b07111030b031a0205680142c040d90041c004054445030040040c40844040d01f8181150b40d1ba070760022340e174500061011180c540040c4404011401d09404446010300d407980f074a0f00300e1003000200500241d41401d03491080c0e80d41c240e052080030074142202d00c0642c014060760741e02d1800381c04d000e40c042110b100760446064103440009002e8032441010104503010795849040340c442a408403058401c4e10340fa03d6000c00420100c014101ca4001d07284113125242c2c94650f103d1400d410800100e0304030002841181c8000c20140c030000b01e800c070340c28054403180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 696690233 1250 696688983 696688999
    0xc09061403102a080f0903070308070302070609020a06030e0105070518040504020607020415180c0f1809020a0e0a0f0609031707060203070c02120d0e060a030e070e01051e030c 77
    0xc040c180158030b402103c5404800401000341a040380c0c410261882085c15900c2c0c06010384402d44103d550b0302ca10750001d4000f035030913800b01d0140c6220350000d04080703004550100700003030103400003561072080398080780100c0d035148410a140f410a001e400d6000010f81811428440d42810115000c1c1c081c0d0400b034895507841c0009400c6598040a4032000d41c1c0141c010420384001034020004500c0702e006000280c10704442180d0b4294031402999804800d958980b03100321140710381500d41c4a01d0b8407407081504500c3c2000b0602c1c0e0864409803034070b403803d40e0300c1962030700108090001410742e03074210400380c1c41c0800c1e090000540008403241101c0e03000005102401203283d00d5580360007444c02c01800d0b41c0c0000240f04c08140c0c00522210303c24000c46a844400c060380440954030f8216205020104000071400710300e601e41640034103e20040b038140840c01034000b40140d030518500f50032245090301008010310540c01c0c000508082001e090145050060324640002e0750b540c9441d012902c24048 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 696691483 1250 696690233 696690251
    0x9060c0c07090f020715020301050607060f0b3604020a0e090a0f05010f060501030209030a080f1c060f051806060a0302071e03030b0604031106030a1401030c0906140310 74
    0x80080c003004082c50750040020b10040c3c510708000e50301070007003130b502e0552a08020003814458030881b4100da0009117003c1c07404506a6407100a4036601d80861602ca9880f03118804588454070002003400d07095011201c621944813000040000066144091096540410006843e01000b850a940c120318078100e01e41d0311103240300d142c1500400c005000c0801ca04c03a290801405401080039141ca52800740422912400110124043c0d584240c0d13150f80410122404250218000c003481c81021664928001207075100c02d0075031324454811149295240020000b03140b02c2031f83c401c00745c00708480b001141080318240700504d180c041e000c0b500c94240069040080d40c00780d0304032100d441c1e0000c0b180c1f48610192180340442968524141c0120741070080d8200c60740340a2007203406a1394805401c01c81114034106108450304010000400c86995444003240081601400b5000b50701c0b42c1c2da0300350100e04051511043d80d003660302c045210000400e6904081c3d070f010400c4803004c4213003400040d40c980 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 696692733 1250 696691483 696691507
    0x3140f1b030c03070303170c0c1f060914090f010905070e1e150a0f0b0403080d02070503040f03111e0d1b060e030c0303120f0c070507090218030609060c 67
    0xd070b40101d1590612540000104264008078000504d02c0d660000362219501d2524041c218818580e201400750818146400d150f0441801c064a003a030740440001d0041d203403855001240c4050001e2015407000d90108401c8401c2003080702420100e00c402409840040c1c0e4429684042074003402000400200c005240b56900074103c0710041e004012001c01401c0010711041504800001035000300c0c00c4a0012840c0c905901d81c034011161029a60b40c68103246d41c48607283c9800c4048440c0c1503035001c20040c0c010640804c017070400b601c01f41d2010781d225031451074103a404041401c900c900900d104500d40101d1441c510244454280503501c6000503841071401000038403400c0780d4100040c0c001c060200c2c0f259440040303216087c030f0540440700240014810140c1d43d01458032420302052040c40010600d0425004c26500540d515084c60b040c040565507141c10480b00b6040740c800e82c0d50110741010045080304241c06981400d50190003103007080a071164503400000d11400c01c2c85000202054060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 696693983 1250 696692733 696692743
    0x60309030f07030809061f1a090d050d1d060301050f0d0210030c022a060c160308070b061e22240f12032a0c03140f1b03 53
    0xc050500566200e940c0d240103807480c507054840c0c00b03c2e807080d400012201840c41040c41000551f807410f182e0024a4168034014500400c00348101400c0e060024034070b152a0000c0ca120483d100b00c020300204e185000000308044045031080f25841c06a4056104d252505400c503410359100f41d0740850104803540104044858640000350401c0c40c0100402100740d069200c840d08010b40da094a80750030100c403196149500400c40c04a101a10540c04840740c64a00004c0585c40d00c000143c403135810100221181d880f0495000341e44141000072460100b0409580c90340d803001044480c1604500030100c81410110300c0060325000350781c18082c0c00803e01c0d846002580c5c40c64014018030656584040441d0011454403002460582d007007404a8550042421801580c0a104001134851001d880c00c0b41c421421601c0381e44650b494141e800601c86035444603043c424003e840c802d802d00c1c6185051101d0080700351200c2c2d000d400c4601031a10b2401d006c15800c0300780358440001e22803240d03200000b034113003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 696695233 1250 696693983 696693997
    0x203030723121501030516021009031e0207061b1a0a061710141b09040615020d020c030105010b0418060f03030804060b030a0807061521200a030206030903 68
    0x20500b503500304600700e0071802d00f0700c1c0e42050a0780e050265131107640400b000200b041f06504090303000b09101000141c0030740c2c801c45505019180c02d516040f0600101003010030601340c10b10040c0c1045005210540d040884241656001e20f04952200c01c180c0b2031b030303910098903c0d00c41441020200416489103090701b042c2c0140c0400081c1c90102540038441d40da030b603a01c1c52034a02d8103a040803c040300168400b074010b0720030702031415500d02040da103008a0300560701c500c8031150700c196140004180ca06602481090850b00b58000780301d1505100301c060b19005025506a20030f80c1010014042802e00e9010307102160340c002044c50709241c0d0301e507005d009081c00341c0100c907001c83c003c0c40010515074000503440c09a4011201000704404110030325441307100c0c400014025450030089500082d80f2503001c0c2c41d031503198807020441c05446180c2160700b1401d100e06022592141c0c0e0b41d90b4180a004000701d0a502e0356000782044a00442300440c03101400361101034404e071404400900c522070244221808 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 696696483 1250 696695233 696695257
    0x6071805010816092103090905100302100507120306050931022413140f010f02100507020c03010f0b09041e08030a0912020c01080604050912031e070203030723 70
    0x102102c1c040c017021038136050103030005a14041c000580c91010f11489006074040d440d40004641550244469074455107c0c0074200401085400301007030001504455a0020380c0d80401d03074601d000200000c03042c014101d0099014401d01020980392174070000c1c40c1d00240d001050003040094000500707410412500d04c0803c4000c2c1c0520719075844800e00600080b40c101c01c0b601e201c20340302c4610704091406104070707a0b000040c28100c1e4006602a8001c0c2038459141d00c101e0748420103094202d41a04d00c01d545207070143e805402248003900d820b00403e402030a0100d41040b45c0401000055481030024001070311038803c021200e84440c0b07e42e0114201503820249280d543c2c10610018002001020f2060320102c4d00c28416000c41813000c1501542c0c204169a00383c410f40358041008002c00c409000740c0010711403a01c2d400c00444000020303500c196002000e280d914160424002c46100004107a2000c54104004000c4542c1c2c1142e420b08982a100412621590301e440c0500d2061050074440c80c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 696697733 1250 696696483 696696509
    0x1b06111c0b120d020a0206070618050a210806060a030905191502040e0f06040219080a060821030717040609170418050618090607180501081609 63
    0x1035550941107901c080034141c07000820306564603078941d1694580703210080140c00011508025261520241c4912406100001008905400007284450606004868035004081503105100e0b003104900751b01c017058003296149580c0d2600c0100441d1004045a20032840803071901c110a102e0790000c0445c80c0d01c00115002d070341d02d002c079224480c0340d20758044410034480c0e1100d03a000c580c0342c000d072001c40c0c0785001d9107265a20341c0e44002118810051036507822580c00c1c000d160841c0c0030071004c16480740e03054070740d400305080c100e03801410f07034000340c0142081d64007210b4042d0900d910304002030741c00e1514407000364480d01c418400311100e0700004500301000d40d0090510003070000700c0d8407000c03c1d01d100d11001c41c0200820000040203024034807541120007805071010001c4042c9400440d44000001d00004500d04540c600c034101040c15503510440344d2080c010001416041800080034100740c0c0a40d6500901d890002803a007100103241114540784280069800382c01200150050816901144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 696698983 1250 696697733 696697777
    0x160c03050708061b030f15270108010501030201020a172a1027060b03010c03061509050609040b042c0c090903070f051204091401061b0611 61
    0x41d5940280e01481c0750501800c404184071030508414240c0c6608204607050440d07541c1540c00c901204000c004c16115a0000540062a654040c81078000f69600c1001460750711680c52901081805070040c1581e40c0c90400180f0140c0c5c1c0001e0024143d82e884800400040b81d03000c468030346806102c0944280040c0d110801c080c040b21362140d224440d0010382280c0d2035801d840d0307240080d96081d030103500000c0200152034126202d20062480418005d0801141ca491150b01190864101c00d5034070001a644070f105002c4032440c0c40c20035510113141d2910302074075400d1200240b07003440f850341a00d10843d5940010100c039103480d000341c5002d004a209101c01c4140c0c600726241991940c1400601c103024900e160b10051501c1d09440703000340c80840007076041c280c50f540d5055042d40420015a05c521030308484050965034640100098007082ca00070401d03da4000d000b0144131010380201091045402010041070124104111600d410110205180f83c140c1602d13900c5210342070704100b64035602d01440c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 696700233 1250 696698983 696698993
    0xc1b020a05311b02010209010804080a0c050f030403021009031a1008010903031e0606080105091803040303050a08010609212105090a0b0403020d0b0a1805010504030f080105100302160c03 82
    0x3c0482c1c00d0795485548206801038004900300e02c15090f10902180b4400c0200700400e04a00150031000594180081c010f41c03240c4505141c1881c40c40c110056a20010b801d20171420005000b041d0034600d4101080614155500c03004140315000022041d03082c41700000e8600f4a28001c0f420080c55144000c21281c0300d181030090280c4840d20b50b50091440c03070b540c0c0d135050390f56520402046543c03942d2503e003e07034240070070008159405041111050311011781284820b105100901c0114420384540390303980715209000e0f20002c41640002c09015044404102038100010100c10424840000845203486440c100c40f610300044806040c603441c00e4003c00c5500e4115008020031241240e14071616a42d03038120a050344100c2c000290862084281e040000e1822003016400c030307051003000314070f10300ca03280c68000403134081c0c5050706d05039154800d0005144d04944450345031481440c02d10807541c1403101184081c07060703c02c04010158000b6294060300c101c3c0c081404559070000160f81721558034100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 696701483 1250 696700233 696700241
    0x19021507170115020c040b13050705030103060510060c1202011e0e011a0d14010e0604030507060b030604171e0409050403140c1c05090406090c1b020a0531 68
    0x20341d500340d22040c00410080380103101c00590345451307401800c1c0c50700f1000510025003c881c1099800c002059210303402d1b00380310f0081d20310448241d602e540d00c075071640c1028016210044c11803101881103500900c10701d684004080d14840d0800880305030028000303404c900400b52040c01c180001c003c040d070101030301e103030b40c01c80481c0b6412000203001e50000d8480c061481c2e208171f018158045001005000002c260418042ca840800d9000140380116403600741d0400c3c200b110214002000080c0b9501040b020317204807001070100360000d1410340307810ba4601d1000c60005030110244c0001040c00d003140c4880360105072905a212441c01d0f19640d031892820041c20381540c085010030038804101491f180c1c0c1c101510b040c07500d090f00a0044844142890100305c103030742218000c000c030802561440b62aa0700a0b000100080700740018019031428000701100060103400d035a02e2120303600c07400582d407102c0180b003c0d21021114010a401a5070480140c004500300004101140000984490b01c85502c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 696702733 1250 696701483 696701507
    0x15040f38010f06020616140415020c0a061b02150915070605070c0309090f020705151501090b120603030702100801091401081905032203020a050402030c19021507 71
    0xc000e0342c440e00e0702c2c026610380e0011594402050521220311414a100b000e404002807001c084030b40c40c0640710421208903490640c100300c056400301407024041e0030074030341c030000070700c0c80c1d282074132841c03040c0d060005000c0ca0311940030f4860350503184000390120225044450f03c03500102900e141048111180320580c108203010340301280380c8130000d1407103070203101103801683c2e155803610941420010850f004140f1100c0025150303609000c5040012801c0080121820326005460301925000b010012f100410115560401c00d1140303040103004d007008180c803d40600c61509402c0c40e03603a4030101c1c3c514014080040e5100b40301c6440304204507003008940d4103a4010708003c2c0b2200e0103000c1c040c0100a403e21411180e980032003015041c3c40c0b148010748140500c548207480c03812400310080b1204003203e0b0080c456080c5e50309030030030451a118014000900c41903d096045140640301c0c164030380501e44a0381c0800f071800d18203000151090102c12556010400307110f2181c1401c6000078078141101c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 696703983 1250 696702733 696702749
    0x5101d06030d03060b1e090901031401060f0b12092103010305060f041a100f0f05030714100804080903070b03010512070b0f0d0b060d0e15040f3801 65
    0x51405404074428003811041e2401204036070b1905010701ea0307015a44050079400102c0c14020b008089065032350441c514002c50180c00e810a0212040340c146d42120600c1d44075140c090900c2d8000c00605119a0540e60880e01803060661513a949010890400340c2192042180582c0700d180b00003504010b401460581c1d00540803100180e845c240a0200c100c02543c001d42440101601001072018003000a03074230000100020301030740d0340c03454111130421540e0001d0205e001501c4003401541001c0024030300800100500d428002215008282c5219074181541c2c10042c4c100002014010108111b800c0410701030121001156220200e0354140c10070f010f494032481d82c0010108003994006504019554511202d41c42c054440781d03a14081e9000f03c01c171100d49610380c954984a0f0f0780d40405040b0456042d81c001ca414030100709807a003002800b00f01100800a00c40920002c240e4003402460010b900c101380442c041c90070310b00c00002104500300d00079403440b00d2051107450007250071142d040340d40d40e03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 696705233 1250 696703983 696703993
    0x1020d0e030703181214011d1e0109021509120307031d01021f020912010f0b0a0e01080c04020a030e01020c0705012c0904060e10020702190303080a05101d0603 70
    0x6190b403200c440d0003500c1107021000094500c0b50220b03240c3e055501480c2d000b680000b6408022040d840d014202941c4a20181e8100b81e0a81c8a03e0f009c101ca01c000e10750842c0020013800c0115400101800d05140201290080214011000c0d4599226400800c101c17607044a807110b200e868002c0c4850b07080d0441e426800b000001c0f69005500014503007411039400da81442002100000000c025002510342c0ca80c4120460101c40c8900400c1c42108510280c0003004107850310040d081c80507803e0b2a074404042c400c070350030040101c6440820742c922112070440380075070b4880d0410004c60113000803040d880f1036540f000588044420002424800311042a241d08a406605418408004a01c040c008111140440d2103964038078151040940c024401e2500041c481ca00000c4545800c0b02401c5140d9407550000f1004194600100c81880420103a21440b072002c1c00d56800800420300600301500d02c54907440815070710360712043d036035021f0720016840040c401100a00715511400a584a034024010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 696706483 1250 696705233 696705257
    0x5130b0f0d050303131b09020403060606020c010f0810031e020f10050702010305040c0b0316030e160506211303121404120c082b0b13090501020d0e030703 68
    0x4003841c800e50154100d0041c500303682c2c07841d0b082000010b03031031801c8582c00c2d6804041160384ca2006c400401900502000586880c154985802280c5458000509541c407230800d0b040d40d0381c2d1100b480e581d1008503282040030703616000590000181c5940005010b044000b170b004500d00c0004c1003810444d40225401c00007a180c4a05000c1500440281c1b5000280100b0209026501a80203903401502c40d01d4062551543d0b0b402002c01798205644400151030055074bc00c00c201c1d81400f600404040d802d02821060101c04c410340000700b01445460f01034440800c1c00b10807107004c2000c0070800070420308508420b283c2009015801c06540b88218040380f148a01040180f90320b00c24450080c1400100400c0c0e51141d03192415560641c16096080002c1c8114100029204002600f8010801c0340400c080e201c0000034440103041080004020600c1c00b03089030225524070441c0540300f880703040000750304003207401c01c180680301d51803040303848500f0400d00c9151010008000c000050180d6120076103008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 696707733 1250 696706483 696706489
    0x1101180506060904080405040902180403030506030607090b0304060b03101a10050711040e0a050304060206040c050d030f120e06100e0105120304060302030c12090717010c050f1305130b0f 82
    0x942510080c21700b49080c44140024201a0702060344180018208100f0f04049501c001c141c400c103c40c102c0000740c85a080c0142c13030408028140e04940182445580103044c2007c144540c0801800641a04d460340000700643e20140079003500766010002c02e001c50358043c032081e881c1400c02c4455070300640e800c0d0250b8405c81e1013203090302c1c4101c2d841030410b500310305040b04200141140911550940c014409100000350041000b44020211034000d403101e440c043c20300c0742c0742044562100c3e0040d4014120703400044e074440800c0d002400d4500380035880100e4181800b0007044004400000c91180c0f1003403101c900710600c0f42ca41207802c00810130016a0f00e0f0001e0000326094003a80881e40c2d4000c1c4002d01c040b900075009181e018441c07a1b4500d00f44810088464541070b000d030313642090b68108010910101c43c01c8056105000c0c0b11134001d002809694500505a102c1e00c0e00d071701c11405000c00c124104910184000c801407a0040c40c5145142e00c0e0900c0000400034030405030300c42e4921801c403000d541 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 696708983 1250 696707733 696707749
    0x30507090807120206030403210c0206060f010c0b04172b0e0307080703050f03280b030a020904021314180c1c0203100e0109050c0406030c0510110118050606 69
    0x284030038201e501c01401a405e0208542000d4022418095260526a00750070000030748400c40d08008800f0854009400d00a410140003620190085002c0c004240569070031590034420543d001625141e180d48500380183d441c13010300c09130065908000355a0030900c2c190904c01419801500345504071705c6500ca01841103440d002114040740e0403e00824021a0f0103002508040d400303030801a140c41c40d40c801d0b0b01803650040b6401007900c401900702a4090140112581550b8280001044505072071400642d88bc424200300920554034140043c0071502c94540f800800180808144046e030551100c8040600080b219204c00e42a0111504680900041d040300080800b070580f00f103588001442c4a020000f802c1c0681c0c00d8402c010680414012501c00e445034048007000000d11002c051800505002c1040382040c402e50828805102203050178164a0442e40b00f10b8050400f04880304054950072101c2c1140e85441d440d0501541c1d00444000c01480c08904c42e0090750025a2194100090300f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 696710233 1250 696708983 696708989
    0x20a0503030a0e03070e071e090b0417160b0301150e030604030f02121305010804112808030c0d051b0118031e080103030e01030e011e0506031906150305030a030507090807 75
    0x41071591810703800000b41ca2324040714025883d10444a07500d498040c802988140e00c50402a0105050a941c11509100e04400000c079a10b0900720755160104c4042c5500042c0500c01020b80290040d0f04494013409035204642805016070392540303002d04024119000c807140c0d02c005401407100c80300c10000d40d0800c550809203084820002c2c079041c40011915013500400880f6955690040c02489650711511241c1a040300d0340700c0001c85010034103c0c1c1008403d0361101c450750384148040d4900390b03404144200718644624005403500c1c103400300400040d08051040d4100d52808103e04000d44c43c0c413040c0c1520a000c2e40754041e250210314900341070800300d0014040000e5202d4014400a8030a517408684034905142c041070491021003100d0071181c030018640c001c11007031307184881258a10300032140c1c4040d00710f000e041201c031a0810104c81c1d00c00b1040c0207003110f607070300381202c03491000c01c08807009103803c441202c2e29455a00c0c00940106130607181c000101c0e004000c0080e04a03800900ca07810b03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 696711483 1250 696710233 696710237
    0x9040506062412180a051f09080405040c170108030a080709030201080f09010213080f0c0f030307060e1e0c03060f1905040618050703120c0b01050d020a0503030a0e03070e07 76
    0x1425028000c0c0c00f40c04840034088030030096883d102c903180304a04201022100340100081c0114840d41a4a04001103a0503250a496400c09032014003003112403040d10101c40b010b880100c1d5207042c0c034204990540820713100400c450356900000c035881c1c0002000e4024900c0d507484049031034a44102c1544c43e91242d10000f07002130465000075039075068500007981c00803001000507052071a800c03500441180c003600484c4542d80214210303100c1007410480c03100003d41c15212003000700d10780700210b41c4034030446001601d25034a816442c1c4550101304851468180d01c1b800040844040700040c07512448080300640c441d2007904045020002e64011040c000c00018601d41000d0302800a00400341900500685119585441110101181c10010031072a44141d000e00038250940c90421485640b28014000f0003141b200b00b0000591100c0503541556070894403007855109500c009410138442c0d0b00096010b00010900c03040c002d80018407260818003c070251507009891301c1d00140001e40458281c40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 696712733 1250 696711483 696711487
    0x2003012306030a0c0c0210020c0a050603090d0c050705040203010f0501030b031618090209040b010f06050309100b13060308030a060909050c0427081306021c050d0902090405060624 79
    0x3c03409041e9228582040701030030400410b0403203400040d00340d1403030703000c0c02c0160300006020042c83c90010300d014081d000481d491400c6080416041d950f9581500240d800d00c02c89139002000e210081102d10000c1c04010800d541c1da40e11036075400d002000502c10b05001c01c0c1043c0f50010309243c04103110721090340301c3c20b44d0345055203008188070050f560071804010030b5030b960910401603100c903c1664801d0b4041c0c041d907440e84d490013000d42e610082581c80002085070620a20501b15804244005503101410740404c48898240015800c4501805a140104d14020f800001c000c50000603500c645507407502000490b94540146003694128040102144c01c001e005008034a002d41c440b078401c1024103407103150040c1d240a4035100c11161101503681040c04180c03010308241d296042c1000c0d09052000e000012222104401e840404c4c0c20510144134002c100c10315101aa540400340a90b0002e2480702c031400c19060080c0c0360442a6030a6020710148072144010b2202802c03044801e84007003070b082e8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 696713983 1250 696712733 696712741
    0xe030c061b03040905160f1403040c090e0f0111040b04030209040606170318010e06160302030d06240201050f04080a09170115081c12200301230603 65
    0x100040e807000808244900c0c0e0700c2019000d601040010b48044c24605000003111300340b504a20303000c000421155020441c140013522541031b40301c0e0260582c0342d040c003010754980e00d80d8600885c411000b500a00c4c10146040e21100328100c1c0054134510042d1410000c00c6200145040d120710b9201d5405512030309081000100014181042c0041d846401440001422921103000022040311203100c41216480452140640c0280f1003600c0c1005e402420085005041400494900d01440012003504900010008240b45c02403044510703c000c110010800b0765101d2003035106078245032003c80309561901c8003c09000340144210b034055155102081403c1c0d9551341e49045c240c4c80b510000081081c1e400300040c28500c0b1601c5000c0300b02650002040030010f589051603103504c1c076070002071554040140d900c0c1c81a03501c04aa190a041b03803800c5850281c0d41d010b00000b405030321020460711000b0710040c2221458080155060740d202600a41800b10102c04441c1c00c203010b00505540601c00308041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 696715233 1250 696713983 696713989
    0xf0809130923160e04050a080304080a1403130209090c0a080708070905010e0c071b0605180301110a05180603071107120305042c09011a0118090b01110109150c0e030c 73
    0x52076215104a08031501d072903055548048e02c3c0c1064400f00c90480d000b0413074a80864000482c41280032480ca420f60452501c89000304940003021030181c01911a580402c0322800c040c0440841030754040c08030090160340b841000e980d9400c5d807146006601416074003150101c1ca50041d41d040343d41c0e540b080703090340e1100741c505003683d40078400481e904140055415064200b90b9859002004a5199591150541005041c3c2050b4010045c4d1090b4503040c8680d50f42c00000c42034544e0340b900307850724135160600c1402c0d80030078500080c0e0031507112402008008841ea840307035207218000a020240c558944c0e54050300704118095410007408114140014000001d240e0609140c09110140b1310341410848040380010ba075080d290950180d440381d0100600c04000b440e11000d41a0138070307014400c003004071a000382a441a026441e540e40c0c4600b405005688148440c1a10002c80c800811141e205880e08041d42c402e180d032440f400b20b0070850340021550040c0070f0080c078000050302411402c2055010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 696716483 1250 696715233 696715259
    0xd0506180304151806021f0f060e0a0e15100303030915090f0605060a0501090b0c0c10120605060304020108040b310b0a06030f080913092316 62
    0x3000c080c0c07105100010709040c00071075141c280c00c1107444a088a0110401c40000401d554100c401075501568410289a80a0606d100688070340c9100144482030b020000e400303000140d02c600c085540800500044003034992000d00000203150407107186450200401c0134840c02100c00d810110309400f010404203001c1d400c56020356114444440405036244002c0084501d43c21094440302d00e682441300400c0210b00c00d0f03d401003412200105501d14120000b0401e850a000f0540329290200300c220f0804420802d02401d10ba00500d60100045e9660000b804600c118203403a107500d042850018443c242941103d00030764040c0e543c12030303c0d41c3c1c03500e0b410b800d80c0020340480c8044508420b0710801d4035016184c03049100641500c1010b0015034103050300007030b40c05040c140e29a45810010000515a0014212403d500c181070944401460000900072200c040282d41503505008242d400c001c8a0401040d91b1010981100c240c0c5010030030f0312342d0345d0702541e02001403160030a100740a02c80b0341401e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 696717733 1250 696716483 696716521
    0x601050403020d081309050105060703260c031006030218060a2d033c0b040f05061c0308010603090f170306091302100507031b0b01060e0d0506 63
    0x149189410394a6020600c802003c85050700c4480c004034180341e403d042001c00e040201a0303940d05000759410140040c0c103070b1103501c0000302072114006144000444d60f0340c03034120030200c6101402c200c2c6802c4e40c2240190344120341d0340d82b803240010300118180307000b0310a9500000440380e000940b612001c090041c0e036801103075884240040e83e03c209644805248951b040781ea140c554001c5042030a902c041c040c0c81400703051034041c115120b580d081370441c591101c00001c00036003041c802c440310004034400400001c50069040b40c2400e840300c41620701c80e00703e0340c01980c0c05c0d0384804400704000350720442c4018140c0000c2c00604500010000c60f8407907089111b00a01441009094071240d540340f0a0043c3d1314410072404c0e08001c4100015450180d40042e400480c84007695140c662030f81c00142c030303407084030200c005201c03010402005241c0f00f151841e165905400c000481c40456003040d5142c0d850912071480003039040160640b030340c2000810401c030154010000c04082d10f03000d10444000309002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 696718983 1250 696717733 696717737
    0xf090915090106030e0708070311010503041b06031d011a040e030f07050105010306060b030f040b0705040305010c080411010302210a1506031a01030903050a030c02030d020a05041706040215030601 86
    0x2000e100299558030700880d0003481c282c0c07000038a11109600d01800c1403080c2d4045101038118450801c04540c0d09828944000c4003481c009a030ba54403450b00c042400c4600ca16002000b00e075680c00704a468050b4800350000304200380a1006001c0c9403092820b0f100c034076038910b44050500c610000320f401c09402c0707050410612130030703039080c030012490480041d0400740d010742e201d0391148010000d114480c41041d010341b1200400e68958501031031144074850004c2e00082150036180300203001c0600c50403d0f100074641c000300078400c403100840000d1150b14240e5003642d020400b03501e03491880d0700a200310307861a00d08501d031070502169000111180c90004104203007164559a11603100070800301d6100103000c032a240001c0304140c2072040084103125542982c10305242810500100e6004020f03240308602c01c1c0b4000c240501c00c1c490490a50242603000b4020900208048080981000180041c0c1341c60703021401d50b40050164041d9110b100f0354020303400c4520381041c074820031624401540e0085040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 696720233 1250 696718983 696719011
    0x90103090c0914010302040c03090206030705130506030a050a05090106210602120c0a020d021f0504050a020a08010c18060c0b130f0309090c02151501030e030307230f0909 75
    0x240c1041e4040e1103d01510782d80d901240c4005104610749407060200e81c01140c5802c22800d9100d50116129100c081d0079001032010209800000c0f00c0c81c40444405440e024000382d40760705004401ca03000e0002510502265410003000074040310f8148558000c9070351092042c0302c2144421425064140c00e2802a2000b94080100c0202d950541200500550102d6032040e501d12204000074200030405540001310342061102c00b0303071412054a400341c1c8030400d041c0007409482d10703d05146015100407009402c030580d07960000e640d0303e040d48120007442e0b00351900808044a4809400e440c00d407800b0300300100c3c0c0d214027000c0118007400151680800c41e4564080980469214581400144581140028444e0000340303d548028040e0500d0120140000c00b004000032214058010000380000000c060400c1c4445007680300e600030001c0c0014203029030380c0d00c0c00e00d00401055405036601c0e00d41c2482100c03842905a081d4203040b15000c100174940c0c3c904206040f02045030000020f40b07079032031307071444 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 696721483 1250 696720233 696720239
    0x120d0608010510081506060f0f071202072d0b090604030602072402031302100c0204060e070e0904051c11150a0e03072a0f060e01120c05090103090c 65
    0x911403280141d80d2603c607408214604100240742941c07a640500d0241030320380030f01c50146c44420540d51141c4d2110400d58950000c0084c1707640034041c190000d400038413504c210455031500031035484240d03280c820b2869204400c44604042c0310940940055402c54410350803c4a04040e00181c102d54200512481c40d255403a00c13603c050740c10400096850b800f100903a510828074200140b6071141d562082941036103041d164a44892420a80282c058003030145a000d20701c1c4549410006607038000c104004803070b29280d101701d81107011103160010400b8a13030004040c3c50300c8480d55200d503500000910900c900444401c0304040f5000f12802407100c01042c07444901b0040c4010314a441c080c0c0700303180b260700d01200304106a901100f07201101341c00800c0f888000c05d0548402d04500c206050140c00040c0b140082101c2c0b205043e13024045654049401017140d9901c4404003c000038241d840c0d042030a068180310003201c04045c4800085101004664207550080c0c201e000d02a0040074100c0290303607 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 696722733 1250 696721483 696721499
    0x306100c051606080f0105030a0b0402061314090601080f04030f020a021302031519030308060d05031c05060306160c020a0812040303111915020702040609020702031e120d06 76
    0xc11900b40801000044041c003100e0f51100c0c2d0680c0c0000c100421956070b524080200c3e0306c81c40340c00d07400713080c58290340001000d40d00c0d0342c4101d0354203152840450312000d90b01d2044d20290700b0f08030507240c07148041c0701c0850401d40c0b00d1090b00340110401040c003082921550b500740c9501d0640f50308502503000d10b50101000d691010794994a010041e01d0159072440c0c02101d40c40c00c0000c1daa0524411254190001803480c0200c8a903002e480c1c1c14102145540c841e000041d075a0301002d030005106200c00102c0311a00f02c40302c01c4102c96103840c800240301030f0b1903c00c01c250b12131404441c440c104060110741d5142132032103681c2c8000c9950001c0d004091040d154400142072840420f075060a5042c0002c0070000c155121a6003448455100d0213000f000402da400c400031145c1092001c2e11150810721500207820303880c2c1c12242c90b603500030401c020355079481e07000002941050209078424000c0b401d040e00708038040308018065501244c00780441c02104811381000d034109040000f4602d50b03945010402c25 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 696723983 1250 696722733 696722743
    0x105040b041118071b0c080d080c030411010c030c0b0a0e0709090c17151006080c0909270f0a0605181009060b0d2001140306100c05 58
    0x5801254000d865240609002d00c5240446460300d0080004064400c01845032030f407880c0d000740b00da103004c01c0f0034109a030135200c02000d84900980b0417803056400141c6040c2c0003421040c0c2908a4482a046661301401c0e41150f010445000d042c01080c403103014680d61003100c00d00500c900c07a0070b080005500781d48500b40711440c01c48529014aa035400303030300d00c04003042282d40e0040102c044203204640c11a0b40300914204c1c18403a11800305190350f003009024405200ca050711200b0713644100414504034a95120b041d40510454012035807a00219141c140c10320102c441c800c00240080301d081e00d442140c00c451002010880c2c80540b80700c280c95050040a00040d400d00c12600020301e410403940c201503080300c00c013400103410710000e000c03860312190010a000e5000c031540320b0b0008014a00f8100a000307000d01c0768a9a034040d90317a0f40394004215580e0707441d10a07889800340700080d00022000541e410280f00c10599200102880081c40a15000c5102d41f20a40742d03182102d011482ca03138a041c500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 696725233 1250 696723983 696723991
    0x30a0219050d08130b090c0a12050c0433050a0f051f110a0305030f0a020304020306040f0c090204151710050f031c11060604180f1b08100f2a03060302030105 69
    0x5822903040c41c07c11385400c1180c10041c00e2800700c0380e0000000c55a42c1075940c490f925045010b9030301c4600e003408144000740303091101464441c069903400501d440c131506060140c05464411005240086182c1080c0c2d004c00c01030b0740f800f0340f640b2040d04c1c03400407034898441c582680750100074031401c100c00c26002c10302c10004100d00c60b844603501ca043c0703131010206404006152a220f00d1040c0204809660006550b03078025800c1072100b40e40742c03100d04002400943d203400070880c00e4000540043d81100125084660103c19a43ea0403180d5180706145400b400c1035560b000c024075488c4d07013844a0700d8054904a09681c00404039a00402c4100ea038425400b00301c004100802c0c49543e1300f0000c8903003400342c0d680c801070440301004000040b6040102030342c2c0300040909120b00360150801001015410700e8448100f151186e64501c2d91950821344e83c07075500380384c080e40c1c0b410000000d241118a004022500760f0030403030780c401107503801c0c460001e2581c1ea624103030425490314000400744c4c4082c8034040c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 696726483 1250 696725233 696725251
    0x70e0f1002010c0e120a0f05010e031b0f06091b131407080c041d0712050c03240a0312140703050702040c021f0513050609030a0219050d08130b 63
    0x40c81c5035140300500480038078556103020b0841c5d02004038a04034007050100945501903003c1c070701d5841d80e0074042e00604a00c0e0807184ca0340f00003d14900d549220f0100c0d912144060404c9403d814044a00d89844e031380c00791074640c215884104501d416130380c1100c6807228520041c015001d04800140000c05a0b003100c846611406295410322101641c0040b00d10350016504a440c1d240c185030a140140080428115080a40c2c03d0380216148600c50000d0110030b0b8001c50f0701303218034180310400e8091940b040d03802c83c2180d40c5401c6111709040716600301824000c0014110011545140c8400d40021040c00b102d00c1007040803050b151454041001510060380a076480c1603c41e03035030b481480200d8400c04c2d50207055601c0b040c402ea054198400044c40b02c140c602034042281d4480700002e00c0c60072440f98005016000700020800b09000002c043c0c1a40519039085490581400240c092404000800980140c10502942d10b055003c1e0a4441d0048807002c129035001a445d00e030110603400030f407940c3d14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 696727733 1250 696726483 696726491
    0x70e09270709020901141e03040606030206070b0106020c011b0b06150f04030606060302030f04030c060b131505090f07110705090a0c0201050105040519110408030a0c03090e010b03070e0f100201 85
    0xc050751b8004420070b03004480c3e440e030328035024151103000260541050001d0401000100250420605411200040d0390182405843d0200f40c6043d50b28000c013402aa80184030b40d440c1e40700301d58410050000f0820340d8010818011003291a81060403500510f00703500588040409070b0003140d600024078995094090340e81d200d81c11441e103401a1110380c2e000c54109030060003881640120b040d201034000d58507051242000c5c0f828a0088040c0c0195601d056100c0c0c820f02c202039010341550014006240d45c2c0304549001600c5000b004643c26040c0c1c0c0c2080c103008003000250b02d06025441c050480b8195100702c9407d05d9035280002d81400040304e41c00c040340d40301c0c09283c1c0c0740b40c0c090140c1400f40004940920151424040c516448000403c000c22502c3d1501a6928800c031610100d8004e4010213060b240d031a10715200240590b005010110001001c0d81c5000070400c90450301c85040c0c43c001e00c0054a15110620308607108200314000030741c4402211480407155881d00750802801c1106e80000c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 696728983 1250 696727733 696727747
    0xd02030916060819060f06080402040b09010902040608061f050307020f190212011437090521070305091206160210020313030f09210b070e0927070902 66
    0x184c440a100403200c4501414102d041c84020010020281a039000713180c581940da80e41c2c00090080c0c92405401500641d454002298118060f002001a10946e880b241c3c1581c88030401d0244540d208251060822800c000026105206000658000ca407500c11240041c10f4800c44034144814000405804640c6282c55021420182c0c015461030540100811003c01702c0e2217041580c500045c5a015045404a011000e41111046148500b03210b0150901c0010400d00c0500007404d100d10705903254490b0110103514900303002c0b1602c441341d200c1a142c0742441c0166500f0303100b64000342e900c030364059070400744410542c00c10402907101d01d10445290045080b038480c080e08245070070410b250628010010040c8803040d1030028203141d5494a010f010f000110300046460303007529041400343e4001d003400c600d114030000c5011070007180075840c10075241d00d4410055458003101c001007508105441d002940e403d1a05501500b90034007240c844ca942d809e200001030404c11240c00c2202120360202d034030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 696730233 1250 696728983 696729001
    0x212070b0c0a171015050307020703080901020f0601090921050906130e07081609030c26060109060f061b060c110a06020705060c07020a1818050607020111030c0d020309160608 77
    0x176041882c03803030514a00e1401e00b1903000f51912818000074280c2c0500164600c6240d00c00c00015010f00302183c01c0e966996150302000707000c2e101400040c1ca2503116005038600302c00a41008603a03000c5c840e100c0340e203400b00d410240000c40d004076150a0303441c0740351100040c042103032150007031059003965244452032500740700c001c1000700303010036031810000c50307280520020300d0482e42103050310444813100250f0016001203004948002d03030b03c0419405640c00003d040d0302075401c03d0381a103041105c84540c4544a050071185000003000581c92861415540c1c0c020400300c0e0b100500024142c50040b010403005c0030310707600c0d01542c0303c0d08980c3e042d40041d6170024404e040c031a440d00100c0c01c880492918855800183c40350402e1301460041528900c3c0d0341164241c15400501d2501c00d030f0030110003031907441c142181c0398030b82200c0c0303c0c002d5420044124621798058003100e1164120465060800c07020028410003900010405c411a1044c400c184c036090802c440c41714005d00c6541d48980c01c3d40f03448440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 696731483 1250 696730233 696730259
    0x10360e030a09080f07090203060d050726011a130e0d0e0a0b09090708090c0d0605010306200406050d110301080619180605130f05030a0212070b0c0a1710 67
    0x2030f0f2800d4118401e18002884045a818111480040056101c2d222a40040c2150f1100c00d0b0040040c8034920002403040440803803128280d40d01e184611604120b628224240c441c0100c0c1c041400590b4080c044551401c2c00d21211444590300c0c000480e07c0045060ba41342001341115507000c602ca40c10355408a00e401010744001c0c00040d00c2050510340c030310b00030840c2014040d04100074445044c0009825075010003000391000b43c0200604400f40a13801c0900003407000380010b8030140c0c24800020060410100c0350741c60b002c1402160b038034151510340102e03056004403034500400c644030803040b80190302c0c10300654041d20808000d05210304200040300c40c0280111002d05c510f5080c80b003400c064600044110251540008022400d569211300440d00c40c048103100800b810f148040c40c1050100003c082c0001003030680803150310114403900e5002d58024000020034002c02c0d40c0c00203003501d14060103400d03800344500b006440c0c089000701c0141480b034115610a1b038541903810400400c1e581e900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 696732733 1250 696731483 696731489
    0x703020a12050c07050d050318060c06070804060b030d140d0f0504050708010e0a1115040801021201061116090e1e0a050105060a0506090f031c031410360e030a09 71
    0x140c0c01c2c1b06024981c3c2c1c00742c40307015060400d199600070741c0380c46070a41c85050441d00074510190039900c42e0719020b10003802286080d101900c940380741080709600e0b801c3c006a80110610701d6100c0c9610303075041284200071a0301c8a00d4011596840b0704051610300b82c640200341c01248140e001d00030b1541802455030071a030411902c4041a8864941e01d0045010300f040104005d030b080d42c5070400d0808505406180c1d200b240c2c04101e40b50306c00a0741d6180c0e07100c180411816903c040e80d964901e03d0001224551f94200c0c07400c10180110660010003255404d5408035506910240a4030400048001144160091400d40990503040072543c00204072080c031409600074012204440380604040c0032807114001d024a0134042c04a05401007080e9408000a5001400d0740e00c0100c050015464001c0150446a142c484401800004180c11440506500d01521031a140d40722401802d10800b508400b0200404045480828001421424240120115111468011a92145800782c02890090168 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 696733983 1250 696732733 696732739
    0x3060901050c0a0f090b030c2205010f1209080c0d09080303190c02340e0903090114040b0423010903030801050609040f0c02061902120105060703020a12050c0705 71
    0xd00300406010480240c980c40200c510b00030b8130b01c03104104150345c50110b5400c481040c072030210400003a9901e1000816442e03e03180e0180541c070041a100e500269064082c2d5800304243c003014000e841c0c404c0240c09171140811102181c103100035100e111039940301401038000c80e04944040740800341c0081c103010041c45504002d62840c41c103080700c2e0300031205c01c401a10f0604e4488910751040c0d0b10030040302040244941d8140c4254035244404001c000e0800311803c040348106400081d95582001c040d403003406c121025601d040010b07c01190118030560141070500b40520021809801e581c0251014041d4164940010b42000c40c2102e401031180d20058100002d5080c10b100203640503411a0448505803111901d0320081c00c00a8040e1200e401402ca0861420b00c0141005600140300e60245400c1000d14001c1c0d0052904107090340f08856440070320b4110100104030718208003005041d03c1e406403064a444052641d2895448403204455100061001c40e4410a0660034021200200022 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 696735233 1250 696733983 696733991
    0x702011d0610030f11121609021c05130803090601050f09040c060807020709110405180903120c091315051e2e050d050f0105030307060e030405041a03060901 69
    0x30b8180c00700100a0200400d8005043e51050810020b0100c01e400054000c10380c61340340841d009401e07911504240c0c00d44900d4000d120008452815208444482c451000f001c03505400419102001d0a4050107603032501044000e0100401ca60b14003a502608500c0d02070241075145c082001054018608603510a108000034000050040411042160007504080d5425a18190180e06000060b480440c0170350511969601d00448580280309850302114861888401000c00030f4140b0021941170302142d004001151040040315042503001810310301017840c081c040004a501e050460b5200c040054030f82091011b810245545140a004141c40200c1003960780655080b00440781c00b0380c103008488400302c11100d0f101c4043c1c209072016411105038050226030000a080707500070709500c203145140c007010868103419240143d04030303640107000754208462a1142c40c0200100404040300784020040001e07144c40e5801030ba800810441c2e84510107403040c406240c00e100008006180326490 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 696736483 1250 696735233 696735241
    0x20a0807030e04050a1e09020f060c0703060e1f0203060f0a0b0309011103130615050a030b0109050601020705130f0906060b120a060501080103030f0c08160210030b012001020405090702011d06 84
    0x30161181c00c1801c51302a012a1f101850b00200700030544001096400010001e41000884000140300f001c80707100350404c001040031085410384611a10f50f61020900a6181c0a0f08080007a00138541088004004607540043c1c24006038085085a02c01c40701d98401000300007281400784036840300c1c4d8840a2100385145000b410840200e00d0f0744000410817036481c0f1086111a080d500b011000d41405419a541140c0303908004055440034818800540c3c01c26001171000c0d480481d000084802c040c0103429000309241c800d50103400d02c042329112550380e402e46030300880c09034040ca2000704401c40302c01d03aa40000c519500c0071410010500c0800c2030402004100e5070360b022000b41d0460307400d03203400d003030120f104a01112401e001c1c150292101d01c000c1140b03507500d94007c00c080c120f00d2089544400f1607480074025800d5422414026001c51544108160560b106102c400e50b0304480400042ca401e4a950001d51101026284200140e555842405c0c0c61500e02d016407904c192600001c10701c3d441c5c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 696737733 1250 696736483 696736511
    0x804030509130207020622060e09180a051c0f140a0305091c020d0801060f0806040c0e0d060606030e1b102a022701031101020a0807030e04050a 63
    0x49515002801261450201200107420354103481d0f181e80c5c0100402d50701c81c18282406030440c840f41c900c0e0303042c11004e000081c80320b00900b40d240ba40c10703010b40074006641d5000e046440303584001c800c003913050150845400c00a00e06002180e11000559032a52011100c060b000300692481e02078201401500113094000e0000b0205403011900140f0300840c0595424110034180000d1010000e110103002d040701d03950701c0d0007050b541c9508101da5110202030781e0707541c01154005131840320075000c561b602021a2a504058008010300e000310709003007a0700001d52012440c0c0100b0164141c6000f5901c90381484800d030315000303443c1401504001050708032060603800c0c18800c03110a2103880303014024150700080b401640410300301d03400f030240d800040040c007220024440c50b1050491182060341101c5508000804c802071411402c60424800d61b821a5540c0704651140300074070b03041d40304403101c980000707000c0300040070703904d00c640d03244005d2840b40420b00c0f00351003020f011881150705018416070604 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 696738983 1250 696737733 696737737
    0x60b01050c0a02060a20010b130225170c03120105011416060609061205010b060301080c061e13031709010c06020d06090204260c010206041b050306070f030c08040305 73
    0x260115421691000b94460a07a800940c003041506c40c4144d10891551419040d800981c5050082c1d800d80382c150b110b641c0280482c880e0120020301e000d08205c0e04000c120501a080340b43e01e10500e1020f80000c04c41d0740030074054000c0307a08030341c0350f82c000110b054510a50a165600410085c03c0100070a101c14640c81c07400c0c090440000c1040d2102d030140414007081b600104014000d802007000001c1e260826001948040c04080d9150340c00c0c08560071981c103100342103d048400041c060306074000c181d010800a83e02480c0d1040d01e6904070880c0602000c4440e00601c0d012550752224250145540b400c0b000a86011420001c805001e0181242c10b9800425640e071460348a04010303510400300000790f0090816801c40016103101140100d11030702c607011800d100c0381d424401780c01a0409003c482d5600e5201da506180140c0000c0c0101d0005000c116034904c18003045040620029240d00200785032400c111401c1c800104404880312306030b9010300c10b800030380d401450000200e1416131000343c140c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 696740233 1250 696738983 696739003
    0x150e010e060a0b0f091015030b040c08061c080906220e10080a08040603050c07050d02031806040f060c02031903050304290411040204080a1406091b3a060b01050c 71
    0x50344001c002481c2d100c9c0c1d10194a07010010700c10010000d48d079900400452049807000c0c06035074050b40c01b01c0c0c00250130358091034455002c02024a04a002028080d03160010b0369040ca240070400716100400b014804804043d000302c0090102c2032030000304002440e089940103814540001404d00701064483c8225401e84015080c00300d801e4807500000b00851140364409481400781e04188920706502000030030610071040f060300844041c031010000580700d24811044480600f24040012602546014407007a00060641c1c03900320a003a100e00003000301450460010388000100800c000f1324210700c8444803488400f000e1890181c0350148451900034201030b114032500c0b811240e8550f1150120b82c0500038103416076884000d2071071701040e5514181c40034a410300a03000010501c03500011400c079115508105e04100c0303005002846000019040790103d01d00c501c08408441c2c0b0401c04140741903418000702e20300380300b0031410584104c0c2c12400282d41040810010b210204100107191080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 696741483 1250 696740233 696740249
    0xc03041127070201050105010e0a030f03110d020303010312300f020c0c040b060a0c1403040f060e0301052802031e0c180607150e010e060a0b0f0910 65
    0x201088200059840d00c01d421401d010800029080d10001407503900103000d140c0c540c0003445640d032aa030040d80c0030014088a40c1d002120648204040b076a108860320016003e0f00b00003142d0030340c48500500b40f5140080c400c1c0980c0c8004010020450424040c0f40c10480500d40b40700103058000705010801c140ba450804214500b21070005404040d51042840007003d12046680f29840700c2c100b61502500b04803140700f80e140404108243c01e102c41182c4154400d40d40b00b003103802242d980d00c14a080c980c072003840c0c688003d200c04981c0038500c440b1a80981490348400811110303410815003510801010701030400400891112040d1440d02803a803082c41c00d140168990b5540500c0d124200620300c5250b0342103e8140c20700990307003013090003000e2225900d190035654660354000e10425104080f0300511859040c0580c541c4e002e9503a11000486901c440041101e5403031405051400b6016030b0242c080e20f42c0e0740d29007491b520700722520010145044c1d0340f86100d031070301384050b00396000e1900c91307046 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 696742733 1250 696741483 696741503
    0x50f0105040b0102010b04060807181b0f02070504060603060e090708030406110f0105070809070b031b1b0d201b0904030c1e0b370906060902030412080c0304 69
    0x1443e80c001e400501031050040c03c200301540c1e540420030783d5641144600e41402a00003006000d4426130b0080f41d42110b4420356a0301c00b181d01c048101c0d04405081580c80031401044800300e200d90f2203000b002d000b000e075550040341560406d0300c0f08440c0b02c000760107104141e20480c0c042007601404002da400300c1d421803c01040220140c000c40b030400407500000300c5294078010402000940098415014554400445a0f42d43d07da0303e030b1450342c0c40156105050341d004084911951b00300c000041802052007501021100c01c1c905455242441308640303400414880c2d0f5128208002c0800d0700146a401c020080040740301c80210210341c00c0c0d0b02c900450003406880d00043c01e240c0142c0c14282c04075400721140d40c0400068540d485642440c0e4001c9880420348008a20f4004440d442c071400e0b044841003082010f50001142840034204280b41d881103502c0322450408240c0606c0390100400405001507600d00e418680701510a6514001c002848040014440c1103080d10003640d0340b0907441182d0079 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 696743983 1250 696742733 696742751
    0x1a4614010818073c03050607090609120204021c0e01150506030604091403070f02090a050108060609100503070803070210030227180a20090d06180f0503070c0603050f010504 76
    0xa0003c1c1ca07201c15130100290480c41d03501c1c400501c0c00410450b03024106661003a03e9011046662511078410480021009038090200241003034114180380d00c010f10051030324051505100e8403006450f003914501d0b941c1c8003000d12148081c00380d03108080044800c84065803e00002030340d503000c090001d6005a80d201c10302e5041040c03800141441322032110072030382c1f224042e29104e074070300040800c12801482203402003500b05006000b100d045c0e4286a020700800c0e51103c0034000d0000f40100a0b1003400410400041d058805020304005450390b4030266070360300e0040c01444421403070018294209807040000180c800c02120307a031055800e030000d501c9014604540000c6030035107105500029001c0041c00d11148454a6008102c602c941e03003a11240030070007000d85105030140e0a1000d400003911240f00380040c0d0a40d204d000303202c000c183d00507040c0c140da886020b0310742e80c0c0c411308071410303480001d0040a01071249900c10041840349010300040c07801d4810402c90341018400c007409983c98640f16 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 696745233 1250 696743983 696744029
    0x6090c090919080f07050703031d220f0e070905010f2402010b27100e16110a03050403170306030a11180a1a461401081807 54
    0x44030003401c1004c81c661156481d04041d038546081d840118041031001d04c644041c0900302602066141c402401d00d140d0390704100d4895041006510501041655170b28030310201c0710b45129001c0d40c000c2040c020a1014100a85034081740c0307040c1c003c80f01840c0e413080300704841045000b0b66211902c4804041170850300080040e40940b074400d0381e1660040d00d0b400c05500c1c0302d01e40c0c00110940c14000c8402240c035200c0d014401200303212030017440342c0090403a0010b044003c228008a0141150b0b240a07030384046103c25903410000b1002c4114000b1300001303001c000348042d500742c11011800c00b4659a165041120009980d5900d07013400400a603d05051030340715644640744103021035440c0b54014414a00840b1200c010040e040c0b0940520b034a5030480c9a10741002220307400c05018110a0a0b260800d20500c01c51071010303c07105041c41085088482c0d00e02000c506060014140e00d401e02035088019000034182e10f00090402c40c000c21280d01c5001400320009800084500c9481f007161103031070718916 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 696746483 1250 696745233 696745237
    0xf010b040b030604030e24090f0d03080f061306080a260406081b030403090602010f022703010b0d0305251a0604180507031502090a06030f14070206090c09091908 71
    0x8258400d1040a007904107c5207601c00400594200300d03030200c41d100c2034108002aa41c1c802201400082030f82c00020302c0086030850240d00100024031402099209030100400d6407590741114087c1d4014107855401c21640c11103a904c0318917100704920b80251114640307115802a480740c401005483c4001c1000164099004060304c002209195507910f031504020740110340a00c211030041d0710303086c0a40140d94032803080e900b465000f003211102c0030300d001040c2d0200c15400010690705550760301c2d841489a4441d0441100c0700c0c4680c4460740ca4040078010100c2164041203020114407034502840006a10061500e02340940140160917586444020400a028944c582041c0e0075007144c0c0d00d024420005581c4048070300c1581c42040d002d028808140980c010b07004415002070700d0000c02e1064600980020304180d01c10b220000c0c2080644018412810341901c041002d42c0002040c80020b01c0c040c0614586501e0a071000da140d81042d131000750351011064844941c0d910484800c00c104042242 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 696747733 1250 696746483 696746509
    0x130c0306050112020a090c120218040903230316200d1206050a06090e091002070b04140a030206010909140604050c030d02010e0d0e1305090f010b040b030604030e 71
    0x80d040040d980c450f00020103143c071410342603200300e2403440b00143c00b66550007404a40041d6a941c140b0503403110440300041e400448483c2000150060700040d6602c0318030400f01d40a00035500e1070741624002c00c2c0180c8003c90002008900d680400802104922590707001079910740340c2c60801e82c2c803442108043c1e0303a90942801c00c03566000307250048080c6c90340a140c1030000226850200b045a5840c4108205010305114071030201c5c080003002c1050720855a075044d80b0441c03140a480f900000f0316000022a4040e8004445450601382031005001c41d24154451101d4504020152546039460107903450b101441040310307142d200d4424000300200c41d80e28054400a850448186082c0b0b4506a52180840c1c440b4902a210b0403003c0780c5103502c14025000d42030f4502000e811100850f00040b1254111095100e400101c09080c031014620140b00c0e16118580500c0600000b082c407800013420355a161520301d01c0f40f803c08495a6180c4e5000c582150090785c98144070f0780810080b004107440c07071000c07a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 696748983 1250 696747733 696747743
    0x111f020904140601031d06040602031909080711010e010c080901140f120906010f180608160503060a02070203030f030402041803090806010603020f0d050c040b071b080a0209130c03 79
    0x145030b405160000070842c0e4040d12007601c0500121101d5640040409088a110769040d032080b0701141c042085580103507004640680c0908840070f95122040036104540f20841d101c0c00d00098180600c1300004980211140910704020908100070009000c4c41c1404006068a140000c0843c0c1c0390f801030701140b0900103102c0b01541c441114102c0d08960350040d0b0404030300d03003410000259801c0c002084c441e0581c0c05541d04d02c440749003400401d850810418503405200c40e41c4003c0840c50410400209105081948a108001381000e051505100014000165890040c000000182d07408025a18414007104c0d4450b103e036110700019007e41030b451884410489030400c00018154024252001c4e1040e0301c080342c02d2a41e0307425081701284620105a56030007402e021205140109400c4160071030031080c02503040c107441302d0b2a00c80030303803040d81c04840c40000352a030080c0c803014075035000e00184418009440c4580881e00488c10102c4014040e200e0169403c81c0441008110745805005d5038100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 696750233 1250 696748983 696748991
    0xf04020d0606090e060102030910080714040e0403110c06070b090a230c0904020a090507090305100222060f1209061107030e0406061b023d111f020904 66
    0x10341e40580f440225004030054400d002c00005d100b5400001101c181e0701c0094608040202d003107004903050000030b402e2004225104060110080e202c0020b04050b0080c0c0180c4180d41c00d1600d00904104c00c00040c10368075410451003180710ba90390700c09447c9207540180d40210740e41d0b1401310711400d1800e0100700030007075084d0440c041e0410040382043c0d5800000031044030708800c006c804100003010101ca000f5881140040140076810440d00119040f20b00d605281c0c00300750300da0380c501d0304105c00c0b0030101c0e035034560107d0303101c0c04041d040080700d4407180010700c43d8200d2810890000e100710060202d50041c001c021468680c0c94285a205020180d0002d00810040340300d03070b4086826500050044c0c4c0020511100342034185801d210301411142961a810082e541e202d1030192600001d210a0364407541d0040c840300e04c2d1310105c154210b1340700d605406d0407000413500e68010303030b0000e40c0050f03104008070311a402c1242d03040015000000940017480700c1d10045482c0300107000c2e11075007003882c0d007250034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 696751483 1250 696750233 696750239
    0xd1109121f051b070807020d110102160503030403230304081011120a2301030b0711030f04050402070f051015080129010e0a0311031501140f04020d06 66
    0x4110703034214402110115500000c0a00148141c0784140c40c0010265a1192032404410b461002002c105100381e0405003410a99000508100789803038054861030034041100940d90b90500070300c01100302c44030343c002150f42400042a0f403400396020081c442c041200000d181c1041d00c103000407800701c2c01d200b00c82c0e455454400e07072500c0e00380140b840350704142002031401c0c01904140c00d8031404107981c043c101d000c0d0743e070300e0101780500412131504094000e103a41c1d8095140340740030558060b60060402c80300034140154000c0403110300d00d45000320340e0002d02c90240b801c4011421076080f14422640035803645440d007000e0703003a0781145000070150710640d61800401c0d68913800c4900c10700c40300c003020407a99640f100030f11b00740c9d80c10b910203501a0044003440140c151164100c80d000003410715001e040644202c002c40c90f400310a80040d5580e40442c8081c0c034503498104081c8104103800007080d11203525140d0f6030a00e80404003000340c454543c43c510f010b40781c1c4072036050f101d0900c603400041c8261a9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 696752733 1250 696751483 696751519
    0x120a090c08030301060f090605030103021c15060803040e01270c0219060c0e011809090f021809010f0207020a0e062d0f0f0604050603040c03060c0f11070501050d1109 73
    0x310f02206d01004c00d2550303030000740e000e00072007e81c0e0490341c001e002d014509206c2012840608500e4204549904107196580d1000da1144035450103828014015940c513404d00783ea0403c4004140c1c03140c820020400108003030b80d10341e80884100003080d9900419450840c100c143d050066100310449203104901070b600501040360400c00d565040b41d15407a010007910b070011147e10741111704001000320306e088100030602c0942c0c0950301c1e4a01450b8040080241076002a201d840242c12143c0800c26910900c5801c002c00c2c03141d9944803c10b42402c40ca400c50342e501080100044e40714107070040303400c0e000082c400e80b121010140480110190503200b80c840d039a04081103071080480f03030f01400c000c99240c0c2141c140700642e2400038400420050174a13280108121481d4030040080740c01d91520080040003800354007030300c43c035020540c44041103030101d000700600c0340704820311704c0010b03a1011400308010b903080811162030425690000c130722400b095030070400302c2c801c0c0304255410200000c000c0320240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 696753983 1250 696752733 696752747
    0x180822050d0606150206070504140a090204090203010608011d0109021c2c060108030d020a0207080f100b040c0c030f0c050a0c06020f030301080309130b0330120a090c0803030106 78
    0x2100c13240085200210003808a90b0f0f40021a441c00100324104001d00c0805614140000c0c00c0d40000d03d6641c02c01d48031622402603070426400b1142d03e5401100600c07842d0340101041d40906401e003104542e011800c0b046800c0148184181041d1031f0b40001c0c481440070007030f02019035014050009104042070124585040c2e8450020341e480030181c1144000019400309100c0d0480303c0c0da1004504080b01d03c200d070320081d40580090000d51007020800a0550f400b4090690b9210640c0e010b8690001028140410f89404902c03240c415443c1080041c0303a00c0d007164000181d5074251419940509039140150740c465038090015040e0b2050b95159401c200d0000a00030a554280e403d03510001014071065903030740828014030f108c03504203000e00b1009080820308000c040404000c041003105005020906121900715601d00751222a000803580d0b41309d6180c0d10107942e400315005450300011150302c0b124144c01400d510411a19081c0b01824042e103180140050b24050040c5d99070307542c0d9000054054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 696755233 1250 696753983 696753989
    0x2040515030705010315170a050703050105100506070201022d150105041805120702180703050901270314190c0605010f03030c0308100803040612180822050d0606 71
    0x280c81400c801083c1940310780102d040784c00000d281da1540ba030414824980700020104094420f2181300d545001042d004c1104000642c02000001500d0504a0201595110740c4d0400f9005580c104005001030f640041c20b0b20b142c040602180600324a109265444029003207072000851080c012104c4100fa0480440c17412124120b0f01040407a402c125040c041446a50340a05590080d41d031b040450300c000b00c01004c4052005280f101c203e1020803580303103400740c1681c50000203652a002c104440c1d4091181000110310384e05901448140f0320b00300070f070782405400e000302004182c0d146916455a550150340900c04560002031003030300420300042404d0b10300380081e82d1180c1481d0002915025281410341941c0c0c01d079071f80d000c0d1031483c3d4909646141d0050038051000312816000565034070240f0250000e00034035680d05424030424456401600c804030000340c100c0394600d900b0f07400950040700301c070807084070410b64a440d64440307014403255039420360000c1d030051140c10400d003c01845a10100070303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 696756483 1250 696755233 696755239
    0x315041a04050f06030a2d031110150b0d06030602030c070314070818030c0405040813060e06030a0b030715050d05010e13060e0a022d01020307080a03020d0902040515 73
    0x100d036803003c85000d40c60a00340d40190f056003111010b4404246030448840c0c5000382c03120204079240f070f800c1c0390961104811009a000403600041d00c01100d1042c001c460841500d48014005401a005800345040d82c512414204010000d00320f0800c0c040d0340c2044c40115040f400441d1603150640c4680e40320340c4180000c400080e540300c18150000c0d00c21041d680d600743c000d0903503030428010100c00960050340e003505170b500d4416030712224020b40e0369010301c0c0e00c00d912680307a003031326103a8441c01c90201602ca43c000d2400d00a803801d501400b0b03100d04043e81e5106450b43c0d40840d1803040f01020a00b080321796044008c0c1115054000003030503400400a0880e22040e05041000303a0380c032a5000340000003070b540211843c0c0000c40900129620303030801000b10248609945e41203005600141013032815040b02d45a14000c1c0b0345201e060301443d400000140c000380051458600c0582d031301c0082c0e20034040e4910505a01192070203680d01c0e254080803d066001e8410001360500c2e04418096200e10303a00ca0f44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 696757733 1250 696756483 696756491
    0x170c040e01021e040321121a030d03020c0a0213060b0c16050a050931141e07030b0403050d020408011b09050109030f02040902030115060f0c0c0b0315041a04 69
    0x60f4003502011681226000701c05201c500400c41130220441000320040300810880040b0701211440c01d11480103122803111040c1116440300081c182050f41c2d841078a0706051040c07082a41500d008184c125405504450030070440c40c1c82503458005020a802050941401040c20180e88000048030380240480303031400740200d0b80d64030420140a8007400b4064010360340c107002c600d403101100380031020840000620070305100d0284210302c1c2801c682e54182e400e0700c2e8800b1101d500c40c5080c4241040749002c01070340100e1081013003203c0e64404480c400181040c032007500240a140c824000c1d240c0c41d00c08140300350354071640c48410b64080c16a4040e01040403102d040904030f404d02502c15101201c00c182c40300d0740b40a1a6858000d000f440d800350a81c0c2007500c2e240d50f00010307542840390300380c402ca00d5103003041311504041008003802480003001040c0f09504a681000c5a5040032004c103d40c540114580c0c1e070794036080300c10300070303480240480d411509021036041c5d165400f0403102c1e03112900360383c01c02c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 696758983 1250 696757733 696757777
    0x110a05340b0f0c0a02120706170903031303180f0305100b090c0c030d050711100203091b010315080f0f07030224131811070309170c040e0102 62
    0x1012280051150082201c402c0046040280340e6501a107050300c450402c0d0f440f540083c1e004074061202d800940322a07078006030401d00c810f0f0380218504101d00c0040c2618002483c00107107040d03981c4005040d071106503181c0b02e0603c0802d84200b174503d250240c0000d24140c1704d07036100d03c08280d1300030602040344d180c06010031140031007950340303e0798410280c01440a80c994441143d42152948007400d02d0b02ea6010411411085103654000c450080b16181d07500390041c048500e00e14280480d2400700c04000c1e0040040c000400700025404444000d05160441e160702e1100c0160014100100743c42c025160b0680b000460b236902151082803152507005507a041e14039882402d40311112400003d600220446e15400211201c41030b0b01004030202c100207203441c9840c0c903106d034400142e510481c8003244000010710748010710301414030780a008482c1941424480d642c00f4003625428026508154840100c0c003400342c6042104001c1180003030000c03c404001c0c80795031801f0354001c801103021103542c2e803109 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 696760233 1250 696758983 696759073
    0x1512061203030f0613230601020d0216180b0904060b1306030203120703052a010b060a1e050d0905011506090308030c130f06120614030d110a05 63
    0x1c1c0c0c81503120311150070f11550b6041c01c000303803012141301803004140d88440d040c080f0940c0b600c01400c85000008406402d2600000080c505017206030b01200b15080300c60214200035440c0308000544420080129842c24500360002c0244a040303041e0313074000b28480900c4140500c82d448411410800d8a01c25499200d083d0000150b50f001d02c00290981c2c01100d0024908400001a064943c800d10b40186480038400318212180004100900d100e05014085024030100b445400020841503441a080c003610450117011016850020f0303803011004e11000300b000d8491011a449112100d604100b204018200311380240f080302c1c0100c050b4110120080341c424052400c0ea000c40e503221000710702d1036403007585d502110341011074004150b400038400403d8500c4800041030140c5119a03d00040c81250a071071030a40d0000d500c0945264072480315140c0729100400c00342035241080c10301b949030400202c071310791828601d0300700038001e03018100c120340d204003002d42c07104411188121200d1002c0100c041c3d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 696761483 1250 696760233 696760237
    0x3090a1502091f170603100e030d050708100611070312120b0604120206070f0206070b150406150302091503040c03030908010b0306071b0204050703020301050a09020408060a0b1512061203 82
    0x1110000c00c41d089079130361807810007186a691100025080d140326602c00a501e10540b600645c041ca05504041040c1047d19101d1040a50040c0c1914100201d81042d01c4280c0a0b4141c0340140710811000040c0500c0142041280b40c0095902400a01e00000100e400400d2401c004400740c21240c200034030000c003450100306680c19101e440141241c4450f85508208042d070204c601180c0003040d011840b8056601c00e000f5001aa010300250840c515000c0300000001c51012610341c896841c1003001d02a198101001207140c40c5142001690b85a295000507034100940614140752000001040100107210514508a0b0b109403514003a168135211843d0a0342c0c030340c1080e0740d01980300200240985105040040300844030b1094240c00c204d40380c0204040e200c0460702a004280c0000041100e81005400702c00145070320b4a04609040c202000d494aa0310094141e03400c2e1074807101e00d100c455443c003841c40303106201510381c03951740c54408456104403242251000e100d0311400c2c05040c891070022007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 696762589 1106 696761483 696761539
    0xb06040311041d01140712140a0e030d02030a0209030d081b0a0c020607261c05070e030304030b07020606121e0f070603091211060106030203090a150209 67
    0x1070640409400507c00b01d41c940541c1c8481800040e0640d0f410010070000450008480c1c0400c5185000d5140b585020341d10010902c503030081c5d56070007001e1060301981a00d0401003101d10070360b0015030442d03508228a080540d503901e01d0150078020300500c80c030b40c00c081044841c50f40120345135030004803080702c01090901000700b8030250040082c00c001e0205500d01d15050a00004140311411140382c2c60603940c83e80e0210b40824001c040a504400b000f030304a070388880c0d81e0b0511400c00b083c00d985c00d00150180070041070243c1002a50b08041c10b041070b00900140d1501e414000440c05840d000348540c1c0a601d540300c0c2030030b100384010b100400050341c010400400c2410700c8400040c0801d10b08080c0709058600b0002c0500106820341140ca440c01c0c01601e030b95450140d40e003070800910700185522030f41c6480412100d0140d010300200e82c000c1d1031240010006c200c40c9085161084 = true := by decide +kernel

theorem cover : BRFrame.Cov 696582733 696762589 := by
  have h0 := BRFrame.cov_init 696582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 696582733 ≤ n) (h2 : n < 696762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
