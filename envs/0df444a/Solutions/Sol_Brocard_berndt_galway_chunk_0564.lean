-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0564
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:28:15.578386+00:00
-- url     : https://prove2.me/submissions/399599aa-ce42-4665-baeb-fdcd579d79d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 101258992 ≤ n < 101438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 101260242 1250 101258992 101259013
    0x2010e031905070b04050d1b15092301060312030b033a050a090f05030304030b130203010c17070c030f0507032d140403021f0e1305040204050f0702 65
    0x10750403400301c10032800d0052500f802c90321442d0712820304407030950f02c50307024454500100341d11410001c0c0b00c0a903500e00000c110070940e12540c08074406c10030790301c8640d15003d5000500451080841c1c503000c50021542441e42070142c0f141c040d00a0303110699141104091080c40107001c1e00504030920700050183c100300183d0000b5490405580c0d281421030181c407070280b181035405001c3d0711141c001c07036214251035902c0b1480040c54468503401400c40f203103210004011030349000040e030342642c0d8440e40d40090341d911904e004214616008006c3d5156003010524103005070070139510104000d012a5041c45a0f43c0c0075400d0780d5456813540020000380102030b040240c0c5225002500c0418420328008114841c6801c2034201c00c2c440d11a032031240e02c06072195281c8103401c0714403960000c0d01906e041e400c1ca89181c0010b08042140e201c555918680c180444614500c50404110203480090002285510040c0408001c0c44216000c038040c03031410010524841c0140f8480380300b1651540140025401c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 101261492 1250 101260242 101260267
    0x18011b0801121a0702010209061315020114190b0307060305040201080a020310090504020d020a031202101b03091401050a02030f010b03310b010329070c02010305062808010c02010e03 80
    0x80003130944086550901012020340d8900700144901c0e02548516440642041c80700780000c1002007a03030040d68940340112400100302c0f0842940228100240c540c0c88150070300110252107240c01855041c014070102050007501584440d0003107000381c1e104c10f065500c82c86e0402c100d11056890380d03044102c0103000c00900c0ca05401107540b250c409407802280310742035408500942810340048929010014514002c1f590400281105d1781d14254180122401d507402d213141c2507601c0d10104101611003840009014992800040c0040c1601c002c00c56840c144401030700030b40082d06e18116115440c1c7c0001000c20800c005c5d070b0b001c1c003220b0030810502e1034034041c0503400032140c4030720b446003000d510f1101003c12955100c46009500592200428022243c00020340c04486000709183d4528107041c00007181d4400c4804000303550a003030004c0c19448103000a1201102c2c801e02e50499594052500c8101118a8000044078082d030003c0c01b540400210a9090b00c42c2103100380440d50040c0071030101e119 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 101262742 1250 101261492 101261543
    0xc021f050f09030c0303041506030f0f020301050604230619180b0901080607030e0c1203070c0f030f081c02030a0b040605030601300203060c040e0705030c040e18011b080112 76
    0x1d030140c8d000160715569549003815658818425140c002c1c04a00f18403d6040a00640c1d0b4400c0d01140c04100050462008050305255044024031180310100004e41d141c503085108011802814006c85160b5502c1c0d06640c1c00d0306403c010750524074103200400040d410480b1115050723503203000144c2290f40c1e46490032001054010b1b44909603102d05480e441c00c54070744031841d030320305400e4030091a41d4045605004041c03034416888a240040003030350801c0820505280d000c04640c0c000c940d641d6812112441d005640f107030b06259002c141c130000034009005441d03030280011035000e171800c1c000305540b142096190042445106042d00740c0a00c051800d11a4094004030011400407076514000b02d40c010038079141003220003a41211001a00340a20459903a10a0703200400780b030b0080c61450200c411144034001d52003440d03039444030b0030089010b05005070000c02c0c511070220000c00490100e8056007071201d03a0000020301150b240c100120b040061a84005103190f000005480005800c1c400030000c1c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 101263992 1250 101262742 101262773
    0x8070b0409090201091505040617220c050406120b090105010602030904180b0709030b10050303120703140c0a0e03070b041a13080304030c06030902030607030c021f050f09030c030304 80
    0x280003030210710b0000e40c64461401d90b4a03503413655261402c10740c01a01b01201700128007078044ac02401c02c08140c580c8100b22000c1c0f452910007030340c4040d003850b0130488a4016000550f0080c20b1060104244c0c1e80b80c0400e10626005084c2002c2c10344625461b0350890790280103500060b002001180303006c0c20203421038495140d40e42000100da10071600c40000d1010146c0b0345000140000d24208240001290066082645904003a41040ca0300b0002641c1c2c1c8504440ca01c11200300400164460b8003075071080f18800c044980c201c0e480e160035122031141e41d02048000b00400c4c1002401456410f002501350281c45c40b8420561900b424407102c425501c090300480540c1520400c1828410742e1110704100003840070b1001035071621f0541c0342ca5560740c40341d90041c404040ca400d42d20400750740c001801d25048145400c0014021101e03000132420807001d258241d00704840080441100348190340911311800c0d515171000c0c0c50380c44002ca159124402c2c2c202c00c01840e4800d0000c600440c00011540406 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 101265242 1250 101263992 101263997
    0x60c0834080c040305100b041d03070b0c0d021606150506030406020c0c280b09010e090403030b18040b0c0403030906050c031b0105060102070b0c100509101407020708070b0409090201 80
    0x10240e8036503c00b440c148007800280b211700c1d1203482e81d001f00d062501503600324403240c2140d80103c82801070b0003640c82c019494041c00d07071460b0101144455603c00101c0d01c401401c1c03401550b071100b045000200740d1400d4001200c26500d0b003030002041a201140441c03d44000510701071079038407141c0f03406010390400a25103416014a403003200540d580c2001c00c4140d0740946140141055184400c0751518226912400d03041e0310420100a039aa880900d40310040d004030340b0890283c80d54201200100003611000381c110940c0388412080d184400ca03e180b2941c8510300c0300c141980e480c13100d40da841c09944402004200900c40c00c0c00040d00070f1020740024151001102c0c00c2c503111810303901d4200d4060404400307a9640340180412035034144241c90180010307880131450000000c4005075200e40d0541c40051041d952000310b9901c2d44148000e400c1000000d00134018001030590cc00c041d03a03030503661900984030b0750200140101002c10798070100c4049000c1507040c1451b20640e0805410041c1c400c904 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 101266492 1250 101265242 101265247
    0x2031e13080601090c020606060702060c010e07170f0316230a03080a0b0a05010e040c140304110109140915011205010f06030e07080303040816060c0834080c 69
    0x210340d482500c0350001000540000c1a165261a04030400c4480744615041150400410001a80c5a6004448015505841c0c031540c0c0d050003d400340c010649140038000900401200154652810389001a44014002074441c40c403051003180380d4a1044401d10300d41084035031000c030041900141800c98944000c040c0d0741d00c810203200e5441c102246000c08401280b614424045400c00910810190080c261003000c11242040c0019015011800c08680309586541580480c1d41c0b103110000480c0b900b00591903104d090a1400c0d080041009841c00c3c00550404c4d80052103000c0c0079403403096803202502c007594540b5840c0c02980c0e48000c8d1280035050088204402c3e64042c000e2287e54004c1501000a8900c00e00740f160044c2a66148540c2c1d60305607005800510080401208594001d58400d80841da200e00c03c8643e4500310001c0340300a42241c1ca40728800307100c00d400c6180c0512942c103840518070040c40840b000c0e40071481d150041c0c0481030305118180003450041940c15000204d00000d1030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 101267742 1250 101266492 101266507
    0x3110c030403121b020901090f0f022110120f03090e13020f010504050a0b09032406030c12060403030b040f0e070f080a03020d120f0903020c0f1002031e 67
    0x3031465025034811903503600c0f540301402240d5804001c40090f2001d07000701031001092a00096001403040c050a980e05584003105d8003010320315031112140221110056441b08100303801320168a8035405800c20791100080003035014640d440f030f85019141105107d20241410381c0b6101110704c47d00804030140400080c1c046505c880380e58000348960360000c1e020f03d400b0840e10501c24800e5001c5c40c00c905000007880244410380c0d420540b4400e4440c131690701500d074003001303000924180c00f41114a0358107501e41100e0298881c1107000354131034001503040310300c842c0d03446040c010140d49042d640742503904010b011a00007403094110786190320000300f01140d00010031000500f29a500120250a07a0048070208407011242c11408020000799028080034503c42c2c402940380c5602625040c00c0240b002261340480300d1a51140c8100844803604200034150f51502942d81c0d80000501482045168030001e92444c091034400300c5922550b01030360900c402507481d034001400c60384600685039000d12000b07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 101268992 1250 101267742 101267767
    0x60904050f040c0b0307020d0c02031507020610050d0c090903120513030206150a0312110703121b0507050f010c06090308160801050f0105070201052107090e04050601060311 76
    0x201d02601e1404110391141c10503160503078002c81c40360f018088101003481040180d50300440c41c036030440304500701034140c1c008074070000e41484c0c00d141d001c814204824042c458039a81c0060701d944606140002014669140c00421216042c0080c0082440c03c44582c144104110783c1c200c640f10354030038209810b0207801c816201d030a440c012907818100c400802410014143d041284503041190310070203803010040000843d0880f106408050b04d0080c0c0f00303d1049a807407007007048901c0c507010030781a0ba901c130341c036032602c07000c2c4000003000ca00025803462440f0810a110ba00f26501495218009040c1c0c0c9242c94203002c121555402d01a0602100b07006050105481d4012030740306611a9507008218a0b00c000301e5641042d03121005010085020010700058807900c4441c1001d00d002d080c01da89030609403004a9440c811101001801d804007100c43d101140306400b40790107414103807601441507031192034019046c001110040e0140c0c0c82140108000c50190b030001c0368440c10452514a04200500351 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 101270242 1250 101268992 101269001
    0x1005180a06120c05040f050f06070f0308013b060d0f050606100c05030d0b061b070f0801090302030f0304081306050306090a05040f020111032704050a0209010914060904 74
    0x118002c10415420004116854442d030700b503000d1103040080c282410944009050a110f0080710301030009240990002d6a84106541119502c02440d140c1c103c00703440c00500d42c0300c0078801e014060314040c0541e12001120140106484c0c074580c0c01459800b0031045000c44100040d0256400124104c82d560200d000c49903186c07800d0740660000e0271242001400c0c000c3d0015040c0a00040104840ba030500007400802118411442c20307401151032040400060a5441524114513131169109400d040c00c810210b0034500320388102c1c0f07254a00e03640d10480c0901b60384030b003c0f0080068008200881c07a00b81140040c5821600901001c0e00341101d2100a081074100c03508004080341c80802000f196281012035076a112080082c01e002a041541d1110a42680040002e0620903a079410000040e01003054070402484110007440c402c0205d004200e000c44841d6519005509202c0003920140c014022160710500c180c0d00c0ea07001c9442e003941c0c0685100d07807180d200e611900801071050305a42d036018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 101271492 1250 101270242 101270249
    0xd0902120d050711060301080a170f030423030313020108040c0f0b040f0f03110103090f0b0705040e0f01080c0105030406090b070e040b010c02030705040f020415110613021005180a 79
    0x5402da510766840c206021111034401c0c05610685c1c1c1040144400344001c075a0142041d40040e0741d92203003c0a51030b0038128000d28172003068503500401044140721070001783e0007101d000c110710800071203650350440c5c4d100e110889003001c5aa800560040041d4401c520443d4014004e41881c6150f98541140c465098080d81c02110031a002007010700c000c500d1040c1450040080e801264800e030720359074403403503d00030400b107007818180e4904070703001032245020122000c10f0344400104003d150648010700030b0f0301300c0e028814403403080000140030400c450000605841c4280001c0c0100300c2903400446040e032000704122086a121540100003844001d00c0300d00850745070721030000b241e082c1d100f800b007210800107400b4100003142d00b8000141c1c401050401c29074105842c04108480c03600c460130042e21031a4481c666a1010a00c003005007a8800d01d00e90f902c40d002d0069030025115200300c2541c0082d0b000010394031801c0340e5100c400c1c083c000c41c0204040e500541144154111100008045101560 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 101272742 1250 101271492 101271497
    0x50414010f0b07120f03020c0f030307021b1305040f050105040515060429060909090a1a010b03070e2107050310150b090d020907090509060a0503030d0902120d 70
    0x500500030307910255103501c0584034018a5500f0031007280c40d01c4006600521a1034140042d440038154003c0c03084d0111016512204102d9940841103584c0d613680798022140f18005000e00740c05415601107071002c0008044004101e0204d0340c8103042280010100580b04440c007550300f406000000702d0a0080c144214000d4010301444c855140a09100c0b4000400300c0f0300c42c610b400000c1d20185280020540c45006509003411011508804540030b440f81e0344402d94084500c00401901a500081100580748548882c60070340c8240c100a08011000703019000400c5010300000780c1c1b042c400c4540b80f03140b680c0180200c422681d10b02c0304d01d46409246480720802e030800701080c005403d0403c8000340c42e0500e11000c00c02001c00316401c4680d81400d0040f000c0060780050070048075501c0b40920005a0f400038041a82d90030007c01c00b0300140c03ca4402d060048044200042035460b050f03c07001c0446130054042e500d4031281c8070a0030020109400200e078803e41d5201c3e07981000c00f0400c0003451204158 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 101273992 1250 101272742 101272781
    0x2030a05190507330506030607031a03030c010203060f04111206010c1a06040c050c070e040c081e010c0c0c03081c0c0302092e0f17070504210206030c0f040504 70
    0x452540114150713040d000c480d500742024840181c0340000c01c198001507924001400c0c08050340d00ca401c21340380c1d41640c1e80c5803001190402701c2d01c0040d80110700400c000c45003000703e80301b068140815940020000d40d00e0800610a0460002c81026059400b910500d0041070b50030b841d036203010300c01180c2c0800348110110301003003040070b082034412900010010309003141007480da42192966a042c0c0c0c0640305007070f43d051010404208254840c2070280c00c016040c0e0340526070070658103440280c0740d180401990300b80400504400d001d1140c8411030358000c08400d150a00b0b6844010181d8840000300c1c0e40c10f01c041c02d058500c014544a202000486942e02583d141014403c05c240c842606164500250010100c1c801c2040000550710220291b810314030030200d0641000d40340c201c502a0b20202d10414981000724050f80b0200a005607210039202400c01c11b00f4030203440d940f06900300001c0d04900200701192003040c04002800551044032441d40c42c01c0c0e11a808101601c44a1494040c040350b00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 101275242 1250 101273992 101274053
    0x31107080313052d0f0103150e1e150103020a020307020d0b061912110604030f0b040c090e0703020103020f04030f0b01080616050a080604230708060102030a05190507 73
    0x2d403e00e840c00680b00e44d051690300c440d842000051348200342455200c0d41500003031a41301e902a80102c696440780f0940d005102e40e032082c035030345050001c03030b01c880c81c544241d100c044900d44d080351042c1c05400c2ea500600c9021011600540087d400f01c41a48250b00c01442007a0050781d54101e4061710901c40c500000d1706050010a10800ca1009070f00a141078241900c107101800940e00d04110803500042c00501c100246000f0800d94071454001801c02071903902048140204064040e00640c400c08480741c21740e0b51020300300c04035140c113007001429401c180000c1000d5846900a0940c802204507643d10b4541e49540341c8580140401d03040716011300313180042200d07420522000307600c0340e03211000010110003004018018810819039800344805c04010070180c0e15282e0100c0c01c0484091a9a10400568440d03808841c00403149030340080c01c07200c0041d00f6035102100b940d8003600d1a0712400e00304500030304a0400d000c00ca1030b0032410810180500c1d00428411940035003940c50302260642d10254 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 101276492 1250 101275242 101275249
    0x60612080d0504140f15130f020f01050906040e060108070c030e0f01020f0f0f0c0603060a0611030702040903020102190905030d0c05010f090c090c0306050607060513050303090d03060503120703110708031305 91
    0x700a00030741f43c40b00300082c1342020400d40c840000e801c1d0340c111003c01d0003606410042c0c68a002c2d400c29107030444400f050100700401c40209640c0181e0007601e640180d0ba903400000c68810019580060000300342d20300c681540d003403891650751a40c1c01401541c00200e100c0c104103103000d503600c1180c84180c0c070a80402e1030309401800901888c2d10140c1e034151035031070304e107022030203005051080c1005c10008070340c29501d080d018415a201030b0350040c01803101d0803950500a010b9000503581001d51059104440d0707107240144110341c01c031000130703002c2d0030320052041050f503140500d608280c6465407901d401f5690802c045c0700e0260304600c10340300800c540342441040c1c0d08894441d5850800d01d0314045040c0043d0b42d41c4170598072410ba001101091310741e01c05160024903641244001e02d070380b0001c02841400c03000401e058209102d59641084616503034402c055a07001d203540b02c1091031104200c80703070120b48a2800d008942d600b102c00c4036560b1780d9440290f46540d2081e0203413814000c00f0f4509000d50f29 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 101277742 1250 101276492 101276533
    0x3081504051018020a02030322050111041806140d030306030c03052401060e0607020409020a030303020405130513030516150515061c0f06050607060207060612080d0504140f 76
    0x5803242c10441c100b084a40c8082d580b8440601071844030203002036849c4c1d031b0360641d140d40400f10f03510a00a01c000e501044092031190000c0c000c0a034000061100c41951601034401c050032201001d4a06003202e141c5c500f0311000c01e0910005608058840d41c003c00807502000303030440118480c0c0e005000710600c458520b5581003401c002440c40c600e10300010000d00d40c3c045c84801c5034040855400d50340780d680b84002030007005406402500b00103005000010301d6010350203401100c500b170b0392554011072949840411200c2c00c48040d1252150440c2242c08244600301408180304d009000f0200980203888100355001d12500b50800305840304104403030800410600000301c201030354520304104100100304100d140c40c2c0883d20106544074881884a580754202400401c0003406099031071100f4181400607502070542aa401400c5c40740002c0c40114560803960442d0304940818242890710b202a001b030100070b00181d4840c21a04c044c003240410500560b2000010394008140700798018a9040380c50b03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 101278992 1250 101277742 101277779
    0x8070503010506090906040803070329040b0102010207080417030903070b07020f01260a021b0705090c16080a21090302010c020d09061404080f0a05010b0f0607030815040510 76
    0x40c4070341340a0001c0b84200003072a542255000d91425260741e41d10300214014070360070b04140d408081c0e5005103001010a18030031400709100796414800c46070710310b00584c20303803003001c07002002c840701000304101c107408800440840380e1a000c16a8501004c040000b0f162180d035420080b0ba102000070080214500a00c0080d110391003800d003440745a001043c04503810a0410815108602c20070004807449032316411110500849400f5120180404820543d5111035006031401130b074024010a800050741c1007903441c0340c00d903410440e003006c005030351702e0055030044502c031828420009980141c040941540215580b17004400041c0c01c48541402800c0d074a02c1c0071440190b4102555400c00154407540000a0750b88a050000034207800c0e507429400d0b40714591002c1100c0c0210003115500b800d000ca03507824106e010318000e00a183d000401c000410580c0a0403c1c1c0c0180704010f003c0000c2e00444a240c3e011000007031501304c040c6064045025500c0407a40c07140c02000030081440704011074a49403502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 101280242 1250 101278992 101278999
    0x3070306091a010503090c09010602030703030f06052206181a040606200a0803010801020c0d020601080d0f0224180610030609080415050904050c130902090406080708070503010506 79
    0x81180a0b182484920350300c2c070300746041103c00000602101ca0800540d4a560000342030110b16603035034640252681c200d080e0403400030341024010309140c3c0040c003444d41920b4000b04000300b44940e50088800f00703280505d805401c50340707421001402c214101c112104940d03501e1008210714183e0a507040b1032000060106100f289401003e2000c194070140c2800c4070a12103180114100380000810310b00081e082000b80081030010003c12025810b401806821410794115070035000003580598440d1801d0050499a92041e0110b015040c815040c6100c1c40e1060300550f004290141070321000290603651850075200140c007800401d078107440440c25900181405001c0a0811700c84044503000c1c20701c4060080e03606d07550030009000c0c44400701e80c000d00d0481007440292003000030151080d089084240d1041e443d00c1c0015545402c0c8404550320021030a001520580c10012114001d401810f50719400503628800400c07061070410020020b030000b200148400c6161408041c01d50300000d0501f0302 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 101281492 1250 101280242 101280251
    0x405041502160f05010b011b030210020a14070f02010f020c01120207020a0b0c010501051801030b1810110909070309050303130201141b070803030c1c090503030c0307030609 76
    0x300341a44000010903082a80260703840c6400904603a51285908016000c1481c000c201420484150f02c443d42001c001c1c0c8641c3c00749140ca8082c3d580c00c400300315000e00560820314a2501551550340209103200c2c15041407580d90712100c1210050fa00700003001c56040d206000d008041d0342c0c1054a14100745441d10003001c4104004c3c000030840360000240c01d048a0f00400c5403400c6540d6075400300c014002d054159522540b40c402e07118040d040a101d03a50007250102840303903024200d242c1e154141d03500320311060740640310010380004081441c030300d12003035005000b6004d2205240e8011174104100200c24031346c445c52304104000f080703d4040d01b110141850104007800081d000b00540b43d2207107081621800307000880c00160f8061206070500d488040001500b050061210b01c0e9076003558420404039111203499400369590303807109807140500e0701024043c04095800c0d01d031512102c52000320021500c90711513550b4600d5a041a070340d8040000c00481005a401c0c4c0c1031044c1401851041c50030300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 101282742 1250 101281492 101281501
    0x180507090c0903030c020d240c020c18060109051903050115030c0506070c0e04061b0807080a110705070f1a0a0912030318050708010b040e070b0a020a0b090a030e0405 73
    0x82c07540030148401014040c2c80380707091042d55545100d03507081c1904a414040030074a07440c0080000d0310301c82030060034640752258520549100052030410400301401412414a1240311007281020040c1a0f0341084510300022400d602d550100e010003080d020000d0280500314a811070079180d5100401d2411034041c201040403800542c00c8800700c0c0d134182c50f59503032420541024008030050760062041c119a0505000800c00254006052000c8007280140d074184241c03c121011502a1020800110fa02c4040307000744409500900c0d0401211034071625250455440d00d040a500340d104524078000d1240405c600c41c0c2c0c0038684010000c0b48002540381491010001e001f140c01806400b2102c041c4000c407030101800b0340c1c890700042d000511510300402940c03030174607a590030f50b00035400c00794200312170b4a0f0603003003500404500305080c41c00b6211550508185402c0c0c1c1e0000801d1b4001c61240704002004140c28488142c020220500070f403410440f94140540800703c0b0865481c040d514041c01c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 101283992 1250 101282742 101282747
    0x12060711060f0f100b07050c0109120c090e0a140c0103060f180b04090204020d0b0a0b181002030f030702010c080606040e0604050a06091e05100302030d08040302010609180507090c 79
    0x301d900400d10603c001480d1513070200241c000403660014040f01000080c010140103000030301c21010308099807425505a1903005c000c4c40580c0845000b00703000d24591040c0958103040d0084998100c51004403410005ca13525120a12213004088400a400850085229507403600a442c00307031508440c0200d5251401000b904540784000c3e1546101d550b840b003130101a0703603d400c40e00c0d00c0b0360010015521100c2c0c0b803400308010031080c28440c0c4900040403002442e05601820b4801d0020030100c0da5112030200020301203819403804001086010800c40385200b0b0503da070141d40109c1459000140e103a03079001015080480140c8540c1c8940c905000c01c0100c151003050003030344514286d40101d881e4031588042e1029000742c4c1c100028190034028510390800a20302c0c01111203804100510003a11030a600460084181c040690150032080c032070402d080c0941c0701540c02078442d1000184e203540d00c0c0010403c071081d1141d41c00d001415001e8800c02c0c4001040381401270305c0f04510402030194038071400b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 101285242 1250 101283992 101284021
    0x6060503040b15030a0209010b0d0c0207060219171c0501051e1002100e010c020705041506080c090405011410080106021e0304030b0a05010510020f0c06090f1206071106 74
    0x381c000b080201c03903915076130b1014884081140d40c00b078400529943c407580c0200150b000b2942c03441c040781c9000360681c280761000076080708480840c1c0103010304007400c40c092010031450305c4082c1d5444810780701f0b05420038082c0d001866000c2c5040e0320380003000f205546003026544103074801849425180c0780455107403402c650b444c9000c0070444aa8401000d91b06060342000e12003082e0910142c513003640290078110640104081d0b030615030907942e529880f14104001c490401c040d08811a0034124141301045c068a0341940040c04400082d04110702800050309483c030036080b4891004400205d5102824445042e1400d8003180c14465843e606200300256a06944046605103500c090b00428800009000310340103590040d4080c5410314004c039031140580421300c18180241c20120300c50102902c0071030f100c0b406003d58006080c0000401080100c2c035044000225071203205450894a180d07a010403e0718200c00c0d0402410262921500103000c11201c1403d803022604200300300b0602c0b0b0743c0300c82ca = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 101286492 1250 101285242 101285251
    0x70203180f01020a14010e121908180d020a0308011410030f020702040204030c0602070b031b0901121e050c25080c0708061b040b07170d060905090106060503040b 71
    0x1200e2a03410114070040749410120320380901490250703a2403109141040d000b18a00c40c2108048810301e610326010000c00d0f2240780114907551848a00c03d100440c0705440c1b040c4c12851442105424041d5018220704010050700300c140580d1220071844201900311082500408070040341502106041020034100d1000c3c410f2013003010390301c11004941e139211382c1c1030714206900900700715111520391510400c180f800c0c1c000e58025120350038001404090403070441e44a003089001051070a110720810000c80d8100a005a0505c1500c514540c0324400610952501064504206822541c009107002c200c0c0e00c064030800001c2801c222507007030b0b4880700c408100c02000b11840d82108030100e040148880c001c11040c100c440c0290341d00001c1c4000c00052890050b5400c00014032910000e504031503803807045200d0040440300034060900814031646c00381ea80c500407000410301d884007030b007000c004440703a83d0031591000ba034590500280c40802d00c103e9015254500f0101e02c0c504240e10380c0b1003070907401403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 101287742 1250 101286492 101286499
    0x150501081e190203210d11090607060519140a06090606020c0d060902030a08120609061507060609110d180302060402060c0c06030f09100c1e050f070804080607020318 73
    0x40c61046450403c0220361350b42614000280058124400f43e05c1903215001071940b860600c6021441d4000f040100e5080300f00c0148143c1c500845075880b5400752800a18010080c0fa210701254041074150051b4002c0040840c00f02c510fa1a00d104038800b29181504200ea9691910314140180c98000480000e8000c00f01d03500707e824403107498030380050300050b00000c3d0140245498401088802c0000d0700c8140003442c000c5030701da40c4040600215820449075558011400b5042a554603141001010000d019031001f248144c2c4031035800381941d042011001c80b03400d001498420400a03072051427000001154140701e070640f582c50095440c5030280c0064803806000404005145003045594400c041c060866600c82c9442c2c030110411910484000625020701c1c4d1004034008040c1c0300c3c80c0030b0040e1588500c10800c0d2031100101c000d034503c00c010410b0000c10444414540080c1e409404500d1243c00560303500c0d810441030340d0900002511a8040d9442841445000d1000400100c00c2e00400e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 101288992 1250 101287742 101287783
    0x1031b0909180f0501050919050606060c0f070609080f120901030510031b03030813020a090c110114070f09060527090403080402030c010903031d030a150501081e 71
    0x240441542011104001048446800301d0f8104114040d04864880d400400c182c2e070346250000a0016021007080b4018440d401400c000b416600d4044040c05407040d41d04112610400400c08140c5007203260781201001c28103145c420090182c041204082010304113000e48035048007602490b002d8000c0800d179506041c2c4500003d504126599214401140c1080d00c0c1a2240c200e01c040d14500c547c0d50200750002f600e08800100f20340d0761420525202e0703a0180199000e6441d00c100b210080000d1242141082500d5101d82c4255409010381003800d004400c2d2082142000c404c0a4003c03002100c4204c24840300318010441660030070144c1d0400e1a100041c800c1144250344003071040b2285071616503004440100340014141d2108100744191300c2a01110701c0180e4103c01500c6216062000400085010b0707111805005203034085032800c40301804036514a0844d03502d2410380b0b582d060039200940c2d82c3d44010484094208515004042d80101011600c1e10050a181d1940710940f41051250ba16 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 101290242 1250 101288992 101289011
    0x10804020d020d120503010905010f18090201050c0d0207140406050306010b070303060b03070305190509070b1c05040f06060e06060f0307140415260f0c160303090201031b0909 77
    0x144802600c1c8141d02c0499203848001603130001d42290021f0261041461601001007001d05545072a50305440380c1d056448440c244c00c8510402610240340c0c00c904110052181c0f03c102d800070003000b5903c1d00d0300e4000d44070040c1400e03c0d012385540213241c1c540c81141032800c01c00c105c3e18023249050541d40c104040b940e6032200c1d41019800703840320340e02207a41c420002040043d03059243d40801e0284c80030201c000400080f500721107066800c2034514940c6500070302c008201c010303902c400030a01e030b54200f0a070300c0601c148000070b9022140103c1d8141c03280312040080004104032482440080e110740c4c0e4540c82030b400c00e1700104440e402000c4800054003400404506894010f113401402e040100d161b1f2996180c480d48d112020340b4141841d07038003061410041018101c481c00300600c120354201e1b45100a41d6588110a071310090141c841200650104919115603000040c2c150006010740c07000309000f04144001021100c61100345103500ca500c0710103101a990158500044032150000819040b00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 101291492 1250 101290242 101290249
    0x405030c10050105010f08040803012d1401180b0d0f0b100e03010c021f1509050c090f040c020c09090124030c050603010b0904021c2a02010b010804020d02 68
    0x14a0010000a01c16110807071104007241d005079050303503820f90300d584c0ca50318440b8003665554030a03900244100b8044c0f0041c0300700c00c0d204100381c41c0c0240061071640c600c0c13020740300050200341a401c00660f8221540941009580211034580d0411090500801e0300b40382642544440c0609051200c2140c5c4900410740217040e42e0300701c40c1c4034205c02002c000c1052401c3c440640022a0010034602950070148500c01043c00803078400c1e180c2000b41c2c200001c07141064030860090082844181c4180000c540108402c859882005e114946412a59545d41004410441180d0000b480c0742e10907400c0c00d1880311034a81c04514149995010750302b20380c8546484c0203480c0036110f404079546443e03007503000300d258078285041c40d40200c1c0d01943d800c01242d80c980d42030012134842409441c412031400c0144141d80d0801c1c2d802081341c41c042d01c550140e484040343c1600242e460800c00d0109605900341c13078064400000c81100d07417060710350000304100d950940020b000c1a5000b00046d2003402c0c1900c1c2d0905649 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 101292742 1250 101291492 101291497
    0xc0312140a1e020a14030c0408150106122304020303040503010f020306040506030d0516060609050106020109020a0f05010903080c0f0105090a03080f04020109090b040e03040b0d0f05041a040503 85
    0x44400310840d0862038048414401444100120b021254011809514a40b068421070305054041c2e036807030740e0440403102039080950000c3c0c42100c2e0200100301c005500f96051003a140024195a030340c0201c1d5240c164000c0000310104007900b0020f2a0803080b040b42029040840088604030341c07100ea41d9079450001034118002c680c09a07401d035082000300d0098013401d0303000390710426045a00700101d45401d410f040c5d03a40410320780000428030821a00450010039072500708203e109030004101c1940300c200000c180d507420307400340001d071f03448445c10b404501d40b0b119818007616101500904842c5410700007082c4c5401480042d25080d8001030460b10b4a8003400030800c1421f0340c0e00203003d02d042110907641e98456810342540020308050106022002082519014a40581d0303a25002d90034501200c0003020f2000203581d00681e40c040c0c0300c418034410701c00790000b003007035054181c4c1703d1200002c50030503904c8a14075200441c2c07400d03080000250b003a000701500c80107441c07010102561203190070b51852 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 101293992 1250 101292742 101292761
    0x330f0301060e0106020a0303150602030301050d050a1a070818070504150e0c1b060603100c030e1f06060219030c0507030f0b0106030b030a02030706110c0d0b061507030c0312 76
    0x402c801c1c0010031450b800080c1c450141d440390b5010442c040f840c9500c9454500207020304401038000300300402962030980010608180035205851409846a86102044005e404554201c802d52402c112010360031140d4182e01c20740d00c46003644919000e0132001c0d10768009010f5584150b030341b83d80b000c0300340703190514070405400380b1a29000b80d070030300c9603070220707a50005510607100003402a5020b03191400410807034000d500103001080550310100141c006000b80130510003c02d41d680f07060b01860041040b4226a614030324551607814400e00700200e095400a800803020b641c07141d012a100041078000200d4041c0d0185403540d4003078213034600030f030030070380c4a50010b03007101144500401801030384442141203440f16102007080c852400b0030b06841c1c040c1c009000e9850341000030f0400c051401804010b4402e480318080d03c20450001000644078064924142d952081130402c200550038010380310510b0024000030241003c05541e0000e11141e6038400090410140319101c0d6111282c54018040d007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 101295242 1250 101293992 101294009
    0x20708060a1a061611040207051b03160302090f22050102090a06141207050c0d030615023d0c0f1202090310050405030d060e330f030106 60
    0x1509003034400202801040018603024045101d0745460b601e0107504803049000d1000440407643c82940f160100711001c07002c2a504245c080110000182d82481b40191814440000ca1881007000c03042c945040c1907982540d11041c0c1410303080c00943e0765002c0c1c0c00da214284428140301603a4085901d141c24100c05241ca00b0070100c6081281007020640183c200c0000980e00200344903591082100e2540e800c1d40e84201058041040d00c2d5807a21030075400c0c0e88110742d82025841d003800c02c01c0403882c0c5518041002f0010303a48036000d101c0506565945c0310314003c20710041014520000320082031500305441040d260100385144401448146012041003501071001c0081203582c810141021080002c03400024400d02045a8811920302c2640e15500c0b02900400441081c0301c3c90740c005247c090001c0d162880103000520103410030b23002b0741d0064606d02d0500a01403e0814981301700300d520f4082150044c40101110200000c0c00280783da010300700300c50b508041150003000c680102020380101c5203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 101296492 1250 101295242 101295253
    0x16060b040f090f031115010501231c0501121205130302030a200411041406090d061e020306010e0103051302090403020f0c0f090f0718030f0b0a0509060115020708 71
    0x5210300031083d800201e01940b6440c06055510b0740d802e031500c0141c1d28203684048070340014000c035403145c0061080202d50303c006c034815658100b00c40041da0488240c030340108100e82030504200e1a1030040e51700608a040c8518944000c40d0368203c0c40401500e904410080c0205490039004800c1d05504d00450300541070b0f45651015041c80d50150416182040606e28100c444c1d04950a04d031192440740004001501d04241c1080120013149840b10b02044d4010000d21400a581c0d40d4a1031043c601803084000188034859060180b601200140010240b50700c14810422180d030005000c40580d1424030340001e140ea03030340341c1c10038844605040c0a90018080c80c00c22041580001f08100500381e20012900c016404008008504139041285508a040000440c0352203101c006002d400800700e0811042e240d03102080410014007550099964000b01c4141c0801d128011203601c4c5c020b0f449210070720a900d4003001c40d039034450040c4550400c41003106c0d04064054405c3c4048005444071074251362 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 101297742 1250 101296492 101296511
    0x9070b0309010c08071106010501030f0e011506020d0f0e19090c08060406080c130c03090807030c0209010504111204020316080703050705030f0613060f06120b09010216060b040f 78
    0x900801030f1802210110301ea00700400d4005001d81c0603002c210017094001d119682c20103004401506041c0c45540b49113454610200c400751080c000d42a12042c0c0c1c00d008004035151440081c50411681c4c010404e0040d110300d001c1209600c080e42c000c1054040d6030705503000d8030308580103045c1000795000d0707140c6524040c0c25201c0c0366440304149005510031070f002e001c180d07202c440507600c0710100440d0a501c007845041c2c400058a46403c05401110706041c001008041600e6070011680050030440001707030b03070f0a440c4085140250030503015180580b03007040b171540e40300560b407010b105408150016240d1400064219502080450001911295001c2101340d803001c0c690f59810050004891600803020013103400d04000805e0b01e0b000c0e400300010642c075151400002510710080300309907403541c1c561030710344861041805410000c00b42000250b100d03a207581400b982c45100500240c20503401041a03041c00d803ea03042c200320054001d6000140c81c034103100043d005020a4421801c0356041442c0103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 101298992 1250 101297742 101297761
    0x703020a050706110715050c07020909010605060a05031b1303020906190914010b09060712020c0a26010603020303030a0b06070b010e011e150c0807170901120212070809070b03 77
    0xb080c01c14070812408004100b0200148187c0b00125a0b2518001e810300c031120140c500b48840342c2e00701c9a043c000003489501c440209000b0b80c8140724010204130004244840c01c00e4003820352450170380c0a14010b003061108910140c03084028407000e880f0b2118007022400e940c0c1d03882c0c0091034001c0051083c1c81c4148e03a5540901c060030f00c200803410114901c100014810301550204c603134150004000c03074079000c580d680b214814241850700800310300c95005203100580700e40030500c3c041c2243c0740e034030103007541895840459083e820b448603100741d04004080005071000000c0c1e940010107010003041c26030f52400801c0150040c0780d0081d08141e48440000740340301903200313114107031144003044074520b00283c40404107000140c07148014800c80c3d99010055948a100c02c0d400e0544980c031828908101c136110800c110160b0020220070b00380c0011828140e603044180a031034550013080c1903007081400030302910b20381703001020081400300900c0000c4103850144001c1c8083e02c6e404001985901717206850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 101300242 1250 101298992 101298997
    0x5030606030c0c010f06090b01030605130914101a10080705030a2304020a0b1204020d02060c1605010e0d03021c0e090f040b06150d0e030910050706051008060703020a05070611 77
    0x7d142c034091800d41c4408282d4401c0c001c101c180d40010740f04001c221303103461000f4002c00c2968000e0b24200c6404212510f903400601400c40d681614880c0403600c0200851a0280d4198924003244078003c10040e0280c0310750003544c0c1c2e0b82e1001c281d0400c10f40b03c0d528184154045c0010400427403c80006584051130160b44400c02c500941c02030307030001100d40d140e0f00300100780e1080506545038012000002801881c0400140c403400b4405841e131800c0c80c011211481c981402441d00c1040c0d0340c154482030145581c44215040040412a202c030011042c1da10081d48881c3c003003544403a4103e42c01c10300c10256001d49441c00102c00040d116510a00d400e42c07245031040c0080d501101c0c0504000c010444500c3c10150342e14803488030040c903510700f0020144600080002c90482d680350b001c10b000407141380c0c2e030320890010419407648902da0f81d44554038181040700c2c3c000f41b6514031720746001404d02c03120000140165101603a8200181c2d01c1c1e10b60790007515035000300980105136a003803042d034000c52001c1001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 101301492 1250 101300242 101300249
    0xf090f0f0806010605161202030702060403081809060d06110c0d120507020a0305030a05100503100209030f2d03040e0a0902130e21070803070206040309060f05030606030c0c010f06 79
    0x2074660b240d0329010111040d100d0b0a0301c0d101c01514a240300d001041007085940d40000c42801200c1c5001d80d00e90215401340c025034030603101039801180010340315240aa03075034448142114035022514080001070043e41c0047c0014101c05e58440e2000313030000c0010100d8503010512000c88000710824100100102021020b000c040b5041c40c000c07510544c0001440180b4a505440d000d095581d41a591030007010001e120010542a14500082646080c070040a03000146c400c05030f9160441d070240745c035017800c24114001c107522211048030450980324038065050100c0503006400030386800c5040c07860055801c41200b00081000b03210410b1031981c450600644240c400c40d001070a4100048100c8928541c6510142c1150b2407040c0ea844580b110075207504111200607051480580780d0344c1c5560021208040568442d200740001d05030040740000040506140040c1610800d40004000b8007000d010103001d05000700c0401c80e81d4a94500340d501d8900303840000c1003401c560107011006400b2621 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 101302742 1250 101301492 101301509
    0x30c07051002030c0c12040b030106050d020d06030b0603160b07110607060204140f060307090b0a0c081c050c0c1b0a030b16030c1d0d0201030e030307080405120711010f090f0f 77
    0x10032081307140d0364009403008c40d440c280000e4256840e0980c20390381039012140014400f43d003007100074024507240c03040d04095030040600d0051450aa02454a04000c210700d0142c070340700b0084100100d00c0c80c2401c035464264002c00c206c07104190341000c039070907004000d4000d0007140085404100c00c0c010302601e07980450100da490101750990400d110403848141c03044070000b580110107004030b00b00c100050140311101c1c0f410540150361900c41e1101c0d44c2190100d010800a508040c641c6003029001d415040707294441d44a191070180683c656403014001e448925450110144840680c6c400040000864005801019034035020b40c03290008103c950385100442d143c500610306442c400d503c107032980b103101d13811a1200d603480810800d00c08020710080b810076440310242e2400382c02c1803000e0b500424941e200e994241c14030b840d04d00d00300070a480090201d1403050281102007070184034110350801003820b095681c3e07400c0c81e2003100c4802c12500440503140e4281c3d0001118a8a2409082120400f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 101303992 1250 101302742 101302753
    0x1a0601090b0a0509010f0909020d02030105030607020c010906030506061308010903020f0303130209130c0b07031e090902072303090405010e0408040510050d0c0c0605070206010b030c07051002030c0c 87
    0x3034101c10490b000309964103000800c240003000f00d65005c0d0901d184440c0003130400d450a166120030720b00603640309042c85090250007000421071403c0070840c0f2604508180003034480748001800091139a0810302c41e0f0310405d612907003c03400e280c44110444e501080311016015045460702221800b81c2080141207006204d0103561444100d40841a03c1c007400d602d10030b480c2001607940030445081c50180c04809000364407074440c00080d220421600041c071044039441d444503803606024208800c10342d240030158007140901243d1651021070714040d100d5441006031074040505040f013500d58000345840c43c5400c80d003081c440c00080000030300142e520441d828841681c803a19042d040d032005540080003c04148028071071860090300d0b00c4801900c1c1d00c1d049040c03254108902054808007405200421204c40d00d8009004440c06921381c498002e00003010554981a015101440000c241041549011400008200d400d001f07011020000c2a8107540340e060405081101da48105010340551049 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 101305242 1250 101303992 101303999
    0x80a0309020402132d0501050c0f062d09030a0804080705010905031b19021210110a0f03050601120f181a010812030f040215160b070207051f0302071a060109 69
    0xc0c000813901d40c10385607004529281c90000159081c0e0010b0504001c513004910022032b80d00340c00c100b01da20607030051b012480d1601c001e00700c0010f200d01c205058604541814208089444008200c55a18a440c5854002541d640c00c00b0586400303400d03001061542404258400d104000001c2c02e0300294064030a001701140f8210300d5074030700d000f4501c507518469202011015141080303015507605481d03426922500050507011048600c10001e030440301341c001c6000301c4850b501502800e044502c40c2810429800d14a0010b891144800b5981c0c500c561a249281c100302c04c01d400042c3c403e083c8042280d000b03d040d10b008640c1e00c1c0c140407d0710b650740b941d034000145080c000411081d81030751100d0b0545141c179081040084a10010001e0741c02c00c0c03100407a4805400480c00038200300f040070000e015096010b00c1c14089000d80035184004643c0b01520031303c41903980a220401890805100141c8040740400039000fa000707081015022620000080c000000740300c4049100707017002d0361140402e540303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 101306492 1250 101305242 101305289
    0x30605031002040f1e030c09060e15031f06150903050c030601061704020303070b07080411011d0118090e0f1006031707030903051906050603120304080a030902040213 73
    0x324444d1501d00044d45404000219003c4414004080084068001552245c03212036a40200da030118001c581d41c5d4034100310078441c801145410018001d80440c1141d500c0e00001c0ea28a445542402d0303045c907036541c1c0c6c0e041600c0e80d40090000c000200488400195000000d0004c0f22144002ea400c1d008101c0c24284034580401c400e41a01c000b40c5a424080140712885001840000c5c001c907050300c0108410804104d00c0e0a2440c0304100c07a95540c0700c246414542a110034444400150520a03084085000318034541903508143d1030a03e040140c40d0100c011310040400d07690b200c0032500c1d25120394204c140c0f801207140c40c1600740020440b5141c01a13001c04100300c5020380b001505d00d45d804c007510704885210500901c9030381e001c0c0c40c0002c400f6440c5e40b16681400c0205000184c011915030010b401c111260003081c1d4401404c84c017915903030300007250485180c84004c000030a1000000b0381e549202d03009602c00806260041c0c01191504456030003035180c40b485004083c90444081000c4504c40c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 101307742 1250 101306492 101306497
    0x7060e0f0a08070b0708070c090903030e060402030607120b040c090518060a05060708090306010e060f03030702030a081b030c06011706060f010f020a0213020918040f0b0c0c0d030605031002 83
    0x400c1d802c0200a0300c0e260440c83e5030360340c01c0036900720b941036010404138004c07600c10800030001d031184010014100321203150103011034240d0304841c03515401030300421000d47c0e000700700c9a90000490030070002d0031243d0042d85000780800020a94000e24001d41291000e42c002c1100082c0e5074182c4071071160f0740c850f03044401c07440d90441c0c3c180e62222460b04244140d044c084041c000c0700c3d02c80c10140d414007400400080c101402600841c0401016908101203031800e0880788480c00c9080c0c0240d803034082c441d004a0340350f1801b00d40161040100246090051b264a82000304001442c030669448881100801d0340300c5000303100c1c401d03c4044900048250300004240c543c00381100070031a0b5240310b0107000640c0c8845c2c2c1055502c066008290104c0c015850340040d00c110b0120024005075100054000c0003410342000143c03425000b2040c1c200320000f501000c0749801a900040920700715581d42c2807a040c1c80c0f00740123031400c0a01501a00028070740d0903030442400d944049003a5000140e02d2503030b84040f030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 101308992 1250 101307742 101307749
    0x15040b010801031728020d0e060c1207110a03081305042703050c01090c05040e01050c03150a0314030c01060510020709050a2d0609060b0a03050a0e07060e0f0a 70
    0xf50ba41e0484071302c0050594005003007400100c0141194111075035009510780c100d40701c20b040560450006940129882012802c0b203100440344282060100807403141e50340006807201105010014050041c060509501d0210303510051543c0c1080c0d850f46004601c4d80c11091000060030b40e00303000030541d80307000d02403010b12848803003940c0701c00c00c20228143d103100740d858401d4003484020041411001000e000c0c00100c54002c04039441080c0c80c040910084807622000011a64036000900c862102840c085a410010219400e01c011080600141c8080e60700d0340014004074503101e1114881902001824001852000801200356580144800c000083d1281d000580010001f4080507445a101c540c20044004001945980210a003041c0c95850400b520b0107090030b03034490b00001785a01890303005c0c01c0d0059003440842d2424244022a00645005609042d107441c0010b490000c0c56101240d0071070024202c0c1c480660b282006420511007000580c00794002062102d02c41c1041c80310318088 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 101310242 1250 101308992 101309003
    0x4091a09011a01050a090e090304080624061e04060915210f06180203010f0f05010203090607151104050a05060705030910090b0711090901090b191415040b01080103 72
    0x441c0b940c801121558008080c0300180b0811903000305078500500109031042c4290310056581d03a050062140c500342c00103042e5a417031800e83c00c195071200d960401c851041502907031416103500c0d140043e0703507034042600744a110b44180800c1c0040c40950011100e01242c010848031001c0400c01ca008548560030400304174900890005516603802c49a40558070130300c01d8400000f182c94682c0c0c12110740780290110340c520700c1d0f004801880089259020000245400c0d45418901403030030300080e45900038109071070b2140c400030070102d0602c150030180a01c1062440030401900c1d000103065061078000d4080c903402548000808540703418900100c440c802d81260085052075207031001c00449807410b4121000b0000700503400039815100b00050800d2601c2991103002c9480074034288050790030001d01d403600d01c2c0e0600041c200419a03041d44541c0080c130f9003500900c0c03540890810006000f50040700710a80790203504026000c0701c1200d0005030624100c60a01c80c0551200045546442c2230001900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 101311492 1250 101310242 101310281
    0x51008062b060501030f060606020607090909080906160302012003040f050f030a1d0a0302400509010c0c0b15010c020d030c0512030c090405060f04091a0901 69
    0x14607007200788601c1c220302211080a0072800d0541e40d140290381003030380125055010b00d810710040069502030721001e000780d44000c0c481440c00000003001c00c2154415041201c0d5127070354031414000c000040313803401003001d4152656924017080707411403c2c0550b941580194a4000c100308120143d13400c0d11070040040c102d050540e12261200700015069090495007403003a101d84c00c1c001c01c0c0c2070001d000348041d80c0d243c0d02c0d8044412103d00c00c00241502d45180b00b2510703400184010b135201d100c0e0003a0408400031062681c00e4400400003060301004400030700d030000a140802c46942070700507a2081c00da180081c00030481c0d000050f9a052a050300080400032060f0000d55420501c04d403281c0105d505162490704015240c011401d03615503540141c0c001100c910032441031280801c04030010b1604540746501d1880c05650301031590043c0c03408203101c0c03034803a4007042255680f010024039800c1c0081042040fa19286001c041d02d9608500b00009440144005034507180184500d82c0c505090858505 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 101312742 1250 101311492 101311519
    0x801060b071401140f040605090105070c1203090206030c07060e210d020702041a1f050a03090f0c080d090602010618020d0f0501090203090c030705180c0c010c050405100806 76
    0x6040300d24a2a40782c00c03d650300d004007100c00c011001d59601074014a1401e1041c1d0409007001e0b019504020302e140350580c140410b01c2803d81c1e1003c1803d07080c94004240219079490788004502800041201030b61199000c0b040c041220811802454039600c0f0752800c1018199802c201500ea0311700c03480d007044850942c4030503528110b500c40148070b0040c104100624184603640014100d4040c407910340c110311103c0412200d01c1c2003d0749555000100c50344c28000780a0103400c01400e61080b01001e100b0981c48886940811010f41103040324590300a01ca00b591710740301d040d0342d03907078440307860034100000d40c81000000c0250041c8a40c0c1c0c19980e00940d0781e2a41044450450041d61086052014183e40c072103204241561a101e42d50207420b24800c09641c030b00301000170754605244110000e21035000040c00300000d550ba81e030401400c4240c000020016a21500c40010b20b0040001c140303c1035003010700385031400348e0010040066810840c0d111a000c00d00c100100c46030f100403116143c0044c40d404010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 101313992 1250 101312742 101312753
    0xd020907050f0c010c0c0210030213032409050d080c030c0f250b0f060f060304060e33180607031a03030d1505040c090902070503040f0308030708010801060b07 70
    0x148000050400c0003490090540f60160031900740101100020342c0f0340e0704002c11883c014484a80350726283c6400d504184031051380001c002d00d50f00c00107003201c40032440b2075a040b84c3e564418400c40e100490800241075203050140e100c01c1403c3c030f010006040b510024022220b46011350780124000040107050040500f000712141d80100d4004820b0301044000068040f5011402d11034588a006044c02608240414000080001d40401d1041550040920f02e50b11441d05603544240c10010102d00b004031140c0b540c0c1821035031811050550a42040f840c415400303051541a401c2a41e2403ca0701c9503a444d010541200038001ca4074010381007000400e403010f119401c54040e20008216204865010f0000a1324503402412210302c140d46035044410800006480100140001d840612051242d040002d111880c14003a000354168041007100901408009850142800480810580303849040041c143e4008a4124001400040c0041000b04040c003035075044400c41c510007410b09200c2c1c4d4a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 101315242 1250 101313992 101313997
    0xa030b04060e0127030806060f070305030c070c08030a090e06010f0e1f1205010b0712120204080105010314100c020d0f11010204060905120307030c0f052b0306050d02090705 76
    0x600080d41d210103550804a2140c124859a4620500850b200d840c1d40e00e0003400300d18008147d28452a001e10586140313030183c034204d6140a0345440c10030703074035540c801610801d8011600041c10003000c1020224009030004018800c03800c0c1c94035055070076543d41d0110030780c00000701daa03140010304881050705528002c004007240c803907008280b40c06000c0c00b50020441400b4601d40d610019510000c05101854184180c0340900504940c140c5030107450f8a40d180384000c00d01821003082007480c0c0d0001d04816660682d40500141c0c00240050359580c01c00b80c0c41c00f00401c483c0740341405056a21682c1c00d00030311900b40c40d110103801401803007081c0c01c0c0030341e010107a203100102400074600300303c0c006100a10090001e400142c9520000c40e0400090181c001c000c121961000e500402c0b0110110b500b04003144000d6a10116421040300140b8000c0c0c01c1500c55507032000843c50102560b14004103025440c400e445c20b954080100550740c200f041001c80c10800069000403901c00450403a40c4101700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 101316492 1250 101315242 101315261
    0xa02030c0303130b01090203040c031205120a020307110304030c0b0a02070902070609020109120507050f040b0904050f0d05040b1c020d1a0108060301020406120e071208040504060e01140d0611040e01030b060a030b0406 95
    0x8000d420f018426a401080c0c03b000c032002c2c000d03142c0c00000c01002d16004000704046c282c00c0b8000794105800c6544140d1010300b10700070043c8008000c1005145948200b0801c8080c0c040b8010664450020749850801b03000040c2c8200d022461a000c081440000a1403007003075250400020140c10b8a00390a000c2080c0c0300d03d40003a001500c0710303040001603d960810ba409207102c0c400500091100d41c000c0c90400d00e60203419803c10030100010000143d0580640300c500060300a00c1c050418540e030b041c00242300c1c10145912040c20400190808285410f00e110490402e07211404a0380d15401050300300c4c8240d014001c041215441c00601400b0380c3e900c1410242c00001c100e42c0140d0700c40e9038851003a0f080050444451a00240512017030616005610040c1032040081c080ca5041c100c45211034200d07007200d00d0290300400500028000d05810150101b8400c81c4203540d12900c84180d0900880b09010035030b9603040c4880031231805e00340100750b8000c503500301100000d03070b071120f5903000043d000580 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 101317742 1250 101316492 101316497
    0x2150406110c030309060f04030c030e01020313080615010216090908040302030a08030106020d0c020d0b190507090f05240f0c01060b0702031b06030c0a02030c0303130b01090203040c0312 82
    0xa020032100071140249a0b4040e03a00065441e40b50041c403103072400e1002440c9280a649000500c0002908110900d02c0d095041c101642ca4040910040b441d42c080d4001c0c00d004940c0701c0400040314803021070b100e80240c1c0000002940894403000680e42d0f00340004440208407050403081000b42c00a512075105548038000780d518007940d03070700020301e42004d6a800384e489030000001008a96010041a240203040e401d2007541440503400043c4050703501d000182140010314001540074403100b840c4001501c0c482c0003040139003400340703006100c0c00e1381703009040400d200c5400126480c070384041c3c2d050000ca4141c501081258040410301e100e034002c4040d070003207102c082c00350755501c05081c0580405803002100203615802507004240c1303006081e100c8000b284030070442402198881c801101d600c54a144002c540e69030801008a10390300c107031580c11301e0074000402441400c0140e001d400702c0300c2d4010700040201ea40c9480d502c0040340f0068030001d080345a05141080050440310079804080e10a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 101318992 1250 101317742 101317751
    0x5031b0a03051002040602100b18040501020d15060e03030f03070c020d08040810111314010e030a0b01030201020d0f08061504080a060f110c0c04020309160305010f11090102150406 79
    0x2d5444500d41010714000d20800c0c2d4000c03809100e0164100999903000e00c0000c000d225a9100201003483e00c603009a00038240e6084000150070300100f501249c818846000c000c02000c2c3c1100310842c1c140c4018064600010303001981c801251800000340c2e000e202d03e034640c1c189161948481138521a01803202243c200c0c580301113480203d000c07500a04004e000c9c207000f80900301d000540701c000302c4138900c0400700010b50900034110301c41b0300c44003400c003920400c2c0c03500c005411141b8011786142c00501c84040c0d00d0b1059800f00d42c01c0010909451b81200d10030307000c9804000d1031080554207a4040c0c035054001500f80c8002a0b81407501103038a940c12012241d08904c0c0a484141e0103080900d41e03101515019114151a2288101885558526051315001c541400740e00d900d0340b5106c0059240a0384500d4010012030414101031080e4900104070310881c15656507646040d42c0039000c07400b466142c80b0702c0c1c40c41078042d150200046440c410816405404140c5030381012070f070070107000b42080d1249640c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 101320242 1250 101318992 101318999
    0x1d0106081b0324062b0606080a0504030e03010f0e15010302090708190c0507030f0305060d06021305030304060f09080109031b03020c0a08030d0b040605010503060d080c03030c0405040e060105031b0a 87
    0x9140040440345d07000e480d00b000c1c0c0421030381008012007280001c400c00360319042081003125400385400d43c1040c2580404105e689803401c04039140c070003103588164554a0022040d0801030564807241c0340c4480101510000c080c80c005080c24040d007480042e40055440001552440c41042802c0d0f0000081100c2034108066247c184206d5007190300c0711011a00019844040c10381010070b1641d00c603144d00d0306120624003000070a0301d140012000915180e008140c0e02d04010700c0714403003c050040034003120340b125581c0d01c00400100c990400480424100d40d000704101d0011700a07107135500d400d41c440750301a200654031206012001e070411303411806000500c040ca0744d203041c1650300414480c0c0045403100d60725400c45040755400844980b203585402420440341c2d03005025290300c6581107980501d60780d41030a0520f000e20800100c06101e0100104120010b145e500c094070075150140c0301080070b4501c10802c3c80d0340c0c010a004150b45980325020f450542024082e01d0348c4148005083c081c49540c0d07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 101321492 1250 101320242 101320249
    0x2090c0f0a110606030604030210181a0f0c0901090b0a0c020a060f02010f021315020a0c18110a0e040b041104030602040303022509050604061d0106081b0324 69
    0x1c84441840061808581034204080800400703030800c404038003400c0c0c01e0074075036070103541c1e200b49251135403900782c441c02c0071820451042c2080d03010b40c0e00050268288103042c2c03840300030580c04490012001c0c4420010691048600d000da5501a40684810503218148245481550030003501d8034208400643e003080140c882c038007444000c004170340b1a11b4020303d200c8030190035942c1c00610b0851444c8148041c114130341c50540100c048801d60384850190060b021401c0b401c00c545424080e040714102440004d484405580d140101c1c0300c00501000368031044500c000042c420a1980800503045400c8d0000514003a400710100604c0184000b072103a01d20822608035820650040c3c441c0c2d503011a080041c9074042c03103901402004801705481d0403803056054400c0495600510040c41d5a54000800c0b5854950140c40680511400f00300303120034454601410510902408002a1010340807603071481d405062407203000400741031281180e035001e00d90b80700c020b051110004405850054480c0984 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 101322742 1250 101321492 101321497
    0x30906250501050105040506011106011806031406010f050d080d0e24090d14040303030e190501020a03060e061e040902060703020f0d170a0b010306091a010e0d0f02090c0f 75
    0x303200754000b01e10741d8904410002100c074018200b0b4144050540984680203001c44c880f4151141c58032000ca022514119050090503d608003e01381500840541c1d00c45000282d0f25040340d44000044d42031070340b10f0080c400c5d0103c0c0340b00000d00d07481041c0401900c20150340c026040d041040c00840328090f201284403208503484034008000c2207d4038090001c800000c4c81721840c442404d00b090190080212821841c2e0b00c200d02c030150400d5039078040d09916000c180040c199201c0b04103954000c0c2896410404c0c000d42c010b000250102c0d1906000180900c503050f4001d106d004028844c545404640506404a044099103154801e0f86d914100780143d462001800c48140242c0c01044000c4d03091807070718504084188a00c0078030120030a080301580c0d01c8905a540426403003400301e002c202a5005030094942504003490f61818030440c901010132055a900c11403809a0325204d41840304820b10080b4840030784050000c40d15641000007501300204250341058906603000d1400380b010700c6c501d190340c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 101323992 1250 101322742 101322817
    0xa0b0316090207110306060906010804050705030a080316030506012a120e0a0617060d140604080d0b010801080a02090403090e090703200a06030e0c040e0d02070609030302030906 78
    0x716804600030050154802a6a4521a06030010103850400b480001ea100d200141100e04000b40381c030001c4c0402006116040041c030028003180c40705041c0389000c0400341c0003140c5010b5040c40c800901c00c134a600c13a020703190040006846036034020804c80c0f00c0040b00c0e1420711808002b141f24000740c130009078a15826041d02002e035981d416282c402481040b02000c01a8000001c00c4101c03c0081c0c0c513242120002904200d08442400c0d01e01c0040c60510640b000c055001341203400350908010602520034000d098900c0901c40030028070b4507003030066407502d100780100714031075110034140c20040c01d080d0119030f04180a81825104255200c2c0c00d1440352008840042e900c2c2c10007102041045031085a4000c03201c14481c5100b0a403581c5800318911050601c04d14042540310100c600e4000f070113004100d420040030b001484580d0785000303913559455a40000000600c40e26000040c1c00b4820b18495050300c2c1d02d5809513146c90403403401c00c003598010001c0b008880e62034110740241c121658042c40d811 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 101325242 1250 101323992 101324009
    0x5070b09030c0105070317041e031101060f0e041202030c030301090f1a010c020d06020d0903020307050607050c0d0518120d080a05090a0b1b1204120201020406080a0b0316 75
    0x441a200c0c0905050032840034003141405414440400001d40000083c58182000045140144c1d15400d02c84280700307004c4626410f100e20110712400341175008200d020840d510b20002e100703980c0d8880301e02c0b000c0c0185110b0301d40858030301e00c049030008241145a10040344188100c3c2d0500d080144d149066030700030380c0441c071481d83e503a500c011031110500940b88155503102540e210f82400d9000681f110741301900007032080381031034284c800b0400154151041c13242c00e80c00400a03c034441c40c021f50380707038040a0240c54038441d81d4000380e07401d845001180c0402820320090201c3e40d41c0c42e4420355441c3c00c41014040380540c41c0c007590026841c2c149140c5c00750a0014014851402c00805c0a480a01c000c0c0030420390900384010018152000910a040c469100703025900d5513850000721030f8255503024141c0c0c0d01039800503012507201468400b0780e0090340605151148a8000002a4201c0c4102e10030400400c00100000c4d11501907584111048000501520f001c804000c0c15000e503080c05401c0b1566 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 101326492 1250 101325242 101325247
    0x909010f0f091a0f0102070819111219141614030706091e03020402030421050c0601030f031e090f05010504051311120f060907020a0f11030a05070b 65
    0x3444041c004810052124410410401d45902ca140c45003ea00d011064020300c2c40d0045108164400c016180c000c2c10032805542c900074610007090480115046c1c1555a08042d9a01c1a258603000b0a0b0801c40c1d200035009007a40144603489a2100314440d606403000310800035440c20680060266a0580342000000b00c425424070184a0308028510300b5035000f903102d883e06022443e00100c0101c1540c00140c0e4a02c005015000355440d18020b981000b5006170012083c80104001c12072903150001c00c44030b40c0300003c501c090b01110300d03000d04200502d0035403111004102180222113103008090203490403210541e1480e60348689404041c01c0040080c945503010400d0200c44a61200581024039115240600e8440040c00703010409079000c95165a5400102d40424000101d400041100350303000314519003101881c00b010000c5550034010001c000009003000d10106603400001e600501400d00b14002c1e0300c2d0308841d5201e191500c0d405120700151103022803410411803004005103400240d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 101327742 1250 101326492 101326499
    0x2030304020901060c0b19020c0f0c0907020d09030215090603130c0501090503030706020c031c020d06090501030b04030f030f0e010b030f010504051b0a05040203090c2e0503040501020909010f 84
    0x4032680b0140d01500401c421003c2d044001498002c082d501f1a2950f4074462045050710701580080c442c120f0401041d20031101840c0c0d402e600860040c802c2d090031039541507103540d0400141d071141450406200010403800d030900061520303480320100610003481300d605200c442c0c40828180c0e402070352035000f0b41250a060008200c01d10b0b00a4018101c03c0c03030000f01c018542030103c0e0b640c0c024501c00400458003c1280078020300e04005a408501c20110741c03416428200f48207a00075130150001851301428060301050901c00b500032141226400784c20980240d4454404079003d89c4074003136000070151a030840d03c2890032640600c6156200d004000200c480320302040600d8810b500b0302c036008a9040c8000c01c004910041403d92060a114105120301d041c20b4000a960303070785641080c0e41c1320348040700380900b500300040e403a2050326003a2403004110000e5490f00c0804510030344040034241441d00c03c0395007244148003031500203200d038001500740740e803040000c0e2125000340c1246d50b9800f408070081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 101328992 1250 101327742 101327749
    0xa020d0315030f24020a020307061a09010e010e01080703030c02011d1f0e09060a060c0809060d02040e1f0b070809030a0f021314060f01120f050610020309090121120203030402 77
    0x121013515005421860040356500280d2603005d540006804107684045002c106c200c461810003174031074000c0411401e5a102e80c1d05080c000001e00904020180040002c44c0700103001030500241c0f07805858880300d0a00d658011900d0100107500400c05c11048031018209845010a040201600b00414003d40b000200c00414441d003011100f440f480c8402d06111054980750030b504250341891801c40000042810445528801d00103015004180000c0d000e40050203030380581f00391130a080140fa1151200300c41004a0000591210750041068108005030704021000300346051281c000d103400d0294000000f400c04404c044259910340e4034a008a0451030480e15007651405603010801004a04036082a280f83e070080516004500041c8141030380d0303014403a83d040c4803407404820b0000100c0055500b000e070109807075141c021240a0444090203001006441004c42d000d400c8270251303131900403a00a1000390f901011406010100d000b0003086150401c111900703c250000c644c0e03803c0c184140f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 101330242 1250 101328992 101329043
    0x2a2715020c0901051c050303040503030a060b1e030702070b0408030a26010303030209150a1119030e0906010c08270405010e0a09020109050d0c090f020a020d0315030f 73
    0x101103401140c070020865480710341d1141598000d550074155000222009080607080040c05802440003000700010400000029849804444010f0040780c1e030f1414a80c80d1409080100d0324241e4030308850b151610103800180da406540e0703104554210303569001010090348541c02c958019000000c520501030780204c4102c000d24910040040110503189401c59000c5060000a0815800054074407040c1d841462000e160540c140312195510300f00300e805003640301e101c0741c4c1c40c105004007408550700c40e0b00c404610701c15a40546a030b05031980c10340100b26601c040240540d050021503c0b1040109070850081c1c070903c55445c01000c500e46000c0f1010b49040355401245100700e041038014031801244021aa800441d0008040f80410240c40140ea5104d0f06d0f40000b030f0005410b110f500e0070302954011035001c803004140e080081406d10450740059100365054a000b69201c81355050b02248039603c00008400420f9080b03900545076514114030404100c1d0a541d94086c0c8100782c0303031800c154030300c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 101331492 1250 101330242 101330279
    0x6060405060403030e0d06020415030501050f01090302120f06010b13050a0b0403020409211215050f010f021606030203060103140702071e0f0603090b0702012a27 71
    0x441904180c50480091040c0c421804010100007003450211120b44519008841203580640700359103881d00d4004161000f51341e20b000400081c2000000282030411f1100011858410303558010000d0031a024060607a0142e201c0300c51a00c281c00c6a240c50140a10405e8040c000c2d82e40d460350341e0413450441481c4088d0580101e0300c07c2c0716012080141251400888048a50640f004982c050341400c180c0c0f44608525904143d0581001403c82002e0348910018910520303145c080089008071118100b494000c6d0040075004280c404814200e5801080c0218a104c0b1074411511504004443c0000c10035240e07010b00082a004002d000a80da0180038050f000b010780d080c0b4410902e00350000941c0d41185229071801174001c02c82040c08241c4c109100c0c0c1c042e00c80004140c100316604c5c00c00030000c1154840580e4018a01f80100348070340d1041c0070795040040ca20b800c0e41119011031260000c500c0c841813824050013400c1d445902c10b0000400b5260200182c0c0c40086a00c92604c01c2c440400d004a22 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 101332742 1250 101331492 101331499
    0x150402130b0a05030f0a02030f06070801033f031802060901080c0d09110a0611070605030702010b0306010e010906050a060807050f0d0504030f02060a1103130501020c16030c1203020d08060a050a03081206 89
    0x20040bc20b58007090041c11aa00041ca03681c403c01d002c0204000700d0510020700b82848901185030f26821540c18107a00c54040b2960100304541160040700031404510358002d6100100b0821101d00f50703c40d4400c9a00040304140040c94481641065012564110310440781c911219501c42d590b4a40140c40100515941c01c1100c0c441d0504051075403101c4180c0030301c2050000201c0418021031003580800504d01001e01160101c4d61120020380c0429000d104102c4050308010000c40c542c20305c00c0085e403c4070041c2d10341c1c450640b07aa00003960b8503040300401c200345442c140300200001420340580c2c3d0259000c1d4954103180c0400e2400203003490f0700186855041d0f414007070080c030200e0b010b0703081b241e02a6815a900c1600e841c00c1c58468007912505c02c1c0c149184c482c20f00000403220794441d0300021a4828103a55400c00c0da600b980d90b0000840d1400640980c200c48030340c0e0140c038000c0200d19841200140855401910350340010201c2c5403940060b1a0b04002145401e9480624100150030001c101c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 101333992 1250 101332742 101332753
    0x10b010e060909220308060a150f0503040f021c02030d050429040806011806090b0906040e011506050d0b120601051210051503150402130b0a05030f0a02030f 69
    0x3200400d0740e910801c2c400324002e0038140c1c002610440302483c08005041c00e0208000c40c203c1c0c500b0300800c1007038207813036440c46940042400109100d150382050140c010340e0b21030042406844e1400d40741c58100400030b41d401004514054010ba03200c0c000f84144103d4195007603a1916180107052400e05032010200901001b00801c2c4036440e1081c0303c4001c1b0f0100314907280d510b402d1500da080414003079a0f004844600c18103001140c81851708070b042c60f51441c2640100549681c90314420141c2d140080c40f65000030344440420b803a82010b4002841c2c0700c001b0400454016107d080e14040c0342d0180d0f005100080780031078001c0d014641070180c2c40c001c03401100e10002c04c0010341c0040c0e44811061283c28820464100120302019060108205000624400b04075234038011840303a80e1544c080c80a1071083c010340d5100c500710a52080002e0080350050f0910111504504d801002041c900f01582d61011742c401001680380d8003044a03082034602000a0111450540f05041c94a00c41e078492840d20f4029 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 101335242 1250 101333992 101334017
    0x9030a06021801140f0c0a1a01030302100218010507050a0b090709060801060b0315030a3305160e030a02060708190504060c03030f1b03060e09010b0a030b041112060702010b01 77
    0x80d9054540c0d404c0d5172020300d42d48680100e945441d2071451480100050040252001c0c49290717a954607048174040d03000d550100e000401c1c8207089114120703d2014010309550b001407154840c3c009403440501c51401c95060050903114500303007032000c55074054980c0c00f0200a10050405000340c0009001103002840720f50300703004585820f400300801510000e03540e00f140c4c3d800c3d50b03010090011102c0d08820b11807024804030440d10381d01046590300031088942201e50341c3d0170207820301c2542d204189007a422062019805801c89070341031000f076510b81c14803a0b00c00c0800942e076100300030300d105849541c2103542d40d480445003044a044821410382404000c2c4010030065130000807020b02c072641481d00007818011003005100404808011f641121490000004165010b80c44001955060740402c2810303501d80a0003820307074542940c450380141d1488010400a00c500041c9600a842604c8404030380c0f0b0090049550408244d401208680c0010f00340840c441e0284600da40ca9542880d100010008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 101336492 1250 101335242 101335277
    0xd0509010608010e100f27060c05090306040f05070b0d090606050303120106050702040612120e030606010c03051305030303040305040f05010206060f1201090506090309010206010e011d07020309030a06021801 91
    0x40f01510303001001d460306084440d4611547c4070b0440107070000b00792104a203d0310f001203480030034144111205880c20000c0c880081c000c00030717142e5a900003030040006507100c0c2e44403000007038030b04002c0300e00d8070424001265002e0304202070300d805c2c0b40c94440020b4820f0181061002d50303400348d004900940040060038503500c1c1c22480681580c0981c00e055907625040c1c4049801040503600c0b003d0001c04000641c01006401001d50311420b06559913803801c44400c42c20561203400549207140862414402800080c2c000c50140212039400c480740381010340c0da4004642980d204450441c005000000e0078800c1c0610f034015900504000c0c4020301d140c0c68580081441d400d00c1d8140540300301c00c01012502c03000025000503840507030000545070356040c00d00700341d5600d82000c6c60490160066038008a04a006044814105c51003840c0403180c60004a42c0b1038802d650142a0404500003000450801d0302c08203d4240d6281c070a200c0180e56000025040c2050300f1822016410450b103440308451144 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 101337742 1250 101336492 101336503
    0xb01090b1e0a0207180203060108160203090d030903051c0908060702030f071110090f1403060c161a07080705090a03080c030706060803071406040519030909020d0509010608010e 78
    0x500000c25a10030342c4800a9180c01c02070b5100b0155000c118103030803250006034014500440c1e080c3c954030516229402d100e99144080b001d0755005034814840da031218602002000740060081c24155401a102c0d1191410030301c0d04d022030132400d61032403070b00840554010417110090491102408880c280031038029141c0c41a01500d9100c0a030116580003813000a0410101d1700000600c18041031003d100040c0c90107000c0d220f00c20741c46000a800003a4a05d46c41541a40c43d50000c0181030035903250071944100350050000c0c2070021214101010010700408103904800420b12406a4907150840000b012800000c2903802001404d0120240a07140d41c1101401d480e0303c620a29101e0001b01005803440c045d001d4027810407403c08600054608021009100d0180181000382ca40c01e100c0040070768941d000d6900a04035484003441072080b000320b08140c00a05e1192400e071810301e5442c404e070b1040e17802c001e00c0202001da03198144401d000c402d100701c1c1c008050410091011205142c44152502d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 101338992 1250 101337742 101337787
    0x140c0303070b06090c040b0c0105040c09060e0c03131502030f0703090302060402121f020712021f05130b040506070f0e01051803010626010b0105090a060c030c05060a0b01090b 77
    0x111341640115440038052000c0d50040c20040b01503549805007250194080c040c15242a039a00320741036400b1520300110701482c01541c00d1649a0221030310b410000461b50f6100410b01e06e50f050083d1030440010305820103103506040f11000c0503031241070503036401d5041c0a0240000042c14a40240d0400082d00440e203194415011140354500013074144029082c00c1c0101340c5d403070350742940b100c0c40186d6605130b81c080d18846009141c158032454060f070040c1d9175032610b11442d51100750440810300040500e60002a40482100d6000c19035205580d10420007150a0701c00f00c401e500102c042001c900d5001215005801c0545004e0b0001103501001815500c203c2030a0040d60465a80c0f8203820f07107003500304000400c04041c040c0c140c60039503507814401454080519100d5401c00c0c0e450b051a40c410f02c15964910b07001001060a5842d10750180c400300c500c03480850030311003044500000f182081c44620300c100c1e420600490035201c1e40c0e000501c01c1107590016640e94a040c071141d01d800c40104642c0300305 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 101340242 1250 101338992 101338999
    0x203070c061a03011107030908030903060105280b0d050f0712020d0603050d08011508190f0b040f0b10032a051902030a08160c03050d0b030604140c0303070b06 70
    0x1d003442102e00e144810341d040e00700e4043d801d00c1c1c03206101c2c400440080040a000356035410b40c3c662194402926841480011a41031f404400140100c4c90140401803003100a10b800034070040851801060b50005584641d1385030700c000c10070180b850030b18010281c3c4143d544016100914040f0380c05800a0500d0698100503a8080341d500035070038141d4000f10140da004400c40e040324541c2d50000b00015001d024004e000c2003c50541c102050265600a008441240004491100081c0504014540c03050368002441d2903115482170303500c807071040340381910b4031b800f011400c05082418400c140615142e0700342003501d000c50800c07000010307200c0964050240003c40b60071200516040307800d40510b0b030000b0440c4401c15481c0e4080c580010041001443c2a210004166100c030407402c060b10142d41341002050f041e1092000281c07040000300110640c2d11b2000840514840201e450404c00310740403205025a02c19210062404001080041c1d00131001145480c101ea9600c4100c80b001500c40c900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 101341492 1250 101340242 101340251
    0x1020d050f1317070608010b0306060d0b04020c0f010b0d020d0206030c070b0c03010f120503030a0509070909031106060d120536180c1812060106050d06090203070c06 73
    0x7011140041182d4009000c0703081002001e40f01e55120100706650080310036070340b040c07880006106009072465412202c0c0740711000e0541d6920024440c156210061404035543d884140c403c055460744090319a041151008040f40d00d8802c1c019030071500c000404522034144412041e0050750342e50514018190f054415075226224142e031560030303001c5e09000030b0401c00c01070100f100813035540b000303181251000d103542c036459a035030700030f503c100007a03444080e2240d0010030020301075440940040750080310300c01c110341c01d0035658004007040304e41c800d0341100050000780c03031941380403c2000300540010b01100d4201003038582d40d94161412041160307143c00d00c04041030385c042d00c000d0410b8144050958800e50080c01540d114011500c0310039001c118031510405001c01c000300c001c8090f19203d901c00c00c1105281000b0801403041c40d41074190625846440e110500444a5042c000035008041c642c407400e07103d440018101c0160307506504040340355481170040040352940f0000359500710350000300014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 101342742 1250 101341492 101341507
    0xd0f02030307021008040507050d030e0f150a02071a0c03070b100e0a06060305070206060307061d1807021902030616030f0c0504080c04140c0c101811010305040201020d05 75
    0x303056000b00721020f0361111404542641031600500440c0c45103200e082035840c3c86450b0401c11808004070040034001880c3c4d404040c000342041c0c807044105441c000c0011140c0007003000f07400c03016409024440010307080381200b0000712406002110054800c49078407820401c0c2d540c00d241c1e80e40030b000c5016203e0380d800404a81d0012404880c0e001034641d011280302c2910705187e040b0b01418203031281600003445e1a00260000b48041a00d502511001f00508201440c15401300e9141e001c403500c680800c0741c0e10440021981c0c1f03502c2140901d44108000b038110f490100006810300d85400241e6030780061201040005980225020743e000d0800d00340d040e440002c1c814114001c0c038008994115171403418810480c0580c019018004a1b00d0480803559209038aa051009640369048681070000d4104041000000a81e0280080e06590030840b85051149000d4006503900030b4520507003c0b5100f01d8460500000344500004003400313080c2800396062a41c0000d645e84000e51a020400a010862070b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 101343992 1250 101342742 101342749
    0x10e03090103091b0617010503010510030b06030f01180201200a0303021308030c1f230601020a0b0a090201080117060a050901110706050a060e160f05090901171b0d0f02 74
    0x2084c01880078180080b1250725141e01401c48081c0f68a80000c2d6424100001214581409603501c901d21234107072184128a169140c15403d000609040d60500441030070201c400000d108041c05031150302c0d210300c1000841e0001406502229900a00d44e503c500318810491900044102503250b2624005949141943d842052824260012480c40c080024140008000080c2c5040b200d50691b10b03e005688071940d1120458a0447d0b8540c290441800001c4412015a51039070b881141801920f40b012015560001c4100080f00c2e000310265071101b5041c19540d02260351409022024010490076a01100c41592418020b090400403910381e000100000d4003034100000c00e0712640540b40e1101e4a0b4600340001c0c103800c5508001044c50602c00042401d0300c5032400d4020380540140400310300703041c0d0301111041070340d82402c0103110040006c61b025448103045640248000e144020048005110090810f0702140030740c440480070180f034686550310000481c0d2856440181c1c4c4058451a1021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 101345242 1250 101343992 101344013
    0x30a1e0201020c0d06050f07030612020f0f0402030c1b01020f16020a03080301080d02060a0204030201140d021c05070e180606070f0501020301120314040602060705090f0405090d0e03010e0309010309 87
    0x340d03600218480504d0b4200041e58000c2400340c610342d03403510800d556808048040703030207520500030074100c41c2c02403001504201102030011540a8034254950448101140690b402658030542c20328001920481c4080300784019900a91018020352402e454010400d50b14007030040d034440b18144c01c14070380c8110b6640c460072400469015440130384940e51804640e440c0c06a04030f500d800340c0905800941a040d1b00d01c2258140c9030f050711a02c12555910100e803480da0010341c0b800040950800200c03207840c1c0d01949208100d2031102000c200b510b00f02000504040b40101e07000e005424114001e038808080500e80c43d4041404ea942c40d031960031604000c05c040c00905409030095100100109600d90002641082d60b070013929032019006208100c0074543c0720300d11440c001a00054007048180e4400c50041814860003000d500c1410300c030304006811520103030307843c1c0010343c09007424a40041c0c0203840a80c808000b14000c02c8201e1062040940381c1c030030091503604243d035801c080b02c10000030300328 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 101346492 1250 101345242 101345263
    0xa090807110f040c0306090606091208030c0d18060b04021305100201230f01060203070506010501050702120f01050a1104060801051c0b0c0307030510080307020103110c03071b05030a1e020102 84
    0x107000c100803138440a4000d00050091041403070034601e012604c0d80c01b0b1407401084074002400d11400001c1a11074141c550000b8202415802e4100071035400f080d142e00480841348840c50360803600c103c0e589841d0040755903801c2160f008074018842400c484012160a2084070000da0f001d03420710340800e008038018100001e500c17140407882ea400040d0b01e03d0841020341309051206941d4003c2e41c998500740e030f0324091024014099400b000041c066540300e040a400e1040c80507003d40010080c0f40025070400c20480301c00281a907442c030800030324451500403252404040055903180c9400d100e00203001030b10502909004446e01c14014140c4403041c45941d03202900044110840d0a14201310680c0e507105071b0711040001d04150200c0d24031900b502c000340440b0200c000441c0f5003082503006601030701143c45070a84000e0148500d5050f10340a10092442c5031140b0f03480d0408001c002c05500410050b5044240654030150741c00b00005e16407100621003e03244001100710640c00e200403840d00c42c0499 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 101347742 1250 101346492 101346499
    0x9030207051504030c050409020603011208090a08030d051008070911070506071205100e0402010c06060308040807050301150503060712020705031204020306090c0f040f141008060a090807110f 84
    0x903510b881d926280c0c0064002d8078407030b890003075803d40c3d01c0341048280c03449808080c0d4440700800c0100715210011100310142c0380b06540700390134485c4c4000060f44e29041030340421800d07000000c0a400690b030922456500006103850b18102c5170800d0110395a07105680915005550b0314036110071051015400d59005980c00011640645480d140061590003003000c1d41c09003034240b0010030a000c1000d40a0342c20384140c00c03407c418641e102e400440300100c00c02402c1c0e9026a403030102101094045000304054a8448020182c4a14000c141800c564003504410708800c0340d010240615640414250b800c002c080c501034018070260b1400700f0081c403940c0402000c070b200c001914441409c010a601c1e1040d030003101511301661707842007001d0300c40c00e16104050b4404c2c40240d1101c070b54a0725510080c05020303404c0002034100a42c172001ca030700b0102035038012070101e030b0720b4030800111104000c4181c0c0b04010400500000400e5691450180189030300144000200c080030100d9403280942c1d0000d001008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 101348992 1250 101347742 101347759
    0x1030603121106070c12030c0c0b01060e030c0a0311041104170d0801090506030c0112060801090b0402030d02160b0f0903030d0603060605060f1b011407050a09060e0d03030903020705 80
    0x1d080a4a02d1181e1490b2116a000344000140030501403200e080445802010342412515a6103046006101c0f940c20b120a0002045208022480912044e406001c450f10754040c0440a04109445c001c4645001485040d040030b003480000c50809540b41010000c0d03c01291564159050074002d0180340c1244a24040c4d4008030003511038005010009a030003030b01c0707501040e6260050282580c908039a503035055404641000d80d5940f207010032604800103d400040c400342ca42100300e003943c1082400b0307604000c070702d0140425450203108a00e004c200c10f0004000ca554081c520307150b007854912079108a82008036001c480480f0030411662040d1004090726580c0003c070b50004014006400280d8000703140a1010846051403821030303610010703020002d810041030030021040c1c02c3c02040b440100b035484900119620307007001101402a005030311099111041d68000611040b00d81d03110f203041062000345c0300016200c8c02040188150146000308244116090a0b480c1150b40e521090300300609 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 101350242 1250 101348992 101349023
    0x7120818012106090c03020408150a0209030d03050103051203010303090608040312110705071401120506032811150703030509150c09010e04150506160f06020901030b030706021b01030603 82
    0x86a11103429591001300810503891590380c01c40c124055800340528642c8521510102200d000c0105030340080031182c05803501c103d020103c1c1c00c20050b890000d000c41d45a000600070400b06105020b00c94225008a03421503141d42c400400315901032003900140300640300400d0606215611113403c2c04103021040c03101004011101e00d00360300079007040e1414042c140c0086003040301c2055010754440140e4903500482100c14501c8024100680350583c0f40c466040340c0308178807090300c058a600680710034107004ca420450401050481403090748a03c505000507418950349440c0c400d40c5c10680d0107190000d0541c0d2581071151070801900706040e14000394008000c000075221000303240300e1388282d0380c0741080c0051106100035184d2030f40b0303100342d5110910320510450170142d0207030401801203c07840040705981d80780c0302400091040140d6100303800081084907540c06008a1119003020b9004040a520b001002900c405095030144100d1812116a032a544c0c480c2c0c0040c03002d55001280300148030103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 101351492 1250 101350242 101350307
    0x7050a05032809060503060f01051314011206030b0c0a051e0319020c0a060b0303040e10170f06040311070314030705010c0f050412230f0712081801 65
    0x3400c110646240c2c2d5680c41c80c0015115a54503c200c5215440c0c06040d40c441004004007216004a254100305080c04903c090b41c402d44101001458503003504000300c0d0041000402840000c9020780020b4146907040002420b81c0b0042075010240b401551345815100c08211003521804864503145500548202d04040139100114012080e0041107a030740b410b00215170060f8000c281000351790390401c98910010890035080240013031001815645015141c044c641c2c00d600e01030b1142034203524203d03002c2c842400484211070160102100800c2e1607080c0c208429650940200b00400300030940d550724000810400101020310350210782900070f40000c060f42c540c3c90708540341c06da41075030800a040b01900d0281101d150071107203595450b0300e0070b4186680e03105100c040d41d0080790f051a204003416a402c0404400c15049084100a4031403031108000d120b1910425800c0300c0c0c8200c801c0b0201800181183e81218800c8d00c1200b0640c05524005c1c005032900030000a502114580d8030040a0b450507 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 101352742 1250 101351492 101351527
    0x807090e010902030c221701140610021c020d170c1c0f02040602010905010f060806070c03021207060b09070518090901090b19060602030a1d0d02030d09050a091b0507050a0503 77
    0x240071040818207a42400c0700c7c142601e001300c2d540d1200ca003200001c1149810300320816021800303140100c447c4d07035410001001030489603e0710031005801450018003410b91107070003c1c1d40b01c2206030901965080c054449803892080715803081811811115032600c030b50b800c4e003041045001c040b10231922203603202c401034060941100212259481c041c0c2100121850344100d1090b154540b00500240d602c2071030695110980e0300b010750a40c405c04601601c210a0f0078002d150103031207601e01040059118050040008c4090803040c1840001d102454030b145009008402e01102150042ca0503142c00f12824010400201c0141030f000703d000401c40313946540c8455540528065804110141c0d41d841c0c100c2c2c90740039000081c40040c905600010f40010910031040d048400140b40350190700c0b9580c0001d1a10f40c0c40315804001c290614000c00140c40c102d01d1000081180410502c600301d9014418150246000d01c0c040c14071102080c01000e200301040a40300a42e8058210fa83d150003207040c01c4d8080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 101353992 1250 101352742 101352749
    0xb060d1a030a030206040b04030302070506070e1f0e01030209040e0105040c03120c23160305060703060f03080708070f06020408030301050909010c080f060310090b070807090e010902030c22 83
    0x18000c09422205504001841410050300b560280105e81c4559440e8050350038050400d03030405400b40f041501061f130a02c98603015900f207413a091400b03901d003814405641403075440003030500d001880e0310300c0c0550016000c602ca80000d10b0010ba03201007200c001401005040c0180701c182d0b1800007000f0420001485001c01d0341c0c02100348240340f1040349400c844070145142d008240c40f45200f0340000403030204880c034003800fa0050a070b803045240881d0003000b0361010362081c2c42c10f0740148203026440390103120b444080c0400040802c2c1e02821511b0b0040c0074802e0520003850808005030746c0b824000d0303000c3d01c58402a88280d040d9a525034601c1e401c0d6494000b030040c68855442d440c01700d110304c02c4c140316001d0314501f141c8404082e0b0351004981c489202c4024086901400380c0011148402441c1c45060041031103411400c1d203034101102c0080440f1001880e83c1c0c1800b041c5081444484240c1c8800c904580c006140941d42c0c0d0303034880104809000319656821118003000c1e480c10000200000c81003034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 101355242 1250 101353992 101354021
    0x1c060e0a1103070b09210604050a110f1503090705060c030909060108010303080415020912011a01090609030b090c0607030519051801030e011401030c0e0c120a0c030b060d 75
    0x10341d072000c105a101c01d01c030320076095082d404110350400c60800d80c1c0c0d5002c00c031040041e10202810001079050a01400316421540c1d60801501d1004005a4101c188003503d021b84404003180c00203401715510701a0301880c034440c00e0010000901c00c034010003031000a0000a8141a00d8a038882034156a941040c8080f5101d0592500000d800354466400281225019580c2c01c1c19a02c890725207819010203036400702c60250b001c014803031903a10ba00d96445260b0071000000920304001e85030742c06104803507040d62410845e0550703040055a0340304c1e40c440140ca42210782503100362568090540791120011199070420340c0420201c00341500480641101240401400f82524641d00c04031a944980e0003200c40303c08050130565400d5100ba448850040580c0000151001d05100c3d4442100e509900440b502c01c0b0400050115940020810b030f00311025001d42e50a08087c86100a6480002000140c0003a03540010119030f92281e00901302a24014081c21341d00c0001c0c1031241c025041c4003442090303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 101356492 1250 101355242 101355263
    0x906043501181b03060c0e0405150f090709120c0303021603021003020708090406090b0310020a0c022803080a0219051510090501060f0f0206040209061c060e0a 70
    0x100c0d03042c00703142d0340c50b20700c1000b80c2c03081c0c015540c411410f0a142c0c0d10310071030807481d03650101c0061043d10403140c5138141610b81d07040e041940c0003044140e5000620052081030f2803403552456480c3ea02c1040b00480d02200d0b066a01c0e0b42e0800100c0d00120180d00c14502030200162490034030005024503025039010fa400e0740c02840403003914941c605010320000350844045020080d0b618071035805003015900c2000000e1401c1d540302c0015090341c0c02038000d47c58090b50b80c225101c1a02c0c0400c107050304c8031107101055040040007580503140342a407000290007110308000d2101041401d10080901401e00182c02010f0744c4c984c00d00d814160408001103016205019126130040702600118120981c40f90003424401e03c0c1d100051103101d0003420f00034080c481b0181c08640702c4814041ca13400303441503640f13082c103000c3c82d032100418001c9044040401d640082007407001588606034100c0d0300410075a002c186540d0440590042c0c034841410150802c2d280c031000c00342e041c13400b26880c92030743c0c01040300e0034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 101357742 1250 101356492 101356589
    0x7050d0c0206070f03050a0b030a05011b0c0b0103110112050709030501050702120706111e180a03050d140d021209070902282123010602070308090604 66
    0x80c2e0301c1405541007000b1078068880b20f045944079070000c6500110010000c034988a03920042843c00180240c11240c60b510b940301a00c090003200f2141d07500e1030b441e20701040d08107000e4442c884131351818080a0402c0e111200c000005174010500c10f0b1071528910f00030049450800700050040d105800119020b5082101140d901c610004003c441d070707500c01241d40e04d030100d2341c3c1c3c40c0d82c0100941000c406124009001d00c480c400158445101c041c0c03001040e00365120765440005051705603080030a4460582d0340e50a102082001900b083c20024906128207034031101807410000f80902c864004405000044d0410399204004c0480c2c002c2c1d0410040b141966201c0240c0b8050b401a0000c0400e004803c0201e02c0001166494240354808d0f242840386000780e0b80310021142c3d81c28070161840132a01c0311003034078800790700700300c818041c0341c1b046c0500380c103541410402901c60085200241c0042c201041c80d469695034002124010481e121081c000d00d107500020030008030704503104c5210301030a8580c41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 101358992 1250 101357742 101357747
    0xc0f03180c06074b020a0b120117010c050d0504030905120c030c030a030804031d033a0f0e0f0307081e06060108070c0f060507020708012403020402071a07050d0c 71
    0x40841c9044159066032000303000d00000013480f80c000185d0303121000c2000000c89817001d400401412410b03211081d219818100d00c0b40c550000b5001e00d401981c03402e000781c40d2255116082d6803280780386040102e1507448505086584950a400c65a0700c507080c10b4084a001c400014030982c3d07401e080c9c0c10385030b604032003100f01610303a10409009008941c0560003d00028840c035900303441420041c140c1c10f91942d084022a10308285580c105d03051491031900000140d164456a502c01d0b0700c2c00d11a1488103070340050040040e142800e0b40424018a165060541d559446107041c2142026044945c2c5542c2c450b001591360b03032002e0710394034480703240700218500303650110f042d500c1080c06865482c4261103405048270300d030744004410ba85440d0341d0013400001031814000c803409159240d00402d26607061a26050844644d400a01003d002c0c0d01c041e00e4206151924034401c0f07e40465005880e07010b24101617245c0c0f403942c400c1c560002040400c21407865040340241850079004e050804c101040308105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 101360242 1250 101358992 101359073
    0x20408010e031c020901050d090804030201200d0311040302150304021009030f02090606070f0b04050705010207080c0f0607050303010803120c0702011e0201020c0718050c0f03180c0607 81
    0x30f5040b001c07580c1d0141c48200486800820780b410041c50520f21f8101c400c52031000b258444541101e1114001908000355a48071505159102581d400d000e0000c00032034a0399904c0ca0203a48c58405e245d140e560241c51503103200103403801940c0103442114081070720188903a036079008a034102c1c841d821b00040404c0c45445800c1110999030300c0981d0b20202d061035020090305a0000f880e80b43d10180c100712110000d0040100c4030840d5118111051040c10186401d0741011901d07040a03045500c0301c00304020403500042c044d4001e0b1030544d0020b03548081c0320040798083c03180c020b010b0241d11000000041d92132000004000c220f8200c00000c900d6151081441d44a2091560180c00140500c481d00301003809500c101c05c021809000043c40c2005090259041c81d0300c550010506509025406991b82140d0141c03d80c050744126800385452002821382c1040e00002c3c1c100101c0310340c03080061100e05010080c000001d280240001d44030701e410301c5c2c01c00600807000b441c08440c4494820100321480301882 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 101361492 1250 101360242 101360257
    0x30b060706020309030d021603080108011e150f17010f18020105220902040503010b030118030503100f0b2502010210090213020c0c01090e07080f07051c020408010e03 73
    0x40d240900300c1e21910083d40001d816104079000c01c00010005a14900c01000070341803031806c00b4085106424007404c070b0030050703000b0480d42c0d061824914082c5425600c4030100f402440000820308804030724060011440d400651440b20400e202240d480000c0c181c1c49008290354000344041445405008240c500800141031401e00703400a2100543c01800500031003045c1d1020800c1c1c0c01002c4c980b00400c5001e0f68000c1806a60004060005040a00030110265816402404410b401c0f452204a07040c102c4000703010060084040740c404000040f8140080064200341d0b04900e484034211078543e40721404491100039034043c3c11401041599402a1282c2c058015242c28100754507020f0141c80c0d4943c0c12640805296800c2c401c10701603101030302c11ba11504000300402c0c1154800034083e1450350300f00c007840403c80400c04c081a0b501120880c0c5c0400d82c00340e40c06d269200c084095550b80a000100d400120410103811480410f640c00b600c12683e03031000030b22002c07171801c02254981c4a03000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 101362742 1250 101361492 101361499
    0x50307061418030a02280501030501080c0d08160302010b13151703070602030f041b030807060207020604090504050a2901051207051005030405010b0609090601030903111219030b 78
    0xc000c42151001251420008010f025a8801e001e507500160700040001c907180c003d03100103e03051070112100001900640301c00c1c2801c000a504003180700e035640020142e202d00c102d41c2550b0b1281000b010300e081d01c0001400402c6410b0720459868064060151f904500340900c3c0075400d2191241028040d036000c001d11040e4070f8110030709015401041c0d82e80e0000040907440200110350014a140c40154481d107000d503e401a50f040c14640440e404100742c1c0348070092030b40c4000900c00b05008000322a082940103400680c2d8480910200e503a41c00b4030f6100c2d0304840d1900701040144480484ea10100e03074420b4848444030b094904001c0240c0800110701000014800014013040c01d04814224610f01c0200031680c131581d035040003c0140316115400e5002500200510040000c00d000308000002c0c103d40031824100f9090106042e400b0040400d810151110550802c0c54060000f8010f44809903041e1015201945003ca07010740c40305034070101d85807140b495044818401e12803410700101c0103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 101363992 1250 101362742 101362747
    0x10e090903040939020f15090105060607420b0f0913030c02040204170a030e04090b2208030106020a14060601090b0a090e0103140c0a26070810060503070614 69
    0x244640100c513010b001184254400c109290102c1302c4100029890f020354030301e01c1c19041ca0141107244c00c0d101d0251405006e18010701130381000521803101c504422004081030711902a14030300c0320702030003500c0c0590040c50303103008049005030f4425041120b86200c15a4600e6815810303c05101c0000070803a46210040030b400a2400001c2c030569180f200380c0e00044c030141c00c0070786440c940610300320140e1401c00103500c107840c601c04168020f5640005140110380c00c1007803058607221450384d40f9008040d10940c0010030400034031625424010540c143d003040d6225180c0d070715408041d6545080c1b200c280e850284004120858480c0061403501c01c400603035580c11001c0c5002240e14007504020b04400921580c40004940c819000802500071800b404201003840038880d00c2e9820b041080003441e010700035692042c4203800040d0650142c101103144c0c080d0076580f0100c101400c001140e00410300a01404403101072511007500b080e42035031401c81c01e0301c540d180d03113030300a0380c078201103c039140b1001209 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 101365242 1250 101363992 101364071
    0xb07060507090302060417010902030d02010b0310090b060d0501090b0115030f110f0306011b050d0815030c010e041e050f06010f020a0201030507110a14120a12050402010e0909030409 80
    0x22807c00803414040300000c41d909040c0e0380000e0030240d0b1707910100d0043c1c0d902e1080e60130501e0100490001c89140c101e00f0030440940e511101c92041e00140b841e03024841e01440c42003041425400200060342020060483d541c44441d0700340c85008601000c800070b81446410112840107103e503c1048901d03400d12881e20144001d500705981000300003c0c113020640c12000596031a465440341c400b0704c25009008003c46081029215a0019158a031b03c90800240da0203d41c60000320303240c255509003072648a4001c03020005000d0500310001b8141110a080240c6052400d81c200358000e1544c05048069070350b403080110785860400c126080103070703c418034901c00355000e0b5202940200c1c4901c2d00040310b400f03080c1924a0000203003412550405515001c0d01c0d410410712550000006d02c444151410590704401800c068880015828030344c0d03101c012404681c0243d80c540340e1140007900e4032400d032410b080d0301900c0707400600c120b104685c00d240d0320140c07101401030490310001980e52880c952107507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 101366492 1250 101365242 101365259
    0x50904020402090306010f0503060f13030e1201060611010c02010903022104030204021b0d0f121e1b09050108010605121519030c0b04080616180b070605070903020604 73
    0x5028000381d801c25820048450741d51030600209010300320090780110314500d03080c06e1500d8104000c0c0b0300c5000925000604c41c0c2d289140c0e210881c199058070f4a28074030020f51002440d54007585040500302d40c6407260010b106030b0824480c0c1985140480200111422210117909a07403402074010700503003050004405608a04610b803070b0708003a4440704d5043c580c803a0b010508036800340701c020340d00c4040c0b105030340a492020401c09a12111900d85203002c09060340000d0414045c444000301000e881e03140200003451014410724003040c1400c420b0106159000040d05010355a00d0604001080180b0108055000381d007035504a40803a592140f03482c0300d00e82001e800710700c09003a18541400290740340c01c5541e0394480c0308580503502c2e011036080d42d01d9483c240444800542c0443c0300c8520600c0f0402127100c000c50035903407107200844407801c000b40161080710381c198109820040104648808102c441004000d0090301c0d00c50a4100710341d8443c4070060321100340610009504c50401c010a100345807 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 101367742 1250 101366492 101366509
    0x30309050d0f080301030b220c05120a060c0c02030f01020a02060a0c020f010504151a0f01031503080309010c031826070804121a09190804030206030f0a0f060e0105 72
    0x60080701020701010076030f0f48950650744281d0040d605800c60b0002d000500005584411020425004504000040d0b44c4d90002daa4a2481403510030f80e94003640b010060414890407610320740c880340401c107144070701c40042c0005018a105a00030704c13440e1a0324040ca0340510840b074003203560f5002000140d8a0b508443c3c00703040206404402c50140150003480d55100b405014080c40c49846500c40c1c1000c20740c40c142c216441c4140d09070413510345000340002500e039401e000105100030b10b00428484820120000d50342c5130795200801c0303841c00108000c5241810b50020700c0c075000694081c000141d00e03000d07001c928021201d002d03140245000100582104454040c481c0740f486602460404895845030262500242d201c0c0c0c502255070410201001071144002d046104660707243c0b015810030341a0155981902090b501e09070b40000400001d109503142594000c66000b443c0d2662407605040c0303031089800a580c4040868246400c426000da4a4001d69090b46c8980701d074041c081c2e181408210040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 101368992 1250 101367742 101367769
    0x140304050a0f02040f141906050d230d030506030105010e04080a11120408011e110712030605120a020901060806100302090409020402070f0b0c090a0501050a030e010e240103030905 79
    0x16541c00042d0705540003406492401c04080c898040e8030300d000b42e81c0c07e6241c0000b0703002c10001850300400b84840d0b81c2c0c0a101681640c0c010210200400304665040f070040518050303a220381c4640c880e40d01e141e40e4503800c020310502c4185c00031f1201e07076619400317000c00001c2640c0003440f0410a100014060307124070f00c00c203014800e0100300e170b40003040180b04220300e51050b0080301440c0d440303d40e403a6038030301c40e02640c2e114122015020002c03a101d1040100c420701882d20010248115030b042e51200e14400d400203405000010203141e0b10301c41e00c03c3e12558404c0b80c500124000c040240001070028050b007002441140003406020403880c180d40110000c1d404101d40f2a4495555862040940c90354070203465054030a10f00c480d071140d000c3c101021001001000170000030420400050551105c094180c01c490003030070000c0d101c40c0000c0c0705502801e420003c0741025803821406e80320980d00001c079926418581d54403443c20403c1002000e8400000b400090003140c00940f04014600b4440c1101d60f04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 101370242 1250 101368992 101368999
    0x3080907150c06151a0c0106080d11150405031b010905030a0f120209011205070e090408030a0b06070803061009030b04050c0f030a020d1e050f01020a140304050a0f02 73
    0x14140c48420a24440040060540001d044030059408011184c42840d07050040d140030040c82d246030840005001d41c00c01d5420781d142c80c0100305031007404001d400060103001800c054aa02c00801c0800a090240c54a00300c0014412200180c0340e01030740801603400780703802c00040c40c9854100450b4940c00a40787d00c103511039650741c2c3c1180b00803c5051000d0140c03482030b03688403d1400c40c500ca000308942c500c01107241d241481040050f219a0300501100540001d070540841c1030f50302c0a1081e01c951610f00205504541641c00300010402c13480003d6204101e444003c11418070b0620602500c4e028240d002428441c04001085c0c0700d1901d031550001412261600c90f40359a100e640d034480e811b20a4904403025417180309a180c9501c1c100344c1060b213881e002d038003c0c64501101d40009030900d0080d94003a100c152a550114420308869540c054400e0f0030004940400d610382e40054000d60004001e0b90000324401da00c42c0d000402c040890340201c1d0024002d181a400c1615000e5600200c60401c1340d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 101371492 1250 101370242 101370253
    0xd03020f09030102030412020715090e0c09122104050f0d0809030a0b0702010606051204200301060e042006030a02031302040608061501020708150a0905010204030c031a040f030809 79
    0x1c580e001d000542c440c5101d85c140408104085001a10b84401a0049503030115012440c40000c0d80c0000200200ca01541c0310900c5511003c006004510415207103942000100461203c0300307000090728140c520805440074003030386c0704441404460269001c0c0c2da42c44003003414080360618000e4030f007120f01406543e000d850140d03010300292411511000880b60700b112981002907c030340a01c01e50780149201d0800034a0044042c0f410040548002d000410040100840210304841d03404826401e100c00350081080d242c640750041403801d001c50b0101c4105000c10482d4198400350490f0301180350000c1c28081c04c584950305208080d40000780b03981d00060300c1546c1100542e503540120801411040c01030400f600b04505500078003030003500b0141c155070103c0410045886c0018900c404c00003540700108058850600b034401808584001402a42c000304000c130600c5180244401100c3c403d102091180034252907841c2048012180501102d000740d0410020034051f0340f1080c0e028641c1000c0d2030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 101372742 1250 101371492 101371507
    0xb070f080c010203040b0406140c0d1a060d290f1507080f030609070e030d030b0102031201080c03060a0b090c0304080912100f02070b0402011103040b0406030203071704050d03020f 79
    0x6089130012038064981c14002c07002e00017446182e100740d40608021039012901031901d80f045480e14403030420604021a61130404c03d4015802c0715044c41d100c5d8008100c01ea8a84140400e1b5014116040390000c900c8a261480360f411601901c5002c1503c10282155041010840800004041c912071030028400304002103000502918002c000f14105034000c50307205d0400105000f441d5000030465000c0c0002071070041c0b00c543d0002002000c0e50803d2802041119035000101d0960150709018500c03614000004142d07100003240600d107001c002e40448159a40b450490740030b585000526603002000d2201055580e100c000c01140d1050042520b90316180c25440410003c44503a6840a1541c0001d215005803002c9405407988613440716200b9400c1402a071101581110003910007030501030980311007010408140103aa005100319002c0c0d5032a0351752013102601941c000c45020000032800e070202c0d506030520b030982e40c0c01a60094006c0046440e5400241c00130740c40807030441c0c034805040c401e14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 101373992 1250 101372742 101372767
    0x90b0301080a030f020a0f06020f040504020315040b0907050d05180a0b27120d09081206090a050403021902120307030e0406080606100807030b150909070201060b070f08 74
    0x114001c107030702002050701d02c03036038140100905a80648001190481e0a402d070215003005200380a507a0042001a40c03102c015000080b10703c80d07070784403581043c004010003502004414405210321803d44007444489959000c21640140c105c80e00790128030f0034000c00000c2e41850b404194072294100390942c00e05035580080d031800c07100440403950350b030b200820071120035550350f1001c41a003024291017110218041d21141c44000703400c440c280c07880010030301e1070300c00c0c4030740c1c00483c661900300b21440d5880c204210807140d515012218a4041d444840c041084010345204640c452509907024004680002d01000010b000840c01070742e02c6410394001c0e4800030301c2803009040051003500e500d0000014001880142c4480764408086604002c013000700715161455503140e005040c7c601440c903603642c080282c00500c421a1203541000b07443c0700301c41c5490060402403d4144044400003010340e1044000c07802c0e82e105004e0020703054014804d01d400605a650030b012068400c0c10058106426050790 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 101375242 1250 101373992 101373997
    0x30a050d090519060f060906080c042003040b040507120f02040513051c030b0409080306010f0c0f080703020118050c060c0f0d030207021f0906050d0906050103050607021009050a0b07090b 82
    0x151429561745201c2001c0404030301c5075034000c00d031040061011034a0000000d0710b40700401110360050780c90380301310f8039248080c82034050219524000203440e41003d060840401c02c0884040740e00748030b008004200140d80242c1052000d40c403004000003615141e0901004e040058400f81c0f811b440d8040a1000481c24042d003112a42c0780d11000105005048008094890072104a4088d514080c403204c0460b0315601100ea00504c2801e012510340350700321007180c0030044044e001c1c0c03000491207a50820000301c2c83c01008420300960080c00360381014502500b01c180c813400000c0955000c0c0708000918181800540701030308540d400d450003915841d260b030303041585040003c00080d60010780c0d14114501042000c4020443c41b5a030074410700d2180e0090242c0c4128000c0100780080440e6100107581c0c00d81002100f00d41c8070900740919603481c07810300e6982000769140c001600034081c02c43c1100c0e41034030403040e0503500040108211240390326032001c0c6e244003809010030011105070100790f000e4030100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 101376492 1250 101375242 101375293
    0xc1c0b0a2712020114090d08100306060902031b0316030f140a0501060f020a0b01050f06090d03021f0b0f1201020c0f0a1a010602030304110415060306030203070503030a050d0905 78
    0x101004520703a8210000c1c21112103a000d074422011280c03c1c002d003c580050307c201c1c041c40f50700f00f8088980f10311080000359405680010022410541c01047c016184c2d0081d40c01042c070280d07690007800d00744200030f82c540002c0311001000624161000c5400c0d109410607180c4070003040000440c808541100c9030110022141d8400040e201c000410200b42e100101c1000c0345180e10203865294610340d00c00030361420610035944244201c6207201055914103003221481c83d0014044500c0c00000d240103512110156040e40c124407112064041240440c01121a0200010041342c00300c22940c003001000a07400700742c001c503076600744007101c42100100030a404501c03060000702503c40d020716048030504c825052078840320800c5001004416000000d0b650030a0b4001d131000e5987e5100400320b8014030031f0703401805e018030b01d00c0b900041e100e07095444101030740d0080e01034541c403079260300505550b44900310038100007a03020020b14039085855030088800b18481c038207554151615058070b500d08004444d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 101377742 1250 101376492 101376503
    0x306050402030706030c170601090b07210f09050112021303051c05090a0506091212130b090a032003100b0330070c12050c1c0b0a27 58
    0x209000561504000c584028145407801340300c004820580188401c1d504c036075440c04130f044803012940981c043c500c0c90016004030030f5090785942503803d10030700c04c850400801c0d02501c1400310300c9200c607109201c1310080d5121900e40300c0341e42d4070301001102c0c0303a20105100c01c0354035428000310035404444d9034140c005602070001019800f8401c140500109000410b1030140113080280d0342c03a1b5154141407808403401140c00740e0315003080502090082c0310850001d450b80c01045203038480c9c0c1c912035001d00b1101006401450344540c485030b1102e0140308001c00c4d1603001da0280810800502c0c0100005044100700010220407004000401d151280821941c060541caa450102c4681000c20641c0c2c400000c038101855444544801c03064848500e60380e28000300000250001441f144410010040c81c248070288400902e41c1071983c0c0f14050890b84c07a1059050120b002102d2411102c0510110307080341c0b407003025449640641e40140f80074203241d2134401100310001d01e102c10741d6000040660281 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 101378992 1250 101377742 101377751
    0x405030a210809060a0e01020d0f05070e0a080309040c140a0305040b060d17090f030f0303331c050a0c1e0b0d05040507030506100806060105040b090f04060f0306 71
    0x88441d200d616200c000d04003001103041c00c01482c8140080d5081c0c00070007103000010b640046404083c06807042d121180c01c0a4144140f2240705041a4440c07071286c0c0030f41d600c00142c14000410807407592020300c82c02c0c0fa03030741c0240111507207481c03e544800302141107400c0c108000041d40e225420240c00425a800210399180104018828800b002d6540402c0032a402680100d084d521011803070080240e0700100ca5001c03a40e030700e194035441e0446081c1da900900b240c82030401d01800319500e50084402003020410b0109890f00d407000031820700880f050402c0080441901882070201e4802c0320308000e408070541411083c082a0280a40000c0900985a28115600b8000e02503c1032803501450f400843c0510010400140010251105441e0080c2c0104403911141413841ca0300c1c00a810207412400f5600c01d021150311544c0c1c101d0121070005050b44c803280c4c0c40800540f6180650b1040354440b50041114100794a001d0351400d815080003000020401c1c0c541d24140c00140d4190000c031482a80c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 101380242 1250 101378992 101379023
    0x1140613080d030c0c081204080903070f08010b040b09160504210c060203270d06050c03040c09060509070c05010e1207050606090103020d0f0609080a1e02120417030405030a 76
    0x103004c0c2a09466017410030b6105180c2e0703559010702a00c60542c090a0003d051004581044100811030f819442e00a04031040d440c3c8417004400d4a024920461450750328244070380c8040d041c41c0c0101d01800400030140403259540c9402550300e80c40c051641320030890100004280c600c19111030b00804205040300905017140341c580024502c2e4a9003200c001c0d5030040c0008030b00450101c240301c00400140540c0c100c04000d000c0825080030065600802c030900340010009007100807006144160f0003408040f00c215a40c0d00c42904a0700340e40245c64101e0390070000540c2c10ba00a04400f504030303108034000158800d4100728141010645620b42070320110000c0c04109010f001c22500f80c00140444000c42c49525540c001024110560b000900c0b1125100f42517090041035480b0f07848040d0401d03190350351144210b000905900e400340020308201b01c41c1d0040f4469920001d19048071414104001d813800c1e06000342c04240090001e0b07501210f210030003010449403130a0007181c01c07252081500c00f00a406 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 101381492 1250 101380242 101380247
    0x20c09011d2d0415050123031002030f060108010b07030c080c0a06090b0601020f01051306090201050408060106090e010605030708040308060d02130e060112050c100e270a0e0601140613080d 83
    0x1315010314212040c107001c0140143c1c034085440b01034a40707801007030360b81000001011a091201c401c1790400003c2c40402000104005030400c2d512a00c001d030380300700c0307581c0c0c840c404461a802008030240005800c5000440014503140040141c000520300f00c8801c2c2c1074990b50441510104d5078100c0d03805043d08180485540c04008000500601100030b0000d860502034985181e07114404c013605090326558450296405103080340c02400e0b201c410b5495640e126440031702a00001d103c2c4d0064000305c0000090046c0c805c8080d68003520481e62003200a45943d00d048910304000342040d5800504c0014007401640c50110040e201b01d03c06201040785241002070702e0a29205038461009410404900310009034041011001e0030805c5070344100244400004032400d9101403a081c0e00401c140480320b00b00400c00241840801021801c28520355655013004250b6641c0300c1e400441c0d80c404001880b040b1400841c82c0d056403005020075080941451542072a60410b40c000c980d1900038040401c0a1507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 101382742 1250 101381492 101381513
    0x603050a0e2b091a030a060e0a15051f08060a08030703080402030c040504170309071503092f0405061203160507050f0603010303050c01060306060f06020c09011d2d04 73
    0x70341031400483c3d1070400c85807140c0c3d02c02d51152019810020009032038201d41d40c040742c080c04c06140034250502e0b02411440081001013140140700d9481c3c60000788600d440400c050020b0800d00c00191000076403d03007a20100d00141c61142c0c445481d103c0416180c008001400d4100d001e95212101402c0a0062502f01700c0494010303401117040004000101d0840030070580d28011080d5002d40e242d840729880e50408240c0d811083c140302401030340440d040d905400011900340210901710b40382c0b92490103000504c0c000b00c41c000c1e5560704803c1c502ca0b9841c0aa020070f40c01180036160140c0d41090000460560f03200803810404240c00904040034442e00300400710140030306940e07610940300e0b60070000700c6900052000901f04140001c2c2048048003c1d00804011039010b101031021300d440d401ca18108002c1d078001c071001440b071740a9515060ae0503c148504a940c46925840f66040d004841c02006800401e9500000001201c845852a50940c21007141c0a01880002142171503d441d01c0c008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 101383992 1250 101382742 101382823
    0x12030a0e030c0306010b0a0e100e01020f0c010e13020d02040f080607030e03030406050a0b0d0c060e0d020a0302040b0d0b100f17060a0c09050904060c0f0203130603050a0e 75
    0x9900c50b00c1002801c1d10001519415200d00032102900e410240f0800c0312816042c2e03045980003011600c03c500003507000038962031075280c00d800f81c03028100b1900c0003031303600c081c1d401420307000546401c80f1480c241031019003034503d9403d091015190091039120003060341c3c003e40c04140b818030000010081448144a0a41c01801500c0c05001c00385800d020965240400707040580380540d0307200880d21600c05944003074016200078214403038480503801d02b0b00e010461403081e00081021205540a03600d003021110001540c000c100b0303001e2501312b40074040200132505070542c01c0569401c0400c045824a0321035031140c9851b00800d0001d500700402c5813950790036580024010a0122565442500041029603212140300c4000540d6980000c0071a140340300b5502c501c3e000324042060005000c11504214003e13609511130034403003003044908980d0ba201c0c3c0c100c1180d0704a0b101405109517482900141c0d044113004802007003065a26031505c0c04c000944850f80c650760000c008040c06c54400c100300e110301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 101385242 1250 101383992 101383999
    0x30b0306070801091505030d02060f06030d080a020705070b0403060e0c01050406120e030d0914070509130314090a080105040204110c070302090c0c03071a0a06032004060512030a0e 79
    0x1c0c2441440074201d540c2c103000d003c070038a460309030850301c0311210303500c1c00010b1400504580e843c0040120194582c40140c80c0d0700d40100118002800b103040000384d8403120484c540c2d034840319565158094000f500115011582c42c0502d10000075025541c101500185020340000601002c00210180c07900c5103040945051110600c4100301c4e040d000030380386055902c00740c404581740b01c030f480700070381144076031301d080c1e2512440c041104042c41902c1e01c03104075140c1d80d8403c440101c4c1d2900100700008904450b49000c84c07800902d410002071042c0070700d822070341c40d500905040680704400109070909580288449a41d64001c201c1545414010905680170000401c1e1911084101c940c0e181c056030f020190051118030081107058100703408949000030400141c0361200b8851802102000c10b02c40728402d40d00c060b1010801e500001d210b08022179034485505141c1120414400c0750740c0502da41e00d030350f1190b0340b0b040014281d2035140d075414040074200c01440da5030001c420080c00101206001900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 101386492 1250 101385242 101385253
    0x60201060f0e04030c05010e03030c0903100b03330721090201020c0114070b04120221040306050711010606030e12090d06021b010c0e040f0203240103060306020c060106030b03 77
    0x200d4402c21040b1074000d40c2520f0718905014082c1011405003040c0d4100c0046440000108261100d18101030518800c0440039628200e5910b50b860055900c3e409100d94550000e0280503030300850300b40e003440400c036407041029901e040780b406126000d00031101000819540007280d4000021440b43d00c04001c0c59030000c008011207a00000c0d940c121118a040c10300101c0104510048003080c242c40540e036118407604d500789403070301d0030815a2480b901800050300c41d843c40410465100c1440d08842c607040b490981c201407641d12501e0181c100540b6030014000541001d12042e10280580c101400720358901095032480c0040d0140350070b070141801600c22070188401105983c84e003400410300d5401030000f50f01c911402e0402031541d410803484d0030180d03280600011050b1742180140074660000c48040080310036464124090b48401c03a49171150300c0f00000f80c091055841c034004110b00c40b040c50005407585d10382d0350b218202d074041c046040030f990200300100405940343c061034542e00710a4001c1c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 101387742 1250 101386492 101386499
    0xf050a05070c03050a030e030d150b070b0f040c0504050a0b0f030f03042615060103060f05060702090c0c0a0b010e060105070507151701180e0c101103040302090907060201060f 77
    0x4150700c02c0c0140040800c00c0000380c1c2d4003614480d8010448034950042901e6032800110108001040283c8aa819140441d480082d68080041c00d4a901541243c2e84400c15514042a070240341c00040c012261440740380804642901d6034401c1c2481851040760001c0c80c03c8040b0100300c00444081c40092007540940001000004040103580482e103950740c2c2403800303c034007001b01a10804100b800e81c641d4402d62200c01084803201c076199000e1842038900f0401181c0700c921015401c00c0078012950007100400404e401070501200b1681e000c04465115800c00003070540540c205441c0301410f403101c4402c04010b0128031001440282c0000017401c20a00e03080340380d529a03445074528414100741d0034220131100615402490a40518102c43c1c00c40c440c150f8440c074141190890929140451518000f034101d82c2d0b180000ba020302c11a401402c16100d03450014007111003022100c3e2407106400103100010068403010922030081c28514054000f8506181000742103540940c80480ca4800040040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 101388992 1250 101387742 101387747
    0x1113090b0405091f09023106050103090f030c0c090e030403030e0904020d0318050901060302030a0b2416080309070503060f01030c050d060212012403060528030c08010f050a0507 78
    0xd20302d08050700000c02c2410660000910681c5404e40444440c0800c2c1c42d1f90608000e41d90304c4061842001608000c02a2500011400c80344034142c01010024032144140100c3d02541c60024414422103038610b100d922031414030150362283c812601c00e9030022505000705604070484e122410401d9071420f4461815400180f102018908003a050080281505840100181d01311000d4040170707081c0c00a650755424002d000f5403003200c110803050f141a9a03c991407900c0c40c84d1600c22001d820031020b9541003240b10740d04562000b203450b139801c507580365040c0026031180095403007501420050243d1519000505040910040401d11440200d2005100280c000c0c2c800384107980c7c055030080c1c482e401c14a0300500a203d409400645214074034000a2401600d0030450401c8400380d4a07070b244d5580251041c0c064071071500640350700042541010148107105141c0004140c1c600c4188a880d035030b0b079100c024080c1550740001d0440e03511110f0002d424210382c014540c000c00c2c1c51004201a14180100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 101390242 1250 101388992 101389033
    0x9220b010309020f10020312070f0311070510050606070507121a010b03040303020a030e06090109021002010c09050f03120304030507020906090c1806130f0509070207060c061113090b040509 83
    0x40c034803c0170380c0a403403580e80b407082064900d504000580e0712014200708070085d01c03540b40000711100081c02c00091a41a0450406a0300026800002400c020000c0691f680223820020244c98021900b40542400310300b04000160080400f0b050076158680317603040600c3d035079800a22688210004800402500e80d415048a40c855018234005844500c00a821406001800d15040b000d1181e001403004000c419401040114821203036141c6200c80740e6004d900b6240840c1407000480e1400c0810407490501469000c068a030060581340e0000618500320542d41094409500040340807440c6070850230000351540d0040801c075a103091a20b4082103850aa1040e085442030010340840c1741c100302c0c1c407240180d600d4078a5900030381145e1600c4900003110050103104480c8951141c002203080f6500100c2c108050340c034581d80f040c240710340c035440e00f0300906000801071441c0d01c001c01c01d0384402009604514082c01c4e034800b0104030f0b88280760412050f10000791202d205600407855501491618200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 101391492 1250 101390242 101390269
    0x2030417090f040603210201050c04171e15090a0f1e02060c0a020f040e06010b071407060807020d0f121e06030501050609070915110309220b01030902 66
    0x48003a078401d4804082801d015040300c110380c005040000c04003c120000c0d03a82020005c4807280071345190b251501c103c0c01c1c5d44060b11035402086042006100c40002c410120740b2040c100003c4401d029924484138201c50441003500070305400c0810341c01c41c49856600169040381e00d14000f44046082a214405255566103000300781440410b401039840030341c681a084155001000c0e030b0b444149503440c0b80d4441c40050001c920410116540002c03500e003074400c540e51440c4030300c000c040c660300700855a016a0b11001007903440100d0007051420040b0200070341c00140149039240d003014184400003038a0403054155400610000701e034403c0c1d805038031902818400640460204803248145012036070a0885501c0d840450304104001c0141314054010344d016003401d80f84881c031603880d40c000710348003c040d0080d100001c29118400400b0b5100c0c0402c01e10321150788082d03915013404071300054150040349010141d001e8980c0d80d0101d50300c81c42d10076080781b2a02804c05000301b003030035400540c02011080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 101392742 1250 101391492 101391533
    0xf0c0d02030705070918021206010501090e013501020c0a030f0f020d2a0506010e0c0708030c030c0904051603200d0e0a0506071706040b06090f1504090501080d03020304 74
    0x186203c042903101415141b40a07005401001c0000b1380c0b0210545860090092501294658a0020304030840b00800e50485400d00f070b00002000c40d0b0143d000e072014440741d11203110180c007540410705006c2880100000c06505006014001552802410385007001c01d690b02800b0000700d14418841d000f08000441c0d10f024640107110902001001c01c071381304101614428000c18a8203c0d0070004d000820505868800b68000403c0e0780ea00c1002c4002d203d04d50300100740c010b02f4000700746401200f501864001c00c0103120182446903000108044030384c03c50b42240303001c1d098041c50300c165425102d500340c5c4201020304400d1800c0c00402e4501d642c440c15403d064026650f10200e00840c0003801305000c140e610801b89c03255420300030701c014046d8032103100ca00050950100841c02d1440d0600c2142e07145c0d01c0142c180760034580818100f1004103101d07212a0b8100b6810151702840200820052001c1d008104002951f5410300300141d00c0e011040c5031b03030300506104105002c0414203200c0200c0c90020000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 101393992 1250 101392742 101392751
    0xa02090906120304090c050409051803040303080a02090402030f0417030912072a0603062111040e031603020f060405120c030904021305010e030a030e10050f0f0c0d020307050709 78
    0x1101e0b000e20710300c5541d000000d02031a000040f0f0301703968444024011504850018403468641104c054006c02c0c1038098480c099000304030420009016200d0503038010440c420050810300d03504081026a032040b20700c0001e03c07403903030101700030403e0380c060400703400010030306d410b0840ca41020700940e0740110025019040344042851800c1003041c42d4051025094104e0500500c156502105080c4825000f00d102107130411f00c01241e10015120427070b2030040568400504030600c1d8440141d2840c1d0300380e102e50402d072601042c000c0382c1d00c104018180d160005081400d20466410b000742015070401e0800c500750400000c0c070012a100080d204810841c00c00c22030303590300014003100d01d03500c038458603590810700100b2080c2610f081004140f00302c5400380c940c40a101031010406460703c0c00d8a100401041d001d80b8520304504155213200f408c04100d007403c3e4500038500040c1c9950f80c010145100c0003240c0065400511142403050071f5403601980001c1d410081c49a6440352138524a02410000301d50300e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 101395242 1250 101393992 101394019
    0x1505040b04180f0c1502060f0a180c050a0803030c040605090102100c080f09061b0a0c060207111203030c0f03040c15090311060405030a060b06070813030b0a02090906 73
    0x60750b01182503041c1c1404012003520392890042c983c80035880054480e40d80d03441000910300702611903024000e01c3c07035015102582d542c403400d14944601900080403903a55400d8041c1c1003040040c0056014029900714100364680b2040144901c0c058200c055035070400e0091220410030401502d0603101142082900d0b5411080100e2034807a41b40c0c980c416103424103d49104070354104214500980c1085089040c5650300032025541da041a00e07485aa88030030b18406180e804030074098254403c0030301d05a0740e440c00c292074034801da0f0403403c4241e4800f10a420840f00503e080c820b480041300c0c420002d03504601c2c0c0240c20341c107a030107210192411600300000080810031b0705440d410250080398102a1001c21040d0024403441841c0003ca440b002d030304e160200c0610b0003106950444900400134142c2c20096035440002c2d08103072040d941c00980c14010342c2c00054907400604611240c44440c440801d00c1c5003069001404068100300d40c0c2032040142c200f054031005441d65000f4002d43d1100b0306440ca = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 101396492 1250 101395242 101395249
    0x12050714010302090d14010c0806010c0b062116080c0a0603050a02090a030b041b14041515020a0b0a050609010e0402030703020907180f0609031e05070b09131505040b 73
    0x30344070011791000c2c914503a0300401c01440003c030b48100040b00200001403261509844e00c42043c1d80341404641c0c1e5014a000140103101000c0d03200d02e01920801040c072510000789211a02c4011000143d001405102140312080d0f903400d00a10400f80184203206018010620030040c502a401c10141c40d40c1c0003c0c10707501c098041300d85181d0060041c0740c0740c1e40d60f401c1140b0000c9040e03404855481015000301070f50b00440a4a1007a1b1709141c0201c41c00d051141c00700320062944801c0e116801c03540c0040080e210b8425031070360030900000d030007600d40c00285e0314142d83d030000f000b008082064030301030070702040e52900841e95054404140818155850324000245498040c0d44000d41c442010000c202d503041e03110a4030044014001d503804801a04d510903001c070745415000b484000b42c1d511701d080000c1a80380030407500e40e01c28000f1080020100342c0b45c079414108140c004034501480000e804580f03081281d4001680031070440200706c030300015100183c071400507108841c8100d4445800724540d94 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 101397742 1250 101396492 101396497
    0x12160c0302090103060506130e0c210f0304031a01080604020f010507050d05040f0501091406160510150506130603021e0711030106080307030504150e060a08010f12050714010302 78
    0x150020203142c2950b0792454014017a11080b40e9042c040d00b0001c20110554059014002241c020304000d03002565421050007024030704030f264a0100a15010010a52001480961420008800034596031811410024000445038948684017054600100040c810225016801550450711351202d03c46100c0100d4850090010103412030003078046005080760881c0003002140d040c51841d904603940e07031340155150f031290301c40c40c4000a5504007013401440c00c440101011500c03d60f4258502c00d4a4540c640b034000e45c0104246450342e00c00103e0306039000c9001e10001400101d0300c2600d0b10043c00103940101600788222000c1c56004103990030130000c00c0c140b6016101d4030401540c1c0b900803d04010110040350369a00f4000e51074160085260207011084901c4e4a4064440d9403401d0b01d0301c0d01140540302c88007213140c100050300c1c0800715a1740d0303024014005040c6a6888650a5044c00c011b85032f018025400844405a56486035000032800700710700017199800040410102c5800d001a0040e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 101398992 1250 101397742 101397749
    0x141f06020c13110c061504060302031005040501020c03030c1c09350a180f06050304080c010b090a09060507020304180506131803140f030c0304030216060c031112160c 73
    0x8002040c04440d5150000f105880f03412801e1b00900e28600703090070b10085580b41d0001941582100c2201d8442d0700d22504400d07000362003980018500025444141d05540040d41c0880300300e03c0000d03081016032909e20304141d84403000882048082c00654401d034460b075144144c1603104030590107001010303c0300080c04100e1050981015600c82000e03070001c185140920440c199030301c20820200d4038201502000e400e90b19151035051440e15142c854040c150000300300b5084a42d00c64440609603140d51543c03901548800c42c010410940a150502c2502c60050020085600c00c4c481004840c0150154902c0311941c1c0c0070008403503c0d010081502c403000b026140003240d040102072034481c041e003001c020140d4002d03910b9083d0841d00c4080716090f80700340840c0c003e00300c6080c0b0208103080032803001035411a2183c01200c010001d2007000e41a03205040c1d02060214581546560030b141e00000b034043e22011000c058064414180b8500056000d160212a0b011902e14410410410011102c1c40074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 101400242 1250 101398992 101399021
    0x50403021e030d090302040f0507020a02120102090409080c010e0d021c0c050f0d02060c0a050a0e04200a23030106030b0321190c05101a04141f06020c13 67
    0x701a4003d8041c1104080c0c0c40200d004515240002101c0c00300c5125440c002c151660141c03490300c00c25001c0102c8014000c0d0071000c02c2d5401c1040e4003066440c4d01c100070030644112119900c1d00c0c207000b100f030f00f16030b03102c3e24034010707604422010b01c0c0055000c035006044020000c10304014501c4240226042d002c1c10a0007001d83c450091513500c1c055000500550a046076400c82e8210ba0320b80c0114092030040e507620002080701030104000003400307924021005480540000b8424440c55440350700c0a01d921164088200000ba8004840307030700c80007480355204004612250a10a030275034880d079210520540301059500d03508890b09aa003803141140841c4180c110080141d1200d92601ca2580154180c6000d003c07141d81210032180a2502c0459483e0000e0290003214140a4000301405840c40242910b121803142a54039640f644100c402e06804030400d01c0c2036190010a0303a1080605c0e00f002040d0465841c810025240d00017400782c20300d0b10544003075500302d19004420003e055040c0c8840c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 101401492 1250 101400242 101400253
    0x906011b0816060507090602030702061b010222080706050d0b031c03020301081935070c0905060603040f060e030909070e030c0a0f141801081605060a050403021e03 72
    0x800c405403911800b1250207108100010344030140203440210b118450440943c005100080151038894040c0c101c541c209205286442e0b110903009007280c1c00710b0564056684d04282d8900a030850032011030281076104010103c07141400c4015020b40a012004111a921440303010322030740b010b00001000e4012107020310004107410b007028003c0c2d0424014030025128544102070302074440740038407141c2078200c011030341c03078400c00d00e4066410440d60106511072003410b590044500034040c000e150641c017580040c0c810900303040000c02a2080501000d2151400703105100106080c1d45266071016402000061505900030740603045002d4162501c0d4072074903040400c1085c94025252521400084017955200c5032070100b000741400950080744a00c0d91000d00500c0781141d24029807e90700c10080030350402c004084540d1150003005d0300200c0f0550840c80c00c0c2c01c005540742c0103003006000c0850341e01e410a02c55440051090049100183c400c4045950010521419504605014001505640b1f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 101402742 1250 101401492 101401507
    0x6040909080d11030901050907050d02011115010b070308060907020c10030f050a020c01050f0c0a1404030f0302011d01060e0402010c020f030a05010c17040507051908030d090c0803090906011b08 85
    0x2151030700203c485c1003085d400d00c00004e032190b6002c91038005407200100800b01c80f80d031603001101c0200c0103080074a10381c4200c8420000720b0700001c4120b8000c1c15a94032050742c13203201d841d0007402c81202918250280105400b4402d2090b0080743d500024001928410340d88401444201d01611030104503843c414034040c24464a002c0c9070f001040c200343c810300203000580b80c02c0341c03056480c0701c100c6521880741024080c582c810740c41100c0300f03407a580c0481b05041c106070301c81d12800f68031001d240c4101c016070b5484d03483c0c1200c01441b111448070b82400d28002c1040b00d1406003040a2010b0003000241000019440c510840da100781d000c200c860030140440d142c2c80b0007450094001c0500e281b030031000c11000406041400255005075115582c00700181c4842071904051246c01e098411549103000b0754418082a000c07401c1000d0145801821008a855001030400f200c000034560815901900b08110444164a8010455802800a1808411061a0741c000300c840704010384005054035800100c44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 101403992 1250 101402742 101402771
    0x240f210525050a080c0f04020903280b060102060714030601030e01020a08070206011e03060504020d05060403031e14130501020c030705030d06080304030b0f0c091503042006040909080d 81
    0x1005030b800542da0501c3d100e495001c5641d85805440d58180c0c000300c0e00d400030320309051075000390441083c080c0450308020580321001d010028007014100036038060440b0718061007511650150040e800b80050702c40d07420624001404007881d80b5844500c000c0000104425900c241c0c07011003040140300c02107440b649006801003000f1801c1d12200014801d900010a045250304200f0703540016a58100100c5450351751200094400200181d0307120401e05d03400c5000c12018886244120702c01e07a0005840d803421480440c5135425250109049880d007441c243c40301030108807541c0c1004000f00c000ca5140042d14003d80039100b284000390003808082151420807200001504904c81c2081c014402c198482e08855628010fa22020b0400c85854011030125040700012541041c0d149680c50725200c42400400e41c0100c2980f000000d4030b40000400c401c1c065001004000d2000c0291315940390551100010001d005a010307000358242c1c2c80c1c1116041044001c01c8440d114810031052040b0340521080b17 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 101405242 1250 101403992 101404063
    0x14040611010b03071d0907090e03030109060b03150910030c151b0c0303050a051213031d1e01030e1b010f0305040c06030504080d240f2105 61
    0x411201c0d824800035803040e1a002c00c103281585c0040d0311a16050554041d021321844005e800d115490207409004a03411150b4012034a55200c200f00840c0c0c1ea5140140140c1194082c0e0710501d45008248240513518118640a12441100310398804150301d5a680041c220700f2107510040400000d0800060780c04007100c8104044c1541d911440040b81084140312030025404800420803901150280f0010303001e480581030b501c1292602605200c500560040701400c02c0d190742032030b07a80f9618210304041c0e001c400c6c941481601121004107007501c1d0040380441001d4458032204030340d20301c000d00040e48250302460200b0030743c60031154100c0400d2882c0e031150001c01c10380c40c0014940000c50340498000c0c05860b00403640400010714a40c540754080b001064007800407075218408001c04a80181903000308061a9050b9200c404912403030390603080d01100503031090041c4207802c4004c200c2c0c900d003041981d208440e092810540840c0d18600346040c02d040d0100c0c119405988407440e2056140243c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 101406492 1250 101405242 101405267
    0xb041112070501030b0901080a170f0a031506110a0305030c0d090c060807020a030801050103050a0e030a031a0a03050a060f140c03071403012102040e1002070c06080105130c140406 79
    0x80800819a00ca002c2c4458030109004882503540204181000111002b00d0a66800d00e000b42142c18001c40c0400740b03039107500562a0350b0002e5201c5015141060144480d54000d00490500c5401181e0352010f00d0303140d90030340e00080e06200020001401030300b00181202c051a0300c00c081007044c0107c46c0b80c541403801807405900000307002c07000010f40a40c000212801d0030360705903d4011040e840e2500441c041d0038024401c0c07074200e44901c0943c414040400c0503110500c11070304c01050241c600c41480d4a0000d5070030850384119865001000070400c0031814180403604400c1c081160609094080d0281050994600c8800c1441d0100308900712902c4c003450280206640740e545580d500c0012840c1400280a401e00750750508030001d40c0866021081e0a41d2440580040f512941e19030010f402c000b1a01d040d20240c40d0000f9004082056000240f0f0103024142402c4006504190104102619244d078040e58036581d080d000c0b2040e0f000d00350400e20010301101465a50b138545100808041c1c2c0b186 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 101407742 1250 101406492 101406497
    0x18090c050a03060e060a0519050405070b0d0b0102060901020a1205040606080d050a080702030301033201020a18080601060c0209041a04030302070302210d110c0d030603051006060c0b041112070501 86
    0x4510900c255000b01400303060210f468034142340c807a04c100801481302400c11116032045400c0020100072680c0517001110705c0c41e00c00504c400d0380c0700c00603040000c01042d9203a41e9104001c1d400301c01c3d8000c41d40486050322103800241e0750745c0e0f80c0340880c010051034015400078442c100c3c645c1070540c0d114005190480f4169103407202c0d6154451700f41d94a00007808000e1207139804000c4c9000c14008134401c0c0c0300082541d4860903501840003ca03508a030b22000700c02000070051000b01c151b408607980140d004204003002052203600d403d200900d40820180028464480c0a001c00c0500c00e460f194000300d40b40700c030394032096801c243c40c001d0b000f5840800b08801601800c0d540a1550103c060b50b0074145403014090b0307103840304240010f4011702c0c521142c00d9100310f0911000130b8001c810808000840c0050b200095400e046080440c6051300000d903a080580c1400c0091081642c810410301505501018455042c1c65a251211020313142403182c0360070103145070002020480c001800d00c100c3e402038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 101408992 1250 101407742 101407753
    0x705010b0109120f150f0f050601090b030108070b2a0c011b030e2205100306050108120403031206031505010f0803090609120a020d050303010305070f18090c050a03060e 74
    0x10301e441e0700e42100d980c0c40644950381144400d03010404004581014507502000000e220424000c89001c984e107c025009005994800f00165560001110320241c04483c004506640c50494070300c4e910541d07809032201401e00401c0350241842d21140c186040c001422240045035900500e01d0b42d81d90403011201d000481c0d40050007044400c03070103500002505580c6910f0a180d00a040c40700c130b02c1382c5a24503101004410901e45c005a25485214081c072078140c25507a11520b5030070490305031501038208020301d42080c8440c0c2c20b200e0301d07601141c3c01c0741d0340760600d8940c44100f003007840004d000c2070348041c296074800040358a40c6c20b0310303912481c1a1082a8048111107403980d0200380d032401800030780c0c0d0304548100141002850840641c2c048200711100711402141254007003651004011012601984084014801c100e8148001c1005e030501903180200a03240c51812102d20f056071074140103040c0c0c0c541580c0c0c09e010758010200c0c05010081c101c107500541e00d161800040c81d03a070301c0409050141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 101410242 1250 101408992 101408999
    0x26060a0b0a0e040b0a120c030506070201020412110d140604050d1e030506030a060606080403020c040519020d0605100504090501120206030f0a020706090b01080d0c02031c0201110705010b0109 84
    0x185003921a24280756032048501c42d81c01c424003000305900300303040703038088590800028150f01d000100308105120307040f2002610318614003c0c4c40c00364068011801d59005000a208080c80e4984c80000751340c00020b40140300400c280851100c041c0c0c00780152194011400c0b03103e103180b0014601d07004520440c120780c807103030035454100c40c01420300007500b6030890a036400c00c0c00c540c07098004682118000f015148964070558501c01110703195441306000c503881000300414140c05010200d0301503400e0341c050155260810070291000130111200001650100390088103055991040010b803001521754500800030381c8000d00f82e0340081c4200d040d22401c0c200049824800e03242c0c0d40c1c0340c1c640e001e081e90b825500cad10740034845000b00040c0011040340d0f0034000c0e1000318400c3d0103030078142c40c00b8000c10a91541440078160070b100c3d010180b50240701d182e50700e510041e1000219261200f00301c280b02030040b0707c180c90490240c66015a599040030780071030208244801035221404180e801d07240d205680f641c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 101411492 1250 101410242 101410259
    0x3150115090308031f0b03010303031d01021908040609020a0e0105040e0f0604080c031309020301051e0d03080a0b0a08010203090606030f1005130213050612031201050d0326060a 78
    0x121800020f000d003005101050103080561454019841152040401561a989a83c0042e04241d201303900003503d820021000c003540754420410400c08000a625010001901008089001d8140d03410400700e1400034007030000c9507102903003040d8000c10003600f040e46d5004000f03000c2420700420303110741d107404040d01c4400e40c00070340d05000403c140c0103420b45039950b44515155412142c868401c42c0030801c0f0281e8101560000d0b403003e04403e50300140c803941000244000a104255480009008058a101c07103030380b09070000c2405949850190050781d01e940d076040c003034100c0341100e03604a0075042000c1104030064001d18803e600000840d0702559500c0c040503580c2c880d4904003841c5402c0040305601c440c40a4010551151203111002c010f80720960200b1078034074500c502141c40e290f590041c0105490101c50344900d844103400150304190540c1c050b5040f2180c188207540c0704400001240c0708160162500c00300701007410125006c5409801c1510131080011100e8510805044401250540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 101412742 1250 101411492 101411507
    0x813031b1802161101020708060703050912040b0724060b0d0b03060c04060c08160305070b070302030132031c091203050a030b010e1201021206090103020603042003150115 75
    0x94608540720b000d40c0e1135182c08403d40342e00d459160442c0504200801e10300c90801410707014081c01c1e50000b0702031030009496410518030000450740d481c0304100401811800b6810340310180d401800b48140b1000d43e088542614003690f0610001605000c00050001c0709a03002e0440342040040510000580c441016100d40c01122803a40c80941070000780070951048241000d064852004945000c40d01401c1c0c8281c1c040c254001c0300041c1c40003800000b00b0807030540854200d20103080940c1154100f01c45c00c40100400e500e9000244c01c0000c8c5a02305140e8803061070088039028040d6803500b581220b8900514606d0421000450851080051005201c0e640e0005039a050b0703a9450412005210480c06800f00701d40190400406400000f0a03070342e0184001a021900b000050b0b58000b04059000e07054030040c801407041d19808010030250b280c00d81180d9101780e0102d17201602c08001d84507250104807610030780350144905041034a84c00c09165800381610a0004100c02042e8255001c80700c42 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 101413992 1250 101412742 101412757
    0x6020a020f18070c06060306090c060f14090f0f090c1b0c0603040b0a14071d04020412020f03070f08030304021e01090e060f040f050a0506010c0f0813031b1802 70
    0x21800310b000241c2d000e110310400114a03108620116907180c1e40d0302c50754107a40144c2e50603100d580c6400c0d01048102d07006241c032500d0919508004192004508070f9082c1e5018951109010340420080926030b1782c1e074016800080030000b040303842c0c1c070306203844500f115800520000d005080d00d00c40b0100340c504e00150103214900028415451a40d0b04ea41d52116040c0c064916104c254540c2e50f091109208000c0c1c56100350710303698402032100203074442c00d071101d04e4038030a05020364810001800a0705101440c1e400098054509801410f20003010924020380f40d0b202c544109154100441c1c5400c01100840c040e50003180c004003010cc82a1100201c0500b0003900744c04140300d203c0402c2803080754000e9543c409402481040c680130054042003d4034000d0141200d001c1d81c1d8010084070402501c5200d41054080c42d10005a088958403004c50644044d13000d88112404140c502c414283c100c0010301031941f1070640115640321303d02c5614080072902640c150021100606080c00940e8400c0c1d0708031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 101415242 1250 101413992 101414029
    0x3150106030f090501020a020d030c03200c120a0e011d090a0506031216060c0f080c0c0102040902040603020a03060e1b0d0b09130507080304060f03050a0906050106020a020f 76
    0x12a46040800d500406000030a40661500c806240000c60028400342c020200240c0180400d5008590010101d030949070206080c5481c100c0300c242108050485050071030300c1c030480b09603218141401c01303103010f07038511031911241c00c0000c80010b071302e601ca805604511400e8032100d00a03c103a03501c2c0d0b920107401203010781d080b80c40c80c400560005007580140340c0102004c4c080e03038502d01010150041c582e0103000b4210300d40034541e04900410441d8481d03440c02c07104600d40790550514510740100b10100103418010003800c003082c0840308130020f6040301c004110307050085641e01d54170440a0082c0d01b00024803004a8a0880f0000e9404410001c0610581c59281e02100c000b11071000880c0d15003100710305801181c0d841003140084d0700e522030b07828000c204c1000c81c4c143c1d0020070318040b440d005454100c808150018001082101d07000164042030400c18140031a050341c030300380040c00410001d000078144ca401d2100004010f41c000c1443c0a445c3d009850304101d000c1d06000344a238060b032110030010fa = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 101416492 1250 101415242 101415283
    0xc01051e0c130f060302040e0901020c120706141602010c03200a0509130b10020a050d0c3e0301090b04030c03050c0303011401080601030c091e0e010f09060503 70
    0x501c1014000030700300d48551204030700d1015140c000d2084030703410a0304001e001c00d60008062000c241c8070142243d1056101d402545040318808005456500720f41c3c10712031030f200200741d01c41040b0f01741c2c0020384c40915414001d109440c0441d2a100510700000c03c0c4805546091800c0c1d025610078085d01210305030000036400b04001c0e0348000d1403503521502440c010030405000c85680d59403802d10307a00342c010780000c010603811691410400300003803102c1c0b2282550700240001d00011001314009030000c540382807001d20034005040ca42e82e0001d202c00012840d000c011075030b84102100d02203070b0b10b60346ca0b80c509107080c030a50398052500302d6074692000b606e0113501200080021788516051800c3c0ba119146c03450802c0c400844c103a2a43d00213070004012680c410356661307103550740f103000e07554001400d103014040d1450b02803020744a543d01d4090b2901381c0841500311440d500184021074010040d4100381c0e942c0350303996a242d80c14044030703000c0c0490040c20504005460316001034502030361030700f207401d015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 101417742 1250 101416492 101416501
    0x31305190b03090c0d050106090b1903020609120f0706020c0d051b06070f030905030111040308120a02160b010e10030302060a0c0201110403030c0b010801180303020304020d0c0b0c01051e 82
    0x907070002041c41d01d041c45140c5944050744c0300c202c081700503203100700b001140c12414400c6034429900c0301012540541c02420200300391b40c1041e104441229010345095a6541c101004140041c40c6800b00340298030420600302c0072803034000f80420840f840b0780d0950324280c82407410000d4480440c0c00c09455035100710714010b000021f680620074242d00c000c00c024a030405aa4950280b50744440d4140c02081301101c04000604080c01052107080641d03aa1500d4142180d5807401680103043c0282d400003042c0d0001045100e290341251044203143d4004200c03060f00f07240c02010501c2c24000c41c10682950004200d1b5001d420743d40c5000d80e03a00d60040d100c19500e03901c0d808020528068114115900c2d51040b502d81c2d80c03010020710107580641d580c10301d0328599040003082004181c0c00795006c0c5c0e00d052011101501c0c0305548001c10b0b0b031716140141c8e40381c03940e00000d49058040c034405003144080e2140040c00308400002092804491402404103584001c111a9621754181101004000460024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 101418992 1250 101417742 101417759
    0x222080d0c020126010e04060b0319030f0923040608120702010804030e0901090b09100812090402090306010821030601020c0f011107140102010f02091804210203130519 74
    0x980c003075a010340e007650413041c5030340b80c4040c080083c3c4c031440300005400180010301034680a072003c0004264020f202d004e4006040c400356810030743c0050100411001b20009903840b80b80b182000b040c440c00140d400c45080c0a40c1d4510f0948284000e101d1890946c00142091000c5941c4481e107000120301428131149030015a01050300070070403800c01180f003940e50104c1d0780380b507011806003000640010340e400d00c40c4144410307020050141d108050072030000304003004001403070388001030541c4402d60300d4000b2600420081e0189905881d45030181c6c00c00411003850018009070109540c01e840c140518000c4003107000c502c020340c0c004d801a000080755178001e0900d42d01056480c1c82c10300d007421500c0031501400307007401100c0d00b05007002e0700701d0f40c031180342580d09000300f8602d0325006904520b4100705200240f102802c20200a45010940000070180040f039a070740d02d4010342c03003403421212244450000351a0b034048048908440d00c42080480d0600740032282014000ca01e4416051035820450365 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 101420242 1250 101418992 101419007
    0x30b09151809010501030c060c020d12050c01020706020903121e1b060a0903080709060801050d030e03120304031404030305090d0c090c020f0f0c01020d210222080d0c0201 75
    0x84035000074140003100a1000184030840c4204004030001603994194580340181d0081e075800441044002110400580e80784103140b41c000b03a1102005c949056440c1003900c0c58081c80d400c4c101d255101150f00070620280750024400d128003202550800d000101440106008403594200c46004102990f07014824000003044d0114044100350b14290035036400c50301d0504200c552000040d01d03004610308154021200c2c40d0007401908164060030f08100d0020309003801482040c1c81061142000c005240c0992034110007400d0240945040350f64851400d282c0354003d5404a000511ba810814030b10300e10081540e007500d905030781d010300c0c0c02829401c0101d030f01a04003043d19034401c558000a0228074034819000410b90b140c026100098a01e08007178240001c110380c8031140d4001521580690f03901007458054500c1c00d0070200a150828840400c1c3c0583d02d0f001c0d501c11785e100044101d40884448088181030910242c1c241c0c00c140c41d07452580d01e07599441e04101c04a4410202d000c0150b004145 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 101421492 1250 101420242 101420281
    0x7030507051009080a03060e2419030c0f290714070f0501030f0c0905011b0605010b2505030a0509030a060507030c1e0c0201030e100509010e0c01030b09 67
    0x302c0b1480c040c2ea152200c12a800e054040310700c003800103580700d000d9406008143c020000d1602d078003082e142200101c01c04001a05502520303c2040714084080d076a14000c51007244ca80d16024107840e40c5a1810940c02d48242c081d07140707122072a03500040d95820441d00100c10780419040d800400d10000c01d407a4498102102c100c8082d10030200310390080f003080105c28001c00180c84506400d0f45032000140071581000e0512404508200c0301881c101d4108154500b100c40030300e0500450310400440d108282c06c14140204242e05001c000140700e040c84000d81069a10401d08410200c2c4032114100310300c00c280401401c41e04144080b4204600400260401c0e91014091f89c6070785c4600d5803901d044a80450350302c00440c0ea60100c68034500d070300070808510303004865034010b0070403030402010f0003202409400a041603210104003034101c1c1d050021079011345183c0d80500140c1800810707140a0041c1c400e030f400c454030404c8c40551b403a43c42170141150300d0001520034901d50301c2e03008062290261001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 101422742 1250 101421492 101421503
    0xd050306041d07150305011202060f0d0501060c1e0507050f0d050109060203040c1703070809010504080d020a03021605010504090902010e0a091b08090303130c05031203040c0e010b07030507 83
    0x751281c030024049a00341c1042c07001c801030f24046081c44619810006080011420940b4020040c4800c01071840c10748582a01103401c03540390042c1e0045440d691064910f0514940d003030000000c1c0003500144000c4e501031188143c1041c003000c169500042c400f80f000f0142c140d41c0004410801030401001841c00d141015152403680d110545400b401e46601d039030102c810355400010801402481c903051005044c40340c003100303a00081c0d0644541c1d00e005414014005e664000b504034491381c020401c440080042d403040c2c840074400b8001c041c0d181c040c0800d042d800340c040c0342c5040d920f48444400d030906840d4141c50320785c02d10307050000d00402419920000c0b4140143c000312500e103581d0380458900203040d203010124800c3c0d4440f901b10300c81c0a2002160701442605001c0c070100c0140401501d52207407040300040850089030070700e8040003100f940882d0f00742c02010582c4400401c100d004500c280c0c0150703110300d0b4003580c0d10500703400b95509100d04404180207200b0000002c0c4240b000b040740d01d0040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 101423992 1250 101422742 101422751
    0xa1709030c0f0309030c0f010f0f03060302090702010b040b0109050109031704090203270102040303140702030c090c0c1e060105090c09030105070f1b0809060c0106030b0405030307020f030702030d05030604 90
    0x1201d609150031500000e0800560010518085070b26080003a00319958040d00c9045000c00c003180040c0c041803400c07400c203050000040700c0c180041d2082c1c0c000001584c00038407079031031405d050002032300a0003200c86260150b401d107900310180e940100826800c960b410396a81d919549142c03501d80d40744000e100000144042040300007408504e034006580580354151504240c1c4641075004903803c0320a03000d801d000d9006010400210f508186180003c40452803000d540c0e5480d0f100003410808000c150a030301003c1681880303441c48800000d4000395860b5411180c58003020204954042e400c6e982c3c5281582c0190010f004a0504441868000711001c181508114842c0006825103404a030502d0020341e20740e00740c0d007000303038045000601050920f110000c1c0301180d8894460622680c00c8190041e80b00180000b00c42c4001d600807002036070820102629401c3c0b902c2c1040d1298810303100013005100705803201c0301c24100801110031042d80180100691500b80341c090710207800080006520580d42c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 101425242 1250 101423992 101424007
    0x12d030f05070f02060106020f03120702010e010f020d0b03070f03021203120112020108010b030f0403031808180306010f080c1912030807031107030c0b0a0b060c0d12020a170903 78
    0x1640034950280b11540c039201d40c02035416034001d1034903070140d00400442d40481c0c000385041d407000c81103038440d0405144c040304556801406901608403503d000c54150301c0c21000c0200c00207a540034140311042007600f84200b081c07800406d55942c0890081440d901c00c0c14404200510f030012110001074125409d503410590311008071104d00109910004a0002c104030820841da0301000240c050b007040c10b0301c582182000c0c480c0c00d2081e90014402000c2c941c1d15032009580c00703c04904030120551012025594070700030481c1000d400000b103031260203441082d0002c2000e19041180c041a100f850b8007c09000d00da01e01000030840244000715002014000d020583ca070b041740507007952600079120700d034a130b05140ea0020700702c0700704003c1d00303002040921805c0300182c0d0001085075110b03013081c1039120325121240120000e091400d556a0300c90000506440c00750004030b80c030b01c0c0c581d00c540c0350344044400400003003007644a0540088001211101c01082c400355040080307801107100c8080300d003040304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 101426492 1250 101425242 101425271
    0x1002220308030610090602060402090903131e050909030a120605040e010903020c220e01061212091a03040b09070b0d020c01110906030c031b0d09060b012d03 69
    0x240d42040d5040c500020812085003000c1141e169038000a1509044540c50080020b4903001c0282c4003d200b0358003440800d4003500104182c1d000c0c0c0d1064058104616a0351441880c411880c1c89210240d4900f20380008492808948042c4a0038010300594540681080c085606051219042400b240d2360711010600e030708e0318810003040d50707a44000043d04ca48035040191034003103044030b0079101c2c3c1541012200c000d441c41c0207148240c282e82d0701c0404c202c004205224090704d5281c001a88035000c1107144003e0189850726522480c0554680410140c1c44070080400b0521528100d0b15240c020030218001890802c14180c1c030900c4003095070000c0d916805806002d501c04130403030642c503401080b0891902401e200d800c084160030141507182001c5503000c207502c0d00004000b8480b05202100054608003518406e1200c90800c07941569100804503c0c8801880d0f078140c192040e914088030f00d207142d40039552804000c03000e00000e446640d180440410044001c000ba00101030710b6072941017a860 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 101427742 1250 101426492 101426557
    0x2130c091208120f150a030314090a08060f16030c0207120203030d06090b040f02120402040b01140c060f0901050405121303020a180b092202060f030a050a0605040e1002 74
    0x8103618103c2e15103051011154843d010001c00491003200c10a1040000a40004040270b900c042005082d890307050000003d600070805a0000c0414040c045c00c001412140070180e40c03003100c800044020040760607008a0131035106c0b088050240e80060350a00c80c100b5080f60005001d803008003124030b0040c82140000594140ba8800014903480c0c04040105107458040c2a907035891313001085040c2020626006240b10011344042e000701d0383c509a00c0c0c4964410038840b950785041c0a10030703554291244015a443c00200c600000441000f00400c540e001c040c068180160340100042c0102d84070601c43c4020ba0384012504881403c10780c2e800801038031000340c0b0300021309104980320002107a100c030441c00d80701941c46651107004948108441c07918000380c2c40d08204a0798a01c01200c26583c40462180c1c0300b1141c11500048012040003601040744c3c10052090b0150081481820303910b0052005135081010049503a410540c0d40241095055018100c080d0300700240041c460340d40100d07a21050f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 101428992 1250 101427742 101427751
    0x20d0503121602031615061a07050d0903020d170c0d200607080115141c0b06030c070314040306180614040f02120c0901080a02130c09120812 62
    0x14111020442001c0c00428080002c007001e0002d5843c044910750645010580141300170030100d0080c030602d9040c4031650100e8050503600460071002e10300d24004030f950740c000703280c00c072002e11903105490000b0b480740c50b13043c0450341c0c054100e14150140c0e607107034044030000404c02401e00f43c06120a290904040161110160340741c3c45042e446214040c409800f09901100d1607469485102844415680801c03400d0441d10965508800000141c4040750040c00300f1900800002000c108007981110107041e07840d00244409042100e21406002d003c014001240d0b0a01c81160510641020034001e0020f0384c428074081da00700c3d281c91b4130380c0e99150403601c00143c407007400c0c9c15403006401001158410225801c2214080100600e402c1d03880141040445800a0003071210009000a214042010f10412403000301411010341e190b10b1403a686070b542e80c60582c0704110b0b8940100c1c00e0803141c49510114280c0342e5506510600b00071000c22400305528007150a248100030803001401000d01d100d004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 101430242 1250 101428992 101429017
    0x11107020f0d1b05040e010c09271508010518190606051201051b0304050c06180a0e090706050c0307120903060c030204140f0f01080c0c070b0409051008060c07020d0503 74
    0x1450b09100512044404250840b00303148e1502503c02c91480e0440f0f041d00844d01d0301e000c00e220320803440400003000011350307400510250504036000c10b1800000c14030300544252000070046030391130020030740015612030310300e84d0b450b0801c8071165442103507000f00300c01c030310f0144201081066071200816205400c2c05a0040f1596444041c401108a11000f031000100c4d4110024107608060325010307151354058207818801c4c44009001c01d80d0400d044441185440300a1088180550301c0301c800080309000c85010086004035600800c4050081c402e07102601c0b4114000c6040003020f0352a800e960f42c004880105012543c8000400904240600c000030304550ba00541c0f20b82c9400403010700c00300108401e82c402c08101c207000c4250f4464407001710381c5c40000d01e044101da40310714444034070318410054109290700868102180c00062440208100c1e001c030003007000555201200650000c602d4081d40d840d5401c01c10200d103107040c1802c042d166581c00200b5070002c68540340d441c140703507601810001c900c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 101431492 1250 101430242 101430293
    0x118060b040903081b0705100e190309062a03090303020f15041101021207080909010e010b031f0515180a030803010608041505011d01090c0f050705010906110318011107020f0d 77
    0x10927141c14003c0c19a8905502d00420710141581da01410140450003084200718451265441000f400d041c000032800d1030314001703500c04100e802d008260291901045c0d0241c8a01c80d5204250780000820b4402301c40c0000150b52961901e40d0703100310700054807083c107045110704000c00a079011030800520542d071041c9440ea80d2455a081808001c0c5416448000030240303001c010401200080d007103076441a114500400c50f85800b03850075080d64040d0b00041e070080c0c641801001c107140d410f0024400da441d00256020203e01100030411060114000240100018001042018010140513400920400d81c04542030411000481107480c26403000414004401c41805941215690140035000c2a40140030220b41c4203c00b4149050b0110700f601089000070345001409001c0d4469450150b101c4010303c8825000c00a82500d030304243d070b80c1c2e0185400031007071542441c4148224540030a00b0501d490404000390200700d903100c02c05007070f40e401041c0e54107007000045607074150603010510002a0300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 101432742 1250 101431492 101431511
    0x33060405190311010e010c11120f0a110909120703020c130207030f110304121b03030f2c1507050a061e090b010509180118060b040903081b070510 64
    0x36401e000f4a0f035a039042c03140a000000d2581d03480500311203440d4100c0c2c00c4032200308441c400304407450680c5086960030701400b01181c3c944400801c416030010b004802c0c0c1c203508a05541004801942994891625031102000c208030110100c0980340c1c590281c010b9070302c0c480101c4049810442e0040b0160b000300d50000313080c0c04140d04000860000c0000d0300d040441c000c00450102c1d500e12070342c01059001c2c030041000c0740402000021094500100780c0c194810350f943ca240140503100445001d0340818030071070801c804290114400c48a84140000200c403c180030f4042c001c601c8190710380f850050303004108040105000300001070300c05100715000214941c5100f2280c2922400c0440d984545081850810200b640d12510034107485084880c2e030480c1d119203542240300301c90380038000c0e195404c1c03102c1ea01d402d408411a0301c00e9075020340418401e0302c044030108000c995072040024041509000030a4400035001640310348a01504a410f00c1d2108036243c8a04e030034400e80034080040e48580c90038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 101433992 1250 101432742 101432753
    0xa0f0303140f010b03060d02060c030301090b0d0302030f031504021206010914031203090c091f05010327030306271104030c030f03030623010305330604051903 70
    0x10300440c0c00900316a4420b00745050007061801c810f2082c01050840403000c40c8040c1e0356202e1220b66a0750080c81c040c0d40d00a01c020494407038100f44150b04d8810324003032441d03809040c0b43d4100690340e070b4158069407078003440d181103400c207410103400407e0080076101c4800c2291541c1c801807510300e10380650100e041c0361402c001410a072007a000300c40c104110200c00d14980e2400101001c40110820040d41c50307540345840e80745003005c000301280d4040d000c0018814141031803489490312090003000745d002251203400540c10364000c490303110480c20b400140f0000d000c07015994440300600c60314006c1882e42d550301080d441181002102d40340380c026902e02c2401c0b00c1307091161882800416854508107031540c2c0345e010b000300c51171001404c07001c42e901042c800c040c4a9880280540205408881c00c48641120b405180c030300e044030280824a0400442c01142e8103198441c0c0200d040c1c0b00c4c00c800b152100c075078200300c01c40c41d100b903c0d000704090001007203d82e120014a01450414590320620700d143d030070134 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 101435242 1250 101433992 101434001
    0x3070606050411180607240e0309010f030e0a08040f08060105040603080415140301090506090708061f020a06060b070c0e07080402060702120a05060603011415010f020f0a0f0303 78
    0x120b01c580d18004591141d014a5411380c1e207800b02008084134409403510105850340301c0c084000b085040614100150709182c45025000601850002c11001e0b078141e500c5a40c070722400d1010786c00700700d000c6180722407a1300ca900243d442d41c20200079501d081000d0340c1d400d82103400c0354100c450326021545090140c100f0821015004100450b000d00840c1d00d5901d680f5a14856409481c28000b40d9003294126280039a800d800c062042e0500785030342e513969109030340c01403d003518035900c1b411181002c22003ca00c603912041c0079030360040011800d01850302902030f0301d250446d514802c1d0700911580340301044051189000030060080600d179070303e96038506030300c003444540c004d841d10f842c590061180b8154821901c0e1361207541942d0303960f900c103880c2c00000d0b420326000b0040d64040c0f00d4001000c0c1004404100310307006010a900078003040b0701561110040c3e09089a035482d1099240d0690941766100b4280780491084038010303a088500c0480a550400d2000d490903141e1074400c51a0404155140c0304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 101436492 1250 101435242 101435249
    0x507051215031216060209010912050a02180f010b0a0e0d0501050105120a030503060607030e030102070f1104020406170a02090306040b0906070e0d15020d090c080f0303041e0c030c060203070606 85
    0x140c3d403030306036130103504104400342d11000743c041075002c2001c00f1942d008103140b070043d02d01118403c140c0e141038580281d454040700001c0303006802c030000c0c02a2400d030341103869000c1d14444014100e943c1c2441c0850800380c010360307404010851803111a078144e80320285020320250003100045400c1d8141014005030b0401056550000c3c1c1c1301308110000300f68041c042d01c0d0811400c03600c3c039a50340507070304049882d031080703040781949540b0000300f0800300310520703c036108010710070100c224904091400300400c0f0300540c850240030552172070711024200400f440c0b41e5032180d0110300040c00e2041b204d010901e005400c607011292101110140003110f2020000e03907030304c0100d9284c66480611600041780081242513001844039900e0f0b81038004a100a4060740d248070481364042100c507426042c0314501c0c4085104084c5140160544140e0115000c41180d1146401807860740c810b8031600303500d074000b00203404240e4000d00c1c50080070001901180e00d98000385040c1e401107844100504011701210101d61 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 101437742 1250 101436492 101436523
    0x2070b09122115060406050c0d0f0504030f060603050f07061d0a0608180d020705040f060308030609090c040f1d06010501021207060e0607050a090f0e0a050705121503 73
    0x200202450014800c210141c42e081c0c40c410103480b40201c80c10204004071580b54042008100841d246901102602c0040301d200d04480064441e41070580345c04840c000340e0400901e0400081c004170f500c0c5401d0071403086c8030b06800600740b5500c0e20790ba81003148503a03128804d504402c03010080c10341c0c030501c12248200e030440c0f862840b01540c030000d00480c580303100d80420f1158400006042105540c1504540100c480542d0b0051144a00094490166000b40d901c0f0307a107040007414502200e4829001520f82c400010791039500c2c3c9500304102140000c000e9811440303181d10b0600940c50764090030712907118014000c1440550080c80b0364081203490481c0380c40390701c04001000280e900148810003028025141e598828040c2420030180140442800803032088030184203a43d60300100511205038169110350880e0b0302d544020b11404194032452070000a01401b0608904955116680142d0305003410f5142c9050000900403d0500319040c1107914060b0070281c0e0542401d110f1412455540c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 101438848 1106 101437742 101437747
    0x20c0f010e070603090b06040509031902100506090403020a0b060a030f0503030a05010f0803220806040b01080d0912060c0309240c030605061801021002070b0912 71
    0x785410510841e040068254403074403440c26410b07800400b4101030b80754070041002030302020b011005140020403080c02030380c240c500041411781007034026000c15584050801d04890004000790f020b80c6c2d00e0010040003941c0031940109043d481585405161106000704103602101c1d080181400107c1031840c0a06c90000003651060100580901280c1e80b19120100211094803071100280d10500c01e44541c40da1340f507100c0c41c0b1051010170f4419081d42d01e101d4a85840f40a4a007512031a07440c10042c06030034028418010740101a0070f00c0e80d0060725103081e0650f18011070b031010306095941c005a020841c82500585c01c40c90b00312445949400070380c0d0b202c0c60b58400c04a0b0f031241051606260780f00c014040c1c0034810444000400050130482520401800150b182101c541180102d040000d18103c507071029090b860b0080080003c9803a00700c5c042850414014040582c88406 = true := by decide +kernel

theorem cover : BRFrame.Cov 101258992 101438848 := by
  have h0 := BRFrame.cov_init 101258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 101258992 ≤ n) (h2 : n < 101438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
