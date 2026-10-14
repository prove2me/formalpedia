-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0716
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:18:16.162922+00:00
-- url     : https://prove2.me/submissions/acb8468a-71aa-4929-be7e-820cab6d335d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 128597122 ≤ n < 128776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 128598372 1250 128597122 128597143
    0xe0c220203011d01060309080f0a0c0618050c03030408150a021207080105030d0306140d080708040305030c1b130203070e041506030e0c0a090b0a03061b0f0c0b0411010c05 75
    0x44100e050f40b252114620301601600194140351030043c90b034021881e61419603880a1211540999602c4d60040540703610105000040c101402c00c0002c4805002c040e01c03081042e1310400c04ca68905015804042d104d00407805202d181d0ba01007541403445500707a50500b900a18483c0005260030005100f0081c2c0800c00c840010210b125003004100707038103080000480040d00d924040140504048400300078010182e1076600c101108070550041c841100304855046a0040000d42d40315600e1401503160340151207058100c0c0103141d03103004d4007021f807402c440c0d40000c010503e1103412040803c0030002d42000c0c100c0010459503c443c07007016183d52050070740c0c00e82414892901b180c0382c09001020350304801c0418140307400844800c4003035100c5030900400d8500c00207020031400d40140105003510300951002d0b2180e4113141d04415010f41e01ca1102c090a01c0c1c0ba035501441d00c0c101031003a03810700d00c0600028006c1c1400400200410580c403190040c0349814501001c00c96810389a40e45002070054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 128599622 1250 128598372 128598389
    0x61412130318060215010806040320010617011d060108070303140405030a05070312090b090d260702131802011808070f0e07020705030d030906060506030c090906040e0c22020301 78
    0x24481c21054141c80322401007e80300c000b0310342d500c2c041e5001000c0700c01e100f0ba4003800841703030003000741a1002074002201501001d060510540c46480140f4080c0036000e6414070f8030048001c3c00a140000407410b01d06076480c1c20014881c0f03615650b011030f600f0301c0741011195000350900003c41c0540d024000d000c110750207440105001819800c2c5526044114103044040c809030510070030020074400b0507507042c200126407454288400f82403d00040118501074400024840c5141c42c0d848222801381c100d640c000d45c0d40c800d515a0700f080b104101d4119000400000b06002c00410040d842507030200189982034540b000001d682e41c0c4060310380040c80c0c010b100684175403030060241d143e4441a0381d6104c01c091009080300b910382400b2a4031751047c0c42c444c0081613124003809051001c56004840108000380c507049d0b8034a0b0189a102c01608083c01c0c0c28480c0000c800401d42c1d40c07805001e01c00c48980c2c5e00d00600510343c80e40e400c000c101d511411f024004e00c03610b0f2828000710602032024500910948 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 128600872 1250 128599622 128599633
    0x316030c0c091d06070f1107080105070c060e07050a1403120f070302161a0705011103040c06020f010b06030a020d0e0a0609031404320a0902040614121303180602 71
    0x150742c03c40f0540200141c03001a40c443c030b00300305015900091b0007982581d6030030002c070305522036a51075051a556801c03580e01582890b0174032007071550001000d001c42d4040c1100b00100e10405900b181c5032020b510800d60b01080a003424404e50041403c09003200d40018129403a90a240c5201079403074100820f5040400d0b00826034805041c0c0500c5582c40080d8083c00d114919810681c80070316002808600d44054203021503402e0030071000b58400505208500c5040d500d0745050718201c1c08403a900c3c010f050040c00784464103081328205000d801036828004010a00b56542e0304642d0001713405c40d1094441c0b0715114000554810030a020948825004a0b070101d508116410041d000c0507000725040c410309820442085203c4d850801450303414074000e00365401118104c00140300c42e9000c403403103034809e6200b10700151200c020381c01007023250015112034030040008070780c0001a00401601c40d00700402840003a105080c1c0161510145200341865980d1400c00030368000c41c171005406c2040541d000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 128602122 1250 128600872 128600891
    0xd0501060308180d02180712050f2d0105131e0e0c0a080a0b06010903050d0c11010f0905092d06130b0102030702010e13110315060406020316030c0c09 66
    0x9100480c3c0001c201900d0141030429a80d0204030545503050702c00e40d0074001100403503a114400d040b28809000d003003409110700d051141030386c413024006940b0043e0b40144540f030744124442420104c1007204d6010740d245280d070720b0041801011440b0f20304040150b9038800c64000fa09029058101d070b801c841c1c1c1c0c0001201e00e0b920024503d00b1886102d40c1d48160402d03442006043c3e40000c14003c5039500403c500c8280e110500140c900a0701600018101e01450245a8007140e1000e008100c40d80130f4480f490081401c05c0054a058000202d0200001e0880c01c09021740d0038400c103059000740c180323072520700c003800302d001c01080222030071442010903802c0f0010711529140000501c254101c90f02410001c50502500103075403880348102c02814840d44610000007a0340713910381c0c2c0210403451401400b001040c03010103043c1d40d1040320041101c0b047c100305d44c1941d041031825117003030302e0b840c0d0021450a038400c40072400b030440c8180c044080002200f242e8002500555080d03000309000507001c03030040c41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 128603372 1250 128602122 128602147
    0xd030306211a010302150708070c0305010b0102011506051204080d020705031b01050114040c0905151e04050607080d060f0905040b0604090b15011b030801050a0801060b0a0e0d0501060308 82
    0x44140d54000000b80010041c800b50b940d0070007443d0b44005c10741c40c1558445171480e00b5402c0b4007a064000e40740350340c003000000501c501074001004002c426030082018040c09210400d841c0142e000f6540000e01c28400070140c900341011082d049800b0345242800c081001c000304003a64041442241c81c0d40012400305441d000103524845040c01c0007000380001c1d8102103000c1183c03124400c1143c0700350b8448004010705805001d101c030162402604c1000e0804110800c0800c590150b81d54484180d83c04542d423200e000c0150a580035204c0c003d1802d860201d46171907850700d0307401281c10781c1070007540c0d020001132560380c000a901c0104040716020a01e454142040b4003e41d00043c61140903d00302031003980091030114086511000c6040b04140c51441480100c071103440c0b0100ca54240c2c085914100145600100300c01d040320000c8401c03014558880640c14281c40d260b200301c107800d480511aa0f800240207112005402d08060840310b800c420b242c0b115800e5407980e603c2601c4a841c0001c40e00320129 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 128604622 1250 128603372 128603393
    0x2060705071e15080c0703050903070e1f03020609100228150b03070b031e040809090106020d021513201f0203030109050402010c0c06080a0b0a060e0d03030621 70
    0x243c00740640c45110b407840000340c11098014282650312600042ea0010035003c0d6096942950029044401d015243c01404031018002e5901c034880070310800040011880e991116415070b54040c0146084c10f4610b02800b107840320204080c8194000c904012145030340c01d41503070844c920a051161000e04940c101400450904042d545619080920300080c1d81c90000b440c200700d51244200ca0b80d641d98011408150001c41c4501030703600c070700c2d03442440103000d0031a020b420039107011120410284d0f604d0009aa80d610641d0140c809a002580b40c00c0070285c07000c80e6036a10440c20740843d00200c10300c1c1e9914000b64070684421800d41c0c82c07000b00020b5402c06900f40d02c800d80c8100c008010010824071702a540380014424044c0f10750700d0384001011a40300361903080b10b240e8403490f840c0c946a1074005c06402c0c40c4080781e6000019142180e4501540703010751940c011900b1680300d001c1d0480c4400305110000c40300341c005401341915200001489a60000e17501900c100610025a824585241100018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 128605872 1250 128604622 128604629
    0x5090f061b1c080f040f08130f080601050105040e011a0405060706050a060b040803040e060307090c120b0108040b01030605073e030705120c0109020d030f0305060a0e070c02060705071e 81
    0x20f406810032845a079444203160300b0079003105114240d5281c0c1e14001400340b03d80c401006d0710030350104000070040e005100e21020b60b10000c00303481160781c0794401103810f800b032803044036010381e010001086000035040d00140c40021030a8028509500c40d400709001d0761002004607840c60342d44003003101851107480340501516031000e600c0e152501d800001641c0e030141d40540c40c6290080e80c003240031581c0400001c1c0003041410000d10503a4050031000e400c03490f045142c141041d0415041403100c0d841010450b03c2240c2c0118440030a9082d91907540041400410103400d01c822039049008003d0038011240646603019104072403181412606d0703810f00c04085007581c5a60003842110b0004d0004240318203804011100140c403000003a082c607024200d441c202075040460000204245540404003017845502520244000d8a8200034032040060511078031000210000c0030400d0301d44a005c2d500d05040c0001c1c01c05080450b1741e1100d0b07060407250342c400c01c054446a00c00c1036076000d00300d510074005c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 128607122 1250 128605872 128605877
    0x3060112060507030504320607030903090b0c1e0307020a0b0c010e150106030510170303061f0c06020f1b0d020f060103030c081e180f0301060605090f061b1c 69
    0x3800e180e6151f515158030031800700c1c0c5496030b6041d1540e8000c00413a804d15204d0030300382181d8075420500000b400410040c0f2080d0000341002101041c80f4041400301e40c2c9000708580184a074940d8580d8100c0d0781e8100006c990081e0100f08500d101580e1000d410718040e1481802541c8c2e83d5a80d01242c03421109016244005a04040c010a5a080c403801d011030456140d4200880d896035030421881501c800d030341003100c1a50b02d101e0a03806091000000d180714850540b141c41c4a101008072040101062000c014000b85141c00e10302c0c002a015006408800c2d00000e000e424580030441140d43c3c1d071045119011542d00480180c1c07030b59035040041544000c030043c0541080d504544009101030301c04800507242c2c140018508032088018200e24180c00d0701c0c041e0294a40740b800d2007003020103480c41d511920403c445155411701e0b1806100d600304585083d240d89140154010500042003102410709174401824007000c0d0405034180c05041041e01a00d018004a00500c2c00c1c082074208003420309002c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 128608372 1250 128607122 128607131
    0x210708121e0c0a060203060418052508070602010f0606080105100f0c080706051911040e0c0706111b060f0114041b17010e06010507080c0a020306011206050703 70
    0x485801003200ca00840100790501c140060140035149442680422441d510844141c8030600809078043e50103120120703014000c182060401c80380c81d400220020380345411a0582d20f8506807601c0043d021514140840b01c0b0031542c40000b10704264003680443e000d42d4450340c0411411169100312006045d290401810550500c004110545202e0b07507500144400d6541c4204280d00170359104055a82c03051145603070315218035040000d00fa09881a021400a0101089048002e40101289031406480b81c504040c6000d450000c03401c3c0c0584600d0800710200f14900202c0c04601604000f8411001e0080c3c5d1134081c240c4d02c0701d040d8191080c09580390444810b020044041d580c0caa130448040704d4102d034200416100003030042c1442221001c9410b08080c00340700d55078204d42140d40540d141c981c2c0140603a40c454000c003010300c044503032500083c0c0070800000001c02410103800606040350407508410301036804a03141c164203030040c1207240d076860616010004035028855208955140038003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 128609622 1250 128608372 128608393
    0x40f08061b04060f020111070c0501020c040c08161704060b031009030516020414040b010503010c0302120609090a06020a050315010302090901090f020c060f040201261b09210708 78
    0x680c1c051401454108080001900e44d20f500c00d40044040b643c0c490069075032428146070458911200344a1980903010742c1100b07403014549071240052480c4603403501c1645540c3c88084c0d6040c4c00300d8880c441c00b4041c0402c4403030860059040784a105900c11480004e0402c40641010b1520303080c0610342d0170890805c6d89401c0001d5000d0199440324200300c03403c100d441c40a20001c0c000d02844036101c110017101d80c00b00400e00640301300c100c0c1201c1094000300031091124138118140d104061981410019070004940030f4181540039640c0640ca840941c0e810340010354030682a13038003260700d44001900100c2070040c5c407a400d905c1031a94020909003140751401200218801c101e05120f1200a2070341c1d40c440d41e10110403501101c4400010005440ca0741c1350580c0c1141c039a020503a420390000e206506403c0607030071000e20f0b0501c0d2141c054200d0469550313131031000e01c0748841826550304001381809146001c0c1c6580c1c0c45114400d618014402c1c142d01004d000c107180c5899a4443ca00c60b1340492440d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 128610872 1250 128609622 128609671
    0x17070203070303050a092004060f0b09060a1103030a0b0306160e01080a0f060602071820030907050a0602030d050f0c090103110c060709030b0c070201080708060f06040f0806 76
    0x107512499140c100840c403030340c2d9008450024514814060710822400d20f100c00d00b82401c20b5000522241200c3c02c000903500e40090760f02d8140d42c3d016246950801b080b1200f02c41c079040001c9d1003400624a00306032440704840200d030964100f03075050001540c840b0710303000e1b051400380315003070f0701100696400803580031083c1c0080c04034800c82c002c02d040c080254085100c251240e00030404001c005001440344030360714035009580341c04611901c841030425212510b80d501e82070050400342d078049060054452000000c07441d10368409800c00381c00303104000c400507080d16503c0d410001007107290095601c4000345811881074620090903690444500c130300b04a2110041c1080d1942c081081c6400109511350f9007000c807407442040020f80031031207400c040103021035108030604141e0788558070420842d1100f120220840c05400b8001b1302064080d40001c514501c41e020450340004014100810300d103a81003c520302c1c1c0e016401c424441000c4490034082c1c0c8030200600e40e0030001c2c50640000c6d540021590 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 128612122 1250 128610872 128610877
    0x6080102030705091c02060c03090405100303020d20060103060506090a15061101020714030a090b0304030503063016050d1703090f03040f051003140a0f141617070203 73
    0x403502c41c00c1c3d0310408510b0240041081900385d070b0b0103842c45a0750038404131096525041100c1c86481103003018000f4020500c003080030300c01c6941c143c0041c070b0301c051414815030300e0340300c2d4080b06070208860300c1540b621050b01f009032a000314001c900005803818503070f041c8030740107000800e4060741ca4140700412003980a4038804400711840c6180c40410782c100c0d0310489019218100f005441310401c24581c00400c40c1c0400100000b80075921040c0f40716503141d19411444c00100c4014010600c18800103c5a041c49600c800c48a00501c64401080036640d200600840514024126680c0320803081e001c1c00401c0c0d84044007a0008881400e2410070a940d120b8003501d004904082098010000c200700140030422080601c0f040300545e62116103c241000c682059031040c1445200e104942034602130203403003540004840e1420942d05a5036040078400908001002c4105c0c1c183d444951480c00b1902a48481c000c040c4020240200c100302c4030018008419540f110083c400c1d130b00c003070000e015000000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 128613372 1250 128612122 128612137
    0x40513020906041d0c0a06090e010603020a0512040b070e0d050705040b1c03020c030706030b09060f01020c03030703121104050d1b0b0a050c010e030319150f08030304030306080102030705 82
    0x140d00001e40e4031000818081d00030004401c80c3e40090380071414021902180d00c030003c003c01d0b00d060400703554410089400c007105101c0e0241d038446000061220903c80e03001445d0480003818032624044c48a010000030000840d8155800740d10901840384155200300c081078441d4046450300d030482410717156180c5450b0907114007132146a03640030030391241e1a00354480003040940062840c0c64101e504029480d680303030080c02440390003401c0f4007048842c003903c102d2018130fa01400c4030145075111130a100510203c515003905620481c0810f14455504100500003d4442d5540800701c440e41803c81040d590510181c24401d142803005004035281c4002910340d4580141583c01460707009104188448415004a20112400180d0364002e40e0094000d0260100040080082501c11108030741c803804141e602400c0d65004080b000405070301500070414140e03030f015004245030b90318200302402101542c0b02e40704907000401081b040c9600b6104880040607200020340c0340d403500e124000c1082c4240503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 128614622 1250 128613372 128613379
    0x10b010e100e0a0509100e0609070c030e010c080316030f050114090a0e06010603021b0c031c120518060c030103110409140d050c0d09030803010b03130507060305070e04051302 77
    0x880c031600603038402c000310f40103010141020349113051021504414004600607550f680700714001203203250500c511024031a01455a83c4107442019980407205d114200e010f141c108030102e00210082511240154011010880c1c000e5111130020340213010749c1c1d4006171203040d05107040d004100c1e0b4011007406003032918080354140b41543e90080302c48014400581700444505c03a410000c60b10340c1c1c155004069145503d45004034012220120340d039038448a11100e078154001c00348004400b9040402e120046559061000441c40011f8010f004c8800881d4070395103c08640d4601b00d842c1c9418010b60341c100c1e4981a401e0320359810b50701d0b000c6500f03000303403c239500450b5038907a07071401d0002c00c81c0540b1407000e0382010b0310010703032040d000101940c00888a00d4140c0c01010410440b607802080082c084a90083c840c6c0d0540c1c1c605859580160002060f205803120328541c1580003031000e10506026110540380010345003003020005096840504050f40558906801c0c040244000140004501e034100d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 128615872 1250 128614622 128614637
    0x10908042105120a09091a01030c03140906061504060f050f04032906010203040303080c0c0a0215040f050906130908091804060c0203130909030507080409020c010b010e10 75
    0x2000e40700e01d41030051002800c035000e100c680200d0707003c000e4010702129101c1d0b43c500403000d848020b10400c0b42d4078030074040d0b120194042c0d18130b101c0d406a081407021485600380003402c0c6060036882c034600c00040350702c0c403000c1d0840001c0002902d42007810304012080b0303c0c8400d04241c104140a0943c4800100c104103100f4080740100c0318544000c2107801460f8001008509c0d011901100003081c00000426100ca1b604c0100040c1c0552000040e40c08072038240d511a402ca483d24821001c01d039100310031107140c5015101c11200903850301c4880318200361810441e59680c9140c52a40c80f5203e0a0783c009611410410050100b81d03601d003100387c0d0346100420030008841d206468400028881d1440f01500844803900c4a00a01d070400b0320588541d00800042c00083d82d000300032078aa1080042000d100c030034410b42882400300c039602c296a140d202e824210310f070501c0e98503185495041035100c1c035106030300040d001c1d01040083c05401c42115003800c1100208010200188488030724014202c1040703600c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 128617122 1250 128615872 128615909
    0xc03090d050919060c05011d030706050a0213170d02071d190f0b090112030503010312020f06040c1e06050a180f0803041508090a02060307030e0105090f070801090804 73
    0x190b1489960340d0f000010000c10703040d80c1d0480508003000844080d6129464040345100510182c06240c19140b1140041c602e840210b50703401d40140750141903002026424400e003205a2100b40300300d800b8041012142a900c0c0c80d1b480250700e00b000d170400810441d0804a400c1287c44a400040513031100c2011910009540307200780c8190ba00c10000c840301071701c4e050044d00070313410400d9404800d8600e01a02c1c4400c5507a21810f0110070342d90040300042c0050030410041003c201481030740d10400310350f4816075605400110109144c6982601c06888245407200c0800018219105400c0b981c1140402c80c403985140c41005841c03805850100070905c03520681d004402d6103402400d801601c0d6a09a110209488180542d5640c00500560b550300c81040b01040c85035000d209a5486200603e00a05201069074240070140e08003400010501d51508900c103203001c0d00380100b601c1044a40014222818903405003460203006500000560345001100e10203d00110308030303416262200c4080100f0042d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 128618372 1250 128617122 128617129
    0x3030319090b011401030606080f040f030512010f18180b0a0b0303040905090d14090d0312020c1501060507030e0d080f03010b0a14040b12180307030302030108060c03090d0509 77
    0x7424005008418142c000f0034640c408005100d4203010a81c0c1c00c10200c0d46500064a1000041d54203400500c0000d00103800200841040765809102c1c0c40c0003070806800c0c03129119440c03400e0b000443c1203050000140f1250791600001c1c80c0e6109040400d0005200101c4445c0b81d0305040400034241c0110140014194580e9030049107001c10090116540c0e1651a200c1900130b19054030b44602c18018110344685240c420007218410300c0e101d100d003504d8040d00f60308024200c0e49000c1d0440c1403100700036021840003142c3c400380440031440340103802c4440c2c80b401c180700300070b03416000b84052100c103100d40c0001c6503000030054a605421b40340503401c11058101a407442c060030020040720f060010020410742d40b14030103080902d8107512442d020445100c10041d80c1e00442c02181c0801900b802480350428109a1750740d007000400c804030101d030100354030150466002d0501940820380010040006a00402c07250368000e142c01d00c0309045090070210141c48a24840001080120203d00c6800b0755a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 128619622 1250 128618372 128618381
    0x5030f0a06080a0b040b0a060f2d030f050c01030519020c010f1b1103090904150b03190b010b121602030f040f03050d080906130602091201020418060503030319 70
    0x403080304582c0035042c1e43c40c4c0314031082401ca07021030720212110040340904140d401100251011803d40000c80d6080c840f52003414200c0340c1e030f0110150401848451440b1145060038040c500620500030049064188103143c000c208210504042c0342000b00019207085182c0c1305140b81340f9000150351249041d03603042c01b41c6024040601005d162000ea20742d004074440112820f1070240c0c4030084101e03540d001c4a0340320b005502c60340340c0040107140007600292100700003c0324482d9024000031100188130101b0311f030810310880a11205501c024401c240440b40300d40c0743c010070014500c180780000c0310040000200380944500e402c00c5c203a00d442c004a600a1060300c00080c00b59401c503466564400e00025001c03001c0c80192024050b0741385000c4010f101e079081c2c0b4452640c0070004c01251b1516444031f400d8600b0340c0410781c0c46582c02c1c01507281564070841c00300b40d10403101c4000350b110b03070600c00352014084810105081c0e0602d041c004000a44000c42500e41c01800400c04014001381e403034103c800741 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 128620872 1250 128619622 128619629
    0x11b080115020a05011a0a061d0d1a0a0204061d03030a050304020604030611040e090115050f0a0e040501050105010207240804020d0501020310150509012016080304090c030b0105030f0a06 82
    0x194240505452440042d000c0c00d10034038402c644d0880188e942c0c0c603065480e5080d01041d0381041e003008401c0c004e10b00b400e401c1e00c843c0b18030078418410303451103110b01107094160554803203e0013034002404000f4964440100300101c0380500030a00c406200c0c1000aa80340305034440032050107408400607095645180680b4021500418144100c44d00d842c1e58a000340e015004480d6000310a03000f0071004401403044400e140b0f04600f584080e24105420001852803120315140d00000d0f00c0c41c0401c4400c0e014449501a038810380c00882e40754148000603003040100e07007082c030340c08000d990507222802c55480c00d03030003200050501e12066122800800c03038503040c0b4030011b4a03540c0008180501c41283e0341c0705d0b0007190456a569002c4a40c24031040b1064450030f90b0f8940045d0f981181c0d80e240007040c0d05040c4c42001d05004403494981403c1c00d0304040c1909030b109107000d1f00042001c00000d0003d0107803108032002c600c1e0400401d0307510000a4500c1c04003070f100300c02d00b10a201c000b411880b02680100c014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 128622122 1250 128620872 128620883
    0x2090408090d030e2b061d0f2a0907050313081b01060b09060414030f0a030c03110111040e040201022e1104050a03021012051503011b080115020a 64
    0x80d22a50402818011003218030724014001c82c0c900175421980c600a60309034080b07041d0b0090b000c84003912501c0240400068100c482da62030704030000d0850042100010751008080600005600c2c2040d02d85034088640c5094040e81800f5282d0b030150741d4681c85680d001e0281d04000da280e8031000035083c030f4101c0c3c1c01c400804d0180001110b10a5242c1d42c075503207011804060080c4a12512481051160702950ba081c541014003800244005410103a100c018074030040c080703502c1301404a4100340b5081081c6420340218207800e01d04028540c0c80b244076100e03554844024070551880380d44d110241d1003075205120340c4010190110b8110ba1080c0080300185042d003400c10a425205840c0f01440c101c05d0341c5c070b102124a004444a2011040000d460489900a00c1c070450320b0310b507400340110000e0000b20841040034030f4980000c40c42c984d11416001c4c8400c0e280002411100905050071501e03004950b0319500380704040b19010aa008030105e042d2072081e1b01c603400320445110300340e02d0600342d078900500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 128623372 1250 128622122 128622139
    0xc050a03110d0207030c0b09031005040609020907080c1611040c030506040c021b01050a05130807091d06041410020408101404030503041b03150c0201050105120a0209040809 76
    0x605a0000d44601c0c0340a401c02664850307140490103a030748039150700c001000c0b80c241e00400c024256507000a0300c803400c005019038100f00086154070f81120402c58081311003d0b524141c003829420320040302940401503040440c40350500e0304515174175000301c021461240c01045c0320203080004812080c034070083d02400503c011280020083c026101c1101c02900943c9450350f1000c15510008030070a41546118840000701c03144801114507500c13450601060110400400301605806102e90f0f00610681c8050080c0c0c50812060f80155516058442407041d15240c0020440c003000c0b40d81d07500950300021403100801c0305407205041c41e100f08070300410148040380000d070016000c80c5500b41c0004141d8100203400d021500607a02401c25100500041d0007480000e0025100c4484030490070680b55600081d15a0b0360381b4590b100030442c0c05c00c01c08580310f25012940503024025180500700464894400880c00e41c1c1142d51000d8403003000c0e02c10451a4041000d01035146e00300d0742c000d04094280350 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 128624622 1250 128623372 128623393
    0x7060c0b0c090418032d0507060e0a080f030f011208161e0f02090601020d02030d0b19060c14010b130f060f0f0e07020c0105040b071103071202041a060307050a0c05 72
    0x107102c086843c0c10200346d030304172201005401800e941a5008248540c9403071b0b041075426180e1800a046581360030b013003481405070040c0860514400b03000f144a0110441e5900d2601e0084081c4140040e8404a190004454000c0029040b00182c03100340043d0340c400d1841d96900d08100c000e0003a0140030304ca0603c3c2c06040c81702032000680f0504803141c02510444c000e5221040120f940b403a540a111005030424822103061541a800c100d01000d030090a007010030b00350006941200c1c909034000d4022070038001c800d03010003000c05d002900d1010200002c004051085c000f143d41c07442000e56602c14030341d68081c4a58016801c0d03011001034010b8040c8009613944440c03070f102d1280c1440c006d1441c510303510701c0010000ea20002e1003c80d185d0040c0d550b0307424940f820150b401c40b1340040b00308998410700301d00c003040585c600b000740300c005200601000e100c084450050104840141c0765440981400811f1801c694884038101d036003064040c46c0c5940c1d100302c0140d084034a55020f840c01000f1f4014014843d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 128625872 1250 128624622 128624627
    0x21080c07080c0d111c0210080f070c05100b0d060e1e030a0f0806011e09140402030c030402060c030c010c0804020a050d03020c060c010204050d0c0807060c0b0c09041803 74
    0x48090758040000c48041c028824104036103a80032450081c02038419850b408581d0400e0104c1780018400380300041403030065a4001507014841c612240c00240400c402c10403034840805050380c01201a042419200d01103450300358560307a000e07102e08101e1751501c44583c500e4a410320000051b07a0081c00403c00420713245d060303907210703c00d50081680040460504468004000c411030355001c031180c9550401c844421010f5a030300e41c0c0103000030306012054100d07041104014100840300102e03560380300755860414001204034070443d451300f8029807043c400c0111110039035046a4106404a507a281c48245422030b5516610034400900c41030350174018070030306181e04500c02c1c0d0700440c0f085881c040d11a07181d109201c0c01d000c0042001d030041e03003c00f05000d03031410140e0080c134044488000151400b0344800210714065a07560048541068242082000300c2080c000d00002c0c0c0440e181c8860301502c075844800c00044050400302c1203200002c0c00d200d141c0d41d194020b5080031040f12412800310000d0402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 128627122 1250 128625872 128625883
    0x203070b130f0b0c010606080c03010e0a0b04020c1c09030c1e0b0a03090605060409051504030519050301080f060c0d020a03141e06040606051804060305070308041403010209010921080c 81
    0x10880313a600702100801c110b800703071090510810091504a080d07a2070200316101c41a070152800c1800c1c0d544030131002c201d407514002029043d28010003404c2d1241403d00301c100c1c0f07102c10100d55003004002c507020f20019000744107050407520505c11441e880c01800210306410051a4001d8980c1ca2000410000d03454045e00003842d070500840003082141d50b40c1040c001070303030340041c0010019040102d1040c0340d041d81200d025002402071074800c0c1410b0414042c03408002040e038010001c01c00200c0104008402080100103061103540545068240390010300003601503005031110054012807a085000e00c00e40c8150088421809440a00d0424400d807021340b07250810314101000403000050494242801100c023250311940d599454012522040c0c104089040410b591142e2103190000102e10300308600742c06940200c8401d5038451501c9491548444800100790190340140720039201c44c1c1c1c0003a401700890750700c84103c5140d108050300744426452940c00c014002c010205010030304140010303170b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 128628372 1250 128627122 128627137
    0x504050f1f05011e091e020301060527010801120609230d020604080307050f04030b0a0c020d020a030206010611010209041a040f0234080307020c0a050d0203070b130f0b 74
    0x1e04112590b210742c00400700455044107100e4686000d64100030301030700b42d40031010f60710303d010b03c42c541010320b0301214060b41e0007a4445c000045000c81d2605282d403c03402c0207112102082041000303000140d00282039080141b2640d03215208964030081409207903040001000c1e8801b004451005c071010040e91615140e101d401090305ca00c0c0b5200400c540009185070050360440d84241c00d66072028000c4071258060040703542038040601001000a0300e41080320701410901e40e011404000c0d02800074603100c1d100b0b00d41021035100d418007001007038000c5000c1d0f0554646141c01c1c404490780082e803601a00c503e500e1207404c103180690038000d04414902041c0a00c1088070140001c0d00c003150104240e0007010150308541d0108002c01c45088000305900402e5444c100c411254a0059101c514507070300112402ca0160b04142201340706440c02a0802010f4841150448281415600480e9551900d4000c02c2c111010001395160f887c007640343d00ca4000c1504400d0b5008140d101c2a109110303410003032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 128629622 1250 128628372 128628433
    0x40e040b011707051002010209060c0105010311100c020d02011b030215150303090607030318140606010305070203070b090c0a0801230603120d0b06040b0c0f0606130504050f 76
    0x80303000e8602d50301c1d280349030700a1401000d16a061008000c482d0511501c0c0000790748d401c004071003044c1c581034050014180b1040c0002081e40c518104102d044109014040c03203588484141d088940e0082d9044400d81e405507070360420a8054401078440700031000c40e54064400c8215204109940001d81100841c24a160740c5242e0f110391404070140250f003104154103402c280110082404e00c0400350034118068503000c07075814038403092035600318415081030b5201e07503409072030010a420810240c0d80065080c07808000398941081c00a480c0c0c080d80c2002004208040c0110300d244030100014900c003100148000102556100d45034000c144070b0180003000d15204d0100d40b58007152003031203413041a0241c0684210303d92100100001d0303103d15039403152640c3d10884200c283e11444003820260149180c25655031014801c6c5500e02180074481c00c3c090741c40030081201c80c0c0c9828007400f451407500c9801181c07545079854683c3c01c00300d1040c50007916104483d4070009101d003d9241c28500c82c000c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 128630872 1250 128629622 128629643
    0xb0601170108060718210515090604050c06191d0405010803090102150f071101060b0a1205060307140d02010c08030709230a06050f09030106080f1002090f2103040e04 73
    0x3100c1710f05054490a03440c00b007054035011002c030340f060748041058450710030780c0c030703d03090b40e1300c003210b5190301a600000242e01210400c01009004c2000020210040300c400307041400070805e02002c100d4101c0d68900700104001000c60342003503000e441a92100042052202c0e6071201c00480e620740000006500600c070311521703000104042c161403070140c01c02082c0c181d00d6a807070407000d0b10101041c400c1603410b50740c1d81200043e45200b901c050094950b1a540d03061609001990a8050b10300c040c15042c406d402c5140d0402500000c46103a18154030203072104010042240016110790701081409015410004100000d42c0c0c4d000361a81300713681100078040018240c4030010394140c1250b595054014030b00c0c9005008440c040d0003c2c1c14400c50243d0a00c1c1703400c070044046429240e85522070b9030254000120b181ca0341b0340503c4540c0b0f03c0311507100110702706180310300000c0c03001d54880e50719400b641072000e42c5001004502c0c1e0031408840c00a00716540c2d0750f655840d10102103401c580c1640c081c1e500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 128632122 1250 128630872 128630897
    0x90b011202030903090103020703090801090b0103020406150807120e0304030b06040e0d05090910050d0b0a0606050a051204110d080306090f04150e0709060303030605040e030901020601030b06011701080607 90
    0x840c4250b80c018115a401182803024900041d0300035030011344180c06010302c00c04000340040b001d010701c8100a114030a05512945180b0600054a0264200943c4c002c03220112903c45544070803059840500c03403402001c01c80700c005c0c0e8a00200481072842c001d038040024040140300502d100c0320302401094030204058622034170241e44809146104e04c00045003000400d60703e2a03d200d209800824114521903601d07680c0c0c0000ea450002c07070340102c440c000410f0800048682910584000b403030a800c00b20320308900c2a800600034070401c440c0c1801511101c01080c24004006401c04803c21b010301070480d044440e0810f24035580044921600c21404800010304079001100ba142c000da61140700d1440880d408440100509040c900a61a6219540d0300182c84100d500441d401140030340c90001c3c4403400c050901050708d202d11000096a80104550f02c1140d074002000f0341140d400480c020165105c610040700c01c8008180110895901d4600205801d4408260240115920f49408004004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 128633372 1250 128632122 128632157
    0x8010807050a180504050c061908160203090103020f04091e0b0d08070f051f020a03110306090115050405030a03051c05060a1202031501090e12120c0702030115090b01 73
    0x10540290000f00f04102c105003420785080d00000e810505c00c4003039a50100200c0301040650300031101c8041c0079402d03510025100c6810140303040c1c000740203140803256a180600081c0d0707139200d0062100c1c10190300103402890000200305031409892010010711140340303003447d03512030880c002281400261404040016910b4020b0b4043d1803154403116003420300903503841c2c00c0c0c40364805140a4481d4046c2600d1f079580c1c61107050180c01881000c0f0b0005854000c151001001c0301c0c000c125100360840e04200303000459840400880c1182c10340810b000840d40c8040c0111950300965101c00e0701b505c51542640c04040c2c112001d804d02592000258818642040302071081d070b1029120b56400805410040c0310500080001c0f4114500250440e18540220b6449180000003640701074600c80d900d1240c0d9900c08402d000c072a0305c440c000c0c280c890134a03108901001500401802c90b01c200180001d14000f152400c2d00255031000c4840405100d80359541c40050140091101060001700041181d144200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 128634622 1250 128633372 128633389
    0x405010815030d030b03100f05100909021806180c070b0606070f0b060a17030408070608040c15090801020304060c030e010c080a05041b230a031e0c090c0801080705 72
    0xb001000c00300780d145070030780c000d08910501d1074240c0110f000c5151006054001c14004031843c2c0030019407071924203002c4004512030b130041d80e0f07080e04156a01025948600340307841ea2a92a0b242d8121030f44072040090100c4030000d111404a0007180100300c4255880d002800311140038441c8450300b90b0350403082060758411160014420544154005c01013860001d282c0e038090000303042000240e1311740b094048400d01c1c0001581003548000740038459103e06001c00707401001c8500f40501e250500395914401c070580c0c1e000d20f8106196034460b40e00b42038030403000c0e2070080001100865581c2018240200541010125000440d00f0304101000303503c4148180340440003150f48404450321141c00803c007401000d001a40c4142440500d030100c0000c20040383c0040001c01260b107100d2401800105440a1000916208036003092041000c942946025619511540c00a4002800c1844d00101c002040e0304080e0780580751400095000360005141e50603949448120b6030040e59130b60030080e100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 128635872 1250 128634622 128634661
    0x5040b070e03030304030809070801060909110d0c0902070602042d060504051008090f0f0604051203060609040b030115091a0406082d011104090e0714012f0304050108 73
    0x150300400c00a4081b91049401640150703c0070300340c072101555120100d00350351301034020f40314003580c0704402c2d420040c40052411441100b500c010040480c01d0f01e440c0c000c00c840344558075003960006404010040668100c03000b500300038510180c030a40181802c6600e0004030a00d04518880c68008982c5070300034002c0d101140c0006010301182381c6401422203900304003070b01502d014800c040003800c001c1c00a0020700151100d45008103210301c2c00e400c0251a00549201500201000304140007840c0c075103a00301e613011030080d103011a0280e04003003c203004021940c0c800414080103800032a0304106500020315010450b05055104c101c401e0400c400c90b1150301c00c00f0041e9000307030301e43d0010843c41900c9046900080424201c01400c110301c0174291116000c01809403000001c06103c00c0c0541c2c0704d01c0d48180c0066004004042c00d11400300044440a400c8905008841d03403100340d521100325070070203030008004039402161160100d0a0f40ca41140c0146030118586100050807103039005c2005102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 128637122 1250 128635872 128635879
    0x40803061c02090703150e0702030304031d030c0f0d06090804180e0c01030b010c0605010e07110a030c031407050312060103050c070c05130f02161101020c060304060b0d02031005040b070e 82
    0x4e031912070055000306450700741c8040d103803003940000411082140005110b804990061952444c003031034003e00c03050f413400f02c0c80b40d1900e40e1712104049440004e107000d8903c078140c40108106c0b0002c00002c81c0e0702582d0b003000f00b0365030070100c0500411541001400464040240c2645d0340150300541c01d003550043c900c40d00b10350340300c0c0903415480d40c440c1e007040841c4001070400c0d40c40b414845c2c490784c0a60300c0c240c0042da401c0f600c160074050202e80c403058140740400080050035907002d050303500038803020403075801404000d6000c06405410580d20100c13101c456004d81140e035a000b060741c0e07910030807004440c00c5003ca0710f06000285681e0301c0781c00321001039510032240110300341004200040720301000b800d6424643c2e619440e07900c844843c40289880c0d90b922902e000350440c03502d403102192074070700d00440c1150848401c00700c641e160b03981500c1d002640510b020410103542d20200f68a8114900003030750610600403c20000001d0760320603406180605482c0b21030790769010f0195501c44d84010003541 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 128638372 1250 128637122 128637139
    0x6030d1407020a0e090d021c0c030809010608030703031e0b0d03120b10020c1003150501050318010504230303040305090d03030b0306150102010e0607020a0219030b040803061c02 78
    0x806502000091a600b480103120104868584070307640c0e0312110803a1001c146510010141500d20f40410801e10b4080e008400650540c102000042075858441401418404c0e07200201e00000001e4000c0e80141510104503511a02d403814014054442c1c82c2600c3c000d440e8407000a2420240c5010f550062040039090301000c0c40a0340d011140724429240301e03442a90384070854003031545c078944680003d00655008004045100b4100001c07a01e4500341003042c940b4100304c01810059944005e0116442404c020352240d8802500c1c44607188000884601546080c3c108410072441005e2492410038010300b000b640d00c404850766035248819107015020800601041c00545415251088880d03c24a00414400d4504010a1905200f6542c4035203082c0b070351460906a581c2449468482900180200a00d003001e43e0007a490340007150010340240040c00881d58002060031504000b958010312008084c80d0030f0030420615001551284e100d00c040419801100d40790b00102034405400030000c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 128639622 1250 128638372 128638397
    0xb01090b01020d1d0a15020f0105042105040911040f090e0c06030a1803120b0d020f010806030a0c060e0f0603070e0118031e06050708040b010323010507110606030d 72
    0x42e40108100b6000e98070305401070304c0c2030032615848190b200400503607141d000c0c80642840086d0414035540603540444c0e00d01010480843e112031040005003c800c0e0b5034110b1142000011261403046400c90b0019500f01515480841e1b81174008104803000c0e036900350099a211118070064a1a020f034400e00c7c0da03c0001c07010034500c0c00400031a0066002c03080020710f9010804c2d0482e00103011a000d0f40890b820320494012010307107000d060178402c03046581c0100c1d00c685030b000551001d10254403504101c880c82c0000c41c2514200003480c0c03050342240006007100d1381c58000415034070200c0d1040740100311105194156080810a480c010303003254403420082544400111245014800001c1010095420007c08034107649101044a45251a890710000c00b908000003940d90280c107203410401c00300104404110035001d040c2c152503020781a198a240d1140070b0240e102c460300500340903540781805200d6410741200c2c0e14a43c0c001c00d070003920f43c66622071003010b072100017002c0c2e90008034072540c8148 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 128640872 1250 128639622 128639627
    0xa080703080904021912231308130e0702070b0703120506191409090a051902040b120607080703050907030f080c150108010f050411060304030c1401090b01090b01020d 73
    0x2000c8091001d84010b003413403030070032181750f28a0441040c4030201e142401c004020340e000780120982990301d0f0085044030401c002d00c91481c800010102460b201103034040c001009807613021550560045c1d041e4805150b261446600c0a080945030280540304940e000604130440070240e4a0f5a609500d40c0e00c00d01c1d1801c400407000e420005c18042e40141908040011040d80e5076000020303040040c43c0c2c00701c02100e402880545a8043d208521319806440400300164000910414040903110003001640781840810080e0404031104c945c0f00d1440c181da10708560b40011118880e038160b80d1400540d131035411080d401c44d84151607003211904084401e0010800b02d480460311284107803800c91038580c0c0c101170715051150f00040c189000421750010040c01900340035050329502d6040b410000c1d801c156a13965240080c10300c1680c0113102c0800001c0515000342e034100d0341280c204412005404400c09400c0c0200f40d10101100c1402c0c07040000314031050b1a210300c2c40c1100b01030300241304020005409 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 128642122 1250 128640872 128640877
    0x105070503040f0f0506010b04090e01380414040302010b0a08070b0c030c0f03072d0b09010b0d211103030f040c090e0c0a0b18091009020f13050a08070308 68
    0x341d94000400030207100141080146c60300134060144480e4995040c2810401602d41e200440181a1704190070f82000014075a18942d40419043c42c0003800280e2001d0041019401003035241d11a10704964000711980d900c000a2145103c1d500070001c206101c010051240301c01c2c01000c031039900c61341083c00028007000c003e008441103041204d050900303da0180c1e10700840c02c280c0180c6600041408001c0042c21500410546010942204d100007602c81c40040c40c2040100945100c8001c030109000300300a6002d0078074004d0241c241400300c2ca041c2400e07404205030080b032f035405440500071907165070b201781c505030401c5001601451540d1100c0c3d0302903d03444000760040d1008101100e00189805187c1b00e41d07230036442c81d84045c00d90703500b01e1000c1200c00d4500780c0c4406101e2000b0403c19410204006003d443c0000c22a04000a521648503002c0450f1541e000f40c1c0b280c910000720b49643c1c10022000d810391241500d050380180381c5400500903004014842c0c07a5541d401580c0900000310700002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 128643372 1250 128642122 128642153
    0x1201060e12010204030f030f050a0221090907020c0108180309100513060903060606030b03031b07051c020406050d050616020a1e0c090b0f150f0c070e060102010507050304 75
    0x289288010081c0c81c841e0880e03005500855480d0b000c044c00d501003542120001c0d040614a08050782844041d400c040d48031010101d041d00c1c091448448180d0540c1c4640c20342d80d10b114090000c00607880c1c00d0300c0203592103a589802c2400711303550100144a100190b104500c0f0458154061810031a0210a0280190490440d5010f005082c402440416051400c2c840217040036a82e07100b03181d00e1400c01d98129070031600082c0826042034609030403910300208803060030885011b010301190305419658104500d40d0021644041e01041c60302d5402440305c80019000c0c021182004a079955804200d400d02071003d00130b00c550880710000362104c13140300089441c080389005441302c0810f103641e040000001180c6031600ea049800100041c040c014411402801d110a02045030458200000382908141d80c2402d1003a0019991003080e42a0070082ea28030100e06000141c540000200b004d488010500800e5010354500000580c1c96205006407030080415840303283c80d548854443e03144e103928006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 128644622 1250 128643372 128643379
    0x30a020a08130e040b0f161403180f0f010b0f15070602090a060f081e0c1803030c0a170906090409050102120a05010f06020c03030a031503050a12030609021201060e 72
    0xb40001d6103460010302601c1503200d05d0540c2d078203180c11640e001088002801f00321640001c64050b40c00303e60820841a031081000009945984d5082030312503960b4200300c02c801c1623010f0013984202c040c4000802c484440e12540080c8106a070010500049640c00f2011342d80c08030448034407100c4050b10343c0017881c00c5400781801500e8102c10750042680070709280d021390000b41411030003071044c9a010014580007510101104802501c1e10540d614007070b8064940300390040700265030482d90701181d1080005642c0902036a44442c04821030320348a441d44841070703920b0022488407680c13090a09088502903107008110a040c02d2003102400000c1203078400458541d0360030080340072001900c8006911a010320075000c580396060421403c1400031741e6100c1419984240107540b0f0035640071040c1d8a09458500d000915151a001c441b05944800c0c0d00260860280618000030b03c10008400b110320060b50700c0c06c0c4070380d990358074060301284118615024401c1c0002d0052080f00d04c0b502580d9000c40c0000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 128645872 1250 128644622 128644657
    0x2030601180f0608090f0d0807020703060e070e1b0708070614040c0302030c030d0c02100c14030a020d0c020d060b060409020c031e160605040302120a1808030a020a08 73
    0x150400741d210303030507a000000c50007010714040100380e44c00201c40e9440036031203010341050101140c00942d25045040034a00380150314002034042c0d0b108001420044d608006c0078003001f00710341c42c00313500c0f916079005032445000800c000076010603444c202107101501514803140b07400e4464a4110094110300b008542c007949480000c00c0962104d00c1a0740500d00075a0044185891441014944071041d00128000e40014411000040e000030740254565015920700e00c03003402a402c202c40d8050081001424195011403cae22203078800009020b0218a0f6021a207442940c3c0c0000d0720110210b0900035485411180e500d00002c0c00e40d00705040d46600646611b0415032182c42e03480980c0c00c01080003840c1d5001080713201d0382d0300c403c508041d1401c41841d1903629000700703024400c00c001ea4004003d0800c5480700003150800d03208001841c100c03112078803003c0d12441c0b60b1070020310003044032001c00d21100c40544007081908001c02225004040d41d001800c0c13504d03042e9515152508801c6c10f169061881 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 128647122 1250 128645872 128645897
    0x102071401020a03061410080a020c0a12120506130c020106050a0909060b0405040b011505071b050f030726100f0b010f08011a0702040b0d260f0d02030601 68
    0x1039035100311521080c0800540c80e03581c1100010121000f5a00040120b00d900d414400745459408083e10140c1d4285441c2041e5031396a682c101c061f108540500346180f2a0000c10400e100c16000c100e1004101c40c0d840081d580f0480312428280e44090300c8190b408515900c40480654050344006408a024000400c000743c0d1440002d02800c4194072002c0400d0300c810941082265500c108d80d9094402c46081110b400d043e1501400305805004890300320725100e52000342180194150358040798868110800026101d0791003a00e2000b6100e00c50090b9440c0340020742c185004103a9000303403800141d4030319901610640e1400701103540822035505004207961020884014010700c1010112060085214500c460006042c80591a214820002200c00501c6001680d880f05c003d800c221004158561065000180060030f0100070703250301c011800e40e80c40070029454114240702085186500415440311408900d070712580002400c0d10b141007050060030581c1e5805160081c50600d0610400d400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 128648372 1250 128647122 128647133
    0x90c0216030b0702071d13140303040602070b0108010c120b0103060b030a0e0706051e0d021b0606040c0201020a17090708060405160f0311010c02041b03020c0c06040e0f0405010207 79
    0x1058000b511080080b104200c0d20580410880c8002d1500c00038805c6d0f0350703000c00c0d40d2044085e00a00360054207041d0508000a1180c0c0c40c00700c000b52180107040e26075a0070f00380360482c025030007408100c40d094205c500000342c000c01882041c104190701d88502030411520342e6200000d107003541c400d80c103055540102050010281000e14032509100d0000105141c0c01e074000361820040323030f0103e8100036003000500b1504180807070b04c05c88103046c02d0010733440ea80c40711882000f03402143d0761030700d02c010f402040303a010410001c0c40e54094541510104039660302d2800c100c0c282e22508520202099405000d0240f0080c0055115440102c40c01514071441c1c882d00c455090000075071b0f081d82c2540c8043c2c03501d02d40318003c8009100070050554100c1050346181d540105189100c810141440000700000d8295165070f000031207400c9281d0344401d048060b403100a03000390040b07414107545200d04e4030540c685042c03180c00c8030103803101900040c486641d5491500303441c1c170004108403034654003440310000041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 128649622 1250 128648372 128648413
    0xa1b18110d0f15080a08040306020c0717030706060b03150d11150304030f050403170c0703080406020f160506030103120c06020d0b010e04050f060d0606030b151801030203030301090c02 81
    0xa1200c0410340b0025450043c41285070b44c0c0110711031360001d0140900190030401183c0c22603901880c0941c459110301d042c503080000c242c1c410141500114040c80a244020005000c440c1c0300d0b150070402c041c5c540201440c0b60000302c0d1030110009425101440a2400e90140f0b5509840354180720030214008000c1960555106110980d1280200900c005c25401880b2414505900e103040c5003058650340301d171408400d01142c406c1c040b51002421a15038602405624044c54024420325038a558410000f540c03544c41141741c1000380503c1d001045185903548900341110401031007182964215200c404144104008074001e000c40c0c851301c5800100b65002a2076180044100058904407903800076202801404034140300300e251500700640c1c480e0015a00d43c20980a6680c1c5200c460249004401403203160805030002190504020030850640c2c19051494404d4445540c408070009285841c2c010a00000b54150820f01c0140310103444c6034000b000c07010080c8125030900c8040300e110070004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 128650872 1250 128649622 128649641
    0x301060b120106050c0c130e16080d020f070608090a06050c0403031101051608070918050105030c010215061017040b0a0c02070602150a110c0a1b18110d 67
    0x88004201c03442141c41050700c6600402040c00c0035840d000c1803180b0b0b02d0301e403e50b58a50700e21517500c0d402114007405459000d00741c40c0b0403a41c11a5824014030002000c5e445080c4142d0045102c1d07800c140030801c0c40880c0c0110b0061120008041c1c0d90b0600c28203070303420a03000700002c020788103494103080441c020740240c034001c0420410f256950360031810000c0032480c041307000d0a41c0c1d0b81070006001da9a080e030801c0c42101d8005250914084e10f41100c103c941c030510b50720010f0b405807001c0301600000b1065100d070b4100c8a0440c22600001029801680c640320455107150050320001c0005055007000c0c60000b515028500c0c1c1900039a5005018881208040d24251142d41d03100d0204001d000541c80b0b40f00039410745000a007105850500002d644410682c42038003111140f00200302d00c105241c0048901c18040f50119440300f0003041c2080d03841c441e046013a04d60b0719007031400b003e00c4604125804103948000340351003441d1410070750500103040218005c21282400704020071400a040c820030760314 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 128652122 1250 128650872 128650889
    0x801060609180209031608070506120a110d020d05060a0e040201020604080309070302040e03090a0504020427092a0b030c030705031009061e0503010c0e01110a0204060f030b0708010807060e0609030106 88
    0x1300d05100301c87d0b02c2c0400c2034100c01c0c0905010465483c2d00004071310401c1d400b0700031302004104005801140031482c003d00c0c0d403419200d400072910503c441501e4010302c2c0709420a646041c04140d4941c00c6052211065030042c1c0540c00408c08900842e03a054015644061101c0c00c442a01d540c950100e02120b140a02c0605d0702d030004100c504070b03494140d170648001e0108032019070400d820402100010908039503100e5000710150b90301c104e0311440d85c00096000d600101d120f18103031880203036600412641c4055001c00c003401e100204601801d98152130052141c40111360035980c0d03484080c0c032117520141c10902a00d070a0040042c201005002d56800b42040075058079091408418600640c03900c6d400403486641000410a4090b501400e42d01d503841013483c2166100c0440541e81c2d0910b040082d01079041400c041c2c0c049075200100c0c0c403503805c8a2007a01c1d001000c0e40c03209022180c3c04000e0184400c5500901c004004051080c0100ac26550005005510341619100001d00f100d000e58000e10701c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 128653372 1250 128652122 128652163
    0x50a08280f0c0914010c050a0204050903040602070b1306030507110d02030d060f0b0d0b19030602031608040c0b030615040e010819030203031f090c020c0a080106060918020903 77
    0x801015402148030b4182c0300e0915a1146041c28821075195803e42800c40c1000030070182d9500f40700e400c20141d0892034002d04100581e060090b001c544a50050003071802610a5600000310100c03140c0031218140001d00c40b0311000c03030408404601a0030081c0004003005154000d0030440b0f041070001d850006810380056648c0c0340d02e655248151030140e030140782c0c00c5c40441c0040010b00c00080403250100350151780000c2d02c078440f4001821f01c40b010601501c52020f030410110401c181a40150700640c80c131090142190744a0404071580c450448004018a1040c1004c1204581d0325000d150880d0005091b03c450780c0074140000500d81050303110752032400d0107200400c0100c50900c61701c1810352400541c100e890029450203503413880301070650703a803203543c06081040369404403c9510250207001d8041c000c2920702c41c8025070b20200f1002141c810705c1400000103010805200b40411203116440340f5071141d150812580d80781c002045406406502001100d0255909024040c008031010101c0035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 128654622 1250 128653372 128653391
    0x180f140f0f01270e0a050d020102251e1e11090907231311210912030a020910090303020d05030c0d02070f0209010b0714030901050a0828 60
    0x1d01448181c1c0140704031045011010301181ca0700c0c02e8020b5410403220003103850300303190320428034064601c00040c10302d004803401c0100c51541900180101120312074240c20721404104120f280518208000b40048071840366a5140f000d4035114100850040d001000c09000e0107844414000090390100d90240b114841c50344149020808150400c0f030300c0d0000c0804600b00303401105103030b0842c1c6142400390700c9280c0074a50350340d80148018260301840010301c442929003460100a8101341c8542052a0b003015012240e001c0c8804405c1c4213a554030001d04410080b07041741d4007a540060309030103550760204035440c1580c4a02d800324040300403030f40e5104019440c6050084c10488884036880c10040708005114001c40f69500396000020700103001642c900c2c113440c5c100f2020552920007500007000340c00000da0b14007988042e0900750f02490b00c00301c0c0c807100c0d155003580307d02c0b51408082c0031610a0043c40e0380d0510403880359a10000196420350000340340c0e21140c5000f00c08004011140ba140d00ca201c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 128655872 1250 128654622 128654641
    0xf0f0a0f0f0f0e060a0e18100b0405070e060414010302131d1f050603070c06060605091014030c090a0801050c0a1106091c030f02030103080a0810180f140f 68
    0x304010300c4841103400c2c01c2d0130800005500300c0c207503100703102403940d2940201c1e541c05844003c404050303594200300c402c4040c0082c1040b020304817070340840740319915100009003014011100e00200f544028003d40c902814600d42894803802041c45504042e401e00030705070346504000c06030015005902d41c4141d03601c0c83d4100341503100d000a001103600d1111101000207070140360170701c1003541c10403603016480b50799595040b6901402044058100c0d814185e00081140e0050000c00310004240d400481d600c803552010b941107100300b40070301000e6004200041c40c0c031008401034400000d004089009440e42c41c10401d007556030540755281c15280000e0b0214080b0341040e603c1c503030544024040c0942c3c1c50100345160311a0601c29160414840900104403240e102e6408251550202c1a0464a030b58503414220899008180b51401103a41900416054034684090404441c4140341d904060f00140311000040c140d0225641141601e400f00c04540b0305079210028030a2a0b06914401145000c0004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 128657122 1250 128655872 128655899
    0x3011d06060607050705061e070c05010206010b0a020705040506120a0614100608040f020406080a030507021003061203030c020c0405010b03040b0a0e0c010c1b030305030403080c090f0f0a0f0f 84
    0x610b1003a60708209030000076a000c2200e104031507080710a26103a2000c91301e8802c80b15160103503100d0080002071010104000d0a249600f900c0c2d00f0703400c0742c0050b80c0340c0e800a03049114130064140543e000b141c040000380381c55002140e101d803014240401110000c0003143c41c2c400f11150840b240390303d5010741504002269001c41e402141400c8a41002c0e14040000d4180c4201510213021600c11070702480039500d03981c00032402801c02d40200c41d640d0300703d41401402c1e50842d0100306d201d03504140380f034034095110b400b8900a17145a24858160303403c1c2643d05500400e0790b90640b001358007482c041100295540d1003054001e000e60350302545c1c0c0c1c0c40d00d0701e0131111184000f001d60050b40d20380f4070303100440040084c141c0005e00c000c1c00c000407102c841d0308000006a8820b80410ba5840f5079400220400d03a0040180d80945d2180e241c500f0750303807648201d000d00d0f4001d581c00c80ea0002e0049070a0911803424014640030424080e05040e40103440303c011491020b10b42d0031002c07951b100b0401c00c004c078503100c002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 128658372 1250 128657122 128657131
    0x1080d120e10050408041a032202011403040c0b0d06170105010608061c0b070305180d0207060e150304060905062401030906020c060403020706020c0609060301031b0b030a093f0c0203011d06 83
    0x1c0754400448140d0020b000c90000d5603100c20f07000c100dc8006810000040135220203000080410340d21a2100300c01c84010b4510b6001b51104001102403000c0740c4001401030398182d50580d12120134941e0759100b40710704040800701141c130f40d012081010300890740429445019010a55000c24581340071921566183d202240c2c2e0340d010740c011a00d10045176404030b140c0040c2d500528117006208420710000d424500c072481840c03078081e0004240001c0010650200c00018032500c142e0322156a06034400300800b002060807200504014150038103588a17a10100701180714500060071306000740040791514404035170440141e405004188800341d010400c20984140c2140d04c00d28048070400070a41501042c4802000003822280228a034180c002102026000d0b480d02c5a07128030317003048038901174a0b5082055407107103c0761411401c205540003044003030220310280074403000034480c50300c0c2c001d80c4800300c00d008005141d401040142e17000e000d808a8080810f043e240886601029142440c20190 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 128659622 1250 128658372 128658421
    0x30a0e10020d0624080f060301060905010902130f0e0c0702130c09030b0a0e030912010b0303070602041d01030201020c010e010315080115050108060d200901080d120e10050408041a03 80
    0x101c0960341e41741e10603905680441a412048200c1e10f801000c00d000d441c0d180c008018040c1440000b1510f84411350142c501d500f8900300b660042c3d039030713414400072501b4140076080501c074904001400c26829840102066071015003101c2c040e07840d4000c2c0c1702c21a01d08525003400900030120410900c004074031810340081d18034000b00308081500041c1c581da40314801e030741e40c01200c10075403d030309000c42940a4516000302030180c0340c0c0c03080d451504100079803041c0242d46920000f08542e400700c00d007250340c85058a5040c6c00512100354220019103c00142003042810103844040040c00480301100e400000e01e0343c400046800103512105104050564011504101031a010040c2d640d850790b6100b0109900000040402841c4080c905401c4000c440c580360040c500fa4000240c1d0100060007080720b201941d50305200c060b070300a104040d588003804c0c01c0c4003507114001c240030241240c0d004a030058071403c1d240c0e04e41941da0984c01c040301048919140c285d0800701c10880040080c2010441001c4c07a10f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 128660872 1250 128659622 128659679
    0xc090a0b07110102010e010b012304091b02010f02090f09090708010c03140f0f1303050c0106031103060906010308190e030a050604020901080d0816050c1509010c0507020303030a0e10020d06 83
    0x4200081070009143c0c260700c50041d0020341c201e40000c1c00412100030300b90008083c0244541041d076003211180e0304608000550c60302e8000c41c0950114800c2d0740703c00000420941d40c1e01c8030b0004001e02c5030b4000d860074201c1e00a10400080f0301100340305241d0118150784010400a407560076a0341c0384000189a4150381420404210300d4841e440080c80d840240c558540203181d4003414110781d6801083d44000c69503103003840c044103100c40c00341000d10314203045046a0007035403907003181c580b00c1a00f8403000703107151014405895008100e42409440c14291720b022003507018604002464440055015141900071105120560a0246040d4054140c540040040c412540f030b00501c401d000614000c06d01c1c0381660402e15031482201162034649596046a1b0385404100f001e4801600a5802032020340c0307081c1815100d42c1c00340c0140d07400355030000c01441c11036403100f400340003800c4a00c01244160080484502d8840520f10240c01c4860314400c0003c0c4907400d180001100121402c105503a20444 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 128662122 1250 128660872 128660891
    0xb070507121406041b080309010f03020d0e0109150e06070f1b0203060f0108071202030a170f0f0706201603020705030d11070b0a080c090a0b07110102010e01 69
    0x18960048450700c84240c24200d40c6400c045100714440701007a607040c01080300344814043c0c0748041c2940041081c1118500c036507121403540e03985c42040c22150116041100c800c0320070340607a01400c65006044c00201d0403902041f806407c640c0c06050403641c081c0030f800300c2c864200c210b1080c5500c5804c1c10b40185101c0c2000b0318050300030840b00609034200001d8089090b0203540707200025400d130b50701500f19942c0703042286803249403000034001c40d40b1a108044000a008440a921600450b000f5019020403e4030380c0703c3e000843c00f15a8840e40440040060f07800c49900e401c0148045282030b500651503a4080c6091410ba4800c0541001201090302d0418584c44480084a102c408007510890030381c02180390903030030146103a1007640d150040004c40c2c034079582c001807001109103041c0e040d01c05403901ea0346100c1c0c3ca801040701400010740c040d03001405201d0000b00602c02001c0041070014450b50310392040c40e070b590210304202e60303c841d0106007814030758090190105009444000b8009102d6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 128663372 1250 128662122 128662133
    0xc030f0c030605130213090501120b090106050a030204050c040806010b0a0e1005030a0c020a140a020a0b2802030705070605091003050c090105090d02040204080d080108010c02030d05150a09060603060b07 89
    0x449840c000040c2e0b80061b1080807160f40042407001414204011f102640c1d654440002101501405940b1042007100003102d0241c10302c2070606a40006001920382402e640a00c801400000d019140000c4100b001042254040068500801e42c25140c7c1b0b076109400400108481d1809000d03038051000c3c64030301441d0542046c00c5e254000520f283c00600e1240e0510200e05d0b00306246409007403001002d003410361103180812800c040034000e54002c2d04c155500c0690503818840c0c510040743e8a0795000014540c4000400080011081d0303204503820450280c88240c14402c0070b9025901181001610309110705203000300441030300a0341010051803808411981c2e441c4280100c103810018009003148199a440010b4545a90098811520346803545200360b95840046900780200d00f0072400080d18130b074140075040049401d6805507042204140844001e0040a00700d00402288445060f14079243e9002c3d46c40100b481d808042001e40c40c00a0250481c0c1d45038000c9112084c08000c010701051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 128664622 1250 128663372 128663389
    0xd020f060112201e0406050102060609040b0402120d05030411030102070c050114040f080105010303140a020a0f15020c0105190b060f030c040b07050a0203100905150601050408010c030f0c030605 85
    0x64012840442043d45030140e640185214401c01341c0c07160001c0010103848000c0f00c085059540d040c1c908020071070f210342c016652101c0840b080365006284200140010f50f0205000d50000c0c80600103045035604400f1090038003044040d020000f80f0080100001e0142810352071005013800d9000b10f24080060b00d480105140600a01c0d0500000d0403103903007085500c6040f81c008000044501d01545d844070800c0380a407070280b005800041d030740804540d010034660100c1d82021000c0d001040700c8042940d59040c3c0c2007401c1800d50303d401c000407049141240900041401d41100c0b400001d15141229940540301030022154035034501d801b80d000920740314081102d01c00e40c2c4000790941c0780e66035400b143c1030500c1550030034011058081001410040001001041107100b20f00b95542010441604002c40d02440750182456020300d18500000034140c029071f03080001854080e15041e01e614102c2d0a465840d50b0000020703588125030803100b2807c1c850f81c0b03204407452505001c29440c0000191003a03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 128665872 1250 128664622 128664659
    0x105010801060c0b190e0a02040b01020d0918060902030403110f03030c0d0203092104060e040b060f090112020a020a030e06033c040b0711070305060a0f0603020a080d020f0601 77
    0x11009980030a841c10111411500e0700c8a064000303012050f080b031b5500b0b49805200004902071810704000442560000c55142c04480701e5541c3d07400ba00e481e04400c010140b40ca484003007101540c507580850000c045000462043d4002d45901240345150748000c0d2803d284070f6400585a0828820310904903208000c03148448402d0700056183d03140d1800030b41c180348200d20345001580208041400302401580548206c6041c2c0d25034800c440362000500c802c4d190120101a0f112034100700c5404203443c0d020203054000c406140010244003074400c0301c8126440b055080c00941d0010180b01c0030150f010101a0042405860160550500c030042e4903000d44110403804115080120101e000ca815440c268240088005002c00b1402d05003024401c00d607054500400080c103058500e4102c0800051003001c403030740440200303030720358039071403000011b20042d0880160342e61030700c0000000d0f82c6c413004100064580c007005458000d81c0940041d241c00c2001c810031985401c000300404c80000040740b00c0844 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 128667122 1250 128665872 128665883
    0x90321090506061e030a0302071a0304080702040e0c090a06090612020303091c0c0e071d09010311011421070801031a0601050d0203100602010c0513031b0b070501140105010801060c 79
    0x2a28104005025021101c4c010702d130940700f150b8010044c10360000d100011588074040040f42004401456403261004540c040c146550801441c00107050651010f00045400425103240f0228540025100c0e03a0585000158684800044c0070440e92032017018010031226408102d803090650207e512802951110782c171400501c0a0204410f0f03485948d0b000751940312941122143c0c850400025182c001c0d1340020010f0450708071480c081c10720050103403410200030f08009840e0718607038038138141da00b04200c0a810010031000c02560b80e065540501030440400c0b495544a09440041c1740758144014008401c029140e00100f0118070040714031a2803084a4800c0030351b5641d8900103030f420b0f10402d00880c088920000800c046403c1255546080d42d19980c000c2c44035900a0008658501131959001000021220104002500150420080c0c0c4650340c0d0001c16544e1400a001c0d1900100401e03920340c0d44500f03242c00d0120502e94900d015000c00d080010240d410003000400c1001c01e81c400405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 128668372 1250 128667122 128667139
    0x306020315030f01061e050d1506080703060e010f0b1008041109011401140c0706030207050c0a0e0703180309050607060f0c0c030305011a0702101209032109050606 72
    0x1034201030680030a603003034002e011620450040c545013402410f1604c81d00003c1010020f40903d080c1120640500b1180c000f000030146880586840501810030003800e050181e0f20200081c1c14401805a500194041d1600242c1d90610140280c00e5441c1801c1400310146040040788070740d0360341c1499488617401d510b402c82403507603903240032b03c041062180d0b42544030100800002d120300c41c00100d40c01c60751003030340c42080038511141401c1c0c1038003c00a440265401402042c4a0a0700ca54043e000c114000c81c100ca0944140901007842c07844290890721305400084204102290107010341e0007000303a40c00a8210700101a01c0c02040c0309190f0145c0384c0300c0d03900000d101c2c0a01441e50012161450401d004200c04030200c54050710305615904218040703820200005041900d02c41031000000d4210141481e0441d207900b0040000c0c0b04003a12010700c85121500c071400e100305c0c480c691b0681d02c40d81f00e191000c0e1032030b900c00d01c0307000545c068051002c1c141440b04000400120b011034100009441202c3d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 128669622 1250 128668372 128668381
    0x1032409140f1b22030b04110f010e0d0804050a080c01090611030a0f0c170301150305061e06070b010803071401022b0902150307080601020f2a0d030309050f1603060203 74
    0x214000e410707441315481501d811402205011081070348038001c0b0b1060b451b0382408200f420501c1304101304002c00701c0c003080c01c0004601007401c004a41064280c45640d9452800fa204c0d800a03218100981002c032069020304010380440d600140c2000280c6540d04000c10b2403200c0381c50250740d9101d181c440364200200498400d0107203010b4014200c1e282c0e40694500004002e01400007a2600709100e0781c9031050308405003001c07250080c070445000e244040c2c440003e100800250311311184000b15959000b03002008a4400b10340c1c042070f414081c003040f4014550700e4055003851000012003072200704250348104003017517070113400a0381a0340ea0000a00c2103a80d000c0c2070199031004180402d00a90840784002c4014104003140d40214803444d0310341c031011036a840d600c1c01260740c0c074000008003080d039104c0c2e466070050482e20b01050f091550004454525400114082510421400c030110080398440741d51200300030f0f003404a0008082d001d40189094550481722001d00f110604c00030301415800400319 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 128670872 1250 128669622 128669647
    0x10b040311060904020c151e0a0504110a0807080c011103090d1128120302120c0106090905150702010c020705011101020706021b0105060103020405060901032409140f1b 74
    0x1100d06120041c42152603080031802c1c076071580d0040014451800707447c0700080c0000c851400103610b2540041c0d00501a0361100c54150061201600c2903911810702c0f5106442c5981e2100600d000d40444000350085a00e886c0c05075150800941045061010190382c02084802c00000d40b404554100c580c1e060304212403c04051141c02c01c034240340c100141b24041260180c01f00f00e56581615080a08200075540c0e5941082c0300c42c6003140140140c01c0035100d0114019001d016141800d01c10000049190742c03284500100c40448508980541083c101c030b00b84610f5802c1e031264031039136600013408400e20041000303480c1c001d103000d12418480105240036034100254192100658003403c111b5588005086c0400e480320108010070344c40d802c2034000340055200b0f000341d4080321001303054036003040030031001500a0140d604041c1c0310240030b1034900c610380e0b41080b040c400800883c600054150503101c040c441480b0b00400304222114000180081e201100741d103a60404090350b003a90f103940000200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 128672122 1250 128670872 128670877
    0x601030c141801020f01090f12030b040204090605040e161208130f050a080a05060106120f0501060e01090806060a030f030212040609060e030c010903080f070605040804050f0603010b04031106 84
    0x15081c100004a68103202c2202c41625800c0d82400340c00705d841115400d46590309035185050010312101008004400003051400c0002242d104c50802207031000321b040c0418201d801c15400303a14400e84488040107d400c0070b100d48244100e82c14080c0c20406000903480003201c4d01446506502e813214006003042c41062410b0b2000710981da42020326484c0d581c1c2d148188640140681d5100340008132b40001d00c904c00040300791140d584000078280ca60720303100c41690001000c4001540807604c1c1d088190340c0103424825140a00300985415140c4040c4000042c090480c0d600103183d207520070814080d00d41e503a00d00160450b540b146105a800805113412403d180840c10034112003c000700d07000c1240754000211303400755400d0759255400c0c106040308041c0e444104280381c0d0702249004400348007042c0200700415a03034003088044c2d0b00e008013a555001c1251401c447c11303500d101021805000030728103002824200c1100322592400c55050550b00714052080303100050201c4600c043c040c8003520f40d0b07800e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 128673372 1250 128672122 128672147
    0x203090303121807082d0a050a061a03030d1503050607050309120901050318010204052107060c0b070302070309030f080703032a030e070905090d020606030a08030601030c 75
    0x640e42c44006a40e94120080e00980f4404000d451510b0b46a04088001034103104903080c001c01011092001000c03030701031034040d1050390186624a8501c11886008001c0c80000e24424401054125118184001101c000583c02c00c01d051412200c042203650020a4408480115000040003141180ca881d04120386a10040c00d502554040040c810380244c00341d03116070220001c3c3c070030b02c0395070901c540454404c00d15014080b500034808030344401c4500c00c1412580208200052406494000007045044444070300358403840b601c000380e09134103010300c0940020000c0d07040c04042d8504a86d654014000c0040c0310b8410940c1c00708165041c18800c090f52402941c001c0a2190008260304061034103500285c8182c0c00710303040c03a00715a4080d4506004410b100d560009188a58008000c114082c1011802031000b5209004022540c01554407a03a80603400c21070043c203581403140c0c4043e0030140000d0115200e030f04403800300d03c04034280800f1254422001d20340001c05407a4a54181c4030940d6119 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 128674622 1250 128673372 128673379
    0x1120207120504060206092410030503040807050a0806040317090c0a0608060f010809070501050c0c0913120507020109090e0f01090b060f0901030c151b08070605150a0b0a020309 78
    0x2548a2107540d00700c001041982e0a60342681d02554848075101c2d510b1105544440190714030000e04030142ca000c01d40b064018103207484407541c081d5241c4903c2c1c5980c00641140e00381790810f0074204010b1424030000c00003000010098002407510b034178050001c0d190804c1700c240007014017001884400091203002c1c1490b40040400c410706844840041980004555850040030040280619580140e070424070603100440102080c0e070420004541307640044140d1034591290840701ea800b40e580c040768512a5840c104004100011420320b5200b01d4032480700380003803120802030800580d0f840350170b40d070039942c00110128002600304542494000c140344d1581c5103501c0c11103960100310500c6d51082c041c90703041320b01c0520400a4003c1140144080c40014050091000308003d0038140b180c0c15200e00c640f5007440d1a01645220155000112161007150ba40000103806403c10910344622a003048840403041465080718002c1010044103003d0790030814000f02d69800803034403c00c02c54007010b4014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 128675872 1250 128674622 128674643
    0x30a030203010e090303090705010e210c10090e06010e0a090906091205040b070609020f09130c0b03040305120603030d090c05031506060409110904060305030a0807020304050109030201120207 84
    0x4000280290801c0c06590010b20720440410126407000081c0ca0050000710040c0c4840351800f001941d8003c070011456802c00e001c4034901a500310411a0404030000c0f010180c404040d14504004200249003013907001d0011407001803150700400d2803902c1c2d0065003820320440304041c0d00c000408501e0f00d03038401c15541d814801c0d00c104105054205241181c4203060401e0101c0c46110182ca250040b03000c4c261202405000b05800305000e174001c486074600240600d4240d803404c50204010b00c0013100c0110418003200c24040030405441840f4008141503031100d0f045042c5a07070024050301c1844400f0b01c483c8000310100b1341e079a030148100d0b14910072040b410171514816161424000c8006d10465210f401600c0c410f041c10703103000c844a8410300009000a10301410010040c0081c841d14290523000e2000b4004504961a60300ca00c0e40958011001180c440007982c01c020f00304240104035004542051000708011b0741c02406007015613a090810b030120052035842c0c00d0090040b200e010700a40c8a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 128677122 1250 128675872 128675887
    0x70c110a150e030705010e010c0b0a02040b03040516080622050f010c0e010305010909030c170c0a0b0a0c0c0503030c1b0304140a090b1e0117010e180a050601052103 72
    0x4000a9500d908059050f6010555200019121142040b442038086172700300314060005a5034450040d8000c038080001801d194441c0c0400c4046d804c1201c0880721544006000d41000c4c200d443c0400040c40c0800003480d10b071402c40000d40004014200462000203000800c004200080c4203450741607110704020040c04c0d0011b80001c080e0400c202045011078500030000c290060b80740900103216405445040c40e244040d61414030118540301c08040c0314900340511180040e06009000e4440d0140003c41041c2c140560408200c444150072502442407407000c6100041e400b00540b03034405081070119840b0140440d404d41c007000f0b14200c902d130b14080080d010034208180340748415015415078050500a854860000484009110007a804400c2c9d05da150390000740a408001801c4040c0f40a1040900c0c0d008404034030138081c0c000f40b102500180411006c03043d074546110291210b1130041c03540300c105481e01a1a02410b00416004400303070008016600b80a4504207400c03644c03041201d40e0f0701c28 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 128678372 1250 128677122 128677127
    0x20102011b02061f23060f07030503041401020a0c120201110f04030516080304090209010e04050a0b100f05160503040e0a020a0201061202090f180706030b18070c110a15 74
    0x10111a0401107580c584980c41c1016203084c91003081d50201d206545501d00f2000011002c28800f04440d60703c6001001002100c4d2242009070468078032907102c05460b400d003407030f001f412842d9001d003400d00c0e40e106005500049a000050a81440d005803600c040580318210482c00340c081000600c404420000700b014000c07407132000600460b4002d50613030311541112070011000180300d2090f0704181c1d005020034000558254002d10403a0814144100700c96880404242620b20440740300c101582d40e6804104541040d03481c2c9240030302b03507162920750138041e072202403c00d0044a000b550104080880c00d13003081410022200601400c03e14030041d49844071509000c0d501c400302000055003440e01c00140c8610300c20340c8441c3c1d9940200300962a170364291064418007401414900d82c059021a05507040006104040242115503004104490440244070182e00f0701c5200d541c02d07403800b40c20007217070603800000680c44650001e00c1c2c001c40e0740c5060005051034034940140c241105105038030000d258 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 128679622 1250 128678372 128678383
    0x804021c150b0f03031e04090606030f0b060f070b0c0c030c06040c060516030e0d06020a0207050103050c0f0a08070507020a060f081e0105010320040f03021309020303090409020102011b02 82
    0xe020a000c2c024040e6681c00d001d0311031012070105030035520a00c204c114120701500002407840301c80d90f5150809a403600034405a9106074054030100380d4404210700c5100a600030309920103c10303150180b030040707040ea0f0802184506032000e0200b40d09c80001c5080400003d0446071040058021a502ca20321800943e880d1801034030212806a04290f00081140c01001541e01100a4020300c8032818495103058900040c24030f403c50b44407800051030320000e03684e8405000704907099402060180c1c1060005000ca6202810700c3e034015a0500c46d01c000b18140404071101c1094034508002c45480b80f08041d03500e0702440d00025030010604501050040d48032a07150b03160359056980031441d451f007814900600701561300c441d541c121200e005100d2540281c000f5000055406004282c0610030341e08000c49030042d03086604074078a008130030002c0d49411504264500d1840300108488002a4006582c0b0712803502c84902aa480d9083d074819603000f980005082d0200c0351aa006041d0740b204025140c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 128680872 1250 128679622 128679653
    0x105130e0303100e070f170601030b0d0606081516050901020718020901031a0117090c09010306050f4602030708270c0d0c08030f040812190804021c 65
    0x84604c0300003a04148201004107102075184c803601d10300c40c01e41300d040303100700401024681455240c08004415803030f000d0380e20011601a03800041c645090901c6141441e00440600c01240300400500c4484511002c41152850150070219540e400010041c0d042640550000018444e078a1110340d0200c460380090080340000d9a080080081c80204a4292140710042c640000c0e5610b10785642c0000460301346804c42c9011701182c4509003018000307404400d003604221a1142c48405200500707120003981504110782d45201c18241460440c000c200404201505c11003020750941a448200300c101c02c40a8407404e554103650702d1038580005802e0500c1641da0521001380c1510480d035540c403031804420f200302d051010300740d4012a101006001201c0c0f903c241c030032060f114400070300207104100424150084a20403900c44e07240c5541582007800348558100241c404000f080083c102c1e940c0c0c0710600340800d00341040b09440b82d00102e006091305000d41c0018062000442c0c091000c4495981c204 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 128682122 1250 128680872 128680889
    0x30702012c12030129040b0f0c01060e040302100b1915080a0204050a030b1807030b011505040303050a081302040f061a040501020703080c101407031b0203030105130e030310 76
    0x450a5030301c80c6a41c8070034400c5504d0325100100e84180c9190045d40348000801c1402010705040c0c0700d41744500564040301ea0764101d010005107a4101d094203003e610010404090040641e01e4152400ba40724841503c1d0400c00640c0c07001c4d041101e654400200c00d1040300b068444150395203a5524080c1308140400403004280e581c40003c039480c460340201c90030340310040c0456018600d10b9035520345000e40500740010b480780b07041007400020000c02001c0000d5010726000e110703c0d40341884201319020801019010081c0c10003051000c20340150031901200d00601e000c0340166200c071424003002802e500300035801403d1440034101418580c00c034109036a00c00e0b50064144444510759044c0748103603c1542c0c090381020700c080021504110240ca110f0b140c0c001034400c2d40700b003109404111ba2900c1030804550000200340031445e54144100242a1101c00d0060080c2440300c00103550f81c0014828540b10b0702e2f11302d517100d9070a1819080610f0f0003141000b12503e030300301003103c18074801c9140a031150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 128683372 1250 128682122 128682133
    0x5032517090105060f040c0207030f0c0320030a0f02060705010f020d0b06090306011406070609150b0103090c0308032a0c010b0102060c0a0810030206030a0b01082a030702012c 77
    0x40110042c80348134001c102c0141500e41c0800c0744002d01014058011151055008944000000c07581d6192600c001d00d2040d80030748501411072130039811942074041c60b068803603a0b402041026803800078940f0105a0800b0392411048280c2c40011203510032484003d040c0c4d403c20011880c1104581c02030703c1c076030351504424031100b0302d0308051085a005a4885c20343c1640f18100402c94040f014900111061002e811075187c0347c0c00340c6490065603030304481100c05410f03009010550080034032600311526401d113410301c0102c68a490307600541c00326000243c00744100101084000fa4000701141148010b40c15461101d8105d51100000b0303044080e0122555080a24480b81984040360315845480d071241218103041c009241103c1006000709104004122030b100030015980c0c0f00c0146200e4940c100001c1401c0c0301c2880010241c0303101412001722550076069010070a8100945455903a6900194130780300d58660f00304a01500f0706c1250013682140d0704203044610506d841200c4014900c038001c441 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 128684622 1250 128683372 128683381
    0x70c05090903090102060a0e120f070b101503050613090507030c0e010806191103150a150509060304230a0c080d08041e0b2809110105032517 62
    0x30380341d00ca103180c440d0068019600160031902103038404001c0d038404d48d044803100000c412140746254800c441007100604040307080002c102c00c8446d1107500c00741d0181c1c4901850726191030700e800081590304176024141c5600000342540c42e01c0b0712581d2813600c0300d00c060141c00c0e814101281c071007000b0700042e98014049034012402c1c0f504078411354100c600500091845e42c3c0c0315a40c102200c0301c100316018047ea12518681c0a0004003005140580c0d0728050b502c0454488608003c002001d590240e80c041e01c0450184000c0b94019080d0345410005440d090381d40d80c2c1d40d00d00110644070b04049150204542541d2108c2040300080a43c411441036114040c1e040d15101d00695802d034006044000968901c001000251080312040148003a00c040c0204008240d440044019040341d640144a800400e44c1d540c110b4907261071080c141c00a107080100b0165a02c2e4508180c2c80c406169041c400c002020403040826a880c05c0c44074203201c80d2200c2070052030500204200072502505841800240104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 128685872 1250 128684622 128684641
    0x21e0406080607020d110c031e0c0d030906030f060503010207030203070b07050702090601050a0c050d08060117010b1812011121070f0819110406021203010b03010e0402040b06070c0509 81
    0x2d409a0307495001400d980300b1a500c121000c120358141e40c62540603042061010392410809500491100800f02d4480558000c00c1440d01c0c1d41c0580e49445055108282e80120760130003905025a2502d28000c070340414500d40144c060450360380a81d405600c00103900d014150701001a00b12584a007401c02d0090303c41d403004807424041c60001a600407103070350200b12a90701540c004d0030b10b69a07a080644900d03009441e181d0801440040b0100819400001c024203581e20803001d141c11840d107003020540b5414603404640a000b1700d4644400c18426450400321551401c0348810802100c030020700030209101e0000030f080d001141c01c02032580c80742c401d400603e01c55242d03891107640d280c1d0700c0e40d250150000c8101c42c0e50002519401340514100c480d0800203109000313007442403000c03041c074664941c900440240f511914420301c00501c001840144001c4841c00212411075003070710704240c459192030000600404094042c81d9006200160b060104000088124116070040b03c0501c029031701c01ca00d1703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 128687122 1250 128685872 128685883
    0x4031b05240304140f0a0b07050403050309040b031e0a030314070f12060f0b0301030b15090106031a040c18050102061902160209090f0c01021612030c021e040608 71
    0x400421a15001d010040324020003455000707010f80b0100c0340a45261a2542c04e140040d95030021540059284009202e40000d81b50f80086841c6001890a495a12010740341c0c000ca501e00d40c0304940341c002c140501e5070100903004488000e42800510700c21664442031760307100340c040704401007402d003a0845c4030030541c0c03050b0a200382e08681b9216656103003042e00300c072100f5040c149001c0d4a0355902d030200c0c0d81c82480c9031034005051251180c03681d9506500300480c40a8004000c0c17210308000e5141007040362602142141129610f09011840c40021801544064901141c0c00d80044c0341081500505a0051505040003054044580c441c3e4484004a03110002120035a600079403610070440b01155a80c01003210040b0790842002891640c0c0c000348001d1803d4941100780e900220040000701401e00c0744d0400c05009000030a5444403e140c903200780d0216110b0000001040c00d644000d060054803e5240340c0d82c01010355007501c000c0b1018400c21420940041e00039071800b40045007052000a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 128688372 1250 128687122 128687149
    0xf030c0504120215030c040302040f06121410050f06100e090c2d091c0201080a050403020c090a0c091a250b0a050601080f0402090103062004031b05 65
    0x1905894103082c250108901620301c0c104076009400707186100110300000c1d010798058070b10285e000b60f5882c6180100410350701c0c402c407081d005a181c0801000a0045c45d080001141e0740088144000e00520300b0b02e40c18154141591813013503040a00b00b000b11444800d1a81c85005c04541d09110384082d034404503080103d004040b070300403800c0d0020949514408024003034aa460100c0e01030901c8081c44407401c68040b660401000e2070f03021501c880305141082d689a2002800d80007403800210070f0700001c12a80c000381032a000305907154045400e0510902074a501d105018290041038107040350318100030020b130b0450600280600304042040400b21409403086c00440080c4c40c20540f00700000910411622802500d150366041c03042c00243c941181079114880d0302c400004c00c0d00d4a00c0001d0310740031008001e2080801c0d00b10130400103949103c3c80318103403900064000f88500d402c50548400040717040b0182410800802c00104100050380e031441e109a4134039035281116941c00c00c0c46000340340c608 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 128689622 1250 128688372 128688377
    0x9030b0717070302090301020906070614220b04060204030f150f06060e0613081501030605060a030f0f0212030705031305060915030403032d061707050906030a210f030c 74
    0x1000c0b80400c1d2194001e4280200010001460010410002020307a4801581242d4071038440e0750001c1084d07810068650301c61280d03442a880581000b10304031103480406401004540200045810b00002d5410340700516803011450120107001d0502c246084500140d00c000c49040c54081d501c4444280690011902c01c2d840e0407a4000c003c0c000c1216170f40103000d0f2030311a00602000026038120401984425460b0310700031101650460800c07405071140100550f010302d68041e42000010503040700468180d801c10001d80c030703562482c0700041e25148090868000e5110218401040c09004002058100306140c0c0e5070b25072030740e18014400030340252000340f5071204225000030301c1d15007000e00560303220f480303841d0008614603440c83c0c18241d00c8100c03482e216103858039894414211180e01c0743d50082c011801c030000203504a0b4000a55400c118000c0c0e030300440b22500400c4039510104829100681d014041415031141c40d0140643c0c1902080c050740000c00c04071020040e64001c4c440c5040300c00566 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 128690872 1250 128689622 128689667
    0x150705040f0e041401050f160309120c061b0f02010e01050105030307020d03090801060b070b060a031106070221010c080f04081806160c050a0605041d07020a05060709030b07 76
    0x2c0320400500900a00544407041890b8a03805940000c1c858603108101619240d50382d400d1600360121084514210142450302e01342105000c5420b944e0368146032441842d200440c0801450098003502400e990f5980380c24042c04051103544c0c008080f200c24070352507030082000241d401d24441c280c640078823801d03415800c101304500147c24447c40d04243d41d4041c0c1401c6240c290b0351001a42191066404009852000b04401c0c0400070121411071300650101c91000d0301900f1138490012400128a1451081c2d40024190b0b046484502d85541040f440b05400c240c8100c403d80154040c007010141c09001130b0f5000000b40401d002880603901540c4c2002800741004191000c5d40c1c0100380e84868150700c020244108000d829103450828100c82c0315082d491212407900023440200d20880d0080e0051c40401c1c0418005201303115200e0080319203045030390300705840c1c4210590400400c00000b4002c3c1c001d03441040407168010001c0360840344100e2042c480750766034003811180819000510441440c0c003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 128692122 1250 128690872 128690879
    0xf0c0f0411041715090a06242108070b060a150e060306040612061505041e0b01030915020304050d050a0f180510020106081207030804030819050405150705040f 70
    0x36a0043c83d096403003100702d07901c085004d02e0b0100000421641c03c03105038418200e00c420004240030b001e0b0205150003884521003551450028950001d0040003070000032911001e404a0154811030300c4c1a800c402c080d03940783c1d264200484c0d80d040460f01117000c4e180c45100000e00310b180c00240d504441c0503030386241c030545010042040a40c805030602d0382c0a80c843c030700420362180c00c0c4580c9803c94030415001620400006100246c40b032542d000070310881c90008400311a6603114002000c84d1810400040c1d240600d50040c2c00030003103d0f1001c2c102c0c000410300d281c6860000ea0081d070046d4000c00803921090184002158148203040c80c00002910001950540c0c40c0100a50022035103003180085c0c4440d00c880114441000042c0b031800141e4490008011390300c405e004e004c20380500042a2031800c00191406080c1d41c0000c1c1c0014100301044000543c9244030081c200340901d00f1441c01d10141c1003d04043d650303410b035110703003130729400958003c54082801241220121660f009181a0071440c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 128693372 1250 128692122 128692139
    0x8070305031804060f060c05010b0f010207090203041707201509120f0d05070201030513020604030b090f0d0f0e18070c17070b100e190c020307050f0c0f041104 70
    0x4011075400d403c1511454042140c440d20303800c04014003115500e0041c5030301c0d1030400509484004042c1c5008280c03003a4111000c1c0d83c04034000055842103180940e0701c0c1c0303540c5041c0300350800d55110702072804404aa06400c010b038244020100c9100b00394400807500f13101c801c00032450781c3d42100c8400001d04008202942c04c01191001840404c10151090b42c41650360300741c245001c5c2d505150018400058803401c568040c0f05154115501a00410740502d40341d0100740c0034400e41c003000e4540b4035a000002d0b0310020411031203040184110640708107080e482e801508803908404c0d00e0703000c610b8440701d107800340c2000000400d1300300842a100c009600d44480554051034044400e503041d100342c801d00e9424440000041581d103128001a002514091050440b650a00d4114050020505c0e007032040d2000c088000f9024980e15190001b82100400c10603469407190340801801c1e030046140030f030709a11012803000032071081500c84250b481005010042102c0d0241146561080f05000a0080c280e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 128694622 1250 128693372 128693407
    0x90e06070f1115100609120803060a030c090c0e090405120a0201020d0203010b210708040b150301050a1d010207021f0302090603010e07030f06030f110604090c0503100807030503 78
    0x80c41c00d00ca0700003079001d554141030190214600c3c0c00c03021580148940b0b0002107098000400c1585030a80415060148000030701100c81c20160601d50048041030701a510584101c00840e44045004480c81c0c3d00c10303c0c58040c0c841200c40d000800c6160040413100c0c10100700b0540b041d40e11901421458454031900c800c1a0030154035a0304640d0b0030302c40000000e07030301e10056020340035410b041900e4860f0702c2a0f0035008030001d021880030002e90800e0180f41900031100d59003195000510300b01940d600c0032002d50b201d039100b440613819824a81404512074158ac4012070301184075480c00d0344014804070440c01d0f4456050002d40003400f0340c030031820000f49415255940c849524016182c08042c0000070380b141c00030b80040c07081c100c618041c81310440c0c1522854840340000f08050103264510b440d5030500b20040000507125030380e4034a0182c450b680b01c20031500904007410041000700914280203115800403110522031750b4081030046003192000801d50202c1e43c3c0b0000662130907080c04d03045c05416 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 128695872 1250 128694622 128694647
    0x913030807050f22060513121e1406060a0b04140a1212020705040b060f03071202030a0b1305040b010b0c030f0f09090f010302060d0c020307060e0313090e0607 70
    0x818280080b48681091030002d0450803681a01c000100002c2c501c02141c940d4180d11174001d00c0300c20414810a01d440320a82e8003180c0300b11182001c00010790604261030b1404c40c0e0300030140c400d00b100820070070001003024211005200104c42441c0d881e40c0601103d43c20030f01545910b14000d00c0100310325460400d4040000300c0103003460310156514116010728440410046482d03030344d1615651401a41008040005c09048605025950043c0045002c6201795440100310010000014403d940103240c1c1c40041c0301c2010003113659140c110310480042c20b034030050b2482801e40008001112245000c0c541c09990054007800841c2d1078903410040c1740d880070034042540d0000f842920f40b0a11408007401e6030342000b681840e5100c000b00108203034014010301c0c1d003c40302049001030000d40c9804082d2000020908000620b100c800c682c00da107580102d0b08010f117000e00344820400e0301040803000e48011b041103016011440d440e441d5190a84414141e4042c04e903000c000002c00d118890896990007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 128697122 1250 128695872 128695877
    0xc030c061606110d020705190807030c0204021216030608150f040c15020c100507120509010c0203070b090f1c0b10080616020715140705031b010b030c0913030807 71
    0x1d4031400040c2c142c81d600030030410f400344c903030200780c24050007020701079050402c04012030707150041c41c181e640310182c0c043d0040c054204501c03180c0190071034a07254126101158000c0402911745414030f2902244144060340b000000c2c1004000515210000f4000a1800b91400e00503626903400e407540102400c001c01c140e61002048600081104809854518500d0140c1c060034050005e07a0611000c0b802014003681001010882c90000c90b0701d26942c5c50b1062400c1c9412599085541c004a451061018001c1d5040c000c5050018001e14144024031208005403100181c5a60354010480e071501150005900c490811541000064070022902d030b2059164520101194403103807030790301d803500c219556006072140c020000d500c16010816035000780541082c40440d405561001484041410200b4808450100d440b070304010f414401e44e64090121070100c0758035100100c14a0280c02c6003407070503000340141d82c9002e8480c180083c0b0320703100e0400c1d1441a0030301481a90300f01c0314140020440c008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 128698372 1250 128697122 128697131
    0x110f07021807090501080117030316030617100f0e0a1203140403020c0307090e03040b0c0106030506040b0103030305090604080304030503150a080a0c0b0a020a1b0b0307050301080c030c061606 84
    0x909000d4881141c0142c00c940d90f5160054104400035204481c1030b000031f03c4961854444030314050000003105d502030445456210b000e031010b4020b5000e003c01b9080303020034059041c824101c24100003203500032100040300c140402c1d004205400d040329107079888080c030741d00300c00d00c1203011a0528180c0021100b0030301e8002207042e8a18002c4c4103456080c1c40450058110044120172480e08002d00b40140c10b0043c0101701000b10300090300e51340d10a0348200c5103040e4000c0740050b4220790079409640115041420758416242030b20307001103d4070003400100c012a00e824003240e06030f0b4000450780d204903400600a0300d140c80d00c1d2816540e9400c010506d00400080d09910b5489403078503024400140000d10082c400010315150080f0403007642e400003040300c0f406004441e0034a40c001145520b01e46c03c000300c440b050a0040300c142203400715401c40d03000000000280000d080c1c0c00401035040b070704102c054410f405402410075032143d44107110950b00c13840500c0307a00403000203d10b50064040c0b141e040040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 128699622 1250 128698372 128698399
    0x1b1e160f06081f15030b180612030d06030602090306071706011b0609061e15050114040e15010906021603060e01090b130209070f0503010b0f0c06040609060f110f0702 73
    0x80c0604840d400000c8441e00b1078400d540056050300401b1085001221072819440f00c5408111800c80c008186d203201c1c0081800502400c0c2d0700f441151500b0130520030900c1219145d0900740c01941c458101702d400382c40703410300140c80284074600440707015071075500b80c15444c0c49603001101e411010074026504444c0586000f00000c62910444100c0d5108070700101d18910514000c900d070f035045002291100c0d00340b4540104d10042440f070031081d640c0c02d0070800501001540d10007000e004541184032007441d680113014000807040503e18140f4000d07665900d14a45426040b0b80b503158000900c0041c029030001400011125004216114001c000018104825498112508005643c07682c861060307004100c0950610100701903001c0c160303081640c01c94124482c018160300c814031400c0501c0f0408184042020001d404450305000d503c1d08030741c041d0600381031501c02003140c221700701c8446291002201d40c01c0d90341e00420702d17140d21080300c0c1c5040c18071082c4110050760003440104c2e482140002c014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 128700872 1250 128699622 128699671
    0x30303020a110d08150402040b030402040e030c0f060603120c0d0804060b0a030614060301060806010303140403120e040e060601020c041e02040b07060501090209151b1e160f0608 78
    0x44405110b04d54072503d00d81844001c00c102c055440c802580214010441800303140d01020850307400c96810380e00020729001c1c1c10f010300d00758001c0b40c0d0464441d000742400009851400940140182000c030207807070121115140031800791003030840000c0f0380e81040344400700d014024000194401c2c060b00c00070484d00d1621000500d1714445800c129500d41d51441d801d240101c10782d10b401c3d0312000c10b4000300803c508280c4e000b56a200d05120041c00c000d9544048030704040c1c004240e0b0003c40d40429040d28980c80c0c510040c104900c0284414025413074a6881801080300041c2a030140c1011380241c1070301081034040c40050400400540c50000c103280e4050000710072072005200824002c0c001c2a11410340b40b81c4902900d0040e8017014500d8010302580c000c1d5036514550100801811440e143d81d0403082c540610003401280d540a0319025040300154a090940c03442081c03100e44038152900c1c801c2c0543c940c0d0f00c0c0d0110b406602c45a4204907000d020550161550941102910b1502880d080c0300c040706 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 128702122 1250 128700872 128700883
    0x3060f0406090c05061b01050604060b0304020d0c050a0b0d1a0f12011e0b011205010302011202030612120a020d180b1b0609030a0927020a0306030537050601030303020a11 75
    0x40b221b00c4002080c0d5040e020740078860075400c040e046800340061841c10501714090b000140c4064401d08aa04400c400c204104603004000c00010b8500380406a485100d240203030030207200030080c507007425103001b0607400b02281801405002021180311070f0303103402071003045000f0300d2560200750b60300c6d00c95001d000d0000780180c84051034076501184030841d1000042103400750004032026903041400520051303801026030800c0241d59400182c60796907420025400507031001d150a284d02607640c1021440d80c0d004018a04855950211028120318041c01c584601c3c6410b1480a030b40c4138400140900401880140540e0508040f04000c10886540300c03400c0070002c0c0d840c10048d41c0001400e40116401802a400400c080045040c011b950810705600d040d140304042c110b21580064040c3d4840c0c025445100a1a0403601302c0706070b0b4120641d089042c0014408804002c003543d156000c40c08a41d60180d00c110398800080d0a00780d186036010707806504000c60307002c2481450818600c154108001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 128703372 1250 128702122 128702137
    0x5220905061002061005090406020f0c0c090c040b070b13140a0302060703060b0304021005130605040e091f02160f0503031503030f090f0315090f070503060f0406090c0506 75
    0x40341d003003503820400d20a1803140102c00395002a8104420380010a000400301d030002e5a502c85540e81e1443c0c81002032042080e0103a41c0c100115407820004400605402182c0c800daa4900403501c4100203501c00740643e218681c0c03441010040c000000d20116907464220f42030101c3e01c085449075603202801d52803426284956540005c80204c1807541c10026243c0000340b505007001681d0401801c11007602c8010006802001c0b200040c1d1171581c82001156400b2040d4000e0072910b548416006059500c18030920729002015408035610980c0460040c1c0e822030002e0f1381d0318502c861500313020040c1d04410759044030401d42505100208081890545403907200d01d019507900c0c0b0380050301040e1030302180e28081c00ba40c0184a001c4124240ea0126074005d0421103030301152110101c0024942001c600391078000c1d0001c10103100b80c2e42c0700081c4141103003100000360350f05a912a402c0c1a602d01d8226090f15801c00c0b4000820702180b01d5901c951151406903d01c1c4078030646501c042030465001c2c04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 128704622 1250 128703372 128703389
    0x717030604052a0d0e0334020f0607021f1d0f030a140304050d03170f010806060d0c1707050102100203060a030f0f02031c020706140403031103040305010f060312050702030d0522 78
    0xd0301c4225034201841f141c2c0b40c40e8081440c3c90f00062900491000c440a014040c020440040c105065680e8407540003140c032120f02100c458003180360b03001080400d585420710b01d0419507c1c81016180703014000306c050408017a004164a0031251285404281c48549a4080380010440898283c0307070701340018289402600e03200822000144c00201c58a80100960000000803005014075030b804181c440e04444120746049503120700e424441105030003a8000c28526410400d01c00034480041411003c980b0241c0075a02d4036a02c11f850507050384011903213182d1100200e00c05100280c000710011a00d03d000b61050901f80f1410b6000c03138607094100544044800d16072892015240d41000172001510030740c0382014460704070300ca035101d4034000d900005003030000c550841840751908100351401560054000e003c1060807101540081107140401d079000c040c044194030040c0d01500480b40041d9015008002c0d0008407001164290080203000715500c0c0503181c07880d04005e400c2801d10260050b01c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 128705872 1250 128704622 128704657
    0x60204030c15020d0302130503150405060708071209030c060c080907060207050105030f0622020307180605070b0406110c01060906060309030801090509030717030604052a0d0e03 78
    0x1428a2610707a4a1540700001a441403190989156400710384d502d4828020305015840c0d414110301c2220246c0c0c15040690144601310407031420080c6101d81601a6004005031141a102d103c4e04441c408011509913001c01d000046041c1486030a601400c061402032900c0c0203003584a50b80d010035540c0008148000a400c1000d211104609002c1030004047c00d00040c5007062034800003814600000745500c80c0260740c90005100364a901e002c2c186410440c0c2e072801c480044c1100042d000790002d94040b070004860324000610201040c1c030140a0701c11586a40d401c14200c3d40e1080d1519800901c122000b503140c000d44002910b884000d00102503683e00080b50b418100403002d0f0845201b580288105802e010815000c2a042496513040d41da1481d000f0420f959224030700c0c0c0c914802d211005050049044e9100140a051409140100ca08450a01a9031500841c444040200101d9216400e90604006159000410040240300300b0003001003003241240100c1ea045400200b1810b0b07104181 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 128707122 1250 128705872 128705879
    0x30602030c03160503011223061303090e040b0105100215100302010e0307050f10031b03020a030b01020a080a1808070b0901120504050303150409230f0f0c06130306020304060204 78
    0x2000c481c0c00d0440c3d41e868000e08640c54200302d024031a03030790b48000d0801444030050000b483e18108a1102208000c000c80c0e609090000000d0b481c61040728003a000680200800b003518100d4001ca01e01560300700c5400210740c1d0800e4100180250521034001c154892241041a00d001c9411240e12034041101040169451400090004002204190b2003a00240420701c913650700e5100100c107014094642d061115011071040e80180603603054080703c0c4407000349802079140d0540040480c100640e40a20040000704016a9220110719008008500900091040f14485e0580c03201d485049400400b0083c0d483c2030007410706065070802c18002a001482c1d100c196005000070401402109041090345819200c0d00c0e100c1c00302078400c00410411440c0924559282e03003040b441c15400681700105084803180302462011144a000b03518006c1c416100079236007021403c030f404c1d20314a4000d4901421280d04100c03807644100b031355940114642c80003002152080c030165104d02d02c29003005940d02d04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 128708372 1250 128707122 128707141
    0x708220c15032a03020903030f0f030a0b040e0a060218132307090302090402040207060f0b0405010603090506150a030b01030c050102061518070306080d020a06050a090201090605070309030602030c03 87
    0x50001c1c41c0e1203000c00c04111510f0740e03550410311030300203c4649001a102c02a81d03000a04512401c0c4020000306030210b200d100101e409801140120300800e02004000e00d444184016200303d0303a80d015a07500440340720008244150018120f0041c5906c504545402c8400054600c00b2030240255440f60388200c410565154603425800a48013140898201c5c075242500070804016030100038051800c00707003c42d08546498068600981d4081e2080c1b1820743c500d0300480081c020207501d00c0c8100c0c1080700002c3c210b030180c4a808440e941101c0038100507a6009042201c020500c0425900074000c03507000000f1440c1603001501a600c030302c0d800010b0501e03010009180c180007401e8952140b15540254a40e80d941540e14128000300e909240c00941d1030a8042d8010100c039406590706025400d0b60301440b86d03001c16042e242c0e0703200f2401044a80c80f030341d444c1d900b00c3ea44210020702041840006000f064015009441c8c240c0c400c2ca0174050240e203e0341c80c80d059801c01c3c0d034428240400030091096041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 128709622 1250 128708372 128708381
    0x320040801050f070c05060414071502010218090105010c0b0402030f0a03050403050d050a0c0b0703060803130f0f14060d2309060a09150902130c080118050708220c1503 74
    0xe000d885c1428072107400e501d178241c440202800042406c011076911108600301804130700024451042c01c04c01001a196010b03000c2d41c0690035042c0341c200f0072004880c944c43e02007004c505030740703040e0346801c004260355448100b00c00020b0030a0f43e02d0300c9040c5e4102c140450410a4101c2c26120f40c0c4c845883c1e0f49076103042460404441c00310418043d0500030600301c20750080b1949847d0381c1007210b052560300c80c00d400303400901040c0c1010200d404002580c1106c52440741c903c03c1181c0f5604c88040d5001d0f9105030b680c0b006c402c030380a144156040034a0504c0340d4980322000e0034489403100d000160401002250201003c418121081d800ca1100b0030814007442c144240c0341e2141c1d103440103015920307055650b91403102d000c0c9490340c0b04640d10145c01701503495040c041d01d03a0f1404100704025240502d58040c0c403d120902c142c0b00f01191034020740f11000001e0080500034589519010441d4517509001c0a01e442da2070603a05107104407045480c0070542c5513000c0c2c5c0081044007076451034225160380c0102030b41c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 128710872 1250 128709622 128709631
    0x106050904260307051c090f03030515040203060a0509091204030609020a0e06030a060e0c03010608010209030f070e06010302090d0602070b01060210020c120c150907180603080702010320040801050f 87
    0x31081031041100045e08071044408001d01d640e1a0603030600d48032a48001803103280c4001d401245119084002c254056220364001e017290182d11503500016030401041c0d100466105070494400030041289040211080c0d40040801d000c4e241240c0341007181d10000d402c0355106031921915003e562017582010800040030b807000d10b40c2c440b85440c210000c240d440007540b078010300c1759540c0d081007401c40000744200404403200a00078418107580d881c81c1400307904185440c40c0b00b800746101112088a000494500311040202c90b11811781d039220045d00250050f81030103401141501003000098131610040a941d0710495440056504011000b440d1042c071085c2c2802032441001180f01d105400904070802d070704a00801d95541c120038008505040e250001c2210010344c0c2d03418420011008100c20090f0f80c03603084001e051000100e01c03001520b05500c400b41c00c003201000404007551003030700a010303181d02607001c58140c002c0b002c668800320380c4140d02c020780b50f0355076009003d06601e00344182d070b801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 128712122 1250 128710872 128710943
    0x110a0504021218010b18101d040303050712021c050c0412150207140a031211090103050709080d0f1101110406120923210a03020c0106050904 62
    0xc2022142c008401010003905070300e10341c1c03040c1c3d036030281c085425085203503e4100600402040e01480e002d0307048640c0152281d401d010869000840c61100740c2d402c0b04c1b51095000640309003070315951415001001c02a00120401074803403110032102d801c1d4002052800d140d0000f0380c18200011601c2c50441e04064406240200d0030001000350315a071440c0703449160340040c070b5404501916010305001f03115112004000203d00704081a842c1c1c4003080700f040c0d0a000352914414043e5009940c422649050300c4010444418400200654401c0d44600e92140031400c01c1e1b00d0f40390300c54102915101001c0d1003480080c00340a160350103c2c3c1c3c820304032407184182d14024008100800841c0d02140203d000d00d5003007003103107118568004c1c11904513440940d044092545865507c592605590f014000741d182d092150800e101410b6100d80d034400b591403441c2040905002484100310065403004101c103429649a01e8049601d03075075002a1402548a0385031641d8036031041c01840648003050600000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 128713372 1250 128712122 128712127
    0x705061303200102070f05031e12152101050105130605060a0f09090e06010905070e0a0e0c04170d030e0a0c03081303050a06050708150102070e22110a050402 69
    0x2608110481c6001e0552500c2c102c031200e0318030803140217004071100980303400708010420050100210040580403d02c20030100385888a08007590b45109100ca81000782010174000703031021603018401e050103100141030f04021460683c110b0100c508054040c90181d55480040101c2d1030810704140d4903000b059400d00c40ca0749003400081c20b03801001440001d001d1a115140440c600c1041c03c0c2002e00f1100703104100d01c1141c3d603041a0340316024095412030f0303403604001c50140d0b806814901100d44006090458881c1869885400c21001400000d94908144408110385803034602c07440020102c00c000307041504c07a82c0c1c0000d00f500c0702d25801c3c1030320780c00091789003000c109920bc0039400e50307800507280ca40d9050a4010420080801c0d44090044e00410188404204098000e540602c205548400b5140c0741e06102c0400403038000310003400340c0c2c410002004075044002c03040f5404024400e00d891885502c0340e01d50919042c4280449c1d000d10481015489841e01141440151005490460 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 128714622 1250 128713372 128713411
    0x1d070f0f0521010905070f0306051305060610051306030504020906010906050d0509030f03131109070e0906030109122c0a030321060f0e06030f0c0904030e15070506 72
    0x4a45103207441c4011200e076002c510740e03a00c101d025008000300302d600408590901c0e50b1200d10314219810350101f141d810b410000402e04400003040e140004c0da81120281c071098403207404114000300c001c11000300740a41449281408000200100c0040c149920b022800c0d1600344100915028000c100e241808205041409030341e41c000c003a903c0c2c04010030030003d1203880301c01c402840c5005074604d0b0201c0981c00020042c44411034821088901d21503000201d84114030010031486e510210707180e400142841d211700581d842d100c205290045000b07030000031151903070f841d114150701c2c40101800100c0d004410201c5811403d9007403104e102005d8030042d06828805001130385400c001d00c800360030450300b50b581201454102c1000141d17600b024800b001010b50b907032003030740c0100d0b11442181200c41c100000100c0c0c50801040000b155801314020700f140c0a005410800c8032070019000754100500c41d90f0500c559100d29109c40034000c103110895031030350300703a10301181391480080c1b0301e2962105607451b58 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 128715872 1250 128714622 128714629
    0x2030c0c0f0d05030f070504030605040c0503010c0e090601120209150406110d0806010e01050c1510080a0206070321050f160309030f030e1018110303030124031d070f0f05 75
    0xc0c0c0e00a121682d01000c603031540340c1b04a40600641c2c0028040301d00e04000d100811034118035aa007218030070341c028001ca6403030328001c0d01c0c118200300440e9040001c2000158103584206494512100300c1900107050400c04404522882c510000303100080170b0000e0103100950704007006a4410606030000c05503060546030080c10008064541070510a905848211684c00b541c15078007149542000c43e0b8070511616140b05402c0c50503902000f02d601c80c000c0120325030002203414810b980d005031070300d4641001607038116008000700d902020101291080401c090406000c2c2e02e0061108408402070b40c00c105c0c030b0304038100d04000d003100e060519200d00240002c1e001451854024082c4c1800100c241c03168040358106105146515401860143d900d80101940d40380d03070240c24040c40704810300c0f2101c0d005256480c0b00a00035051007410a6900030b044420414201b411041207140219088003d1940d071040d50782100f074120710940000400f44464194910780c41c1c01401030307038203080c005460a40030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 128717122 1250 128715872 128715877
    0x9010225141c030801060f050403050c060d060b04060c06180209150102030c0114100816030f02010212030a0212070305071407020d050a0c1e0308090112060902030c0c0f0d05 76
    0x1405494004480440c1c01541c46250009a4007440031560064003400c0ca4001c0c00f40030240039110110350044c41385c41c131240c07151040d03800f40c0386d100005181c403920100410030a03811089010051356240e510101c1c020300010b0243c40205602d4945040030110341c45e14106840c000c2610000707100011609001580e60b0f6020b0303541250300800130103100c0110b080101d04504c11103134000f25541c240309010510700b0500e003000e4441e14891485040740c070345452859482e01c0910707840c50724040b0042c6050011480c410442c10415105004440840010b6082c1d0310795604202c40c00d410442e80480d84283c2c00459107101ca1b806881c61504001c0b621384000003078200d09039007442e0190030502245c9042191513299003040842e07088021540080100d00d170201994003039014102d11130000300d500b00d882085c050300355402c1d40e5100d203d4504028a84c00112002c07600111080c1ca116100e503400940040f15100460142c11903081165940c803c0340c0c10107180030b01062107034900354440201000160b910406 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 128718372 1250 128717122 128717129
    0x51510050a0e030f0a02030f240a230108010e30040305070905040203101109040f020d050403030b0f010206010e060913080d0203010306141b0c0703050a050309010225 73
    0x30065194080c41c5421511058480748003501889080703e0242100380010f0701202a910840898807020303501c0b640140c035504c0340248191204416610070500b0b40b60411840e601c5228580006219914031000500c40d100d008100c800c0d2250300001400007040a000e00c1444070b1000c0b000340883d440212038020f040c401250000c286d4100c3c91108011030010070115002503030800116031002d525007103001c005101c10755049200b0300c100c000150400503280102c1c1d000d020310110880c00c1401d15828000504008007100e020240d0070008940c2044c0c440c40703000c1c0540c2c082d54001501103503540c00c1c001d0003064003211905540c00308004000c00715140c1c0080d0303802002600c1119035070711810460800d5a0840000422400010030036038901d00b9142e0155040300c2c0508800c1c44003409591021840c00d40c103075a4081194110384070500c5035085c10300104111044513040b50ba0f0300381d490b11100d0400c81c030384008071001e030000103140c00c46681c1001042e030710410311000c401101041111800c0c134001d0701d11 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 128719622 1250 128718372 128718377
    0x3020a090b03180102070812060d08031b07050a0b180c090c0f04080a0818090408030703150b13091113060e03100e010c09060206060303160f080a02060901051510 71
    0xb0010b0742c500c41200d0044201c0640200a5440e00e02c640f4041070f40e90000341c1400c0c2064004000038140d4688081507514480c0c11485440c9561284024030607180c0d008195504003d00c10030064001400402080c0c414900585490001c0c0c200251551246c1d03100d843c1c10389040d030003170b180001c0079940e090b0300e203400445a25500b80da078450a07244520501072580504954081d41b5644400d104071200107000340c6092440300100003038000c0c1000b0303103900306660207044484180b00054181d8003943c8000c2c0c03020407581c0c044191a0380c4c0c17141010164060000c845040d02920b00801540006001d82a82d00c403000b250281089642c074072850750915184201010010701034884c4516031000d10260002d900405407e1009550a01146000c0c280e100181c0340054001c0100003010b0342301040d154015203008019500e410740c070560300604a0124502074404580c0c00c0b03100800228090000c00c075010841d009824107280c00c99880d401c4600c01019251480c0203102242e9003641c03500b41d8841c9040060 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 128720872 1250 128719622 128719627
    0x50c040501200106080706020610050414010324061d060a0302090f04060204050604060918090305031b0c0105070207060216080a06020c01021303110307050103090209010302040506061204060c0f03020a090b 90
    0x7680b0203001d80740b698081d0300c45004001003c02d1680c0d0100c0d5440c403c1041d8105040346582e43c805100072100480700c1082d007002550010310008415111005440048088002410121000c3c0c3c204549060b40300c0140d002e0f20386484441030f032500c0d54607584072604440c00c90005141d600496030300c2ca001002c00100c040ea8038006010020136906480c090f1001802e0182c460380c40d0280904450300b0380c040c0480034004804034402540e441c3c0a03081030543c0c5a5616800c64669081d045600c9003854402c40c40c0d48018004040165401d100e11361113203c9a900a25041d0314000021b807c0175010100602112340d002c005001001c0000703401003404d50700410040e5184502c20f030a0b40240140c2103c040c0714860707100004180140401c00003084071013101a5050140d880e801502203d0304420029000421b040041016203400e500c40c903800031010702124641032f0b00c1c404000401d8021136003115121f9543e02000002c0307500180b507440000c400d0404614202002c0c4024180103a6881500f5881000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 128722122 1250 128720872 128720927
    0x604021504030b0903030403140310051306080313050a05011b0b1b0703020d0206150d06090203010207080301030f0c0509040317040201120204080304081605221d0105060103050c040501 81
    0x160049a00843d0803c00c000c0b410308180001d5030f100ea005840650008040070b4440030482800800c84e07000380403040c4c13005003d030b01e01414404001d25140c1c0d04103072180c0c1c8080000321803000f840104040141d2510002902d400d00c810407181250320b03001a410491100245003030b42d4085590303400c0b4076400190015456481c15141c00c040c03e2203d00350312a02c5008500503040640000b88024030001c030381c094551681c3c901409251f41c0692110055001c01c020410b2008290300e0b40c45590a540090005031030440d89440d0308046074002c1e072003140d004130400100c800f4090701c0c0b4110030251404590390544ca041689004140b0104c603178550b15205850008039046a0140c402da00800e05030680030342d110380d9180081c0d6242d400c24424540303940190032058a081c60700b91000001e4500c000c05001d104401c0310416902c52034a502c60b10388540e540d45440101840c50a42856150343c0b1000100c1c840c0b60141c001010f450000d05160281d1500380001d009a07070308084202d003183c0741001045404e505 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 128723372 1250 128722122 128722159
    0x50a0c050a0c09020901030606080c0a05071a130c06050405090402061c111b060106051b010b0a03320d0f020a1a011509030b06010e030c0a1e17060402 66
    0x400c007500070714159280384001014000b58002e043d04c0c24090b00c00300005a6912800e42d807047d0102c80c801652401004001100c601901c00f81001e00e0260341e40200342141d6903418102140b003518503866900c41410513404201644508030080e040c0d91034002e0405160801080c520180600020302c44c42001c01e942201598100d00c3c1901d2034103c0d00f06000000590040d06201c0c1d100046aa044d11080d81450551180000e03200c1c0c12900703147d41c2c1302d281101d4441c4000c2c0801c540811020355540316011009181d4a5102500146000301104071244000f54004800c00a151035011000c0c42c2c0f070031030f081071110041000c0b1600c0355181020100c4500c03504040703042440000d0300500075031841c0d0040010403103441c17006050752500c8003a108000702602040c0d9405d01c00e03101c01000c6c00300b0100020381552007410694042a0050112065500b041000807440c040c1c540221428040d5401140f550003404007030b8030001d01100315828114000744286a0319644c000304068059001c40415078072041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 128724622 1250 128723372 128723383
    0x101a0a020309030703060203190501030f0210020f03040303211e02160611030a180b04061a04020a0f120c0207030602130305070b0301060206161d0105040b0c06010321050a0c05 77
    0x50020f044e24130403a160302d0940001c0d0415960072080f9090002d1080c6908428402c042c180e9800114a003444c41c000e600b0030286040c9440070b14110b01078032592400d00a020000713000914442d4036509048042d448022030500500a441c103241420b01e90200c00428a0382e14101422076480c601582d2034445480d541110385200d540242090324094005211801039805140640c0744c03d1010320100c880480c1b042058500d103580175000101c0703400800c000810719030020300b200d5203185140038240614800501241c1042e0441c0020079000c501040030345a000d9550700015064542c00c2001454081000b0340d190880e002c018207860380025050300c5010005a02001990f01404489a40e601e400710050140c0083c07050401511803c800700d09003800e50900c1003074810041c1d80c0c00c080ea020190754001104420802181480070820000c1041e480050045c8100a8014000c094039495480c02200003542c6891044a14080001450340c040d401402c0301c203882c001b407408d000a141c01e820404d0810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 128725872 1250 128724622 128724637
    0x150c05090d06020c10020403060e01020715180b04060c11060907090b04060302030d0f030b06030112030509120f1605101722030c1a090715120606090e101a0a0203 71
    0x1d01c14481c8017140760314030350000c00c00c0d244920402d00c01078441003145402d034002c1f10b00c01425200302145c2c0d1f64030261250300070707542114139000c0b40d03d1030000d6445080002101781e4007a1a0360b62201007114030142c004901807001c0c201e10009084078900301d401140c444800c0d01034094199200ca40140e070b65512501f001e0007840e002000e440207500b810b0005450200c01c082c0c07001c08a0b0400c4100306075441e0990a0724100d50fa07140340280c0041803a60100d410f64440e4041507842101c000156041309000c0210044144aa9008103203094030040d4804000783d0b5640240d1040e005051210880d5520800034a00c01704001c0002000740c503030340c401c2954410320b6100c1ca2014211606001e00f0b1507441006902000e000d540300200302c204980410f41003010031920740c0b015500400c0d0405c0004100c060b0150f0440e91403070001d003d4a5207400c4001928110307400100002c04294040c040000b0068123584c011850501d0198910701d40041d1907101061030405800c0c01401098241c42d450007802281c094 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 128727122 1250 128725872 128725897
    0x2040b0604091e02040305070b071b030606050102010e120405010804050a0b07050d0501060c0c0302061305030601030c0518010f120f0b07020d11010605030c09040206090a030f150c05090d0602 84
    0x81d981c640321454000e2003644081103042200000c2d110442402c1d200716400d513074000c00070b4200c290501183c0e4002c0e901040e0b04442d00c10032104e129030422100d4074001c0243d44184004243c05140c2400203007560a40611800301d600032100142e81088090210b5049500070b09000ea40e0b50707903508005060180501c0040c4c50302201100700001c20340d224004009010039030740100000c0e40c991070121440381009800401110f01d10a040c400343c502400500104900c0f40c0d0304509035500ca0010078284542a44101c4080c2030b02e0106002d03528041d4010f0079a0340c141c45408215603d000f03441c0640d100103108620340304d4440c5100c0002d000745916407542258001001080328107040f07100941c0d41500c0e110010000300844140020401d040c00703000d00700e41d80100104071b0340d04010100030000c900a0001c0340d004204001c4848143c0b43e00302503400840c041e20700c01e108440b560800d401480001a14081d00d03071300c1d12040c01081500705083d50194081540d0000e056201403605000a10400f90b90090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 128728372 1250 128727122 128727127
    0x4060f05040902010225090606050a120506060f0705061504050c0a0e030c061204020102060702010c0e090c09030708100e03030408070308130c08030a09090c0806120307060f020702120a170702040b06 87
    0x81e640706c003001318022a845001304000d030035503030482101d142c080d58920703000141c80c801c04ac64000003142c0045401c098010321a80c980089005858020740c402242184c079500b00340700b0006a0078400c032003e8078402040e1000c1c00715240520500c0b20314030500c1402014003000c200005020b4904111000a15401601d819642c07008100035001c1c19500300d404a00601c24400040c0e54644103000b00f0036110015107910205031507900400c0003008004120808094040c0007010250303908118a034000c0807028041c11128170009408002c0d5240d60a1400c0705900800c10302c03000908510071a01c6007a00341c030f0030048c1c54482c560802c40b2409032810180074001450008070324603402000800310f41c040c81c0c4490000c25075410040083d51002514a00880c8000f00020f0030b80c24000001038000d902c08058a14040b41540d07010101c0d0801512076401c03e13030205140c0c0440c1410311502400d01d00b41d100030700c0504450f81d90021119503c102c50441c20002007002001c544070740d080790804070401489030380c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 128729622 1250 128728372 128728423
    0x1e040e0a050115030902030c0f01050c030d02040807080f0304030f140d090915052809051009060501050c10020f070b040f0506010510020c101e0905090604060f050409020102 76
    0xc0940800e00034800301644070882c0c030041c1c1d40603100c0e0361000c56014002d4074154a00200304190144139002e0141840020008001c1d070700340600003418041e03007140005031a0303418a9a02490007190f034000d800c169014125000c42103000009580c04c4170360000e41d403005010b442c03800d01d07040d80d980c00044e40e01388101010308491a0700b11350350700e00f0396440850402100f01301071506440e01c88140f0515401140b403100328003600100051a9290000940740140d45130b554103150011184200e0340e69000101d540d400384011005802800001e041c00d107030060078000309400c2103413929111404c10300c407940c1c0002c1040030042d2950580303c000e500f00a00401a107010b062103050443d5030407046646d4003404001103503e02e003480034441104410750040c500e082203403041c004650f00b010700c0c040074044801c0b901104039043e4860700e980060707196502d412107032601c001d100d600800a0019489641000c1c401e000f07141884041300d0480d4000c07100441c0641e017500042c0e040400e01889040401401d2850f070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 128730872 1250 128729622 128729641
    0x4030b100b270406030807021c02031911060c030306130e120306150c0303040f061d0307020405010f0506091c020901170d050301031e030216061101140108031e040e 72
    0x62002101c1020040e4525003803810441204c0350303400001c2c136041044c00380b0001350034002081541c45015103e9014101078a0300024944070140da42c0e06c1410040f11425810000002c0191b041080b040d03c1c418185464220f000c0d490b0700000b8001402500c1b0b10000c80000c4116030409600015040c05407142030707150206441c00746e0300860321103000d0004554038442c40f00d1f444007110555030713010740034604540711070f962815031500845058406a407643c0b2920017580c09200316042c00308080d0b00540d501c40052040c0820b9501c142d0000032a80f48009042000d51280c0d07044988920003112031b5805291403009507000c2010700a4080c0d04240714100101d5200103400c04448e030a00c890040b200f02844188086400b0b20003400b0003482c1000b40054110300c80c01f02130001d8030030345c401c3c0180c1d912480100715400e908996640800000b40c107044544a1200c0284200d551a0001c05d100120a42c14100c4080c0c0c0e83c800d0111040b03c0710944658a15076001c07200603030300038002d000040411030a1400f042d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 128732122 1250 128730872 128730907
    0x1302040f020409060506090303040302011409030d110d080708150103090605010605030403021011071509210e01021c0c03120e0109030e0402030601080109052d07020c030a0804030b100b 81
    0x44400642c9031130303404242d61415609403032240704005d000f503240c0750465004460310708480350040c2c4002814844c0505a5601b405054807400065403003158211b058a5450301e055004000b000622000100b0b00070860380c0050500c0d03000401001021403484c881e40100c00034650082d01070b10103482c4c1000030400310b9100c40207601460080d82154640c44042400074211a0046d20700d082d084401c004500005030b8400c00c48a15074280070000820006586a005000900b04c050200503848244043d401036017100d00d030004010284002c2c03030300440488245070b030f44900d00901030910079254001801c05125030440320080840283c00c1c86450400003040d4080e040c403800032000b280c602048003c0301d003054800c3c4c030f200d114140d40d0141700780d28180007013000780400380c80c41c01d8401c0c1c041502c0b081c200314900076003c003035480e5040d01e02c03a2420200082c1015050650240700fa00406c0310300f008030303801906032010f40390824141403060700d41168405001045920114030080d0100e16030391880b202804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 128733372 1250 128732122 128732129
    0x50607020607050c101109030a05010f111305061305190905150108040609020a080d08010f0503060618090a0213020d0f0e10020c070b0418060501030908040e1302040f0204 75
    0x1c4484030340b91031070140c4490203000000c603030707540c0711220409141740d40b500044a08030311441c5462810916801003420321a41200c04d83d52a03440b80618203002c6c03403911440700c8c2061141001814030300384440240c404010707440b45501c28070000c145400c01800c01c03031230000100780040c0000586404841914445c10341c40c8550500c882c90440003030b0150103184180103140d80e050f520420385076070720b555520082c045144166002440840e001c100c48808120301012080a9107400380326600d0700140214000582d0411402508a042442855100e0f00d202c8c0070a15032071420f01d00d0301d80d81c40065501d02070020b40d020390b11113816403500c64010b400b030703004003450b880c2c00ca42441207560742203441d400d840c5075011960090b8802c1c40c1c04491f1842e1503024040520703862042d11082070b900c1c3c0381401c00d03801c59003100c00344449000d00ea4000200c64400d2800510003801c1c103001d105000e0301ea0b00501d001e43c2c4654803008a4240c001030b00c64134401c28444120b50300510070401d40540141c950000c0d00b0500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 128734622 1250 128733372 128733377
    0x405190c030b0d1218141e0a0b1b0102030f0f1302010806060d02090409030306300210030b10180807121b03060612021302030411040218030a050607 65
    0xe20340c2400d41c0c4240144049a07a000d8004900070007103507540d11460342c8600b80282002140402c071856071402c224018010500d8004c0100148403402c2002008100c09003030601da0500202d20759050b45404880f24100c8481e03192080d144c4070a16400c030b20142d245240b61507075520000801c41c00042d0004042d01820070320060104c5a030704d030080c10b404017454034000b902080d025400200c9510306880203007140e841201016081c00b030400c0104040d10300418044012903100c0d041070181d80b07040c0103050a14900f55401c208440c91607000f0f05514902140c01074052501c41c10740d910b001d4026040a006400c0141002c1a0a04010401407030400140e08040e01031154071000a98030300b0004555054070002030185484142d80d81e6903004e002e0382102442c1c0440300000c00040030405601c00c1c01c0050000c0440b1a003c0c6c01c1c1c078030410594156450707418140e47e10510511000c80c09014040710602c10944006075111080d45c00c4482104113014072179814410641d24a08004003c68028001d200c0c030b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 128735872 1250 128734622 128734631
    0x1050301020c0a060222031a10060c0318050303030a0603060e0703030806040203060f030f010f0b090c0702010c0c090207050705120d050a03090f0606090209150a02070501031109040519 81
    0x14010103007030344035040e0b1004081c1c0c000c1c4202d00101d000c81e4000c0c12081c49155400812180d00c0c440e09040e01680c0d441aa010007a408600000c01051015a548103c010003034a404505102014100800341000642003180b10600c1d80d003445d40058000004d840c00800b200e407a407900380601e501a04040c041110802e04060384400301d064000750640c04e80398507884101203652000103100081d0801005142d001d841c0160091240e1020700061305640c200c003001060110149400200f42e03101142424003030000c2200304240c5a41c00001d503441940c1c24138216028074040c0c200302d00c8018294108540c0d007480003c0403001c006002598208454007a0780201e00140181901d44c2c880c80c1c01643c0c200071400402041070110303c80c7c0d00c50380040b489241c510031f0506194444004540351a0848580300b82d001840b41c203585070035041c480b442801c01810394a811040c0800075110442481003605141d2901c0f282400d20340c070201900c2080030090010065880c208410000d10040d02050311111840e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 128737122 1250 128735872 128735879
    0x5010e030c03091e10051207170a0f11030c0a17010b03130302010207080d05150a05102a03030516140711010c0510060f0518010b0f2b0501 61
    0x8019180700c0401d400107582402d0b82c140901040280c0000c2c002100a41c42c101001103682d450000c94414415541381c43e03c03401515800040c420000e0000781c207012085078070078000552110324070350200f080710020440c00d212050f840c01600841d20301c051103050100401030300340444005010005140c0c2d07246c011758004506d80102c40d100c00e0084420b40b100400004450131401400601c803148603100044c80c004d100d407103c010a402c01c01208030241d03101c0c418070010107000e20040319a12000c0b50310b007602c60310302030000700001c1a01c0303205030034020810392201c1d2510800c01200d400c2c3c0340d000e00101100c54a031800500816003100c2e015040c82000f011481d14390f00c9216801c00c44d00c0030f009514641122621101c4e2000c5480e9141c90400550600501c000382062114811441030603101144485c140309030044580d0003608058002c002420b80c01c440c4180200705541144d66514000760307162040f0081308041d2082210301012060406062400c071005005001c05004a00300c1c00c00170740c2d88 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 128738372 1250 128737122 128737151
    0x906043f1d030a02060f27090a140703150f0b070302070e16080406021b0105040204051803040e270606030607170411010905041d0c0f010207031e0804120501 69
    0x4503140d40c030707400d0751001d5103c10050401500800b44501150780d0181400b0600c0c07181450040c00b0b4030314405404940340c50550318103220303c42c260006121441071043c182101d0550101c0f40703005080c20201501c1d1500c940504bc0e8900621000e8841e01e0740c0ca030070f8140c0300c10f1503202a80c0000c604174010b1082080000b00448042c60403806051180c240c90304a40318014103c61042000d00700ba507003507a080281c1250640b00d10311001c40c4d807104000100e2113103007074010401103800040c0408200c8560042d440343c00100882120140c1c0d40901031040c0540352074014049460300b0785030501c0038080b82005900d40b080300280040c45110124125807066441c00c40807241c52410758265a503d20f031180100b000113950b0303903040522200603d0802c131043e51701e80009007911603100c00c805181c81086000d203104001417141c0606500180c6000302c2c0d102078440000d6890350580f2016007681c204903048454005201001c8907400c0d0400307030941d19151100b040c0024044004407c464561912409214900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 128739622 1250 128738372 128738417
    0x5131b02010c090605030a1104080a140c010905060f0c0a0b040506060a0302010906110c03011802010206010f080a0308040f06060f0501180609120201020a05070303170f0906043f 78
    0x10f60343e4440b0040c50321100b41d03095080030b01170301c0e0196210903601d495602902c001d8001081881c005100d005014104103080b104040900c1d0025000021140200e0741c00ca8005021150150703601760340c0d01c0c150350701148507002d280b510302903078012800c0034020f0140702e001282c042c5c2d0248041e500c43d52180320810103030050b140b000030b000c2289406c0c100a05030107168180914070200050703c052914907400a1308480041c4000c40c107a45207a1854015940d0402415014048014199000d039051582c09680c551140c2c00003010812440f00040410280b4032941503065481789042c401a511031040c98480307c541c2c098030f40091000e0401110040b0301081c030100f240c507162207440c03030b1a041c903900a1404e21a03d900ba4158800e0564050004100704180c00055000b56540003012001040006034400c011384024641421b10050102c00640840c800c0e4000781e105040c501d00070800c00d810403940481000c01c00902004c0748429100559940c030402d103004044c0c1d11800b00c0024985e0021211 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 128740872 1250 128739622 128739641
    0x30f010b0a021b180c13050303090f09090703140c130227010c0c090c08090d0801090c0903150e0613032f032b09120e060405131b0201 59
    0x50380700310034400c0310f84008941c0380303000180500f400400500c000741c94404450151280107000034001048590103c0c00b8607400040c00049014510701005140080d00351000c210400c0d11800034000414030b00d500411480004641c0400d5000d003010012441d26200c001c08003440340650800e1355002c0507502c103482200e51403110740380c182d1f0017078924030032002211501112840c148100d11401d40d0100300100d0b682c200400340e21001150010150300700500300e80018110482550003034805034903481c2c02024031030554007011000074910b003e19408170364142ca564030103088600380e0441641a0394040c0c1000d100b00720083c04642e040d88400d1090076407044001805400200c6220703a82d4580141101c0950036002c650a2043c000f2100c90503550540c0c0c08035003d081c00148010f03966111000084c0c0c603000d2281e504104010841c056210300c01311034680c07a49042007104441c110780d010755a50054501505010f4003444031143c10030074820003017180740381d6a0210810241c0f154420740c07050003480c600e03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 128742122 1250 128740872 128740877
    0x3f01050a054006020403170c070605091504030f021509060901200102161103070e0115170a020d0b090606040e04080903010c080a0e0c010207050f010201090b070302030f010b0a 77
    0x640302e0140c2940602078524007012400090400b0b41c41c68100314940e07103204240a0200140c0d03803403440c0307000b103200c160116284100040a00081212410200b041c404860701c5040141d07440d44000009140e01e007a80003585a00f20001c1004000d0103260060315910520136102d406420640c0610003205005684d40d4a03030018042010750125441458881440400000e8150710907030252840341c26608400289034144606090000500001c050401000c03001540544880c90528284041d1280c05025010300343c0e180411031007050707200d00040f081b082c0b8180781e01716060900b000b0103000381d80210301c000307400f42c1082c16040c402c1c40d00c00c80b80c5004c0c1000420251400349003084c0590300840003402a1200401804004c8a40c0c5080c010301c40c001c152a90341d00403601c0c0444d0100116041e10f100a11694469101c0303509698000441c44103860701110301a4403020340f040104e01400450300c0003014080403100703004485800d83c02440c010718480b001c400e4540e0721000d4400307003402b491420000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 128743372 1250 128742122 128742151
    0x3040b04050c010918020703051606140a0b06070b0618070906020d17060925090e0702030a020703030e121002030402010e10020a06020d020c060906040203010608011401053f01050a05 80
    0x85c082e550b40189030052081c2851814200d410030702e8040601050030650300507485c1c4208444904824051a5010440340c400b080100341c00d2010802602a103070000f40400c0002020400300d030b81d03901f140b0301c0990944166036614689080020110400c502c1101e001d803040070020310200d8050013250401e41040041000d4607941c13202000348680c1e004c1c1c041902d4120072090703000385013000c0e00ba400000d141c54481d03228403480c01c0741401c85018001d000c8000c40d0014010710b6005603000c030300203088a806181144ca4680300d400043c080540404002496200d80320440c00c05c0c6006401951040e4000d8841c000c4c91015042030100f003001c071b81c0e001401a040400c49000207071140d4064030014481d848010b091004a45060345444019144c442080d40800c0c00c0200b18030302409443c0213400c129000b44028400100070b000100c03018000c3c184118100c04411760422100b0032004508880c140c100c18000d42c01c03003058545100c4003c00348140d5420040011030001c4180260360049029030020203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 128744622 1250 128743372 128743409
    0x106060c05120a030b1201020a0206010b04050f040b190f05030c030706140309070302090702160b0a0c0201030911180103030801080c090c1c060b0c152203020f0303040b04050c0109 79
    0x16070b00d9101109a106042c1c3c0c4542c0c0a00e15101e441032800460144400143c3c0c669000c50702a01d8044140d00011059404010901c080d4076004c100401d03046040c0c90215030303200b034030001030512440c4036030130032101c01c0803400041c182d02a0082d040c12682c0c10750540d032980c607005040c1511012140243c10124009480610304c0f01c03000002968410084029500c00c0c079203070343c0046c500074401e03640100141d01c0360000d02c400c501109041070050400c20300a81c0b40101188001d043d450340f04401905060342d440d01e5009103c3c42c04ea080424050081980080701c0302c003c40002545000c0c04140c0000e50080004550b83e01c0004c6d1140003110014510413580ea188124411258824601c010b00c500c03407115030382094480da000da04083d081801000d03440304060512103250240d540703036503080180c0c1b501c00e02c80d9071000036043e480040a040d850310500c101c5418180e1030f00300c0e001c42c032182c0c0744400010030040c0202030103005d00451168081d00e203c00025801156581e0b15030044503100061b4441c0d05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 128745872 1250 128744622 128744653
    0xa05040e0702120a050912010606090519030f1a07050406090b07210f020d0903080d02090607080d33050405090f030304060212011a0702102007080106060c05 69
    0x3281d0145240c81151609440d4000203003040c1c10004a80001c9000403039101103074540790403140208220701008100c400d2900000803c501103500c645400390710749021119170b02110b07120034030186421040c0707000382c01d00030724000312920200e4498113111a03801e00400d26582c45101244e08a41c2d03950303601d420150130441d600301503903c05c11084446a92480d9440018480d40103088500c80b6135845000705011420000fa0521106031040010484001d2061000030091416100308420b00180140c4a050b52004a00d50388905500a0003c10020843c0111000d05400c0201001d018a0a90034400c0200c010000210908024940900f062030002c0c00142010391086901c404c408003190305244041c06002e003035a000341c806645498000808002d00074048220364018041101c81403c40804080244910f01071801c00911406a10090710300c0f103441a010307440c03035a188030401070040c404401a140c0e2064544204c40082d400e20a001643c0b9010341402c000468005025002c048501d1100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 128747122 1250 128745872 128745899
    0xf0209030715020d0503010b2b050a060f09020f041211130618060510030509160e10060809060a020f13120512031608061908100b03210a0c0b090c0a0801020a0504 71
    0x7400d107100c1c450b000b10405900c40b0701880e4081e41d10700c2c5000633560f050001011b8130803040d4001200180c010000354405112100c100d130f0803074482d01c2d03011044c050700c1d00c0e00a0403003041e041030350f80c4144400b995103d00d5040350302100c00c840c0450380104415000001030f900785d8116100d01350b488502c1c0401c202d041c9000f82c0195030310541d0a41a030b5100700d1821309800d00195180c0180141440354001c1091882c0c24003403403805001c940c10211102d2409401003a07441d403004150301034050300880c4010f900d4080c10309845031108002002d600d03158a860117024008500d52040c0c55a20032298500e600c11070300402c480c000c1c071115100000304004100103966032040035000340d800c0300054030100b94135412441400c020340502e5016061041d00d8041d424161200c00c40441e00c2908009000d04120350446809040b1444400e0469120090b00000350f50881c1807490181c00e1000c0c1c241003045074240800c205c410303070b40211a080d40e42c2e038648d89401d0803800307126003150100301d0800080c00700e1010030b241d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 128748372 1250 128747122 128747167
    0x10905151804020307050c011a03060112030c050706111006060206010909080f07030509120610260601060203090112060302060702090c04030f0809010806030c130f0209030715020d0503010b 83
    0x480340790307080700e0007040499104442581c005480414481c80c12403082c0a0842d4110542d14900d0000040800094a0b0b101c180b0840d00f00c011400030081c1094003403900e03118007503000030641e00c910b592400f016100071507000d140003441c000d801503070041042a200302c0003950017590040c02c2c0d5a0074015035a0041480301d00c1514201d0050011036051201c2d4001090307064440d944003500c40c0304800038002c2000050321101c68940010040044050003129000129440e07045610b08400305200d1031124410380031140c0e5800e000340340006ca00b241c0c0000043c039510360282d903600b152080c81c9019200301c0d03220b400020350006080107a40050b28103560403d800015501d00c40b443c2950307030799030b030340f6415003800e003c4a0495000c55484410b42c0c01640c090360140d02a00902140c0380b03500005100312500e491075101c00c643c1e0b801407444004040e8181e0303d600c2005000c03140c8494480b00e0300405110490b01c40303030061054407410111113120f142501d04880010101c00d062a951454030b201c0340c03c80070ba = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 128749622 1250 128748372 128748397
    0x2720060f0705010b120303010303050904050402010e030a0311060916031403190c020f0105090f01080406060b0c010501090c03110711060d0908090307090e03040509040212070602031801090515 84
    0x204406960220340020310115105500000e103282040c0103001880000300384400c400d810610040001c01d400034203c3d04111021903001445544520042c0c0b86681c4149c22650184078642285040540144158a00141c030001300ca40c2d0f6580c90614650360110f14038800c150704003c8a00300700041040c90340980e02e43c03101050301c1c2012510510100c0040115001000180c8024121030941c186200d0002c003c540030300c0c00d04d2500e407918001c107480c0d81c401c8941038100000440050140314140d84204058891000380c01d90701c1c8441422207002e00b80030300860800501d0101062100d60103407142000640440040f1400c1075482c1e100c60b14144030203100580c00c40300030130200404040343d108403158a4480e850007a160301c0f00000341441d11001ea00040d4495181030500c1d510010000b083d2003c9500443e140c484a03942d52003c03440b185001a1095803c0c0306d142e00c003103601c503004006010400014428000ca40c02200011612802180f08079a08180d080c0d9040b80c2d2840701a0080800701041c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 128750872 1250 128749622 128749627
    0x41a0c0102070b190606020102040303210f020a020d030e0c090601050f2206080703060b030c0a050702100305010302010f0806010815010c020d08040504140108070e0702120a03272006 80
    0xf6150b299a04408031054100001951000d041c651181d200b4800074119a1008505060031540c1c060000e0103401961042c2e001110491254001c42c0d4118a90301000c6000c155180d082e080d001a540e018003905180110381411088180254001503142d0104402130101c06240c0b10500192119030288102c641c000d482004180c20311403c01c030203188600010441018214601900100714240c040d249504050a00c04100403101ca4481036942281c00b29041564407191031100359001d12030448000e4201007051400d81409400d80d10071070489000381c03903481c15041034490446000e4000c54845010a91000c0440c804211301d00c1002107051043c180506a4501e07900058100070080f401151a101d00013800d001030b040500a402c440160030050380c101e9410011115204c44a5004203020800351000080d00180b0030041428004251000555038043c0202c00802800e43c0e418100c100400651013850400101c03621204000d401800c0c0000003d038890a01c59421b146001e5158481000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 128752122 1250 128750872 128750887
    0x60f150d0507031113020c0c0114130f05100c1e06060b0309060925050409021912030f0512060d052109040c0306050d06050a0f0e0604110303041a0c0102 67
    0x104900e0001d54003400c0310913104d445140412148001e028500e08001d4018413030281c0c103000016610342e01c102c007401e280f0010002a00002c15501407038130f010100d000060300024042e920303540e9490a07204141c4000748844403241c41501d1540384114000c0c010354024030843c000c00d40810baaa2421807190300c003c1840c60f510b01005080d60003d44800c1032603001700c01442140324017000391641e0f144045151035000d502c1a110b4400d10b00f031603c1680d024540340c01e00b80c001c5584080e034014800413010b00054009131203103440b1243c455140801c0b07000c1000c14681d85e1016005400381d540c6540d050b9565510741c0e40d20424003003100b004040488036403042c1c983c21a405a42400d026200850050f5016122110101040107540d5801c2503a130034107182410600c80c07516a00d4030110043e40040c0d000c10503845141d0784400529484402c40c1a81c5c0c6840c1401004040100d074150040c0d024038140036030001d000c1c04250702d0344103e209401110109440418101c0c141134040d20340300e41ca013400141003c42 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 128753372 1250 128752122 128752133
    0xd0609020f0406150806030705010210020304050309040c090603060e240d0203010c030c0215090d1404030c240908100906021c0501060807031a01080a0e0706030203060f03060f150d 79
    0x46600450a099138000c0c0c403555031540076441c60350010b07048008003d600d2a110001c1e44401c0d51000b1008820303000000501440000c104580020001400c100152500800d006040041601403000083d081030800140369490f2607510b409040c241c400d100d04401d91002c54500e01d407628149039040080003180c0d07000740c0d4080c0b0401018242075100801c91a0030700714000d06144501200380c0f40801d482c1c040c8a5070101c00614481149094100325003401c020844400460080e81c1c4007c0080b40482c50118031000030102e4000320100001400e240014101c0080c0d0b6050428003038a841d81d4891003124440e03802e29004840f038180210001403614000c004446024002d0510080005895100400243c4d81c091a03665004842d40341c1040754080c08400b046421102d448200e04020020300454090340e10355110480c240180412030b40b445949901c0500a90000c89440d44555500a0500c420f407e010481610030300c4044c05100e095610f80300c8100c0d020180303e8186402c140031807541d500007107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 128754622 1250 128753372 128753381
    0x10906050103060f060909050303161110060306050c180907050706020c03031005010212120402010e06030411010201050705040b04030b0403030905030a02060115030c020a0b07031104121205090d0609020f04 90
    0x5009001c0810180403110403d001d9924503480b0300813051501d00c08002194011042c3c13034002d000c0d1440a4485804bc0e801141c61100100700c11216000b5181c074080f4048140d44403c0850740b2801042c421039070b07496855076013400350001401e000040da030f105806610384001c10030323404034441c1801c0b030407e00a621104100e0704100041485c9a200105001c4c1d60720150400c2c500506017440105900100754805107544d0043c40d002108d010000f00c042011603000c0c070710003000b0110242c105901d9141c0307410491000c002100d80302d4050b52800e004988003510403c115030542d0701008090340f030b1500d16550b04a045400400503020160713544040d4000490034001000c0c080d14950003030401b035040c4011004000d411040e4581451718000d11400d1550300885c2108069130000d080c07010030713034891000358080c0800052130308450038001340c0891a20742044035000c4181c05030034044004400c1301e100341c0d001d104803000e0551000140c41180c00090543d04000798552010f000d0544141c172801c0800c0a0340c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 128755872 1250 128754622 128754629
    0x60206061c020d1506081b1c08181503040305071a10030305031504060815010605040e0726011203090b0f030c0307030f06060f0e040903050a050f090a1d010602030c100b01020109060501 81
    0x7258140320032545141424023109030803041c0c107074103034041b046d0354400360544600e07450080c5181d01018590300c04d640302130008181e21030141d0001c0d03403840e1501d00100782c0e0f07004c12001c8540c0c10402550096000d2a0501944282071501e800d501041c2140c6007030780c1c180c1000703181e02d80b4841d00400009441d2128000c01c0d0081415034001d1003003c04541c4502240f10050700315604025050004010f640d030450079940d080041400c12031007500c110f41062008121b882d0a14440348500c0000042c20301403c0c030021080d40c0690b0340c1c5000261240140940c46c8180d2004070707148a420f10104e0703028803201c030045400440e6814002280601c1110381d81c1038800c0d6a204401042c8181851252203400801c00e803440c0c002101c1c01c02c50b200070f03030f40c001e0075a0040c5800c00042000204100d18800a030600b240d0424100821450800340d48407004d100b1084803000302c0d40c0341d2514200000741d0f030f4000000e41d441100d0f07070780284c41e001058628000003040c0c14454a4110341d00c0700d0a01020443c5072103028081c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 128757122 1250 128755872 128755903
    0x40e03070318080d0c02090915150a1e05040c0c06050702101a0928060902220f030b0709090c09030623040b0408070c060206061c020d150608 62
    0x70756082081c59085000c060340300403100d41242c01c0c0b40c0341c200c0e80000101d80d107603030444d41054a0388078023010f14680310545e900011884c00300028030a22808908211030031000499003000411307181d14400582c202d18414101100c0e00d000c1c1c0900c014a0990020070356001d40385400c01c0280020b417141004d640b4181d8041015030020715030800e140c1c0d054005d1000c180708445004d4900f05c2068082101440c0080035004103500e40c642699480811741244e48074004c151030240103480d210400c480095102043c020705440c000310071048102000d11407072048a1200d400d05207410b1443d00c4084c60007100800308020400e0280011600c0703806072081c04d820701015a11a2110780c1036180c0b2408503a1411f649100321440c04c0440c10814a40c1c00e0500ea01541c0400d000c0880c0c0c50f246400d00d658094070703000800b9819000004242030b41d0000300c0d588199411140780c5017042811542160419842901035040010001c080000c03581010300608801341c40034002030095035072030303415003891240001d1015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 128758372 1250 128757122 128757137
    0x6120109050d1706010c05100b01031d1501140d1214040608070e0603010b1b0c0d080d050c0301050a0e090f07062706021f0605060a09150206040b0a0b040e030703 71
    0x12104000030003603100b0f400f8280190051034580f00c3c140e1b20b0303283c081202c8c4a00e0319070480c0f0707005920035008003001c124082c09544200d4009070203d501d07000c0b0350b01465012400f04000081016580940141588014154018004494a402070802c1703480e00310f0818040403407140fa8854080c8002040200710556070319040b0700380084020103c40c84c00c03035158424441400180140c030010001c075020f2500700107200382e80a03c603000450401081d5203074954407103d0790791900144014000101050b4002c044204255034804d5400b01142c0428010359403c01c002c0f60781401081301f0ba9248a8000510100b2140100c2c0800c03000d615080154000d4000600141502404005841c0c03040100ca5841100f07041032904090009540750001c3c40e200e81400610b400340d21000000350b001002421020f804155100485940501030000a01c190620f00e0319002800341e44910200788540241c0c4d10480240c1ca5449045058010f000c007030100a44c00f07940d402d80d41100d880204010144544643c5a500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 128759622 1250 128758372 128758397
    0xc0f0e041203090209011403070803040801050f070f0504090207060b040608010b0301140f070f09090509070510020d080103021306080615040605120c0405071e0207030c06020705060306120109050d 86
    0x8501c0980500550901d03043ca0401c80059460b036080505545807240516007866400c80040d181440c00e80c890f005a000005005c03a075030806400079441900083d00149298680020854001c801408802d000a40600c03050001140301d80080031038501401010403150255000581118403a80c80607000da9035405450420303007002e000c0c05160507140b50f0214814500b0740c2403008103800c02032a6500308090002040d960070301901c05070b405404100000c000600c0d18184065031a070007800340d64841d644075264041401c2c40060072031004d06040d683c1d50441d0740307941c0c01d21041c506a0b4840c4140a9100c1030f020410010400c54288201c001c4281407040080c1c4100340812960303da0441c60107070180003044000510009103032900004140d500184507515207804980e01030f516060207102030403a03805000c05c0d80d4005280300949026110702c4d40201c2d520b450aa0f80c5000341d2142176089a000d00002c5c0007450007900840751a00c02900109481020395034480c240003003a0540720105042d00800c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 128760872 1250 128759622 128759633
    0x50313120e1005090307140d0503030403110c04021c0519090305120f04170c030d05010e070311040515090d020d0b04140706140c0c15250206070f0c0f0e04 68
    0x402d00c038559003001450151240c000c2600c4490718011010605030700d08045070661200c0c0703a0144056001026203841e400c00d40780042c05511485400c0c0c9880c46020f445030400c3c074181c803c6409094040018be045042e82d085240e01800004000e1204910004001112401c0900034140403500c203594480d40c0d80581b5081c0303181c914026194130304406806040000040310120708001c01144146026200e440001d1032500e103108504059112a040c0400091094001d01c4614043c901c02d8034107001a00c1503400c6614580150f108003070b80540f94080d0b0724800c0745880020f10340c644010300003a016010640107d00000740509003266090600340170030092221250505aa84d00b03014050b00e410740c50700100512468901c000c0030903c42001828100103901000f2481e00410040d08100301c04031100185006a0001e80781c10101050041d40320400141401540d114194010142c5007000c460392180c2e04903040643c012648003c2e54100864101c0004407100010000f4a80803244c5180a1900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 128762122 1250 128760872 128760889
    0x1801120b03060c251103010509010c0e01210e06220203071404020c0106081e0a0206041e12050115060503040f0602030903040e0c07020102010e120703050313120e 71
    0x4820610382010310300c241d5004110541c004605101c1c1985459211001c1d41600d44000341074201c0008140003142000240361072410b00600440080065a82d90602942a14600710160b030000304229042d225a601405a00b42c0358941da031400d842c01c41c0b1b200c1c0300c60b08407405030062103040e9121008002d001e0f62050350750030307846403130400380c03090000707541c2c046603440c01280901c0502002003204a0496203d41e816a212501c2c218001d001090751094150340b03600c3c1c824040c03c1308080c002c182d000342c0680082c02c7e24113154043c2030350b4a0989403e25062245d490041e00b12000f490b860301c0018120301c1142d0122906010f4000090440c10060441602860b29400541400021300c10000400c4421141c5a1400d42060f400341e6250340380c10300681540300f650000c0c2c100a50710810b07c101d11058001901910707101784c00820062100c3d05682d584c94681e0300d0b40c9490f0850800c6080c0c00240300700007031504510980c041c4c511851503a0782c0c401d0a03150a404041c00140c0020b0081000d2800701034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 128763372 1250 128762122 128762147
    0xa08060103050c03071a03061c200f01080a0c0c050607050903060a1b030e120d0905010f020304020607031d0603010803120a020a051213020d050a06140c07060903090504021801 77
    0x170303c040e40c60a40301072214148031403880f01d00480032000480c161a810201258000c4160000d60491014581891310034100c081c51800e042602c1865055030400305951403490740140c640a104e0f1b078980301c0b282c2c080c2131000311703410400038100d03100c40000e102040200c0c0909a0740e11040c3d11441d036001491f182c00c400800c01d0103c20300300680c45054880a2900e004030a84c1403801207501030024600d18684010301020700c420702800180580c90b014070f80d10030303914144034a0080c4040e0b00d804a054080e40025a0f0207540400200318103400240100d51220417211f18035070030141c4502c0c441c00588140c01c00d07402403942d17030030000d82c40400c14251840546d100400c800114245850080c005259000300218690f010300720f04042405036410710001c44003540c1c0141001e581d0b507440d280c03098864040c1c640c200e420b80d08042d000c0d00174000c00c4060b284144a040022030030000346440c0d16000d007000c003405505000c800d03100400d180c3c803103000174a0800c041c945007105401c0403000040c8400d14808 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 128764622 1250 128763372 128763379
    0xb0a0314071502070e010b030703060f0609140315370b010e03010501210311030408010c1407020f060723010507090b030408340b0a060b130303080c090a08060103050c 73
    0x210244143c1624506950647c0c07030b5400501c0d10ba81d0b03811002d400400316500300c0059241400800100d0320350103081c0c42c054525012a481486100f07105046c0e1b80c0711000202c8a4446e0074000041500480f60590490308a420310840ca54807102d11300d03524114064107506005035240c0c01140310650700200004901030b01034008110540c074120300c10030408807420b401d1900e280c00c0d00511341412300c1144259600c00f841c205407036455070b0300d0703140380c1c002c1004040540104080301c0c070b0804189505000d44403595005800c0044c001c00c1d51040103410381c0036900840c0c0c1000061644048541d58941d00d001400c080b03070000542d8203140c00054101c0d0b00c10307440550485020403c0000151114082d0382c440e06610904816400d2000780103003070b045c881c0710007142c040f403001240d00c01d0101d100a0300d801034170014810003c060302d5201d82074440c402c1880c0513162081c14801080003030b100303603460b540c0f0900d508202414620008002030f500d00565000f040701d90320140060052100034043d1094022003103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 128765872 1250 128764622 128764633
    0x60907020a02060a0c1406060a06020f0d030216050102031005040b03010606050f0d06120605010f0b0702100e040209120a11010215070804111503070909060b0d0b0a0314071502 77
    0x4080250344052020000340500700100d801c610050080390514900340d405441035122842c4840300594440044450b00c0c03056a00030ba000078100d0010501d000c2d0341d0b854078050043d0028112054010394410249010745004520518011600038409140205030000002c441107250504101c00d40724120341c10f07072007645050020044140c01030101d074050640b0441c0c05482d09580020f84000303065a07448113003444c0c1894204c50422500d940418140c440250300300c1c020741c1e102c3c4151200d41c061002c00079004551b40b40344605ea2030180500f44207103807005001503d01620340010842d0180400e2040802da4090140d0b00100714842da0311009902080c8000c120350308243c40081a103040c045c2241c4240249440801c0620480b04450000b44402500001c1688486101081e95a000b2035018000881482010034142070b2801000200c5406200c881c0c14039220640341402000300e8107039154031120480002000400701c1400d52210341c03d22000e07050036403500f0000030080d10051608011074001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 128767122 1250 128765872 128765881
    0x2a1b010612030809030405030a0b07020f1204030204051f06050405010207050f010c0210120203040b0105011b0206031f030c0305070f060801051008181506010f0801080316020a09091101080609 84
    0x74440704010752901841c0030010750700d1340c002e202d00390704c526081213405004400c184028132010f80412030050205a01700d07100381142d01d20450303d500d0020020720450307504000405c003500c0c003508410341002d04000d140c00307605245084900d101c1020b070300000201d20301041c100519038041c804800180f1090b240c0c00c518000000000702244604400240b080807a59003111440d1310900b64544e04842031801150b0301d040605080400c050248a91030000382c10f01070718000420100c440340704242e409080181035460b03a482c160b00f0080c034200304c01002000d940002000c91000301c0b02c0e40046000c1c030054003146051102845028a05401000911100300010130040e104d12260740d41c0c419507807811910585498400650f11850101003581c1c602c0f50080410100d00717051030700c0b4001d103001d0b01ca44c0520030604000ba81c11000905c40e10b81c3c660028040403103a444101c0326482098401003c00216039110f907040000c40341031190554019200f004290003650704142e106402c02d000702c91030900b0703142 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 128768372 1250 128767122 128767139
    0x509040c0806031e0a061e1107020f0402122205070e0a0e060c04050402090414041506060c080405091005060301030302010b01030501060e091303140f030619030b010e2a1b0106 77
    0x3802c07000103015560b19041d00700025000005054403180301c1c48140714101d1800c46a02c416000000c0a034425100bd00e64110035103014402c541511000290086203940e400b002c80b600c03049840c8000a45070341d4444031000091092003142c002c3c00c0e40d102e000000707062451010044480c04c0012038907650110007400741002d08071081c4c6048801c101c8001d65038034071101c0454090901409074400707204501007400108491003104003484003071440e04104c0b40c1d688100031161411050741c007410070700040100f80300e90700380b17480c92a13403280300c04940708000d41d520030101d08a03610982c82600141d65400359210a51ba040c0591401400245440c3c0d00342d06c20030001440408010380010b44102144209104150140042c409030310702e9244910b0300c42602c0c0303500d620305030300c101c0307480e07100c1c14181ca2185014824030045a040d03c1c1c11106454407a82407882d000c41401021307114400d035100c150844180d40502082e000c0080e581c04510a0300e468140c540100c000400d03510502d00d69040101c240302d80c03117 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 128769622 1250 128768372 128768383
    0x90b091504080f0310050a03050c09060a12060b040b0d05031308120a0503070201110a020a05070e090a02090415050a06030308070306080c042a0903140604150b010509040c0806031e 79
    0x1031420000c80da6505d80b441201c460720300540c0025007116006000009100e0041004090890305907503d501d980e440404001071110280a0113240306015068040811341d1984020110b44000d000080d6204910000440109500c942180d05c0c0d40000b41001014071584e10301801004070000510fa02d5000e91004c0f00d2034002d41d20f0103020440301000050f0b07070510075000721048440d9003c0c410340d0740d620250002c1d00e031982d505080e1403600c510b80f400241102c503204441c0c8941000030180413102e80355070810144071405402941e0006521141d2a10103281d48100d9008280048000034124a18503010307080c503000502100c103140c42c003a0f007046004400300e505601d014080754001208030380740742c81c842070441072410445101154070685440580144080d0b0959004800030104a4022007490360341c0d040446000f02106054144065003d120390001c1800203414140541000e071301c500840e0031900700c1e0080c000002d96482c24052503003014403142445a201404102000d8120640c0c00d6491 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 128770872 1250 128769622 128769637
    0x825030503040303270c090b150403030e01021005010e0f06030607270f0905010503010b0604030c06030f0e0f06040201080a0c0e09060303070b010807150804050c010c0204020d090b09150408 83
    0x15849420204c03040140201c01899032641550300045c014050415031440300c41401780c503204905c1c010b00e404081c501039402101541d40000342d24a002d06541e812610f14080801c0765040d4403e4004200d0140381e24041c40d130180c0020769a440461410305200421070102400b0716000c1e8001c01c0a0207480c6a0009900100301d1050f410b044000100940c040f00300340b125405003400362140c4070b001c03403a40100d03006581291300840007440100d506108000d500e02c2030348001490795161181c1040118003c0d085442400ca61440009000760051070042c10a84200004505504920108000c44d81c1281c1600d40111210700108080c1c1e003d2000074040b072140e107482d0340c800c200d00400200295002c004039605290311400c2c401071545d55070042a038580c10f5010340148810b4032070b01e401040d4802c862552003560420020204805640c005552240c0104c00c00da8205400f040301c01c0c40a42203004600c000752081011074818541420400c0c20151841e8800180308201014000403e01d020b058a454 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 128772122 1250 128770872 128770877
    0x5060a06051215060d0603050609070b0d0b0301151202151c050c07050304030f050708010903140c07083a0905060a05040503060103030f03051e070302160209010308250305030403 78
    0x19500c582d48030820440d40f0308021540100000b658810b50007554016000f1a84030350304070380e5540c89941078103031a03454031b014507650581c0a01a444c10040070350008006854090000074440c4000001e8101c50100c3d40c005041452112954204504140101c0d164540242e0b08450900f0b03c07210302c0194807540485546012a12a404180400d10840442d900d0313590040c03c0300c1d40d9940e241b0b4000b004042c04182030711940a40c540004441006000b001d40440d459915140030050050301465185c000030403069040c071030703410089152103041000a14400682c03104c3d5803050200c6480780c0e4105407c0300c00d01c2021410301e400014094008810800b80d41045400c540c4a4100001c21100b0340225480303117034103104560001083c5074100100320007440710799405010075a03507200c1e8003849952403112030180d102800001529180b003903014000385403200c898400c0e105c010b80c000039002e487c00e800980d445100003440405621402d0202c801c45aa621444621514940c0380601f16010040001d402d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 128773372 1250 128772122 128772157
    0x402010f080a090c0f030b340314010312020d020d080402120a050a140f01060509010302240708070201030c0302121f0f0e150306010b0f0904090f05010c20120a0201060803030a0f05060a0605 83
    0x1a00c60003504452400343d0340303110b41aa95a542d041030480d0dc2420b1004074054018a006020340b1440450036030340b800350039111a074241d100c035030910001d102c0a02c81490b5074002d0488420000c0c5060044585190150780f080303e14010101d001810704020622507440ba82c0350050030031451311103805041c1101c1e0100c3e51002c010140301201041d1581821002c0d519a40018600003080740a0024140441c000e0340c041000700c1c008403081e0b04070b01c52400c541548240440028003014000181e0160015130b00031034010316590340b0003210400e04c45400220b50b200707100003044400ea41c1e029623100511402c500410031540b40010410700b0f4071444006c000f19140028a40c1c990b52610307002402c0081c0d000d80c4e0688207001c1c909010b8000d0140c40300d04800259810300044807404d980785122100200500500110115807801071117503030000101c0740540d5214800010400028000745100780b909450200322010b04a6000086800c01040e01d8401d6070581c40c10f200e5194007800740d40071408a1132600c82d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 128774622 1250 128773372 128773471
    0xb070f0b0901150303030606140304022d0d050c03060a02071502030402060714010506130c02100e0106030b04080d1b05040302010f090b0412050c090402010f080a090c0f030b 76
    0x14054101c0e0400e50f55900c0301080c0000400d80d0650101049500e61b0345d900c06145060740550794140b1060b900603521502c020000c09c02440ca440b2052040320300d00140030070001c0342c940810156049100180d0701c680100340b400141d4102800311079840b0142c41000c500e814680e50740c00c5400b40307412090881d51640400000c00319140e0008450003240c006051440303034000030028034041e140407100c030703130003404a1032129038020755500030215007601b59000740007610400d0344004002c01d012048205959201c540c00008205803540c20ba009502540c0c040f5612a501384c00b0b00d007a110000f4070554903002c40c101a5000070381c04816a030599509117070074208c542900d80115620038040c2c20000c035503c00041c0009116a40a4184070454458006d072522000c0d8442007010001c0c0446000c1e01040c104260403c1c201d00c20031405500c13624103140090301e40d101d61200300354080b0b00c2e002902c0310604400188140b001003a041584001c68002210702516041ca61500912542681262403201d000401c0e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 128775872 1250 128774622 128774641
    0xb030f1303020c040623030c09130204090f0803061026130b0108030a0e0a0b25150b0405010905040f03030c050f16030e060f2b1b0305010b070f0b 64
    0x603d10140104140807454032101e0800110502611504e91116000b800172064100400c0c4070340b0000006000c50419071b40c41c1d0110861041c1c288080364042e50392055403000079207002d901d0640301d010303e2140d81c403480c00d00d050021016140e5180300034021581583c101c408403448000310120004000039955031115601420071400b4810000c014a41c11800030413a10f600001034012401d6039a1080d680340110b809000d40c1c0390160040c0543c001d001c1000040b207064107811000000343c034011600c1290119103504452800d20043d54a0058603811849001c0c54180a51809000b40b01c1003000715040c50b5440c0701300c501704640020700741a12140c4540040340280305075011018501c9079103588258030b450050100501400803800700d1498510013800b400c190095900b180c04c818000c510f03181c0b042411955007402e00180c500340c09820324610700340503c01e00901e40c8000d8020410b1490105101c3c010701503440c16081542031040a00100340441c0d5101042d00c411074101c501000e003511012100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 128776978 1106 128775872 128775883
    0x103020c06010506030403140f030a050109020c06160908010c0507020406060302040501080406090206070204020d020d0c020f0d032703050301080705010f0f050a0207031b050108010b030f130302 85
    0x1030283d0f0403c5401903820502078140903079202844541d4000c1d90340303c03448007440e2050120a1002c1003800380103880c058402d0f03d8007503081c03880700b400042c0d595100a1034042c03900c00404400c41d0440c00b03500c1201c05403512400a0259030502400900b195022202c02c078011882c1c8031000403444c0c0b191083c1e80a40300143d5510b034164850f91111009010a428160390040d400c110480069132548014945a400d081000d40c44100440001c0106c13007d020300c0c0307002d40d006078034803010040000c501194883c1060800042158084108007503044841500c06060191200014103158002c80a10304940079041120000c6454900440c0c2e44c8031310001c0440860086c500314607240340504058030032940584111000e4075540d03140c18a100c078026040c00344010398040c0c10300141d640242c02c6800f40000806852a605046d18114032003c0002c00030114901c0860600040502c00c1c4031 = true := by decide +kernel

theorem cover : BRFrame.Cov 128597122 128776978 := by
  have h0 := BRFrame.cov_init 128597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 128597122 ≤ n) (h2 : n < 128776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
