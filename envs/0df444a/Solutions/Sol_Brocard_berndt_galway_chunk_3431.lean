-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3431
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:38:17.681315+00:00
-- url     : https://prove2.me/submissions/bf8477c2-8c78-43e8-a730-339ea4e0d876

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 616906474 ≤ n < 617086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 616907724 1250 616906474 616906487
    0xe010b01120926041d040515070203070b1005030a111c12081906031a09030901050421080307021501062303100801060b09190b0f0f07020406031a07 65
    0x1002045038141c00e0f00340500f0081c025011590450022480f82050345031038503688032a0000c8101c0f41401e084030b0901c0305001c428040000001e0701c510110400389440307000a5600e208240c4003c2c07050880c00000351b50303aa01e00101c4406090014107544d000e04090406004800144034210301c22034403203c41c0100d1840720904080503d5100c1d2900c00c41600340c14007954010b40040c0030720360140c0d00301c2103121031130524480c080c055489908140e425080b10010300701c1c0200010001425076000304030410702a07800c1010b507812512201041205002c40380036642000d9004071008180d458003105001e074241d0041003903581d03c004120003100700d0381d03247c00c00c48103a6088010070320315040700da00e00341c0c8600d0b0040c004c1d40c0c0620354440004411356580405801c45885510041da1a0008564601d00d07140c810880900054a140c0b01d84102e07041c0015028148254070004d02c1d07400c4001050107505141c0c2c42a2074443d03800903c1004016920309180c920f10003155031103c46050312b00f0010380310500500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 616908974 1250 616907724 616907741
    0x120b09040203060609102c0f0603070b0c0703290a050606030c0a0314040c060207050114220f030f12020102180f03070503061005032b0804080903010e010b0112 70
    0x180103101d076494140502081a50141c40c0f2250141c002c1c0c5c0c0820010500700058802c501c0d660104655100c25038401c0d001d00303c2c058000d01e803c69214040c429142c1e03000800c9001c0c0c415503010180e0b3790b00c0341c0b04034030315041c4550b00042010141d06410f48814550b06141c16512142c104020565a6614901c408444003200c001382e00c05410700114020020910151444a243d4100000c4213032000c0c01c0202250000c0b03074101c80d0200b00003401e218540d41031214034018202807c11017001041c48a0329041c0d4010880100e12144894070041c5d04030080e6407a030030007440032a804600c1e076901d070308203214000c1c02c00d0070554607820a4802210b26503c14801c80b44004030007101320b1044000c8508000c243d40643c00180e91510980402280301c0d034060041e0781c01610802035070070403e0b1911b41410f041a804515181c4054044682240021020b8082c24030082d09031030814429604d518150299000714050745030158641407510700542d03015485031907081405d8885490070f03002c9800040640e00c824 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 616910224 1250 616908974 616908979
    0x108030409020d0612061e0c02120c0118060e010606080106080402040902010e1503010f0b0a05030a020310170309090a60060201050708060f030c04020a120b090402 72
    0x40004015a0089a000c2c0841c0c12010b0808a2101d0303031401e4172400446008000c1e51031560f41e070390f5000301121010550443d4922240244085680800d001c1c2d2147e1458001c101b038144000754258401d5001e6104040018128000c1c5d1100011410040c004010035a01040158030b00040403a030540104042d40c12202c0c41d0b51041459500c6900f0301001c0c0005000c100c1c107000100810107a03076034a07002009009090741e40b40507100d600d014003c00d232038032066020213a0b021041121402e141d5002089a0f80260740030000340e80d0f5210b60700c031400c4015295200d2800000a80c194401c01038000c4014911001c3c1203409440b80c0d110b00c1a0002110003805100d0a244002d0485000324a410161202d03020006d40000350312887c0b60720080c08100d030024a5105442d04401c50100c600f004111100103840b0701d10080240d072401d54005004128060410703446006500bd10b0456540c00f08491041494054019500c4070740100c00641180d41c03042100b03804a08019090b08103081000c039061045400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 616911474 1250 616910224 616910227
    0x2040e07172a07050a0b240603010302180421270821040302090f18010b0607030c050a02040608030903010b03120a080c16030815121b01050d05191103010803 69
    0xe403003100d03041d0f61012808035410b001c0d148481002c0707145548054031491091425044603800000704c55403030354061158034841d0000340011710142e2140c425441690301d5007607205c54240c40d182015540c000c0015070000e10181c600121031490303503001c4580c0c9038003140713903090013510f000500e82d0040411550145d00704941c454800c01540d403000e00d01d44800510f04401032480c0c1910398002c6450307082c0c101c8040380240c07112028007036000c0a00c098a501440014020040c8085042c0044d809100d0400040c0402008034041414000c0510a4003c26607008100f080019540c03402d0507220313040004694070035480c054031f210380c2c1d00380030030400b14680f12981e1247c03802c125000140c80f80b2802400030380d039194003403081410710140f40469022103406034a45c0c4c420781c60555082c0448052071a078281c098410320844485600000134664507841d1021200d0070451440c1004031241c0c0207082545444034288420311044110025164028040d580c6050008042c1c81c01c00d0007403407000f072084d0000e5500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 616912724 1250 616911474 616911541
    0x151202150a12110705070b46080103061a060d0c050915070b010902120703091407141302070308010b0c0a060906050a0b040605060a0c02030102040e0717 67
    0x100008140c8903816040000d8a6070b40200e10904440600354043c0100800190302001d000d4100803840040488015251500400d940e0441050030b9040c0c1c00803014091070401604c0340000303900081412425510440c1500b0041c40c000c0c600f04080c0700c251800c0707180080b01e1464581c0c4203d21200c1c81030280505291601d064005d40003025007100c50401c010060009907aa60f5480e100404002c41d40c0d840c05446000c1d60900101005060b480141098410030100403504001c4d0101a40140e1500b00000e0800c1c450400c40311403500207071902644d009650020440305903040c1c900c292400181d0308444940b5824000b82e049100740c20010f404640900010801074402100a001004040c000c1d25000d0100d03a4500007525210042110496100c908104140d07031540b045070390741c41c01201c0502000c1e06d05404520a03100703140e9603400b00b0541d0800c920a40d14250100c400400081c26030820918005200074112070b0740003404000c520b00c00d8003040c800300650600c244c909550301c05070b064a14 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 616913974 1250 616912724 616912759
    0xa0e0d23040308270108151201060b0705030d060e0415020a03110c0d03060e33030d03050a05073608060411030d0207050901210516170303090a0605040503040315151202 74
    0x23a001c140c5030940d5902c503200070626504a13409007030000d00c110011a01c4548060241c01a210b1039000740710382d9280c0a0410010a01d54009100c180840d090010307a56514900c0031030103000355910390040f0b5000060b00403070b0306000058121400c1c155a900300103032038072903180916000f400d40300c100100444400d0808602d141d030081c41a8817004807160312007144140c01107070410f4000c80400c0c02203a40c8030100720222071107004055010070030f86817030008032a00d0201544220f0f42560008880410350900035201a00d240c050070180034030404603829480c2c180b40010303061603d080c0880c0280107216040b00501c2c000600d440903144001e14200300b40c0c0c01c1200b4403000052107040701e0a80e000c0c0c0584d01000c504240302003030020810f100145400c60601c01d2280f910301c5045020660380e0700400801c90f068602045440e60a64060004606500c50742041c1d859402241c2020344094000c007203002400303802d43e2140b1000c588981040e500150b40702010600c81c0c0988502a41203161540c00c0084e00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 616915224 1250 616913974 616913989
    0x910090f05152115070e220c0201110412032a020112090210030c0206090f0606040e0a1401050402040506040c0e010804020310090305030a0e0d2304030827010815 71
    0x84003c032511004080c008207110746440c66540118581c41d0080050180d03035544020700c610103000907078003d68000910704140d40354240d611205141d041d82d903040700130105c0c800e403c038601d071801d000a05600d80f038a684001c44602c41e01d03642240840e00d17030190583d0012010515030440711040c80703140e0f0313030704059001551803107500d1002202c00c44e40e540019006903904a00c0c2e900740d514690b00007641e003441c0740d000ba00c1c0c541c0c0508081c4e2654094044007007001c4001503880c0d8800780594011460400740c56001c0e1914418034001004807070300c10101d200002d41507110368404d078002c55007880107480b0307002400b08840140b40c40c00c000500d86003028556500441c00c442d0011310240440300028001c506580858040380c80c200e0000d4400030034428221410f01034440c0181142c0040c041c607840d03e12019110706812004c801649100d201c2c10b841c40001c10007a18005c580100f440d5503150140b401030041d03c00c4540c1c40741c1c0101c410300880f00d55944600606845041503d04490341c3c2c20a034002c000d02c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 616916474 1250 616915224 616915249
    0x30307080a0203160b07110f0d0309020f09250f09030605040f06022106040b09070c240c0f140f13050303041719030f050708090910090f0515 62
    0x150f02c02048a00d860a4034005407018150080d0429041c40c24000001490800c0001c00c80740540d03c49600c2c82815800032400b401d050029090005004030380784081100002902252035000503a00200310010019165003001403245018540003821104825912402c0002c80b540014031116002d200044150340b100d0f421900030111000c2c040d0050b40c4440076a40708140c2c002d9454145c0131401c4980521607032083d0008030440e4140102d0f1203140c040341c24078a00928a00401141d0940304c420b0090740384100c42c500d2a90341c0d545507a040d640101070040e0608580080000382d0a080341c002c141d10074401d41d28071030580300540b468034009001d40481604410305c1c84c0450b40744280c0001d0103a8003000140000c00207a1510885400c3c00b800107030800006680e401d01302c50b0301c00b900303100203640024803019481140c1000780e00c88909080020309406a04c8070160002c80c043c0c180605003840c49405001c49450180501151b00d021401c1806d03210140e0f00c2c0c0d203031505102d00c41d406901d040d11031101d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 616917724 1250 616916474 616916477
    0x120b0f06060c1605010f08010e0622020a0206100501030e060f0a0f0203010f092405060a03063302030414060f0903030403030302040302041b0503070f09050d140705030c030307080a 79
    0x4011151542c0d0741807001ca0103100c680c22500e80010080d40d40c04c2010a41e4410a070b0800c600702d5850600200050308008003513500c5030f064521f80301d2581024100309100c030504184115200c000381400650740d014140d80d0480c14900000e07000400e58820b004d01844c0c4041c3d030001e000135444420300d07074225180141000d2041d0307071070300c5802d485150248055802000070000d8002078901d00140b420403039403d42c01300165906410502c24a0741c10780fa2002c01103910540b11291345c0c40d06034804500905158000400710700900f160760002c1040c0203015081200e404c03070b0885a201104030140d0b520312440c42282c0c11065001c8103d49240fa011015007408268052000c1c603000c0b8803400039013103610580003200070950119042c801c0d400c01d8428040c00d2841d041110041039404107000c0c0c52404020a01800c100401061075080c903c04e103003400041c00040c012495421503480c0800c0894948034030b000162296240004e15894001380c4030002c0034004c1e020b580307890465141c001042d80841070210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 616918974 1250 616917724 616917727
    0x60f0e0a03032021090703020a0e0c0d05070507110f030c06070206070b0115020c2b020d1502180406060f0503090309030d090501021b061b010b09040501060f120b0f0606 74
    0x1c01010b80c0c03400418100d00140d0280c5110102480105413480014048426643c04860306100685130302e444642038601158456600f95188451244c170f5100b14a1450915820101806507044d000700140481c24854082e03640342d24016800d0010403d40e10f6400d035490f07800008541c1c410b003851401020440d0000d001ca0f840e020064440d14084d07102a8000184220003039510460f650f8140800111400202d031110340007141c030407140e03440e42400c1c540307602e080410549075011552a040c10860203a840b03080d2500e030b181306005210094201c07900800220a4901c1000d00340d1420b03204800a688094aa00b80c501d0200d16048546030802031004280e1321003000001c40c84c0e039003080301002592150b5104060903040000081c103084c002da8200c00311201800d19401d8950780c01f8144d47c410b040780300800400581c0700c1c0e4411b02420b100185581c11000c948188400e004064111109840c1c44030651880130344d40701c40c0e000e0401a1404003802c6840200c2c04108105900b008254020b1790081507507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 616920224 1250 616918974 616919021
    0xd1409010c110a12020a120b070509180108071a0f1614010e03031006020c010c02040c030b0d0b09071d150d08030a1b0905210114010909060f0e0a0303 66
    0xd1240309141c200d2440302610b103104c0b10441c40c0900c1500064000d113900c00015000503a95140c0f200c002030030070404c0c03050206928107903071074401c1110f55180c8041c04040303407542c0d00c414050705d81c0014001c001c00300c00151100803411031f18808503000c14250f1b0503e03919051915260716201c503080b100494481070b0000140da1012000d00446040d0001c50010b15901c5c10103013041e14800895511207419500400d2a2711000d80e0000e41c201034841d0151404070741e54003254000c80081221030207080d400106140c2e0b10040c0124000c044d071007565080300300c56400c1c0c3c1324110207080b0045000c95440c403405c20381c00100500c0100800601518001e082152030209a645140c495001160b10421035650f031441b201d2400020f0511407405203107414aa01c0c40da0070b04000c41e0f143e0702c1d185c1216401041100c40c440020000750f00c0f0381c2c1141610f51001c1e4103961110481c81c080d0041084c00d03600340e0b0624024040002d00d9104241740d802c901001840d0034169644c0560190443d2060724404501c0c12552 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 616921474 1250 616920224 616920229
    0x40e01020c1b0a051201061401110c0f01091e03120e091503030405061b15070c06091403030115020f070f0e090a1e0b010b0906270402041202030d1409010c11 69
    0x2460f5850b405c0c0e4001181c035a00b041c8064803117504d040722490400c510b14050559180003c01d40182c0100d09694117014000844016690310032140e0042101c0940030300041b90442003616a0815648680740f5118000390300b03d8211035800090030401e42c042d2546c1d01180c01d08a00082034241000c000d0140d904080e552400070320325801044441e0450102e003008440070300414443c3c445411218145000d80342040c1d403005140410b5507000416a640e20f11006061008885a000281d0a110220b035034039a100d4500a402c550fa003240040540301e003130f951030035080c0d001c1000c006850000c400400910302d014052040143d016181e60b000d07014410004000c126480052080d49142d40c42241c0c0c0250549040941c00d0816400704075049002e000300031095980074216800a40900900204011a17400c0701241c813042c00305469000b440080c0000314664501e000740310160003141a5501001b01040c2583c02d044188210820800c0070403a03941250b001d00401c1050a016029900e5285a49000b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 616922724 1250 616921474 616921489
    0x8040c08100501050f03012904090b07170a020a05070f14150618240319060603150911091b0715060b0c030d05151806040e01020c1b0a05 60
    0x11000c01960b20b480050010341041040380e0b51100c4158000c101d82c0d8002e101d086424807038035038090b444421000b420f0460341d41e00e800107650346810280d104064107080601601c450a84040b40c01506c94202c0020703140003a52082d00d400b035a180d141c1918041c1c043d5141c0700a80d5000404882c5202c040c442240e200c401044042108045519600f0050603c0410440e4803a4013450f001c10781c2c8600c40c1005404e002010000140000214809510384980c40009042081c1000c00c0c2c21440800380c5107030180b221a402c4002200d02816005600b44000001c20f41914280403000e03081c042d034081c01816a003043d0800035031005032070041004c103501101d01c1c0c1d20168025042618988016060203801140e1031203003000920604481a203000c11500740310792613006400c200c21103907030380340c00041105040a188402254000b80300e030520895403004070b61401000c1d59442d0069290188042541c0c00510032030f04100701c00001041c550b844002403d80382c3d0540440c0310b403c5100000c00140ea5100c0d1038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 616923974 1250 616922724 616922743
    0x4060806090105040606090207021503150d031e03050106081f09090c150e130f020d230106080705040905130f03120b06040e0a0504140f0a0209060312040608040c08 72
    0x800410b150074641881700c1a1040c0d900001d2220f44100000c50050741c40c60000295004451025616542c655042d01000d960291403660409220f980b03100805a000c440c0d0314103150140602c41f010148070804500703c40c800d00502010808600c04980302c0e000b03500c50707031501200103003211800b1600c410b429415107031016811124030941000620000410709416601d03e000e602d0801c2542e0820700c00a20094401030304200b1040d501c44a050403062583c048480340301c41446c00340280203514844100941d0907020315584c0c0c01c9684000301701d0700e1040340301d24018121561043d080034140f0b040d000080c58043c107024540203543d40c3c1103001541100541d003d040c02070b00d4040440c241c1201401c2541d200001c00d40c403510041005022240ca0180b125400070b00c58035000800e65524a40040700d60a4810744248600c1b0328042420000d8002410203a13031231007600e410709e02c2c1e240c00b070600d03035500a03010103008004803c0c0000e1003000c0c440c1c10540d41c454081c008024600b9500c600da03034100030b65103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 616925224 1250 616923974 616923991
    0x30b010b2d0417030c03071403091801081917090d1b1509051302180a03060b040b12030901261005011407120e12030d021b0a0f0206070204060806 64
    0x424100041d1070031144071148450f2201c099481c01c0d0303a401906450b8440c5c10001091070543d580100c0703c4c00010401d544099001900a8858a8088041d0046c05209100d0580d40b840303081c5415144011104540c59103940c0105080d0710540b10045c3c460b0b26810180c95950007440f0f0703102ca48007140074600710400e91112620315010050502c103408140c1c2c00035000c01018084405810041034882003112045912680001078481c00d442409559800008a40d50340c0584892408414050158460400c0440031241041400c508800388200800c406084408580081c0a440b071030f5402040c5070f810340426800d401e440190101c1c00c552020b18182c416211b0401040814000d41d42c10240c2400440c3c1d0b0404a079040500c0c030394401305008a03900e0b840c02049032121921106885804450801c035644505490700d6840f00200e500094101c00d220354042d403503c0b58803c002080c00300b0304000030340c4c0100890015034129006d1007055444901c0132a00300395100d06c00540f0060500c80d4a024001c42c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 616926474 1250 616925224 616925227
    0x3180605131211030304030f1b110915280302060316022e0e0715020f01060b130b090114040306090201020c090114090a0605060703020a1a01030b010b2d 67
    0x241010010500c20159480511800180680038280f0000c2640d41c000e81c14a0500d2000c100c82204035840b100d0102622680d00c52014804100071032040300c034032298810364002000d40c5d50140540c02041d4149103c42d000b40080c1e844400c0b1158014000d403884180c50402a021541c0b80e000c070b40380341d0084500706030310280d8509148600b541070002d0400300055500300c0802050154410580386150328403800402c0e40c40c0c100018070300044c0309a03401400c0070362540201c1c01440c40c0203911210942e0b0140c49a52070103201107a100306031000d403070954583c032402d02101402c292840800c0c1d400868480d06210f00b0500c407011100041000b48042c520400d404141e86038030344006440c2401d10842240324400c1080188031240c104c1411302c0345001700700c902c02c986848011070040200880e81115410a000040010a00d90006030070360069100c1c40d00342c046220344101412100c0c40a010040a000c4444010001c050501d00500401d1a0000c44500d07c81d103c8503481007011803020300701911100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 616927724 1250 616926474 616926511
    0x280f0608090c03010621020a08030c030c0c041a0105070501020409060b04051002150a09080705060c04180b03030a050d1409010e0d020118120c1b0306060501021c03180605 75
    0xd10420000c0c0106070300a01285041030301070914640c0d103401800c9000b8000b091b0009542d683e0201c01d00414144007540d9031001c1848600b82c582e404218001c00c0c0344154069054039003418410180c4158074644c800322062071040044642e035000d400c0c142c44941d0207110100700700980d40714540041989480c0c69594900d450148000a00d07103211a800395001200c54045240c42e464155503c800f0021001a4010940c80c003003010340103403070005c0c055116180401521641e0240244152200d4203030046c0c0e41c0136940e562070700781c807511304146400d9002407021004071409000030b80040c401c10940800c40c1c00c92078800011a44003190b8012141c1e4445000703002820061021281541d41c0e031001b800222840030742034058008000d00100a275180c0fa03a580c3c40385220b204030358045540048001030a54804100c182408013501041d00c0041c50030341c0c0064a5800020004001044c0f40e6424440205441e030540081c01c5141e0303095011809600002e00085a42c8505482a8030300540b048502d46c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 616928974 1250 616927724 616927741
    0xa2d060203090a0509190203070215040602120906010b070803270601060e04111e0c03030f041208071d01030605121006090b0612040515010e0f090c280f0608 69
    0x43d4941d2145025582001c1449131404500108a5040c00c00d5940035a49840700310080346070126103541030540c1d090740b500740020050150010b0140300c480c1404080700fa125000216142c042c203100d609000c0d141040031400080900f0040c503440241109a40202c800604065403a2101200da0084c1504002e0043c030009400064a028401040d0740c00c1011954848200b41184100d00c0002529031105801000e0901c40e4421540e030224144107880c2c0700e081c03610544017400c2c07095038112010340e5285143c2280f03034072800d507680c810501c1c4c1d030300d601c4480c404011603041807440840c060704250b16004007183d152a034070300c00210400c0390001082c2c1840d6101044040b9056a04215142c9040400c00d01c06552070b542a83c6120810206480c00313521a85045031170407149052940c40c043e414000007505e0024000c4103071103a0410003680c5048c3c0d43c0c00c16480c0e210311010b80342c0b03507200c00010704d41c141c41c00340441d940346080000e140001505488290382240682c05503c2200000d154004201802 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 616930224 1250 616928974 616928989
    0x1415131118182413140f012313021503071d18061009030c1203170603120706060806090616090303021e010f140601090f050a2d06020309 60
    0x822554001d44100741c0e0f0341542e143c0d80e805141d10f0f501030961000114402c44550315000500940c4081c4d2008a9804100c507681c4400c2500211000b652922451642902250500d10040102e501c8290070035034450340025050310302c0c210240d8101c18002c5442585164a00085000303041d551168544035170074201401c034403d4505096400340540200c01c0310003031180d44015400c14800c07034480c00f9500c51140c080303d010059030710107030450b6110100041d04880c0c2d4542d070901c4074000d54500d18119500e10b180801208240c0b181c5800d584506500e03026409440060850203120704404100265a080d00520701711040d030b40402e10741c0009044c0184d00040e9410401e0900960524400c2e0703514588001e91030703103408801703028121400c0c104008516400e5100c034600c504108020000e1440c21243e000003541c0441d8500c4c04a010300b000400c0440c6099000d80c110f03a001800fa01c116420324007000001d40c10403c50f66040500441c01d6902000344491329005090f9550040d9220b82c83c100400803003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 616931474 1250 616930224 616930261
    0x109022119050303010e09122d13150509130c09060206040317070c0b090d030e0c13020d0204031a07120507020c0103091b0608041415131118 62
    0x114201001d240060004000e0f43e044030364040007030740c107503071032000d80c9042507120000074080460003e12114041d111603c0020048a2440300c03028882d0454030500c0c99216603488403540300d280b4101044404100390900100e244c02e46411800c080120011410310308060303850710b00c555200c05554081d980e00240c140c000b03104c90300c000c24140c1401e4802420f8003a40049010b00e110380000015034403030050a001e008640c1c80030007804a0701d082c0d42c4490b200d052550702d010000b41000c02c90680d171040090a1002000002c0090aa400510603000029888200c0810286800307010002c04a4000a840d020805074814100300500d0b04103001000d92805080e0a182a860a0140b2010700e50000d417040c0c0e00322003030030b0020b00e54000d41024284040060800122070120440202c3d049502421b240c2c00b8601ca42e680c81d81e044001c000c40d54036516542d40d40f210071502c5000081400700030703401f4200414050001c2842d801958004216501d10303400c00840e1042240050080010700c51104504 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 616932724 1250 616931474 616931503
    0x904050a140a0507050f0a0e03060603010e0c270103030c0b0c0a0906080424060801060b040506031b0c0102070605070807020a110d1b0306090c0b1e0c01090221 70
    0x35500d403a5841c8a0606006495440c03000d584200040c0214001c40443e00b14080c1e9a0500792120703070741c4030014056904c3c181894000d010f4100451902c0c241400794070301d030b00c266602409000140ca41030250103100007146906488644941413001d1101c000000d0203503019543d01103000380c0f50304040c05004000340c080c4030f02140230024080840d5002e0404800d440790703460008120384440c10054050798203000c507241c15000155440c1a01c0084d64014012103031183d0086c001c1c60354440b40728400380120b110b03054000c2e0b42080000e0403248108940000c0c0c0741104e2480e03041001003a00142240c002400498a44d9070321800c1c00400740d00f00e0801540520148002d09a4104640d5501041d400c10324099000710702e11136804007000301c44d026010011040c6018a880d032940c9080000c003415026030144d071044a020750216203d002407045420385000b141c0f2101848901c0c025160b000d40c80b500e419000c9540c3c56080b0380040e030359021144e900b696041003c041440c16014600d0909000000201 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 616933974 1250 616932724 616932731
    0x120504050918010e1c02070b040b0f0c070803191706150d09050a0b0a0507110a081c05150931020102070f060801140a03020d060b060d0603080904050a 66
    0x1180c0e0781e4040c1e16804801e12229095400d040d04080b405004c4080f62621280a000703104441d180d40507204203840312030341e03084680070b03031b521000302e10740d0301c6030340128079142e03030108148140715031004001c0485101e03600450302c078160303502c9119055400400d0a0351030303001841080c03410b00e6400800b65240c00b6200c8030b85105410200c00084802c03540003080002500b01240307005603004160b003e980510b81100598900b07581c10f10b42089c41c40e000f02c0e40540c82c1d51904022a20303c41c0b24084840d0085408402011000340c2c50f29000d003250404022084420800c4141548905035400b07614043c0141041044100790f0150402040f03c0f802803114966814a000421032080300c44545503050341e0300c182041c0f12520710300040b8109006900820b03945408481c0016017603900c5011141250340d40301c1b02c00601e2070340c20200308800c0081d02c400783d070080508004001250300c65000f030b43c0411005020f03e1070070036003c000070292180d036030042d43d4000020400703004a003014000c0c160b01c41c03281507081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 616935224 1250 616933974 616933979
    0x9102601050121030c060e0d030204051005120403080405160b09010212031e18010e0f01060f060e010f090e2d071707031e0f0e0c130b010302041e03120504 68
    0x5001d0960f40c402d0140401c07860030405810b118065100140d441c0c0b150b0180c41000342c03040300140203076100340700e400d005483c00c103944c0421620034410765050780c003201c1c80300b80c3c66140da407805c4036483c078090f00c1030710076016012140440e40302c0042108004c1c0f402c03019158448030007800280c20590207644d112070034102041002404140020900070700450500e081c184d50704c0d04021112080000d0300c0c548425880d001d4400460b003000102140074119a1000b4000251520101510344a05208400c04298850890303200e640c01507024216440c030034600500555a0340099045c803c0302aa40c40c1d403c04c00c0d551808214141c0201c2640309c83d040145100683d0412040051295a00c0170501c056480c148010801c0184207030400709080c8503250b01d00e4030581180043c2002803006643c100007841c075113406400c900c20040b41040f00c7d8a0010240000854021441c2014100128006040542c01c010200d000f405003d5542c40148140f200d0031000c908514024014010a50340c5105001051204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 616936474 1250 616935224 616935269
    0xc160305120a120212011d19020c120d2007020105040b0315030d0e0307060302030108070b07050f10050a0b0d02031f090b0a050403020705030307080f0d09060203160806010f05030402091026010501 86
    0x223503000c1d940c01070040c0d03240828407800b030504025034600310f40703d0720000301003d860710300d134010803110212207041008280034100c10400506c103100e0000c1c04118280030411005030310b103001c1c5502c503285036106564007041c030000034186000841414003040101039410502d0504015080180403a07050451a40d410300c1e040c1c55035031145118541c50803100240d0442080802e108040801520300700700c03100e01010650180c00b40c00708584066090b441c011001603d8580640c2e180030654010340600300480c2e0300c0e2916200b059880b103404000c980c5800c10b0100146441d81000d1103800480720002e40c80c10203250082c104055540407600c241d2090004001290030b030300407524189800c44140d41c1c0c4920540c2c910000d0f00340c22340c0180c00f140c400b104001c00341d03c044115411851156a90054070b41e140e0b001502e801c000300540703c0008200f4000240141052140d03d600102c0d4000f20104542d603844c0500c0603109480380094502000d07030050803e06009004071409402613500200207000602074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 616937724 1250 616936474 616936501
    0x70506060d030c05030d0204060e010e10200f01050412030501030b160216140109060302030112080f090d12030509190308060109050301110c160305120a120212011d 72
    0x681c1c8180001403204041500445043c2c000c10b034030070152601c1c1d014614100000f9081480703800041840c02540c0049580300d5103071802d00900040c80c0c0d001da8002640308440c82c41c0f01e84446d00e550180b810060745500e508000381d481550402001040910705840c2409010581281120034103041100500029000e4040e2682c0040c2c8482c040c10f811030829002c81c9840400390401038034802c1c0400201d035203401c00001c4202c91800b07880d0800540c2e50340c201101248002d200d8460501200c1c2c00502c0000d900c2002003d074605001000d03400d2030800c41c0040c0c8070091100080707507114155110444482d400d0300070158840c003310003900021800907001c02e041c511540c002006c01c1660000101143e004081501c05441d01500030401c80c0da034203a01c116150301c02590907000d4411440405ca001c65007144800c29242d100c005018040880c4042502d55002658082c0c24007281584040407269a440640040a1940e0324121207501d4408003420415502d9000540b030003c00c010482d40010015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 616938974 1250 616937724 616937731
    0x1204230904120309020a03082d09060c01020d020a0306150801030f0b220b09161410050708031321320304140f03041a0304060608030705060a11070506 66
    0x10307103030b000660099100320000c004000d0025800300420300f02100f800810720180110341c1034544540e01d0031008d94054504003004024003883c1580811a11705941400c2015143e50040c1c4800542460b0008082c01d040c1c3e0004460400003c1e901c0c031003003000d00c4800d07074650002030a50a0400a42d4150b44074030a5191210314050300c40b006207070109408624495507100c0d11002080e03040d1a40310305161901c4000429218455140f1a04007064524181d1055800444400381c0d810b0800302407241c2070000200f1005c540500780a4107000c1c410108061000035032090039000f00031140071505240040a51002c181c1c3d040fa10400c80c0c0460354038a0b040741024404001038000d501c41124401e52075039000c000b020003007a082c6000710500c0100441a189040402401801d403000130301c410003040d035217006030b10a0107042844007a143d004410681d0003160428041c11011840d51740321401146142e01c10482110f195202030108a0005281c0c030440d5a8880d0320400c480c6002100c0e02c6160b507452018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 616940224 1250 616938974 616938983
    0x1802101806032d051f05010c2918070b040506030a090602091003150605030c030c16020d0b040302062a1c0518060a060f0e181204230904 60
    0x3d148203e0f040720800821407104600e603a42058041c07200d07003c0c030041c11068400f6486840b44089007041d0411003500101542e2042e0b660b1070031030480303483e000030013110081098040d00c4000b10604044540d0358200f846a490b1a1403c40d0325100300d40b0207464088a81d101c510f629005000600c1650b5030242240d40280c3c11800210741d0301c00c0c1d07042a2000748208103542d94401440480400b01581503089614015180039219112540d0f5030010b0382c0c944403c4505044445c030800000b60900e420901030a81201480102c0c15040701c980e02081100140c090309550700c2070001b041000301a0b0400209074044805c7c0c1c8401c0425510000d01c0c00c100f8050743c800e1090b0740020652003044981d6020a4528000f80441030101d414610300070f02d19043d401c00c090f00030380141350001d58040c0b200e00603141160a400003c00004e46440803070344001c440942800080d00140c001c0b0380e1000d800308903012403443c201079002d40c0d030b03440c3c4401880d83d000110000000030b4807404540c0d40c9941c500c03080d5603200303402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 616941474 1250 616940224 616940231
    0xf1b080c0609011101060509190f020415180308120a050901090309050d0809041b020d0c11040c020f01110405010e01020f060705090d0f0303050415021303080c10180210180603 77
    0x19191030b81d024100300c7d0002900035000904000c0c10070907182e40c0b08400511414100f03d001c0b4049044e20a0b0701c568028900c00100320b00da01e078180e901c030340c01c4150700424100002404a840341c4e5114800c1c0e01650f03040f608884c94801780070b1004e142e03204280e00035588100030000b13402965405460706115101d000e1044901c401c010050010100445560180041c01005902500c0d600f22841e0035024403c20010722502004050490013001d0301100f40303402280d07110310140d2034420000039105490181c011030050018512652409005880c4a110103030140341e2107500300b000052010000d03483d901d04562050482030007009022980e41d82000d41494100c2e5606940404641128400040103202c140201c803030b00c043c0f55042e80b1440c0107031310400d90020034494031240071003130340200c0c0520703100940602070402c0092583c1f4000c2c040d12412034280d40300b52120103a00c1c01284c8090708142a4036150041c2d0f8011494209420302804440b070628441404100302400e00140046c024031060694 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 616942724 1250 616941474 616941497
    0x6040b0f09010b0d4d030c07030c020d050f010b0a0b0f181e18010503030a080a1509050411060a1b0309030f050a1a0c090910030f1b080c060901 63
    0x51581141130304949a0310117880c81c4444d00c003119104e08603c84118204068202d41517480308000700490600c800203101e040c00c544a1012104080d400740034100d05009080c091200103803034440380748000320b0040014040f25110710155a0948110850992040d01089400d00c000c180341c00584207001c01245c2c1d062340741d05104000000d00b209060740c1d070b90300080607a440611191150410300800784180d40145085048900841b0806800e010345a8541c10a00542d006e040c41903000c5580042c0c032100109010104c000101460758080c0c205400c003548480402090001564070342101034002d4401d685441d010b00402041d29001d010950400760061414006043c4221400c1e00656004106a0302214292800300c0d0f80301142481101e0544005043c040d06c145088815841007140a10451a10783ca030301c100030041c0d000074088002540600030200c00700b580c0b000724030741c041e103c0d85110120f89a401d46602001543c1d41c0f215840c2d602440c44502188c0f1440248e0b02c3d003c030b003801c1c510007168 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 616943974 1250 616942724 616942747
    0xb01120509012d0b0102010c4d01062112020a0602040e15031b040f1b020a2a060f0c21030b030307110910180506040b0f09010b 56
    0x2402e0100348030f00c00e02d41500311040110f050301119000c65207460402104900e48010390980b02c00d1300e90000401c08401110f9451b42c01c2a8480400c13091072803403070f0a140450030704100c440c00b00c1d42e0149a030b0700c0480d2100f1590882403090b280903004a107110714411000c0d1038200004403090030002d016401c0800e45292080c000c210118503150b1108095413116283c1185080b425000c9507003a403a5110301c94194481d04000c10340950940c10040e1014010b10303104140702c00b4001e0709884e6103200e959640840540d075103503103503401c2c144c1c200e9000c0c02c0400748508202812400c030307424010441003582c0c009004007000d0503014007103400509040003004440d9409032403000759083c1c064410310840400710079004c400c14507001d840700642c8081103403e03030350800d05559000d040700040c009103031301110a4241c9004452254400182d890103005103171900000000e05299011403106281c61700b06000482c40d00d8090140c20302c10a44041c00303814410000503500c110184161884400001803481500b07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 616945224 1250 616943974 616943981
    0xf04061a1c0c0216060813061503020a0e010504110c100b0d080d090b0112030206011e08030a0201140604110306040c0203130b09040f0c09031106090d1103100b0112050901 75
    0xa44600704202101c51444082d44808078209000d140e1081e8620201e6003d0040030903a02540d14403954040c0311096544000003491b1400c441c20251850802c00801695003c3c0c5500140403801c1801041e9490b020078001030b0b4400c640e2000391040144030baa501100001040b0303010103003410307002c51003035002004150707800210b40c8081e18404001402516541d030a40003601c10700c1c4201050b9425a030707100d003249050b203d10302c00100142c0000d401003111481d0240744803840340e042e48003540403e40c0d03481041d1559000901490140c1d44030b1078000400f00491074002d90015007514240503c541603480b4071401d10000300250b104030746d01d003c0300c10910300c00c0041e40c041589680c52070030700c03e4648000c076820703402ca020300a1050382040203601049034a070040a800d03950039100c01842600390303911031106004d2092001c1d08500c0a0001080568500c0484c00009001d04001e8099090b0107040c1420300301510f454000090a00405c100980d9000f000d08214000500e0b00064980f1061071082c0903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 616946474 1250 616945224 616945267
    0xc080310050603040602070b2428031a060301090807080d0e0601060c0204050a020a0f0c030203191115060127080102030403080613050f0a09060b04090309050f04061a 73
    0x40b000300401081241e103074020805240105615940e60780c80c0d400317403003250b042ea8001c14081c507514903000f05a820641845c58020040000b00c0115040e111780040d070640d682d40c03055403021603200c5078501170303030112210350780041d81a0000c0c040030505440701940391180c050f0003002040e0015100480c030782d882d803156070303070200707440981d130495a40b601c00605051000038241e100b03e2030b04022900c0650a4400c0301c0300d0b00955101c0c15141c0d5061301c4140e1303445400c00020b905500042000a01c002990120740f0841c000c2d42e1550007007810035203141454080e1002d9140c0c0141e1020b020701116030b812600d000d80d1034811908a4100b0009864141c00c0301045901071b0500d5030000c0140300c10103400080861065006580500201071042080420713a981503e1350700b403038000c020200c1c00a80454000d41c0b0340bd03010700000b040704103041000c5811070313101150581c001038081c181440580713005c0d242031180c82401ca400b80111401e105100c102c80e0010840c0e903a43c0e000000344c011401034040a082c10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 616947724 1250 616946474 616946479
    0x70e150634030806010921020103050603122b090302070506090f040501080102071a010e04020d0f0b0f010603510b0d050105060301141e0a0b07050606100c08031005 72
    0x16805041e24020f080700805961103404074001a10200303889580c81d401d035205014040810a00e645544c005500800e4040c01c4e8a401d80118172048100c02454802030940041460610000210413a101450034807140c401024032824000c8410100f40d000071080c0684904903031003680d400d03404d0000703004414061072090300301c0c0c208400001d5081d0194080c0c50514046c0341b00003400d41c0a0b1104da604031409000c0c2c3d002503002e050108000d0b040400410300102c1c0320742c40c800c0000ca815201c00e09003010868010f800d00c84610f005010f11795060041d00350045c0201400c0a0b06030710511081c03540384c5410f02210360f10b035a0602d111070000c00111950304d0f10880c1c919024460b510390300044090345c0090040c0340d0702800c25000090302e040030021a412034101c200c00200e41d03a0071400b004000d04101605030490700415000b101c081d0355a10008006040508103150340780d400d440d01501b40341c0700501c0b80d0b100b0181000c0c903002045d0448031340b01d070b2160300104282c1e5903503819441030740d1800385030030083c2c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 616948974 1250 616947724 616947817
    0x80d0510120506060a120203060f0a0207080f030402010201140601140c1e06150a0b03060f0f1c0320030301030308040804092c0723061b070e1506 64
    0x7030038407401055650094005907000304a803a02d034241d040103a0b12020000390140d00c800005041e4400c101125500440000d8001d0b00c0c0ca2495110f2400c19000558020b038104000401c7c40708642e0244110402103407290750002892404a002900f01401c46a120fa40806c0008801044880c1807151010001440b04101003031480704c10129038900f012100b07052040c0209829612611341030801c0011556902e90b52491962041c041c8000e00d03c82c40d0180b42c100c5000f110048039552100c2d0001c01c00041c45021583c4020b081c14010040070010b415444240701104c071126001e003021085038103403038060600300c0d51601e5914050003213102c0d660081c007815107040d440001d4118000c00040c40318112000209840c10482d41d180e0302c8442510586480c0c407200b401c20340808105c0ca004038400b0100a01141c00c0000c8031300c180d6104084034031003076201d81202d20144002c1d00f040c1c1c3c1c1ca5800c00c440c41101c0340f1040045020407114401d0038592000a400e090210b07008003003c0824009140c010300058 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 616950224 1250 616948974 616949009
    0x90306070809060a09150e010209040c020d031d10020307092c0106082701060302091317180405061203360a03120201140c090103050a09080d0510 64
    0x14007a0005035070544403801018007140c49564180101da4101b6000414031a061100140c0c48004002c100309881c8155000c0c42140d04943c0c5900c501000c04100d600a4503070030822500040440f4040c080b60180d01a60010710500c0b908001480c0388841000c40005175a9140d001080d650b0b0281035002000c0401820170748180303801134a90850307000100d120118180e980b2000180d8900c00101c030700c49040030071b108105a441d0740e20a046c1d0308103c3c00c0000041c01c00d032207801180708010101c0d80c2c0c095142c40301308460f0400c89007405c0007007050365882d00281000d1003000d0b40e5000441e15500d05104940b5200462040d503140080440301500c03680c105c0b644e507050f5020f111106e400342c040aa04006c148080c0c41c05c0078a0000a1241c2020000d048040d4103096940d060000810401924119035803a10400520240014170a01400000000c04e8960109100040c00e81d600103007011070042c144000500044c112106641024541c400e02141c16a2000c1021107403048036403244181a4048109 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 616951474 1250 616950224 616950227
    0xe070e0a05060f06180102060c0405031b0a35030f04180f05190e0609030702210a0f1b03150f0f0f0605120c180c220501080709080d0e010509030607 65
    0x5410110000f0b1f003d0302d031151754900c4001c0050040740715003501500900c03e4682c07000d018100072040700d180100504c3c0501e84480421014007000c0e0550b030480d454014540c101031107038104401103042103070021441e000046a54801c580a54850710b0402001c14030700c20440c08590300012410400030740c0c00c20603840e007020300034511040c88e8a040c202c80e10b42400b80b000614040740240c0700d000804021803511605500713010140f4203d6580c00c01c2045080003100764400309000500c2d441e4018410418024041e052410120351084100103d001c030050042000a1512480400303450010100043c0204801b00b4540600411301d20072180c0c030700d0045180b803022040e601c40c6c01610800e81d60400c404084841c0da0355207a10703c44103030f5484046035003e142901840410f4070343c0910b0303258200d41080007042115010032046007800e42a0710030840c0501c000d5030705c21012584109185880c144561408017420348501016076543c04002a20103d9505640180211518000003a04031a007600e003d440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 616952724 1250 616951474 616951507
    0x605070309150e031602060408010e030319060602070b0f12040b01090b0609130b0d050f0a03110c01091a1e0304060501060f0207050103090221060a0e070e0a05060f06 73
    0xc088840c0008440c50380800039440c860604400300e01802140f500008090300602541517076012a0b2050041202040c190b00a009581c01011021b0085031241408032407400f4200a80707801c80c860520f414410442c50b64000390a0048038200403046035100d40081d00c0100d5845a0b01da0300462194483c20700040102140d52181200d081c014104410090102004020301c111214540e01c01136210049180d4a4160b2020402c03001c003d107410f5003880c0b65980c403810200c246004030131b01c2c0c00c903104070024140c011840d492240c00c0344002d0f0480704881c400203405c0054034002d5182c99040307000c0058030748890780c0842d44000c0540030100c801d01d072814041c403196031007200c0481702107007014000280d0f2400344502d0320741c001440d005880464181001100100003488059074005120005c4501d040c0346800707003880000701540a44030626240c4090025038480d510855026031142070304002e02841d02d2085608104001c0011415446200000b0072180510968950040f0001022503890f0700e80036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 616953974 1250 616952724 616952741
    0x606040308120106121107080310030f0503030919050a1b230f061608090310020a02030c060601090f03080c071a07110607020d08070516060e030f012c010906050703 72
    0x80d142170141c00f04400b65000c3e1050381001856030380c0180044000104400061340d40201400c013031100043c1e6a80301d05c81200010075007990560000001d00c860300c80103000c504a02090f10001d101041c5650752840c0c1d440342035010160410b00c0036003440410b0701004030890010700348041c0c0003007031030f1001e5103542ca1206030110182c4511019aa50380c9a0306210f41a204d4a07a4116010300c002c860540b55164194807003550103a05004803003400c411186c003032001e0244150030342e00440c2c4031030f00654000d1624402034011030510962882c2005010749164191054036032040d10780da00c03001d030b094006207030481941000d0b090001041c2001047c02c181e00103000011b0040d21007504042600043c4500c505c01c011000e50003455207040b2002042d407080042c600c0074410300880e681100843e03a40301900d000c54001500090b5010345903182850100440103c004005c4c0c001c015040106242c0854000da005290041c0d81e80c003403003d4041c0d40c00303601000b01e003908548107000710310702002c0c000c0040c400007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 616955224 1250 616953974 616953977
    0x5040501032d061b090f081e0309040603110909060105060a1b02030616120e070303030513060f020d06060212070308042316060f02060712020f04030b0a290105030606040308120106 79
    0x2400001c0510105045001300d0f0b047c100500f241280c0c0b9540300350f468403080200110741c442007001103900c0d215031080100441c09568205000c41c0e113001000082840030b07026010b1540818014400b5a03964021a203045866007084100c40041c84502070301244a4240039506020341c0d002c10980091641d00078400404959480c142d082c030904c81401161140b059140b110b6100d100c0a000190190b4481a0000320441d92120b16030115510f02c000e40e01c014200e035114503000320f10100d03400d07503a000348005002c060001c0c0c8880038842040c0240c60081400250800000c0d1000c602030000784020030341100f44440c0c0000152441031215903856920b921800c031283d1400d440083c040e481942e00800000080e805060700340c0724000e084810840b201c41d200c0c00d4070f900300310342c200c000300d200028001584583c41c031004500d80310f12140210b4440556401d80340140304001c409100383e5000011100b81c0909141c2d0322038441c14003050840c01580c2000301058400540d421035a54208103c50488416 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 616956474 1250 616955224 616955237
    0xd060f050603061003052a04021602040609020a080c070f0213061508010b120702070b040f05030d0504030b131104091b0801020a09090e0307051207030905040501032d061b 75
    0x5a13814001c443c080c40c800640143c2040010f00078400624800304030b50400542e040c1c410406205c001412030b4003120741103070a90b288914a10460915006500007088000c50450412a8601c0003620400307009041070302c1303d4000140c4104000643c2d5400403080c3e0013030001140c10498140d51001000b0a0080815180e2220720b807004403445036517603178181d40303032501e0090400300b40310903850341c0d85006441c2c00154010360401041d0140c40c41c019000421504010030716007881c0034181410002415114000c00900700424008540c02401d8243c0000c0204880064800c0c5400c1014405445205c0103900c107040c00300c403100784401354564651030380080380481505552291013030700301e10403146102c01081c500182000145025404074902c001168150382c0750640655030380d13003010441004440e6030b030b502203000008d25074481d00e1030000c2c000035641040103505548400001ea102e4900065040c1c180c800a64000241c40da010030606901100501c840520f50f44a07181c14040da80030900021913 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 616957724 1250 616956474 616956481
    0x5071805060306070f03020702030c0613141f0507050a230606010305190b030a170301150203040501020606040f0213031410090b010515040f0f0f0902090a0e060d060f05060306 77
    0x10302203000744c02610191121020f400d20000c0a401039000600c0580e40742c003c8134000700c0203845400040681c1c941d410300301c1e070354141059441c65802c0c0c905d01c403107401045101517046605030303000002c500c00400c81c00d03c0c1d40c41c0e111910300039241c040741200041c215004101a0a080240c6035000010b910307408041d55030325074854004408482045070703038688610803a0041601c1c88440e42c000e04004030b01038155005c10100343c407490f42001030b1020103015811b000004100512030208a24000c400510165240c1071410700000d58850b005480544560fa40c1c0380341030a25801a4129003048050440d1045650b50302d007003828030b51044c8425074a09000d6000c089860a03070b94810908010b40c021240e0f03a1a90806040c4a95144031819036141d0480801000c00c035904516000f0f8028100840300d2003400381024003013200305540e58400620ba80c01408610706c107a5451084005445420021040700d82e5580c001600c076420f01100500080d181c503c14103c00a500e8101c00d204040035400c1b9410390700c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 616958974 1250 616957724 616957729
    0xf070606080d0c06050907031403030f0c130e0c0d1a0102160e0a0c020102090603010e0402180403020d0e19060e090112150e0c09070c02041b12090f0507180506 70
    0x2c0092809400109480801400070b000c50707200c10b42140100040391119030704c0703a4034444900301d9807503020300660021003080b002c0d03840c00d180107510003840c000b094245131622070705010f610b00600580c02c666580400050043c1401025600a403142c00d00a00c01184c4061190711070720700940381603005029113071030000f018101114000031103040c07804030003155403100c0000c40204040b200311030844d5020018120f855581c000658003801e00b0360030b0541542014810090364186558003455482111070030400842c4d004074003200700e200282404000111a440040d00304d007100a241443c41d079400070082082d6500c904210703c4941c3c1941d0078602641c0b034884084800003041c1b801021881803c00345031440074035400014400244204980c450316448001510402080314050001181203c1c00415480c0a00841c1d0007007081003800020135400c0e00d03004141000003d504544e181d150740f050800c0200344408411001c0d000f006031510252a00a166851114540d00201342c0b800c0c9400302e5010f1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 616960224 1250 616958974 616958983
    0x1204090e0c190b0d0209180709060c08070308090f0f0d111506280905040203011802010e010c0c1505030103030908030a023f0d0c020105090601050d170f07060608 71
    0x10482d80c1da02401c9500d4482c40003429448144001c003140d40038812021541c681130320b0340511011110780d803001860b250310f0090840a80e50b21440c10091815030b15400300d10322004a8204940610b058101c6a43d83c4548901d080e16441c0ca01e4003500c079400c400507031607030f021484101900081d40e0324600000b2500915545030440107903408880c010b180840d98a16190b8101c01c2050a02401c2c0c540d905c025090090400c40c581c3d200408941d102d004000c21850284a031421400211061110503141500000c00d4030f08600240e80c140000c1c4004a0280010940c0707000080c10003d2130304043c5107540710000c0c0640c20038407049000c90310084010a1011010040d281c104925a000f413a030192034402d81c180c01c64810360b9400c00141c114100c00880300d81050f2403890039038101c040315620403003a0296421903101030b0381c00c000c6914240c140000d82c400840c0050455204803061500103a40e400c18a00c1c8000030003003a034080800080c20000006090050203800303015110400810f550b450070b0b952035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 616961474 1250 616960224 616960249
    0xe010509090a020a110f0a02181501030c02012703090501090e060906010915080105090612100b1903141c022116080310170303040807051204090e0c 65
    0x1030700640004039042001ea001d81042a000e140c10a82c0c03500c24400c89042060400e90f00e03c4c02e400c1482920103508124181000050b0040d448234080d150042000b002010890f094a04054441003942d403194400d403c05400c13041c0290300c00d0f0190709583c15101000601c01d50407000310f0f154040c000f44542c0250102e004540400700d4031131a559a0004000c4003090060026041c000c1c0488081451100b14085001c1a190384d25506e006505000400000400080902d48200c400080750b0b40c0c0b0040c040782c1c0c0701550480f5038000c510300c034442c400200d00b20000c000074006004003030000000d1040e039500081c100140eaa007502c0d01140380304e00541040e2020800100583e2104d4417011060346028007200281904281c06070030180340a0480540260302513007524040408014007202c1110681c0c294001c100c0707a00144507400d1120310403912404000c0c005041c50801241850a00c0024030115031450710410240d5600e9817140d41210043c03d0500040f42c40b80702c0c88890354540e0900c100080c11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 616962724 1250 616961474 616961479
    0xc0612010314010b2b08030a1508070b07020123030c0d24050d0302010e0106090905070806010f0303050c010b0a0e071706090c07031e0306080f03070f06051513020306010e010509 78
    0x1446484031171505801e00715000c9080316924801002c030042000000030f103010b0f1b0f81c0580301142042444144c0124181e40350003c0006400c09102080250050f400300c0b17429542c2803c0c1908032200300d0341001c000111060740b003001c0450010070846801034040c020144c0d8001c41da0f041010302c01c600025548103c3c07908907298050300401050080f460008080084284644004079503010b103002100d00391403066010790102503c4a001c4410010300344501009400c810000b4260340d89401b190045580081c0300c0a030a000e0300181e03180c0f1b220020f4100c1c84400c4d03005800220202e40c0d0341024240a40704881d24000215500303000070340306140d110040d0003440300030190754850700c50800100066000b0b20049003404041c052091080800501c8101c0101468400280e494039100c816410078a864600807031030340041080500040407540c01d90104d42d000080041d05945040c2c1c2c41031448030300d02d42e12364440c01d24801007040d9606500150300c074500c00c0e42e40303465810810005540c01c0c0a101a10759 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 616963974 1250 616962724 616962739
    0x10606020d1d01030e03070c0305060603240105040504150507050a080f1005211c02160803030103110d150608100c0e1e120a030806011d10020c0612010314010b 70
    0x4070b80758030a4000c0d0320341c44c0041069910348105960b0700c600708013030b6074000c80c4c03190026800c1120515003481740001140300524207000e072403210440c00711850710500805100d581e648001c1014007034000200d010070180c88104000c00d042c0340c0300240142e003016980a0000742e0700390000c0d001e0b14071010146d02803c03405002e11701e81e030704010410000701c03520b0310300c1c100718401e06100c0700c0451001c002450012040020b034030488004208020b0809803a075040300c5421008003c00c120000380082100e0440e500003003400d070302c0384100c00000c1110f85a004094001c0d00f5150710407905070004c0d84840c003200c10303c2e81100c000c40c1c0b40c80a540e003900c2e000ba462070081100b0003075000060a14081c0c1003e0702d021030b820a840c202e400c00014500140c440400905580120410010103400400f09070b0404002d0030115500015a48028560540408068080c008141c81c0705441802005031002d8460002e08507925800d600281e000000d009100c161504401c40d441c8800403e01032090310407000c800307007500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 616965224 1250 616963974 616964027
    0x150d02010c0b061504120605070e031c0309060f021c15060809031e0a080601230c1507030c18060e0613090c0903030f11030a030c1202070302010606020d 67
    0x12400b6800c020f140036004400004640c03000c00001c0020000381c00d50074000c0b0710500302c40c01c201049030320003407040052040105611080c1d6a0000e0341500d00c0f4100700d1200d80740703400c03850214007a11601400400703035401c0c409000500701068000e000300940f01320200c88000c0d070405040c0151050b4110555401c58024014400cec24810155154403590b0681141d15042d03693310400c54400d203032801100002000301309104420b07030115110303400000920704203440400030014400c403481c2000e08080460f03400143d00100800610940f8014000032a102220781b0301004041c0c09001840c02c2100010404031020680e500044860001d0b26901e545280d0300c002c131a001d00c03040d0f60003804600800c02c2c0421340055401068000c40003840499559240400d06d54603015041d00c0d07200044105015004041c454a1107000003900e81007400c614022441c80a0a402510b4140003680c1d820419030001805000741501500810204c071050b9085400b0496500f204892847c0c201d6114007502c591314020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 616966474 1250 616965224 616965233
    0xf0c0c02010e100806060f04050a03060c12092415170114010b040510020304031e14031608090f030715080106050c030f0304060204120b0a061706040221060c03150d02010c 75
    0x50542c80340341e500e4480c40c1640718000203825214643c41140d50300c0d110504c00307685a03402007803b161103114541c10702c40300700381e990381144888400c0454041415044c00d40ca404100d1034110181c003d036030003040101a911010a02514080c44408218546c00c00081c100b0160b90101d00c141250350001c44c90f41444c1c1407004211a200d11415003004610081c03002002203059014000c0d86040026494000f1040c1481c01e045030320410760101c48a90400e003c400c2c00c0005011024001c6d9901003074650383c588102000800700300054000541600c100d041c08201d101840441d00c410075059100e511642e03980303010440c2c0f24031541d014220260014080340da00841074038099a0420711607100541080c2e203810103c595035500b5401510b01a10041c00d0084402180c0f15801c007400d0001001e50f0820b5441880c5a655440503100900039003181500c1c800700500070300300c0066007809506941e648d0401c5003607140190015118107560500c40e101507071082c5020307080341d000581d040e164036400c41c5903501d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 616967724 1250 616966474 616966477
    0x30f010302040b0d200d300903120804080c07060203120a0e0304090f140c0d1a220f020c1e07050d0b1807080d14040311060703030f0c0c02010e10080606 67
    0x2c0d002800c0c0ca000c034002500b09501d80c581c242c81f94240d120720303450303144203118000001c1120701d05008a194050000c1108100c600c644c0c4d290340d041007c1251281d00e000f803402d215160341c4203020702490002060841d4044001c00d69000360342c442c2c2a09845400d003080413103020802144240d401003204109500082d008224074004407200001d081c144000040042c0d1811142c100c07030700c40000f41c004101c0d1298480d0303a03000105c1e4060725007003001100200303c1d100c400645141d59003104200b45141000b40d600000603980844100b59128070080310a190b440302d0b041c1110f0004003480f4040c00b8540000640241120b0001b400841905020744488403400c0c000382003a06a210f442c044541c01070000c0040324010080c0c440108881c122004004040541c080e142c03100c00c0208100130004a10032801d01070005c04202c0b8540d503680e1840c58198000c001030327004029220f08101021b50f4098006500605e118002c1e200c4030340328202801045609241e00b03055402065240000c1031050070300c0b50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 616968974 1250 616967724 616967783
    0x90702100912081005010914060904060e060a140d0609050f06180c06040b0d0b0105041d040c09020a080708150301060f24050d0216020402030f010302040b0d 69
    0x55035056115006500c040c0c1d8900d840580d424410318a210080641c0b002c520f9a000740210705100701c6a0a0a000070804815481201c07a071010314102c0d41c0690f510141202e040040c0203100b0020380d6070f513184801b01011b0480b140341c4207041440002881c460441d05000c044d010040c480c0014404a0b41c1c1c52000340b41d0001d0030b50341031041880c14585054200f0507640250352040000e481a90200200c034075054074048a0f0b4050034040c8020400851000709840c008440480d000c41c40c1c60502d401200c050095134800c0340000d442002e080b02411032803450602440c0204100b150040e200ea82101c16480f800300b04800003460000000c11040c4194455600020060140818403048070002070075610707070f07030000031001500c0d030010000d0402e65080442200080a0b8599001106001c00703800350003110403103100c690300041d845060202e03000d240d840241d0b000f03000b19120700b0310b800d0b618604042408100d0140f45400c1071540b07545000d45d001d142c09544402c0d001c04444c0803003000c0c102da20800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 616970224 1250 616968974 616968977
    0x1b0c03010c26192c0c0609120c030a061a040b0d060902150f03150a180507032309010b0f03030406030e15181c080c070f120906090e090604020907 64
    0x348003810040f500c0c3c02400030b2035070002e6140e0304036086800b400c9a8180c8542c5005115840304960742143d4466600b611595281100c0d00b60b00785c00000d0000781445034041050b40e05000d411003140800c00d0039484102500c400075004035080c028202444101d0b0b1000b007010b9800104841c40034005000d940214280e2407001e40364407045803000804000d00e0300003120031000e41c4004010800e41c101c4000e4100e4084004443d8000340c030b0700d00094680a040c44000d081402900c138000039100d207011303401c40140070890340035003025442c1880c40901c10382804e03240c451965090251800b00d030301d44580048000100100030710300d8549414400e03802880000311074855401803140f801c044002491185104200295070130081e80300e4102c006040498890700c1c3e00100e500380200e1210203600021640d0f0200f4140621030340c604440c20070001642d0100c90040c042403680140c0c2e07040c0ba80c404a507400700e46064603030450b40c03902c1c1ca00e50b048081e401c607204c0e12541d0107000010050300c5c1808007075030046210f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 616971474 1250 616970224 616970251
    0xd050d0e0a1709090606210a3902070506091c0f0c05090c0310090e0a0f110111010e190f1a220302060415021b0c03010c26 54
    0xb079540ca81c01011802404071500c0b404580403806081491045034040e60841c0d2580c0b6082e4400c502110350a2209215074403440800f00103100d140c0c1c242d100320100078501100758203018049884076605541094a00400c04441d440d01e442c440c00011000150b980c001d0001c0e05000074501400400c90003505200d40e500c1d054443c1002003112546507640d490f000f0011149503d042c00140002c90030041c00c03200da1540108200090340340100c00c00340a54500d04404200902400c980501e4010b80d07070300107000e20007004200020465a200100b41c0d019081e00c480f900080d099070402d088580038100c024503904020b12100d404201c800c1555811071040e030307103085141c83d0350f10740f41c3d2950095400d00380151441e0040c022490039565425050200c1661491002081a90001d44548002d00000c082642c64109580a008650140c2d00380c80c0036140d8420100075464941680e4040d40200b55000b946840e210b4400d1610882d155480202030001074914052100b5401306c401e0001072031401b00001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 616972724 1250 616971474 616971493
    0x409060b0a031d1e070b16060b01050720010905040f0c02010e0c0121021b0a1106030402030c010c06180606031a01150c02060d02160b090304210c090504050303090d020d050d0e 77
    0x50300f0003600c104c00c442507c040361021240b401800311002d41c40910305012050120030b0001360141c0c209002480250300781000e1241c40001a04c5801507038010b180e100b410030032141083c0006a0104903605503540c020b00856490703101103600c4084455155002070304d449141141a800720f2103000e640d94401000518000b4000040003040403c0c04a208068202200b40401d00c001411100c4401e00100d40c460b29504103640029600c02d8090386550500c4a400035501c1804865071003080411004020103031801050301d032070402048140012603e4220b1500d808440c0210340e080303641600e00380c1d0218554500000c1098a45141802d42207a02c00802c000103d244a41400075100c50681c02031036841c01625807401040100e001803840d1102c1c0d000340020002d20400f0150001c51100549449207038546074148400c4070b4041d03801050320f85082c4070900c0104039000000718440c004103020b59610480b4581d00b00d880b41c50219040d00040d5040c0415020081294043c1d83c0c0701200004940a444 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 616973974 1250 616972724 616972739
    0x2101d04023001090c02030a2007030602210f060d02010c111302090f1504090f09050115030b0705040e0412050c0105070807170903030a0b060409060b0a031d1e07 71
    0x42602c10404140c0c1c00d0b480040080c121503020b280c40003102c50010b942064032035000180100f6259282002541c0d501507604074250080c800d01c009150043c1065559005810203040741e41540e06003203158074060b07400650072a80d10314001d402004010b0103c2c41d5810745030011100d1034400c1809a42c210754007034100b00c00e9070311903024884080e4640c03800358458101400b0060340c41005050389005042003e5000d441141c070408840c241c3d450a000060000d50981346c820050102d41030080c0705600e0b207074010b038205800c08500821a0700c5500301480c00d50380c1e0707801103c1030301131407040c20020190800807400003640f214550714481240e1030302c0c43c00c2036407044015080d2603040e40c0340c4000c03400c804240440349a10001d02c0c900352440260f44445420407901c1c586d907a2000408041c0c40b40d0351406412100c2e82d0f041d08940c004c10100310244660381e210003e41c0140e501001507100401d15052801c0c0500d40300190005140c0d2a003406008100d04000c0c55241840280e0f01000085c080c0b1030010481c003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 616975224 1250 616973974 616974037
    0x207150f0605010e030a02010207030611070206070609170f03010e1305061e0703060b030f060604080d0512010914070c021f0504050405100e04110d0206030a0902101d0402 75
    0x80103103180810158505400506903403060710429000340c01c41381310400543d80000eaa502282d510140c0014143c8007001407804501a20b0070003580410f0000303030300c0c052000907040038003024060703079078480c010001400000f50b81c0700d071901200310000e06200401561822040d1300741c0c060520415148104031035900c00f0704010084615034000c101c80d004480d84400051348a5a2000c00350170100803050402e40c0b40001c9000040054040e8004500040d160703840d0241518010b14800081394884003070180060529084501c03058041c1d21841c1c00091212114002e0f01100138401d426440f00383c80d2800200e540000b002026038112440e41283c244541c41142d00c00800c18840c0c0d03030551202d0600b41000700380d442c00b61001014090b801c5d03040c428041d940e89910341140e031000c0e144d10070241d000d0102380c84526402c006540301c2804010401c207440150441d0380e44078421034501041040440081d1814245200039950a40c0070110524190506a0007007421030a00d40012292004000450603103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 616976474 1250 616975224 616975241
    0xf0503160807060b04021c11040509240303090904060209010903170c0f010e120d0e03190219030f050d02250311010501030f03050f0d09121701030f06020715 69
    0x740c1c031000944009100441c850b107200c0e014200c60951900003034031140c50020455040c0b2401032076407031100a00d03058411048600500f00038124044515105212a40301e0008510010000c240400819814031700402100c050b020010403070441500d858840c0002900000203281c1408a03040c80130000c18100114810004003100c481c030381e1452001e9007181404041240800b050b81003c40c24543c41001240419001c0400c40c6d4980d110305a070529180a050014034030540e0303000001e06480c0e07504c60512103d1102c081c90702140c0302240b00d0790b4500c1092102901c00340016035004480c4d0b40701845000100210040c2d5a0013608110b00c24540418084060485000012040102030304141c0c00004505070394809070000c12440d8550b45a502c8060500b000c01810400c002404200e10000c05060f43d5800703d4120040007040f01a2900c084003440c0710f250303103000c1294000140540e8110004040c140c81d441440a1420038240c1e42c2c0401940150310304580c10340440340680070301071051188505 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 616977724 1250 616976474 616976483
    0x1b050a060e070b1303241515020d090e0703090639080604050403051210051e010e0402090d0203031309050a0506220605030d080f010608040f0f050316 66
    0x5141603803070541807510145900404103030700d0500120306108540c482002c100c80e04010580e9440c0410040a200290b0343c0441c500050714007903030940c0d89515600e0b120240c0c1c1c0714035860103041c40c080f4801d980c0c4094400c241c20002e071100c071003801840a40f0142e140c201c012800c1c085822081c541d01e607402d5030310b034506140701d0811848000e0f42040f6a881030729207082c0124600903207009003400007030a5000040146014688490100c0d040500c034008070790803050545146010760401c80e440c41d603550701c13038801d040c840c402c1004211000e00c03a015682c014030805031181c50080b24140e0902010350400c6850f15800a10f5254400160300c0510082c400c181c4040303880304429003000e540604840003e0520314540341350800300301c0551106074004901c02011035580304141401c00d001c602414683c0c205070b4050203403981021103143c200d07400c1070141310b1100c0f803008140e0700d03980100c400340000c4030064000b0b05502c5840e07001c44c0d40440d500300110f02502c160392400d428082d444508bd100d1220489 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 616978974 1250 616977724 616977731
    0x302100e030909060132091c0210030e0a0308060607210207080c010818070306060801020c06090f15041106041205010f0902010509120c041b08070c0c061b050a06 71
    0x140c19250842c0e001c2ea001c5030900300f1518403002041607044092104d00c07040f611b0b8179141c2c00c09980031485025506124002009104200b94550004900400c212000c07030181c000c041051044500902603403001e0441e40009007070303040003071300d00710342c2408080c20341d6805c0b00003048504089a8030700d03403901d98210b5400c0030b400c0000900500030303c0c0050942c801c1401350800d420282c09a81d102d111282c0207000284411410b5580c58101ca0130304856a10061003d860180000758842040d00617101d42d0229009a400760ba03070f00c03030103583c4940c81542d1910094000c04505207082110703121040d046800b03100960b4180202201054965201e500521042800342e0001000c118003401984c03903421440900b4000e4a600d540040c110f80241ea903500e11503030040f4025003002e481000316460042000b002071000016101c440110668000308a00000782c002002503502c2c0d000d004203102c401d41c01075048001c207240c524216030002e01d080127280d11301c1520780201c001c0358080014a21480c065003000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 616980224 1250 616978974 616978987
    0x13150c0207082407050904140a061a030f0c0c070305150a06140102070b090303161401051003030e040203060406120615080a110904020d0f05030c07120b130302100e03 73
    0x2490420030f400030005020714200311000040542c5802ca40200c030703500703025848980440c00038000e0411402034080c40d226031001c000c240202a0440d01c00c98128240300301e00c507801114201028801140c60285000c50080403403201c4440b03c005200601126064074030390354403940d840f400d2001c030345600c1e540141c1040901c21650b0440c45801c1c020301c40d1054907140040b040001035290b0015209a48485102003121820394a0602c22165140c620b603605403601003840c038004030302086585107610380d0f40c0785c82c002494a854040078103044c0c80d00341d204c0300c2c0500001d01c01c10000e50310040045401545901c03000078840c0e0003a00e2000300745d116403404a10314101075031190040703195600600b0315a00001c074000c082010030300d00000c81401521505029a030ba40089412102d0000c0003d0440213000c2c2c1100c180407001c400342c03018100c12400d48060350398450070718495008022010700709031361540c0440c00411140d840744904600c0383c0191a11140a140c6100440f40298801d510303580001460f07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 616981474 1250 616980224 616980239
    0x1308030f0c10020909040f02031c08040c050d030801030f06020706091110020c0a050d080405031c03140f0a1a0418020a0b07080304080a0507060c0f170f13150c0207 72
    0x1540140b44050344214200510b41c8009200904040c10142440000001c044203545062045819103010302d01d602604184ea401e001b41000e030300310340c00d4409030126100401d072850070030312003801142c040e640c50b900341c0d083d0f44400c1c0b0100b0824808855241d400c0152800180c024003403071043e9400382c45140e038506000c030b040c05001d00e0900c951504540260202c42015921000c82e201968070a03a04c41d054100c843c80d140d0014070864100c0380e41841b0b81000c48140c012400c40e800410511136406005014520710201c5151400350b620a00001d084800155240840e0b44900455001c024a01c484840c40c0e201150444001030080c200b94030b0300d07640583c15802c0008840e8002c04202019038503040b00d6071100245800090030040c9001000101e1008035480b60059841c0780b03030021410017115500400182c40f520640d5603450129070480600180701d105d20180310320815107200801180c0d0307144401071411000d1507074100c48101200e02c6410042c45c8620900e0712490350fa0700140021400c10741c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 616982724 1250 616981474 616981483
    0x108151818010902091503101103010302010906020d05030a093215040b2d0c120603160e0c0706050103200907020c040c090801050901050109060506041a1308030f0c 72
    0x407245983c1001d0703881c001a1120103c8035840750f00158400e803060107800000381000515003521a83d1341c00c29031034a02100308000218103d91003600c4052a02d83d5800c8141d03210240f508246020400600018290b0700c0280c020280861069224506140307140d048000c00424519404041250300f80c80d11400080800c100c002c0c07070410f485170f03a0301440d02e603480200e03000d0f0090502e541700d98540c0411401c145100407404440000308a208200c1c41c003200416183d4104880b0a0101880440814100e05011a14042c500c025a0003480410b0510701082c0301000085c0c400c4040d030000300900710128800e4400c50340a0342c4145425103a0319500d5a81507641c11880b4055882a2819000d105090350001080b99501c0c0081c1c4010071704c800d11760000c0e551400d141d80090500c0d42840100300c1008019840700b81031722014641081129150000e001d4580110b006039031480100204032280114030700301030020700340804e00201314192911211800c1d600210f86a020041004c100120720100901 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 616983974 1250 616982724 616982761
    0x6131103130c06051312020303070f060c1206180c02030c01061205010b030d170604060b0d1b0e0102341502010b011b03031a032505030a0c0501081518 66
    0x1134918103240380b904403024500054400c004803924500d04d003400b152400e0040c0c07145540c015802a445c0450741c100400030709201d40c00d80d00040c040801c01c294043c7c003031203204191403110701d2100101204071048001424002c203003800390f00c03007448200d000000900039600a4a00c9500d2900301030100d250080c00c1d07851b18041c0a00c25003015500151481d8070483e5811150741d034143c6044146c80c2c4070013140051483e600400d200c2000062100241402900110b010700320300c801c2030300c4111319140111b03003210884200300e00513040202000d94415501c0c06842d04d21241400d50204600106415a80c03c9140c4c1e00c80d0340c98200445412034040e80a11070980000b50a00305042c203410881400e03515030040e10300080c241540c43c00c10327400d041d00329850000d0003c1c1c042c045444500b042c04801d0890800103651003120701c0422004103a60602003140300119910042078085182000700555510100800507500402c800440100903961419841082e15041d40000b610b410000d140280724190351 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 616985224 1250 616983974 616983977
    0x3023103051507140a090b040b1c0624031d1e01090f02040203070c06060f05040f150e070203070b0c090f1f14091306051c050606131103130c06 63
    0x114100141642c00c2840350f03101d00c8200c5803041d03a4041441d03090720450055081f1806503103012a011907404404002048a1424529820b07c0c050402400009a4141d4098180703420316000010002c148460b407041030040103810046001d15202441100c04500c0e070444400c6a440050f180303811080c3d000520070800b02c800024014281030b6211502d00d0440024001c0c01154002f00240c103c2c0d1180c0c1e034100806910603410700020780c0ea21161b00102d1403d000ba60306c228980b100300c0700c528015105a040140000e0070402130b440c076080352070a8040b40100504290300041102400142c40c0094551107030088004c2981c0340c100d244207010703042e03144030380302d50090203a103451a04000b2003001c4a480c500e5989880ba0f802c1d40c4540e121203060003890320700e0741c00c0260980f0b480c20343d030340301d8008205a40003514401501d00c50344c442071528030701140c0d0103001a0005c80c0032411505213034031000c0020b0840400824616100d141254240d802207038000219041c04058400700f0010804240041400b07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 616986474 1250 616985224 616985263
    0x109060813020603191a03060915061905060706060306061502101104051806030c01050f0f031e0405010c1e05040506091206010e01030c080111030105010302310305 72
    0x8441d220103041e0040041c2c4a0040030001400e81d48524032005c844881403d0203000080c42c0103030a07170510f038803402010310901500000500ca94000a0302c941d002c40300c00c001303003081d07180c0009010410303402c400c400c0950a9905004140e07521024002c0c9016880b03120300084c89071650074070b401145c40c16080070090000b40c1c03c0c0e034101c02d83d000420451f0004110000947c05043ca0500c000340d20441d8412034000d031400c104401c20040d8401e0a078403d1406505480354541ea98004440e81e2089015108808105010b215004071104002c1e5a10200d2016035280501c140704510300300c1c29045074100c525a464140d0076800d16440101904020885550846022180702c0c9c060818080d5004807402110302240c025182d54030140c582e100e000400d810388d0590b586400c04218030300001d0000fa2241c140308000041d01900501c500d0310a0a40400a58190790070701c00118060361000e032025401b005e1666441001ca803580104002100c4090809001e15195181aa06002c17840c1c4405015000313 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 616987724 1250 616986474 616986481
    0x4120b070906080705090d0b16090e06010519020c132c03030105040e0c04020403060b03120f030703050601030e0f070510020c0906060c070b031311060c0c130b120a0201090608 77
    0x104400c0d030f95004080ca080c1a61540d1400000c5511014200d07009080d400740802480400044001007018000c100d40c1c55000d40394654082010100096424a0009804000c0250841c62560032200d2284d024810b0303030403986243c030021f106208551300300e0f07a02c11f9890400b05001c4c040541034017155a28448501005c0812079031981d2a4001486400c0c0104c6c4c980c1e11b010314030881484044c3c40700340001c00c210b40319501e03410032100a15401202038002d03c01c010800082c803201c4d9050351040064150306502e580d072004000c50217000c010701040e0606840f01d104400700081030103204168400341c0d0040c19854504810440351003c0126164295080940c1030503c68880e000030981c004015581103035945060100c181c0b500b8801d070302c9488040310120a0040034013108003480c620601803029401102140010030a280c4030326000d40d03000b40d00c030702a0040c1905200d102080c1c050107240c40001d0000001010585180c09408141e04641051000d4021036030090301c1d11018008034a0034403d80d14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 616988974 1250 616987724 616987727
    0x501151b02090c09060702060d0b0a06090e0106051b03210703090503040b03040f051e07051e21010905031e0a020d080c070c03030503040b011401020309010c060902040204120b070906 80
    0x100c01034084030f00144002401e46035a1100c400703c400d01580644950303034400d4401c1240c0c006103440181c0741d2180c0c12111002907668426000042500c816100c0d01829034079040060b1919800b0f85250f00e45920400c0c010240d40e002031014000082e04900101c018103032070480462040070007082c40c401d0511309190400419800030075101038aa03c0700b42c1d26900d455509100e68070100f4908004d10900c03990400c28841401e01c80d40194010700e000c02c603018152617508000707808004241100100c80c0d903105007082403a00000711221341242e59203011111011a20560a580c01c4c80400d440079800007501c04d82155144100d021650145000c00b420907032003500080d11104282c442c0020030081c40c0c00310306081015411560302c02d500141c1c0301c035079076640d14028150f0b4108807010b031480080d0340d0000841098080d0b61520100d0143d0185142c0b014001c010340751500d10310030603101240d8440000c0d0041e1910310003072014109e14124003142110518050341c412a00800d0341c0c04000d11200304110700c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 616990224 1250 616988974 616988989
    0xd08030a0f0c170402212a132a020d080a09020a0302011d100305070f080106090b0a18080c1906020a0807050a0b0403050d0f0603020d080c100501151b02 67
    0x44500e400d0300340c030791102c1c00002c0b1b8604100511611000440d1102d56200c540003800d0352848421442182032041764201400400c20054045500214800a00f90740014561300c150902d032101e2401000da423481c0c80180140c00b0000e0328600140c1c7c0036400d180d1040e50800c44403944031402c5401440110616404075030529078511009052246540c9501d01c1c070b180d1141c0985501d0345c090101c080e0700d080444000d0192001340d6906001c18101d003514408648a07030341c091b0681c2c080d5110902081e18045010300035a000b84640c0381000080654400d440059030041030080424500600c0312134100810040c0c6103000e40262210320400300e8007001b201ea004200018159040fa21103a00ca4040c1cac10061b0803c04489401411058250108010113400c940030741098100700d1000c000a100754401401213404502001c1d50142e4855501400140814000e0807030700000030581d0000e40344200101e05498080c3c10103203005840d10b00090500c4d0f03120745424007114149520140a04c0c031900410080c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 616991474 1250 616990224 616990247
    0xd0210060f1a0307090b0d020702281a09040510060e0315070c020f032e02040b070b09011413153e13031e0b0a050a0b0d08030a0f0c 58
    0xc03180044005010a8010b11809000344190786c112551941c081e0060402940b00c0d11089200b8a8034000d0a411028661804603103081e4001e02110b04605241e1504030203600614601e019110400001240c1e84842c05011700418200820614060400034080c0034001d811042c05c1c00b980c040301006450410040b8040d07002030490400010305495400480c40304139080160070780512901c1060400300c80c603000880ea02c95102c1505072811041d0000c04d070240e202da48544100c48000b40030000105403034808054100e00c1074000010144c1480d14280e0386044111000100c400f5030204400c1800010310f041840352071030100c20420f081d40c070900e040008007145034944c54031031030118500c0110004003488420310032020321b031626150030000f50b24220790980011180c408100c05000303511205203003140020740e4814106151aaa01304001004000050028600940b100000e40e1329807074000c0c0094400d4043c24031a5035a00c0c01c1307248801a03a010025001595103400140c11607942e210340c40418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 616992724 1250 616991474 616991519
    0xa05091c0f0507080f1309291c030207030b2a2b060812030c0304030c11040614010f020606010210020703030f06080109120201020921010e0d0210060f 66
    0xc0312111408110b480e40215440100300000c0010390000c9404008068070002d60420401000b180d1117200345c1d0152801c3c0406110300d1400680b4081d5110300000d80c040b0b080101070010081e41d65512920112000e03681816000758003d10402d10500c09040f68041e0301c000d50181c484950300454a01100c00304240c60b1003941c001c408500d0243c12661582c41d030030740080c0e2254050000032254074071002000d1912a07040d25210f01c0300064505030304001664454045158424291760319628150340c016074040040ba503407a4401d20540240ea600c3c1718002c0508001c2c6400c85001c11280b0015003200011180780301994043e02c1004400d80e80003649902030701440c5400b5032644018a8150007401e807414141d9600c81c1040804074400302c2c1540040c403540e01403c1241c1c034807a1580c905908038825480d40d00c0e044000130000c140b02d0346c00c40c1410070052000c0800040c824492013225804c01400040b0400141c0050840c0c03900031045001d0300c000303001c00c9062042e01500d007414968050303000780418413 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 616993974 1250 616992724 616992737
    0xf071a13080a030c020f01060f06020c030625050f04030c0f08190204022505060604060e0c0a1808100b030c060f03060906010903290c03070203071115040306050a05091c 74
    0x219944244014001d206c159002404000d8030303010805560041d078052000188188204941a0300c0c000606600801c402e000f50550445600c01a4050f94102040740090040030480e007050810b00400510046004d5000c2d1142d060404d00d422603d181c0c1580311500c281d000d400a000141c1d01c803210200c25940c126001a5101c0c4519106081181c0303449005114000f5408450f05020006c01e446121b00d01c1203804106c115210301d542d0031901420b845840103c00c040c4200b0004038050238a03441d10b000780d442001941c0b99224000b5141012140003003402540303504c28000181010041081c280310300322449410b0101e480090049800000c10702c80c0b0a40f05a808503400e0390003451481c01075034002c880b541c54401803080b4100301d0a00c4401302808800d44074005400303d00701034180ca006071880d902452900d50320340c43d40d482d02d105032030b5000d0b40481c5882080c62040070080c020001180305401c007098500c0c010b0321a500b150340040001c0d555170842960074080214402c0940b44003c0c1034140070303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 616995224 1250 616993974 616993991
    0x30306050f04060513091e0309080c031507080a090b161403010b070f08190c030207050d0b06010804031205070f030605090402060f0c01021e04050f010f091a0f071a13080a03 76
    0xb01104802c80307140c9041c0c40a2414103500703041d07102750303206e007030301e03003980888441d20318420070305589108040c034001b0441e00c2c050101c1c402d140b1440c26076030000101c0002041c80130303a41d21400103030302c0e0550382900030040c80403500309481e4015603803108640c0c04aa105e81150303d0405e41e601144035404004204010b1040c8001c1004a4481a940c0044600324071f466089035054001d0200040050300b6001b51040c5100086c1a10f010880a003109500c100325202945401005407901c28015204800303010101c40004020000c1c0d01c84c2d517211310055561041d444803080c4001e0100c941c150861030080c0f18403410000507884603000c403403402c98400c00300e69981d41507109450090183d441503d900c0340c140140b20800440170000390003503917012956003c0c141c0c003040c0151205a10040400040380040d40c2c200400c850031040c1c0b800d11140c0f0f0190a15188c004114240d180e40448030894008082130460030240c154140f0090b40008103440c01c00c002d02490b1203030030982c0695101c01c406c2540b2086003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 616996474 1250 616995224 616995233
    0xf0307030503220902040306140c0c331f17070b0a1101061d010902180108070c0512040f23270f0603010c0e010504031e020a03030306050f0406051309 66
    0x1040004d0001220440d100e90312460514040d0a101500b166402a160040ba800c02d502104440810910b10002c00c0c01c851203c040e006001000900c1c0000c0c0c070361002c40e031440102024115841410207800c00b000c19084003d0701038154105401006032000c01000f00d601c03daa0000e078080030748648400c00c030f0325040082000c4900d4001511100c00c154200180019105804102141d140d0700f040f510461a0781c0b1041e40300224040c0400b1501c100000c4074103007010754002c1c502d03a5004140c0d807030703e2904c41c0c0304d6485040c9000341c400403681c100321002804008418240b0b0f80900035000400c1001c14880c2441c0d5080c5101c0c425400082c81090511184481c140b000c01014000104414000e1130518051050040c510003c90b81207011f94201420204502d2081c1100d49a1240c16100d80e8205411600c1b041d1542c03141d807029540314001c4080100150351031a18980086100f03a40c0420740d03038242418000c88080444409000d2802c040003070040340c0d140017014a001e20307444400100d51016080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 616997724 1250 616996474 616996537
    0x90408031024020c060306090601080a060f06050706060e01080307060f0b040903022103070909020d020c01020c1e0a170d06150201060e011e030f050a1a0103020f0307030503 76
    0x1880740b4250b80840301c1d0700c280b00302070010451001d07a02500d26000c0241c0038801d1900c4100d0700141e10014000003d412580109007013078002140079000a10305440d072a41000c6a0410f800c07080c0451780200b2501d08201c441d004010282c6041422640341b545008000c40e0b0324040d641006000a4841141d040c0c820226403040d0208800100140702036a12814040d40702c10030600301c0442035114003c01d4130500c8050080300d004114566402d0b0f6800c0c0740c03810510094201c0e483c0300b002c594003000849500c00090014000c90880c200240000f4034400003075402c004035892840496411070320004010a8000c0800402d82c6101c3c8409642c481a03500c2010040285401c10705000901c0780000c0411035055200d01c083e07070120351007100d0690b00c8400c580c1100d4501501da01003410605030901c005541c4050259015200e0811110071030026a201002501103003180e2008944480041007917241c00502e00c081a0780940103040468110f0300c9064a920803031483c40d01c0103a82c07000964025407e4034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 616998974 1250 616997724 616997729
    0x30512071218060c0215010603091e14100902060304020108062103040603060e1909020a030b13110603070906080c0903060a060806090712110d0501180b0c04050904080310 75
    0x340c01c005101c00c1840780c002e110440602a6649450404035035040d900005010600310120b032140c0381e00340e180c40011406044d21403800c61350400b0360043e41c2c5241a01d85014104184a040c20344640e00d4501503d624050013116484216800c00c204140903880300c074101d90301720b902841e00300c18941e2440c011501e82c2e540d10f40d44003200e80780d401d44c070340c14444084064015502c039540c040c0035070f84c0e60740312080c061035094401018291202481e410007018660000d072040d0f202034508401981d8035225503820100071500719082c2c0c007000382d0759030400031480d5800c41c0944085a81c42d0079410182c40092040b01c007401a03038280301a05021070020314902c400d0390f80140b07008044400d04d01d0400d00300005045140b00782c0b201c0344078050100e10444400b1403c2010f4485251001046111940700c08803660b103882c3d0041d80000b601012500443c40a020703030141030202c0307880580c040303046d86420350341d403c0000c0000824072004d102c140050340e6420f000301d0704942c10408141e01e83c3c8891500e2120000d0b1907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 617000224 1250 616998974 616999007
    0xc03030c020f100c050c1005030f0a060f06050409050709060507141207060204050a05180c0d06090624080c07020d020f04050403020706080c03101e0305061906080a03051207 76
    0x5503080004164004413446030548110709442841c00100240603c030715101e09a080810800c1c400542441040759170541c0c0b08a030050046411541d81441e2003040340282c00c02000500c00250500103c0b01501035070360010700f82e21f40f05220750f2800c0e0004159000347c91000b001030620b11880001e070795042091070007010242c0e291a903244030034a0210000d521620615010710160040050381c0e01e45001c1034001810010103603d03031507442075440c140d01c0c0c0c00b410800d144651b4641000c11a00400c0c4200000f403e120280307001a030040354452046d81d0040311130982009056000c003ca41c90803841511443d6605907000d000847c60307840003803803011001101c41c1d0080d140030100000d259001a4070411180725854521031515107039400e103490320003210400c0040d000400700f044442c8085c010076082101c500d5002603807030380303a545076030512406543c0b2180b80c000070802091010300034850240204a00e80040510f001c569030041c0c5540650f8001a00030040c0e180059103040c006c140003804910103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 617001474 1250 617000224 617000239
    0x207060e062d01060c0b0907030f030906030b1219031b110a0e06010507020d1b06020c010e0f03190f0f06050117162711091c0c03030c020f 61
    0x10b66405108801e0454007941001c0d6111032030390005204031205059a40907170320440c0c3c01c5665155001c0060019002c440310f031041020020101e01e42014804115209a0711560b039149418002410f032004950780a1040c200a900420b0000000401c4481c101a000710031000040d181000d9030b0400030b5000d0000074009100c601410485440c89021900d00100e070743c0d100751900c5000e8202800b1080700c09030302080c400c11101c0d000d890041c1554244900c50080454a0408401c1131a0160926400b07100541c0c40091002d0341c568018003c440c161a083d5000d0703c100c124a0002a075810a41a1200154014400c4401440500907036090324a410204171000c1d20b00924120005003424400d840031008000c040c11060741c008a43d81c100b0321042103012800c0c508002c082d06540c44046001c0454100c45c8400007055a030302d00949141c1c8620000d165116000c2c2e5083c80940b401600c0d00d004948800060603000464120010066a030140ba05120f031100a1005c204500b03051607299034007102c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 617002724 1250 617001474 617001481
    0xb01120c0f110717010e06010602070f050405041712060307080c090a020a030617060928170c10060f050604030510020c03120f1801020309100b0301060306051e01060e0a090207060e06 80
    0x41504804e0b41b001c2c0c500c1c102c0d03c0aa81c1c4d2002207071507800c40e02400c2508820b40d00100424a459000b0940080c062510700c0d00c261007044120843d0381c00300180d1100c80700d800041121925041c00703240c2c010030800c0081c0642d1b9000100146401000904c00e490395980424002e40c002d00c254450800b03056900134494002c00070004055540000711409005842260144101000f440091075002031000029264040b42d5a4550b0070b202e920500d001340004051001e200242d100b00302e0b010ba041d01012000130014103204031f03920b2104243e00300a0007039104000400004500242c240c0b50040c40a10051b1650003107a203550a6100c1e81ca4040c00e0382c3d04010030300400c0821b01d29941d01514181c001010400074064400c1d090340030440e0402015003208000194181454000c104400780040002076229107a58560341200d0050b42c001d000c4100f03480700c180300c803005c0480180c0034000905205900c0c1030110b0000e04411080d0050030000c40d0049902d00030080603400100f4041c003410141d600038503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 617003974 1250 617002724 617002769
    0x10c0509210316062909060d02090a020a0318050c0910090c0503060405100609210b09150a09110111031209010e0c06030c040501080402130606030b01120c0f1107 71
    0x483d2803100351581468001304c818408001001c1c9203024100c098043c4050001400f08840380800800032600301c46007203c0440141c3c1c401c007820348141c03c0f640c00141c8071901c2c80c4004080351080000b0300d14000340307001c400e80450b01c0000e00c0c139081315044902500f035640b10486640c0c8400f26a000c0508203050485202c4010340040141d440380105441c104916501c00394880e0340980c651042e0b0010a6240100b1b001070042c82e000714406000b18913040759000c083c0d948101511808907158403141c0c1240041c8030090800e0440300da000603803000c041c09454a1506c60055642c94115100d060200c0a1032801d12128184260356024403140e803660760b03e15040b8241c83c041d00b00800300007401d004205114810303180002c180d0340114050840a41001c4c20100154340810707014005030303400302e1504000242c801c458011003000d803269a13000303c0c003140244000f4084909c1c90594400c01760070591012803065101141d002e85074014039014280c000200c60240c1021629000305c41ea9080381126014580c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 617005224 1250 617003974 617004007
    0x210a060c081515030a0617030702031519050a110a030c020708030c0c040c11060c040302040b0a0302030a030c0213110c060907150309030329040e010c05092103 70
    0x40007521881c907079a6a6003403840d5180849140d0551109030a503031000c5046400014640c01010000d000884586030340403a07041010f90200e1240075400050310b402141818400407680090b40542c510b0705040c82c03517580070500315216502e04015a82c1002582d02400c50308081d0482800e10402d90380d03400f21080060103807140b0039041004d03115115000484090000803546007090060282c00703000303046001c000180181d130780d8410030415850020218500103010150241100c540720698075440c501c148801e4a10f803c43d014400d2810310401c00158402058000c11a5072600d800e0b40c1d01441031000a110109100074840740c140740600301d03490b0020000003401e403246c1044c00c648050342c0d0b03916100eaa5141c0d6008512200000d10380d0411240d029420421030284203040c04995414441ca000c211002c0362450407280c0001c501906c4540e080078031504600800380c00007403100c049801c00c043e0907446003e04460085802c1c00e858000007c0a00c0c103501c0c07038513908060b03d68403c070500d44203901 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 617006474 1250 617005224 617005241
    0xc030d062408130f0f060606050c0105010f0b091314070c1106040302030d0807020708060f07030b030106140d0807080c0a03080f0601080a0f0f05160e150405210a06 72
    0x8909411240c01400e601804003188500f090b4094041000c0e11a40d91079201026813208030741046402d041c50000a540303009110151440d9500d10b51031700d82040300340d0b0a40c2c6040c0e0004100d125104010310100911404644aaa0040d10b0b8101d01c0408010403400078828000e0040b17410040ca030902c0034540d80565a440014010110301d098105a0f40030005030b0b00c200d21009600d0741c04180c0c080320407401600d0496006003030780191540e49541d081102d0606008135414901071681c00304208040d5058841c0c2c10110700290001c1100c9400c10050805020204e8510340c80b03082d00f814a0010456100301300c4250303681c465070840d140c034505100c050741c51282c101c080b80450f007103800043c410081015001d11440d4169940701c610303140c154240000745031400c130a40ca1207032070302030301c095042d600d000d9940521944d12840c02d0a0030b108034014514054500c815100d4100c0c0922031100c224440103440980740111660a081041c640112421100b00d048401c0c5134040e42110009108856001011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 617007724 1250 617006474 617006519
    0x106080606030c18180f0109060c120c0f030506030c04060902041409040b150a030b070f080106090e06040e0a0f030c0213091203050702071a0711090603120c030d06 72
    0x40c0803d0490810420310b4a208000b0601014040025030042c003820510174840242004c0d0703500c3c1c20107100d6690a40304034136400e4500903101c40110311400da003c521141a000001c400b0008540c403044010400d503c2c0c0000b0070100764032540452031940d400d010fa200c05203070003002001056a035488000180d0000e208071541107500c611600480c0c1490034065110b0355111a1b0b8600e04d648210a066482c004000e0741500408143c0f00840017031b031000358983c010072254031141c081e240001d800030a4004144c00039010000c00d104c04105006c00d0110030703a04218121800f08484072842e03816494103480304001b03400d410036038400606040d0850f40c000d0720380d8002c1d9103403102280c403000e85005890b65003130000d10a0079403080d4020054801c1e407100740c00c0b4080307105440b40c0680d100c5540f00c44101a080a01a154002075404100702c404041a2070a03c01030342c0700307002440c0804c0040c0c1c8031241c002c00984c88200c0081c48050600d014001c4401c1c400088004200c210386074401c9142064800707400a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 617008974 1250 617007724 617007733
    0x20c060f152202043302010b0a0515070c12060e0705011209021504061218030918140703060608060103092f0301090b040b0f09060a02090d05010608060603 68
    0x301c42440005581c0000700015041442007544000c0002940200c181c000d840755500703100c08201c0c240c11100c0d850740703080760740b042c5801880a0921084146a042c0c515015a03240402c0004d10346c0380e101d802d0b03003208c40458180752000e80319020f0482e944180c403001010b141803000045448141c80011100c1d130342c01500100701c0c0742200c15a155480c6064080d586c042003520f02c080980d40c1c400e030003c102092000d44030041d01d01d06860901041c1d0015002180840ca0a168000c03100300c41d440ba0543c00b10b08031100801003141c03070302c02801c1c018190180513800b51a4202c0030a080c8019081502a6030f500c0c00060380b00d203041031000b0018001401140002075061001c59a158480d0140c10707040d0b82c000350b881d00c41d0664410704040f0030114050031f08188181d45020700329a5020301c10350041c80d001d401d01c0209031400d490400d84992000b80030b025060205801d10a0008000403010340c409495200181e44050746800120014002d450080817903003050000302d9001d501150b910b005200960446 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 617010224 1250 617008974 617008981
    0xe0706050a02070e0c0d05040302010b04141b0a020f1b01030e01050f160e0d1511040602120d06080a0507150f171512060105010f0f0e22020c060f 64
    0x4035014410100c0e00340060703002e03036001d10041c0e04600d0700c40c1e080314000303c2091030301c88484d118030180c40048405801507595080c1508190820b800b80713405081e00340500c0b1049151401582c0e481d10241200c0350050f040204480804500030004040503103a501e003107841c03141003412503148100398400703580d002171300701041c10000d1041401242c0c040e001d4481c07082e0740303950751441c600344202c0f500f2140c0c0308004d01c8525107034880d194201840c44140c01401004200800c1550503801e5070742a9100600c040c000300010000c0550228403440c01c01e00480c0c030155103541011107103019001c2134010840381d010303200301c40301042400610102190070300940b2600b401103100099130b02c4d68554420901003030502d00001381d0182c0e5121882e074090804503070041c200340c0200106441450300e181e82c1501d50310480041c800d82da000440806001090f2030300080c044800b0030002e1000c00da00c04c03007602500713001e8003001c8164501a065004080210400c41d00c401c45135502d160b40340c0c01039410101030390414020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 617011474 1250 617010224 617010227
    0x1b01051e0a14270103270224030c0304060f061e0501020106061b14121213020a050d11100509040b062a10060909021305090c0f03031308010e0706 64
    0x26205074281440c141e14980b004100c0c0c1841c041c03d4034207a00d04143ea1440150120500e01100c1100500402205001c2c41118418445d800d1001443e04900290240490b00000b0644084960014035085180d4403a112840c241000d001e030769282d9020300e41450008030742c01c0d01262010001c48659a0f4940c481c655550040e82201d5641c080e41340011600e940e101d2200301c4c3d5850006070070307109030b180c1d00c00e030903041009506100c990000030318440400940340c8003980240082c42d8010b09034144c03040140d04150b0029040c55982e22079070303014010b00f034082020701c004160b0b0b1440911015101040744002d20b07900401a41c0241781e0395101d00c0ca0300858448030b06003030081c0d50704c030035802c40808080c9404c0300c080c81c0300c001001c0708600507201d00c0400140d030b0650740c02a0b0004080c5000003180240d541d204000c5070804143d003400c002c920700020084021000290891803030000c0d240d804281c0c18450203c1c0c03c40c0b186903051103400d1240000052000070541c00f18a01c0e8038240b00b0345854544800c0c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 617012724 1250 617011474 617011477
    0x60f16060209060d1a1f030e03190504031b05030a030c0f05010518070e01030203060a02131707170c010c06020d060e040c0603060602060c071106040504150f060e031b01051e0a14 78
    0x11030b1a103c4480748005001346d4001d90047d40054244000c40341442c3c2076407400c0c0715070f0385c034800c00e040010700c089010405c00040440d8a4140503007000c1c2501002d01f002d001c250307610940d910203010440c501c80c0d80c0040c401301e10a4018030603003081c001d12440c43c01d01400d44483c4040e84d0840c400380b03d2408e00040b03611710040c030781b410303a07034020b010f03105a423902c1c21204065006401880d41402da0340d040050440b025001c01e06140c460b11000c0c0101c1c034a801d0180b80720b10000032800020350400181c006450b030344041d89150a61f0f1120f001a1176100d1400c02d08003c6c461500304109401564007801700703011492003110300300c42041e9400c0c0000740c1c4400003262240070964111401003000d0000100007075a484144146e80400f805450170030340c1d540c3c0050151908e80080d4048010421024014185191050b8002d0202030500000340b094010200740e03900c6e0780140001c0b4030360741c1c0f40040c0a039a03c19001c8809400101e41645402904525020955800150000045440c4c560249845000c540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 617013974 1250 617012724 617012749
    0xa08060a080a080d0509030f030108010902041a01021905010608030a031407020c010507300809010605010206060109290721080c0a051b0105130b06060f16060209060d1a 74
    0xd00003404d14012000100c058080070704014954002801103046015008020714020407141002048080311070041c4012142c0e030007160b188041c005a80311206036000201e60000034500d1088541500311400c1c1035005203441d41040380203010002d8601c120700d906030450349804041c0e0f400002c0b1929140d41c240d94442681c09618003042d001d00002000c034034035030843e54940c128002102440140c8000354408410300302c07070381404034117803000b40009038400b449400d001d04020f000a00d62401c040001030039410082c1304900010580941c0c100001d00b1103600d165044007030482090710344107240b07003042c04418119140500041c80b401c2856485100c1c0182901502c200c00d0158507040b076120040f14943d01c00070408415560644502000c00000d2180c180f088540305100254012030b80390560f011030014100a02ca01000d000d564503090381602224050042040e980340045400c2c900040603000d0b007603150b54048400306082070114070f56013201c0e002c6502c0e03940400c44d40342c02d0001c0000848811 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 617015224 1250 617013974 617013983
    0x120040303110d020c1201020d020307090311010c110d0303090f0501061703030606120408091f020c03120a030b130507031b020d0e01050f04030605090c03010c090e060603060607080a08060a080a 85
    0x94480140c14200f2801c0e40300c000c46c10015141104c217184c000c003070f60320a031051000180148020001d0121440162540c54824038011402e14502d8856080001c0d942d0341c030314818007040e420300d010180698030810f4100e51000b8586214581e030f080450090845110301d2000b5802440c1044600b81c001c01101d00c5014028101802c0c401c03c2c41c035003515110000d1044424400804c1944140d960300c400103000c9aa5a84203c583c00740c0c64640242403101000d000c1e0b0190b4407120a03c0340f003000c00c03010348501c107442d450005100c900a01c001a0540b00010a180d116854241800002a0701d504104030600440c0d801001c50010314500701e95604601c02da030000a40001080c00c540c0d8440c0c0018120120080c0007503082c5612038803940700f00c0d6010342e10804242d10001c0b6002d0281028000c04e10350301d40500f81002c0c164905100107031085c41c01001171788958030020024005a8418041e00c8255800140068581d1a820000361032040d0698285111303031490320002400000000d558030003142e01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 617016474 1250 617015224 617015233
    0x4051e0a060207080f03151207050f0d0203031903090b01050d030518060415031b030b03070303030c2d0207050a08120c0109051507031a0907110120040303110d02 71
    0x40e1075110081d08102c200b260380310400c00400301c40c5000f002c080e5008034081071032154582065800c00c02090205c03020300d003043e041103404000d16626144440a5500159108495094940700103411807103140c0d20656107201c0c1144420742d0300d51581c01421210f101c1c207011a0707943d0f03c4800700712100441e0080280007030303000c20003c0070311f40708128010440174025100ca0f00b40b6031104420605410030214590010b666240443c40341203246031520441c0030a820100402914440401e8035030b00240000b50502d601c0e1100b1610251085441e8807840f540a403d1302040a840c00a0700f5044104102d00da0062062036000725851034080500b0303040321341820082c01115001071158a0a402110003030100d5580c8208460110b1810b00031075a540d442142c114141d0b01d058140a412a06420101006200c2d0070600d04c06039240c281031181c0125090902844d1010324020480c090300ca018000c03500c110510165500d2300380408090001d0300e21985034001005c01d50b148403641c4031521240000144d02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 617017724 1250 617016474 617016493
    0xe300c04093f02010c02070510090605160602030a020405180c1602150f0306010f0f08192018040b0a120f050304080304140303030709091d0a080304051e 67
    0x42c04680030710340b8894040000c44400710340040030700035042c155040c0260351a4183d580a581d8140459805840b080781c45492100c1e440a0017800e4012901408043c0300d0001400140308081c2201c48443c41c0d40000c0a550303e00d4411905006500540704a0340507141c1259001c0d1405900d020481c030810940c5221070030002d8150100d85400485801a03800c14200c0c4102419042c0d804c0082c06500c40b80d1030103d83c3c3e07040070070006003500f10002140e410001541d40d907880245e031103a05140c1040301017002c1c040381c0f01c00110340e000508884200d03083c66642058420441b10f640400782240015881315114056038000500060b91a800c0e41154421006501400301e082401c13034980c055401402c0f007400a99a55445502d150300941080c0c4490307001080400c401c14030b29100b10308901c0290080c40c00e60611303000c05000048940102003442d511a8401000c520f28648010800d010785000c90341031100354140200c90b0b50041c1c4003554140104d91500600081d90420341404100f280010b082001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 617018974 1250 617017724 617017763
    0xc050f04140f1902180906030303040f1b120b0708010f12020405071107081b1f0309081608040315060303091a12070e0915100e300c0409 60
    0x80c0300034240e40c0c05003601e03040f84010644902c094031241050548680018101030200b10b03480d000104010301c2640700300204400591295507400759240d03c00c84114800e030a000c245280c20fa020b40107450784001072108001413060300510380d400349445854481c610b90300d8403002c0400c84007a0081c035032075824845468006041c1b562080340d12000500e0111050b8100c50072880c18104680d0088481d544a03040007201004c10040c12030500104564620301c00c0c0c0c0e43d07a0f01200504182d00001e081c96600d40303102007440001d40440f5901d400401e107510280c0d04501e040c00e80740c1c0160109036000d01c0503000c1c085107040385100720000e40b601500c450340305500e0100603034155042c1681c1004500024800403404500d071200c080d00482064441c20880303502202032010842008086103c03080d0107500305e06198a51200d0455507031160f16140398440c060f540480e80ea060064903000303a4021448150b869080010395001341040d0540c00d844000c080c0c0c0003040292502201d0240c4680c00c1048544000c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 617020224 1250 617018974 617019001
    0x60e10061809060b0406020f0a020108060d0c0306110a03060807050d150207060f02281d12100903090e010e010b03060f151c050910091b030c050f0414 66
    0x8040a05600314a9846142c0030781610740980c450050501c02044c00d100e61501400138481c6251020000c0030b000246800090130300d180500310901030f8181d00d80300b9080c07110700e1804402840d00603a081c0b000820f082d540c0e58540c1d02403000500004d21f40b00d404116208040b41080032510010402d0980d600103460343c9508805615403104810750070403c1100041080c011140015451440180c1312403c1400303100509818410385d460f000b0444081d50806078103e005c020109100001001c1d40031000400b01d0048100142451460b210382820840103000c0e0b50417000c0a00c0c425610000c14a5542c0d02d44905600c0a014580e01181a0710060061603025009142d05c444020005141c00c0b07111004246c86150804502c40c20200004210050f149040000b00b040421071000b0003a5103004011726803550a001010b41045481c0c401070b5091011103900c01002c404140d600c602001e99030b00d4004c0000400b03100702da02a0500f40007008043c0741900c10900b80103086682c9520b00e603202c03000641c50 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 617021474 1250 617020224 617020247
    0xc0c0b0903071809030e0105091e01030f0e070f0e01080727140f01050607050307080a0509030d050a0f08060306060f2205040b0c1c05070903081c060e1006 68
    0x500c60142c000030080c40540701c9070380d0184140b200190240550400801c0e610014001505004080200c18680d07110382d00022915007c0c0081c0c400c41c0c064003001200609486034502d4256030070255480e622107004190001190f0a45080700003003541c1ea4464621020300744103808054128103c200605032286600c484c000e01d00c00c140380e42d641404010350b82126580100f000c40703012280100a0a20004074845000d04001c651690821100365038007903880c880c13008018030f050800320304404000d005406641d046100282560451003240e14010460b03040044110001944440da0710302c05401020700d2400b40802402800c0c0c16038990040c0440c00c80d4104085800219550141310741080007280084154840d003c04a55070405007044607a4140c0541081e15000040200b042881a21610307042c0c1c4101c0203a000c100c0c2c1d0381d651015145250b00c3e0340080c02078030000035141d0041c9061003010940306d54400d0200107840d101d140480003004121100714560421400902000e40540c0e02040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 617022724 1250 617021474 617021479
    0x30a0b1308030103031101060801020c0703060f0213121509120503071205010f061103030720030d0f0203040204050a051005130213030c080f190b06030f010908030106030b010c0c0b09 80
    0x40c091156034a24a207a402640194002a000380c40b0545080e001e00400004018550096007042e4030340d001e9030b0b11184140305c024482caa41e854000f01380003007030301030701c0d42d906070b0150190207075a0301e070180a80c504807050101d51401d0700d40c2543d003d0b1803c61040790745c42500300c0c00c1c40c40100f2400000380d0355944094242010f020646110010150f0580541800f9280c0c040702004481c1c07810a001d05580c600d0401c120054005000b080301e01a408a10034141e6128007900102c08815220802e0035441958030b046162818003080350401c9400b50020341c040c52003a40d003040181c1e1640c0040b81103032400c0e00c0001e40d010207040200020b14001d000b030885200c42850041c50803e1840709209940e0942e4022904070206220070010443c0c01e0101400079407048001c0d0241001c4200d048500240d41d000c010440400017000c1029030b00c00b000301e1886400d150000b041082820704202c0c40940091041c2c800080c02d1503136503c055441500f4407a0b625070b11259070061141480f084d65015044400c1258 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 617023974 1250 617022724 617022751
    0x4020405040311100e071d0a090f2108011d0f090106050a0305060a1104152624030309010503060f040b0607060212010e040f121b111806030a0b 63
    0x911500091181d404960040080020f61719502e0001d6418507071150311a43c40b48031008038840342c2603000d07030405038001c06c410b4000030941d1482c603200300c401c401c990016103e890010f0070b04440040120000380f80781001d48400c0d1860380d0700d5131000700c1d10140c3c3c80c00c0410120100041440203500c00c4403241c000c03a0030030010500d00e8450000c16180e00c10382d44166081d0f8051800c1c0188044107100742210600702c82c101518003801e02c2600950312083c0c1e446502002200200445040d1100036810246400300300c0c010030906040010001c0c00c0181c00642141c50034007000070038130345400400c54a0084041c1c58a40c03d544d1214204207142800d0a081c0e134010f6295a1800c0c1e466031920010944140301c2c842c01a29001c64843d01d060b0124140c11517001c5071409000d000200d844428010309050f844071245480009410040b03605600e864041d0310401c401101c90820401c0c540010b5620000658441109103070b5a0003882d070040d0280d60103901500801c4081010545c558400b55001c3e000041d1207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 617025224 1250 617023974 617023997
    0x30b0a060c061d10050402040f1407050f0409020c0604020103060503010e1f09080703050a020607030510050d050c0306100e130c0b031b030a0623010f050d0b0a03050c101106040204050403 82
    0x600713041201c000104010350300c60820045141610440c42d1380c1011034420000303086071071405841100d0107407401082c080003107480c8080c0750803030049501501da17035002035440c0c4d80c1100780d9588d10001958100c2c042810202c011545c2c1c101441140749000b070380c40c01441c01d58000c01074419403800080c000f2003010303103400704100802d40c0c0d4801015254400d0380c9042c0d4800d48400300030b08081000d004002058100814060700074030b50340c01c40080d150220750b1814486001d1415500d00008000c1d00341c0c15004140800c01819402606e0000b2140200e0345901240e071a1907011442802c0600300034080d800408041c4903181808010b540d2002c00400c002c55000d1050500c100150011544220507680300d260038810b012281c041d043c60f81203148091410318003a40c0020781411907101d801380400001080085203160326801000c42d40402404401c80307151282050380c0c46041045019010340d4440f0300c642c192a201c1e510201c05035141c3d034007a02c1079071190343c208000342002800070340401011f0b5540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 617026474 1250 617025224 617025281
    0xb090307030c080d080a0b0102030a03020306030a020a030309080d02011107290c041403012a03061805040b0c071e0201030212241c02040b01140703050901030b0a060c06 74
    0xa0020702070003c0180048906030a00900d041d02c000c040400e01c07403c102032030303a1690300001681c1640003542405a100e60343c0c1e9010074074040704803802961001c005600007050607004401c110995031410203584102c4180c013016401c0e100d5000c4014000d208c1008a20042092400e0126859016510072285070718440e12154910701c3c10340d4040700c01080002c08000b50810941034501c2c256040d0024802c4c162092554224100741303459484010820705056145039100b58084000707000c00c08102e03503802030751128007001044203d4003161403401700f00110b851400b405c01540c44940d881131000810000d0007200d4842403400300401ca060680900032500140c14241200e445000d081004109502e03041e10380310070150b0035800080c02148412450b0b05205202420016955011382e4003288121011004036111900c0c1c8441070001500030402401b011390020081010b00000d03a01800b00c60060020403080c00454400e80022420136000040003072a250402c50303030017103040303402081030741000340c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 617027724 1250 617026474 617026493
    0x9050609030d06050d020303031522020903071a03010909030e0d0f02010f08150d0c030209040812071404210510090308010e040209010e0a0e033c03010b09030703 71
    0x80c04103054201007400003031000544154401080d085801100b5200702ea00800c0d182d11000e8241d044000713840034621f126440754007040c89480220205c1c03002410501d00484002d40004001c50f20038001e0343e42c005101c40c0b212440b0f0100b2a1411407a900c2c59203018150030042000c040308600740f00c28100c1c0a0642d40e18290701031101030003070a8140e03042e48244001000e0640101e001000c0c807800b88103003d100c454040b1180e29110042d070b90545d5042c494180034010107801d900013540690071008020410412902900940701c00c1030b036000345602c95003400c4d130710031401d0000250741c52070520040100001c4940c041b18035141c8050056003100c42511020704001c410728840225039112f2070842e00b0940e0000809004000210250f040c0341040d5000482800c018440d400311026107401241802009512454402c0d03200801c90382c1c0e0720591140e0030724444450344c40703940340b42403410700081a0704120051440301c03003134045141c41d582c01d008811401d900032813000b036003600c03c02a000c00056030b40c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 617028974 1250 617027724 617027731
    0xf07080a09050706080108010c0908030301090b01020c030a03050910030203090a0602070f0b2e1d0903250b09010c021c180305060f2508070519030606110c1e0103090506 74
    0xb178400d8100e60402c0d4084c0d095803031400c110000c01100320010803164201100340c90640c1c0f14410085001400100100e1034030281c0c0d080039a150040741c903003a0803d9000b000500301124180c400310a140071081c000e07401c0340400c0309c0c05659908044c240c0d00024070320340e0040924601c01e800250a403141038440303130503202044800300034001451540c40e242048041080d000c038103400440800035400e00402c07a04205c0c94040b00c4040f1038a80700446e210075403d205a5a0307002c2011707030f04510550801000c0c4010030152005a440e40e040341e0200301da4842c180110601040c15400802d0411010101e40d80003450780040c41003009a40d4800748803012071061150001d40c0214010301090915800c80345030140e010303000c4000342103820030201b42802c121b0105041d99049080070b03441551480350a0781d50f42300d0303501485c1440720b00c185441c84c2a5019803000d020f036403159898040303840629000d00da071503050768071503a8008400341502200008440c528013524006141c00f00c1c84000b42d941c1c24bc0f9111098 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 617030224 1250 617028974 617028977
    0x14031506070614070806041812090e07030207020411040b19141215100909020306012f011518020c030f0a0f110d081303020a1223030f07080a09050706 66
    0xf94107000c0d40c42e03880301145070000002c42c1c0400000745101c40d110318000b0344180003081c0e00000341620400324040c50404c030042c041110b04407450710b8480c10090080d030100070201e11481c0341401c1c0030076400f102c03c15501552815012685030041c3d440703001e0041500c880c412010032004e10984000360418030040d00350803c0034503007040e41342041e01d0b9003134509e0501c00105006001070515003070403c0c0d03c100c108044070303e01035005071780340c0340ca10048030200d411a07020001203080700b10291b205052840440e044240e100000c20550401141000701504948103d0701c0342c01f10020450030a4174107034000c01c2d50300c0101045038600000003600401d00d07048899000007180d048200207580c60303045001041d6000390704000e003040d000d0108024042d900007070221100c0c000b228024130200b6008000d128140740c0c00298180910024880044c410041450986080100b000801d124140e404081d28000d1b0030340c50301e0a01d103548001d03044800100080480c0c245c81e840d85144000300e03c05004401c0070706500e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 617031474 1250 617030224 617030261
    0x160b2d06011d10050d06090c05030708090a051c1d0a05060f0d060306060512030c061305160f06030605030a05060a050c041e090b011715060d0204090e010c140315060706 74
    0xa003214804441c85503100c048080e0508c4045a025039004080726880500c600300101707a91140080b0741e15110000707800601500c038080380381c1900b0030440080051000c0c1b90703643d403000300c4800e02e00017514582903640540060103628184800e00d4103401a024001c403030031241e03041030400143c0380c003691301c1c50780140c1d2801c0d502c0b8001d12280c1409001241021a00300c000c40c505540d140c442a52014000c02800d081c8448051843c1009806d10410780324040d210001c7c044640c540001c1d802c60b08280c031503a0080307803400400045509010894440b02e1303801901410031a0303a51108540613103002000d4524040c02048089007110440452000300c8007601604c100030ad0134598090100c0312049026814400180e020b01c4000d0300400300d05d6884045a00d000d004455034001084441c01101c2117400c041d400418040b402c00903580c0000400060b0100a21803980845003da802042642e46201c0840080000800d45d24981e100f01140c503401801d09807a02013a5258001141c0400c0342c9501d4a020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 617032724 1250 617031474 617031487
    0x307080d060b070317070504050d0b0708090d1d0a03050a0b0a0f0506030c0409080d02070308100603020a080c03130c09052505041703160b2d06011d1005 67
    0x2031007448090200785241900e4015070340c501400030301c02000e44910404814001400c150b2180007a900144001703800110481c01516091001810884280c80000c070b0040005c0d0040300001031002c039090b04d585072100500f820b940401240d61050100b90f0300a94101c400000080041000c01c02042c02203030680103e05114007100155030044401c1c40b0f2281c20b040620019580114441c20741d84012100010b03484030034038007001d0b1400b4002000c84254400b01c0d02c0c0701403640040d0542c1c8034510344841c00c0030710b5481e1320041c3c04074020a80d1440c00282d0f01400108030b40301c00310086801c40b00c1c8020540144000b65941a50036482e90007a40100c1e445406100401d13814036400042521031541c0c0c140d4007690b40d0401040ba004511950300f0090710280610318050702032089402c0160900350042a0300d80e903081000001d01c05030f42d4040140404441d20301a60980d950002244030301c002e0a040d15107903000115a090310010105a000c518803410880a58650325080c0b000040744d140c02d0344904 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 617033974 1250 617032724 617032747
    0x3120b03070b04170c060d231501020606031506150403150e011a03061303090b16030f0215010e0405150f0a06091505220504050c040501050117010504110c030708 71
    0x300302d541c00d95139a11a41d034240480d9150300998a00000c5070800195005030540c80c1c0030301405030354100e00c56407003070414071465115280f50300020200c00e80032290140c880505040d139601c401024443c00400d0031021800714523000710031a0035900b0f9840807501703082e02c913102e40c81035440c2c642500d60800da1300c1154203603c02080c0224040525120107100c14021a0303404a9202d00d40100030050072200d8200300405c150066244501070900754444580380d00c2da0701104a05a54148010340208880880d040f42d484c0c400600c40010001d02c1c80303000c010f6444d002e02800c0103080a402100c9074010001401d5042884902c3c0e1441800c11860100850400d4008003040b54095001903410790308210458443c10302c2d107c0c44004941d41680c0100c405510707142c144840b4200340003490001810700007030005200002480501c42041101e0801c400c1c1d0380c51005551100405a00307414180e6000d004010301e1030560b121941d042d111107038152a214401c0d8040781150b01c010303411a554800401c8200030034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 617035224 1250 617033974 617033999
    0x90c0219080f030c0c24160206041e0f121803110d020d1208040b070315050d080f030708041712060405093d0b03190303020904140a111603120b03070b04 67
    0x5a0314009646480103d47d400035103510b4002c101900000b15038018818410202c1a4100c102d50024030394503d0314424030b051784103400c50502c00030016200c0e02038050711412151103107048030b5000303001903102d586c46418132800450740c1c401a81c0c401201a1804046120384032409603240d100e50301c180c04c0e4030702468110781842020301b65004041c17508882c0080c900140880e50107070b420031184994500700c5480e0000d014810054900000e40e0040140065590032850442c00303140f046a2044010a071201001924003c0d401820507a9480001141c0c0c2401c00b6440369802c0b00000f070a41d1100c2c0d440591038111015904404512241010340c6000c1d07400b11503540b04441000048140640c4603040002030391031382002c01d00c3e03108100b2002c0c0041054000c1d8101c502e02e07240640144003001810380c20300c0a2300401c4400026260900100065a02030b400c00c45030213087c0c0f60341c80c80d1201410b0b1802c8900004020228100301d91b80e0001c2565542d003004070100618004d00802d03921820100c00305600c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 617036474 1250 617035224 617035231
    0x1d012a06050c031311120718050604090f0201120e010e0a0b0f132a09091203090c0b0c07051c0507090603030e01050d0213090c0219080f030c0c24 64
    0x114205200780706284c15000040d41d0034135000b04103458901a00000100480462651084140320b0360200003544542c2002480c0c0034091400201f00c1540d50b0014881500c0100302d0040095041103403010066000c0e01c070041d60590401000100122121b20303003801c45005e00071081c041c1d4044840d0740208400b9484082c0d02c4045240544428100b402000c0c50f0031039800e1008040810350f0305410401e100380c60840d1303c046000e03c5c2d445007803681c840700d600003400c048200b070380c40c0d030300300b10a080000b4041e01520400903800000d108195240035803d10380d54100b805804014082e00380001501d988840c0c111030f500c040710001e00d075441c2c2d00746451441c1c04942c0c0e100600e500d00b810710070004a80c100d400c0c0c2e00e64000070300f0400c0e81c924024102c90000c0c401e4a07888051201c0c2400d010402c0d484030760208129014540890f4034100d81d60341042e420403081e44e4004c24000003040229500d00444000e9074007d410041100c1c18000c0310031105051040e4100d010302440d26141c011030070010503403280d540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 617037724 1250 617036474 617036491
    0x6030b0613060803030112050f06010e041217190216120e031c030513020301091101030c03020f030109020d06080a0f0c060c03121a10080a0f0b011d012a0605 69
    0x1030303a89043c6045490f07000501c600420b4101150000702400000d02030003802072518070607214030303684032400c8000500066a0695030400301ca40354031030b41d600906003070180802c85403442c44942c2d540000f0084103060420106962a028010003100c0900c030490500c0e954840c00030004401d091180051040811050303082c0709a02c282400607007982040d801081c100d0480c0340c086016600c0007490441507581c40b100a406610348070103203050120460a10081d220702344d0782405807158001c411000e038044d024849916020400041245c1d844076801403c80200c0f00c40c0c0403e24507610341036682055400401515120115170f0b408080010745100c0300e01810950404c8582c0c0da1a0351001042c0713490f000c6001c4c01c19641c503034586c0d51050350920b50752000e4000400e40c103084946054014060a0240d40c1c0c86000c07410701c0680584c6281328010b03054a6072041e5a40e602c45400703c600711a28619028420f81030001408083d83c13002807521480d01c40c201d9030302d003d400000d20713480c1030030440e44014421b04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 617038974 1250 617037724 617037731
    0x1109180a0c14041b081b04030302013306051608041e08030f0f03100302041802130b030613061e020403031701140d05030c06040327030f032106030b0613 67
    0x1101041c440c00400101044d454842e116a0754003007404a681c05003d00803d29031000301d400010180d05402220007034044500d014004e800d0722035080040b040502c5160146d403560181031101c58403035405065414103081c22007650300c41903111180a0f51041e04004490007080007504c0b0710050344d401980c01060040c0c0258640116005008014020310305600d0700c3d407030000085240c070144859480302541c0c006000b004004881d845400448009010403800b9000d1b041164040f080c2e02d00c10807c00f900c02401a04050b520303003982c075080c202c0c0d48200715022a555401100b004904c5104070782c0da600e4540d00143d4903801d504003c3c0c1700000d00390554001d070250300010b01219407614a81c0e24443e0054a08a00d1070103113180040c00c60003050710304d140c0d9210b01c00402c0141948003641c4c252414000341c0c00f160300b030480c400140008200b800040d00c845030040a04000070720915002d08010305060340c6c1c805000d200c0d0b14030020f880c081e62080d91814821000c4c17100388e2401c001000c0c58004002c8042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 617040224 1250 617038974 617038991
    0x25061a01090e070e0f012006060a050904051504020112060f0e2a0a020705061c0e0714010c0201091502010c0e030a02010c0b09070e0a0504030207121109180a0c1404 72
    0x200f1100e14a0444c1d80140c8801d0401d100590050111117800030922001081e00d01803801e5941e03031850100c1d0b40610400f1a9040040c007400c0c89132026000340e401030054107100c1101c0d4048a138411024000301e04101c400b0102445895061107680c001e42480b010003d40c1c0382c503115903019844d0700500406040b0801000341c1844004280108109060000c40607445942c1400141e08160441d0b108507009807001480008901c6015451403114030304110405c01d10802007401c81d0398003918051a507130310742c41c181800b84a6000301e4a20b01640c0c41450020329050300c0e0444407507000b0700000341c080941e464001c04181c2a8104000a003238100540040505c0c00090300028a102d082a80c041c00445c0b00101141d1a007400340030060281821002d0250b0504020300c54000504003164144d00501690300701042003411b03451114151038200d6440329024200c2410080e4020700a08412207400107c95810442042482640c00781030207800541245450700e13807501810a2246480b5100703d1911554 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 617041474 1250 617040224 617040227
    0x14070f06021608060402010810270606050a09090e0705040c0512180d20060c07050d020111180301060305101a090108060106140f070609021c0825061a01090e07 70
    0x510703171003502481e19104e1902c03400c1142441d042c1c540c22089448000d60300a8844070880c0c0e1020307007841c400c01020840159507180071991405185051400230b01a5203042185903c03030b0f005006494083c0042e40c48462303843c0000380480f189c41b141c6074041007000c10320420700d442040d43c0c9640f0128404040d044e0445c55040e854039070703050380b160b2010300070705040c80f0510424a007240e44198185404896550070034004100707858200040480d854403601c680d03500150702c10300840910070311501039a420f10a0003505900f40080c0926481e07015962407000001003082009030b854050490703600054a8964041c08800604400d4641c60080c0e0f42400104400800000d0703441c110b80b500d01c6e0259801e401c4c03041d008410300c100c2d01c0c0c0100900001c81c0407000d00ca865803140d980207108031005a91040e20200e9040440345544000d0589034040c4410004400500350079241070841030300c1084582d40c541e848800300c1c0c006810b210361840c07058101082c0e030358020b12444007030014900c40000e41d28040c1070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 617042724 1250 617041474 617041483
    0x18121805060d230106050403050f0c030303160509040c0503010f1d06011803121722020907020a020a0b0304021c200a0e090d2006011214070f06021608 66
    0xb5201aa48010000d048484140811901c84032102409103035652041c005125400034001034516010706504e91f0010500014428140000900a5411503444001e807030a074150035540f450070303c101000640450356232480b0302d00d000f2445803503240e100e506140410180720f42640209201d1408020143c0561407004044c580c480e03801d20f07252140441e10403200c5101036659000800302d05401000740c0c1c0e59900b002c40c07120300c05070341c1684106a590307903c008445104111040a0320850100c8213101604004030b10a80c0005035004440d001422b550100d504461280c0c003190302400301105000c00c44c6055904030409100341031160f1071100254032103407038800310038412034000400090300f2045510740d405101c0050400c03001c0c512291134481d182c1a12030440d80701c8400094103421600c800d00c040c0c4c441c55a1800700030320050841c0d83c03e18404124a08192406440f83c003120741d4a002490010800701020f0300b042102e0140301d030707d4450043e24040301e0b80620080921500002e00200c01d0005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 617043974 1250 617042724 617042737
    0xf030705040902040b101e080c070204050405070b0d1b02031c051306090b04050f030f040612112107050708090d021207060903140d0219061812180506 66
    0x1c0700051241d800c0e03c0014018128000a2500f188003004540100e90b082040c1c0c0c4520405200c162941140c190811220074000300c41c80b4000003010702c8030601509060388071550241c490001c80b10140e1f2680800c540d9500a42241c2c0303aa1901c032280c411000c500d80380403040302020b41c00103604007510320150503c0004c0b5941040c4c913035951040041c8950400b82c01c0c0c0c0044030380024040041b9681c07030400203080041140c0a4410f44524210342c0000f04c070000444401f01c13188111a030a00d800c1a2048800b0508856054031941d190209001d01c44203c0d4014203468000d000190304801c010852842000e0b4028004014003c00344020404291000300310350a0150407968900d404225200140340003210490900d41c0c1c3c400c2c200041030383e903000003801095a006091301c001188041c126a40e90b0581a000c0100680080820646507140302225041c030510a0310003086640c0c024660103500e414018094a90300c0031040342c40605a00520b21800075000354580300f100f44d003044013013080da11404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 617045224 1250 617043974 617043979
    0x20a0f0501120b0a120f02040504080306032e02070c080f031207020703030c172a07050409050715090801020a0e041d0a0b0c0408010608070603052208070206041d070e0f030705 77
    0x9000440800c5041401306c541158000c00800607401d150070506603d8008880309406031052001180056010381ca1150100c22105403015962070701d41d8a481c0039404c503134800c0b10b044154000100b628041408215054008a4025a20f90b1580550040c100101070050b0055400c040740600c0400e500420380c0c04102c1d0400c0520140c50071980700e030142c1d841145544e428580c403c0c00c0740c6160400400b04040032400c194111900c460312002000211041500010301d280d01c451070030003800e02c1700000da050076001801e0610100ea9600200c40c01e90f80004020b41c0010038034409000d980c605403003100e603014050802c90781d00020f07182030151795505908005c3c150180410005200300b502100326405044114020310943d0b41d24990a0398600381f40c060742c8042414080050b007410105403001d80b22000d64001000561007130b46682e20303554440c0406a0300300b001040081084c0e10601510001400c1404c008001c600c1c010f2002040d001c13046501500c40c201d072441004150758000391107010b0b02c504 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 617046474 1250 617045224 617045249
    0x5061311091e0a0605010f02010c051909120c08070e040b18210324030a0602030703021b0606100f140c07120f0c050306060d0809010c020a0f0501120b0a 67
    0x681c10a2a21040402e1080105040d61020000d41e0f003407a401000c1201c1c405c1e00c4000f0030b01080401a0b01380d440c1c04c4000740000368240b20140520540401c0e404211101d810403021043d290812118664411102962074002d54101000301c440108540d400070885200c882c45241496541c9864012001d400d62400100e280d03404503104006210b0210400c09000d2a2030480c24000700188890300125000c0c2c000c020b40340a20640c0c11904c44d415413007050000d010b0180d100719a95607200a410140c6a14101942440744082c40d2601c103560269401a54000303016510f098801c00c0801500c0042210030407190040054400750000b4542c0420303044d40c8400f5031510180c1c80414038101643e402074100411030f24018042c484800c40c0d40f640d0364000c0300c030703250429246d40925941c0d01c0140e071440d07040135200c817100d004200c072800a449207204c14504811091101d400092190503103401c51114580c0c40182040107680101c00c02ca018040b451003400040e2040c000114260103902c0b5006000b0308 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 617047724 1250 617046474 617046481
    0x80406050403171006020f010b03150a0b0a0b1801020a0809040914031b06130f0201030921031a0d0b0f0402030307120207030204110c0a02011413080102070506131109 73
    0x145141407030300354158001c21580c1c689000c0d441072071341051250740c000d8050030300c2001075450103001d42c0880020144c0185810004207140b603c91a900803c1d66042d01d60f1184c414610f40c2d10034040c480200303182206143c640c0c140c440204805941e50820a06642c041c000c601c0000f00303040709542e602e0108a40004490384181040440304098242001040c0000982d401c0071001d541420302c40243d0384012920180c2d2510f00600c02c41541c080050061607041500600640c8207400000e100c1e442070500114001010021a100c0c2e020481c14401003622020b40988146030314844496445085507568040442c0e603c52050003400505088200712004001500b952410800c6131059503015a54041c0c000100500075218802804100d10031400c2c01c5840589080780b0090b658000a032038080c110b0710300c040e40152694100c1c4403050041c1081488015100e01d5884815801000024000340e61a6018030b00f003401d1210080036201d00c0c0070443e441e100414403111560040d074405940c00390031920b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 617048974 1250 617047724 617047727
    0x4020f04061707031209081f0b0d0506010608070e0d150207290a0e030a0f0e04060b0d050a02030c03130302010b150c060703020f0d0b18250e01080406050403 69
    0x1040d410410700c80e8032590940d8480d000000f0350394222400340c409640e2958060000f140c48103aa40700794003495101000140042408100c103884504100000180005018010501c54501c11600b0b8450344c02102c010442d098002c02c5550740710410380b80404180444c000082c807001071064003e03000314900130300c95243e1103042c3c0c12100d42e150440080108212141002d0407200e0880f01d0075010303141c0c5070340440c1076070040740900e284e010403450103076041c5180070000312045800703622142e0400980004d6442991564032903680500340b02e508842e619024400e18009403280a01032403011441042004a030800d41e001742c80d0010122001d41d0b80c502c80c01d007001c9000d0101c40300001d0340280c003214030411101d12400100003c619403400d8801c03aa507600400e40c00c80c010304200c0d20340080304101400c014603560340700d4024100f005001c0c0405000c0007801100214040b1820646110f40548005040943c0d1505046420152500115106103035000a012081c0540000d20903600c1d07170701080815 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 617050224 1250 617048974 617048981
    0x30f1107200d050604030210090c05010e0a03140f06010807120b0a02041508061c0506010513020408100647070b0703050604140907060f14030901201204020f04 70
    0x312402002040c010b0058280507403200401d541c218058400d6a4482c0c50601040c00361140190304496500240b42c984001591005080681d140d0310004407540800025803891110201886610082000c02e580c0e2040038507041040c4c01044e829404403000700001800d00a10218040d8420400c903c43d4031000c2420000c0d0017075801240f4070018898002015640c400d01507445844201d45002c2c407442125030849003905008001340c00c03030300701200501c000c1c00c101e142c1c0f0702925040c0394014502030b59184101d040240c48010f07199960344800c02004402540040d00c5801d849540210620781016042e071080c60088002d105a036000600700761284400040584100070f8000e001a4460700d41500000c00411080f0780880c41649800a0400703d00102110a8450341e40d2900400703400f810b04a054134040480e0102d1410003c185440342c100c8503442c0091400b8003400400401c0300300b5445080700f182c0c1c40c07940c03003000c3c07c420610580c08140032008055400c59010745003d81405210404203000d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 617051474 1250 617050224 617050283
    0x3070b0114031903020a17030f071d0d06090201231215100e0a170a0b04020f03070f030201030c05180d17070f05060a0902060d0e1606020d030f1107 65
    0x8121960140605801252000c05103207c0c41d03070080d50202e00010f168081c08140d400b0003218104a000400c014020b40e2403000c8010401c210304000410000021030005841008850321901d40c94600d00719604000360b51485003910f00c403640c0008511402c5021406108000a440040d031404116140007442200c01e1083c0040c1040e40040540c00000d003202d541d05110754000c2019a030000b41e003440c940080240c09150f000134080301409512003040c1c010018109030b03031000001640030201e55041001c4d0004004010f03210603114130b140009801c84228600b60818090204100190040210104d40e001c500c02c4440070071359041350a000c26441015501e05c000c00900052400c203003d4400711305c0e2400351042040f5550b80c0d0b41c03100e0100c140e404c095402500808180010140c0ca509908101c448080030412104102c1c65496441d466070220b03884400941c000c840c400791400e80c54012002c00c020a4002070142c007480b00305031281d61040b080302901c1e0400b0250494601c40300c90405420 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 617052724 1250 617051474 617051503
    0x30405280c08031c27210c110d0c06081b040b070203070f050105030711010f0204032301050609010603090c09051f0e0f010905072016060203070b011403 67
    0x200d40742c480b00d42c0e03070b030ba584035080301540d0359004e0303180c0380c01c00619001d90440c614541c0003202d400c02d55155a0500100c0b12071044a840700381803101d192007a252498141801c0e0507075101d1401c0c296034140709607210700c4210701c0350082602040c5440444c401e41001000c6a000740b60040c60b0340d9030102e08400f500d0340010300760a100030000e400208043c424024054a80c0201e0a545442c0d6036007403035655041c2c3c1842800c0c00f103001400010f280c01d004040003c19285c240700040380d034044943c404022a4440d4008a4841d421031042d944804441090707131442070000c0b0009c2200e4100340700040e05201052058000b01515908441e003041500b072004001021040c80038041c60400315182c0292800300e802d6110011249a000a0140758030b0200034041c801c850307140c64103070b428060001c1c00341c20300903c01e80501c400070342e01d10b0101c1ea1100c0c460505040160142c101002011510b0003004c078140c0c045c03800c551080c0300c441c010074a03401646044a1292440192120300c00021038105041c4a01450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 617053974 1250 617052724 617052743
    0x120b040803042306160203210c0c010f0903110c15030a06050a1706071803080904090510090224090613030b0705070c09090809090912040b13090203040528 68
    0x200c05100090803402101c11103003e44541480c50801c0760b80380540000a01e640f0354030441c0714108e41116046580101c0f4008050b441e05207a65001420340c0d0846c151410559520001c080a065101804805000086001d422a8400711000445038514120a869168400808500b0b91501030340500020940540003c0403d0b40c2d81020381c280c1e446035204895140590070000701c80610400940030101c22060301040154103644806480b0380004200036003042d51660118040703070301003100b850f8030607041c0c101280409441c4180041c0f01d5101103210a0107071002003c0c4240b101c45001e1f90041300b81030381c1880d01c0c3e1200c0203186c54803550960010b042d02a003803007403040e8164030200512600b405510303400e8029941c1e125010440b140c002010700400c105105149a51800e5050b41c4d40244100044500c41e4659541c88a82039000f540000b4691400080c0c03099040c21001c0702e04001c20b0000703c11403d43c07800c2d1700c03055112945101500710115542c01804114204511003940443d04500c000d03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 617055224 1250 617053974 617054033
    0x307030c1b0605160207050a14150c0c15040503070303030504060b0a06021b0915060d060b0301094a010e060c03010503010b030606130b0d020418020a120b04080304 72
    0xb0090000b074034141e000b50032002030340070a50700010703c1c04215400580680d07002d0b45405154010092203a45041c3d00407003184002240d05186e1000e00000d044484c060130419034007600b04041800d12820001d42080309000401c421365003c1080001c69406040c0450309030390303916007040240b0855018560000b0100c10100b0925070024150424140018626a184070b03080e0800c141c0140450b41c0c1c0015100051a9000c107060440180801025034040807900e84d88450189204d0780003608400e0b071055403281e1858003007601084205840f1000503140c1c079409400d41c481240c403440e10790640648400340d040310480060940c4184102c007429400e664842c1010207560300d05500a100300ca10030360806040304d242d4030340812264050394000f040880c241c1a200c0b698070140001451559100c00101b8180015807902d008200e071007103c1000d05020540c0324810064941202d0300700c0584034000c0e603181400101040144da8009810500044d107079503035481c00d07015640901d07410719114600d03a00135 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 617056474 1250 617055224 617055233
    0x1908040308040605120906010806071d100f1701121101140d02130e063003030c0304060e0a030e01050d09060e0c0a06030209010207140102071d22080307030c1b 70
    0x9421580c1c5e0425a44800380c0300c1401c000d944690a010304409038100324086103071140540a90071010035000c01c4071500c00c4854002401b202c01c040512404200f02103000c2401650203108240b44842c0e041c82d04030b0950410408440c035416900740200026191b501c00e280d0741e80685208071041c5a64480c9903510041c0f1038011010390040039040f401d20f21040004030f07540103200012841014050091035183d11200040f0a80b40d038042a00410307a00320518801d03015078180025841030041404050741d900b068500036044035800190b01c1200d400014884001992241012130032200c2460140c0d1958030f51100c1d40014200d1b49002040c191a202c0c220300360007000320343d01c1c0c0203136400c440341c0c0b020350358030311040d010b038855500d2050043c1c01502d414010a4002c13580c0881e900818812030700507548034922440d40000d00d040f0284e00c1c1310700104101c522034031044070b145044040d481c04400b901030f03503440812034007001d0f05000625465201c4824281d21640c4000070a5010154400070b02c00700c0d050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 617057724 1250 617056474 617056477
    0x10c05130b094605010c020d11040c03090b0105090c1e0405040903030c020c0a0b0f03040c0510051e0a0c06050603010e031605070905041a0403050d0237021908040308040605 76
    0x980303a1a10a0f4005148040c00c550322800c0d04440060719440814451a420800c0890fa80101200c0a92042e20707030200c2500c45e48074031907112000e40c500094009050402c10342c2850140d2103544220f6440040100d401440d8055400c80149228900b400da41ca03015101c1c801e0140f9040260898907200c800c006041e030540045c1900e100b01e030203880e0301c8048107050051214107405040400312042100d2900e6507aa0002558402d00a1003891605a161000260996018408000069008a201c900c40b400c020001f40c1e001041242451070003503501405001099002809442d203541c800008280d0749003074000389192012b140649980b2070140103084900820808141e80900c205403002c10f40e58558840c160141e41c001c8400b5080403002404024000e90080048041040a102d800d01d042c0186c005425456941002c0d400c490044480c0d0443d0381d10244400c02e074542089011414158000c80d40400142a101c0c0c8035900e05481c1c03e010f521032246e680010041c0e40d00060008200c0e50000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 617058974 1250 617057724 617057809
    0x51e09221b0504061409100302041a1206060a0c020d060e12030613020702152109010513031103211512032b0f050405010c05130b09 58
    0x1041031036200000444100c074111180d002060b0100014400c0da8050340900c00380f040700744102440e064035480071440790b42c0c8104410780031940110301400024003090400f080052464031080c20200c0a468003809000081c1509001c0e0500056200703200d840b551a000da0342c1d030040c0a071905256a0702d448001407040d0483c0d4031aa0103000c84248250084d0402c99000b00c200a02020303202400c0c004410096005507001c80c2d000300e04001c4c1801188030000502180d0203d40502c04081001141860814000908502c05a450501008502e196a00007400ba05401d450100d00440c6140b0741c540c5075100d411031001070a1006088419801d80c0401d01910481c840301d80300214641c0c0d10180404170140c241120340c2a001070041d004045c008200707401000c1412000d000c05042102c07400303003c4943e16a05000542d8a443c108402d00c0006d000d0140814264a4881c3c85c2c042d2880903d60300c50002d0046d20308884000855140554070032200900480800c068105005134002c2d005a4490f10310 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 617060224 1250 617058974 617059039
    0x3040311190c03140c0a0b090108150d0b04020a090e1c08040507031209031401020901020d09080c1c02100804050f06011a0c10020d060e0a0c051e09 65
    0x402003425000c2002040c06501c9021880140c1c15940c1c1c140007100c84c40702c803420a2081c0080c1681d03607504e14404400070085030700c85690b0385400800040c280c040c000d14004550340c11102c40c503d0b030f40300c1004200240d80c10420102c034603110751002444072201e540c4102195402d0038800104054003107030580c1c01003100f80c140c10f032102c80c076442035480070300484001d410b54101007010408a483e480c5090208001d6103058084280c41c0d550742e030300d003410b110035414440e98045180409940c0402801e01070081034101544003034500071582d543c0f07507450b0030194002c000000e10454902140e01016211540c002e000c00305612001a000b804040d007150140c549200300e41c0a0000070802094482c141c651540b054280140395009940c043d40c00030300b00e0f034114404c440030455091100e10207841d05110410b00459054a06902c4421311000940b40d40707001ea2602c1101c901e21070f001070440340c0c4c0c9940b9407809034100102d040b040380c181c02a1a000c1c4d81044207400b65100803d03850b04500108400ca = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 617061474 1250 617060224 617060233
    0x20f0330360604080a02010e01060510030216140606010909050408070b0916150f0302090a051c1a0a050702030931360503030a110c0303040311 63
    0x2012489a00100309680406010001e003000038000800c000850035848440300042421440032207241e494108122400d0f1902c450101301c0b030403a60b078207001d410040410701000348001e0342410700040d800001c801503481416030000e40300342c005110303040e0101425085218020743c0f50054080b0340c0c4400b8102c403c58000b03032040601003400c104510030140680d42040d109428442c903a17503496902200a00340030498400d5554201500c609410501d015003c4400c0340a0341035a828006001c0c110040f0030300f002d26006002d446007548410307090724100c2e0070031501000040e140100d4100c80b151942c10240c40e440e00c4184d08200046401d405a000b651700d24804c1100d44c0d40d03e0400c13a1a03008035954550301c2800d40032040c0300419609003071007200702107140740300c01c2e5002840148120780b00200c0d11a404160350040c8140d80c3d15000714840ba250030401c0002490391990350f0700387c0fa840300816001031107030741d1256000102d5041d8192010b507501d050840344da90400b82000781c6500111802c180f202c1c4030703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 617062724 1250 617061474 617061547
    0x8010803070b01090c05070b0a06030303060b160b1308280305010b0901030b01021009030c230303010e0a060e01060314061002100209030c0d0f050d081510020f03 71
    0x240002140c04194100c01c96400507420f00380540c1c040c0c20a903282408000c0300b0b101c000080f03030512003e01e0288111000000f0070914610b0081e040c0c5182c3d80c07144443c08001d00081500d1910303000c2480c1403a500c00a2401941d5483d244001d0000c03200c14003030880d080100d0080103811000d5802d1a030a0400e44843c0040d442c184001c0702614030900490150903014000511154000c0e001000c000da414019984a0521400300004880d0340c000184c0014809803008014000c0820301703901d1940c2064000c003010800740e101c031942c030721040c4100070160301c02034000351a00802e0344c0000060109801200800c0d40e50302c00007000350030341502002c0b0a0410a011912518007042e02e01401c180b40d03000b03400e400311820f187c1802904002590b9406005200c01100c044d5a0006034105131032241c2440c808800440c2440c500d02103030034180c901400f05e03010038003041e60910000215140e1048408107240050200f0803401c045440c1d103003101921000ca00705200741c440b107543c00000640f100801d0100788 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 617063974 1250 617062724 617062739
    0x180f071202011206083f2508130e0c0a020303160e0604090e010509010b0306280e0d020f01090308130812010803032a0904050405070b0304050c09070305040b2406190801 74
    0xa8025600321240c41080194021513207040607c1800b500c1088088100d40205031200040c0d40c0c840e80710003504040201051180810403036900350000040b036101c0b41009036003030303000e5902e00c00904006208099034100c80d101501c603161443c145d80c0c0180c403283c1c855545000c5c02c1d02074100c000400056501f05030020703110140c148221685a43d0007030007030102c1e4590200c04012100c03804117100304d0100b01d50401e1300038101c9004071500b4440300401440c0500600100a08241d950908200982d0401003582d020903800a6803581003200d028850254510b00e14128015210f020b050042e41b001e11800029049030104c017551040a0550100c48a2407841e0700034040c400321118500080f020900a80d801410180d105560080c403900851320302a40310220710305980c104550864199108124000682c102090304541082e2541018402810540d4841581c0e140c001c060300c41041040700d101c8140e06140d141c0004d010400b803c150750310300240c0900c0321600c101000c0035010900c03c200014400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 617065224 1250 617063974 617064073
    0x1005010504060e1e0601090803130e1e040b1e07091406210903070218100b040e040308060109150c0611040605040603110f03180f07120201120608 64
    0x2e8001c030010004c0e481c401c500080d100c0780b01905007810808450702c086034114040001313245d5403541d25a074050b25444c150346440b443c00e0080c81d680406100d410240449441c42c89001c0c3c01c580c1c800207454960b9146544503003000361312034020680d94085800d0020071b61f0042e0486e81039035140c1040c524519440380c1400060300c2101860071018400e0601b0418000c0300d100c01c1c5070042c4e051005c0da13141080a40000b5160f4081100c128000055030041c0f19802a1b5404400024040d242d03034241403501d005c0c0ea08480e01002803014007400079a500003420f0341e00c2220001c002d860090511840b01d48604001040780c940d5010458080d80b07840d8422041843c25810b8070202c03a000da55a61a1509000d000c4029100991118450081c03c2c000c0300074100040740607510a090040b2201c5441041c41d2006d8235011070829008020b400a8000340301d05800030f4030003034a5030340a0130405c0e00c0b05400b8801c107005040703079400358050340111184425151070510329000d0800207030504122000b110440342244 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 617066474 1250 617065224 617065231
    0x902090408070c2411070509010b03010e0a141603060b0c0102070b0919030f03020c030d020d0c09080706030b0d120e030607020607200c0a151d06030c070807051005010504060e 77
    0x140c111030340c0c1810695120342d007212015507031740c0283c96045a9880100d159110700b80c1085007a600084014401c0660a0103410340c008500034051101045a22440000303e2000e40450b16600149000241d21402a00140004c0c8449030440d81e444e400c68840324000e4100303110481e007401805000c034840010010b1400142c030610780c0c0600b0300346660387e0300340c0b844c50061004e00309054080c000c41440850078405003c0d1107450110140e80c941283c0e8a0204450080c01281c0070b0020280e000d000c84500081e10303000340c5026007000a83c08103880c00140b040b5005002c020401241201e217401504d03403081d224030b8400c0e400d808888803501c5d62201a038544804540c01c0001034050700401040840701e819a03409904a0b20546005800400100e40513100f1900143c4100c940d9842c3d1a25041d48001d03005184411b010b0403e52004802c070024000d44030180c4016114000407900703005015a0300c0807141c0f6550b200080320804803500c0000d1000d003c0c00d101f070512492400c0302c00580301d801190320520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 617067724 1250 617066474 617066519
    0x50a0603060e011512090c0e01090905060a02090d0507080307020928090609052b0f0e0d0212030412060b01050f1c0e0a0302072102100c03030902090408070c 69
    0x1896821300035a1031018041203104070410540c0c46114400011502c22190094060619204502e083c090000007002041c0c1c01015007a1400c079030034020460108900750807102101015a60f002035a00041110004a0014215000703079200001c0031800000200901d82c82500c1d605a6030f903c070b04010320a002c0c20300e4078030805038083d0010b402e5007803182d00c002000791040300c00060704001c0d625801d240900c1d030f108590b00184040070100f240194a1001d0f0524200c51404003155902d0f030324020215903c800400d80207005003202c0788210760b200c907000080000700c481203e0322141c0c4c6400d810007003a017a50042d0b036141e1411a480580394410030495680c40044e0590341d151844410000e41d1100080842200069480148140c0135900340000c41c1e0a50080d401003c1103810050b000d07104844030380c0000341e111034040101005032101943c07040c0d40c800c0c500300720025a0700341c01e0640142410310070095120342c2e40e004000400c070b41034024200890044601c1d648841d200c03203900d142e2103131b400e80180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 617068974 1250 617067724 617067749
    0xd020601090513020303040329040f170301050f1203040812030a0c090614070f0819030509010b18150303040f03060e01060b03160e03100c1d0a140409021801050a060306 74
    0x10101c0d8904c07802c00015800b421030203400c81c0c9c80b02e201200b01d032010b4404648080d0200b05d9542400006c4441180062104808a03c2c551500b000071711400040d40c407490150034584ca03011440182881035800508580b015203120540c51481d6580d698403c0312543c0200c2d142c803d000b84800c2c403410074402a07071140e80f140c07000e81008040e5072070342d60004c0c1d41c11580c1c42c41c10125400040c000d00c1c0540025010583d04640141f00000c01a0039a10014204a101e80c9042c1040c18166554015078142440c00030500c0c4090303c1d00320440d00d5160805d85980e070941310000740050018000000301d0f045034010001000844444a0002d098a5040c0701d00c42c031080702072011030b51200b07140011902141450808000c4080c1d40404207081010001d00440c070b0039550003d0002241d04640b201010607008100303c0e884140f064001000f401c2d031340c002e010b0642c02d0880751107841c2e121a40a03444081d0000c0000c14016101816880c0740c400900886028018840700052050701a000e1942652891070840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 617070224 1250 617068974 617068979
    0x13050a15200c1e0a08011404080318011a0909010203091b01300b0303030405060f10031a010906060504050a050906010e0d121d030a0b04020f030d02060109051302030304 74
    0x808200c0c103522120094000c000b011440c55582024205090a51102201c40103d0752810001c0c24802c41d840b011240c4d0601c0c2503030b088001c014541c160700507403001c07036161a134031565000002c10207100011245c030741ca800c07030100c080401c4d011401001402210240c20a45c1d40104160a0303001c240c4a40c2074039072020f55a450040a070100030306402106140940b490340412a0b11380003100304800e8442c603880ca8460110890000303000700c1407001415401140341d400c0581d0707440d55810b0001c01009003d859030703011500000140c4d452000450300300c460500304041401203200422420b203d03178006107182c160002040b82c010019581224030083c03111003094642424030005100003400d0390304020840c2405200c642d640051400214010300200203000c80303c80020b008984226203960120411303004002a40d6800104402c0c290b9100200d0300e01c588032407001c1031841d400c41d0151a4180240c010014880703a000407200d0490b04500c07024003d58840b02e404070340b8501603044c080e40540080006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 617071474 1250 617070224 617070257
    0xc080c0a061b050319030510080d14130b0a020d0e0901060905041a0904050a0c0b0f0912100f240602120a0e0a1413050c030a0f09050313050a15 63
    0x221542c5800754054078642160303805080300420000c10b00340b02003a07964040c4000101d200b400d00025110038001800200c10403000904a52088000101c8040002803003e030700f4561400310f40003c010498100743c60700c0d2549000703900c90784d40d00c400303000007603010ba0070001d68900407405504035100f07601c0c0c030901d060906003841b010340748562180c01022548180e5100070344071180040d20641c040d001826003080e151034890b032225480d90142c0d60700e0809000b02c050a20801c021215111030480340c50500161400040b13050110810a158042c0d183c1041840142c60b190840388031004a82d840c502e400d254164845528280c41c0948001070703018410f00c2d194404080d00806210380a07003481c6680303004000000e20b440311180c220010703010f944c00500610f820301074000c0b0600c001110041c000c2e80780042c20781c505030000601c107a10302e503201e015035901030309590b1009400c0c80d00310003540d641e485a10000b609001051290a0165481000000e05080b5800720702c64044219960b507143c0700c841812 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 617072724 1250 617071474 617071517
    0xc080a02090415060f080115080105010f020109050105010b090a121e05121c111602010509191d1b0307030c09080a060e190b0a0207030e0d0c080c0a06 66
    0x201c0a4210703596080240922505031983d4004182c5035a5940310000d01002c0286003560691002144440302d44280e0751a5401641c5581500c43c207280c0039420000640c0e040f030247c05205400752441d440d1000204100c0c5220005051448082c2c0700f0055039036079180d05181d010217450000d080c42107004000306113112070620b40002e050081c0704803130903500700080348000756000e00314662840300c8184901e1840c40c0340340940e0703c404150902d2103080813840c2d0319041012062510007410044001045511640d490003400c5410035a42034031441d15841c0e040113440003050301c1d106580311a184000450101140d840085601110300d029401c0d44c07104d203402d401901a10031120244030b90410301052030001002011701c50f900a04011900011100416040100a80103200026110084813020800e004101c5400000c200001695a0801e040866402407035000e5070340c9c4002010420b40901600c803d110023903428420659440c3c100f103004000c80c0310818405c0c4070124240c0c0040ea40c20345070112 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 617073974 1250 617072724 617072737
    0x70f02060f09060d0b0301060f03110427242702010c15020a0e240d0b0301110a030b042a12020a0f32161e0b0603010c080a02 55
    0x654981c10b01d500000040e0140d000540074211040d0b07101e4003a40285401d000e054018440c2c0008040711030f056880d544004007002d28000c2c0601d45030582809440c144c2c05549500f142d404400d01071182d02460305c0000c0701d00485402100c2c0200640b229070000d258824440f4112402c403010300f1850702c1c54082850702c01c1d101c1c42681404003d02040300804c02401c05481c84102002c0010b0303071402c00d400e014140f401c10710806030060188905801d803640d460b402041d00c50b407881c01c10f551500410030900c0003404499503a10703095402c18410380710040c942070241211118a0310240701c024940000d01c011140c13119003440c504405100c100d20140305581400c0b6015115140040c145040e888100e0b0690b1311410350790002442e441000329916500440401c4011006030500740c40200000680039076030080c60880c0c4000c04001032600c905039000003003018903540309103502c91403104800c0d030140c0b203c094001600c00403d00b10024180f4075062040024150f901c0d2200d119588480e03411500a40010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 617075224 1250 617073974 617073997
    0x12170904050103030302070203100b01050f090f0d0303060312020f0c0f13050103050d0e01181707080d0302030a050703092612010f0618060c0f03140315040e03070f0206 74
    0x4012a5045486500903140618000d80300985d4454151041c10f151010700c00000891500d45002d681450703a000040301c106502d40e0080e51307101c08940000510b62030814801740d40c4400c0c00c0f0241400c050301600f0010859006045031180309460034000d9842d00b02c0000304504541000b40c0120031498001d5070340b5030840340509201001d426030002142201c60a81040e5966480b0031a400b5500d540721a41610540d428238004151f924030ba010360481d900b4500030380051242055020034040380030060003005100030004c0324407003409100003030001e60056030801c40d5581803400090805000e4050740707089540c468015880d084010b40c000754107900c0c1003039503d00d003181080386000c6089110740300d0b0302802e1910340d8140d40602c0d00d01d010f0040041c0c05084c0b2104080c8640401486800c0307078034456590f07081610344019030701a01d411100048000d9004084800100500c0f4051500c02000010360600340e904010641c501d0809907981e0003507450042410304204002d00040c00e00038003400340400c02 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 617076474 1250 617075224 617075227
    0xb040f08120403031a04110414030a020303070b010303090e241f0e0306010905040807030e06120103030206180f1e03071a070e0415060f02100c020f06010801061217 72
    0x140038420320382094800341c00282d200d500c2c6014584c0c4503081741e1345181045908020b8070000303807a5415140150b200d8a40e420064030059512600c080c020320401540c0201036a95550451520840d244820301040c4c0020340f03408030100303c003c1a81f100380e025001007140350901c0791f07191170300e6046000c10b580310640082041c060024a40e07489691000189020313141c000030400240107062030040140c0c010008141001b007480701280d60711089401c0c491705880c00b1042206600c0220b2102d104103405104115103002c00001407540c00300302c4900419440c1025106100341c07613040ba13a80c160500001c1d1850300135806049400c860780041c000c8074036042c4182c030304000b100d40b210750030540b40d010b031260300b4555101044505a44200c2110300302c04121400c000481283c90702035802c0985015501c00d104068012609090003005039003900010707420180f085440555000f07490303840300c41c9046c031188140b00c000308080b441800364109940d88a01c50f103208080c503031a1105840307921107003030081010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 617077724 1250 617076474 617076487
    0xb07110d080406111203040305310e01090c022b1205090d020706090b0d05070e090c0d0c09150e0d060608031801030e0a150e0f0606030105010e040b040f08 68
    0x120400b0700300a2a00351281040c8031201c52580e41404029400800001d80420401c4002a001810b43d4040300d400440159046c031541310000b6070940d003010035002d9804a1000040101003041594140c9980940c20f000c1441302040c16651801400d1450740d42e84528910b1034019070076201c20340c600e104540f4242c82030801c036007803001c1112800d035895003843d041180c181c00655010841c0030f0090411b031808249442c5089941200b0740900142010b4280e200c201007600036200303000040032003000400c031600c2d60605010710700b0716502c03542540e11001e0a06806a0700c141c05080e9450889000c442891100b40801e130307048038070282c071008407075101164030f400b034000c0754040c4209006010540700541d07950841d01da01740c1400d2101d021036410141000c1e40f4078464071010071640e0400d640310840c882200808821440078140006c5800302a00c180051503001740340c0000c13200c0c01004207034000c000c3c698a43c00e95441010048034050310303840c2d12401140000350780d0075002103214001c0d080c0070709080717 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 617078974 1250 617077724 617077733
    0xf200a200f120106091b090501111c0519090e0c1c09050328081324020f16140d0c0f030306150c0203070e01080d120f06030c0e100b07110d 61
    0x10f038406d0803480c242c5d1080311000c000310b03001030142000e404242408942040b410380959a98036803c464802080701a45c1644e40345400f8005403641441040c2c4406a00061004000e019540904c00c0c81101c03004080171650217030360401210b5000c0b2241c65840c0d485e6118456800280240c140d04651a2100300b0821000c40745001d40c210714a101483e8526442c20f04850042007201d002c1c1881c030312410110303018000100c4482100501000d03040314211030850300c800c028003c0c0102c00030306585200001d0002403502c0d078840303c0c0000b07600c0382c3d0244460241000d9007559640382c071440607001c50704510791440070800c089110071b46284a8603002c1503042c2c880035100e00e600342004000000c240b07062807210441c6030600009003c0e04007100301c12a103606d40b07503002d80e03940400d00301c850901111360824550000310b604921124040450188801a81c0e481e24400d6250644601c6402c14030000c04203840c62902e400083c100c0300e00362091820061b041d2a1302d20001c0e14101d84980c00032840403902c0015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 617080224 1250 617078974 617078981
    0x31b030e24010303030b030c0d03180f090b030601082413080d0920030d0e0d06050c03070906020a12050c010f050c0a02012403030f200a200f12010609 66
    0xc081141c40c11290b54550302e00601541c41c6440098400e0b00098540c031104c0d00c4001d210004c040d0180b800c02021385014540f000d02d04100c0d0004140342e120041e0200c0c40c00d825400050070300f001941147d9032070382d0314580e8503103560403440300ca4012404a48100188030070480c11981000d90b5a5144501320815a10081036a000300304050016444c1d041840c103000e01c16a01e0428a201c16991550f481c10a100194881d1074601480003800204a4107503406d1700d404148808083e4461420055400e020041c400c0c150412104030380098021003001c5002c44c1b0200b8115480351b030220b02c5180d02120f440064456400003030f40d40b210f9642c1e80c0000c0d10820b00c1030041d2030041d12202a89561001030050081c25182c0d402e0314000302491142d2609980a03588080104407605450f00014015032a40c08071000050000c50410a10341c1d2960032221000118010210900c12103000c04e81c0002c0296000c0c988400ba14015031000e01c21300740c140300c0e040c039491900f40b0111220000603041d40710070031b00c0c046 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 617081474 1250 617080224 617080273
    0x110706080f0c130e070c0503070b060a06050f1614030a080a29060f12090706080a0c050d0908040b040e0a1d2a130507030b01031b030e 59
    0x5203154003400741d11201c00d081c498001504111091400700c10040b4109507111a04c078480c0e55101e407000103001c01744917000c85500c2580c04030030b59550342c04504246003401000ea822500c00c005c507103400560716000310f0444805440700305900d410240480000c648604c101402900c0740c91001c030420341512018801410b09034a1038444004605240110768201c80040400844c001c03400481ca0a03081a03e0158a85030101201c6943d5100c03000280000940180310034842000960300c00e206103200c004c62950290707582541d44002c6907550300c0f036400c00d03216400c0503540031403401c214042c000c4020ba000240d11034041c800051a0603a24002541180d10a501005c0209009010b00c48802c00341d02400c55070040d5064014101c3d42e00d20701068480c54240c2c442d15007074034510940f8a002c4540941040e55200003005101c401c14001550f802802c1c00301d400c540080d241c98104040303580284698100c104145403a0520842020404d4005204c138a515904034841c14460b02c1d01c0c40418000d0a54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 617082724 1250 617081474 617081477
    0x3030203180a180f06030c030b191401030b040f0b090d0e031203060d050a060f0b010f02070f151b08040e091b090c2a12040e01031101110706 62
    0x1e448140016050710750790740010742031007040c04803810880c40c50b500c092003944510441001505102480c40800140b0040e880201181d0b44000000240107c140360f95108a08050031340c000d9011040b0320002b1143c12540a13204580e1410051012581014019911174498401c2602c12640d90b02d60031401c0000321031511407648100740e8040596801154500142d5065005000500c6483c400f0707955808000c140d02d0103030305450018001e1102c2040568a0302c1d40140c01044401601c030248000341c041281c10381d0224000c3c0c0701c0303108103510028100c4110b8040c4912640c00504040400c03141002c0020f03000d0400c100780c40c8411110740740002103001035205130307030407603036149481140001c1e0030000b480e0403429001403130800c500d02146030080c41101c0d002c480002882c1c0e20081044118064049188075621082100e112440a20022030400308814002c8030912010b00b01003e51034400c03406003050140b5901c00400010f400400306031111003050401c484001c43c1d00c54a10300e84180e680c00f040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 617083974 1250 617082724 617082727
    0x20123010f060c08090d0213090807020a080f060c0f040f0b0c010606020706120b0a081f05060607200312190801050103091a06040b040609021801020c030a0b060d0c03030203 76
    0x501186603000e40c0140602c1c100f41d1001c1503542c03100c03141e40c06840b040307502035030480606504650700d5040b403078441c961041003041035024504204482d608017180490240c01c8a840200d4030703010020310200007000e900000c1c025a070720102e82e008541c00c006601450400305000201d0014900f10009000d48895404d460f268000401041c6c25100107030f0101013903400880003400102d81c001d101c0e4140e42403064001c00d80c00821400b180510006070f0114119028480a0980d840c561031102c05615612090510031500c400701040b40c80d220303e45000302004000703c03c0b0805117404984034020740074001c050300c1ea0003824451411031940190b0000e040d980b40110010380d100d80000c456405401c00386800c002e400307125a07e0fa00c11a10101000b0031080680000130010355464001d641540000fa10510005585103041d034040c1d000b100481d0340c0801440320280c000d500c0000d5940d0180e000400401610300c490b200c07140e00d507002500490f00310302c0c4104c00030302203014456418000e6120b5401903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 617085224 1250 617083974 617083979
    0x1d0406140601081501020a12030506011806050711030f0706020313090902010503060d14030a1115070806100302070b0f24280f0305070e0f01050603041202012301 71
    0x6008440582500405201005080c80040c0e41e01c000e40c07a5000111038403900a11810000503850000a400004e250302c400900305010a941030708414024002a00c5048030b40000411400c4c24425034050030000902c140300001c0803400c10a14008038010140a54806c1c0380c00300c2801d81008150707004000560310000341201c2c5403440002900040c501e1050800285071144d000038018800600954400c11000440307a042c032211143c2400c00341e0160b01220742c0d8080c0010042e00311441c3c000400341c1070091082107042c0300032400c08207224244aa46288640d9125809c020140c40303a0602d1100705a802c0c401da00008000e8001103002e044034940310041442c200c407081055401d518241e2090f04c12a162087c0161981441c0c1241c2c0c00c0c3c80c240c43c0442b4a05103c41c07041e4110281d00034a4100358400000051010101d0014291280203100180b07507900c081c0b040754001030a114043d0411030410008000c10340d690000030380c2c13505510000c14405500151a0b22280201a05015040218004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 617086330 1106 617085224 617085233
    0xb06120c0a06020607170c030406150b0a050909180d1b0c030804140618061e0d0b0306180c040b0d080301240e10030c03061d04 56
    0x2a10089556000003940c5420940b5144003250805146090414054044900c02c847e907044c0e0b54516180c599404000340b50454010245248901000c01d5481400b401400b400e00e40d41c0c0d0381d9440b04400f20410803507c0380540450228840d41c028511140804210300d0108020350600b000044d244c1244510090020400148070002046000c02008030140c00780c0180c840004820b028020041d0070b21665106040381803c4c2d21007a1a00ca141e28030b000c200800c0c0300c002d2055800c00c10440e005200301030b504008550070040f901c4403100c1d0f0860400300b10326584054180070001030f080c5201c0700d503621406015100790060b44c0f00d003000c01c0d13691204c00c54008000c0c0d0001813244c2d29a580d04d0810352078018880c4001901c201110b14880070b501c6250000d0101c0401414500400e6542005070b000f0040480340b10140761700c64100065851001800c8007078688a500395100c0e41c0b4007480d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 616906474 617086330 := by
  have h0 := BRFrame.cov_init 616906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 616906474 ≤ n) (h2 : n < 617086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
