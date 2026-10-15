-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4704
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:28:24.416341+00:00
-- url     : https://prove2.me/submissions/a3b9ca90-cba5-49bc-89f0-82b4d8d70694

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 845863309 ≤ n < 846043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 845864559 1250 845863309 845863321
    0x2060d0204180902030c01140a120603020d05060403020d031b0809100527071206020c34080d090e070e030312010302030d08090a030804170c0c030d03060e0f 69
    0x6015600074002c2d04142c000c0d10a0030801c01001402c614004174041d00032500c84440f01d40c01a00d0500003035882944142c940400140100e82400e0b402110305403850f55258080056141c2204503078850744500d004000605050501a207041004e0b81d00714105400d0003400307203c001a50b40c400560100d0707400c00300050346401d19118100700711340ba03070b400010b0f24080800004820b184a074045480503c0078652640c400ca206e280c0d1243c50038048d903002044070b040d003c000190380c1c0c0e0040030120484000e40b9035048060405c80c180c440307100c22014031100c0d07042030905070602003003c8a004189a2004012100c403400024020503482d1007001007240c00c00000800742400b0341000600410003d0540756624400788003450201000e002c164024420500d403211000d0042e40028040e1080c0c1006000b28181903400700d4007410010411128040070707800d41130201c0d454002402d403a1185034041c002c0d000d40b00c0c050603e4015010710382c4c0c041504049003084101c5001c44205d4100e04e01c0c0480c04503030760300c00d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 845865809 1250 845864559 845864561
    0x80a0f02040b0f120706180b2d03071d01051603030507110a030203071407060203070b07020a140604020f2b0f021504080f0a082203060f0b041b090302060d 68
    0xc14083ca80107512040d07449802a0045030840035200d4540340d114540d000500039040280c40d501a40607204802c110b80041c5604900c088580792000c5180c0c140070003030080b1100c0382034106540e100c0100c0c05030750500306000310080d0003130081d102c00e02c2c0913410429800e03185605220304842c040c2c1456503a4000c600d11030302c0b0b90000c1302c1c0d45280000b03e6400854600e40207540354031408082d03c00c1034000901810302d040201e440c07012107a8680c0103505040d07868a40c000801c002501e4001588a004a103100041c48900e01d00c015480100160102e40b9050051041c248402e8103101c0c0b04500c11030010490401107800711015a250740c2c84070740100d403549412101e2010051000e03610206c2c4941c2030b245207200c1001007003502c0c1c0300390942e6030000300b0f52110b82d0355503500000217005034401d001a070035001c8840c400c21612050b8003940d4000c1507aa46403402100d0340a00400401034455401d21042d082c10701a00f5400203a98510300544c4035560340080c08001c1d07a0000038441c803000201000c01c208a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 845867059 1250 845865809 845865829
    0x30207171c0614010314070804081b0703110103140f0a09052d0721080307180902130f12030804020102031b0109030e06070b011509090f02030403030501080a0f02040b 73
    0x7404400c120300da0712034521101140c804020b2500090070090070380c680c4012207008a000700d1543c0c40d400c017152601c0d0740d00c5400360410240ca401502c040b5031200000c004c00c1043c00000c60040343c6641c02c5180300000141a00c21003500c5803034880c1a8028040c1507040c40c00b181c0d0340300d245088000b412006500e0400d040166055925401000714a06001c03059404072803010500c0300c19080b10313044c81c5d88001d10038441c43c01100e507030302c0c405440d001c080110790100f00540d8031640f80d141c0341002c40d010a01c032714198841c131703004001510b502040c2c5c03981041c4100c03030f801c0c003800c01c00c0c4a20740350720725010300503601c280f848000404100100022904690003001514080440914003000110980d50242c0c020068800d058000405010a01c403050820303400312810560001800b61042e0300305100290032856001d0000108062441c3c0043c9182c0148201c101e1052018409640c0b4106420010305039041a0005410740d00400500000145c1212a4031041d030340c1aa0301145403180c0390b0000b841080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 845868309 1250 845867059 845867107
    0x102010e010f05180a15150308031303020c220e070e042009070c030809070503030f041404060501090909061512030f02010606090e0a020d0c09080c0103020717 70
    0x801c0140e66840a480303a08071904c101402d0800025031082c1ca001c0650b40d500c95080584400c41c00c803480f40040311030703400a05c01554940182c001c2c4940c0d070b5a400300b441c3d004031220244503046031400d400b0135a042c04a40f07690b2100f283c100031110030011001c401091141a03141500b61b44110311300350701c1400e1280c13000802100d40a40c4052500d0704205041d0380b406081413070144201076034031949143c4594020700400c1076944101ca81c3d000c40c1e40035114490b000d010094030344100c507400192544c080000340b0080d544018840d44991506081408544056104a10a41c00d141050015907404441075084500d0808003044001c11401c5c200010040940d001c0a16281000040785130052441007851952280c1d031003940b03003100042c0403400c0300c3d020b00a00000400c038100412410507281c648a4000341e0309503006141a50072400700044410b29020107020840c420020441d08000b440307800304070078082c281586400000d940e80a8140c4c0351010a006552000c140700441d00d08034030a080d2102 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 845869559 1250 845868309 845868311
    0x3450c10050c060112030c141c0302091215070516020604090203011e0305030904020d0f1a010813120302070510060e01210b0c03060d0c0e01320f0102010e01 69
    0x10100000106035500421405410340305510001030941c01c02802a480d884d01595010f9945045541d02200232a103480c2d12810b41c03082e4502100e00c141c0c1540d4810080040d62030050f80e910f00842880000040f12080b41525007000102c1c0c07101d14030307028205a025075a458225524080c442a040e82c81c0e41301400690413410104020a01c406180d0055041e6010035172150400d03030301040880c45100050200406503001440502450b040c503030007810111400303007000700b6980c00c44046d1000300c0e6102c4940105008011b0f04890301560400302540c0c1103280000480003150f00d6456441c0c5d90041120803008250b80042e8903418054140199161041442070910a441d91140240d170320303840c01c1c09188140840d8807146480000c04120184031540e1294480015664402e03485840d41c1004010079000198a00d520340041c034103560355001381c9038400d014040781d4104140c51803860180706010846000c8159031861410044691a02c06c0e14100d07950f103580c41a0400407809800104660810340d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 845870809 1250 845869559 845869579
    0x8030c06041e051c080c07020d020f0a0e090c150c0307030f11060403030b04050a020a080c130321080c0a020c0d05011d0309031501150c02190b03450c 66
    0x5003624101d507080440b015500d5090548031004d0030301b03241c800c0481c025401400d07100900010b09044042d41d04200c0d005100c0044182c2d940d005091011301110b00d04119001040080070074901518008004c2c0145040241000c031801840e650304e12480d000601031200203212240390307521441034903034040d07804015504113040514014000e080450141c601c1142803000280c0c091100780b00b82c50200c065035881c50f00b03a84440e81c52482c0e0358401080d0110b07888400001001007000d01c1c1c82610460007001c81d1101070340c0300314401000003030060300c1c901114004110301002c01e507000400030303045082143d451240e8283c80c600390740105118a644505807505a1070020351200100c00b42900b1310f015015142421541c90702920380398424045e031400e400c102c00303584404511501d14044102d1000e040101d900d0168580078180501c207610410003101d001040040c120060000c900d0045c12090000b40041d0101c09008002140f00020041d086105024a40320070010010845000d00107801c075104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 845872059 1250 845870809 845870833
    0x180f091a0a0f1d06180a1b051f02010b271312030606092907031b08030103060b03010b061804020d090516060206060901060c03020c0910080708030c06041e05 69
    0x3402002c54a00034440c018207000503100400d00c004203401c05d0b5160041d14021640d40d42d1491480b480c088606040380311200d020034140c84d80c000110140e20307044591f452074141d030030009080d0303828444114056500c008143c0e52002c44102c000c225882c0181d0040c0241e95405100340c640424404050041e00d6400e51541500317070161300c80011b5070300c1a51110101505c500012030400844480203c1d05044550f518007550607840c05040d80320b00c20300d8407407003800c1c5195450300d01d0505407a06581c8010000010003c10800744510f05c021901a0020b0080703007404800203803640160403200f40581810350114505036030744e60440e580322040c05000c1040c1c5280d401c1c516503400400d210070304400d84606022458500003c2c015109400090811030680e0a280c0b003213030103008401d0100c00b035202d2401d54030071070b0380c4260361ba80c820060041d81e801c40074602489036182990741c2e40b090070950030401c8150100300c00400c0b0168820340003420107100004d803052901059600c1c0c040908103000e070000f0603136 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 845873309 1250 845872059 845872091
    0x90409060b04060e06060d1d07060f08010522051005041506030b010206091b0d080d0b1302180910260d09050f0405090c0604180f091a0a0f 61
    0x1d07100030ba03001c0041c3c0c1d440b00804508610151a0746074845024000001007200d1034100b0a4040400b6840000307545050f580280360000a800c40300c046403904842c07006442c0c0c0301d84102e005100c00c036100c000906c00d480720ba401c0304405030a008041034a8400080c4415100020340e4010710029100300141802104074a20b0241a401002c000a080018203101503100280560085603690068401c01d000501d106504201505501c1e4200030001c00c1c08020078101ca01a0a0070f281d00d00020a042070b00c1c1c070030000c1c240071011103000d213984107000716045040c07901d01c202e141503400d50380320200d0349905851104c040260741c090030284680e07000908801c0c2c102807a04240482e00011640d850740341232402d440803451070050540003000d54599428030704e01034001642000c10002540c04600c8002e000c1401070380103401001000c2140c90b40d221003280e0611801250f5002000108a8085650355500380007485000d5504901400f0004c943c000c400341d2f11a154074194402c2c200450007000742090 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 845874559 1250 845873309 845873321
    0x200c120601150804050601090504031b030f02151501121104031b0801020405011202090f100c0515070503061009121a0f012114101401080c030d08070509040906 70
    0x1a0b05010188030042d168040c0205034001c0d5071060140403268241910714008100c0180258100112030b0980350b03030700d0380c039038004895a4003a07551101d0300826401c010389044c83c601d80081d00f05201030208103030741c6001c0c40c1079a41c410007480c01c0019251100e6140000d0b080c0305078441d4100d8130000d800070410007c00009904041c41d81c400300380c1c041d91122814200e0260f031048501088690314a032440001550003000804401880c140c0c100011001007169a274001c0101c00114022403002c400340502006000240c5044400cec0129614001d00024101d000203080540601c00c9000500390343c030700030701030000a000b480e00f81c0440740e0514100751900c1c0040003190b008030720300038000c1451700c229010a0740c183e899003203621048010b05004030f0b50f40c0442081c15214840044104526182c040c0b0030b4100f040507101c0045005524020350481c40360060744800a10340c42a103031403110341c43c003017120301020149003440e02c05503403a02c006852601c1165812540300d89054402420015254095 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 845875809 1250 845874559 845874569
    0x181506051306060906050307031b030209011d0d02090711030a053f10170f010b180601140432041107060917030901050a1506200c120601 60
    0x1918041d400801104407000d602900c00010580c01c028042c1d140190300a60f008416843d0004000d00c2c0c08100e41100c014031856000041d4002603e460300d917a1000c0301c1440e83e000c0c03a030305880c030303620170740000c0c440c5101c0300c000a0040030480e0000c4c40d4a406404054103480001059a940b6800580010000c2c1d10011807280d80410b80c00d41d880c10000d080001460030003c07201c10b006244683c4811a00f5540020701e0307025444032005021a030510030b1008500010748080041a20240700045942076400d05d4440f00e010f0142190200d0403540c505c13644c41d8101c0300a0924411031684044c0c51003151003590414180d00121200407080b01c281c11208280d10391080d54035601c81d031103003400c00c030070781704030350444c0d00d49441c00d1210102140e0b15a012104242c410464a0340c40000101060301d55003045804010a9641d07800300481d0405c9400b40f08085080118528451802d01001503c828102000699852074800b1610044038042061680c240b4005109844984d581c4204036540c280c24091 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 845877059 1250 845875809 845875819
    0xc2d020c0d060605190819050c04020f04170111120a06030611030a0507090b0f0c030c0a0c0e060924151b01110403051e07030b0103081206031f18150605 67
    0x900c0118980f178080a03416141400050540109440c00324004080104c80a071000c2c000e4603550501a0703514802001040440d210543d1190b140c10b0300d81e18001e84011803482e440c2d041810705864403c84204a5014402c030f400c9003065501e0301020744d40100103070303000102064542078004421404400185200d0f491051090081c1d42d2440001c8400c1c800a2052100c2c1d054140403a525210510018100303010075001164106400e480c0102c1c540a032448081d5000c0c80c1258082c0101d0392142d07200340c0e000c001130311021054101021100100155884442c1c6c1c540d0011210441c5655803000700740345103464000c816111910035007645050303603016280b2626903290540040c035000c01d40080d641129041006405040741c4200200440180031412040c1805441d0002c00012400704040303020f07501810100c0d441e035407410707000b0b190030303201a0460744240d100401507401c80114000400880000308804240b840c40580d181c03112050080700101002e12401d603002020400d94425401c5031f01c00c0314 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 845878309 1250 845877059 845877079
    0x4031407060f150509070e04090b0a020c10060303020706032c1605090103020d17040915180b0a0b09040212040f03022103010e06060f0a0c03030c2d020c0d060605 71
    0x801c0320303e00a2a40301c1d0035042a06500002c04490190000081c541c1010380080b0b404041940c40f03900700c0c0802c4a0120310a907000c0b60740c040a141c00c100c01d540032120010104010780c01c1d0740f0045c2d682d020502c50b200070951218000f41c042560460041c1c0d10b625800b0100381c8400c140c140040c1c480ca2100c50700b516280d0000340c00115881e1001140d4101c7e0303005004210030400b143c1f11003c2080c98044011070f00300c41000f0005800d030301d41c45101015807800000700316181c10940901c0229100301503c4842501741042c07003aaa44d182600c00c81151800198596208034010109019016041b410008018000200028840d40c00c8920315207070703c2582510030448900a840000449018081041c450140014001861070036025a0400c00081806041051114881109512262035503000883c50700f410401c158250140c1c0c000b0741d13090300f083d00c04d0348091041d90031f44e4468a41c15108600140700c40321142c3d4000d00540c410304c080074048496030500360400c43c001d0000740c45010700411000b6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 845879559 1250 845878309 845878331
    0x6041805150708160509121608070e0c28030e01020a030605040c020304120b06030705100c03091502100908070c0e10080d081807080601080f011109010e060304031407060f 75
    0x20721000780080c0c0c25103801b414010b00c44c051081c4044417640222480c894842545641c1280541100c0182013200041c103906080c82e0041e04204070140242d40003940a204000c0c0190700110380e06015041410b0208800b4901c5100300c0281601c03070700454140d40700041d84049950306822880513660292010301098000c0c80c800c07a500e105038490342e9041d2049400a40004503c100301c02d07003000008003182c15141d01c0d200001c0c45d40c6102044000801c5402c2c032604209a000003591004141c8901c88800040c507a90019444042541754540404d0343c4c1d8905508009450050b6281c0d0754100300c1c43c805454441d4402d214484055540c294451601000041d0b44040022a200d0144807984c4a10594841d082030200b4940116030303180032801440804900d10350704001c40390007042041e00900390301180c11010350071511b21101e80325041c1000c002c040421398000e4569a074143c070640301c031540c1c7d0707840d420205c440d84441d01050211768030001d580d80501c080b542103640d4401c40d40c2e0042047c40549 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 845880809 1250 845879559 845879581
    0x3250302071a071a071709012a030506100f050705150a020c0f010b0112020903010b03010c030617060c121315060e180c010815090103060603110a0b0306041805150708 73
    0xb1902400000c0006c480781210b02e1240030041c1e0040d800c42d001151007669580000e034000209070320100540041840d184400ba4035016240d0404d20542c0e02c8240d130b602040f402004402c92520300c409005000604000b084010405d03004c0c5129100c4c441d5243e8284014800c01135403001c0700c40034241c49161680010360790180305171075022105844040d50407a1124168000e5044410180ea055596080c0c41e62aa1020700940c400845150340000d004c0d07060550610011f080f06080c03155a5000d0f0040010003001d0100b01c0701c00b00f52016184800d5558400740c2400302c80303180c80007421100c124101c02c0c00b80c000380d0048403d41c0d0007006002082d41d00c0d03250440f0f8400d44a949030f01c00c1c1c1e001680c2d04405500400a15404c0012000d00201d12640c003c04610359110a900441e8078aa1319101042400009401d6051001084820403045031501391407480b24040036200700e128543d59040c1e00140c0781340394404001d041d031203000da60340700008510f10301035540d04a40c60703004101c0000004109001d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 845882059 1250 845880809 845880811
    0x250e070207061b021206131214090d020406030c151d060909040203190809040509030f07031407120f09050406080322050306190c0203250302071a071a 66
    0x1280d80d910306a221112100c3c000d00303035012081e60400b495103680d00030710130705008161003426181003043c141101c0e847c040c0b10a000c82c0c100d48040001100d448030941040000316840710030100d40814450406000140c000c0801d41e10007001b03035004d074600144901495519080580050300c4804080b01407480d071014820072600c14aa0242007040003001d10320300640ca294210707001900311000440340e480310311543d842280b81030341e694501245440c010718141c084c841d8066240c0014606003440c17440a0880d03030023070354001414002400241c1200c403001c84181c1d009244c005a59003a241182d0300c0c003620200ca001902000940c00010208a0703081130302842c002c0b900b041c402180340604680601d0501804211141d103c0d5003181400030300350764208549070140906040c492150b90b51840f10000301c4004034100c500b076400500c204030401503400b003c4108800003000e0108000c00a20301282822415044042800411480300b14840200b9010341400e80c402d10051b03d60a46030420000e800340 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 845883309 1250 845882059 845882069
    0x31b15060f010c02190b0406030b09010503150606030a110310090b010c030221210f010f080604030e030c030105090606030d05182101050f061302031512250e070207 72
    0x82d42181c02c1006080c00380084176460b440c03812a41da40c5403103180a44942d0300c240e00c444002519109202010310b84502003900511040b001052804068640301e4a51800180087e21506022002540c2101c168103c1401003440308003141d030f00d2401e9131040381110f81d64040d0028140c0707042d950190307030350089104400b882d40540042258090700240311013481d1715107031000d1480d6000e001c2243c4981401030a03203442904d10300c101000c0d1034a490f90341440360b01603200c01c0844c000d03050100616000401c1c0140c00ca6050328241d188d0f2078000700802d240a00c00700c5601d426620b85030030418080008500213000c0c00084060340c1c0a401400800c9505008068600c0c08848681c8420b041510308a1881e02c40c00c0d0002044801c4503208402c05030842e001200c20400d50300300041040310502e003206070b24000062112045085040c41d0403031003050102d02c1c18a500540100b03e4041c540d074002c100a8104140030880703640314424113042440301811500c220502034440001040c1103a002040000c1910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 845884559 1250 845883309 845883317
    0x1f08010f050303181c050604150c0503010609050f06041806090b100206010e1f06080f0c1213110a06090504110408060c1c0f0203060f1c030e03031b15060f01 69
    0x2c5211380800a40d100d000302d00d0b00e82c0d490703000941000217070f06004542c416801211204803a042c0c0480000c20760341d0b03d5140d401000310030401845001d821a103448142c82d0103445031580d025148001c50131a1045400501520101e00001004142e5540018080c0c40314894103000d401c80c0602406010350700b030f102c4100560031850060003034490007844180e0100c4503003160a01d89821034990840c548954201d4800075010404129000111580c510f41001c05142d0243c0b400541c001c0c09146c41d1805403a040710b10300c1c00c801c9013040c0481c171751000701070b901c000b011084a2a56910003401c000018440c0e640500e041c841100101d01c101c40546040701d00c40c0b0007a01041e0703101401c50702d241e845a06041c0320f0342d41002c07203100c2c10a00c030300c90606000302d58040141d40381024420008900d0b182c00009100b95441c0e06400801c0b00c040c2584211a40d150130b04940e122904c0300000d00314041c0a6005400b1903103080c0c000d1246a0001e0025845404809200515100e20042c850360007034041e496400700f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 845885809 1250 845884559 845884597
    0x50301060b040b030a0603060203090f071a0706020c100e0106031e050601030f03112d06091e0a0206070303140f0907060c02030a0203011104081005241f08010f050303 73
    0x43c2080001d5134480a000340c000340c0503840b1b5650608a17081910080e610380d01c00c54007000c2e800010014074026100c0441489810707030a014060000340300c1e420000341115004079118079070301c00401105600c480708e0b02c81801320040d080d0b0085d000b00140d04c0103481284c0e0b0340754110f11b0b0690f004854045180c00c5400750401e07a0941c0c40b074104041e2052400c0f000c1104c480074941000310140701a044070081c3c0943d03882d140c001c410503c0c40e200c0c64805280482c1e0010b40500c51200300010314036070f00544411002401100707240619080501420000c1c1d00311000003028001c140d0716600174030280c050052a5501d9449261254140c2e80b001c039a140520390106200b071105500900300b61000603c0141260a141c91546c0440d0945808035580004100007260611860000b03102181740c0b040c403000200032a1030032010b96201100c8800c1c036021420038403811440551584680540e412040c51003c004400101100038081d80e4240302c0d2000100140307001107407902c0d001c000c03940b1075031841d1324910030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 845887059 1250 845885809 845885819
    0x50c1f12150501140d050c0d0506010201151e120812180604020f04020d0c080a05220210090f0e0901060902030f0415060503100b090108010b090a05150913020307050301060b04 77
    0x200d030034460300b8010590313014801000304001c14001c451040351490001915183d41016100960708080e1029055905103032200492060105800301103511031285141d407024000908080c2c40c00d035401c652284112a02d0315014080c0a00050070405600c20059031681c4d120200080d07904030708a00c83c4030715003040c80070802600c6c0c4140700d10361a442c010401480c3c10048185042115905140d007030115003d035040001e000b190b44a0180d101c0850403260344c4522910404e000c200a8003440240b0802c207007d0302c191683c0c45039280d00080c0c4144200022040c3c2c40c0c5d1050009002c084401200c1582405800301e0409070900035039004903c2004c410303450b51105c2d5114007041d500301d00186076030740d07440d1301c00079a03031340c04001074610740e001200c001901580d4981808606001600200303071903070410380e4540094884505075070307021400840008094441c074621180010445281550000418091200c405414001202101d10807011548903a9841050500380d602038440d02d4280d1209202c2004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 845888309 1250 845887059 845887067
    0x100203030601171b070f03020114090a060f020705030406090806090d0e0d03112a09010f230d080d140606030a09021c0c0302030d0822050c1f12150501 66
    0xf8100040d2018003603a200600a014496003080c1001d80e46c052140310a003085c10b4081c03040722840e141804d02e52101d46000da441941d5410080b2009003c2c070340c4e81306030001d00c040680c1549d02c2150b011040e69a160350343c1400404400141c000d614845c0140300200b0b100107400640d40d0151504e03070315a450f030314036004104451501c0c003207001c3d0240000c0e560039501404090001e42d0442c038106240d1122014000703680c0ea001e00c2d00142003405404003000621407101000318060407607403c8050101000c403d0500080d6480c007500c1020f402940d801042c1c0200071842d00030700b481101e01c000800c030065404a00b150254410307035a15811030700c1000030603c41200c0b40c2104410500107040c104805d107980b030b80e0810150700050191200c5d01c3c407071014000c610b4184410610641c281c600380340c6908003004940d0032042a20001000900c00584003420004288010300e01c0540007010180c082c0c680b0100100d080990f40480c400260000c503000000c140715105104076102d0002d074118440e420480155 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 845889559 1250 845888309 845888311
    0x80c03070c06111b180709090b030a05060115140a0203090f0d02090f10030804090606230d02090d0209070c14011406091b1903060b0301120b060f1c0210020303060117 73
    0x5a04024841d1001d80030f03140c2d20700c007503001b1039591303864507092898500ba59040702c5160340580d11a0308030203091404210001b80c02c074107441003510030348205a034050007a5200381e403208031402d032641b000c40c002030120780210252000e604266913000d00c0c8083c003001c0103001e482509000313500c2940080407805210412a241d58000a40c4402c11101c1c0d407a910362070300302d0300540e021101c5683c6071b00c024442c642d03102c880c207038030128000360110000c040301e00004a0360040b8903500c3d009c1a40468444440d40c0c41c1001c00c0c00254001c1c10340442c9050541008003124400720003900c20000c90001c041000d40305115200b8003800b20080702c0d100e13442e504104144040003504500d008032400681c17160301c0c0703a104018002005038000c02c0d403c200d0300c2a030142c25120281e1000c62401c6042c030041003035180801160180d15030181040f000d035581c0301c2c00550a07400040321140c0040c00c0810f83d0405502d0181607040302c078000c0b02d80c00101000310404036528841240c505000601c0d10109040780c00401d4102 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 845890809 1250 845889559 845889613
    0x40212040f030e1c1106030403080c090301020f07050d0305010503120406140c0111130e011406070c08061810090302150a06050306162304150c080c03070c0611 70
    0xc042a410100b00080c001c880d169900d08103036074030b490b03d802004170107502d0b010b0380c981c241d550074210701d06500e000d001c80300d008005200805000400355240c3c0d03020340c1110b4034005079041080d19440107040c800d03921000500c25102081c03402e000883c1915000a9030100428812140d0f450030342041811503602d800c0302d00c140034045051080d035000841c28040c040104880522540d02e03004030b01d00b10f40074200d684c0d1215003803108103001030000c0c04941d40742c9020204190b40640d52440309180152100107285e000f001280503541c01d10411030100b10a6400f481c440c0030480c4e6403221010528011a80300c0d65008001d0fa12804503070080c18038480010f45e200d07600f60070016629a131100401e0901c201180c0400d100056007450050345604207500003844a500c20303441c1141c86903818405250320031402580c101a60b0b01ca60200024030500c00c03050349070ba014000948071803006450550340c1d008040100c1342904e91880103e0418402c4112403640d00e1240d006110b45003007200605c40c010540c1d0aa = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 845892059 1250 845890809 845890817
    0x509160504080f030a2a0b04081c0b0102122713020d02120a0b030c09180102210c212e050307080a0b010306050901150b0403050705040212040f03 64
    0x10000702c000341400700441d8030b0111406556280c1180340000c19003810300c42841d40080346c09400b2502c0d2400038164a075059030080302200181c40e00c2c10100480c0c000c0c8540305142151800e2039516103045034000525900080c1c0031140400c5406069003c030780545808a021a60190b0001d0003000c42005190001040500318840c0c90002401140690788600d14030f200c1c0caa000604102400e1615012640c04194110100301e040030f4100080d8541d03a0f0720091502ca05100b001007aa010030380170740b50141d4200d001c000c640da903210075980049128028809a00008154000340c0a0305001d8111000e00304c90303100701c401d80d520031050810082d40292151801804c00481c3d41d00503604504000f84088040b0b200905652a04040600e400200d402543c902e401007419280001c000d180d0f0319064990025005c03440317030b4a90301c8003401007108800c0d212040c42119400070341c0911110090003030303900407070940f40c0d1743c1c0e00ca000340310a0384128021178480280000004001c140d0600c1c156822038400e1070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 845893309 1250 845892059 845892067
    0x111c052502120d081308030402041104150c12020f100e071a120a0b030c040203061c0f0605010801020304121101060b03010b0417010c020d080c0d090309090c030605091605 75
    0x410000800b549800150b98008409401c8442c0c001d400300360b100710001d0709034260b85010b80e03890001d804044e200030300580d00da246802c0c80d4054081a0303000b4001d005042c120a004082004100c0f5600c4c0e0800d40f48120803007095803072917201299090301000c2c000010b080160117859440004d0507014070301d00340b501030341300c0124100c0f103134400750707425028851352242d110103c800380e446515202030900104946401d15001564901242c08240b02c401100c00503160b82d5032a010401000348541c00d00d200c3c21030303030740014100300340c0c0144200c4a42c0901d00400c5a40e803980729540c200c0c40140d8020341000103000044080b280720300036981c1c0c20250940007140580e61342d17002d40540c1d002a04000500c80d004101440301d000105488403000210000900804c00c6200d0069110f92401c8004030030001d0000000e000780d45010211030b006015100104500141030034000c026007510b00901c00554100075a0304140303442401580c040d20350085c05005180c6890146200f8030190400075418010280 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 845894559 1250 845893309 845893313
    0x2105030c0114011403010e060622061d0a0b03061b1201150e04060b0f030709081005040c060f080a02300f0c04030c05060f0c030a111c0525 61
    0x8025001c0b044040d00c605039403541040154400345620059050080e03150400c400c402240029403550406816076680700781e40c2c0c0c07486140d401b02c1003924003501c81c0c6040c071a00080f03584c4021004821051030042c83c034a070f91036006501c81541d107003000043d89580200c000c00d199084105501101c0b2015040380e5141c40c4803500d24194440090b4044c0a00100c5200d0496080c0d8200900c1d60404604480230082c40342020030749100740c0284246141c1c030610100018500341e00070701d0003801a00d03160781100c1c40c400201d202c41c005003c003101c04032601721003410000740f402e002d41118100400c0c65281c00b042c9036a100391020003500401c0c7c1400c00c0364004910340c0034032903c01c05408520b0b042c40c50041c0003403130003058002e60f842021304080b21403042000100003242e10514554266041112460354480030b140107145c440c002c22551800074040000c080011980104900c0c8101031844142d0b425000003a501603500c42201074240b0120300104100e030740c400203203809030411701100001200c10215903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 845895809 1250 845894559 845894561
    0xa0c0905120c10140304110a030206070f050106090c0c26070b010305011107051c09050a090e010e01150905040812040305120c0a121802030105100603152105030c01 72
    0x100329504442d0800d941d40d1610303040405049440c0c40850501d2500d500804a0811040c031004102070040c8051940c2d2206aa685d21380b450b004607001000f2a4a5540364200f803c143ca800080444040d840e100b400511400603000312034512819480301038200300c1e507850b4403807140120406403451807018994640781018920107010b6640c000d00c00c8140c1c030341c10f600e0002c0c2128002c00c1144030b101d10034459640013074000501d00c080e40e042105410203d40c640d01c03041c0c8400249400030790748401803407404036440c0c41070f602c00c4501c0c0e041d6030000d000c24034070003440e242214403086426405504c151410301002c4804d400c8180c00c81d01c40c10849240c442c92500e00000d101c03090750200d00280c80080c00342d0328041140200b54014101c5151545031108100000e040f881c0c507100c549003519115105004000705550b030070030505801500900440c0f4141303c06060740045405000003103881c000701461140200b080720f4042d1881003401180128681316002e000a4002c541140c00e44820802c6414899007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 845897059 1250 845895809 845895829
    0xc060315080d031d0109050303010b070606050907030902043611040513050f060f071b060e100c0318020f0d060924021e0f0d020c03031803030405060a0c0905 69
    0x11541d00098041e035018001c07014041020900304130360b8102280300011074000320859044034441c07500b00b95aa00c5a1a103200078000e02d034001c56101441c4820001c0080c2c0507007008d46802e20880d020014001d010404040100c40e00103200341c2c0103155080400b04500f0f080000c5045802100211990845030300000e041d64001c54140309a01d8a070444a41082020403c0841c110740d140041c01336484c2284100d40c0c1450002d01c84410440584461a20901e90340b002d24681d13500144d09100c0c10070400422aa0b881e00d8620034240545040c80000a1500c01d20034003002c0e001500311040002510b401300414180d01901aa41c072080c50b80e284e80000b1083d11480c2c1680388102c0440c40c400121410410b485070030300d003070300b14280d0040100880201800d4003040c1c14640d40390311340e6150135994200e00410b0103404150b40001f880001d410041d001d00201440c4180035002520440d60705141c4001c0c0c803800b0551b001805a8070080100d44c241460707030031000c2803000c07a01d4005216592000001c5010f44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 845898309 1250 845897059 845897083
    0x40e030708210106050715060503031204030e0a060e1512090604031202180904053406020a0b0c030a11040308070210030c020d0e032e15030c06031508 66
    0x3000600c940040d200c9502c80e034840c100c070380d001c0c8800d614201d400f409034464507400034415040700c1d100104444032a48900054000601241e881d1a40045800c20303010050302c0940200c0c1031030f200110b140c034100d01840305a41070350b55410f2a5000134014407401e07280c0b168100500490601002d07250400d60b080151040b015140201040d00b003500b005001c02c654203030b000e00064010007001e030940001152100807004188c8000030a9542c908245040150380902d100d44060544085058501e00a40c240200454002c00d1038507142d4071035080c0d07511480350700c0c01000700c3e000c0c40000b040f40d0015030165078060241c0001141c0802c450203154a9a401500115080040421110103600b032400e4000ea520b84a400e040054be890054085d5580d2080c11100e020400300c3c11140c01980c07402d104010809146400640fa00101d100320503901c00d41c081407075500c2600e0301011400030810f100681e0100d80d00620f241c6603007401c0520880c050300c2611a20300030441900d03000110450100b0510402032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 845899559 1250 845898309 845898323
    0x21321082d0409060509010308041502070e090c12160b1c0c0f1808100c0c1a091207030f030c050c0a0303050106030b0406051003020912190b160e0609040e0307 70
    0x6003040c0644088a04c2c50304194001c58501c00184005100307102141c00b55030080501640d282400740e412881c01d882900400c004941003400d210fa0441d0010b1006031111049403842200c030141d008040e41e81c03511116190790180030400030407091120308001d22009141403071600307444050003121000c4c7c880320070300840041d004000a48119501002080800a00354800c1c107049203410009503544c144444080400c41c0d0354424400b60074041c014030160544c4c09000d0b084d070404c02599812601c4000c4031030010300d014141400c08030304546011a04080d0741522046601c1550b0030046006110b0324103410207114ac20840c4403541ca004118042078544290f40100d803540c10850000d041d0341245003400e01940c20700c0c1040c011a82c1c3d8500200a030f411910300144ca5044c0c100010761045003c0c01114503c4c00b034601d01114038080510380d0b0603503074054185c040c1c0c0c2ea00e4100c4221080508902c8810010f040c3c0086c0a1551414200034400c82c200108007181c00da0751928200c0c1141e2125104807815 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 845900809 1250 845899559 845899567
    0x3040f05210310170d05030910140601020f06040b041e05030c0c0301060819110406030b0906010312110c09040305040b0412110901060203033601021321082d 69
    0x500f9444203035402400c0802e00340d4104010035000196112160f0701ca54050080c0480001c440c100104030314455405001004d021b04080b0700c2c091204520305983c02030060185035444410004001501e900499000c003040c0c1e015511340d250b0310705618107101e071840c4003180d0703500302c3c0003041c0b00300094910b81505101902107040224100760840b2550791044c43e4540003804598034122001080c40121500542c03503a0680500da0009402044c054000900100390042404295007001400a042c4c92007542100e0801070488000d9441d0108890002d10b01c1e07000f40508c1400b070800c0305c1c074240c0091080c01d06a0420f6164000d0014079000341d08038005d020308192504051055200c1494040d030b8090394440225410024020344911000340402d204842c0720074044d801e000540155001c1150603401c984040741542003060103588075080c80c1800308403404011502e6020410419512721b05a080c649400c66940d0760a0002c2d044800c1d1720f800c141861800018010b074000d842c1c8450300b612100036580b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 845902059 1250 845900809 845900821
    0x5060c03090f030c0310050a020702120a050c0a050a03030f03110c0f061602150c2214090622090b04030f090803090d060f020c1218010e0603040f052103 67
    0x395414482e5020310943c800030281485481c0400c880d180c0d2286c1d000085181e56600d04604043d12405400079005895003289000c540300200d007600509201d4000d0781c800c4041141042686140c82c0107140d442000c0c1c000030030001e401000000c104000601340031035071900b11880000940c0000c00070756015048001c0021440c402441080d901640c442045540303401c0c4950000e43e0f030514220b18105210004020420602c180016181003003021507040c070b940d1f00000500d000701d00f10742c4104400c44c0115007800b00c5500d0082c000500c10000604030088151b2400600f100400100000b0105250f81d025444003180c0540b030028803444c001d0321601000c141e000401004014242d108c40120703007007400701892544e14a0001c030001074001e40041101e8010515840007442500e420002a1288200d40412401c603c3c02802000703000b4040c040d02c0c040c803440156036240542d1402c562241d01040003a000030003a00151078214041d00807614010705000038048400c3e501c0101072481d8201104000c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 845903309 1250 845902059 845902069
    0x1140c040609050d0c170a080c0715051204030f0c0b0c070209060306040c060c0201050c030c160920070c080a050c0915130c121104050406120c090506010905060c0309 73
    0x4010001038404460007002c0d91920030026001c3c0c0500e1b40c072405646091402298104000d030240794001032855921001c004815541e070301c2c24842c002d15030039402d10304440c0034021010345590396044940d801e100e035a00c2c2e400b214080310211500d418040790111351408180800285440745070301d148515910001801007010780c1c840149858400d606c98001c00c400201c040a4007000c960b03460804103030040103480181e459020704150080700c0d101c04540300040e9400000c0007134041c0c0300f12003400541074031010810300b6105028903040c100d02d114440f01c2c150118030720007003141901481c8118503460301e0321500c6090000181c4241e800e603008500d684020b151003240030f50440d80788550b1620f88402100451b15800c0b8000b18508c0342650340c0085041c4502441c0580340f600300c00c00041040c0768a4500001054101d4041c07580180e14007800441c940b0f0480c0c44074080c81b50000b0511200c2071810f074001003d003000602c01410030054102c005400e4803407501074010200301da4040c6032070300103034001c0c42 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 845904559 1250 845903309 845903327
    0x30203090705090c1602010210020d090b060402030106021b0a0f06091d0601080105060310030c2909060304150608101b0e013c020610060309030e0f0301140c0406 71
    0x307118510541c02d000c6400303403210407104c00341c0c05c0342c041418114141c00180e081c180c00e00c12000300180000b507807050181c955440811101d208020700714040d102c1c2000d1104a000900800c80035a10403c4407000900040800d40a800801040482569200d6607020024503980d4001004240c804900f44842404143d004800388900842c11009140200000b080e007039042c810980034400001c0490030025031068060050b41d00034260420722075845100c4000310028540c45001101000484a01c0c40200c9040b5110304000500d031500f1070b12a030311002c20662820012034480366031000000b900c40001d000c9120716409400340041c61540c2c0810700040918032800740303810003c0010a5017100ea03084141c10340035505040100c10041603021240c1d104090f03060841c80c2070703210703010002006c96001640611401601304445542a5500020390643d10100070050200f52a180760840e01e05007210304045d940c80090002c140300c0b13100b0300c01402c1454103441c1c10140e0800003500703010b2903410001314 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 845905809 1250 845904559 845904569
    0x1b0c030b1b0702060708030a0209040501060f1b020a0b22090c09140d140a02040908071b0f12031704050c0913080714120a02010204030302010b0a050607110109150302030907 76
    0x194a4001c1c2d03503000641c6803066900041281c20088080b56090030365505440c01070340090400c00c41561a80000381ca04148680000000758008071250400810f05419841b9145c4c041d02106c400b5090014080f041d130440d00d54405000689551000d900c00b6540a50009050221002800210b41003001b4001115600001c81c00d1550b201070080039110444075402058101152000100c0480c019a040030003585010354424102003000c400d0049000042c61461f2007034a004138600b01e80245960002050320920f17801c640c2000041050003010014001804e200303162000b8201244a16551444e200713441c1079655a10172140c101c004c0c2018100b0310303042120300c814940001c210381d8135540288900d00008201c0c4942c00b14085030000204007181c1c5a07a1000c07a1251180f0144000034000d4200703210503001503003880c09800041c10400c00b2041600c002812103842c2039125280c1807444c034440f01e0013074104018450005002e2159140d030440d030328519540541c2d00d042c01030b00e0500e404816041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 845907059 1250 845905809 845905861
    0x230a0320060c1b040608121209010606081308070c1502060a15180e0a0305030f0a02090f100c141f050c1204030e13141b0a1b0c030b 58
    0x1c0c440300c680000c001c80f003001114005240002d151011501074000f0754006140d40c820300744c1c0040c4011004003e00540b0459041007401951083c8800b42610907a00c9602d0200301c004000c100300c1c0c42080c4d0400d54650096000360b1038030503183d44208800c52a64008928025180030311aa03903a410300000d600008203440030300c58000c0b80401258540e45a104400c0c0e012151500b0210301075054204030008000c070f8056802d0140b103800c0240055004070b40d04100703445014001042050507200307413041907001501c83c007481c900002c24031405171120107000007401003400c612400203d800c1000702030140c1c180064540a50501c05116460102c82c9001ba426828541005144014403060701d02001605a801406843d1400c081c2e4112a0403a542908400503100c4a0010b2030309800000071001402081c44081c0e503210000d62900c0700860414041c1c2e80200281031519214600401e0790701c80000b200d208120890341c40e20f0f00042030b6031040341d83e4a03051080240d42041c80c2d0f107200c1d00010400c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 845908309 1250 845907059 845907067
    0x80c2106030c1f0f030f020301080d0f09031e02031009050313050a0b0d020307090e01060915080f0c03060a090207050c100c050a080f0c0d021006050d0c230a032006 72
    0x440c415003242c985040c4100320700c540c441d01c0100e11130b0301b00e404180c4810b0421562942c42d044002c5d215448013100001080e6156181c43d0082d10403000304085a41280c40c0c039095031083c4565190f600304c6024241d9040c1b20f80d5041c09081c020078032800303500b6807180303005640e1002800442104414541c0c002481240c400108104c03030314507079084070140000050700590302d694600b000da8980503950014440101d4020021542c1a0403200010075210110400c1400f4001040300b221114000c403180b40e40d0155800104d01c807000c0d54400f66411400c0146060300481d1195020b0b4120b800481c015501076105000da01c00c1400d207044100400c00c1c49140c034801b0f10320181c403059920007103024014860580040d102141003517400030384800307010000507541d060040040003951340c02002a1000b510b444c140c0009000d01c1c0226880c00055071140714030392039924048014200c8003004101d10b001d904000c402145607980c01002030081d500c41d00d0307520100e014603e14071024100070054580034500c100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 845909559 1250 845908309 845908339
    0xf06030109030819090b0c121803091e03010f0501051005190507050111030903070c0b04150c020f1507060b010201181101022506031506050406080c2106030c 69
    0x400541d0301c07034514080130100101041c000d000900e20003030003030600d6140806100d01e0f02c2d00900104900a815200e00c000ca481d400d041035005030355100b02003680e0f842001001101d0400320302008841c2c0c41150000704013808400820300f5a1460340311740d9500c41d60303200140014030f0f203100355191011841c642702d03050480a5661104101c40340f004e6005100010540600300002501305400d020300b00601e958076400c107908420740d81c2c4c024403c11100c40c50703010004908101500155411610058002181e02d03d01c1e07901681c428011200076a003201c801140e803a480d4480d0a81c0c980d0030a2010100c1c2ea42c4d00c41400c01004a40d031351050b035411641400407072031070170501543ea03620458014009810310645c1800503441c1c20440c2c58604104004c01070444020320a05001c0e50440e9116241480800c4600c491260000c440e4010b102c0480c0c000d000900120740301e21081640300380003c1609142c0b00c0d000c44445c8907952945801c42c0d418920f801003110703e050511440b0b8004e8001e0712040c81000803c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 845910809 1250 845909559 845909567
    0xe070807151110020a201528060b0a140304021f0309060f0e0f03040e0f0c1608070c120510050c09091f05151c0207050d02060f0603010903 61
    0x2011541c0d04001441e120040c2444050050074100c041c002411940c0d22010b031005000c8041c0501c13007100c0c0d98656190341c07a040c64089251200111010f143c2116542d80c0d00784850b40d12540324610555803550742d0b0b000d0004c8041c1c030500c000b81500c0442c09031100409080140f02c07244a2034041d1800d0414002d110040c3c440381c06681510389113001da00c51100d4034083c110000c1c1007640c005000b40b420b2a03003030aa008120b034801c0410b04206410781e803c4062143c0307425031f40d01c614410750b01559500c10000e0302c960380320054075400058080e502f500d415000d0040304241d00005806940368140050307140100704c0004403610003419040300000000d14607803500b80d180c002100010300340f517072a00700007120040400201d54144034000c2c0b9647d11420050012501c421100315180d40c80800040042114508000143c01c294101c1150a00d40503500302c1603074000b40d00e0145010440d80911004000a070240600d034000000d0b5030027010a0b00d0b01d007040c0c4445500c042e103024041c0e407409a010300403d1344 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 845912059 1250 845910809 845910839
    0x311121c120209061611180c090409140d09090b010e0118050409060b13050907150c060207030f0311091c11041b08060906330307030e070807 62
    0x15041690300403603104081c0c000391140c1c581059016000148491154107050280a521401a1060f41e810301454040c4009625146620440c4501000002c0d0540100000400c1030355005400440c411500e80d0b00c0e071101c0d0380907641c0445141c11001320910159800200760700149465041440080010000070304040a03c0542c03d04202c41c1d590940d180403a401441070041ca03000d0305c00c02180c106420410010030000c016181f00d040740c4440c0b40c1c548041405502d0050001001030300180d850042c4c900d811074550002c46080c420b44d0001280841d80c0f51025043c5079000c3d440d000d8003a40c0c510f0000741101d4200c04841200d890604c50140d843c0c403065030707003c46031a41c11800c120032102c03030902d5a040c46a9581c0164410f041040c6107a061540f250318001d101d15a455508540d1500000c2020041c012103203103400c0105040f80482c030b042c2c4e603080300c4d034040b2402540c1c40c04c0880c0711046d481e0580c42114001c0109441e0b100c0e040044004000c602c00400603940505091801c0800001841748 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 845913309 1250 845912059 845912113
    0xd0f081303080a1104080d081e22051005010303111c0509150d0e06131a1306151a040b0307050a1806170a200c07030b01031112 56
    0x10b8040009a280800e40d840018500002d201e100e8a40399100122540c03a0707006803110300016404404585081c2c000c0300501001c41c21194568469a0b40006401864041070303e8a45072250b80c88401c00426420f01c0803144190a01e1004982c56056043c003614030820048600c032258480c80b001d0808440d0140b031880c02030460701c0c005d5591444c5100040788a411115000d100301d9000800043d0000c01e58030a548400707840c0181e803040d0795213540700c00b050448408040c10000c030f001c202c1900c000c07443d200700381d02068016004a048155450326811241e69064094600000b12000c1c000400c00c080c100387d540c49050340b00743c0703024100140501940405040c80342803000220320700e250a8000c1746201c1d0703075031404410310800d21380da100028030720b81344c40c03185881c02504400420340600050042c080c095418141e180c449610034103040a09030f218541012407070040c0c8902000183c002c401c168001c0d8000c030580c3e4044a207410811032a5a24903103145800d900c000d194041d8481e200c2080e00900c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 845914559 1250 845913309 845913317
    0x30305041a04030225080f070f081c050d1107151107030c02090702071703041503090b070c020a0503010f0e01050f130311030d14090c0901120b1015020d0f081303 71
    0xb900b4144d091005c3c42c01c2e08861054040e0a04034225010b00068200407110031460220905981d42482a110301c500081c408141c41585c81c5c034405580294000c0640e02440030002801e0304c4401b0411805800410044805003200007007000c1300d0005002e54801034071401c408514240041d0b401030503081c4100c04c024098441720000441660080c04624001d1040450440300c142d048002c10307440758000e00070403a40c4281c81c1000c00003144a40718500449600030721001d0940c85200d4107842181c007414080340e2001844102092a0710b0a0151048140010801241d400015001d5a0a440d0001c04910500394000c04004200c4028241c8440c025050f0a04080d51031581c031500e807d511070780b280c00c80002c1c10242c22541034020022154030456402056421503d40d203400c00600103003c0c49000c61010071a50310802080b94900502e4000c032001c0940002255601c2500e5100d020281c54440560000303010070151a0300720207800da4a602a140c100c00d03034503089000d1401d070a01c00f10090104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 845915809 1250 845914559 845914603
    0x20111181905041d010c0503060904140a060f0212150a050105210f0f09060c1804150602011e060501020d03090201030b150c010608031e091903030305041a040302 71
    0xe56210110341c00501000703041800700004c0d9401000b81d9498525001c1240d41ca07203201d9445003482181034901828000346100752075281c80c0c68072214800a40301403405805910055000035149104103901c80c81c07450005031f00c490000c0e0301203440705030060491000a00d49030415089036200b61004040c0c03502400c00f40d403540242c2c9010440d07a4200b903180c5601505060500902e6004825480d01c0380f070121100780d0055507070100329525420245c0d03828402c20b1003804029925a003110f1504080d801c0074100058040340e81001c00805241035200e00d001d43d40d24074158900083d1408103070746448810784144201403402000075a100503054080042540d41d0984c102107a100f600700d0118440010b100e807001701c074054031100300703984151075a082c25840c14000149100001c42561880940200b00d20b8001703115015007801ca0703200d120082d80c03084546803803200c11440e0b03a43d140080c5000e07603000102d0746010b1502460301701104c19041c84d403105510420001a030700003039400d0103245000d01d80d040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 845917059 1250 845915809 845915839
    0x503040203071520030d06080f0a110d0503030f010f05150306063105011209030207141906030902030c090112020f040e0312040519031b052b02011118 66
    0x2d90407007460a12940c400c03641000881c0b010010181003911982401005000c0d508c01d440c07640c0e020815007185880d0850104840401d1600500226415011b071000081003859a1442c0c11940100d03100e80307015001d500188075003a44004510040c2505070b806101117584550211050b020082002c1e101e218005143c00300510003c00a4404104004980c2c0040c000d1203c883c500b91103900443d400500920354203032000c6490f00408d00003581580207480140d007000c0c2200d083c2c01c0441c41840d00300c0c0c0b10b10b08100d551480040303036030300611050b54002181a40c520405040c0284001c2c0d8a01c1403e005006001240c511010884030a82c1266801c00c0c4801d03020100d005030003178201340d00c00b9010200e5401d03001c000c410340c1640f06a110304180d0309901001c1b03000001081c10b4000240c0005c58018194204619409178280c40d94003950032143c80400115209600640b0004517140512081044d11256a02402a48140514070402c10b007000200c0030f1440c5808584950340e482264103210380c1c50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 845918309 1250 845917059 845917067
    0xc050316080c040b1602060c0105061e0a0506090f030a051e070b0301060c0501062301110303010b1c0b090c0406320f07121107090902010c15141f0605030402030715 72
    0x5402d0340540908e444075610280c0c01c0c02008202d910601a0201041c1c882d0b2031010003880780001307075005103034000030740c2010140070b0150004e200458101004100300980756504107c50f22005115500a200b0203200e03200080e14480c512410300f00a60010340103200d9062503505690644501f8541040102d9150604c1805407000b80d11003501c61810954400d02c0061b044e4054400e2482a04d80c494013070030340c5d80d19503580e200c24421001d0107001849a210616410344855000d1520414040340c51035501000402c425000c1d18039480000000508103c3d10fa004000140751103209440f9000424021a50080a241e00f241220014074002503401225100d04150303400250403a072480b100c982c420101800c10340d90900311180c0c42c401c0000014001c0600d0280c1c000c10f5a040e03503500d040d04c42940d0b40c040041c40b034016042541c0d80740c9140000c0110f60054151040c0300c1c540d0700c40c00300c521010501103000b125400c400d0170850708008000140e100040c41e82d04031134521808810b188880f041c126 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 845919559 1250 845918309 845918347
    0x11a09151503060a170d05160605011215180212101a030f030c070302013504021e060403081e03070513050a060815030309040c050316080c040b 63
    0x16a01040c190070301e400150100019511884040e201000943c3d1500201c0094000759074014400c1c2d4400c111001000d0f00c1a4040d1004244100102c42401025611102902c5013600510100703d05440100d003407086c00c01200d8280d41400750100000f80c5c035006014080c00c02c0c01030181c028880817910003894141008180d50440038403400f04500b040c2103d80e0551500368140c2c02c0c1c424450403046212101000c4102e80022480100034400d00b031840e07006407407000304a00030821a00002e650030031240c1009622600b400c1510300c3c284214501481003011590842d4080941c150030369050803001c2d1a044c00720740c00c0d00e8001c2c075500d86480ea501c4040001c0174000400c004d0580001c82800190b0350060007801e44410080500e0310710a446405100c401c1c0420311401001502103070104002e0070485001c12615031002d400d880c0340214034400704040d00d011044040001d43c00100f0811a034a0360104200c05641c0ba1520116a00303100c1007166090240c0c1c094038214000c0000c2c0001d0035a1802916 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 845920809 1250 845919559 845919601
    0xc060a0903050c0d020c09090f060a0903090302100f11010204120b0a0e2d061005060d09020910170703030e190816030308090c011e030b040e010603050f011a09 70
    0x19440d07809813000c02034659101440450040c070a400205104a5011900c0760781c42d0612401840130303039200f2401601a081514098050000da00c00100c056110380c8210400003029449654002c1141703c401003610403d0002c00340d642c0d2041c0414401d05d6540b1400c407108070303002108030000307407150918140240340521004131107110b441d454500d107100b542c505008840034002c0c009008405100d0312911000e040b505400c1d035401109050103240317040006000c1413001810001007134880c560104217040c41c260b03070390758101040c100104424036010500416070b044400141041c40d14603a005404e0284410074180300703042c0c0d00c40d55918110750755101e00003005c801e800c64201c04941c8000d4000c0c0c1c0044e0000f42d001030072410003c0c0319540005600c0c0ca0340d10040e550f000c5010061240c0290480344900342004150711200d00d2000381ea070314055821181400e2000048007803462074090318003900c0420403049a41403d84c0d08108450800c0820980f8600707035062046079603010041048041e01403a1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 845922059 1250 845920809 845920813
    0x21201020301090e0d0512011526100b2104020d051203100509040507091a03030f2d0319020904180b07050903030304260d0f050109020c060a0903050c 66
    0x162019242e0403401c034109010060f640705405d2244115090302c0340166001e55540d0403401000500d070001e8594250004914040369201205081040000c031f0340d494165001c51b0702c1c0140000070804910303070300c0104185220280b82030100c40042d40c000c2c01203180c84c0b4001520600141c21b6440c0c86110680556000c0f0030380d5020080b480c040c01c55904180e035100c00700301c0700100c0410a803c280303c20902441d0080e0040000c989404000406840084004555038a600960156a8408002070004110a101e0b0320740c03130f40e2b8126010050315401102a402411100c686401d41c080004200ca80007600a08012148005481032402074420081c1407608985801c01d24800022050f2400c444944900802c01458503000302c02c039414040c0508066040d0400c10104001901d130107203001400100000d07030a4001941c01241e0413580040b81d17150041600e48129800e240000c1c41680e014000c1d0581c1142015554120340b6680c0c0c0d00104203410b01641e0304008402e03d030284043d2a1041c0c44001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 845923309 1250 845922059 845922061
    0x30207140312031603051605090904020418051c030203310c06030e01110301380a020a0c093309020c010e150c0915040308030103081c0905190212010203 67
    0x22013489448911a24002840d04000c0f500460110b01d0541c0203050566415040c03007829400c0260655021340120b81c86603603109020b002000049030000e155000390050541e414040b012035240c9104906403204041c0304000704800c0d2503240a0f1000551011004211815041c0310310a1164602040c05803280180c8030002810303d0f0306400020032114458002c0c8000d41c41c0605004060100303000b04d0982042e0280010301c1c6511603c0c0415041c80c1885681c0d00c0d0042e100c001c003000b603110300003820040c3c200b600c0369800d01c4103001ca000c0062054031800c1000d9000402c6030301965841040409103145e00c224400c0204400c1c00c0603201901d02c05d03030210742d40c140a00c0c0d183e00802d010070703039802c0760301404c2d10015140c817150401d58842d0580d009114a0550301070304201c81c40b031a49400400008041c40b000c0045200d100c041c5029620444010ba0344200c2d07120ba030700e00c81607035101441c0c2e00c900303118107400041c6010580c0340000b00030700c0c0012804e507070b140f00181e000405800c031401e4541c07000c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 845924559 1250 845923309 845923321
    0x31c02030103050d0206270304091805070e060d03030203090114150114040e0f0408040b03040c030606080303040312020f0d020d0b010f230901121401080601050d03020714031203 78
    0x2a00450489219a04480040a1050007607071200811143c9002125290f0200603100c00c010a81c000c051020000741ca19098440b00020121b8100c02e004403d140e819203a4042040410005031028000c441140b03c528134024001550701c1c09104402010180c010005c01d004005c2500100e1820a220100700600d29185041d1420020a099224009035004024040c5501880220340c15610000d410003200e584a07559807002ca000500201c88000040000280020b400406140628441c040440000e8070750308055058451503048401250020001d010010b0740208808002c00c401c0c200141e01d82148004942c00c0d4010b81c400d0360301c0c841c0001022242a042a030003007054000c00d07201e1b094040291303c41103440004030b8071400c030f01102c3d9007500d4000c2c40e0204083d08400c0c00514100b61026840f1a821003070302c20b12a41f50000203807900041c025200103000440c05024151114046002c40f510002e6840c204d07840340c0541340103051f07612001500c0074401040c40364140c1001e1a902c0c2084c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 845925809 1250 845924559 845924561
    0x150909050f1902041a1308060403052d030f04020301150815101d0a0f022206080c0409051302060f031b090d060b0109030b15040506040c1b0302031c 65
    0x21540c0c5103200a940390342c40050407651096401752034541300351808009070380c80c2c03080082d400a107108092a1b10414005900070082003e02e10551080e9100c0e92100d581c40e0041c0205501007812502e544140010700d41c00010b01f8003601d5006682c41510043c0c3d450340d0003c240146200c1e4000c101d917030641c03e00882c15950014485d060307081c0a1545c402542e0b110204151080c0303482c094454240f080030841e880c2208040030b103a402c007442c4903000400d150069003070002ca0b4090601041803190f00c9021040016400201c000105050301b4040c0a41c600662440182d00c11401000e40117075403a0041282c03207540c3e0309140318550303000d0007196844049140e10040351708121402e01a03064801982d40890040300c041e1042880c002d0a040740715005940c900d0003404080ca0310504000c0316070300000128603045062806483c6900c842c0001900798001d000c240da10003400c160240341080c203e002c0346940f003561509100c143c0b00381180b4000301454202d04611900141025414912644135050713411 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 845927059 1250 845925809 845925811
    0x6021e0d0c020c0f0a03080a0e0415090f1104091e090615080a0803071d0d0303050a0c0c0c0e0c0f0c0d120c09151701092c0304150909050f 61
    0x341c080343c54070680c407002c201e0060a116070454000c400e040c020400201c0020161111801d1400d00c44030750007411003c5811141c05131054580d0070310b0384204000f0144188504944044000400e104c3c0b020b0001d440342440c45a8455040007540d02c0c0c040c4030384600c45c2c0f488910a02200d042c1070095483c2828004080c0041c9034801003034852040000400c0000010b1440300d0a504c040e600d4159500c0c441d0a80e0b60403041c44007124002241980150241e82e2110900c09192003520001640d00385030800808032149041c0102c1803050034104a800701e41425a40710480d803c44d0f106412541c0c811121009501402d0703104040c0c0e08020500305541d20001c5034015060f1302581e2a1702ca101082d01c010010b541c0c1d00b03408100450140c090500000d107106078480d034503400320b0610019481405560032201d2100b684508285031f034820303001c00c61030201100503007501e901c0541040e05400c5074031a59201c1c03003144602901103c00c1150344912501079143c0720010300348090200400d1a12030500c442d2024 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 845928309 1250 845927059 845927081
    0x70e010c17091903030c0204200c0d020105060f0a05040b012001020403031706060d051015030f060609300b07020109060c1803020609030f030a0c0c05040504030c06021e0d 75
    0x44480c80f0000b02c05400c01c806812660903039101000c48002da02880010000e07400c0c1c112032501d03440824449611004c00400ca9211444000c000c1640c820a0090854802418051260041d044142d9440d540c0c01040f03000e9500483e00000d059501600580320384491103e0a40346580e0301d080104c04800641c0548201c9000e134642d1102040c221441100d412022103800d6446182403100072000c003a1035010540c070030100207215100742e482d960101c2102c08031900348800252159408140000c050254030010042e509103940e01070700b0802404203003111480c03002104001c90f2141e07107800807104404030351240c011045002905221314021301902c40740c00c0aa41031030420034a21004e62041300c04403a026040034910014a05540c2041000e500003da1158581300340300540707040a105100415440a140d22091200394661a014041e00d210b035010701d1045142400700400b01e50001115427540303612100061fa11100c40d0b076210403201d074445100e0a108408101c83d0f412801d070f5403180c80707221 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 845929559 1250 845928309 845928319
    0x62203030f020606030a0b04150e19050106051009032004020d06061b2d0b0108010c0207090e0c0f01170c04090b030604110d1a090c10020102030708070e010c1709 71
    0x1544d4002416500e460240b0010120300314980003802150714005281900450711002295849441b10003610313001050a80d0005503111003101d50401809114500003044180d45a01c0502000703c805803540f130071488040e05151a6241200402031641c004002044d0000c00854032012140440b0300200311901070308022603100f250000140d010b20903c0d010099001e80218a0045c045864501d8004c440c0036854410100080d400300040c804002c1c2806808401c00003e07507004d0b101c0380240b8001d501d5009044107858010350b600146000308a40304206800e9a044240161000049491094080d007010000749000705100e44d1103c0e120081c030441d49540000d00c030600d0b5042c101601c4210030303180140180040003844500e81041520810360030700511034440c64403403035142ca8044580c101c900303c0c907d0308040b492021a180c0740c101c40403003245500c0218150b15140340040d00100c40030b88103c0902207000c0000b80540c4c40342e080d40086591250814001240100581c0041d0300400c5c0058411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 845930809 1250 845929559 845929561
    0x303160f030506100e0a0f0e0702010b060c0d0320030a060609140a0e0a1107080712030218010c0c090f1b030207020907030228020a110f010c02062203030f0206 70
    0x140388240261400f0b500c0041a00010086000040d1850b085010105400c00e0441d140001c80562074180350000f42006020742c0d00a10704414001d003150315240c01684100801d1101020380100018111050441810001101485100d1421640004000250100400204011030102190840000c036a01c0d900d58602080e100c0381c540b20f02e804506040c0750000f840d48010005080c8040c01560010205000003600407032a050400072644100810342c0c40e00c42c00a018000c1000340c08202503c4890b6103011800c7c604421056070900c0c0c50365002504000700f1140546c1841000e0503841c00605041c5410840940758240482c003600d0504400310313404024030400300c2030b1800380c02114440c80e0300030603003203082d52400025002904072852548030b442c1d4102010541355842c2d00c0501c840c804640060004242134640132003003642c8003c0050080842145504007070360858208004a03a044400588071500d00c0320191142c0f402d030036110700080440c6c80020900d500840c41c1c03000695036500761461 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 845932059 1250 845930809 845930837
    0x90606010507031206030c0305060f0f060a050402280c140303090d1b050d05071b030215091207030f050609060f0c0901051306031b030506150307020f030316 69
    0x1550021629103010400030424440020303c201d1400103030795455100041c9494485d03ca01803005000d40085038039030300800c217100710700e0104804160710044e10b150740c540070300d8100c0100e03915907464402c2901440c0c020450700c0c1c1d5588121030701d6960440d2104100001041d51400a004a4400f03400b41c400c61500c2da8165403421000c0212482110100010001c00404807005c0700c02208203c8107442c004440a00180050003d0001c100362603c00e54a0319200c1d225420070300b1f003110120400004c12000268208010b8598507001c04030108807070300303050311100c080780030404030381c0b6004c10468039009401000c8204084107072500010b81c013039811603900395101e01d103482e991392094070032701b42186d0b440000034002001140181309001061410905102915201e0120241950044404a500c0301e8446610800c4111602034800342845c09004c6400c1200200d04400c1c9103440c10380c214040080014a400d0080164200035000c0f4011690740c0d141c55840c0c200c80318040100c083c002000d10303514080d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 845933309 1250 845932059 845932063
    0x70212100612120f1701080d080a090f061104080f0a12051204020d02180906071119080313020a0e090c0405040305090d0c090e0106090f0504170d181202010509 70
    0x4699500c18500740d210710a126080c2e510401c018154000c200340205558170754110590003030300902c9030800501412601440c0030748003c41c001c3c001050711389494074010229082d44182481e45800c1140015410049200e182c0513110316080006140300740b07072a004d0900d40009154541d14011489150158000403088483c2c0c400c4441590021204601003005881c102c0d110600b0280300910742e003c10121486002e450480850f0a0312050f0400c2041103522034022522072020080813024001126a0501c002c2510200d550040c225600210000e202030301c40c01e9081040680017840c02851941d42c40c2d200361a100229440d296500820140d404141003030b00030640120b501d0380b6040d007070440a42c1446041089a001500c00612218001400948070b1013020300400da80800860b00c942054200000d8401d849480e5100c107191904200101d8150091803004504040007250b54070390b503800110150807c0c0c4c003001030f52600c10120f072080011304107400e0184101d5400030301c003070b5503090b183c59 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 845934559 1250 845933309 845933339
    0xe030709110a050c01020d140403080f100e061c050303010603060e0105090112051e0705010815010816020c0307060305041b03120c051609060314030304030c06110702121006 76
    0x100341d0410b2041e4030440d030040c2c0c007410100a031000014240360000012005490b440703880214104086000e02c828542c1c050a000e5200c4107400321404581010020101c00507140c0c40380384000c00c00c440c08201c0660720313101030000c501c52040c41c00e554400340b410203d45030391080c82100003003803a28000042681c4454075150407501d004040d901560719048401c1d2035050004d0080b241d90081c01881590844502d412804502c000c0004103012030500001620072007001c1c0208405110b91aa40d4516a0740440d4159119400e4100c0b00300780b01d09214160328000110031440d500d802140000304000e030303055100e41e1045004100785821040701042d40c04000d03500d40400360001c0340b00c040300410315000d041c071419145d104a049540903001c01e101314a50400603081074401a89503442001171149042038010389600d0100514550b04003075502406038442d5803c001c0c03003139480e40b511502d50b035040d10070b55002d107030013070301403825281d80000c03044d1101c3d041010120054a0103401007610b0104080f82 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 845935809 1250 845934559 845934581
    0x2090912160f0f0b010f12050c21010515030f01020301050d02010e030724090501051305040b0d05060c03100611060f07051c063204020d0209190f0614180307150e030709 74
    0x6490740c82c00d030390180701200d01e1002b050140e01c0840c6050140d150030034841c2c84c0c481e09180031080102000e120405007042d800d540504a01c3c0c2c014401440240d81d03041400c03015542c2400c001200c0c00c000d40129040210a0f4000140200070030200c0c504100040f0920b00300318983d41c2c58031901910b440042d00c0500803000c0801e441107092005002c0c40c2000c2e4818120300c06c0040400702c035004c803035450034039040c01124680b0310194003000340b01c1101c1d01000e0540151240d41013000e007000c48a40354a17910680104502c1c121210340707022482c407900601c1200c05040946804840840f07603d4514030207041d06205000c03c50340d25182c0f984865408603100d00c85807607a114a5890300c0620410040650001c0d180c00e20099820411151f05582c0c00e4540140010343c499240380310ba14001c40760490b908144c2c07081c130a01c5908503840c01d500c0f010324100c1d00d020000c1a4088040d070a200b02082c6040802e40042d450f0310609202d88160a4000031100100f0300120304498401d43c80b130358080c0a450541001d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 845937059 1250 845935809 845935813
    0xa0c020c0d030903022d040e07120507050a091808030a0204030b250e03030a030207062d05010e04030804031209020909070e150f1219060902090912160f0f0b010f1205 73
    0x1b40200d6807030545c00001c18242c1200494544507207848c0207800e0f008000904a8050740990006c2085007003140d1100002c0440c0b4008000100586500c007110001e00c01c0020800b610020004070013243e81d0381564081c5401c0312a03050507151400e128420705152400c4c6440380d012003c2596030440c413501d005039811f00c1c0903021750704081f07a6042c203402942040348221b82c050380391550307080504042090054903400d095105160030003529261002c50300c1c180c10240d40c1c00380120401001c40d4102c1e24558016505180988540e060040c00c2da0050840100003513004130300c0300034441c0511002901c8015500c014038075821940b1100188440004040b68854001040c4030011805207403903c0845482c240400940d5112903a040b0180b0040c0d006c1c4004840040d41c4420030003d41c14040e1005502000c000300512412807030303265006035402041c407400010f90b1407000704401c020b50207010102490380490204081001c5240a0b42c01039824020010504120000020700080940802d070b0103d80000c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 845938309 1250 845937059 845937139
    0xa0324060210201605060f06010915020606060313061109012d03020a2015011215110f120601020c10210603080c010f0609020c03030a0c020c0d03090302 67
    0x3103d05469003102090945100c41e00e9048000b00b40301340051440b45a007050030305410b1504000240c000004e90b0000040e041801c2d445120715a00081d169410050440741162640d031040c00300f14000841010040c071090a0000344120750100d4005842108800d884d0840c001d00f0900c200d90500000e82070380c0c01e1090f10b002c280e0040c03e00070307401450805094a40800c40700c8007550725050718100721107040015400751440c00030008030030028a002d0200e403800d00003242c00e0364403484803525880510384119562252003003c4101d84c1c0c0102d401c0320422020031074889222031110440f0342d808543d642d0240c01150780e038402503d460311580b00b200c0340c10f45814044d03050a404035a00001d190940d01e5143e0b0b641d5030040003041504007e09070450003e4004141d0544020342c2400f076559a9101421190051200301165540801640d40c0076010701d4001072041c402010481c81c008504140c0d035005021268240c0600d03a0010202e02924020f4643c0000c50080c2071060310171180d028000203a6200d0300c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 845939559 1250 845938309 845938361
    0x513230f030d09090c0e03060c270906040f0e0a1a06031f020a0905151b03031b0d27030306080a08031314060a020a02010b06070203120a0324060210 65
    0x2501c80300140e0654900051b07501c0380c0d1004a4a01102170f90181c0b01904041000c070f00c114240c1c5000c540000b41811560301d001800700204031032400280a0521a948841200284012030b52100104a80d2401125980015410302d80003070490061005072881c400800035940b4200003950750101c5031103041c5103035603100a840c014000d4000003055010840c41c540000b0326503407403000a41c080c10221469543d24011400c111240940350100c070056030b0428800c01c8040c20350303004c40c1c00c2e1b0112001d0016642d0070503420028000c11481a50103001680c00b5020301c440e40307004050352040e034400e45040000540390141d1960b03400321484010311512003080040d80f0070044424485006204080ca00d1103200f94580250034040c00b1038141a6076580400d00c0e4613500e609006100e41c0500580b5521700c1e00e11181c01094603400800c3c0107110140d00001d0055609100f0340c01611034248001000030100781441071012000900d101c8c580042c8607414601411076074620600440704100400048940390704 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 845940809 1250 845939559 845939561
    0x7050301020f091203070c1d0f040b1f05040203040f020901060504230319060515010809070b0c03160b010312030e06040b061801081e030a020d0513230f030d0909 71
    0x101341d100e10500061221400050f10300345a40007034114904000c41d002c021a1484440e41402018509145480303400d01020510240d0100e41108180d054841c55501424404c002e4680c16445160014400420403090080070900c485045100b04c2c1e800640d40d070707141c500f150310340107502500001041c01060074980103a20030403641000000f4091303a46102384410391100702d151000084c0c407010b444d402001400e0403e4112050705040909015007507007404034540340d0743c040c640500782d0301d004000740720001807204000f80e078260452078281e2014140c2d146482e8000c00421320040313840d41c081c4111940568024000c031035001c48104000d020702c0c0c1d00d588800704860f00240810750030000070408800c102030ba0040150107012100300824000441101010701070943c000d0165840e0030605c2000802c2d90301041e01c0081102d58640300b034a0b00c1c0b49a910f81840d041b00e81c0309401030802e45104956864980c1180890709608441c05103800300c01c1c0090540b142c40c0b00510b000021200c0d01d042c8548416 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 845942059 1250 845940809 845940829
    0x1050a03060504240501050c030d09020f030d0c06050604091104240b07050c04090305070f0804050603090f07170709050c0d02040602060114042a1e050403020307050301020f09 77
    0x200e24010401558520100c1c0446851854480d101c440d800d80c60241c01c00464410402041c0a180c02890b001d8501045071303c1e030044950a66940b0785546e066002c2d90340e04220304900304802410b444c1c01c040c070f8610250551444500880d501030401d0001a035a10b03003442181490703600320301010a88402e071000c05c4010302c4031b00440190011412104000700700c80480350f00142042034542a51001c1e40d00f4035504d050342020099108509264103c000281c0c01800d50b018654003461840e0709403d24079050100d40180d420190304408007200300803048400040110005a030281580c01454a84040d8070b00303440c1141c144117003a07204040c01c01c445145503020355402120007851038106414a00500140c0c0c0c041d0b8801c17001a4030480040c410880c0c1c0e212201c020340411101000040142c10300340189450807950f5204000030750803c002840d00420181c1a111218402c0400e08050360030080c0c11500580001ea0081c4194400480c403414144211024030090010803402d05c246c010401200e009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 845943309 1250 845942059 845942077
    0x140603010b0309070f27020901090b1b030a260f01060f02070b072a03051507020c190f0f0b09040209180106030c1407020a211403090a0e0f060105 64
    0x11590030005617038074404100300c01610a90107415407850b41d0400038100c003201c08102040142c810051004945c0e0800c0c065400c64034070200d0242c0b205d840d15210b00302071082042d8050345000006070700c0d1920b80d22610780719030a00000b440c450b00000741d15500c0300328082290b1000850380000c005006030b030700501d00d803901c10038640304440040740c9819407513503580c002c0304c0c04070340ea0703518a000d190754a40d1500200c121010391740880ba6040c2d2440c0c451035510b03038001d02090b00e02c20020002c034100d24400c1c001c041664001030149140350001d1800d01c80581441d101c1c22040d405200004143c08102c00c1c911000c4072144003c2c00d08082210003040020752180f00199442241d000e92402d100d5241c03049030307000740010f80300040d152450182c0540300ba0300e00e40b46e023044148104200303c01641e554404000b0b983c0e07034109000b002c00ba20190195040915a4041c0030f95807044807031064030788004001c1032094010380e00c07030100580da215408140c2005a0340d03d07200045000001b0750710f5201d1009825580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 845944559 1250 845943309 845943313
    0x12060a0f14190e0106180204061103071208040f06051e150d021203070b0106020d020c0a0503030307080a0f062c090d08090a1505090115050607020415080f0610140603010b0309 77
    0x1070b0b0340e401d549582c490942c506c0c6003884e4021508001044c1c100364403281340d1140c580903514001c42e0f596120301001c42d00c03104d8020700800c3d8000c50240145441c184d01c14541c0144100014100344101045402a40a9058400c2042d400043e02c40704a242e00f220000c002405048512466900b0041c1078620450003030307000d01c001d02049012130241d03c0020300801c01c68015000111001c0c20090030105000c0b034490203142a00c070104002c1c2c50000442c0e60002907460310380081d4482d01a0b650203481300c54800c0c00e0b66803c050000c200c99032211144030701c4d5581070b0400704a9150841900402510468091045400180784000207502451030194844440419500c40c501c00e907440030011403e14694860039682e51040121200003440b989100360381719542c403a0768514000c0000c11501c51090020300654407041c0a50b00500240c40420140c1902010749051071040c590301659104200c6000300c206500840000f0044e0244000c084181400340030241713140e0a242900740790b64809400321500d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 845945809 1250 845944559 845944571
    0xa170405011808031b04030b04110a090c0e03150906070522061d01020609101d0a0b04020a1e033504090e0304080d0c0212060a0f14190e01 61
    0x91000e0a248510300c0c3c850342074543c0380c1c10882484026441c2a088107000040e003004144041244000b0141d4807503485800700c852000c0601c0803460895086d400410301a003000441100a50000c24144d0442da040e41110044040c41f400060f0024080d1075030b5045410100118030b001e4440c10003800c0030f00031268510000c46454070094400d84095100c040010340d912101c802d41201051a05a241c80c240b0081002d4100310300070903243c0c4066a07a10403616612010002000d4002c00d6000100d000002981c40420b00e90a041101d9441210228480c881114000ca00c5034410302c003c001c0c850011000f0407001e0300b580c0d0350700401ca2080c1545040954039922603400e41440740c003d039129401d10719000c0d4a85261080b03510aa414401240704140c000788020300c911003001428020300b500741e03e0090744540481c00801c03035a60b00d04a00f03071658010942004449252034000c0380c2610340d90712040244465002c24822816010f031020f50841401290440c000690390b00300c60707080c4085030000501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 845947059 1250 845945809 845945831
    0x91713030c0311040606050c0d110a0203101a030d080a1802060c0a060f060e2a0c160b070222060512010b0901122a0506030a0906060b0a17040501 64
    0x10705140d402203a54250f0202c03e10443d040601a0800426103400d2140c10140030744ca145484864000c40242000794110400f0202c0304100b29190400d5000b07410b58010740341800a0002518841d59107180480f0001c0100d80c1608000070702c104482c04690f17641009450300207041c030103809901203450b1810b01078014540941d6800c001410840c039010001d001c040d4452424806842181d0703082c402c402e240070b10070082c2d00007000401358000700c0c13103d180b0911100584100300c4646844032001e000030b8040b40c154811a80094143d0406051a00b040700301c6a03920041041c03403081210094100542d0350b04a400031003d511104007040e4036a001282a03501c0e03401045030002588140c0d1801d80d12160404030f1810300300e80c0d407400b4002d14880c610040c070f00c64842e5207a0901c10b5151b40c0031401554001008400700403041d4003d031100814850380c03420f11901d101d000d8078000d10700342c1c2c01c01c6c0303092400104404000704a50000e88030361515050480114003039040740d54024400e0301c0c513540342d081c5051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 845948309 1250 845947059 845947073
    0x601030803250507020f0604050a140d0501020c060108060a0c09120c0e100e06030732041103070315180f0f150e24040209010c05070e01090c0309171303 67
    0x1d07000b501d96a05071a00f4881c010442c3d0520117504190150508210902c40c0d600c445207824142d602c050504203240b80e002c3e010030410302400002138559440031688280d40c1d040450018100c514410865120b078484a10310070440d9178a803520004601c02440400084c440d08040b060200e00603040344a0301551030922014001045611214100084009001c14083c9514a580000003540208662070070310302d40e4500549100c160035003034550642e010424003558044603402440260050040c103244090141b010340059944a02107824100c4004001203054011070484083c46c02803988002c1d0080001d0050103850305950100340c40d0611884841064080d204196289883c0c401460340f812a602100b2807000d001400d1000c900e100d003c0f0800b003c03148015100e40e040ba401030b0784034407540050700c00480d078031030050090042910001d4800400d1400a04840207417200b40b01e4482c1c400021411503000040003040c07800c106c91030350148004000503101c40078641841c50f030099140d0712081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 845949559 1250 845948309 845948371
    0x60b030f010e010219030603020d02210102130927240e1606020d0207062d0f0f03091a0a0b0306010909050d1407060507032009120f0601030803 63
    0xb82c150b03400140e449032407034148025440044481c0303010800c036415607001900a00c11468060f10504060310341c0716101030324098118502d40000c000b190703100611134451051500f0343c4140b022103444c080c01c00d64a03041030340d58002d11007414581c0c021504503541d908210740d20300e000300c015901c407251140711340800c45124485003114824010040c501d0f8929110603681031540000007150426407500d10300513000148101603900318180146401010b8084005400c3e0201601c1c08040c0e45030300394804030303800c030004006039a0a96160310001c2035035031080c2c4c10f0355512680200407600c4040880e4024a413003401d1a0810040703e4085005010316000074604402030308440680e5a0b1142e42400b04171041000b94010019414484540500703d46104854080c03120080d11041e107510005484a11a03400f8440300145020940052103506019034616046002600d0040000001d510000800000c0c40740d010302d4080700a1141c0c1c2e0071a03884030a0b50300f000d0078004074510f034080c0840300b1825402c040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 845950809 1250 845949559 845949581
    0xd030f110d03060e060105120c0915030a020306011806020a0201180807031b061d061c0f02070501060b1207051b030403120806042a05040306050f04020109081603060b030f01 76
    0x30540034103011301c2d91082c54021303003d00d060280401c80d106001480d45012a440701354010881e85a4100e14045656004003901155442d4400400c0101030412039000c0c501030700081e03a840c0d454540d01d094100f44070240340a0140507901c2103007101c0c010741c4964840d0300007626006420260617551030580345000b030f560700704075080080d502d00321030340680102501c00108894035120710f20090b1020740b180c1144c90801c0342c0717018030b400290b168941d0400c0c030088200ea42092404100315884011110000d411038076040301c00d5403c6c0703540054200f56000551f0380c0400e80604aa815441d0b042041e00c4550025000c52105070b101450b00c1f100c2c0300240042c00c01076008074000c002c40c001c0d04400400d10800104000e1089262100010500c10401a4110460240c144601d066080100250358601030742e8401000380d403e003801c0002c401000d4042c13a0150f0300c00c2c1c0784e035120b1584541002c1d4a400d0703ca40c0f113040c40c90ba07251041010441c2500b01c00070184028041d561901411040203095620866007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 845952059 1250 845950809 845950811
    0xa0e0306090c190510080402030a0b010e18070e010501030b13020a1e0f020607030e0f1204081c17040804030b0411030f07030305040e060a180b0910050d030f110d03 72
    0x69900310b070402c801c00d050728052a041d110f0800381001c000520700e00c0410200c0c820880c400000600315141080440d81c201c1e00507085110540e910002181e003150f04a400c86990000444404461200083c84400390758400c00c0440d4240c3c28030f40118000c0043c2001d5a0f440389660201645e49c1c100741c80102189010366541050705c0c0500b100c1c850050140a20030010002400350441140e540450308a4100055140204090152480c03682c544001e05840300d8071405600b450400451200c401482100c8100d020f541800f100c4001e456040380c0364543c0003000c1031003111400b11401500011540c4103100f04041c90615403203803504817130701504580880d42070b501e56140020a240412840211040d6400245103460035940c1c010005d00580c40354a68503400700001c03404940c2d6901164000d08100b080c2d0106032003240c541032014007070300c0d84220300494040b800b2606071100c880400041e140e010b0f01401d0942e915503000c540f400c80c0064400c040083c1002031550381c2106020421039586603542c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 845953309 1250 845952059 845952073
    0xa060e0103060f15061e050903120d1103010609061115040605090f030306060d09050c030f0d110721050705090a06030c090509210403020301020f030108061302060f0a0e030609 77
    0x10541c00c03126041d030f80c080482c0c004c14003008595800144000c0c076800300000c801d00d4560004085d212400381c180600e9040c02008140001141d40740d014140912489800344802d142180c00d50303110f848207005100016410000a0008600410000112001c90740032141103030b085203c5030400460554085640036150341c28000440c01c01c10400c0c83c2e034010480514558202031001071140d00c40d00c505000c10320307182d140360401d1190a0241c214070300c1d0061b00395088a40c220840301c5e290f101c0000d00001255038045200c00b2024001001019140100d1503480c149003039010300f01640b06410700c1201e0f070b8442c00c08003043d181c644ea4840c038081c3c90500030111700325086240403807841c00c0c03039000740140500d01400c210039600001010403044d00e030503100380c61100400e528200306100396000690190700001d040440114210f00450491345400c5c240c03011512052900c0a05152504001c0d50010007845000c2c04010150700820900d5000d0810340041c01d42c4102090400c10222150348098010300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 845954559 1250 845953309 845953331
    0x21070503030709031511091e040504031e0c03081b16060e0d080c070f030221130b0c1b010e0312074d181006020f030f030a060e010306 59
    0x8001743d805912040b5003446192110200c020a6003d010742480c4907000031184014030a22150b1100e40c48403020b40107008920701403d014000c0340105d980d400580320121301916070f182c4103954544001c2c0d85683e40300c40646407500c0349801000351600740030000c1010460801036403524000c8203c0e25100700004a07845120200050410100781105400d101d011010001840c1c8200111f4821650003000084400010b0804034034100040d001c249080201c01a5904405580f0002e80210601488104801d40d181e071190b090a010307461080e0900d5100349101c0741d01170280800f8a1481d0018540090465000000a8540381249106200881c80001d41609003c070b5806620203c00000910320000c042c02410440d00302c0407000c1110030314002c80d40500300ca410f90303001c003409514010040c000c40034411012031605181038034851200c0070705070300001c4d4003030012410310320901c100c1000e941030000d1b0714207a10302e9902c000c01010800f40c0d24180498203940700c80d0054040c50282c41c0000c3c04112103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 845955809 1250 845954559 845954573
    0xe1207091a030105180f280302031611030d09231c031701050409031704170c030d061a040302190302040615030513020d0f020a0b0a1106060a05032107050303070903 72
    0x103060101b160003044490742401d01c1d4034a2554000380d1046289590091400e049055001d5200c034940c400c1d0001d88010144450422107400c0c04404805035a80aa907811060301c0d42121403040b0959000c040504509100000502c0485a00d0103030940382481290320b1901010a400c20302103000c203a42102d001c40300c1d80c0507203419000d410151410000e1808685010f0984900c4103800200c0c00240c200040c1000b1207a1003400013040414509901c038102a0a240e8803500040f4118081d1341c03404100048901009240070303020409001e410789454296002d03c4024041210101e00100d5000c00010050700c0d24400d080c000c0c807031035000d2140c040807420000c0958001810288100e15082c82c00000750380c030303103a07032184441d0310210003072000c2114404070351103002d0b0b98404d8003c40c0001c102405501d03000086840d18000c90b10a4440a07511841082641900d9014480d00342d8800352078001079a500c4010002c046019402041c00d01d0f1480d0385152540d841101d503400002c1205504008000103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 845957059 1250 845955809 845955823
    0x5060c0d050a06060c0803040c05031204210b0a0c020307080f190807080a0b030109120207090b1f080415020a02071502031c05070e0604080604030e1207091a03010518 73
    0x2141e40500c03d080c50402d00901121220700c0240460400101080030440c0024100000340f04c040d0585402c94540c1e81030810340e0300540302d41da03801016250a0704540750102040c0c82034643c480303440201d90f2196041c82006120021400c41907103c10040340c1d000c120802c016040c000140b0b90300659a1140342e9101d1006244202c01c4000d001c220414801c41c2c0d80c1060005601400c2c0f102c0000d807404002c00080e0142c00e48410141003104243d18458001d5408500c030001d980c82e04901707010009482c6d0901448002139000010b0389080c9408803240d082c4140c400580060003400d4031103042a003462484101da0284081d000541d21254041051200000b5500907480b40390028501300718004513062200340310301e940c8848903581d5100044009025900403c00e104000e0100d41d207540d02e6040155848100b510142c0c04201c0d07018080c601480c110846813140640c8501904d00180b6102d50075026201410910880070950581d50403252000d110300c621038128180501c01c100c0d00d0462160620300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 845958309 1250 845957059 845957071
    0x17031209030a080c0c3a1704020f0109030b070804030207080f0a0602070206041806080d050a0f0c0201120f020309010e0706090b0d0902040f1e181b0305010608030403030e0d02012a05060c0d05 84
    0x1c44007502c440035401c1c1020055225030152b600003a000314440049840722040d0308000c0c885454841072184960340900210701c02c83c425002c85284135181c4100319964a1900c1c0c04200c60b50204401c400043c088c0d401924500e44068081400c2549460810700840c400b0a400d1a2a5984003001c00104003b045031180da0107203820410300c0c00600b43d50042504903001c28080500520241c5001107901c6020554228500ca4204102003281c43c9004c0300a5802075a0b141c50343d60a11205a03034012010401c80201d940944a040038240303042908035042e0046801e80301050360b218292070150300e40303008a0f5a21224601c0000c1c00600340001c000c075068201c403504811070b1511216072800d800000740c003003440b90088062003420910903404d94000d00607400040503542444c4000800400010250094a1003520380103001c2210900f40000f80c420b190000e4001032101c080e100700383c00c1d5001d4071904d00f50b502d0000b10200000340c4905103443e80950f0b81c00441c500001ea0885c01802c0e40c481c06411075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 845959559 1250 845958309 845958317
    0x10020a05151e090a02040c09050f060c0307030f1211040305160810090602091009050126060103050a0b1f1206080d0807050417031209030a080c0c3a 65
    0x104150904000b801040c11100304065004408110040b004102440303406034020001d00842400c01d100402c81410780c807903107010300079290121006141c85030035a5a0300b0345240042d81441000e4800319041d558403c12081842484084080001d00d540900c03041c0c0c003040803e160fa22440c51510b0392500d481c450900d074941007846810311941d140450b03503807440c500c0114085244801810000000d124041c80290b1140310340c805902caa9070070074002c104a44098076481030344a121001407100d90b461040720240640400d00050841d0f01a03032003035400000c044800179480552502240041c170700d02d04007031560395581d400341040903400501b034908610000d000b400458545050150740381da0420720b00003440311500024000300e01c140150740c003c14101040740c61130402020460f403203071700164505e003a2000e00400540d52840c0042210490821580e40c00303005da8072255440029084511594110300903144580c0d5010a03980b40500e0103900d03074069400243c40c410500c5a1107103600480d1042c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 845960809 1250 845959559 845959561
    0x30c170a1101030e03270a120528020402070605060a08010204062c031501080d0e01021f06180f0c03090b040602030a090b18071a07080c0c10020a0515 66
    0x20741900c20850380c02001c1c28045a00c4811071919811406a10807444c05c41d150922808200c1201c41201c004d904015900d02c40c007103032202c101000303c640620025000303911548220540b070460341d40e00100c031061040550004034007640041c040e1b90101c8400d641160301c6d0b40611000707180c43c0740c1680040c0700c4075000318a014500803000e000c1d01801d40c0005002d11051181124030540005000c5c0020001415500d44146030100401010801c1c010300006100b0401710701d84013409041201d805400c140c0003800908035a0034210302c0840e1009820510039101c82d000145da480301003070b240000842d507a01203000500c4d80c841c5404c841c100c0c0e90160806040c035039142e002c21003140400b601305421820140e80ca941d20001d21001e0000c4210003015079002100704400d0703007600340e10001030940680035503000640d165501c001441d111052810003d0003001817500080e0288010420089007078251800d4102810000d607007048105c030800c0240c4c108002a2040203000c1c4070389140254007002203005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 845962059 1250 845960809 845960813
    0xd050c030403170108070b0f04030c080d0305061801152c01020c04060b04060518030703080414220f090b0c0408060a021204020f011107260705031504031107030c170a 73
    0x246d404280300e81501c641c8000740c040303034901c111004c95001c1c5d60031041c0c2c800c08a656040076a610040481e043d0006850700c00496044d2505148808a810108190980300c0e401c14421240c9030f000c048000c02130004100c2d000b0340c4106540c8000000c1d903242905045c1502003040064100071155514502c51440c000043c03140b2092041501c065414030b02e807150316404922004402c18102003d8030303925200e10302001007040030780c600074000e80e0500c0b0864140404c80704140501c0444490308001218050f1a02d158120708543c0110210700344c0032404241038150713480ba0401e5020a8600240c2c0040c00101400380c80703020491542c01c0010a54110300e8800d101d14410010000030700028031400306507400442a038072810380d07280410240f0f002c0d15042a5a445517112610041843c880380d85010401b030840103201061002c02c81c0c0020303020f449128503030418a644610014001c9042c418a40c0c18600c00080030405103014501c00c03030501855070300300b1440c031300c0348440003440c05190782c841c01034240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 845963309 1250 845962059 845962063
    0xb0c0405130513030f09030506040b06040e03210601090302060f040603111801121407030b0a1e03060b030a0503040603150e150d030201111c140c07170d050c030403170108 75
    0xc030311a0581741420700c0c8210014220740e500c195502c043c0462080d2000d00040c020301d400310340e0041c9002c460412050078481803681e01e038041d039502c5c5050070711070b109640b0014200031000343d402201417502e0002140c0f25030000720140c00c030302d4440307121800216040c0207640d014428100071010407da0300b401c05003416507150708d030351121314010304100207500c0c2d00420101640002c00c4042ca411603442d901e00d03040500030005c3c08940d058911810088800003100c950302c01c0c0c903000d110300c8600700d01903170390541e240c0501601401010607014420702003810042481407001e4405010160b0b80420b4000b29603882c2000f0003c0c94004a8848440c1418025400c40c40348201c08810001c0d248144060a079040c16401025021002c1f180c0c1e01002840b010000188204940203d01d1510100042c400c65200f000360b89400301e8448000c0c0d0010052071010400d811840d109040000e00b440380790500c0030740c901058401c1030b01e00d694030f128040140010540c00604540150059042c000c040b0342c58001159 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 845964559 1250 845963309 845963341
    0x60d02090406022a0f070f141903020301020309030d05010f06050d0506010e0a1d18060106140403060f0509011802010503150d0228090501081b0d0b0c04051305 70
    0x2003080d0740c0003941d40b140d6400b0003010203910343d45101c850400e0303041c0c8180740e864117029218840703180640c01e00072407603020404c81d000c207440e00c440701140660a03180c103100040403000544070740d1201c1001c000005a809000641c815603000001d983c9503003c90041c0701c00c0e508181c0050703100c001500e1050118990200903101980d20b040008502520b41e134005a6800744062102c2d600920f8070034000c180705030420119240c001d4150340d0415a556441c485c0840e0440d902e11000e50350700b040004104d503d00c40c04441507408505907000d031425a0700d42e211421100c01501d410043d54a68040000c040300a1280086003132901c45105907207000d55000070410710008100c0038401480e00704102d80f9455007102c2c03011040d409004c800c004038000e00d071000545058202003a04419540001c951074410380503d030b049070000030090541c400c0300301d0043c158010366180aa00102d10076412030107e0010540d10b8090522012002da45500300003d002c403ca6000d00703480c00c01403c02003801980150305140c9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 845965809 1250 845964559 845964563
    0x30203090904030c02031e0f0102040f1a2101030c08010b010804031803050102040803070b070c030503011203210915020a050904050c0715020301091413152012060d020904 75
    0x801c100341c0d194035080c0c1c1d4042c103900c13001e50548a808000404420301c084042c140120309005c41e0481da6a965175107090344218090300b000081403032020869084105003104000708442c19841c1000c0c0d8424181c1c40000006040c0c422040e0404010824400ca0343e44007005840280028044030307600c0310019008d4040644020200aa40c0702c048030038035807041c01000590782c424001c0d0b40e15569415459074039080400141da05060700346c0850750503070080c600d2001155041d01c0e11402c2da032915425801410340c0450603403d101c0d100b0010210784c1d22246555114070b101200024020400b41860704101c0201d50111224074810803407a86495044400d44000c0801202e01203070036521850182c10601601a004240c02105083c4d00111000c03600954140c860b004002c01081e5101345c00c00300c002c0c5054422890388a07000c031000c00032418507200010f94020b000804100c040f07040e0b66000f034090b85040400030700b01011403070016090000150640150084400c014441019000106181000703000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 845967059 1250 845965809 845965819
    0x7090e06062a010e0d120e01050702060a0c03090b040f061a030a060209030c0307030f1106091315080f0d0806060702030d120915020909160e0118030c03050d0906050703020309 77
    0x1e01e54402c002500840d8481c290705060320380740030503150090801038641d4072500e940c40c1414044820002d0500c50140301d18000d0740105030580b100c0210a00400d00013062804040e00c0300c40d00c0011070b0340d40015034081c40c800d510f00c42c490704d20f900301101110026240920400074107041c440983c1c1d00080c280c02d1302500b00384010b82d01c9115100180c03804410440345034060043c280300000f03020b204808103002e24042c6114a4881c1034203c2000961b204420307500b50710141c002e041406181c226404550300090030381c1c07801c182c1c94130f820300a03103051a04500008181d0011402d041000d0344003083c55007006040d9019800c0c02c074140c0c00681c580d02c41200704410410300d0703520708400500036040310000d00e41009080c000b00d45200c0d090006580107002c6603002d094030401180280044c0720421184248580d2440d54940c041c0b80111100300c07a806443d074607101c51341d07000302c04603c09020f0b140045200e900180541200f0366409440000d440d4801d0381406000e00200002c42c0d004000c0f0b0f503030400100d40f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 845968309 1250 845967059 845967127
    0xf090c060a030e010c02010203100b040302010c150f06090c020d1706010c0804090e0304170312040219081005060f0108010e2a0a020f1621170307090e0606 68
    0x7003200149030800c191030040d07081445c1401c02680650045005224828034a0b40d225100c4a41514070f1045102c0280020000d80341e1f5004141011510811a8580c44000c1060300b003085903401914155042003030340568510141000c40c0d0104165400443e460800b0b51621129540c158207441001b8001030512002c11a40d108201029085802034800a8000c00024248851480c1c0c2d9802078012202c6e034404480082448120000540d411502120780d5602d080e41c40340c1c203010114603050180450070303c1c41e19010400350720500146545154250000030b40f490104108166039002c0c80c44d590610440b900107006607840800c400383e0111003440c101e060802c1220490444107032842800f20355820105143d40c034a6400b2402c02400f901e00012541e240303100b0112008200310a108856901002d10f1907068000e420100c50800303d400f0389024a1700b4101348807298840d9200720780b0000066000718081c0b1001080195668004200351240740c01c000303141704041007a400e107501d40664550191 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 845969559 1250 845968309 845968327
    0x212010204030c120b0c18010c080405040908181c0f39051905011202040e040b0403110a0b06040e0709020a0207081e030a14070c0f06080f090c06 64
    0x50100d400070366000481e80c2c10a40c2d2000a07644c02e2201842c1195030f641c0c18070104117062410310075961140d1507148025002d8a4400c01511404000c1070b08955049007480005107a540d58072404c882c05020b4104a9600c50540c500c507480b080041c04828804c09807180d400443d41c41c82c01d4000d2010380c1c041000032a0040030708080151450f03241c0380489544070150451025802d64000c00b1410224512440d40741c0e4030b860420200020303151506280001d28034040006603c24981d408001c101108014038154075010300c08195002100c00b0b0380c8020a0b0814401010340c81500c1101c4210300a02900c40d004541d03441c440035140242907184295111200403107400014024a4020320542c04115a1400b8003071010f91a54220f01c141c107140c0c0920451b13094805440c41140101440d440091840c2000c4000140c9a11400c80c2c2c0d1460420810700450340022008449200640260700a010000c0e03e4407100500c0c0141c000d041d11041c441c1c09040c0000c284000030705040c5a40210303022034542d4440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 845970809 1250 845969559 845969561
    0x106080903040504020307050a230d09080d0c050703110303060604031118190c050f0403061e0c09210c0b0c010f0f0603050f0304030b0a05190504150f0c0507021201 72
    0x90f030005540144000300f404200b0303030403000800c8003c40301d880740741c0711030103011480d4000d0100e012080d801107820803012001d62040d0380310018440c89030b0001c90602c0c03044803808045881940c602004580c001031a01e0074182c00c014016030b84003452004516500e00200401d81d00c0c016880000c050080c0245400002d980d41e1200742966070041005018502d08184c4044040340e01c232903841e0701c0700d1030700701017442c601d108008991b4080c100303514051406103035a03104001411108040d0314102040000c640c42018140102c010769400382d920101c45606000c010100d01300b071a4003c0411741e60303004185000581c8120440c00f00c07503401c1d95441d103c588180c3c1a50140c094180c201c0c0308076203400c11146114906502c0390041e80e0043c012208211400c6404940c1c81c410b82c0005401341d814800010f1902c0c6049d000103034800d00d01004003091350f400c004828255107007918110341149404454454802440c810640d923001400414000b0003c02080500b06224005020340039140c0d60058903989402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 845972059 1250 845970809 845970817
    0x3050601171b04060b030709091d060f0402120f060f01050a060e280902071403120a20211b0d151d0114060315131e15090507080106080903 61
    0x40410617a60b686450040248585a01d000300b1000520f0044403540440c0e0076444085240a44c1000308007d456145005491070300050080f030703010094482601418400b800303042c5000c01d1a6004020702c1c10180d0680c100200d058000f1401140001410000c0d1a4060410061404113807842e07600710382e0024030391200702984481e400c0c6400d084040040c2080459005000c1240242d106400003150005095242c2c07041c0d40a8414015864004c50302141007a4041038003101c08100a081d9038021209081c01d0350042002162142240000e42d020048aa4003d035441442500081181300031010603403214010f1400200d0126520150410200c55290300030b00500404005881c903000f0108042106600901071801d0f00700544201c0c1d04681064816240110041e0022920300c800c2c541c2841414154481104007094403800d0803650300720441d00036002c0c0500558042141c05013100321750701c0e83c8410340c451b80c0d204d4a804100280380d81e208110750b0540b04580303040310b83c0c0d0f110000782c1491401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 845973309 1250 845972059 845972069
    0x1140c010e010509070816060905120316030f03150e010902160f050105011a03010b040e0405010b10030b01021e0c01030b0118060207060e0418031110090b0103050601171b0406 77
    0x310f41400d103c0444e10026140b401c41c2e490780122545558400351a42c02c00a0340e2148801080b1f500000344503614286265158080e1500d04403802c2011004403005403080e42c1d9016000325105e03229044506905002c1e400c000000c0010806c0742c04c1c54194184036201d0144100d220040d1701055204040701300c80190004a42c1045140d030308001d0605005d03000704003c0c07281c0942c03406018400340300b01540e8025207048518400c030f69820b00307240c19080341420270018422151956200340d0310500d030b5105c0c007400e5203084090f980041c81c804d07510000381c5040c101d4002883c01c1c1c9400d018202940600191050f0382d14020310300030511726030b0100140d4152921120100c0105034868021a07010341c0025400125000c03075640640442016060104036032900c1e110f05007040303400c0c4c50100482e001e11400391404440d401120307010b8610b072807140222000d4083c101c4100b80382500410502c20100422400742c40344400c1d071164100b00038607072a0340d240b400d0041035500200c03114424440e80ca55002c440101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 845974559 1250 845973309 845973311
    0x40b0d201201020406020c030f0723060309010b01200601031205070507091b1b0303050403052203020907020c0117250509030106090c0c06021b0316031d01140c010e01 73
    0x410310201c0034003035081409020014455000e04200600d00090340c68000140e081c0500b13112824203078094140030521440c4484030310150710142d0321b5120500158410f00f0220000a80034907003100042070a002d00b046454040b5080301d00150300d070f1740403071035a044035803211260001c2401040160340c02d01030f98a02404034000d0003800101d10119400202c2f405d2100e00f9000d41c0310070b21150650301e250f1081074034501004d1901500300040c0c00381c3e10058002c1e000e400c04a0605070103850400010814804c40000c102e905d640410071410300c51080340c3c101c41240060001030ba40700000070215150030000b10300d03822000e00400c480801104e41703000c034005840040020013034448806440f550010140a000e50328005000490f007880b4810300560003181d5448030307051040b944500020390084000c200003004070503850100c2250820003007000340f040a0300384400c8a4541400b41c06a001183c8136072407c4074250909a0903a8002c44922101074a4010b098603030802d116900d00502402c1762816042d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 845975809 1250 845974559 845974579
    0x2070f0b040f05070501090b1b1006060e04151202010f1707110c0a06080109020901110307030807110d021f1d030306041a0312070f060f0b040b040b0d20 67
    0x1010007800026981801201110b904d550340e8001100e0195140c070404942d00010301100003006104110440a485410100c48024092420000c101c070555844140860310b4015240401d003401c0c0103600481300b03185001441f062900c058001e4044c04010001e0401c490003590b103141600401d404401050600c5480f4910301d400040074009105101908010b8410790110803400c6c982244003d0070344013944d55800403a4a8460380d04041c1d009800258140701907008900100b4000b0030191081c180207075203c1409080c81b0380003800b080e002d0101003203030340c015160300e0880d03d400045c00701d078040018860410741c0000180b120001c12070364a00300c81009401c8800c0800900000195000b00c0c0110744c10000c101c00005a1034448400c800b885400d500050300f9071010500580180107880d008003c00760300010581e8440046640c075150210400e40d07281c81c1d03030f0407505207445446540d03442601d04000201240c0b0000710310803400d0340020300000c900001c01484807403000c00c4200c2c1d940040c1011004c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 845977059 1250 845975809 845975813
    0x2010c17040e0a0608030c070e15090a02030f01051f05090a090e0a03180e06090717010807080d17040f05030405100305040b061f11030417010c0810050105040902070f0b04 75
    0x1c42401c3da0748881c4207080c01d00c00300f00a02c0200072a950303401220300815031107180020100200d500108860042e2507040d81501041c1c07160700446101c2c641541005035645845800140802d0381038024a001d5440400700c0b820f4a03407013601a880c203980c030782000c07500c802e200c0340065900c10482e000801c00d2414100341c0300c42ea0745d000a010341180c1c8a130b115200c00d05e900b5205401d0401c000e00c52030700c078010011b000c50580e0030082c0401e5000350840c07400a00d50300106460084141080c0d012070310395132241908019881041c04407c6807900c0e285030080b01905222030310400100080e0001d0040700402d480c01c801c021040089400a2401400f248445864500c001d030041804690036561500d011001030014a411440c007210040c1610040e0680441c6040848141c5821800c0007000d00c010000403420340c6261031640406020003001107125980060014410324000e4003031103c4c00c04040007031005a0300102620151404801c0058891240c2d0070000d0010000100c01340c0f01680b00d03414082 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 845978309 1250 845977059 845977079
    0x10140402040b060c0a2004020406111603080d0f06080f0106090b0f0a180b151902060f160201090b180607021504020909010e100c120203040f02010c1704 67
    0x44114021070303080002a02840601080d8400e1542e4040d20360082d1580c040080c1e1942540b58101a1880413825241c0202c008a02260701940140005c1000101e030304480b00b508100412140e01e00709011020146159901070b050301561490001c4181c460140c0310490440381d00103401070178804116005000490702c481d00070480307800b40b010f240c0c0c2882780652040c1000e46285003a00d0f0003900f4004e0307140c0703002e15681d00c0b030a004000c5c20415459a0b21200035684400d0070071700c2c40098120199039401580d1034101c030302a00340100c4041d50405010400c5000690091640c0701d84070280417440c41d000144103d0040041010040c1441200024045100440c0c0e202640f40f118038011075607140c842d5001039035603100b0244400302510f903400018005046c040e2035107820009210000c03480814401c8880d00f429401c610402d8510347e20f20302c03540800c1e4000740d40700b01120300000c11480c6043c1502d45080d58840110042e0501c004400400100213035105100c1001003401c0b060b03515a900c40480003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 845979559 1250 845978309 845978311
    0x50c030117120702010e12030d050610030b030c010f03111315020604050718061d0a0f0e070302150c0703060b0414190c020c030f0c0307080a03201014 66
    0x100110000e440350046000001945040880400c08903810002c0c942c4c01150041e08420f1215000242c40f2840c00403207070100040d110441c006800462075207424000d11010342031040c0d4050030035007815050929910301140c80c03c54400b00383780c89010100d520360154080d151802110b0342ca1580040d200340c07440507011039076007a01e0307900101c00a160344025040f82d5610080e1406003483d000205c2c20006521880c483c00f1503154100c0c00404c24580d01c51803106ca01134820440c04105d0100b004020562099100302ca00c503c151103802c12400504601a6580c3ca030103002c001e02640840200d500c06002c104140ca10721040d02c8210340055860f482e0400113410501c45070f034000d504000120f0041d543c0c84417a248a540b0012022a4448485200201802100c5100e6042d4000c100d885c00407503c0c180203018125088000410070350244000f81480c1c08140d80c0044903603044500d900340001e500021000e1500001400e100242004c259030382d0a117001555401c41007442c00b0101111807004504003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 845980809 1250 845979559 845979569
    0x1908040209010503070f0b03060109090507020c090603061b1c0612030206090303011410090f0603090b010819082104060e0606040605010e040e0c04060b0c1209010927050c0301 77
    0x66407803079076180c060561340c50050103a0700302d40340900030520400385800099584444140740c084003280d582c803c2d4500b1200c0070355414006030003281080140e41014444907420030802e600414091511440065150113544071003d041030300041c00020f810881441c0c07010409114408000555442c02c1501103000d1503a411009809017000084d205203020007501c0c1210540b038000411690800d00300104141c40f1202c250910040020101e0b40d8450b0003000c001034130054600190b20001818410000750050b44031000702e501c03050f5040b010245400490b90340941c031401c0c050700d038010410b84288026a403044141c41d00340b0030741004244a442e0300034240140740d10064035010f888000a0005641c413600405001c1403071a0245001800c0c241c1c40224903104401c00c0da01c06a51240004050303582e00d5010318015034000c203d180d44a10103101e142d2181004038082441d090b2a00006014036103580300b5201c2526070000c1e0861107012020700c801070b528250308204158900340d00d000410760428011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 845982059 1250 845980809 845980819
    0x1208010317090d0f05031b010b01030e01060f05010302090612070c060c361703040305070f30020402030a0e070602031c1107020303070312140c07061119080402 70
    0x7401c008104481200d10208001e05050100f03503281e1110108260040e40c111540c0c442000030b40e01500c2006041c00e46007104c4030000c198400c0314800101a01c0403540400b070541d1502808201c003a003140034100440d0420300700903880b901c01c140010818025003603048109010360041244459204c4003046403140f0400d0100218180a04201c4080100c0506205500e150038840c1d4000c10503283e440c00c00703900c0340e1142e00184c3d885030749184a0034602449052580e0011606104118090048501614003800840c210a2074520b8131005000d0910000740040c1840c5c0a280004100f0b08241d9005a005001903540c0e007015033581e130081003030711020902c50080040104c0c0680c40801111408000e020384160a5442507455100600452803141880c1c1cac0708011540040e1028406490418040c0c3c407805e012910010085041e6034041030500b60050b10303034041000384400081a0388107130b500103000080080ca505174078080c51050218691088018005500402e5030000803284514801e80d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 845983309 1250 845982059 845982083
    0x911061204150b010c0b0612070b192102091f11150106020c01080921030108010c0306050618150d0f11030601051905040506040b090f010f020c040c0c12080103 70
    0x80502e0840b5041c400d000e00145d059010540459454140c403500302d840140000d201c1c01c2c081c85007a10b001d8207680070210510000c14821248039154950720701000142c101945208500350243d241e4105840704c01050790b6011561812076222001010162010142d070a1440c0482c00005007100d182e50000070040e10036044124a00e40d018810a8100c0d82d80390020100c0d00c1e005030054492120007890307440c1c036200340350748828590203414540c004900c0006107203543e541403450355800c0d07a01d0b080b03c01c03040c1800c04d032041240381c0742c7c48110381d60307c002d201042c0086030210000900400d03910345203c880003400315142c491462103a00ca045200b070084810020313050308000c0c481860004803404e0317000c25400e0240c00404030f104291000261064500680f90030f485200041c0d05800c141c0002d00c203c1c0020800310311605050003040384140c02402d101c200c520016400035a1010072008580c003541d121b03031240400c2c0d409129841401540801c12682103203440c0c03801410103909200a1722440c0c0d03001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 845984559 1250 845983309 845983343
    0x12060e010e03030c07170301120c0801090507060c05030d0504080d0605011b06110c0a06140c070213020c1914150903090409020d051c020d0201020408060a0911061204 73
    0x101c01c4000e80e0031154055400e41da01c04103081030390f41041c503040d510300071000200c46940070407000640c040d10290380d1120064002e0300381041400c1c040d0300402c0d1242c1c5007000b10b0001c2000040c000e01180c0341498050024107040c80c009045003d180d20605004d81000d060008000c00d0001030404030541181c01c05c5015540c1004445c4090685200c0d0102c2d403a0b542d0b0400030030a5600a05443d003c40304510345000015001c0c3e500d0140c43c03180030f44015680d981c002004ca800101e5031038010489403c03031414404141c00150484030038a1100044c5940058a407448180c280000b800b2503c10029100002000d0f00702040021002c0c2c10660300c500621207541403900c44070700068007a0310303210021810324030307000305100003000c02c1401a0b91105031540041d00113101082080c035031540c40781c2840b0740800b86001c0a4030f80902d80e140b1105590050005201301580040c000340d0003040c9003008509e007a034a0402c0c9a00401c5400c200d40c002ca4009080810080c2c00c0003428020f501c110203840388003c0f45 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 845985809 1250 845984559 845984561
    0x42313060b0415450506090910050a031a0a050108030d09051609090501051503031602060c1c180e0402011215090c140c0601061101060e0112060e01 65
    0x207000da0300ca0306000307100078854800030407103c41c904001410b240c0082e800c400030308203c0070b03883d21002800038404041900041c00c1c403030306003105440001146020743d06142c0000c0c0c2c2401003c0f440d41c01003010000244201d85190244d100411000e400014825101d0810b10108941034120300b90300002071002c1034018005104050480e0300000143d82805011036640000c1c2652200c00d0380c0c40d20510f070000d140744400104d04001414020800140140c072032030040d0075194010200199003028030388682560324084110f94074a1540c011032180a0034500c00a10240200c1082c00300302e10550380d00c400038403040c880201c44a90151140d800b05104c180241030321071810301500031000d00d0500400c3c01540038a00058100b03103202c40c08180c4248c1010304002421541c1d0020b103c95845a06131403085821501191600760240352a5160002e401d80035507441c2c4c4103200704403c11030b51082018040300203500c401e0282005a10b1840b5039603541c07040d86a0b043d544202604d00a1508100031205441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 845987059 1250 845985809 845985821
    0xc07060b0a080a020d1b060e030607020d0801150504150504030c170d110a0204090305040906090504210210020705060f011e150e091614030f0f0606042313 68
    0xb0700800506003107900744812044049405c4030b1444404e01c1000c070b940078241d43c140107030155030351320f1074141002806c1614002c4040d089400b1740d00b0500680801d685d00c450058152485611031402c07120711a0700885a81c030895025503854025900c5520354540d002f801403044a01070100642d000d0b460b239440c0103140401d204a2203481e070146165003070b868091048c08600690715426582401c4840e00807405413030304414101e00080f0b0000701480101c00030f119034800340102d01802c102d5882e095455002c0c0d850003c41714182030038544071400001d4400c010300030710000c5041d82903480710240d24106541c0e80003035503103465511100001040900000c83d1a0310400e507040203400340e00b40340450740c001a035441001c000804c030180c1c022110503112201b5607806220295907540140900b15001000300058221306180000c0400c180705020030b03641d00e0140c001c6038182c1252259200c0400048503880307030341e011100020782d400d029601e084d030089881202c80d40c182c0d64181686c500030751050071181c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 845988309 1250 845987059 845987069
    0x80c0304051e3604020103231b070302030403110303070804030c0503010b09070f0806120106030521040305070608130c06030b03010b0f100c02040f0e060a0b01080106090302010e0a0e0c07060b0a 85
    0x92600ca210365519120f003142c98006006040001e1a01d644c2204880001a049a0701116010180511114603208540c56050300207901c0710740e05114240e82c000303480c0d100d5480090502003141d82016055034052085810159201c1d0043c0d0381e8550f6840c080780074200c2072054510a501e407000c80001800c110314224401e00c6c46a4900c0c02c0181e100303409035580800a410280c0040740342d1100d0540c03120900c1220080c2d80030303070001c204800f0b5882c2c003101094070700392410982c0725080c842003000a0001a589013030310740c41e082c079100b00c2c1d5520905844108101c000500842e512a00004106405900200707041000354001e000089007001445802d0b11942807684c0c228080220044506214103681e2007203600c000c0020030024100c4808400351000794610003540d0304658248868515103205000200b4001c1c244031500390b00d0010058520145440040e040c0007040e41804103941d542c2c0d6192014000f0350034000c00b1810b207203441c5079040c1c108010448045160241c1081103160500c15078007116 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 845989559 1250 845988309 845988379
    0x606030c05160c0e0718050d0b07050319151d01050618041103161e02070504020a020a0c0806070e040902090105100915020c0922080c0304051e 63
    0x4034110496080b030188031006860300050158045440c0807500351460103600305075510401d124160016007980c00740e6900c5944100f91118000c2c000600400c84181d000b45603051694403955014101040401610300840c1c640380313041d2200260796441c00c00202954880c254026004104030a0404030f0782c070a014940c0d0005040c001c800e1200342c5100c2203030031003c015101040510101403100701682050760400081002000348021065002e070f90b8146060102e0841c03070f01003481c524060740310203130380c05a48e0059800190079050b4a0007040000443d40d4890070482c42c00350355a02d1240c503801d0503950b200000b04000407010307040c580390050102c1c0b01d400421807807551340381800308141c0100003181c0c86c0600c5015600021400007403242805e0040045d0082e04400d080030040080403400140804c0c0710740303441c061074136003004400d0b1200e0070a5130220b100c6a603080410b411902c0d5002d10761000b0341c48001c1050b0b6900303a100b031901010f50301c0425200d850b1201400384038260b01c02070304e031a0b80c4001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 845990809 1250 845989559 845989567
    0xd0b09100b0a05041814160516020d0b040b0906060d051213080307030807080a052214030f21040203030d020f07020607231b1e040603150606030c05 65
    0x1c480c8880100300d8080320f0300740585001da480c400302d500074403001607400509076509030b10046184500501e07648010740340c1d03402c0450655103d01a0aa00810b01da0820b0004e00642d40021500d03141e01a040960300214a0b40541c60503141070100345004554034800c5014100110b9541d040110600400b10b078450050456203d005495035050f4111078140f4480c04a183e50010f880b10081c0300501146000740d4485900303240c01e9402411381c9038054802002285001c0410002d403900f610700c01c000200c0d18242003008480d034202984c0d25540c2c0c0d0b000c80400e000000320040b807402c011000f40544a800030b14040504107803203212013201c208a50103500340e082005603200001050b4020603074810b91805803810b1907002d8002c00c4054020950440d00c0032141160350300c51050203410100a1503801c0c0050104a01b038001c2000701c0000b460840d03010310303850021160780c14454070100502100240c802c000e020764030b05014000710540780801c0000c3c3e10341500400d546100c0d001d05460703108991625854 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 845992059 1250 845990809 845990819
    0x1b0306030d0e1c0c090c0e0607151104170c06030702060609070504030506190f060609060e030f0f0d09061806141927141915050d0b0910 60
    0x11009412140b648090508605404a42c0210503219a140207400008199040c1031622085500c803046e06014070040c20b42144459403041c2c01c9072022640502c180c00f5504d04100101c0c050020400a548075400205010411b04514144c106040500340c00311010403040f03506100c180d100c29100500103030048800a5400d0802404040e0040001d1a056140c030f0f580c1d40300c103400c00c04150340008024209504080c140a07140c02100c049204a4000300101448c1100103801000c40748118018424450496000c695052064281e07030350300d00090b15030002207624800c0d260f01c1c0300c402c40d03404900301e9507020880c1807044c03608266800f4540d036151842e5007041002c0d03540003071300c002600076101304000c400304410300f0101d4250018080c5d1601c101c015001000c07498085102d5182040c21008000200100c240e100d060800340502a00e0b031400208413089682014002c680120807108000782e21882c480b0f500c034004050181c8548030130044000300c40204590701506a5020140e9160880207001d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 845993309 1250 845992059 845992067
    0xe1006030b090103110d0b090c010f02030a0e1309080304111807142a06060102070611060a020d0e0f030a0305061804030315090e101808070f030e15031b0306030d 71
    0x1510001b04500e4503103625a40320742804008030782994554018110582003560004510340c0900d207103001443c1081c0707080000910104001d105544508804040d282d5190004e80c000810349401280700340c1d0384c4c0707081d0401004074101c448005001301000c44400a65004810319640204290382e00c48450704400d500301c21681d0010300c50498804100c0382c0070144200c100c800d2100c10381c6a41c010f808649814000641022215844803051206994982c0981da501007000e69108504000058a5215207070003003005125524281c0780c14412078829501008001015140043c07150350103010700c0d9901070a006054109407400c2d050350f8600030108002070f0094016580790b0058001008009075540d000205544c4800e07890707440703900b041441d4401c2d1001c0303008525240a0101021064001030b6645500920031340318060596107020402c1810544035413054452808014000c07940d0050448100040350b00039104a076002c04208110721045014000740ca10031a4010041c185e4502084401e907 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 845994559 1250 845993309 845993333
    0x60609040b041106160506150a0b0406050f0912030304060e01090305040605070f0b132001020d050d0609090c0806090c060307030b0103150b0705120708070312090209010e1006030b090103 82
    0x9500820600c05d81176500004810340e800741b4011401440c103030130900d04040840e80007440c118040c100304841804100301490481d003c0380c800780342590382d8140840444906005950344d05501180e01e4403400020b1030b001001e140214080c1c0f60402c018044400620b08862044074000c02043c801d1104124050080c0301806409000c2d9800d40743e02e40817907070360551980d030480d000d40e45010200c40b0340d0180003202090314a001036283ca101080f4642400103580c0b07072038045103070041110000308104004c40c1500306100800301c00005100601241ca008540c0e0030b120b000341e22040c46030100080d0f000340e002600300e03481100039002500d5611074000413400b41c41405061418991100700070341e002d40c1c5203c250307401030550040890311a042031034407074142414030030b203075510b03840500a1102254850302110f0000d5807608045003103044a108a00c0a410305200186d0b0180203c40001220804100300e58400c8055815151078203403103003810303811a8814003059402c03031941d03401840007900c5503510f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 845995809 1250 845994559 845994593
    0xf16020a031b061b0522080601031103070b0f04170321100b0309010c02070e090309010f0314100501080a0204030c050f0f10050d05161d19030b0603060609040b04 71
    0x41100500000500000d1198440c4040005c500040c4050100c001d4000000010103580e04c0003005450404420398441d418003019001c22640359440700c0d203580401100008140d8450001e8a8040c00ca2298281e5001481003020700400c1c442189449a008001c40b07101d442031014070304514075101000445008024140701d28084402c1002c10206600000795118058140010a090f02400c01c002d09214490b4020290685100706100d03d07454040142c2d04603010a10b81900403200c03800046024060b070b00c0c50041144c46000c140468509201c500d4016070b003084e2aa03000300e41702c0b1084142280304030312014160a07400c1a084c0141d290106111611200c0204404441c003003c81c001010039003a031600c00c01081000404c40022203490041c10fa01800603440e1420480baa140302030300d01d900145610041080303689010030103075980c4103003001d06000704410588040d00c03454000c912080a1356510b209101d240005665498518400c0f817155900c421300c078000d92070340d903120065064900c40ba = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 845997059 1250 845995809 845995811
    0x6040f1208010b030a0b061b0106091401030804170a0f051e060c0d1509060b030907080a17130b130303030f1a06130e04060203010e09060408180d020303030f16020a031b06 75
    0xc000842c408101d440e00d23001c0398030000066814030b0540c0180c1110340195259072040ca02c5070042011441d42c0082e1000c40380d60042140c241103e001074a410090301c84401464568811020414000c0004001c0c00c4030032044014039041c0406241c490b0307102001c46001419083c100540c8152031050340040003403080c030070f402403000ca4680c0d024106660307481d005a02d101728007108004004d0010441c8000910345440a80001c59140d00d40b481c04480d801e00c009421940040d01c144010310a0303560300000c0140301c000f16162032a4083d0b08144c02c107544810350010382043c0004e80c1c201d807113200c1c4107004007031080040c4080d0b0806052140b143c010f1200c4010780154448009a101c85660301907200d28407503a801a80c82d0304001038141c007180003502200c900c0d8024801c0200040000c0110750f50900038082941c1940390710300004040f04030346035000350540004400e004500031240000d5000c0d500404034141c2031400403104030303600c101080f030150014081c1c5106001000900118401c0c1d64010381c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 845998309 1250 845997059 845997067
    0xc051003020d0e03072006030a021b121b0f15090f01090c051216050609030109060e010506030d0f090603020f070503070f0c05010c17180306040f1208010b030a0b06 72
    0x2010b03800f201ca50400c0544a9003001074010101711080c40e0b48624801e102d42401d6403045188003103105800020486069154001040450780d020740c0c20390348941c0c2c20320381182d289040340700d003013100c41c0c102c41404030380d680c210f1500c2a0f0340d4002041e0500d40156038002441e64040c0c50241ca9000c400c0500802074074000d18810315504d01080c00b5031300141d80540703c1e1044480c038150901c0002a001d00c4100c180790000b021701414840c152105030201e980803280661240800800030740103040148004005500d4500308070768400064000511410086042c0c07031204043c46000d0b03034240011001d0100080d500c100910a40303000364050036107202c0201c0c2e81818400d13140d0740c60f40f455202d5042075854128140c020001c02207041c2c282c8001d0402803a00c01040344c040d55407250001d4144400c0c800003500811031b03070f00e10b50200c804540303c0b440c02002c4078501e0400d4204500c82100e204400c2d240a083c146000c070b84a4000c840b803504813403042d03d510745150350b80e400c4140108800c0d5552948044100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 845999559 1250 845998309 845998327
    0x1106040302011b02010e090c0a0f0e030303071d030a03030f0f050c220b07201c0b040503091f08060103021201030b090a20090a150b0f0405060304030806011107030c05100302 76
    0x1041c4074448c4801c100b186603907102007407000c0c00c1340003810100402c00020410318429910080142ca41040d001e013004840f25240204000c0110f2189103450303018410f41050400b0b050307240c0c00501038034492079000c00c111444500f918094400413100040d42c0360041240880440c016010401680118401000c103207885422605140e804084140c43d118155a0300d8524980500b525407030000c41110914a20700300c44000c2007030003035020800340100422100140c00d002043c82210902e0b4002040b103801145007803000c0001ca1a18656040056014030001c0c000754002e20894502000d0114109103da1840da03502524030342c0100300d541540074000d22900011441c0c8070184903005480c4038043e04041000522010040c02006404e469092a810340c0c1c01c2d030b08c00404031003940d4041d02e400c0c0c2d0301c00d100c1d410032403a8440c942c84141c00403400002c100615501000302c0b4001e03242680c48001080442e19034580d80c4145000c042c1114a004404201c40d02e0562079018084680742009402c1000704 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 846000809 1250 845999559 845999569
    0x170606030105091b031302040c0e0307060c0303020408070f08072c0402030a02090a0b100203070f0b130f06020d1d1023241e0103090201200a1106040302011b02010e 72
    0x650f0301050a0000d000c0c800d003140340034040c42705008818680450300c02c04200010350b482c2000d100c0c81041c004644900000e140c0300360111406410b65004492180390790300900901d186080c46900341034007605038040303540c03484c54801c94420282e1061941190a0b100104a052940500100d0b49071003120003c800503101c038403145119080c030b01d40c0002d40f000b186003402080100c0b81004803c40d003042110000003a40920411085600004009629500c2010000c550740140038050a2401d003407201c441003080c80c0d0020180e00111003401e10030349150300c030a4040040455840b42242d00a408950800c040c1c5502c0b031410801100c2040f8030101c1420b400500380e0000751000e1081c060b40c1070781070b24140d450006074008400140d8410b0070300151004400c8515290070141c90400d503d03410034109582c4100b84c8030302d403050300c0c0701c4000803100c06031400d5549001019089500040b80506c00103145030440c190f070101c80c1c06860b09500b002070418a06104103900ca4124144684032000100070703221 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 846002059 1250 846000809 846000811
    0x302180904030c020307080c03150a11040306021e0403080d090c050418020307050108070c1b0306420902030a020409090c06030e0118030e030f010e010c170606030105091b03 76
    0x42d484090b0001c0d90f030300500d030506401c0d0304413004582c0f202c1030803a020f490000380c04015060426584409840d9030182c04045d02e4850041700a0b1039000c6000b109208080d0b00038040034072010600d0440f0100e246207042d580c042e510000d005880e060129682e00d80300ca030031402c9518070412840d9000c545400c001012502c110030b03040b05840349080c02004600b03040008001034102420070050342d1134072141c020b000c24000440104a28840c090180b04444941c035148c02550340401f06003d1401c14110101c014460b07030505103140c00514418a480214400210340c0215072590310100c92400c003407114019500140040c859594204070003e0101c11600c5041000d504c05d54111301d8072403804200509442c01c41c000240181d140801c6030054002d030b43c46d141c120540c18140a201c040e10300c07002030b0600303002d1400800d02d9401d1070019507510703e0650014222002c182c8480044034804034090b0031408044894503004001000103016600e441038180340d2000c48000c04994124600b00700300081c1d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 846003309 1250 846002059 846002063
    0x11b060c2a0b0c04030c18020d050f09010b090106080114030f031210090b1003240303030b030d080f0c07021207063902130f090f030f1d010302180904 66
    0x11020407180400c4811140d1030340040109000a040c1811500d628800c41e0461085201d80b42c5001e040303140d01112a01520721180800030108928078160b88011420b50f400c80d031800c0c0c15468009608000e141420919058138101da4079004140c2c20009a182c0d200c050200e00c5616201d03086090b842c01c032040000b0800f440d0100c0c00d0859608025203101c1c44415a0303001a420a4149082031030f081e00d641c6c10300c050490a515000c103070509808a000141c0381d24041d9078811204181c804005c0c5034050b081320786501c405030308494031924280005c680a09003581e00103082c64480d004039400ca5101009082c1da140000d0040d52078460703c03002c1d40c0c80c2c084641d10100101c1d15410b00034180c803207198041940d100303441200101030303401c0580200140303d1100000f032113508d03018a000700c2c070196071340881d108000ca5541000700c08424100b0801c040340d100e80c214001858500321800c1603100b0b103620340040603001c81e1303807580070340480055000e504800c140c0c2c4426200b01c072032820381c0d41d103403a000780c0918 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 846004559 1250 846003309 846003377
    0x20a0f0b090a08040909050d30110d09050607030908071202160306060e0a0204081510320316270c11010b010519050310050406030305030a0b011b060c 66
    0x6d01c49261150814000480710424854038201c990404207403601c405007440ea40411a5143d8164100494024038070f038010b41e03198903000b18800da4071000b1b81e030159510700e020700d0440e40281e8905000b00d058034604e1000410005040c808940025540303d20441d01082c640140c2e480c07151803058001407481e46900c10b5844940350030003007003c02c0c04400a140c100c0c0c46220107501d40307428101c201381e651070802d1130700395101d000d0b10014111160224900015200031a02c4410f100103a041107801c03c0140310712445190724041c240021454001469681021400d0545501c50f190401030396080700c0740e9404001030702c080c2c00da16003c07103840c0c4603009180229440310320b00404400d25050031035800b100c00074103020b004c104513101c684481545080c502d6107881e041c3e40d03036544c0b00d251a404511503032019070040c2c00d1450100801d074000000d03620030b500f045030402106134800011501c804100c29401c24401e040b00480001c94000c0c1c00030307542d08000d802c0c1600901180540624605201082c80c1484 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 846005809 1250 846004559 846004571
    0x21503043e0406080f2a0a06050307020f0a1217070e0d0f060204060e12010c0804030c0320060a0e031c02070f0b04080301090606020a0f0b090a080409 66
    0x704007140807144803052100c0a00880c003a803840c0d003006034640c1c0e0050590903440c4410802590380d81c1c21040c060040312050b556054041081d440d65811500307210b800c1285550f4032003c00021a07910480301c02d0006010211031031418034152400d07070001c1c4c0390100310302850a0301da480400800903444103601c12004a400728000220080120b40c40803403030182c04000d1001d0064656110010b1000400100c40c0117800400c1d034940f00d8542101010000c1c5141d001160016120380c001c0c6d00412220019180d064ac080001c450017400c842138604060046a46030011501080c480d145004884e842414803c0008103441c8401034807503402e03002079009a200d4401c01540d060700d4029988001c50420086041c14455505e110400000c0c0c2c0e0746890140d404192001803140c5118201c2203d40c000c0a1810781e4206400c0461895009000d0000c8190514800180301480003c04001c1d0f55080300007006091215590349910b01409003020311a4401e441e02c0c00e010072100e0380108020070041c0030005030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 846007059 1250 846005809 846005813
    0x110a0807030515102c1002070602060403140f1317010207381602010b09010308070f0203010b04110c0607030c0215071e0f080f07090506030604020702150304 69
    0x2129000300503004040c00d041c180252a441d00d0605440c035801211207000012140508945801d00c0d0b178845100225203182d682c4689903003c404100340c500c00e5840c1452401301000599941c040c81c030400c1c0051f841100042c0201c2c0c0300e500c0350b9034130103800c0f542e030341c81c04c1c0071200b45100d0317070b00b2800a090404441050406c40710550003440901c03081d400c0025424801903850300310303001d40f244003c6c4858902461218000405c07110401d00000244c1030002001c0c2010720010018544500608000d58617145100002d0710b050610030707049a03800a00e15142c030341603a88182008c4d4a0701c40482e0159240e10141400381c1d01c41c019100051091550280c0f140d14800d151071514401030050070900d458054000d01180c0d0126400d2038030f1014402d031501c207413144a01114002011051002883d216040e42510140d00581c04d001c0c0782443d40ea045500e0b141c040003900c03040b00c1601c0004c08614081400c00c0103082c450003550f80710302e00502c01428400960003051401c0d00b0f004459204400c00010001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 846008309 1250 846007059 846007067
    0x406020f3903010e0105130c0503070b0a0e041d10050a09030801030b0717010b04080f070f17070b0706021c02030606180f03430506031306110a 63
    0x259030482100d8409a01501410310310145600e03207503071103042030148001545034900b5006083c0c081c101c0e0f4020095071074030001c0c01d00d04064840c0c2c11201c440c85907100145500c0d000403858103845014004500c1c00030013071340944070100e802c00066002622050b51800082e03208000071140121040580001c0302403441020480304024403041ea6140b8080726800402d40c003480803030640e0703030141c81080340c0d4031103140980d101031051414007060392130100041352114059014008039001c00c000c0b038940564446200d074550a15024900076501d08180400854400c24194850b0400001c1070740c030304d80d071681100071455000710b8068071650f40004900d01115804a071055a140b10081c0450550034a100000c40a100d41350103214400d8800098200c20f0f5a01e144001100c9801400c58070f801c0030076400a69101140414880c1c890030038120415440c0b0211800109040040200f0300044d0428080001c103400c06040d042102c00c004c6070240000c0e54520506050381c0c60107074103031307100d0b144204024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 846009559 1250 846008309 846008323
    0x102010b010215010303030903090806040303090242130b04080d08012102040b030a03020109060b10050913020417010b03010c03060e0f04020f190305060f060d0b100b0406020f 77
    0x5811540041d14030f888035803100001c0b0741900c1c0d00d4075020031610050700701164001000c0d0840203190040100780070400d9090f40c46011460710035101644220300400c81680c00c842d599584841504038140d0101006180c180c44e00c4400b60040402414115070013002104581641c200101e8264001000d210041040101d07000c03604262602d00895814003642028001414404081d0006000d1138903086684942100c492044064110380444689042c000d0107400c036144140c5c7e0b0760389406642505420300741100c0c22003801c1c645076540307800e00d440c5c00d0008030741e00e0030141311040e50700303000200e2404c05401340c981b4081c4190700086003400e4490304040c21185413181607030505113403890400442518528a90388060200a8004550343e90700102e101203913003541403a07009142e145140c0f030b68070900b400b01050368022000c4411540d1028211864100159003490303000d04400d40c1d01002860b600f0f001903004551000380b010301c1c4c4d680d0a038a0354540054001a000da00b14030358411600700e04015407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 846010809 1250 846009559 846009581
    0x2a0e0f0303040324020415050912030901051e070c0305100f140103020d030216120b060607080304150905060f040506070810170c0a2411192f010201 65
    0x7840ca000d01e1643c81003044200700b01d03030301c440500d00b24001d01611800d6056500070700081c2c20303407050f500d0001c10041c500d6002c45940380c4228203001455040000c000142c8075841d4040c0c5460346002e9803110354992002ca2407807043d844034010015640018900c0c0c58000c0114030540c02040c01c07076040c00c58803054075000d00700c00c1d0031035151020040c9506c00200286045940680740000301401c18201241400c03a14201d0a204110b16000081c0b000004006441150b02498050030144c40d144100300891207a294003824002c81800814046402c4103070444100307003800d0002a00c0c0826941d15418014100e411224000f804001c01061200a00c1300c03981c41001450460003510784846100250801802580700f160384409080701400020000c10f400c0110040a110525075160000300503d00302040d048071a80113000100710081c001c00345900c2c88201140a00400f5814040c44594107404078001d41d0100c602d03113840030310355170700700b0714403818840300044558270402a40019083d02d0f082601 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 846012059 1250 846010809 846010813
    0x2090f0702070b2a0c15040b0a081815070e0904020d06020307022e1104121e0b100501080c0405090129040806040201090f03152a0e0f03 60
    0x200080da980c082003000c240c0360300d5050180c45001144100d000303400b02c400004040d0035140c6900c041a0000a401c04003ca0121445100e081e4480d02c0030050b4001c0f03201d00c1000c0d070230501050700301c5400b8080c6580c0c0070030900c5402440d10449140c0782d103040c82c074079050001e603940c00d010b2010341c076030004c0024a0010283c540e55080d041035070115400c40342c003c0010b44896404000306262a1081c0400f183c101e10b03400c408400811100a00d1019540740c20b01512440d1410040c502c1d04100b0350300b900c084034584140a450b500c0f003074580e16900d40d2400e07020b81c04540d080ca0608001800d0740c3ca06405500003c05609015040a0014040758005046040118002c2c441002641da8011100381592000d90950700910400e0401030442480e0070284090480042000305048030000303000e6100d03038000d0341d4500c81640e955500300004501808082c0c9409440719103150202d0f2260021400c1400b4a040900c3e89071141140008281e81d012824001507141c0b414030101d4074200302078148100080340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 846013309 1250 846012059 846012061
    0x31b050d0609050115030c0509010603050601020615010332060a051011190f1101050301120b1b190201061505031b07020a0b0d0518071a19020105010302090f 69
    0x16056003051200209416291920ba0040041c00c1d0407050b045c41840060380c0c04140c40f0b2428010001150045ca03010340045000011a0741c0301e07010756401050180c01800290b10f070302c4000c0b085615260000c40c18151108000c1c43e0100c4a84e0110b071003c001d10780003102d000e10703240c0c0404c9a00c2c0064461032103500c500710103014941e03c240e59842d8840c0d0714113101d080076444800c807905111700094600b540319143c2c0c44010034802d829a40c4000e10344205414a190805d8038010748041c00300380510183c0014005649001845001483c0c0d00501e003007164a1660008240c0140c103a484440c21415140301090510300c1c42c0d40902036913024000491002035080e0504100820b039010080805800a41151705203450084640c115200796402406c0d034005070744c46031841c3d000c507031052607892a0b10b80f8020001e000d148803038065007680c5c80722101610b50a4649107414001a0b010080c041c0003034401c1000200d400019620503840f44a560004103c41d1324500400c084204001e2165032410302e040c1c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 846014559 1250 846013309 846013319
    0xd0b0111030d090f0203030c01090c080105070807051c050709090b041107020904020a09020f070209010e04051b0a0518070216030c1a0c0f01140108032502180106030204031b 76
    0x7005440000c42e000100041110307503814600143c05840c40084c1d0140400560300d1702040041d00205190350040b800a1a0169079002c41d5080744c03012100100081c2d00d00c0042400356108030020444090009100410072103201ba0f80012607009450403008940c05417400c102c0b406990003003000580d0121030030065801c0380d8404002502c15500024880c0c9454030005085645207255a4060310449004640b1340500e0708050707580750f1126070260321814102c03000090106100e804c0c1c2d03200b140d0003405880c0d0300000c502074440c440c400c1c14025030700103d040f0f0003242c55222900610409a030030440e441c050b0a000101a08054402c42010101c200340340341400410f05005459044551170242c1c0c0d0f13010035903008920341d18000c1c0500c006071401401244031201105400001004040c5508080b0b5640c2c1c81d54225035034030480725400c00e1142180041141c240700310040c2083c1c140041e000034101150748030800e00181c007d07005000400c3c0d0100f41481800360000414540c11407140250500900300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 846015809 1250 846014559 846014563
    0x30b160f0806060405191503410117011401080c010804020424090608030901020a11031f020a0206180714030f07030b01090b040212011520030a020610060e1c080f0d0b0111 75
    0x12741c114130740b0030600812900c140740069080b00140501d2100f05580c1c2c0d41c507130540c003100d100e00240345000e175800c00103400b50281d5820003050485150030010060001e1480055505800062060f80d20039540c90303404406001040f034941021405121507020b1034140702143d030444040350840025980244140c00207640c0000f5044805074020704101d403c2e001c007c00091800018881580c00402c0d0340c00c0b10050000c4d1030300502804a00b640030783c4c01c15540c0099011040035071041040560340140003c000301001020349407042c20015080c0d4503014000e032401460115035034030449609030210010401400e00c1d21490703100000480f01036103440040001500e10441c180a94840c0a542c1112400c1d200d004103002460001544982d001d010711080020351680c008030008400f43c091300c0c0c0016801190100c03440280c0718661071b800e082824042c1406500030200c0041400000611480408070b906040500101d0700005400c6545041f0b0400700d0068401d140083d905100945042030014a00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 846017059 1250 846015809 846015851
    0xd0225080a0c08090a0902070605092b02010b090717090c090a0507020a0537150c170112110117161710030b160f0806060405191503 58
    0x206241c280051405810000c49500c241d0350340702d40c405c5034880c00083c00042e83c0c015100c0c0318050a420007103507440c0003c043d180c11011030240c0b080d4400c0f03110250b960103100c00300007400340c0794400001c0751018034001c9a5a01811360307004001c14000003141322404080941c66620807401000780070000034040204940400140c9156010754403900000e200c54402c011540c0199040412a4840c0011031f102c0007044d061200751600c81c0e415102d421041c1d40c0c0c134800525000b45e1001c0c00b88441009060500010541020071100b004070405e02803000d040800700460282c00c8407080c3c0403281006240c4103004101c0390022a045c007034100c030110040360202400340d50103c641040c00c0c0c00310712080001c881e0311240400528109000c0000c4c040c010740501e03060703015244100361103400b50312815540200100c001c01d402c400101070341079a603045445010b0064100030050101c40c10039071107a000507032035034400503040c540e02041314041080c81e1803104041d010794030905007000400c0700d0701ea00250a0348 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 846018309 1250 846017059 846017077
    0x30a0507020f1c05010c03090807060f061206021314241e0c010e03040b0a03150314030304020117070f0e15030711120901050703230d022508 62
    0x100100d08802551540c4065100e1028000c0c0483c0c56105801c44080c0030501404040c2d40d40c5d03180506d40b000b110300a03c01c840019800108103801c000f09a036541000d800c088803004112900c50b803002070005815565102414400c120160b00d4216800d10003000101c0c0b135226414490601e204044280c9429001103a01080c1380700500c1019400100e2030820310131010001507119a00c2c3c003594005103000701500c400350f480c00080c855200203e03c030361744e20f000e01d001d0755981c0c3c0020441204194081c7d0301402d102100e10340c1400b0b8190b9a611a01403216003110404855000001004210341c0d1080c00d1074a0035250004807181801c103800010300d02c20446c40404140013164241040c3d40e40c81c5060700351240c0c028080159640b4000c0c0c00209804411544401240b10301c4000d8242c0005000654810582c183c0d100381c280140364030b08483c081c452081003503458018640110808480c500180740c60401020003683c0e5203e0f1000d0f1201408c9040f00300c0003042000420440050240801c42c1c003030b20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 846019559 1250 846018309 846018317
    0xf01330e0402041d030a020c0406080304060503180a0f03030915050103080a1b1b061112120c0c010c021f0e0a02040504030504080115032d080a0c020406031a09030c030a 74
    0x2c1c4000b20301e20844d0246421000c00c91102248081c01c141e0f0000d600380c0f401c1c0703080e102404001d684040c0103589000e0360213842c022850500c0058540c404049100109800c068100ca07401c032220344604031071000d48078042c1d00081c1c0301d401003000e201480c0050011005d0184041006616503100c0a50038014040e0940c01c002071001c00d03003c080e011101c841d084940020103511880044a5a60003110380c41c421000855200e000507200c0307c8010901000104420703505903e81a0044401c0030050b10041030440b2880c020704c038800c86c0484c248240301c00c07055076400503d1001e4001940385d04044034034090200c121300781030303c14607809400f04044001a5069038007060b03c0d281c1f8a42030b6042d010b60f07040403e0562920001218520406541e08201c90240850180034a950289011003007400311f0500c1590400c0f6080b00000303820070004140b00c1c48989020800000b01380c1c000b9023554000da00070fa800c82d100710340354140b1030304804103d40c10604c1000250b141c81404100940c0380c0c050140344100340 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 846020809 1250 846019559 846019571
    0x7170102040509100e18060609180616030b040c0c1101030b10030c0e090708060d020406081e0f030705070e0901062c090c210f01330e040204 62
    0x44502501610041c20700103203860aa441d200c441402c45201921441c0701c1280348101103001d020300c6901c8660610035100240040e40d48480074440c1d1084044c14100000b0710f141401039407041c0c2442100d0061141982e42045030a2003880141134401c0c82c016244150f182c4091201002e0700075202d04241640000a21007116000d401a00140701c1102e0085e08121541000880c159040c0d200303440c201d403680c070350814902040c418048a40c5044a0b504041100000440c80c18505000541d18030351000f8130205d4031b07031b444045190802c4507030300c8494103414040d40e16210801e41403054258111030700004508100301c0e500e40b03955640c45889800f44c6510b04070046402c168080d04502c018050700d20007070005c00f03044541300d2440141518a607071201c1d00d0201044e4020701c00b0031004c044070b2004008800703c400420042507201d0020880042a2281e01a102c070380090070300074007203523000a07142009002c084048420286503000c0c0039503040900c81405004005c811400c07150000c0d0107071400240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 846022059 1250 846020809 846020849
    0x7050a030f0f060f23060f0c2802031014131b0e07110d270f06020303010815090318030120043f17120a05090309010207 53
    0x20800750b9110b5809a040c028040340c90302c4007012160494884092180e50b040c6480d0001005041d040074565122a041154543c000b040101804490701210252100b0840010080b610644a1800e1190250800ca0307a20250b1405024040601c2244402030118140c1d614050301000c0c0014122017030101600194001d10903c000c182c110b120038180501700b0a612950f125550f50f4044643c003002907030300b9103082022030000c501040940003907212041d200c01e614030020780c1d03896902d2400d09502109400010b0a040d44410f10000b00035513005140d481d41041e034540e0620b403020110401808404080c4aa545400030449040c041481580a45072004000082c003400030500e062040c1c051118061075500c50b220018400c9582e40300b4141c0da5804c9000d1100508041c0441c6010f509141e0100d1801480c0e8400c40003060f24071603003406140c49d1014229458170380041c40005008018041044110040c0f80714598001685200460404005400007550740406006400e80044100c1050340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 846023309 1250 846022059 846022061
    0x1080609012322080a05041a130608312109050904032d0f030c170439050d05030316090801091416120f03021c050702030601050907050a030f 62
    0x10f000c0768004020350ba07480610310000e0250f0024000e2007607102c05407122040b509a04021144403200030a5107040e1140b401d01c0c00e603010fa00003060803114800c505070949040c207444400c03603d441000c15814903c1c4510341880080b605607104410b01682040d180200503a812442c010b04890b800c66502c0080d0340c0303514048860181000030300c0440c0041640507400b02d04041d000f4003d0084a036500b10300300080c400300b28140d403d0303144c100c03001c2070342e41d401081080440b00e101c40d805801100146c0399480108100d030303800301940018450208101e120002100306041b40e5170024a0203c03203042001002d600c5441e2244400350080c10b400084141d0900e00b02d0051007000d00074a8614003c11089005007010b00e52541700e5002070649014800a440007070351070074841015940d003002041003800c62540d402c20310b1140000d050b030540c850641450100fa00c2c1414040680c1216a655600e800151041c54644001070700118403c4269804200314142e002056230703404a4149000304a15000d00d601c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 846024559 1250 846023309 846023371
    0x50a090507031410020c0f0d1d0108040c031e11030106140f010e0a080f1204151422090f110f0d110a03050106110a020f0d060f05010806090123 63
    0x851041c5c008103021305021804124240c1c076141ca0b01c15035031540c14085081341d071701120f640341c4015000031000c40003155208402da44d078410702c039564a0f03c10360b440e40c48040120810b00e01d01c01083e0326135000901000a0780481ea039051006400a01080b070411200c41d42d5011034502c554082c560084501c225a807040d00c242035030507005090561601e40b10200070303445144d1181e00300030380d10640c3d0480070020100c0044400321500b15007541c4840c90f640c981111041ca030705091460040080c41070090b903846a01e428600ca803080c040d000442c0703241c0070b902e1041e98500310fa0005c240707290103403011b400c110500072112401d0364a0398855440b000065410000e1507600c11000d801704020075903102c030513010b81c80541683c4003922440b544503660b4103119030307502e9111f00c002c1d0081500007480702c141c10003040110303d00c7d1044102191880c400d040800440380e0990201c81d141d445241400a0031000384500300300400070b51745149100048805110192001400740c0050302d0b0301038500003c180d200e402031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 846025809 1250 846024559 846024583
    0x70e04171209060a0c0c0c0b07020102100608011b0309020a0509091f0506010908160905040c0e04120e0307032315040f02152a0304170a06050a0905070314 68
    0xc90300a04100c0840c568443d01242c0192005107040074007074001d40100ba074074545c5903001c800d60100702d007048441207403500410012419803080c0881d0031000c0202c0c1c00341201614440c000000c0305c031030404d40390b60002c1450040506052070031015001507202c000740c0e0400c0d1442500e004110703031143c0920078988816104d01d81e81138080d41c1d0070b03101400303129003019010720000d07a2446000d545841826480300c1100c0301904640703603038034420000150342e07400455102d4010155482c0681e075400440300c1c010006c031000c460300c0c5004110768041541011904103c1c40c3c2c150300034407519056645010304018225903450484041c800810f0260408010480217900c5900402040c1d0801b4a0300318015807501108a20806018400060141410003603c0048101091440c5009000d4071856807445040808240780c1c0010000441c0c0300142c040b51325a101c202000030035103038109040c20ba084036400b5124095031030401d10703000c1c0030540000d5010147c0f0f821900304c05141002080720740c9017000986903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 846027059 1250 846025809 846025837
    0xc0304060206011a03060d11040b040e0607030f02090d08070f08071b060807080f0601110d02030711040608030937260304060e0a030803010311030d02070e0417 70
    0x1080352580428254100d4100c6400c0740500001e20140c20101d000c01c0300e81d5600700410140030000b0540320525031040342e0300034000180c0994500007240c00d5802c070707501100712070380202d0502c0549541071007100d02191038003004600304072020300050002104004081d08041020402d00280181d04118403041e5178404600c03075845100e490321040851840342ea43c190314020250000740d4602445616225800666a40102d41d54801d1901c0e003148001c2c216030f0401003801c86615102008000040700011160019900c902007480d0241e0081c001078061805241840800c001d662000000c1d190641c0b4100c6e42d00f111000c00c0c007040391550680641c80c9640c0411520075080c0740c81789206050580b80e0301085210614802d80011560012901c00480313540c1c03042004208043c41401c540a00d00c44c02819414010782e00c2c0c60703441c3c15410030303003050b6500c44101511042034902000141d980e1105e90000d040598030f002880c0c0d9020a0041c40074040c03202c4e030343e49a40d0080c200300840300c0503045404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 846028309 1250 846027059 846027067
    0x130206121003020a0b030c030601050f09040f0e010b0409020d0222180b090a0c03060203060409050609010c080702070b07030e06041701060302042d0c26060114180f03030c03 76
    0xa8801d005800340c0c401079000703e1000e440070400c0708a03401100d102d2480407103000e1540c0c8401d401140c0e554001e14081d03003c580c00340b118134000d0365a809906103584000e407011408000d80b07400c0381d00b19894507007400d100d1480c0520180050301c1d0102e030072420781d404545a4040b91400d59003401c2003448803144c0f40840d03140040841c851605040d612010b00d005600030708095940850b900c0c0e803032049a01c040c060320011701042000840c50340040d64051000350012542100c1580d0361850726505130791110480c4d441d151540c80c083ea01040c91588100c8501c028481d0500e41000d44000d07202c3e440000e010015240c0e0341200c0c0b616004103e41c0100301c2000c0c1c20751809540344000340240450f01040f4841c81c2000c0320f00e03031200c5690307032501000982e85e2a61100f040c040d0140100030000034140506028502e0040740001c900c00740d03e0ba01d8030740403106242452800c400014945200042c2c0e4080c010014000f2959160b000f840c210b1405401f81d501138000e589007000240386005801020750244000a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 846029559 1250 846028309 846028321
    0x70507061106011a070210020115140306060f0d0b25030c0311031006084203150609100305030d0e0c03070510231204120e0913020612 59
    0x80e0071880d4050341105440c03003642ca61608100307200000055202c080e00a00040c4054684070030040c0c41c1d121a0b00002481842c424445040180103900140340f40b04c00c41c2281c050740c28240085544060202d0325024840c001d200028810841940040d1030807500a000541490300b54421074444415840c1c0ca480d1700c80c034490b000340544090f440725000a4280b01024407607021f80001d6038000c021245408241c941068000c840342e2400070480422541c0c1001640d00c1510b402c0c19a85842800405e40d224140003a070010750b0780d2600300403860085d403051075001c0364001e200f540d00c0d0300550206c0d000881e60701e444004050110345900301030504e00000038861203611041c1c0c0407802a040940546401584890070552200190720941d50418551801110300358459444082c0451482c1c503aa00442c0d0900180300b03807600144042c030102c5100380180000d10601200b500311a28252a00c1d504082c10540410656a0701905505244080d4000c2d40c1c00c550303550b025034030591450701e0000c0c0d840c07500d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 846030809 1250 846029559 846029567
    0xc03140336090613090503090603010609060206010e071d060d050a150506040e011a1b07050405180d03231e07080114010507020a0b13060318050c1002010207050706 72
    0xc0180c02241c00105100303000e080c58104140301d5040103150107202040c001c80540900040041110180800c014440c5c066981001560191119589010805003003c40180c60010180c103e40800c1d40c07014200200036074044823600300310380c090b0351401c61b1068041c0425040d009140c03003a10030900b1322041020789000c690010040b0000100a10380c1c00d42c1d00d0b0140301d0a40300303500482c40794466400043c41042d41031030602d01411001c070030712442d1505c1c451450258112504420f90150048001000b6610381805120b030028009022000c140b0ba001d00510313580d03c0401d903140c0c280f54440103180691084413000040c4041203c0c4c9101091a0440314a02441180030600c81c8502810000c152024403c0e00043c0c140c8045d07a25020a120b1a880151840d4100c820200c0c0e000d80307858400b2a01e1003184028003240c0800ea0701d0501e131141021009820b0f50301c024480095841c02d807246030049400000c05990010007a150104039196015080380a0b11418001401030702c80d03e030f0b001030500e501c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 846032059 1250 846030809 846030877
    0x10e07080d0c030c061a030601090b15180303030a0501090c09120212010f020f190c08030a27050606010f0e030a0809040e160815010f151715040f02070c031403 70
    0x44003680c20716030729842b85004492070141e1054011050500b13041c40e48440000078420107104103011642c0a20f03510009e4910340c006c036810071082c1d84420040251000034012501c0885581c185401d01e181054085008640341f404040c3c420b10550a41c5a0804421b60004225100d0743d00c0555480c6070480e501c51003680158850b0341c00d18003006030020828803465034004082d502004162864462900d000060300d107290401c64a00044419900ca410000c044030032600c0c860406030590b0300e865000076101e112880d41c43c03002c0c00203071004895a50b402280424841c0d9101c401d883d111448030011600420307001c07880c0800c911910b8405120702602140c403000301c0381d5590071206c400410741c008006030380c006e2182d920090f0061005100b403111046c41c1e840050060700e01400303810084980768113842819203003880f030f01600000c50480307401c26000b620b060003650a015450a031907035075503050302d101c1448054410500162003015602c4144200d409001440300c112001d2480000d2000c15514 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 846033309 1250 846032059 846032111
    0x180b0307030c0e030c06031f090903030c020d080709180b030f1501060e0a0501050a02150a0516050708181311090f09040506040b0c070b040c08010e07080d0c030c06 72
    0x1c900f258441d5901e000035000100c40300c040c00290444d15900708825804040c0802558a0102004041030010841c49040f08050003030b07801003288811440040c0c2400c510f00c0c074070130801c04013a080002054010620070100c0b03000d01e03246030341c02d050743d02d18100609041c681c00307906004e443c000b40b03102c030400034a2210032054090b01d150b040e40d85030b100345e4440d140000074a800c5040340d43c0c01c0106600880107045584503a00540c0d090104a03480300c1003c2e00708684803101d03a5950310a01c10b50082125020131200e000b81803241c900306031038131180440d0080000420501c40d0740c624a0000ea00c2f80044090030b805a560b00f4407100148080b400b031280c000d1810a40502c200400c04100c501d4080c01c014003440e040009420162a00c0c0c031900c01041c8002d1131840100000c00802001451360030300341e44a02e004200302e0f540c103820240d041d070a5480b25072344001a0b0b40200bc040c08403110224480305007180300d003440032700b84000c0c1c0b5054540d00e40410b03014150301c2c80e100d10061032028000040107614 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 846034559 1250 846033309 846033317
    0x708031605120703140f04030b0f010e0610090909050c03030a08091207150914030f04080615090c0706110d091704060905060309030d0e0a12080c0901180b0307030c 72
    0x482c0c03041500d9098040c03501c0c00340026004200c0b4000000d03c10000385448544002c2e442c0c40c1a4498888a8220320195000e100c1c18201d1401002051a00102035400c40b000311410600201800c1d0028501c1c5400c1c0541100540c3d42c0c022101045002c10074401100406010b0f0fa4072004000d601030f000381401c0b91841c00038012000b05c9902c1148510841e40210381c413402e5011141c80188042d802498013040481740003103010b10554007550204090b103901c00119885a03900c504241c845800c080025040240698001100060982c0e0b03d48082e80e004141039805030f183c4425050001c090300c06107042e0580c440001540e001421041d810440811740503a415255076549414450381c2e0b84110700c40d000010b20011010700080c0380c030350020340d04009040100da0800714070340640c400300c451601c0410307010340c040301608040150314040c103403012203e0b0401d00c046280c0701c5804412440366081c01810020b02503046000211a88000e030302410510030301c0c0d41c5a00e840c2402030300800069481401017 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 846035809 1250 846034559 846034573
    0x181809010b01090303120203100306020c070602280b0a091a01031a0c0406030e0c03062e051003050612010c021f020414061b0115090f0c020d0f020708031605 69
    0x20b50003001a641200e50568900074444048a0500000c0d0805450b80036613801d150b00000126031103001811015414501030106035240460191a0903051402003403d40309040101e9249641102e69403405900030381c2100e00d076980c01e01d420380205040c0d10300608100c0114a40c01403c042100801d050724810605050800c280040d43d4480307850888040b42c02410400c4144003041c80b9411510060140504841d900d854100001e400c2c81c03001c450a17112a14501100ba680c11402c07c031004401c04c61401018401e401c0c40045104000507841a4090503160004030b61561035104001d210007030a80000c1100c815000802500c8403640907a0710b001c2d0303200c6003101051a4151080340d04403015030a0340c51030101d20000307000d0305400c5200780000c83d091b00380b00c41c0d4090400780150b40d03c03c69200081e0441c581000c02c0300d02101c40c0f2450390790026240c411514203683e0001085480c2888038100344a6114519204a10b4a903d0341c0040b0f03c03d010105590340c1102071511401c0f0300f43e11440541d000c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 846037059 1250 846035809 846035831
    0x40e0702030c0a060e0c0414060108011706041e21181409040204090516080706031e0b0a050a06050c19081b010b04060305033c18180901 60
    0x1c0d901901548000d240c00103031110000a850b580300c108034040d04003e039680744811100140448040e03040c000408104501002455a80b201401d809445020100752660040f842c420360b0b02c20b0010001414008107a14415001984041388182c456001c50280c200811000690300a0001c42c848540815241c299562010380d00460b01d20a440e2500e41d00300400700d114041014884014000743c0c0c201341d49102c0324010030ba0510030500d429038150b00d82c2034800e03d4485c0452404000342e1202082510b800c01007030302143c6881c480981c4500d20a000314804080e4070000306401c101e0343c0010f41c4500c141c01c0000d641504003000d0440c500e502c0c0b081c1c80941c06580c00f802118210600c004000410401c082583c5130340d900c0c03015000d030109800020b95074071058041411130f001d617041505c00780e00101300007000c0c2400c0300e0f0070f00c2582c2454500c041544005c0404110035030f0203c2c82d5016403580481d1230015203005506e894848140200000f16000c41d80c000c00003020020340d9041055400c045100d00707 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 846038309 1250 846037059 846037063
    0x308060307050d032f0a0609060b0612071b080406050a0905041b080c04080309010503040c1e0305010c0e030d03090302210912071202040507030e2506140405040b18010b040e0702 78
    0x9019040358004d42540341b042e90301c0d003008042544c0100d600030b0707035000e42c039425403680d5001c0c204950302d0444250f81401c0c081d0024100346031080203107030108003021481000030440c60940f001c03688282042503c540650f88255041c4241d60480c4e80c200c0d150100d080c1a00e903414a00300039070805916509800c0e210917580000702c1c07146009520441d0310812400c8000d5110360025030b4444d0068070001500c07522403800c06048038080fa6850041c0102c1c4106106014003072044400d0000c0505002c11007a07144004070703480340305c501a0501816602d0f251101030500034004420468016031050146142f2148820703115041054a907000d86403005061007080400654541a00e2010010010f5010a0390811000d400001c1a4904050715014a00c003070300030401803800c1c2d801d03030906400345a007040858190a25220340c0118100300c141e05010040c041104211001d449052741c000c104d010780100415940030030703e842c2e2400800d0380c1000054042481001d442a24820080c00c9440e41760444101d03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 846039559 1250 846038309 846038387
    0xa0e011403010b16050604080307030b0f0102120a0324080106061d040b13021602011803080403170c030d06080106060c020f0f011e0305010302030114130308060307050d03 75
    0x303401168104018066000c058000e0640340d034030350401010401c20740e80c2d03050902d18107450883c0d11403c00720510000780e400d80506c411050041c0e481004120420000030750302ca0007090141441040002e03100c0c1000e2081d044100705015800003003800700c06013000098482d50f5442880515440d1100104880d4400ca0542290000e43c00000b1149101c400400c001000610a810340c403c000310400540d010b25070003e4000780460391620101c4201da800098004004400c81545054a0a406100041030301d02030701c0580b45c0142c15140342191001c05100c4903c24003400307003017522011900518000d10b980103682560040c0c4000e00c402e6988010560300b196480e20300952117444035111003500d04094502c860300050500d82100d12003038007000c00240c10b040c07100d52000692944014402e50809000b2001200300f010200290b0307142402c25002900030103040101080114008241c540d50b00b040800081c18005000c164900310a00e800b0780302c280c4410794090307086c1d04007002100c00e880c05134200b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 846040809 1250 846039559 846039587
    0xf160206010e1f03030804031106090a0809040f15030c060e10231317060405030f0706060f09020c010f05060303041802070803090705090c0703051204140609030a0e01 73
    0x5005607401d2400b40945041d00610f81464410b80081c40450b407100d001d800d20046000b42c45504090400b400c1c0200505401d1509000540c44582405041440022a008800d403c10b040f56155104000014050021008041600d074100301401080040030070354141102c0c812002481801e40d520380a641d883d070309100550b4004020303000c001ca580d000d490242c0f44240000d4041b10520071002c0b41d101642c028410540802011500030b001d800103489203420005220f0340100101d142ca40d481554030301c40c01a85d220b26100118442081000720b40061000e000104800116240c5610b503080c02500130100158480d130070492416180708a91103034900450028010354541420321401d486015000101004016800c00030500481c1d00d1001860040c0c0c654005410311914000400440320406068074807600000c01000000a4000d4202c0315042e030780e01c0001c030490741c40b170a00381e4900100344024205ca0148804110280d030b40031000f40940040340e100c0080c40c5560100442d51a8142644 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 846042059 1250 846040809 846040813
    0x906010e0708040c0311060c120a091e0611070819060f0c023316020c01081302040518011d0d09080a06110c0a1103070504091104050402030c0a06080f1602 68
    0x1061012404400311040640d0300a0300640c03030030350300e00c48c03441c81e21003040840f81a115020030441c0020754403081800c001e0081d049692820070018a00d0039038a12940709803800e012090f0480d42460105000000040c10b030002501c1380c40304a1500400c9134100c005045416034600b08456290f81d0786031043c81010a00baa0003002c00e100da00c0c03001001240f40749502c010310b03040e402d146500d507980c00d000988107010442032040e0000450b54040e00d00344c0f490700c0403030500a040e41004840c4c3c4a280303444a205404403404503044c1c490340003025881130142202806542007000b001c04946001344a400801e8981040301c43c0229040d500312144100c1e0f000d510060f401c030229490104030703903402c01c981004111120520b42030310300741020f1400b40d00d6103040369142d08030a541c00c1d2600d0b040c0080700040c030080d5814080c1146541d5078462440340410800e1141d6518400f060a5403420040d82c214004043d0000900c9a1245009030540341c0840303c07140300081090002c0c8511103243c81d001c4c202c05061b00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 846043165 1106 846042059 846042083
    0x203134412131a1e04150809070902090f060309160f0e06010f0c030c030c02190f0503030a230f0417010e0a050615040f050906010e070804 61
    0x444440e516060090144060601c00704070f424841c4d2080d480e6003240d0034003d5450a90186411582600000328000802103810200850080294034202c0d40c409568215481c140d200e070703540c2c00380c00042c003241820607803d0010186400001c41016202c2200c800513400c04d07038161070350001030f28141219080118142040b01180c0041d030071710f42040d05010858014003900c0006400034204a01c85074890140361017005030f80b01d05a4001c2c640d5039203060548032102440c00c18007401905031130343d0b0b1002819140010403180560f025031648000e03a45204681e84054100300340c81c182035001040007440610200004201900c01c0c0829010700c2251081101d086a14050740c00d0001d922085100c0d02060001806950181148800107030070402c0c20049000f41c903280b2a09540c1a0400083c48080000824402d040c4c50940e18210410360341c0540031240144140c0b030243c9240c3e1007170 = true := by decide +kernel

theorem cover : BRFrame.Cov 845863309 846043165 := by
  have h0 := BRFrame.cov_init 845863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 845863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 845863309 ≤ n) (h2 : n < 846043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
