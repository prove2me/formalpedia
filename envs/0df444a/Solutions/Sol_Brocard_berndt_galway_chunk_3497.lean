-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3497
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:49:50.959017+00:00
-- url     : https://prove2.me/submissions/03e21f6f-cbd2-4649-a55e-b57ce299d548

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 628776978 ≤ n < 628956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 628778228 1250 628776978 628777021
    0x80303040308012c1305010618050903070803060f0103090c0b040e0f07020a14030d050c0c0c0109230d02040e0a02132a2d1112040302041104080303 65
    0x108074000050342206121641d2a240c07600d03a40c11006007032000c0024003204c029005981e5440080ea22000040c0248102401012940710302d404031b00214100c08101d0310300030005025034004008040c0019000d004403035100004407290120400345000480082001d500014071800c05000c0124141400d840035100711106613170b03423110741c1c0d03510907a82c820b06100303884d25005a404141e5040c0001e600700c0f90301c5442405030f82282d0801d140c00f60f00805842d001e41d950300d40601c00081e1864145014000700c10031780001c0c02c288148a11302000302c0c444e000034030b880f0b040000603522845410740c0c0745119042066002001400000000c401003030700c0b00040c005c200d02c9214800f15001c00780d40c09009120000c6410003900240040c1d103050701d010701e100460385004000003c0e014078850880c84980d00710003405104065800c000500029208104041020072585e008040d200b003406c404900b1101541d0b810b40c7c01089440310901c0d6006640502c0c1c1004100c1c2c0004001c018114112540d01011905c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 628779478 1250 628778228 628778237
    0x516061a040c05180d02130f1407111c2106050f0306010b1204021f02250e0a020c070807060c150903120c210203040b090d0f11010b0402040803030403 66
    0x4660840a4603e44151054400121081c18554281d89402c03010005601c6c00a81015000d2071485c1c901c800301e881c0364a540014542e1010404400082805029403051722401c1043d00161500010f555400c11200c0031044164004160b08015226540c100740100100355403022001048060001420942c001c0600908901544281c07c1c500001c0d4039040350342100d2070780c1c44c0c900b40c1601d0051104004105a0f002221208004494445000e04e42d81400440d4090610b03822400141181c151121a201e02c5e901c80340c00041c023880c01c03001c00440d0444025140180d035001c10740c803030b0f03420002c04d64044280c0340030b8800002411038100d562041418400c3c0700340e90720b0034202e0b441c040c1220b903241400307000100080d043d8404801e540c0d001075205901420f2000703480d81c10860035a601d042d412449a441368021003030004100310005580e8010700f030b82016010700703e203180000f49840c40f4803a081d01004031144491017050b00c290700400385c180f070142003513648075240c0851315607942c0b00b568101d0008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 628780728 1250 628779478 628779491
    0x40308031812030712090c03030210050604051e270d0f0f0e190b0c010c0201150303050f0f09030111042301090b07030207120309030b10150516061a04 66
    0x10700001c40d000d48a104500416400c503212124202c50245c4080004e0100a9440036080d01003013481061200461081e4000d003024400b50020800f40c4902410250180781098180031600c69540c0ea02c48045400505000c0e0540e5103e807000380945422554405c0041d00c5c9010700450300c0d020424800c880600c4c2c8520a890160b07a404544140b0f01403144030006a505007800024034081440145002c88006190328241c0c5034540e02c030141d8855205240f942c2c0d5a42001203040ea02806030224180e014a40b034038011b40b80d030314080d005200302c2c034101d10900c0001031600600030101d4261020203a010b8000c00007020032001c403006e150b1290141080720324864a501c25240c860744442c00c0800810780d00d00c0511860002940ca554200001c101d0942c0548180810054004002059024002d0ba12400c00500c1c50a21250f0028003911030100340b580c9000601080c0140040f090b070080d1540381c8180c0e02c200400c03001014440c00f84004010f10f0410020320808071500b890740c001242d080700d041124 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 628781978 1250 628780728 628780771
    0x908091003090b0f07050f0d1e020a0905061602270403180e060d03030f0b3f0c01180302090412110313030204020d060f0906080601120203150c0f04030803 68
    0x1003084800c10b00142d01000202d0541a030640a4019190042c00c08103c00d0701c0d011410b00c2400c4003c001080803503010074030bc5000c80e07105d08584010607050310807030300e003100c541500143c481c6a054041e00900d40030703203100d0035112004d010728a0301840000c00092428070746001800c80081e540441200910100042014044021942d021f19401866880046940d6400b9805402501c001a8a49950342d50184640c1c423420340502480300e44c0c901e003e030181403140c4281c032070b10340310f43c2d1408504011810702c6075030b50300014040318286e209080c02080040000c8840b003140d07034582c00c001d40003240305c000e00c003c1103503140041420365800d448546150310032018180c0e8a000d0744c92102d03a1034a00c20002c00141c18a98001d200e488000c2d04041005616444003452000080d800f080c3c00c141e40f4102040023071000c1c421940036140500d0486c2c01c0074010b400181c2e4032905555100e0428010102054100c000002158800c4039214480c580740c03641c900340180282c20440e040070204c299411036502 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 628783228 1250 628781978 628782001
    0x1507140318040f06080a0f0501020f0f0301150206010b030103140c061204050c03062811030903120705091503070e03011128020d11010b0616050d170106030908091003090b 75
    0xd40d88144001c0610310101e8845407d805035040b01a03c4955003040803c0c288155840100035030515040e01320340d40d524001a04034604d40000d011411500a44014024a1a2141224112508032442e640d00c410f2480b151801c1c045280320300ca5014400140045150407130388003880c850350190060b95600a001014192146812921401403a13540c4012048050502d0b200c0b00454243c610005180c1082c0a110a0f031507100f0740c2d00000c1c540c0301142155402440901050344211a450070a003010845404190345284100e1004c120090100000d0f480c20300c5001e10064400c001802804104111800542194042d40f04142e00d440380ca100c90781400164800d041c00481c44c2d0780100070888031394004503a100b04514011034a03548515480300d01d50764600140000110007124144040003a1804512b81039516100c0b80900050070301c4840e441c3d00b00c25059045550301d04012030800741a10b81800c00c0c0c800e042c65541c0c00214840c0208426915034070500b5814400d880c1000c06440f802d40200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 628784478 1250 628783228 628783241
    0xa090f0b0d0c0b0c100504030801030b15030601090c050c010524010801080303060105090307080607051321030e01090504090807030219080301090c090902070b060f010c021507140318040f 82
    0x5040400c1c100041200d50307a031600420210342c01c1c00982c5c100d00078140051041d94001d881c1540000c2c015030040c001d10200c03003400364000c01342002d03a00c0c041c8001d2000ca51118414810115002e90b1403084640ba2800343d01210101c1040e94004c024500d444041480051a504100b8103120460441c0c1c19071035000700c066074161280c50f8001c40c215903403007004440700e500c015141909030084900c001a05032003048094003480f5161a00c61b01c1d02c044d140050f0741c1414607400b601c02024120821045140680c507440c141941516082800440250050ba41c4403680d9101e203811500d0301c203a5100742300f10140a000941c2c803d40c20341c0d0007100700b5a44046043c10b940400340c0920010001005074407070551040d100c04050707085c44802265244207031402c980215500b0f44c1d000c50210208016840c1c1031705109540341c02400d226010129035000315071005d642d003601c0c82e001140045c3c6002800910704043e04034502c40d0040320f503100070500f8078000c40081102c00034062400c1880154440f4507500461 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 628785728 1250 628784478 628784483
    0xa0c12091401030b2b05030d0b030c0d030c06090503160609020a050a1a0711090906100b0423030102070212030705070f030b070509010e09071d03010e060c0f090a090f0b0d 75
    0x440d07035008081c04846050004074090500c0d29016a100001b00140040c1105118070140003030a103003c1030a1604040302a85118814145900020f00080e000740e8682101504100d000900818a00e08035186102e0485801c000c600007642c81010044c064101c40030181c030969040c031045999606001c5240f43d18058250381201d00386035545071b40d8201010700f003e540a0b07101c00105003040004140000c4042d1440035043e006102005111000c41894100038044815194540f40c602483e2078000509403401036034442510303003a101d07655025016100d0071754006010904075211504c07025a0380e8001d00c01140c2e50700400f240001c1500403606000d04807600a180c7e050569114001184c8551294038014103012014203140080c0d2120005140304d40703080d0b1140948141203521000c644800521030300d100303a041414940c05a540451b00f0303a040340346101100c1c1c40d4032003070360162084e000c0c5d5041281c001c03522040c0059406900d800c5444000d0741c4d00810131140d941d08007486540310030320602 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 628786978 1250 628785728 628785739
    0x3091403030a140d060e060f03070513020c070f0b0a0f0804030203070f02040f14070306140307050d0c08060405100b041a1c05120a020111040e010b0a0c12091401030b 73
    0x464002c24010842c01c011425400226864812844107640c01c840b0302c0d80000082c00034074000c02515080c050340d000d1490504400a0500724500400103201c80c9a0080901d0f000b9000305803000000004c1185e41e014026043c00901c0c4035807a8800d40820307400c181c01e9100042da468804000fa64090003030a03009076099406146420656141c4004049510074200d0b00140d469803110f20340601c502c90014400340c92010b42d0442d0178900c2c0003c0030394415411240135410116000741d07403640d001034104100c54050ba4903d40c60b030101d0400c2e0010502a9012040c14041c0b0000c0100f08007002c10582e41c0c1142044003080049901000e003c01c9407000c14202c4100c00790f0344110038071031070242184440c01d44181d004142d2a4444d64545007019041104114044c902080032800d0300c0d020700804001040e02c101c8541014940803035085440010300c124144400001515003042c0d00c04c2e0a000700310360700000d0011380344410540080c020300140c4a060b4252800c01c000700d44542c8030740143c000b9200010070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 628788228 1250 628786978 628786987
    0x29010807020d05031e100f0f1409060409120302070515070206240402070308010503010f020304020a09180602121008030a140306040f0c0f1403010513181e0309140303 73
    0x8240c503c1e6001421062450034180490f041c40300d45280254400e10301249102071161610708508100c07500c036082010b03110809801802000000740b007184110800f00d40322656500ca0b01c0202c3d00500a00d41c001c0d10b0359054001c807400803501a0000c1484610038000c071440c00d019160241c075040c03c03d403601d100503017151002c61107a26840c0c003240801c101c41061601079100c0e0380b00042c02c980c0304020440c040391040004210310b24081c030030320400c04407060055241d4901580022030415441c0124020035944810b584480001001402c031180c0e0310900855540451140009038420308503044620b100c04c00401080a80300403090b00e241800c1500c0d09034120410a40703039011030b0401030140340c01940d207405101903002c1d240200d0034078006070344807011403802c3d10b500100304c0e110281d0518404901000100203d440317004218240700800b1800207800c54003109501100102800080c003c0141c884032040c0c0000d6000c10700090307610903107611440a42d40c0800001d408280811554140c00600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 628789478 1250 628788228 628788253
    0x818062b0b0307090c0801081b15090a031a09010b10030e0c040c03060602070f03051f090f060204050316030c0e040c1d01140402031302222901080702 66
    0x2003000111941500e40401c20003030070340c04207192010b01d9106070314290719032181c1c0c0ca40030341001180f4054507080015200326903005e4680c5216180d1040b0345801412a2204204c61032111000c0d1846224014100a002a0f5a040207041c801b0009054088058203002107150143d0512070880081400307404182da6122400d4140c00400703460404800b41e0040900070700c0389550300d2040c0c2d00034059030380b8000f030620f042040003440c0c404190001805d00c00460002d0000c50000650140d41e00003030020f50580ea041e0902c010044c1204850090010700ca001c10030b0104a80f6401030025039070141e0444407804641d521694084c0218807015000868143c0c043c003111115207003042c1e100d8020040082403950b00d15842100400801890340e881e20000d005002c80701081c4141d8000c030500b00d406504500b013140d81e61208084d1040004d204800b80c41411a80400d41000d007000814100d80410496040d4001e4210031466074010864002c2e41d40d41c40342c5213602039000c42d0f008880542c0204400c400c2003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 628790728 1250 628789478 628789537
    0xf0c080c16080a031e0c03180308160504031202060703050a0b1804080c100606080604020a052208150433090203010b09091e011a010e0d0602030103081806 68
    0x34021004040c0c175401c142d0034202c0b2108030343d000f82c004100c1c00036110400c0300000b402c0390020081144031120141c0c041001c254090040380e008482c065074803c2c43c206d802020b5034980f14a510082601d6403000d040b8850540105041b8460300703042e01c0c1800a9a51903180c0c0c0100e454009545900160704111610301540c00e0708480c0c0e2042c03041004501d051300c020161464070306000103c1003144e4540e9400d00119600c50800380c1c0284007903405504111055a01814600811201024101c1d03060320111115600340c044a00030209241074034800c0d503c40d0840340429100b01c40a0320300c0700c070b12035030000200e01c00d40350420300340c107114002c0c50480d00d021481c9000c0c002498090b40d056483e0300b840d844130703543c012800d8011103001004100c50440769070250f001140e5208a000c03d645410340480c4030070118111000301c4402440d14202d41c60311280004c0401c11140c4010b417400748044004000c01c0403044c01069a07500300451051880014002c00030706204030204060f45140544042100da030340c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 628791978 1250 628790728 628790737
    0x2030c0703060e07030b040f0302120901090501030902240a080c0c030703050a05070818030f0c0306010b0901030915021e18010302091c030e101419120f0c080c1608 72
    0x20410340c0c1300d4030340e1380d00d5a50100310151000d40380c0f15148007100c804c16404221400a9100c0800450b0400103042c001130310704941841554141500d0f061624115a101090480b411840340740e101c0c045401814401c00a4104e0251030002c00e0319a004a040180040181c84180840c400290714110f19550110707000d41041011000348002407003c0400140504050300d0307640004050980002c40322820149081c1d00f0301c8000103180c01582c8c03442166280824000c3c155614a840e0503546c442c1400102c00a10b07941c170018200045001800c0300c1c1c154a0b400501c0700b448c081200300b5400b240b44c2e280c1740103032152051154020410302003007941035000360040e111100b030080c12100c1302805510001c0e0b0108034550101c0c0000c1480403101914a030100c14612054858580083c40340e05465607001d0034420b48560303207200c80c00d038043c03044028400c0c81a5150041034100c14005081d40d92803400c054088a141301d03001ca440c20001030811a150003d035640c8240040880c0011011a06d075540560300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 628793228 1250 628791978 628792001
    0xf05071b020a151404031a0705091f0c1506171c080c0403062301150507080c01020405030a080d05071b03270e0609151f30060602030c070306 62
    0x2900006a0b140440143c05000298041c404d41c11002c080c0740b1f40c280381036400400050500000b030243c08460344070780c4d180c0760700003982c2d9405488490101340152030360305d6109801428000d080c1c08000c1030b100c0036006841112408640410a0031018103002e0303d03910120082280001d2100340d08071143d1241c14000d0f00a01b8550289103004d440340c540105541c00350103185812100e40c6c44098039109901c1e0120300401741755004c80f10310000c44000401c030344180000685081f20204003c04a01c101f90704541c002d00c4000c1c104e40c4c00100b54604200190046489a86841d140c00001004103001e00c601200000f1030b2004003400c02010782e410343e0480250440b100c41071050307040d10419000715110410240035110003410322860480c0070808000e034009e004000b95020325803421282e4071820202107042e8014964076180301c1704648101d0760206400800c00c500c0e26a001e044840c441c41e90302e40300f030003403c041c0d0600c0540d442c0c4401345d0b43c900c2106c18030f110640c84200204086240340d440201102d6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 628794478 1250 628793228 628793237
    0x140906160c02060d0e0d030b0303070f15061811040f120f0c0b18040b0d0206180418150501081e030f0409020c0f0a021309150f05071b020a15 62
    0x50758002c900c0c15044180743d4040035968218150030900200102c50b0700115501e02400345862050100707869018856009024000e0303001001c0811a81042000e50744003d42001c101150303070748a100304055590201c2044070780c60150411030f40b03c544802c80d8241c400c0e81602c0c00140d07241000070110010592000d0701c584188036031110000303207480307800c000134840e09003442d441f42e980344400e241d00168405d01c5413050746410340c40e002c1501c410210406640d01181c1254480241042c0200082820703103050b5070140c034061a0381c0c10a60704005a1039898041d80300110030101400c0008200e41080c02270b2180c3c0d0b4880c1581c500b4070400b00c07a40f0051960f482003502d04000061942c42495041a008194090303000f09140d04e034840300f00a4000010900b5005104015031500401c1c0c80c4c40420406d450200c1d2515107840c1070200e40d440c480c2000420790003c1011103c0701e01c5c55002042c00f0b0301c0030000116180314403030480e00f41040880c4150380051803182103900e00b9100307410004107641240c0601 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 628795728 1250 628794478 628794497
    0xc030a020a031d1008060d02210d03051e07021011030708150a05060c07050d0b0f07021b15040b160507050420180603070201091a010b070f08040b1c14090616 69
    0x140c5503481c65425480c0d10270b41071401000d20b03401003030828080c1c514010404d46000d0070403d100c18040d41000300405841c00d040040d4844000407400c0400e41c07029001d0f407900342210a00c03015900700046114010f0740c0c0c0d484d41c1d20344070900000c0300c0d55210070304c00340e00149004c401c2c040d6192100041a080d05040d084914456036038010483c1d4901d11001a10455940703010014000f8511441c190700503190301c0500302081a44101140300d010070b540042c0202c000c4403858051078418011540646503010146854007680ca00850b0000c3e40000308503601c2c02000c1000400d42810300031b00c0905141202c886c940090800074400c04c903080545540c00c0303200808450402031721548011405a0525400803032070302402c0c2003008001c0d00010720300780c0b4004101d0041010341200c0080c1e4441940c001900703d00c5140c60308042010303006503002014144c0000a0610070401c040c103000d6051890311a0502644080b40d04404a004084601355a1a0082c01c0066003c0c51030002540c10300a0714280b072400f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 628796978 1250 628795728 628795733
    0x60f06040512030d0c1b081c1109130203070c110607020901030f060501062115090203010f090b0301090201200f010c0f0215071d060c030a020a031d1008060d 69
    0x2c2d004511104030a42c00c00140101800605d010f100c0d00c001e02401c040100248200c2c0a0051105d8020090a030a03c041161005c0208542d82e0f10204071140c4828001500c82c2e07942c1c2901c039030120000a10400850f4802c11101c541802a20300c580b4068851090742195030311401c072000000911258000b40400407800142e4a0a580c1400b85015500b007940c0601d46280900032903c0c1a0400000d000c0101364040300d281c1c0b41002180e003200f28042c0460826103440318500081103d40060b48031500100003c507110420302d01d43e604807101d200e0305101a00310403040c1400c0310b004c460007034005880701801c05100d06100c03141c1c2c402c2110401c105d03100409043d060600310f0b819144504000b401c0c6c0006400b000da41002444521040d001c811202810720000103040840314020898a24021803440400c950f280c07000e80b8491326510381503990301d48000e08020f48030040c07154214046100104081d5044081c01c40f484c0c031410024110303a111210804094507040070050410344c3c00320765400503100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 628798228 1250 628796978 628796989
    0x180b0915071d030709020310050a0b04030b0c0901031d03090301060608100b0906040e0c180f22061e0f080f030a120b0d051b01020118021203040515030f130b060f060405 74
    0x31a6058400803a070181c241400c202d010a5152f0010220000501042c808a05d003504200c4e0011412004035039500420001a0054546e9007420240c01050a49407040b040d8080b00521a00104400800484d9100e23001a103e5002c10356a5100c1a89215170030f2200308030040081c140b03844001c12841c106659107400007884501200c0c541c43c410000700d140044002d6201811580041c12504140c10504042c0864801c8009a01403c0d0002010502d611046030980c094400b0300b41d220315158281c0f804201640c1e040c90144500c4600c00c0541400003407041c0041090141011030b05d0285d4648209418100e998003d06805459815600c41d000e0007655030751003104e000d592040c4050318a054007070803a84120f2423040c43caa415641000c0300c88401d080c0c00100340035007e43c116650441b0402030b152040c9540203070707000660024a01e8403116500110b0401840c03003004420a400e401d40d40f00c914440410580350001070800f0b41000204003a85061104610300d8600541000e05003035540e0300090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 628799478 1250 628798228 628798231
    0x60f3c04030c051603110907050d050406021603021606090602060c03040302100f0e0d0e06250204020c1b0604030b0103030f020f19051e060712180b0915071d0307090203 74
    0x50007504001301001000a450040307202d100e03041729a42254a41460f001e0440d20855000d03400b200e5461001804000d42903058403030b100401900c02c82000c51901d400b035074a0080724956441c44107000c50014803541706d4041001614410b9002d8002510350741140344285e0030140c0f007113080d40691408056640392502c50703601c43c00c1c3c140002180344040180d40c41d0808482c50146030030450610010201c0c0d80300e10003207400d0702442110048003403119860158040c440600029030090001813070303e03414400010a4003400d03d1040184152070020001c0080503c00c03072100a155100705001040071a00032007252800c1007003030040c9e07078a0b80e0741000b0b45800c010b222044420010200181102400003c100c0282141a005040540c9004140039240e8a0100800703c1c41009582d41c40c80a4100d0310340c01a0242c05111340100505c40e11b103241034080b0b0003080340c80502078031a140151603104a00350680b40180020780f1003030b18901c07c40c84080d046203400e8440641610909000281142c0d5503c0110b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 628800728 1250 628799478 628799503
    0x20d14010e07020601060219060204080303070315090902220b0306070f020c03012a18030b0a05150f1c0804180605031c030b12060f3c04030c05 63
    0x4556041c09403035068400040d0201046501c500300501c00190000381d2400b00021003020003084035101c0c5061000b901c200d03004810a8000442841a070b540c1640000d04000440808240c040d0741ba40b0440c402c407034480b6406540414610400c096809514560340018000c0c2c1e100490302e4844100800d1501c50143e801500007600052080d48941d410300581d00c102c0412402488180044d507001103003940180d04070000c640301000103454680c003038061004040350034282440d150b55203092088d0140c000b180c200f40ca480c1001d002515101001382800d91286004244007444007800062002c0d4480c144a002d03c580086c00700c007408154110040c00c010a0181c414081c5000141d841c0011b84516900060081d40010f500141c0b139a080c4c00c1d000349040807441c00140751a0088001464068400000007003401040d0502240d00251203816200300e01c0c489282c80055035084401c02807000d1104d5905070943c0d003214078900301c03800200346a0818080d2808100d4044291550390911000c03030400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 628801978 1250 628800728 628800761
    0x103e0d0c0b0a0b22020408060c0408061006170615220e0405071a090618010e150912031b24041707060e010203010f030209011205031b01020d 62
    0x200010444401d2540b940405961014009000160301080b100340d01041e0181101c00184140c410b4410343e941550014000e010031100503050042c00c00d2225885801054010f0288100043d0a1542c8006c1b8801310f440980e6024884411850740004151000e0720785035000e4081b000092205423040050482050320118600e044180c1100100701100c003980000700b019412401c0101254000c15180d048682e05803154901e038145040c160140e1003850201c43e805400400d07440c03051001c0a4400304944070a07240c02c010988842c00704441d01403581812070040c00100400403c905103484540040c1d008601205c1c06c05021050000024070216010100359006a1300030010b40a07400303500e0f1150b012103200f80c1c80340c1031a441d0300319036018480d0b04446250703001a00d0b800704025a407103081e44060b20389c02151a56140c41151081340103a100503071181e0344020010031440c0e23101d203040f00722581c00343c005c516025030304009110700c006060382ca00c4595402c0c40460f0340c10704ad44c080c0605140034a904c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 628803228 1250 628801978 628801997
    0x70c08030a0527010f08041b03030305040b090c2107182307081303020c040501080606040b04020909150d0b01030503120a020703021b1311030402103e0d 67
    0x1058484410f001000b41515441c00340311500590700b0604035140d90459182051039035485040100c0c544940600c014070400b619103002040c5036060b030103180a03d00c60450034046460340091140d032202a14002c0c1e612103072048180300c0074454119034154082031103080d1100305645d10309034100c0c00300d1050350040c07840c0c44190300c1c03030076050844000702044208111645641400c640040c4801002002c1882c59244200d100c1d0a15008100c1c0300d00d03520b00200b09002070341c2c503005050b40341c0e04203582080c09203007020540c4d00c50380f1303040c020358000c180040c00400d507940d1842c40d5100e07070710140ca02080d00065141c0503000403031818a603c0d0702075030003200116a24414400380c01c403035400c02840c3e9030005106006110003c3c1d80030a802443c0c155000d9000d520340100c0c000a004080304048454065142044030500d07003801c030024521550084450b0b030001480307490142d81440d0284150048040703418000440c001b10042440f0085407044010000c40002ca409203280c1002e82d01c000300402c80504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 628804478 1250 628803228 628803247
    0x30f01020d390509061603030c0c02091603091505010303090608010e0406090201030e0a050f0c090c1603140c01090b0a0b010c0311011401060f0f02010c09030602070c08030a05 77
    0x18201100003000321210314010b080600800c1112104540044981d100c8010308100b0310501c161500190010407a81d9684a80304031510142600c00d0224086030030810900e085034050414401c4140e0068159070080d5210f034900f503020741d0000c0f03411051580d610001d4020603402c043c01707428880c81c0b2100050650450502030200095903000c1000c21402c0801400045040000960050340c0140042500101c51005801610002c82000388600c500f14140c4188900000c140a01c060404195082c1080190a00c00815001c42d0481110001007000442e05845913980c1819580240f40118070341200310854891540002c2c084905030307445030801402d00c0366035148590050980d444c10000c1e08503080010b0070f0414680c401905110115802d0380500303100703400c031140e0040346400007030866844e030b0307409048041e03480d2104c0c000505660a6007101801407003049001d81e003503101c2903800703450765841c68003a42c4012802c035030380d5000c20800140101c0070000b40a038030001f41c0fa8180c4032031250 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 628805728 1250 628804478 628804481
    0x1218060f0f01091a060c0a02040213031e050604020d08090607030e01080a09120c030c0f050a120203030402030a0b1e0a0c0f0305152b080d180b18010b030f01020d 71
    0x40e0000701450f460000e5030340701130f240b007075041c200c0c000f084c1e07400354031000c16110071030920303c003083d02a4000c0e000041e0300356030014510004040d1380c854486200380080d480c102c202032a8004000810b01e50003900450058a080c2d81c807004250311892502c3e10f0300b224080814001c1d006090304030042030520300b840511f5030700000b5507039201700114410802001261520501c1000700684c2405010f4a05a5034003418880c3c408600ea8036000f140c14501100ba514040b955002000c1040d0f54400112108107211071001c0101c82c016a001002042155440d480d0140c5121001d00402410320442140460000c1905c0d8617038810038005d100025034504003040507005c210034692880814ac075150810011605c900e84011449006a820300c84000a407102d0b191440c80c00c04c1500700011000c07036424101700e49440102441604040140303e401c0000c2440c04210004000003412101004005502c20401511103901c4c07800040001c1400110f81c40401e081c6181e80c00790300107a9400182d0b0701d403801001d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 628806978 1250 628805728 628805731
    0x1b19020f0907091a0423090f1303030b060903010c0c0c05030102071a0a0b030307080418050c18031608060412090b180a03021c21051218060f0f 63
    0x544610380140b0300000c0061054003180110f1300904110031040188041120942d406009415640c250560114695280c00d6a4030124907100d070481c400003031200b060088100d8064110096170340c00076220303564140d01801c7c100004613000b54060001a034150703801d00500303a448a903a1920f001c0703400b950625034610641c1390010382c007030380c0104114000180d10380341540d2107407c40035280c9040e4440b4040c14000e49001000540d0511010070040b041c44441e000800c1190482001071405002610272801030b03070800c4442e422210f200b0b1040c0c082c0c544000b007100307010b0f403401400c1d1138034000081c01407090080503400060f0240d1000c000c000812240c28a00c40405039241044441e803403502c8100d55880c41014090301c7c030b10f480c8070003102882d2100f1140d14080c5500038035002c0c60346948151031888d0301c030625064a1400d2101c199102ca00240380b00400c0994486d81e90b18034003181800680818500900031001c3c03905030151615883e001841003d0040e0f08040441d5030600306060106110b000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 628808228 1250 628806978 628807009
    0x15030d0302161403040503031216020703080301031b050616051b0a03020d0c0911210105030304050402090a1203170106030b011707020f070801060614120402061b1902 73
    0x81001000910140c0c60050800c0580c01160081c28159002000b820360080b584660781610011a200300fa03a03040049c07a82c403c05e40340c19030304201100b01ca0203da803840e07984005001c0f41c10400041c0042441c8080f24694071454111580c252541e40c4003007010742e40b01070352203c40d4204031242c08080080a00060410054510320002c01507100740010710740314401c1c4402031150a6503441c0b03504011a0086500041c102c0d0101000029264801c1450075404042908244030001c200d5444102000320302c61b05840c0301070000d604140c245801e0000030340c0b2040b01d4590010903502c001501d296020900301c00c03184070b5540c5501491808000080d8040b040c0c0100043c181020a4800540d80c040f200b815020b030126025070843d00c803600260f04164000c4104441030140307250216500f441504010219002503440c448608106042c950083c054082d219010f00c82400c081009403a00601400c50360001540081e405030b0401d840b5864500444060740b20030b803656200b04c0541c030780f83c4000e41c143c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 628809478 1250 628808228 628808231
    0x90f0a031a06030a080c010902130903080a02032208130e0c0306040b130c170115020a0807020f1e0901050607030c0f030e2101150521011415030d03 65
    0xd003103a40d1041495001441648480711400016499030f60401144403c140c1069030a81d5402940f41114040c02101c40183d010303a804124003078404071a0310403100c09540664410110707440307a1100d40c01a6002910140001c01c0951000c91050300d940d160400203031052812540c0c480840707154600011150340261801152039080064410101e81100c0d8001c0003114001380c0003400400081102090010841e8003c0c601060342c2c0e00340341c010b40c100e00501c25281c549003241c2c3c2e81d0340008180720481c5000f4001038104019080000c0c01600c09032030304a100620283e1408610004110441c44c1180f03030280d0345002c00100030303c0e81464283c103405440c00f40e0764503240c001c0305d40740030704643c8800304000c282c100e00d51104401c0c103100d201c074071150150041008100e0440e4031440b4000c0d044c1c260141845520341a001c071003c59660301150b04865028003603180702d01240115900324491051300940030354079008141d1205241c081582e2040600000b0000f030041c0030010f240c03800210103042001d15 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 628810728 1250 628809478 628809499
    0xf0709090f080a031512200d0219080105070906110a0b0103080717030901020a09050f090f0712290102012c03070b09010c0206070e42090f 61
    0x609642015075005070801c5915958010421044000340001d95881000030714244000c1141c200c0406420142e900480d40d12811a05c80c48001e0111554400d0306035000d5840001c64005050400003103404000382040f1000d0799075200041425940700f11075000010305282c1040c40401d804c18011406504910003d00f0b00103000e581d41140300030103001c007070141c201c003150b038004001e6244880e86180030384100c1303240c8070b040880d0340c03a020790030825051007c61181240803d45041160f0048c107800fa004110b250b0b55241c41c50140310011015011804010400c0810b00502041d4041c0d0704a01c222008840160f0715808072815500c8440e451641c116411b0a42ca44000c000c010b9641e250a042c840030f00340c80100c3c50007414035504c80e0200003810110040701b080003501040d4000303c031604203502914000c2d503070358804a9207082000a1700b07034000143e15032502c40700708002c60f4901c5502c0c0302c1c1c8040d900351803008220012034460710100f0030044000903603042d14200000008484402510104001e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 628811978 1250 628810728 628810733
    0x409061d071b110a0b04050f03010e0604020d0c1a03160302120a0b010c0b010e090c06030f0f04061112150a08070e0403020a08040f0509061002030d0c1806020f070909 73
    0x4441241110407034031410b00d07080c0040c4a00c210303032002c030103000511381c5407080d980b0b0320700d5038a5400c82d1240d00d200303040700c011101d40781c103060050000c803100c0030002c1c0100da607480d800c00115074020f82003520324000032440824070003400003d1000d0540c1601880d41c807803900d104641d811100031241c0c2d108040c01801004150492404244c1e000342c24007401060380010400101c96403821820003502c1000c6680000030661aa04450750051050105903205112500140312152005598000c03d260000d400101c00c000225911600507100d44404a69021015000001500b1064160800c0001e8005000c541d058071112030140c0c40c0107841800d006d500d0003003070907101c0c1c031103100c0e000f042c07019030000400b010305c240090000950300049903030b10345403110300040c1800a82c0c001c0a010321003c6010460920305030a501d44070300416402549400040031406000c3d2003000c848005001081541c1748528400d21040409804958020003800b583d070031142c1e24100c2c003540003440031803404014401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 628813228 1250 628811978 628811987
    0x905040c110a1401150b030105030705011407171b03030f24041a0a0b0c0d09030c03020d030c02031b090c0306030312070905100e0102060a0506061903020d020409061d07 74
    0x4042d0004031803043d0041d00d035000c40c054240340700d02526103039000360042031005c0f028000e107041e030b401601260714654071000150381c1d03108001c6c420000c140042c0001000195800d8448500c44482114941400001c1180c880d0303201a2481d40380340c0d60000b200f0800b00840588044e50720001e58901020040c2440794240103e680d400d030064051510b42c14000343c030442c104c106212623a006011074103041e58403412000d880d040104200e50f00c0c0548060780340c0039403140741c00205480d0082c2d039411040d803451b030070401c070019500d00032010f1010544a04015aa080c403001d0301000d440354201820405030400c102c244140102420583d460920500c082c0c0d450020035240452420913142c007054941c0c10040d40d000c00c2c00e40c01030381d000b030700207070318000305580f1003107114100344203070200c03140781d00c5d002d10341003d840c0126103180c0c00c8074050041b40000984c0050340c44142c051814010b18022544071600182e901903003248240a80318030040140244030714041c01d91000c1590080b20301d0400340030082 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 628814478 1250 628813228 628813243
    0xf0c010204091e051915030b010f060206010b0306030d050c010b03010528020c100534080106020d140f07020402120405061b041e08030c0705040510030b060411190905040c11 76
    0x110345da030741d00302c036000c242d25155650041d6420a000e15005d60307468540fa00140d850703002d503c006003c0c04000040900c0180241e9000d01002406000c45902c0d804084074550032400030655190348408a010703460300c003031050320b004a03942c82108111241003842d400e510070300310607032080003841048001d2084001041d1200014000340d00400c41c1c2c0c0b101d414104a615090b8a4508070701c0b540310482c1c00030000441c8040810216454a0340e0507a070b907040c10b030380700c1340305010820101c2e01e0b401c0180040060340c4014183c08200603841c2e0304004031a000f140c121b8000400341c59240140b1818002402030820090741d100510000350012007518010315941e03405503109031000d4070800082802000452100030014151910072a610f500d121901c107031b62460988140fa00480c035040101c1d01411000041d031042d660010085281c42d00c84006000040640703a404103101d09007407110b80c0105040088800b481d4507e0380c0d032000f901c0e09007000c00088035035207801035090210320310588410310710114910 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 628815728 1250 628814478 628814521
    0x103150509190905151006030506010818030d0608030702031c3002071a011e03030e30070b030f0a0b010215070c0b01170705060f0c010204091e05 64
    0xaa860500c01d40000041c0c0f400c054020494003c2620220607140b954005a10070281c821110b0811561520b0680840b6015a180f50024425400040c4454480600d880c054540c001c100c91801c11036180d000200d42641d086400c143c7c10005002065260401a00c03c55914001101d20911825140940380b1103400034121031300d000c3c246054420b0303c400741d180d2102e000f055005540e2144603203040101d079452041c040481e466014008a0813545140318100d2514002c901152a0360454400b80c68050700e030746117640d104040d40c5003081000c0d51120307055807000c6041401e0140036070021203203040800b86c4e081034070000780501c00c120303052050501258100050200c002030000031080100d0030144003415886031a80c030350041c0040c00368030003004244980039809181441e42c0700d4030704054062241c81c5030841540000000c0c4140d10f003210041c940441d040c006145040c04d01102d80342660080e500c01c0c940c00350f50300341501e0141d110900c40c2c152486024000c00c05490461000040001c007501c06 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 628816978 1250 628815728 628815751
    0xa020105100b070f0f020301050f160c020f01030207051606020d080c18010807180e150d080d0e10050901060e0a0b0a1a0c0115090c02061302010509131a0103150509 72
    0x2c1c4418031200090442e0286d4001d0000d001920f411a458000084169038580d02c08620410324241544504a518012a401000e0300103070114400110081c0d046a1030940e5940660301860412a0010020b00000d20342c540142425051544029016400042c03040c407070050104034481c0540e008a4a2640e140740908000e00a0b851382c41c4104c60382413050889281912251901141140640452901c54100081d4a80110840e1000d026410825850050005d10207008040140c2001c1d04842d800c1d50302e04003140c4038074088600450940728140c038503c149954036801841000c018824244e4091000740c810300c46603088070041103510219101e499910100152000545040e641c00c5580d1844018000d01201d201500c40724038040d103501c1070f828030a260a00008881d030000c198244924440d1611481002043d001550b40d0340c060030801e940300740020581d41c4030403083d100b04611604013038145644403000300c0014084595409040d040c28a40840030081d65840c8010242d01074542d050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 628818228 1250 628816978 628817003
    0x610030305070314030a0e0705060406080109020a030e06040b070e060702011710120b060a0501090506040314030909010914010e151203280e0a0311061315050a020105100b07 76
    0x1d0864020751104c48140c8080d42c00424082050001e4105840756002c0109a403480750380c1d203082020b18880c0344105004100030b5801000681d42035805059050140d003000f003010b20f240201d09007001402c6800300c0340743d16a1000e02c03504035400309030382002c0c04c400c0d2070f428a001502c1d0006040d100120130864035565444000502d5400000d4581e07006010450141d00b80300210b15111545000c02c0350058010400c00800242a610441d03943c800c0380e00c0502003919103070130f5032a1409280e040403011912807000b0046020700340c4401a4090083c031241c940010098560a030f0303517000303a006030701421034010030100340100f2004c10500c41c04c01100440301c00e0031041c2c0103080b443c05c60190180c00d1854081d00d030b041c0d48902c52940003040c103002040d84c4200d010b10b105020403407001c03040c1c0400b400716546109050f40c2402c2050040040b034480e0b0200da4446680c55402002124900303a0803400a000850011181a024026144c003c003c659043c6407150400c2c0d40c24509000b01d00300a0320140c00c166 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 628819478 1250 628818228 628818233
    0xc02011d042a0318020a0519051503010819020108220f08190507031b030507050f0106090b09010e070e13020d020a0f03180204050c0c060a050f0108061003030507 71
    0x1486a4614a1105850068201c4104000005140855003040844d080a001d00c12444001140341403141d801000b140f0b00e54100428010b141412402d44816111070b1200442c841d40d40b24030031814545045011035a17507060541e002d0806040c441000d86220f005060b00700140c2c1c00942440d808102ea141c104c98411034106402c40044c00050081c007200300d203034011414030030140024142000043e1103904101070385041150a885203043c00342c0001c680303407035204215070104101410075000303103005800c008594a81900b07084482a0351b0540e0f07035640e1006c110a91280c0110f14156074100e030707060010f40c0341603200c10004100908020030030001e2603102d6107a555482010185502150085442d141200d5a100c002d500144145000c074070420302800c01d40d4484e00a10100416550001e47c02c0c52861703082c800a040090030604820b803080c0151100c0708810860b00340b10300b015180105282c00e003025603400c0c1007c103030000c2c1c00640140c41002801441c00c103000007204e41c18504540d41d1341c80790 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 628820728 1250 628819478 628819481
    0x50415110702330c071205010509060606120114130c030b0915181e012918090c221d0103020904080f040e0405030702101107170708030304210c02011d04 67
    0x5420506d540c01707900f918003050101c154007288c0714155882c203d86d96912403404005c0d0038000e05145c0c0c03103215500f400600041071040c1106c803498401034101b002c00c0070b00c50514002d840c40d0044101c0020756901c00840e8501d429064a03070400e0012421000f281a840c011659010303005084581404160000c106c1d81c4804289601e04121003014028141d6118400a1141518028942028207040d800c02c0068010300c6c040740d82003581380c558060031061410500c5091a4024400510703100e05000016074241c400751010301c030f1114222400000d50034021100d032040c0805e004503c880f045d007401400140c031619403041d0000c0c0c1020042d5111b44090303443d05220f106a2700324181c0604068140010050004090100e65108691070000205540301c00c64140c2002e840400540e072021508110504041c1d4004000c03a903c030040c0e58980f500e88651614560098808840020030610307001640e10041c000e40c030300884507140c0308003a2200c41d00000e20a6031881c00020301000074501740300c0765a0703a5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 628821978 1250 628820728 628820743
    0xf04060e031905060901060e15010e0316090606120b090c2203150c02011515030f1a01090605130504020d0e0a03031a0109030f06050415110702330c 65
    0x100300c02c19603110010301d4420340354081680c0c5100c1a41c24400e010031548881c421140c4144440d00b2080202d4402d10011602e00360f02c450415010b0054103a00c2038400d030484a9030010f030803107003008100149003010081c220740100301c602e1100c5280c01000c941940e140210301c1d4014406240e02c1d1340340e915140c1421045010800e01d03404890619000004212141d800404600c0c0010720422500c04900026801c6c0c880300c200482084a0078074092020209000701e44e0408007071803070000f5641005114800480306103034899145c0e1200140401d10a40e40600440e01520003860b000c1d05010201c800c0c1d0a0300c0c01c9a0007580d1085401141c4010101490740c400200141a44222407040b5002c0c100a0700070001060f0f0f00c924081c1c48480300e88254020040078003141e034460b8600c000d40c840c94031204000d00000c0c02c110b502003024407010501890b00d01800f06102403d908072aaa55100c0c810441044010225403280b24080342c00c41c920b4009542c1c81c0000d40c00c903484801d54850020072900d042111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 628823228 1250 628821978 628822003
    0x50a0905070917010b040c08131511040e04140a0503042601140a0e0109151d060705040501090e0903030402040b01110304030b01090614030a060911090c070501050703020f04060e03 79
    0xe1074001a0f031484015040314002c500141e80c10040340c0c02000c800c450004003212010480c4a403101150000f58124642100f001001e1000051264011050307002d03561065104a040009042c00c3c081400026481c000f4901e0140700184030340100e6039500f0352207000703034031a00c11421380c44618200100c1d42d00c03040315012035200000304481003190141c00202035082e40c11520b03091400c0301003c10108148a103140d0180c000440e05503481689031000007900740e99009050300340c1e079106440c28108003041010f0003100705490307031030721503003840c0004100b49425801000c0b4410080c0500c8080d2502108580e0401e4040d0317000b0030300120040060f42c000000043c0c0821600c07000400005000300d05840034146c2d04d40c3c00c000e0009650310719003403607d58208030b0041d5058114009240010b000740d400706002d9881820540902008440004c88010707040303a0105100c2000130360901003080038030595501030f9282c1001c40c00c040c4000012011400355000380009c0c0070580500d062160340c100580d84004a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 628824478 1250 628823228 628823249
    0x12020f0a0303030509100c09051306050a0e01090531050a0b0c04170f15190c030207060f06510f1407080a1b0803060316050a09050709 59
    0x1a602e280080c0180b40854001126004d1003009480c08075560140d044055070360b41e40c0201581c100400c21003808484445007403016a5030f40001074036212407081d20010400d41c4030b03c4401d0761424030800160b0708010081c540881c8500402c1e0210205140042501600c041d02485529061b240591511041010181400c081c0000b000203c0c101c40004000390781800414807950300c08600070544d074829070207440da061b80218850000103105e00355015031100420401c000b40101c80c0e06400201e450240c82000005d400003000c4040c047c01c0c0c06400c244502c000720800807503280603105548120342020320800c264034038059801c0403000704031512a00343c00c0c00700c485820445400746c030b81400101c0000000300b142e0b0081001c4941c0a018011407400340342d86140d1a003513855585024991018916000340842c40d1360546040c80c0804e00190024440c0005d03079a281040810140b0381001c1000c143e01403d103010302880140c9030140444200d0300c21a401142d180c588a40503100c0307000135004903070fa10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 628825728 1250 628824478 628824499
    0x24030e10060e011802040803120603030708070c031713090c110106150906050f04151e0815150d0f0603120305012102030312071404140307061812020f 66
    0xe6107908168103c44080302d1050326210580a10300c268000d40c487c0c41500c0c2c02c2032010b0a00320b60310404d2558480c2d002825079140c8115595400c0b09038000e050103440130b842a680034401c1040030b031203204650400f01c044605090744c8807500c8a540109014001213580c031890520710705e500460315034800c0c01c0460000d2200303a0316103c0342a440d00c40707000140300081040038000743d641e0207282210b464502808400f8039090610f4402c010742c09030360500030108081c503162889040c0f85980cc8008866107540c1c1c0d4100c50030800b40d580c0701000f103100064070502c0c94007559820f00320306c00100c0d01400c0d6100d90102d846505407025100810550340042d02054440c80e52046442d81580005c1c146d541400c20fa0758015001d4590b09040b00c0d007020000d4140c0e00c1005100c0c00940c0310207426034084000e281007440c80d110b0821108042e0841c2d408900140b01300c201841941c5420303c1040080c2049142c0341070002985c10f1100080d03d040c0c440d14040c500c05585000c2952203505901030b0002c00a40021000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 628826978 1250 628825728 628825739
    0x11d030706170a09050a0b060d0c0b0a110601081b040f02040314010501090b0105120a110c0309032103010e090f1b0f151801050c0a050c0a24030e1006 66
    0x8051080725542d820450401c00991000054818902c90b01e801c50028150445c0c01e0396220040e4501821190780107520b194400009182090380b40c1c00b52801044c082d80b110503030b82f80602a44141102c00b003031500154014000444001101e5159540c40442030300501c207100080303002446068040d0003124000140841807210082140800c85c0c0d00b04000c1200e60380e541ca244013140c0d48901c030746000500800036005100c2c003074000503030064a0710200048011010100c4991503000c61404420f42c1c00101e8014458a42840180409101c420301086010484d01413110b0350301c014010308603c80180303404a600307608100120010800884100c42c40c90006582c108280343c070510f405445080d20340c000311124105203e8205161540c4241d443c24802d91080c2082e91004041c182070401c5014440c0c0c04816504006004045000300e018201c0c207004a01840300b0500143c0110ac17541400d076543d03e400c22030220308400050007501c2c0000300d0001001103141004c225502c8801151306201002c02c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 628828228 1250 628826978 628826987
    0xf030a0903081503070b0d0e1c090e0f0103060905070810050a060510021b2202030114010c030f2312070f0309020a052e020c09011d0402011d030706 65
    0x503864000c0d2907500a80d41d0740d00d0700a00031030160a42d40d030540c00403502003040e4050382018055241d60f42e000451340310203010005181c020241e01c04040001c540b203402c5000707a0482640006086070081d04140307841d11700c0380f0064140c010300c0003c100554403013160b4144881440307000c010b80049010b603140c4d0120454900702230402aa8118410b5140000014403407a0155071032000b000d054000c0d0440c414603030841c91402590740d03400fa03041100d81c50700590314503640400d6041d84514800058903941854509804501030016060502c883c9448a00210b0340220440850007943d2801c0c03039040d100e81800c0d030181c11444120602c00301011840f804040410038003d445154144c2c0d032048400c510348030840c00d948050001a42001c58601c2c140700a0414040f80030a9903124980700641c0400b080c4d16040034600d01440c0801a004000609107038913140d00c8007801001c4500d80d5001d140c049204112003680c01510081c14880c98076024045550048088004608010706690b01d55985002c00750 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 628829478 1250 628828228 628828241
    0x17070b0a09020a06170a1a031203040b061c1202071203020a02042403060b06040302060c070305070503070b03070302130f09060501030b090f0414010e010c202a060f030a 74
    0x24403070714010f50085183c1d4840d0078001c6075110f940c2064583c83d100d10454a00912811101c4038980d80b4101202000d910100540c4025810f0480020b0b40da14190802c000d10040c040c2c83c1606c81c000030b4101e004030192a10030840d040c3d8103c50050301d10000b12009a2400010768084600401030320645c81c24140c0202d01c103141c0c14000e030ba041c0465640f10603091820401003906036407082c800401417001c90f080d0b51140c00c0d0420040c1626250640f00e4001402c0b98001031a240341652010303d0500800000340014402000142d0051004a040816602071400000d18400c2050b901041511702014020f521200800300c86903000110368646036414003414090160318046810859061403a04208000350311880c8800070030341c1151115030b10208410503900002c2e660391340f0782c02c520310841c1082c4990103c42c00c01d80c68501c0d03840c460b180020117031a81d82c0c02d48074080d040b0b84d900c1010401c04003041140d02c001d0440d0604400466030014119008107007900441176404420810403580c15030202 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 628830728 1250 628829478 628829483
    0x307020a0c060f020f0705090a0c1107030c0f120203060f130b01030b0901150302030304030b06240306040e371401020915040b040915080604030804030e061617070b0a09 74
    0x17030300103004145880f907031000d8a01c203c5070403002c1400050f54024151303014000a50031403602da906090031311041b03882c0ca4110f0700291400d1285440810800c00902d100b00b0040030030f910a49020340131a0000398903030741c001301029840c80d06000003a02118070240c001d02e1040c1c1c02a146505940c403070a04003030640301111108074039840e0810200300704c00e1200408045175801002507151904541d580c41e4088800381005030085449501c0078171304800c41c00c00c40140401201007940300d00c0d050041100780c2d0520303111440f840d04121101001c4400c0690701004080a00743e80355030868105050819103416501c001c0c0c08141c43c2e1049030341c48031041d002488404001c903080d0100034080007050580b441a072055981440c0200700070449030040750401d658550602d681100c81c10742d070328503240c00d01004031411070001f12404101320416400c4100e6031420b441c140c9502e03041c007a0460b087c800c0c030300020102600d00342801e592001108910401ca681701a8401d4048410b8107200e1060005800f059208 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 628831978 1250 628830728 628830733
    0x1505031504140f2a030a050a0c0e07170414010c0302041a0301061d01020703140d031d03091509210606030105040b07050702041b05121501080c0307020a0c060f02 71
    0x160551082e001403015003105610015110082c50368036201424255500c074a0850080c42514040c00d07501441542c010a0184000c3d042103400d81c601003180038a150405448015090144011940c0c010144041160014003060054403182009180d42c070350070507085503540c2000b40e500300c0c00d07078580c0280007209c84070a0706400301d0071410010390f21408240a094001001c14000140e136040d100c2058001c0304060042e9166903442c2e84403041c6056500040b8001c9500a6000c103e04d240e042c4a1040c10805100307261008200481079241c50f4031036158944d1050183c0c80c11320401000010031944507a80080000a0030641c00b00041c0030b092227221540c1c00c50052600084d0070f828180906407045170710820344601a62009011340b401c0e001908141d821690f82c0e003140c94a106100c3d0f40b056006403d8840e00d4890192480d400208500105002d800c010a2203450704242d07000404241c2110101c5c80080c0c40c0e654014080b03290004202011b0010f440d84c043c0040c995400070180b43d8050019801d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 628833228 1250 628831978 628832003
    0x132d0b0409031e090b030103082214041a04140403080a0c020d140d050f06240f07080f03010f0e06270703090516151409041505031504 59
    0x300001c5495214015002c140098140344940c00007000d140c03154800b609003505003036181c0245000b40d4109810885000c074001944408654081003211300c81042503104801d841d0500c1e9182120142d60a00d19004545842540a0982c17203d41100c103461806801040800092032801c0740900b0251801d8021800c0c0c0008501101c140e409400e4441040390003c040c000301d03529080300c1c490800b0380c0c041072000081c04000c80c0c003141130003402d01034040c1c1078690714541410810044002c115244202e419600080004501f58003002a508072000c0f040e481a1501124280032800f44215801000c82c0c4100100101c0d40e1251204801c0c15601000c44400443c0c1c2c0316010301000c400c4801c0e001990080341000c800c0c92400b03405800b0b0340b005045c80d02003896004c1d81d4a9a00d0000b00303010032507010602c0001440b94026142403544000101d11b0401d82648002046120034403c0d2420039001d1920f503c1942134a00071460500c004080240844000d0400e907454287d14004c01c0c0c8048032081d00907032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 628834478 1250 628833228 628833251
    0x3010b31051302040b3a06021201080f07031515170102030126190809180f0708010f0b03040c030c06030b0f0a0f0e0a090606030302070f090515132d 65
    0x2050b1080041c20078808441030352070801102c2103a292210036608034039007906e5000040c1c0b840c005414070940c0300d0310300151941082165406e260b038032489001030703070301609040000c24000d1708103d1116101203000100c1c402d141d104c2a0141003681c04c545104c42d240b4424900e007010550003141218004203040701c07100c40040c141c041c0e0001e4440119841d034405c034200510307a040c0e9907003201c810348240c5100d46801c03140d6011450307010b800c1c1600c10703000c2c3c01c11081020075482610820303403046851421001c5981807421541780840d82d405a54070036100800001d0030410026902005150050140003503940c1c0c481e402000340900c10350190107407004840443c19810160001c0003598281100000341c0c60a20000c1070251500a01004100784c445480002080c00b0b0300c03800d07024500079400b40c00380301d040c8102e03503811280d1648124080752078081000b00b8102d00030385003452100112404140c15084406040207004241ca0381908000c038105030401c0041110501750b01601030920902c00c002d19171 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 628835728 1250 628834478 628834489
    0x20705090c0406080601020a170c0105010509060a1a04091b030b030c0108061e041a01081012030c0609150b01030f02070503030c0c0712080702090603010b31051302040b 74
    0x81d241ca042050061006102803806039181e5903008106104640000209072101203640704010880c200d01e1000090441d0303248400c4c02070b94003404041d00c1c06c1d04141046004241084070501c03c01c54000c001c1d01c0846800d004a0b4102c3e0700a220703401040c00303614902d03401c04401c0400c00000402191400d00c90103024200443d142c0c1c2d03042e4058450002c291380705014405440305402c030b07810103006101000e820b20b43e0307613205428940a229a15a01030b038078203000134001c5d03040941001d4005010400801c4181d40e5603540205142e414a40014150b07070710719007540a0200620020a02103c89100503e40000c03075100c0d000e01302d400d9800348590f140f407981d698100e108248001d0500d420402c001401c44801c0f200510001040000311811141e55161102202d111240121076056000880e030041d450100e03506500000c084008001d80450320700080c0c1c0d00402511010784001400070605000507440e003c059000b09540014805468421116402c000480d00124403552030300d04400700c40d0420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 628836978 1250 628835728 628835731
    0x21061008070e0a080706020d1b030f0314150a0518130c080d0309150c0c11030304170f010c020102120114060d18060b06090105070809030a1a0702070509 67
    0x24100186285441a0884903084000c00860501190080d004500d85840b000c4200400115020303158a6080c914000d082555002c0138408021f961128002c0f40b1041078455100d46500d420111607400c1a003800b030b809403408401000c04100c4400800a007100c1c80704040708105812503418400ca5211410400148074544901c82181c4020300000e48040604039a02041c2d400380c200100380d19618001246440061001000069141d0071010100401864850075980e09003500740f041786880c0500403d84054034501030715400210400d85034944040c4101c601410345e8448401500e48244003444d6070f55000c245485103580303071100c2c68070388600c18400d40340c103059001c0c201c0e812039180c00d00031240c04130103100f507540c0500200b203550400300c541d2044c2c3c014a10700364402030110300181081c6080314403030010396014000400140086a0380070080341c46240e40150816124400301c030109191201e10350005144d00f00355048030002c0c841c0403003007610401d0581d086541c440d0f1a0814401800780 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 628838228 1250 628836978 628836991
    0x30c2c091b0703030b03072c09030a081f08010c030c08060910030210030f0f0b270c070f02090117071d06121f1523060318060a0221 58
    0x1000d1001d0000603100b90000301121740020101c80045880f044060110f45014030101046a001004041a0002c2c1b0703a0305588150b80202031420030050f80d1002d8041c00c001806e0008201650943d009a1800100f10401501d41c1c3d00007004646c0301c684000e0300038144082d42c000451104070010f40d141c5001d0107013922070115664250340081c03656003032101c00010016004185503c447d02e01207813407068490172000c4085818085003440c451800c0c00100e142c560b07541a000c5220b445406501d00400800303a030014050700c45180e540076241403000151082e4540250701c1080200005482c1c0140c1c85540b4074113011805507841560344044107020f480c801e5a0030b40704a0413400c00583e2605d008a0442441030500c02a00c002810b003403070680c094a102044408c41603a240700d4141d40061121901c4041c0c550715403224800c80a041d51480c150900003010751141e04000001048141a18400300007462450202c84c45824080b8090010b5040b810754080700c65940c0709040070368110000040d0060a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 628839478 1250 628838228 628838281
    0x50925050301060506091f17070f0806030114010e070306090207080909060d03020a170903011b1416061119030203040605100b07060905010e0f010218010c080406030c2c09 75
    0x244031f4116000e0b603080b01280805d200162100d82810741c800b00b01c040c8038640700d50b50054203001c0500d02030094000a46410b00980c9054017130b000641400c0421815150000c160f0469507a5030320040340500303a90f40004650034008103001c4108100100544207140c400c80e25600e007555000280101d40c0f0000c0300103070042e4492503c1d1800302c0c1e085828030a01e0f00110781c403145030030008000729003901c2c0c040f1175001c108a070281c1c1e4007410550044c0c203402e18003034140d082460316018655840c0d0009080704040c0c140c40c0c1c4ea402441c8600760407000c40f40c0d0f0516000c9150041078007102c01030002e40040342c00faa201030405000038a00e1500340d465400f5140401c90940c02c1017029100c40c001090004000c54042d0b603201c0d803d03101e0300002c01c42c81030411b510800250391035418000a0685010341a0703091b05111360300c40c0a00004440f078007a03800b80c0e801450005000200c1d510b04454030070b0342442d086030881385550b02d9245410f49544d01c20302c0701d9041e202c451064a51005442000054580d00c09000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 628840728 1250 628839478 628839499
    0x201050708090a0f080a0201021614060c0a06060b07110402072307270b04090c0315020f03010f0608070c030504050d050106030b0703090326070305092505030106050609 74
    0x8031500080c140301040540070f071200320344451184400724465007010169500c0f419000c811981e0400010b000e0041c00c070300350000180780611000c080f0349290011841000041012001300f5000c0140030022500f245040c0080da82d01c0100d07414551292405803110070308004040124181070007120b0b2480e5001c5001900117800c5034114800c4000164000d160340520100020300c403c642000084a4542d48a0000f0407001d031204842103405020300c031400f0354184800c2d44042003c407040c0c40101c07a0404030402c0f00c040308d60705101c000e10440c4102c04070f00f07501000220b00c5048501902c02943c54540310140240c403080d00a6801d1141594001d000800400c800d00c503d0a0042030551700e0b601c1080042801a00c2c1d0303590980500702140c01c440026505c80300038003810343c400805501e082c00044070011800150b104282c0b11500182103070141a15400440c1110f40100039006c03044840202219042c1c0001100d00d40b90045845414825801d1440218103443c00808685040d0030007071907030817003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 628841978 1250 628840728 628840733
    0x1603020f0106180504050f0601030b060f0d02102f070f0902161b0f03080c16060e01030b0f06031f0501141c0b060301030605160311070f0c0b221202010507 68
    0xe0003000b0170480c2c482c040d09040000d007a100304503c0307000e0752180d03107241c40d10302e8030b841807003007103074034140c115104111420741d5101684490104e442001103502d00303c0d03001f40c076003c0080c00d42c2034400c00d20326082281000d0613150401c082000303016217010080c078590260390703018420142d0007140722030004480380e00b80c5080020070044e070710034403444011148500075950303000d041e10000c11503005a955400010358103944030800c2c8841810f83c0c0f10f03000d5050005060031300062499085680140c1415981d000a510340e590306850700c443c101e00140f0b03a03030352481c107e05240d85c0e14698460301ca808600001d408280d940c02000e0064000d6003c80c0c80c2820a00d00c80c100043c2d042c1c0c1c020705840c040340d8032546800c85886a800542c0031354000c1c080030890f800c0444456440624042607a01014a130000302c4040202d032008850482d9000005150307469202e042641205e40b8503807003070f14003010004110800200702e401d0549a0000c28800d603401c0340c0da40e904841282e10307008000340011000c0124000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 628843228 1250 628841978 628841981
    0xa1103040b160216090204240f0305091c0e040b0f01050d091b03140c10091e050402030a0c1d0a03030503070e15090910030c140d02061603020f010618 66
    0x181c80707520f2044880703040e0100d00700d100507504c980004000a130001801c0c4041007032208204064040b6241c14442031410b000300915000e807900c00c8800701910b07200443c030402c804002181d40b800f166000c2600c0047d0612002d401c469260380d2080c000c50500d06d0108003840c1095a0200e0030074181c581c03a20b000c20301183c10700205144001180c0b80100150350030303500354107001c4100c0518440c00342031000c00e05c00d208191601c0c41108180e807181811a40c0061000e82c44100342d02143c55890121040781c078020308507502c441c0386401094025202004124180c0103e8000343c0c5d8640c0962103842e440041d40d101000142042c1024a80150010f481040064030800055030b2100c1e29141c1607440c2056100022041ca5940e104100b03096400700f4900207030314250401c1c2d90400001c2c038284017090b1841c0d5940d491032446100b00000b58080402c070121940b0b5183c140701e4620740c02442c0a6650109410b0441307400c1c4100f0b0103400511a03412010501c420510507501582c1d089405909082604000c940 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 628844478 1250 628843228 628843261
    0x40e0f040c060f1b05031b010b3a0b0a0e010504121808070e1b0703020a11131503060c050f09040b0109170706020c0a0308030604090212060f0a1103040b 67
    0x40401c07603074913065028800459501c181d140d2040b13019580c2c07044183c821f000c000307240b1740d081d40c40740c0d14150000d8100e68616001c60140c2041c200c00b440c9107610703098401e2038114400342900b0f038410091007090811803e07800d69841803181c402d003000100020142e0f00c2c00c81e0b5007120000d1400c0c006000319084140648118110096912282c25140791101c450320b040881c642e004900707441004080c00751030305104e070300820480140340b0072606050440d10000c3d540e02011401038655900780d444480203441d4042d4507440350a150170144200d900b120030ba04400941807100b034811900d4045e251100c02d00c04d1741100c0c0e411300e0b06462242481ca1a0003007000420143d064203041c8854840c001464090910241d08504014405800d0040c41d22001905220100303081900c00c0c4103c0a0910003da400c400780c0740c105509a40c0080d4250551000c50b105d0910340da0301c44c20500c10081008000380d4070300400c61240403d100c040c4207800c0803034001c06140c0020b5600030084420308000580780d40c43d240811 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 628845728 1250 628844478 628844507
    0x604050a020c031b07050108040f02010309151503020f09100311132a180b2a03070309050103060311090a0b3d0206180a0c060302040e0f040c06 63
    0x510384900a001e07145160b04c0081403160040c03c04025030382c0c82c0e00a12105005081c282030503406890155031f4102400e001d080000d050503034809544050120f007024489070050f1510040001042c0002c1c00b02003200240701c02c910030500340306202920709241030100c2c0500c0002401e0340082d030441d0364110f410200c03403d4070f07070b00609208095038501c0000d008242040d88802c2c4605025001d11240d8642c0f404840c0480c802e01c400c003003065899414507141403040321000524540c0310303040036402c82c0155205e00030420141d000c081080c100e4030b602100800220f4460748800140036035481c0154280e0b80c0030b200c094013a141e40d01180000c1d080c07400c07803c0c0e40008207100028911600e880054807040408500c40c0c80360600140025030343d421403110594248504142a01002541800950b20400144a4150711000180b0310f43c1c02402082160140d07036001c55100340c541c1d11550002c1c02034005109a444e41d01d08413000c01c0f1182d4520b40080e000d0360300b10410303141c1c0d0703410141c041e241c0100c0b40416 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 628846978 1250 628845728 628845731
    0x30408120a2c030604030903020906090105091f0305060106111005010609030311011517010b0103020c0703060b13020a0806012c01081008060a050f07020714010c02061b0a03030614090604050a 84
    0x4400b0b50b5070034406035114604c40d81f81d0001080c03e50042c440000303402000d8034091030f10f40d0014061340d0345200615501104c104602c03200807000c1c0c04580b00602613a030009090b8400e04c400480e41507004002785403036140010450f41880010301e550000e40c2c10a02c10400130406d402c800f0f1010910601c0c9000c14070114500206849504030400007624445a202c0303241e1400700d4440c24582e80c002c0c01780300140d981c2407038103600300f07035050450030344400040c80024806a5100c074292600d80310508a01040241e00b84110f444007141d42010307181303100488210740011b03203804448094016601b0100072410703074042100048270700507005440c440c50181c80d03424170104428000819070030400a0603c1890700c050702092504152803403060340400607110105540201509110b07164001d0214046034509280401810070a40045851489110200c200341d00e10f6862402c200795000800d00c90a40c0b181d034007040302c0b56a940500300b40c000d0131139416034000c00710350210b5420314080c0c10240e0401b080e00340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 628848228 1250 628846978 628847057
    0x210c03050a03150b0a03060501260612070b030a050a050105101719020d020c0d03020f0a050706140906060f01031116080c0316061b08041220030408120a 67
    0x2441380a900552101c0700025100c0c4030a115559000100041c140c0441d4404904002d03082da030801d020400030903950050500d42500d41104101704603080003081c0300351007287e59051912031800540300403542c29080c141800b000040900b006c0301c480c120301c552175583d0700400f0340343c6c00c075030000807030140c03c801b0038002408801c1c05040c598401040c00154403080141e880b15000001707428420200000420702d441071055104d002504011107420340f14514003950358203000c4c500140140740d0f040120568868404c20007000c0304000543c240034007004c985200108042a004405036061000c1406c00c0480c10f106a8142c4c510041400072349911071010541000100400b80d480c5800154100c1d0000400805000602541d4420080e49404041a4540800042101a1908001802c01854019a014503158192094022007080002c0746041801d410a6008450348c940150103910854000d104840321141c070600c040340e4260040c0d40b00c40340007140c940428040400b03078007500d0964040070172 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 628849478 1250 628848228 628848239
    0x10f05070f0c090e010501150e0904150f27081e0c060702010c120209150306040b040507030c1206051e01140a051315090b0c1603210c03050a0315 64
    0x103190000f0b440b584800060310f42c0504802401d540c4180d0015521450114500889582c003000004c06400c0a0702e8070000798032107240c41c2d18481c01900440a01900e010245100a0300d50740249444100c402e0004019203031f010840e031600803000400503c401c00030070291007101b03050740082d29400030618082d802e0802c01c0b134110f4200750048030b0410040c0d41d907208000c5a0313030308071000a6400c6010b120460500e6402000b03d9131005c80910240230310080880014004d85c0c440c0c10002513142e000d40b081c0100d007000080580508101c0301c0000214403003400440209a95120344002c03181c0c0108040d2000066004490350014803554560420140c4481d600010882000414007005c2e90f5480d107903a0040c441081c1045c03004c5401c441c00075161007440c3e03000c00c0e42c00201039013070356071a02c0869a07a281b80c880c42072130901c154403101400202e50304000203219105910001c101303210280031821021000c4200d42c888060700c4004c02140f818401c000340241f083d40326444102003070000680f11078440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 628850728 1250 628849478 628849493
    0x30c082d0901090c0e07020607030b2107180b09060d021207030f020a090c02030d11130f030618030219020609040908030702161220180412020c010f05070f 68
    0xc444000c1107a4590b43c1d504100400c800c040c50040034180b0700d00e4074074108148001d407a5000541a402055110f004825066a174079541c802d810b5640303058004004107180846445030490f03c941a4030007400a03008501036943c0c001e88074074150081c90184a941d5101c2000602090082d0680c0c102e19020080e10303081c02c0800c501c00281d401900048440c50030351041081d090301d80d400080800d424409419020b64001041c0e0720850b049110204024680701d000a00d90b000b0900c5400030078100200000d40809054241d00079240114828055104a03c1405170000603004008005a000942c0004290100c008861181e44024940d6141560140c0000c041e240b0948044e0380c142c2e07002080c02407480e010007040182098226081e2407aa1a04014050701005100064424011110509142c0040d03061b0f5041c002e400a016003c0f00f06141c45d200ca5003881203c01301c1e1101c5d06120750161090000400740d400a030141d48031529401118000c507642e0f00810f40884410000700741010018086 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 628851978 1250 628850728 628850731
    0x130206030f0a0b10050d05150307091e021602060d060b0a050d050a0b0102071a270a090902220902040c080a1508060a0e0f07030602040509010501030c082d 68
    0x6811550325070b07040c89080036044641e090003942c8620701e030640c5800d20b1a044403c0d40c68a0000c2000045d1a41c0e0b9202c0e044100368000d01c41503403500407a800803800b29002d03071180801200b0710354411001814020390900300e1203080c4000c180d5034025009040140b074103000800c290210b0107008034801e030303036078140221981000f02c000004c14000320304108070390360341e1054603406000d044051201d89800c1001039203c1003a4019164036003400d041f40413070426501c0c1100e090134801000051148034860510000c42110a00c05100e0411200e0001e142011801503101c1e1070340091030031034038071900b808800c5010a250a09015240c0320420312015959a1150075400712440d11b0b40852450301241031030459000c40c04080c80000503010034800e0841c0024201d9200180820002d01d81540004581c50490004001d0281d445400c1c0d000c82080b0305a00a40b0407640c090391000c03d10390b241c10055007034074000381000c400680c03002c0c0018450f80c100e085002d01e00a41c05d10400c0c4001c00c60b0210014001c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 628853228 1250 628851978 628851991
    0x50906120702031902031e1201030305030912072306040804090915020a0201060905061e040e1e0a052109010e0a0b0a080f01060c02100e0102011404060c0f030b010905040513020603 79
    0x1289246541c0c400010104220b5051f00c002c0c1d01d41405403800d08024803041c08050308000313002c0001236054034100000a0440b915080c0039072035224a182c6013001654911400b2032805d003210303148140650011b81e05000f03662040c1024189410030b0540401084001d105541000344503060200c41001840204a5541c00d940081005410822a0415100081d040c98002c1c0c1c3c814280851906201c080204520411100804c45417410864949041100c0030120040308461801c1c0403a040009000341c9002c3c86481030b00e0700c0c0000c0019050000701c00c003100c00c0c0c1c2036200f003102c060950710074036041007034040080c1180c0c001600e41d40210303c1c4d500220345402c08110f40205024050b6600051507004007110300d88a50340400300c0c0d0100c1c040d01005074620080c40511002c14400ba8003e401c1a0030318000c55090035090700d02410010058400340301c040e4041500c01c4d0304090104d00c2401241500c913010b071100c00c011072504042c400241350050034400c5140c800302c040001030303440e0401140180c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 628854478 1250 628853228 628853233
    0xc0b0910030c0905060304201c060207020d02040c0c050f0102070b04030f12020315030f07050f060d02071205190e09160504050a120b07021b0607050109052a01050906120702031902 79
    0x964480013440446045145071260b491203511100301280c510408149c00c1d0302480158841903280701280ba05c0c6940d1100941c01030404003011807481d0701c00e10000c42d45018a040742c50080d4540140c03403c0f4410400040c020000742000500824021200100b80a6403841c1040040291083c0c07501241c001755003404c001410441100a40e1604010600c1050342c060058200315140500140084c4980d0f41c07260302811b40852034201c0782840f41d05a80304039070403440803219841c600400800551151150302c0c814480440c3c0d4003101c5108580d0b088500320041c0141d442342d1078800c0c00e440c05190140007031040040420000c142c540301c0038a4000189a12000d00010040c545050103d2000c001c2c40300301150b02240b1082229202c00c8005112904252a140d659034114108a07015000c00480605148503081d01c002040c060026407035503800b400096213107596008401103032648520039820780c2c810400d0000c511040d6100c10415005105801120b14106c451082c11001c500240125005038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 628855728 1250 628854478 628854503
    0x100506100801140103051e0c07061107030f03050c1b07080d1b0807140321240913021513050603091507050d02070b040c0b0910030c0905060304 63
    0x341400305180112032040d041c809100d40c18081c125040001e0180243e041684440204104848090202e0a8284074250140075803500c50014601030703005110440c0d41c3c078980640f01006031111030550f851503a041e0b5a00c0011144034804901820001d09038008501041110385089560364030100d100d40c51400162480130300e882d42041c2011800000d510902c0382b420709444001d000c0c03000060203564440321a64841005041c41c035250001540444018840040c05c21010101c0322040c501c4904813036031201803961241c8407803c450410b0110a03500040056441d819031800b1018507078030407107000150b0348004480c1c0001e6010050078807482ca00c15030000318181e0440c4102404405020709032029441d43c14401c00f40c41d55041c024031550303030003510705021800c0584039808984c81c0d0860013600355100d01c41400d100240b10415201103905c04100d2000007164002c150079159641070050414400d4a030840d4241d000e040e20300750540400810410100c0c6a60f5508051409140a500102c506 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 628856978 1250 628855728 628855741
    0xe07030c0311010e2404090f0504021f0c023d120908161104111222080319051608070e0a17010b121606090815181005 52
    0x212112040e5076040014000284042e500c0d501c200583c40c022001701601d15800804141c665030165030468512a82000ca4000c081300254000760b0045000300c410480c01c840050804503094842214000454424200718000d03140444141d0401c0301c1000b036000d900d221040203010011071413116440800e1014885050150744903e120300c1c6400c0c00c0c80308010105190b1a08580790080d91082100c0e44400c000190030441ca95108054840d006041400041d9210784c202c40b468012078165011008038500003a60702058a403020006641703030303510403650a050340350480180c0c0000d02aa010005140405003c0c01c81480740c14031844281e031700e0f25038030204900020a1250090010010840705944420072a9240e001490444110345034207031601e10304505036800741c8504540958000b440c030001c055940f001241007074a461600a01a80c99a26a1400d4074440c1c014007403140d090780011030031524070444031403160300300c08118140703100d0441c1d1421491030140c03480e1007144030b50789980a1022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 628858228 1250 628856978 628856993
    0xc080a091707030206090d060b0307080319031a010c0218010608041208160318050a05010207140a0f02130f02180a0b0a050712110a1226070f030e07030c03 68
    0x40300c0704600509601469a0001486400340090040c820410045440c0401c0170b950b001150480b806000c0c0c540d441e03a215409902c0e82c005445d25120340d21500300914905100b40b094614050340903107459074050f1200011a070b00200050120382110000f813501055000c40130391140200b2103944c40b41c0040c941403909442c007045200329030301032150300e400303100701c003403140740604031074940762138006500018002d000125801d540340282c014090020020180038043d0010804940680456010201142d03507155442c085401c025203140000c050311001450840711500e030044039100007003a4200302601c9042207074410010300b1003071000c0c0e4440e50402d0514036224401409200100c0703082c2545440060a030b0712600d28020080181e100801c2c0c1c0343d60042540c5d00e0401500e10032504010000d1805590101d1041041d802040141140c644210b800140c000101138020040d0087c03505c032640d060385c100c503008184105150301d80d43c80d04090041001050020760240300744547c0716146041108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 628859478 1250 628858228 628858259
    0x10605060703021509011503031107050108010501050313083001061b170c031201080111031003030e030a170901080a020403020604050d110a06110c1210020a0c080a09 73
    0x2405014240078100110703030013180d010203001094030303850120350700c02c0e540c5801400500d00170380c01e84144507401300c14103a000c0c05c8034a0101c480400c440e180c984a03401521b1a0100744500f40c00641e007040005c00c20300400c000b4098407481042040d00b00002103544588041c500848118200100050350f4100550400e20500411481c10081c0c41c4101506c0b4840c0545003880014081500c0004c03210800d0900004541059909200360382d164490703181038a400e10800c0c414040b0300d60030003541c02116030744141220300030406800000201851554280c0f030b8168507a103820703031502482c16400301040045a0900358003042ca05140e5403a5901e0002601030070f40a003210740514414041840142c0f11b00007150140d44c4216031040040080c0d20709884e01d001c040300356a800c1007250381c0c0011682d41007035001030150000d80558200000349001d00051004005000800360f201e071211444500090b802030503820f000d803524001006168440c00c10325484007403011b00003242481d040100e00c01d24240302 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 628860728 1250 628859478 628859489
    0xa150b0a0c0b39030c0a0c080d020301050310111c0e1002040816050d082b05060108060d030903020f06090d082a0a20030627150c0c0106170c01020106 66
    0xc142c1c44040d140c152046000003005d0f00f50301e02001980540c161700900b6001141c65010a030150389a141c5005107000e50020310910b4024410b1402810154460f40500b626010015007194100440100c100080707a03038645481c002d496a80390710741507841050150b9071b04202c140c100503940c0c500d450081803811100300a500305503050100240043c0d81da039510342348401e40100c00c540c0c548000140354600404040d14070f030148080380000c4180c0400b160801440740009803141c0d401680d4003010321a01c0748062030001c00251040c5424001454280c07a07246801c00003501481c20111444003203581c1c0703118a402903a41000100b0180400c0055031103840d01b0f003c100054929904468407030603a034644ac22002056584002c3e40e44e1007403400b110350070b017034200d004040310003509010700090b88180081311f164003080381088100d01c00c90b10004407400308003141d800d484540c0c1e40392000f85070710b0341000455810554075200002001e89901d40c000d0040d00403407000d0301341d03440d02000190840e03c0f0703540003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 628861978 1250 628860728 628860811
    0x24060c02011b060621030e0a03030806040504050c03150103021c0c03032d120c0801080a0201031805030304030f091e06050c01060302031006030201080a150b0a0c0b 72
    0xa560060364412007000c401c80c41d148030701d00e841e2401e2500700302410075038021004852954000d40c11039050f11341c2d50400740e40070ba140e60031305002410030b120903031400340805000709005001003011810035a0005034424017807010380b258a499940000e08000141051460385510741780140b040d4507000d0146074403c1441501c1603800c0916540d00365082103144001b8080c00307076140d0303a842040c40c000b00c00b2113040340b45216001102040c030710107800d500b04030611141161610302d095141c035001d121401c0c16501084010400b01c403860b40118050b2158103240b01040c00b0700504500020b10410196000340e12035100c940480005140041c40328050394880307004c203440d075521104210428a80c50003a00c0c803520b8450313610104c03240828058842640001d4041c03040b001d042c00c90700610303804032040d603200b42e039001c2c03050b100c548015003602c040d8898030702c2d548900001002041c040f80d001340030404071400e0004180380d1030340391100f40c007004494070601c50b031900843c2e0030a800920444d081a8510004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 628863228 1250 628861978 628861997
    0x1005010f1a0406020c120a30030b031c0909060306092a060c140706030e0c19060e121204060305070c05060c090a0902030a0209040e07030f02090a0e012406 68
    0x100a40d100c808004542c01040a0404200c680c0014012042020b8102040d104510100c083c80d46601e40748c0305140021442c01c1c044546094442d0003050854030008008018190348044807405041003c210503044c01200c400000b0004034900445000310b020741800100c9200703a05044d0021f03015021607440d9440162209a048400b80d41d5080641e44540b6101d50250a00d162028840c168502d60054500c1002d100144040e4950841401352070a80295403401a140007031020003035400e40160460031041405011580c0310310007010142100503d8425042a070008860400703810030b01140d100003000509006040d0180101c2d50024060308e0700c01420703016521110748628005d0100c50036074000266070703c4241c1c0c4890403200505090720b01103650782440c1c851306001398000f590142c06641070a5451070403420109a6030100c0c1d401440c2c400300c0c01c00c507500b001310800009040100c1d40796a11b00f62281041c09104010019286003541c01c4000d0b0030044c01200401254400e10402840c1c24 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 628864478 1250 628863228 628863239
    0x60608010e040b0c0702090907090b19090e120d050105031209030d080705310512060a020c030d061e0504060609031b1a030a06060305131101021005010f1a04 69
    0x111003590050f00240050240e8498291554480c40f641401a500c135140d0014401c0802c0007103040c0b022240603e50402c9082d0b003107003c3c003e0031000702c1c1d201041000e41c0c040401000c0060f400a0f4442040c4a06403020381400109401c0c0d03a4001000c44988261345400511841c10b0401c9200300e419040d4040600703080421000039a542c1003140403904104120021641250160f02a03a0320000321f030040488a4000d8801c0f801c003400014000e4180380490a0009010309107040d0051203815180c0152440d591007245d075001035403100c11403415511003000b031a03100012500c102d0000c4d200e200030312200304103000303000300000c0d000e80c200500c6185030807000c0126a0304804104100c1394401d600103103a00f00d84142c4400f00e50564098405030550800c04205120760707100552081003026402c11030316848110071412984200c0745042062980c01c04100403a00c1d101d584811440148115122a10360320055030644000380c2c404c065800d041001400513841002079140c948102c83c0504d41020f20b401c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 628865728 1250 628864478 628864499
    0x6030504080f090409060627020901080619050d080c010f0e030d0b1305010308190e010e060f1b011a01020c090402010e030708010e0a021e031f02040e130606060801 72
    0x200c01c0700e0b00d144000100d462207074949420151005811441c1005129956080c0d9070203585010346828030300074280e0000c5190340884c82500d59034601a511440e00c1c1c0d540409000c04810307480c090040c0364000020001b6241e6910761150143c0d03108500954555008002c51801d4a0f4141c1ca1001c601e41400300e00c01c0070400000071380c0e1824a03440e00115004110402150508010781f4043c100305050200200c103000d140705c0244850001c0c031080d205400c074420170841340c20b0359207110580040d5142440138041c0c64208042e10000420302c614a00d44400c0f0111030307000620004019030117946801100c0c00003c030b9040080c60005c0280043c003000e20403200084e5080f1401040241030010030788205409480410000026080740c10003080142c030102c8481d941d40c40456022441280301e00c20000854107804880039840801400902c22114081d0710000c04d00e81605c0940e010590130b03c00040c410204402c0c07103008041200000ca8032403800c1c02d00000b6282290410380c140a50743e001001503880c107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 628866978 1250 628865728 628865737
    0x501020607080411010c0f0c140616170909090606030606061e0c011404060501230102032a070f03171204030c020a030b04081201061d090a0b0a0b030f010603050408 72
    0xc42c0c4130f2180440a2401a15140c0000c080601050f100c1038a02c070030040d201540d070081d18007044010498241510401800d0f21030728164450f00100c0104403000100441540c2410301c5207403507914103202c0c83c0d00101c1d010342001c4802c0c440981c440c40034450300713042c240016034100001340c3e607540c030b459103094480740c040c1c40b100d01c682518603000408800c08002036110880340c3d22903486098081c107140c02c1c00806000e080c098981003c94003c01009512342c6241094455901a006542007008410380c49400042c02c0c0c2140f030100c14402c400c050a010107016a03005000544034402c0c0c0a810350500040c0d082c1d1003061000e180c07104110705950210002a40e6a209034946007402107482c1d1403001c038000c46501c0e840245210090007e2008201e40360010702105c00301a840c0e10256a0f840c0004c0f5400014008940300324440d5100000003403e14020180d03200e00800d001013800c088907070101e040b916455004088074180801030007000340070507284a006188a280070311082c1840e0300c450605108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 628868228 1250 628866978 628866983
    0xb21010506032e03020301060320040c08070518120d030b060703140a0c0b0a0501320d0203070e09240103120804030225060210090b0c03101212080105010206070804 72
    0x100410420318080903c100d100103182d01400a00050740d8a1400da1010b01402c18228080405c111004090b400d083c1b080c441c109200d41c0d980c043c0c5864800007a02c40b68404030340c0b03c04020b07260b101c151050321810310003042142820024035040f01e0326000141218003881085106000400084002c40e51101c441d115443c0c02807000755582c3d922100607030380e00d89a8035008141e20140340801003005400d900182c105d0b04500d01c0101070030392421304c5c42100d1042206034608190381200601d05130422440640c10184042c00316000130f0340b07480702c103441c500b000c0716840c80d40e901003000c0f4003000700d015000003054290461079a941c0d50441d80c03800318200c5200d648104000350400000e052520812030040403080b00c0c0440b8031407241c1c09854006034002801800c000d0700c540048442c0a4005d03110365110f003500514000a0754884148002003640081d0a0f00b6200c1c20282c8081041110b11160083c41d6124410101940202800203001610b05a003c5415904003000300080359420048055000347d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 628869478 1250 628868228 628868281
    0x40f090908180d0f030314060301050421180b04030c080f06060d21090509090f03030406110c2e0603110f0109180617060103030c0f0204060b2101050603 67
    0x142ca40403650b0286241406000410104640e00506805034080c8141100e28141c1c40c440e5941c0c502810700f47e07174054400400c00e0280e10b01080c40d032080112941c000380410316103100c440c5580c0422481c00303100c517006181c016000103410803c000300c1c0c509140050054001515484610044080d00c52000a00f01405102c001900000304072644082040710a002d0009065103d41c0e1200100200c003a40603040c01040a480840c1001d4800107403280105070002c021444c560301c907507440f0040c180b00122481c0c041c00c280143c640141c03040c8911074100081903842d6821891910385444d00781000c25009003800d1a124003800460305120405030484400e0b80c14592080c01c80c001240c064071554014a900b0a40602080c00d9040c1901300ca002c6565035072170030b0f04a20444400985406080c4002408142410f50300000580300f0f00c1c1c954070b4180020310001d240d640c3d84401040079409a040e0390307140552040301d4044e15031100002c5000d040706582480c11490a6512031804d003a0403e00c840608 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 628870728 1250 628869478 628869517
    0x105040b101b1b03050c01030e061302150c0708100f05040f0303180b090a060f1109090c040b0706020c06160e0402091f0c0203120702130e010905010c05040f090908 72
    0x284031400b02103d00e042c41902c0c00b006a580c00e00c942ca9075603118806000a06000e26402d010400060b143e00420b07016014416030300041e800c00c642c9a03034070b540400b0041801c2c080c0262103c005d1000c6402044d14030098100c0440304450f100441e44541d8481108903e40701c00c1c000801d2031181c400c0805689401d0004200700140c043c40007095101030000c110075011410802000004584411140d01c078900521244c545240e0a509490500c11082d203401c509100140311440e2500300c0c40e0704112050002440d1a44841003030307002c0c0e80001000d0f580b4640000703450941e890108851640041d8841d20107070440502440213022130000da009034495600821380408035900d06600b45058420042c5046100340c00020180c0300403200340c4180e129001e8903d0a0440c041c0c4201114151a802801003284050755080e8200801e59450300001565a43c0e005000041091180f14621051921519100c0c1e183c003074070315901d000c04d400652419007000280400942020140c500e0a401680d001904 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 628871978 1250 628870728 628870733
    0xf06170f011a1c0605070906091202100305071812150c14091203120603010623060a09120b09060a0204050604120620120f0610110f0a0b0105040b101b 66
    0x4600e95000040c1070246088103100e80725810805107001c8400700e8a1300c85c49d80303580f08044030300c01c80c54030000380d00820380b824400c4c1c0c030507c29800aa84140d82c0d041c1106410b6641007658a20b95040d0040a0800c803e90161000e0081d01100d02d1510003c0c0c10301440803045e100b00c01410030400701e501c0c4d10411030100303181e0002e58481c2020a542c4a002d01140e032034102e03039403031098628001d40340e040c06075103840d40c041b92040210301034541000c030144104210702d68010510500341d129580003030400c016410045149204140031400003402114000001c2c00c210003070500b17241003d000ca50300c1e1481000304003c1a2a0141a00c080304c4020b1340d0101d0460160034400c0180404060042266061031400c0189491401c060303d01008034069112203943d950522014407032041d91000e41c0041c0350034421052910440750390041410342d07420f9071030a000d08800076181880769038080f1411159100148007509092240c900000320403992512003039150a00505a07212485514a000301e0540303c3e0317002d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 628873228 1250 628871978 628872019
    0x118092916020a030c03210221010b030112061112040201090e10030b0406140117010e1b0409150e0307060e0d050f03070c150b09060904020619030f06170f011a 70
    0x1c108203500850300c1261f40d0f1a5030754025070003083c0d504503040362003817480c81000007126554140c07060344100e140b031070f400c10603403900300744d880740040342c2494840b20081401880d24002c5c040d403094a1a550b00981041e1001401d502a039805c0504e62035051030030854a82c180c60781c5078007201d400c000300c6581a2500d05000e8041c113034500039000c140c4265800000e00003211a04d4444440e5580000c0183c07107010030f00030391501c8401c10541104103c803040409245030a0303200c1d8a11910460b241955004103080b6034007500c01d00c0442d10001d82000c221722007407084c98041c504030902400042c143c1102c803240c019245029110b8141101c100200c0004e410034001d12400c600e154020800d400507000000126018048001425015005034030120718242480307540f0502031640140f01904025414201203009000c29031218200344c1c031549070407111407003446550060603483c6407202d0a180c101d602540b60240c1c01000d034076581e01d4007603400189500e1020800091f84111480b680685241e0801c52 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 628874478 1250 628873228 628873247
    0x513150b010e040504030c1a15010f05130b030105040608010608060406020a0c14010207140307030f0e030a0c030818060a050901030510032001090807050102060118092916020a030c03 80
    0x6822a10713282c144414103820513408002188a4081a007200b5011441c503000140107854a9076803407001c40e0000d45e10340c0207020700d40c2e1a41c610710707000c0d00f00607040e18038071003480c000d13840b0195001000005000074203213801100c029200e035500920503607141405203641c1d00c034020000352030a60301050f02031300c0904c0b507540c000c00c0f00d0b000a40d0742107a05c0d007902818000d600c20201143d0004540ca80e41c51040004030603560003d4040d1201d0741c403800c2c2d0344000d03181040c0d03418145505004d06109080040c05d40381800c03020f1800344544030f23282c58428000d00503c03900c12240b0741c49a98144211041141d00c8011140c11603002c2ca4085801e45614402d43c540500b01d40000780380301035a10a680000050108586500900740e880d00c042d15070f220340070f42d101c00c4240119401600200c0043c052464690381d00800c0c1d540e0968000748440d05603c80c82c24000349039807007c13086032000040e02d105940b02400990048041010381c03400f1a6502e034040c1d0342ea4240a0010309000c0c0b0964140709040c002c101e8003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 628875728 1250 628874478 628874507
    0x3070302150903060106050a0e01260a06050d0302011407051606021e071101090f06021b0a03020a1d0c030f16032a02211b1f0501090513150b01 63
    0xc448658503400050b0523508004e00aa0025210311041c1006612813240c66410703d410000030410074454902000d00c4060041001c2307074141d15000d0005060311101754a00603680245d0001998450404440d2902000135202c601003100c01d00003200c0c00c1030f443e4520084a5400071700140d481c03410821180460081a51f0a0101d2101054030800d108030811170f20b180650982e54080e880f51211019100003044d8000c5d100181d000039a029604c00c04407100c2000c85400405543d010f5a0302d60015006100a40084552520078404c4060302d03035410107042e8000c3d01074501c042c218601400c4800c0301c0c1000810001044130200258500c10b40207502001d503007105022031000160048401d180f02000d518051401441440c1305030050059208064943d00841c5031041e14100940e010316440c140040403040031805540d020345201c05000000c840003012521300841d140d850305042d90100c560090401c18119407811003000004d014000c01b8042624155001491004040048803d0503c3c40c191 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 628876978 1250 628875728 628875733
    0x70501110703081b2b0f0903020a0906081b01021515090a0c110604050a1b09021201170f0c090c0d0501030c050f031507050d11030a1b050903070302150903 68
    0x41301041c6501c0c10403405420884040b42d0a00a517054144030245031040041190f6044004101c0340a01c114000218100310b0700e0f00d800040c0d102c2c0c0000303c2101080d84222a0b266840d881003103d4002804404c031308803081160303041d1380c5480d4030000c0e480d051a85101007800543e02c1c0001c62401528403480c048920241c0f0446091070150300210003403005850800101d00301d0342925000a0001900e58403c80c2e000014203d0b19450343d56103007030381c0c01c42e005508001c10340c8540459480040c1c030250400300680b5880031120351410a22640b01030010400003c0d41c0c101c01060500e111740000c43c481c20840a07900f0f010583d8807401e56a206010380c150546d00b8500748400042840740e07036102a01034420403110008542c180400305592416501c1c030004120b6600d80010b0b1400380640060805041084004200000c001300b178242582d10840d95890040c0e5545581c80840741c1010300d142c02c010150810320702d0085803c5c0020b58409aa200c0280b02d800480d20681c01020030100352426410040c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 628878228 1250 628876978 628876987
    0x61805160219150213050306010f0f03170c060412030b0a05060307120f06090906050c0717030c0702182703090904050a1e0b0a2c0115060c1a06010207050111070308 72
    0x90000031171080d40300b4148240304100004c1230007a00b1210002c01c4910594172000c2d070924690703504d14090020b400c0d02201761400d20800603038090510185206070f10942d0050500e106c90b072005400c80e14110045402901d10fa0414031458840004494105015050800307044a03600b00c6070024046134100c1c0c52101e401c1810008001d20355801c0002a0340c403c40090003250780b1a5500b8406000e6440d001d031140494021a0b03a2613450300004640000d6000340e80d610345040ca03000308440300203c14441a14003546800c005c80d683c4507140c1030b846c50418540b1805a41d421500040d664087d0682e103a1141c10030002042c00c00c141040740411065015101c205045024001100303114000802560800c14040c00102c4008140c81901404810204000c5181510401d003840b415544404000c140d96690504111681c8003e001c400612056460042e50100c3d403801006401c08a110b16011020700f4051264a0380c02040c49002d039002032811030308001e84038a0141c50b101e019803016129040014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 628879478 1250 628878228 628878247
    0x16021203040e15060a0f02101b17072309040c020304050a080102090d0b0613050a0f0f0608190203070b0c0c0a0510140d0f0618051602191502 62
    0x281040b612100324841243c0c0ea52800d24040c820307070790440c0354802410001030042e2401000f00d002d00134018070403503203481c4070380f06104122840c41448503a101711003034074500b00f0780d031094111130700c840a801d003400181091840604041000c0c201d03a401e040101301d1804102000c801501e45180e001030081c01050102040a500ca41c4240078103809003044c0000407a0750b0005000301c0c5d03600200a027039003042450a07150249641805004140d20040c00002d01c4040c0c1c1c1207006d150700642500000056440c2c070040488103c81041070001842428940100301400d03010034400d0000d80030200150b070100403440064180300e441e40001010150109003000f0115002503c00d0319000b09031071524032103403140b04100603078058500980000710720380881546030718004064444041c3c00b030404180700d2900c007030100a654041d002000c4205040203840498040c9010b030320307000014001c031343c0100000190005d44419003242192010350280c01d0311000c1001c0030300c44401900000710115282c21045 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 628880728 1250 628879478 628879483
    0x70b0a0501080d08190b130905010f05061914010201020f0c0601181a010e010905060d0902191802070c03060e060a11040f23040204060903050708190305160212 70
    0x82c0626426071103901107003194103000d4825240502e0b100c40703035070030b519510340c9600c4068039440175010340210700070f180c01c180d00909002c1da161583c031400c00840d0106a016914040321030081c8498450302a401082c00c0740046988070300c1c142c5407541100030300d000860005170b001e0700c42d40c91034403900280003800b1482c1d900d020440074140d44280c02070b082c41a0902c6034440c01e451408441c0c846522a03214641c56541c000e1003070141c0800d06050103541d496442e00020041c0d044500d6080343c194441c5011801c61400c03007440c039041c40c0d900b0b414600071801c1c0300c420303164136101100d03940c030b02c590000e03941081c844c0941b1588000d540c4510107102140d10310000544940c010348140102a081013903603810025100b0544040c0d40c10881c81c014503601e040c1804929540301515080d08040104110449840d240018006012591a0725540d81c0c61440d0451074804140d2002c10302d5004003110002143c1c14001d40781c47c040c3c01d46481500d0341040d401000240304080b42c000d51000003c40f010035101800f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 628881978 1250 628880728 628880731
    0x90112030206010b0a0e0918060711120a08040b1902030a0c020c090103170904110a020304180501060f0309150e0c240904240803091203181005070b0a05 67
    0x39909640711a40e031000c83c0703101801005410004030b0512001085603080c0140d880f5131082c2d1070390311909804400e01c1d049082130410354400c800038468000e04103081e0020400782c0000000c80c48a1881d180d03125400a000310400b1304000c00000d00b00010400000c0034041d110881040e4a401319503a00300344a001004112400d450805401100548907452504400d00c904a9401c00300403001260065207070352566101c407111030313400381d65084400002d80c016009841140c0080e0010350f6503908000c00500721000250442540904000041c011182d2042204000c0e02507804d000c0b80d040e03100d280c1440901002280903220307514102c1507060242c00010101502ca40a942040d16050b5140c101501c2640540459900403020000003055040a40c441004d040034450401d20650764403252000c83d54403540038403080c3d030001c101e141c11494401c2452a0f00e202c2c1c1401940b410001d428000000079420400c0c5200c2e001d11003a81d54114020000c403911103a1180441700c061402c011001d004200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 628883228 1250 628881978 628881983
    0xd060e07030b01030e06040204020c0a0f0c050f090106020d0e0111061e10081e03041a03061512180712200f0306240607060c08070f1d03010605090112 66
    0x52a402c001154002d12a60000e0a03444000c0c2c103995135250203100282d48642021f440501c00c510364500490880c0002050880c440d03100c800c4503502e0320781040180c02c507182d00e15100700c1e01e6000406c600b5400041e11101d980c0c0c18100070406403c1e0300016a41810070700e00c21445030240504028100081d030525050b00803c0000318074141d142c0440c1502d10402602a47d0b10b103a005002e031107240c400c41d07503a050400e0703404000c5038078040c1c82d075a49801248502c4004074040e8801b005114507840d040c1046a5401d60801d25241089074000860042d04000340c184401c0c904500303031001881c50b003400500040e000c240c1c400004e0f00110b01d0a21992812100e41d2401014441a000d0135440d010790f8113401c601d0010024421629145041c440014403040341c2c0000e024002c02c0f026854442c3c001409045020b201b0001e4160200c0d900a84000e8009105204100c8603e6580ba041c0e508106041d0b14840407a032003642002066000c0b900500b01138011a40c041d80321800041d460b00410283d550052 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 628884478 1250 628883228 628883231
    0x60e010c0311040612020f0a020f100b1503091c0903110901050a051309120807020d0908030307120f06080a02100201050132191a0c100c02030d060e0703 67
    0x40428100c0c1142d0030441600610300301000308100c81403082003d03084448144400500d44501f40020741d5041d403082d01d1500158124100c4602100342c00d221841c82d0111160007400740d500c1c09000104441e000c080c002400b910080301050000a04200d031865108a2401c403e0151000502c041c02c6a4824881220300c0e203407001029541d41070880b01c940c1260006445654400e0806003007150171000c510407040e51032303600d0a0910209074010700b15062003c550f100c204d03860520b000000c0c2448081d0001100344580c680003006025400021658007a0302480c00481c8002ca90303000c040a400f8070182d21840c1070800a001c1100c0c0e001044641d01c00d80700301c4024100c0205100240e0984500344141c15500d90080d01e071121040618181d50b0190b80300030118200030620380d00140080308003131900030703051000810900c101c0e600945500e01505c907803082181003151000b001541d480072006402c0d40240ca8a1000c01e80750300030001d49800d01d034812818801140c94080b03a1741e0f941412122140001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 628885728 1250 628884478 628884491
    0x302011425020307080301050d020d0605010618080607020a03030e0106050301093801060c020607080d0b13060b0d0207030306081509070605160201141b0303090d081905041a0103060e01 81
    0x3030b400003003120701c516840808542140c0c80d282c00c102c034890100380240e0304000160f0141d0001030607885464068403540c1c441022100ca4107488111186481c0c12140309a0302c410140000c40f900020388050701540f510b40483c0340c2900004172405409035520042d055803c0c40414000c126078191082102c3c00c280307000c500c140303100e1440c40229100450168289240700001400b040f44180b002d108a180094a01807070050303075076105580d80d40440b080c00040b9954410710091071030204440400d18900c200240300035810140503403164801c0d10401703e40c0590005141041600a81080005203407210a45d00c02410100b80f0100380c0d41c045813207040710300500201083d020300a1051b0b8685a9407904104030018042e801510100000301c000e4007010003c1c8807000041001c600486411207098020b991030b8107044611034509000020785201f071002e00001c102d04c60400400e034010030b94203a10040b40c5500c840c140a580640303072501c045100840f400001c408d2080d00c1d0040401151000000c2002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 628886978 1250 628885728 628885801
    0x319050106090b0f25050706020c010f0507150905030703120504170a1e050d0b100507230102130303080906090d0e0604050a08160b0c0d050703020114 66
    0x88540074011080450722024051001c0d45051014107485558021600d1400720400320440003824403014280a011135281854100034013030049000426081c002000c0d000c001d1800a8a10031a5034103007010400040380c440d00340543d044000402c0344040c00c00f081305221394103049482c1e601020b800d9010820007006a41000000d00c1064410382d00000b102803203c100f201041e01c01e40c46004800100007568080c2c0000142c81350b40d54000c4104c68444030344e00c1403950240001d4604207240240302c0c4005952090f684c5030441d08803503403180d000e094404d004800309130f0700000066944c0e03c07071015880030400c0a01e40003825102c00949010703484030080d80da0b0340307605103503151001c403008a4641c0061441103002d40c0649400c124080d4001c08031400c0603290f01c0414040084c6070b00039005940039140800c6c05070030031030860018010f43e242181c0b90604000b52180c0d18803441c0020410070900295200605100b903010640580500c074082c0c54904103482c10130b8003040702144084881c001480c16036403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 628888228 1250 628886978 628886981
    0x9011e0c17030610030218042c16151407030c0b0105090712021605100614101d0f0d050105071d09061c050703050f010b010318021e04020a03020319 65
    0x2c1000003c00c41e8804104c10f03002240a900500e480340386440c0d08090181c0c072a40c403400b454001740214100054406500b00b04102c44104001c80c0c6030b025088003203e044040c44c0e4110300d00070756138894140003200c0c050340021502c0e214410f8040140d92404070b031901c201130380000381151240c021b03c07070708005981b680100144041c040c0c58071400b1800e012040c0c84403400c603801402c500c2c4400e49451003602c14684034a801c00c1001035883e03031102c2c0d50310014042c0e03000c101100303100040b0030303941c041c000c28215601900800c410f084401c0e40351a1010038441c56035070040d50210208000c2c0210449206500d801780c00b03031400b543d140006caa80002014110705013031a001c0740c40207000b8100703507840d1074860510081e4410a07c001c187c44122400100100d0b008014030001144030300700403c920394004602c0c03400c40d0010710000381014202019809010466405034a803d501101d050360032000b55412a0904005030070465041400440c40c00f85164141e8003442c42014401308900000444c001d5110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 628889478 1250 628888228 628888231
    0x5091005090d06050603010612030e03070602012309121603171005120102040e04051b0f301b01030612020d08030a02160b0601020d08090303060609011e0c1703 70
    0x9800112040742c0d98085401904a190040720140c0001040c545503244409070581182c402e40c0410440e1303581041504041003610700404282c0300821504815907080d40c0303c081c0d403a5a4044440035000400c8010318107202200f805800582c00b0b0740d403032410396880c6ea504540d05400b0b4000c19070002000d02101440687d030352080125101d103012940c100b00400c03c1c40c46000c1000b001cbe6642c24000443c6071707800380b2501c0703010314000c200422004101103a0701a807000240c81303942c0609407080e652082da03203030020961200d0a5140d4440d11141d1407099210080940400f400c0c494464004031034030200f0700c40d0341c001c021602a44c040c095903460320405440442c401100035003258980c4250004601c1c000c0145420089c4010007525184050b806255100304901d400e03a056002902403010542e0100402500090f460401e06100d1070210a0641c4a01004260034050480000e82d20400d0384502c51010b40200c1d035003000210314071003103c001d181003014141100c00840c80c002e841c42200c0b004003501e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 628890728 1250 628889478 628889497
    0x10e360f070807120c050402030f04020a1d1918030809010e1f05220b0601030c020109111203040503060901021207020f0706140c15070210061d090307050d05091005 72
    0x240b601a1400418010300a4030280a48085081405c00714150b07490340011401803007101c400000c241007500401c00c0e8000d81d50701078003140c84400700c1c5034880c0c501c02041070ba010f4140480c412008803030b02112070140140c40c0a0390542c00c1090200001c041c0c1115455000310303d10802005000382e80007a99a0f00d0030200e112003c0c51032928900600d0031100e8000d03907400340955004010350003240081040000403130750111211050312007040365070b59140c460058081c90520080c0490140740d1140c01380300d00c3c851034250064a620001e0384d4112010030032207008200140c101c1340649040c44002d8002d4000804502440d0301081c00710311428400a041e01e045840d0a01401c1c640e89031003801e89044403403092003241c03800103001d20441540140286281c80414440c800b10502c2c10340e5000341040d500125250801e880c01206000c80c43c0545c80742000201d40750030722507540d1a2003403000d295028070800144188a200088040140e001e00500380c0300b88140e610002c851031000c4240e549000d01e0036103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 628891978 1250 628890728 628890733
    0x1020f0303040602030c1902010c030c0c0b060d170a0203190521060d120513050a080309010804020d0f0f05071a0d05040201180605130f0608010e360f0708 68
    0x109001c1800781c0d005641101b000b51205107005020b044920a00c64200000c001607551550492043d80e05401020f5280180d40b1b840300481600769102140e10780c002c0d24041c001c03d0400048001c02c403041d43d1440030828041041515001c0d80e11009560394010100b5600a0030703040c0c00407483e640264290303213461018101902629803034a0000030601c1004041e594401c04a00c03809010900594030019841519a500c0f42e50b4180c41c00220340d20121070744014022135649038100076041c030100036206010b40918000c00e00b511503000040074200010f03000740489a00308007420821000440ca440500d12071000e503000c043c0d6543c1c184080340400130701d50300418401c10880c1d0080e15164441d0354450301c141004031401501075012181d1030425040107000c83c2c400101243d949920f1401c9030010101d010541042c1800d110f80102040380c1840f40264101c80c480219041000d10b03181018080e0001244a006004480c2040012035a200d0b00c1c3c640c50055448103203140501040790000d48004400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 628893228 1250 628891978 628891981
    0x33909360406271a071b23010506090c0702031005040302160b040501030b0a1d06130c05030604050708092d01050109020301090e06130602030606040305010c0309050c01020f0303 78
    0xc2415104400800c2111401e0361040c51103d250180d860070703242584004000080c40b0503624040741d000c0351003007000146000000c10030050a5000707100c03040c14411500245020f003114903040d00702d0030000030a0300f290520140103d032034000c158061442168216500300d9651511000030076903100d600006034150b00079000307602e8405c21980201c0d4025200c0d00c111040c07039030b085c000940103034a1600f240b03c140200040c100324940e40350240c0102c0742c404503502e48101d86440c1c03525480a40040400b1000c480d030100007602c6035034224000c80a00510f110901c10050303da100201030358001c8070090310a51800001c1100540702d401101e101d42c0c000d0000307000100ca1510407001142c904550151506144c16a00701d08050a016103402020207441c05a181d5040c05202c605541c40e48001c40c00582c003082c03c200c01840000c4030826481e40207240180e803902c2d8031011510603c01c80c1c00142a9609002d400c456041d1b050b880284058012000c1c1c496024004004a8403040c4c62075403a81e46600510 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 628894478 1250 628893228 628893319
    0xf010f11040e1302150d0e0c010e1f0c020a06030e0d0c021011010e070e160302210705130b03100906050a031e060509070815010b033909 60
    0x481c03c42401d00040c00b46203280d03960307400f8810581c00004010003540d15001d418000400c108074801c0070710000d09004911440709400310360318880c00648030b070034910502170054405e40103107000038081e42c028181e10307642501d80c030018000d000c0c0c00070106441d101e400d40b101c0405104030b96404049500821240010604280442d00040786d032800c281c00d95a04d00503014501c0082003084005d180030306407501d03071b031800801c00a050b0b00c00030002002c0c140100065402c256804800329a94007084a111f0300c0c640303e80e00d00f00c415001c3c04040e00010604001d000c5601c03a20800558440d81403125882440d48c0c40d80502c1e030a45149100b0b298214001c0c280600024009541c2c03041040c6a04c04c80c8805004552100002d44005940707029541c0c102d4a001d05c80d0010501044000c01c003140030015081d450f2100801c81c03844010300d24601c01c51250640c0140184400f4070b01c0340120190a1903a00a05900300c2c1d03852030384030070101445040c40d0340440c500c2c002802510500080d182c4503030f1040e1030268 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 628895728 1250 628894478 628894501
    0x41211030c04061202040b04020325020f060a02040920030c07062007200a050f01050d060b04060f18262a04140106030213080f010f11040e 61
    0x4208590500803204821032907151845102d005184d000545482400b150060104841c01034000f00c1c0500e004000b001100c0b040d0601604c1c1888480114107030103100800e040381410300f03442e511055405043c0c1441901d0105030060030503203884034420000504c0d80714903805003280d0310b150213030048424070000b512800c510014002c1203000724004a00f5400407418803904210969205040d07100209461090115002901803554800d154507a240b480c140b0006250740d0f0544900b41c49002c3c40668550203901c07030701c150b030021103518109124041e243d40152107990400d00440002071401c18102e20050720031076551a101d030040d074110804500f4001016a03076500e09502d0381c0c0c80c41509070307606540c145c00c00c802c0104100301081040350459055121081d007034107041440c81581800400e41440e4010788050341111020b04005a035442c1d9030301d413100503205941c4015424001d012154120001c1904814100b00d01c00300e0400800c6448903481c00c40707004134001d182c880490080041c0007a00c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 628896978 1250 628895728 628895753
    0x60f05031f1109131b05070807080a0509130c0e15030c030403020106050d060605130e060f310c06080108070303050a020c1c140c2d03061008070b0412 66
    0x1c00b02c42c1e151103440800b0451040c0144d50001c04c41303a0760130000d1044103036a0352050481100780b80080ca030019903180c081890140c154060400000000d14144850040040f030303181c440f016020465041204042800924000b0302c05030225403185011511842c2900305116a84600d2103103d05641341c400b0250303403e403c000c1c400c03020342d96a0540414640d4600b02540890392281030040784d0766003080207200d049061806205211402d050142d022200e0119000b54412401c0300c258605565400ea80c1d001c048111442e8050788540700b0800400c89001c009080a03940580d0f5804162030380c07841d04544884092007002c4003900034000c2800041c1c0b0410041524202500c115403111440c440000d0861000e22258040c14909a01c410104911078141002c80d80800c800341000c1d0742c0780000b01d05216841c0083d2221000e91040400c0307c428200602c00502d800a0115400c601d0321200d42c00101da2503020382066445415000202d5584200450301907400302e5600b80c1d05001a50303038001c03100f00c0b0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 628898228 1250 628896978 628897001
    0x50309090c0319092909010f02120f06040603081c050c09010e0d0807051c030b0306070e1201020d14070206010f0b0921010f0c18031e051c03060f05031f 67
    0x11221741942c881c0000403c0781c0d690b060108181140780c2003258802d800c4031460030500030214010b00c06413102007040b030001540f002856001110319036440000400a10b284d0700010508000850350032007039058202e610241c500d40c00c90030020341c1ca03403038070300d07000c50140b00440c81c0011000242040c0900f0200c8403900300324407032002d10303040001075581d541c01c00d03c5546060b40e40c4104007040208180c0d150040c0303c120203080d00a0f20031b41c1031080700289541c44100d066802080c660403110400c0000758121011001260350400c00c10070507200746092000240c0702c400040c840e480010607004c810040c00000c82c0c1040d00c81c2d616110346a001d012014200d849500717059201c17401d03203c04108086c0109424508600030000e4401034112018200e000040011082c000c0c01031010700002d00f824032120075807000300700c00da03203450078518115282042c0642200d9a02100d80503101c40301e900b58000d01e040d0b03031a6604042003280c0300c5090654514031081d0010b0a2042e03c285d05490510b5a80318000001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 628899478 1250 628898228 628898243
    0x21120913020702120a0f030e220e1002190e030304230d02180a0c0504060c0f050705060f0c060601050f0a08180a1a180703141504050309090c031909 65
    0x129070540c0d4604041900e2006e64121203074100003070030594085001c50341c0102c200c4425039040d101d03890400b05121041d01c07419803640d6031440d14545d44001c101d1403160550b0741d1415940d41c0c1001603220f101c4260001201c0c045241c1000c00c40040c6000301c19201076540341c07046c0d4003281a4908407042148141d42c103035904507400012100140e111600070100c1d1002c1a10034070002d0600441000440306201d9a56042100a00c828072007194071110b6250b400781c00101d0780301c21111901340182440d000b640302541c004c20010b48100c043c4000e501515069595501380d4005545100040d6284c0c41100c031101a80c140410030f0380f0900d0300a51415800900c1d50b448441c02e400d403220000e147c03001c4d50a050304e02c072545041c15081101981091035000c10042008602205290b04d0203540303504a0000801d00b0213100e0008850420800080c00340c1245028803103100d0a107401d055440c1c1c0c0c002c00c80580030303200d2031000803035409840301100d000f0740264400810140e482601e18000340030240b02161402d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 628900728 1250 628899478 628899499
    0xc0c08071409070c08180d080d2c3a09080d052a0a020901081605100c152403020f040506060409090204020702060d0e0d02120d0b01030b21120913020702 67
    0x40556014004c03401c0c0344080041d10700007143c0306c10b00c002c0c00d0001080c0240039114405d001c11a0101c0c0381500401101c0d0340c81d0004a0071180d04118001c0915007a2f00507040c001808059603010070170004445040080e1030948280b100c04444500c11142102c1d14800070411310007040c1c5040b003202d08408040c4003039406244e421b600081c06c83c407003a4843e4819600405103a500f040010038030070300030041180c3c000000b03000c040c3c003d851b083c03611202601d81c000c1e10009031510003032608000201001c40c4500d8100d00101c1094502043d0740d0f0106a0150320702844940700e03424180300c2e03a07000c0c20f4005c11041c02e1500c0c140401000d009402e1382260020313000d00c900ca0068071520046c140c110341104010500701030300c40d503043c50851018a510119407190240380303440f5890100310b50901c2403902022508010f400016030140141720021a0800fa011000007608001c40b00b034410030b00c031600144c13402c00103052210f441c1c034020802210b50000c8985400709807491941d00410241e440503042d2442c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 628901978 1250 628900728 628900733
    0x120a03020c0708010510090615030903050c06250203030609010302191a0702030c0105030f04060b0a0e18010c03020702060d0f0920040609050c0a0c0c08071409070c08180d 75
    0x50960642c8200d83c035039100c030300340124800600103540140c0900302e002c0010601c2c292030030001400c1c195281c8149a40c1c1c410404c00e061280044070310040c0c1000c12104141840e81d001c0340c0a0840c0c2c0407020301c8042d140d424078a100d00c04021640205001419500e80d0303402c607001c0100c1c02d82d180500c88148410140009400001d0313112030700c1c040b400c2007880c507101c0341c45005150610080c450300c01d0420000700208000100d2440050750056003010000071540014400304001d07800a4208900c6020766204000040c000c1000e1300410012440003803207aa4111001034050f4026800003d50100040c4847c2d0002c0180740d20181d400c86041e84003043e4040c494403810824800c460344c00d844900e000407020081e0410380100b50040c16004001c000500c2c00d824803482c80e01404a80204008181d403501c1d085c413185a1120015217400d0003610768191303940d00c500e150380c0704200c6c12a0107680c0050025130765a01420040040382d822452451031720207603200362903e244074491100e90000f030582080c4003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 628903228 1250 628901978 628901983
    0x708031b0a081b070f0b0727090e0d021506060d021b010e010506010f11161814010f0b21090c0306090604050717030f0a0c110f0a05011407140105060108090106030302120a03020c 78
    0x40080030720170340f03103002e42083d443d0741c191072b000030444505038068281d641321294000744810a480d5495890700c1e16440c0e4400142040c8038011086011a0003c14141c1405141e07420b02001505614004c10150003507191540c240c2e40100c0e0100c1c04640c0305c46501181ea80a4440152124001816111400104109079480f500c094001241d1a1089113000a022026100c0d0307030005030305a010203400f5031410020960058103030040942c5c1c01804116048a40343d0382c4e109100381d6104021483d6103143c215001a0354132017490015200e4800c02010402c446004503100e130045400501610f012402e100300d01c491140d0000409000b80700400c50000c8007a80d140207852454542e50b5640111030540c10840c00d0901c0200d00c2504c280c1d0f44022400c1e495481d910400204c4600382005145045c0205010041380228030b8007a01c1d40e0075108a10384a4a010350000344608003d80310404280c8444461601f200c48030300004000d40d118048500003181001c000c0c2034282c8042c0303409441c20500c01700030750 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 628904478 1250 628903228 628903277
    0x7050910120e2d0d0c05030c101505090103050a032f010c0806010302210903131d07081905040c030f110a080d02030708031b0a081b070f0b07 62
    0x2c01540195011102844554000c0d080c400d44100d8444003020a9502c46074a50303004071480c4040c0018014220f00700318003031050b150f950b612a016201001502e0340d40e14050186c40132074046804240201286070b20f000c280d65030580340c000380200146005550152210070076241841040000070162500c0c1400003440300d0761800301a800032440e4240607201810912010742014145401400607803041c0514001c0500030b1420120060740395252a0085030441c480e03208410301c0e10801100108042a110162000042c001d408035180d60381d0382c0a04481030003050f60300202621210f42aa0810340058000300d4005006c2ca4924100d1030307580d91442c00d04040c21100b100e29500148544180345404a80000201070749000340004161150009440380700b000c900804069002c030119a81c08222442e200c0c1d04507030f81d050385540c3e034900703035018040d00000c0790a06a500010701d4202903048000056a00450344a480464416901d5444850000c0d0041c000e02c200005418080d00d804003003203400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 628905728 1250 628904478 628904501
    0x30408070605180d0f021e03010f0209090f040b040f060f020c010e150c07031d0d05030d2405060d110a090f080325030207151d090705091012 62
    0x4030394802080081411800c500d0803000c0c881c0f140300c4d0181c1d01140010110340411907044698155140325040001030600703198440316010340c601903101039102030603402001c804800b10707420400c55841c0420b03500301c610201c40081c2803640640101d400148a6141026010b200e40b901241e82440d0b0030783c03041240c0000c07000d42e000e41c0d11080c00d0f5440000600400303a902000484a10040c50030782451042449800401401c0010701c170916002c019031240c44102c40400142008048000c40c00e19540c0c2c3d400280c103412039103243c1242c08110003c8120b809031609400000395403110328200401c000d0b034210f8081d22400f1525000d0100003200c1510003040d8807000e40c1c460b4070410382860310751a47c1e841190014542030f4001c04c040315081541181e000c600c0c03e80720900c010120911300d0100c2c1001e00d681e012080030080041c54160700c44c1c03c045480780e41e030b5039142d0705807500c4055001c101d0340d003100b035561001180003080f40711068207003a0307807556645040341041030810400c11102c608940726a00c03003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 628906978 1250 628905728 628905737
    0x201081501091e180f0e0106151805030a06150f06021903020a060509060109060801020702060915040f0305030307120c170709121a0f040b1f0905092805060a0e0304080706 75
    0x14503941145c64815138140b090030000801400e818510408e05207000c1c1201b250a0250403100c509140c50074101c2140035100c007a00f0f032052108185489009000c0c44e001442215200e80c5020a400c28880205030403101c25034024625020071282003903a16400107420740843c01401c1c024000b0903200e002d4580110000c1004040c00d41c9080305203070481e48240c00c01032941e40104805009a41e038802641c0a100c170440351003449116800070f00c801885036500130985a40102e0001080c014040040c61041589495650400c4024400c1c201140c824030602804500c1c40140b040c08000039a1000340d000c0d061f820a4900240c40d080007000702e0443e400c084038800c50f503686a00e030300c3c041c1c500030a4000781c60100032130450030a0350f40c1c40a1264014070b01d69030042906640c6400250000c00013004103a00d02c420441d5051407604541c403010340c40500030581403440000c20190003000e001c4a141034005024207280e4403005111406440d4850f44601e580c8424040030406644c28417050008110b6a00c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 628908228 1250 628906978 628906991
    0xa060e040f050d02030702150a020304050d0b0f150d03141e03150607080d0b0d0b1f0f0807090e07031e170301150503060109031b030201081501091e18 66
    0x180b00b4030b801100342c100404c6400601c01c40005072110880e032120b0070400800551282c01c400d504a2a6020f01e40c03005038000102d000d038900b402032580b8014000c0c10855914950b654034003c54200701400e054045402c82c045e0001c0310046449450304851b400340003a40c1c2e5241c508415840003084e00310b6610200c288400006101070304c0501c1551803210201075a5050912070b207500c900400e070250f440c00c04034841e10380072024060355407281e280750001e03403000c0300341e145003450f54030400c0c080328101a64024500d407580124143c00041c1c040b4003141e8800c001024501d0070325214501409030ba12000d005032240c00320120004020001e46c14154010444c0c0f50018101820940c2d00c6072058240031031a514100014003010410704100903071303102241807044d1750340c4400004030398642440e40084c1c0101c40c0d400480341010a02c00e0b40350308480c002d0765190150b441c0ca05410450300900b407141400321348011000c01098030418402e460b071511003422051010340d0b0300b10103001540341e21121444603640303d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 628909478 1250 628908228 628908233
    0xa05060a052701080a030522260c0103050907120f02060a02061902040f05091320030d031a0d0510060b09040c020c090f10030606090c0e011409090a060e040f 69
    0xba64010b01400307009090a20460f140038000f881070b0054681402031072800c0903281e082540b40300000345948805071030381013000d9185d031070010200c02214840b0301884140400940c031070700400f03005100080c00341c009540340182d45444074600540403114040c207511403001690b07070364001e8500c54450740c014200a2909c80e01403003048540d080c0e003c4005205000500c203940c900602a03040e210142e80c90840381c1c44251a080450400c8580200300011020b030410011444103803840543d041542103580c4003168010a4003541e0400f16486002410710728500d829141070400504058064000c2e80c034031240301100c030700980c0e40d41c3d04045210500000e20f0b2031642028840c0541001940c400303003032481c04400c00030396864405070400d6001000b0f500420a0140111840f0300110350215042000581d01c256100c05007190700071000c0482c001d13950312111940105810550012011100da00e00003010003001031882d0b016102c0080c103641c3d040c0208500b40800c1c1d82c83e01481c051801d20340c07140c4851 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 628910728 1250 628909478 628909549
    0x50a0605040302151003201c020406140f240d051e04050606090402151626070b0408070c081020040902090d0c0b07060b01080f0a05060a05 61
    0x7030841e040e1881c5035000c0011105025281c2c00640e0303800801c03d0001c0c2a048080d481c0b608542ca5000e50015803048020220810803c004c448e5910070386082c00709940e1140c1e01d032031b2801c06c50301d4142c2104107441412510318100003480c200e180040c00084e180080c00c500d0340100c0d0424804c95118964075000d00810006c410101541940c4411210105142960380caa40740d00300505103601421800d00400c0440d0386401e0352540b01c140802510b41c03a1064a0707007408001c4ca60307a2055172413910004003800d0341c40748001d4080d10760f49169400d91512015546042d08040000e0064074104018009400003d4100000030700400c8520002c11a450104659800705c1307000c0710f964010303403040c00d040c4800059090183e40c00c545801c2001070302d881c071190110303603c1c030302900004090019010b004036040e208400035280c5240620343c00c0000c19280c1c3d005644601c010f803564444214040005940303000d0980000d40d100c0f00140541942170754400118084540b24003502052603d40c0b100030100c428003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 628911978 1250 628910728 628910743
    0x210e0405040201090519150504091b020a08180307030c181a010c030903080d06030c0f06051b01020d0504210801051f091205070f0b1c05090109050a0605040302 70
    0x484040110303051a80c0060300b01030381c0b440f415024000c410480c01c503101c1d8400d0010002c0c070184030007559000e10341c02d00901c0c41c0c0c082e00071085000e107050354400d410781c03503510f102203412800d400908401940d900c99a040e50000c1504003005050718040320143d450520181c402103118100c8001494107091400600030b01800724070ba0840d250050310504c840b8070001c041c90a000070300704010a0900350404640b01e2501d82c0028004010002b00f1902d24106940200203c0c3e0007481c03000344007030b280c0c115407200c01001e07c100d80010705c0c18050940301426074a060043e81c2c0e040c1c0c00040c500341c80480142c3c16200c00b1141a03840103140185400344034110500e44c010844c442c41e00f40341945c1440300007008960890b500146002d010342c0700d150010b01844c0c80344050248021507440d8251545403080d907a0505004030000014046800601c145400c0c091351034045200d00085031140549604800410b00100383c54203540d2184a0100400c0301807000b0f5282a025200c0440d2518103410003030b151101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 628913228 1250 628911978 628912007
    0x80c102a0305090c1203091207050f030703030212030a0212090601050f0d0b010915050a0b03010807060807020604020d0204180b0105030601060206040b040b0405070f0e040b0705160b0a020721 84
    0x8201c00c200c0f60083c0070544002001085421070b51030418410314074550b00420f04141d80012000461029003580018280700f2501c0c02c80d095141c000490050640303400d43c510005000d030740012041c0e600200a070024590010890600500f40317080c0888038a0050742c141d070507031001d40040300103120b46d0910140045881a0a8038200540142a0f40308084001c052094042c142c0d6607101c0c0304611004604c0e040c3c0101401441100096190700b0000e8965000780703c1c00300756104100000035201d00035000310784180210340240800d07944079000e03c5020805014200d9005560b0319081d160040060390002c1e0650040d1a1201558100301c00d02d440c0600c1a00607400350350250b010000041c540c040d59640c0181d11440d00611031319039140a9141428541101c003005200c07000100b0940347d18034015100d140202c036038500a4a5030b00c400d0300c6c148150b10b11a0200c01510071210003003000c610301c0c19040350003440014030f40741071b079252911031110519068620250b213010300381401c0e0707020ba52450100d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 628914478 1250 628913228 628913231
    0x914060f010c03050d060e01031a0a090b06210709020702030709052e120807050d0f2313120203100b09010e130f030201061a0c0a080c102a03 62
    0x216103001805500018034000c0400000042c1a81500310540020f4006e0030344500c00441561286081d8819043d80402d2242c1403c08a0009210107180d0003803032079003900022480d03000e4a5032818000444484840c490703070350f1500019201200700410852009140706980140c481d142e030703c101414031001d64042c81c100341c00c1000b84210017088007072684101a001e03804000114202510301d400d00010390056500208400b018418030038001d0040c446544a00207454013103a130314500303507002d0300607000100000d20900c40e00e170030600d0140c000e0184001c010f45d10701d040030404000d0b990802402e80241b5252130841c00008218242004078003c6182d40e064103005103641400450500001403007009081182000450b600e812482080074080e03820a0203007062444a0402901802c214030a5021511404041d403010f50020415611400716200c05002c241c5070380c0e110b030f00b080d400018031404075014103221000c1001c8203104003005030044c1109c200240a0310110200d06d0001e00f0340740418075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 628915728 1250 628914478 628914499
    0x90507150f14180d08030c0702041112011509080f03041a0f0706021b06040c23010e06130f08061501030614010c0c090207080d0b0f24070c091406 64
    0x411040507a00100c3c001207003070585031100f41c00603a0801e01400040c040600000500008403d07003c024002c0900a40d0f00348031803507800010308068450700c41020000c000d24401405203c00803001c4061405c4c0c42e00d045807201307880c0e248050803e941c82180380655440020708208131043d000f1100100c10084104508003a4405141601803041200003000c0550004260301c1d5600c0c00660055800e413081c4c2280e010f403a151505038070a9440340034002401410800808070f26507490a0000e401c2c074103a450091411444080c0052030700a2007030142140d80500010800c51000f13800c40c4000c142031402092141001144280485081c61400b4105400c045060004113039031800181e04000a180c07145080c1c003182004020600c258012204460001400030280300d801d074080d040a0307050007000c01c0070018a00800245074044549180c101880c040350007088901d0322035010340110a141194544403050f91501854403298200c2004260b580404501445e0048000ced40d1000d029100300700030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 628916978 1250 628915728 628915757
    0x914060d0b0718030c0e0a0e010e030d02090a0312080708061e121203090f07080106030c0b0a0309051906150b0f160203160602060c041203050d090507150f 68
    0x10700380100103000b4441c401c1c101425140350009600c00031034201c54001940b58881840d01e5001ca0700343c40060082c0e003072024241082106128113600358110400440c98142015514006504401c20350f84e0720021031480000401c5103560801003102456440010078a032031031019010200c0074110358090724000820503065840b03d640300740e5514084600020300c60402400301d01d480c1414000003801c05004c81400782c0b0080001c0c80024060009091300d94240c0c42ea14080c2c200c0d007991001030318488004500300314025920004250141c801d01c4c003c242ca03851508d4980ca0000340c429440040341d0551000c00621180784200c0c99190005107030003210701d1030308503080144c1c012003400700e2035045c0024480303400461540c8100c10244c0c3c00f8040d81c242811785c48400b180c28500d1710a040150049d03c001074640c84120080702c00761520317500b0340003080e04552070484494015910682025540750303c0800851800c2110400034040034401d11103889081000074244903d203003008091080d070030030300c144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 628918228 1250 628916978 628916993
    0x50d0f15050f0609061201090804080f0c03060a020a050705060411041109180718090e0c0108100905150603150102071d041e08030a020c06160507020f0f03070914060d 73
    0x4103c2004c5a68129a403540000540c1007100f81d84a0302c12913103805c0040b0100300b2000050022501e16100760703002c80002010064a40c80142c1c51145c0c103070050740000d580214039502a04170761900d881c010742801000da0b1002d103842002d403020744203c003861520500342d281a01070b070f0704108102d03030300741e8100840000031a503111145c04003100f505000f00e0000f002e075440391040d400360071051044010b446550301c40172001000d850501903054000c54102074440e500501d03916005080070080c03500764a20b0422071134000c0c00050101d0307407401d07141c0e40c2d2100c05954910195006110302e400d582c880e424000000b900e007000c030750322007100c0025035807c000c0950322040c40b8540c01900301d1503260380344080c08283c07840701a2240300100488404401d0000111f040d5000e841c0c5103d1701e0003154820b071a005180300c00c090817107000b900050020454100182008211070358020301c0503044040d000c185500081c144000f43c1c0111074860b42e18900c617000e00307145111064020800342c5560000c0741c1c0c141c941c0b02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 628919478 1250 628918228 628918231
    0x9010f0c0203070f020310020a0305160807081306060b0f090a050a06090b1308030705070906050105040e07030e120d020a1704050627010c08010602150907050d02010306050d0f15050f 80
    0x40c13907081a00d180714155103090002d203200300c0d104c600456480108060190044c44191880c49a41e421091200d8a0034000c0c20b00a004010719214500c035550b40300c01c40d204140707181004580742500e038040041e0652020025080c0e6503c9168401d86483e1180e0030700902042d15444075104500c80401004120340004140742aa04101209555803065501c440003d07801035204075114840014000c090100c04206601903407401d90041c4451a66000110750390300490240c451884640004a505103010b940041d880d940320710203480740c480180343c2d0040c054008180741b03448181c001aa182c0526480211940740d5900034000c04140d00f00b580b10b541c0e070340c02c0040000c0406600c0d1090440103000ea001002004000a0300a0289081580700204074031020b204120140c4288407001498064014600f0710596581001308841c2d45468100b145002c2001400d0341031590b520303804115502d030065114a060701902500c1881c40c201d1900040d0040c46158100c8258502020304c0b4441d140041d405 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 628920728 1250 628919478 628919483
    0x111070f05130219170f010e180a020a0e0a110f07030e060d0203130b01050d110907120f1a030a05120a030e0307031205150102060f04050102130b0309010f0c020307 72
    0x440d8aa0703140c003070000240701d10040114098100704c030301c004180c3d2110f014401d01c0d42400700c8100580704c50704866a0b00800307002c3c5440c0540d8103c00150200d0016400b02152403050b41240ea4030300154003c50200072480d048400f445885000f04041c00186004451031842c82c4100545006455000c442443c010031a00404000c0010303000081c43e0f0310442500d440c0c2d43d80c0d0a00f15981d007428028443ea50f102e10b5800c50f10400100c00016107440d02c605403802d610f8102e03002c41b010100c640304110503020000c0a41052040c40340018980304024454003400d0740c2c2004002500c40700d41c44000c803022401d640200d201e680a5094140010000309490b802d48074424590741e290800d5030b05c268040c140550f001202844085001e0b02030681c48250141c81c88900e01c02002035803203450380340c1d0359610250502800b503403224000c1040c20301340c1d0308005d07400b6005400042c240a0140720a5080d04c0d500e9114950140c808000e01000c0f540a116081d05055044020410704e1000c28019499019501c0c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 628921978 1250 628920728 628920739
    0x708060a090c0e0c04030302010f06180b010306090e16080c1003050604020f0a0807080c0309030f03060409021f0e19151e020a0303060803030403082d01030b060111070f05 75
    0x90208002d512145040908048030300d008242c502503501c0f54807500203200c258015801c00100c60002e00c01803003000292011980684190300c60350304080041c0251110a9040541d43d40c1c000482c0c0c0300ba4070030702d81809003608c064004108101030450040760f00d90030954964129640100310383c1d880352031080070b4090a00b000306041d07885000240c028021004040c00031341000915003c4144e0101c0124458940380d122740640e0b440d4001c8402c80703800216801d1516a02c01c1041c0c030309116500b0069a4000c2004001141c90282640820b1a1545440f20000c0c941241108940308a800c00c055918801013502d0000c00c040c500e002200c4440c65030b105095290004804134162036110b4001c0c101810701455400d000300c00154002941d50120074015000640f40600100c3d4400700401140c0c000c64042c1d03507000080d2105d8030051168200300c0c81d5810b140b41c860030f40b54030005220013420700a50182030010707403d19082d40090480c1840c0f00c401d2005400202080c8103240016810f60190781007980e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 628923228 1250 628921978 628921991
    0x1103090309101803080d0e010b031e011e140702060402010804110d0c03080406031a090a021b0105090c090a050403230f040e01050a060f0903020105160803130b090708060a 75
    0x9440d002c03c100b505000e29880b401d8003206105028000308200c241c000e1007040b02d0b10a50040d1822540f840c2e542d160305400480300580322540c81c0030a1540900c01500000701a4100340c1c41070011601d016014400e1519101504401e11800b980641e104100340040c060030320301640000e010202c000c00c000c08505410880e01d0417520313100d10340c01c41c0b02c0d44083e00c1c041c20ba440f07080c0485a0342051056500103403c0c800d02c1100c0355034180401054140203446a0169203c44080001a4000c45040d0308412110f400e049a41ea400f4011240201407210192120810200034041d500200030012010b17942804140000281d0005015400f242c0071303184c42c0803802c1d04400c08100340c400c2400744001a580854046500d4064070780c0141202c0040740d100807010754405040d0356030982810032001207540c40034100050f5000300b000384040e00d00c0381c8403040e061101d90384001280d04155030061070060603007070381010800c01c0705030305402104040040c404280790039026555148010481110140c4400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 628924478 1250 628923228 628923259
    0x3032a02060a0e0d05060a0b060f0712051911010605040203090d200a0308061002060903181314072a110d0f0f031710150905090c0903011103090309 65
    0x306081c0003c88000c21408000c529402d0165940c0410f40311074400c5440c0ca02040c2842c030b0080e00b1961810500c0011904044003a00c601c51070b52420f042101c240312007003081d56040b041d144080810800c8503261001400d021031140c03401c6400a4200901840c410014403100c000c001882c0344d43d8101c0e0349030850b60401100d030aa00c101640040018507885080c200100301034002080510944080e5041401e17546002c40490f56584260340980c8560030401c0f140841d400d88520045004a01030320212415010b0003250040314049041c640d007840d114001d00403415440340b1080f016962660f40c600d01a034024141000c511805100140880119488040a0b44031945c40000054100e40081d20080440c00c1c014496982031074110001050103078000305c40b03510720355110f0280d000d1611406100d4200540c888503004211203d20912417400000030303003aa41e000d80c05100c0e15043c100281c40d65041300c14142920403855180200313900a000300003021000000f95207030717154212850500a200207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 628925728 1250 628924478 628924487
    0x190207030606080d020f0115060f0c02030d08090f0c030d030f0b060c07060809030a08010e060d0c060f140903061b070821090f0d050c01020903030301080703032a02060a 74
    0x10360006000600340080021015400b00d82a901d618240d02034440f8080500f2601c1e003210382c200d001e58a102e04d0644103005041c826054507040b00f05c0b6080c845c0b00000c003074001921300000d00301c1d08800520a201007182e081001e20070740162007200d0f40104401c82c001d4000036120404031540a0415903a82041921880141c100703481068000d080e441c1c1e07510040355042d40303a000b14010072012a07007020116124040000440c1c900d1303503943e42c40135520390a25a40340f400c200003410f01c942c01841c440542c0080b50402021340d000305042e0301c0e010550465190b014140600c118041d100c048400e12690b0304c1c070b41300400c115a120b0100c0103124004403000c0154502801035103000340c40743c0400702e04104c1503484a069260035031000001901c40f070ba100d8182a550f02c6020b540b540040d000103481d890044d000305e0140c08020360040016041c051072101280c03441c1c209902c82e04c107660018108100341a0881003a200040740041c07030301c0080d0180144201144e651a800a00a00002070f0000055108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 628926978 1250 628925728 628925743
    0xa051804080a050403060614030c01050412020d031101150513140f100b0403050a2d0609020604090e06061003111e09040c0c05010501171b04112a0d051902 68
    0x3200040141e640c0b1401e481221203608d012581c002d21602090f0303842d0b0f6005e80180c2b0704864880460701105055a07007441503280551380120280903042d585031004000a00a180795032114041583c40e003842c080030096120350302c41541c1c802915014903101c21842c9450120384c003e42500c8100d4440d1a000e1030304214801903403215801102c0810003008000300032a203a080c6a029400c011a600c04840b41284104685049a480560140c09590005549401060b25139000900440c10903985244820959404070517461454100008125040c941110250141512490104040d2103040000c101621a1442207001007070340c090000f485a43c4607044407602e10b0b001e0400c0c01280301c6120060700741c06031444d04441a5007018000304a0f01c940243e80560340032040e0080c1b0418201c44032403500c0c4504103003100d80060710350140d84d4884030301d0002010400500300303c1c84c8002404180c1041500120400003099800c060503810b20264000d01390740905103103040040f80280038070002d9160012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 628928228 1250 628926978 628926983
    0xc0d0c21020f01060816050906010c02100c05060a06030b07121e0539160f080306190b0406030509011b180f0f0308090105040905090c0a051804080a050403 68
    0x2464900300300c40325804907240c0180c090820081c04145e4903483c3c506d4607840011010804e80450364010041d618200008641000041c1095003011926402159522804012010105540c100000c08200080040c1c1c0c0d40503a004200304005415666240617520000d0700020410540c02020b8081c4102a4426102d140b80726028411854040041201030b00c1c040f02c03100c28640e443c2102c0756615034031808031104070701000d0031541440c10344030548840703400100300b0401200c199920007000581032024800914015482d06849242003000c10400030140c04000c01c2e81074003070404003c00070740481a68203442190070040b81903543c0190090040503e0300060f1718040310303120204041e07500507104a48400b0400328000040303071620102c00f802e1489201c0c540e01c040b030300b10307042000c141d00c8000781a040740c05240c91450b203a40c4440c4e020566070195a00c850035007041002d18514a40158001e00400c0161007445650050148011042600230f2000d025031000050400c0d903544984101c801941d07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 628929478 1250 628928228 628928273
    0x503130f03120201020a09061101021b100b06040303020c040b010e030d0818030f0904090f08070606050a050a1206090606050a0e180a05100c020304030b0a090303050703020c0d0c 78
    0xa03650520041051500d10098541c0c1e0344242d0010320452040c0220b40b0b6284643e100c0018441c90550100c4d481414481d1048082d5401c0c01503000c2c0e90030100c03004c1540c1c1c41e440020003007040180681030845010250082c03084104004c01c01c0040d03000320700400c81c035004903400140b020a410058031b0742001c0d03010081d4140103c20025401d01e4104c8940b602070f40c410584001c405690a003441d9581c852000d80307120030310f8148030750805441d09030456403501e8070034034002c3c80e040c0d40f039510581740382c014280840e0340076102d1100f44924146510400c0080004949146c1c0e664a4241c1c0851941d020306005400d0586852039503007407240c2074002c00018200681000321103130765480224201d16033604d84c0c01512070640440324421400040492006820801a28900300c459000400500f46031103a0015130105100c00000b103881060114410103000b0004038040c061458010200c070070081001050500c1404142c0803004001407541e01e2159a06050008008900f010203602c0540801d811041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 628930728 1250 628929478 628929517
    0xf03192901120b0a0e190c0b1b0c090402101101140106031e09030905010518090703020721121805030304050304051005040b120a091a06130504080d090503 68
    0x7400c001500b07040d0003030041d49095210035007a507041e1052041071552560260302c10746058030884c2e4089118501c0b50039021410303a943c020480161308000c00902e284012060089446001882802d00c6810200c0d03151500c1e292542c002800385100c040c10308104240300c10521903040d025445201c030601800c003082c41d035694070701005010f80540c6da0120894512103c100041003881e010b20b01129074940c036020b158500700300045800784c002d9045102c0c44828411810555180e0100c941e0103101150382c00f60b5140b5180c140b0442404030440c0c08440812244a43d079900c83d4016203e51401c0a030507004503403c10030011070450084030030406072641c0000003c0c0810001d00100900c11690241c0710900d420483d000251014080c43c862002417003010000691a00b4202030800c1e0f1048180e0000030340d1142c07540302d4440502081191000f40c1c0e481000740402494411905130301c0d81114030081c807840c031340b80d40d52001a00a11000684490302c3c0e0049504202007441a5003c0150840c55404039 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 628931978 1250 628930728 628930739
    0x804210b100504140c0702060306211e03030709050105090607020301060b0306040b09010b03060118080f010f1508070e3c15090f040804090f02090f03192901 69
    0xc05010b072080034800d91030510034410360344485006500c5004403060720760500d02035800b446032a82c8001d1080d9070064907000441040d9104103040f40b281e400c03c0c802072140f0030700000d50403001c01c40d80749541c550354010702c10070842035445885101958003c1c40e105880d4030030840840c200d4018850000c0d810f50810381c0110f89020100050b600c10002154203202a0340034006011043ca0203004176100b200c01000010070310f5024106440b913411b100d40700c0188240d51444814101002c4400c0d1003981e9440303d110302e1401203140a030300c0d0901c02c0300001041c80c40c5802241543c410007440307412409844200050340c0182d23030f50700030218501580440d1300307815043d11210015407040302c6965024440302010400c603001c2c00322035480340c041c0030b0200603030380e21080038848445000a00c1216025000c101c0840c0307556031405149210380e040540541c0329000c0c1c03c10880c0b0003034005a080c1c0217074014042e02e5450090003104410050304810f0303800307200f0728018204c10189030380002c045190710a403000042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 628933228 1250 628931978 628932001
    0x2071e082505280b04021306090b040e0105060d03120617030408100b06030112020a050301020a03020a0806180c0d2a02061e070509011115220804210b 66
    0xe190b11910035251961a04070010f0380204842011060000580303680e0400078402d99a02e82e0041d0001300b02101d0300b003840c207040003030700ca058011144558841240c0c00300780c1081c2c010b08802603134040080c401881e061005c140000b660400203010010900380599504001380c3c882c40207480d020107480c481c1301c0d18041040e40e0b0751040c42707640c0c2541700d941035120307140704a440743d140950070007810549181d2809150305000310100d00103a81c8012036050009003030b5000d10042c0000069520050703203c0c020a0405400f50740001c041074050345500700f00e4032901c00c8501001d0341c041c45c02c904158490341c2d150074610007010701e0750f50440310000c00307040705207518410440c81010500341d07800c03100e255440c4008800c4c22200d0600b2481d1141e4120081441d1a008901501010310107242000c0c0c403103030f8141d005240c070030101013a5211954010600c540b50070322200c21002aa030700344607005815a9541c0d0700000e071255128200d06481e940e40410070104580803000120342c0c01c100b1a04850601104129 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 628934478 1250 628933228 628933297
    0x20f090708040c090605030a060c03150f0f0503120702060703110607030504060c05070210050a1206030b090712050601210203060a0e102f0c0307050606011202071e08 73
    0x143c2c500207000c0d0001e4840028020a01601c4000c0c026100d009802c0c1c0e509405040b0031482d610901d9110f940c01e00e00707605206842c90040208200d412a40c6c0e1134085815542c0c402c0e40c0166002c0d810296140d000e01e008082100d0020758103407003841e43c031180c0b82030444c2da079800c208110303403d40101028040d0329641034020500a90160100300840ca48548081c0e507540300e144402034010901160000d9080d0085020708815040380c1080d200e0441981e004100f251104d80040740c105203101c003030081039042000401e0180c5801d80201407180e500380c0782c003603590105104000d06110b804c640c1a0305007002c0c2000c980305a0b405000c8030041d003080d140700320107800f0110016608d4031035518040c41402083c0145420f0310f66420454175440b443c0d80380303611042d0000b140d81c15009000c2103006001e00c000c0004220490043d006405a81002c20005118808140343c0c03484550062000d41d000c9178250150000c003480787c000e54500c50080e460300d5032103401100481c0f440c00c14241031004841080143d01d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 628935728 1250 628934478 628934483
    0xb061903140606011d040c23040816120f0c05041a010305061f081312021005011e0b07030210020a03200406020d050c070e0705041403010c050a0309020f09070804 71
    0x8580b15500c90004481612210400504040e4a450a070301c4078246944143c081d43c5a81c80c10340c0b802d0401c1c824001d1910f28036244003002c041c00280030410300c502480117054084091442c9103206103000a4810302c1c440e5114080d084131101400300c010855261980002004080c000340503420808040031400841c40016501190a2038006200792904420740082c81c121007a25440941201004450724240105a4200000551840c17008242003c161116201495004019200f400428402501e01c1a84280a00705d2a00c00012002c0032910112044e16481c038141500c07891a030500700c2c0b41c403100c640f01c4220f01344005184000307164140c0200c5da900a107003882e1035019000001803511740c801d078071038000142c02c012040f030485d0340308600814240380f0f0301c021503d0164485118850705541a500c03031010030f0340040c00300042c043d41d507a18803c04008034000c01540b051500007500074407689014a04166403150758000b1590f40100010380000301800e07440c0030386410b010180c120042a2030a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 628936978 1250 628935728 628935733
    0xc0804110405070503071b1a0403092102060306031005090601140d08030a1509060f0f0b070c050927010f05060913030807140c0d0e010203090307030b06190314 70
    0x505607070030140500e5014040c207070b80f000e00e0b40ea03c2c01c004482884102082600c2c0080020400780483c07030f280441c00f031288058540c40e450b0304061034060a100d4043e48103211403061038194000c0e544602a41003940c50b01642c10903a41d03603901c4e000034200740e09191180f819600d014180504072000190700e5040c0ea240c010348180702c0080004100400e291500000c0c01c50000f003000800c3c00110303800c20502c07402c400840c281600d03281c42c240000e55000d03805c00b29000f980484d081100c80348081e54a0010078504003121b00d00360042d150302c0c4941015001300790140d011500822181031685072201c80e040f00c100f002020500c4a0900395000e0401a050171546a04240200b0003134640a2112402000c422544924402c00d42d5402c1d116080001c2111041c817002007070852040880c68000c1c0000140362014020f601071070345002c0c1418560428a5045500900c40d012498400081c0c0c80c0a6075004007038041c050340c4250006100040e60102c00301c0c40806105c0010402c544c1040c48030351068110107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 628938228 1250 628936978 628937003
    0x60409080d051009050912180d0b0403030c1e0c11061b0a0203160f060e030a0209093009010507080403050a0b1b0a0f0e18130209090606091b0d0c0804 66
    0x400c1e07a5904011031106481d040070080013200145000c94290905805270003248100302c0c40c1c85d10f20700709030b0071107050b00480d49607024022410b5000140007940450b40c0002030003294007020081c403d9a41701001803c1c00481e02c200c8240e9542c60054500025558941484200f041050b90b40c5540c0c15032401c034024443d4403401e1080d541c032050400156401a864011110303d000030407604104031000b07054050044030680c1e0b026840d0f851039184580d15460017005211100702d034114206841d850703a804c80d00114a01810203070365640c1112150403003482c2881c0c0385c0303450341800c0c10544210351004006101d032004402c1000f02c0040c4080c8105200c480c00c04401d25109010f018901c185000180001c1d03514042d010a64021001c4459817000540031010f0700c0040c260080704c100083d40c0b004070103010aa0004118071b030091207150321101c984040d0107681000e00100300c44840103400e00381255200281d100c150300144060315000da03442642440542404240a0f00e440d02c10b4405441c40807001c00d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 628939478 1250 628938228 628938241
    0x12050d0f1b050307032702090610021e0304090c0e0910121502091305060f0619080403020f25120b07050c0304120501240e060409080d05100905 63
    0x2207111080030590203500724410340d540302180d050344001c1c00982815643c3c04a40c0c11040f60f00e105000034450810606003181440c010000c406500030803851050483c43c511000d01039022540c009561881d505d09490b0100340540b135811405a40c1001420910b00003105500c00e034801408000d4000588210f030003034951380c5040e0482c240c41d01445000c56420860040011091108142428000e5000504050f81a80003c1a03404400350010316540c0b030b0003d210b40e40c505000710850b01c13042214154034246807e13601008403124008048103010b00c800000e02454028080b096110840c0d80548041d0146401c3c40400e048501954404903c14480d02250717940903565960b040c0c039000030301d510303041d03035480e80446007940500c6007002d032404240400541c0d0440c4150b201c034014440c0300041341c3c1c00242d84003450500c031005800c100b8683c610004215407110544a507800190030742d80400d0101d00e40c1029175583c800c2c81d00301c081c1685400c08216280f001001c008007542d41c0980180820303140d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 628940728 1250 628939478 628939481
    0x1707110306040b0c0901030603120207140f090f0c0910110d030e06060d0201021e0a0b06031204031709090106020d14032707080a030810060212030708070c12050d0f 72
    0x2c40700280b12480d4800860307001e80c044009407403c09030501d80410482d40300c2d9254500004464a800d000d0b81c070070202030240090001440360504030030b56100d941040c0400c0010060900902a802d84600d40b03400300d1000300c406000c580781c504c00036062000001c0b100d80000c2011032040602501070103480c58172140c40e0310a0188a0000841030700504481e141d850410a0740e05007020101e041d4402d81c554401a55403152000c40c403440008040c02c02a41142403a5540b0040202220f00c07a405c1000e080e41d140c100c601c256010703213410010a6500b468a080e0204151150f05006a4040a00000002c40c654000f50f00c06225901d81e9500c07103100c020070010a6203000c01d584404103030000c40c0342d01d00480c1140c803481800c00018002c442c8100d40c1d51407a2410101e8584082d000100803800304001081c105414200900661008111841e012903405c8202e000c003503c46403c104018002c249100e1044402030340c0940c0100380a01c0c000b0601304050710b191f001613840d07200582040d02407440c4008070b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 628941978 1250 628940728 628940731
    0x80f0d03090305040306180c080f10151802070f0f031805091506130602010504050d0f050301030204110c011d070e0103020a090c021501082410030219031707110306 72
    0x50301d406041c24155034601c0c1c0501f02c248650391007500c01c1d15044011401d5000f00d80700070308940000d400e00403c140501420b08407003024044e412400d00d0002c15014030441c99803000c4410b8014070400d844418a0104040d2003000d00c094410014003001800744207101c020b0101c00742c401d8807529562030b0030a02010696120b4803030f8030f80c4030a0080020b403002025a01012241c0402401c040c81c00e0090015404074040c250001d00050390369004001c1040010088210048110300f0903421400c0910401401d0b4401400001d024035101c101c1d0b00b0b40101140203546840107818001d024039421090324900340c202c1207400c021240f05801000440141541410b0f040c2c03500500600c420f64100042800909056240c1208600c01c1002c1c00e9503000c03400f80d016001c0e01256003e80400300c032035400d5148102d902d9500c810055114428880c0d10030083e002c50040300e50650314500303410f01681c41d0500314070251b40040c2a4021141440030382e980f40500070000707144a030911700c8107a00d00000341903a4100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 628943228 1250 628941978 628941983
    0x2c100e03101437110d06080d080c0f030c130b0a02100f0b010806040b0a05030a030f08181b1504181503050d0e1c05011a090705070209060d0c080f0d0309 67
    0x743d0100900b1080d20342042010070400140a450f000c40f8640c0082258502d5201c1c590640050508412282e0300031809074000481002c06410f100c08080c10104910014140e050070a400294091200b0b42003040701000301580e125503a21030303040d544080d450b0440210340340d80c0603140c0302105074502118401c4c20a280f00c10fa4a03030401d0b681d070105200007040e05034143d6030701c000250700000d92690100006500b03148207540315820300740d603030a015043c43d2010f0211000d0415242d42000b0700003000440c540612ba01140030100520f8880200d504c140d000d8030094903105000401003551100300740ca4200e0748500110403c0300040180e01440541d2050100921a41021100301e500030b10507003a07410313070707174401455130003040120002c611013100307859801c881c0740e51504030310826aa0950884101640c2c165400c48080c42e140400406920404a009200321400000b20f01e89849250581c0501076216180000b41600c1e040321135600d0300c1c02c2c401c00c05503100f05860b402902e8400d009102d10550f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 628944478 1250 628943228 628943311
    0x6070f03110f031504180b07032009120709021b0f030a210504030c03030b0301090203030f2209060f120c0b07060e06072c100e031014 59
    0x32190602c10603a440984215001801501c10325995501c0344101030720700b131443c0c440c50070b00c000c5440c28090301c44c8018480001d142c90031074083c0240420f618100034040440410503070f0740520070001103803241800e605444030301c980030020403016503a60003403c0701007054604000000300031440e82e070f40381000b11040c4000e030010f01440da0080d000301006000703003600ac924441007403590024081162000c6906900054210030304101703040c0c0510507681a2007003078009100d04011a00803d40d00d20540c00d00d6510030300e002841c9642c00420400d6651101022100c1042141c0e8810403400580b240e40290300d071071002c4040000e110300f0201f13401e040c0d0b43e5010200c081c005240840140054205240984461362110040795481301e05000080c17260103283c40301c0e4440182c003031401100101c01c40324118000212141c0480399a102a12624822110324120140c03061640101e401d04e08810032008183c3c2c1820446851254132203012440b8124102e02403042904c2d0381d88401480408102944804 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 628945728 1250 628944478 628944487
    0x5071406190809030705010e010203040201120207203f030a020a021c02220e071214012414010804030c03030c0201060b04080c03060717150a1706070f0311 68
    0x5401000c50650011003c001d0324180245a143d032420b43e00e4980c061040c517503002003000215a0014035140c040500303400e0450910030255680b0100b0284d5159201009605c60a80c680c182d8590b03036103291100c51903140b000400e81c001c00200c0c140005a4100985160444903203548100010a0710615069940100703510343c0300340c0070f104140d4401e100304101d0340c00c1c41d804000540c072100c9421105a0880c1c0c10000c0c49240084214116844801844c1d000d4001010030400c049208000712030f5160003101c0d15a48592018419004000180c0c0000300c10100c1c080c811003410310460584100c45240b403000501c3c000501c0119081c2d0000c840040c0072401074000356010134400e500c682c6a0351844d00000603841e0300d50700341d80901c0d0172640c001c0d03800764030800025032103003010311006802c45181d0400503a054800f03050300800e520000c01005500340c401400300d00341d6030741242c4000107000d0198031001d00b441b0250400d458400c111a031102041075001c030048604e10a106240101550b0014036060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 628946978 1250 628945728 628945777
    0x604120201020d0e160806090c0405091501150206060117070305071404080d020705040212011a04150c0302010b030a080406030f061a03041b03120302030c0c010905071406 75
    0x125044284010441d982840342e0700d54101c840c0b04101c0358500b950300038510205145020302528120350040c1100342c0000080c08480c8400042c01c0b0952142104c02040346c1e07460014152420480c410143c560000780d5000107084005960400e070880040e60965146907038040054441d030b0544651703502030484000000b04c03103034801e41c0310310b820460500d4207191100c550b1f0200e5032130703802c0360304801c0098009031046100c451b01000740100424040e2402c1d81008810454059240414031070000001003808840850303103080d400b21006000140b1b0b2900152004440007807140c0b11881e4114050342c80e140310303088580740c0043d101c0ba20310b51149c2024074203410b04004801400001500e8002d2580b502000300300d40003900e0003030400d0b56201c80c40b2a2079151a0800c00d52141c0710300c17002c05080b0000007040c00070981040300c03001102103074240541d0700e032107607103c400c1d05118507031904103154a42000501081030100307800c400c07285080f02c43e18010154000700101445078180f01c0e05011001c40700c5261 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 628948228 1250 628946978 628946993
    0x3030e0d060b1207090f0501120210140a0e120a0b06100c02060c010203071b21090b121005030f49180501021b041b021c020c030604 58
    0xc034070409012551610307190118460840300e40031489540c01465050004e0391043c070a05024900c0c611040c41954502030300324034840b041c0d44019000c1c68205241d80c0d0054041c50b0001d14401010078080c2e41d440c900c00c0014002017060920520558000389046038008000551082c000c0d00000e4603030040d250b0004100300c1c004140100c0701030285810310303440940d503810040c0200034084800540d40e4501036500511b00c8045a50740011172900c403142c1c00210b030154144100d80c062505c0c0d041e442254000c000ea070010307103030380c4400c1609500140641042d480c40c94414014040300c1d03231f035601c91900c030340c105500c1d4040810004440d80c085121546041c040c158107002c0e640c01c0c500c903100442502d41c20601701910030311039880c142c05070000b448800b81d0701042c1c0800040880352545045400d02000035107800c4501d600b03550f00c180c1e80018940300d80d6182d200000154111450703003580302c0003003c06500c0e2100c1e4485804020001c1c04207030082800803e00c0ba8088030000c014140d10794480d9150b60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 628949478 1250 628948228 628948249
    0x3010312030509120a03090c120c0b1c020a020102090f060f16081b2107030c060203091c0c051209031c110328090e0c0f1201030c0e0a0603030e 63
    0x9514403400c000004e014800b80000c0655421966001c104c0d0901801c1140c440011940101c3d500c40c0d11041c090003044030b0308840320564000b450780d80d649254412100803156031030440c40310401e01c009401c0328030076015401800d40d080180c07110030380608a082005400d001e0145144c1c98560100101000d2801034983d07036002342d108114003420000c203009464450500421709403400e41c0421032600e420440284880c141d681018642d902e0182296070081c580001d407100100070580100101c4c0307412405000c40c506903070200c45142c0c1c01d04000701008004035000042540d85004910b42c807030140c40644201d07a202c040180003000c00c1c0c100070104c1000b1300b07050f5240c1c0307041162a641103d03180800b400141401c5801d001400c10f480041c01c41d840001249107044414003d8a5904010820404543c2503200001e03200e0140c540b8004000748110744940d1240d02400980040040100f01d014a50701d82612020302c202c200a50340c84100f402158118040500420598500043c02d481c0205900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 628950728 1250 628949478 628949491
    0xb1503070e190b2b0b0c07230a0b070e090a060611070f03021207091107150b0d1101140301030b0a0c110a02040c1202031302040e0703020f090603160608070311030103120305 76
    0x38903814495403956040d0b90700a5a01c0104600d0003d187d8003406400c1d40d204150491442c92440c1040311741124955450303210340010306000d1008001022903010710520781340d07480060224900c900d002800d1000400c01c0c0c7c040c400c0440c024059a011458002908100f621440c2c1c80d14242141542c0030040480c003943c4a4104c2e900c03c29901088009082c000d005000c2c40720401152183c1d00b9140c070040700101035042c05005480c204020a02e40d6a1844921a241d000303078016090903c0000100e80080c2280112010140c0000001040114002c4a00d120390b6000d2420081061025000c0702d0203081c2030345c441e14030343c0141c03466805890154001a2074036500d0800d1425250007190104c02d0360012900d030034082c2e030700803080c2c015424140241d8980c01d2102000d00005070840c2d00190310400da551105009040302d0300052000d8508000010101d08540500041c2130798407040148106000c58071640007904200e64075040721000c000340d03810f0300e03805403c0035405446824100e00400c4020401c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 628951978 1250 628950728 628950799
    0x604140a150f021324080f0f0a0605040207050303100b0712121b0201050601021213030b041104020c06100b040f09051f06090911160b1503070e190b 65
    0xa090704014078060715402000200c24401c205089103040408010105c00e00d481030124000400c840c240702070344803542c440d20144090900307850b1600b00b04c00500c11908a150414400038580082c000b001029500c500801f00702e1040013a2605501c030060b006e840e0000b0552504080c003505483e0155411344c0310b28140c003600240c0700610300001c0041d04082c59042d030150b590f8a00780b1805507418400310082001c484060741c45c19030800400c2050b2080d0b0310004d8400200d050201c0d0800c1422402041f810500500a6407520568001c03240c4a800649021120000000307000403174006040c26601240c200c1041c0800385031901d5000f0001c0c0600807c1100480e0044c12600a820036207400c400250509541d80543c0c10709152100d402c603071402d2144248800c081c0304c804240c2c0b69004c130280d011a84008140110780750a5810100c264800300e490368540102c4001103003c4e0710310103c2e248148014170001004403d40200f40301200d036000c030074642100002c00f01846040d01030005041c2569803804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 628953228 1250 628951978 628951987
    0x30406140106171302030d031a04020705010518060705030105011b120f090602070e040201140c01060b0d18030f05090303120c070203011104060507170c0a03020604140a150f02 77
    0x2024100c10303100b40c00c0304011030b000358a542c010b00341c040141544901c4440d40f540d500d05180d00000e6485c040d202e601d0301010340f18050900421540f00601e01650701c003030300941d1500704d14603220740030748000c48005603940300c0c004940000382400201c180c0078000c00e8232110b103540d013890b00460b54625070301c80c05012401078840200008400000310801c0080580c0d03505040842070500401e503c915600c5001154080d03201400281141d070b41260304903509007011a089850303100c1031441d900960803121600c1d480c10740c2c006813140b0500010020100304e0a0701b0024101c1e400d50159101c004480003030001005101c45250a501500040c07040100042c2207905060800d1950000a04c0446128064a5001c24138808600b0240507114500c8003102c403da0619003000d100a00138003941c8809411002010156516a44c0e24000c581c9240d0b04003094600300d40c0700e41006540d0751020350301110b1031100040190309050000c034100007200d5000c4d0f140b40311340404000510150824601c000c001c16030030003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 628954478 1250 628953228 628953251
    0x408090d050a0b0103020109140303030a1a0310020409050c0f190509040c020f10141306020409051501090b0405060d0203040203070806070206090d03110f130906140a05040209030c06030406 83
    0x4000b03500b940c4944030000456045200040c03018065030b100820300c418403c20169583d6000c01580c2e800300f94a40c000a440303010f64444032001c00b8a80303146030180540c125040000f04150000d000350b460021040c00103498510681ea10351103003051610b24210207000341021005140c5414a410030b842c42d250b42403040d41c00016040b079400982010260b4015844640002e43c00d1212a4007412030030f02c1000914a8103000030b0740000010b1440300c80c6454017030000300700102981542c010700440c032002c00c1a0314081000d0103240361000d507841d011520341680003d400d1010012a001d641d0301410301e070f0404485240c80d0b00a50405402240d040c000e8070000306988104104082c810768056008100e00d0402490003800c20401e2890175041504003800c80c03912030150402c60f022650003401059031030049002d50024104103801c18001d15060210008100c03c2d40201407202d02000c694148083e5620420002203100d0349480a405400c600000101440d0000c007442d80103028030804502550401d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 628955728 1250 628954478 628954483
    0x120f100b04032901080703140f0a0308040807081b100e030a0f0306090903031b030207020306070c02130501080d0311070b131b081617150714130801050702070e0408090d05 75
    0x907045084154086d410801c11b0080c1011750300c10041ea40f030054000c2d0400310386000c0c1c80364402e80002d0240110309020508000401044410300f07500702c0010354035107141d03614809e441345410120441034450f401143c8101034251254614014001d4029890702400041c152144850041038105150f0b03100c0001442030030502030160511720a9400180002001ca22120050011420501010310600c814001a200016059040aa10704001c0c110044500c0010214024000e10440090070080009416840080c0000b10510301d5142404507402c01103400c00c00b4010f0701405400d0000b20030224500d4400b51aa807407401d40264420384d01c0c1021501e0306044100c681e8040e500c0340e88015880e4468000c00214540541482e9415800b0f83c21320388881d40d80d60400066100311566840d0215900e41d0248c0382d1010741041c803044403601c0e044000750103000d4040381e214010301e5500703000000d9603151000c5444015140412040c1d00a80c172107840b000b810350450030300076400c42d424100c0c150114404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 628956834 1106 628955728 628955731
    0xa0f0f12081902060f1e060904021f080402040605090402010507060b0406091802090f090a0807020f040501030b090f010c020307060e010908120f100b040329 69
    0xd41030201451007a01c032180e03003101c078400c01d040d0348035004076005110301c4851040a10565034440348100000c85e200320b0810f900801c41c00100b032450a581400c2d0000d00203840b0782000407120944156440800b401c0030003046102d410807003145000c0c0550b1000e00703030548041d1940d041650020380303d8000d6071030040015859401d00703841a10b075544070400a040ca42d0040c00a840420440343c20ba02d1007070800d0780500c0540000800850129a24500a8201c1d100a110810013615201d801d078015a908a03482701d083e90702e0ba4010380d11405960b0107180070b1100000707a0700300f50520750720300340c100c0c0b10940c01641011824500d480d004800d03101d5040d0001d0011a1407000310305101d004002c21030004240800c0452902d44c414082141ca6100d0b100b1803282c003c10f0b807900300340781005091920421040040400003440040c040140705000e80501544031404080000d00082c4140c80 = true := by decide +kernel

theorem cover : BRFrame.Cov 628776978 628956834 := by
  have h0 := BRFrame.cov_init 628776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 628776978 ≤ n) (h2 : n < 628956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
