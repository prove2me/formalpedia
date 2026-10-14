-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0813
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:56:39.109905+00:00
-- url     : https://prove2.me/submissions/73d10487-d995-49d2-93ba-e199a492a475

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 146043165 ≤ n < 146223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 146044415 1250 146043165 146043167
    0x110309010c03050c0a12020d0f1403100b070506011e0605030a1119080a050106030b0a090f09061811030c0f0f030a02120307170301050d0311010b130f06081903 70
    0x102540120240312041c080000042c0c0188207110802d8010704100c000011b0010009081521064451092101d243e200610041d44240703655945040d07036920a0ba42d80300c00c924107200000070b500001c103031440013603400f0400c1004503805040302c9121000f22000c000c000c0d41c900e00f00d10329003e181c00150f0b0a03c0000c00140240c0c1003403420441c1980f1992420391030032079405a09201c0c0f8015408141541c05005580400c0c1c07040c5801091145010807412142e2800980070744542c3c07240b0410383c4d403909809156900c0a41c0300d18130095000c10100002502142e0000080c0398266050303416414041c054040f90402246d107641c000c4008000700d4820041004110118040390321b815018828802403030016203454000b03030540f001030340040d0303103e10103807600094041d2601c001c10704901051004200e5a12a11100506c9c12b515090003010403101c00c0d0024010700e4511049030340070b1444086c01104000079803241a01c0d100c900b40c00d2180b15104d690082e95844807208a0141020300200c0001103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 146045665 1250 146044415 146044427
    0x15050a080408090d0204050702070317040303091701060807260d05041809060921030b0109030f05030d0c030b1003020f181f0e04050f090a120e060c03030604060611030901 75
    0x10603c0201086a03014094000c6005c4503401c4405401503800761005109102c101a00710034841d0295054a01e030034156640240145424803461983c90341c05140300c6070004007908414003802d42e0340c04590442d5920300320b4842203110580e4a41555140315010600b070a80031030b00a1008080ea10350914041c500082c05044001412030124200d0f81d4013100b20000c4c134140104660180a4500200c18403c010040168604e0880c00b007003d01d89800b2a80800d41d80001c0418100d80d002071292240c86041d0400b5070079445007030540118107140200b80128a0b070580c2c4204080c40041c0e0360f10803181509003040d800c030301c60513050540310f5100340700c08070549100e1175185502d104064a42282c4404003100003903030359452941c28000c02d9944802d802c403070400e4840c0c40d07880780410003020120b04210840980360100894050001007510300351003d550700804904119080241800766200700021a4944982003036422510a504210700001d11714881c0c0e8090b400340841c2c4010f1031510440c10015954 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 146046915 1250 146045665 146045677
    0x80c21090718050103020126040803042907020706090609140a080304030b06030d0504260c030d0c050c15160203100204090c020111031303030b06040504051015050a080408 75
    0x3561240520205040115411150352003440c4880442c40394198400902a11003460150781c06003024402485140d00011805420a81005a941c2e40341c689003800d98100034156254401c0510b0342140d0203010040349401c6224034404d50a0701c85e22512400700700c800600c3c134851040010030f000c105100da484000025080030500070083c440040e900c10b002421900f00349e2054034011480401c0144034141408800300c110302c02e2130300c40c0c64541003010101000480300d4004a03850a244420741c401d00003000f079180200801012a20144800071008003030703404120044540c1d0040b03422401c0281411030600086801305560541001c10060301241c0000c841d410507030b1305111b0344006c090b404a40e84000c00c05400c0e2410040b0b8134501e40c003406402c0d11b441100c01c4081920400170806070018843c5101c0c1815814640400c101290400150f542d0055404c0903034800d1500091001d00603070210380034100c62242c04007040007403100d5010b544030300407889070303c010492041c0002c2c002481d40b002094 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 146048165 1250 146046915 146046931
    0x912080a0501060e060d0e06090f0c010203070c0608100905090a03031b0807080408090a12030f21090c050303030903070b070206071d27100f1202060309030c03071101080c21 76
    0xd0301d144107c0b4441c0b50003810b17541c0c42e21a8101d14040700c42c19038148100e41c107a40c02800150719101d085c1d43d42c1d0140700140d12034081004230341c101040c60446c00308101001000401c4080c4240c2c1042041c0c1519481268000ca020900e00211015101103403061034003d0130342e90729903001503034403114261451440200100c2d61400100000c1d10503a47d107240c00400b40019200d0540d2907413640c0b5000c0c054074003031008072081c800c008050b15403100300004d0199030200611008100018280b42903409a1010780202d03070700d408040100648400c000000d4100d00380136502c00450b5440d400d1090340c82c1c031410f84e0b10200040c2081a86900c506889142d000f0350100034000e000c00c00c0010060b403c541c0c207a950b0810001ca454020300441210100740b070f0020b807140c1c9100042152803e4009540310404000c001c0c003800c40800020284003007841611510440e03007040d0381d501c490301d00e40181007142100400f408154000e000c225090045410345440e10307082e10b1402c04040e0b07000c1d000074243d440104400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 146049415 1250 146048165 146048171
    0xf0306051e1009050906060904020609240306090610080402010810030b04030c030e040b03100902010504030f05160e0405030901031d010f050a111201060503190912080a0501060e060d 80
    0x5030400106000d841c4034040c40c100d20b440c418286101482a61000360a05250b54003044c140203581e0b81d52000076400c164111079090ba10003d40010980017104503e81d4506d4408a008816104070785e04000c505c5880102ca00300d6007581c500040004405141c405c80740022200d40000e4015405200c0081e041120814428903050f078039075901d10035000481d0128006443c0c02d04140c201900014000300203842102c09000f195802404290b480300031002140d503188d101c0c1c1d030303040c15640100d0407100910740050030b280e4240d01034284165180000c00800030159280d07880094402c413072a0303856019551050247d8039090350000110040c0801d418400700a021a5070130620801c1c0900c91201e10040e40e0102245030300c2c0ca140d941007102c1070442c1c3e0103040c10040101010742c0d15070b414003905581250400719102e4441d40350140e01d403c036403924071b1a80c034580345401043c040c08480341c1100f441c40c2d6944260544d221940d81c01a16002e20840c00820002d440c400018034007000585100a030000c400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 146050665 1250 146049415 146049451
    0xe0c0310120321060803070b04080415021608010b0604033f0201050c2805040b04030602030f0709050a151403070801080f01060605030105040f1d011a0405010f030605 73
    0x41242010a011004280740c003011000321004070440f000c0c0811101d8041007241d141c020314030b440f40300c2c030b610003000460124000390401c910881514060846c03003542c51221502c04a0280d40d8199038502164504041c0f03074005284581406100c808600181580d81406e02c0d5640f08018101c20841c0c1a04c584901036038140d4071070104080d40c01000105035064480e0201d40c41c080d0840384003800c0c004403800c00700a1104a500c80d920480900703080c0d45050352401400c0c80048401d4040d40e00300441c0c0000005002007032001c039401039401410780e02110000d0f51034450080d0380b0080c9a10800c0e80081221404014006120369030340c5a141c801c0c1440c4804400c180c186581c1c0f80e1084903040045030181c0018003500c0800c00c10000740c010108001c1103061b0603c0c00252450105200341071155481e44030300407507100d080e0401c10300f46440180b80c002c41c1d1010f604450181c1036003800390071400001403007903c16240038051281210042c0445031a60360031512118050a0014114100001e5240398 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 146051915 1250 146050665 146050679
    0x1c02070510110615040f02030609040b040f0503040e2403120c10110c010608030c030306100507050615010f020a0b01030f03050c030301090609051302030c012d090504060504060e0c0310 81
    0xd45482090054005144c0201c0d0700704000032070702000c0c9015802d42c41402000031545070b0101c001d801c1034000c5c003032007403070740d03c926002810240d8250010030a0101180010b070300403101c01528020032030f07018400c000441120491003a5504403042c81d070716510201d00d1030703401700c0ad000050a4001034141594030500420000c0300590301001601404451300092041805200f84500c0c2d0203030080300e014510305505108240c1e41c0740405003200b44a01516404c03104410700410480714102c0d070000a4600780d281000300440f04c500c0003a0111301058041500c0c1031450302c00301d200d0901550042d00c1038400e900b507468510720a407ea46007141482410809500382000410240d8003c103a00400800d1312424200168180c4401030009800c1c440b00c125070030010303540030440042c512400c0ca4000100c6030010011111003c15110824040005a00b2580050b1744080c100c4241c85003a0f40610069a550060108a4043e8802c1152001880b40030460740740c0000c00641e001020020b034000526100e0003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 146053165 1250 146051915 146051923
    0x4050a030809030709140103060209010219060507020105090304082a120708160f030303020a0210051302030f0d0207060507060b030303100e0f0603030a05090105070f05030c1c0207051011 82
    0x40d00d0078a03021481c9503440c0740400c0b819004d0b100b114030a02800c41001c2c2c025800b440180070060000d500441e4010059208014942c0702240f00d65a140640d25a401c11200812040d5080d80055090030006045444008100c404a820749401020b22424040c003c3d0855a030354a1a8a030075030425161280683d284010340e05a01c0c07110001e03000f103916290449103000b50600303600d07032400311440b020050045124038100480e07030141805039462002440890a02d58948401400b540c508024071134405048658034010a01c00c5d802c4038040c440171404550794903040d0004500503409807a0030720580f4840d03009001780c81c2c401c0c0d4002c903456440e20006400c0d80c10440d81e00c1c2c07900c0300c27030a03040040c2c000d0102c606030080030845043e101c9003401008607480c1c1c070400d01d1601c04e0010020722034074103034843d500311042e2540084204060300494503120340c0740d50010552030700d58441d000030140003c006048081c081d4005c1e4004001740b40c50682407120b05079044032880f050022254080c501c81d20144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 146054415 1250 146053165 146053169
    0x20705060a0203030118061206020a0302070b04051c020102131703070c030b0a0b0f010804080a1803060f0c09150c020a1d0601091e0902072d020301050a1802130204050a 74
    0x82c028584070344c10010407040c614080d01c1440030302814148100100440ca122062515801800c00b50741d51011041c260080c3c42086030080602e41c000003040103011020420200001c500d0800c161076460303d40e401c90a0340200c8031f02c1a84860164000c200c40e8100103495a107481603402607030b0804240e624bc030441118642d005440030101c002c100000090b00c0c3c4103c14100e401103408d01999038003840003c0c10340c20f00900c000c005a0b000601d94007500d000e50310071503281c0c01904d20032040c10344901d002805440784184042401f4108803011001c98000c04243c4240e0f441c1942c4244080c00e8404100c0d10800000000d9802603012440400d500b440240e000b001c0f16800c0c0340d442a00c0c05c050f000106400481d078401c00016032400440d4000c481c41c1c8801c40211140b054000d41c45103c0c0d4102806071041c2210303079036064031100c06030700f03031910300e00c0c02817119680224020800c1381d840c0800c0c00192a1403106415441070444860401841c1c09003845000c018203820040c142915900480c035103259239 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 146055665 1250 146054415 146054417
    0x503060915131a090705030102041805010f031e06090804080109110102030c03090d050f0303040c09060e06090613060f0b070b090c0105190c1a040b060102010903020c010f020705060a 80
    0x1440044200072144188603400410080700000780702d40d541c8400740c0d41c032a50020040700c42c802c0b901040d8280700c1003095401070311005000f10b41e16a560040c2c6044100840400321109090800000d248506441000d0461350000b1091039240c0e40e81c0362007074017259051012280c02e076135101c6040c003250085002e400600740700c1000141a4415052503e00380940d41141c1d4115032081003106040e031404801d450780f62100b0307500420a02c11034980b15081903400192103005200110400c010312104510240491340b00a008019040c3c81d2291072035103a9007120166004080c50020400501385a241e140c408240c101c0c0009900b07070ad50144070101c0e505079100076035018020545c202401512400d00d034000c0701d504000c1443c0c8080b070340041c02c42e00402c1c02494850589aa00109040c06490a200c209900040007400b05e414042442a50b03842502d003914460000750005441c1e500500c40c5901280c0c054004040c5031702480011103511003c01c0c1d0080c1140500c2000107007c0e150304001c0c00300f00b83c0c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 146056915 1250 146055665 146055673
    0x50111030114040e06220507092412050d210c020d0e0d110108040c030614010906080102161407030501090f110316120804120317100e160905030609 65
    0x2e15020002600c44000c40c052294004400340910059000081001e400c551640503c1e40d140c00d0a00e10305224560b4031591802d8108800c0031070701e00d41d044030042140942e42100f0b22154840303500d16480804080c00404590040e6842920580100c000c0410004100190045841c1c450250000d44640c50781a80c09603100d00f4003060100d401540d840e084080c10340e0b0349203050820b40c84000c0814510b03e040c5050103458008241070101c1c15003680b000d19040030052009035465030290390310490034030039140ca052800b403010500b10018001c48011076101a42885048078030b46601d48003070740421000700e00f4400e84000100042d000e0140000840c007a00311080f604140f070503c1d61003d1110001c80d4440e4200307a00340140c66885c104070506036102003204d0381c084130040c5020142d0344150b4000c0f40d0b050400010030303010168840d0484444006468a5030381e43c4d15540d800024a44050040c5002c0d0324940700000d10801c0a03100b055a0744000d49003841d182a52240843d051950075a81c03006c15400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 146058165 1250 146056915 146056949
    0xe0d1407030b060105090f040e190317010b03040503030610030612030203090f0f0d0615030212060a11090303090f0d0b1008010605060306010c060b030f0d021e07031e0501110301 78
    0x40ca071010076030f0005003801d01301d24082c000c0c400100e201040344e80241c0304d00e603103003001e4440403020000401043c403209004500f8844c1d9080141252803d8020a052500e5010000c01c00041c0e20040d2400740354400019402c0d80c403803c0070440303010b0840c2d645108056541c2800503000045000954219000350091550b40c46460207018400302a2000c0781d0069889a040d501ca0352034001a1801c40c5030403000c000381d0400318209151082c1c140f036201a40c444200b41e400342c40e100000c600c0500a2140d044100032900ca040081074660103a0143d080e490b81042c803145405003010801134101c500c00034402d04c2078144c1640c90400180301950105650f240d0664144011710007481240b000e008100e4030070f03045180410009040c0201030030010f0505448040c2c1e02080e48040214560030012013080c1c66048803c000300030b54a140040307189020901001c4004e6804001090100640e904240f1140300d03454914030301070b8000c85a800454056580b4030701c1048106034000514041d001e100d81341c4284030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 146059415 1250 146058165 146058173
    0x30c0409050a0905030a12020f18040e010608070b1b150613090f02060d090203070905100f050f0111160b09120102030f0f09030c0303091e0604120e0d140703 69
    0x9800140580c004a00d00b4080f000850800010344801c800f00f85850010001c028441c0c50280c051701d25010700c40500482e10705803000140b2090482074805440c10011004004222826600d8920031151990402c02c41844020300c0742c80280101c45402408240807030a07080b40e14900b6000303102400d003015082d401d1107250b1501120b08582c041c819807050003414800d03143c1c0c16140c481e03800005d209490004115a004c174460f00078002154004042e5825103035a2000d03407001c2c0600f1100440385403110417000c100c041000c241c0900395800034040c04101000100152003000504181c45c00070310402c09010b9501011a02d607138068545500002c1d216841c036000d10aa00416090086c01179005208200b021707c49841401c0d8403082c481084901611214015401d501c2000306201070ba000010812076800c40001d4206a000c2d441c1840c004052011881191152010b03503008100d424103580b41307150b103880b800e03e41e244030b88010724100b05242c5aa8554004d03441801c20f42070f460300308080403c244 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 146060665 1250 146059415 146059421
    0xa1b03020c03121003051213060f0e03010903020a0204050610050304020609010c0519050d14030604110903070f0302090703021905030a15060c0302010b040b0d02120322031e120318020402030c0409 86
    0x1c0000d84e911f42d082c41509454501c1030301c954002c0740100580c100011940c14803503a081c81d00507a01400801c003040540c10002d49814040e00142e000f5402d080104030303941006c440c11100c0320199a01c150554841360b00b00255540540d42c02810003006800701030101d042844402103400603181c50310b18030000c41c0742c00e42c1006e2105403000c0c02d02180c0f41c03818150816040c1143c0d40100100c80c0002c184000340e1200020380144000c03242c052042c04000b00d042007001c02030f4030a0385d008803407440c035039981d1640840c20b0344262070003d4280310b52650301041c001d0184c3d000c1c50704021820700100c1c0c0f26209400040d0000c882d42c0c488000242da002c0000281030b028855402c0000003510184118607404010030310b5544110402406202e070360084001c0c44601744142d559100b01404400f01c1b0180c0d08945004401d0b05000642b40740c0d00c1d403070789040e88040d03443e81d00b045242d000c030f09040c0c1c82c0c0024005400529104003800b6840a190450340b00607076851000318815106c030780034580c496007030041180031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 146061915 1250 146060665 146060683
    0xa0816090b090114240406030e0c03070f170109021302180f0609012601030302150106030c080c030a0915051602160e13050d030203010306050a1b03020c0312100305 72
    0x3442e2201c018449403491074500d20b0440c80030f40b006801d00c01d00f4010b03403010300902c40341495007001c04240860f0288d41758102192050110080b84d1201480004260303d42109110312640a0300403042088030b2144c24946100c9520030100002c2c0b00007503600413810003002c01e1804601a5400240c03030a4001d2950030b0a8560401600c140c184400540046811486816002410b00003003070580007406002c0284e918944420001e0b40c00035517500d28011356202d21414a950b00c55110100118005102c0e202d20032408030300b507440241035114104c0c0c1c0e440d15400134004125003501e41400c50081507842c0c064251a444141001a807840d00e407208074500c404280300d030811500702408548010b408140300e41c2c2900c408030540f200580755914a850394a038584402411409408013030141c064256000e54101d07405900240300030390300c602510080b0303030404144a43d5030713048420981c1024400d6020f003115011050807030307280000c20b14040294160886210309040c00034541802040310510030440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 146063165 1250 146061915 146061919
    0x30f12040308180705060f090a080627030301030818221803020a150b0a08010f06170a0b070513031104110703020d0f1b030f030c0f05090402090a0816090b 68
    0x350f1403564071070540c0356135291080c28440c1d90041010404503001c041118811070707000300b0106e52581c1d90800030b0344528017142c40700c2e04071103141c1f205034660034074401d0000f840d68120701440c5580c0c01c5030341d0100a90414207000d800f01580101c40d20041d140c206892002030703111650500708071a000c000f48203417400c800e0658080c00882000703000098001402001c0381c2d034031080550070800f0302003a5000820700c0c3c20006a00c403040540c000341c500b03019440050244001340e4180310b129200c8003410710700e9200d181c0398001d40e403080c1c01403070114402c0681507801c44180d2034141c2c90301624800c80030580c0c565030400c2d150312200030054007103403405104046d040e0f000084d240c0d08242d441e0720083c0d100d41400200c0e00503c42d20f95010f440b224441c994aa690003c00c0d03861080c0503955007401001c451034201407402083c602030b5040a0f8500924500380e0402042e540c140ca88004002804042e40010408903000351403040e01003840c041c14800d6111000c2030b01c90b903406451a040860050f82c0341a06581c4c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 146064415 1250 146063165 146063191
    0x60c02160605030c090405010303051209061302041d01050a020a0206090a0206190507020d030509030f070b041401020f0109110102060a02030606120c09190510090807090509030f12040308 82
    0x4404200c0303080d503140c00c44125051090310b0382c0e2008002280c92050030356090744549013000100405410138050700e043e24004040b10416620409400c1d80c03103009482c41d0807100540c80e142401450a50070525800d80500c16a6040112241229094130025501c032000c0540208a1802075a81040140c2d444203080c1c009004403115600442c040c2d2040031514050000c0c001604480f0a001c2c4040b138501d00e6000d4000c5001c5103450030010b00d41e4102080540c400d016108a039040c0c1800040c1001c156040d0850241c5094030b84220203e004100c22421419406034540403882e034a028410000c8850090042d07540d80180e01c0f000909141d00285120b049a1041c41441541e440b0001a18810030680300400d000f03840703404003c0c41c18060781c944035901c08800c4c0c0c0e11a000c080c0340c0000808031041620212240401d40c0400c1d10155a07602421010b90300c500310400200405801554004495005480c504042038400d1840b5910501c1c0c00d1300d80c02658018041010340c8201a281d021054043c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 146065665 1250 146064415 146064433
    0xa02100204231c06090605071d061b07080307050706080108150703022b05010503030c0a0f0c051e03060c090d1b08030408010501141f050c030f0a030207060c02 70
    0x1042c401241a200c0c4034144805459101182ca070030b24500c07508a41d1825030724103085585030079405042607940854810781440c0c0490300d81c501074000c0740070f2400386081c08228011045c081c0040c60b00542c041c841d142003402000034051005000c01c0c400b41c540e5101035503031210141401da150a0456010804005801c0c0041007034020104503080302c509100c40341c1f125500d822134100c01a0192411a43d9900604201c01c00d08202c0410f50024100c800c03e82400a6a658400c0681324051a5090802030300204010310005507070482120280d8400c5892200d26926040400c801c280e4a0056201c2e00307140704840c00b141e103410080164043c2030f4840c89490007000d00003064154071800e00040c00203054030441e0940944101110380540508800c50b6143d0b80d03225130035806040c0c00c0c468540d480315008140b01e0141405040da400a02044c440c070b0030303510f50015048581d07901c10f0303098181c50b000520691441200c10001824100c10642d0096121320003414003100b1110401c41140c2594040880 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 146066915 1250 146065665 146065679
    0xc210c030f03040303180b0d092d0b0a11030f09060115090e0702120a030609050a0504020d030f02100504060e1014060d021201020a030504031d090a0c0201090f0302030a02100204 78
    0x11a03090703c5e0b040c03810491001914980c0144814650400203044401055000c0315243c15800783d80454010b205000000242c440007410580c0d01c1071011196080226068000c141001e120a41000d4a5080011a4441c00c6180704098100391001070b040012402845188181004070b86d0161140781d18084060f0754401028001001601c02c00840010708000103075041c0c002e02c6900546d4841c04209507841052202c010002d01c0301c0e01402c10503900d050f01059924807203100311445143c2c00b0b0f0030041c21213400d46094070808450920710b4114800c2c0d0001d40342d40c200c9030090500592044101103202c00c500d03040241040c10203010500c0140c989411000910074412140781c10000684112034058618000308800c00c60204180c0080d40c00080e0003038029038154822441180607654041410310501c2c2548a100d19900d8016800204080401e040c1c200a40c0045880409400001403240d0190340392029035000e08426000368101040459030700c2d405009003c1c1048569808515090511074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 146068165 1250 146066915 146066917
    0x3050d080906040b09160306150807050604050d15090501020a080f040f0b1308040e070e0307062a0212070302190602060112080c060c0403020112050105060307110c210c030f03 77
    0x10002d480e01300c52402151020700f003440f02c0000c86120350f4a03500210b45900b490301c00381481686804003840c4c0c51400040c20b0b400884c64800360740d4010082c81c0b41c00d00d85000c00103103003101001502d01c1c507a0109406213140403886100c160501c55400940c80c0e1100b29000f4240724002402940c01aa055040000107040400340c4400d643d40004240c4043d04c070f074042840d2400d03001d0f0b001808130400060100702946215021882131100f5030f103c2101981410605454088a1103120080b0b00400516a00d15020108802000c5002c54101c1c40040c080d8000030b860b400100c8001d81c0c1c0e034101c42d0060041d42010881075110542d91007140e00f903140340c580001d5039407005101b03012124000d890550f003081042c0d800c468003005403000320740d8981401440d00411382d0107440103c0c04074100b035150b810010601c0c000c85048400092045042d51b0320303c8004d0780c01c80e030081504003083c09101003402560365090303003540304600600342d40903803200654420b9117040f4200c002140f2a610002200303420380c00c000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 146069415 1250 146068165 146068171
    0x902040c0305251b200a0b03041401020702060f090906010306050a0317121806060d120c03020703170a080603010207080306120106090c0e01020d031b03020f04050d0b0103050d080906 80
    0x3810a002d2400e403e41c201c07940400140e1600d40d030b201043e00d03d01030120072120b1010310b400e60007001202c50f41102c201320442c201481820100e040900c0000d003c00c80d0380c849000414908400545402d06580c001122076101542c8030f83c901101103003081040c20440c400a612500c01e081c02c2014505000c0010201e5040e840010700340d03602841c10202d01413613602601e03498200d41034041c0c054204400c003071454046241031b011441c8100e00010700145082000942e80e1078210f0402c826081e0110004c407920304200700c003074081d48074400000000550f92000100c64600f603081c0c40341c07035081000c001407500c003000e01070601ca80c0c01845030101096a6008a03501701c2d80490750500e200d11950000c9002d41801c2d4490324809103410402c40006400c109114000740090b400e0720304070880b040040d021207200c941c804070422081910b0b0180309000354020040714144254182c2019550030000c1e0f40300e840f0340811182050f07028010404c02c40100b1844118941a0070030a006181010366999951401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 146070665 1250 146069415 146069461
    0xf050411040b06090405011202032a091f031110030e0309010f20010504120305100302270901150b190e04090503030901050603160b040315110d0902040c0305 69
    0x9500986403035a00c3d14100c0f0800b4401500c00d02a96959003000820030303031b10040c04d90080c05000c8041c003187e40e070082100340340d195101d030912072600f0f00e500344000214014203042d68401c003945031a008a00e0744882100940c49002d980510044681c140a000e101c4e6041c00030a040c101910002c408030044143d801c240c10a02c2c040e89a00600034044541c1c502d840c0345407900680e417100c4c0d0403031980107400181c881ca0149020300040b6141075011411100c044405021805035480f0a00c0180f40c0303111410f985540d1907007450802108141c10b000c0491080c0d8400000ea95034a403403803900f44400001100501c051882d8605104480d0003110340003004008600401014042d005110b135110380c81002e9a5402904484c0c032490115000f80c000e103400c0e21050301c20301c204104080c44007501d440d07000940340038440407400c0515540d507411101070f205580001320340d218a1110208001017000c1d1203103038480300303010551000c280103000403111a0b9841c0410035051008001080100c0c65000e405a096 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 146071915 1250 146070665 146070671
    0x313060c170a0f020702131a060f1b1f0b10052104020301110d020702150a020a030c02030f0a0c0303090e010b03010501050d1b11120412030c1a07120f05041104 70
    0xc03e0f14440001e00c200b80c4029805030305800c5144114070315030f100c50095950b840c50b40e0f00c00c840e0142041032601038901d0030042c64508000041508a140a2a6001010740f2040325044451503030540d44480301d8030302c0013030819a203000301405494551640400c1c5556420040c2c504001d03103d0700301c0301d64820740303490200c5850b50700450110b460035031044500c00380102120341c030381c8800d0b09424042e502030b49081e4420b0361085042c101403000d40b011262203403401e0300101014045968141c03080043c0302c030240c0c0d150150288103001d03000240005036181d8820048130b8015403c0d454003501100c01d94124462810b118001440036040400440b4195002403d26984400310702141c00e002e013500d8080b0800c90a1011428a003864200c031a82c079207040e10005641182060401090b0039000c4c40c0f08911b1080c000c15017030b50101c0e0003035a0100c0100d024131416490a60303108004444000b05882c003200007440307240443e010519a2055040340d50344144288940e042644801108480c038200c414440e80d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 146073165 1250 146071915 146071931
    0x91a030f07090504140a0f0b010207050d06150608010602120304020d0840090b090a0b030708030a180e04030c03030c030612080a020607081b030c09060313060c170a 72
    0x100a81440b401070000074400e0000490040d001c1c2d4042c8010b882411b1031508101c100c600006007402041400b10040c3d000780100d0b860107017000210300c0910350507140d03d030b80c40100c2e175100c0455160100140c02140c43c0c2031941d500d0004003c0c07905019110071412100c0074000e100059a5090504080d0b5401c10131164030340109a400030020004100790b1440c104c2422004101402625030640c4600c6540c4002070086559032110b00981d1402000e455104035000c002a20395941944000100000a011544400e031a086032602d103501441750745c00410040340702d0120350f000c00d2804101501c80c10144801a040c02d6502412144201170001d00303054403442c0c094011807080d0301c01c41c0100b80f06803c19056810b02d00740b001e031960240e019680180619000a86014040c8020b14001c0341110301c600c561940c04150280203800c0a04088000002005810515a0303804091030044034184031610305074207140b40c8441160b0a0200700c4c010700089404403541c000c3c681807556408a041140814226 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 146074415 1250 146073165 146073167
    0xd0201050c0a0605061906170a0213060314060a0501020307060f1b0824030304060e0d0206030708160e061605070506070302032d0403020d020a0b03090c01091a030f07 73
    0x201a00c0345000c040d20440c5100000e100103900402e01445d410342d4040c00c1d0701c1c9410310864100380d8a004100105416017889801c0d80f021320f8040d07610144a4000505129004c1500199250180d0164001071b0b1180407080d6a100c3c8016200d40240302103030315490f032901e40740010b510f902030094081d240b141d9900d000e0420303d0310b940001d0004541c5070b015079840c102e0389401030a01c0c50240c4a1202d00501012298281a060402d20200b0b0f28002e0045080a2402c6411148401c41011040d00001900d000c0f0300140c803010080c42c010101c5844110503464442180d50007500c06007500c0081251038608400aa1200c03011a0325030040f030300c01c0a40f210f4050900c11b181c0300b07060b4030032a000100000c01006241e80403001e001054a421a040b007038811400310211929101040500c110308204000c10041c50f10580c4803c1c02403020300002c4085540f42000304160b0000c65820f0080d40244800104a60340024500c3c0078108000010b010700210b100c1d0920395000c0108017600c0300c407607100854002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 146075665 1250 146074415 146074417
    0x504090c08030d0204140436150603060c03050f010524120601110106211a0405010b01022401050906010c050d03020706061d0a0203060607060f090215070b04020d020105 74
    0x90500001120740c2c0d42003c0220b80005d521600c01c400000840030a10741d0740c0d01e464001e0200c1c805100d0389460074100c039800c540780140329100c04400c605541c0800400090741f2000d194170040702188002075060310794288107046c0e65860a044040600c0c000801010142c0a60904d064410540c0c400079800740b040745e00310902c904c401c100c204c120030210b80e514080140ea41c125100d00001e0741c4850702c01c1003881446081c0d44260090186540e00740945039145201036002400c038502070705d0181c0c07414a6904070b0445407001a034050380c1a0b511101c0d0710940d541c04000c0c5e10540c0d00e48580d031400034146500000d5602c00180103241c85074681d50080765013a885400090340140d0088183d41100c501d40700090b0095018650031915281055400a01e00c1c008803842e58046003100c402d5001643ea07400c1c240001e62000704820341c0b2981c24049a404142075108030310b642c00502c4c9000419004500402985903002204150a00c070b04100c8800021100240c294000340c2c10343e040c942c0d640e428801038030302d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 146076915 1250 146075665 146075669
    0x50705070e090a05010501090213080a0c030b13060513020118060806100e0307060504031a0c070201080a18060609060b0901050d0c200d0305090c1804050f010504050607030c03060509010504090c 85
    0x1c1982861b00200d010200b6078014201c2040307000314105800c1d503903640380d07484009d00c4202400c00d4541000230804038001c1e4882940c0880f207940581440301e20f9580d00c0003102c03010340d05000400b0401400d48110350300b0181c8000c03001c4030403052000c8285000401080c1c00c00c000c1800340642c42c02c2e01b541d4000341c011107402000ca08010250b03200707291141e00007406500188001c1c0c0b01c202c02000204c01c50400741c4030b1180160004036101d03142c411150015105184081c1040081c5070740c03241d1040d0407521000c104030065104040c0440d0452414462105603026500a120911404c0090b40b110b80e070080212050440c8041010880342c072101c0f81983d03009c0c0c0c1061048480c3c1c60510401208803004200c011141c00341e610204680d80303807402e4040d07640300d4085015402001e036500a960414130421a107521034416000c565074544480c13101425035406840443e103e5200106214000340c060298444007400751034104840d514000008000703e80c10b1007280d0040d65a00c154105000c000189100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 146078165 1250 146076915 146076923
    0xd020c01020a0f0e010503040305160f050706020f0c0f0108040201141e070501150b0405060c10090602131403030403080a0320030604060b160204050601020f010e070510050705070e090a 81
    0x51900a80c01010f000055998107150009100c10000ea5040d03014030142ea00454040c1d07543ca0805009807211055100001e40076581c090010050301c2c00280c0401040c0c000d0400d950150503180d000c44445464940f40700819841603803000c1a8040c139036404a1001d90051302440c00e10450009001a8140392103107a20100e003040030119481d50002c03084c0028254035115030000c0041d001006a1112001514064003003895801c200400981c90408054111020f110301603d420100c8240840100e581c412001c80d0565000714000c00d40c0c401600b01000208000c1c4408000c030b6005e480002d440e4440c1c0c1c080100300d91400308400030782511a500c00d20000003402880400481d803c540f20300150000c0f560188210300b452400708105c1005001e549207020081e08454030701c0c01c41c0d800c120192000805141c114810074181d195206001d003d8004200c0c010005041751908240c00d01584030314401201081c404108120000076100050100c100c4004040c03e0016440306040c180c02c15103070f060090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 146079415 1250 146078165 146078167
    0x3121e090304050a090b0916050f03010f05090f0f0c2a010e0706050c0a0f02031203130b06040b0105090904020f0d05060108060601090608240406090504110f0d0201050d020c0102 78
    0x30461110000080083d00c208490812085039640b1840c030540c2c078188010781e00700703c0042c00f096604269000c4a0748000b81400c01c40c1c2002851449400150401d0b40510144081448100414100128400d0700071440e1000c01c0d601c0e02c1d082140038468039018102664001c40010f05104481803242d00e40a40c0d27010034021304074214803104080c0a002000e500c0c2050307000d480e1000070880d001e8421203210071102d6006d0075114489840360144200d01040c01c2c4c0c1c15000c0d54401800d05d1003004010351040c40440541030303211f415404c20886580c4010302042c0100d03d044900802c41c1c2c1c0000a44034000000c450464140d03943d4404030714000030144405400c284813040c6038080000119007541614005400c07030748075a075a032004441d803240038450f10000c20b500f440403c80c840c150011140100075171402d148021324074140800c0880307003c0e80c4111400c59075201031008005e0f038450041480101200c1008281c103d11000414107540780d40002e0500c480060041c0e80844160191140202003a00031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 146080665 1250 146079415 146079421
    0x2060d24061812020a0b071b0e1501051b01060b0703020706020105060607111201020d060504200a0f020309061201090506010c05031903140405010c0f021f0207061b0f0e030304050303121e 82
    0x288190a5901b0aa0300643e43c04142c00324440d030003c801e27244207462040c1e01980794616240103448950001c444210106180d0b0032249480c2070134020040240700c01d442c607550380c10041c2002410001250001c00c116414201484840ea5605041e5404150080c80344091804000000707501d404404440d08943c1d40081182e81c2051480d5016004607032090720248020450740c851900301a1000e60160003501e01030040700301191049000707540c03101d00c60044901e0401014009069900000c0040802045140043c042007000b409080e03001002801c20780701c0102c0503030300d450700c9000d403026440c14840d0f2111417001251007070700302168510034003514007864206814280d010300707601240d41c00812101000d084103c9d100041c0324810012580705200584244d414900195214000580e040da84410a140c415540c4100e086501d01554a41c2e00201850b0b140241200f100400664482c0d0000d12040026880120071034016801c02a106040f40d503c2030485460900c54213140c4007180134034020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 146081915 1250 146080665 146080673
    0x14030a050604151401030b0a0207030207030f05010911190302010e0102070e0f0109050f041109100b1209011a030a12031107030e01170402030a030c02060d24061812020a0b07 76
    0x18a40a440c05400e09020740842013030031071018002840001c081e550a06c0018203448810b5010380f1420344284107998400c0d41e01d4850b55025441c945c0251f500340d546612090402c00c040300c1c0c900242c04213540d1002031032a102d80e22001a07029104c003130b041c080c1c09600301070f00780c0c0700340140c0c40a481c0c0440941080e0408003400c500003a070900911400d203103000049400c004d0140c041c135100ea584400340d4240e50716404203104d1200f101904001039101c43d101d011807280c10450290000c4031280c80182c61030f1030b00c4c504150075140141c050901d503401907070980d2156240495081c0c0802e4110702c6004800d0035850040b001841460812220030801050035000c1650080d51148443c00990311646881d000c0c0603413105207141924000d50660054940074002402094001d401c00c1c001415a801d01c0808200da000782c980f80c0b00103680d2684110b0320f02c00d162124480450140106d8504241100400b2040480740200b80c0100718107003040c65191000c541d41c810104000e01500c062a0f900c9400c1850 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 146083165 1250 146081915 146081933
    0xb130207060c05090a030f0302010902090a0203040204050c03090703030e030304050a080a051011030a0f090c060306050321030c0715060306060e09011505010518030714030f0601050a14030a050604 86
    0x200319a00ca080050502ca8140328030295103040c00010910807549181d0754820740c100703040c01c2040f0250b5488409884c0582d844c501d02501c20001e82ca0050b90303d24040c030401c03080740d10041c0440c200d00400d005000329a080080c40000f40ca505080840d14040850000381c034502465000a5202d08518800304503150041074840702a0b00c81d4003100c00803030a00380a0010340301c4400e15110f8483c001d10014190460300e41000e1019920188009400e850382e484c2c4802d103d0f1141c021002090300c1d00010042420200400300580220b5107000300000c0c91032840001520001d4496075940201245000c14404610703c1440c0050f4464030401c003590303480c64600003401c614030807034040c11405400a84d01c0901030240f40b2808882182e0818160305010056a064001459142c02102040303111541ca450070007074100909029a0307181e10b481444401c01d460403648404142c03154001c6401000340352a550305450a650440304903020301e030681c6001c24540a070302d400151682c8180c00c00d20050110141e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 146084415 1250 146083165 146083177
    0xb0705011e0c0e01080a091a180303040515040510020301030605060a0503010209151c061404240510050f0a0c050706030b060d09080715020a030f0b060307030c02010b1302 75
    0xc49031506080c0046007108607600800b46202240c1100d031044250342c442c00e1343d0b65002c40c9a0000040700c00164403102c1c6c00390854588440c00c00b40b1042400308200c0c1105081a0000c3e02030000e524626280d510740362148421b414803e42d061020001c182005424000c8a03228031080f20300b15100d40c1d5a08000c00900340554070540140000130b0301041a04040c001c8030f65518016200780c44814a000707012100750301c07020301200200c2c60303240c0b4800c42c600240140d000411004a811050b10810b80811044805100c148000814030f116184000a51240010101c480c12144901a84000c2c030042d25644110f1001000c00303040044d150b01c0042d040000d40e00d01c98056400c486019031189415812203a08801d4158850420b0020103114125500140c42251049002c1824810b4036590070107403a1080c0500084e5035004500b106129605104070300c01205000b10501032444100c0c045175640c80040e05280c201502d4254980780c850007500308550404000c1e08983c410461912950003d400c81 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 146085665 1250 146084415 146084441
    0x1404050618070503070f0503060306070e0f03120304020f0415090e01092102100c02100e160f06030f060303080402040905071e05041d0d18030c03030309140a03020619060b070501 78
    0x60322406c04028416000c2d03a2160398043c00400d52070311004015038071402d055806940c04910b04110b90b0242d20300b44508802044080d641540320701341813040041226950b858680160300d800d05480c00f01d224aa4508201c4a5419000a10000051039140904143c0f03101400c4109910300d0041c015082d0111b05181441c150300350344950302e032082d10000342c420180c0c0400040e800b441c1c4401d11200d2550001d03181d031039404200c03240c050607600031018013011540328103280e03801007004121725505400ba40000c01c0b803d801c200092030a55a0190144030f01810217030081c1c0c3e90b203424104100341004510044c1c088800080800f0581d40a141c80404031409054021428002ca0b401d4040780740c0c45400954032001d000d0320041070178a404a0303042082407011440c403441d80f40d002000c61034a20303010001d540130b643e0118ad40c00207420840209400e440d0490a81c0d4400d00c944001700341d01107089a00180c0e82503040c914202800300c0d641c0a0a02d0342c01c840e0095000050960401c02c0542c0a4000039640c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 146086915 1250 146085665 146085677
    0x706020f0414010f0c0c060e0111120a080a06031a071b151d0601030803100306020406050711091b03060409050f061519030204020748140405061807050307 68
    0x1401348211070a8620501c01000881e0312842807200c0d0740551280c0c0081c40042c0740200c41e002d0044081c91034485116984116518001030011895502141c01503112103025003c2c42601d10f15a100076400e403110000d81c40c11000b03400405d500521a01d4001c0d400e003507249282c040b042d00b500b0b055091002600b402c0c0841407401100d03c030302d84901c0408180035041c0308041c0c28160301c0d60701c844615030f100610741040300b1103504010000881c20300c0540064443e40c4d0760030b52294040d2500c1007444040040c154070810700074003085007030254440410464941c0605240d01d80c1c075204003241c05400070407401020303401140d000b12894900003902c681b2424400151241d95103042040c05045c041401d0f800210300300c07212061003d400c20b5001004c2c141c0c4242c114209800c42c0b04604990050b0070102203100d10310781d42d01c00307111401c5080f0b82d1985184410401c8961403a2295410441d082e902c08240240c1d11000007514179900d140d004968403030300042e01455407920b40001885d55104560400214103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 146088165 1250 146086915 146086937
    0xc010801090b0303070602070807020d0c150c120c03050c150a2f091804030e012007031509060915110702060d05040f05030a020307110409050d050706020f041401 71
    0x5950058140002c80600998034003c442c0d103a84001c0e521805003070380e0b054030422038980140c9440d421501658010304c500c2d491a4249000c800c0302c1d44d02000c900c81080214013015000c2040d61b00d00c06030710906030400c0a00074486180507640360150301240101c602a40e0400c545007031341c6850307081c41000a00030030030003203146000c040c180d260b14100c0000b04421649a01c01c034101a0f20050404441c002c14400d1120b01096211060395400c880071400540303426100c403055608464496440c1c815449a0407650448294841e03580c1203a21000d040c480c00c40b0146400984141c0c4226641a00070307030706106094031420700c285145400e100080c2c680c0e10f800404c1c3c0c0e00b40c0d4a00280c0d1010381d4001c098030300e4103070252041005032201400c00d6890344045005500022801c00c010200860940c025549559003410032000214200d0b1074140030b5410328544500040b404240c0007007000307080c1000d607150742d09400c00c080240656400341056240010307000c0341640488820075509202681c034000a0380c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 146089415 1250 146088165 146088179
    0x17210901080a0606020a0308041a10060305060904030206060f060f0c0309030f03071106070602090307061e020f0303010902030712090606030204050604140402060c1f0501030303060b120403030c110f0c010801 91
    0x24103103114031401a0806d00e00e940010344114a10383d04070740102116105400142c000f00c6900d0b00540e6442c0310312090b54010400e07590180a4a64400000c4071040754521341030b00e0280d00c0351b000a0195203d0104a04030150316610103058512180c0b102200366111505401c0169030ba600420000384644540c59510b00c40030030000844040552109091022604100902c80c0540222601303c640a0b000d00201c0c0d125103040021034010030701340d914010700032003251941640c83c00c242213420442d00844000884103100208880c1101c2030700d00010ba690343d40c2e41c41165032803881d9000b40f450909018102e020f1200581080c01a68002c48042000d0f0725601d0410045608480d2040c0c900b11a500c00280540342180c042d1803220342d074105955209600a4402280392000000805d44544e18001401415450701c650300c003500a521101e4604690403580d1000d5481c0100000c0c205611044100344c0c051088142964583d10f540c100d901c1c04201c04416a214101e0281c03040c0001c4110000080309 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 146090665 1250 146089415 146089421
    0x112050601080d02030a030506060403080309010501050406090608030f09011e050408010606030606020a12020f010f061a03040f060b0103150909050105150105041a090d12110309090117210901080a 86
    0x140603900103500c2c06c001c1c15800d4010b05001000d45920180138040080803d665070001d43c0300d04031042c00040c881d81020200803c590450700003200e440c1c0381c0305041c090310b0030003c21100c0c00950946400d840e5141c0da00120741d1603000c82c1d8000418003518002c03808017500b000203041540c03600802840300c280c60b08022411100984921801644030815190115011030340b043d07880e202c0703032050759001402001c6036820b607520050700441c0c0d0345d0f823040d00b004440e540d03c1c1500320084005160f00d1035401c0ca81c450010509004034040c004969075030030103119038026408030340341c2c60000c0302038050180e503190454024150742009a9255003800006000300040c2182d002c841c15051311100c3c200707410b244c4c0d4040000007601c841c4090003001c01c40e03042507507070f0324540b400c40c80e02c00e5031002003019820500820f51030300564000b040b68070070300c105a4180e0314005401d055078043c10181075054400302020f0f00c3c04c3c0c1384500313036165050240021200c1c245648001c24040300280c80e4240182c640d03400490031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 146091915 1250 146090665 146090683
    0x8060d03080106050c28200105040501050309030c070603050412090e1902040e0408040617040803010314010b0d150e07050d1704170a02130e1e0102070b011205060108 73
    0x1e28400040c03040074040c50207428090300050480f59140800801141c1c007505040d65240d40b1406045140c00300003080d8244084c144a5070362401242e0001800a011401107018150500401100248803100d0400656000d240344c03d0844460300e6a4510240081c4029102034905000705203440c1407260199189100f20f420044814000369a40d20700000200c03424424282e80c3c6400b0000004c0c50008840507601650085c285155528a0100c0191102d03007d210b1552098407580101300c040780c00c02c0c06890469410118020405004604287c010988440d600743d010110050480c00d10901641c90300c00450b0740b078000c0040e402c1401036aa5200c81e144100d80d8400110051304001940c176410103a8a1101e100a25040c151130340184003a041300d503680004d169101558407410f6103800a116150410f00150400c640241440c0103611912420340d00d202c00b040c54203035011801d00c00d504031102d50b070304000b902650b540c40708802c24107403d022500ba9524861040086640303040860030340300c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 146093165 1250 146091915 146091917
    0x1218130506090a0e03041a0904060807120204020715090f120509090414211305100c1101091d090f150a0c050403020907030209011404080709051003020d080a08060d03 73
    0xd1a5561403d1400a4004281c0340c032075900061000091244185020310030280804484a03182c00a0034140400c56100b944140c42c6076105110811041488a01419074540c041d2000359950f001400c0c451482031890a01c16070303692a000d078241c2401012440c003445a48a00c40300c101100300070804469a00560038031b16801010b40001c100001c03032130001c0e403c034080000e05444042c442d5400c50040e08180c0a0b00d42c061900000e00180000390103c10400501400c50300412900f1308000001c0c1000b240000060030b0400201003214503a010300c0025000308030b000e060600700740d41180304204a2400b503441c10500d11410f6048040c003007001c80c1c3e004450380b0901001507161381e08405c040181008130500403c0c000c0801010000d42c2701d46850f584205034a84000d41e0b43d824820005010f131042c1004c040f024141400300303005644020030700908403444d80501180c0b54072485190a4040140c0e0301c029030000e48481d4040400005201900707031146aa04e0340892a501e03801446208600420700030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 146094415 1250 146093165 146093179
    0xb01030e0705011b050d020307140a15152403050c03072a0204050a0603051605010f1110020703020f250e360705060c1009051218130506 60
    0x10025503c604800c41c2001c82072130107401c0240c1c2540b00c640c00d100f4082554001a01f0020f030302000d00c81d11070380e0916101d041c5001007408121a4035801000c20b40b1074003042c401c40d124030415400040c442c1e0450702400c42e0322140c01055010700160a140d0f81c580204001183c2000d001075000d10149082c4c82c803415840e00d40668140604030f000303414598090300420f40312000741c490805601c079031180341c1c0714102d0035200060280c1903040144c98680749130403010070410f000000380540e903409a0b030301d0784032443c03030800e540e140080740d00907800c02d040001c195001c24808250070090680c001004441c00c00b8140660781101040d003012203820074003500e1810043c032080b00130401020210912540715046a014000072080c85503210141c080001e07036040805c500e03804110712400c040c0075810040008036900c518101d0100c0c059901c43c5000040b03409007030303541c500c000b003484004c2c41260030444591004968903202009603101481020080313074010002540800c49040c1c0714451240143c034000c040c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 146095665 1250 146094415 146094419
    0x1b0d0303020c030f04091a0418020103020d0e0f030a080f04050d0f032403060b0607110405070e0a08070807060c1a150301020f07060c0f17041b060804060b01030e07 72
    0xa4000e035002c03149519107880100004040c10301c0c1040030700058111103401164807416103030620341c4040d410072460702c0345150140076000e00e200d0001c99400700c0c0e428240543c88a0458007a1402414141e00e8240e0301c0c003820807041e02a10340840100055050f40c0c4540c1c000e9150500901210107040704c00800960180c030307100c4002030094403414400080c034a0007007980320690076021080700360a030700e4881d140300400d000d0041211074001c0c058085400d80c0d00600384042c5845482c0d00382d4001c440207002e1f59840d80401e030ba891244254510141e400381420131581e42d00e0701116a02c0d10306118052550107004c1012580511416003580b000f500141e00d050742c0c000c1055451780d1060044c103038a8010f040204c061030b464400780090508071440071005501c828090400d1410303900d08030104803c0215000303101c0b003042d40201b200f180701400c881203130000d55214541000381401045042d84c6c0b91031484000100c80f0b6000185520a600c079903800d0080c85035420040d0182c030141010802c081e0096001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 146096915 1250 146095665 146095667
    0x207030b1506190305010b13091a0411070506060904030c0809040f0c0c0512162a1202180403090b07060b0406080c010809030a0807110309090f091b0d03 67
    0x5816044110406031848819a820000302d00e41e110328030801c00161001c511041c00e9816219482c010084088180d26110b8642100795098100340a40c3c06255910000f03030303103001030700702e41c0c0d103007041380a44100701d000514141002c09401c01d0100325494401c50000400038203209010a000300e034151a060b00d101c90030b41c0c401e0303466080100b140b60416652025001150030900650040c04c01a44070480c8200c11818507a08010440079244100c0401304107190011154280310328074660004124007003c41c000d4480e5960f10002d13490002030400c6500d0100703120f840300d9030340c0384118801c861708483e0f10f80c201c120780c83d62103084902801003200d199080003800042c00c000c1810b18452a80042c480a604000034100c40c129041841c3d950700050000019507040b18907107810800c0f2500440c1070080a080c001d04001c402000da004110340c4240c003105180e4200241c804008000301000c156240200c0050708081c03044071a1001445143e0265540c00f8050420044e500c0b8040c02d0010701d20703400e0310 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 146098165 1250 146096915 146096933
    0x18050402100908150a1e0501060f08010311360106030506010c02010e090c09040608010606110f030910090503030a0201090302010c030e1c020a17030406061d040b04020a080318040c0f020703 83
    0x1111070382894460542c1008500c04400b24490040d0f01c0d540014123504104008164005000c50300007402002001480413400c40508441c1040d4101d41121703058806101c0344210440075000b040031110a000400d0380c1130300021300d41781640c0142da010091952044011a443c0129002c00f0f40803c604a01140c103e003040481382c2e074021781d690105c92a10b07132080007180440e540c0da44201c400e17956070031080c00219400340020103103445090003803080c42d9540311410b46900c00c08010700d02c1506082500e41c000e41c01400030500410b40101a02d84840d00c00c01e029010f030005110403001540b13060300b034600950003440342c080c0245013840105501d41c9008040500248410792200552044503031400c0040d42481e100700050702e5105883da240d050500e040303001c0e82d031a50410b00032407400841d44a00029a11a01c1e070f4800d0b00030080108544450000c104000145d4000c00401c0c0000541110498041d620307070450b0f404169010000c0341c85040c82240c040c49110805c0006800c03c0f4402c002081e0084c0e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 146099415 1250 146098165 146098171
    0x50d080f0f0c0910030f0c020705180a09020607060903080105120304090f02070b0709140406030803060402031b0301140a050405090307020d0309090c090501020f060708060d06061805040210090815 86
    0xc00c002e183c840d0a400107208800c04144d03e0002a03221410724402d9100b0340900c2e020b11707419000800e0070b641400001621441d9100307100d40718001420024007100072541003001d603140c000d46010342e207581030300313000c0042d0295030415408a0b80d51000060103081100812004140003000756003041e007440e00c0340f03015090142352401c0036134003405003501203100760301d00a0161500d078881d940900e1500d502100b1189600d401c0c94810787c0340c000b040000c00c0902017282c8d44102c0071500142e80380e4035014804041c18070200c45030922500440003090010f02901c20001c0204102c59a45019070b1318010030041e07503000c884540058205001c1f250041c00d1800b00380c10594401e080071014151624000000c5828030b43e0382e500007070316140082180b0350701400040002103c09003c1c040515111201030101803010344290f01411201140c8014451541e10480140441d15032083c2400310151485025200680307050340310340114008a06080c0c00381d40210200d52a10001e058200b841c1c1c075017030881000003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 146100665 1250 146099415 146099431
    0x60412030c0b0c0705060114030607030b270702070527040311120a0f0806030d080912030f0103030e0a03050601120f02040c021006080a020d121416050d080f0f 70
    0x1400a40c03001036414401c1c0d80c450125484900d07144e40c101e041103481c01d00c042e403010385600e004015000c0e40780c86c041207490784603295003008a0740c03056020204520340300250340300a94261340d084c20170740300c07010500745401140740350300701d03080030307456004025001c40141640810072854246040000302c061742d00b9076104c1c0c043d05094215120402000741040400c1072461100480021041c00c1d10780c0084000031109894905a0100c1c6450400b296449118910400034840c0480000305c01780010445282412070f490b032104c2c3c403810260007003e4020007e000032004602c0907420744110703082c2005400101da400c41c000305281c0e460280e80b00945511140d042da03900c1000c28200025840d6030050401e180300c9170b07004001a12007042d9140c1244c002d80c1003c402e0380c000364524070150b9250881410190340054480415000b24002500c05420f04079103034040c503c011800500c40740380e584103144154040c1c81a030350310344102c1f4400c07501824110b4502000f40903005c0800c2122500d50000f5501c4804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 146101915 1250 146100665 146100677
    0x60212090102031c4a190602090303041202030c03010203070f050a1704080711090601020a110a0807182007060c03060306110c01060503030304020108061215100602011a06041203 78
    0x4006401d4101e41e05000c0141000d100c1e0010850030311708032a10003071005260701c0c496500c140c1384032401e41c8500365003100020340a50041060180542ca03030407920401001000c4a0360345684082600389610a0b9405078428007910004441a09040c004c4078807c08291307490b54130b00b450903141660b9680008840400b040340082898046c002c4040c00217000c0d60003a80403070348a03012480c02c048401e005c20f11903030282c3e80040c1840505e9800040442030642e210b110b0144403035980b070204082400c01d0741300f2032a501c02c5110000d60006501c071601d0400c44800014056520150605100c1400046c4130181540040092401041d190340c40411801e07418680450665602e8440005640c540c40760b90351114400a40301075504024030480300189402e502560079840c242d000a485134200518081c0a00c1c0381d40450303c44070b2818800c040100c0802c031004107144c02c002c03800400c00e4181d4041c81016601c0c0c100b00c14115020306c1c1c01e103d1003110050a44e4542801d01840030241000d4100c210140a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 146103165 1250 146101915 146101931
    0xd0f030203091005120703060317160f0b010305060a06050f0105030603030d0507020f01060801091106090d06020a030203070e090412110c040218090106050a390c060212090102031c 79
    0x510800c10f12a03640c507a94030161216406520110105c0002e07042c0000d05151500401c0020f02c11f01405e40030540c04117180d5141c25090180088102c1d00c424024900d414402c0b40d041082031591466050300d000b041103a045564003040c410488500713000703c5910004d02c45600f41307158410001035510450140589041c64050b500200a0302c409580e800090781010303408001d180b0091150320f0041401c94002d02841000b620780c0c20300c1216100300796004000c00168103895454004004c0c461641c8174804560342d40c60040700400a40054070030b6000523061013071424844c548400440e011b15041405071510842d0181d050340c07000c1312101440024042c100c43e034200c0d565984050711620444041c5128290392903c10400c4620050b0004024800203100c1070f8503407130f400f801c2e440b04140b644001464803241c81c4d2007005030761850640800c1d4242d11016000400c16000a48011210940c0855580b0a86241c40880c10300a10080302d006031700c242700311480c07160706e462081d11a000b96400011515 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 146104415 1250 146103165 146103169
    0xb1305090c09131803172a070204090f0602071a010501170619080a060609110a030207110d030e0a0e0c0d240803071101021b04020717031503060105030a020d0f03020309 74
    0x1402210003176002c02c41010300f030030f841d109004001e60b0000241401c0603610005901c5580612440ca02600c0c24650109100c0c085454552205400f643c115105440040c4240f030540c0c080d600041044541c2204001c410703145050019055050b40c40586402840118411107004200c10081040741c1c000b2038001407200491140180c0c5c40074149840260a0b810000e0070070005441c0c0b107502c601c0c4001c4c6880c4c01390150b40c4001041d9151400c8520300035a440d0218140046c80740c0007003a11a41c4003000c2c000e00000c04d50844210000294240c0703501c410140e2f648003011010000b2141c030a003c0e4403c02810003408a1075011034141600c04400c4d010a5640003103041206d4143d030004c48042d80000344134418000c07550b85140f502e260920042c60320b007441d0643d1800d400f0100c08064000e5030081050410440c64690902000780c1c00f01c0c00700d48030f10301509240450050b010180c0d00074040e2000101d5181070115061503419009001c1119264196907425190b000d682c2c026011400240854011a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 146105665 1250 146104415 146104451
    0xf090c0c120518190911120106081317070203010b04050108030f1606020307080612010e07090509011b02070f0806010509180708120306120d20030409060b1305090c0913 74
    0xb448100d51340025410070103c9000c9504c1031400c413000d51010300c8100e011440720914541540c04925111a82e9104c01041501c5107214507002010519000c4a0985503a008409000c106000301c000380718a90308801400201c44081c01076140c1c60300308000f80c4600c7e4017040006c066620760302001c1000c0c002e80751601d204070f070030903150f000c000b90a00c03040c41034518102140844024902000b082040b04803200a5550003e512514807002c0e10b40e00004d100c42c2c02075103d0001848807184625103010301c0e0000075110a1640150981044041d40c040b5004d98001011410f9500151902c0340303d854141100e104c9110301400c0b01d502d4440d1403404182101c0070b111006030b040b19400040d869040c041c08001403075194620b03c05a5a20000c030541c0050741c48000c091005005107406800341c401c2403031090131403251f40c00810010341003207400241c11650360f00500303050310f11130741040e181c40e20f5504000c0207035416516003103040028481d41015280110012003c84d24115000a0488506040d0405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 146106915 1250 146105665 146105689
    0x1c0b01270b1b10060303030506060f030430020a02040f110904020906040f061d09041e02041107030930120207090509010e0c040b0a0303081e010f090c0c120518 70
    0x350b921384c9400c00c00c00d42c060040b07941081081350340c03500380b00b0540c0040e5000c1c08010405024101d5608045004104801407150702d0241d91b00d00840044000001a5179145041d404901075454291000881d594034805d18080740000e442c203c0c60034180038100300181d00000381d0703594080c0c0200400a208000d0b80308900c001e22603912004805c541d240c4041071100f0301c103020b13103000d400d500041000003070b00e00b00c014041400c09980014000120300104000301151400c001401030b000607814140340d00700150038112050f1135000400390030009070903002d4a2004100300010b07804043c9580020340c0220144072040514812206140d56402d102c1042c3c460960300c09030707180d55801d807083c4040d005201302c49513900c0c01d440034482c401e00600459100c070a14030001c0d0401180d0000f29960344414500b00700304030075210310360a0315615400c4a66214000303210388180b41e8139240003020800d000f030426510741500201034284810451400b543d540c0e1040342c0030312003142212004081a52042100e0071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 146108165 1250 146106915 146106943
    0xb030f090d050f070b04060b130b130902031908090a030f021311160201020c03030712080117030301060806030102071506080118050705151c0b01270b1b 67
    0x8210304020100314100841490050304200042040a0301d1251003030486003200d600403032409013a81c40f800e1203801481d00c2c4601d607600141600d4440b5404426800811241c41b00300c03401080451004104c1003280c5020708001d42541001c00744440400e56411100d560b5402500c41518045070100007401c0204030340c1044030718105014111003981060703000c1c05100840e6800801007078005d54030300000f078091020342602d21042003c0e42011a4070910542c031510344042d040300d231502206c3c036091000c03102e1030100c500051030007800051f999080300c0c081a000344880002c0c5145908005c000c503180d00c801060703990150340820076400041d08510940b8040440034078001941802c0402090030f5600b0b04411004001156400501180b0081040022108116450b00246141c0d0352240405d00404501498100c1c0d000b220110059064010070941c440903690b0210740801c01c6401035501070f403c2c1420740d0b01054540306100107140c05005100810380c068890318400401404246441c000c003950b40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 146109415 1250 146108165 146108191
    0x9010930031b030c0c0b030601020705060f0f03010b03010914040b0606070c0503030705060a0f0903173303010c080708130507050613090e0109030203031b0f0f031e060f060706060b03 80
    0x180710010b8806006046d8440c0440d1440c144440003d41e61245800b44070300c00c05000030041d036005818801c07a41c449124144407501c941e503a008140b0260824071901c00c070a400c01e40190002462000360621490744140c4030005a25441c0c280701658200c01c0d0100d945140c5542e0104076560108058900c0c540304000904481c81c02e001e0180c1503e00034108194804e08000031000025001011081c03115081141c04625980b1aa0045400c0c000c00c1d00ca41e10000f00030058001903c4150001b98500030240c009001287c60350508803000c0008642850005490201044060b122100038881c840d000d030003164503298582c0002800380e400701d14201c3c103116503010b0821a50307000f1300500c00d1400351140200443c0040d620701a48031704c0020159012280001e800ca083c0b600ea882c192070003014640811034071011840c0310048198030996180c58440120104080305099440f1400d10900c030180002000f400000140b1411348c2144000304da441d522030002107500307243c4002540c880c1641c00880 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 146110665 1250 146109415 146109437
    0x21204030201060824041106030405032830020c0a0b0603070605071704080a06051e04080405041a0405070206040308100803030105010e0303070b090309010930031b03 73
    0x42e00f1541298000c4a06030042c0300e580418000c0d05500080c8900480c0b4002c0250307440b480c261254030800d000700da5004001100344424490004050700d8180c504076015038207144e00380c84840c01100e030340b05810f0009103100042e034450b40041481e10022106503c3c24170280200d136440000f641c0000440c2030103540816070079410b200c840c420f12600801c040c2c0280c01500c1c109803009003607205207040507090b100c071104001c80b402000e00840c1c0c01440004181d50550380642350440c003500050303482034041c12440f804072f059110103a0700240a039522a844c50b00d02460030b814400604600c007000254000081901c0d1000e46035405080d02c00c0782c00303602a205038603003890042c0040c0c4d00a0300c0c0e1f100d4140d240b901804044000003c690540d03500b42080301010f45504000b074a1446400bc000b044c1e0800e000070b000400400001421295409032103100300c26480c0c030820051042000c414400c5e4070000d02c065003c840c00c00040c1e0509034064640520764810b4101c4050b0136414003402180001c6080080d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 146111915 1250 146110665 146110667
    0x60b040b0607050318180106080403090519030204050703090f0c050a0b03090a031d270601050c03120403030b03030307091401080925180209030106051212090a0902120403 75
    0x5036002500d02203640310300784840b544809075203000d5143c0c08015a100001d2250380b943d41c00c42000b00c20845011440120341c0c44280c001e00e2140d0554084000c51140c2401168902d4604c24020700d4001c00a0705003041c40c91a002c000249c50007400030000d040c0d0310000c9030049030600382058003a42c0202964209186024141f104413880796000c11004403085c000d000000f100803412250064051610f00020149a003045030345002e035004150340704260303c01c801c111002c2e40043c101c0f40644036542950950340d0a0040d034079071055005454464004101641c04e586601c0c0380150040d0203446c00003198001000868559881694010301150349010104050b0400c5960400700d51005e03e080002c0b402e01d41c807241d546001c4071007401c2c40c40200200c0e0310b503280300324480c4100a0504d024065005805075201400030360011080c203000b0b5007000c002203100d00703005580d940f400404400410309041000103064071f6400003d041540310110380c3c00000c041e0301500280c6000344100e400d43e03500e81080d01e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 146113165 1250 146111915 146111921
    0xd02040b09090702280303021b010e060c0a0c060509190b01150302040302060304030804020d0c060c0b0f0c0316090807030309050f03011b030f0b0904080c070b03090d030207060e0a060b04 82
    0x1c05021035010056183c03417007603401d980a01503a440001d2920344941841c0513000b0340030b1040c60040001070304e0a0f10701104c80541060102130071880c1540e100d512151000455403040b00c0c0300e03401060202081500244083d44143d90220f03000007518008070703100414140313070440d0321130981c6c40c003da6000522280f17900c842a5000d080043c03c0451800b441c541c00701d50180070040c0090f003801240f80000b415901c4203186000f14503030003800074040c1c1380c4444003d8071509103010155145040c4400040380c400b1116000307800345280f45462401c1d0781d034540b83c0107031700c1c000c584101e804c201c86040000f41c1200308000702005188240c990510031414501441b5000d004400c4280c800c0e810400115240b00801441450030203080c0f80201340d0200801144014015030101d054118409400304407d000344040940343e60000350007030b00c14807540d034800054640001d44082c0c2e499000342102c100220300035802080b660b441150f01240c242210751511f420a80345d00d0099a001e07848410700c400d607103003500c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 146114415 1250 146113165 146113171
    0x6030717070503130f02011209060509010c0507020d061d060907180209010f0509010c150903020c0307031703280b010e060a021522080705070f0b070210050d02040b0909 74
    0x2141050461800040342e135101100d21401800c21030000200310b00b5a4032135942d040d061038907003c01740100c1c04c071441c05500401c030454280300039510f0160b00031340241c1300e401120000c1d90020031400841126449510040505200d50290308440c2e207110141c424050042521030500e0001400c0325034035009180340085030710468490b1080c0b04100d060107aa8100b128880b804155282607a1580042070042e282440b0001002d00208610074408100324003039000300020511035426078184480c83d2007816510001c9000c01401240341c40350800160410380c0c05507610208412224800750540b81a501c10703c00c070b80c02003202e50340d10380c452010f407942c021012444204c0c00f0f0740e28901d0100e242d000252521150038109465141d0360000c00c0c00c030212004940384402410140000141051500401c25440800300702c8044c015000d0002c0d00c2d4084c0b9100710201d030740e02006286050715540c01c001300c800f145240a4184401844102016034903440030704083d10319001c0c031580d11031801c1d04100c81180c0007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 146115665 1250 146114415 146114417
    0x302030702012a060e120403050318040b09070e0607080a0f0207150e010e03030702041404140604170a110715080a052205030708030f40020409020603071707 69
    0x116010192020f0081645103e590821070000d0101c0b400064a800d00c40000785422042d2400310b404030900c08044004c0ca00b010280e0000c0000307144517414030080c0c4d00703034600310344c0e021102e08000380559020303213451520100018401751904002c0c1d981e070002a04429100d000090102003640807680c1c0411641c005091401000c144a110031032000b000204410b00e00c3e8104111602418043e8504109407021540d004000b844000c6085044840c01030f030488042d5901c5851003105080e104010030110b0160360812150001d0344031218651005612284030310781000a1260301300702c00d0b003044c0078100103450500034000301e10700060740052100001403c9d0400d070f24078040510060b10241e4070642626468201e08040c1d540460a0050442c05000c20180009600008102d140a8144c400620540d28030f0110040e50070314003003650080d0244851340c1039000811490601d80c81c281c1081d211030500c0200b020944200799070100d8651740003a205500402c42c42100c0350b03c07203104822402d521500f5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 146116915 1250 146115665 146115707
    0xd24020c0105180c040b06041d0702100c050a0507021f020705041401050a05010e060c070803091201050f190b030a0b07080f040807080d14190b040603080d020f0412030203070201 78
    0x450762809441300036554003280700b140c1d00d040c2c0420729100e103401d40c0e00501c40720190501421030804030401c600403c6910b9030060003015515210a202440740301014101580e5450401b10610415078030369004a1082e80e0101000100e02e07440d070080c009200840e545a03000c0d040300c1d8039090510050744c1405110000c6600308400500650300d9101a104c1101e20034605407100402c4200401d8561090842a840c2070103070017000301341d11b84008020301c1d00307010640c1c3c14409200394001c55422100142c501604000c45134000c501d01c201c504003c2150440c0b040c8000802c80049800686000c4000703000302c400549110410014907006501240c0c0308181710045401454156100e24484c413506400909600000c51a507091901725400440340c40b100c82d240c65a0360502448054a1251040e0320281c52420002c8269060405004040c101c82e0b0081c0c04508000b8200410006500440c04a007800602070000240b08806210240c42a5000b81c000c1e55a0364194000100540d42c003401503104011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 146118165 1250 146116915 146116951
    0x6072a23040b010309050303040b010e060604081b010e0d0303090c050a08061305011b12060902130b09031903110606042313050607050d1503110d24020c0105 69
    0x2446120041030040d00700c40000301c2c801041e005130000e040a2501078140c1c4808000c2001304000c00b00054180c81c44501400982d596900c1042000e02c00c0303000310125904600806682c2c400f030340e90401440c6070141008608503200201040302005440803d80c0003d407502034040901c62031111403005400107035030844105003040d41c22076680300c1c05802403050081c0d00c04483c0900c81c0039405814040360540101000e00042d420041c680076080300070b10f0001c1d1504100084100d581c6c03003107a0646072144600140c45107099499001600010103030384d05809400c41d6240b0312b05000b002d07900740b10710070384503850301c14400d15916103050f500605050103540341106171500c50300e940c0181c0c901410184160517455498503c00d601c1092220300081c00352140d101400600742c4c01a015013000341614800f044034051490f56082110183c0c400604240690605070415040640e8030891090084103546001c1d00c501c0445400c001554001003001c0394042065a0262005e0290a801500c0005541d66840f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 146119415 1250 146118165 146118209
    0x10c02071703190507060905070b09010f032f130906030309080703020105030402121606050c15041110110f0102040302040e0c091504090f060204080105060a060c1106072a 75
    0x300380074802030003004294902044800e412007d40345034001c00f40c03000b059541c4501c0c0c2103074000b111111301203448210f02d02000c5101e0300c209148860f0501d5201850807a905c0c0c1e0b030b000b11034803103000385440008110440108440c1450f40d00203200300f03180054591f01c0e500b001000c25195420041e103981140008001607a8030205480c0c0140c1c0407564801c2000c0041440e51502210a0710707040c020b107903000c00060054101c40548410008103042e141c0342200c1f103c09451189084400034140d03004502203610324100268080f49620b070794100280e1040003100214031304001d0031069035090b0b40004041c0b0460030580621011665050018048000d81e003000810801c2c008103605190050607140030460760b40ca400c412800d0703070400180c01d0322011a05040000c0c0d40140200c07402507003000c0c081400742c104204500c0403601c461792180f00071900340c0e0360a45180b4801203400d07400502400b0300c80100c0c80300d01244020031043c0c021070f022041ca03912250541385186d40078171040031400c4034009030f070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 146120665 1250 146119415 146119447
    0x603120f09030305030a11090d050a1403040501080a0b0406081203010312030e06070f0e0a0e0105090705040b030a09291602010209010203040b03090a0c0b030405011406010e0f0d05010c02071703 85
    0x1041b0030f040040380c4055881c08500650150250080d449800f280244040c001e0101c1c07070203400707030081007140d20380801c0204c2c6075568071817441068005000100090b0f2851110342c00158040c000410110702299100d41d41850000c160000400c24240000100100202840c51000c091b00074201802032414600c006615120024809804e02000c298140840f62096110b190300c4d1000405502d0510385815603540740c035a090048500580010380429580b0740146c042e00c0480303050104191441d9910340300500a08261041122200c6c101c9020003c0400205009071400004052000349403030f01099400303082c04901424010369104211688859074080211010b0b02d0070420342594a032115078003c1d01e810a00c1c00090510f001034900801c1102e08040198020380c0034600a01c404440560280030340c400a40d51540440c000c1c00040700e9034104400b05007542940180140304006640e200c0ca400e440c0440409001078200c001c0c1408040c04414548901e8840d0310021810700320b0b0950400b5034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 146121915 1250 146120665 146120671
    0xc0206060a0b0c010e030c010608120708160f0c03031d01030c12020c10021801090f0f270e1e0307170313050d0807090605180108060d02040603120f0903030503 70
    0x2c00a000501140031002c250003988410102c2c104680d039600c0704200d482c0c005c100c54000c4002502403126505071503011602680c0805070041e6465141440820b98001d542889000890749001c1340a4500041107074520a40004e40c02901c410303503601040242505102c0d8800c40f0b050506152903801075a0b02d50060501030110b1f140040180d40d41c00c00401c1d1480d04181060014465000040b51000c0d4400121074098402e42a00d0300d000e401c1d1102120300982c01c03503010f00090704400c01d0040201c850060080e075047c1d00b20082000c80c0c03002d03408840040c2c4e100d45045515076130060310f040039004100c0b009404130150084c040c0d4282046643c03100701c0c00b924441080036084d00480420508900c914003021403961081c1100c0c219100c900340074020302000c40b0840c0c04221241400118580140304680842d1103040d94050b12050620054482d90310251800d03422080243c0d080300161a07a220320000f550050061003003200f803050000308403242c804a202d003000035030001000002d800809480d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 146123165 1250 146121915 146121929
    0xa0c0801050405071b1112030c06060d0303062102030f0708190302010b090910141909050309040609050114040903080411011704061b030605060706020f0408070f090c0206060a 77
    0x2a058036030342c00481e60031000c0c105d400b40b1850100450000c0000d144a904000b130002d9480f80e004503102c24440341c50340601c81c1d41100c01c0e0441c6d03000402d40e14010341508030052107404c00080581d03c13100003000f0401500143c002500201c0c10b210158a000c10a04030201b0300d0100404500c1d0904041d95103443e41c0591600e61503128030b2030710701014000c1d088075141c6000507101080910b46118080c0d0b541e06111885c8401914140b074a003601d11541c0400c500c62050700d41c254081c504c403124000700030484484144c030a80420300c81503201d81e440d40039a200402030400041419418204209600080c00105134130981c03400d000040003e800045c0213034003a4021080d024100c0e84d00b80145c4841c402d5049400345030300700308204020030080390b118038800c510b04d010302410048048815002c4400c14003030981d21110910000000441c0394009101c140e002c0030070a800c0076070314529275203440c407036801622494103000710610401030350348940041d92055200a0504c0c0c1803440226440380b5581c0200d01c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 146124415 1250 146123165 146123171
    0xe0a08011b0e270a1a0603070507110406080109030305010b070b1f030602190f14030c0a02010e070e1902030103020607020d0201020a020907030b0a0603020c0601050d022103070b0a0c08010504 84
    0x100030780d00d06462030740401c0c018403940c01003c1c00440d00a07108904a405848007840c1c504255201c0e07002c0b84d8100400d070700180100d4030315184d08400307481d903820107101111240107a08217020303c4e4030380d401008010461400042076001d298a00a0260351058200301e107401414400703200802c561025064200252500418100c48443c14044a041040e000684618000208201d50448444a031103c80902c1d55078150020ba640340e0864408114000c8002c50a41c24004901030000c1d4400802d10a006800000ba0074001018100c1c1001c0e410381c1b01c0382031040c5000802810710241d540300303280e050780b031441140f96605541c0051880d000d00040a03001e000d40107000c0c801c59000300a04220250000c10f200c41615100100034050300503603502c9801441d458600007031003070080c003e4641d21b19a48001e00000da0800b03091044903c00e911041c0c0e1300014088422802c100c4520442001c20181c00242d580c070885802d10a008602c050508240c242c03038901a8142c207680720b12000c0c1950000c403004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 146125665 1250 146124415 146124437
    0x6090105040306020315040c03230702150906091216030806060d05040f0302010627090804050d030207050a050a0510031e021605102901020703080a0e0a08011b 70
    0x48449008607007000f03201c036100009201110321000c854504104044405010700741071400110181e50225003a10342c0202c001007848a60400e24a5941d40100184102d0340c90450000030104059030a6480b062683c000344144006140c0c10320003541c8009030203c200789070541c00c600d1500a0700305402c0c00b0742000010000b1481650faaa02240c0c41d00740d074010180301508040c10410009088004110007541c83c1040014400e910b0f00b4510b14150500700d41c400e1140758280403140038004514040710300c1d1070204000319280c3c0d5495480301900b4000d07802840d502d4102000d03c00581e01d244c008501c21040d9140800107507a42c545e1002424400c1d19020407c840307140031010034140505145002140046060f000c4422030183c121146400740d422110121441c4010303030708a0b000015950168622140e0010362800e00d000186e07048034041c8101d03503259540342c55510275900454009170000750056081c8525242c0082400c020b0060034008104058050040381c85100756109201e003489486405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 146126915 1250 146125665 146125667
    0x90f030a0807020106050604030510060f050a030b06060904020f0406020f21130512030703020105010b030c0f0f0f04230901080318040b030106091d0a03020622050f0706110615060901 80
    0x1800046c100030741a26141c584a141103a11446e0010b511006589000c000050302068000d00d00d04540c2c0141c00ea0110340c0c00c40e1554128514002e1100b90060405c025020441d240c5100510021380d4038134941c0c0e102c0d410700d03400030300b002c11600780d44103117a102942540a40c6040e6120320842c1c600b29083e107035a0000c50382036030700c2d507281540101d500242700c0c1c0c114030201402000420025209600030030541e80c0301d01d1514046c0c00180c544080b10041403000f140c0781030003d801881c10f81c0d0f403001e10a00b04400d24400151980c8260088441c0c5440c3c492200d01b000150b0020100341d1100701c600340a41d42c14242c2c40c95890159203464410080d100039100c0003074035144e11050b2a440701030b000303111094494820201518040001001000c0000003805141001041c44100227500d64098510303501e48500ca60400490750600c040501d60a111080c00038001700950440703160f044018211071440d02c58003600070840340724110003640084013000390040c250800c440b60340c80c04403074883d107420304040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 146128165 1250 146126915 146126921
    0x503060904111011010c0c0804140303070f20010242040602030603060705040311090c040806070903051c09030206030a020427150303080f150d060b09090f030a08070201 74
    0x3866038024000c00d03403a04030311381c1c40580880480303d80c100030300ca000d003400404c0f034841d034981c100a400100184818403030304072504810109440d00404981c1060300c02e0300d54201d80d030900f210072528030814003080c21180742c04240911499400740003401c603030b03200909001800242e0585c00f65903e42c844582c625107140885510038213a0082c00300340000d103010300d00000290300544000b40300e4803e50000983e00f40c450421101039039400150869500d07014014800340c0d48014041408401041c440032031207200821141c7e20817860396513414901c03865401c19600742607454403950300c80c50480c0c400858458212401504480c0d043e540c2940e01ea45001584c8000d000781c0d0000c5030218240c0b08500b5014440520194801c41c51040400814000e840200d0034001c07035101c01000314280c2c8000815032044c0621880c0e1105503510071245445c1100e00050a4030000ca03400c49003a50380e24014455030411046040c0d102e18280014071104490320065692070040510843c00c000c04c10b03002584041c0300390 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 146129415 1250 146128165 146128193
    0x61805180307030c020a0e040804090e120a05090a05010302031b030402031c021b03010c1e020f060a0606120b010903080c030d060b03010504050906060a09020702040b18190207030503060904 83
    0x34180e075161034080c6401410307015000b40c26032007490a0000030452144030300312036020b0355000055901c0c06281c0360341b010141c07888031812442402400c0003060a24022001401d0a0040f40d445a50340c6a4000c01c020041055404c100d0402d44140104180420321042d9140c0c4480c4e00e00500b0349955407803000a1510301002a00794052060807031090202e500045e110b20f0402c4041403025003801044141801c941220380c4107400103844407205810300c106001801c02d424821b205503420702c2c066003111843c11320255560384c1060b569038010055950300c01c00405072100c0010052000c6050080020041040c1d0700002e4030080c40019481c041c03076030420031a61540f003030381820700c20650b4520b03991a05070005d208071801542020b00140f10301e000803a009202d0440181403a000c541002c0e0200000d40002104a030000d503903484408959032000f942411408100d40c3c00b841501d024400b080441651800004082e4014800307103002982000c00d99611820035901148507a48600348424501070360 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 146130665 1250 146129415 146129461
    0xa030f0204050a08030405010f030507020604110324100f1a090a0801050403020c3d030603080301150318050307031d060c010903030e0c03060610050c0609010f0c03061805 75
    0xd82c030010300120084098003c87d035007601c500291a5200005030203980d42160b8040060300042d00040002c0c40000030010400f001904407125480301545a00c100c0c00f00c02d224040c41c140000c2000041d403000e00461010300b04000c0c0c5598000d20f0900b28001a5982ca0b00f60300302d41e800895911015280c01448030001c03c4800c000303101031f00307103810007944840d44840007034040c02d013142d8006005801c000e0410000c4941206034880103003501c04034080c0b0032b0380204040030141c80e11702c0000450042000356020700b070030100d0f404419404100103400c0310754409090001c85000c40408010445c040301765120300b909420f000c0c84090840c80381d510f1000c02c00d4141071b03000700c0106000342840015880001442d02c2038804020300702c01c40c4034840c0ea9420503402c841e85a488503000900900301601d901c0c0030610300742411418402c071110128141a012541c51083c1c1c1c2d07445028407043c0d544c07030103480380c44106d6003010880c4a0070440950071440141c40104011500c41d000310f0203546c540d18140c0c0d100000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 146131915 1250 146130665 146130679
    0xc0918011104092708030a0e0c041a0a0503010c0801060309021306090b1206090705010c0f0c0b1e04050901050f0d120306050f030c0f0d0311031204050615060a030f020405 75
    0xc0d0f074014002000b4281e542803c40d0344000c8070361400540c100d0070703c1816030001061420b40c0c1d41d44d0448000740c00c005040c0c0d145801440303107060303180e1560301030001c00071101e2428400f0000380600340024a42039500c01440303a810803410f0148550030401090640708140b07400f04100c0b100303001091901d1004030814494a150103400192000907034040d20020000321440c1d0042054450208d41d01d8500b912401019040400104155030051284000c12071040001f031202080c0d503115032007220865806025080d0f00002c41144483e88d1078000351400701c94000c89800c1c40c1c140381c00b1a5230520705000b400d01441d5902000c0c44075035283c040b03801c00c1c0f81c0d100c00c5006800005c401c004003d032a06204807809200903003403040451801190100704581c0c060051200c1440e11410001c400c00c040e0015010720024102000b6044400d00c02880480440b4050360340d0360074140303001d6103016002885500010b00381003250446070340c0c000895020640525000c01e540c610fa0306150028815940141c0e40421 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 146133165 1250 146131915 146131919
    0x708030406110c01020703033c030501182901020102070506151002061e100e1e010801090213020a0e0a030c06030501050312040905190c08010906080c0918011104 71
    0x40d21150302a50700b041e24094451020350b0100690b51001749010080115000708103d4085541e01403480c003101c50b01000204a4402c0c090443d90909080c80c018000240c440005205008040d40385030480303c00c1c03003400c01461100c2c1200407031000341c00c680450348000e01c0c510000142e2003501501c84481e00030056403041e0518840340c00d007900c45140709500074181e140782940c14500204015115140801c103041c2282004170b0b203400c040800030454400400029000300e88401845c03c0c0d54440c45c002ca0b48a03181060042d000584108140c0c00b01d621681003008150042c0c554000190811060100140e122104a01c098500c821510b08cc16006016002d0000034810400018011601c060302c082000741d0300c80c408d05840e03110480c03c1400d00e250802041114102c980c0c130155100c001342001205a90000540034151400207104400082c526001030156078405d215110041000500400719448003002180d0300c042e0081400c0c1501074504141c802d154001c0d0811003a10140a01d05980c0d01e0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 146134415 1250 146133165 146133167
    0x216150c021f170a020a0905060c01020c06090c09150f010f09120b0f09030306010207032004050a0203330103050901140103030504030c1505090907020705191404051005120708030406 80
    0x19450140f4034a1030000740022072a031075401e10031070700150140e81d07500c51400c1c2400144138080c0e1240c2c0d01c05100b590300300441001300d0000c0c045940544204005000d00044000c1003010740d00b000780c0b0254007001400b59182c11640c406000c9141c45e9020700344803006c0014420103031034940c041e912001040c2500c1154000300300ca030605451040c0c1c11640b0090454590900e02640c0f030004075400c07070140e07004200c00c1c00490300d800400742c0b40b401860070103804581d41002041c03c1d80e509075003030017240780c000c0180150b02da000c0c206602e142c500d4208203482d14005d0b0144090140103051618107041c0d50f080031030390000c829003112039803401d179075513034801545d403454000e11640c01440207481012412034042501110702a10080000c10307a80d50500303003000b40b1300f0011300060180444c0250300c0350b41400039243d22600c83c921805c50b01e1480c0031105a1078424803911580800380f500344550b180108009a040c604101d00307044c1c810540326101850034005501d80f4200310f40e040b0008511001c68001891 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 146135665 1250 146134415 146134427
    0xb03010608030903010e1606051c0204060e1206040c090e07054615170a0f0e03040b04030b0408040e0a0b01030c051309020903031b01020a0216150c021f 67
    0x700004d41c020002c2590142c01e045c2c40c0c0c500c5040d00080c000340c0400c104020f0388280c014010070320180315480c107040b0070411120200c0c0e0281e485400417941100b0710404c03034540300d07441c2200e40b4010401fa101c10f203041c1d40c404030501d4081c01140800b03503072a0003102100d0420000310018080241c00382c0c40c03020b250b0618040010301811000c3c03009685d0507000b4040c1c4019201104100c6a15180104441c00c01a030482c500042401d80c3d000c100c2c40c40d2003100703002c1c2c514158601031602a9000529008900303014400d90311980c3e11048aa4001c0004100036581c010448040f00e0308440d05031499212850400f02902c9242e1140c04482440c0060018182d501d0748402c01210090320108400754500d0380c1a01c46002e45001208003118481082184080d6074000300100c0200a094a140480b021131a42407500b4289503140c86a501080e0390301030715010403541d00c2514044107210041c52030159003000c01e8904041410400140007240c2046448040e01c00028a04422111500301c10030a1700804e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 146136915 1250 146135665 146135677
    0xb2404020c03040f050a030b0c070f05010c2d050412020609030a0303020c0c040902030a030c02040b0613030501050108010506060403030c0303020f0c0a02030607052d04080102041508161d040b0301060803 89
    0x880c4e42445070000306031800c100c45034100c07580b01c2c4506500d07903510080c0001541106030261501c0c49c054129400150007882564103245a540f0340b403c0c54151200208038420001c2007010201003503580542c910f42d004002d5400703c078800b5801040310320551021a02d0780c002c1c00c14294242c800e5805800415030990082c2000700e02200494000000c14820041610580003001c0c1d0943c20006100000c24812800500c110f03001030800300e204003004c0c001c205203a20440e04030044a48611040c400c2041c01c2c040c0500401180e0000d20040c180384000803842c2c030940c800201801a00d4140728200340c001e40544001491501002d17071034800c140305903521303850801412803090081e503002030206405941134401d20030060001e40d2410b0400c2c04119644092405c3e1354500a0046c080001c0034103003400208043c04403c0c141500c26030801c8000360145a02a1410300c07000d003600424001c681d40402c14141c54502d038800030b4103032040f90300031400800c9038098464165007410002b2480d40800001445 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 146138165 1250 146136915 146136929
    0x70608090c03070b0d0e0703150e010b0a0503060609150d0602040e0714030619030b070507030207290d0b040912090906050a06050307020316030e01080f040b2404020c0304 75
    0x90484030010103031201c101e402803900d82131040c040d203c0d00300001da010070381400900045442964903610b404841c60071216600d80d1464840c0d00380c00701c034072080c010205045001d55003c4481c9082000080e10307103030010100e50182d4a28000134048034402e00280c02d049001400d550b065400904160002c4c1d4454080c08001280c501d020400140c03007984410b5280c1403000369581140c45003402c1241800c900e0070850980c0103418000b0000c24002c80155001340031544a4555404040c50040c0c28243d00da84004c155080c440d100b1110001860075243c02000030b442c8150369400b40d072009000401c1e024546c19085894140c49804114824500e0002e42c240d9448429440e0341e51411030054810a0044a4009014a8041080360300841c003564000c03210380190b0382400042d030100070200748045800e5001524504075221256049a0380c02e030001c05503080c040b40e81c54162140c0d45141000361110408261181440a800c5035440c422494031070014419950350048800241d500d4010303004581c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 146139415 1250 146138165 146138173
    0x905040c0e1503100e010b090c0d0b01020d020604020d02210105040c12020612040501060314014722050105031b030a08070606050901060c1502210903070507060809 72
    0x6078080a103600b5150304a80010000c0c81d0410380411210080d0000e000b00c100550340350b050280c0c03641c1c0d455031340320b2003103d4071100030392102150303101c10b815100d0903041d0382d0654200c02d5028103010f50110b1110b074066010384000304842043d10109101e04076210400c4628980da40e50390310b1504064001900460250800d000001c2c0c5940d02039284409501d130080d4040340c00c01c1a80310b181503440340c007075015004800029280e50751b9201c2850140c1c1c80d02c2c1d006070903591003210305d440702c5094140c8020304400000700d501412284180619039041c52600041ca500c640d90400040d82d80c201070101a06080290f007501d00d28455201c02c0a4002802010b109005020401c0c0705044d82d4a008444030400070020300361a00c070360301c540640340d000690503502c040d12200003140c151520300c00203009100a603501e030305800c0c50341072035880704410100324000207004004940c000222540005404210780c102e4400c4c0d604e17014692444d521641c10000c00c14000c90b0000150036802003030712842110308009503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 146140665 1250 146139415 146139421
    0x1a0915011d0a051608100b041805010b04050f0d05010b040c0210050c0901051210051c0b07110706200a1208090312150102031338030103021002070905040c0e 69
    0x1000c1526404c035801240c80d80010782c08060144140d0700d00781c22038512801012419201c0c1d98406981d030058000c041c000c83c220000741038005051040d81c2c01480387c01c09550400d0f003442c0018208030701110689100703e00b921071036070a014080d0310a00074540c1c010f00410200e481d12a0180d118800103482000c06031900000580e40d80820045442040c01690360a10f030084610400d84800c2c00503060210605210700003150304d840300c100c070004801c00d88a000012821614007462000130043c610310400410030040940e03140000f50980c00d036906800c113a515002e115401e2401c4580d0440b482910f0300c40c92884030207100f00d052188145022a0b546c0c1c0e01142e4900d00207680d28801c0c240345400c0c1e00c0814001a050849000c490900900e0510580345013103081c3d054a0000c6032130f42c03c0200c2e050325403c000038619001400d209420f90304449440c08030700c81001c0820381c60205110290041001d01c1c04003404505c2400030b0300c0034141d0502d003085642094104488140118020080c00845003004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 146141915 1250 146140665 146140681
    0x120f030f182d0d08030a020c0a080409021314011d030a06050408130506031005041805060a050105040c03060f05060306040e0f0c0f04181101140d1b0504031a0915011d 73
    0x5a00f8610390402800c5241da1a0b1602020081d8007201404429004003000040020200401007009185600000d0780700c3c075a00413900f0b0700d06c20380d40c001c25006410403c04101a43c01a4061414030400c0c8038403107050284602280c200070651000428851525042100b08543d64000c0d100c0b0409081c40810300580716424040c0ca0710090b11601401c990306402040249015040384d407132074103204008200305032140e40d8503203081410303035600c5841916600107100c68201886a00c210b040f00345814051a451300c484c1581c0400c0ca400b80c01d0007100008002040781d29640c11051010f6800700440e400310f03105801907504c030044000224480e090b12034400d0900d241c1030040c00050f1010140c0344001c24099659100092803010307416040c02280907a202c909550b441c080d00142d2400080802c0445c44048010003001c201095081032080a200500102e803020703260b40d54244441204145517200e924500e80741504281080c0b415130360f503c001140d40010400b500800d07580002c6501c441c0d07140c05075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 146143165 1250 146141915 146141929
    0x3051e10050d150b01020d09030f03140703050d0e031306052d12060603010302090109020306030f0d1d09070f050a0309080a0c111509010e0a05040c0e120f030f182d 72
    0x5a000005411844180007042d07d006c0140ae880c2d1003070900511181d0b2030035100280e13800402c4194041480852009140300b00b6028030401e664404026603d411202c4581c1b10b40e0036414081d55040140210303a11404459000791108048440241c0b80484a58052000043d9021803002445401600c0c049500b034104601940d0580340d0083c50803045a080000c880000d4000820081c3d0601c50311034418802542405584c8100040c0d40c1d520b015211301d338450824100c0c1c034118942c040c001c80806c20103a2030740304944801003401e41c54800d54403003c000d001c070044c0c01002c801410b2000e000070702142c50390304124040034091143c0114051000c9117401c00c6070142410b2100150900e00b0010621326600c030307002c0745002c1103000b4a00d03003000b0b442c1c1d000305048501d07403400500031a5120744001e403146000c841c03810362101e0f03203001080003103014005661a40940c08200552440204100403100d4400281242d003134000f801c0c2d103000c6000201054041941c84108868148030140e41c0c1040c0d00b003403a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 146144415 1250 146143165 146143183
    0x1080717120405010c08130e0108070608060f190306050a06090c180b090607080f120903070302150606041d040c050a03081c0e0a030c03090603051e10050d150b0102 72
    0x103080d504083c07a0000541c1c01140c2c0d070074101c03011310080002c0315580d040005c074800030b0008650100c00d29030400000301c2c81e21701c2130307040707501840021010130040f651a81d100c5481ca002c15a00d02c40c0030741100c641c02101910b41c1e04014503090034042004071a0b46241c0c005000c441c40310328180250a5842d4042d0307290156801c1d0f141000d05102400d003c0d0700d1444d00144440d10019050f02d2030081c1645a001e026002a914010039940014486400602143c50703142c0000844000d1868504959406942d84080300604641c201c0c5800028050fa5228020f880041c04d1300c0503085450342c8840200865000120380232500745402d14000301d41d6040000c90401602c2e0b05c640c1031442c2640910480035200040a01c0c00001d584941000d481110300b0f001400c3d101e40701e61140142c40340d042c5800b0b03200c203006030001c1301050710740000c10614940d50100303240e0f00304883e600001107440e1107000e0a4403170500d0300069001100c156075502000104c09079944030042507041040702400d54001283c0346c800039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 146145665 1250 146144415 146144443
    0x7030203030a1e020f0d1508061612021207020d08011a030c0c07030b011805060a051309200328120309200909010525110601080717 58
    0xd10014102c0d00e01c80c0d101d03459403034007030260342911802064004140e030b1042c4c0d01001221004034643c02c070286039000304602e620032070b6007450140303060034845961450001c3c03521400c2104031904202c007501880221041b0403081d60107655a44000d10030700341d120410307203114006116400b05016414821200c07141a40c0f49135550408848100100310181e4001034030140d0180270070010700052075020842913000b50300c920304074034070796140c0140c81184140b0f401004103036600b00001c002e907a5540c04400c400b5944122002c0b002c61003041d5510004007501d1074000c00c081244941c800340a22009494089050b0031022203464105100071458860703090041c00319000340107407810300003510301000c40c000c0b1a464500000c6c003640940351415a404140f03400201c4001428800c2d242d4203145500f80d6000000c00c0c002c1c840760401c550760159280d41d0743c0f00700c1d06c1ea5414030309030094141300c0d0700c503000c40f05c410008603516540c541c400f45444407078602c5024400d4a084010905840010548a50107845 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 146146915 1250 146145665 146145667
    0xe010807020d0c080405030f0d090602010b0d0618020a0627080c010c1b0e071103030405120d020d0614032b0f0504080f0a03030b010513050607050f0d050c01050c07030203 75
    0x203540c0c19034086001c03035411103c510085c000407030a0303102040842c041c04180c0005110940c0840740240550400c3d0304000c0441e41481c002d41c20b030740c0b108600315100940c010701c0040e041c61401c442008541144800a500c002b43c8040014403503400b5480044821148800c84107107088080d00e00c2c6401d085110380001034024600e05045980a00207120b0114090541c1e01000030116070724540440103034220070101500c41c030a0114481e446040e2110040c82000114030b141450340f1070f10b56900b0000694500a20b000410961002090301503c14907006400184610341d00e0300100401c9902c03c0000034000d1081181d064841c00e0324842401041000301500c2206140290f012100092500c0b02801803080030040003868010410207503440c8000d29000e800d64400d240f500030191895840700c0d03410031006100c8105110303144400d2600b1030f80100c80e0140e480c401e51415900b0003002603d410207500448000801c9250030500800c00381500314000c1096640d40960301100c0c1c00f6a407009801030340 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 146148165 1250 146146915 146146933
    0x807050702150a050f04060305070f0903030e09181504060b1f08040203071d040605070306150e0a0306110c0c0301020412060f0e0f030d0b030c0d030c11060d0b010e01080702 76
    0x741c0d041c01004000e143c1d15003e80317468100390051031036038015440400080e540e44c04111404e40c0c494441c05140031545000005c217403841c2ca0050000c001684041d2180d5460310114a0769520b078014101d2280d00d03007056458030b82d02031500c100901402c076020b4425a040090f204218613000fa82000284603d21089494140300c0d40b044400c450001c004981503c5800004608100440f41c2d0f50012508102c48081e103241a02c3c001d82a00c6002c4d07c0403090504102c8144a910360039000c08000560030b00e080310444001c0b02c0010611116584003130411441c0c80b00e1a401168107000510720401503000b03d6185204400034076080f0b100324030903201824505c0f81d41c080025035a8000800034961000045900440c0c8000103007031000065a4011070b43c0b001031055154102c5004560b40c5640c00c0700a44449050035021551803400b22000400700b0604c01805010004130702c030306182c17000c1c014203129100d5404503000c8004280914555010030360342c844100301584944103c034814007865000c1c1020308 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 146149415 1250 146148165 146148199
    0x120a090308180d0c060f08040302060c07060f02030c070203070f05090417070c0608150f0f010804030215040813050d0c03060216050a050105010512060c0304030e010e0607050d0807050702 82
    0x2401519165030121a081410b003865030b2074220103404103010368183d0340d4903450b0903805844485100c003402c0910039403e08201c082074001c43d00f40d6214110407103041d55aa083c0c0740c00e0005000301014403002a201109124002a1900240505601c280c044075403a50301c1c0c440c0f424200115105007644030b04510b0000c1c000440c14075200d0824255008403a08060392a540d41c1030075421a040007002880700302c100081ca003048240029001ca0030340b90200c1c3c0221140100329041403202882d41800010350100302094400c00140c1d03407852a00350348582608280c9030a02c4141e01034502c01000918809002c10755103040c48400d2015a8000c2c882400e4a15568031003000c0d40007094a50040000101b04074081a02404640d4281e40316000000c1c066040904000c41041c519418488591001c0200300541101c0411a60025014241201c0e24005500100d907920340c40d6003070b0fa400617404101d9908028002030075803044030b10381c0c0701d1010546d107002e011102405141030180d13004044130f05c0300c01c3d10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 146150665 1250 146149415 146149417
    0xa050309040903090b0a0f030f060509041407050d030f03050109050903090d020a0b040b07020a0b0a0c1b0506280503100e1902030916140603040210021c030e120a090308 74
    0x314031034140941030617176030750504106801488094000c11a590142c01c820703603151103100420404828100038203070420700455907a0b00000c000034802403086654504400341007122600524000300000c10008140c98000c00c2000c07104a44404603040c01e001140c550b500d40120b0784540b00003001581051380500410805966955090b6000007103000d022640203400c800a001070944030041d56034910a6206210304000c0581c402e0704400c9081c420b17400002e03030207025041c0454006200d40174402914007645410b44083d84a107500c940000384000103100d05821140180212a59142500300145c0080c2c07601c0c4401c65000094030b07405c510130302641d62501070f0300d03030440d5900400f000c64105001c00704089a1066032042d413540e00082d003001c6100355001c0050302403c000301200c012004c0b82d02c040f90342408003800c024810701c0c400040302c18003442046030070342e0301c00c0100340001c100c00d0480010700204804c80c01c80e900707030040496120007091004221080c0415a42c0c4001c00b46103035841d03900740303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 146151915 1250 146150665 146150681
    0x51003021008060112061205161d0c090904031e0c032001060f0b0c071409040602071401050c090f01020606100f200313120b0103030f0302070816020901080a05030904 73
    0x140301070351700c0010402403c0d01c950009400e10500c4550049041e007070080c40c04440701a60400381500c018103114000c1e42902c40031840200040302409521070642006141c0180d0708965002046841080145a0f00c8070400400030b10040310034004c00d01e920f0303049a9030300320a5400f17804101d8035441a85200a18500b05011107a036034000143c407916010388229031500b660001e5140c081c0400ea145d54850244080d2005004400a071300b881c0e0b1461001c100340300e8006001419943d80031440d203060000055259180480c8000200114580f42c0e1140343d803600030500442c0507920306203011b81d95500001744035009441c0108048401c1400302d800f103442e1a00815481d04001d0f004450b0086498045000018031140c40c000d540c680c0a090480c68800401c2d6220410303041507000c1d81c0d00801c0040600c0d90540c1e40600d060728222280e03c0c015000307849a07100c0144030b0b40d00003600f961000a44044c2da070302c10340300300e400300c03026603071085180e1355102006006842030f00104a004028a042c4e407040c50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 146153165 1250 146151915 146151917
    0x918020906010c0501060807170f0c040902011b0b1603182006030403050a08101d09190b0405150c04060f0e04020403030302030f06042f0f030115030510030210080601 73
    0x3d04240141c2c0c860342540c9056201ca07105038410b850a00006402901030113220703158000506020100d07011481d0741e0f510145645001c0d0360f5540b03541f81964800d11050300441d2803003111040310031151510441c201000c440d04040c486c3c414003035aa41500c80c0c09240451041c10812207040f82140d201d00c125002c03c0300c006c09030a0044c81a0003403d03103c28000d14841c2c1c0c083d4503025111700403080080c002d8035008003070201c1112100805e200c64442c455600f490b20300c4500c1a140340b0350701c80121602d01280450081c025a80039400501041280000340e44110310420948001c1528080d881016041c2078500180d030410500003071216901c600303c1e03202e040301585001c01d0b4040712480414100c2e03010f0340042c0d0009400104100da0400d43c403503155000041500d040004081320529414045071101214420a024070b40c141c45004040041e0303444500f68030f16003980c0b0f5a55102c041c184080c842d00d10000720781000e000030000b50071740c0c81820403030740c02070503d400a07030341e21804a0303c060006043c24 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 146154415 1250 146153165 146153177
    0x31f020403020405160e0103050f040b150307080f15010501090e0a0207020d141b0303030a020c0705130c180506040b1b0a030e011418040203071e02030310091802090601 74
    0xda43c0e640200c03805040e0851400c8000780507002d008100488440b02e180c181401c02082c070854640c403405155200740c104e001104a80c498803414082014400f460f2607140c4200349011604c0c4001045090194205100b2940003440c0c001400000580034860706021902c40c0c60100b209000101a50f07500000080f40149810142c0c1e00180144070059810341e00c010507030802c11000d0341c003000b0f60440f41341c80e46174404074454504002036580c0320081c204608141c011074085a500f004000950282038001d10908640c80204d6032503006006181039040041d00820384080300340380f600340000a81d04042c224a01e0b09051082410941d40301052030700c20383c044a01364901045040c010302e282140b29a880c003202c4800c400004150b00c04202c403815000d10104040d6281190ba82042060f0900c2580c015842c2d03521280140e54980c12141c0c1407042c043c60102c81d02c5481d6000c8011442403040d02c0400100f030341c40c1d00c6030004858540744440b1a0030f40c507000c02005881c2182d10203a102c00149002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 146155665 1250 146154415 146154419
    0xa23010e190603020d2306010509012604050613050304032d060b030705100917030c03040f09050106030c0806040f0605060c07170307050703080a0504090203071d030606031f0204 78
    0xa5841841c503601040c0041c3d8045001c4c501c024950081004e020085400c60003115201405e60003012005050320781440030002c2d8102c4164000d080300e4903000c00401200743c2800070605122000402120106d41500400c800161031901d00a4000c20650700301000f9410a030a40c1c1d00d030428109440840021148640071242c00c0030b0400c001c544610703216010208100386490280743c1742040a81146208801d0240075240241d4045000011640e103260a4015000b840480ca0f040d481040e0584406020000d000308020000f07018180c201c42440c0810401c40e03a8801c011801c5505848141000920340740200b01c4500c0c20384c00c0204880103051000640c2d43e91b510026545034419030120050340c1260784200241d0009040c0098071844c0c20010710303d459600d070350701902d03500c050000820b502c0d004180b441505100740182c8000e001d041c0002c564a040469001d4007002000788034944240d5203028040c0e43e0704000c914140600000380c001c0c0032014400c803a040a8889031204d1546260f428040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 146156915 1250 146155665 146155699
    0x1b0906071109010e011a0906090301020a0f08010e040803071d03010f06290703120f0515120d0801050411190521040b010303030c020c0306150a23010e 66
    0x1000098840e04100c4181d031520014040a0001688014100f203440c0004101940300030181d0840220b001d140c05070340c2c241d08800074066001c0c1e5828560990300c081101e501e1180c002981560070506515505d085a903648440d074002107044400419810050001c50f0909008410000c28195400418070394034882401090031030300146001d40300345032500401c0083c0c0b4182e906000b0300e80e99907a01c640b1a5164010400401e01c05d00900600304041d14800410044650303000c009494901402400346041c60740d202c3c1c0040441101d4644502001e000000d088030001482c1c00402c69144c17150f40650707181c241000024a4044011940100100800c2d41006c144030550b01a2040325120700380c1700c1c98007100030480b000400348400c0e464507410b0180804280a100c056044030352519003c902c0890390a0124100380110715401d4040c4070712000d004040500390003120b0801d8060300d0007403005030b0b641442082036811001402030504041000300041d44035802d011340220000d0301d094803c08140c28 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 146158165 1250 146156915 146156917
    0x2060a1707031a040501080d0f02120c06060114070b060909030c0115060f02030c0303011a0c0f01060512190213061806030c060504060f0c0c09020f0306190e1b0906 72
    0x52801c00180e59003504030b09000780018011036061050320100169030500c0602943c813140300d00542c051161141d2103d91140c42000f136450a000760340ba005455204840c079150b92004240d070f0b164086215040e04100c029075050580d20b81c03d800200f4059a520b80c00140049a1030241900301c01d80010840e15003284000d000d01ea42e1030510000143c03449203068070080440e40c1122200e001c40d0010000540741c802c002058030f05640001d820040c3c01007000401c0d02d0035216110060805026008034040180010750114040703807000d490851103103161303840d5035407035421000c2d0545080a10741c00c000e0250401c04180c03004401c0044000401985844445003240038a04448035007a0701c1c0d450520070005c0130b440e401d0003000c3c41d08041d03040038103200014010005203611030301000200c8802c0014410721080250042642020071544c0d026400148206a8801c495607800b41d81840002e460144c025042d41c4c040340d44200840201da21495034503031003110813140c43c0741078290900c02c180d980c4d5107200c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 146159415 1250 146158165 146158171
    0x80d09060e030c241905090319050901020d0806030d0c0515011e06090609051c020a080c1806030309060c01090203070e040219150e060f070c17010903050702060a17 72
    0x4001000c43c085030010007080d03080c130401c1e10b18107450030364180300c0068000300c0c0381082003000000105040e41c0d4003102d2440e40c040d2256050740c03000804450103106410034000e01c0110300c20790980e02d034911101c2050f40c80010543d90b0f143c06500100094103803d00c5020302d0071525124609480341c0b02482070780d49425034002e8001a6141d20b07041011001e142642c601d40008204d14208100c40c58a80480541401114070580780514240c45026440a403d03030507020400d68000c10801c0b1180c1c070b071070080f5500c021441741a1f0280e070f41070303d841d600841d980c0d88044c41044010011840d168102050040f40e0704680c0030304c8069900c84074040300517071341884010f02800c40b88a030351146103480c0c010001d000c1c41c40f25210700300c031404182c248402c0c140c03502841c245203254100360a58031a5000030503218840c1d114500107510000c10884108802441000f0858440301d08c039032201d8171090b400307900300da03207a0000170041101003104500506100016001c00d00450502e4084001100b2032601460021 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 146160665 1250 146159415 146159437
    0xb030c060705190c231021060605030601030e011404240207050307020f01050c1c110708030904230114060904050f04020307150e09100807170613080d09060e03 70
    0x2103405002c25403041084400d02c06841880703281c85e060010101d014400b140c80742d8030070009440c00d902220503140304201d5101182807020014540d481e00c0080032900309543e201e00207403c2248220041e00140955484c410380640b00c10065100e60750740e0405050080701c249401c03000e0110240c0703503610302d04c042d01006004001039035640f074a910401001c101c1601c6007605100041c0810780026100107074040d40030107d0a404281481d9451090311840400786440b4040d105407600450035a4010001d04607000b13042d00e05009450070034032666206911b4251010404400d1801008440c0d284901e40030751010180c40645062840310215066940444240c28054851401e00c0f0460404102e0741c001480200b40d41c802c0c500c0701d81001800034104220481c40380070407101103204c1032040040040141005811030700d440c1c0d03807412440c16155003040150064010100020507810503002c907030b46629417004655250011010b0701000404c282c04042d50b201d60384458031a0800c504000500701c038840 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 146161915 1250 146160665 146160683
    0xa0314070504050c0f07030c061508011a01090b0a0e01120e0105060f0301020f0f091309050d03061401050301090c110714040617030306060307020c060a0f0e040b030c06070519 77
    0x1000c003070000f614005807522907110000c0200c02c14104a01c4250341403507a01d882d240781a82400d0506501030b00d90074038400742060303100c0300000710910305512400d040c1c1440f2050903030100e420b00041d00d10009606c65000c0d0104100442c081da203201d036003016059181410309144221989a030841110007a074011200c503951542840b000d4035151520424281c0100c0096142400c3c4541e452042e014a50301324840010100d6100000d0b91050080804c042d424081004191141d007005950f544c3c803901c0380d00200b0328000707004c00c806000d500c815554580684400f842c5921b04400c8a00421503601c4c58000c1000321068043c46a0042c400390000308004047c2400349800300c0300b0881211f1007540a0484a40d0440e42e410807842c02100752503003c02c04a030302d036490b5560400164100340003600b505501c841c00040c210800d136004400031441c2540d90380c1d10003000c01c5480601044801d01d101c655450761000149040c649094002058418070a0060300e003644202c003422821004a807031304079001a1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 146163165 1250 146161915 146161919
    0x405190905040c080f011116060902040e0c130b0a050d03021501060f030e06100608100306020f0a09050102010506031218040501031101170705120a02040b070309080609031e090a031407 81
    0x4102e488600301700a00200320b070348680d4100310b07510302c91000851444d40c0b0b48444001480003650118001a07009070060007400c480342041d1343c40348036444c500751040109504040490000d4820b041d80340744040d1410040342c0c20001008503603420000700301d0851155004122a090100c554140203000d5070b02c1d00c6107080c4d8820b8015056444015208245034842420000301c0100080b0384022503815003481c0c009a181c4075140c0c580d00e956074002400490001074102000c0d1780200040203082c2e00c40d0b844086d002c1d101c00c0120700380d440c203840d1030798960b00100c503906880c141000104111814210500b16401c1e17500d02050a48900f40c0c402d0380d894084403440222540c01c04a54403414a000c030804807140750441e00500a03024000d0700240980010000850704256030341160082c4c42041500360319140c0750f150017440040c05010f0148940a80000b1030b4010078000700340c900300c0c1ca1203200c8910005102c0b08007001c50f0820880241e0000e0448e100001040e0880031220325050701c81d014002042c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 146164415 1250 146163165 146163179
    0x9060509120717090a0807030503030106030506100c02012d0c15020301061d03010b06161202240618010602031b0706050d0f060302090c0a080604020a02030405190905040c 75
    0x50003003004100e45070412a03100080c0c0e4140c0c00d07081da22a800d1480e6120042c1c0008107241c520150410f111038440d101000c001d002000002c0c3d412100e81d07030740601c100d0780c0314404d00c00125034401007a4080341115031301c40c00540c0102c03038003207000044907500c0803012541005910320014480901c1c0115a00050031000c0c80a45503012601d5848030b0000c0d451545403040c0104421407a003000c600f01d15194140003490340d02900402544140206801e4483c0d2a005450746042040c0030101d50b4054000110b0705258008210100f25521070b401104030101030400300d100c10500102010f0f4044080004c90b014800361002840c0a00300d6a40115220003c0140d441159521714080740c003241d0001408001e40d82d84001140c910806d000004031318801009601c01c054001d41d0402948041540c0030090072002c403001900d104002ca42e2403070300c180c9649040c0002c9101e643d40101c0107800c03c100c144007a041003886040161800c007009280d0036610183c00d4100e0380280c404442c4418032040402c254 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 146165665 1250 146164415 146164423
    0xc0c05010e0307210c0b3c060d02030c041b020607030b030c010f11010c0f030c030501050d06020f1b0706030b100909111c060303020d2a08070609060509 67
    0x44140301c40190310b80306240d142e0b49000d0340a411400c203000210b01100100510032081c04003001d5004195080e2810049841c0c00c4091507409080e81400b02d03e900d003070804070503600107005100f02d41899100e9864000030700810b003080c202e069030544141d0a0700010350722a0701c00e91260498280702e001e0000c215200090500401500160416091418204d41c0b6a808559411070140900344900c0c1d002d80340b103003a100480c19001c00c40701940780070b4000437960303084550042c41444d241d0b0f04000300c803414541541120000c0c001c041d0000c800f00e070000001125980208621001220300f00d04081680aa400d00c24030010200c440302c1d081072000708040c5415000d9101c800f50102c50001000010383d0004016079103511a072150142c640c404a10301028260031900e00c21459805111140b6a2119502c0600564481200148203104220403503d11440d48209810040820000003036104941800e6666000304160b40c0650700304110400660544142c51400388602000b0882c1d1411000711424 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 146166915 1250 146165665 146165681
    0x1b0c01030e030a020d1206120b01060f020712020609010507080307050c07051c020d031809020c060115020703030c030909020309010b0906102304120c080c0d08090103180203010c0c0501 81
    0x442c1e1081c800250995000305542c88450818680b107a031070305400c600b41010b4a060380c40864100230000d0360000788101c0703254060503500240c6407444040144d0400300da40b0704151081741000c6d501d00c41c040c2c0c0185030200040c8443c00341454101e00b0325a175a214034040f6801550544c001c90b100050a42401d00300344419002404100c070440192624400c208030310000401d070080c0f042d45002c1030350b01050300421030040415480b004440d5620340b249403403030080d8003261070503620f80304020000403007509454803494000304581c06046064a1541c00707481648140004400b840760001000c521003500d840550b215034220000071032405800c02c02c0c001c5402000d080b0718042c183c000c00c402701c580e0b0040c4028015035003040d4002204904040d01d6070a50140d9008514160303031851142e01440030300e078210300503100460305540000b0202010045a09620300c4018080d41d02441441055802a070102202c4a0030046039128140c0e5980020701312441d00b12082d0114207001000030a001c0300b4410a21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 146168165 1250 146166915 146166941
    0x1204050106120c0b030a1b26011d07050d020f0a0f0f2f0d051e03040f150b030d03061802040305030d09080c010c0207140402031e0901021b0c0103 64
    0x6882c0003540c071402c0e03020780b450044c0e40e12064000080341908a070365000c028000d80d1400c801d80c00a0243d100282800740c3c0b02c2e1000350300c1009164460009502d036148038100c600d150001200b0061100c1132800c8a0300003018901800302c1440360703550310009800107000c4070342041e00b496135800039854081d007010081004942002982102000b20b1754100086040d420301e40038002e414400c0c09041002002d004203000c116600801c0d15031284242c00501074222644244003001401c414100ba4803060b0104440c00380915030808040c50124141e00400e650550f812140451401c01410101c0d00d00030340059402c0c00030b5a1440204812604681c0c000364201e40000c081d8545465500c6e0b1507074078045c0095a5011a507200740400401072640e08854039200c100000780013a86941101944454040c030600c500b0820390110300d582403500d4804c881c4100c01e000482a4987d0213004080e00980c0c004110b440710b50344c02c005c55040c00c4004144803d8941030f9070b00802010664200040544402c18000f603 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 146169415 1250 146168165 146168189
    0x6020d0f08090c120c03150f0f0c0a03020904141609091505062a0d0815100f09080327010201090c090506010903020405010b09090f130f06111204050106 67
    0x41003500c00314001c401120b00700c4100c404d0312020340d81c40b420144180c041d02d605100700e45444042914840880e482010041c0b030712086582c40c0399101418174012640750310740300000c00004880502a5018203099100039100081070004440302c80c040030300641d007000890300202d0290031032075030001404000e415000c400703020711805240032039080300031f60103418810b140101d0080e0410300d5036240640120f130f40900c03c5080000d80401340341c80b030010b0007050740014035200c0040d10b035104206481d20a0728010307007101d10400444408980041c4500c1a94080003041c08001400c442c040025185104909415010b11462058110040040502c0c00350659042c00d0280b0041250080c080c800c682856001081c81d55804004951800c82504000d500a01d8400003190007107010020340001c0703106540d90107880d00d50071510300071564116400000d5440344400c00000801201d0502c40300c83c030845003c00c0b0008404c0b42024145c00240000c0d045c0341e079140412042c00400d005400c010700901c01d5030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 146170665 1250 146169415 146169421
    0xf05060702011104060819060b040801061a0306040f0609020c07140a030f0311010b040c050306030c09011401050f1911100c020705062a01020a0e09011d060a030b0106020d0f08 77
    0x10815078013551091707000744003040c00003500000c01c20990b038805101010b0100187c9407203034140e146c00c0d0400d0041c03c2441d072a220700410790151360030300c1c00142d080780960981140e40c0c820402c0080c01c400200b1b800c5031030321050002807290460001d44110404040540501414000081c1c00d50b02d918013102d200b610300c1e04080012442982c8800c40858061503c60383c064200c1d1202c501401e2101c4805401c40c0c54a501040c00c590b0003030203140580c90890075a40c074594000f081004111003805048009890080e10400c81d6018000602901c40702c0132030541010070580d500d107031034800f10b03040502003800c03080a041001020f20070305c150f6004031101004a0710580e01e00079512603850045d640075407000140c1d00c80b030a80b1034080f41021003c4c282e000074540c0b0045c207203601070340090507054045002c01421105918101c0401070503121109039244a900d41c2202c41419100c001c0d000c603400050308600400411702c00503015018110940045c10220886030f03009058100d000001c2080004000034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 146171915 1250 146170665 146170691
    0x11121504030c0203070e0f0403030501120507090c020106030c09020702030d1b060506011101020d0605120a170f09030a0524011d090102190c060b060a0f26040f0506070201 75
    0x401504a41c06140c10b041850092010074609081a081804400307806c1d4100014582c000c03584a200320300c6940c042c85166a9160a5510a0075801c0000d0680d005210305010503081c030790084100200c00d1001084003562910740d100728607039640103060801d4002a1800550404000c80d40c03a203903640ca80000010302120082d6040d40051000070129511a0003082031a0303c41c401318114a0040d900171569a280ca03100480201160301c0f0322800340206000316010010040f903550211a000540b224035005880d05d204860782c8034080800d0015402c2c0004401501d08029a2601d40c1c407520040540d56070311403251203010901c400507802c0c0d01d0160b0061207141c2c1a00e102c240303030017400b104000240d1030300190140a40030701a08240400300300740742c041e00141c1c010000782e54203001c1c6200700300300e0880d0005d00c400351003900255004101d901406603e281e208241416011584c04047c1a910000d0000024071407010790381502c1d002400c01c0c80a0074400c0c18072100c0d0b000b4210f0300007000303850a6116 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 146173165 1250 146171915 146171953
    0x1a070804021309020409080a050a0e0303030907090f0207060c0f080c0412030c151b08060301140714070209010906030b0906060307050d05070e13051b150706181112 72
    0x1042101c81a200e00d002c3c011503c039600040010303980b00307003074544840507690014060f811003070b100000650303d09040e1940f07042c04011a80a80c0b0040060a1304904002141010380081d400040031980c0c2001180c0215507984a03e001c50b0301d035665403042091414600400d42e9501400300325100504100402c8506803000380b0514465041c100420111801c1c201844540800740080c1c584905185910102243c414019440c03074070261684100b540341d0f070084c10301300d802c240e4403d51a42c14441c0460419400f505e9119510010001070074a881500ea0110b458000c00313a11045040b41c40344010b20800120300f810aa1196680008094910700440020355421b858454980102c02d10503e51090101c28402c15000e40201a28408642820000101807400089003564280902c21424240280342d00e00d5442e2403c005100700841c0c1d03501c0c503000c180c41d4003140f4107c0780265144410100d00054480643e03c81303010340d131401c220003144420311038030f04500783e88203201d5040f0398085260719030061 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 146174415 1250 146173165 146173189
    0x40b12091207120507060609020903010c050f0301140303130f180902010903030509120304030f11090f010b030601050d0e01050a0b06071a060a0503060103050102091809030a0c1e1a07080402 83
    0x559020f5084801040590f000d21030403102a01da03d00f808001b1030340d40c00940003403a040005034002c00c8660480e40d4221134a001e1907226800300c10f01000100246401007140e10860030005081d2480d0002d090a0a00c2d9401c0f0b03540210b013412450380c020808034280b0961201780d400c0d040c5051000800550008200c0d03400c034007008003802004101e15016813100c032a01003405030004c04480d0780310384a003400a0903901c0b115081340c50060340741001801d81000843c0d18010054000500c0459080c4020752802d83c02c014425410040c0500071094010818052012070141c40400041c15080960814081e80c09c2e004405001e11010880d0301c1c009441d03152280700355185000b950b0035075210321001a640e050240c0c00316a06202d502c2c0040107010041d03000b0881042c048441800080b008008007c0a20046880e2200c1d42c2082c049641c100e40190861003005100e01c054800d200c514006105205003040b00681c1c0030301e10420204040d00b8030540b4a40c01650504201110f8a0b00b80c2c0007401540e0340c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 146175665 1250 146174415 146174423
    0x10b0a150305180106060e03010501050117010911090a03060903091a04060806030f030f0418050105012f07060e040e0f0a12020309150918010311061e040b12091207 72
    0x38500085003c030004601e101400c1451009000700c543d9008000c11241304400c0c410700c254641400060b041d802a01120340303441c140c8024074042d80c078080f806402803058082081216500b000381419558542d440a009144542e00009001d070319810002c1c0807140301d4100c0000f03142d4902d0110141c507003800c00d0300c089410610b00340d0300300e664150201e42132502064000c14948004240480040d80d0040504182c0303505204101811404900035002e40d10284a031a01140c3e03540c0381c4e8982c507481d01914240d0034524810b03000c02e00c107501c4403241c0341c98040d5100302d000422500a00d04245428051030084800e2500101081446080b41985400340c000000b080c44030307002c03580e4080d18002d0050740c02c01c000091a0314120b951441d80c00145500c611051441407091072624a010215101c050f810399800c1110241c907011540c0911000d41e00c40d0b85120494120f03420b1040214014000600213480700701c80307403074940328222140324140304054103088554120350b10a82c0501030f6001651411900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 146176915 1250 146175665 146175671
    0x170606010828090303051605091e040e0703030806040e030702151315080402130c020c19050303071b0e07050a03021b10090507090903050711040204050909070503010b0a1503 76
    0x42034640c0741000020401c021009400c00f0801014160190f1025100c2d04410808515030480750208843c0c6100b64a40c07194024003413046004030140c2c14220006143c0058000644000807440329841c2569a6204600107101c4a081101d24109130040a030145180e03402941000b10560000700b50808090000015210206084814044100c40400245540d001d1251580c0001c50010541042120180e0040095001540c040c94903032080c0b00c090f44003940580684180c2404124402c603150040200001e545240450781d60740c280024540c081c814010544030841c20007070407105000c0c075800000000e083d0341c01c00c40e00c6a004001c84036020341a240050b91a002e1a040044000b044040e00205104000314405800501c3c1d00015000c1c0c02642111401a542c0c1d0144081d01c0c0811001000580140f00c0c0c0070004170186104000e42c20000c10160030a1f40310300200c0c0d541d58080350740d0705c200d034045602000719040a200e00d0160b00d006032018241182031452a0420030a072404800802d59 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 146178165 1250 146176915 146176951
    0x10f020708030f061f02011505121005060105090418150b180402180403050d05092a1f0503041b05060708090102010902031207200307060503040302070f0e011706060108 74
    0x51003401c020003100c500601d0200d4400740c1c85d0020300030001001d1380790625030440e4000c103181c03030008a100014030b40358000304040c060b1055114094180549058140841442450b503141d5030750080346025020500c039a0801416810400340d80c28150780c0250b4154502024003156407104a010210400d044008503000d496038808542d030510348546a40020185c9010b01003055444070050141a41091080c08183c6402000075141d00564411152981040101d440300b038407811080d032100d810007020144864624401503d001070701c0a100c10019100104202c1084100401101c00039190381005090300e0034580464a40c0c4154000901954070101d184e0344568800d402604400e079016068421426202c168045e881d0000c001c201c94002160303108070702404045040488540005000340002850508151070692010b04143c00f1409011408a01d035a210341c4035100401000c80548034235032400e0f54002c400303074002c41d154800e84c11400520503541e9112210a410100c002d40b020000c5c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 146179415 1250 146178165 146178169
    0xa08061801060c080f13080f01060509060d15020a09030309080105190509010b120d1205061008040512030705040f050603061f0201060914060103050702060103030228080c010b0102010f020708030f06 87
    0x20150505ca0f81318902d0000d11035158802c0f00c160941200e41d0041210050b001e520303141801d984850280f2a001407030707040080d200d45441c1196a401501031b480d08500c0c0785450b040007081e82d014112400110f41d01c1c40c01042019484560b00c00200f9901000304541c0c01c1400c254240008940d000c1c1010b55281d00204840840a502c1051401401805d1811286044405917242c010812360718003c2620426025201e410328000c182c465840148880c040c462050815500060081d005581c0c501c45c00108013035045090004501039021a141c071a1214580120340344609400e8008a00610040c0284201505c42c00c0c8203451a034101c0011060401c5100012801000b00754440100780d0f0900164807100741080c501c02d4000d00081c2e8041c0031340e95440c0e1051303a032803500b0301c0000c0042c1e0140c0401c2408100c01c003d403e80008482c203008410100d240c44013203961f004007202d4a030507551500c030400550b80911662880103e1400c0550600225440380e2580740002805454030b1681000040c50315 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 146180665 1250 146179415 146179417
    0x304200111010203070f08010b0403080f180315040209161b0228030210020a02010206070c0f080f0c010501090b01020c19120c0f060309080306190305060c0a08061801060c08 76
    0x140395070000c5481340303032040c0c0050064161001040100d8005400454018a41421542600c3e080304e0151b20f844884d845500480d803007869030312201034048100ca049a80c042c001b51111a81d00c17651803415040900421014480241004900c0408010043c0c50203811485031a9506000c202204200c0420b00102d03010a14104541c1072002000c103402c4041c801840604083c0c90082e01c070050007080c404d0080e80c1c0d40e0030019010340964480030011f0030151080110302c03d894030440d41d05480e2030b400d5030707850b886400c418641640708801082030043c140d030034400c41c2e0060030380d10018411591f00000113510307814007601090042c40c031103002c0300d5001045810130340100080e0840460404690400c910000a40e0041921183c070004002542502c28018110301c640c0142800d46151201c2d41040486071800c002480700405102000003c540144a418425118002081d1f910509940001c00248004100710b10a0b4001d510b030541c0307a880e00001034155509401e24214001d00d5007480b00032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 146181915 1250 146180665 146180687
    0x60c0a0503030106020f100204050603040b0907090c050d051003080307271212030c08060906031005040503030702120408070b030601050c0304030c0501080609090c040b040b12010e06070503042001 86
    0x620000000181803a800640b244802c000c1c3d0050703c00c0c0e0f87c94481c9000a92060384036660348a80f0074008580031404c0c00030810b4110b07001a0480b10510382d10322410b01652850800c1c0c80101e400880e2016030a4081d0040700da01c004444405250f5074103540ea100b0103400013400c510108030205110380401d254000182c414102c60b0b41ca02c60ba910f07a200d401007502c0030320103400c46540d640320714880040340c001e0003449a40041502c40c401180e445000b480819100204a10761500c81d4501c40752211071180303d01801140204080c0d0740d2031800000c060310704096040c500048900812003040000c1021441c1410340c0c401040c034070383c1d980fa01c1004980e14018203040508500000500000f00110340b034165003281c0013070b00d070394183d030f07035254100a104c3e14112402c101e107411503500309855142c10b522000e803d9a004000187c3e80d004500443e9040d880304403078140f45c0c3e5444819500510040001c154001210702c3c2442c030310b141507906c03400d88107904030300d81030485a0342d039010059a000e002082c803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 146183165 1250 146181915 146181923
    0x9180305091908030a031409031e120a06150203041a0a030b0603010603020c01060501110a030c0615080f0c0d020d0b060a121506060f0c030507020604080111070506071d060c0a 77
    0x1d0709032a80320f129140d5100302900030100f490b00b500c01e070a202208030306034030031255140a58144008058100c0c0d14081180d400c41d07510a040000f804003640400046008900742c08002440c9410b03c108400c090300040c0c0940c040d54000c0c0010005040c2c680354000880d503030195055214081708400b0743c040c0c08088040b542c40403011001244680c0d055001c0d050039075011009218031076540c0b0040d6600801c164014580c2c1e000121420042406880009507a40c0700380c10024401420a0b9031310111081a04005a2904102540c501d85101000550514402101d010307a01c062103034000354001e691048010140e00d80b90f0006046507840c500d4020040c00001003086025905103400304c8645a035044000d085031800c4408607941d4458454040f11740075580b500d180b440d0b82510305541c2130300558403c0307900000422011441d00070a01584941e03e00b5400c40c0c40c2c0b40d07081840c05c5814120010480c0f800c201001c031465002c01c40118004100c010b0070345840350385101c080391413410003000c0d06020f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 146184415 1250 146183165 146183209
    0x4030f0317100501050304020103021b01110903012003040b1302040507030504050f07030510020913090503270a0e0712060e0601110a150203060612090105040209010918030509 77
    0x406058101d0040e400d020015014032a9541e20503219002ca05180d0143d5400180244002001940640d00520300c1002e45004c070242c070211005400e003500c030216410808048080340c002150f0030240500b03211641448004684620303070700300424540c08001d001801c800c029602144a805448102c0b42040c0d03000340c401c1c001850083d8001e0058202503d04031114410440518003214002c1849029242c1c80070147c918800c602c2c0b41c01c0040d40040c2059580925802c40e03d082500051052041082c0310b00d02441c0c403072030300b2808420030b1014900d810280e4001c800c0c12030314560300c055001045e1813002c00221100e4070340e401c007110045211a003062030345143c6200454250601c1301c0e1644624400d984000b00818111085070715a16038400080500d5005a15100c4491458015552024014055030708207059111a2050840181c80d56401655200180000d5080070b00c1c0c0540075100c402014040012f150203000b40780c1d0041075018003049008501d070380c11555a4600c1410504c2955610 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 146185665 1250 146184415 146184443
    0x702130204091505030303090d050c240711031303060507142d0c030403021c0b04110102060601090b0306090402040609020711030606010905031c14030c0315151e0403 73
    0x21500030032040f06040711402e48100001000e00e400001c81c0d1040007144003030034030f000380040150345a400c90102c081d002c0c0140e5400b10401c181a18840c1d0004000403000046414184406441c2d0800c1c2003103011036801c10480d2031145035003400b2601c1120751040303001030f40d0b58465800310b5007804001c0900d64552000290341650101513075490321102c0301000c51005ca001c3d03036a2101002d01c5060120b980682091000300054a4800704030403040544c2d03059240e41413561740d2410854042101c0868004030f0307101840c0e1080d42d04110b181e900c82801c1c20000702e00b5040644801d22400005c203000e1103480f01100140440d113a91300514001c1610150a64a544061508901c890300911009010f84985d03c000346140d0300c104606412100e001c4c01030103410600300140020044004803810600182402021200c216840118402d0342d130b034590f40c0d80380d05003800080d403051028458a4450017146c404012400717940c01c01c6414041004108003005002419158150300850344050840761071540c00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 146186915 1250 146185665 146185679
    0xc080f041509050d0f0206060d0602160206120703050903070804030b060d02060a12050a05040807021201020702130902090601020d0801060c0501090807050c0a2103031a0405010f050102010e030913020702130204 92
    0x50342e048840c07644c5030500d807121400c000300e80e07d4030b044070f4040d172011070190b0b400c0100f0f5050b0b0003402c82400e1400b0ba002200165000b084c002ea100210482c2c0d40d8004600300008a6858481c0d990043c0001016520f0140c0f2615034240c130b4012408040d101c919032802042007a81d810203c0704800758003510300c03919189100c0c03010304140c0c40c130881003908509100000d40c04481511600d441582e21051550400c0d4030364003842190022084008565907003001220090b07910310000225145486601181c0c5900d14414462a1003000c1c01d003606642c4044802d2001e03581001c0c1c000d055030700601d0810a20034680c1882809845450341c061300032840050180140070000c40d0703955a010301a960741212030354a41900900324403120014031903441c407600020000344030713400031941c2820325003038040c0d03508076113000608543c000c0e40040e52840b0164004c01041d40c0a0060003131030569000035504003071f001c40c0440c082142d10340c40251143c0d400a0100c045541c0d071280e640240054803411506d1310b0711030354 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 146188165 1250 146186915 146186923
    0xa0212153d0806030d0302130b04080a200906120709060b0a02011b05090d03110607020c01020c0102010b0901211e170f0d0e030d0c05130501030c080f04150905 70
    0x541c14880e51a1101c410800c907008801090050704041c00820030311644202c00c0b002504401c06846508825010000d400f03000b01010b400030300240c00140189020340d242c41c1c191040c8000d070819040b10601c10280b41943c1d00d003500d550100054071444800d200c2030302501e040c0112070300b280402c1407a00c030002ca07201c5040c1000e44038500094008010b01c102d0344100354141c040036802b54002400811804240d4100390031140740881c46802d242e02240e1100b00380e6403c08104841c1c540c0180d0000400046a40e410841d040350a20280001c003c07000301c40700440d0b2001d00c140110b203080c0100011202035403441000e00c040107900404052804540500d403450000000803080d982c00104404032a01c200c031a90490381e50b00402e401a41c98041d21030985009001d4444001c4003078001071014141a00040c00380c40304284282c0d50b002d51b02c030000c106000c0d000300e0075040a8109464540501940c9401c40b0520307411207004240940c4c1a80eaa00e400020510000142e5a0f01410009400d00f0828005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 146189415 1250 146188165 146188249
    0x100903081005010806102f03030609010f140402030603030d020301080f060609070504170c0604180609090b01030f0c050a030c06030c1806050f0f0a09030b0a021215 72
    0x2800d81e458080d0344000454840318150b0351a40e0254080e000b81c0b1815000ea1013404516440d96206d4910340603046032104120310200d440801904000100034152030490070050141804064007101c0a080c008446180b22074401e065025940c00008501240c0c0c0030800d0351140740c4482000e6581c1d60311204030302d80b21048510440340360701c07421010418600d81000614415420ba41d556800c007803410284101c00d155401031480b59010782c00e050b10f03607916003000038000780c541e80f1444e82c11804121000c2041303500d10b42c05503000301e142c21b052400180039070400310304607900702042030002e45550802e08250709043d030040760b00480ca140b0001c200304000000703004441190700c04100c1c10046040c140d6505400014804030388074028024003610b03005401400908808500140c20700004010b01640c030760000c161013000c9600e16004004101c1c003100c400350f124080c0f00066040030700500b210882d1100141c0a404084103c2c0f80c0e001c81d540766260710400011001a00c906061800c11200c00004602c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 146190665 1250 146189415 146189431
    0xc0b25120801060e06030a0504031107080606011206051c0305120702010f0e1603020910031a0a0e071d06060d23070f02070e1b0c0f2a0d020310090308 66
    0x4800000c0c3d45402404400300440010f0320191a540d00c14050a00920300240100c09100d01400804910a410070070a40909080070090245040c8140050148903c22111503025400d004082c8480c3d2510094020003110500480c0c16101e000d14095035240503d501085d408034070380381000005681508040010403000c8010010086e1001c1a07036126810603090b902203060249041005041800440c1d81c08000f00102080268807a076071440003c07984440c507014800b002c000c0c48034550b010710030005505d07410703001811100c3c98041c000d10004482140c000039880d10b040010041e44030f0400315403201854030001c01c40794001299030358480d4000c01360a0802c810007000145110700909040c6040700f03a540052800070f1416520b20540c5000a020380d10916900030b4085001c1d19480c05489442c0081024000051901050300c1c600100107810141c100c10700d440c41803c00c01d1015400d41030000c2525a45207040382070010a141400c85509840d0182c9001400c00505500c40a440c2c040c981c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 146191915 1250 146190665 146190677
    0x71505040c060c020609090711100605030f070e07030903030204030c0308120a18020909010603170a11030301050604030201180e190e01020301052d0a0e04060b0d0c0b2512 75
    0x8410b000c4a040048400c02034110b002007000e618603180c80c106d01c0d54041410725207540c0d9900428111414001c0d00903044000e191940c1c030501c11450140a8034082c1c861100041c040b80c0e20b070054034034454074050070b17850078180c1d9910b000c8240f520075012100507541000305003143c82da50346070843c01988148401c2162400841c0890300d1400f20b406004280701081107179a0201445070204407040102600d100c209640c1d030350001002815809165045124414071583c503810900e8024080e00d4020301e031400303160130810040c030a65440000351800c4d03903020302e440080c9104a42c142c61149159402144074805010304001d080d240da80c4652001c8480003001380506804404c420703090340020b0161960145c0d940d0325403a20f0f64201015404c0c40c282e10340302809104415000b160710715240d80c000e08404401c0e08108000e100890164004804069401072030002c5a510364807030703d199500408410302400030b0340b004240c218090011000e00301110981c070303c40c02d9103441d07030603144482040d0b4041a1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 146193165 1250 146191915 146191919
    0x40e34030513021005091306030c170105130803190e010e010b010e0a030204180b013c06050c030d02040f03030206090304060903020609061c06140f010212030a02071505040c 76
    0x100240c2c14998480d400340c8480300440c1e22003000e444c190890707101c0c250801d002c0d40c00065580e2031400350000450261b00c10713600d42c5040020900081100e5004c10f4086c0e0706001c24045c1070018400b0201002e0740044040d41c40b2746903140300c031a054112082400c2000d0078010898400e0806500244110301c0c1300b0003c00c15024648015683c0038005030300c80c0d6118000031810005418031b90001d14600e12141c00b148826005030303884404038202a041080c01030847c5040d4101e5403e95074810714901294603c03591140c41030482c00f50300c2580341c012503003000340101d03240818003410001e48012890b4840c040d510365840c1c1c0c1010f02c00100a200c1130380140f06513004101d0f070240c048125000e50703019070368507405181103401348070b0035900845000c2e070064820004050b40f02c81e07030000e14134072086071180070031a289450225901c644a07401440c0c42016000c010a40e60380c1c00040c0b00d1402c43c483c0840a49139910748001070300a010b0b010f8081e0107111200c80005000109910080c0326611030411180129 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 146194415 1250 146193165 146193181
    0xb07020d02121b15030a0504050a0210021510151d040e06060a060e03030d18080406210c17040c030b040b070f090f0b09030705060408010b01021203070203040e340305 73
    0x7440c5442204400070170100d491142c1c10341145501074021422204215034650201d003400f00e06407582401600190207d111440504c09884c0d040320117100500c07000c0382011404007440703003031461031030511a080d521980006020324119451002c010400c01005001052954580c0c1007120704520420340d250010900d1030080380701c100703200700140003103060418510403207000b0300c2111054045d0441442040002803440001000502100e590780c12000040f40040c4d110781c00c0c021580d00d181410111900f0205501c0040e200300440d040a03828003035200d03403c01e0490901580c001411102d00c0008000601c0b9034910740034000e4059965040c01403581c154115078180c0d45028080e01918401c9042020080c0303070307000e0513018000a042c0d4600550b50030020741d580d4050351112610342d454019050207980c060154207048131484c05c00034590310b40040c00a40f2031107540140030f460f41c10b95020810846000383c1d214550005011b0000c2541200d048004000c909000b04c100084e0030b01c40003d043c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 146195665 1250 146194415 146194429
    0x209090109231f020a030f0605010525080a02011508010603111203090306040c14060711120a0501050405010213060c02030d2a0b040203160e010b07020d02121b 70
    0x41d8011030340c000a00c44400c60b5006000c40190b4201640c4101141858070300c0c00303200c980c610300c501200d006175240c0610001500b80d81141282402c3e40e0b1826008125990f00101100d9103100000450794040c40c1114000f40c44240c000b80150041e400800d16408440e01580700700d580d03a40782d60442900698900c041c600ba00e01c039010040090090465641250030002c0301c409941030400c05034be003041500b10110346044011a025103001218400070800c020a1006d40e0f044d002041d02d12503d0300c00c1c02d071501c5103580400c940b810f0090305400e00048104d2414007a00744040e0748040280310a09081c2081c0740030390082c044994a110101b2070011b00140921a00034225034080c02401080320303205800c2c0e0b00c0c0c1c042004034803110801490010f10041c0c0030b4009283c0d403480b03180d141c41981441c0c0181407800060005440e0b01650550302032080034410f002c0141102c0c044403480360344070400e04c04544070705800d188c020740040d4080c440c500c0c1c025010a221008000c10307440c1c1085031804d00c04000c05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 146196915 1250 146195665 146195681
    0xa063e07080d060816050411120606070c03020901030303050609131208090c060703030e06060607020a0311180a0c080603060c04050d0206040b070302060703050108070b040b03101a040302090901 85
    0x60008108044000a401c5002800b81d2407541c02d0005989561041c0d150f041480155001d0108140100288030f1b03840c041c880d200c0c0ba00c840700c10a5060021a41400425003406803003e44144404a0003008000703803000903002469010f0a0310850b56940d240140c0074080c00c0e00c10911130b40d0302c1c00001325541101c125030600550040f0044480c00d00d2020309607041031020304600c3e01401022404800c64440d107005103a440d119582c005118045603541c136041a10141c8041d00c0742c4810094140545d50b2071001c0c109030707508800014800700380c1a001858884140ca00c7d500d44281712000c12072681c0c02d541c8000009605034541e20780300d81d955410581c488404580700c0010450601041c0000d0402c3d55200c0e010a1001c3c00e240d240540b17420990b001a045041c0813001640414100004c1c607505004490040034a40300030190750b400d1402e480042d006900440c0200500800058040b456060041006001411914550b14925412500b00c1e50040c04268080c69803032010403e19503051044441c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 146198165 1250 146196915 146197031
    0x307030503060f0a0312020a050c09090718060503060103030c030206060d0b0c09010c0206030f1812040902090102030d0e06090c0913022e030b010909090b0f06030a06 73
    0x100d59a40c0000f00400c401014960030742015480c0d10200014170950040c68201c4040e400a0000c16454600076282803d4508100d001c2ca50100521407410030004e54202650015024285240030000100000342000e61090b036041c03044000000c149078010030107204003030080c0d0035941c06a132a0028888650f02c0f00304000e10301d45c180e000050500d600480548001d500500d400012400e240c0c0000303203160401d60300c1d820350708411014021b1100a03200103203500081301010f0841c1205130b401746040c9005900c02c005080f500003408280c45d0b0301c24021200419002c80f02000300205c042119690341004940c1e80c0050f120300e101c001568501130801d140324021140e480f0b101e101d0280c1c20f103c04102151108030842050b0200d440e40030090100150a03d0398540d0f000400780d183c40c0c001003480080754050a002c44c6004044008920120b2403d03034800e80c0041010b10301e0b101d80c400310b4904a441200508294505070580303a881e0140c5801c1c0c4020482200d015001600368407400301420302c11060b0300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 146199415 1250 146198165 146198167
    0x30f050f06040221012303070e04060f0615020d0f0201181214030103082d07061a03030408010219050c100507050d0e0105190b0d030509190b0c0f03070305 68
    0x240312842c00750002d15240c1c0240702150040003038480f0240c0440802c0c1c02c02c850580301d00c0a200c007a444045010010140110000d01e5014540601c0610594000d003009c0c00c00d81d190300c20f001140805400c80710061054003c2412140660700000b51151003040c11030001508414911403205d00c1400350316008014501d200700d4043d10b42d0703078514814100c00c0c1203006001007078180c10040c20611f40610300940c000c8100715624100c3c1340d401c00842d41c02e12080034403441600145044499000255014150302810004030350300c401c00459894800c0c0015103506100c0014040b48209064024001e0801d000b0399514516040079400d88060250401c000019401020820006112030308001e40241660401d1440d0601c003200d080c2c161024403441c000941e440c2c005218034010007518400c42c01500a004000d91008040021650301d03801134081c0c108503000c070b008852559050009108030004d00203201c006a0ba80070952090740014025580718060141d50806901c40803044510743d550541d00c0c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 146200665 1250 146199415 146199421
    0xf0f05010302221e06050a0507062a0903060501080606030a121103040914060405040203030f0f130e0105120f060a09060216110f0406030b06060703022407030f050f 72
    0x11002500302c000b007502940030f1054510304204121140c04094080040e8240300844010f88079140400c00d42d1089041040c01c0251851941c0c0c4401030328607a0b6880b030000b1885ca91b455181611000310a90285a01d0080c0041c0c07100300383c0c00002c0102100e00c034035403e0115a9a4102880d19900c0c120303520f58060f00b15a9000e0005075001c1c43c2100b103139030b850800300d9070f00380b0005d601403860300107030403054105550b4034140c04d440e00c2c80d09640c1ea10080403a414801440c1c5a80070988a005075400d04060013030202d069455010480b0561320050340f2412012030b115a0703007640c0070200d003081c801c0d6405101c44010380403629402203040d848009441c0b0041c0100d0300c0302c2c0d51800062258140994181c0da0904c40c0b0003e41c050444003094080c010034100a000c01000f0421034043c800180d0340307100c2c1d40ba01000b007000401c88020113030300c0a400c0341c04544400d0f031410141d0074050068540d8401c40c08046203216a03408982c0018000c540940e0308110707208511006004440c3c003503d2620401c5082800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 146201915 1250 146200665 146200667
    0xf061a04050618120f0d0305060f030a0b070c0213060f1d06091015090603060605040e06040510030b0f150a03031d13020c0304170d05030114030705100503070201060f0f0501 76
    0x1142c5078103c0e000d86100c4070400c1074078220b41031030a030041d40382094004404845100b0340c140146500114100d030b2002c10400c10500107583d403a0f10450007407000c4040c50002c0d105501a034090341c8080c2d0040d10201c402036003400b144004000b80d01402802880c071032004940ca209415004003200f000c482c50445640b81c9200f007001c2c01100412950088114140201c4c05d0000461101284003843d2204440e05040c90009800d030380ea281c0000e030400c10117001c00c02c10043c8030561650411010788001500303459580c501d400700484c680002e060002c44000b0701c101d40c0410407106100351402009500d213120404100005081c2d01e1001500254814004c00d09440c1e026002800c004001802c45511200644008003a80c01c041c1c1c0389002030f00042020847e00c2c01e105400d0030300b0f413020400b400e014005010040d2681c001805000c6601040d0030040c0b08649040041d000a020010034500704041510001081540100c07001001542080740000d0a1711150f05000c09861a0710034117200c06080c200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 146203165 1250 146201915 146201947
    0x1140109120602070f080a030b03030f1e090d080301060e010503011202091e010909031b170d020c0102030c0702011805030c0402090117041b060f02061b07060f061a040506 75
    0x80192201c0390b08100800000d40103070b00100505c1e01c03c14015854002046010b8220341d01d42d10014007035002000109401c252074000c9411a82c110070290082e04461078004901d40220408540c00540c03240481051046802c040c0d07048400c0c03692800b00400390380c801160f0380d01003072284070140c88089490724010710f40103014942c401881c10345131075407c011010036022600300ba401111120350783c0c081d180515a200c0344034000440c1560004108041036680d088001e06080a00220031601044007211035080c1e40444811740318900c003e54807428a40c2580050358803404c41240450000c0f035030810468804920f10303040350b2004010380450201c0703109000280d44081d640b5130400c1514840d950010345041302c01c0e806580038145941c481900060044607551050700f020b424040c0800d0100b1b0545d6000a0580d44034800444541c100036481c1d10210f0203008a01004240300e041c04011300c0807802980c4900c0889075441b104998800c0581c03181041c07841540255500210100081d0310300c1d822480e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 146204415 1250 146203165 146203199
    0x3020c120a0507140a02130b120303150d1407060e0901060e030607030507050c0a060e01050c030f0403210f1506090302011205040203030910020604030921021002010e0706021501140109 81
    0x1585c04041c07156000a42c000b022000500442d070b44c81c41000350b50f04102d07a40c0801c10404400442c0385041c01000c042d125151010881e00c03e041c61100d8800b0000d04207041c00b91142000226201c0c6c0792039607030240000c404001b049001e071040300000281141f0841c0c080d4003100016002c0d20b859210154200c0103054001d1400d82440410484032400ea907007000213016560140e940091412814941c2a0948102030a00d410045043c41841405e401400342c1503009585810400b10310080c40021009042a01c40303401d8540e1b00e40b01001203103940e26044410040b000c1c91148890766101ca0082e03800e40f10f5804042e0000b010801c2035406508684d01458105000400b100e0402d458240094000311031468400c00681100c03003030200705600035440d03030042c010007400003e905a150300203500c10103203070384041d10514080184014042c001c1d0b000c4070300e60b0703180e8050b1440309480c5d2101940d03428174889044070140081000041401d034800c08040204016540d601800b8a40210b803c441c0c1c501e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 146205665 1250 146204415 146204453
    0xf0a080a0204080f03030901050106080103020901060c1704060c0c0605040609090f060302030d02070f090c0f081305120a02070812030c07060e0109211e0f0207051003020c120a0507 79
    0x8000c0824203c0c03003040b02115102900b402155203190903a100ea0035034030103a1001d400c1c440e0110040c00103940390924541035800b2481d2410380c0d46458204a82c611482da94000f104503000540421000d07404410300700211b000300e01c0f655541d0f80d6030f40100c076284a948510030000c1d900c45000d001d86280c58100d80e81c1e81d0007141d008204242c50780c001034148014442c1d8000982c2c8034040070068868900a00001010320207070421503482c44010107404001c1c0c1c44050400c02c00510002b400c2d03402480120300c4800e40207000c5a403503034140c0f5001c031160b6220310365107000341c0f0404a001402c0e030000a003140d0f00303055900702c45007182c44032208026036401404089a407640c99130f0100d66402e800344552084640500600c403084100c08600c8809240070394140e200f08900c005a1340006588050707d403c1c03400142c03801c980043c10b0240124102902c64200b154040d00f58103410700880d5040e00a41180e1011300c0590740e0601d000000c05000b48a40401030740490814016000401c640c10070b8110ba40d115 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 146206915 1250 146205665 146205667
    0xc0f01140903070b04061805011e27090b0a030f020108091005090d030e06090a1106040f09050702010507020a050616170406060e06030c060910200601080606060f0a080a02 75
    0x241002900b0000f258000150440d400714003001140d6100c1442041400c425520030281414980000e10304462180c00000c04070084141007909446842c0c021307201d12000d14880b402e0030b41c1d601800c0c105840c5118404083d401d090317503401e161522a28000c2160f0740b1107144600010283c0c010740d41e02800510901070340c0285040804e01c032031240100c0b441910301d0800b501c010900e024016003110f01d460201801d6034800c0040155110340000c000154580040070041206011000038015110711f42200b100418800700000c4c41c1c0c2020f0300484d005590640080c00903954105080381d80342500700010f42030340e0101002c07841071844d01c0c88140c0626600d14140310b8524101c440c1c203041300341c142c40c1101c1141d2b4464007000703e403010010b00d68003d1001c5004e410301c001c403c03002590f41c0c010400c99a100b09000925801d820740528851400c085910503818800b450340a00182c982c1c409100c1e20196000e8580044c40d14a00202100c1039414980c0505c3d06100000308120750f201c000900541500f030b4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 146208165 1250 146206915 146206927
    0x61e0b0d26040f06091517060a0b0708040509090a020a0603020c01020403171207020106050312160b0106080a0b010e13050a060503070902070515010602120c031606020c0c01020c0f0114 81
    0x2800004101810f808002514980c3c0350100040008201e94069610002c07540d400a039034540c41031400e0500c1102c17001300c109a403958000034a410903140d011480c3c5550000e0044100812076001d0300c225842182c50120795903c240a0175240d019001000f0360140103000c007480958001d81c05022100703882e500060505031295100c04c080c070109074460410f0503000c142c0e00302c0c29400e888401ea2140e4144000d1001620f00b5000c25a40c010204408080c95000301d81485003000008010700c2450b0805a05a403075690344102600302d0304140c90100303569003080d4000c8681e5000307a0445810082c050708142d0f4030070700c0080f0b00005000c094a60618079407650b1b40098180d41c1080300f0303005000030400040c2c1e83c803201d18142c4e2411602000301010307101d40000400102d90041104841003080400c036940c2c555141c8481c505600c64002031400e183c5159403030406009055010f413043c0c1007420122000103503600d005907915560080d000e5408016600c102d2a030754401c120401d00240c2142c1042d083c45 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 146209415 1250 146208165 146208233
    0x2121b07050a1d041113240503120c100f0e1002070809010c1a070806010f0e031005041e03050901030e1f020c070302040911150c030a0807120207061e0b0d 68
    0x84810406c2d1485500c0d05034040076401c010f000e070312003c0c000d90190000c0a00d0310000c25140d500700034020410010126142c050400240103409800307202460030007007240038628890060007269410400303445039074071841c4e0000d01482142c20003a040a0040c1c1800001001104c40c4000304000722464400c404114a1491604000c10701440003038a03032000500c0c0c200001042000c41c418040208003000071400c4468401041041036484442c00c0440d03a541c4c5c60400700051a96121041118110008083c0030700da8408090420000240c0c0c050103c50100d000d901d903103021007208030383d101ea0403642130700d1448002d070300600e03001c0780850566100e075540f07400007011590035510503101780c044400c030700806140280c1074a001c00709074001d4900b002d8008c1c4a1554a000381864034090161f00008a420103009603032950409484040541d5100154608040038004a115074440c03045247c0f4101032507009070151080d5914081e0003500e2004154460043c0041c425801848502c454250903450b9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 146210665 1250 146209415 146209429
    0x17070606150215101a0c030928090605090a0903020c0a0608060307120f0308061c0311120313080d0b0612010e090111070201030c02121b07050a1d0411 66
    0x3068503a00034010b0700250440d2200400f0300280442241c000605082c0506406440c2040000001c0c504154482c800000003525611810060541c06056080502c442010f048581c06a9481555042c80010745d00c1c03441c0d90644d400e034051241e101c100703000083c0c42c420880d402488443e0083c0b045801c0c100c0200d001c0380312044550022000141040c0400000b17044c00c01001c00102182c0b114001c480d911a2140030451352984001800c0040d041701103803d07981e0f0401c0070000881040c00515031100b0600d00508800700f00b640c441040d008001100c001180000c068902c80c112030082d55205161540d964007441d4442a852006c5d2039540b02e580c142500e64070090122400c8040a0165a5040c004c10880400d00217010300e4180e8102080c003014008503a040e14003241d42828003180c11032004d035080e03092500d103620820910202080e100000c52000400100c4059001c0c1580d200381d40390001d10020504074041d0342510100750318041c4074146075880c1c495209008141141c032402041001440f4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 146211915 1250 146210665 146210699
    0xf020d0b130c12020a0501051b01020d020a110a0b0112030201021603020a03020f030403021f030b040c05130501080c1812190c05010e0904030e030f060f101217070606 73
    0x2015921468040010b80d00a81000e403048880d440030010082d4001090040039002d114104680442c0303980c070b1503001d9142c101c2c50040d100c0003903444021900080c002900b00030b1114000400c09000c4400b40000482d1225040340c0100031132180b68244494a900241c41400450071594200700c00d00c5101c100c6075110310035522a03806060101c19900300245001940490110590400c01c010801a0344062011070101e11040e0b51119107030320307200141e004014080c14a500281000500c1500551105c001c1c911504024804201c0c1c3e0b8450340110707590001182e010794820010008805103006800b02d414500780c00820040b4202c20650545050484000d2402c030208210b049810420400c06247e101a020a02c3c29990105030714001640024000d0300141c18090901d031811034139241807018000007610f03201280c0c49410b00a0b10110301800403074132000a440614004243c05c4010940c2025440d0040d0282c40c1c40b00e600240302d404e6900c04c8000700ca10b0360307035080c001802140c81141066 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 146213165 1250 146211915 146211931
    0x9043206010912050d0906080c03040618050a0b0105030607050a02060c03040204110408071809030e0d0c1a13090e030409050c040509090c0103202a07150f020604020d0f020d0b 77
    0x404801300b0a005406d1110680110080c44422800c02c602864003006882d0702075001031020411444c945800355925200303890240c40d5004011a5000f4001450f80303450407143d00341e08980c1540d960f81c0d000c9455008032000e600060b04001d01080c6181030380c001031600030303000600006210162000d6020160320035804103800b600721f030702c0410240701c1c44c80711204034061030001489400780703c1e900144031850901c2054071a59003480c1010a1241030301c0340c4005000707502c405107407450318480100c0c0349402c803038001e100604101c1c00c0407408008030f0103000c010341942802103040a00384100d0038007400d0001c1006441a0050000152075994540e03010b024800a101030300c0401907942c0014256590300c45a400c1760180d0b1800c40f4030044201003154950b0306400014030a5030413407200065020b60041401226206441c000301750701a00e034450620307030f00e40d031b46601d2849001c0315003e07030f204c0c041200d001e03511000c1440a003001c503089030061412039200800344440000300c0d5403080c28202041c1c030344178 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 146214415 1250 146213165 146213173
    0xc0414040b09070b0d0903030f020d020904060503030406091a0904110702120705100e010c051608161202120a140d0f02150129040b0904320601091205 66
    0x30900c01e04400040c1c01400401c050b00f000e508011030755503a8407811481c02c00c582e43ea65800c40505100c0d81c0440c160000c039410640d44c911408600c1c00c065080840502d1240303150080c001600e02d4000304a900300c0396246c40754000385140c0544521034018102d100c07203552804101c0309100360303911700c10540c40c2000441015240e40c1d00380180555507031202400b180e1a0f010007410301555440c803541d81d04042d03443c03416500c07881c48640101c9658005040043c00c2c0e10031180412039803034030800044c4c1500c3c1c50204032202900210340c8910307000c400c0d10900e4164003400b030b00303034002d402d0a01d00403400b0720b0300008a60207090306a5031b5090015a030380c0e0400203608961b0006e492280d00201c0041542201e00c01401c00700054003403068545018841c0c280f00c070618140d480100300540001000904001500c151515515015810350340d01102c641d174455894508105c1c09484020500e2075201d94001c0c800b5625242d82920b04895503000e0322090600134003450014014440c5905100d665200710090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 146215665 1250 146214415 146214421
    0x12060121090c0323100f270b100b0a05070602040b2a011a040513021f02070b160b040201051b030d1a030d081308030703090201120e0a0609050c0414 65
    0x484242d0641048031406030012944080d40d2040050704406a0351420800240080c80a100034000c1c003801f68225850640e0310b01c141e90f20340104051115681c0111500d4046940d015207006200720315025110045c101070204505452080300a009100e2191500510f4181c65005203081c2c3c0e041a1280084030303124a4250b46c90f81844c0f400380e0041251300c0c00038040c2c000040070107560403121000041c0516610380003c2c043c0d280b1440041c504980181800b4180c54001743c504541c0524903407000050300c110f480000b803040449040750310050913940c0448001c040d03035a800301184405001a03040160a008091486d2040a007002030035031107000031661281c1761002d10b41a102d052080203801058040d03821281d4a011810b580040361a1030315001c03950f12250b544102042c02080036002900100030070810503003690014040314002d80381c00c064180301054900070741303400100808145e000490b030b500015105400015041e0310400948400e00c0c5030078081000c07a1010207040816400312814 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 146216915 1250 146215665 146215673
    0x70b0417010c050f040504020f0f0c06071e0909020903120f091509060f1c0c030e0f011116020a05090702010b01090b0f04030807110d050601050109080312060121090c03 74
    0x80d0b10301001180c10098108400f03614041e845006900c6201d0084c0d800007900390424441c1e03001c075071132807407948091900c4d688009503983e030700e810864401c00442c20005100c400da0f94403000517003040c10981d8a11000c5401c003184d400103034000002458040c1b14031821792408850359000391000d4030300d0202c215114000b4034100010349540c41c81300b854002c810465109962035800442d069600a02406995040b040c1c00000c0b0459030f406400d00090b1509080e03070203040e410b8101d03911504e03e402c00c447e4604200700a0b00d080f181018071003206000c04019094440c004c01211008040c00200040c070042c3d5641c001c0341401c0812600000140d5607118803410030b6800400785405000d8003581e941c10041a01801c0c0c80b10310407808043c1c40c000c800320313104041011020b160800080003a00c5404200c0407031a00d02d990352428090f05010840040780452024400410340d41e00e244400780300191512080010750310249007450034400400484048601d01c03010b406074642161043c05a0b914107851424 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 146218165 1250 146216915 146216921
    0x20f0d080405071502120d050412021c0e0105090307030b06030f0a030906080a2408010e0a02090408070c170c01020d03140718090c03050603010b010e03030417070b041701 75
    0x681005000460052002207100090201d003640c2c2d80c80200407018901d0007007a844c045070b07140c143c41012400a8010070070040c80d0440c6001d1f503c01c00c050411800300c2c600598031466aa00c0500c03401c440841c040302650b1240307126030301c5581d060521924021006010078208110381e04250f5500001e0030030700126050400484c0410301c1d070803018004490722030350000c080c440c1d00c6c4030b12001c205900010414086003603200300300d01c02e0008000c2010a1070440d18118101700362003100c0c4075500c0c005030549880303408079112801c0340d030003450b02265030340e50703910034209130840f074400e8440700766078840480c04186038100b07a100d11444a0050444400c203100091a094000500408050505001c13800014100390309542013184c40c00c0c90940410034044c600d0780d0701030503032004032042c1c01c3c80e140e50540d0381c040e8000da0007034400390001c0c80401c0d0010015969050034500705501540200410003400d4140d6140400596483c020349810940e83c00c130034800ea40050b0007118510040078117000200500748 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 146219415 1250 146218165 146218183
    0x504050c0a0605040b0a0e0d03020c130b030d120b0306011d010503070e06010c030e03060c070c050d0302031c1803080f0709050306061215150a210305090d0b0403020f 73
    0xc1d4628003a42c24004010400e010700e02c80c00007158004920080300d07038026418071070610b50103004082142c181d418000d40d40c0c0c15102c03442c1c1c080c0e981c0210342040c040850069007100b100181c0105564446040e00b01c58000143c120020101c0d9034508030f20320355506201c501c0c02041e1640706074081c1050200d45200010060344201d200f5070105d1130030015092000305903035200800f42810505c2c182d103402e043d940d001d06060f41c0e0ba030501600003040024142c04014003c4103001c2d581980d40640c80300306000c1036109a18010700903900620003060b001d031008070b6142140c01820400700d501060854029449503050030101c0c04200c1f1541085903940c0c1b030410b0a80e1092540c40c0041c50b46281a001c2030300c1c2c50001e03040900480c2803164000480c90708210413155000c102c10a5640740ca44401598410b10010160304d00c60711060100040c4c01003c082100b0420078542c0080c0002d000591781660300f940820f0315903070800c0d0800800030205210b60401482a0b002c3d0f000303010820800c192042c244400d40c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 146220665 1250 146219415 146219419
    0x62603030601021b06070c06090f050307030b0a0b1c0c060e040b0a0533030411060a09060806180703050603010f0908040302190b030108030915071e061d010504050c 72
    0x600401c00700303030790000d0041c08045150180d18500341d821404646103200d2600050a040c401c56000916a41e02c180d00c0c2d4104c501d028141c00c40161214105a252100c0340300c042e10641b5444081510801c081d80a10782924004266442c0c00c1d502e043c1e804210b071308002050350f0300070300340204000c0e20390000e0320702039500003c4804125007206440060991413050081d68001d11800300a408110080b84c1d22004a0700550000020300c9005c03050400154000c88d42150840c41800700c0d02c84908000040c1d507214030f41ca032a05058030741810750440713400400506040e0320424444202c8034080e48030b40003a02075000c07031b40e01140d140380800500d400c0d25040310404800d04e02e400b041d00041407100b02920180d0f541180c25130005070887c481990048403942080040b03142c0000006140131001004048503402501c40c102400c0120b4520f2245005003c4054550585100522810011107002140840c45141c0c002060300c1c56481c01c0e8916002d003040500e1580d17403801071005004041207051a102c8007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 146221915 1250 146220665 146220667
    0x80c1c030e010f11120c1b01050411010302030c0a080901020409050f1f06020703020d0812010e16050909010b0c250306050a0c1b0c0b0a050712030606091703040306062603 75
    0xc04030b00040c13588282c090040da900aa04081903240c48000c0071220b041d1251f40400340303000c0840c007019009100999007125098503121030410554007034000c2e20302c41c0320544401410219080c0d020380c0e2003040204840b030155030811000c21518040e1107600e02440d18004d00245501e0401440e03680d401c070303104a44080500100003040440e40c00608001540c1c3d045d203040010030742a01d01410b09020340290080d611460f40b00104643c400300c000e6034440c002c00843c5206054240209039410703c944500c1030f40240910780144039a00707400c030041903801c0c121800c42e5094403040c0d130008901580c0480e4986182c411031130403c10b0190300e0144e2504490802010030486110740c1c800340800b080d1000b4001d60420f0f402d00c0c001400085040c1c4001491441c0c07a80e0b0707444c00d0a2000621507400010100e80e04050f035150100d50b107100c1d101c1d500a49500d034030f0311031819040074850000d0a245480111032840300304070100000d4041e005410003003ea030490117000c00a80c071203842e0940700e030b11280c070a9a1b01c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 146223021 1106 146221915 146221931
    0xa08010501171009030e09040f050114011802030613180b090c010813020d06020f04051201020a020607260601090e09060906010506040e0103080c1c030e010f 69
    0x3001020f85070050003015120b0100c80c1c0c1c407030000d80018141107407100d05050030f442107900a400303a02d005040c0c40307165484909480500760381c0011034201c0c000403c250000b40c81441c460940c070243c1981180790180204041444c0c0642100c00b01d44c461304900c0708960b90b02510f04005400203400034103480c0452105943e00c441c1c0c562540003904100002e1003554079030303481e407916590017400084034800a80781c5602035000320055041040d001c1000081c40e03500c040b00321850812600025841d00c0301e164002c0d040c194010040c1051001d00386d06c1c5209043e00e020440411000300060761181d032103110049070060401e030000c116401c100b01c28000180030001302d00e0311900d80c0c84102c4403c0d070b0700c0b4400d0020f54007841c400c040440340d46800500000b000c550143c1104e103080400c8a01d2030511540e00b5200b480c001c24030304042a9642010b28401400b0b000340300d4940c80c3c0c02c5007400490 = true := by decide +kernel

theorem cover : BRFrame.Cov 146043165 146223021 := by
  have h0 := BRFrame.cov_init 146043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 146043165 ≤ n) (h2 : n < 146223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
