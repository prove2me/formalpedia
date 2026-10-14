-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2407
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:37:13.477981+00:00
-- url     : https://prove2.me/submissions/187c95e8-e1d3-46af-b3cb-355e766a744e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 432733812 ≤ n < 432913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 432735062 1250 432733812 432733849
    0x70e03030f0403020a051e01050304080d1524020304090218030d0e1905090403030b1f0807030b010912062403060203100504051510020c040e0102130b0f0306040902040605 75
    0x1003d10542c9442c0c56038070000d000444110700188018450800602d2600342200c1c10303c40f010020a0411240388240c40710f00500b0f8000b000b50824100b00868082480e2042510300d031401c2034200c000125805422401c003202e41c00840c60986005441002035000d0040f54119280082002d02942d03400d0007038155541c0b2980e540011140c440c000c0000340407000656004030f81c4525401c11903502e40b140c10690064040c203002a04150f420085618003008a40c66410300005d0b021130752410303410481c0343c0d00689140e501000307040c3d555001598500c809010700700d80100281001c600040c559045056041114030218100004482c900c40c40ca100d1a007045415680103c100a00049071500c05802480221018030079410b219000386a00031042a80900858144c803116003046d008212254840202a00410024210510860003504180880c00e4049802800001c007442d80205654591243d00e960a05d0341e120801008000e2428800890b00316880381000911560b0724900c0c180d1a260a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 432736312 1250 432735062 432735067
    0x3030903030114090702101802060c060405250e07020c030601030c0905060604272306040509060405062a0f072a0902090609060c071409011d070e03030f 67
    0x140c4008001c800905070b801004d0807410082c005070300003100240740360803071070000389541e42c0300c54a2464094842c1c003a40005002030480740d1a000003d10758402c60050060315100b47c065403108402c0c014a2984131442444190140020503180b00e009400c0800342c0100d0f800382e2000408241000b4099100b640c804980f00000c1000407094024141d200300e044501515150503c821030103507090305640d00b60500310f02e00c228012034040c0d6105482d0140141d00d01240960040411240020201e40460003079040a010a141000008445004680c001c019050782c0d40d541c9155040d034448014412001040350b07400c0345001e0030311802004000903045070182d07200c849003001c01100f009001c030f06150b001d040c2076004c0f11034050326200040e0380a03c90301680d18581c410001c0d100d0301841071800e41c4580300188140184c00009201d20072121812940c44209280303034100081614244902003841189081c480c100d440740c2d8000c20340c4080315040403120340400703601080c07131034002d901310b0094804d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 432737562 1250 432736312 432736319
    0xf0406080a050105010645090e10200d140f180706050f0d06090f0b01021002120a0e0319050307033608070f05010903030b010e0306010b0901050c030309030301 70
    0x30b0003405c1c0541501c0c1400c0680b10f44024900445207001c01d0014032450650540c0441c000a0411520303030020f01c1020014410b0b1100580030007064604025409407003003103044042603a0502440d060540f0040703c94941000b41e4503000f82644c403103001c46540d83ea40709001241c2c601c150b00624083d04900d12000c03030526041c036428002c0540c003984580321b98070003081088181d2380241156603001059030041c0e00c625091080c000a8a0300b0b4002e04083d9003040002c0c1003042443c0d01130481610240e0032241c00d2500b1982440480c45840d401050031218140065805811900896184100720003202d1500c7c0380108030050210320840200000360001041c8404160305000d07510b04d00c402c40030044040c24900c0191040c0340880e0100300440a0741d0042c800a01c8400b03030541d403d42d0381144081c3c04603202450102c0c003c015801c000c4011900e01511498a03503c6803201030180d010113401425240d091820b80c22940d008640c9075410410200086545003606201441c0940020402542c4a505 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 432738812 1250 432737562 432737573
    0x10501061e021b060a030e1209030c0904030c0611042706171005070c050d0512130b070e1309060e07171002030703060b041203080901060f140f0406080a 67
    0x40310100c4401c66008a803e000d0010140c0c0e00c040121100320783c1d0503950422460254064103404942c00e07014080c484036061030f075000c04010003c059040f000c1d100622411020000d865100307440180c001032820341c403500054207607406070ba000e03020310347e9240c107043e5120b0a50107104405840d040c9100781c4c4126000496440f402104d0242141550200c1e01c401082c10762903444100c2c42c0007084060f00c4030086000b090091191040090300007040c0d50643e00036100c09403080d071280e00e849103c09140d81c0055072007040300f1314201000350b10070090103003a19040401c0f44c40074229010598020324600c00d001c1102520720550710741031b2044901241c06943d074840c00b800e0480d0381e4041044c2240b200004480708030049050995022098001038594680c02012001807095400000407181c0000300461950581071154001074469500c01d0103542e10200c6182c01ea0700203200d255840c0c88130420500c6a1808413421030022800545a04c0d10816800300280c00e680407030340203405980005007003105104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 432740062 1250 432738812 432738857
    0x1802042d0203090c0105090f030d0503090d02070f061d060d0e010f0504080301032307260d020d030902120a0321020c0a02060a0c0b070905100305010305150c0c01050106 74
    0xd18508500b140f804064590325070302c90361565810001d002401240984d9a03580c9210050005412503025003200c1101400c117500a0340c04071b1b2148501000781000a100060305016500304400140e28546000e105a864950080001d107032012904400d4a40e900e601c0d020b0301c20a40c00d020003244e080b10700704482d4211002503903c0f10610b03052208100100b9001c1080320b044a9002401295603091100400000d1480703120105071030040200c00101e032904c0c00d15aa5211040d03101281d140200007802503500c0c4500140400903070446d000c00c09405000741c1c03008c24540e00242004484c40704c51071110341803070a610030171000300704141020035400c070903203000c7d040d802d50541003140f0300b002c44031815a0396035010030024031074000001d0b000c1d5924400c0c40c4140c2d03140e600c0b5001c0411401c240b200541886520700905000301c040d000c05c200558800e004150407039400001400e40100c100065107500040182000040102004080401c0c1424864207009012560741c80c0442810002c440f010340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 432741312 1250 432740062 432740141
    0x31c0b120606180c0c010213050f060c0a140a060207060c02060705040e24180f0901110d020703090b0403260705031c06050411030117071206180204 65
    0x258041e40070410b071038a80031035203010780148041c0d8a0603681c40d10140d07841840b4184402440313500101d03002c1c1000e2106a070000503a80201e4405500d59184010300c50107000b407211000665109420a5010400003025070b2025450300c01034a00e00051030321110140d80c015217046450f40e0b518014a02c4650341409042c1e0801c11603c1c01c103103020702d032144441c054070004d070405043c15045910040310240b408103555001101a05031400b40384d441c21842002c072000c48800c00d1502544000641c6410184a4000c4040340c42c6069410070b1010100340300290000b000071014070944110104815905001501c020f5204060352812440c6d4003130168044850140d500c140718a0901400001500101c203542c001c03800400d0000c2c54052500c950400f40503d0350119401c2443c01e21183c84100d40d8a0096040c2c0d050069010080e6490340c1c2c8281d900c40941c803c881c0076401100c1c01100282c025000701900d451481040c000100b002d0f000503084840320580b184124440e409462081e440481d240e4080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 432742562 1250 432741312 432741349
    0x12040f080106150503090c090103060e0105070206070219080706091b150903080d1b030c0e12061b2203060e0105041709150c0a03022b050a02031c0b 65
    0x100341c03404407002c0f50640042d001030305001c4080000740e41d46008020210101400900400386542d5900f0060000c0c818481e07242c0d5a0f50800c40050310950000130344030b00500e8039600500c804884e010055001c008050710440304914104090350218070316001e003600040c01110010504940030b0100341500c9411381c8140140c02080d40825202a0490944000c61fa004559159603004500207007004242d083c0c292400c0030604404481c880e41e06034040d01070000151125084001b20000f04002d41902c1e9000102590081c40011035000050004401107040344810a0420034240708140307034054000d00c058445410030101300248130003800f03110204d08200c00200300300d08003911030310b0003d1004038070f0702c051010014629006448030303100d040340320350220384e525280d692034a03200c4c1c0c0795610504282c0052048000014040799206000340c500280300105442c2420a04030070b843d603070041401241507000a0141e1581d501c2d1009010441c03410000001a060106404003d203038090081190b94 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 432743812 1250 432742562 432742571
    0x22107020a02150c0c0d110f01030506090103030f1103120f130506061203070b09030a0921020904031205040f0203010507030b0603010909020a12031d0d110f010201060812040f0801 79
    0x2580321000f0f0502d40c2e054403103010707075a4280c001d01607190030950780900e900141202e060600340708072100003d00e020411109040c446400100440c01d98506980b11a4060301c1c90004200090081911140a8005051110999070310195142c2960020000201400100c0040142c4541841003050380801241c5032040d00102e5a00d59558030b80300100514003800608515142e905000c00a44031590392144000305035107811410f4a48a8108603101004111f2070800480c2c00c50b0000071451b0048410413081e151001140c00300100baa802404c1a4140200c2c00c44149405040e4064148513a004a890796943d941510506085560013400c040406180100d080782940e502e030200d038115908202c010450a143d400000c400c150a58040102d800300c5400200405800101c40100c041c11044178543c900ca10106104840b107a40000a048001d00c02e03080c0030318a0050080106e9540c18400080c005850750400307454280c4891207000d0b200d001080801c11080a041d0890143c203002000b4403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 432745062 1250 432743812 432743833
    0x1804020703020c040b13060305150112080a1b020901030602070b06010504050d0206030c0f22140607081b0304060e0a0503010612120509090a09060b030a03080c0a020109020402210702 80
    0x75101d8100711001403180b03840310040751942e46c0708070710b680802c120940f04002180d580d1501d50380e0f5a401d407000e00001442940005032203015842030081c031a4200c0411803904040702011140007051088030307041544840a4040540c0301d910030103000e180304070703030041e9120320f2800c040340d01020050180d4100081007005210310f844001054581540c1507449940f00c0d1250703550701040340903142d03410100c01c5020501d450049100c0800304199424591441d60703040e01c44c10301058030a501031425030801d6040005c2c1c8000741210008040e00d840e100391b800048103155854608650207548144002000d541787c140040c50821051401048120001c200e6940780060b0000c00004010000d402041c00355002c800c5e4a0090f0b01b01d503440e1000600c840480e1030300703403684001800f45000507255249002002144c1d4100080d010401d26010380b2041203958615640c041140c0c0092055400c6540300d00b41080143c940b070000d4500d840300e40e5180642001c0488080060075401009481150700c0040700c1c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 432746312 1250 432745062 432745067
    0x7030308010608060d0c23040516090909170705010b09101703030906042a06020d0801091416090302040f0501080d02240403091206050f0a02040b0f030a061a1804020703 74
    0x104100c03034032440440042d1283c2c0c0007040b01440c7c184a90743d00b140c1040c0400c15900356411010305003450903100d21b10700640301c2407914200c51071400d0080c111045a1135100c03440e407100010303100c3c052040d000810284c80c80c1c40071411081040d9201c1d030640704210414803891410b407000070810b0f80801c00550540c076148044950700c000140026048076100111501e405609074003c0d2050154540480c021907580c0c403000f55113a078950800703030010f0000d4001040c540c440c0d02520244002c4c16601c0c05842c0c941071100152031340d6080300c40041c0700d10780d10000016141c5008100402d85218000034041d89050482c070b061041559494046420040c01c01e03000d145030482584803441d03110038201d416a500c0c80c0c03e890351000c50308009a204240c80d05031040281c01d401c0640319000c84801d4210545807842a04140e009a02401c41900e0b0b00340b01114281201f44c01640c1d1080b10b40d50042603030b603650070202d081031600145c15444c1480001d040341c000000c8010300d00214106540451402c540c54400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 432747562 1250 432746312 432746333
    0x70c080f1005250e100201020c100903110f0303071404050d02192d0e010b03191409010c020d0e030c220e070602010e150c0c010603020303130801110415120e07030308010608060d 78
    0x10110158bc03607101d84107141c40389007a500d01c0d41820084620400841c06525030702d810440708000011840c50b4a4000c045804d000d96040f5000a800804e80c18503e0b420442d02395650b4001800710070798400c00140b040c400c0c1700c0001181c1101040c2ca0218194449650042041d40d00720300982c0003040010400c0301e030b01e101265400799545510900c0c0b8802441d9075405081c012966800d214411f5081c4000300030706522943e43c000090b022140ea07050400740542e509500c00c90303401d5143d00b004e41403e2140c1413841d64461000c0c61200f004015801c0003200ca4115000c2288401442c0d1110500f44207441c0c0902c00c0d80c2c80310342c61400900c500ca000300d0304415082c0000740401450000441c2c0a500c07420300350003010246900a0036262105c01c09081610801080c7c4180c42e030640c282000300901c032500c0800c660682d00c4e011728a06001241d400b054a46c038851480105003655907107400701c0da60406011409c040d5103e513581c0b44c11940b50800c001c0102c40090410b6104030404209040050005440c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 432748812 1250 432747562 432747583
    0x6020f030403051522060204060e0301110901110f060408030618010f0303030221010902031e0105060a0309030c12120c05160b2a070c080f1005250e100201020c 70
    0x4ca0703d18507030f914401613802c3c90b039017100e1403049040c40154108122681d0003030020b4a030f15036a07440e052890b50303040500342c840818207840d6480d820003c180c02540721f0007000e0700008410040710100300d44034083c80e00d1300f10308032815245840044140013007803034010301a810022640b81007060719410715507501c3d0700a00620004061503070004a44126070382c80c841e15000074842071600c004543e0766081c0c1c90081d40c41110180c00341c0039503902c0c000204014200182c180d034800341c5128100700c944e080075801400c02039419014080ea607030048000515031072a03c0c108a800350390310003446a1402c0e00d03600317031000300c1c400c0307828048140220a804540c0340b4244030b841c2e402c20348100c0e071130710342c601080c4405402c6e0401c2080300d007906055043c429011070061070500c1c8520040d4014030b070b489404540302c464036890f0030f0860f048956480c0546e944c1d03400a40e0805102c403915840c42520401c03480403180c0080d013010200c0d044600d02e0644d0701e40b021000340c2ca40d0f440c0c0001c0d80b8150001080940341c409429 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 432750062 1250 432748812 432748843
    0xb030d080c1e030a0b101d060904020405060304060c03140412080c1c02070c05010f1403061305090a030212041a031504060839061b0105010f06020f03040305 69
    0x42c000c1c0c02035820216001015180004465981c1009091480a03001e40100f5502802c104a0420942c0e4413503442c0c11404241405107005158854003008150350004101d50ba1054080c00041003036501c102c01140030714415900000d20f80c1e800800078094407806c60901c3d0402104038200004118115081001a103043c64041ca00d07540d5544100503e00941c0c540c507a0302d0b0410170b03002040030303503980c0181aa2401242f20b01f030000e64400044941d0200c030510300000071421003c40350541c401034061340c3c00034401403900c1c8502044000803802c0302e000b10340940c156840f244501781816014004001000980041d4601c0c0c2400c1a16089024440f078074543c080040000016136004031140b100c000701c040007403040c40703600e94038900203988001c08146400762241e889801400c002e02001d440c0000c0c21440d804800140c1c010041103041d42008841342208040c5d49038a1594940a102c0c0d0384c0603108010480c8803443c2002c8000380ba19644000008081d80100024004240c000500c0c0c2c140c107d045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 432751312 1250 432750062 432750067
    0x20906040e06010b041806050f130902041109100c05061609030f0503030103031e0207050402090f0415060908060f0f04020d060906050105090601020c130b0d081308010b030d080c 78
    0x400030400034a900c20035414540038110000c541c604810004104898401041c81070440d0211030f44030869600d03102d41e691002a00360103000e5030030301291032010b00503190380001344480070b034010905540c48000d094130b000c0b6001a103413a0b20700d44801e082122f002c40c1d141c0200c07030342840d582d140c0d07440c43c1c00b130308460080c04441c2506d911188641083d50240d60300c0510003454080500d0724550f41d8000380012804140b009404003003440ca03503602864a050168001c00c001c80c6050f0a00c0002d600000810f03401030034038840c078545504c3d0350041c01034030302d940d000c2040c0035842c2180003402010786801008268200300d09100004600841050b0400064080c0d50f40588032032001030144640e0800042906081254250622000d9030100c0d0483d40155140b801079615103004a840d014100c90070b6a0150750042500000b906640c001c44203008040c020040e60074003038542e150203402c107401c40c0340036101d80c0c0b505100ea030700c02380220719410740c098009080b00c001c1c80c0000303002420020702084141102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 432752562 1250 432751312 432751321
    0x20a060c0309050703200a0b03060117040b04151118011d0d080c010212180706090b1902010e1b04110301080304060e044a07060818010204080318030304120209 70
    0x811b541e0b42400c0300100103180450fa2803c0c2c0c06e41e150000c40b41c070f50100d210340c403020201c15003120056201c0c613800290b9000550390b0b0b948801c244130526a0000d101503403041c0d105e844c030f50500d009240c0c0044d00c41200e04800b100100041c000e00c1102040c09a00d00c0d07190001d0107640343c1c0d00300204100d5019400e2074a0758a20898375009000d9020079200000752a07003800070001c0321449428001e20b00d0002c3e02d0b015520382401f40c50004141c0314425030f0031410040c800e804c45144005400d032070350710b02c00070500b01c0c41f13811020301e0300710454080c0e4494001140041894900391158032101c820610f1543c0c1558945100191070f406148a04814003049618210565039a58072100d460806000441c010010030b03640c641c444414091036260103c50803821038220303044400600c0306822110000e02031682028000c0341c0c07504010344400d00823124007130f0350803202c002030025001074a801d80003161188814444400e00d11507170406940030b034000b0001804a0000c1c0340401e0a043d405494080840d00d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 432753812 1250 432752562 432752603
    0xe0c0f04020702060703051215090a0f090b0a060807091a0904050c0901030b040510090c0510050c030a051909030b0c180a06030e0c062a030d020a020a060c0309050703 73
    0x15a42e00254803000000f1541c08140e084406814803031a100c0980b2a144e4414101a003402d8460284642c01001ca100040b84130b561500000c8070720500c0b80003c01c80b501d981e038800820900030703141c020815880e614148214001000414003d0049a03070901056107000e040d9030242d102546101c2c0100ba80c40000b5040c40003c1241c0d65142c00c001c1c2c524a40c035a940c6c104044943e2095070111031074000c3e080b600740c408040e402041802d80d080303192071641510301010002c9845102c0c20140c18004148a14400b480307003440981880760b82516025600c0e0101029502c050102030740000c00d01c549442c041c0080340704c0d41320483c8e0182203024840e07918443c03d46e10121030300c03000f003505500081c900c01c0401c0296150304800c00e500ca845044449000c42582004200d005000460226486c045090414008003505480c0c0b40c0c80340c4020340b490001070508140c180c0c5d000c21003440141e8000c803104000c10503148503031014880c2d14941082041060759840b0f031208218400a001c070120b141c0443c55146 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 432755062 1250 432753812 432753817
    0x10614060703140d0b090114130b040906020c03300c13081e0105070c020d06021e03040c141807030b060c030406030504110306040206030a090503090d14010507030e0c0f0402 76
    0x10f80e04162540361030031444504013411514150724001e1116800000e002981c40340c41d5024102e000300110741110110306080000d185041420b80d00546605400e4003060440c4010481d1803209406199640c02400b8552000e54166a040419290f5001d100200c045840c0c1d20f5604040c414001c00c0d0b42d151035107800b88000240b40c00001b01401124102d0a124202c40b1414140e9080c00300240b00d01d58a22105441d48184010003a4000307610050a81c00a001680109a0a0442ca51000c1008900f800c0407850341c000320f6003190446000c42062040b8507121104060001c1d0850760b904450310740d0001c24030524000b602c600e05041d1581c03c1c105499680d4800d4501c141c103800c0840751101e5551100a02415007601c09460882061150060324140801d6480c82640c001e09000d15540f1151140001000244010741e1180002c0c40750b03030765076510002c070b41300070324000d01d02d20b0840f6140411319401c41d45d014024006062074007410829020b00441e98012803101194005014150600410083d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 432756312 1250 432755062 432755087
    0xf06020d09021005130608070c020105030c0d06301211071e090f020705210d02030106080f13050c010c05030f0a0c120e06030402060912010603030302090102010e010614060703 77
    0x2042c1e411401040d44e2180280118a0018072910201c0d070380e5000644800205403401c000003030000c6803040240d40143d0003540c00071f880b41801894900b98000410445100750004005865140d03080c0303111002450310801600980141400c404040c0c0d5110221f0594030841081030101014030802c0309101800103000030401000700040310b95140740c8200d5001c03d107009082c941450724100c6080b480f000d101341c50850b584000240540c0e5010511088070400c2d0011a4079a40c004115500580b25607001441c000d00c06038031340e85001e00b4624039a003011480201a101302c180c049407100045a000900d240384241d017030070084142c100e2414243e0451050251f0f90b204610001a2582050b900864104075180038010070240c1c5440b170744045640a15901c8901d5202c0b605201203405480d000c80106070030140140000030481d4080c1180f42501da60b82d01c1500441e50200d00c0030090358080c0698218442c1c0c00008200c0d0a060100b0242c80f890302108040c041c402c0410346a0401d4040d0300c0c80c1701031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 432757562 1250 432756312 432756319
    0xc03060a0512191104060803070b1f170a0210170408031506040305160e0403091404020408100b12010b010909050a0b090c041a0c0d0f05161406010e01030f06020d0902 73
    0x50003210708011503144413840e400d078040d5113040c000089021020040d1401c581c0d02100c40201c81d12900894001807000b10440885800c20640010340a004010104003007507480c00034041e800780d10b004002080061700c0c004802d1045401a450146d0204442c09921642c0482000e490391030703881d900024400711000d4590000c9000501200b40301d80003a400c0798002d0980c200903429921084481c0300c0c01800e440042c040750480506125070010003610010840d0040c00c0107043ca41d0b210a20b914045140c40313440d0615564110382c994a0410520002c12110f50b00c2c0240818605d010000f4a807105502c07540001d96940c001103103110300c051708421043d83d0024510010740c00c221545103140c0d481441501c03642c0e02d4110440c80b000c1440700070b0750b2000c1000c40192036402c180e01411f40305000c801c404070007040810007000020f404001000c0902d5801443c4055500c15002c405034a01075042e04030030f9480120000420000f0300c01501215401d601041c050f1700c2c0c01381040048060541194020340c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 432758812 1250 432757562 432757603
    0xf210901030510260d170f04020d17120603070f0506070c030c0b0c0115060f0f09150203070311010509030a231225020c010309150f0c02060c03060a0512 67
    0xb46241c6102c9015100d0a4032420799405c4c100200007a110000803400348005040d80100045140107034481c005da0050000d00700c03021800007659815041807040c81d43e174203460404103003104203241d03030004070307038012002e80080c013089043c2501d5406046081c49003034410f00b00003c0710030400c08070620000045134450700000000f5200c8010b03c82c02d0b001403105174820361818940f8000700640b00c1e8800119111502d804080050000c42100c0e40c80e00c03030400c142445580c101c0001e00701034116140e002e150080d030242d5100c801c00d240050400841c2c0c500d4034641c0c0e061100b8080b4507034000c0202c59082e051030400701210102046418240f500c403200580040e030f008502050001039095080388030310f6141c6000c1101400c0c1400700826903c1032100701c0016401807440b4403003540070741d0040b84514068042041782c91b004100600c2641c060148480c2c070b283d02c0300c0d4003060498040000c0f41e040050411074508504d860380100361410b1a51141a10404031001c0903088841c0c20300041d805180d0480b0000e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 432760062 1250 432758812 432758849
    0x40308030118111207030b031e1e0d03020c07090903023703050c011805071a0406020303060402131d041b06200c060307020f210901030510 61
    0x61540c00034403800344490500c031106100910540300e031581c00381c4600340c183c1c01c3c080c95108250341104020040e1090590343c07118501a564100541003031244d128070031b002052030701004942000c140d1030f04100260300e101714101d001c220208980092000a03d001078030398036058610345c0b61a00380e43c0300080d800d1070030103000706044d40865501c60000c110780803541103082e0f0008640c00c01e1068452260084001c48900c0e0000e0b100d0002490707450b210100104950001d0b200700300711420f17807040403202d5a1010100b0840300d0103805075040c00358065210b19040c0b40c41d11601030745030700c00103000501ca684c2c0050f07120380e0b2400f0f00000760041c01c58001d44248041103000e042d412040c040e13605955840c100311540040d8140c1a013100c042e16480d90b12104003c102090302e4607040301e012025015030040c1c2c0c0c02010700b6210007010390b10841640d4010280008408180c50410408103210543c5140d90350520802c21000f6084a030b0130389003842c0c001003960702c071204d981c080b10440e000402441038030181794 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 432761312 1250 432760062 432760073
    0x1509050a0803030f060f06030a091104020d0b031009020915060d02160201030f060f06111c0f110d0c02090a0b13060302131a060a031e051e07121a060403 67
    0x218130611080080071040d0701c0e14010051021030103102a54410030070400111020080d0300903640980c0701d4420f4800c01b1409000060503a0000303007100d540540d039500d91060301c1c1b8042014400b02e5200c000204440d00c0c06402162141400a000440ca0303c01a040040710b611075804440b1800328900c001c540b00d0342c208490442c1c107010039400741e00007424941c036008028240d1040d542181d41d02080341413003d1130500e080c1c4441840911f4100d090082d0682c184058142660341002e000c10744c0c0c2c0d80306070a002680080c056600d010f1540c005035120b40319090846420844552503103404030b40f031020983e20b400385031018220545180d50132004010130700300c0310084c3c1e4000708190b030b200b03c0320f01020320360782040301342101c070a2076210910040e80c000f400d42d81e040c200010000e6840328600428444940142554140c014079020b50f409a6104c0401141880c501c5081820f030100305810100d90420500003454100e86070700401800d80e031000703042074409500300003d41b06807015081c16100e903502e0400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 432762562 1250 432761312 432761317
    0x1032402070b060f04060e011406070b040b07090b0702090c0c0f0a12230301030222020a0810050105031501031a0d0804030501181703040602040504020c16050d05071509050a0803 78
    0x228014140b4412114481c03600d07000c1c2038150303150f000319207441e0380c40d044a000c4409d240460f5160000c004004c0714002c00c64800758181b086004908503816801c06403801820044a50b21041e00d002007403102e0001661003010107a0070400f21802541c5a070140c810480c1403503c040c9100510340b1624030b100c2c0820080303503000709005800b601ca54042003c1d41008070210048140310848000c010070050006241c004136820041c00d4080c05042c80c1003031446602c0c12030340001c50301b002244015007049000c0d1203246c007100180000b842c09604604003945601c61200c500c2c0d07071035030601d603c5581c0100840042442e00c021014001e0501e9003044c814201007003917901ca0f020603140d55003802c40c2581030229a18184041540c07002c2c202412070320305034846100f41c00c05402200c095401300b000040e60b94a50000d00049141400a8000c98100b02041003440c41258407440c0107084a1340410b02203000402c0c40c10455104110f100e4a441502e80116509110740d080036034485040d180125003602c0004c003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 432763812 1250 432762562 432762571
    0x501090204110405150c160909060f060303050703030b120712050c030601060c030c0503120114040c0e0d0816020d050610060c2a0320180105030601032402070b 70
    0x3020002601165403050720b601c80c9004454028000c2020f4407543d60990b402440e4070301703100b003e07a5100034640c00981c03411041ca0b40403004094a0b40100703001d02441d40314056000a0000f400c1106034590340c1c0c094658007a4141c05004d055940d0340e80c0c02140c403841c031011240c6e007030042503031211615480b00c01c41d0b28400702c0043d1040d00c05c101d01d11200d0700340000c00d18180d8180d500c4040c4030031400e50f8101c0c0d40116015080350940000c3c0010801c2c091001400c80c060300460982c1d403c0c05210f40d00380070440c0d54442c1d0030804c0085140c0d68040d1078542440041000d034000181590304c2c41100082c2007841c40301b4030006d410005611a0701c0900c000483c185008101382d07566280c045517200c508032520f0490401c040d000a4801c1c94102d0034020507030700b01c540c3c164494916aa0580e803519400d45a0006110999003107e1955041ea1145040692135000380007100304c0b2030b415410000429518001400010155280848920b920100c01d502481c5450030542d0259520000c0e0304d851950340700180e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 432765062 1250 432763812 432763819
    0x80a1a0405130311030a02061b12011d1e01060c02040912212d1503050f2b0507032007030c060e0f04050c0d0f020405030609160b070c1205010902 64
    0x100d50760003202c00070044800d0020603900408c0b060b242c0d120080410740603640b5459848504018408030f950800c54214000c1001140c5219120028030034140103100040044002a420b5200520f450590886242c19160945030070708106a880c0301250080045001c041d041e0350301710400518441c1e1052143c03861210f4201c5000e541e014900d0b043c82651042c00f291f405540340f60030b01d50200110344c0020700003d5200d000100303100d04c601040b88080c4c2c025401c241c3d101e400c94800b40c40b480c4010805080c25260031240300851240c00d10b00c484040404240700010486d0000300001414460202229403050f2500c2e1040c4118034201e0180c0d80d100e0030310080ba00040e40020005c0c2560007054aa129084060540f0200b51007040410004010040c10141215801e000032a10666144262601103000e804016a501e00708000c051134a50300902090107a40402200b004401e44e9244070710455082100c5d8603201c0700c00e031030b140b032144103241c00051b080c4e0741c02e044400900c02e05411a03811507009a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 432766312 1250 432765062 432765077
    0x9080310140306040c1a091e03071202060301090207111203040f120807110a15020f070b161101050702220b01030608030405090c070204241203080a1a04051303 70
    0x1070040c903403900004c440140c0744045072681041158080e41805406440341000b8910340031480e000166108151890fa40301304041100450040c00d040003940082e20440c80d0650403e001c6500080c11440140501d501d2180c0101d0b03110100f180301e120703c4400e8040107200360b0b06507140480481e5607801c58441d1001031a802c50000030880c04999018503515003010103d8500328581e202c0d8a000c04240c0c40498010b809035400103404d60105620240345a169030281c4001d0b03503401c014518141854002594541c01000703030000150008113200520342c1e00c0707509641c40041040040e5024014600040e41020000b0752200701c000001260610611500340e0810035510b901d00110120b9000c0d004000300760380100018451450300350f808590115041040510300400713a400700342502c88620800000b8000c0d400001e1084030403030218800740110038521104c601e240d0310300601d80f1402800e035500442c1d0304e80c0d21100c0c4000036147c012002c4030181c010b210380e08000500700d0f50142210420b80000340f00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 432767562 1250 432766312 432766349
    0x7020307060c0639090918060e070806070c11030a0602031e15060c0a080c0606010f050a020a030c0311010501270204050a0b0f13030c0e060f0102060106050d09080310 73
    0x4040d03a8411030b48a01c051804d500c0c400c040303040c0d00c9401400d494188004240c00081d07280c114081d5401228103151350b010100014644035090b81c0d4100400202904140002d0115500004d007103070b80f01c82c807841e0658500410382004900940b40b01c07400c907014041c4080000034881c194000314010801618044c07200480740703020100003003040e24004003184243da80d0203000d162850141c104030088405440352800503540b5000c3e40d81c070a03030301e40e44150000d1081005941c1c00c0004030309600e620f03040403460f0086441d0000d490301a1200300905001e036608206051511468030209160405402080706d9610713209054452210740442e10300c911120000404400744a000ba1422600007038a03d6201505001e501140e0f604071280703d200c92201030100c48240030005c0741105c01540104889000603047c51001c100040c0000d00e80c90280301240356030003c80e680010000d044a546140c80d544520080140c003003e4443c50300090100e00b0040107101d501c0c585c20040e0011034044249203000d1000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 432768812 1250 432767562 432767591
    0x313030e03060609070807030e0723010c0c05060d020702030d030501030606050307230402070203160305151302010e031c02160501080115050a090e07080618060d060b030307020307060c06 82
    0x80840f000744e080502400414000b0b40100c43c803030b402c05524200451485102c0015601e0001181d202030f50070071f18034100340f00750b00300019000707001076003841c00001c2c01e075080d00c0b10034414642c4c0c40f4441c0101c10014840b0b607280442d9040d01c407940c0d4010141c81200400030b030001d018003800e01055426501e047d90004241ca000190b0b44201c4283d050340b0580102c0c041c0044009040781c0401940040c0c007040700307800517a030170300c00c1400c1a40341040d1a04501e066050480c80d01c00e2500d000e03411120b8000910040c4c0007200396a203459075092a200c045240b0350404207040c90445c0b0404141540d010306042c014540200f44000b421495050520f1660307914801100c02103030038400c040441c2c90050006c00064031800040000325418245110b0340b980c1d81000401d20300c001c0356840f0018409900384240c1d840c0002050b1041050031442144c07030b0030580b001807102d00e04020014070481d079420404141c0d4074148182d5092a4000b0281d035400b0f551780f90090507254010004960b83c601d462084114410b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 432770062 1250 432768812 432768823
    0x270f13050a0501091e0e120415020c09060d06090314031e130c030f05070f09060602060907050609011b050a080a08070305040308190e010e0d140c100216080313030e03 73
    0x1c140030034052001c49802d14000e02100798a1800c0e40140c7c202c1020b254840380090004000e100703013020b451000c0f00d8009003420050403005220700c4400b000e02c0400e0362400812003619811001c0000e000c0b0203440c054509443c920b4100c0303000d800110400440300c202c0003071802c0c0d1251313201c0d00305000c1d614912030301a5101c0161000b01a0040018140041800d042044505a1052080740c4185031200d00d02200e80215038000f440785511038409100140e4140702c80c0d50401c41f0000241105401d002c00030355a801841c00241c104101080b61003240c81118a840404541140c1640c0080e045424800355642c001c00d41100842c1c061710104000c11310a2041604c074507015610440d164550005060181c1c0302c0c2002c00d8402a11440744100301c50081c0314490750020310000070101b41101d0b031005481b180141420110080c420300134005403d0021031140805d8211200043e510070b030152818000300103440001c1d001d10340110800a1a414074814100b90354003e445070341c2e200f00700b00c0c10196580c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 432771312 1250 432770062 432770081
    0x70911030402090a11040e1303030b010f02371208180c04090f051c02060108010204031104110705070306230910320a0f02270f13050a050109 62
    0xc0851030000d5001c800d960f100c0650308035000040c0d843c003550b506280c052000c0540320760340420161074145027010340504c907003118146c080c2010303440300050b4403001e500c40c0c0030310708070845100c040506806405c50098489202520640a42ea00c8030414103044005200494580700410984004140159600e07030714659540d144c14003c0c89250b0b41142071001501d280601116a15020f94610001031401e108000704105800c09401c40d0312181c0000030720b018010707444811a40d00c1080148082600010a0711102109440201c0d0807400445c0102d1584111007026007540030342100071042040a810902c40d803840b0002c100310300e00140711001c100c000d003541c91071a01d40c041c82400395030301c0301070304003040c01020959240005050540c101c5414040e42c035503040d000e050003042220000c1c00d84109010901c0041c02142807443d4010040396890420440c6842074040003003070305460382d41e91103200310100041c00d41c5441c1501c2c0324410020b043c041d50400811420a4000302e0000c0c0b1503c10201e42 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 432772562 1250 432771312 432771319
    0x60a05071401090512070c050904051b041b110a0203010e0303070f030b010f180302040204090207031407030903030c050f191406040c05010509031c020a0209070801060801030b180a0302070911030402 87
    0x103642e1040d08202c0607800f42201f1110405030340c8001604e55900c5019504c41ca00403409802c4104804050444644c018518113105030b2528840c01c2c815552490800181e07202814844900100c03903250516107410020025030640c2032418003401b484021000d0b40c0202c0454a9840f84000170700c03415000e84090300d0425000526180d29491000d1041032031001e900c8524006800c00340d22500842c05a0707106070000f000c00c540000d80d6204240c3d2043c05864000c00c40183c007030070400581d90041044a1500c009004c020300f480c0c0d80c0007844010311541584020380400c4451840b1112080c101c0903042242c251440030700c8540d030708140040440e04a02c103a520202540c041c1303013010300644440d0409040c141d0144203401d40c8240c42d900c82420340a0501850300101000545481001040d58005061204204103030004001164001c44103c0c1500d912030003900a80d580c080028540b0200c80c04c50701c0662044034154418140c01140c00f0f016920480020300c5013801c2803070f03018068441590000d40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 432773812 1250 432772562 432772573
    0x9140c0d03141e0c070909080a140f03090c011e02061b070c0b030a0b10050301090504020607060c080718060c0f05071206020c010b040902030a02040911060a050714010905 75
    0x1e8441c0d80d40140720081000010308100c50b84035200222075500d1000440f20000041850944004028484c000e0070302c8002800f0340303402c540c0c60a1540c0502c10340a801e1000c05981c45007051111010341d42d4606494103220344a18008400a0342c950000701d85601040c01401426035200e0122080e00c0c03000c0e201d400510309034551200d8039085010b070f6002001c00791000d000080c00039162103a440020003200d520745489080455450040710014038140d0300c01e0401201d0110055000400d980c115130740b901000840365035500101e1040e2082c51030003000c040c5025205410b254000c02c0e414014003255032980860511400300e9225240d580c001c010200c0c1040024400151245420040541c441c200f604d40a07692a0518400200301d0b01c2d0469003150049820345000c40c00b445200c038030346001c84090182c942a600030070b480700242d020183c00b8584450750b180600003140c0d0280c08560303010b0035655941c2d40782e0b58024030981040500315055441d641102e071618405000d481a05a0800040c11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 432775062 1250 432773812 432773839
    0x108060306070e0109120b0a110c0706050a17010303050a0e03010b01020705090402150c1c021c0804020d0b01140307080607080f070e0415030204051f120816050109140c 74
    0xc0d0242d0001803c00c0c1008882e50000c600d0b03a400e84c03900e807035480c400d0482210500f094040c103c1034070782a40741d2401180050040d51100742002520004445c19802d100c1e9031441325180444085c1080200320040c0c140500001080540c482c004000c2d04e012581c8078810101070a0425098038080c0c074505005038045482802545415003805070050320081501c200200001381c00c0c0104c0d0801030741400310750800706441c41d8000d4079003145040d11000d407018100400710501c0c410f0303403d4928070a01c0304020703c810002c0d086482c4c510b8903000c01500314101d80d500d5a51003212843c005400c11140b802405601c2000801400000d54180940380c9501c03000c0071655080d8040c0100ca80c0140840104441d80c110b80358551518804e0082d04003034526200b1031217080d0b00500c01510380192400c2141c202d030181420035465081040d070255001f0224500d607114490901d00118054011601d0042c034600c0c4e519410080c0c150f204880c40da00c50300452003a00e640404032038a41540910b07060300000c0454070031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 432776312 1250 432775062 432775067
    0x3200a021608030d0f0e0114090d02010c0503190f1104050f030f120304050a14030405040c1e20070e0a200702040c03090b0405010f0b030c130906060302220605010806030607 76
    0x902e945e00d250f0400051074601c4107100e03800d443e44104400c2c1400f46800600010305814886442540b030b5500003400001100072006000f032200902d000201583c0b42040104500d4a8210550600c5c0c80c0c2000d00015031801c020f2100c0d83d101b403250501c501980050301906090105003840704d070150360060408842a0203d440c0d8a60000b04100c90502417a1644000100d0300903508210415800046481d82e05110500003254142507a0f0400d001e8605417020021442d080043c02c84030380ca140800858980710280001101c0c040d010a100e070007420408038400c482810441d100719900003080c0440f07000c600c032051407184501c0148100340800c11003a009801d00e5001001c0101861400042848442e10b030118020ba0655040762580d46074680e0300c2ca090124061044a11412400380a1a800c110300141442200000c034030030f0542c0303c1c0d06400a0240310b501250040d5005041e20046159030700e924403441c410501166000c525010003c1699403007000e04900c6450040c0c005d142e40d48403058103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 432777562 1250 432776312 432776321
    0x3010905060604030203060c030a05250e04152d050d06021608030405030307080f010f090f140915070503040c14150c1e060f0106080703200a021608030d 67
    0x2541010b0200b000200588040214605c54122411041d48905080c0840020b03901e01070844414020540306084810303c401c0c090b9003140c96141400d0340314801000c0441e024000c25600001500c035140030010f4240c018254803091a507d080c001d41e600703400c850b081020604075000e0b00350412031100074540000c40a50050030015076108043d01d07480416698240f11358403c80b001c417219007000c81801189500300c010607410520700080343c555581818940324191245129004034151030f03c905000400c0ba035803100c0d001e040c1c84100540c0620305034207000c0d6580c0d103026110040b007200341c000540c681c0c810701c143c0f40100d5100d800300303249500d48000c07034144180040503c1c1d84011000800e5240b01c0c00003000384010b2010102a003035a2125410400c8400c140c40440300d15500550104440c3c00100d9250b1419111a828144080e07110f200d8100c00400084506498040c0800d0048143c114600d025003141d1310203034215070100c082c0d0000606598403901c40d18480341e00a1241e46841c9609812 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 432778812 1250 432777562 432777571
    0x609160c060f05040f02040b040c08160509030d0e090901020901020712020402090a0906090b01030b1003200c01050f091b0111100f06030c0b03070f03050612160f150503010905 77
    0x1002c2034110048a04030111601034030111948651209a803046003814024000028011a070411040300d1188001e04503020041c81032050500c3d510824480318011000c1d21012000a0200c550009c5801c0d8058854520107290510649107440011413090050089605201041e805002d50514100c0c51090b81d4250300c3c0221303445a020300c00d2404584440305d48400516038014041109460705103d5000c075101106100d04041c2030140885150701c8141007491041420324001881d14820b0140845100c4003500e80603900710009440420240c05421241c0120340035195070040307131101c2d4441039803020090300c0312285200086840d1070560142c81d141013028620b60581c2e28140c2086007580880700600c401342840703a540d207030078000d00440c1d629100103014080c1c103691660401080103082e61110f0008041059100c400141040e1221044502e1070034500e82141c0541420070b0000403898894000d61145401d014400540c1180310412141c8800792621902d240d40d0074801c0f000040c0c4002003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 432780062 1250 432778812 432778823
    0xe01140115121b210e07050904081308010509012a03051510021b2e0c0803040f17030112060e0a141b040615030b03010f051302090609160c 61
    0x603a03d01c40a0040c1c2075510701c01483c2e84240c1d505002640900400e180500580480e9241c03040c1c55804200000e4030200750741d012520140190303600c2c07800ca0040d106044104000f94520140024608815040036004000ba18024042640d603001c000d07140c41d51b1040a079182c1c0e25a016240d0510380260b0003203402c0541100200100d10014011841c000e0200f455040142d00c43c00ca0301383d0344403000c13049915002c400c80d08a25250301c07002c294210030040601100c0c0080040c028a200d480c043c2101171402c0da409210543c880c50107042040c1288aa0f0320180e4a102d01c4480910000e007000007140d040e00c0184001003006403468941d10010021058441c2940c41929100c4012540e004540d6041c68207040003403c14421700780356000c00718924250140681c1c24140305101024907034900d0400c101d080e18000480043d43c80009024001503e0301240c07081c07800c0b00f80051180f56401a07034041d4001e5624418588410003403018a40341165441000d02048898480c1c42d0302c2040e0841110b406003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 432781312 1250 432780062 432780071
    0x18170d09060e0a020102010f0c080c0a090302040c0507050f0a080a050c01060506190f021207030e030a0b09010204050a0501021501051011060106030f2304030e0d0804090e0114011512 80
    0x195598030489420103824030240c1d000f0002403003150781c240a8812551a850018007800c8c5581c003001e060380ba005030210900714800304880f20071500c180210002160024024030905200301405807040d40415015141da0140c0e83c0300c40e9620303400040da00c21850380071072250301e0945a038804460640103c01445420354035440006100c0da01e032009003901040001c00005441d248a80c0501041240e0015030700355040b0610a155608101040e00c08240d051700300f8003812120000001e08115214400034041c400346014031045640540c00390040e9082640c0c1c001c141074503040160b88d0303010b00040d080c8440c0d40c018010b002038180501c40803a11042070520000c4000a0007042c3d092440980052000903130350360502e01d840c00035003c3d40c0d41b688240c0009038444095121490304075007006002505200c003020f0340c0e090703984505082122580d00164510380341c41d1a011910301030050000d41e541290700f804404602502504c0490741200e1404071054590300150305c5c03d4072014499503070995103035501c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 432782562 1250 432781312 432781331
    0xc0f02240d14130f12030605030d0306050310060e0c0a02071502011a0f10110c040204060e0301050714121b040e040b01080708210d150918170d 63
    0x103520150100311040e4601003042425624102030880b0001c01001d48461008250408140b5940340802135940088105402482410098001e04001e41c8820307014410403098642003941544580141d9038101d054500e146a1038020405a0f0191b0141e41d02e500c8409004c1001c40b904640105190320090059070000c0d1f80d109101d40e2004042c030603034000342c3d46405130709404440c04d00ca0401e1100c02140c01d0f80c088110040132070350707545600d004001417100707000c0c1d41da401ca2820800f03818244c01c02041550b655031103140043c55146d04046407800f0b0743c01c10000c074044502403285a100c0b400700d12001e50800c408203d0f0000040301c0030703001d440045020104c0e82c8010344103100170806003546611401c0701d4241842d0130301061105900c03e0740750f43c0001d030041c040c0c0c02010030401c452030800d212115500c3c1e80003401000780d10900065101a80c0740174080c0668400e070781a0f01003140c14012040003124412803060300c0d01d1103039420040203078003c00726603441038114001070b001c40c4000e184000b86d610803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 432783812 1250 432782562 432782629
    0xe1221010303050319020301060c120201090b01081005090a17030703020d0203010909140c100c0c0e01080705131404060c120e0304050f0105091c020321030a06060c0f02 74
    0x280c109900040f4000100040341481c0b03403a503e84070340070b0f0b4000c518561418000034440070040c0e070004c1a5096014085841034400d4000c011a1b42e000050124907581d00c01c1c115580d01080012f22220900700f200240d0b02900c0442c882500c0b45d0031814118182d9601030450080e540f0050102c01410307400c0c0030070510204944003940c0608003400340015107003600d0030318400b0703440044062400b40d0300400b480540ba4669407010300007841305003000e401540351450031107a444002e4001100d1024084000645074600191920807078600f507400c0641044000121029036450b410703580f01502096002c10002103007030740817000c184000d00c0c1c00e070b002143c0b08480701d081e21002c0c4050101ca620101d018001d07440c114030310051054007420607619090101c000700d001ea8445a03184100441008001c0056407018400711500d12880079070181c41d4507844402a105800176520344088518000d4003007401406081080485504021190380c0900c1a5080081c0b48584c02c0f800c0c4900048204840790520b0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 432785062 1250 432783812 432783877
    0xd11010605180f1f03390302060f0906070c03060e0f030a140c0f0703110d0b0604050a14010f15030e1b120106060806090f040f031d120609060a0e12 65
    0x500c140700b4041c09140f5000001040020545a040e000742d6281c0020345070410700c0d0307040081f030381e05861168803856003c4245100b4000d040d40c264220a0008150301004000400c800075030703102d04010440d141c1014a01c5655070242c8019041c20b038020802c80301c40501075020300607808012a01c076071810f102d0240311424041504090591a0300040f42407003040200904441039000c152444581401c17680c54180c0c09502c050310880c0281d42c0d41020422085180e04010840d1741200214402541e44103529254180c1d2480780c1d04807028020020788400344240250365455482c44000c0c4441c04085075032014109041980c0c03503101440d44441c800702242070140300300030007640d140d040075032a221046c0a90a030b001000d50307c90041020800000400601008030039981501c0d1100c8220b198144489108003002c1041d580714032409951179460b2800101c9500c9154901c00340c038a983c0b92001100b069648480c20000e06810010321080204c034220b001d0482048101d4001041d0394401074a1107164 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 432786312 1250 432785062 432785069
    0x60b060a03021e031003030309050705040e0708060105041401091e1a0109050f0d0f03051c0b011d091302060d050f010f0b13050402030a0e0d11010605180f1f 69
    0x41d401280350103541c8160f141c0032116400a0425074903610707040206859034125404010140b40e41c42e142d100a2201c20030003c070240401034004c01210b00e00c50700440e0303030700d89503c5a00030303900c113120000c01c80e4100707802801c2c01c4400181c60821940d0820b03a003c0301030300e809540440c5020020402418503043e03070040c1405041c0c103100402a0600d0701d00018441041904154020082242c1c44d400c2341d00c1e507001c40c61006800c07015a503004030141c9001c42c0c0500c01c1c41c031140c4a91a40840080000301154441625524241c0310301c2c281010f87c002514001044540d5143e1104007000020003000301221002005480208500d1034013180601c85001c40340c09441035864100820700521203d058100048080c00101da01c15050800015000d2030000c103a0040340d0080f03070040045205548580c0010f84503021902c00d4a20b0f004040400501003a10b1581d503200c0c41d0f080403000030349400c0c0b1f480640c104083c01c643d02d007819507600d0b0500e4030854010748174014450301c9a07420001500d0fa48802c0014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 432787562 1250 432786312 432786317
    0x106060e101101050723040308120910060608160e03070e061203070b070e030303010f27020c0115170304050910241d1e0102101410080102040608070507060b060a 71
    0x4840300d041402d103804500601c141c21388500f0003060002c03414420070340700d040c04000320100b0103955500bd51030074461005070b1590721320f0503c3c201042c5036403c0900c9a104416040030850305200070310b41200c10402d482e1103030b500b50301300716002c8c031040d0020071240d0b40c001405400c200c10061006a9a465917000780f0b801d0b201c0c0c1021500340820180d0100150307104a4048000b50b00b15410480e80c940082e2541c0329580302140c0c1d48140d01d110b50700d010b100c0020100450021502c4e100c01420245c040c0032418000150398030302071070110308501407140da48090407514005600b080c0c1400240120000302030b01d0792080b0740c9000000141441e028002e12041008031465a1040c01040000303015801c1104e0b0505038042c0b402c0400c40951140041c001c0c000100c200e640c185007100d180140d09041d0343e21601000f440c180180315000c04d0601480c10b000fa00440080b25034680d903003132458201d0095002d07070800070b08002c0c04603030614032401c090b0030210f000d260000b0369a5061400901c81d5030026078084007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 432788812 1250 432787562 432787577
    0x91c0206130807030b0c070b0f07141804360f0804121a15091341190c050604060804060c14041a040e0a0207140106060e1011010507 58
    0xc200d5004200360b0072504a040781407d0207510303528031040f260000d1003501c2c04a407200c00506018031078001002d103c101b81d4502035841c0350503030701200180d143e81e41745402a0300380083c40328411581d502013251a55403040c1a0108282c800003034455001d2004140c91003c022a1110003050003400100300030700242d07624250703000080c600030305c9800c044c054031101861303c8820000030070010000d008404030308aa400ca40fa0b901c20901c0c6014040f55840540b500c2c2c3c24402070030001b003050000e6203040a91029103c9516050400c13001c088400110710419600410300c0c050041e0410101e42d81030910a04042c0c03903441d00c1d070002c115240c00c08c2e480200060309650504c41448000d1040b20580140352609480e18828403034400d0b0f4034401c620070b112200b00f02402940c12081d004098a014000030f108942d80c41c208541800b001e0340045100f40e8408843d01d04c1200304a4051081e1001c5621a40b05c10100c2d44e0000c003008150403103600c14a00740185500c84500c2c101c0c00b0700c82c0500c03c0505803076040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 432790062 1250 432788812 432788819
    0xc01050709090e060105130e0105010e19090c060315090203090120091806030c0301180303110427140a0509010b040903080402090a0b0603010e011505091c0206130807 73
    0x1400c003101644420201d601d4030032601c1a070f44010402506503042950328486000d850f4819400810040480305403c0d480c1500200329643c0c0014104e010300c2003000d10725502c84030030840200711101c0d803800416581d02d0134410440c4900a0f04400c1d19060510303542d500340c0d0350780c00084059030300c00c0300c40414a9554090b40c80281c0d80c24550010000044040b55046c0580703903022440181e40500848004869800080c00c41e030f03010031145e110924050000c1c892483e503000d140042c00d8040b0400c80129003000715405990101000391400c035980040e010441d8040c0c0d41080c294500700c1c2d440042d1907502c440e6603c40c0003421075903550007005602c0300007502d8a004522603007140c0b90b400001d84114104201c1c2030100b684036140a8100e501100c48481c103464030011300e0010244283c401341c2200d80840005000580228064100d0780652214071039190740030b400721018825011141d51001145111048100029001400b890310150020f4075294174009092849813150380003072525805041d091 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 432791312 1250 432790062 432790067
    0x61501050c06161e020d0c06060b0a080a0b0906450603071505070206090d0f080a03050a06030b0109090c0b0c0c040b2416080a050306040b010804030815010905060c010507 75
    0x8028441300c0c096003214000fa00718000e40310700324605104100303c4441c2d016803e10400f680060b00038800461b650f40d48900710f180240621504890100c3c465203001e00d02112820301240036031085030014004816802211080c035004461080341600d81d108100340d41c41c40642c02c2d040045610301c00c1b009502e440c42d01c641090301d000e200b44c05c40741e034401c0f0301c5c0c030342c071302c18980010599440c00c0e4101c44503615004100040352004c41c1c4180d0144c02d040e842e080000a0181d07085c0240b5589801c0e6030107004075654555a0001e4a240303210080a200b03a00b0010446030310300d5408110070a02c90807080021507600c0e103418400390410b00c2e001d28250080c3ca500c0445280c54419818181300036a860128404403175801c0308060800740030101003190001d684040c0040905640a0b4140d008106c280c40e89002400184540c2044502900807031410014a01560107901d40512890703040e0345040050b42d92540c00390107000c000081905201d130301000070855580d0a000341a11000e11400069203240a2100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 432792562 1250 432791312 432791327
    0x3030314060d03090b0a140304060204030b010b03150d080702120f1b060f0906040b04060503220f021e12011b050406050703080613050a05090d11061501050c0616 71
    0x1282c407400035000ba81c800242c00c07034000d004503200c585034070341c803512810030a0710200280c10703083c25061000801c02c0204000c940c040c0059074010520310707086a0301c0b50103c0c00b4038031052307600000409a402c0700982d80d01e17200c0d1640d80021712562080342800242e07400311300000092000201d054010001c1da52109801300114818040208022107510410f1004550341d44204950021700401c00030341c15030300b51074030000ca80c014110740300c113107989079510b00b00140103810a030741d058114854600c00001100002c0030a0055a400200c1c42d400301d0120b03800c10140c00c109100c06030076172034070030310a075080c0c1d0310f052000d60f24031403000000c218500350107110742e83c1c03210b2100b494041c0902400705000041e40300701500e0f2415410300301120b2a40302c0340c1c000360341c2890f10488c0309010fa0400080100007003081d0811400b4141076000c565103608103c10a0750030411429080b00030764004030014400f40c401500c08180082c0606005142031094120103003400c1045603120b0304c0d20140502c1000035544000e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 432793812 1250 432792562 432792571
    0x206150103022b09080d0204050a0e0403120b1306081b030a030f0c03092103110705060d021305102c0109030318080d1214060f010c030c0c03030314 65
    0xd08501c0c051a8000c052018030f001460829100e085141018685840f40c3c0100ea007543c21030003158413150303d5589000039500c240a5680284420b0300006821801080d445d0700071681038480300718201140b0480c0300100403d8084541c85a000440442e2091440c85410050113842021b0460420060080226034064906541c02130303100c9021a40842e030702c100c800b1805280c0e450a00c038288000d0404036240e2415803c500c44030321800e640e01e0519030781c06010780309207803203621400c803803e60b4040c2c1c1c140c642c045071040c3c03508403204210b0514200499401880004891032400054580b940040707001800c0c0b507280350300425034008008180341d0100c1315880e4083c0c4521030304845003c0d001c0000703212000600c8010240542c210800e4405141101800301500020044400340403003000f000741020b0b0140d0503020254540b800102d89440341ca0900386c4203060180400c4091a0642d0045482074a50744050301084107440070440043c0254a0a01c001c50003580c020a89030700420f04c19034815070180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 432795062 1250 432793812 432793817
    0x51006140a0c020112060815040201120507050d150815040c0f12020f0d12030203100b070507060e01020a06091203060506091e010905090916080a03020601090914060702061501 77
    0x9489a000e03440b8200b002e10650a2a0540e03800100c0a0024060f2545030003072044d0340101c040c06025541001c007101d2259000740d0b20301c004070403400107000c101d450940e002d400080c01040341c3c1001110580016204038904d62340c500b05203a88800c2e160401e800e040c40044400c0d100014882440b0311141c1400140030310011662030185000b0f628039404042c8030009000d44880c000e000c801d41c0d505000300c3ca100d030b0003451940c0c00c54403e200060080d13104482ca10f4010385249404500380c520801034401c0346a002d4014040c0ca0709004003900c4c2d00d104250540d04502c9007107035140000b0264041c81d508544503101c41d8060701029800503003951407942100d03000303820500003560b1698406180310303c900d85410303045d07207415440d40049400e9603540d0003260b0042c003403009000340c0c00800100d1101940020b5941a031468071008865120501c0350780160060340f00b000144594a02c6500407440240b20701404100c8902d808141801d00c4021511200540c0241e4200400300c0920002489058001d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 432796312 1250 432795062 432795067
    0x816060f080f0406150e0a0e010f061d0c04170a020414040308040209040213090b01140a030c0603020f09040603060c02010506010302160303050408090d140d1701050f0f0405100614 79
    0x10310901202d00d00003072003e00303c99240c0760340350700320002c03450300c1006840c00c0c01500c4c806150540503007001d0103040c48150380d1507280c5944409aa0141d1083e242500c1c044c54020380c100c000b00e01c0b8509082070141a4000d805c204100018030591403540c04083c0e59160300251101c02c0741401080100d450001d0f043d4070000340c50040000103640501030992243d4105c803a070b52162101d001240c540700207206003c540c9451b1000d580140300c40d103000c450403114a40d80e08100320f03d44005120507282148002402d42d46101805d004d6240260083c010440042c0e03201400c0c42d40d0b40d40050f051392100c5c0d00a4496540c1d0300c803290a019428000c07241d00403800e003010351614100003003a01c7c4502603084007504040da503201142c20468581c0071603050800c010b0000c00709800c0d500b8407110003081d10042140b548200c40402c8101400b0704131500a201c0804480d04241c0c1c6081c00f4015092944c40001d81e0040d220380c1440a40c0c0e81e20710034140503118a00804180c43c0c10040042c0500407050b040c1003825006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 432797562 1250 432796312 432796321
    0x6160c0317030c04090c0c0803100e0603010b01080610111f0b0312190210022101080606060a0e061c200408211c02090108070302030603070b03100816060f08 69
    0x1e07000b210b044171200701d00000c212440100403540300c1c2100304010200f860020500c14001103d120700b9055034106014110a03460701c608240c00c0340c6444400340c1c0803035101000030340319150910100950341c07000d042454216160341440f60404405055180380c86540b8090074040b0b0805200700c41001d10250000c0584a02510400b1054001d0b00255000b109240042c1c2030702c02d10a004101400c43c1091080d0b4075901100102011605182740c0f2a281c2080781000042d90500000d02d01d00800c00a464146020a07845003103074aa2119030085030064804c0001e103043e000700000d5004606404a000a4907040342e07100340c4504401c1d802c43e13400f500301c180002d00581c4000f048401e19001800c0c5808481c2c400c400d155941409801d80c01d07120040315002c00d4040300c103950001d05282c0300998904c21295585407007641280401c1d80c406030564415402882000805402035400c01c2d1820700c081e000540da8403000d403601c08100d00201e684030041078200a926000b0044404034605400c03d000c03240380 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 432798812 1250 432797562 432797581
    0x1080f04080f0f180f03030a0c12092408130507180b060f07021314130503160501140907030506150418080a080906060a050f06160c031703 61
    0x1500203401c110380054800c81c0c0342c1c40720003100c50702c000a8091907102d0000c0c55102a10400b00c2c044203004449040d030b050031924002c000c80324040c43c0c030740300c0d80c0c490078140c0ca40c500d00409110100c810310002d1b001c042030307881003201450b240f094425090032000d0880c41009180d01c0e005070040d40c3c090354210600300013940c0400c1d0b040c00d03502075088802204d40e40e5403048020b80b01d2002e250381c0001000a0030301301c00025800400c4a14000e40d4030f45030421083c10300600b03c58030404080d507000c2106010902121650950700e107078600410880b81441910100a0041c815150307048031a60340d030384004d8800828202103581d0044840018200d91403450706c4291304c03890014160750810f2142510350155517201c0d488444000303111905800c26060500d040b810641c00343c10a0804540c0070740001313003400b40000309544940c0015018600c83d43c0f5020912251100001c0d000c1d901840074083d0600d0315842d4042003015501800c0400c40301442c40c00d0258041d07180100c070040c400d030f0030003c0004456 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 432800062 1250 432798812 432798841
    0x30f1f020306031501080601030c05010f05090d030c0602040f090f0506010e010810080115050f0316060318120f1815050702011206090e10140a05180111180108 70
    0x11a49100503079207035030302400242030981e44003125600002c136400110b103850300061410705a0380714010711a00c2c2a220401941d0f004115020000017420802080045003801c0300300c414024400e040180c01503440da0340c3c00c0c069070855009031000800d001c2c400c000441c15405400808850004200504d05200000824120001d5034090502c043e01021440d5005c0702008a0001c0c0f100c500200691218805507464642c024820389228801d15500d0002038640490741c002e820340c0a05035125100d1904030140d000d01880c0c1c0328142e4140c111540b01000c900c407c0e000220490190707841c281031851084010b04100c03030f44881601200c09040092019140030310071200310310030a051207500c0750902e2004030b641248000d075803102e00d810411700144044c0260401542103500c00300340e4160805603801c81302200d54000040c0c50031179400c40865a01c01003940302d99045202861060003031030510b0801403e50b04040c07100d40003940f002886a0120001040e0104012000d29010701d031810440c07108103254 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 432801312 1250 432800062 432800113
    0x6101814040605012123090a200a090c02160e0105091311010e0f1c0309080307050613030201020903030f0a03110301030807030f032705070b12040318090218030f 71
    0x1030341c6c0c039100c0c5684040c00c07480702c1c2d5800080403106031520708144296104c02520400300c42c2c0541000210500d02c440010a1901a1010740f46419643c84c0010b80e10143c00c0e183d8025095005861054109121003e40710002c0c200c5103004403615490702e0288a20071000030b02e064a0f0301580e88401c00010000744242d07480903403d2a290044415160029005045550321950b0010703254501c01c107820a82c41488001c0c0d4001d407924604950749446040d124400c504009100d5089180015a010300340f8aa01507100e000340700050602c1141404240f45901000200e180c00e04003081031400e4590501a00a0540500c2039172415945951384222042c01031500090511000314014401c1c14442d03440303043c1180c00952140310808466203e080010310020064440e8051a403000c60858101b07011a170443d9401507402e9600da45580342207546180f524201c404424400a0005240303e50340051705004000100340d10404aa11003003519042010203180629040503544215070015003000580d41e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 432802562 1250 432801312 432801377
    0x1a040305040e07051b1c0f0c060e100501230307030b040803070c08192006010302010f03060b1215041e0f0b0301090305090909010608060610181404060501 68
    0x12a03c410105481c2030140c805812060410a040c02070007031000500c5680b0400c0080c940da000c0c0e00190070440d81d00100c2a00380c4003180c00c3e5110080028050b61003003d901400c44141c40c100840207515a0a8800a07402070b407200300038550341403010001c42400702507541d0407001098a646180e03030300041c4540042016001c00c40100020710740d00d0084800085d0103901002003960f4003600040d454040305c0400c11000050302c900340780c0d0f240a0304809410342c60000f070720082400d6881d40c0c0c01116620040d5500000301901c42c0d20004e401f41d01140a04094080c41d000e601c02c918100d4196122807805081c0b42e84203e00345601055201c21400001c032640e01618008104091003a0000300a484010300d170030340542ca031042000500d58020003a1100d03c4040310f1401d12500e800d80d525003a030383c69000b40850b035000380001c83c42d20302c1c042610000d01041d504003002c10101c0d01c0712240e0101c400745e00c0440d903000c1ca90084070781864644a050003500017420b02107a1501090b14003c8400526801d4844 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 432803812 1250 432802562 432802589
    0x7080a0c0308030601050903071e14030312090a0c0608010302012c0609030a0b0a050414070b0a030506121506010908160b0d0b030a030c060b0405130312061d01031a04030504 76
    0x511703920400440780b04460180c110303480c1640d5041101d1206009040e13100d11806880c1004c01c014083d08020700002c200140194101030700019044000f000141c80500c135071017603100c9038002910101c464001842a611031516561441c0000b403d02101004001c5d10090100d18600035015503540380b424446041c3c60994031a01e098001c03928007000f180e000f40038811701c40200451000d040d0002486944210000020616441400359884290717011b0440c0f2540140a86014144240e22031717640244020b03c500028a02841c105040c4070b008031120f1344015041c02045810750300504800d00038807940005150071005458244401140c1c0e0103070f200401e100040007040c004103a0072002c21144014241c1d040f40110f40b801400140507480100c07002030038108a40c0c0c0915240c460148100041d41c0d61003140e02c0d01c1d98003250201e141a868100d4183ea03100085420444501c20710303014910070015540715410350610961103001c6c5da24040030103406901700400682c0c00410348040301c2c2c030301c0036904 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 432805062 1250 432803812 432803821
    0x70f03110c0d05030315040603050304090f060302100f020d0503060a27020307020a0303060e19021b0f030a0e030105040f020d050319120f11031b0d050405010e07080a0c030803 77
    0xa05140d0300000e840d0b800549144140107000c0040025802458249841c07a552800101400b040da0b05d6880301400300c3d0400e220401c20141c50360010410a14a444d0015105460b030b80082d42c5800490300b101c0005400141d8661a42d0701004503d80401e45400c4c200e003589803d00c00281c014105001c0d4040c044000504402043ea1504400c445451412070540d103914100000940d00c6a00007000e8000a0500c82c00084880c00c104285003e600c0c84c40c1c2601c0704081085038500654004400c0a00350b40c49240d40c007003048024031940e010408100c0203103a540400c5100203203442c044168440c805d904d000c060000250f0b10541da9030a20780c2c10740380110300082c181091802c0d0b0050f0f407420900381d11918050702e9000c0e07001442c40102c134407440d07080040c4007047d00300764210344100000c00342000003000071401c03000508448c7d170b401060300203038545041c0700c84402070141c901c2998221a5a91034a42501d03601c0814070050014008001c020500401162034241030015031384800b4120b81300010215 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 432806312 1250 432805062 432805097
    0x901090b01020c031009050d0c051e0c042c0303191e090f061b0f03270c050306090f0604020913050a1a0606070327030209181002070f03 60
    0xd40c04a08000e0135255171182108440c0081c002092040b10580103159082c02c1090240640e4100700b41c02070014204130012108001e81042d940403031461030310540920305182e582d513004001c0c0601032a81007803090009070007081000081c400c80c05078160003d004200e0003e0880300000c0c0480262840440c0403400b1108001c5540413071303d642d8000740c1c00c0008030300501448590507400c0a2084604000081c540550401c4441025601d07400041146400d074503c14030940000c0028480340300c0c2c65413080a0100c200300646642130044070040c400450410041c5004d00405520400070f001515492264180345915484010402449911108081420b039644551604001c0f6030180071030b802014241003540c4041a8110410340074104400086c04906221041d0380f1303031a5054440d244c3c01c42031809039460078144000d80558a004801c000000b6990700e00c01103005045017210801e040406260076400d0110180d520a21039004001200c0041d00094990951603054941100114000c8a01c2c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 432807562 1250 432806312 432806323
    0xf040207020303070b090c010801080d1202040f080f07060203040e0703090812090c030708011a120c10050a0201060b03010f0909031215050f0a0e0f15060403060e0c0904020901090b0102 81
    0xa03402d0302c0b001c40c104040003012a0300c10300911070101242d280300d5040d801140e40da2001d015450b01c40d00801c2040200a0207410041d03816101444054101600d440550104ca08540d006020301c0d8448004000803130001d100d414081d00305031001e035103010304140c5c9401c40008040c08140400d9615502c1c8408c0c0041041030722402c0e014a8000041e130b0404940d42039546c2022031145129000d4050005400e50051007200c1c0c1900705100710346019552601040750503a00c090b248a0b06024910b108040c9550b6420b014180c480d09450340340d06c03442c00d001e00908403001ca40142278480c40c100011b0020700704035403407001100c1c00034034080b9000c510317890100c81002546401c488074500b8114103400e4000c04541e010103651060303e442c0084c0c001c150030045004001d1196035840d50308440031070840041d1300e416a5015144810302c5004607404800b1a0700343e0f01c00c0e03100391203eaa49203000d0707001c07140501421072049804c942411690506030000780480030184903070340180350760b0311688003503074002d211 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 432808812 1250 432807562 432807577
    0x70503130c0b040e13020108131a0f10061803080f0c060106030b030c01030b1309050708060c070606050d05120c1f06170a05030301140d050d03140c07020303090f0402 73
    0x1070802425654044465041e00103025104084c0860000110b201c81254080b4001c2c0c0c0d0169610195900da0030b4500c44017000c8640140c0e01c00e5000a0203007588044c080f5030500400b11350841701d52615183c0344084034440585c2042e4108180da80c5801c000034044103250040e240c010003c1546c6007045070122032684a15906d0209074040c82000080041e09a801707000c1c40e00f015419110b40345d150500440403502030010a40c2d108051080298880e407003503000e40c0c20148148200c401490700c42c000c071403806070102c1e0b400354811400140c3d00c0070000c0030300440c0e0003010150303031000751803040341d44e03003516808020110340c0102400f181194203540200a90183e01407502d40040140e180390310008040c244d54001c290075200c0400d4407280003d00007030800c071400c2e08030b009541940d08007242e10f00c1c40300a5092455226001610120220f038040c0104005608135440c00202c2402076440c544440c00000e00ca040c15880502803200507860101c101c1b4a10b5100301c0c0e0a104aa02810014000313018020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 432810062 1250 432808812 432808823
    0x71403160b0606070b07020c03280818061605011d101e0f020910021914030912010f05091c1202190f0e04090c090504060b1207031502070b07050313 65
    0xd02003001d40114403100320030401d8050701e07419590076250903088024a00d03032b41d2200068985050100e4213600161010143e07400080e401102504001900c40d000b4404040c8001000c140382070402409110b901e04c09440c0a9940c51011404c50290340c40f164072054180790551a40c0750311600810412080c8401648520b00700070600c0e444c01035100135000303020402c4c052100034042996131400081d1580b0802c10700c2c0e8a86415407902c0c0d0706c42da003910181a0900d961301c0709100d103d0031030789d480c20a003115840480c00095424003000320001500d00103814011310f5000369181514200f03001c0c008030010b4420b401c1c421404035000e01e006000784500c810880072144141203108001f40e20184110011000755a0f40c00e580300c403c2c04000c01c80d100102d00400035091900100903910482c1c01c401da1080c019800082c05180071000b04880600c0e5119070702054009840510401000080035031990b40c680360b04601341a503d170340700d051800f0060056000d08c000400011140110f40800e01d2000e580324 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 432811312 1250 432810062 432810083
    0x3010c090801050f010b040302120f033108060601110c0303070f03023d140412020d0c050703022101020406030204050f0409030c060b0f090c071403160b060607 70
    0x410010261559401441e889500303080100d0000d030702424106060302d04001d007503864146180d003008a0012682c4101e0710320b0198000520440c2002e0020741983c4030002c0400e24012281120100206c0c810b40501243d0405188188042c660002d20a9844402070038a2007046005414051400052114040d81844001049001c112503011401c640521079021125184071889820030694102015045414850072041508540aa8034220281c3d00f4901c0040d0a0028038160a41c20f0400c403020345e130001003540d19014a0340c0c10008842c011105151070300148036580d17100c83d10f5194612003e031050800c0311080454040f00d038060104400c0307101c001c41d83c551781c6200c050080d401501c901441003144052038802c1d810b1500407007684640c140e40714a106811a5511300080c000d10b03d5035500200301c6c00380490141c0b03c0b10001801003900f00c0120351900101d240402d450000412211610f80040c0020074102d00024103e0b406a0b50004c1080c1035541e414002c65841e010303805025040c4041d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 432812562 1250 432811312 432811331
    0x7031a03120d140702030307050703030204080f0717010204140603040c0b19090f080a06050a0b040e03090a052b05150414070b040b12150303040e0109051e04110f0301 73
    0x103000400c00140c2412043c00b021812510000c28190221413820150300708200050500e132140008114441c0300342401400c05840750241c81c43c0800f40c468800c01d642c8064130911440e030a04075140d190743c24000007540340604050465602c1071464000c1409108084013290401c08903214a2000d00010f21030030380c450a00840d6008c50068105c107003c0820304091000c1201c221241d00340c419989480000d11000040d035a49800904005060301455541c1c0c100d5510030369182c3c0200461001c802c4025070711007211504101a4808680c02103100700f2412200c088541d491f007000751303420f2401481581c880740da2410b0a41c2000004224500100074071001c000800907003071148a100c00706034048034290350301d509451004c0d02c00d9024061400f2401e001002c814010101199441030008460041c100b03050000f0a1468020ba00203181d503000240041c401010a88a22030b4001400c0d46810860748000940c004203c6001d040a8080d01800f080311140340c07112a038104d0030610180c0200801401c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 432813812 1250 432812562 432812593
    0x6091103040b090606090705071b182912120d1a150316020313092405130b060912071502010605090606130f0801020a121407031a03 58
    0x48034101d80180440b004a0310091002481c40e110f2240034090302c1315a140d00d04c040e102c6030810340d003c440510101621902d1485d20702d003040010708031790451081d1806070741c1c003080581e00c0c01c40394038090907070300b540400201907440036441c1e5029054505a282075100040d040c00c003180454050000711002501410115281d0300c03101c0d900d9120006030886034120b40401c6039401064503041e80000c0144003040d490031114002181c200c1443c01100c3c90b05004980c214022500f40e403180300c103207682d00503800000740e084003106107083c0c0080150f1602342c18000050760014044c00031040841e9103034040500740d10796004079800300c0e000600310844200399401d242e0ba5400c040c020107c0341d03410790007141c240c10300500a006c190381004285105c3c03540c494050000c0c4d078204032000740091400010014084444001c0c100c0985102030026a540350402c03009810180792501230b18042c2c2c541003220002d81c0d03c50800940003151803801051080072460345000c004200b0440c1640350154890700b103105c90 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 432815062 1250 432813812 432813817
    0xc1f03050919050a1514010512240103120906020706080c04170a020310090213020a0203090a03060c08070801180b0a0510090e0a021306080c0717030a050903090d020f04060911 77
    0x5204402c20170003145a43da10b8800c0e9110790803082200c0c05034600621481c41e1000c0342500c115007410031038403000c15446428040c0841c200080e0003008403200180180120a49241065052801c0c4130000c07918000000390348942d648900c0d03080104160200d2030b13041101c0c044400429842c403104400c00d141401c03c0e515825010800c0784248110840e00c02004660300070b00030001d8000f403140b2038146648031142c0c081d601c0903a5200450004101030082950f440e490780e80a907005640016141c101020003411085016200605001d030460042152070400c2c9041e00d5400b0103c5804241504000c0c00b01d140503150350030866020031300c60300c8040c003691b0004041c4101c0c0d408003c2000301e922071070756801c02c81c46405040240840041c00c2801007a0140c190703650410f405400391072414505841d0007100307100400b02101013140000c00c0c0803409125000e640c1c1c00101c0000079601d402080c4000031284009010024090070002104d18900d40c2c80e42e0102000b131944c00b03020320491000700c406003040c4c0e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 432816312 1250 432815062 432815083
    0x9080301030305030702071403031209010b190f060c210905040204060f03060f0f0308160b0103031707020c0a051003060816080f0708030a08131202030c0c1f0305091905 74
    0x40c80341f000d000440a01c1003040d4180010042c010b0b51800349480e00d41c0c205407800401c2090290340311007403035801d521141012a00100c03180300d2207001c51300340141030310001300692000040205200c4104080f1343c500311304007401c0b6034030400c0b603418941c81801500c04003010350000364090301c003250000e259600b01032100910340e89a41c00b00801c9448100f1760780325414900505900100c140c1d002c0c000a11000d00500032050700c00460408280103944444102400b6041140014039203074141c200305c108508500d800c044280080e0107030546a50203d4006a86440707024451000402007880c2d040c004e40c014006000703004103031000343c1c8801041d003051503520310441d02248109442411001c1011404c03101341c0c0c0c50000958175040102c81b00b2140c2d158041c013034100c151500c0340c0f502c0000d1041c03842c1c1004003006030095a00d03a0b03101e80c411400c02d0103145400d4003640c4800c604007483c092004c00da40602109040001d2241c82d04001c40349850701483e0070b0740c1100b481d8003204040c07100029105980 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 432817562 1250 432816312 432816317
    0xd170c070807030503040603021b030c010c140c060a050c0705010f05090f160e10080a0c030c09110306060f19050d05070908030a12020d0c030b0a14180a090803010303050307 76
    0x145a81c1d411055840c441840003078010b030000c5c0802d01445103e81c000f813040c200300000c0d4540090407a80309505661001c080385099a540308041d80d2030503001030403040f0890240400900300305082ca0400d403240070050501c0c400a5450b000520007503213000540c2da680da0840700801548100e0070900006010641e00c4c44424415850140c0f900000011003505504d010311000e521145070103610426620081d05006007c46120720201c0d500c0c01c01c1040002e00d60080c00d00c3c0f4401482c40c03e1112504040c2d8103c501c40d9820049407402c0799400508072500500c1c280e0301d10340d480001026500150148880c2840b02c079000b6000402401d901078007034081e4020381c40c000c2100703844520342680c0c1000d07684a20020398000b40209507079103000e02409101149110405454800c51031064001c03aa032400c0903e011a5492107081c2648c00c0072a29480034000c1c420040b0000d00a0f000050030002100c1d08110030040c2410005000400380d401058816621129494803540c480c900a02240c204842d00d100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 432818812 1250 432817562 432817573
    0x105191413030c050904050d030b15030f160e010905220c0207182a0309060f0c02070512190512040909060b0405070503180312090d120c080609060d170c 67
    0x201d43c94905c080781d01440d440070080407085a0074406501030a428541329611000c20200f608200c40000000c61040c01b000600300707054075003226a040c41544c001c03418000c021980c0311404869030040414030580d1403c07500441400c1a80081c103a92444820744140f01034140003601c00c009400042001c1603800d2214000e1030701003c0200e240c1114071800d0a8001d0511032081c1c804010540b09050030404441d160114441c1c00d607444000030b4800784201c0f02c4182d50b03122040505282d040c020072001d402c044a815201941c0c03009041c0d9101c1050050010202107e1303149000c016080042070349250300c10307154a40720341d40d03001e000c0d00070000c910090740c0c12400d050200469241911940b442004184c50f500e080d038441e10140340680c081e14507001e9451004010040788510042100ca110380c021000400342d4090000c7c0c01002c0d003030075644454689040c8036540c00f440740c21400d041e50001c0b05503102e8000d0303a00d810000c0c15001014102425400d05501242c80750a1442c00420468004030220780c0e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 432820062 1250 432818812 432818819
    0x31401090b0a0e030304020405090307061401060e0901080d0503180f03120105061603030b0a030c0e0619060c0206090418062703080f1509090304080705010e0105191413030c 76
    0x6030383c045451641c054004200040043c6010750056400485000490342090b00300d940d00c0c01101c6141d103825005496070b00c0100706055104e01e9405d00d8040a0b90900c100b03500d800380403030741e4030070308420305040c00008800280644810f002030044601003108840c40d0108412500f07450340d0092010000780000a00040307000e0a100703084031210200082c40c40c10031200d50314214020400c50250076402182c002c80040810452140c080103850500300b05203c0b803d00c42d0030402c595680c00c900042244a40d10100419500045400340c682c0e0140d800350b0b652185240024014034044490f40b04051016034807905103c0641e02644504070050400c40900818010a00281c0d083c0c00307004000a4121000805102806e5a11500722809107401c2100010321030003c2e4a0302421284002a0f034004642005611000c0109000400d82824034692058091000030f00c0c0744101422000e41e01c40302d200c1c4020403031040404030105003202015a461b414000d07075040c01e240d460710040e69804200071010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 432821312 1250 432820062 432820081
    0x1202011805060f0403110d0e0907180311041d0303040515061c020d02091303080a1104030f03120f1406091e040f0506040c062d030f06031401090b 64
    0x26654000004002c2c41d030301c0d4643d9031580d042c01001181086404914006429070030000d0700030b1900b42da12600c0464162406214510100a1204040200f51107210306003030100c60441d410f9130b4005410300308031200400814040c2c206c242c005c1902d241180840f9409400c040065409907209805880030a070701d1844140385480291007155004401100384103075001d12142d4155598409007102c050b104a940000c1d42031a41101d143c0c0200c034000c90094201a4070416442c2c0c0101e81d60010004905004402c1c00d00d406603002c01818150101c4100041c180104412290b0754008082404080c40c00120350020b081003d4a00781000d0b071100200700207262120b41288074a81c696840c000b040010700350700c1c01440c0c0151003907403055404600e10001c00e0040c8440d502c114019030050145501c0c02c50000c0010904401c42c580f01c000c080001200d0075043c4040c80c0b88030001c0e24000c01c3c1d8081c0400c0803070087c801644010034402d0090013880202506411035132090303010f0010654984c0e03541501 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 432822562 1250 432821312 432821351
    0x927010e01051305070e0d050109050304030308180304030b0703020a020f0105040c06030c020120130812120f04020f0f01090b070b070822020411160c030b150307031403070b0103120201 81
    0x30003001c10480d1b241d019050418090601c0c01c2406000041060000f50f02e40e68203503880354005500194440040000f16000d192018110480600085203480e2460b1985c8103200c2d00500a4010150000b400070440c43c42005000501e414400007013106003410f10341051003400303911440d40030a007003c541500321401032040212011200310340100900b103034003003100581d0181403009050b090081001c00d400c181045820000c042103400513a0b250104120441e00b110024a001c04a0210104010060700c8455051408513400c0ea41c01040d0000e034001a01c406d40f00d0f400030070560724003144001c107009946078401d010b11440d49440c0c4942c0c54540060940301010000110030f421310203c120010b0a05501007001c2543c0c03050042d0802c20051001100d15210b22402d50780c1004006060081c40001443d0681114002080301341e0081c1b20000700781ca6403000d12002e490480c8401032201c0241d420300454071600e034001000001503842e23242c071600003a40280144015031900300d6003040c1c100c14560 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 432823812 1250 432822562 432822571
    0x30b1806040809041407030207050c060415110708030c0c0907080402101202040b0a02031905090f0d05030903010504050607030c090b18040b1201020702190b0927010e01051305 77
    0xd490541d0360780e01e03090030580c03251880c1504079541d051898044248405038034000c408560b400760345c40c64542070451415100540c0e46224600411003007140340c2000b0046c68880f042410401c1d030700c80c00e038860310b421b00585034008090b5000c0010070f00403100c800308031880300c1c0b1400c0724010120746815a0840c0c04800440d0000d401400ca101d000c070920b8011054009000c8411030003610702500c451068441b40c11603480c100260340046103a0054030300743c8010310300c0f03009649412410580070350000b400341e8800c8244c00340640c07041c0300d441d000d006040c8200c5008110142c0240303e070b81440d1500c2503503400202c829000191804007446d19051081c9101022181234039421030400e0540480b481560800c0f801250380255240201d2005440b585e0b59150805401c41c001a1100305030300501091503070300041c01001c100f10000a01c5540f4049040d5144d0800c166000c035820f48003500020303501c981d54402c0e8183c40682400000e002032031a9100f0781030360001c0c1c03811010506d0443d80c01081e20313010344 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 432825062 1250 432823812 432823861
    0xf0f0b01120c0804031107030507140306090d050a050c07080d0c0209010806070e041a0a030b150105070c0b0f1c020310211e080f040807060f0503070f0c1407030b 71
    0x3d000ca40864840c0301010346645004c400d550841da40d0b603a402c0e1810070f2540c07000c10400b01c0c926100c032007440e050003070079481028100500080900400c0080041c400c3c0b2011205004000c640c0c002c600340d04100340d030054071003901200d40081c1e181d500a014180d51180c102e21070340402002041010001c100305000384030030f071a0726521128480801c4060001c40100a4245105041e002182e540b0045490010342c02840407007a0f80c1801d50b46010b08880c40192903051140820002e4006440207075100c04540c0c440002d103071103540302181810140716200f09001b654980c40110b5424802603401140500400711784a405240d58070101c00941030380700c0600f4040384410040f10040360803030115103014600d245144201e002c0a0750341e5450398021000410310508041010300c282c0c44100003074009040107040410302082000002055071000825490801030049903580c49240202d500b20042644085859101454880220b503540c6c1c46200607601c02220380040341445031030030301c0ea404001009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 432826312 1250 432825062 432825077
    0x10060506040e13020d061e0612020114030702030906130612090b130303061805060a050f0603160903060e06100905061305090c1206040b09010218040f0f0f0b01120c 72
    0xf10880c030082e03010b0002a07800c0240d500500300040c1e8288541c40ca140c0d04016481406401910040211206600304000486544103805c1c0503031b0704131403000620752000003840c0e41ea0b510300108a085000b01c800b090741001011800c0c01e080040903401c441a26080d80d00d1005048101c1e1106c42512901c0c400034000c1c62014000c039840c1780b428a5801610707802810041009035440340c0c4a629210303144140054240d4070010301c40e0720b03c1c10801d010020001210001000888080041c0e000c0c4400340420461210a202c0c01860500640b001d400840d0031140800c400c0441000c4503844c0e66080360b0352041014104404140e850807407003024000c00003c0c1002881c1005000a54001e0030054410a494410b01d200251155600780780421429442c40113043c95040a20f0040c00c4000041c0003060030b64018800182050311401214669040450700441c980500d11521402032250205000040782403803400c0c203c031203050b04140b0b0003200a036903204100c010104400e080704c0e6580040350025820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 432827562 1250 432826312 432826321
    0x2061801020a0e0f120d0c060e0a03171b030a02040303030b120705060f040b03040609051c020c010305040f02041415010c0804151209031707020a0308010e070908070810060506040e 79
    0x200700303142540014107003c4102141005e40741c68050940d000340000740481c14080200f00342405180c1d00142100000c0c221103005603400340035400e1590742c0c103900c409a100051801050801c2804600c1500802c5035680d081103101580a540580001d50100e030802d00000300300d080070003003d22a03205031000f80c03407900e007400700301714141c0c0c8a4001c0b00d420030018003000c03541c5003072403000318007541c0b2845000400c10300c41d1a2080c10900840020881040c03d28040810b2a1b00402d000216400074600020607903214030340302c403821a001b880a50400c2c0b070240310f9000d0b07028655074140614090008201524200001101c3d0200c401c01c001700000c0b0140402c00411038600e001d421100f03c07030300b8400b907001207212230300f01201d00e040d00640c00034801c0040550b400b070a500b1500d42000c1944080c2c07015401546014203241411b10030380d005018004009502c06100329174243c0601056401c1e118596910a002907a035140b01b90441425494042c00140a191060440741101c05402d24069140d49 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 432828812 1250 432827562 432827569
    0x30206030a0b06160b061503010e27010f05060d0c03060e01060803130612180f03120f06050f03060702120904090b0a05040308010e100b0c010e0d02061801020a0e 71
    0x3020740300c51145901e074108240c003039980720007820b151645030480c81051880ca0814540940015003c01c1c002c00d001010031391040300030303000c0740c0c1514440e14850380300f9100c2507449005a1940c0c000c05001044580c8054203011042d08000a0b01c4521801480503456010411020310701c020070040940c500d018003080040c200b074000243d000f14207400010940d668180c00d90460317002100b040039062183d10144040c980044080f481c029482404025400e2500e00c642400100000d001c1c010222003041d100400d44140724448a07001121400d1104006d81c0d00303024050301d0503024451080018603904d40c018200015400c0c440d01c02640180440c2c60801d0401055074424038040340c0054a0340380344404034500091840c000c04e0240000150751a160038018108070303041e04200b0f070703d1012406004807040045801002d8442c4140b1082d07131000300d03040c03443c0181182140c8100e40e0042c5203a01080c03030b8001c0342040c4174101107900761040c24441041e103800c030311807060184c02044440358001810300303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 432830062 1250 432828812 432828817
    0xa020423010b25051612051002041404150b0f090406050f0303121008010213080f010b2b02040905061b07020306182e0f06030b04020906130504081801020c0a030206 72
    0x50013a01610601c1d40801d044a0762109141c00c69409000b442c1044405c100707080054004441d0320751411814541041c0c0440599040c1050721442107448844007044445802c004030f00034101e0103005070340e80b84140451844c5030040042a40302d245000303400103003030800380b4081c0d03074003800203020318541a40c00c6002140c020300508a0314a01c0c2c00362401160030102440100110f8601da0042064a0f1800c860a4902921b035101d60900e07906280070340320561541c4443c904100308001c101c1c3c0d113800042d046460a440265006940217043c080785800f07000300030803024080e40c0004803013900900c1c001d04c039001521401030002e4159004000040144001007060381c5226480b0090b200c40c08240410f0100124004080c2d42140000c0c0340c460000000e40d00c50760083c0c1e0100380051040520355220383ca010f100052003e8060170150b00014515034515a01c612011480c034010400b6007000d08084841e600321004041401c4c8100d0215802d0390b00001303010700071441c010903040009003180d0034050144c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 432831312 1250 432830062 432830137
    0xc090f0218220e0102070b07020d1d06090315070e0604120305090d080c010e0616081b041205060f01120f020f04020c3a0206070509030a020423010b 65
    0x14201010310710488000b9005030140200c070b003400540c55035180d043c26101048060000d209662044044401982e004250400e80070b1000c400404404d4100c00410141d02c522840560700d801100280803031b000c900c0900e2400b85581c1d03643c0718260000c80303050084602c200c0c0204200101c080010304c0020384640700801c081d01e0007503c04010920682c4d1401c40036086016006402e94448499440d00042000f20a5000310b9649071045070003a2024040c20f0980c5c003404d407201c0b10100d40503841c5c0e8240e52000b200c0042c1112032041d00d0030301580c00e002d9111201034503074030644102e800c000241c5032400d02c60700010300c2c3c100c80300d801c0e4046142e0800c69445101100a90415003d0050544652060103441411201002500d1001d000e40c040c902c4066015042d01100e40200400400300e99800551a03a01c400c05080096549500c0c0d00000e14100006800941c000c0c10030800b0601c4074080b10901000e210358440c0c4501e81e98a0b4200ca503024050a0b2000b450111070a8070b19102442001050510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 432832562 1250 432831312 432831349
    0x3040f080c0108060a304b0804030b040302030a020d2309040e1b12190f0501060b030c0403030e030d1b060b0406140907260915040c090f0218 62
    0x1000c0300415050102d104542c801d880002800301030880038005960551f40b000f52903110600c141d07140313000c10180c2241c4008a504094a125507080801111904503409190001461070851030280740081d5242d01003900a8014012201800c0000c3d00400307029401107400d034200301405080588980c4c81d90000901c0039402a218108403030b0f000805d000c10580d200c131980704000724a6200c001c0c481c040030840560343c040e501014024120b11070300402080101c2d0311001c03010b07207501a81842805445940c111000740e50001041c030480103200e40081040700c1c481e80792501c4a0445404143e00c0c1d41c00e850340d000110360700c0c80380407007110740a8401c2e4451b54851a4000703881400340000c60b003103c0715604003480101c800e00c901111898840100741d4400c40600c0c1c800761800c0c900241362640c080b45022a0742050034600440d0385007005000140d03552036581004400ca00d02030030f00041c2e44060740b056440c4240342c4140000c3c1c0b070080340204c501d0841072520600901b1010f0050000d91010070548240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 432833812 1250 432832562 432832619
    0x210106120e0c100504061d0312030415060618060c0b060906061b0304090605150405010c060f0c0c02010807030b011d0d05070e1006030506090a090203070803040f080c0108060a 77
    0x4441d070301d400007903c036480303a6130310780d601e40c1d00b4403001030700200103020741114880c0744c0d142c0c94a9940c0e000420301d4101c04100e180940304d484500e04030456580c000b88401c0410b04224002c5086035201e1003c4000c1c0c83c20390441d41c40750b50b541c82c0135958401c1001010304000181000207840c2d0034554006e6401060280070546004007040c03410340c0d106c4c41028540016080002c040110100710f002e81c0340500801c8440080e00f4010200c150514420340c0b0415048c0007031b00008100703111079544603001e00002d00ca014072034058040d00c018031b50307a0201d9040b800700b82ca082c0400c100306c7c840d1041411214040e115282c203081940c0c2001c4050341c0e000700440d03001004a0711440003d1003030020400410184861078094140700e5040e03c00d9015a402400402d86800e041112540d10900c059401104c40c0c0790025640c00c1e540086801e00785981c00c02c030f0283c440003a0004040c002c0030807602c126045003042e45c2c51222403000444165106482490b4000d085c01c4062102e00a14100b24141c810700818405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 432835062 1250 432833812 432833833
    0x80403020c0607031d0f090109050a060314011e02310911270108010b0315061803060108010b0a2c010603060608280c0c05010e03210106120e 62
    0x619a0303000d4402100045d40200c24443d905145a0240c640000110b58003d2070400f80404160809014400c03502c4c20b80d200c80225044110aa010801968001802c81510b6211460180c00780c405c51210300d07840e280b06044414856014820707a0207810071410481c0350b80014401c49c040045100ca03500d10000310703206002400e0f141c1840f0701f6402c0d800074000203440780d883c401034401100c840c03015400d8000d0701d550802241ea81c400819410355005200040e103d8171410080d418007003c030311003103810a800080845036080c1c41c8015001240c8100c0c00c07a0725580e200c0c0b2049090b100c0c20001c094005800c40c000380042c086070f01e03121144074249031b801c0d80c000c0540c030090703074103194280d00210100ea41d03070406201c5180e2009206030300014000075580700420180c2181700d002c4018110348807165541c0303001c0c400d1340e00c41c07640703103180a40081c001c1c0015510a0702c5103407244d20051030340300c00c05c0303c40d030503103602d6062401c2c814101c41c43d9440720328586140c036044502034403c052081f005402070f0503401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 432836312 1250 432835062 432835069
    0x309030311040f03050f0f06010e040f150501140a18020a050d1a04060e1015110a061506080c071101091d01091a03030409020a02010b2e0e01080403080403020c 70
    0x10b10081810340c1c00d004020b4954107085080c03046d10f00440b6496005040b500400080010b00c01d41100c0040b0210402984c031410140e90301c030161040180108480d1703070720341d414407002d80006040c2e611420001d500c030200c807000c2000411a6114170702100c20303c0160b281e4901c01c113501500012910303043c120700e03000b40e91982008560840031104a5500e020054a20609092080d400500302e00c420305141400c0180c06c2d04103103207043c81410072000d6881c224461070791040b0b58198000b1840401c96920042d01c2c90030720060200400705500350420500300148051040b086540a07010040003545443e00e641c41e15011581c42d42c58081c18820140b100051006456030030840c4803204002004082d41040c60840981320307441c4141581c401044030482c4282d038040125000c0b507290400c0180d0f80c1c00b1101d0f0513070140ca1805000d682c00554880c540701c130164270a18000c103c1c80261a02400400c40520942c1e40c1307802d05203001d001a44880c0020300003809040b1480c2c1003070080c01103954181050b0000b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 432837562 1250 432836312 432836317
    0x40605120303190501061709031c0b03191218051f0306050102120906030a0e06070203190f08061215070e0f06040303020a1509151e060311010309030311 67
    0x51003260351000042080c520105031a03a0f0300003108580500040d407520b1720080c200000c0306550f44d40080f0160200d21100d800f00304849948804c0208450394440b0340b85890000c3c86034880340c502a0003010f030909040c400141c15016856804641c0c1403507601044412201042a030548112050040c02d02050303a5442105200d60038604103140c40c503c0c01280300040503107041e54011815544032516584a12010006650404800380c40c0c280c1c89944100c10304028041941c408240b900400042c40758995012001f408032004403990b004801140b040101d03904040d440c40386001503c21800324659103000c0ca445c40c7d200800708111690300d034000741004a441d0003032f11303c1da000c22003040088440b4205000180e00c080000c80d0030750300706807a607103002c0c1d190110704070020014042d002200700000c1040e40018a035a400c4000c0780d10400d044c001d040001c1480c031030004154103011210002d85031450090034107513940f1251103416103c0c08130064001e021003003011130505454001200540c0d120502 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 432838812 1250 432837562 432837589
    0x409060203040201031a01021b010203120702030915031014030f100f0605040204080a1b0f030b040b0c07050a03051606050906060406080a030c02150f120f0a090b0a020702040605 78
    0x41e524102880090101d03808a900030880c50034019042c0c003280e801140c02e000b5003404202074902c0c4a03107000101d04500c90501000c0d1860703030207024020b039170741e00001604162606583c0c002c621051b580064085020403100c540000122920a010326240b00c250703600c28070340180c1110140001300750128101085e0b000f68030421075451806145405560146d1001010140c030114500340c01d0030350064840740350720b8002e822403110380b03522030724001409aa00c004000c2419211955502c1c0e00e030240c6001070560302550a405544007042c403c43d459802c490b040380c0d01c14010404080e01eaa415140303500701c074a681c3c0c4c0420010189001043c0300f4041d940c4070300040e00c00381c807071482c0610420040300d00b41c0d041651568410300410001a80129903940d0080d01110b91080141040c404000715218902a10340c040070049900c0c4800ca40200260b800340e040a11108201e9460741240c40031500000300c09000c2e200420f010400c0260b00f507005100041c00a00040341c03240c1c50720081a80244030b1366 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 432840062 1250 432838812 432838823
    0x150a142713021f080615070b0910050609070219080405031207021c020d0605060a1814060910090b040e0307050601030b0601051c1d0601090903091509120302010b0409 73
    0x25a1a030443c074028510348411556111120103c641c51031000342844001440b16004143c071a0720f010224080c001951031080d031200007035a59240c041801e5484080404d2500452428400410242d141003403101b44600c201e5401480c2c1404007090440d0f44000c41c0c0b406860340481004041040d071005c0c440c0070311507914141c95503a5020f80e03105218250054282110122103640161070051b502c14441c541803542000002c2101d803540c4000030355600d11513000340c10080340c00d460b240e000c101d182c100d0341104200c94050107240d51400c090080e610b9048070307031407210030110310b0500082d25180d0012031141800307000003802c5042d40302220328540c4081c40a44240e4080c07001001040300c000301481d0300540a00e4210309121140e080400700941100702900384035101c2c98a842d5080260100d4502d0342103450844420b03503518050701c00148401e090540010701d02140108038005200c80100c1030b0361540e5982c0341d4007447c0103281c60380e11407001005c80441d525146100025551400387c00b02d0940642c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 432841312 1250 432840062 432840091
    0x5090708060a15050d05012d0c0c020603061e0904050f16050f010c0609020d32032d0c0304140409020a0504020f0c030f03150a1427 58
    0x10880d18507180c0c004000061071424020201550303000d040400e800c8400689140c43e80c800b46182440c050b003030039034505004001c074210205100c50450b8103090b5003110a0070401c00a2010842190803004e41d1101a400900030404a030840c00c00c05031208880400d900788201c51100080000c1c0c44840a40d42502c5945c0100422401d54500340b007015088000d01c0c1506281a190030040368400400c12605414007010744100d405100082e082003410543c020310112402e0724510380035044401114980f9040f01c0340d441e500d14102d026149411040760000015410310314480d56409001c441030141c01240d030741c0b51000181b80d082c9907020f00030002000e0051900c031800d0007104196100510482440b5038200100034025844d030b024510203039182500c01507507130380d005070309800588202c11182e0401d200001d41ca0440c0c0c4000350245000d980032800d0300b48040150000c02c100c400c0c90340541081480b807000141000e2606072810b4181c01000e81200e1a4104100c0d41da0101c40b100300c46800e1300c260b06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 432842562 1250 432841312 432841319
    0x10b0d0c0804110907030e0a030f09080a020f0f0d050a14060c0306011205061207030803100b0301180b220b030f06150d0c0302040c0921030c031809050907 68
    0x1240111116090a45401070903850540c0340d2982442449085901580b0707039070080b8100b28400d030094082c84071004100c0d0101d950920780108000038403403110303001070000c1001088091012400c1c07c03030150024101e117191040c1d2403c02410148600c1c0f0250700c40d0320501c0900c0024401c0c00035140e074a01403e00602e1884542c003c45040c07020042c0030004c62001041003104580c3c0001e107104010415480010385551100040707929800490354505607440b5441c8000100206100110700c42c0054001c07040d48541d4540f4428043d00003030290780035410402c1c1d50005115429030054811b0030004007020400c60700c4400c12880d1001200c0d000240c00d80301c101c49681800c00300f054000b10801c11004007650b1403c00304ac03114106180b0300851140c50200d01030801d000d509140007010b150000c0c402c11200b514404041c182241e03078440e40b4003c1d82074001045041003001500c00d295905522001c41d5003c5039642120000e014400c2582040c03000300c0049003d20b4207108551140211000400b2032504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 432843812 1250 432842562 432842587
    0xf0902040c09140d030c0f020102010b090907030c0b280203120a062301020601050418021005030f0c04050901030f061d0106140303090d1b03120c11181906030b010b 72
    0x3034160680940d8281302000002984151480180e03900240510250b0040c3e100403405803510641e490b40c01021a828004800d074003107084001c81e4443c21a250800d42c0c2c5495686140c0501705200d504d01e0801c0401c0c9040c04440c094030b0900c203025205076403603c1002c500703483c1d0010007521040103080d0f83c0c0c4800c1c80301d60b04140c001a00d54646000d9120000703000c10001359580c005001c0c980c0a29198140103588038018540100001e42c002c00c44d031140fa5180310000c0040c0c2045600311034500c440400300d01442d840708112401d544025002405030ba0a544034480c5840c1d00803c11034200f699200c220100c1c4405d13040181c0c6240844002040842c40c103028812050340c0d0a80062103a00300300318641c80c60751a440050600c1303602503003440318a07146921450840003241d1010381403061440000781340c0c0ba4050b03e5071412510804d49502c1e200360700800d1240800f010240e0b10f0100c1c00c16404104080c1e00a9440280003a00490200d44992241e40d086510602a80300000400c004540f0603480324 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 432845062 1250 432843812 432843839
    0x807020901060203180609010210051609120b040b0c040504090c0305060106030b0d12020a0b16080f01271b081e0603060c0906131503140c0a030f0902040c09 69
    0x44a10065003850a81e2585204856900318603511a5000047c1400181d00030300900b50003410b000d800b040203146c40d803111141300610300300000000b00c41c0000450300050b8607415051854000761030482594880d9940e4880c1100500081c0740707001d05000004e03030760340c075400741c0580c8a200d01d500b03510a910314179005250210680009060604001080364a911602682245550407030304444808070364403001c0c0d0920425103400f6140c00b008400300308403080b003541c001c40d020003103581d102d00d0350352041d441ca00c07148070a009180d171440c0039060341060300d94250001c140c0d00360400c40c005211800b039541e00c6040e12181e650f040204a84100b00505240d4071068005640d0004100c080c141c078200b0300290700c03100d00900710030000a02007602003140d180d0340103a0380c1d071400c0080c07407000b2107455003502c46100d4289420540083e00301103c1c4071451441028640c0980c2c0d840d00b0243c2000400d0360298041e1140c624401a0503503070f01071900141c0c0c0d50340114008016591260b40c49075042540c2600002e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 432846312 1250 432845062 432845069
    0x2100f0905100e04020306042c060109150314071503060905130c03150b0a090608010f0c0f0f050c03040e010609060201051b03130f2301110307030905030d05040807020901 75
    0x1032071803140c0010100d4100141c403e0910040300c0045e981d940c0d0fa000a0014414034a80204c01408982c240c03000303402400e0703c10105a1001c080314856070b40c64284074240d42801d02250980003d00c201000010140203c83e001002410191407030345484000300480d5040341044200004e8440310308002e440a144a01c13500446003000080392029541c03904e031222809880001d201808242440050203150b9001c000b4044c0d00030310780c04c2c0543e644c02000003d000b0318028480c40b5481c0900300340500f6203a110780f10945003a81c90701030749190751103400d9032441d046030000b4051200c1040720130504002803000300043c18450f85105610350500c81d00a14000d4160004810b40e03141805024590f000d103015500003000d140f1800395a69680307200b01c0107001c40400c004000f5503083c81c1f440204030001660400324021a0805500c07680c60301d07a128240c9070100704043c4842402c00c040380e40c0b98429000800568003c0741124503000100282d00212001103606030748170100030a2010071454001d4149004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 432847562 1250 432846312 432846319
    0x306040b01090503280c0f09050f1303050906090a030f140f07091802040c0f0e0301061d06040e0a0302060f01140f010309020109090c0c0b0105010f0203030c0703020a02100f0905 78
    0x100f428007020a560b1410460640070400c0d518100c0c602d081203a040000100358400000c4c60f0746541e1b40c9840907100005d003d561700003424440001c0d491f804148544c0c0c070030318206016a1a00310300d1313201910b0302d80c03142050301d40044007005000c00c5a11070300403030401144110914070540320f1504000765100c1d203c840b01d800340c0c0c010700c42c0280d6202000031004190381c440a00081e405400d40785a901c25801d800303000b074000b42000c0446881c160402c21091803203980341c5079148050002402c150880300140101669900554815542210144191503000201903c009100b46c40045001d10745012a10100e00580c400302c200050190100c0985005210381130219440004d800000394541d00001c800504055551002d401560b20501c4004018010400200a400005d8500501048c102042a10101d03002800001c13a94894030000c0c2e43c41e0b04603406903041d500c030300070804641e60000c1c006808600c03400c4900c1015994000a01e82c0344071031601c6218854603000300c05000050503030b01c00d43c031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 432848812 1250 432847562 432847577
    0x6091512090111040e0c040510020309043c0e010e0a11010305010509191407030f0b0d0206071e05030a11060a05090607050a0917030c100c050921120306040b01 70
    0xc540f500740c280c40c1691201d1070b01d004960b4500760681e419002c0d9500155018507580303441a02241c0120081c05812402d039014060a0841e1a048611f03410b03800501041c01e808400c0c0c001c42c00404071003942080011180401c022803801c010303d0a559030580001d0076604002d0f284410400c04a02341090401c0c203007010302c1190b14080011b041003d004002100801d404090121810001d031300100d011a015508600d650401c800010014005041030031410380c540b4a0180951414603816800540e0041445203099825620b80107212002c0188080c2041303101c0c400f400098090000d030901d40c01c207a64400800030707000c00b40c074a45140900303095916464070007072061205002c102d59034056098100b180ea5462016021618598a94088049040340d00d5213685a08008401060020202c02c219000c5440c405403138422500914141000320b0002c1000381d101d4103103058803159064408548508050301203056030300309601100f608204042c00410402145041e109001c02c100080c60f1100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 432850062 1250 432848812 432848831
    0x5090102070911070b18070303031a03010908030601050901110319090918081b0a050303010503070e0106020d0c02010323060a08070b12060307030f06050702010b061c0506060915120901 81
    0x10b0307648901380c4050041082c0d10300140304070b444172514446c218652022501056902d060050080c094404000020f01001d080700b40075103014080c060845401100091540e00ca80e0010764035035102e540164140510030403034003808513003032002c0c20b0b01003c13021155120703004405005002d4910380c0c1100003c90710b02141c4450142e07400b00f08120140d07001c40031607a03440d041007194082036210f40140015105014001003009004009181241c0007036084883d07080d00c0d80c1070321030007000c00d0107000c005a000186540486116420381541c43e401810001003881c040151240c0320003c1d01c0454071016010340900001d1b0901c9407207000144801000380440b181003030002d89092082d01c5c6031000030b20260740030038580c0d681031000000a5900500c1c5c4c0032410307528503142024100894400b4099440d0013100a11400c0503000c455030b5440882c000444502d21420500051a0181103250006018030448000ea1640a9030580d60703180b05150a40710803a03400c0c8244000401442c01c82a43d06105805 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 432851312 1250 432850062 432850091
    0x70e040f020406080a0b040f06032001080603061f170313080105091209210d09090603080901032003090f10090305031801110a05040816050922080a050901020709 71
    0x51741c102200000218500d0301c100001405000c4802c3c1a19603280341440000404c400c60f1100480d0308000c1e54041c02c284041801512078007011100e05d501504260b0005600241403820002c2d02c8a9080f501030400b61640505a01d035003030480415540c0e0310001d0018004041e04040d84001d02d0590300030b00240c40c05800300d584030071001020b001c084802048507030321940c0f00300056030680035664144105400611005640da401801c003500407400c800700114206050340501c000766600720b010035180c410350300300450007000b20400844005003400c8245000a811100850241c40014010451491007246007828185070301407802c0800d1030005004002500034007170f6540519407103021a068031480c0d4440b800b40000d543c03101014140001c1d69400350350400c0c05402503070a498100d81c2d1400560045803040300d81c9004095020a803c1e00003161465080451441070503444d6030080d80b04001d40c0e5111198014841c1c007008284003207a6400f05507810040d03d001805070640c28003101100c084074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 432852562 1250 432851312 432851327
    0x1802010e0904210c02130506090c0301080a0803041a07080105030706020c0a0b09010203041e0e070f140d0b06040803041424070822050406090e0312130506070e040f020406 75
    0x4000403011659001c1c00d925001d42c1e800401c1e1360700680503003540c00c4986280c0c4014441140c5a9206075908130100320528240c0b410350703040e50340c0c42005111090064036080c40580000307000300d5400d00309081e030300e0364142c418086138014200b81c0c480d2002541084101130515215400c00e100310740c44070440d44020317500c90241c8821542000042e95448010600403404c40c45190812032058958200d50794070240c10400c144100c60062900e03943c0b81c0c480707074812913080e2081c1341c2e6900022200240380440056070f6004180d90340800764005030109080c0c0210380c01750041d60210030301e60030110f400c10041c02c0031540c1c10f44001040320940443c1c040c1170321407019011074048128003100d002c10910100521582100c1340042260703202d078800c62080000040384040d80c000c2901a80c180b240000b0040940d008070030456070004040d605081086580c00080c25000700310181c2070b00745030090000704d0b50a20070f060055410f0340c0d0300d50454085000b88130a40380781d8190318900710320410080182a9001d8403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 432853812 1250 432852562 432852593
    0x103051302090c0f0c0303070f090501030c02101d0d020c0901080f060f0405070b03010306020d2d05090102160b04051b0d03030e0a02030d0201090b010f050d150207061802010e0904 79
    0x3c003640394602c40c041c51100c0e00074045010540d00c030000c00e12050540180400660007a9aa594040952100011001e0759070303601c50000981e1040240f6124a07569400501d013190340000c0340c2941101520a4030316026003078517140056040150007509505241694501524000c3c004014a01500107a1035a40c40c008102107400d8007481d002c1400c00400b40803030700c0103014040105440756107908054009601c01100100d2003450720241064911543c1c0b41c41c40030901003202c80981e210302e40186005020010030815295500f0800040e10fa800c1e03120140066004c0c2000506c02d107001d04d407252424010283c00c42c035002c10307064409a250f40300140210300e00da062034080f40021441003051b01d049416440294075001d00131048000c560f05520680c11a070080d0000050790b40e075040317215001d003000d004540e046004070040700c000c07410300b50041c8000e00c02c00303000510305203050703c540c01203a02e9807100b004c5040040e000c0c1d200f5503902160f0384404a070116803c00c02410039076a610f084059a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 432855062 1250 432853812 432853831
    0x90d05090915040507120c02010621061b0801080706050408030f0a020a391d0402061e030604050603030c0c10090801060f06031521140307060605010305130209 70
    0x5148a080d0807140b003003480c000d00103111a00741000058441c12505c0c19407891589460080c0c0c4580303205000e45030841e5407101000c1ca554815030412188402c101c0c1094038450b4444020701400134207030041420f100202d6441c0405541049007444c1400826484082000014003042c0483e481c04011106954030304030b00c065860042c3c5405030300f04804840d014211080c108442804403586590120181c10441050241d44d24803000061421000c3d00400314a0340350781601403450305042d21481d402600040c1071504042441e05104201c050206121070065008818022942014011680c224404801030350814400c0003049603205259400035114000010704408031728003991903030001d000310303200a1201c80e450300b03030511000640340303c2c01002078901241c0c10500030040900c20151955a1450309100c1d2170b4040740010110381803411b544001ca910440e14078420108003d124040c0f203070714003062651074a4009022900c006200003411881820710000580d5100d440e0b941c014480d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 432856312 1250 432855062 432855079
    0x62306090a060b07151503050a020405070203042309070c0f0f17130305070b0f0301031106130e040c0906080a0b09010f090308090606010c0b070807020109020621090d0509 75
    0x107a45510181c0300d180d0000341c0f03004000030030701d081c80104a400101018200d6060000c040c0c0141d421852840602c00a0007036040440050300601d0a60011508420107104880c01d040d1154164454280781300c0f41c1420300303007081c00320707118500302418035690001450405c110301c200c16440380c031072a40d150180205405000096242004040e4020190241c03000d004a611280e2152503c44100310740c1c0001e55903031180400000c1d40f400c4c4401114594071b10603056a003140d20355611400300030303000111241d01c01401e22170100c1d00805402d01c20018220103032851003608290501803000f1480b600007029140c1012400c0c094204001188042c5030f40c09440005165600704507070b4010038400c0520507206081088110916620400c01802080041d00b9190942c69650040d0b4103030300383c40001080c00314054000b4401e1409044419809200e500021a11480350b0780011442d070310500d110707244400444010395442c848040d000d503115180c1b400410507a450f10602400600415241500c5507041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 432857562 1250 432856312 432856321
    0x10080f1e0105010e150d020c0f06040206090d1103030f0406030b0f061c060e0406050601080903070c031106070218011505160b061305010902120f061e01050c06011206230609 76
    0x17920003000c403840307910f00001d03122044812908003950018038406158030600c4a900705e007041c0890310a004550041041746001200d42c140544004e40300d6050f100070401e02050078054800307000900710050001000c07030751141061000b0f802c649011010034040c00891200c3e10194913000b0403944191000c4152403100f0280411802c003500d2213803c010458074020090000304002600400e00840303090304ca4000e80d940b0525010351304c0c01004009401003850303800810100f1590803941654440c0905080e180242c1600030500c0706100c50500322403036003910010441690a513890f00401071043c0340c2503203030a2071005d900101a00c00c0e60f000e05441490300c00306038180c0da000b1800782c03214420841845a50307581c81e1000000c0d04428618500e110105e000901202c960580c020300c5400010050030714581c925040d040c0e4000f129041034180b10741000409401c0c442001110300801a88180074483d030b410340760400c00e80b920440300d00141c81c0303860b1036002440f00342c0100701e0380311405441c1d56145988 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 432858812 1250 432857562 432857569
    0xc1e03120d290102010501060f14090a03061806060f060203030a0c09031208070e04060e180309062803020a0f0c0c0b070b07171311030c10080f1e0105010e 68
    0x90a002804002e0450841a0b48a070349540c16000280c0241c00800c0140c0e40c42c40292001824002c503200064032000c0310700e040d5800d1001611158002074280344810ba140d0f0380384c0b412100c1d4170f045260b028000349810401c0142c41d01401c00907080c1c1c4403a10298600e4481b000c2d5603800098542042983c90b8129095035502c2451800015500102d4907000321801c1032001d0071400d8140d42a1000400141618019042501032641141c00c82c07588210030396140c900f074800d4004a5024540140001c01001c0c180f03a5818010300a200300d0303480c1b1000040301050707040b00c0c0c5d41d103206506414140103000c0c812045811460840c45040d0508144113684424900000f0191903a00503444d08500403e400b018041e1214081d4405d14980c2c1310003d01c6851000110f0b01d21504541014006002419410005509040a901c00d240c082c007100c0810300460006031410b003840701d80b8400900d2420402c035844200002654200904c9040e11000071070038a61100455814060241407003801c1c4581c0701143c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 432860062 1250 432858812 432858821
    0xd080706140705040806010503010c0509120a1506080f0a1a1e15040c1103041802070c0305010b091806040308190c0810080f06060f0a090203090c1e03120d 68
    0xa120010041d40b4a08008082c0c8030303402a000f48030882c45220000f1405040512444011400d80d845060410f40c1403401c101c04001d0007611130035980503e801c035800060690f4074042c03102503c21404100c540c24a028149020407107000c50345240c3c000941031010510884843c48001c4036117181c0d010940e0349840110440f41032f0314940d940048480704000d80d400240b50107541c80c010071242070207811078405040f92a02e100145074441c03a0020001001179000f405000e044203001a2000350a2001640303488140720030603403050725140d44078005c01da010700e4820700c441c0c0d000e06240309044405040984942d030340da074000e200506100706003010074500d400e550308120185026090501091000443c02450302d141a24024802c0084076008140da0030041603c0d2000151940209444e54421007001701340d8140040840d0030807150702020070044410300042d8030510050004080c0b15a046003031080c0886500e1040405c0a510450203602d540c000c074000318000307002000700e601c403140c078031a110040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 432861312 1250 432860062 432860081
    0x50301030b130c1d07030e0a03021c11240f010b0301050d1718010e0a06050f0d0e0a1a060f030309040c02010b1801051002030301080a0f03090e0403050304050105060f0d080706 77
    0x14241113004501c2c00c040408898410346055070140006420b400c151a40c64500c1140180942c00a2401c29aa41019400d41610003410300d8401c096050904900342061240400a10549541c031445618001c0c03c80c407040d08503d000c5001d200b603615208004040d80418000d40e44034a180100c0c41c0144400004d89261460704030690310f5803a9040249241d010001300400703130208044601d0001c0307910b802c2c00c1020407a045501c03011318003000c41d843c00e00990300050318290078a548142100551100300088881175201d012604840c1212401180c49100018800d82c4120300210040c0d91a4601100382d4100920944020500480a21069000d0450041640d42040c800c80503c2021340c9a245618101d403030a44240c000c03501110f5040303840b484240035100d4150301180403140003920422035408494060310304030280580382d4054a50350700c820388003580041c4010080c4000c0c0002885050b4100e102210307400c0b1801d0000020840e04218507401800100c80400d030364040c442c80e42c000d21540c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 432862562 1250 432861312 432861329
    0xa080c010f060b030a060902030601021018060606050a0212040f050d0212030f091320160b0a050613050702060a0f02090a03050607110a0506062110020415050301030b130c 75
    0x101a100c0c003400f65150012504c51580a08100f40058803480314030840f40294010390280000b0001700c4001c00c050069413121550003200c066072000401da280c45208050b00513a0303103a540d80c1300746a46c000c0c503220401c3c0062466000030401040b640c210700329040112541030340e42c0d11401c0c00e1030000078480c4403c0c01d19200705002c00500041202141c1c4002c16074142d00307c4515140c2c11140000800300c0c2d0110000203115901c0c410001186003d15000d0008c4c154021241900c07544a581c0304c441e41da0041e0b1b00c500050b52528144000381c584600101c00110490b202000b9624004000a42d580000740107251f401340c3d1505402100d00c0703182c04032801e100020f0440070340b0a40d40e00c1d000369202d008a07030380750000e25a660010191400400e200c12a183c02000810b0a41c0300c5104201540c0c41c4045108642c10000040c03826004052001c0c3d14141841000181c0310352500d504001d14200311500e02041020400043c000102e907160f0168120b07082d02000c0c90300ba40c0394984100c00d0016074101f83c09 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 432863812 1250 432862562 432862571
    0x15050703141606200304050705010509120a060501030c050409030e0909010204030f05070e0c03130201140c01140a050c0a080a0207050a1b030c090b010c0219210b010e04050a080c010f 80
    0x60003855000007200845804c2c10b02032040307a844500340103010649005180e030f00203a104201359131260000d001d580000902c4440303a916520482890040c0d030400440b400f40d2604010820710142c00200e10003400c0c117440c01d000d0070718030307603001021760060032071151280c0000004544502400d505a1700519400400c02c5801c05150900d5075842119108802c80c491302000002ca00046100c19a400f5000c00410501701000310ba0064131250018180014025024480b408405000340900c00006800307880100c124206071407a0025150010041c94400808005440078194081c0085500100c0441300503102d804038604141400807010014110840c0394040c0221260410854801c482c07040c60284076869403000720b81306603201214403e0101d030000c400140903051140d1810f00d031071108001502c041340c03505440c00c814141d498a0511450074040c56004101484c0e20301c034003610040300080d525241075a01c01d5550303011508001c001c0301001ca1100c050710404d4102100040115a0500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 432865062 1250 432863812 432863857
    0x8071b081206010c0c090903030f2903010225140303180d030614040906090602160b0f0f070507050102040b1b0c0409200a080114101505070314 63
    0x1140c0c1d009485503860500c003240101e1200d6000b40060348403d58020078030440c291503e00315500030714400c44294285510790700c0315000c00d0004e100790200c020001080c41e021101512116121441b2808541d000742c2c030400040c4444813000e81d0044802910800340b868504051612000c00c1c0c4401100c00701510000c8107200b4098a1441d5040340ca0100104480b100b00e0600030840641d80759114180c48080510743d4243d00b0b040903046004081d00620000c0b400384219a59081283c0c02400194951581400780108022400007483d4000d490032a004030a030800e0074100c0340716003002e0242000c1c040b000a0010810200b90142c1d03000300f540c4821251a486511507a60141c030282504109500074015034080c1803419201d0462810341000324810710034180065500d0f00e040c0205101c1c2d0011600000081448090007002b4401e0700c0c890b91003a05040c44d11200e00c0c580700c00d0700100203443c480412190400d82c0401613542040c3c06240200c050f803071301200d540261243c8540d030700f1461160011035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 432866312 1250 432865062 432865073
    0x913020c01050f0a0623120d03020315060c030d0915140105133806070f110d0b040209100512060702070803040b0d091707050d020601150f08071b 64
    0x4074814411204040c2c07150340d5040d1107000300c0f0030501580d06030008440e4044106c041c05039070300c80340b04000b500c1095003403540015140340840400740c0c1000690000208030b50000340c001c0700c250702c00c402d0312110f080c50b10369041c2c240c4a002c0c2201070310100b03907035600d48001e0141d042590b5a02841e012000c001e1204044035604100009020340340c041c10840da003010440301c09108104401100c10140032081d85668000070010300003584000c0800304440944e030295440c0c0c3e00a02070144100503c000440480c9040000304001c049924400d087c50a4181c0204e80928180c5510030780c112050079032a51800764000b4099203907009150840400e01004899442c00101070340100c640d5000c80e034000390385030030a940e24850f5000d4168003c6061000da0f80d5030300b0607041520003c1c869154810000c2403035925140395033102000362511b6119002c0e01c804940c040c445c960241541c04d90896810207011b4014088100b00112141000000400140312901c120303a180300c0340c00610701c508000d00050502 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 432867562 1250 432866312 432866321
    0x303030207052a0108060316090b040c0216060c050a32212d0d1103010609120f06052e1511071d01210206040b0913020c01 54
    0x4507068801c845a442580480f010440d007003040a551404101c3c54a000440321510080c2c44160944101145610036040d84107030071000d00b030800d800260809111040000343e07a5001d440100f0341d040060442d010503845101401a1100350a1407180001c8524242e4901001084081e284040d03940c02c80b90010404d442e010306518189981e030441500d8040551f46840d412500c0e203004000604405051460700400b400d00d8040c009024090300c0344408804c100034861070609029803c001800344c9032240c8500c12204040111803d845c110340c11303c840039220036024004c80700d01601d00001501048100100314050580c00542813116080c1143c3c90090b010300b21401c0141c03811041000040c91120640582c01c4540406c1c401000c0301d1400707800d5421480c00c0b92080700d5406039450100c2c500b09583d142c01c61448103101c0e01e4005600d4045182c01e40c0b4a141c609c42c0c240d040a8004801503a10f21003035900740c13000d0781382c0942d60f08007800001d8540e0286203c1c90300f0a40c004207400701c40d01c106511 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 432868812 1250 432867562 432867577
    0x903070b042306031b091207050a060503070507030c05030702031f0b01050c100c0903081603080109050421030f050a1401060f020d0c020a0506031006030e0f06130c0f03030302 77
    0xe4070800c2e16141001000b07545040c00b6907030024801c3c400904411805400c4884240180010340d01c1d00345030074003045248981c0c0300c1144c5580e011050130810b9041c58040c41009060900e015070031411b003134200400d075104400c009410072289003020b5081c01014011100c90f603500404030b9132444240d50740c0c51a060503078a4144e036030601d8003100062950150046559690805018240607401000c11400500013040342d1010031024010200000d10303100010880000d500000c0409081c070f500d401890003038141c00100a040c101014400041c00d400181000320591586042e5210160101140104080e07564081640c0c00c1c4800d0100c5000f05921941c90704101c41c980400c140e0701c5880654034216a034928030010b81c0072483e100d28443c820340020079071910083c03c0d4524540d0318800a26243c00075140c90104102100080050682520400c03026203040d00142c00e0800c90900c0c0d580d15070000500300b41400b00410107907801c01001c03280100245c40a410344c840b130f4036200c1c00d000707009401140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 432870062 1250 432868812 432868829
    0x50a02220c090315060305060c0f04030b01030305121303020307140f01020a09030c09020307051602040b040e0c030706020f07031b0801090503180105040e060402071a01060224040b01060f050903070b04 88
    0x15400070404c6080c0541c00c2070300e0b00040200901e8803510204801607100052a075020841840f0110024800c80c55460082d03000f5501c194481002200348403a1210103445450718003070081d0342100080e0048151f039103690f003201422003c8803c0954043c1030400744806000c9a5200007119204190002e00d00d806490260005480c010b0300c446540041f48020390710000441d90501980c95451070408401d05014806000858100c22040124040e1800c1c42c5840039241c00c00603002d039041c1020804140103200c00d200070842c071031150348540d0b21103075a40805040071440317440c25030b84040070a403003800924000307008000c1d295190500640301e400c00115585841d050724601496907100c0d20945040d2801c0403101d41c5076458202c1044000e511031441240c220b0750190104c550307000c04070802d5008000035000f03403071090000a0714014003441004105081582c80052101041d9490701c028199419420040c00c01801c40e481038909002d188130300e5034140f0070b80b640460102c00001c013520440e92a00c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 432871312 1250 432870062 432870083
    0xb130c17100b0102060414030c060a0212150f01110f0304080706023304030210050f0603100216020906031e0c2704060c0912060501060e010c050a02220c0903 69
    0x15940002594420b03014140141e101d0401b01d00403502d920110a80c04180900b01d920f001d000c010141e00300b190880d500f00c601d99000c1900800c10700c40c80a8142d00460305820642c2213880b110001f000d00380c59a04513810841d9035011303015480010485443d043c1000811240c4071541c4141c141c8c0d603086a03005001c014020304000c0d1808110024030000414040d118003c108180102010810b40d4018025400c40c80b40b47c012740c030307003c6941c031405024101c00a140076030340c40d204062600d400d40b40d92a4101d424410481102d042c6800210700c40040ea045030b00d0fa0040e200d0300d00103481c055030040c4846000e42d045140c0c0143c0000092032411001e0251004070035a401e8004030000c41c0e0410403a6840e01b854900020300040d0503a0120803081214280b001295445407841031103114041c508480041c0d80314014800c03140c100c440760401d01800d02e031101e410000340d0396654035200c1128000b0b0140740048a06640717900c4141c0051005120510b0400c030704240700d24010900c1761940300c2a500365028 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 432872562 1250 432871312 432871333
    0x6110a030605150412080d0e0c01030509150f09030909160315180c140f03010f050a080a0b0712180312051608100515040906050f0d0b130c17 62
    0x140312906404050f0005414a841c11005800f065044c19084940e600d040011991f82c4805114000104c9000401003000b04000300024085500140138a09070b540083d4010891500440041d40c0c018881c0340e0341c4000d900c4d100407142c518010a9650350348038610004121109201c0d41a81100001c0c1d43d0301030140c200781d0000401141514080c01903c0000500e0303a4034160303501c0c0c210b48106810b43c5840500026211181840ca80014004092455000004010f02003402e0041409881c049494bc014240b4007204140d8031000c0078001031a03900010002041c0e10b01854500b0700d201392640d002d01850007116040e440c42819520100c000c591074a29000c80c001ea14800c02d482821801541302c515a11301c40c0039100c499008103901240700d1503090102d0140c07a2020030381242002489a6a1101c0c00e06900300161401c9405c1750b80a0340705940c1c849441e40e40c84422900540c5c03c2034034000b03162031303503d1149440c1801e007401418044500700001501c0404034107207102241102d0640341e90849 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 432873812 1250 432872562 432872569
    0xb040203060607061a0a080703060f02090d151104260c0f040b0f12010509070b0a080615091f030c020102040f05222f03131e06110a030605 61
    0x1900c0c015040b00c02800440c00185103036010352007040170700020440d41d104110005007801300e00d8002407465081241e0400801007039004200c10b10000720b42c01d60800440798081245c0c5c00e070092011344050020824008103108075403083d212a6805400503981d42d48811860400e03000e101c203a0500928400e10f640c90321840402c060b04d10b402d00420480c0d42040c19030821000e004004101544542c5220703a881d41d0b42ea0740c589501402850302c3c008141c038545181510b041840e1648001711400c0100b189140c220b030300804095120700122062142c600850401c1d48290040c19040754015119480c2d000c2408030301052182c2060903541d080c0511180b40c0340407400d0740180e200e5610a0000b1010901562401010000c03084003040010041c805110010b0401d03285491140022645000e40da02c903500a41c2003880e08a00548000d036245090a515041d043c9011900c09422020400c004201588140102c02e9109030441000d1150003130207903030005d43d81d02840204001c60310b4640009080d04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 432875062 1250 432873812 432873817
    0x40204110f19080c0a0c06020a021e0703060b10050304030f0908010f051b091c030201020f070b040317011d09030d0f0b090f01050d06020d0609140a050a020301080a030309110a0e0a0b0402 82
    0x15403a9a0b0708013203a215541f40c2d400b1350000c09140c1c040d8001c420007903640003c00030000305d044201c07400a21303085c1c2c51800c01c0701c01c44d030300c2d2607115005840c11804110303480d400204072600a5410304e04091103140c0d01c1c600310790050540d080700c00c565092040004140e0b60703a8111500441c4007560001800212480c03070b102c070340300e660100b0340c1201c0300461401d1031902c4007000c035104501900000d031034004002954100c89e405480115005580c5209020905900851641e8003d140b603400d54130300e5042088211803229040e8484044002c102d000546030f88003031040d5810400c0941c001c0c4641b01201c1d505101610ba1645001e0207006d02000168207401540d4400303040b6000035190f010b00361a140c4583d80130754050680c1001c0a074a0300000204c0e09406d206009150b95409e00d14207082c102400900d080e518064145c42c03040d801400148036030741d800b050046c1d00c95814200020002094a05030103450440e881031548a02c0b0b00c0c000090b440500540da600c1000300c0d003000c00510340c08804010032030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 432876312 1250 432875062 432875077
    0x4110c0a03270506070c031b060e041401120c050a0b0a120b0105030601180513050a0e0604120e0a090606091703180f0d06050403110c030106030209040204110f19080c 73
    0x38461144100001d090100090103042d021b04840417484d6165202c1d13003c0801c8040c28048400040c0030100909584840070004028044406000c0f80c40c1c4a00c40d00c0141c001801400202c01030f607480c440800c803209100b04001c00f0040c14001d441990b901d144ca04030307045603002c18085000c3c03806a81d0350541034418000030507416150b8500f55100c0b40c1c011102e2504015000410400081011902c0d07900c1da0600c1003000440340001c503003440e04000c50300c2501c02816181e40d09900840c1070100042103070301d400019103198540451009004800500c48a54560019100914041010990503408400347c4191401d0410b05002c00c0901445a43e481c4a81d030011540800041d0b00030655150090081e40308841c001c241c4c10029880d500c40c403084440580b41100842d01c02c5140d000001710500031000c0c00d40c01100200500c41ca10303000715045080050000344503a94503001216210802030644c0d191346a12a02c03a51a120810007400000315100e107039101089030000040d904c21202c2080340c00f00e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 432877562 1250 432876312 432876377
    0x60114131a0c0106030605010302011202070209060402090d020d110108010501050a020d0806040905060702010b0909070b03010b0906070b07050702090f090a1b23040e010204061b0204110c0a03 84
    0x1462410012004040800700c103890032074010444010940303024018200a07502400f8002000e514500c0050441003032001c103425501d00521420025990709402c6660004040c0d40142c0d5419031640001c0d035200402070003c0d030041040406005000e40032052a05d401c0003a00c9140269072100c00650b41d43c003c0084101c0160b1014000300401c038402e01382c05412003005080865150b90300d958041c01c017401200e0010050f036540d400c800307035032034403280d400d030400b0240c40500005828800c100034a031005001d040c51400c00061925501d89400045a202c0c54200e00590a1414a1580240310f984800000d071312404844000c00d41c41c58103600700b0350180d13034402c0c01072200000c195030701c072074141d120a440d1020322001280040c000e4028061110b007030220752056240c0911b2501040211060f5810554042c1e03c1030009000e6a80c218540c04030400700600a4030080c0e0b904e00c00680603101009060101301c60210703081c500320400140345c03807800b80709444429100b11600000c00300c01c054010130709070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 432878812 1250 432877562 432877597
    0x5041406030712150c0302091e03030706090206070b0115110c011b050f0318030f0a0f0201080c0f07121b0c15180807031401020406140c101103060114 66
    0x280359910030a4400700fa1050f6103a0340342c5500442c1c0c1104407003c06100002094001510300480c0c90401e0f182030b4160000c0034803191203904400800e0392405240001801203699111140070f55551009445000343e01c985029017560710307100c4c505000b138034070b4018502180c0300314443c42d003000d004107402840c6101030b540d801e400f4102c81c0c01290700e09480c500585860180d607a481e020f0641c10b20040c65681034510210340e08400c0d000901d46011260000c00d1034a4201039050300c00251030941d1484181e809103446610f988820340d64800a00c1440f0220152680020f1102c2c200103509000e990b17540302d84c0d00c03103406140d0860214a040740c0201d0f40200040481d18040c00b4210301038598801080300c0749080c590086600480030180d00e072680108076540e00c4074600b0401c11242c00048205052001c3c021342c00c003850320b400980000c103045480d21580402049a0001140401a0f2611042e0215040c0704010f0002c0212440d940296020750001c1c101c1c1c051104070428410446011080d000784441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 432880062 1250 432878812 432878819
    0xa050c070f03031506081f1d0709150804020103060518071b05120c070602030a02030a030c05122401050f1812070603022203150f180606050414060307 66
    0x1180d6000050407014556901080c00e0121100d0248a01408050326071420700d00380300100083c403820b4203100f50704076100500e0500c034404d5080405090441d98231000703c41c90711400c900740c0c6c11811a0b0800350390b000e200d07250100c0042e88691060300480c001c1c0c030100142d0b610341c1d05100800010090042c07a034441d05000c555481d11600d002c07561483d0201d040c0646001543d22103083c800c1c490200c07680c0042c0412405480c28091100304011b11080c0020351512901c020040c1d168050703000c181050564a603011407509004008941c039500c000e00090415141c10000341c8504903580c00c107070b0312b80b200001c160002075009804441004020074056800c000e400407010802d03c001c0d0707094580100c03808040c01c1d0a07402c20403a00015000b6500d003d42c41d890030b030f00e41c0c0718000c1141200416002d44c2003400c20105081060110000320100c1f40030464801c48108103018200784603c21a90104114000c82031050355400181030b2141107505004130300354568a04410a02030319201c0c0d15803c412001c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 432881312 1250 432880062 432880073
    0x61211090c0904110c0d0c050615031e030307030e1207060b030a06050f04030e01210f0e1218090c0909070c05062d0c040603022b060503060a050c07 65
    0x558401d45a5814502d8480454081010303903140001c0501074140115400908440c144640f414010b004d140400e810f035000e0301c42030380e81e12000e400351045020071040340c11952420306c40500d24581aa00481d58042100c00c00740e902c0d03004450000c00207207410181d206000d0301040e607400405c0c095041e142412501e0b1655401860030703c000c55458401c01c500c00d8001031582c040d442c466000188565440e14182c1009850361803904511410000c180161214603000d0300306a480b200305410000440c00c1881c0e00000040c11040c2e01002ca03485580e40b10801c22084500a244021a40303110359040d211a00c288003180034103a03403c0b480c601c000d01011045081600815034000403600d0001800c00140e114a070034a103007950180d0308001d8242001d03804c800918440326810001013015581460a400c2c080c2c1203014a01608081540010b921622922000c4440140301001c0e12480346001c24440548001c286134821071b8000d0080f400010802d200a1041c544500b02010490f49000141d81e42c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 432882562 1250 432881312 432881329
    0x6060a0b09120a120504030b0c0c0319120603120914030616170a090204060602030a02060a05100803030f0a051008030a0e01031d010603051e0c04090305070b0a0f061211 74
    0x3034907078807940510101140b0722138883c03c0c8000d61920b949a4031803c500303000d1081c3d0002001010380b0380c2704011520420344000201c0c2c20b400000d04996601900c2c42c2011920341c1300640c8580c404600300b140100c103001129206054000c200c1e01c0e1b0502640e41c0e83e248000b010301c2e281c1c0a50749a0084400143d45040009814401c00221b25084032084040355a0403180502501c0e001e43c415a0b590071001107040a101d101c0c0502410300081d824941c071002c00031b6965000401c988109603e48010600481e41241c4000c0503010810039640c0364508180e90901e28002103a170f11510034113140100e4050714400d0140c03400e8500d62400307140341c050450000d0301c0035260a000d01d810140e64a00c00b00d0090580c240c81c80010383c0d1000085001407450030720310314065807480b0030052004e5895408000700c8000465000400090b6070200740c01e050b5003000e603258098454098090174030001017180c03004417503000342c10254002e1000c219443d12803000721035100b5a40d0ac001c240b081c0c014001c08161900080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 432883812 1250 432882562 432882589
    0xf02060702010c0c0e06031203010308032403011d071401050f1c0c020f100606300507020a0c0807120605061513030312110936010806060a0b09 63
    0x4100381c0305100c2e03640302070700010660300c41c003e416903170014480d40d40703411300000c420411400605420341d411515120b410744006020406492144031402c08015000da1351681710701d0000f8001c0022845050609a124a8015180340e0340e0040700d1000c42d88214290040c8090041079440c541400301300b92680c1e07056400362003102e5001100c00300050f5001494051400d1086850740070300f28644c0729021483ca480541240548100d00380b003000d000f5207034048680740c40c2c0c00805070503a20307983c3c0300d80f01c10384144400b0504840407401c0408001d45242c0004603910145e00c41c4400c203090707540d1040d14588404950003040c2c504124441c020010074401d0700030030380100004000c1c080f80c00381e82103000803a61088800c80000700c1ca64404000781030f04030f40100e0013010315200c02d00480c1501a144107641c807600800c94031403603581000c010340006480d2505164481903c84840c281c2c03049070041c510070824441e94405200c1c1c0000503519041220301042101d1089080c5803e2460130300c00c01080e8050b058 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 432885062 1250 432883812 432883817
    0x15020102090a140102100c050a1d0d210507150b0f090403110c030c0a062601090b04060501020307050d030c050c12040816080c041d01020d0501210f0206070201 70
    0x4001c1109030b4550290100504810210742c0c03040e120710001a00740380b010108500d0702441c281200700c3d81c07504903041720103100c400d21b0203009000303588981c0300111004032030f0550002e0386080c100080048001801c5103042c41461540802001c13884119903620907040010031407100031450740c0e0380c610745801420007070b040200342c582180114000b20300501800c0342d00340d000400038210003902c0300c070504c103840c8512000c1d409069041030000c042151411648a000c04022881d01484c1031600c00321402a0241030084103c900b07542d503820300030040c0503082c2c01c4610803864000002141c0d8000021a44220390245c041c22a407482280107400516110b03401e038003807000411a21740f5501c4140300e401901c1488a591503207903418003081918111810308920b000000244090080c464001070b500071140b01160b001c00d000740051440071000580500320002c0b0340c00170551100d4503891b60400342c1a40d0840c0c102c0c1301240307248103980a00c07485d00040035165241a070301100240c209200100700b02030060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 432886312 1250 432885062 432885067
    0x2a030f020a03062c0a0203070e1506030c07031202070b0f04080c0a032c03030315030712061a060306130b06070b0403170a0606091401030e0f0102090a12030915020102 73
    0x3e440f5001076424007220801242c584c0e10701c050f01c4000745602e52200d600d03194000c00a01e0726a038040b0f81e41d1600d03401191040c070a800001141005102c40000c2c900001901807526418800300b1090340341c1000c0401c4020030800c1030501d5180c40144280c488040d0070820f60307806600d800000343d108400c041e00545580034204002031001e18100070044040d41f09541740c8145130601843c001118041034076400ca0b644044207200580d503030005c01e607500310a680c010a5021600300e00020f00c0d08005ea40106600c00e05210004107100083c2d2102c42040c414000180001e0580b50410002d40303c1124403680c040001c0c1340f012814412540a200c4001d8050400303841c080c0240ca445000311000c50342140010062501c80140c8130300c0454075508a1700ca20420b100d89401c10314003810161b0f250003070410003188066150b860b42e209801c05140038170901c00f80c0310f100c40100d0f0100d02030b6000c0400c003402068400c1000550464209000661640540e0780d02c1056040007900320402841a151104642d0217 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 432887562 1250 432886312 432886319
    0x80a020c0312090a0b03040f02010f03090203060712050f04030906050703090909230a020105040329010602010f1a03060a0504140105090604060c0804020f0f0402040803040e042a030f020a 82
    0x80150062003070100c2556034844401404110001c4c00940200902c508213005001c0000c01041000d40b84650900b04075010002c0f001c0700b10014014844081d5140c0308034814005241e400c40700c500141c003c040810f06c11640d0f80071100181d0101550001c1c0013820fa9170701041074a1194020b011841d02c01c1c030b45100170703e564090709402d40c1c844034808d840c55100e0180151032110342204284075116400c0250504032131f1038002904600603848064811012441c3c4440d03907031072000c50f08110700d5a020340d640f02ca50f11098028002d1000658003040340b0710b0712641b4685401d510314481144940100100a9076403036201c0c0750040c04c0003610807503172100381d100e010201c5c0c0e4080c0a41d034490400350000300043d241900700030042c0e030003410340300083c000424180303c050784030300d0550781000fa416250748444459400205000b482694003540a0740800726010591400d00c7c45802e00581c09000d2301c1c1419002c0509041880303d041f000b1000f000c144000800006000074910000707240000c095000c220380c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 432888812 1250 432887562 432887569
    0xb0a110307050c12150a02031b1803011a1f14040b0a080703050c27030a0303050114060c151b0c0a03110f100b0a15080907061b080a020c 60
    0x109040442c0d060b0810002c003030407410070340250302c86030b071104008001415000d44180088500509030072511130300000050810707081c80c600c0d50158a82e04409940c1d415546854491540b00705d403129102c0d500f07002c0018642d1072107030002c08080c00000c04022880c0ca0701d4080302034500980c6403000c14041019a502511290b6002900042c1003002c5c0c0d5130740c1d680d0510001005100000c00c07140030715107001c09000380c41c01000d090310f81d5400707150303601000050140e403403c01c40b040d81b6981c1d0383d0512a240195040541c141c00690403280c440079026400c0034003000b04011401880081c086a9102d4856041600445499a0b4000d02441002d900405da622032405180d0300860301101145c1c07250005004140e4040c601040c3c01c000140a441d41c8001c034000c041c0c0b0f8035045400058465241d40002031950b8420030540c008006102550180c0c08090801800b22a000c88a07246180501c543c0060303541d0040f102c0c501c60143d001125119801c00b503541d602682c0104560f003007103110305281d610050302c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 432890062 1250 432888812 432888817
    0x30a0803100314120a1b0b09030408060606070b0714040e100e07140901030f02040801090f0302100c1b050f160906080a080d0203250c0204050609040c0b0a1103 70
    0x264407075120000d1819800d11100c605a01c256420b0030354088003903190100c403244203490150405140650b0403000d003107000d051210b0a400b014000c1c480e100b0504c961114008014002c81d81c02c2c0d0b0030745419a498004200e0180121580070704040d115000007990700b032250400e0b800095800c00c05504007500c502200c01080c50032a050280750001000a128142060070b40d5036101109140c110020030410007041194020060854107042d10780059030019990b1750151009030000c0d600030030401c015030404440381d41075800198003501513034104c81b04101040c007a000405c0e1a41c0c0320700301203114925506d90301c80c00c0f165090b0b80b0341c0100b02e03224403040403c0c064624051207020f242d8011134101021801112055440441c19600003003500000940c0f100c150b82c80300d80c1400303005031203998000b40f20f50340d210004881d44901680108883c0616000f01c1450040b034021f5600300300603540c0b2000e01001582c240e4014041c43c042000070800c010b1104000c05142c40f807441d10501c90305a240700c00e49181c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 432891312 1250 432890062 432890071
    0x6080c06070807142503020108090c2d0409080d05010e04050c010507030302090904050601061418060d09020d03120b0609010c1205040906060905190b03011206060b0a110d03020301081506030a0803 86
    0xaa405c88810000d540e07100c0c00b010b80011860000e030100f0201500010900c0f0190040d48041504041000c091080d145410004001700600144642800c0740b612144641c0000e0540d120180782c080040b0b100728205030420b114a03800f00017040315503004801550241c004e003d044042503000c004400a035200c2488150140f0312a9004000070750410001401070182c10490300080c00042c000e8803071481142c80d007030412140035504c1c50340e9911082460005094441c0000c1c0d005040c1006050030141c0c0304a008040e0381003604100318046001c0c0070088148219410903001441640031000850310000c019400c0c8074007801c140340340c255289015002e540355130b8071910202e0407040c400c12250600d4900d45054190301c41410404a0400403c1112070006004500704041c0d170301e00b00e4080020550005010340344102c1403503200d08000300008e0015007a05803c1102d4000c640b04c1d002001d000b4000c0c2c2e8181c4100704050802d82c00005000b602059008106550501c070703200b0390310081040d000045001c3c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 432892562 1250 432891312 432891373
    0x30f080d0204090b01021203100e041b0b04060801061d010f1e030e0f031318020705100f0c030e0c01030911090403020c0907081006050c03090901080106080c0607080714 74
    0x7a03404d0000003a0500815507024101c04200300104001c5400c070020740b2007610103c07888000551142d0600c820304030004848500104508034020030440c001202030000c81348203075241d1016a89405040340da18081003d0181c8071400000809150742c001c40c00c000d88807459140c09005d64880ca40d07a41c00c100f0748140350034082540c803d42c00d0a00207080c0481118414070a00441c079000c80121841038848403880781072610f11142c02c0e02e50076800e464040701c801d2504007044405d04800702c00740100608500e54447e1580d49450f01204200e4040d000e60000d018a900141c0741e212418001500038010700041201d1005100b440708000c0c0e07450890141c05107000354014a0400e90590500410000282c80e130810303c4035442c10409624046a0340e01d05440032031804a466000c00724006155022b0408020b078400201c000100b6840d00c150710100440703200c14100c0e030070412150284211445011000b8000300400c005107030229400c2111400034100307080488502000050445004000e00070381d142d032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 432893812 1250 432892562 432892571
    0x16050109121704080a230c1b01020a0b010501030c050405120d031d06011203030b0306130b1e01170a0c0b071101050306130b04150e0f070e030304030f080d020409 71
    0x40d03290303202d441e003000c120700c0074046502410680c4441140e40210f4a88100700206c04403506045014581503540000f12490f506845010810074030b42ca078880030a0415030300c0402244d20100350b200103020f040150b040100601030380d00f000300460140120495000c02d1110802c00010280c4030800054070600c19180504000303176101000500341e414100c86070178004271b044401c0c0055000421528111960548012940e41d107a01e030075000f0780800c1c512190b25000e00c508101080f0310b000a1002d00034800c0301c01c4e462659441c1d03480744403030011150000c5680255001804900e40c8400c000d8034421069041b07036080207480d40c41c0c0780f00d05003d0b0068040c000c00407410700d041005506003200120401d00b001e0b42913282c84c0000c128090302000b09a841103407185013904650703c0b268040b1028084400305070401319201c1400400203a01560000d0300c80b10b1403400100300d6446aa8152079010009020f10303e01480c5031258901501241400d4032a01c204110380d203c3c11407541b00800081c1005000400e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 432895062 1250 432893812 432893843
    0x406052a1b0304030206030a0203060d122f0712050109050102160510050402060a050304060905071409090105010b190e030d0e100c24090213020720090c16050109 71
    0x60401c203501260a0349600901c0180300680e83d03a01601e9108070003010044c0c41c0e0b640d500005e01d000001307110150050420040142c19150b0110071040c4541403141c1a03041e240c10000700141a2051010400c1d064101a03010301215903400b1034803c8650050340049504a01511403c0c00c903849898074a04ca80c1d1485a07030350401c201449600307203541c0521810015450190089441840fa0614900c02c2100020008040180399070126071b02d26004021161b816488a9105100c02e013150040d070322450382440040c22100741402050b050b01c8200780744c241000382802d0010325203446a0310400074401140c60040c86030f102006202501d0741aa40c880c2c18003420342e014440003280d001410004c201c251842107020070040986104034024032102c00c20908005203808000301030000c0020751018014896180c414020b030050700105000b4404c3c00c120b030400040c290f0316090000c41440d00941c80f040040c22200030840a081074040c1032503500c03942c00042da503080c215118001c045512407000c60103107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 432896312 1250 432895062 432895087
    0x18010203190806130203100626040b0703061703090d05030415020c011706030607110109020a184a03161103030c070311031504050601091a06030406052a 67
    0x5090501c0d13000c1085203503080c940b10414a003801c6d405140305116440b00321a0141c0808006040089031031100b65171641024908040b950304240d514000103400e0100101d4011000c08491440680d4100154174000386503080c014001c103401e00a441c680000d000000c0c0800e40281c004254451545c05050b090344c07810009002a103191301c00410504e555020080140c40002e01550020b050b400e11030f0038403000340c00f10750243c0b0300648001e400c290aa18005000c403038244031040e1610841c80207105980d14000d03c0720411000c289000c0c481c0703204462010b000080e8407041d001903044992040314040320100c1c034603d158072200b1102900c0340003600650900c080448081c041c5242180034510785030042d2080342d03541ea00350001811400c0c4d00d000b44041d0750740821180e640c481e4803003008002da25140c00c05a48a400911402003064181455a160341403101542d40c01000010203035400d60300da6886030001004010590440d00c2c004c42d0000e020824001c2c00d600042440502a07540c035001180e00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 432897562 1250 432896312 432896329
    0x3030108011b0e0d0c270e010c0206040303020c10020f0a030f0e100213050a060512090105010303080406051b0c0106140d0b071d040204060504050405060f030318010203190806 77
    0x941885900c00d810400c0c2c03503a00080e21480c8100071100c10001d03200303600b009110381e042da9100c0903000c00801c00314030941507018100d60411103125002c00140d40d111000909840d40a104080180c10005c00600082d000307501921400c060313501110360301e0b040c0c1e085e140203c2c0d028400c0510080f901062100061b9458080c0c011b616032100c4003448410014804160359200314894001a50f0700030440c0702450400700c165000070a0002c1036041c0241e55aa005440f5070310840b81801860201c000190003000140103590480350700d555201c06c00c1d5901d84444c002440c01500c024201c00f081030101240c000980084c042409008000255051401c2d4130703c0f020015803060103004030700105e40040400c1d2070000c003a90040e41410101b0041c2a0314464280c45602d420184e603000c0d02c080740224100c0c1d03001c400360040d60025203081113107031200400c02c074070f82046d0b03e129076042e030003004112080908000d8404a0030418012242071107500c0c0c18444070b0f50411103010740000c0c00790080101500d4200340c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 432898812 1250 432897562 432897581
    0x906070c03020907201f0906090210050a0206070e0108010b090d0b010308030621030304060e12120a11090d03031109041406040606080709060c0230010b0a230a170303010801 76
    0x1482441c00345203044d485e884d2646c89881c1e20b0360356110002d0a204c500c1e00300100f6180d009056904000440d00c0180450700119200d400501c90100040d17186809903508103101c10b0161288880b5078606820140346031b1100038810b0b0400e0103140d4010001c0c80f542029030185104208450300c0b49441d0301800030318403004001600502c600e240310340524101108a0380c10581050b008510180031071900c0e803402c2e0600ca200030103058000b900030103c0300042c00341d83c02400700c40701c140710451004010b0059801801555503000d042134203c100064040d62005180c89011102c0740d08004c65080003400302d849030f010038001b510030142000b070395103030602c6400090f140130b00300100c3d1410503101c000d20015032805a40107000c0b81003903400c1950b4581d1164000f10380c003820849628a202400b403100c113218481107044541c00e2507051842880c01120b11000d0340c82400c2c0d0320100a66180d02d001e02222002d0f0095000101c031040840d14103002005450300b0003180000790b589501d41105a42101c20400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 432900062 1250 432898812 432898877
    0xb010203120a150e07080a0605010e1f090f230603010324020f160c0b16030e120a120e0d150507020f0715020616050906070c03020907 59
    0x10400400c410415402e4105110141c0010b02c03200000c1c1000d00d0015941264206504000400c00e007941e20182041c40b0703100c200701c148104c55460380191000d02000d6006035001000a28032445a50001c0c4980301e005107a02e011049260364440083d2541450303001080000411084500030110250710100c0c907102c243d800b04d14540c90740d201d40720362240040c5840511204aa6800008003d0b40c065860b042951100d0b140da4450b64070155420051207101200c02c9880250000b8030b9007603100036034a15001100e100040c42510790760071100b000c42481515805810010804000b4004119040c0103c1c81500904860b001c0c98402800041159250038810301c80501c11000065609100c059490441c51000c201d603103d400c4168113140e038050f0b410815224039400003035035642203242400d070201c480c4c017a0b075925122150100604841d403640c00000c036004000c03510803401e2400040085502450250f00f85545a42c002941c90f8001d5410304001240081ca0350050a541080200b84030b2564 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 432901312 1250 432900062 432900067
    0xa03110309060103021e060d021c09020312070318060c051605011e0302090d050c1302091c1a010603020d0c48060903111b060f220501030b010203 64
    0x160780565903201c050000034001d42120002c180c03440d00c99100503204500c020801c41c0c0300d0088002d503000035000f0302e120304513029a0071943d0079622143d06c10385286c640c01802070640700300321016030312039507000c0380e02241000507040c0f000c08104c184100c10300c060940c03a645c0b01100000c504010b4584100e02c006046501d00784c040c1041503030b81080c4461110012100a0f207241207009d00242e000f4085c404965412503c40c503049820070102151900603823408071201c0076644464002e0004171300802289a8005243c12085107202403401c02c2d400722240301c0e10f25072964107841e0251500b444e5003a44410003098000c2034040c2c48002030b00480b0354010191510600041a04141000c0d0031040001a0070380a41112825041c448011444030020301450514140090b24039001c00140f07402c036800c0d8005095041d8040a00301c001c2000c4003281c0b0030400141c440513920701008840d034400403021074034640401034441c100c510342804004000140c1d25403c5420311741400503040e110700403401c90454104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 432902562 1250 432901312 432901321
    0xf03271002060a090c080d0908121303080304061b11010605060a02251211180c120910051503060c030c18041805100608011a0d06090c0b0a031103 64
    0x2070503507001e00f1914000c240304d84c41c2d04114880d9103003900315900d94011044440c4030603401552074000c48aa1a0444021015200810400740504000e034500121308110800100c2d00f00c030b01444d00540a440e000611412449845d450103924101d4000132900350140c01e80b03001c000f84941001041c00350780c03052401144440003901c91443c00300030210301002c84030ae85218080041c90034060304048103000700c3c0703206174100882c071031940700c003114802d00005242d840026408032002d4080c400b50401c1d182080d0510000c000d0b84c040040c0500b145110f01e9400941c0c000c1c0a0050350302402c88504c5403050391a4000070315007098001000c19103011b6040007802901075020301103595400c141c4540503040180d940014000c3d1242c0601d600400d4040400a018844040b41441008140f071400308000355a034080700c0c1c261859905088120000041c1000b000c0c05c1c8001c0c03a400051244800180443c1d01d0355481d40c0d82c0035943c10480c440000801c8103884141c040c03091085c2501080c5565003180351 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 432903812 1250 432902562 432902567
    0x7031e0b030c041805010c091a07030e130f0e0d020a080708070218061305040c1712040609060816020705040506040e0703050d0e0604052b060f0f1b0c11030f032710 72
    0x141200305e00e80e00d040002c61205245c433030403000003450390003003104528022442c1d0306e101806003040c1c00c0b07022524000d14402c0350000081c0722a070700c0b00380760040d140d0f9a40c29103640601d50004801520300c4e58081255074016075a4040d071461a100c120500741060a01000303200c001780f07510000d11200740c602001d000120382c500d00300300708440642c0100b184000c908180c142c00c0c4188180b520107940000305012a00541046040058400d20b68039540340f581d0f40c4400b980401e070500030500260304010130500c10741c10160031050380404054808545018002c0b0340924004540d4400d64882d000783d03070b42e680200e90003166405c003040101c40759030410741018001340352211883d4002d811500004105907513403a0400702c10290980141c402c01103500035a900b00040c1c00540c0309994024074020240302003002c101d84041100342c1c90b5503010034100540c0d84e00c0621f0410300d500c10307906208484151080340400c0004004050000980a424030f03a21109002543c0110000d03030300c50b4224824111f50300e035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 432905062 1250 432903812 432903839
    0x171911270f0405040609050d181a09030d0e03120f031311030f07030519030206071d1207030224070f0f0c060f020607031e0b030c041805010c09 63
    0x290441004060800c00019007401080903159412600300001c000c248034507680a280814014070030341c1c03c190700072039007291072603989200070038642c013940001c1c4084400c0504491802a044070034618050203080028500002000d000000500d000811041420b09000344600004140401400c268403d000c2d0311282c080144001d0000206190410600040075891911030b00007034240d4034010504e145036501c54815000030741c0c1a22650103a003c040b01855607103221650558040c11407500e901d2011030b10502043c901c400300085400008400303a8460100d4034038010a0801040d000d4954418081140164180d440201800380c9030380c942e0400c0c4004595440340e00c076403482d18220261402203001c5090b003a029100d5205503c004c6012500944402c8003030300103408450b600e90f5219411010b881c0491241002100131040001c80c2d684241c0040c06500c000074103550b0140e84a5021504540780c010580f6000081d60b8900c5085c01800c0c0f190b1030221240d4600740c5241f5041c0150540c080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 432906312 1250 432905062 432905107
    0x717060d0f0c030f05030334030b03071a040504050c0702010219080d09080901030e010c021b0301022502180c0301120807020a03081909050a03060c171911 68
    0x50300741d410301000c1058103082d081c00b465019076032980c024600e09000b540c0e42c0044501300b181e80402188500030304070f05020308813905044070201280d84100c0008901500c040c601d02a05440380c1e0303202080c100c0348650008120b051020926403100c0c5050100f03c01c0c1c81020388011700c5020b04109000160342c1c041072000c24481229003a600500360303464901d185100d00302804c003180e0301d020750707c00401004400800b07050b44240e80038080c120328080342e01d00303d510b1100e07450003681c4030350035102c201c0ca200c0215083d590310090005090180d02c21890010208407000a0540c10345407020400b10302e883d002c00128455464005551440c001c0300c2188184018040d182d01d80b40a8902e090402258030100c2c2d09460307001d4014801182d60b49002000c0d80c2100090210b5500c5a295602c00c4500c200340354411180d00401243e5401d103140c444800424840248004010400c10101400703c0c420401034018a044480c0c1c1107610f20412106049648081403d44114804c20005418481101002104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 432907562 1250 432906312 432906323
    0x15050a032006070f0804030b06010e0a03020907050906031e09060108280807060f06231c0c0f06030c03020301060e01120e0a0602040905071110021608120717060d 71
    0x4a0010002c1e849019808009000101400000c01040b900c4c03006082124418000c0340380130f4481200641c0c07600001645980c014120540420161800b4400f09030131046a090851408a6900104840e03038002c6468000101d00c198102c0d42e101002602c1c03a62003c0380b0b001803c45541000001074894005109800090020414806d441503189002e00c444607804124199070741300d5880c2801c068001c4682505c012850072000261650b00b9000d41c4901041d44502492020342d03050400180740715180780c81a54400d003c40c17900c001091011000c002c0c08070054074410451504000600342c81107021032a007058010701c0104240385e00150a048400c00900f058148802c5010309403004040c80d0819444a1290140180600a0543c0104203550841c00e0900c0719035034400d0262141030440c40c40f40c04a6000140458807808941d026141d03542240e01c400600d81100c1d1200450382c2c1050f0700480d072200c604028440e60f80d0b000461340510380c1030342501c0106ea1520b000010401b0241ca10003918 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 432908812 1250 432907562 432907613
    0x80109150c1b0312020703020c030d0e22090605191a09060f1206160e030a0305030609041b0e06030d03050f0c0a110102190f0e09180312090115050a03 66
    0xf014002c04c0a4801108015421500e803145410300955590403400098000d01945415858a900c618140180d4a02c040d11520200c0300388803441c00b07200e9500d4403172005143d03654580d400081daa8000d05000d6154508903001c8400c01a170b043e030865070b00c0103e261354041071852420850300ca20380140d91003c000c03110580741040c61000f117081d035020003d40c0304403402042d0070000c0d00104104990498212541c40d003600d02804801d141c3e98084070200507012078810700c001940c6140400c4a280d02034402d1155601100b0031100d00454130405802001c1084044030400241341010040e40c01980703000d1070300748440e051030000a1750940d4041e1020110000000c1c0740c000c0580600760f03007600703411710400031951450b0b0754241601011031024080b00140c28600c0d61000030788600305040c220203000780144400e4680454400d10810700d2030303800c1c0450001b40303c800040c803082500c1901c51f85940002280c640d4180240140b5030410b50441c80c443c0700c0c007034018404038400c00303540820a8101e448035071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 432910062 1250 432908812 432908867
    0xa051c030e031908070e3001060303200a1502031009090302030301030b1e01051002210304020102150c04210609030929090910082a040c020c13060906080109150c 71
    0xc90604002051001f660074140700104040e4031a2864480f040c21204240c50b00c80092245034446a5510010b0003107240f03034250b428002440d900031908103c1c440819030455654000c600d0558810350410b0340581c101000410500583c201030039403084c10119900102940319102c4002800d06004441c0111801c25540d41c10038000c0010902105400c041d070104c0a29441c10059558412141280107009000000303081d01501070959000e560514541410281004041340001030810703403450648604403e1071020901a02c11041c0b46402030741c40542c2e1500780400f000028854110f055010041396480340c044035842e00684500842c11203c1c45000e80ba43c450307109c0410800d4102059038002c030802c40c3d030b1710391201400c440903280640d402c0b06903015000400003100d8100e4030303e0b400741e00311185c200c0b182d15240e18203800000000800060041c0ca030501e100031200702d504401101d1707540340e90400503c030b5540d40865200310784010a00c200c070080c040090190111900c4d11040444c960f0041 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 432911312 1250 432910062 432910129
    0x6090b01112a032b020304030506040b060303070b0a09030905010203032404020c030316020d0212160c260127140111070c0302120a051c030e031908070e 67
    0xc071100342c0020700719020b040c803c10b944540e0060740a41040405440c2e440c01048a00200a0b203080320f400001401c01ca0b40c03551581c40d807002000f005554180810480c0700c0c0051014194540140c01d4940e00040c42d201a107400b4021014030f420440c10356009000b0400342c80850000c00c44199800209031400e0007170b52011030042d006d03061801a0350701000c030821620803019000540310203283e5085448142d160b2005a80321421541400f410780c07800c208201c1c040c0c0342c0b0f42c05074026900c600d2000719035664510000ca885074114004800d40320403070841c500406024001d803101111755065224074a058030281816940040d00e008100b030940500103c1e50600c01e41c0300a0450118552140c2c0e0756405291401e039a04090004910074114800344c02e000940c00140d01d00000c1d403000081078081c92110b0512030040030409070900301070302d816540340041c0c1e080c809440909110364405002c1020b01401414410703006000300d04001c0c40407400d000541d200c00c2c00c4902c40b00309046ea0000c1d8807034890f00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 432912562 1250 432911312 432911383
    0xa140607081209010b180105010804020108040503090312030109150e011511030304030806090a0b15091908010606090509190f0f02120a050610020c0f0307030b0a06090b0111 76
    0x2e110780040c00308210140e10190403640f004081241d625039150032910401d03c00110070702849001903400c100140040d40900071058020313015008a80c145800350340000c1c07403c144071441c1d13054000084010001d4a2250141c60001200f00107803014090805840100d5000140300300c00401c5070785100a00002e0052400e52010b135081340a90f0b40c6d901d8142005418214280c0d01c0171b0250203140e001400080d510320030f0300300c0e10700020000c01180524002940c2940c1040081d10303441000c00b8444042001303d003000100400888001241003450074401500e110280d41c0000d008900b01001c010503040c0080310424424170307038180010340d100c0d20356840c801410750508010819100080c0708a4a0f46842c29052052186000c00d10142c1e84050500244900f0002c3c0702025910001c2500d00310300d0201f9030000c48040150846405070354030788501c2c03243c0b03405550516061342d0b0351a042c00501c0300e90203180390f4a0803c0c2484040d200004000030341d9020b6a03c508002010100c2c68100c0b107030301d024103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 432913669 1107 432912562 432912577
    0x8060f0301020903030d0b0a08060c0307080714070f0b01081f1d011503050d180b0d1509021c1119050d05010f060e0a14060708 56
    0x4148101110004a02503055400b80112803058030208050300c0568070209000c650200320300148194050f15401011250300100c0800c20200c200c10102d84d0480344510709010b45075101c110454510f054a01c019405481c0000c1c0307401480400311041e00c20f5400340e6640c601c00c0e40d807030a145039212404003202c0014003814464400400c4564490003510701c0107001400c668002d00e00030790071a082100b0304407100056660500034030504021030080c2c680d00f410090410031042d00200d0f00382c0e40612404201c01c0c0c0009409181e6a0b054200040c0d181d81c4607101421140c0b210b800e01d019412010b001d0b084a00e02094515080155000c0c4861030b03044040400e281404211808503220300902c402c6060000030060a4000e0b903551003050700030140c1903040309403941000c6006001008400c402c41c030801480d03000384110500e003031124170018422100c848c1c3c0c0b10003038545000e00d0b0041c0340 = true := by decide +kernel

theorem cover : BRFrame.Cov 432733812 432913669 := by
  have h0 := BRFrame.cov_init 432733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 432733812 ≤ n) (h2 : n < 432913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
