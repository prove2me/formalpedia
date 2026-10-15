-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3895
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:59:47.898478+00:00
-- url     : https://prove2.me/submissions/9a83e7c8-e728-4eef-aea2-cd3c7b640367

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 700359712 ≤ n < 700539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 700360962 1250 700359712 700359731
    0x307051e0a0b04091b080903180f03100911090712020a0504050901092310030f14030304051501050d02010804060f11180f150f0711030102070b1503070f05061c 70
    0x4681080104a0031700c01211801c2c0c0c8941402c50310342000700c1da00400c1303410034040c0300c030030410080c00d0522800c03004155070780302d26070300b4000703810921461829241d86986600350800c00c002c40ba5103000302c8402310350000080c5407025010300324584075504491a21350010300d80607403900030401c1e18090300001d4003071101503840301100801016401c40902c8142108000850b1101500003458410700058410100240c034650780d12600300d070f82500446040c0094483d4250055040000e14840c9010361b00908034400a114051083c2c0c0060f08014000d5000e10b04d00c0c0d0160340c024000c04d41099101c040003801d4000741c4818002400102c507400d118007800682c103490b0b130048628100c4404c404850341c035020040c20041240003013041703e8a412070070040c001b030540e5031284006041320358050f061005500780d907400082d01f2a400a001110441c441074140011038601c00206a24400c0540003842e5645c201941d00702465410701c190341c45008005100d1300b8406540500202050300544240a0f1400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 700362212 1250 700360962 700360979
    0x302033001380d0b01030917042927030d050307020c0102011a0603060d241a030604060e0a06020309030c0607021603031b14060f060307051e0a0b04 65
    0xb0202546821030707000301111204070b2507160710711807900c0300d040e0301403a02c0001201c038006081c80c5000d0506140d91000c444011504a0b010024607402d030f001c030295260700703000403103450141c400300507035640381087d000682c00a102e1084801c042c004009081d0415801440c0c0120302c40740380d44403070300741c060382c010000c0c3c050304030000d10b000384c01702d03000c0e40c5114000c1da004a0894820354840c0d003080460940030001c50030700780c0040d40c108130040c0900450000c0c1c0e40310802d15048400380403400069030090a113035440c16109402c040042132030254242001c601c002540e825005c0c00180c007065032a048228083d50800c21f403001c03a41c0c0701301c0035501c92400403541e54a98005192108041c0900d1001480c0144003003401c0e07103130681e00821400104c0c15928112041d0402c1c0021a6900c95403161800106c0c142e9480281d900300d21600400c035500d030583e49030510020142c055400381e840848140801d0f5101e40d000c0f000348900ca44030310407101c1c0b01d40c002041026030342e0114462000014022400d5030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 700363462 1250 700362212 700362239
    0x6090204050610020a080a0207170c0114180928020309010606020d080f0c0f121029030a09020901120c120803070302071110051e070302033001 63
    0x6008580400a942c1d0701824006440c84088070030005030050000d00c0009080c2d00007902c4403450510481e02c46540b10f190051004c0760b003803254a11940058580d007015a0301005032600303070305000b107002c2c203000703a004c60740600c50340300c1002900c9440202c00042c8442c21004055220b250060320003072a003125000d032580298026100500d195080c2070b4049462800020f401408807960f076580d20295603001c100c0600c2039409002c10145e4001000100b1002c1c207408040c1c070440810803491119414240850305c0900000d601c11601c0002460b01c5d1880000802e0100e440d86510703600b41c61741c940d20303075a051004001e0b003400250700c003c05400104162120700c0c5c05a0102c2c2c8688204490b46449514400301c2c4481c5920090080d8010800120800e2081c0c001d0144c0510840d04041e40480c0c42c800208190301201d03038a00090000b04089580340303800d40d0800c901d00c1a03400002c2ca0440759484c025268462030380410b01c0702c2c605048005150450350003a084001064903054101c0d40c5480410303480c0d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 700364712 1250 700363462 700363481
    0xe2d010e07061d040e1f0608030702030c0112090c0303110f07180b01200a02031005040b041106130b0904060609030203030d0203250203090f03061005090711010f091a04030c0b04020607060906 84
    0x207a01d051f8011442943c004115a10580c0080041c0068030701c1380c004440051085100840c403580703072003013000003c11012052001d548240c032451030303800c0e8ac2d115051411102d10b14480346640149410402c40c030221141894039155400c3c0407441e12403c00040e42d2142000e9003154140134031b850468900d00b000311341c0d004094030032010344800c44150621641500c0c421788000e41181070b00c00100b0005015149086a0843d019014a040001d01c100803403c0c00c220354480020300c2400503010740a0320705440b905010780403a003451030712541544c000c00e68902070000080180f582c00000325405c000c80b49030f808041a184005001e10500b0164000d4813600000c001501031501028680501e14011841c00d10419042c9650042c0074a040200000300c2000303403541c1c0c18400c1814104204020038000d1020007560380c00b0119001c8804e107403a105445210010300186002d01041c000000e40c422241040260030003c846919220b44c00040c0d050321a05100509041c586003401c0b00b040f103190000c8000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 700365962 1250 700364712 700364773
    0xe01110f03030406021e1e0d0b1c0c050d080708131509060e010e03060f1504090c03050709091e0314030108060a110a050a030e2d010e07061d040e 64
    0x2c048801c81115803d00502c0a140b0040d200c00f28280c01fa40d40701e10181078a00e507114004120315002e00081600380264250b484581c804604400741070040c903643c510001c0c68151a165280e05c0c01d500c5100c454014400000d00002c40010103a043c1c440b034000c90405043c03004040728410b800075901801d5a03145204040200e074580381391010782e60040c20105105400034014162a50310716000002044000741014060741000d04182504d45a40c4038026509200700032586e415421070501a14043c82540031440300360900d1103240000e06000310b90f4001c40c0204003448031400613860705450000d010440760400d4800400005805c10000400340e000e00740303401c001c2280e40500d084003111031150101c040003207031080101180e664801d6104124400f107000959140101e60400c554550030010044925105ca031442d50110305820710400180b002c03900000d10b0024034107000a00b201c1039510740c03403004030a1012800c82641b1a40c20045240740c1200603a400d100202c00a8070b040030484010101c2e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 700367212 1250 700365962 700365997
    0xc010b1f120e03160606230402031017010609060b031005090c04030b040b1503011a1302090d08030415020a1e020a0b07050c070504050603060604020c030408060c120a0c0e01110f0303040602 83
    0x40141c8010080e5030302600c7c0c0c040001c5107251503c1400081e501c00740000c00c1c0a06480c200103440c10186100140303421416002151081c90032007500c065030100d41100c080307031740c4c10010f200c1807410018115044540903100c2085503680e07080268074a00855001412101d05032042204012007520b100b48245424143c8115040071203050600b21802601300c40d43c058000e0480b46414a401c04203c040081411000352070071405c900469130025aa1004031901c1038040148010040c841100c8204c151200c4003c500305840c004006050040c12840d518184d44e0210b40829100e2092000310002600502c002156090000f0014190740c06080c4080c618041c4c0840800c4500c0c050040602a480003001401a42c032a00d08000003035000000c0820f95200410001a00f41780c241300d41ca10500d0f050300c45070f40b180710072131701d045a02e0300050030201007616041409400541201e184540031200b843c0070340804d080c1034038140c9040550206560644408810001000955001007041e6820644c9850 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 700368462 1250 700367212 700367219
    0x421082a0f0d0204031a190e0c13020a0201050c070804030206030a020f03040f031e020717070503370b0a0e0106120b04051606050a0c0519080c010b1f120e03160606 72
    0x4540780161141c0744e101341f20f103242c407805030003c0d0803034148a0722010540e04d80580000c0080c0310f01041c0d0b180c0300c00f12600403421200094080c440c042d4001640b000052a01c401c0c3e90b640f0728a485240402485480d020002c00d104420136810f40f11604001302400f90340e4200360818441000030060103c2c00160030b201c508090b1424a411460800c8058005041180c24041801d0901241101d4001540310701c42000039507603010003c490b0b0003c1c2c2c40c000203c1b42e121155141e400c44010503d140002d41c6601c5034040003030b4050105990000b0f03101e4001604032002c00419014082503070207200f00034041d04084003800000070116001d03512038811a00754103400005c0c560b00811610070500800c10500c01000142d0140710800d117030f1407160080d1000d0142e030500781209090780e0901620014400304416181003000d1242114003c0110390410540e4020b40704071041c0b500c3c1d0f100c420300b001181c01101200305843c0d0819822800f002e401e680c0c49500f1401261204c0d403500c5415a50241041d1000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 700369712 1250 700368462 700368503
    0x1050705090a0e04080d021209060a0603120e0117011706160c12090306150305100b1005130305011d061e0708040503120421082a0f0d020403 62
    0x9440c401c00103008000c001e894011840440310b030040054511a00400201c0da049803d48020071518809802c40350f12824a8541c2e1403402c03000400c91080316182c03140034000f103544885120042e03540351401141c560104001265048a01d58008043c40700786000424000300200c40010b080c5050b5084900365507130310710303003100c090b13000c14506010410320310040001c00c3c0204140d031040c01160070401072503039407982c812084a2038494612080200f02006008019086c0042108070380302400c00d2100882c00000112010094800d50050240c002451399040060f81210b8008680010080241003603041c1c2c0d01002d444035070700299490081c1d10000e4441c4401b61815141030401109400d00d90f0358503503040e0b880240280c01540d2620040c8000345050204001c0c9074441c61050030b06081c030040300d2810492800f40d1503100e606010182041000c1070341d115442c100e4540c510802c885144641d1807007120181f00700302c41403900d0000020140ca08002c1a0014812640300304840c00c43c150010b10320 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 700370962 1250 700369712 700369717
    0x20301080d0e0a050105070f08160b090a0b01091a03100504020114040b04050f06092707020718020d1113140f0d02040509010e071d070908030a030e0712050c0301050705 74
    0x10b050f406688203a00788129440380e00a895181e209580b0300c42c01034080d403101001d6400001c807900d030009035840325400700000c0c0c8229680104581c0010501c0c40520307990f00d43e00b107105005280495076100741c600080042008400886100030701610004030b00f041d4460050310040703c0503400f01c0d210041c0d00302000200c1c4100c1b000c50b0700c003d8095040605083c02c03c44c40420040d80c1582c08942404806101d0341c54913400003141e56400b0140400301c20013220300c201340e500140410255006032030200a0030b44111144c516140d034440300142e6800b512080c480017446480300149070032038085544011038158120200030f8403c005492030034a15002d080025460b190020f07030f0b8000e1940b808220041c141038100c10b401108003030010a055807107000b11440c0c070380c59511040416044a4010310041240d1680a802c03030090b19103445410300740300008c0c3c3e86e4826650100101650f03000b20700408941400014080c040c49071040809080c1800c05554034400b5840c1c0e0307880b80d4640700c04102d156000d4402c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 700372212 1250 700370962 700370987
    0x50415091a03030412021503131101080106230706020f0d0b1f050306130218040608010b1804050f060103030306170a15020904200a08011202060d0b1306030501020301080d 75
    0x11403074242440b9000c041d1105d0010100c1c1c106090b4800c0e100c2c203844040c080d5215000c0000c0c240311505584c1462490012a0140c05051000e200d0042c000a030348001c1c419010700030300c400e4407045011590407082c2d03840b54103005011103102003074501008000e1402000a81c130002c03004d000c0b010342c0c4020481e140c81d0f4607281c20341d0540410303080c944227030245e805558490001084690700c9018000d56100341d030b11003440322091a40b0101044040e1800e44241006804040000c000c20030020000c600341c4404030302e0f007a11410004001904000c030400078080054010000d440030ba503902e25014000d4a06070191a80e030b11007075020100c8110000401181c46504141a01c0590341d440003814029800382400c81e4005441e032201c5075428188080303080d101700703400c80301564500a030b6000602c03040c03041e04848400d5038000204c00142c0d07280810f40b00e80f07070418840060612800c80c001554648010490b28089080500010500030b040d809035040301c0d065019540325460f6803c0865401e004240e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 700373462 1250 700372212 700372219
    0xf031603230a03050402011206030506101a0301030206032d06120607140c0c0607230703031d01110a050109050f0a150207030201060f150207061106060103050907050415091a 76
    0x1000b1a4442d11039000b035071304a4018103081d003c8054a001007c16074989400955407a800031090002080e940030842000f0000c004410194101d10070840c1050701c0184400b920880c0e01102140a04c00d841d00300f0107220036104508585038091041b44121040125204d0b0f01c240e140943c02040418045005440b030280382d41d9034845c02c031280c20001d120390011b91030000c9031f00c01c90482010704d0321100010a006801058101c103100849aa514240300d0000100384454021040801c00640c0000d00390b0481415903406034188983c43c00100ca210034501c9100043d03209122030354040c040c0c19480b09103d54040d800380e54410b4420712486580d84070383e0781d000f000c3c0400100401000b142c141d000e03104180c8a0710000c80c0040e624401040711080d0b42d006000340841500041d800c00b901001110002c0c0520f003064802ea409802100b1b40310380c00100081d0606072100c00064944d00d090007484007070003000f0410021750120f50548a1501080d0042c0000c56281c030768941260360f2100c02e410340c04c2c040113 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 700374712 1250 700373462 700373467
    0xc011d0111010608011e0c0e0a030807060b040c050c06150d141204080d020706020d080f13060c05071a010305120f040b07060f0c0306081e0f03160323 66
    0x20004480550031800c01540c195070b100c1003c00e00310001c3c00f60321030380e4458864000303003811100704400c02c4070748256681082c006003a1110609854040c0454100c940200d90680c5503981d0f410040040d0001c102480d80c840d1402070036184068020003d407541a500718100e0700980d1340e0980075103074400800039495010260038000c00000da21a4540403484c0c2e40c1d41c0580e0130510300c20160000540040c0c00000c0c442d04079840c240c0039903504100350001000c0e144002c248210000b00003502582c2c001d80304055105502000a640e0584a4004442ca551240c0f00704220300e2440b070014020b0700194000c0b0f40404405100c11403460304518528140e9401ca00948503071205210f030304282d9031200403015405181440000703104020a80a00ba24070300803a800300701020039141e40412603111242c05000d141c41c121017070040100000754180300003850342040d0004011000a0348c03901030070075403c10191000140705407029410550700e140c04d902c80d4980c0d40241c500a8502c540008802c0808141040107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 700375962 1250 700374712 700374767
    0x30b120c0f01032318160308090103142403010b03030d09020a0e0703020318011505060d06050910030c0e130b070c020303030708091207020603010308090a180603050c01 74
    0x500001c0036505050600141103400500450303118141102d507440400040010402070700390101c0092081c0a446018040110200d6405541000103010103030242c01c0100c0e600c4110303402540700e0306a26500e0070b1540c007103142240107416000128000b80303840c405c43c8406811181414003800c508401d0080203142460300584501c07005003400d40040c0c0c0d2000e0940f4001607024500c8140c60b00810042c0d401503038074034107510a060207049004142140f41e241185414441c0c4014a002055a00c200c40890380c5402841c0b00002a08154000c180e1000e4400d00780882038038030401ca00112441409410840b954524444078070758003c0701c1607850040c0c103c007038a0000d42c42d07120142d4004003500748410722240c0d079004a855038104880000c0802c0d40031041c000c020101b005510102d0202d00c50103032602c5031a5001c1500c502042c803006007100c0c1c1c00b064a21450f9101980000038000b0101420520303e052055031000e082036220541d00c0d8001c00d083e42001303520561155000302d61106006408001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 700377212 1250 700375962 700375969
    0xa1d120403111906030e061b0d050709090e01060905060f01051801030615020f060f0c071b030204141518010b07061b0e0a0504050f0106050715021306030b120c 70
    0x401080b620740c050120100c0c800c000d109462442c0240800c1d81d00081e03101c403181c100c545042d00291500b010203c2e9803450301e4100580c24104d8015100b0580f002c200c648a40c0c10655850015030441007469080281003e40f1103815800b01c81140e00044040c03102d511040300340143c035400703002242e000507003c010071260103201694031800554103140000341d02e40d50f20741c04c5405070140001807006800c8101301c60a1210100a501d40116101c0c840550b181041651440305108400e00200716401200b4034203984114941e140d030055030054000d100380c0e0725420240c0403a110441b03405202170140c0014803100c0c108a50056480f1448043d0b2060990a01e03032460074a4000010031900d2a403a000169180d203c08000741350503404588400020050301c104120f12405181c00c12401645018100181145240340c12070440b0745600302180c1d14040d07424a0081101018040220380b07000182e0340d031030b1100c0b2442c0c0740d00310780749542d04102070000f00f0100524880c0103211044160b002c030300710640625 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 700378462 1250 700377212 700377233
    0x3070509070c05071e03081803010c0c050607030e1b040b09070203120f0403090e090a0f06051b250f082101120c031101200307050610031707080d050a1d120403 70
    0x10315060240d010000c0d00c8c0001e03007560180c034842d00c0060380da0a00c400030081304000003600501d19040610440b5030150341559038070b41d104844501004c41200d01390a43c0c03141d80c048441103c0192040c0c1c028038002201940c0c0c5c0d4042d440d030380d80408000e40050006104001922300032545603035552036552500c42102d403d0317900030f00210524040d001c18400002c224040e1035a459100c0d540100d80b92624001040080142c1c1d0004005658204000800112404045041216803103920444181c4500300380c9020a070111001780890300c001100d9161003241c01038000b520b83d038203c1b604600d83e00e0f40000b20b03411031281002000041079550510004601400d0004420f1040c0750141c40c40403140729000886000074070010250f000050503506210b0306000031548482081c50700c01c3d80c0d41c40c541d40c0300d00d000f02403042040c8404020a2072000c0010100c00c4a001a44080013848070341810301c0614000c0c03100c148440e0007800341720444282c040d07010480f1151140c3c0e41a055040510f191209503092 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 700379712 1250 700378462 700378477
    0x60708190204051914010309020d06021e07050a06182022050406060603020f0304111c05010516031104170a0b0108030a0305310203070509070c05071e0308 68
    0x50380074000416203440d404462130201013070383c0c0c1000e0024680311103549000b95442405040500300101c0c4005031b00c40b00001d0620f158001c50043c0d583c800c21807401070285c1c8c5042e103001c4d50400005c0000a1040001c0e000b202580200010840c4003182e9080ca030300494245c00040c02b850100c0c0030080b84c010018140718418002503c5a25501403402c1c043c003000000700a544143d5640d00d040c04244001442040083c00340c9080441c03a054204c05844070303d0000400090048a04030300c080d20030b4072001c041090300c0101c610f00b072a1011a9103442030107000c044a00d802090340f000c20010400380300c1d00507000414981140c1a01c2c041c03c0500c3d8012132461044480356a200e110100d000044107244800c1c000e0840c00c1c05540c071003071500340040c150b0318042c1c407884840703090050040410501181c1c0d651201004151190300c08040e00c040783c10441c407544800ea000c0d005c0010414402d40105050400900c05d900b52040c668613041c5c0903062410840300041a120301c0d040c184000b4081e0300042054 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 700380962 1250 700379712 700379761
    0xb0108012706032316081203190906050f060907120b01090807030533010506030a0e12030106021009111216060c020a05012c19080607020c03060708 65
    0x40e601c0361288030040b841103404c4c1106240d03848240e0704c5904180700500d070b00314610180319030591410401c2d690301d66203008403661603280000403607041181354090301501c0f440038000340b018501c80d040c10001000d080701c0700ca048518040001c0ea00d440d121004921818041d00c50001040b1030849a10040125041c00390601142c0540401c443d60100120303402540700b03034020314104501c50100618103e8000c0c00d41d1860390008001259442c009230203505550041ea0501d0b2aa41c891101c1d0380501a010040e03003c5008031000c0182c69807103e4004e5050f141d15408031100c0000f400c3d0b0040445103084409024048100325404452a04101c0080604800704c2103885003000400035000082c16648980702013101c14203c1c80841c03c018248000420090038852448502c01c01b005240342000b10f52461000c00d0481c1c01d059582e100349100700054810401d401c000c54480c02403550b5840140d40d49005485040c00b0702c0c00901c1c00240461041071030b0741d81d03c1c1403070301c6a491440340b44030b408008586 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 700382212 1250 700380962 700380971
    0x10308030a0b090405010603030306081c03181e020a0605040302031c0311030a050906011d0a0e010e12090901080601120f061d030904060605030c07020607020d1a0a0b01080127 77
    0x180b82d901d01c012540214019000000c066103113241c0641181d440d039211307413030b00c0e0045000e500d4021018008205a098a401c012405903a1903c03252105802c0d074000402d041a8000c000344402c81d05071070404454400c2d10801c0302d080d1544819511805144002541540440b82001120441c83c285000900c458203011400301a510079141c150342085540c40f02c0a80e032002000f060441c100151030040c40103d4140e90380841e02502c0940d240c2004240d6528940c90f00d5011411100940c004070240c801001a2080f042c04100186290390003078440354030034503205c400030940700c030013080c102c0c1220441c14180c6001c00007984c1d1300c00341c501552410303a496666104d50301340546408902da0301c0380c0450307030140d591017003070354100000c6900f035401200c100001482000711050703008041714044e82d0121030b26070700c500c1d030351002514020060000408a1010001040041e070440d194980520f900074414042d080b8050011119403000740302c1c6070032144200d03017a813904c503403802003181040b1001200800c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 700383462 1250 700382212 700382231
    0x203060a09110f120415020f2b1a03010b0f1f030204240f0e101b0614090d0f02030d050c070b1f1d010312051c0c080c0909010308030a 59
    0x20a42020010f081ea00b413a00301044100603401010501a02ea00c1d0380440c140b41c0820f51000341070240c0d0420040621030158004507104c140705280e00841c1850f082440999142e00524814960b0b0520a40c065800e0504c1104c40d0b00d40f5120740e500c4030a003d0207160955140302961555140010343d080241a42000003040101c2180440c048441d0060880c100503a000d0000034a88030f039003060302c41004103038250a02c0302da45206690842260b189800350000c4000d1215084a410901000304494500321805080e40002803013140700354981e0703040d5081c8035036840c001e4070003410038046500182c004000700042c41085900060b00140d104c1c043c03030b05202c26540d80380a6240281c40a1284606407440391700250f0202813810081c100c8001c003900314024407000801441c0040c0002010071340c4038200380710344500c00d10680e48130705a00d0103140c00b000c2c05080c031a00207240c4101c440d00090000b100080c01030001000b21100108007615100c1d0503861601c8840c1c464102421a100305034035008000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 700384712 1250 700383462 700383487
    0x605030f1c0e06040305070b18010e0a0302040b03030d0501120c05060406120c03110a090e10030209010504110c0601030c150e1e0102010b06040303032304021011010b06070320010203060a0911 84
    0xb40c05841c50641c049d5441d000800d124800c0c01710710080d00d041027407101c41c035141500c4550415080b26416180416941c0843c40000d00b180110701000c0800391801d00001032081c5000815041c090044103040f04558aa0061000b10b1243c0c0c001c030808180766820400d01c003c95035000b0902c0948a24002a840384c0100409400d030b07111603007841c0000e04002c2c0c1441844c240d4019590071025207004129847e14541c082050000d0504c6600c1c801c640c0c6004020080c214001100c40c20107501080d1020382d83c4a03c1d010081e00450301a50f5908403840120b4200c45000720b0055983c100000e02402d050a01400000111956a40c201d4110754850f00315041da6121030303000d080a50b02c6514046266070081c200b82080064030103550005003800014000561540413100813104c025103880c50440e59095001805031005a014903002440003a01c001030617400340e8441d522038540c3c00318540386e600710300ba82c07801c5c7e010a40c1c0b0f0a600c6070151800304040315050740b0101c44035041800340c5082c0036844500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 700385962 1250 700384712 700384723
    0xc1e100e01020a0f02071a0d09020904030c030305151c020111010501060e03100501060c1415010605070b0709140d1a0c120f0c04091d100605030f1c0e06040305 70
    0x954036900410003a43c06030b003050010809149620003090355a280406003001002100340145008100258990540140c0d4015298094029004000d00d003010b240c000c081009001041e8002032501010660b2240f4840414003680e01c001d107628030300d6050036080005008006012410300806200404102c002801114020440390302c40401000c80c2d90141400c3c0030300310411807502850b10005212700740e0001c01d0604182e8110541451010801c1801407610341003078441d0385803120314000001c00a034040c0080941d28400c040620a940ba102420795100c40503004081550000b0403c200b02420281c0000c407242c0d000d01d04403071a641d0003521074400c40c48242d0340c1c0070f01c1c2040010503804488800180d035070011109098291240381240e1050a140200d000b2100010344400c4600c03820100841c00f0100142c0080030b07112040b0011080c000109001d1288030b0103805004090800c0480128a0515205203096900744076110031130b049030103182034004954480400d02022004c03c804000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 700387212 1250 700385962 700385981
    0x30711010e0618070503210f070615090e010504050616020307170d0c0906020d0e01090801180b01080c0105091c05030c01090309050406053109060209150c1e10 70
    0x445246040c1c40f0b00c040c0c0c1044003a40025000380c1c0030300070710729801840c1440d10041c803031070b0104a41c0720a03442c0341154a0344100c04006c0d1000b42031103141c0303103c0b0340b00110307007000c03034070f80203020090344c940344801c03030700383e50044901408a410240001e0300c2d80c4441c80646500d8030081c41038914140071562021003105d0b0040100c8010940441c0b214001030461048007465005802c00d50700703852418500941d550380c90024202006985080406146d00a450036005001c005000307001800f05400b83c980b0300741c001d16007661110385502c000640354070301059103118110103a60755443c0c900b441c414080002c010920385a007660310103075018003088050000e0255072274000c0000c214150386050081414803540c06c414031440c9820020060b5a50f038200d01c2d102c0f42d44521450011180c416102c46241030721a0001c1011401c016a01007008841d900420231480201d45e10031640d070b54442d40404c03600940b1140c1d10b065201d070160040000045400380450142d0000300d80705511602c003004207840441c00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 700388462 1250 700387212 700387231
    0x50903100213272d06080c04061a07053f0309070e040206070b010b0304061505010509040c090f0f1d13170d022106010c020a06030c1e020c1503040503030711010e06 72
    0x72000e100b031003824003129403501c40c111230a2015a082017070005141040349410303c10b02200041803400c02005011000172207890460001900b0114020304002100389204131b0181410901201a9100e104059a00881c1003000500d145030038030309880e0850001a100f41d9102c00180062070001c1c004540b40e60103803030b80f1803500d07880e410b00b480d180d0140c0b9058009045000c00f240814021030741e12100b0380e81410400c5601154090b15078906440882d01e6401c075a411039500030b008a02101c1c0c0301c8090084031820b58044640c0c505030301c6842c408000541d044a0383e0702001c0003d6001c140751503403850010700c502441c00e280030720300305e8000104d03440003000f40d0b06901c21090030b420200c011214298072090038280204814440c0d80003615440c003c5c02040103040c0d582d1140b00020f44600c207602409160729101d5824052428006951000c40322075552107081c0e4107980b0104503103c00c080d41d00803580300d0000d60650310740b030a056401910745c19090407590350f1004503250801c1c040080d14003903d07421 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 700389712 1250 700388462 700388471
    0xf0615041503090213050f0f0a0b1e2403131a1918120f030908041805070519030b04230708070e0a1203050903100213272d 54
    0xd1043c40b2190050a240903491440d006c204180103c6204810f0750180c4000451740555490034000001071400b480c0b02a00013182c5a40342d0040050302003d03a1014108030380324000c0118000c440041d0309076041d0304240d056010f0000c2241121401c5000003042c0c030882030b5205500310040442036002088507000c2c0d40c0541c15104c903500c0d5100d4848c40380c22700303100c00c040445500b4a4450b140401c40d145545400c0012007a12040718511a81c0460a401c0c0d020420a41e00d980c3c0b022100514051502154800351030306c404104080d0168045800c2405019140c3c0914420200254001c0c25441c09503900280c5411064087d030420b0342144112119001d03c041c1b140c28a8400141629801041c201c144098108001c1090340e40040da182240c1c3c80400c000b001c8902c910382250a07004141c01d0307903003500c207440042e04640e040d600a842c0d48126161000c08990307031100c2c0380b003198104080c0d07403e040f00026201c890a0019400505110440c041e110050211132600c8003000455406040700142d43d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 700390962 1250 700389712 700389731
    0xe1309140705040c05030601080402010e040f14060a050a030b130c051f0e04060f0905040807020414070e011b03110f0f03040608010e221113050403080604050f0615041503 75
    0x41c0c07080e204c501800d40352032400c40c9040f10010341702280c0904080d05000f800000d504455a46800100400070140070510148801490b0f014202c401034426078443c08244a001c54182011000032045a401c00c070340740e65586070b226100c0885103901605583c00d00b06c62802007000d4980d8021440000380c2d040320306000d960403c9000300807901e42c074851071241d41400010403000c1c40c1c620446c01038580c40d0708000f505484518143c111803060010081d00f182c2440314180480000036230b20303841b507411600c4031002000303281e004444000c041a1244003c4a0607403030391010038450684d00d40711300d40c0d10303048402941c2891401e915040c044540d00c1c1a035400080d09001080c0c2c88025180106041d03800900d0504241606050612200381d401c140040307040703d468240030300380c214500c440c40c01074150381741c0c4a690240c040c09098101d0382074021a204002040c65410a4424140f1030002004e01a410f92a040100224016101e034880d924440a000c04250145104400d40503a501f9440010b4000803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 700392212 1250 700390962 700390969
    0xc060a02100507050423092e0b070b010602030f030a090219090218040e07030f020319080a030c0c051c050c0708070608130b06010e06040905040303050a050a0c0e1309140705 76
    0x414541c6e29a005096000656503903c03505149900044038805c00c8480c50362241c007000403015840c451030107403110b180c0b0000701802c60f04000d000c858020340c8960250b81e02d416059917139204103071842407078800400000b03403600703e180c3c0b10401851004000f081440061181c40c1c51103a819080094450341c001003070100200000c1400c5a0084207540600040c0c1d641840030f500d031000c500c03000c0e0020011003c1d030300440d581031094000700b08103d1440c00703d0444170304104a854005102c8140130a00e054070000a9a0184902030f020950020050100504100c1404074901d03e400160042c484c00b4071441003810030501501015100348401410030768540b140c0100880c10180207010880c104118203004140c00982040c3d20910a0800c1400d041700d850200d0700718821580a940913034900400d100070541d0640195015942406040c0300a4842c401603408440e00113003c50085616240c00401030304004444180c101da0703032000000c045d1110f0300c40310546642500c416a1035000284180904d14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 700393462 1250 700392212 700392239
    0x180906100f0302011209050129100504120f05030405061803060c0412030324120b0c160209040213230921030405010f020a03090303110c0c060a021005070504 69
    0x1841050700e109041c550340010b805642c00300c2d110583c25480b54206010300500750405101c000546082040803194200ba00d01c13405644603c040c4144010303048000c02c1032117802070740c050310300c40c11614103803071900d5075a141851214070044801e8007091000040030b650369005002806250140d00d6420b5202400709801d02400414144001c64140b005001030302c4100503200019506080003d49524110760301403640044031044808458403034404a08044160030014407140b1641c0e2500c0140c94003030b0085040e028a180e08a05218840307101c6016290141c81182c1203070015100076000306840345c02d102074541c400d611029010007410900001918406041d6002d90000090140107030f80500c561040b120b0548040a00d8202002203010700200390722440180c2c4240c0411541c813452038401078094a48800b00398007280c9001030422000c45038800322403948140c8030142a42007901410000c4a8100808103404c51248000d6015040418480c0d980543c0a980b140c9840d14034101801c40da22703 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 700394712 1250 700393462 700393469
    0x50a0b121e070c030c0507090e010507020d0f120902090c2d0405090411120d110307120c141b090603010209030a0b1e0f010510080f0c070218090610 65
    0x200580040c240c040041180381038010400d40381c031024140302d80c201105c2010800320058198010040009035107000c90b440900050003040092181e070b0b680c2d000aa13100c03520814001c010a0300b168406181c82d12940540c0d002e4000c0e0000080c040c2c0454010039480c41c0121050300c102c04000582c070040c808180c480104100032400d0071500401100d001094501030b074458140101141c00109041140c103a00c1000300040181a80d00c0704080058041e503161021074a0070049404c8030392120403c140801181c90040d0041010841c00b030b00f90358202d07494002c0c041d094032500c00c0700400160721a010300c102040b100a180e03000900c0250703001040360b4180f015040d188640c1c410441d074046910085580c41d1007a41003840c1c0046940d40103040350b09001030f81c2071409030003e9113040103c45281301000034180c56080e04e510000a410034026a80e0040c107855610390b50307500c4000030f09603042e407400600075540f0141104000d05e610691640300341d8030640e62411150060020002503480e160500c5008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 700395962 1250 700394712 700394731
    0xf070b040806061e0f060c100c091e030b07090f0306061e0e0411010e030a0302071418151504060c1103030f09040518120703181a090109050a0b12 64
    0x244c0a80c080d030380c1c0d1220320034401c8a019141e050306010b01c0b40d5450054400c0c0d1242d071010384600b500c0310a8008010860b00007208040f4425a1022421103000c0321000c1130f4000700d483c8601c2050030b6850303c16a1260003018a401c0000344d5902148003a42280c502005503c00c00c40401c28900b000c0600641c0300001c00d02244074003442c4030422080b410124040e801ca90099240c140421034080100c0d00f407407000e420b0640510820b82c40c20101907000070000200c075903403200902005030100c20041440b48090042701642940302c04590980d019031641129207030000c0082301d401c880b10400241580080d4040404900e0110041d420712000d24100d5000364402c801031131410078141c020702c529002e030307121081c001d503507c40010fa24103403040b5151030758a16003400c07103408003007400402280303074001303402280012140c1c005120410f50101001c41075401e0709621080d19580407201145071b0300015602810040d9982000806840d1110410060940940d68554491000c601441c585001801c594507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 700397212 1250 700395962 700395979
    0xb2707080403051b0c040612050f0604230a0f0c05040e0c03070603150902030405071508070207030f03031b081b0c060105010e0a1d0403030f05070f030203090f070b04080606 76
    0x6a881070803a0580310b060070024107402d103100904e07498030f40010941ca80180c40c05d0303c04075594020510800720141304104035010380040e6441c9603100d11040e0b800800c0801041034902c028040d0380c7e045070115007284221104000c450301d50101c510112002039500301e56949040c8858105402119403180c01c0000504a07004c2c003501103503644d4101c1c0302d884101541d8401c0b01c0491740c00d000c41c1d44002c2100c03510640d01d81c00d00c1c0c189207407150418404c14010249151503211014082c01c0000e220b8815500a400058959101c3c401c2102c80a50b00300d003019030351000c2801c01b00300301d8824425540d4603a55008107140c461420140004060009540c1850a100c12041c2a000180040c19101c1c203190100e204008007021404d4000310760081e40300c104d40c2180803c070a0902c10142e0f40f00d58040d0f41d0901030f030329064a0f42c90407244180c40c00390000d469600c41016031400384d00116001400b240403039121000c0d0400c400d0400b00c6a41040c080b26100050401404400304050f58008404403440039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 700398462 1250 700397212 700397221
    0x307080f0f0a0e030702180f0601140f0f120a140714041203030b09090307060f021c09110a030803060310050f01090f091e0b1612050a0b270708 63
    0x740c1110005066190305500e075031260030031250900540c0c02496001c3e06403095440458045100f4110440ea804401c2d0380d61400228650702c11000b649000b1903403540c0602d00182c62191002e25404104a03c0218004100341240c29070801c45a501c90030070180b001421100c0b501c1601092280501000100219110041c800c80486c4040301e0407203a038100c9070f04a00c4450b00d415006400c41c540384590100b2482c04000d0904004801040014880d8808000b18440090031400300e019405d4900c0c01d43c009010f4803100d00321250f200d020708500480000080144140000b000081d40e0f0b081120000c1d80402400f440341010400c0991302c00b24804180860f02d05113414040e813550511806010366143c0b8071954485085a0ac05149160000e003030701d03003410b036441c0d81100380c00e00c404080b10f0000045002485c00d40701e01e8502c9140400c10b54654514500368080c000107000050013100032a541c2d03114054072170360340061003414a500b0442001d40d625040c081d44400d450010700c840c042c0103a080410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 700399712 1250 700398462 700398481
    0x309071401022a0303130f21030804021302030106020703020102010e0102070b0735041208040804091e090b0403170403052704290604140f061603050307080f 69
    0x540155494400e02c40310f019100c81110704103505031100d01e40600000a6075000040d1601d02641602e00e001070f880404ca41c0d40005541400d0100b16034048400c0404082c00064420340d081d940241c0000c24070681340f01400c41030400c0740d0013a0300020159000845c02c104550302030245401d80d0312100002c500389440c6449843c0c40ba18010000400c00201c00c05d064411001d2036400e2060441c01891890700e100500569107000d074040d1026030b5007032001d00b4408101841103101c9842140d000c45104d040c03a16080c10031000c1e00d00500c610030142011320394001d048500d40301c2c00c0b001c40e005d408100f01500703103418040d0904203000080b80c050100ea50400c03000c42e0b00501100c010002d0501807006c9100c810702403c808804d6070940d65030050400c8540404d0003402404020108010049040d200102100b0004184640e105042800203040b203000e400d854104046800c1101c060071a5181010440c07040003a03400351f420450104001206004030706a0007141f03950320102e40081003219007043e0b1180c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 700400962 1250 700399712 700399723
    0x2806180b0a03050c01051b070807170f0d050d060305010e0a0606080a08030411060c061f0f0e01090e0a05190b0c09010503042319050f0a0206040306050a1e02030907140102 75
    0x380741800800a40400c10703017000056000303500711f42004c0d5038000d520760180719101c0300c1510850b0920450003500b0001420041014280300a40038000d100110030b42c1130030b9a040d009084c1c0b1240c116031f11031001020803001c2c0165004d80c8040340c00b4144002052414500716401e603007162145900c554003c8000807042802c40c2d4005820030441280c0c0421003002814512032817081c2e5445010b2a0f0500420350070350b120456001c0c4004010711301e0710f070b1103000011110000340700e80c0c11710a008000400812070240d0001c02d4024031181a200e1050305500c40c070340380c80003a0200c09040448001c142c0d043c001030303a482d16001103040710000c0c98588042d0000304603020240c0064510b024449483c2c090050740801d400c0e01416040a07280b8005482c3c4424030340c038100180640300390140003d0503500440c0030a0103244194000e107403501f49400c0d038446c50001c01d4014400000380c0d644140d002510401c0d03c0300359030011104000982d0303d10f81240404d04240199016000d458207a040002d0b17641c6e008520f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 700402212 1250 700400962 700400983
    0x1b01060308030708102303061f21080430030e04230a150801090503040314010b030106091d0607080a0f090609050a1e0b2806180b0a0305 60
    0x400207641c0c0c4586512000104183d808080b25a182208178540c64184403006d180e90003084042d69150ba41e4000c0202c2c1d40c4039004480c844042001c101400500140000da8107007580c4500c1d04019a0170030754400b134035940030307800c01c280220424080a003840740b4500d46a406101e00340403180c9010190b81c001d89040301034081d041c031580e1a010140302242952001d40d400c0122008620520704100712008010f0050f9602d408600c000030101041c0d0000501458501c1c5130f000c0c00540c502855030302c6410500b145029405e4655403140c140240643d02405900c0281441600c0001c03031482c1181166102012681248000c0d0015020001c000b41c20004442e40301800a10100c1d035080da03654840024114044010300307403442c04040c0024031000151380a0b07000d100743c0080e051300c00c030900c03522880b07076113040000c0c0805114400030300c292180d03000c05c01702030980402181c449000c0320000c00980710660030404040c668022000589080c071300440f054568107468415045045031981da40b034035010305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 700403462 1250 700402212 700402217
    0x3010e011a0712110307020916030b0901140f030f12030f150d060c0512040f0c08071a070204060b122205070506030402010c0f08031e060f041512081b010603080307 72
    0x44504c3c0c3d01110501c1200d0b04154002c02241861a00d070411110045920b031032100003a140c0025a0f409080200b201030680d4002a101e0f41d050b18000100044c0f64404156950103004001d82c10034280420080f511760322a41d026079070303124a4901008a4a80c00050440c1e10000079a140f00095440c1c90440303190040c2c00003004a2038140060040c1d41c80d11425520360440d40c114002c001c14040030f007007041d017041c1c0b040010b1501c1030394400402d0783d10603107806000f548000c0c240c0c001c0102c1c3c4094004040b18ac1c400341001c15901e541300c034070702c0c059040304003221584ca01c030800300241c1c0504e400d5255a50300c005020a1440386158a0740350343d92440e401442c0c000c840000c082029a030180c00c04041480d40000d8040c1288020300d420400c1c0d400948245181460304508003043c07481172090a4030a220103000c0c0720982c112202044040c1c800002c2101c03010b60401000701e0b034103c8036001d120409005013442d81c1e68004685043c0340c1076440c60103110480e45409804d1001503060301c2220340110705d61 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 700404712 1250 700403462 700403477
    0x102010f0c230c0d0504140901180b181f060206090c061315050a1d0d0f0c030b0c04140603041a100503031902060a050f01061b020603010e011a0712 65
    0x148080380a83c4030780410301001c0c0c441c61a80008440c1c0c07200051085d514079100c00c1110100030402e00070a86c10038014200151001d03e1842c8140c103480e40b06401a000003801d4405410001c10b1000310b9950680d506414a42a510100076150030012404000e00c003030320080c0001d10385201c696803219201c8000d1442038000040c45d010321840d00f1440c03c0600901e118041c240d210900d00548107a0244402d200400e919860b40b000c240d0303c044900d24000ea02038403014807007400c1d40d80c0048008001d00201c0798107040d01720200c00b242e0803440c483d00c50201545900c1d61541800c8100d2842d01c520903500d0701c02c010400c1000001000242c0c8481684200220b041083d11040c1e5400d08180c1103810103031f094400400d0051803092042d01d51445502c09400f03807081c6031641607640041c0d600844145060000c110010003445101e45401c2c07a40400d00c41d005283d441050f03000a070a03070700c05e90100111501c2800140050300010003024000900810100d00e0084a540c070002c09420a07070845050100c0c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 700405962 1250 700404712 700404767
    0x50a110a060606020d08011a0702131e0203010f05041b0c0c0b0c070306060e07020a030e0a0b030406060501020111211806090115230f0a0b070f020102010f0c 69
    0x10018024603607848581444601c0e110324000b0341d9210b000848500140300c40000045010070034400442611400c2c82e120326080301ea0302072000c1c851500025145407641c5440302e1264000044003041e02a81c4258050fa50b545010342582070480a90400d034440d034541040100101c0400301c0b103698038545401e00c1e03150540581002c425514007a4000c034025500010303054074014001c074200c0142c9110750010810192180d440000505040b02c907000940e20041889010074042e0700b0300184041c00030070760620f02c0c1e00e5041e1980960026502151615101c403001d000c15078082c000c000c100340b0014084c0f82000171305601c401507042c0d00401c0302c05600602000c00c580050007404004850211743c21140c00d0300382207408a000703101c84505800c220907001c40115441007141e080c04048020007845040b10f185d04810020720401d44004070354080e640000c00943c0411030800340208038040c60bc0101c40c43e44034000a0b080d203120f00700ba210040c0c5000e10050a0310340014003031460080d08080c00c08144213 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 700407212 1250 700405962 700405997
    0xb030303131a0103060b210d120b10030906110304080418060e15040506010915140d18150605060f030702010f06080c03120c03030c1303020d0f140d050a 67
    0x801c2c075000c29021107558000f00c00d100541c1c10100e0100c0c0203641c4901040400003080c1c1c00c1c6414005685c0d95500000d016100b05031044e4490459010703483d00008801480100040089403013045a2011a4030307410824140007180c072a2040b0000844501c901d50314282d07540200d54450f60240b6240c0645400d15040d034002140e0015014040b075040030b0089003004d42d100388000e122507402034416414040018442d500c603265030300854040102c0400840b1203540207a4203028001c480380c1e001e6109124a027148003183c0540c0c0610500f02c162101881240d05244155500325101d07445440c0c2402c20401150300c5a000f100c07003075070180009980301d0300c521000701d014008030021b0480c11420f02c3c0b000f1400701c8004c41c00212071181182180d00d080b8009030968290f0144524658141d00300340000b58001c4480d40003040702c80f1402c10070401e01030b103030342c0043d485444440c02555090524070001c410419001040c80310052100010940003d0640c80104140b00d0084c0c0c281c2000240284010580c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 700408462 1250 700407212 700407233
    0x2030f1303020a03060207050d02070501020607031a0d03082202060901080601030f1407120b0604050d0f0507080607030e0a021e06090d0b0708070c051510180e0705040b03030313 78
    0x42c1c0c01001090050799900b0310001a420001040d9160b000f4892030a015074000140320040300c206801030700c12652200000d0b4000d082a0b80e1600c42449641400c0c44155034022100000921a07140c0c0700d0b1500344000a11421209200c52540107658244008056a80e8134140d402c0c4c01e000346420710103640d070400101c01401504000100d030504098421010a05140704184540415503914205502640013401940c1081803a01d8000b8000c02050142303080403030002520b0b46c062441040b49100d00d40e117491901c81a940040c0d800d03003141c4140080c59505003e01d920a0007144002c04240c0259000110b8174000d90b44404a1381e04141c1c07800320307281ca92500707a0710780010080034200c400e00c1d14202502c03641821258403001581030360014100304d000e61010600c06400c4001408040b12428103000f003a900a0400300312a03100d8203000820700032940461010780301a090200d03500c003440356410718158458005030701c82c2e4100415848a40c4000054981c841e0b0010300e03551415065040100b02e28 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 700409712 1250 700408462 700408469
    0x204020f09101e050403080304020d0f120302070c050a06120e120d1505121f09151b030501181a06030f011a0403020603040f050705030f0a0303050903030702030f13 72
    0x4500844a8040e990400008070034101d000c0b400c4141c20307103c580b003181c0343d10803400003c18244007070000c88c025080000e926030205100d0300b85078500e5000342e200d02402c07403400b05d01d45001903000503145041115100484004040540e000d514880c20702e0009080e104401061580c0240e83c0c81071914074840811103031141610342d0400c1c5507244000d00c142809480210000d03211040c04070b00020b642e0034502458018018140041d06e6241c4015441c1a9038204031804101d900f40c0310305240d00440c03221503034428040c0015034001180d0780e9a6090030071220740140e50805061800c2d0040207500e208545419520010420020380504142c401c2c1c0c4100b03424400e5960000b00100c00c001031b1500307c0055a0594001030307001c5c400c0b2441c00303500141d584a540002500b08400f8004a80095a5194114201f6201e2820313599203580701c00c003081c039041c0068801c402c07560060701036806064061040030381000c01d02d4040d518500d002c1802035502c1c4540340c0da81407805000203501c05129405030044018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 700410962 1250 700409712 700409719
    0xa031518020a03061509060f020138030d051602060412080c0f0c01090306050403050c010e0321012105030c0712060e06070f120f0906020a030e070e01030204020f09 72
    0x40d8104000d400c0002c0d0840d55991010a240c204089180c40b4000c50840d045203240d075624140310309001c82110604881ca40384000d6640b5188400001c200f00c00404228109900448002404070038503128032004025825020360080b004590000d5440001c0310800d45c1c03800d07005c2d440d40940d440850303050711503640010403416007110420300300700f841340c0140310381c09064003260140201030070b03040c1d01d4002050440c0e006c2150070008200282198000c141c2c814041d041450a00344100c10303081c251582c00c4c400309515000050040c41c00084407004400001031030100d003030a90b05000c010003503480d00014801b1040c0e0031131054400c001d0200304940c3d41c0b100300d100360b4290369030f150684900340c102881e003107914a040160034845100f001940c1e500c920060368800c1c4810203440c00c240e41c0d60720b04010b060621602c4998011500c181402141c00700b0303100e1003006a5900d4441001402c9a02c403491280e0140c1100c441000785242c1000c01e1819070342c04850042e41c810326144c14282521401c03244540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 700412212 1250 700410962 700410989
    0x804020f01210507020601050603090703120903050114060a0f03022209120806030c061c09060e1b1512010605210903030a06090501050a03031103210108070602060c0a0315 75
    0x4060054020900483c0300d0b400301c1b48140d0b01c1e50100010350000716800403161340000784c20001b05120703101c50100100c16040805805441e61507e0342520100450710a203c546003051051900b05001034800a059201300c020401c2d086074000b030385401045018864400f51101d004014914903840002481d40c071144840e01c0c01c80f00364001d040100101c072028440e009980300700b505414510102c0b5146900744000d0030f56668506803030301c000c20000d04203852107540e030720540c0c01a41d8200506200e202060388020340410f01403040005046541d41c822000741410b000030300c006c0c520411554107480213414420f8658005020241541300013015120f51020f40d00c050200c0400701100550084140220500c074036030700e44041e503080e00c2c028441d00c8e402512506041020921804603414400712400599141121424101000500c05c0400700e0f4805140700041122001c00c03c198001802503001500fa20b1134071200340b29650040c2d100003000c2c15190b45020102500d07411340d050183c070384d0421410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 700413462 1250 700412212 700412267
    0x16030309051e0a05010b0301090b0f091606021b03120a140909040c14011e0f02030f0a08010513050f0615120a020c07050a150c051e0d03110a0804020f01 67
    0x26607401c3c0300e10059840354600440c80d81c2134101800360801c0640c104845030794603220b031591005c0b0b1030380c01001100350b402510b1600d04450383d034800500003002145e004041c900d101a00500c0303405460920f0f28403a5003c408000d047c0003991302074401113031150030a02ca00088812446205108200e07003540d200c0d11000400003003010b1800310005541c002800746000030f20b81030042d10241d520b2030540303c0c800302810410700c0c8540701c1d500d00c1c464140d140c07041d2404c0505100002c5240e400c03d034001c10120f101c041c014855402d1101c811210382890340737410f10450412082c0982c03001c0003d40a640500001c2d031550428103044401c50340000201c6c1c82c00c45241c034240416600a4100b0315401c0704a00070030034001003e141030741d014800c1d94000c05008901281600301503c2c6600700107021200740c0100c405040207104c1c00701e82005080c0c00b040107056403000f001001002c4030310440408140020900040a01e46d510444403036005505942e0310002060f0b00c40180c60700b11450007041074241d984e15080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 700414712 1250 700413462 700413523
    0xa03080613090507090b04090c0b09040f0e010905060c120c0a1403041b05030a08121515070b070923240d050907030b07080a110c01090302060c1603030905 68
    0x903040f41d01402c02000340700501c81c2040141c03450301030060300c007410000050154850140007008032f814020800140440049a0007060301c12002c20041513035952010202070001c14442d5991140790101c08500e05404030909801c8000003070005403502c0b90105910240c1c6000d0040c0840405513400415200d10701454000c0a130000210042d0915142c0100040e4604000601010603584454040d081880c4000d2254003410020162501c0051300142101e17103481c0d40f4540c171026003109100c140e0b16016420f040d10345180c0540582c080295400040012403094440c6403080820100804107a0100c140010300e04d81e1881084002e408140d030700f02d49895840c400421584092440501040d925150803030b84501c41c92201038140000c00001442940c401d0214590200c01d0b103000003078101030000c2c46038071a00000170600260390346210040038160100308680e4003041c00002c040c6040d0480b00400c00c5c58840d104c0090a140e212801c0c0340410600744405100b0031141c00c85840003070340c2c0b030024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 700415962 1250 700414712 700414723
    0x3040e1906030b1014011b0606121203050705030112111f0309021f0801061103070605070e0102190213020c190c030c090207020108010b0d0b091006020d08090a030806130905 76
    0x101c00204113403400000342204000c80c511842c14058442c01d510000107081c0c601307092415201140c0c600e94a0034042a40c3c405080f902208a00a041c05201c005240c0300240860700060000c0c01071100500040000d80b030000080c840c0158130000300c0b540c040f400004180e16002020b030300d461410208200351091a80340e8450f416860007150060b8080c01d943e00c1e034160034107485403282c0004048100500c140da0048690311001500401100d10b0200349484007000c90380c4c1912514005212540723a540a9039041202e0704d01c1d0000740258041c4840c4582c0080d07060034200525804d00394020580403080780d020700c2440100c030200c0450414070f80f907615021818420341e0100702e400042017040842e10444600c00d5402640e810384030b8a4103a403d0850038003035900a010307481002612001c090003541caa50220701e00a40c40e0302c490910340ca0800710068244402c03000c480c0b04101c20b80040000d28000040e90404060b01403c00304200d4070341c24042010580010715621411f0b0400900404100c80000c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 700417212 1250 700415962 700415971
    0x30e031303060c021002040b0f07020d06060305030904050612070911070f0f02042a0e130c030f0b0f01020a0b060111030309030c0d03050610032c030c061803040e1906030b 75
    0x25605d500420301c952a0480c002c5002d00c00c0b90b80300a006c8485500100401001c4807800100003000c0d041c8107990704001d4603507079081103030180c00c04203d50b94642031600815030440f80440321290346041c2014019135508051103000c0da040d403142503e48a1241e640103c6203204d4102811615000503400c0050035009981c4049015a18000d07085031060103c0010300c808004010416141c0d01e04003000301e4464040520302d0754014494607215040010511031020740750881c0d00c01040c60078909a94004482000440ca800f6200c1e00024401582e80820540005a40304444004035110840121242c0074601c0c0d1810720b0380b01c0007042c0100080000060101e01e41a441100c1001c4000c3c04200c00380c0e14284c51564000c4014041199800e002c0d410600d403482c06851018250884a000c180d02d5140040f80000980c00000e0903a441c0e03c03043c0710707140c0d00034100032281000300714840d02ca5a40c0d00c2180301b90091010040c01217490b0081e10110f04032003003078441050003030b00d481c2c3c241f0450060f0140d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 700418462 1250 700417212 700417217
    0x50306191b031406090f13170a2c0a09020705210d06060216091d0d0c1509020108040b0907030b07090806060108010b040b09060405041109032b030e031303060c 70
    0x6000403418504049031621030300024103040540d84410003080b601460190b0308890903411600300390001401303030002c4c0c2644c003ca80c4d43d850800106a40e0340c95040503003c01e0084c80fa540ac202c0a01580360520300038108d0381d0080c0d0050b41d510060404504001031301c00d061105203519004030b2001c685000c003510040d50f50003070410105035540e6007640d0354004d030002158005110101084429440d500100b01102050b02e1030480510000c0c1e842c2c102143d42c0c126401040c8429040030503c5105804e00c480c5556007282001105031f1074001030440d2000401c000c0605000b07400191507080140422802198004241101800c0c071510203444e44010780141021846800002203442d846400700038101d0f4107a8105034903241c02e0901d4415a5440007080c01d80051041000040c65203d0b4031a000b1041e5400e00300340d4640ea042e400301418000c07814010300e051403180d503034200c601e0702c020301945c440c45085c03c1c0001c20080e0751011505502580804e418081ca40e540b002040c4642c81d0445014000e10307a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 700419712 1250 700418462 700418501
    0xe160906030c05040b06090a032301112505010f0f0b09061e04060b0f0c070611190c0b1206150f0d0902030c0d060b0a050604050306191b03 61
    0x1000108111035291101600240010744108410308055211880c003040c00b601082c80d080000001c00c02c44500d5034800c8481d01034000e41c0c0c600680c00c159001c0790407100d03c0024411414030351011140b601940005080341840046100e15441240050710000f5603c0703402401100c150001d103400820740c0080c000400d41c00c0aaa401807442d1141c002885244005e000010a44103800000780400c00c54400d240c1083c1d50b01c90104032401c1e0702020f050001f01d05003403280c0e6401e0000700c5900700b0703141d40d102d2030502c0184000f070400003a0114078a0b0b1108144240c130310402419050006040040c0c0d0b000700c0303008800141c8904503c0402c50302c0c5200303800c1a145e42d1880250242e410312144680a644a6040d00502a005038100507401c01801d190000b81126800022900090072001d800e81084850541e190190021820b0001d0510b0080404644060401f483c0c000483e0f00c6480082034034003820b03080c400386150500b040d0310018402007000c105800210640001900828686211001c4603048 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 700420962 1250 700419712 700419719
    0xf06050414010e030d080c0c0f101404080406140d0219020d0504062703140703050c031204030318150e1e0a0312020f0312010e070206040b011701020d0e16 68
    0x5510555400f60010700103001410700303008110341d01c44000e460440511001c201d0004016010828011750454141c054500030b200b0618136403c48004d14082e44940304203104110100f507505042c0e034102c44a509209070440c03c6002040e100e44101d113030b40d40c5440e1010607a60700e40030321100c00d50041070240d000c403816080814415512802030b4441e0100081c0713405041c1007250381744c5030f10105c42d42c0c03080481142d450301c0f81e84181d840d94050800030b419a00108040007400006c00c58031620400940180030480102c0740304620b50f105d0350001034180003684450310745040b2010381d00720040c40c50000d52003101002c02c0c8024030112005540e20705c52040880300361b130220488034225100c160001d20040440d45959551603019030807074690019405540d00c46c3c124003074103100500d555a19900c40614542c1840122410300f0006032034442154020410000094041c4040c0c0341034076280d1420305620705c04111801c0c0648940c0c481c1e12005402c040841d0140b150005000d41c1c9800b1600d260f800045e03c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 700422212 1250 700420962 700420967
    0x30212070f09020904020c010204060c0515070c120c1a070f030e030901030e03040e0901020d0501080f0d080c0c101a010c0f08070606120b150301020705250f0605041401 74
    0x54080d148070300380e0410080090502a07801820303003010150001d42000105120b25003260000da004401150700c0c941d081d81000000e004aa1641a400b00e5000d4103050124004118208041c0010894002080c2c0b64420601400381a0503507a80300c0140d0320f4441030700c4009800742c10241d07000c5c4041001c00581d04a05400380c0074070100c400b41a0300460500401d1801100906121420300c081c2c1d00080101185a84511230030302e104141600016a841d0f11030a060403c90740141e001440c5500300c4464540c4040c0042000c1c05080124907054505854201c2c1c00c2103c1d03c00d044000a051099408030107071521243c1200d00891100307612004505080001502c0403a000b81c2e005021103060042500000e0b4030401424156005c0c2c03200180c2c00d80c66580540700c2e880b1200d0180d9201d0300c910100710302888070340021200e1000c141d0007903003040320560b148c0c0c0d5a5412000814017040c5c0100e101090700e404095124018100e15a620300081c0d65044050881c3d801801014601001c002039040b1550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 700423462 1250 700422212 700422223
    0x30e03190807081305090705040503121206040f06121109010602030f1c0f020d05061011121e16170414120a050601060f0305010f0e061216030c030212 66
    0x41c1c00400603894281a59203c0c1c07035a6202500c4000d90b61364890010429445105003584521550f4480550303441c02c00c07003054a0043c41c010300d090023000801c4a02d01000700d010102e504a07200341d1b00418101c803160f03403040140500740c0298000d80060521102445221030a50005000954a00c0315907620b841e8101d2301c0c0e06c43e087d04903485820401c03034966001c04400c0813000e600e4244d82c001401e10b007044e4614059030b00c0180758201094492040c00180d26100292642c10b14440c20140c61000c41f03028620f40303c1c201400035051606011422040d00c10800084803500541a8a03480e1741d4a0000764000f8650700e207101c152aa26441e1010700d00c5407103041c0407901542c6903100c0d0001c020144e10100706554982340b140c0542401100240800910104807080c080d100b580c03501090103104050027411520168007055040815450030410b40d215010f0680d0840c078142c956284440e9440c503003514114042452221a40b940c40d400002d101c000050841901d108489117201e89080c0220161b944 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 700424712 1250 700423462 700423513
    0x100302100503040302010605091014010216182c120f070b0403021e030d111306080618042003030711060d2414030d0206010b160f030e03 60
    0x46000040e8a4000d40a0005180c0c0a4441d20010886a8450f00802c520000c00e035041201140020310510009111103032141c41c4601c00e01c02001c188000c02101250070388140300e4002c4001212401020000454118502c2580b4005049050035021500d000d0460101842c1c4505401230f801c0505020b842c8034221031813a051055041c0c2040e0303850b140d1210103a0b0290088065200300c3e00c1098145583c01182201c0c0c00131480a1501c580800100600399554110501c1d0b0003034003003100d040c44142031f002e51802e4030003900d0300c8c50f80c076681d11022a00702060010f901d040f4007041d10800c810851118010b0b0290980940c0004c5011400c0050503900e0003031410050014440541c1d400f018144040504009100003902141c2ca6100c05507030401040308100c0c6074a50110f804e001c1c0b003e2190400c1102c1c0c00e03e000c2c0e00801c450b02d0740c280f000352158418003030b003404024001407410617100261039580c04986c010200102804280ca40684013104590008e40a80540d40c0130740300c1c2d1402e015503020350 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 700425962 1250 700424712 700424719
    0x70303051c2d0c0e010818160810060f0e040209152709060903030c030c09040606020322060c030806030f0f0f0709020f0405100210050a060509100302 66
    0x518680381e00740c440c8607090300d540d15120780d60307002c1a011010002006600d001040b0007020300707400d8111151416102c000041d901404408514840c3c2c0e668480c1381c196001c030380703800103501d00e0000d000e100c0d04014201d04106d41030311000c60081070804021881030000d00040300100041a524441c0040c128800d2003080c50800c0e07507a00181c00360a040036500d5106000c0103404201103800d43c00200b04c81441803500c03901c10240e000082c1070000700250130360000030700c2d00148500c0c940203c0c41a81d910001700b040954510100c00b21301c035081c006082e10740340300c0300400c103105c2c0c02d4803120000e6a0b6041060000d8001a1106865010079640010101030f91004e03035a9112103510340d107043d900003402502c6070350103101e4182030104201c07003401054206a4803d000e0050920600145842d20b003d58101c9490648100f11540700540418120340441c0c034159000d0b01381510300d0344140e041242101180c3e01c86410103041050400f050ba2120003510000c8525450035150181c04441c41c00346400003d40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 700427212 1250 700425962 700425967
    0x1e0a050c060a0b0a053307030905150328050109140a06060806040c17091f02040501021b0111010f0e01061d04061d010903020c0f180a1104091b030e07030305 69
    0xd0801c1c00510070307810f1070980040c0e0402c692101000c00c19200346c0b08140341d4280031a242c1c00309503211810a0050400319500e010903660140604118800642101e28070150016001007258007103806030035150151404201c0380d0795074070820024001041c2c101d980480e481000401800300340c40f659060b911070780c1d01d000b1155501030501005000059400c0248251100700030300c0391581072075146c8501e90b01000342102c00080640e807d66000e910940300d610754014481404142d0340024081c40031014112020810100c01c001600c5050400404040310350a0130000c4d6041581c5802980d074841c003020080007800e07600e20840e07920001038203100034807000304400305002c00c0040c0c11140c081c5516404d555196800d00c40d90a084440e400c800703d000da004545c0300ca9003440c20a91a10342e00ca000e56009010095071100c40708841d9008207541c24296031200d22002840c240415900030f13024482c1d040200e501980307690420906400350b11000a0700f4007647d150b2281002c113800e000c880d419243c0c0350 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 700428462 1250 700427212 700427219
    0xc0a0807060c080c0309060114040f15060f1e201501050108060d1e1a040c030219060e2b0c081e120702062a1002031b1e0a050c060a0b0a 60
    0x101c1d41c1417400c06c1c0e130300030f0325145181e00cbc0c0e4801744150180903000d40205104580360260251a0100c0015160705018404501d503404480640c1340c1c001c000040e01e041c0402e1408140c40807a841203d81c2038101611035080340c038000c01c1d0241c6056050f203909881d2406a139036940200141922244c000410305400030350005a811100030704150514490798245091920781403d00000c24002c540c166903483c0300b45010025418294100c00d03425160300e04a00c00241801c2000c2c20480711403160303a0190180c80170241e140724807401078091142e00131a64800350001800c0a600c01500d1307000380c1600303010b6101d001c03024022050100c402022920064291400081d0042d80c2c2c40e0031400003a44c12403010040115114041568440f0b290619410f0315966048a0859490a00c000b2500501c0300d01c1081070103182e120040f03c4002da031054108560f914131280d0302440c040c00540703010303800c00c0c08003240604049070032001406601e8a4281200c4180d43c1e10380d610b200792880070b80469000b104922050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 700429712 1250 700428462 700428479
    0xb06090904050c0d0c06030c03020403021804031110140a09050c1c060c050a0315061d03071203030504120e0d031103090307061d0a05150c0a0807060c080c03090601 72
    0x2680c1c854003a006803500c0c10f01560120f40f210f100f9001c00c44800c043c0c0e80052144940611512403180040c3c80e045051a08503400721329041c8554004100c101aa02c3c0024102340c1308810f074142d4245840e080d210100f0421441501a0000020090f90102000005480c00b0118031a00400b1a0004020400b0b13007072510521403c94158104010303d03902c00340f00d100114445000741820146244c1e40c455458a45a60040403030300303000d07840c15030410b45d81030401c070460b4000c50b440011454940b007481035200e0000080e1409071145e00c654000b03c001820a02070507050382c803040c030a43c000c02d102e66242c1700c82842101d030055010040b95101e005005002c0200e40304001855014402d1001c90b441e042103100000d02d01000381e070044000454014003020000d810309000581604103541e207a4007281000001068a41034000030008184045401002420104940941c0580100d405a0394402d1820014040d01e0705002140100e103c0c0d83c0840c03400401d800450f0304c12440080034091590808149c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 700430962 1250 700429712 700429729
    0x30324080601090c03050c030417070b01030507030309120506071412011409130305042102030609100f14040f02030109020612100e070522081e0115050604091e14060a0503010b0609 79
    0x1c0003030035030180b140000080333010a0f0301340a94000c1c4d00810010f071561800518245841d0040d1000c0d00c01c400c600c10001d04000340c420781044030703030801c45983d180381c101100c1d55004118520481042c0c400000904a49020564803000020f580c030407041c1e0744410b2500510103400c10007c0c0003e00800c401c000c400c0c030601942440340d4020304001403001c110303000079142c407000303031180d081c46c2c0c1004c0190380080c0443c0c031440c601c0e12244081070000c81d0001081c0300300c1200c024409000249440b140c102103503001e510041200d54010035444d124245482091014501103c3d07100064094610201d41803541d07004292140520f1780d0307050316011030f10604148000403018208032103806100c011400400038030903002821a414900019030305031140840c25120f80d1842c00100000341c000501081d1101c904031800c2c1d42078000042103103000000c0d0500d0840c2c590554041c41c610b060b400410243d1501e04150062700c0c12101e0003800d40d1034008143c00c035281601841d0340101d00700648401400d00e40b40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 700432212 1250 700430962 700430993
    0x1020d0516021512160f09030b06040e03040608070e030610140a090222050d020a0527070309020405100f15020a0f0309080f070602030304030324080601090c03050c0304 74
    0x483c0485818160140e582c0d504498903500c1c1c030b80d08803070400800f4500c003200c505040310a0310780001c245410101c00341c030f84401800301400c21f03505030f40040d00c19100da40092a406c040703801100d81e12a82e8160052024000360355031000904450018022480d001500178044e14049410085040c500364041c5c844102c40b81d8029048100044002074000b0288042c04d0501003000801644d00070301e01001041007080c0d040f09104240c001215009602d03200c0099058800c140d900c4550700d2a50169211010040310745e40186003030050800c401e00b60706420490040748250f50901c01130301e1f0b821086980d0050b0340605480c04160350001c100c0302211020245e030000c25401907401e4a0745039195014440900d5a042c1d000c00d1000070308109080e01080030008600b440b1002d0543c1034227100d4000c0d01d81c400500003804058a94007640805515024080d0240b5881c0345001401e130382d116411612840240f140702600c5143c009412050b60081c015103110f0550240c92034555038643d0781e00b0300003402010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 700433462 1250 700432212 700432219
    0x62a090d06060806191b05130e090c09070f02060c0f1c02070c05150f0921010f15180c050405062101060e06070f02010212070804080c01020d051602 65
    0x4000c030000c50880d10858000d8000039010b08100e01d0800883c4002040c2080fa000314603160064a641c4010038000c4a4894030440c545a5a650315108107920034039115000402c010f1484420300203200400100860f61030806c0e541a1503075039481009807130004140d1907150252b0032080000707084401040007888a000c1c407100690070aa110351080d15100e03050340703031400281da0002d201c0c03081c0b107001c100901c01442c08540802c3c50450050826510380a401401542c0660102e0b000d0712039550655448445400035038154040085800740501030a401c00c4181059482d0080144d0094468840070003901d1800c800d811818030050660002400103c0541d000c000080c440400c841c0c0e42d4000a150594440400300d812054000041c0403081c01070f07000344240f040c24810f036021a281c00007900c50366034015140a030001c01600060341051003a030394103000b00000140a50400141d4000b6000ba00c2c03487c0d00715216400f03020b0045e80c3d150390814541d80820014040820403001e03164508200e41d2015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 700434712 1250 700433462 700433479
    0x31507170709081603200a0905090c090405060403030b010906090501080901180f0b01050a050a030609050c060c10060b040e0f15040906050109140621280203062a09 72
    0x251101401c0c118400e060903a1007451080402c24404038140c040603c0080305c441b04d0380300c00aa00001d0320b40079548500720340c1c0c9842e0800102d41020512098080480113050542c1e070340b5103490115240c8401f141e04902007464090b000c0640c0d481252454181c80207a181d40d4003a5041030019161b050005042000c80e64a680e00a003920010303071800300416102d50b0006099802d1454a407240c6c90050304030718000d00c242441080541d550400040850f071b004000003c55407180d041c01414180e0903054250804000103050b07541900014000d50b5180060340200407683e15400c03003810500c9a032007401d03080302007603000c42c2c076681c03a0170080f0b600034a601605840c40a04c2e40c01050949010303403420756845075998010403c0c01c4060085583c1b0306501e044c800310350b03c0d01c640064000d940070a0201d102000c10417005810020070170000c00c41d59107842c07010401e0b89440e141c3c01075091003c14102d0007405000701054250520001c00750380700300c4090050b42d0840150b14201529000088001d90201c5c40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 700435962 1250 700434712 700434719
    0x7060c15180302060c09010c3008060406080f100c0c0b0103030504090b01030216080c030d020301121106070f020d02060f120f090d050301090b0d0510020306031507170709 75
    0x2907115190818049080409815256003070190400300010709460101404111607001c0d40e91004105402c90b500c8900c60840102c0139082e90341483c240b542c003804400240c0401a107054020406d54440c0030212018420745446440301510b43d0300d58003009466502c030b42e1000c0d030149480d42000034401030300c3c075200c0041042503d07110303420042a4016400300d900090b06101184450290900707120007802c080d49400003c2038120118940c01902608200011502c40e003130b0304e0284215040250300d85025522540c48840e40607a40e0810780d070446550f480c3d5000c01c2c020b4245101681c10b00703504568290030b55000c42d020320503010403540b8102d0b44110100a440341050112011b0800043c0a0103a0f16207480c02c1510b0090710b410240040c403441d070218050003a1941c0c0602100d05580c0307005000700301e00356920080340084040d8100284180610941c001c0040043d5010f940b254004a0458005c00318406403400c0303050082d5200000100300025100b902ea13164100a86c01401910b001e8a0b040c0d034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 700437212 1250 700435962 700436003
    0x20d0e1f230604091e0b0105010c050c0d06110d0b10030c05040e090a020d03020a1b05030a0303021b0f0610050904020603070c1119080c0a0f060f140f091c020307060c 73
    0x200b2000300700c40846460b440c402d006d0340c450350501404080c00c181e807003000e880d2651565004544120fa00c5220300c082c40800300206508108102c440b0340d65402c1d141e14100c007408028101041c5030034041d204141d00e440703081c0d1080c080c10b1400704154440c903142c06d08001080d024000300030f0081c25148030741845e150068032050101180d503402139020b0882c80303440740340c07034010701c5c1651284d0952030850700c109001036900416211115031341820016900d40c1c0c1c6482500354540210a00c1c1e070365000304c2c08020303a00400411510b02c120502c04440100680341c00803c1040d8400b03940207508182d0a00008004500442840036407030f00034914800c00840030000034061282408102d00300c514500b104011880b0b0400010709814070845040481900300303022122021300d94400c140030007201c0c0c40d100d0307520350094290500c071900c103505141d550080c00d83c1850f440d91000c0d1800e07003e0030780300c0300f21991450748a10343c80003944e006001e000c0c01d500d4844101c8101848404c15a18501aa028010700d000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 700438462 1250 700437212 700437233
    0x8100e16050705102304030e0613031b17010504050c0103020304060b04090c08010b0d12440702010c090506130f0906030240020d0e1f23060409 63
    0x8064002c0410b945d0543d10403045011a0303120301a1104d855030b400e020002e038025480540001c4103581180c0c0340d80e462503440c140f8291a60014141c00c40c4c1d0701401000401410442d000e640480401c0c42202036003200c40703030032618120747c098015001044110340d198402d400458215020b40c001013510306001000038100c0d04013060403100d0319003404041080003020300880301000e1040350082c0d40402203031500403010b01c0c1d20000c2404c00c90107024039001d2880c07201c2a0740c0303a0302a094610000e03490401c5668012401510110740c14004980020764440c8140100b100100d032958070004018542800c1c0240c03900107200829100070303100000b1a80580341c00300800148140307100440d02c0d51560061001040e69404000c885110317034001181c046e40000c4001500011400d0000c02c3e0305034004440c4000d02440800601007810120303041c906030070008075009030034402008200383d08070100003d41110400442820b07009401c6d0928000a61030085055021101400102d1001101e94032400a40d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 700439712 1250 700438462 700438483
    0x6081314010c0e0307270c030e030315010206180d0311040b0a020604022806110316030305040b060306150120060106080a141504020d0e0f0d08100e16050705 69
    0x1900700650070f210349010802c00340108180124091021000c403000c0e0102001c1445501c0b409440f60201902288282c0c0311001b8503d402c801e0321b499080c0b01e01b2480a41c40301b48807190040c4540408110903559442c100c2c05042c0e06000144103940000b40184d001d441d054890f00c100c004207102c0012003224250080208200e80c0e8050301ca60300d0144100504201100d50702c0019070404114010020720f100412416a00d05d410481310900482c6407c81c40c3d40f007030592201c0104c24601c091020150550081c50045101c2c000d1b005166a846040c95a5544201d500d80c500c840340c0c0108440a50050160341205150303a1041d05200c40480e1000d0318100007030303010500007540c040420008040605c261400440103450030300c1b19080500103000105484d80b54944601e030700140d003805150740382d808803450b92448400d840105904202e42c6450705403541d5910b0100d2009000603c2000d1811442c00070b5542d0114000c4480d110782d03030a02c070502038103000304051000c1003100388046402040445c008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 700440962 1250 700439712 700439717
    0x305060a02120a090c030b0912040e090c1009140d05012c0a0809130209090c0c3304032304030c0e0601200106030c080f0d0906081314010c 61
    0x15103036070306010540d03984000e1200c2c0c42c844c9480700380d000103807900c01803d08582e0090704551490711030380d00c000d0a02503081201000c1b400c0020f80002c2c042100c040451080341840709490380080d444052010580006214100050080c1414002d03080703011140183c01401414604928950355100c508543c880075a08040c0c036622410b03002c0400258050a8840e01410040c101e40840e540e1184003034001d41581c03601c038002500502c03070b113072146906981d142c42c002480c16105040c8464410b019502c4948449124080c031034510040c80110070002144c0c07107070101d02c698800700310540e00c010480d020b48100c08100c40b0921042c0261440b4402ca821800c03502032032036840b031541c5005085c1d6080c550100c00e10070284010041e480c2e07000281246004200800007440e260919007080c010100f540000b0054402c088001ca048500007906c9802c170074290045449184c02c154050310020751600c2004002441240041c1440c0c1a95010f030b0303504c0c2d00c690442c46480f410a0186801c0d0340c000c1942d00300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 700442212 1250 700440962 700440967
    0x50103020a0816030602090f100309023a020f0a03051f050c0d240605090f030106081b030313080c0a060f0c06020c030f030408040f0509011d060a0305060a02 69
    0x150300c0c10301d00c8000245240c00c000e0074010941d2210280100451001a2180b6404601d0512a4498144d0011800b90003004400c4e00f02105001800078030940c0c01c2130f8000c00300443c00c075010310034560703c602d95482c40030030803403e0a045004607100e130072b40d410b401c981006030a400c2500c60784075862044003441c85a00980a9002c1c142d44a413440e403e179020040e142c50500c030500129892030400c9038010120424045941c2c00081003c441c180b080b900400c1e00c0c3e5054407800150306a00c240980082c49085401603103911070b60082609803207043c018025107410491360f80c001081a03041241e011a030260540f4200b956640704580780c001a0b41c0010303401c0c0c02c0103120502c0b91408a0001002d442c1c1800c1c020600841c0d108001e0512180f400700600c0c555000401c5582070b03100700140c804500d01c40c503a481e0340e4a032901d007074012038005100b04540c213000e19202090f10b103031282ca4a410b0f1032041c03141d4210101038541d82004c00f0310262005800506000c00400401d8040c000140300d4030b156000540d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 700443462 1250 700442212 700442219
    0x718020d0f1d01141909050c030d030f0501050f035701020105220221070303120506030327030a110102160b0a050a051c0c031a15030a020f030a0501 65
    0x909480103510300c2101144140c08012400400c030401124540182800086e5100b1030300c0c00a10380f604a804965251213103901c0100c843d07905030000d0000d503846c0c0c407061100340d84e602d040c0504c609071801d03503d91540000703044d510b00b0032500f1091000c880700040c0c81d001100f41402640510060500c410900c6203144c482c0b410300701d0f0170314055810100207200800461070b018131390f1240048101d454a240241200f151b0b01035540b8140706840f01700b40f1101c02c2e2038244490380400c1d9a00c00c03910080300030039100565103c0a054a1280c180f042401802841c500a005801607001c078449429040b500111004210f03540e8408010013642a48181d8129024550443c00642703440180240100300c41c0b107103441440300050f030718107032a2f4429a41c101f054440581200a0301c1078003910944002c030402414031102141c906401100340c0c0f1316561020020341d000902c00107400c0c801d60852640020340001c0c4d12503d5401d01c001564000380b8201d00500309038195803250700c1a8000c0d2400044241c5560051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 700444712 1250 700443462 700443521
    0x610051c1e06090c14061c0b0d02060c160b13121a160306140f04090c0518010306060b030106020606010c062d05010609240c02120d030605030718020d0f 67
    0x1040340b21011154581020441110403103807a010100b90500729848010b24041032702d4580034040c07c60b40c000c004503110400700c0300c600d50f1420603036101c00c0302c02d0707103d0000141c91032140121f508035003600c01603600483c03c100401d8102691110704072101802d01c00102c0701d0400042005d809507911601081417202c007100014180c0d6826086040902d00d0803501805598403084c0740e82e84020107070390100f5894481d04014904078903a40c480c540001a00c0c1000e4681040029014140d034411541003184503124560042140002d016090250344048041540341d80915003c4003010700c10000400d003100c03e0001e40c8003002480f440e104000c2e101d4010340c504040c81d401030074003503c441c0ca4900551454200401780340c0280c0b194000c6911000940c0080192040c00603c804540140c81030000620700400d0076035901c0280c00001c002840d1050200d0286408240c51085409104c0b00c0e0200c9950070741080000e5000c80c0308140081c0e512081560102c1e031a02840e1102c00401c2502108842d031220340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 700445962 1250 700444712 700444739
    0x3070203090102070b190309080904180b0a090b040206130b0a020304080c040e060621011a0f010305011a0d1b02010204030b0709060801151b050610051c1e06090c 71
    0x1369214017410720081e0034142e040e0321041c410100d90314001c03d440d6000c1c2440c1b1610b114621480380c1107800c0c00d903640c009208411410142c0d84c030401247c5a682e84244000c0100c50303180100410050030540410090310784580a05a2041610048600d1640d0703003c400066174496013500015030004102004294000e02204821550a94080c0054a0000c00e00c40d01c4540040400d403191f00f070035040c003c0c84040b40031851070300302c03010000304403010b100816400d50084180141d48102082d82c05840554032034007581e1f040f20340c00060500c3d0280c1848100402d07070081090780d1042540c41006032240148076406884080864000680d65402c5050803c1502001040e1805000135540100503041c2d10480c02c07811556424120342c2045000700c0308a40c410001e003100030400440c2640e030b00a0000120342c450148008545202c0c05d2959142805640143d0303034130030020209403103020700120f1020801c8850001c4200b07288403600186e42d03140300403640300c990143c0740381100e0700040c400107400b50035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 700447212 1250 700445962 700445969
    0x80d210608061902070506060d260301090b030a050c040c0507051203040b01080304080309040c09030f060b100f05250b01030605090d1b020d0c050d11090708060a060e150307020309010207 82
    0x1c2036150082d5921b5255589501500c96805210406649014000700c828840304503001c109000f21181c4c803056107401c4a1300300f030142c0400d051070030f0701d911201d2400080288070f0303d40c0b02d0f000c5c184480502c01041700414000d0216424404200304400000d0410700c0060003034000040e001d5181d00b0075050034900c1c420140c10040d80350340200000c0c86003140010503918202801caa01040a84508000f226001c006500c010041c0b00740000000800086030000000c1703000982c1e0890803070038a10700440d942c0051101c48004a031003004183c048100c0c000d40419841444004120803180d503550344001c0c01c009030b106441035603480080c401c841d5030501001c25681c0103441d013030f03032810010180c500701080f9000c402840746014403180000c07c042c4007810002807400030107030101000da904110b030070400f00d41d007014450008900011070300360103030010038052a80605040002400c12a060b10728200e200c0e2080c0c0d20140c040b081205a4103054010340c49082541d01030b44e00d40708500300180c0340031810740 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 700448462 1250 700447212 700447261
    0xa0c0908070b03011e0302090c070807080d0504060f05060604050d02030a050319030f05041703041b06050a0306050a240306081002090f0a05280b1206090709080d21060806 75
    0x179000c202503a40d1018007a040b6000d10b21840e65a0ba840c80c141d240c42c810070100926103c00801c003011b00007201e921480c800c600a92040c000409070683c41001ca98040390b9035540000140420b00050a25a80000055101074100e40805a154030b40703e1950b00302c1c2d08549503004010490250480c1e16004081c0030794020340c001d03c058101607440184041803810009140d43c004000030b018030201c845e41110200500040041a82e00e8440040207540700300e00c4400070078181000002c1c01d051100741e14049807060f80305180f5001184041c4901d2490352407043c0205511000082041c2030b083c405501444a0003100507502e4040764184105c0c800d140c40104d00c9000402170400c040d85551400c004549a09000d581840e04802880c600d1904107400c040c503015001b2421202041c21f40d540c04d401814111000d20003640d550704200c03071440c00350046c240c00703410428460b4070380d9024090400c1149804c0e20045010600118410101c2d00541d0041000c1d03031010007805401c00340300c84185401c00420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 700449712 1250 700448462 700448519
    0x150409061d090c0103020703051308060604140f040210050d1401181a2404030813080a050307021c0b09010b0f040e280c0e0106020111120a0c0908070b0301 68
    0x50300c65180c006503003a244c181500090300c0c40c1003611810455007806440e0034214419621501c103195203150031110503000d141380c8152000d50914289190340303e4022030619900a5030346600340504104085d141c1d40500c0030501155015824030b0295100c001c468150826503507240c62600808c2844103c051a11249840380704050851496803c08500c0c40594591100380c00e2803500c003181c04920750581e00c8800e00820040208a81c54000340f041141148c22640c041e51038007422074880700300d0b0b44010f105a00c100411401030400f814440760886813224282500c1d003403911242c2c42083d0444215141c0c0e5960040034646182c1043d040c0d02103882542d00b00513160041403200c0d5a040c3c01d840d8030010301c080c12050610b6012000c0d40c41821030307000c4038206d04c0a84e1031810004203c4d082c040c040242d420301e002d04101007080400c0c1c441150154000710b8030750325410b0ba480024880203030308070108000c144010803908030400054000744958401300c4d03602d616101c1c00a103d541d00e00300c5c02d20b586210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 700450962 1250 700449712 700449721
    0x1020307061a151306080601080a0c030b06030109020721410a0201060b030f160e030706020705090c04080d0503150a170c03060709090b150409061d 65
    0x82940c0c8055806100002e220080541d03807078205000b01c4840f03901105454280c4001c3c1c0c4010050301c00307869260181090305440b10000d40302000112091800914440c001420030900794001003032481080c140007900c000502d000c0794080e44240c110a06054001864104200212500b0041d020020030360b8003501031024401440c4000e44090080301c84040d000c003811002901a07100c1c0409111320304da0a59101100100344035400035144c1c070300594070b800c90001d803d100b01c4040781e01c07482103202880150f9640301400514114540440c03000c100b070496020740d10f510100701c0c903c090607494008084442c43d041c20070845082c01807000c1540c0740140400c014146002444035101c40b41130500d80d407255a01114291041e5030041920751100341920000744003940c641100c9803030384152040c0d41d0070009400038995180415515103000407210074003040361011a6200721900302d001081d00c4060140300000e541c00b5007203904400140e0369031344003c102103402002c6029205640c0d00400010707292 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 700452212 1250 700450962 700450967
    0x2a19150f080106030b150a030501050306070f0806011b0b0405280f1403070f06050a050a020a08041209030209010e0906100b040b0307120e0a170705120d0e060c0c1005040201 76
    0x4043c0714000c2410f44032030540320075544606041c9010220f000c4030030740701c00b403199000740a81028810103009000344004600c0340b43c407035641144195015100d0241c0354492000450b001c40b8440050341c0e00e000c41c030182034005540d1140c00c0340214002c40040c95507502e071540810b02402c1c0b501c0c00c2c0c0d07544034505003104009110078600c0401503130002d80701003410204540340c0d4114412100f00400195000d0501d104000e6550303c401e00503580041d003004941d640705030300000c0348100030340311000c508104005400600700006000014030320b85481000140c3d2030340411525a000c0e008240b03a41003660030044001000c0100c154407140c45102000ea60786400c507051010301ca10b0003a8444240b00000240070180102c03800c041119504600304180c00310030079155140d0b4496401142d458161984102c1d0502c3d084003603e00c0a0303041400740c4076a0300d008501c9070b00d96005110a05644e901c8500744519a082800742600ca022440800317543c89502201aa0912810250031440c00c0c0c5014140000f50742e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 700453462 1250 700452212 700452227
    0xc1e1f0507050909070f03060f0311040504080d0f06050f031618090c090b090615090103020903190b04031803030e1c120c06050610022a19150f 63
    0x1010480000d498403284400c40e40380c455a48003d4010360102e050040b815800f4402c0507170405282c1d4200b2503a0744581403070107030020b070f0f101c09005000042003c0d2450b25044e0321564006101e9070506141c1280c0001d85000c2d2190340c0703000881c1d2075942c1c4042110341070078081e2212640f4105e02034810014000203030300c0c9c000c500f030103501000c004c1b400041150090a40c40101500e0f0041c01104e0402d40d100c40400140102814060084c0b56540c040b41c042d08000d11034803d0301a65030100c03800c280f081001180290803e110a07030340361003001d180e4046000700c0310401d05014025043c02641c0d142c0750401528a0684112103403810403440000c00100f9400364441c00480d80884585015103000ea001c100404041348024103030315030f002030844565401a0201411504c60f00013031205a440104101001010782510380150700b08841251151490158158400650481100d507900d011004078901040f40c00c004800900e8182c42440b1030203200d4058270030580986000402040002401400074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 700454712 1250 700453462 700453513
    0x9052e032103090c0b0307200c010309060207201206040803060d0f0203010e0609160308030103112b020108060f0a060807140c0726060c0f0903030c1e 66
    0xa824600300201c000d0711a030400b45449810440004140d5118503a40c2a1a41705984281c08a0380a40300c80741001d1480c0001501010351002910300360803000015005018030703c0e001c4071041c0e401c0104100054084031820540030241c2d0f0300f03000e0987c2403028060084050b1000380c105074840410403001544601c112035110009031042d600010303551074081300000445400941c15420018100d107454030000760035201c1c001140444211000c0030300d220102031004d02006c1c1c0151810001403000c034090441044540384050013003040e905045441230880c820444131514004108003845041d581d010721240d0f0800c1b4210b65406681d003009001940700c0c0080e05c01c0c0c20a000c16100001c5116002d1a03403118940d07107010b42299a12555400c940d03c94205020311a0008002103000c0030b000c940c09400c5c07000702c007081c00030040303a11040031103242504040d00079002e2442c104400381c840e032030a00c0603200741c01840000b8084000065007035842c0101c6040f804c2c10300d074040f420040f0f100540d10000142d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 700455962 1250 700454712 700454753
    0x20f06031513180b07030b01050403030903110102070b0a030e16080d0e150a0c1505040302060106081f151710030f06060906060f0f02060709031b09052e03 68
    0x80d00c074074116000107031a800d5a40700e40328074180340042c10f202c1301040c07292241e140c5a4003084040900001901e090295010103000196014800d000140030404102c0d110b000500440340840d03034810202038154006020913000907251202c2c2c1c44070721010407050740003110894080c0040c03030a040001d47d51324a100600020003160143e003945540341c0304100207107074416100180d034482e00382102900440301d58804503544100102580328083c0c16101303c1d401264150b02400160346010012540c2e140040c04000319001083c068409c0407418415080040a81480340c1000d60320505018252410165105014080d000104418010410411010340760b2108000514031038070b04100d03000300f602e504103882c06850b003c1c001c119550407040018400323000e41da68407103c080e03150040340c82d68015605503000c200c00c3c8000748001100016521401c5003a00001c4c04070580e9071a030326080e0f40f0b0646151442d010304402401c15000100c030840c1c00c04880b41d640c1070026255070359000206503001c511940 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 700457212 1250 700455962 700455979
    0x15030c050d050a1523090c09120c190e07030c02211c060503190b0c0a030905060109020406110303060904020d080d090b06010e010807090314100905010603020f060315 73
    0x740481503100b510013100c20b0516108680d1104180003080302c140c1c13003101500784244425a03051400003940e92040d00d86021044c20124200244040005000d03009200f500901c1010001511440407003158070050340840707101c2e07514000e182400c00c2b02c0038007040d041504018040a5060700001e850500d56805160341100f4181a4005902802100441c03031440742600020000b0b100b80b078100c0c10a80b1000c8080c0c54507886801299809610900001070265100000103110300c045c0202400c240a190b0a0204145a182e50358504004c0242c0002141c0d41d40031238184502588842c0e0012a004900000c46c91403c0000008080ea400100024419242c100c041c50800ca404030940d11680c0d039a20f4213002c0d40160785001e00003000c0484600b03000034412500210650302c140d50440c06044030703440d2100100e06685441100d180381c9031250b515407180b0204104081c0d428411200018021400060308906500c10800f030885031003a110312030b40007401805060743e04c13109080520501100c40c01c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 700458462 1250 700457212 700457221
    0x81b1215011406280311070b06040f0207060c020a03080109060806060d050a0b09102018061308160b09031c02151504060509160509031c02030415030c050d05 69
    0x1041c600c2549842004c003040c07a0803804440c5464100301c0c406040988042c089480e4243e0f007000c2c0c41c00f810710050070128414002c034a460070302c0e5010540d14810741c0c0d00503207000c042d0b4584000b940c19165075880142e00810b05c29060550141045d03000d040321003001d0190a25216a00340c3c1c03408050602481800249031040800c0400c10a0404003680a1555111450a03420864696008800500c5038504003041400d00f4491620000220f0000c20145420101c90040c081e40c801c056031901a001102003003201d51400c0c3c4981080010704a030320040042d483c0200d2000c6c0030030f5003030b84440d04518050000341c40c0381d1b40100341182c440001521004203a0491f1200300c4c0760403a00c50140b040b600d400424002480c030044a030300385034a000d4a003030049030741d10300a0052241088421703000401820b80cbe804031142c4643c00400ca4188000d0403503603c400c652200302003884c3c0e07541e0300c2c501580c0002001c2041781c0c0404505a400045410b0421008410600103410b62140c0112004016034540004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 700459712 1250 700458462 700458469
    0x60201020c03040528030b090f03040609030b190f020702040e0a02030618031e03041a0603061f0902030a020c061e07031e0501060306230f0613081b12150114 69
    0x22014185c0000010300c03603540d0b0303080055401e20141c80303100c3c0740d0082403014682e50400000711270440340340d40e5804d4043d910315111200c401a0140001ea05171900024030803900a99000d00c45826181200041e690500380c4100000c94403144401103054120b40740754002350390b000c078400364170904a441c128044018070010606500c00d202244040050a06120390000019006188240d02c00c08404460400c0355015884580003120f6180e41607016200080d003060511a2740d22400c1c0461491401658403158580c090703030400c0340c00104850303000c03c240018110400202c2e8200c10395440c42c001d030302c000c02001e101039880140500181070b280c00d01c81c2402c000b04041c495548108400411240d40c4400c03004024081a1082520004503062207040507100c0c61040c4600700001089400030322010b4040c4141c43d040b1003a5100f10014040c2c001035030b084c00303000c40c0b030580804d03080d0030751020050820044010510b0000d81465402001504240710800484078159407280e0741518541c070705c1d00e000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 700460962 1250 700459712 700459759
    0x12090503031302192303030c2505090108061509040b010e04080702030a03081816031b05100801030c150e011d060f04180207150c090b160b01060201020c030405 70
    0x26070851002c1302c1c0d400143c44810081c650020140190401440c1c070107041019520301421001c144180c014005042c00c940d2214074000d2a21959101b0080d050340d100c00003908600240c0c401c43c0140c00030820031101100f40c007041c814100013100e5020843c203082c0c440300d8091070705004d180100301d1b400340400c05201800301680d48041d4000c0407501016403c0c50700030038649041e1080d41c043c91408a1041c3d48100100d2a5588420108180c01001e0b01e0340c0c0b9a0703120554000c0054040c9500514041583d4444ca646a240c8180c0b41c0c07030308162035246184c003001c0031803294010ad54034480d450a0303800b00da500000483e2004000d01c2c203107440202d0343c1012115401480d2100742e01200c000f8a84d0201e1302030b28081c1080352111030651b0441004003c142050303105440e402401114210326002d00031a860303000c00b14000d950310344400010f45800b070b0080c0310343c00301c00801c601d4500020720303500300701d1004101800340003141300035420a00100103080c0e403401240545803285151680001c4040b12040ea03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 700462212 1250 700460962 700460989
    0xf34120603050d1409030c0607060e030307110c030a030f031a0a14120609060402210709270206030a02070609060f1401060c080a080603101b12090503031302 69
    0x100304080d41e07803034074507640c0410b6485400498a14407408030960002000d0395031914016014000428450007000b91962007190103d52440e03458062290711102000558841c490f0340d111802c0d5002401c4d05079142403040141207219030b026513000c0c40017070b6100704e00c004010700034240802e000000c695000c00703110910b00c425030400fa840c5400644031764009202d45075418191900402c840c2c80030006a201d00d01180c01c00410ba01c80c002007001810076400312013a590805844000e610340c5610b9103410708441e64080e8007642d480e041ca03607020040405916614815440e600c0e124034070654041811f9000c000c10380040c0c03990104050040c4005900a035800c41d07400f41d000c2000d030035040110f00042c1210700c2c454079010364a400100d182d6016121240805801c11001d50904903040c000300e90f40e210084c9003d4141c06400ba62078004c1d0b84a000e406060b01c1e940c03210030401504800014120480e15181100c42405c05210402041010003126080038417400c0e4958038403414000700351744152a45 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 700463462 1250 700462212 700462247
    0x131502030c0d0c05030109150f140a03060c0206011a120612070b0708180d0308040213060810090b0703060b1c020f070501020403060c0c1a0403110f060f34 68
    0x40d0f4000d4025805001581030311b00c030220401c100b040c02d44a0000a140c280170304d05950245540030320203070000f4036401c480c406009004641c080e89960300c400545100181c0440582d000800512030041107141c0c207011202c1d1440101e0401504003510007a0503000f40481e8007c01d02a00c04c0c0c100c482d000e0290740060400d12106030343d0354010b45802c45490340f10100c01c1c10320003401e68020120b0701c0d0a006240141e5010340d100c1c0b140391115020843ca400c01502881c16255540000044a04090102e2440403150410001d20816a0305000784e034004000c0007502014500038040c401400d080081d60240e2402c3c0424903081e005803001032001f48140c008030240076a01140e0f00d010080150018001d50748a0b0900340040300c42660141c5803c88040300050006c01402e803801d08001c180b900007a07026000389011000e00007010445803e0400000355907560b5000601000070203009540000e07040a00c0a882c007c9103005501d503001071110614403018103119143c0f1030014244603603000c04500c030421 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 700464712 1250 700463462 700463471
    0x2040b0a020609010e0f06070509030c09042906010c0b15120f070905100b1606020d020a020c150f0c01020c1207060c08010f050f010233131502030c0d 66
    0x190040d40e100c030210f83c070856035820030b0103600400c3e20100320152a039026070b0003000b0300c0e00c940750251095001104000c1c0c0502c22500c9a001940e2200b0480b030040c1d015208454141c0a00d56211060300d1210752482035401400d000d200c44c591340700d405e00c642250890300c1d54800d500e501440d800110402c12140c0d501c4112080302d50302c46100464010011245c6004546a9076a142280002e0312002c88030b080002c3c014090070880345400308020080c26500171482d20340001140c0d101022a08107403201840154041014048103404001080c14603008440701c1c0d095090000000078140318405654000402c0854a400404825019514901c102074151070101e200c403214420503810540065940318101f031410040c0b90300503087c00e410f0301c039000d0701c81c90b01741d04100130b20a0b0200c0700b00b40581140f007070981441201b141c0c2d80e05112081c035240d0007103201280403030f00159488000b0701510780030010380d060710000030211101d89a0b000300195015840782d0750703001442c09500400301180e00c2503080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 700465962 1250 700464712 700464727
    0x304052209050c09010f080705010c02040b041e0b01030605030c04090c0e01060305150f1014070c0e01050109060f0e04050606070f0c060810060e0d02150a03051e07170a02040b 77
    0x3040c010f0b0801c1d0705455842060b80d82c1d21403c2c091040b07910400c200c0360070980c002c0c02254402c001e034590329400039001180e83c1c902140070800306d54a08040c1812400800d6810007850214041d4041e00402440c0c240300440c10000000d0f1a11400705103030f441180c1e210b6032107003040703000c22000e8010000319011541541e9541d1015001c1d00d021980c000c0c40c41315440c0300c44010301c1d003040c0200241e68040c10320b2414949804003a150481c240019940c80c0c03000b4071245001841940780b0b00064400e0318141041549000005080c03404107400c0001404403030503003010940d62020040f0141741c012140424251034810100d82c0b5485100005003804d400403100005001030903080208a959955400714160390f174034841003845186028400001d030b8907400200c090724003021204d400c0750000f0140000c1200c45c0e01002825032240d800da07800b00f504c540c02c104290407035200c1a02d1050910124009078904542c00070024110154580200d011a5000c2151300e0840e9040d1005000103c904030b955400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 700467212 1250 700465962 700465973
    0x5090f0a0b0402040b0405150112021606021b010504030c061e090614160906080a0605041b0f18051c12030e0c1906080c070c0605030411120304052209 66
    0x2110300f03a0165007002c07140c0c82a42403d116584c0b140d20810b01310600100d005004480c81c640c5200011420313a020301100d40d60740f200005600445103d100010781c0c0315413001a40615130031108103844503901d4141040042a00b00c1e502e070b0300c9507922400005603e000b5030700380030705104c540300203210b0b4900d445980020843c03030b40c0c40700d07949070000c0383e40880315501d00a184c103102800b98000800564545010010180504045500030b805080301141d803a8031080424221460f0200460142410072030f60582c0035005000c2c4400c140031880c04c540c2c00c001004c00038903400903520406019030030480301c030120301d4000d405076081e0541c010b03034080c241004034038010b014004548d05804c00740101030410b2041d18041c03103880b0700b08e4015a04005054580789090303c5281c7c000304031a11054003003200c200060000e0240d1006050036480d8207441e400e050401d200100001f80b003c6000300d0394400012030b03060001041c0c0d800c81c2c0c1c088800c1c0390b800c507180c0e84e021061901181a411210f0804c80d82c00c00700b20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 700468462 1250 700467212 700467233
    0x50a030e060709330e12030a0c031202090d08160b040602090427030f051603090e0106050a02060a021803071409090601031a0402010522080118051005090f0a 69
    0x440c4d6202d402031680003480d1308a24407084d1114107000c540c0a0204030312083c054441c440c422400140380034082800c651036281164003103580f8000107500385480c80308154221905c403054041c10b0b4400c60a003645000401c0022110003005024100d0118400c01320b508a450241e55084d8040c0c3c0d021028109450960040d42000390154441e5003007100c064405142c01803806001c0c0440ca40001c085c401c1c0e5107081e1059400c140c0b00d0410400100000d5451603060142030703040a00c203982d42000c1c3c40c6052103501c0a502c040c0c00050401c02c08104240b046540001d903da0444c2040000590f00c40c2e1003541e0301c480c034581a03404c0381c16005144002456a412a440500e000000d941081c21a030700c8a0000703844a0007400014500c0e0700c1040c848590303445400c06154010f1041c100741d4030f011030040c888410402c980c02041200b1402003002c0c001e00310b0a0041c0c200c80325501c1c42e240100d210565030652100c4181055038001e507564000a81c000c0c80400c5000c1845800c42d0903034a451540707041412145 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 700469712 1250 700468462 700468469
    0xf01060f390b0714040b0a02030919090c050f1c0618090b070c080d020d110301030b1008030c0d0810090204080610050d24060519090f0606050703050a030e060709 71
    0x1803842d01d0000d0300c2c490091381e0410710700a4640e01c3d1458a428014102c1c0c25421864002d17045110900c401a440e88580c0e1005103004880d1215001803132a0008079403e42c3e8030301c0745950402c2014001000c80d041c519094500490400030b504000c41340c050150700040c0081d512509002200e400d01c420010441c0e4450310745039024008005143d03443e801d0580d102180e54000504e812420070414000000c213502504549042c0200850111002c2d1101e03d0b1035002a002174401c003491605000413500303480600340c010286203000d54101a804d88050ba00d90004000714000d101d180380000300c2e02100c050b0b0620191121100854a660b1950300341030f03840030221540c42c003c58070740c2c00c04542840c05541d50040160300050301052000521021016007a0440710a043c590700c80d08081620740c0c0720b031030017011204008101901145040840c2080c0d46102c8440305440e4034104082c003425510004031803d158050404983c2c440311050220020400028100c1e0309000e1202440045079008404000302c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 700470962 1250 700469712 700469723
    0x120313050f06130b071704080918060127051201020a11030f0315120a03030f0b0f0a1a04090609021902030c100b0310050408070b0f01060f39 62
    0x48801400c01591110151040140c01c0584140705000a903004c0c000c5500c188a840c1103405520501c001440401d42518105c4240c1c0020031a5001c90030700c0c4604094050110800b02d0342400c2c2407002034a040b0b04034011501226074141c00c810b028416040080060034007a0175007030459170b05040e01c3c0c000d402c203003131200009038240501c0701e0042000080c1c448c0303e50282001c40c40e507150750221001d000c0500100c2500031849411540c40c100b4140001c1030380c580a514080303015102410213000700c80d40a418103110b0b01550010a040b40c40b04440101a109140c020320f0b81d400d075018004515011703a501c0207800504200e002300e60303201503070081c04560088400c08208040701e910103030303124045c01c1001c000c164420380300d4904811941c1c020640600000d0191a034883c0c601a558003079400c1218107544942001451100b001901014141d201d4000b14080c580c40d410010010511041c103000703c0c0c10048440190540f5100b41e44c0b0540e030300c002ca00382200700c407605904912403280c1c100405445 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 700472212 1250 700470962 700470973
    0x706060509010810020a090305010e0106031b080601121e03020c0f01210b19080304050f0a05030d0c03092114010507141e03040f06050919020d0512031305 68
    0xe403400d0000d04141a560703d000501081d241201040d8000c1d002001e2050801030350a0000010880c284200140d09600b02c002086980c19428400803030f5a00403e60140e01ca1150020010f10f05d01090300ea05481c00750304005040e01883c00c2101204050141c42d0b5526500e0601410816400140000001c482070f42e0740541501401c0054a01d401404030840d80791241c0e0362103404a02c0554803105a100380240180c180e04200243e00c0b40303038a100d8104100b20b0f0300002d410300091401c4003000b00510402c4039a50216400c0002017030f00c60001c80c1c0302405008120380032500b0507019800000141034003202c0b00480c40c2a1503400c0c078400e14000c0060721b81140803040d05d1803681040c01080c1c410101a104ea0030840021302640315680c0c046001851201070791040c100b21314a0041c011030045000303006840c0c0c1501603050610484001030000f0f015a03102000e152030020b0300e2050104029011105a0041c840074101142032100c03040c180080301200000704010f8440e03c1c000820031074046d0302144d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 700473462 1250 700472212 700472219
    0x303110105040c030b100e181c0507030f0c08030f010e0f07080c09211e0109050a0204050c09030a1401200d02030c0d05040c1a1204080d02120903070606 67
    0xd0807503400341c40c06020801c21a4080c4007040c0901d01c0703190001221805448150740c0d400d43c2d82103d10041d0b440c50400029802e00800050040151018610100c1044502d50550500107005880344440c01006d021507480300000391401442031000309600540c03030694030300e0403070074920081100b4042d205200c007050011825550711018198881e0700e207501c54942d41e4855a010300c0c015000a0011075001001c40c100c0c03810000c402403003140c03407000786005001080710100035421040c3d4071043c03000141c4c544070025010a800040c00c04125805540019858036003601c0c40f842403061070640c54051046240110070004243d940e035003000c9007034008000e100c4600c43d000c00c0140e08041c031406e40c01000d100d0144e03616069802140c1200d1401c85003460494150841015900c007240c0545006050981c10001034603071200148000c1d00a042c2c4030701d00b11080100c8410748a0140c005818640c01052058241c11035a0458400207510224000c482c0f07031003000c0304e0f0b42c1d50140800b100d08074140300000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 700474712 1250 700473462 700473497
    0x1f0f1215090c05040e0111130509070215060405190e0c040e1902040b24030103051c0c0303152714040b040618080c03030f100609051201091403040303 66
    0x1101c500c1d41c819040075507140f802d01004054980d603240c3c3ca550b55a80d1020700e1485007a0001000b040030b69804600b82c0c98581410008101c070004d040d001036406c20110256100c90b604002075014000300d400103020f4075081008640505094080e601c00c3e441c10380d402c00c107801e0025240d01c440c00203c50520144003640c10b41512008000c40c0c1558000b0481d1030140145420340042c0d0740b840010b42408004270141e1301e42c14040c144203002c01038070013002005205100303041c0305204000018007914085200e030b2a01c018400d18a400d0044c08140c0e8805241928407501c000d400e0042404109140b9002e4500d00501005c55548001214a61401d00915052003a03071007a14842d0340c110010442c02d80d104c2c0c9506003c2d00311941d007c1c1d0030903020108100040d42c00b01c0948007155610008585904e01200e84444001000c2d00441c01804200b000308900c0f9840340451040c1c50040e60088241103515a941e40980507486000303148500301d0308411903002000000d4422240240c0d6652549800708203107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 700475962 1250 700474712 700474721
    0xf250609031e1b021c480b090a03050f07090b0f0a03201e0906030105010302030d030c05090307031202060a05010f1719030306051014031f0f1215 64
    0x190002083d40302d1420003503d8140c0c41698400807292501c0038031851962400d405462444481201d4200180080c00030b551000e10180d0300a1100c0301034520858041468800c41c4042c407440c02200307030000344481152500650000115400000c070340703c1d00556074010340c40304001d004806500e4540200124640f5249260301c0540b40064000701e102c50840d11070850012400d604000e2a014548101185465004080881c402c0104414003088400b4040040aa2000e00420312030782c18000140090303980400e20542202c1141000158003071b82010540e041d0250440f810f5041c00340d03100000c00d0007451052200e2041e003e9081c0c40850390f941c41103c0448800780113000612803080c07800d00c185a10361050f09200b029000442c0d901c8606050442079910704402c080f00000e8840c1c0c001c0046090441003840120f00030700b8041c2030002405204001800000e00301ca04401290003010003064400c14050040d044051200c07203029192000c0012108058108640d055220603030445104032070b104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 700477212 1250 700475962 700475987
    0x11502011103070503060109030c0312080603010504170a0908010e0303010f0e010602030d0c05040e0a060e090102040605090d0c05150310050d031d01050409021c0605060f250609031e 80
    0x74001e00315110480c08503082c0e0030003080703281400f20306d03000840451510754828004511641e031032000c010600000178400700000d04042c0c00b83e0b040c10700380b01c00210b0a00c404020442180b000ca81c881c45031620403240d14183c0d61203a443c80d482d02000450313050000c801941614031034a0701020250f9a02c2c100c1000c3c3c2d000348039510041e001031000725100b06d407030b0300910348580789842c2450034192580c0021094034402c0c0c5054184641e034580c100800c9103a086030350b42c440c6550008508083c600003001d0001c0c420140c03802d00c01c850403209081002040211680604009088507003902c0862142e18526401600e5031030421a00e40000202e6103800c200c0c01d604a941076a4111440c2c41003407000c041c16030851401ea041c0074041c00040750406c10f51001e8030451443d008594881445481c12000302c5040d608024014017040000144181540b000c03229100c00342c4100d941d0080031640d40a500024050004180c4c0b401e08603107609155100802c8644c40ca0641c002501c085158501902d502c6428031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 700478462 1250 700477212 700477241
    0x1140f01140d0906050c03160201051303030519020f03150f012f0f011d012a030b04140402090907080d051813060305120711090a14070801150201 64
    0xa001c1d40c908281c00182881e018400000300e88031420f03590340d1041c0e460480d9203503000761000c81084800e0480040070119054075000800003070030852000680031000702809010f1544403c04156111000d4041015a0307683c140d0445d10758180d080328200d01d600a4600311b80c540d00402c00d51142e4070340b01d030202042c000141c444207001a100c0d90310b10f001d005201d1005d00383c0006400107a450321030503c036440f249942d220000905206203541c00c0340e545850244001c2681c5010404002d0700d188400c034844804041c2600f034940c81030154100c02820400c0342068002d410b040c00398010494500c28140594421107417801c0b541d0b1031800040d941c40280c4203c100c19448094042041c90050b4018004000c203400c1810030240598040750203594009031062100d55120402c0051010a10200500861100d81c0d24549072068441000410820000b00d205824000218009103480d0340403041040c3c5a22240581d89003e01c0040d0004400344501c036401600308168182451042c81030002068081c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 700479712 1250 700478462 700478477
    0xb090105030105151e04150e09061c0c1805070201020c0a120c020a0f0905010b0301080d0e01091206201213020d05030d1b09051810051801140f01 64
    0x4040207200300c00c58108030001001001114060812080ca400507080240f10856440d803070280300c0b1641451180a01042140b960230720f5000c3d03039600c40e106400a00c100ea20761a0040074440e400006000044010201a062000000c1301003a00582c50394040f41074404118950b1140816400e0b07108181a154050300715aa07100c1c002000a010000c0d03003041441c1519a4a103d60f01051400e8041e07004102c0fa41c49145081105d03408034000c40b400b400800d40c460341035500d0b0038074144d95410011005404d00004d2400c0c0314482c0d200f0100c0d6802001d00142032050040c69081040c01050b8591100f2000e884100d6030391002c003c01021502c400a80451148543c0d07a54440b10750010b040e2a001c80e8009040320260001c200d041010b449650343c0040002000f880161088514030000000101444149042040590703200a00d08483d04a030824415031559030307100e1040f40310080e821266011440c000181882c0c00e1054206060340c8045282402c50b00ca10b03000c101100f988225840c0c00035185 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 700480962 1250 700479712 700479719
    0x22101060501390516030605090601091803111009060902010f021218030f033006090c030a0b0415050102011505030a030507030c02030a0b06090601112e06060e0a0b0901050301 77
    0x290301e042d40280d800381301510620390321203400140c03d1000c1e5005546980c0c035402803202410052041c14014268007000304032800c2082d140710541d125103a005014069481c0300c03410b0421051040391180000c00000304800f40c5135281602c0104411802640094107802d0404101d42c0000707082480c1d60840030140381080c081c061a40042840c001c500c68043c01002e030b9900380040100098417161141102a0100c124840d00002d103184441d001c0c8000c6040c0f0900b8002c940d01c80300941904034104524131b0781d0320390703801854802410300400d100c1d4029281800828070004100240802d461090b8028071400343e1011074010800d842c3e0084a5142c0c000d4400400000d00501c0141301d0326105c2d0900c09904651600000e06000300791000303070340710320041c401c0050074600650002e51014003401d0101c41c3d0196400081e81d0b030180041c049060704040c0700d03800e850f11196103000709500d030251818481c00d40c44000041c944925072440f00e00a4001e40404102d02924406544100e28103a580d5401e583c40e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 700482212 1250 700480962 700481057
    0x28031d060409020a1407030305061503070c062703180512100b01021005040b070f180306180c15080c040308030c1b100509190506040f022101060501 65
    0x5580017800f03514503515005413100000b0b041c113140284c40c000b500c0d282c02c03014070615002007406140801c004201304540560051107100e0804c0c1c2040d0000381c001d54081e84c194a0b951114903001d800e003480c01454007090341c070040341864603400c0217110401540c1c890601c0400c03c080d50020029402107c0d10080001c8541c0c0104480801441191401d0264013810011038100340c4080e20110064810048480d0b00005401792b002818981681a45200a041480c1c0686c44c00000e0a054171010801d4a600c89035403182c450981102c07800311116901d9a9084c502c0040c01210004685501b001400c0750743c2c654103480481b9000b2101900d10342d10042d5a0b04581e00c05003e40400784094174004001e06420000e110010000e445c0c00540b070f0800ca9070b528680a5289540040041050303080800184089821a0842d60040c0700310880b170b54900c00500b0141292070380300c0f140603108590744540c0005400c0781c41111402c0e00d96941010040900a2464100749a60b0001c140341184040340c105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 700483462 1250 700482212 700482217
    0x80103060f0204121217071e0905100c051204180b0415080a110f0f06090609060c0d1b0c1205010b15070209010b091c0528031d06040902 60
    0x1c45080c0c0146841c4d21600a8054010500d605507080d83c450031240d000c80e0707002024510342400785c6011415502e801711005103800c046010484880e0002d00c1c50103030071800307605c00d50b003d080000c0c060440c0c2e0300040001003030303002807580c1a130341031090041c440410803c0004407001d17180101094a140b081d8450914050300c20f007002150400c1e0740d136000c400340c50361007109480030f06100c101174046a0400d0a0203c665526040d5107803052504100356031550f40d800d81000d514030310564503240c458684900007a064020854030f40d81283d40000c02d540101004100070aa0380095260003a103003081b00100d6000258220b8010112002248280010340e80070f41072041e102d100c1d500200e9208080300110303100ca41c00740c10845080202150071001c501e80381c003100307000d0303c24820000d0501d00c10200041a8000b21540103400b50148800700080c4101489403150138280000200001107888038031001060103a9811f0740004c409124480541c0b1010202101c9a01c2c020122400c01d8100f100010095 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 700484712 1250 700483462 700483481
    0xc0721080a0c022d03061614040306050a09050712050c01030509100c0e0307090b06090609010908060403080a0f09050604020906030a0b0c0a110a0c0e040f05030d050907050103060608010306 83
    0x580c41c2c502c0041e80d9038021030140c00c0d065a156100c05001c00410051202d004401034071030b8019404028109411103a400a807000c149084007803540e517402d000066200b10742001e00382e54141000c100c0c4e030b68129000025024490000c45d200c076543c444083c180442d640c00700410681140c21203080c10742c465007181c0c0e007044c3e44030180c0340f03400d952820107011510301500a10110301802c20341012817409201c150002c1c0042030303007404503c0468000400b036100d4074010038401c900225040445900c00c40408028081c0f20045640a080c141805451384104403202c40000342448011100d6008600030300c040d40c0c2e0f10034000e01494860b5420048104c400400720342d0541b0a11203100041446811603601a81c042c55080359134149080d0b00810303850310520150155400700ea02c070400228001c0c504402c54100c1a0300038181e0b07c81d072400180b10509054060305520020600c00b5480065a1200b40076030380003c225051705075104010760607104a0b105000105005030010004a90640c0180d41745 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 700485962 1250 700484712 700484717
    0x10f0e0a0204150309050f16170f0304031a0135281104110d090c05090108010c08010e06130b060d150f08061006050901230c0721080a 59
    0x2455101d400c03e2551006000c25680000c0e25050711106100c1d050280c2010056400007402680b003510101c020000c0036846034048180e46580c1c0804202c4040c0b0901c402e40300103105881d961079276420b04054503181510510505a0000c1c0000b59400c20203160802c074402c002c002c1e4580c0c0515010f140b94000310034101d10704e54001c000c031001c244034004890720244c450700d4005400001e080d00742011198034582009014a113000c403001d20b0300b58481d090721603803a802100440e882469140c0700c0403000b0103500c803070303004075251002248000341904400b1219946544401d500d81c1c3e00d20207000d03810340030f840c40d41d001460102081c54561103038100010041024148074036040c0001c141208a801c080814880e0700d105032814052500042c9881000b0500b220080c00282087e00b0441801e1903e07100300c0c03041c030100060322403950340180007800c0c0e50340d244118500701a184c0300c0350030083c1e48080341c440002c1c003c01901044030759908a0b118840c42110300c44400126451382c650b00741d82d210440c41c1c400d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 700487212 1250 700485962 700485967
    0x109061b02130c021005040c03021012050115020d0311190302040509130b0a0b0102060f1825050103021207030e070f0b07060b1f140f0304050102070c0608010f0e0a02 73
    0x5600e540058581014000070001100c1c0403c440c000c0c10071009005015005d405c003414040400c00b11104007046c1d0380c0444040c44000c003046024ad900e448103000909080781000c00014503a07003030314449000700c070700c0d9004c3e12b1034608410300031006c6800404142d80460801e01011314410131020700618109002c0c10011315050f26400060009107080724050034030100900d102c802c1004141c2082d0b0001c0003210b007230043c0c2c040600081d4403082d004008520b4110302000083c1a8018030400074401e1843e0701c1515071000c0d40030b903042c82480070300300030b0140e40003004c0c00010303294031034421151010600340600001d91100c0758110060498407551914520609002152410303030419910010400112015aa002c5500d4070038186c44a000790300d4824024022010b05094403e054420748900c01d01d82001841c41c0c1c06041860360007200369000c01c90300044100300403c0415802048458001c203031701150103960307600840d17604c00d0900410031071141c40c000400c02e440c48114601d1700480002d00160 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 700488462 1250 700487212 700487267
    0xc0608100b040305030301090b06120a09080702040e0a02010f210207020f1e04060902070201021c030219050417010b1f050f0703120b0603061c0203070b0301030c090f050105010906 79
    0x40c42e8105400030307281500000b004010550f200c3c810b1010441c0203464103402c110809070f03511100f0b2001800401902d80343c80441d01040801c0f81214090350b030051041007542c01450415a40b80503004003203003c107600e1804000d0017805140a0002e401d281c01a01080d1130207d550800a508a82e008907088012844880d0095440952040004100305200400030441c1e604000660300d69501c1005518810400d810150f40d001c62031104940d1100042800a03030f4a2804030001c1c0310380da018000402c0c58059220040b64000c000f00b0071184c1203044d60710601c1c00c00c40628200c94105240e19409410744071198072a00320368800103083e01c130a0501508041c3c01d19043d140030781c80008200d001446800c3c2000307882003103100e8098a103405481d990309516141c00451081c030aa060000c0034408101446811076508000070300180c80502c0c100fa403207503524030740344a6001c441d02501000301c4c10400c10210b400f0481c41082e0403948142d5480910900d080000d4640611120027540c5007400c46450b00d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 700489712 1250 700488462 700488479
    0x14030c01031d01240617060603040f0b07020a02041505090f0406060b040608090f0f0309010c0c15200111120403052b0c0219080c030c0a0c0e090a0c060810 68
    0x2c0444240d042103c0203210381150840c0038004c05800580901c9500000e041141c401d9007500e03a44000305486150b603a80381c1d4100f0071810008604010070703a001c4001080009540414041d206030301c00d50f0148281c040c49a1081e8082a1901409800000311000501c001400d04080e44d0000d00803440080c01d81d454000c1c8c069140e1003600010003082c4808203010107060100709802541ca0021b0180001d05102020035440388600d01c82103040000b5024a08180601c0341000c80040442910700d680000c01000003500480401ca400c01e030714100d040034600c100350180988601110b039441401e1801b40b180340c1100c428400038000350104001444a10907603589005101d0007418408082c85d403603c0a010742e407043c0e0720103202507811900045140807400c9065603d4001d0958400b0b001034403889404032940c40c50150f10800c042e07030b1240462a00134010301180350026940440c1c146c40155443c1c6000595481c0030050007004e0060000c4204840d500c5140300c550044603da40d240c49281d90745805 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 700490962 1250 700489712 700489721
    0x402240a030c0906030203040b06010f140301030f02150408031629060a270c02031e090f1507060c021609021201120309030303180212150114030c01031d01 68
    0xe00d40825078812081103071a400c24501c0c80148050b20303007546585400e40d14004022000f51840b41400354055030038290901400b400005125052407186d202c0d0781d40d082c003201c080b11402c402e90103036500e9000e00342210040801c84055481e201d0041d0300d4071b0703401c20318150951105001074910034941c442107145100c00016180c03070003040901481043c180b500400071032115650000082c801c4005c5824503604015042c5a6044a101c0f000a0101e04c40f5005a007140b25004c06001082101d0303111903500d600e03501c040c044000e82036411074441419102800328414108041040c18402484481d0000310f094100003050320144c03069480d003140f103054003030440407640c03c00c2c44070f0f44d0041003507016400c4c00c02c0c0980c018005580d181c04940040d440c040c010740301d06c0c040601015110051071640c0c1e82d88829071818190702a142010041c607001e44952a4950b0402040407458100c000080350100c1000d644540e140050182203404c10b03600040d00200b07145144410800c0551b80800780b414828801d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 700492212 1250 700490962 700490977
    0x2103061309081b161421030301030c05040515062d090f1806120102130603020405010305060d0b011e030501091101110a03090e070513090e07090e06040224 68
    0x3003262115850260165240714101180d4460303405103405039000342032045030004171495100d401544149910218415038030818599801242800310072141c8800040198122400b8a81184003252101d0821040d204150f9a5112108600070b20a400317140600003015420303044199420300c0c44003180c1d040d01400d04040b10782d2250b1000300b00d0542c00e0410703000c10b07009100110751950552880364251081a41e024080d640244600996142410030950449104400503403a80106a6039220010080d5005006a42c0044d08040124201d800c1c0360402840c01c0f544424140c1d501c0e820500070f036210501ca10004001d204003003400101003030003803242c1043c07640a610140e0302c86000000240410040340c10300c042d130398814150f040c003103030784440d0303000681d01c4443c0280680d0f100e032141150140180110a45a4500080d0001e45580135512207000d280e008000d451601b6921003185048484400542c5026002304000070014600480d0444c0a040104130783d4018007003201048059420203903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 700493462 1250 700492212 700492223
    0xa050d030c09080303090a0b130501050c370e03070f03150e06090a03120b1c05010b01020c0d060506010c0c12031706030c0d1112060f0106022103061309 67
    0x780c1c000303294801512400b5042c1c1000071891418410003855a80c0f0f03854001400c0e00c41054085039914856045c00c20f002a0420000c2c04ac0d810480e80c1062694000ea226016156941c070b40030141350b081500138000c140d40d182c149502d490301c805094030245404c4041542c90b01801801103141130541c09000082c5000304404078581780310b8411482103944c50308074218140c4c801010081c080340001648441c0e030787e1502d41a040701c01403a01740c0000d00800c40364a684020281400c0011030000701503483d0050046009018100c000f9005a8980300c50b540311941109102e1317240004114590445070700480e040c9442d100d00302c0f641d100d55040032031641281050f640307170703070000d206060340002c92540450403290b13510030a0800300300081da200e005083d00c074004c10030090310344288001c44045101011000e07100548000180340e0a90311803200702c0c0e40b802911884000031484a10008444007048000038182c8000c002d04100d603011508000c09280e4040d10b80d44802d0b410500342c1c0521200b107407140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 700494712 1250 700493462 700493471
    0xf0230040b0409110c0706030b0303090603010b0d1b05092707170717060405040309090c26060102070e0c07060204031208060f130b0607020a0e1e011a0c0a050d03 71
    0x41d000075039070444c65030b10550009111810f0129008110780c0200c0382c09045c005803824690002c81d0441c0a0144e8580d401940440006000042800180300e0421190402c002c2c2c0540850342c8000032070500b086030002042446a0517650900c841c2e4500a01c0352000902c0e202c2c10003003002450360204452140010f1060420b0744c0c0250841c00d45607403c400c0e281401c0541c107540c00d4194080010040c0443e01c1a5103503004034080c14010340485015184080c0705008004141c00082e101c40707483c10740c080c0a00e5117002e02c180d80c900c13660f04a90003090140d020700310903071030714660f0034621502030401c8020400422400d00002e60031b100030710041d1321480e100c52103040a80005840407100170180c40c003d4083e1003402060b65900440d9a61951103c440011070110040201d00301c1c3c0201200207401201e68040410101800103007144101c070459851045e1142e52140b850b01940d080c8120420a540c1207003916041c00810090044548040d08985051200391201c0d8504605c1a10910110344e49 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 700495962 1250 700494712 700494719
    0x6080f0307051605090c07080c060408090a0b0711310c090e07020c04020a09030218090f0a050d08060607060c0306050a09090c050f060c030a0207150f0230040b04 71
    0x910280540110b04203c02c125103180001103010020020041030300d481000680c10200203e03081501c40b840400002c940b00c40c9010b1170904110b52000700207500c00c0511003000108070700000c048811300790707020b9170306404602d149041c045903145500052400e1a00c03c00d45107020003940f02503105001c0c0b8007001143d0310804001c0684101c00e1034100c8180380000204000303890341c0008003a11001401d441c016980c08030504121031000c01c0343c2000f580034800c02d201e0b91000540b07910460145c1014801e41f04182040c06aa036903031101000000d105400c1000f03401951030140840c03540c42540500f1083c0b0b00f01c501d0340c03142f0464070b000700039a0201f5904c000c01d0055050128041d0042c0c40106000c2042c1d0103107850b0400048240d10a06100d80b484420160081e1541d00a51750034110907403c0340d445000039000031751918240d0041008400e030344d4404801b186d10800c600728400401e60044d01202d4150010b504000c0c0c00c01005d401d640d52580f00215074100e100d030041000f00708000c0100d840724103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 700497212 1250 700495962 700495973
    0xb09150601030506100c082b0609050709120201030603141b0f0a0311030a060207050706170c0d0e0a21080108060708190f0204030807060b10050a0507050106080f0307 73
    0x24080c1149040519010400c14203803070b108402201d0000034284900f07100c00c0b03807420b200c00e84241400c010f401c50071a111040e2000802c0c0c2e84180c80380b803801c3d05105076a200c140c003074211401150303040d000440c20002048032112840804080f03500614000c0b4615441e911809801010b881025105500400354208150750003541c40420000c200c80302c000301c0282c2e40014280d501140005000f0420020b1030940942e02040143c40d80c91313100700295142d040a0400c2611070b40365202e04004104a074035100f60066413005070350b1081d41c50380c0030142016141c0031007000501f40000c255070b041c4603d6140001040440e0030303010710200c2c0510382d2103422020f010001c00180341a400406154071190901c0b01c910340050145520000d00b1a51361081d00c0501c0c0c0d000050000c540c0c0031990300f8400500030003400401c0009140c610702460003403018450340800c1c03141074025400207500181c418002c20240e580704600410301503004400203d0b5240c1c55015035800c0945400da4184a03a000040303550400c01d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 700498462 1250 700497212 700497253
    0xf150f070e010824091810050415020a02010209040e0d262d010602010b09060105090d1e0b0c1b0601030b011a1902060601020c040b24070b09 62
    0x528618007018000c404400103400e4890283c0443c2d86078203401c1e1075010544030941c09481c0008010000f9a0500b8203512883c0300f0111401c0d843c280b070090706034500c0c807035040e401424051644103144403200e564281c9041c000313411031f031903c900310b5408100808003540d80c0d000d07002d24841d641014202c0f0001c1100060842c035100c0302030346c0b4005440040e008460b48881c041e25401030030440802001140401341e00d44240707505d90b520b01403900510012a000e58154800d500302401034a01040320780303551005503814041c042c142644030207140e01690002d03083e103200311202881304014030800c0303080c3d40c0d50005203081100d91110440300483c0059041c680505400086210080680302c29410354031600700420050240c6c5000c03c100a02c218110812a000c89460f000c500d08042888482a00000d4503044250341303d0f0700501c03038440c0c0c0c50118503252161186211f001000c00702e03045448140d8800c82104601c54548020050103000701085203001c00038450313240e88002d410700351400d2410701c1004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 700499712 1250 700498462 700498471
    0x6010e1824100b1206041112010614041503110c01090605150613090b13061205070b030108030901140d060605030a050903030f0a050a0b0406060507020a080f030a110f150f 75
    0x403110071004000fa401000704540404400000d440950340e2600b0104019000b50440c900e00303084001400f98504030402802c605891081e130310720402d4615030001c075116000c0c030f02800205110082c1c80d901501d01980c40424207444070b1444030708040f050107a583c02c482120600fa14221385403820040c1190729542d00080d0380c18100d68442c00c0041ca941859000c002030f00410360f48540e66440510303144da8985142030610707003119051100ea500d40241c10540310340c8810484541c4a108008560f200060082d60b0580d40408011420406800c1c0111400405403414032112803081001003440a05030007440050301c42901c940740d4a081400e004411940001d04402c401e80080c82840074030342c511585e071500b1001c60704000c581c41e211004050002c00302c00600b0356226140040002e01d160b048406001400e008440d040c0d04a0341c1c1c1e003882e6449085184402860750810016141514060100ca203000314122007219490101c1c0c1403c903181030480c14452000c0c4544a040203640b80d540515a50700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 700500962 1250 700499712 700499731
    0xf090801020f0f031909210e06090f0f1807080703020f090433140d020a05060f04080d0207151e030203340f0c0506010e1824 55
    0x50052000070034034540510524102d15900001c003245c4005581d41c1400807503a40c140c420041d04c542864130407a1203941484025408102034a010003240c05020791083c0c840d000340a207490804c0c61340400041d03082c4506000d500441100203031b4450b0b00c40602110003000302c0c9100c8030090801e00e070b029080140c01009081014010003d04100115400a56900300e0007036401040641c2c024802e589440c2c04049485c4120003042000d080f01080c84407803200710741c0c42c0145081c03945004424004074501c2c03080040d4010f80d52000030010360400c440200100520113000f03e00782a01d074401c29003440200c021480c0185d014940500002111000c600e010300143c4c104902c0c0035041c15014220b05242d030807000241540400050210043c1e5040c518840840600089081d403c800611117620f03000d0740100001820040005655402401142d00c0690000e004042d0b90f0b18201c1184241c0000501c09800e0b4020310102041d110b50801c03000c4448069915030302c050b1040b001c003c0b80c45481c0201030300d05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 700502212 1250 700500962 700500967
    0x9050c150a120915090309060c020d0816050304060c020901050402070515060105210f01080f030f0a090f03080903120310090b060c070f0305100504150c1701060f09080102 75
    0x12102181141c040003100e041550300201504203800c003e24054601600604403405480071800660b400308031300c0f92007a21850307815600c2d0361013103e142c078580710029080340b17210038a41c01083d94440034100c2484280c44100941304240e9070303e03003140c1050f84244007050380c1d02a000c04605d804045140507200c155002c50030041c1c40d40f00c0c03982d18448000380440c24440d10002c20b00503441401100d880000e2194405e43d1001542040e03048810200c0382000e02c0f00a42001149494000c0742c058600c0d0400c1c00214100010b54842240b141d1050580ca42070000c0007400080c07806410120070015070061909540b103000100615042294403203584039032080800800854031115401a802d035010306900081c002c04410204040341304402103180d15114902c0300280c19190f4072401c805807407140d0103803041c00c0304200300701c82503520964004002c0c94400500c01030080080e070100103882020318280d00860011081e2050b0350500703811000c00980201365070646150001030107001411110001c52 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 700503462 1250 700502212 700502239
    0x1202070b0a0801090c0c08040b040503060a180b071b03031a0307150e03030c010e0a0c09020702010804172106040c081e0405100501090f0b040b01140d090b040609050c 73
    0x900b00e140501807820040d0b0754031080403840f4460608451215440215140e0781c40d290f01100001d034000e071151512074480d1800203400040c06008290f652103540c05008440801940c404c030b582030005020070100043c00b0711001c0305900a01c821540c907806920b000821901017943c1c5060600c84885403406588051001c2002d503118241001d807114440c82e0001e4000c0b801c500281c150700c0b94189803900d039801c00d4481d80031079401003001c0c40740500c14252521607694500040099010306a4064007140e070003000180400c030005210301e20044640c2010f40392000e8180144850102c070008810a6070a072400c010701c60070188240350f607015803400c02c1c11444c031381403080c00c3c14482084c0702c040715407005101240c20403908000300a1040034141c003e00007903031101201001030031080c1136261018241881a01141800d2050044980044c1c0d01e030383d03202030310074049001a801440d950b0001a5105c9107800031071009208240100e2158201040451072410300034a0200f18407a12440f503000d00d602c44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 700504712 1250 700503462 700503467
    0x506090a06050a033b1c0813060f142a180307080321071b030e030d0c0c06090506030a2f07060f0501080a0b060a030804031202070b0a 59
    0x21011224580703080c6aa0f50041e1200720081d1903241480c0d605031183d640085000b06181d24940c400100c0d60340c421a030302ca5402c12041e41c0f10f0b00b44020360401500c5070381d100001c0e441400c001d540038001d1043d03100b4050040c0d442804580f01103100c0c110305552070301011345641c8842e22041c1c200840b05051103510600c1d14083c1c145140d62a13050f282d014000426082c1d908800720103042e600c40c005d00b61041c8503036a40703520780c896028903644860081c000c00e42c9210f84111001d52070240700700303503110075400c8104448040841c854107005d405020034880c510000d680c0801035035641c0e00458ae01c0a540d81c801d40b0348500e90380c0340c81d0001b1050100d01c88060280f601c0780d9084d40e42c85007085101007108515803c3c03d22002844940002d401c0c01295500d05040c800b040040100c40d100d282c00b0065100d507980820211507080c0180340840c1c120f040c071880894646e1201a4004000030804480540d07aa41c903c0e0240e8442d5004454035039143e584541c40b9601440070100406601d040f162a007003000e40700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 700505962 1250 700504712 700504729
    0xf0d02010b0f01120605060f0403210e01110a140c01230a08040f020303072906150d020c01021306090f061b05150c090418080711011206030803060a050609 68
    0x1280c1004544071032510b8004d540d4200138028440a46180c0d5500d441443d100d030550311034041a101c16940790701c040071486000e0b411400a824940c1c2c0c006c2c0d040716040c011104822b02803820100c5100d4400b568012600d24008039001621001c0100b09405106001502140840003489040c0034480d411030b44201d540c204070b92002019141000071581c451402c80c1b100f0184000c00380d05813001040b11020001e400c0b802c40070042c803a0600d59600041b201c0e030036002c05402c40303419070017104103001d00794030714251005840c82c64980b0a015091880c2404242c0c22030f04a074a0054400c5050801002800d40005006000d0f00e03c0b0100c2c0343d1001e09203000030b0100d03800c0089848411701e00d03c0300c9006210302405071411034101040306110504240b604c1881c50380001e00c407548144c2c1f821404c00421001007104c0c00081c1c1e817141409003000c1c616143c88410306045013445050021a4465102c261003d02c90704000c1c604c0350080e00c5d16130801000f0b0110552864200c240204800c024114550b51520b04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 700507212 1250 700505962 700505989
    0x11150c030a090507170d030506060903120c0106050306100e010608070e0d060209030a0b0412021b060702030111030408030a0b0604051f180308120705190807020712050f0d02010b 78
    0xe010400100b1031800074034141281d4048440c1408044041e40e120b00d021030307101d0350300d8000e640601190b04c2d000c007007010780d210311055113138175a01200c0b8001001d24440c0290110081860000800c1d50340c1d80040790401c202154010b00220707449000b40841091200c000e805042149011071a51500c018054003c001681941c0c0c481e05603100c60130104000c03070b01200c0110f4800303420740c3c85030501c0340f429080c040d1080d01d0884514100d142c00480c40c030f04c0081c2c03084e084401d51031032941031008002801403547c80301c94140e03055520744400c40525070250b00154082c51003144039580d82d00d081164001103c002045c810702c6000200030802c41e0307545140d608140307216214401302d212240c07500c0507918844503086500070403031300250000c2804060009801c030702c5585410307100c1c01c0d81c0310542201d140c481c2060b0b00c0c0c607414840d446039910328421090517500c181d050040341c0005440d51562070a07480c1c0b4190440fa00e0380001c0320412034032820300025003050050f00007840820300d03200010742c6620b4400b5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 700508462 1250 700507212 700507231
    0x90f0402031203060406031502030412050f040501110f030c0f0706170708071116061202030601050313050f03130305011d03180d080d0c081f14010302120711150c03 72
    0x1c0451816038403a0f006e80c00a540c071010501e18a1282d0008201940013101d09540500407a0280b992060103030040740c00564684031182e1511341000015108800d00031408581d0b44601d119481101c0c3c0300700000d00010103450700901d40c4480140701585031801c13641000040120102910000c80501d000c01c07074020035182001c00c02781e41c1d060411140106030201c44825841a43c90a41034850306892000540320180e46141d1000e01e0920f80009070700c002e0340c1d9903002800800c0099088280c0048508040e40704809545604500c40d0700c151460300401c920f00803520300c8180802c02c002c401d00c0341d00c2401c40100c480003100400405203e80781e001d0710b0710228201c444405400120f503544a800ca049540c41800d0325110701e0b03014825401002800b1401000c9289440894112411040c1c955410005400c000c2c49090030700b420180440d040f9a00141856001d002800c10206405201c52080841d036607203c0c98400c050404601e070500720305180700d5a488600c140180c040205003240d50011600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 700509712 1250 700508462 700508467
    0x20307030e0d060c05030105040e030408030a230711040c170703020a031112090c030a0f1b1206090203061608060907020703020d06060503010f02040b070318150e090f04020312 77
    0x24400702c0c5421100401c02400b4903d80304600d03000d1034000011b141030304d1095030108010310690440d01e5482c8140d004400316a44140300704045207101e41d101d850403401c10b031803c0740401340d62181c0301e80c1900701490072031380c2d500c0d051034200230341c01d25124041507040707240707070142c4600344804410400030400b801060415070000ba00c0c66986000c3e80200c0b09030946104041d50352200b62644940c0c140c1e050f20401c2d00360041d6202424207190003e880e0911a800a907422101c0019555507441c3c60172405910380e40d00c108000011709401d1107069140d68500400c004202100c2d588101401c1c280c000b8030078071440000b070396425205503100c043e503a8806415943ea043e0b0b07885106082c1d01e41012548025800012041d41c03104202c49500100125503064000340035584698004171300341c2c0030b5401180240301d4148025000310f40310f0f0b01d6100c001c0080307100ca0340d81143c4404441c09a0703444020a4808184101c0c480c804900b0291405680aa044850384a107070900c2d0380000e07280c0d0700b403001c52603041101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 700510962 1250 700509712 700509737
    0x103230102090d0503090a0e061302131502010c0822060f0f110c070605071a07030605030f010903090b0336011b110a0b01170a140c0a0f0602030703 65
    0xd604849807040d00400b00e448540d0586401341d92944110100350240e00c10150001d26000c01300340c0c07036018100c020b00d010322001102100c00c0007034021200c2c00d4450201d501c80011a0b610310f401010070402c1960000c078001050078400b80400c000074201d500041101032031001130100c61040d418049600550104100c0c81d6003100401404200021003245850010441d0241e000e200041240d1941c010903207100580e100360a4a0a0141070405003003c80c0815010390b46d20042c0c0100c9034018a030b800d000400c5900d80300072074540b1954040880d01d985d034a44d492020305d500418074070002c200114002d451071030b211020945200c0f505000018407a00034000c1141100e115508084c080d80c044000c02c00041200340c501100e17003000388520041142c00c0c40d050003541002c40d00c1006160490f1604401c1d900e04083c101e846175101c00b011005024400c200000202c102404407505440440182070a058040800000417000d600c900c244c0d075481c01040107100e40100640f9809a01801c140e42400c41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 700512212 1250 700510962 700511033
    0x60105070c030c380d0522060203070e0a03150203040503040e0c090906101e0504081b0f0618040c09081906240e040221010519050103 59
    0x10703500020000c611450000c40c1e83c20f451180350742401802408203185020029218000042220042c01030200420028080300007a030001600510500d1350b1a0440c0700e5141495504403002000b100c1c0190000140078206520a01000080a0898117186050b185503502055102030001d0400c00540200029083c80010320540380242205030305452a8a0180d08050080d0701036401540710b0190200420300c2e42c01c1803a840060510980c0790094520544100e50122460415002042210822000c1107101040c031018103860403140000070541c101404010150500701d0589015130bc1c00c1c050041000c4840350130040d109001c0e2000143c00088210031a821240e41e00708461a102c0d012050400c0790001070140b14160003003070200300300a6070b41c00544060100c00b444185181c071120040c443c1072030f0b82800c10381103032006082d28802e0512008100003c004480d00890b82e942d2041081075428000f003030240c2a059030000ac10031b9604642d10815404010000b402c01041c1c02500c0814140c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 700513462 1250 700512212 700512233
    0x20c0d350a0e0f010615032325030b040506030607050f09191502060a060f05130906060806090d02011104060e030c120c040b0402041202120106050907080906160806010507 75
    0x9110b0503500400103461119000c3c00c014411001035801500c4100d80080c1b00c1d03c90010420307030780280080048180500054180c001901d040711101c128200500e218120034002c16246880c2d840200e0070807651002c100840b20024a414005e40001080244040c0c0c01412240041d6200564a49411030800070414000000407110001d0320303008008250b540c1400138481b4040055400c031040c40d41c5848444c82640d1a0b4481c50385402610081070010b80b400000b088110350580000003101d900540310301050b503c040d4000d0304640c100400340f00c505c003001e0108080c00003180c0000c0c0485c110722000100c407807185210754000c0000d5031100043c0da40d410302c0000e1468600134640e115664103c142c240e01c03142c000b00c04c2e51003a03141c2220300040b801c00e4001e58049903030f141e02c2c0040c0c60344c2c540c0921504002c001c490071115542c0700000f186680e5003401c80380c05010307282d445550307502d40440341e5840c21001130400995601c80a100100e21a0f106000a038045801c0c6400c1d074943d80603207800341c1a003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 700514712 1250 700513462 700513481
    0x2003030a12180309080105071103041a0d0612030206010b090109061d03060a0c121b03050417030a0501031101022e0e0102030a02210712090807020301020c0d350a 71
    0xd807034070030000303040c4d22102d030308251403003440200b0442d202c0810507035160a2030042140243c005000821144000d40d040000f401c4181081506d09a1030503403c8081324415000284500403000740002030590401c030783c03405024400c0c071103850021000006403904ca0107100d8030040101e404c1340003080300c81c440d000d0a00b400001e4101d8002d418101141000340510795119000902d01481c0544c0042c01801940f1040b0031080c03854645441e0b1a03012000340c54000d1003950942c2001f0640340c40042e0440c002e520942c8040c0c40000d455045142682c810b0005243c00e9045605c1840780da00700428807445e030900386041c1c0c41d0400604185580e070102410154005d09110b501c08020441000c80c1600145200e5460070180b441c020810180c5c0c45400000341d4507403000414000d40c1c000c0403043c40c0e000e02c0c5403d0291105a08040440c0e00081c2640e00580c2101d06039000114402949500716441c40007990392091245034184843c6071902014821401e00084203400708042011490b8540c0075080701c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 700515962 1250 700514712 700514741
    0x9041a03060712200304110109080a0b0405060604091e110301092406030b01061b020402031302040e0120090d0203160e010e060a0510020c040204122003030a12 70
    0x1c80c9409840a05291180000610101d09000c19001240104500613401c0320f00c0c032044a0a54071513031100341038180300091b100d040c80400080494051810054820303450300c40e08840c40b191400e4030706a400c004029100c1c0b801682801e0307102d0005011071a48003443d00d0303078080603c8144c0d16420804444000d026010380c01d5464000303d10117100d10210350714242d03142da40c00030310101801c0c180441261000e01c009407031400706800602c4040e00c1100003000303821444008480404403074002804030383c015990700520f100c0c040b8070f000450605002e400c40300d0020600810814a024003c40d84102030708400856008000400042a41d120703880020b12540103811660b42041c01811082280c58034016880d4072082100001954628a4252031040c413015040c0100e0907c1c0400340203003084880152800d5000f04008003644d51101c0c400303071004000310384405000504038108101c15540610343c4070481d80320030f28a0361054800100315a03401e4114644600400d108200f40b1000b022001c823171542c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 700517212 1250 700515962 700515973
    0x3020d08071a090309030714011e0c12030506040f06060f18030f0602091f0c02090a091a01140414010630020a0905010807080f07020c040915110a0509041a03 69
    0x206000c1c000040d000b0405c042e021141000d45602e0166060381c0809141400245030304240d0f50f0350647c1d100c0003080c0c50200c0c202600c00018a80d1a503016499112443e80066910700c1000b24910b814050301100d101100010803465003001c100918a4008810580c2400003034060f614185080712a100300550b084901c0c0000c00e2410724250010350310241c2500d1142d042c402d006c01500f02880e0713041c594803c25848500101c409503080c8a280040282000d500030b40d544054008175500b550b0f0b24452f0b41a0b0803c03032503a507040c1014425820503c0880c00c0c052481e10508010280c4001d41c1141075920030f0500c001041144018914901c242e812440e02c84407901002c0b0a0f0030540b5001341c28040318644481c4020368585004403500841101c4200003d0b1450f00420034840c030500d004d0b038000344d03148141d0301c240e00280080340c161204807100701c0740e10403012252243c5508903c00c00081111120529107060040c400003000c9018045215205503510312400c108040040381d245e241000c0a0240c45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 700518462 1250 700517212 700517221
    0x902040806040b010f0e060d0303140f0709060504261f060302010e18190b030d0e030709020306010804140a06060b0910230d20030901060b0403020d08071a 68
    0x6840711026941290303180f030064004901d8020040144058400c031000505190355000d0800c0040450003a0a40500d503840c1801c0103492903800d41184100840503034507000303040030f2400900e02002070b4800f50810038140024005c0c41c030300d440d04150100c00002d00c91845210020a1400c20088403241740300c0d03068180a10030810140e401800441e8000d172103049480050109000003841c65103041d1680d0034500c000500e5042100b4042100000e4015002481040c0000400e103004502031a601c08108034034000c6905103001c000780c201925030002c043d030840c2440000039200e000040d10080216851203102c10250008000010140d50440ca0510119980f11000c0456500c80e502142c082c2d203040140900aa001c2e541041c3c40e604c0003001c0d15010601d0700540c0c0c0b0260011511b504203662524181704840042c2041403035058010b0b2007841c0d5900780420b42a0840310b0039031011490003001e00080000d41e0790034080702c01441c1c002d203603140da495031481c3c10722004c0e00821a80d070b42c4540319000d10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 700519712 1250 700518462 700518479
    0xe0c0f09090a03181d1f0609030209100f060302120a090f080c010e030d1e0b090c1308030a081905010302012f06090f07050301090b06100c08160c0608040c0915090204 73
    0x6401200998101c0c045440050901b9030200c81740e0040c0c50124038007c00402c01400c040f884240c0c024401000e00d02c0094440300700c003448160950043c40007070b4000c103030300110071481ca010070342180c20000100490380e80350f51190001e80240002828402002c01d19100c600d0080d0000c4074041100426607945403074a00300740c402080802c4810345003210b0380300c4140390000c1d141304105299000609040e491ba6078901c241d009940701c0d50510505041150300004c402200300003806040440d600c40e8201894200310318407031a00d15488070f03d09681800c00400150b44c1003110790207415408000c80c02420341c025042c00080c07000381100115803149100700240c1801c04900e40002c5003c450603240011741cbc802c00c00d07091703c001700d50103060810040b02181052601d02102d80c0003460034240a01c088031903466403403031f9400001c0d503140a1100741ca0102c04010640c43c00b080a0071070f50415401c1c030300307150b2101e40c1400d0990181c403146941d0313165245e0759252182c6080d401001c0426056554680701c00c240f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 700520962 1250 700519712 700519769
    0x6120323030f15010809061602010905071d0f0403050901050a2c011404230a0f030303060e0c0c060f06030c0a030f23121c0e0c0f09090a0318 62
    0x30004440d00f41840c3d034035550710030504540a210000010445501c034008400207542907501e40e4000d641d0b98441100018200380b007140020107000240613017801c5080503140801c24018075416183d4202030030000040d4000c0152402132500703190540e01c400c0303000010b4078484a82c0300c801c1c00414090642c40c0c0c10200340c1d10460b640d241c00303903030b540083c0b01840d803041a20f020320b0140e0020b1441d00384803166000b421405030114202c0003800c86035034039600e500189034010140c1090300041d85505080c0b0268494000c4160000d28030101c85240c910411503c0352504805000022101008001700da11940d0401003450801e500521040b40b50b503582c0742800d01e03442c45100455010a054404841022206902030884881302c0b0260601c0000003030440c1e400d40c48807181d8911000345a4a85150311604d200e88144084004020080e08811030204880007025084181c4240b40380c0b07040108044022038201c01e80c50b498201065400d4815260151003010390300b1200b0140003058800ba03102c0050b041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 700522212 1250 700520962 700520971
    0x131718040e0d11030a0e0d0204021b0304060f090e04260307030209040b04050105060a0c17030c040611011104150c05030d0603021002060903031824060a050406120323030f 75
    0x3c4021144220103c016120b0240101c8036000c21240700b20384aa604041c81410b246a100034801427401c0f020f122080304102d580c441494540d0300100b014401d0940290344032541166508149880500d0105030030010840103000400360180b2081c48641c03d00900e100400a03545c01c0b42d95030701d0340b8203120000c0081d006641020300c5142080845e1405003000e00c5454181c2e80050403943c94003581480c00d541241251340115101c070054004a8684600d000107035004140200e140c3d40c0d00c600e050001094491170808a80b000d0b4980141150869180e000b16003c8421000030050b05803203e000c283c0c2d0a0103003900203002800001400000e1030a20f6100c401038910881d40040c02082240c022a40c2d0141221804001da00420216a520b00c40c211203489450b40c40d0225507040024900c00001035140341741c42c4407201d8020052080601e0000e4401000c0e0200780d4040041c513280c809810200d115030718003d000c0c050004440c3e2040342c1007144d13190400b0705440806640e8249403074040b10400c02140d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 700523462 1250 700522212 700522217
    0xf020c100c12060812210408041805061e0a051302040e0c03010303020307030c11060a02060f0c0702010c120905310c0e01030e030915030a05131718040e0d 68
    0x100b80002e549040d100300340039100400018550b03030310600e1254410394814594040a10385190405881d14900895548944d01c120007154945242c4900801009e2006a83d19419402c010802c0344c03607214041000c2c10440c01c001002e5690003400081441c01e42150021500446050340c26a8243c00940050045980302c1d003103154569030b481c001100902081c0801001600708000e000e0100f440307103005100d00342c000c0c1e02c2d00c600780c0d071445c00155080e84003448400140e00860100070384c4400307060120350b00040d60303981d2901e003c0055000070800340c80107000030501d5020320b440f00c07441482145008082c0c50050031034004103a000d141c4000c2e1ba04840740b0000d4400c6080e4100c0c40c003215070b0240710302030451a19021259150302006501a04201080022611060245240980d60301070390021403050f80075641e03079a0800e41100c3c03050b42e84c02408960000d10006003c0d000946c100040401400005540e0362a8030b1760603c4030b0489229142d600c4e9125040c0401c9031851200441c0070030030803403581c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 700524712 1250 700523462 700523477
    0x20d15031e0302070b13120f110f0a03031d04060303050705060108120f090301091509030201270308090708120903010b01080f0105121009050a030824040f020c100c 72
    0x305403070314288010001d0068210f41000c01004010741c02030918550a0250b6041c2d090f1540b5031244126040141602c111340e4070070060080c01491034140c0c2503490281c4171240d41801c04804102580c0f030314803000341000741c14010b90030003440c0204600d005000080060280b2507903410001d1041d00280c10907141743c0503010001403a030f180021051381c001c8010004505000594070420348035005146440d07059500c03032036900c0000e0f142441c01403491014490005840b0890300b002030850302300c08404510350107550030b00f4a880045901080d1030980c50b1421040a03030351060b00c0f5007071140c144d1140415200b044003e1103404101e2014200003181a0020458020700000455589400303a66500c40078050200500150400e001c100c4541c090031001ca031601d10061340c044003100c4048009a443e81c2003055010304040d8230004580d0403030b40c01510240c1c100901050f44030744198200d090381c41159141c2c1c140703440041c0c98050390f81c5072400300b09541e80c07482400b10744009445850101c90004504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 700525962 1250 700524712 700524743
    0x70b09011205160c050102090a09020d0c020c1c1a0108010504031e1205150603090304050f010215010e1b19030b01111009021c120201050705030f19020d1503 69
    0x28869180314148615192010001d00102503c04141c840b00517520303550200004040c9455040c0750b4001049138050041c2d90341c00001c4080100d418054865046410809001da8140e950b140c5041900503804103280320000b0514284914203070740600f0400040c1c0740400014200d070194002442507011b505d4030003081c0340310a00c950008203409a031002040b454001c48100e51220742c842075100c1400289200040101c2c0001581c0ea00204c49162203903000003030900240c280b659403038420410030700007402c4d42a03804c6215401c0010500814245880540c00520103840000b110f010351600c2480050350341c102c081032250301482c903864601c0400e0038000780c00b040e94410300c0b01c1c038040020b41d005001c1c0b516a440100018109402d03007640d20141996480100e200c03012640f031101403080600700040401040e01034291a001424030085c81824805c1005058020a03550360003180e01500070b83c00040c60041c20001c0c0103070f40c1d59501d5140f034100f80032412100703400c280c020b41b400303102000280da00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 700527212 1250 700525962 700525997
    0x120f08010501111c050d060305031b0a0b01090e070506070803040501050c0a1403100b19090f05180712050a0b030c060a14130305010903050318060402010503010b0703030e070b0901 79
    0x25054040783e1944010b1104414a80c0720360640078119042c940302e460040d1300c0031208141c5140341c005035140d030400690300402e2100c0c402a03400300c1d10404003421f05c104840d11100550a414850814400d440c2c1141ea00740610502104c006050010001500c400b1641005050b940044908864540c41c08010910b242c840c0d20507144d00034810365070222845074802c0c0c1400250000760500040c0d041504d008244132030790700e010782052141b01000301105c1c041d1980050a140242e804610500320000050165803a800d411045240d00e08122101c0f41d1038080c000c4640b041d41032842d01c0c00524140503c07150302c059401c4204003d0044040b681340340404003c100c403510411188002041910b40b0658600141d40040c0c40018400f6041c1841981c1da6112242903c40c1c000084001400000801001684007880030b403543c0c2401c0002e03c81442c3c9503002810921041c001c1d51038074007012034000c0400d48242c0082c80e0001d00e0030141c407243da07034032a1460401e401008201e808100050107841d002c65 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 700528462 1250 700527212 700527227
    0x506130b0f0d110d080a180302060d0203070513080c0a141c0f0b04050303010f091806020f0c0307050f010c17040b13060c0f0e010509090a1503120f08010501 69
    0x690080407a29a0760300c40c1c040040500503440101d403500c940990f401c8080c0d4500350f2102c000c03801034045641c1d0701a0a94003c1000030811524102100d0f240d100784050785415055075048910400e005035a078941070001c1d0f866008035010403411603200c0340e022400800100300c945482d00140d900d00031b010380b200d03040302070044070201564004e82c00c1140c1030001d80400d00c81d000c400b40901490000081180c0b00d100000200304e40c1910942e000200400800340c94006010040000745802c200b000c0360580c2c01d0507036080d800400381c0707800e070081036050f0340d03065070340c112015103560f4011244d49650b00d00c0c0454031204000c1c502c00702c952034003a138049002d0149081003480620521103115a542c1c942e03655480580203400c2c0000800780011700800108144180040d10074070b034441010f18540580001d040141076040d445c10450700703019004c82d540750403a845401c950741402c0450601f9605480900140d825440a80404265103039880c1c25504420000390400071590f07a104583c0c0c80b40010344400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 700529712 1250 700528462 700528481
    0x60207140105030f0c0f0310051903020102030a1431050d02030703080a030f02040905180708100e010f02070305071103030304240605030708070e01090e07031b0810050613 75
    0x180d0420008040c5024451800d070b0005e03000c5a0281003880c00170f10012980c0044070005011244103000344614070302640c05aa242c6c003c2d00150300032500750b0380001e46a000e400c4000c3d0901810003e00d0842c00300340c1d0161881c0400000034100020a44101042c011b08120384030b6440d01c82c490408540c0c1d081074900460071980140c002c2441030320b1030f50303038a0656000811b40e800300b5540c0d00305040c1c6800d13240024402004888004200d9041854038000300480d6080910800d901c010404c0100c01c6010600340c1c0c0149401400281030442e0049150141810081803c0751a100099241c1019004805880700318011411528084140b07018183e980c4001d031405014103402202c049280004007000080d000310365440401d0240c1c2d6600460700d0039030250003004460b00711120501c86070714007181c410300400045205010b00050442495211501e50001900d600007011191510082c10880080141100300072035070885c1441c150a0004d2206071000b92080860b550440400c403198003880404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 700530962 1250 700529712 700529717
    0x40302030406140906030a090203060a0903020d14040b0c030a120905071a070c0803030a180b0705030c1201090c030c020607200c060c01050709050d030c0b0406020418060602071401 79
    0x1002e040a80030344544038080c03900b009052040011301d1682d29038001442c02801c81c28404501c0320610300c109810241c00500600c003492900d0380d0440481e80c0007882000710603d0341440c044503040301000ca040c0703200d03e0300b042850a20018100c00007980010040000509664514480c13040050101d820b95a43e1000078040d40d0041c0c1c010300a41801145020101c030603030f00310500d00201907890101c0040980c1c0b0100346a000802080045502070050180d82d44030004810754500c0c48e40d88200c0400e1024051a08025000c000100c4202c1c502c41116056403c00c18541c009607500d0303d10402408030701740d10720002400e00b041c1514080c0005641c0c0d011b110507803aa180200e042801000d45079a503103007100301c0391042004500581c1c840e00000c100400401002245130b2611a00c064032026845d40b01c14010b10000d204007010030303406840d80d052164400708803101621503082c100083c0c002d81e0891807000b010002f0001744800d8552100c000c9a805800395191141c3c0c44c03140302c04041512645502 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 700532212 1250 700530962 700530967
    0x72a1109010f031e0f030c020f0105130308030a0e1504120c0515091606080f090a0201090b031f0602150108010203220f06110c06060306012402070e07051b0604030203 73
    0x13440b9800788042c00031582101d5005040e29282c0400265044070300b43c000c01c0c00c2c0d400307440c02d60500c00e40040104500b0309006241c21422423242140d0806444041c24102010001c200792080315080200041c5c126000c844480e9217810300845c0d5210705480803643c01c0c1d007507580c034001c2038041c16041a0080c2c025000c0c4c00d240800b4035072442408401040c01d9040d0143c1e040c003a41740301c01e05e2922806880142e07203180c09894024000304e000070001d042e0f034540354060030301500141e0380324015409880b0100165034590700d482121591108024903102c1c03403104d1090000c14000d0f400124502a00712585200c0e0417645d8441d1690300302c0c4010f842010a852201807a44480c5d2071642c001c00301c0070b11a80108150076602d440c1c03007003119001c400c6140c00f41000144114509400c10036190804004ca01400195152401c0b4581442d000c2e841403648501000c00042c00d18000c2c01350200904411103d02c04a00d01100002d245601080400118280c4c1c200c62950303140c8000b44081c40303594103400552 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 700533462 1250 700532212 700532219
    0x90812070615080d030b03010f0e190c030209190b01030504020907050c07030b280c05070f02060912011e09112b03120c020a1703072a1109010f 63
    0x802504000c0032031190900720b44000a00da10003000001c80300b24240d41d00080c1d40440f8410942552524141c200e0041e007048802e425030000400c000b03031082c0051809400c010b49501e06003010000da43d10295211000c5002c100c1c5140c02d54080d0b100c0000c064904002c441c1d000c80040d412214140d401941001c0803100189102d800741c002440b40e2808041264603443d500d2b40d41008602017114804440341030310b084200d040003650410b5070780d121418400d0001c043c004000504a00942a001d0440e00302c605024056499000840b008420050002d0000c4440c5442150192803d441c80100d8034540c04460b070500400d601c69200002d5001d46c0302884003009100f0481c0090b501452914210440642403201c411035980c007440c441e1280c0c0b144000030100d10045021074000c41902415034100e00401000541d207140d030003191150803e07203240c880d111108101c4402c2c0a40704038990a41410b80404540914029140d0f4128416030482d0085000c20301401112102072044180c0c40030b40c08402d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 700534712 1250 700533462 700533473
    0x903020445020406092f030601050906070b1509100f090c020723031501060516081e0301050906150d05090118060e0d09060203040509190207050d09081207 68
    0x141d903810210307685141060115000070f0704031060341e0701c1190420303625622009680741c500302d00e128426041404180e460060015076000d448010300090402c040018002080d13551901a01d0b03409410080700354092a00c04014083c41000d010254440c8002d100002e801410f02c4240c00241c45d100410304d0003462034142031300041d01e44e2814007003d50003103040204045c0160b1f500c40807400340401e0540941c0c00880c0c14117050502030b05101d42407203980401404400d400104a4580c60081403401403000000d040540381400394480c4000000c0a40c42d92115858144003d1410b880e421111042162218170400c0400c01280d000d55032008410301260485600550045611080b0000003180c940aa00d03c151440b021006044410954806400c038010904020b0b101c080d0000d410b00071101c07810901c020755a8040d510031580b268800000140103c02c8582100421696203181913444d01d8851400f00d071591038804020340043d00d10031001441c00800100d40036a1028800b0f402c0c5840b0741602d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 700535962 1250 700534712 700534811
    0x20318031f0f0609090f17040e070c14070f061b02010207030f050106051809060a0c1b0302070f0308120c0a140c0c1009052418031c09030204 62
    0x702c00a5030703140c40000740000607010b0400c1c00e030b03c11001d02d40510180d10300307550704040d040306c0c07100080400d010a200042030010038a0300703d001c600f000d0b214502c50386080c40018062910202d000e0180b00400150061098502c0c02038a105803103030100d040230801c201d0840700c20f042d030107801680900000c01c04903618820350815035001c0c0002180d110746840124480924a081c0400120b10401c100301d20b0f0501401515002401520300780140095680014141c1e044481c24a0880078001c0308281094000c106c000000c016103d150b04c4019500d0412029039040101c040c2d44100c513540008944400d5501201d17040350b4603440740041d503c140e44605502b9007000d200c3c0683c0d84920342040c80346641e1082200521615a43c91009960805090084032207150140940c0d40b0030282c4051055078a000549411616041003200300582e40000240343c0017100d54180707601c0005080740702300a81d000c18600140c0e4003d03241800140c8141100c0741d01940107120310b40c0c3c1000391020810440d03c50140c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 700537212 1250 700535962 700535981
    0x40b0601080601020f030309030918040b04080d0605090f01050109150906050a0c0b040f020f1002030d0b04110324010801080a170409060b070b090606010519051603020318031f 77
    0x100d42484000c0e22174180740da40182c84903621507001144080b22860881c400019003c1c03641d03440400c504060307842c47d0f0420f4003c1c02c028604440821312180034126a4000c0c8010a4010940c280306e0506010103c0c52800c203000d0240011038580c03000c10300c5d40b6038581c2c040301484e17156151642145003400c1190a5008170040e90100318019003070002140c1f071503180d180920300861200ca40c044603841009404821240610b014416030715401d0741c2c1e1600070082d68504400480c002c1940b4144000080040c21200d481a144481c00300610580340c13401d44524914042048010714060925801910859024800c15029038072030541d41c00000d050740c00c0c41010740e402c0440d81d03041030b031101608011303900950400398200745d0110b07104c400c0c07045071000c1640140c030741030140c8018100400000d040b0700c200780300058115030b01104140654864400c03514806c16030600c5c0322401070b9900d4003e40300d520150070340139a4020a4074045483c500811405c0341c0c89011400920140c159645210103810400d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 700538462 1250 700537212 700537217
    0x30f110307080409020d061a0d0902060c0f0303040b07030b0a06120f020408010207030e0d260f0a0306060834020c1003150e0103020307030204020f0c07030302011e05040b0601080601 80
    0x401c0011002e002802c00b910303074203401580f2110850141c1c411580341d640085504030307081a6100c0644d2001c2c007106c5803402000c00104501400d400440d00c10310948050f80d502e03102d4081d070800c081d00d000c03029500543c03044102c500d40d5245c1c0082102619600c281c945d600c0104031340200150350040d03000c0700c1514100e660214008110fa00e144089030055840300071281d4000800d9401c0550080c20703c854950100e071341c6104240380780c68a80706c1c411001d861403501a0085000c0c5048142c50080d602600140c041180da501440000200541110f01c00c03c0c0c003150005c0f000c02c40700d41c5c01141c5200800c15a04800c00c00361104009164240f078561058400d601559510380c00a46840f1928203000d5001e480124003807440e482c2184d400d2002e980141c40340d00c0544010300042e600030505204883c2c04503005610303800121605482c03481074070300c3d20041c0e1113840c2d0000205038040d045070307000d4500401201c1e0b0084103907240704c054410031940188120300c4500011030301d40c0942030b42500a281031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 700539568 1106 700538462 700538467
    0x29011808030403080a120207030e0a09020a080f130c0312020c01020f030717220f080a050a060c0203090303040e060306070518010c020f0307090f0509030304030f1103 73
    0x380401010104c00051028100e40f0510840c4c4000b400c2c0c0308115590300380c2d490003801001c2c01c003101a014641311500080c07003984520036104031030425250260595561000743c8800c0c0d600800f444800b04041d0384407004510740b903801401441c400d00f0f0400c034034407100c0c0020346001c2c1000c01c164115844210081e50752034020080da65801e9202402c2042c403145944045042c0c042c109007104056000518075a5940449200340c0444083c1480b400b6030a480c2d40c602a26074041d030b04c0c00780c403a500c2004840700088803a40444c503640d11270310541c1d0a041c00200020b04550155005040500c045c2050010784c2ca028800c031600054582000e07450900018020761021441ea03420505001510f0300050964903100c0a01540354030007000d40700400d40382e401c3c01c1b006001001420894514040005052040010840780030f5078040d00c8807092040400000c949820080d8403c40350350006 = true := by decide +kernel

theorem cover : BRFrame.Cov 700359712 700539568 := by
  have h0 := BRFrame.cov_init 700359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 700359712 ≤ n) (h2 : n < 700539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
