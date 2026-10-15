-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3954
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:09:15.070518+00:00
-- url     : https://prove2.me/submissions/68cda8ad-0937-40ce-8ff1-fe824625c067

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 710971223 ≤ n < 711151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 710972473 1250 710971223 710971301
    0x1e080601080321041101050714010516020106151b11042903010606140c010f05040507051f02060c0d0906060801061e03110f010224040c080a15 63
    0x1940000404824069404100c52810701c0c80f8112401c03240391a844214846540507aa0781c108000012070800344130401923484422041000204858100005c10400190360010b03158059405c00200003035410b401100d02c1e01100458880315255400c00d200c0400403c240001122203200b90401508107858601c51003d01c44106420030221768000000c91030361144104210340703c0da05101042c0001d6601c400c0c0c0404508801c40099203803200c40c00c00034090071070312035803070035192410301000b042c46000206030040754002d90700a210040403195001c0d0303025090807504013580c0800301090024150074010301905641000000304201d80380d4412050b510749a10105c6182c1d1650030a11030703d13029101800118003c040c200000501e590f80d46000d0702010006144118140010b02c00c80340d00a02100c3c3d1210340f000340c00c0c103c00e0000044d00e0008401503d003a2020a0350b003401007054000000d20300c2020350842314260340e180d0780c0c81d03202019004008805840c3c03030680f22910440c0742d00c0c4e0060580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 710973723 1250 710972473 710972489
    0x10f0f231809151f0501050a2601031a010e0408180310060e07020a020a090906060e0c131203080f07021006080105061306051c02040b0901080f0d181e080601 69
    0x2000c0c0c103401100c80c488010340f520041001c41103a0348560709107404d2401c1216030a00340070340c44400004080e08d5071100c0e014071004281403d41c0074441c0100305412981600e01c2132242d8245000c088200c003265010900071207101402040c0801c0200d0012000b900500300800e446071400c20100300420300f4451001115000203032207400502c1410030521040b68002142d200802146205800140c01251648a4240065a154a54400c0c4035041e0003150240ca0021100c1080d402c0c0320840040300d41c011b1101044e540c0f52124080380240c042000720b501d1540664600940c0c5c1c0b20300020b0301ca50381015103440709501c182c1c0d074103000001850090703034020200322000081d545012800d201042003603144070803a1a02d17049080c00383d0307541e0300700841420120444480f4086e5039440403070003c00c0c4080709554042d5105000080ea0003000a01e0f0b071001c0200c1060307d014000b0500143c591024078202c0902640c0491010300884020000011031113488a40038140150f940c441281045400c0c0c1010341 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 710974973 1250 710973723 710973733
    0x30d061701050a0b06070303050a0f1506020f060f0f06030703021005040e06100f120905100b10080c04060e030c06070c06080c030115121e05010f0f231809 68
    0x6040038080c800d9030b0f0f200112070f405200c8944c4000c0001c0c0c203807080c0e89000b41450390303410214924035074030f0b40040c417201c103108010041e20b0f40054900307640005500c120300c010704c96040c10741c540100105450b07000f80300c810807280450b211804008446240144490303010b100f21600080940d80d20140b013113880003251a050350752410503da80f040d6810017041c1c5070140c0c0001050300c60583d4003001e40d8400005038903001c0d0a40e450312203050081e09038502c01500c244140103094840b8602c0b41d10003421407a0807518052076450130f00c400d607041202101c08001184040c1301c1044168060107401e102c0038002029a20354900303100000321a50040720040d40e076051000418003415030442d0320036400c20700c003251080c11036152940a0311030003510f02d141e1003000b0303050404152015040d000101903528440700c0b03040341c9403003007a25402020244a04198122000300005041d02c0200e03080060b00c41d880c1294020341d03101d440300d044001070281c0490308107070040c41c0c01c0b40d043c0000c1140c3d40030324065801340c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 710976223 1250 710974973 710975009
    0x3020a050a060204050f0d210c05070815070c1a06030703020a0b070b01051c020d0816060c1e0e09130206070302030301150509032508030c03040510030b09010314030d06 74
    0x298986168021034003500741000180301180c851118042c1d150155030301c4091840144004984100845200416510948001294335039000c9282c60512607100d01503003540c4c0d20400100d44d0381c44415809800b40702e110040c4181c840c1007080c29984200040c0c03c480300590ba07940400c1c0c143e0b003a903000042a400202e20401040f0000b007605005020864100000b8022404000c50030007140300003c3c45038000c00b0700f40c5c08020742030050340c000a540040c00180c1d9411800c0100182005692080003c1c080c2103030144080a504407556622121f0741d10300910307403509401d0019035540030f012602d04c1d641043d809001a039407500105059407183d030240d926940750412041042850305207030000c1c01005e0041200d5a100015150414460030600001c0c0c080e04021ba1018007c1d0b13600312120034080000c0c0c0282c1079030004002c200b110b5061b6003005600d03ca9000850485524405e199442081640100085a242e00700040e400300403c0589140c441c8500d06501180c88a0f8004916800c01b4802d030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 710977473 1250 710976223 710976229
    0x3060b0a0c0b0c091309030318051005012108090402131e050a1203200d1d0a0b09120c19061b050c04020f0c070b1216140703020a050a06020405 63
    0x49604600d03c1c05240c0d040c04600c0d40056111080714106145075542e4107078010525100390003500031a02920070600d002410303400c02c15281d04140b80d00202c03113030410000058205081003440440543e008101603002000c0d902e00030268028010654002d07000d2029544648281090714010501c0342080c10001f00000d00e045030000c0355611452065000c0d140030420140b41100000c500ea0381842c0420544140420071a8a17504111150b4601d20a50350300f030429682004121204481d19849862016204020440082c02d14082c3c031442c070405100d1072683d400e24048480312041c2040503100f032446800e000c5402e840400c2c08503040c95103800c20420006401210614000c030140d46400f01c1000f254031019070b00c92564031414003481d40054a00c03213214403032050b81d000942480c184e588c0c0701e81e0b0384444030054214a440c0071041c1085008621041c1040807980c6e02c03107045803604a4904000000150310f0723000710b01c00b07034158003a040340040015024440d000b2014810b100041e2204e0801c814 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 710978723 1250 710977473 710977493
    0x50d0c02120c010204031a010614090105130803040801060801091505100e15040e0102120f0a1808121006020d05030a0914061023040e121603020d030b06071203060b0a0c 74
    0x2061541f101090051000350ba01802c1c4500400403144059520208030004840e0740c4102003680306010500800841e40350300200041c400c6074075102c000d102541d25070304024200d44450800620a200c0a038030004224035503040305a100540440c0b0031a451380d80c80e5003800317080007195070701c2d66502040301c0040c441c07800c0c0c820001016404030085080240b280c05210102d003010307180c40500300f403500000c1c0d240035480d082508510064904800210a81e01c2c20101c60780040840034104004a000107403201c070610701040131109030394001c1c01c020600420584143c0d1010300008051a151410741022401c86030761201c0a07101d5200425061824003034000d1030800c65003040d501c40c001c41c3c002e100c200054108010f050310003150002011500100300030b00c0c01c0d00401d54900c01c0030b00070460120050200d0001481103002c1e800b83ca0f222014010100c0850f608080c1c0c00e80d000d8414050400813600b10280c00d00500b10900b03002030f0305d6854028220746500300d84040300c00503a41441794000c122880e0701c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 710979973 1250 710978723 710978753
    0x3090f090703020c0f0d180312030e03041806030c170307200a03051507080c09010e030f060106080a050105090712050403091e0f0f08070611071a0306040c020d050d0c02120c01020403 80
    0x80c40507408d580c0d80305044903c24041504058640300100303e203600c01d00480d0b00070950174074a100c1819101e003003c0041c184620040c0c1d05550810f40000b44400e14500b08007050542c14045c0d8034201c020303940c02c40510108103030b4004680700f5481c1c1c4c14454803100c2c5098081d41c02003004188520041110040e2400010401c01c1000001c41c1804105c8041000b901c003118400d080c034540f0700c01d0395400f1030301c0d080154200c840c3d94132504000084040e0000c0002e03009040ca0a02805240c1e2603800340269014240d422000080e00146016003580d0b0300d85c000ca40051103454095441d030b81c1ca101313052601e214440490160164590200954000d008043c0e000304480350081a025180407081511043c0c80d1280c1414001c0d4014249210502400030001070002050f11900100141c171110700c140d0070484006026919040c014803199000148144094240b6506e00e0b03e0522172a0a90015200201100b410b512600c00240c264080a0020380104042000010f0b107032891824102c02c1003548407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 710981223 1250 710979973 710980007
    0x20709021201140f030706031d01020301240c0f231614030a0b0103020f0a1502030403021206040b07051c050f04051e06040201032c0c0108010803090f090703020c0f0d 73
    0x2486800c65240490034501b25607c2d4140051b600c8008100c0312035110440e40500780e1544000000f00d01140401c260a401140d90703d1800c0d07140d01841c0003910b506c02c042201900c00c1040003c45000990341a4003506040c041400701300a2400d0b10074200e20300a0164465104024507034818000c000b603407080504031880032402491070310a141c0340e0062011060002a0240d43c1400c1c0030b159070b4541c18400c00003030144143c03038003005140d51030007510ba4125001c03c034450304403401440184040011454000ca4225402408907210300106a5032a40000200000b420101d406005a98034138801e03903101c0c0024022150051600d4a4101d0602050780e500c02d181ca049560b0800e124000000d000758495420f007000981915048200c5400b0004072404032032224020020410202c00030809481200d03080e01c0307405007640c0b502c0342c0c42c0c1c0321300a148600750050360840d45503105180800810380c11000e20b0a0040c81c10740060491410015600c1c07501c01103501c541c445003200d80e0f1200910302051400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 710982473 1250 710981223 710981239
    0x216031e0521060315150f0607081c0e03040618080601150e0103062103030c05041202060714060c070c15050a111608070311030c011e02070902120114 66
    0xc80c2c2c102c0b01081415030742d0918000b680c00080e45528100031080841010042e105101c0c9050340440307403c0b885c4815406c1c0a031890201e24486410302c00b00351030703016030f029083c5414000f00341c20103003c0880112449508039103071440d04000e404107200a00241c2100d659001e1000b401c0d40039128030341c80e180d2020400d5809000100302c0c0391006800900c8800715460134600117041c110040700502801d27045503203101c0428482c0103500001101415507180320b520140700c1110900710980d203500980c40b80004141003820168018074103507009112880c4216800f0000d81c280c17084151900c9021540070281e200001880d030107000c802a1f102000b4003201c0e0009881c0f1030405802401801000d88100c1030007003c0034007a02124080c0003e100001509100d034000fa6500c9032225502c0c1c81a00c81a0b62161048000b14002c0c200442c01c0e61000106860354a8a0200c00380511081a25456400e00b14003d190300466645040e000410b5076079a16885c00c00c09506119521001d00800941c141c0b15247c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 710983723 1250 710982473 710982487
    0x50d1e0213061b0807080d020f030106050a0e0a300b070c1a01080d080c0c0d020c100c0503040501050304050708010507020109020a060c20011b2012070e07030216031e05 74
    0x4684101c80c40c2560003800d280d107c01c0b44103c084082d00400311410613040c0d02000101c0c0503684000504942c19035a5160f0030a43da440c01805400d441c0c9000c1d0400c0e122141d850314049800c1d8400505c09030140c62408810803001d0348408522110503214640080d0b0b1f411024004d1080355504407040c104084550500b5514000d04950b03280a40d03c031600911690200117011071008030107452030079913072000792500743c000d45400030344a4036194a00c0744242d490f00611000e05225084400351142e01c00700841c0703024102801529a03070401003044481c1d1203a4100400c1061080c01a14000c400503000030555542d00c0c410446c0c1150203800c10001c004912001c00049100d110100b0000395040409540030502c10300100c40d0300c82c06400c48180d0b034210710414000c1104076203c0b081d50704100c00b40403041031001c00801910826101d0610001c2e800364009201c00a1000180342d0008100d0070014500f01142d04900196140103a0039000709030811042d5038030800100c070211061101c6d1038814a4811 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 710984973 1250 710983723 710983733
    0x18040203070824150306070903060f06140622030c09052503090206090a06080907090516110c1f0e04020c030a03022a030703030b060307050d1e0213061b 67
    0x503020620310f0328445800400c4200d030940d81c1e010b100840280680311a443d1107070015101102a100c101c802600c2c210640700c103540a171080300c040d1180300e800032555000801c20000786400a0380c40d200044103943c0c00c41c1e0382c802d41d182e072100294072900016005601d809070a908850000740050490701d0911200051082000c0008000d078806080000701c15115002180b02c42c00b62001c0f1a4005007245808250a508130a145204404c4803045401150301e5010090560381c05948104100580300d103405410781c025100c500d207803601d40c03040350102c0503c040094030303041002d006020851400c510940d0329035840381c0c5080c0401c4c415107065243c010209611507581c464040600b08040d408152a10390a14060403900002a40301d10f0300703802582d420f030858403540456012004285000703070300d95803824000705076072198100341c641a007400c40850411010313108461803480d280502c061650760708141e030320151211600c4428220181d074148131000c2d05283c0142c103841e00303c101e2907064400080f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 710986223 1250 710984973 710985013
    0x30e030307230a0b13061a0306190b0a090207030f0206010602030d020a030b0301020a02031201090501030f0605041a09030d0608120304080a0903050f01020d05010e160f0e180402030708 81
    0xc1180c68210842e0703945074241504040904100a1051030b2401c10301407000c40048048100500504c01000580d07008045440d035180e40d04403042e010340108000545e9218161201202035030b101d000424007070350b0031001a40070540d40d08a100750035800b00d101d005042c0c0c85080584c2c144154001041c880d418041e0185d07403400703a55608a02c0a400140e15a03c030391098210800c186800b0b0005c0d9103591020502130340329000b0022241c00c09070407000000d01c01340540940e034102c0750014900101c18146864840143c40024410f951060355071010546030601c804045200e6200704002d1919047c20865030780948280703600100c1240d0000c842c040224042c9001c4070b0300507a008485c19990084e0990030350751160b8580c0068868015846103644465064006044005000760200300580e2241080c40c41d604003681c08034011501d03040d912003031600a5660383c001c0c00c81c030304080c203111905100113001199600240600e6200d00c034148000c500342048202d01914a420140c4840d0800c02e12074032680c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 710987473 1250 710986223 710986253
    0x8270102060414010906052e181d0312090601060e0306060405041a0a02070b060a1202040b0a05060711090708240d020a06170903040506040e180d0804030e030307 71
    0xb50000c803c0002510001d501c1940d911758801424000c92800d281801c0c04000c44265030f1041309024492100b640d912401c0c000207480484485281c840c1c214425400100f031401c4803e2403079441e801c01d40c058114100090003500249080030003003441d00080c0c040c10001c1c180c2c132803414000ca04405041640e004a0b209501040995002038141c5da00c3c20001003112085001ea05810b4803d010b1007051400e0350020302081d402403104100070780325541409104502440b5040080c0c800c90413800052a05421000c6400c400070882180e00ea100c0300001c40d40c1c0d02100c412030703600c030550400040601300508100c0c0e0140b41c90914014a00d0041e9640303c02c00040410208131010421250720a9a903003061640725540140c4220b65654980c4000703440104000a03840864061000003120540004104c800344d91002d0001e078200ba18040321104000d0015100000041e600e11904500030f4003000044840180c4d0380d00d941c00b505003428080c0c25000b104000500907081080548042003500d4101d07444 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 710988723 1250 710987473 710987483
    0x6060f050123130815091605040203070e06031003051c0c0b0406020c03030f060415050321090d0f020a121106030604020c0a060b01020c060310061812082701020604 72
    0x42c01d00005109005104800e42602c1c40540b100700491102c400051014840c3d40d20785202c04a61035a5206a60740ca0b1301c1c1b120b40312103c4440c80240708a04003078003e107812039030030305248119034200790000340301c2c0c0c00883e402010640003030700800620004000c0c10140b8110452003c61000d84034500405000074418050320000703100307001c0313820401d00340d04685003c010305040c0c81c0c036410705810300d0300c4005041d00c032103200300e081601d01030207000010521070803600000c0060119058003841a1810440241a80488034050084030100d841d58251843c2c203d00c269820038401e00d0910401c00402d0080c1c00034120903070040d80e494000343c04a0b01c000d00c1c4035000c450080d1242d03160b83c0080d000c4e00c80c03450300740740602a5503079103000c11001d42c004003035080c0c0907000d0b2140c41680205000c80341c00100d58544902200c10410419140213003800d41d9a402d001426000064441c40492070f04150355100b2240103c000900c18001840075803050001980640c982050090002c0000d540d0380d000303080500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 710989973 1250 710988723 710988767
    0x11030c0915040f12060b0609030c090714030c04090c050c030a0c0c0b1303020a050607030806041d03040e160521060109080d08040b0a091a04030513090906060f0501 72
    0x10310369000c00240c034020902420748441d03c684030740e403012401203124012103055042075412040b0381b401400740c03204080c0160042520410034420444031120240480051108640c800f540c091032240c01144182c20310101c199403503103004288400c50f0781d80300040701000001e11600c800d680010049500e039140510b007805130282030b81080380c000903880d4850341140d000051340e100c251003900180d5046038000c40e1007000c0030b9542c5003400380741c2c0f05a4500500150a8500007400b9140980c0004101130003c1d081160f800300c80101c951541c1d01c541c0003881c1c09441c202c00c0008005c0360315071410400b81585041401c1c504902c0b00b5038001c0503141c80e44a1070030a5040000d286034072881258000700300704070445081d100032207805010260140c40a4807000c00c0f5100042c1080080d00590303103c554032200a0100c003050740c0b17a0074500d0304040c00c201c1c200401040410441302200804401900321210001141c40c10707031412a048072026404443c5c9010030410802032680c0080b52090a580c03800d0b5080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 710991223 1250 710989973 710989999
    0x40603020a0e0a12170306130921020f0d020d080f06130c0509091803040501051804051026030d150503030706050621070314190b070311030c09 63
    0x80e62612841c00c80c0c0c3d0b00881a800300013030711089060b8041509014820b07030300c00b003648242442814171044440320340215103074000d00c0d00b0b4001c583c00006054000c56503190201c40c9028180c1e2a070002204800059014411082c5038150500c920308901800d0700040c01c1e0690440c8028200682c014041203102003a2000a40c3c0b548401d001d035181548070355000c01c10102d4514018009401803801d1030b000380c01241c00034079201c441e0920080c070304900c0c5005508080c60721380111126401303103000ca51007003190a44406142c40308d00805004a03006101c0e050240c0c14200301580200f802129401506540340c01454001c00101c1150070f103240c0c1180201e807462203040c01c124150042c0e48415054800080c511061081c01d0384003501400c401c8625a1b40380150f10f075543c0958084982111064106e011b003040024200c080b2038184900d04420307035900c0b90110a0301075444222090076180002418102724103542c1c148201c000402100a0050031070a18203e02e00e5240900e440700da0044001550072 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 710992473 1250 710991223 710991227
    0x20304120c1e03270f1202180906013b150307030803091908040b0306010905060d0b03060919020d21020a050114010b0904090206160b0f090d05040603020a 68
    0x85459182d202403440c20354105240c010442c00500c0c01c00c0f0341c07520b90f00032154410804100b00204803076003644051541070400c0302c0c40c2a55810749034100d9004184030b02d5448003017102e66100e0302c10220031b0007419a641c54814040c0c1d80d843d40f0b1850200b1050541012040ca503000310b680b03213860390302204226240d51001010608182c2c46040c0c00c1d0306201c1c4c20000010403500310004c0d8031542402e016111000d020b245078480304901c155000b0300c100c0e0b05000a00500d40c0783c0c030140d0350026051600d090301ca59114042040755001107284000183c84100e010b110b410100842e64101001038020b040003034045110042c1c000082d80300a1040108144071000e06c1080208417010b491410030130440f24500c107101035500c2440a504540039401c1c01420800d2500203041c0c40d04907069204c509161828400800000301031004080b03912080c14042161401e010a900e14143c42c854030b400815400e101d6110712004070020700300720344c0d5440204001400765002c010769089900c1070502588402500d07400b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 710993723 1250 710992473 710992493
    0x3020106080f010f1406010c11010c17071209210f080c0732091008060a0c110a050a081303170a1107060206062211070c0603020304120c 60
    0x1014071840b91000003201d121065104100c14620510100210f01060f8843c00e00e898081780d0081c0890f04000c540000b00c0ca50640d28400e01038145008a40e104c4550340d184086100407c005400c0d20010410744108510400b180045000c0342c140461202d1800440b122600180300c0c8003100301442441050030054424120300005a2140000e922140440c00c1c0da5910000e51092054040c26000c5020002500e00d646400d0b00d079011521300e00c445211818402d19980240142c5007000003198000342504003848518081c100580010440c049816002040d813981498030410b507800060f1100d0000c1e8000410781481031303000c98103130307210407040b00d90110134219544041c01503140704660101911a4100900c2c009080b900c51a80309441500398582d01d17a107500800d00564040b0300441d500d454550040c10080214981030602c0e940343c03071802c4054440460000e8000300c07000c80c099040110051036030018080b285021401d500c0d0584070302da11400d202c90103409011085c0100010700c141800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 710994973 1250 710993723 710993729
    0x9060f1104171006090203090d0c030509090601120501060203191d010c1b12061107050a2316060e1504030201050304110d0b0f01061805040e0118050c01030f020301050105031303020106 81
    0x1800f0000a170b40c1700144c034041d60007110302502a000326030f000032599004070418011160990380701401c040c80c0005107c10342c1806490307541441101842003448410360702819003c1c2400390301654407603a104d400a414040c81403441c070b09100785080401e00c000042c4ca407055100b4400d01e0b01d81000e41c141e00f480c4520341c460f011407020f22a184103020500c80020303848184114030954041040050300300e445600b0740183c500041980c1c000c800740034007190942000c4e80c803018800030003d40e60203a04070b42d14a041407100010a01c42c144103810040707590000c078000201582510301b4403d40c107030341d40c0040c110311940c04000d040c420f021000c10207201d10358403641e0040c44062320760ba610355600d05014540000c11222580c80c641c07488000706859102c0c2c2c001e503000c142d04002d425010ba0820003007201801204112000c01d65032001990b0321012010941440303680214040e1030624460b5000506441a40c0c8448400b140100010850b90340d0080449920880191341c04c5144440c41c0307401ca01600080e4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 710996223 1250 710994973 710995003
    0x13150513051b0a060c0b07120f0911030f060f010b03040c030c030308040c090b0d171207110709060f15144b03070c020a060309060f110417 61
    0x5440410070742c00c9444030701218102101c440780c821350360348012141680c038500300601c9010b8002c0403802d464010204641361181da00000300304030a0344501c960880d0310050703041e5400070340d00c0440e00407403e040c89a14443e048400280880d40f9140c1c0213172440b0701d41841400080303400000040e080c00501c001f40d401842c0c0c0320052891490340d0781002004d09200b90b0b41031b80d000038007040c00124400503126a002104000d01311b120400e031243c480c10b071070b521100c8003c4200c0400b0010a200341c41c03403030000c500c1303040300b034690074400b1488900c000d1030043c0300d800c50084c1e945458410b0217646243e040314011680e10307030042000140c2c81c050480c3d202406800714481c003100454010800a82c4103d040641c50b0084d00c1e18071000354500c1840a40c0d844840201c070701d00341c100400604101d280740116030090340c90520740b50140c120b81c080380407100c155102c00000380c0e035100e00b502041003d0058082c40f24000f101808a518a940640418411481044694241c280e40180140c0c0d0038000da8200c035004ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 710997473 1250 710996223 710996233
    0x903070f03090e070801080d0c20011107090c02060702010b0102120f070605070320030c1b070e040b06270621010e100501120b1506040302041b03051315051305 70
    0x1300303c001d0022070007030040c18100d009000e115030040d0b100e0103040c00110f400800c461a0180c01e10281e5480301c01c44412641002000d000069441d01d08100c07000c001c1041d1030300084e5900e1700b00d4000b07040c008090440411a4103003016001b82d40c1c0d0008000099a182c020355a948001c150030340101ea100d512401003007030741000100b1000c903425038010603020014190207005540072651100d0144000c840e10203c0140900401d125041120101402110385800329416a929001590320160088404a600b04141410031000b820004441c0f030b9440410780304a02011180300040d9425040185001c2c02043c1d2840d00c60407000c40320140c942c80002d440000c20421840305440740e155100d295032502140d0414000103200c190640002c5492900725080c12413584442101e04108440801c0b000e91100040c8004002750380c862056240355000d580c624098421010740150554000800441c02c91044040303400200307507034040414402d41d0b0210005520f5503409020343c010313031840c0000761051185c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 710998723 1250 710997473 710997481
    0x10e0907030b0906030a030813020402070c03061a060f07030e011b0b0619080703060e0106050604090e0f0c06070303050a09080f030405100b060f0304030c080f12010b030903070f03090e 81
    0x582c46003000d028107403400700e02640c0e00410b00d65101c80200d0000c0015031044c001620b40304042c022070f040d20340b0081c4050314000160302e60380d40c100c0281e042540c0e22542c1e145a4480c0814605201c1d0b03100d003083e2a0a0304090034409840128001c8080140900980340080b140b540e02c079410344a4540303100e000d07440c115051030030044054207044070000d00412700041801d540c14019034010048440c1c200081c640300b800c1d5a07801e005440026041c12566407038100104195440c000500048c006241c40001e42240d1460468504440381400b5070440d040100d142925840314400c41c1d8006415003000304a94071035032543c1005080009028100308000318038542904414002540500d0107101124a103284e04005007048601000c0c5581c0d203e4030400c880c1d4605540840a1a8414001e061002e4020070070f44521909a0110790944886000090741c00810041046114013400f0030b944003d0462402d00800d650301d11030001c010700700900a006140030148100b100c4805055080c54002c09810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 710999973 1250 710998723 710998727
    0x5100e040e06070c141b100c06050f04030e0f09010b090d0507080307050706090f0e0a0b0901060e0a0b0708040504151a0a030507021f0c050904020f03070e09040b0402010e010e0907 79
    0x5260b9204464484025801850700800098000c11610408100101b01d44403801085070315241074200d141400009280c88010078000e10a0b5441030301c074007922400c1441d0515005141410460344503105102980e48070a40361645000b4506461200700034aa8174a5100c0c0012050424040c00404a01c20701e1000316a100e8003002620655205404490f905501e8190548203c03001c1c0c0030f80501088842e82c10001003e269841fa5040101c04e5400111708040030082140c80748244c201001080100c3c24914082c240040040010070304550042d0400748607544202880c8210701c43d1034841d43c4c45100c030100c0c00e041042107100805074121080300511400214983c00d400002d01000400d140c1130008030803d001003085540f012007803000300311045c0c1c00016031004000020114040003010300040302c0c1c0c0c0c7c0341c81c401001614240145592079180c170074001040c40410b02e01580c010a4039100703000c0011130191103281c1090782420303c0c403202d240c0100121200304140c40915842101d99044c00030140d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 711001223 1250 710999973 710999987
    0x1203040f050a15030203060a0306050421090503030f1e0406030f050f13060c110d030515040b060d020f0904090b0f01080613060b030a050f0313050a05100e040e0607 72
    0x1034011024504840da07140e08220022105104952030340c0003581101d000b07a40310b5402590311010060282d09815200c0d2680b004440c0e0464003181d018941303510750f1803804110511030a00e422240340c120b81c494145000302e40c4034024820311a4a41c24045011403100f200441ca40102c0e000800b00c540e1035503600c6400401a2135240c0c1c80c00030039450704000ca401c21015040720340c480c00e0070851801e030b80c1040d60f40d094014184040c1450030400c0741c1d1103a84410000707001005400344603640200e941d081c40d40001d141d10300012201d601c80c07850450340500c0358492005840040c58803940040c0c03500482c01200b541072103001d05250b440340c60407100d01c040100c3c2d80710513400782440d480180c8490382c88a900603901d0200340e400343c1c0e00d03550b032640460010322142c02500603103d000d41034640f8000703285d44852803d01820074001564001280841020b10102c007800010541110885440c518210102c0e41c0010f101600c001000f20b002c0d1400b03080d484c2c542001c1446800d0b54111a25403410a0000b440d803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 711002473 1250 711001223 711001229
    0xc1504080c0d02031905070f0326091f06141504080109150b10350405011d21031312090602100e0c01110a050a0302160603090c170a02120304 62
    0x88030005d14030000140c0b08800303076040550f020120b145514410f840aa030941700660514403408618001590741c000746070680c078003500c000401464101c0c0b14a0380b6003020741d02c41210304103081c03500c0f01c01c010511540e409000d50400c02e5803e0801440c201c81d201c0f000f4402d03900141455030928019030200481d41000203508c903c8070100304484016501007150000e810340c402c10026050412191802903804841d4140c41000300403042e5420a100d001d210a007012603041d581c50755250300c1c010b2003011140e102800c07109030001a0104800c60001c494101411003c0d5403600980840001ca001c2902c44c1d000a802d508002800d40d140440c11004110030824001ca00050140c9224803010032010300642c9070011008010b0042d003000c610046a0b0144050341c003007a42d218031030000c1d0100e07006000d510f060354040c0c1e010381043c0360386000310402914158095010035151443c031102054500244c8020b50f49407040034040383e803001018510704000d10001952121450031000440c2d507001000b00f0813 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 711003723 1250 711002473 711002497
    0x60a080109050d09080d0c110d170c010507020a05030d0f0b06031006031508030706020d020f0d0c02010507050c1c050c0714040b150304240f020c010506060c1504080c0d0203 76
    0x100b43c444d0145a01c86e010b48040c2c40104d045d40104000207800d010141c0b01035940036004040100b03407906c41460f059850340701104006000107030501240c0b000c1c020541d100825000800c040502503444075079030300c100410340394816034617000740d00d41c90142d800000031030900910998803400c10000c440380c003442c540f0820300030910b0407004a003002c903001608400c407680c000c050750410303c60f6150b0304065072002003120040c940c02c1051f03c0c040854031002e480101000c44001a10302d1421a010742102c03400703031920003030200510031b02d04040720028400302c2542c40030b440f00b085495860f0b000c1e1414050380c048445c0b6802070003000718903058007200044919400f100e0034810030b51400c05010303585001041508c03440a04000007404242c89640903140b52150122444981c0030300d006a0044a0070744c8489480e0715000510310f40406024003070150000c0080b200d540c5400c02444d425596040b030181c1458150321090000b4040c00090000d69200258000640c1c1c196010198000d48a0780440305400f4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 711004973 1250 711003723 711003737
    0xe07080105040516030e030903010c020304030605010e24030705041b02070b0304030525020301020f09031e060a0906020c15100b2d2701110316030503060a080109050d 73
    0x4040c5031a000d41d071301507030a64010400c122913000c0c08501601210398038451038803042000781303802d407002d1240c3c800000c2c880d4061516242545480700650340103a00c002c00c03100104082c400004c40c0b00354007800f0110140d464051082e119408603080c4807042e071041c2c0e4824a0045899003002d00304c021a07003c124103509681d443c0e074850b6241103560100b5030300540054014490200d230791101c2c01d4000305101200e58125526031142c0e0002e400c2e0390144250103040c0c0c0c0c000c100411039007000c209625100c0900c020a0203400c01c0600841e0b6650300042081000d6500ca41d815414000c0c2503040300c2550b00d02c4016a107821400d074041c136285840a54501c0007039076854500103120f690714000d0316010030300400c12862507407003141b0102084660b01800c0200000400c4070f0303d803003105040384003c1446200340800b9038214400c005003071708001212200030303600108030b0750030140003c2121421541c0d140c00d2041e00d94450314045003010045030040b944940c0307414071207018004006040519142d60b070791060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 711006223 1250 711004973 711004979
    0x51006180608030f0723101404150209010302120a0605120d0c0201030b0a091a0306060103020a080c0a05040e190b06090915040222140402040e0c030910060e070801 72
    0x90100d606510440015070001d04c04584c101c0da110005000e903070b0003444000213030001710a03401e80441c0c0350a080c000560060b840d8030341c0c00b0141c1c001c00d220156090382050192030b141c1c0310b5100d6003041d85a510181940000c1c2d88145a01079819a2141150110340680034a000341040b03005108500480d441160303041c4400d015600006203058270801c01d0740c0c56403540051a401034000d8034036010b90700c1c4c1c0403c0e21000810344407101d03c505012628044142c0074032038078038814142040e501600c501d0416004209250b11942c12102554029070880700169444521440c101ca450081381c111109002c015818044e01c40a400307401010f42c404d12404210745a50318040280b01c1c40382c07007a005e8100e14084001411010042e81d00d1480b00c80140c409860700302c80301d000e00d8842040d1115608442c210702c40074001c0717104c0d0071401801d803941590304501e0f03e4184514500b211a00070140070b0121000000194003050030b2150b4200481e60745420f00942d9283e44400f800403c0494902d000118110000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 711007473 1250 711006223 711006269
    0xa023f03040803160b0603010902060712020a0213050703140705040314070506040e07020c09190c030f05100303020f070e130c030209010902090f0a061b0204060e07080f09011125051006 81
    0xc2702c0c169000b400742d45062803e276901c1c01c0100c06540000294040c099000000d602c60718516a2002401031000459107455000034013200c140c0c544107400000f403d010401c0d21034108017120f054940000040103c440c0303100105142120580165410070008640041c0c6030541072031050007044680c0030b807080140114103200301c040080300e8042440140020058031005a5031269001c19004e01d001303e00030b0074400010041d58001e03155400c0782c180751481003050503418071005400d20310a002607d2042d02d000f02c0d810f1890006054204102e520202000070070981068070b01c01150301801c0d03800ca541e507c60226000b0f41000d03030700758001c4200c4921220305241c4a081c0301c0070f4031b9280d01d500c03904518140c540718029200c00401c03a0025036406c00855281815401035100d801259100f140c1468011100307202d152010f0a40785190b810030150414845540059a800c001000040b0901d04180d03012404004801000500640240a500c040300c4480350001f80607035043c020340f220381321015203103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 711008723 1250 711007473 711007481
    0x1061a07080d020906160b010f060c151e0e2b1d01110f0606030d05070c0b0a0c230106060203120a110c0f0a023f03040803160b060301 59
    0x20001ca408101c081980189075024090a4001900050506280e02640410b4141d101c01c01d40e901200d401c0100b10380b80f2502c803038001a207241d180039050062581e907046850a0161030303004420b0348440103000480c0102801806000401074240160038001520688606021843d10450f548100c2d112240b01c0180074015139504584e03a6940105c41401c100796078024070520440c0c10801102103c40250b281008514004100540a084c030f90509204040c6031589e26203000782409030602081c000710f03d045405c40101d9140480c09a6603d0880c0c404031001c3c030751008000c10761000945506103645000c03005001c055a004002c1081d01d4803120181e03070724081e00d1003081904014400040b048203e0340c1281c1910324000b40d00c5414080160040d5043c4074810201c0c10081d03200102c40415440c040d43d041410040010310a855250105200c041c04003804540c0381da85c030f151240c1144444410400c48000b08000e405032608c031844142d00d606a19a400e005554102281340440c00038038041c49 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 711009973 1250 711008723 711008737
    0x80a03090b07050304050a030e0102160303050d0b120a0303020c010b060703020c030c09100b0702030f010507021501090203011202041805010e03040f09021204140c030106060509100e03060c091c0501061a 89
    0xb450641f1581d50201c8a91200724016170440c0255100b01e19104004403403517010b50320a444071921101540f02400489416003501ca2107012180100a9020004034881c10920780501d40540c0d1212900c070b0309405060716102c0c00e0b410031000950300c0181b50780480e4142e0000302c11025526921171000822402500c2950004040c4010304010032580c80688014000d10b44050244d42c1a9604e1030310709400c40c1d10490702c001c003507041507020586078583c110100707004d001038860441c159410142500081180480000c0c0a680c1c2c030380c0d80e640e580d0716416044038041e50100c028001d2951500710240c60390014403071280400c022080100300a031980c001c2c0d42c0b0b102e0401c803100300d182d942c607290309009612607001c1c00118000c00a01580585007030140c200602103d84030b42d507031120814240000b040081e1184410002e80120b425080e80c0c003c2580e0750020f0f0200710140d01c5210580c000b5100d01c0e40a03403d52042003681044a080213010341115048401c4076400001d80c08010007400d000c2d01c2004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 711011223 1250 711009973 711009983
    0x20102030301060f0c1a01260d0f030b0306190b0f0d1b090c031a100914040f090b16080c19200a021e011416080a03090b07050304 57
    0x40700600101d07100c0c00024071010b05500d4902481c2c0101e444a075210310340200800e102102038401408600010003c4608820400540209140900341a81d4485c4a5400d80c00c08009600d40341700703201e1f4425049055121760081c145c50503410a41c0046951810640c0034401e02e5061060103259445e00380a1000c3d040005450b00014070102d517202580004101038030a01549645d01c0895500081e100ea14100700340e50302c0000d110800c40510704901c00014a540344100c0791442481c5000780e1041c2a00200c0d0100742255240724a6400014040c040c03108041103110703e0a1407120600408181c0d50340030300589480f131031090702488012201120304565640e05070718204201c0c0c41148031414a40e0308100d00385464075980b44141c42003007105428400e03d0107140e0040c1d250005502d17001704a408842c0b01c101f84440c8030105503001078401200c1181400700d03035030301040a00005a03d48200c1c04204d030700c00c8031036540c0c803c41c03503000c0c0080000c00002c0e60444515000180494010030889000c1c90b004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 711012473 1250 711011223 711011227
    0xb1308040b030406140708062e0e061c06030b06030a03050a140904050921032a040e0f0118051e061203160308060402070c030b1e040b01090b01020a02010203 69
    0x448101c12040d40060001c0702c00a40e140312000d02801410301c01e40c001d114076960024541800030402a60320b0490070818a00400404500c1c41500c03580d401c004c40c018203090445041100900056183c0911070844e030401c07491101c500c2407000258040c2c001d491080c80040d081c0c0d15800b0505a45030980000100410720802070044514040d107040c401300444100e642d0702c0c0031080c102017002d4130300170f0304c0241066101060010050348151000114800040002c505500d045803071902e110100041d50b1b03440c00ba03c03a410700c440301d005100300c2d00034000340140c050b0f1038102a9203079102c10000344101c2048808602c3c03074400c403041c507001d44c600589449410702e092002e10302d40c0041c1d001c00604000c0d0b00c81214030310380a9810040c409020304032404083c09103105102d080c01b80407980003c003294800d505c10041c000015090100e03c3c4280c80d0810003a21259651280503691032111010090032907001d60300304800c120000503c9070590b04000c005002c403c95040049e40e607034211942c02805a002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 711013723 1250 711012473 711012479
    0x2120c0d08040c0312030f0507170105010c050102040305070b13060201090203070504020309160b0a11070810110d0f0204030c15091703090d0503041706040c0603021b1005040b130804 80
    0x71802580d5009030059143c00c00c42c0c1e540ba51a260340d119645088000700782c80fa040c0000401d4280b154560120003400d02c4800340708a480858071641050244034103000034000c00b0020b01909606a50195900070f04841815480345100c102a03044842d44015480d540103020880900c107005e10000c180c8c2c058000c0c06180d082c0f01c100006900020008420303807140b04172605c0c040100a07001001400c10402e841e03950402c06800501c1c0c0089030711418039942c0300140401c60990001519140510b0360758001504a4003484610350520841030001d60050500324040d130500c80c950700620407039118540c3c90034055941c1d03400560002c000880100802e0030030310100504229411030700107019184064a10b003418000001c0c0b403403194940c0c140d580d544042001e022103031090301707006009407800004148074a000e980350030241c4590b010710002c050300410504003202d80448092440703006030b030543e1403207070210310410000c0108580903034914104101248200d288002113504164002c4019840e00741 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 711014973 1250 711013723 711013727
    0xa050609240a110a0c03120903211401140108100b071101050d110310080102072102011407021b01032c03040e0906040c1a0406180305010606090602120c0d 68
    0x80700400500d00c203925110704083e0150700f4401072411340080c0d11884198412400c0040c00c0d0388005000c00b50191030240d03201c0100380c2000030a120950700c03a0584030480503401e14040908182c0304800e003102014030001c55502110b1002110107034007070741c8081e040d80c1c40304840d2020320144d104001d100340e8100306140205111074810700b42d040040c1403152401c0c502c100c07008110362030040050001d00012082c054a04009001c18005003030010081d0b003040d2046c0c8901c50001710a85080503070000c0251021040e6000f03400042030b012058040d0540c519102801139268001e0682509013011400c50b24012903020b44116905010010200c0c000500c0308150405100d42c86610f1002c0c9100c1840001585001214403510803407045000c1e2038982043d00d082003101495030012044a1581c0f10250f0440341c03842d050f00c00b01c520500c3d10341034443d80010109450200303030b040a40300d5424820080741c0690459100700c11074050307a0888000d54040c10340044e1502409000030110340202484592440c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 711016223 1250 711014973 711015043
    0x70305072f070f090902130b01051b07090507030902040e12030a11040b0a320f031503010c02030405240a08090f032101120507060818060103050a050609 67
    0x101d10003110400740d01e4925504842d8440e61200340c809403245000c0e01117040c440741c00c00380c144101e00305001035105100040c0c071901641c805040f05007042c4804403903400042090070b0007032030600ca04100328200703003c008000d047e04001c1070780540c0c104820b0900f400340020b6610440f030703a081841400c5481e030117100009001205450310607a241070102040c1e40c0c000f5130040020811070784545614010b00c0100700365945400681102c0140454610841d20001d4402c5800b00e4003d10b001c0c1d0b0b40c9a5a1020100b00800d6920411303405619180100100f1900040200266a800c60306500440080341e1302d0f12800741404450b2010b40014014400c010340142841900800364100340c0310b1010003104240d18541040f180010043c80c460841018002d030f012509000d010b100d25100072502140d110140e54602501c00c4038100241c4200045c220004010840802030002095032520f59403070078129503a6031002030079245070141c4804101d429100199170369035060b00040ea0302002c03200079441c000341 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 711017473 1250 711016223 711016307
    0x206241503130506010f0305120a05041809050a152f0c15041b05010f0c030c0510020d06030b0c090d060e2d011a0a0506031503030408030307030507 65
    0x81e60b420564480007542c1484040c0c06400d42907070b010850751550820070318107130300c0403201d85405500300503c00c90164860121010340d800030307500141510507002520000c000c50303600603002c1d00178001c100080050320308000e10070f0303400c54100744418800111031030940d141e101c1035010b582040000c156814417910340a40002120101a50103020022610000b645401c960466030301c0f48000c2e130128000b001e00580005840c080c07038480583c800440028064802410000d014000040401004c07c00700300500300180415480a540f50600d550507603014203c0750000b00c550704000b00c0041c2c00b00b40b00a0a507418510014040c0100c0d544a0700d80800600e11700c4070b030705a640503410603030201c51848a000e030760b500d034005958140c445007004c1c43e9085540e510503800307140d066011254030070780d2284007a0096507000c43e00c091346c0b03460f05100342000910058006405000224000914400100184d4031500c00f94405004503901c03000301b280c8010450240c0c4001e2051105241c1082c0d466800051403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 711018723 1250 711017473 711017491
    0x309010c02042007030201200405310f0e0a081c0608031b0d0206040503030c09130e032104020a0b070f061514030721210206241503 58
    0x4901140394100a41c1148044020b200740c80c001840005c00d41c0c24403172402074620b002141d40120f192065400840d2091340b08240c45041400d03030030042800b28010500540848403281c2c44000402d0000790054001000c2138010715140000082c2207440c0030401c0c0704082d500c0f0b50440d103004100c1508079012203d40301ea561001e5a507080108000e60200000e090040c1110107400c0041c0401c80c505207400110310880c401c54009205010001c0c4001003941c0e004448404411345a4900c072000c901c2240c40c51b02d89048140c140000542000804001003d0102203e107c84002c50603072100b0103540c00c4142c034001d401c000006810000d921900740980070181c40303000800803250460b12240c050700c50f02c00382040e107d000900108211455400710491010041e0041c003805071914120701000d10041c00013100050580280b00308004850000007040d41500d804100c0c200039004000f503486500701c84180195045401c00c507404a000b0318000380c0c03da0010284804404599407005103500045c0244032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 711019973 1250 711018723 711018731
    0x3060b190f09090609201204031d0904080c060606070512090609091905011401021509150a020a080601030b1f2102191b030e01020a1a060111060105030309010c0204 72
    0x50700c5070113006807402846060804102d4510010504252828000700300403114820402034510402c1a4580e43c0d01075050305201414448072a800100752820071121544100078900b00820000030601820504c0440011035a042e90354106000d524450284054641c0e4403000c0744000d40c0344000024030ba4128054074117820044800d020501450080da8a0048c000800e060307148950198800c19004202042c0e600c0d110b4024080040d4a40403850100d81c0784c0710078030002581c10441040f083c0100f820300d10804501e0f24003d5407201c003d400c04010f030000215030b4008200709601c40d00488a203280014441c07040c1017480c440520070566688821418800c030324150010840c0d0010392a91409000000981d031030724000250031041301c402403c0c0d03052242c140e210580441401e03003000034a550508084c8100d5010900503860301e822144010507840d41d40c403410782c1c11410700c1e15490042d2001c1c2c941c804941c0b0b100040365100c0f103090150035015402481590090b44c404e2000100090000d80001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 711021223 1250 711019973 711019979
    0x1704050316080a020607020303060f06180303160311120301140f0a290f040312030f0c030e1e03160201030b030109050724021504050312150103060b190f09 68
    0x240e500d4000d248180c035030b0361000c00c10b008a40e80500c1019402102480035518515080c40002c0400c0418610a03008a102140c01a55000180034090341050010200ea07122080380040304007a05040c84210009800500303007182c40d00d800240482c0c4461440e8400741189c0c24404800c165010700350a00750320058901500755a5120030f403490b0080c29911403c4261269081e04540a10440d4060404000d0301040424200719040741650140c917840700038210003400500048002d881410035500d4030b9894500b10100310740e059400440b0580176034084d0384106508000707544070766905c13407a1043d45030410030243d110100150303140071b8103900c1418001200d20341704000c00e08562110000f01c8259104010a000100034009600d52030000760140440613113403480d000391a001c44c0e90203009000d03144004101003100600c01c1e2400c144400481754160714280442c1d901c1e90710044500d6010078a03080d000704281c101d20049902c41040344010700c0009040b5101250b10003815a0b8500400c1100b100c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 711022473 1250 711021223 711021247
    0x4020a0603090f02060a1e270f060810210605090109050604020f0112020403050f0129041d010903020c0f01110606100309140c0414060d062c15090a020117040503 71
    0x55001c0180348d070300c0301e50300d481c1c0c4040307076100c81144088100c508001e444100084050300c450481654100d20b01105182c4070341e51010601500c036000420038040c201c807050089080300c0300209886004600920090325200011800c0b250343c407102901c2038010710001009800c103401c0e00c000010040c03429000801c000b410312401c0b6000f540003101c0307903040003890500c4c95a003400754100000c40301400010210713201005124010584e04a9401662540016102c0c031255a19402001c44504000d200c0219149002501c3d0040d050007a0300ca1038030404480c0940d482031848103800c2c1c3c1400000c1c01c0c2a2915820070084904246094040540707600c010b000142410580d0b10f10f80400c80700606032840104108015600844481029581c03c1010061182e4490f442880303581d800200c00200c5020803820b000b20000c0c120104a407100d5580f8400f400071306c00080c0344c588018903040390360203604c1d45030800707480386020b401c0a400228003c44020900c210118034540140c464000c03139280a46c14540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 711023723 1250 711022473 711022517
    0x10c061e0e0a020f0612011413020d0c180b040509190606020601030b0c19030f09120f030b3015070c1a0115030905030708030f04020a0603090f02060a 66
    0x41c2411036003140094000b14100721001c41620703c400c450b100e0829084503c2c440000b00140303c2d598582c41c50200d11032301e513261115440302d451140c5005560b41e10043c00288040d01481402100091900c80794800e0300410000c070106a604140c4c1346840c061501003004103204000c0c111500c1d00c001210704003008201481054000c00341c50b0060f0410350303d9801c0121113590700500421b24600c0400900358011040245a9a0046a030070006500624045400020084950001c8c00540114040300c000c1d5084541c4006002d5547e070140b20303070414442031020100d8842c884204d01000d00e540443d0708500d0104115132507800f2011a401214040303600d20002c50141c9100c0c0105132100e081c40103100408000c906041c0f43e01e44a10b0f429450011203110071040c0c41c4040003010f41e103540e000304215003842260340c0039411030a2580c0301d040058008600342c00c10b480c2244a5a007054000403140c1c081d02400080075002004003051961a07000d1112960003200c1304401c0207a064000d80a070342488070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 711024973 1250 711023723 711023741
    0xc0112111204031d01050a0c080904050c030a0605040605060d0908120a060501080708070c110a08030d0e01061508010e0a020f0318010606020a110d051e010207050714010c061e 77
    0x20298542010309000c1c01130000700c822070314202c0c01d20710781418503604001119050ba43c1da14041c11031400754200100540a18405280c3c002c1c00c0c101441607010b504406140200d2800300200705080c0e4500c100320071241036100303c82d002a002d0081080b10340103940080010340c05400c03040d00e000c04680101c0e6544000715180c81c0c200d40d45000c207000701c0d41d00079880b950000d00c0e420400810306045801508110b120b80005101d4000c1c1198001103448a004d20070060034003c0c100c9071544403c02d0143c026110f42c4141d68801d42c6405400111201d09420b80106c156098803a10b20a9081c0030034031240c1840108203119007502085501c80c0403112400840c0706112900c400c0c0503240d401804030703007510a554841c1e0210341c404c3c40e0040200d4144044004055000c0b120303105922024030342182020740030b0070324880888400c1c25050240c241074005100701c0f44540203aa1040340c850707080007607000002a07514005900c200b80b070700015600d9808205801c00a480811090340c483c0d201c501a202c241d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 711026223 1250 711024973 711024997
    0x150c15050f060a1202130e0a0c0e0c0a0816020c4f0b0d062f040e01120c1a12010f050303070b1810021801080601020c011211 55
    0x208100c4401400ca524a8010030100d8000e12460314018091400c80c03d107500c0a481203041d40c04080030401c50b40c1c00850032101040030f46008c20028184816001e0320352040c10720710040303100029103083d032920464908000540311100d40fa1a80c0001400c1200214444010340c41040f0743e0002540d00d070520301c20b020000500070344d983c08001a4042d001c03016007583c640180840040050b01da052021892841600c10301c0c0000c1e001011030010b8001c0c0107900b005403907985001d03100150f61300000e15460445450b862480e035039021000c1c84a40c0d5104030701c1010f80741e4680c0001481101031600144900710300880d4071111043c2c40703054641402c0401c0c0d07121020010009101c1ca011407610326558010083e05110b011420f04c0d00004c69164440c01c1001080015808002280c0300d2401c48a950684070507021105c000e40e400410300000d502070a40d2036022010002024400e600c03c2c0020f502c05d40c0c060780900b00e0100d41d0401900c1d01000140061400398582d5241c1e90700d00c1201c2c0140030720160380 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 711027473 1250 711026223 711026231
    0x32306040606090e0727020715050103030809030301030b0115030213060305070e030102040f0e04050307050d02060f06090402031011040b03190605031b1c06050405010b190807150c15 80
    0x206403104103d13244411040c0b1540c115000412540c1c009526240c000d00b0407204511100e00c0e000c0140b00288079044004011642c0b102105c032560b4201da000324182d134800d44a1f41c0450b103a03820f003507a580c0001d200c01040701004a00512080603910b00b00d01d0071144178100541400000b020b02904e903149900700c0c00c0081d0b501c4042281007a4041414180d15001781c00851400f814540400400c0310b043c0100b0303403511009000314040000c10030407121426003000c15551503800c0c04c03074000c2d241c48007170320500090320122003c0307021031425290643c01160300800900740f0915100c0c03904068551a40030307005802081c000081d0208018005501ca0000d00403a43c40012010000340100d95154000500a0388080c240b00c11541d4520306220411408031a404d050aa0207602d0011249800e81d00400c1d840c20101030104000d415080504152000c44e00d060405030240d4540c008480544180c1c820f6a014038020014401a07038800c070314100b05450840c101501c01c4d221030340d11080d5110b400303062650f6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 711028723 1250 711027473 711027479
    0x110303090c09181905030f0c060f0105040507020606010c030923030d090b0a050904180809100e030d080a06030203060103150b09070905040b040f061509050d050304032306040606 78
    0x2d10a5920440c00f0710041c2c101051043c007550f60b00d0440b0442d1103910002c0c0d2200702400030802c02c1c4c85001c03130b110002035550fa036001c2495841c0d03507054a04c2914102c006002045900e07107801918811065a1700410165450310b00444444a503000154284040301d00c020600c0134604002007130400ca80074154104c02c088009140c505042c40150b502008075241c01800f0441400c4116880ca906614003d03807140300000c000b80007803c05001e1217400c45080e080c04020004144080c04841c1402c90707414490452254007503400c403d203800c0c815415000300c02000c500b680a506126000310780c070400001c00503269804285082400e8005907000201d0010011948132103005200004209680b902c005040c1964090942034550260394440c6071113a0b0050346d40d80b125808194040b0035038a050085680d9480100c808682c0e020401300019181d82010486060040b40403207890b5004c1c00441c900351868075444000121241100811403805c0d60340d040161013040742a010794020880011114a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 711029973 1250 711028723 711028729
    0x1107110112141608180a02091816080d03061401030905010f05091f0c0f110f060115020f01050f040f0804030510020a0314061011010b1e011403130f0201110303090c 72
    0x500a0a45006140030a002002c1d840042041c0000b01d47c192590320700780d210700f400b804440512a04411940c451003101c00605a62004032200704c6498038195141c0c0e031031041080b800e403003080c0210a9100b950410b0700e0f80c0c55101e40c1c07000d481a8010300001941d03822490000080d81c1f0144e0b07a2800366800074070042003100c0c03201944a180d10814408215030204190b01408100943c0d400006001a45c08080b483e55814414041d0400800c0700350b5000d90b842e280e09114807030881020030014400d0302d02141400505115150085910b5010401550780f40c3c0c0c1c80210f00c2c0c0303140d0b0307080300d15900920001001a40400c00b600c0003810b2000003503240c1c40044030090845200b0210301213422001001d026058070b8401019012a0291030042c0142c140d400700a400342a400c2d010319040581c103580c1481103a4000c000e61403c820903070301c0c0b11461000041740766490000340c0f840340c0c8850048001e0b00009218002c0c01000c0c51060402c218018000c515681c10350308112507080c4140c1210b140611a0703d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 711031223 1250 711029973 711029987
    0x70f0501090b1e0315180f0c1c02070203030c100b090a06030b0711120406030204090e010e03161a09030d0b010518040b030c0402070507080111071101121416 69
    0x4202d10700b0141c1060100e003014540384100206200e50010004007042d00e08800d02070080840768054a032402128951082c140340d010100c450010f50130690001c10600040c0fa81180c05d09110454100014041429004025070101c02c040364144000c00520020003818410610b004d490082c0000d20701806c0740074450319203c002c0c8001c000c18030701001400003d41c886a5250029902e280c03082c41c07450780790300c1070b0302c0c200c0900420b00400c0004540003030300d694107800170300c15601a014203005883d05050342c0c5003680c900e140d1501c0c05400034883d05064203410800c4c243c8482c050801040f03081c44010b040d0010107025100b1015035000010003410080395030040e1007004c4401e2074030501d403203012036004960b4504120228030541c2c0b40c10413004155000c00040d90003400003001150f0382c020924006a41c1c50382d902c80d0040c5942440030301400c4c006203000360f410950300007054604100d8030100440e0102c0301182032902c210354851056005100420495120381d00ba4002041c1d1407111f030902804c12 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 711032473 1250 711031223 711031229
    0x706020c03030a05030708060d060614120c091603020405060d02070302010e0c0609040903090317070c061b0809010c05010f1a0a080a060b12060a0b0a05030f060115020f070f050109 79
    0x20b03442000b82c0c40040c0da2000459a002d85245000b030025201c5200040f1f115890302c0d400360907982000e40102e00c01803819001800e4000c111141d04819800b404030302e4071048103800d91544507001c840014841c6004012481107013031a40340041c0713410b480b10700140690700300342d0400152540c049a40310070035409100d0381c180014000c2c01826806c0d205c0000070203a00c45e1962480c000d98460241e041018002d44240c1c000c1c580c0705030080c00c800c0240c0c0201919400c0198103039141c010022001031a98025441c688041040203020b40111a0a883d9000e85a0060305105e04010310741d000500461828030031445000c0b80c284021941504000404208514017207405200c6c0300f40780b030200200300d00050f104160951100002c24601c00b81c000103042d211a0300da1948441c0030781d000700128038201c0e0703021705a8001c0032582616155218800e041d650100d05c41800e03e0790740800b0041c0040c17042c5405030349003481244100c43c04000150030081c10920309900c0f6a03103100c0030740c10621030b41da044008040a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 711033723 1250 711032473 711032479
    0x5040915120f29061318030f020a060203040f0209220b2205150c0405030312060109230307153009141c0804060902012609010f060f1e090e0706020c 65
    0xc0f81c4903a2440311b005880400082c103101c4900381c88050306000f0310241c980503400000441d01c9141c1030421a0082d555510120312400c02407001a804035407110325408024144100148240d10780d07590300e118401c0150491a13040c1403090b000048010070151100b0b0f01c0d00c0754015040d407078403071030403862261006403c08280c00c0e004d01c01481070303803000425500d20703041071880701b11291904001038030001c00340d0708401c001900c1c141c0840741904c446101c99100c403034190101c80c8070559440007205170b0342c24250395000145001d83c4880c08849544000c50032150501c604410054010742082c0c1110707808402200c21484658000c10049024450342900d010000d803c9220105500001010f96000400003000c0c0e503500c401040039648150304a40034211440c40300721340c10103907040e00c8a40040031502c291403136003030600f500701541c268005c2400303e4660a001d140811b040c102080a80754504074883c00842d5085000901c2e041c0c1c500500d0015030000014001c1c0340d0510b00004c0c280350b0b8080403140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 711034973 1250 711033723 711033731
    0x150c040527090c0d030302030414070f0315060605070204020325020a05010b0307030c06080a09050a08040305011802060d020a1b060c020610060f1b06060605040915120f290613 77
    0x142c980711401c42035000d55245c94016581d030b0740c91501c0448441004807010007030bc42c0801c0031914000307102042003680d0141540b042c48140b11001c4e90180c49050050800040062002c1001800c05802440e0060741c860030040c0c101d1000300030070b0745406034449240c0c01a402140200184082031040d000418400e42c05010726904541f202c41a078003181c42020704200b0240000303014155180d0000506035800b1050350b4241c030a908010b00217401c030b07000c03d071a01c0d480c04802055282c039614052007269030207058241070041c518511802500507006031020701443c5c400081180d0b0960b040c00c04010302c031342400107542410b064001d10b0071500a081410480240001b42b0460380c000146409140c0702d4a000300341ea100b100004480da907000240100901d00380f00012402a030048050801d461910204014800c2480d254024003100740c8110900e0030038000d11480818003d002403e400d5004801344025a03680820000607222125100f100d0f0245040c01c0c01058a0300340300403840d06840101c148 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 711036223 1250 711034973 711034993
    0x2041a030603060c070c0b03040b07091202150c070e090a0309050105250809030102030702070e070c082d0c0307051b090601080910060807051003020309150c04052709 73
    0x10f90364907805031610240d00004103a40c01085005d04c4000d0281c4400303203000b526070503d0b25001e1050b100c15110075012427801507010640d68500204407402030b40040004540008103170850300c103544040c03d41c440c5405040c2d03000c14191240b1100600803042c0600804a000041c00c0041112240781c02150400400300100ca21b0003680c00002944540000c4c010b0440108601e000c40b2a482803d1120341c1550012041188017600810101c04503190941e1405e015543c99000300c440000c10075009041c0c8005000585410040254103a010301364004190480f0310340d011590300303e070401041d5000a90002880d02d0400034284100c0341008031954906d000000c3c128002808003500803d22410400f60340c00080c00b0840c20880c943d040c180115040201703030344513500e03c3c2c1c0b2000d55002d02d0303006024040004091600c82e100f124810324040d07000e4031020843c000d401c00c030085c021b03021602c1150244400b0030b55075104091a80c0388660f022040c02c66900300115440b607004020640b15a98004195007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 711037473 1250 711036223 711036229
    0x10801050d0b06030304120b0403020c0114040b0c0f070f1409040f080313080406170115020706080705070c062c03120702180c0a11032704180602041a0306 68
    0x1808660300050030b101da80d07540c0780484d141d800755920a0b102100945070400a000d01c1485ca0b90180d4000d909070765603281e85500645d40c0000350f1171480d5036620104810440c641004024041c0100d50400703940c243c45543c2d412038948200354015854000012804010070300000c280c4a803440b90a0300d84d02c0980c903040d00c0d00441030b8000c00006d08040c60000004003034ec42d407005804800f0381d10040c40b81d201c545400c2e0041800c040d03400703156104400c2c0000400d860741072144100607000c003640249046414201c00b2244003c2c09059034090000c02c0c007540d800540041c85401c00f0b000c8a175074580f500003034988294841d00291600c0010b9803078000901416031800b0480c80310070003040724036550328080b074404112003c010425406406200a0501c850030160310001d21072032000343e42d0721802c0115030ed0590f8a0b48030342c14044480c408941d445403122040a250b084031028024400201940700031500039400742e10602c01c590380b95000800340055040c0307003454604d6104101340c84d404c0d4940b00d008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 711038723 1250 711037473 711037489
    0x6020d0908190614180d080408160c030b04030e1507121818052508040f0201030e0d020d031506091a0403020a060f02010c210509101d0c01080105 64
    0x10401d0000444a803481c10b00040f908501009913254000c10040c0c03078901016101d44280b07006a902c00d00404410b80344680c440c070440b42c041c1d504103000c0d510f41007520541c80c855201c210303000c40f1202c083e5400003001c03801d440008d0340708074000d80340c4031856881141000f100b040c040c2d1801541213030078000ca2003c03034034518054070b864a49007400c0909414540c80119841c195a00c03402600980140c02d0a44c60056000b0b02e0040308507a0b0306801344491420003240a41d410f00c041c4000172680d00005012030014014071003003a0040c1000100120f56011440c20207100040702c8000d47d03c07038100c8000040e8103119880303020140f2100c0c120800d04180000f03117080c4040c421130f0310084215201e11036080381142140c005660080410b2500c0743c0d10040074001b9501c425a050241d46051101400a405006000080000c051811480704e8201270307120000d100141402500d881180e4604168102911900b80341d02440000000c01c031102404803440d00843e2074941d030400c160704004100644500301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 711039973 1250 711038723 711038743
    0xb0121150f0533040b031002070215030613090f02100e01020d1110050405030919060908010903050a0f2709060b0a020a120e0907120f06030213091103030c0706020d0908 74
    0x54043c4822000003c1c00f41500c1c422240d454010026202d0710781106a0040c032100b403080e1602028202e03107080300c0e555400200d4200342c00106c0c0804c0c2c010407841c0303580300000240c410060760031320300200e0300401c400340100d08425001c0341034071301c0c541e001c1c0d0303010800c9a20800d018640440101180c2c2031607510f82c40c030301102411540d2504d01260421000b07009560700704401600b00008190000d08062049a080c0f1801e400b00d02a0100810904018098043d0240d00341e02c5003442e09400c100c08840705602a0349910420000c4406080941c611008055481c1100c0c0600341019040440c0441260559441046040e4040202d200442d030013140824030390381c02c180201b041074141102901c1070144200b03003a5000501d5800c214019030002201c03115000d4040d010042031782c8a90a00c0101e9403070f8000a90721808400360480303203244540100060030f21072200d0411019003038001c2480c1d0f400c40305540c542d54004950510003164100301d00c3c0d0400c1e460307260468036145031050341c1e922505009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 711041223 1250 711039973 711040051
    0x80c0c030607050d090206040914061309020a05090408090411030912070210140c030c01150e040201091a040b0d050603061b070f0c1e0509090a0b0121150f05 69
    0x1700102e0203554804041d078000b010020414001003001c000c1030800e07a0011180315100d52040340584580e80400d110300c003030303c580c0900801c80b12411310040041d442401803089602840c03c206d5180691101e00031460201410600d240d145d00701012a54100054070580c40d85a043c140071031400b580d1540e0700002400c0c01d5003007110001581c1e0b041c0c90042e2040ca882070303e81d8800014404000101540240b18104242d07130519442911a90680f0032400c080c0c5000c0d000441361141800780100b1940704100d843c03c9620355518007550380ca0850010b80040c081540d0706030703071501008268201404400e501480c10351000701f04130019846080700740581c000186c8411101d1a803a02000890300308480030300801140b00c929501e61003031445d02c0b400c1c2e50140714040d03c20180032480c41440000c0d50310000d54021131000942e030030111460b055400c07c240380156401401a4480811036014070b05945000508020800c1003000325002d05442d000b40800c2340c0c0c0001c40c65028010a50200c01410240ca070b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 711042473 1250 711041223 711041231
    0x623041703090909070e0705030705180f0d0312050c120103030c05010b1c030f0801080316051006061206080303070c030509210d120603080909071b080c0c030607050d 73
    0x8100d0103441c5024490b41e00d03400440798000d002d0b0702840080d0400413a0100500300401365a00ba0781121540410b82d12031010650900a04402c6040d00354150119a0040c1000040514003000581c25484048058000c40e0314440007114001082c02403d40c40501707144254030f040c00d002c8002e0044101440f002e02040300c840c1c904001c0283c03c0d0451880003e00030818040840c1c035900303540340000031030400c401181d200940358040302d0080059038101c0d12480c014500f8075010168a901c0c1c2e04000300704940c00c0c01118080300140c200c5201d10809442035680d9407003840380d81c603840380c11120b070740d0050b1150364020b004211400340e00c1102d80c0e1141d949450f240742c4070103440c40071440f0003008440740b407141680100c00d00504000050080014a102c0e03441484452108040c081140d515020180a45108101c0014a0705215036002d0700a5030034504004242c0b1080113900c104800c001341200c0e040c0c40000c01340d03007070764041004182803402103006e8125030401d00000b1300103208014000c480c403a21 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 711043723 1250 711042473 711042509
    0x9050907090306141e040b130813060e1e060301090e0115030b060f0d020303070206030408120a020403020907020613151e0203010306150602210d0c030501062304 71
    0x45201c0040040d940280c00340007400e484622030010a508031240411310344448400c440804c440d00b01603000703d4202d40c4900613030f00e0303001c0b1100190115810559100504001449000d640020000001d001e6035842c4001c2c4859803080003072102c1c61504641d80c007a60300e803640c022a0b1b282002c5a04545a80b500000d045250040c107a014281e0207440709550b01082c01c0000a02c0180002c071886004101c8000c0c2a94212004201c40d8000403240a90150f00600c081001824481e0046400c24010544103003401090050710f0454101101d0046e22540c01240030001c5080c010a429040700340c900240c1854a04000c800300700c000030400241c484c805655080803001c0f0300340d00c03043c080301056032000c904400c0141403a0196100780b004031003440c9401043c90940088402c0f000c1500c8690340604409040c030226441080c042004a0582d601d003001002d0000c1070303a1050f61850865600e011501d5850904040c00d0240b54040d03150b4004a90841c8211038120342040b80c05654115129140081d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 711044973 1250 711043723 711043727
    0x150105040b0a03120305060109080a0506010b07030e190602120307081b040b0409020c060702011e0c1707180806011203050c03040b031305060105041a0111150c0c060a090309050907 79
    0x550001c1c0503c40210344091104c0e130300da001144140c800781c036400d02c001d554002c1e0030746d18100e07140050710582042d0b0050000c0c0c1da495005181e201d01914105207503140741c4c0e0010308099000d211841c1c1e0740100341020040160180b00302017100110403000e41c00c0d8505410b02600c5c5900003451240f100f01a40c1185036402c50702e200f590050a2100440e8cc4c4990b00da003803c000a40c0403840440042c810000058021132050080480390b40380940129600d0841e05801405498402480001d01c60034414440e40a400701d203204d03205c0c80f00ca6131002090140c10003030050005042d001011300c4d0300300740018040c09580180007c4181d034940b81540e51403003800009800c6001c2d0381c01c00c000c01c401c00801d2004400800c200d40003501d0288082d2105642d03034004001c00c454201090300c2c51039218065031816036000300c03200311031110a28140e808030154012103030420802169505c0b25004045280099140b040040a9106040c41c400304032001060320b019000c01c040b441680d12411208002440c058 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 711046223 1250 711044973 711044989
    0x19090b0901060c1401090b28020c150c0f03130b150105032a040303021f23060d02100f14130306051b0a0e0f061309020a1103041502060603150105040b 66
    0x942006540c2d800e82841503040340e039502d603040c00d24040c0d030802391000f4020505100f2520120b031550001c0160500b119000280141c00070043c20900005102080202c2030b0b503001140b090500c0752031035000d00300c03e18140755842d00107844075a2031021400780ba1850f0b600102101e4026800080c544030700741c00e0000d14544d030704582c1002c0c2e100070790110340041010380002c6c10380b20301004650a005076500b50340010080b1074408070240c554804001600488403013400d00e05400c024051704c1c12030b40380e20903004505101c1448005900041e00c441036000e801d0740c408060a400c05200b40b001d0301d09180f03031803208841c2a80d8080500059501d00c086914030440e01548070500504030355980c1c0321350f2041405810710440c1d40801d405002c0c42403081884d450f0480489042c40c071100d074000b124a0034000920025045050000180f00749034000106159007000940010000001c0c085401c0c854036200904108000c0c2003103000c1d600c18104880310b0a00030309141e06650040d00c0000b421007002001480b04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 711047473 1250 711046223 711046241
    0x3100f061a0415050a0507110d050604032a0201050306040c0e0a090c0906030902280f140f090606070b0603190b0a0b100203070213090219090b0901060c1401 69
    0x1101510046212a180700c000c1c004503100c4001c0300c003500d10309074419101442290780d031000040082006200040d0b81020050300e4001c0a0b00050340940d4a40d41c0c0382c641641503a060f00400c04c140101c0300707841042410010080364042d01c8804840240d07002a0030341c04058141d510440c1c581c10080b00e071520a0000c030344684001080d69208a07030b1800b428004010f00c058000015440c0d4401140040c024000c582d0050ba01800c070003884482c02901c00c2161a0000714204000000d140005400800c01c081c00e0217050310b003054500680c0c1013010440300d003913103a1485018484410401603284d0b18a03007601e2409070840b28108003075985000003400c0c070040e10802c0c042c00d96007065100601000050b800d106082c454801c00a0b903000504000032180990341c8d003001a4020000c0c4801070801210105c620000c0d40780c0824149510743c0040e0001e41950000c41c21909600c00800030200300d802103441c4140c0542da503801950601c0e03030052031002c00020180c0410302c00580c0c410850300c00d60000410b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 711048723 1250 711047473 711047489
    0x40b100f0320040312090e04020907051c0e030d0b031b060a05042102120f070902130308040e06102105090f070305061501082514040f03150b03100f06 66
    0x643c0f5101e26158001c000c15080d610002604604003044245840e4030715030003641c00401e201c0d010340c0c03028821a603580c4445401c00c0d5414401198400c0c500c0749000b20003440640728081c44e01d0701c0154150000302c940107020f1074883e074050b003030481c05c3c5d8603020b034600f0103d5000d80e1065a50b40401c8001e0312076201c0e9070302000342084030566084c946051200b00c01042d901c01c5429011407a411010181d030f81d481141d0b151003a401807541080a24081e074020b00030980101c540801e51640c035201c002c8141c216500402c001c1c48204100020340c075151501608140a078180740c40d600300e900b54200072400c150386161007465520390120f4020346003003055681e40d0310b0400c100d84115803645083c9469841c25500303400b80c008030f503030008825800743e10228410270300304490006010480035030000c00904200b5003414002c0c0030a46026041c0b0080c0103001406515040504091031450300402d00007422058604562800c085201c2655001c89c04000c0380c00d142c500402d8108440902d80001d0016a10031a2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 711049973 1250 711048723 711048727
    0xb061b0715050403110f030615030f03030a0f11030108070e040303060b0706090213020c03030f04020a030c0e01140103090519020103060503160519060c12021c030b040b100f0320 78
    0x7044960000061040d6842501a440030ba0f4240301800080e20745101c0d10b90303040c0c200400045481400c4d02c0f9590952900030100c820312100303694200d085520540f540415642c03260300d004004c8103640140345040404450302071035903150084007500c4010070301403410070880440110781814442d80145c40074214200866989020b0703450307c0300040c44403c0040303015250b541c001ca0382d6490184295070b5807901102c080c501e95038899003019660715000b00200c0c1d01c00c0101c0008004140d003c00f1080c080c04085405540f9541005041d120441105c0c03107080c109810b14480d080081c00c049100c5000d851416080040d13030f0b00b80e20040e0050503954101750740601c40e0b42c00b09851982103045840403150103850b10f0182101c0c0401c09048800c01d070040c0700100c0e00340980280010114120304d10300010350701c107507020030300c0010305852010307800070046c000291200e00441c010319151290213910b400413100c5c00c940c940040006480d04030000c007038006141d5074224001d136682d0421401c0c041800703031068181d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 711051223 1250 711049973 711050009
    0x3030b04050915060a1d2d0901060b0f0403110d1e1a0f0f07030902090109050601020f010603110d03021501060c0c090501050609040b03012d0f0b061b07 67
    0x40da46554a00d90000c0c0c11084901003903050a04840e2502640e46c4600c4070f4044507400c4003103800880c4080e21280b0b01d11103e12448558141140002d80060348100c40e607207103802c180750103600750360300c60700040d500381d2082011030320302803541084a0480380d1090401801c0c600d148002980f0400c04100a07108008000540d0180c8201c81000b9460303901c19004440f404010b842c4102941400701c0c3c2480104ca0386c500818000358200c1c0365030350321075254030f0013085e091080d6001c164a04000e03032011815a4580090182c41e603010b1100e072000341d010030020007409140d512112a2440c06c2c0e441180500c15568005084c98801d004559286541079421b14007943c1d107442c01881c9205800d000d440c0e54009220203e805501c03402a42e04880c401800b20781031484010801c40180740c10160194190758403201d0f00d1300010104040f100f50150720071650a400060a81c0c00155004540100c8200345404015095035a42c0ca0584000070002d002d184010011145580d07c0d0080d644c005009041041290f5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 711052473 1250 711051223 711051241
    0x1a09041d0a0602040f060c0c0b030c07080409020714010213050405091204080d0206060d170a05160f0b1f0b0c0a1b061409090f063c18040f03030b0405 66
    0xb0310885c5c4042818800f050780d961011a8010901c02c801001680d00d00e0b01044085250000b841d0001c81d4050700b2031415140d80d6034509075521940c00040910740100d4804140b09481075554041d4800c0d0009503d001503111100c0c0d120340850040c140310f15511404900a580704102c0441030102841c642c03a41c030341d21128440e03502d01e5100c030400b0061003071360006007080c103140c0100311103182d0042036421101403030482ea40383c80d0011107140041050912115400c510343d5804090b8960046200c1140c0c6400c9040800010030014021418164a0681c6200c0c0b280703d00c150400301d441d090403003911100d0300501c044c240f00c44444090178040200d405c0e00c1000c2d003051000c0c0229007a0362203610384a0002d241d1312480b801030b8125548d010280200041901000c0c2c55500e41c014402801c07070549400c0754064084010700c401074074541e5a04940380b5145001d580025183e1000c0849282002d40541c8424030407400d40103000921a0803805040f10070503000b500041d00c51900107005014500c1c00d1403038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 711053723 1250 711052473 711052477
    0x120c03020d0216110102030a12021e1b010507110309040f02070f0308070e03010908030612073606080604030c080c1f0c030b010f0e030703020d030e09011a09041d0a0602 74
    0x1551944c010b094442600d6000004440104007180c46012518180b902214000e40118080d160308000700848440a104d49600806440707284046040441014440316401c441005000c0c00600c0b02c2c0c1d90030001c1c000b100006a078000c860031200800c0c91aa0070034000060f00502d24010001d91445440300304154101060b5842450155072b0700c1c400f801007000301400c3c1c80500034081d010110403c081580c3d410548c900c03501c02c021103012144440c0d40d450403505840d06c0003449000c05044a028002c0b50104107003100d40c081d5040f4001d2140701e040c00d003500e856040c0070f00b000701800518a000c00c10081d03800e05032500003076000c0644806820711058aaa003aa5405010501c40e14180040c2d44080c06803081710090b00c410381d01c0b01d440d103500c4401550b620850011141d4144980040000107940c0c0280084481784a5a90f180c6600340c41d60a01886c50010b0300460300c09060103a41e00d402c081d019055841002c000c807404201c48a1a035507036902501e0f40319000c22140202080c00301031200b5500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 711054973 1250 711053723 711053767
    0x1917040501020a0f0e130528020409380d0f060501051003051003020105090310050c0c150106020c0f040605040e0c0f0a1d09070e040516060c03120c03020d02 69
    0x403220310035a0342c904d0489244600c0d8503c5c0794080c6c2c220b01c101400b00541e9000d42e500041c2d42c034a49100c8548041c80740f0051324a8210f00c65242c2d0002404e0040003840e0040b00e441c81500000c02c0d00d034500d00024105e0fa80703c00c004e40300c0000034126060006a498400f0110f10796000000c10f04050100e0600c0000340c402401468090400c81407940c5006110384141032042d00e243c0300e403941160459004442c103034006a54580e061140b25885241b0040394032500c0c3c020000425003582c0c1d4290b2400076130600c10100722030600604500010410741d50041141c1d034000781c00315136814804080d400090700a000035001550003a2a0105920700c1c40d41c0018040c10000085841c1d1012010070410001ca105550040b0568051100c000300802c004a00e130322501f0242040507140d030143c5480c0010095041190f09a0301c80d0312140f8a0320014014480c594050003036854422030390960394801804d404a01c40c4ca6414841c1e0f55540032015038440d81c180c0700d11400c1290701399a54540c5802e00340e074480b8015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 711056223 1250 711054973 711054977
    0xd0812040302011d1c1808210408060a0203040f0611090906040c090302060d06080a081902061605181309050f03040617041106030106030203010e070c05031917040501020a 75
    0x16a03072102103d0140b01c0844003904c018010f044140002c8030303a40c1601d0841e0201014015141074100d2100b07000034820b00980940001404c4148401520174034503a0314885100c03c0d000100800d001d00c13036020401743d074003130030744000035a0701d80b00ca140462a2002c415009000c00f45440c0010401000c07410041c1a80b0004403050312464070352800704412616010340307000102d458200e0810045c10580c0140c441c00300381540c0050305542d0303080410b083c06040b5404031020a00080e0f00322214050784040f1030390f41c00c248010305061409060b811403085c13a8012000030f1000100e280c400080c1d070964042424000503000c10010150302160700090004070b04203c60600030805e603e240c103200001980e048554542e9042d01442c9001c00510700040090401e0300d01e45040c0c0000752040d203c1d0f800850080a4660300180d4035032401c942102c940d64003814200800010b411b0388004240000141c0c2e8901106a06920308507400d010161455603024883d1013044240b00f0802042c0b000660103021000b80e0390b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 711057473 1250 711056223 711056231
    0x3250218070201051e16050f0414010f020105060108010b1612020607030e01180b0903040905070c1103012a0512100302030c33280e03031201140d081204030201 70
    0x1c0e031203210309054110104403103442c030b40001541250780c80c6c3c0481a4014142440d80c6802d920071460441e0381c0c01500b000128a055044110b81540d12042070310708a4024802080b240c10554002031200c2018460b520b451000801c181407055055981500c1d1198006588444001800b1020f500c555085464501281c9002c00307925003980d040c011010030382030300000c40119204a0340d603ca070a00010b422100f0034030044c000810408142d01c505400b070a0315454000c1400510f2a110845c0300842a13050300071303410a8060713541414100b65400103000d007a0a54130404110348002c5a103170080881c000700040c54079050002080c00b41c0220000d03a4000d80c1941c242ca40c64209014032180900321100c070311500400e4046030900822150860103c0380503506141c1075109040003210f14281c110140480440d950030107216410000f01b60003504240c02644c1007140b214240044264148583c0214440d0001c0d111410b40d644058201030580c02200c8035190203129442e0764401c207084500b10055868 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 711058723 1250 711057473 711057481
    0xd0504060b1306080d09031502030a1805010213050a0303050a0c050c180a05100f0b0a030b06032514120411090103030512010806060d0f020a03021309020102010b120325021807020105 80
    0x2c1056410290b03a0441030348c15500c141d00e10103200a50008244c0d05003d83d940b900b605041d190700060789000340c020000907884042480307400200300d8042c0d000700d1103a42c80c407104000090b04075040d5a01c6010340d0418800c0792120b81011800c120b0800c0300c6990000207074001d95410246858182e01450035032404003d01e40c3c40c80444882400140a502e2404100301d41c20004090724000400c64440140f03070200d442d0101c0c20110301c9582054034000c046100c4030004903840e006521001e03072851468540511204158911440b5502c0751a0010f203108607520002024007100481000321400b020f4804601507079a81001030042e040032aa0044090319880005090400094141d00620008025004001603035556070007039926001c00720f070051401000040541d40d004000350f02e41050071000303c2c0c0742c252480020300311104948540c0c811000046454411000002035611440107891495034854880c3c07810305c00b03100b05c450f000b5480000c450704903e104480c125980c1c0940410380082c4681d41b5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 711059973 1250 711058723 711058727
    0x90f05090313180905010c120e070311010302130e0f09060f0609070815100203040503190b0f0405120c16080607080412050918070206060105030103080d0504060b1306080d 75
    0x200b0b5070360300355550340030040521504054000300c09291031140c50015100800b55529820f4852400d0500003091a11648045c0040503015190000546038041e00510f0706542d2103890042c00395003140c2c1059070200d0041e482602d040c950101070702d2005200000361a00301014007540348200e0b0704a66a025240100c1d00300b406035402980144401080200300d07503119882112a280014071003048100089070181c04c648400c43c140403411740540c0074540d19410103061506d000f440b6a001c4034500204c1c0315440114000c0749000360020500f664035803141c0c455042c094076002da041c00c1c1d040502c000044605007a4000074091251217412140c0c804030540e21005640c80e202c04403a000301042c03a000006000400303d182c9044040d1b11401c010742060450030214001d140240d05481a40c0101c109100019404000403603200200f464814a15130460b5509600c500030500b039554050b0311000894200100380e0803181042001401d45d04070f9110300031050010b0509032182084600a03a143c00001038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 711061223 1250 711059973 711059977
    0x20103140403090b030c0714060a11040503100f0905070b040905010b07030206270d022a01090315180501050601030b0405130f0206090a06050d06150c081e0301090f050903 75
    0x68040d11040b0f080c1c0e01d080101c00150780018000480104c04005000008011211080c1c41500d81c2c40180140d15006100100301c3d40321020141505900788010021a6000210041c400d1802a000306100d2441c0f240c15024044101005206004814004c988200d041000d04221546031070140600c4e40e0f00d01c00300c40c0324814084054010381012000a000c600c6000600c40803aa100e014a0350341081c1036005030902d00000304c00401038010340c03110038880d0204084040014155500b040c4085803d80020340045007a00c8024007208143c2c2c2d8030303043c00401c2c1c1e006541800568644a000200700d1410b607000707000031a400b6020910b0480b001155052500c207080c40740e094402001a42039a036100d000c0e41f03540002040780e021008100868094a941c0650002031010751200c43c0c44085d0241110f0a441194222220140d00c06140c0c56040d0342c481c91100032076820200071a41c801404040c0c10500a1148405583d03510000001070f005070f040d0301408666418000802c09030303c3e820103a544038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 711062473 1250 711061223 711061231
    0x120c1210060e092406060313231b0d0215160c030506070206060a0902090f041d06070c1703090307050a15150506300703051605031b0a03200702010314 66
    0x50300c0d0b4a4001201e506110005540006041c941001c8c003a1032950b40c2480d109100307250900703001682061012200d82040f0350020016034801c00080c11807840301256601900a00c0030780302d070386801c000c409009504000c403440100c03084600d80f102c044034103000000714001d00c002c0f1039500c1280c0001c0c5031140b0100d0040d014250060071900624600b20066010b0340150070543c0d4420040d411070007140e941c510640740e0035248000e0181c0b4076403121702d0079824107600800740d10620030210110000120417103800400040300003007807a101d450300c070080b070710318012400014000d01c1802526400d124204450407409500b0070401c0c8441403120001d400c1905c0a885041d800180a000300000c110022000d2580340d01800c0807414232180c10f106541043c80c054070300c8404a9654020b00040107804031542c400e450030742c1841c52131800c1003500c1d9140d180180e1101814800007284c18101035100e500421500d80744810b05940605d0b48c038140168a9101c120700300c0c0844c0c0350142100740100c52040319480703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 711063723 1250 711062473 711062533
    0x24070801140406050303070f020f031f1808030a1a040b06070b06240a1b0317041e0303151d010311010302040f080303040b06120c1210060e09 62
    0x25591030304900070000d041250080c0d6000751a0800810a501c04002410005000d074040080051580c01031180700d00c0304103500c6d0300075085210303c0718140700c2c030b90fa241c2c0c60080b084400240e0300c00400e100c561440c1d22038100030304a90700041405819011500810078004004001c0a010882d07001003008960f00c1d2490784e178000c80706110007408143c80182c40d590203200038109010165000503280c07100089035899070030b402d00200303515941503444403003602ca1414440100020100300e440c00381c004030b24030b02040040d8010300d00090800c002b000641c402031140360440d00c2150305600d80070340500068414140200d14100001418110450b00d51080c00c103118900c001d540d09540f1185584284000c226040c50380030440050855420100b500082c004003000c0c0d45c0300d050600d401c021100f03024011511503811000030155965004c5031198070007000310341481c00207002560050401e01c04400801d0414a0044001801d24198240520030082c400c1924545202024440e1a0051404007201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 711064973 1250 711063723 711063737
    0x2070501022e0b060f0a030b0402070206030f040c0305010e0708060c090d15060b0d060509061807030c030b030d0207061103030106020d030e0f010509010b0a0504020405090609061206092407 83
    0x240e400074040501c00200d04558012640208800101c0c24503404501511740894000840b1404143d1500c070341006003000721000c0d89040200d070005440c1c3d010140182202c6c05c034071030104007000540350030310b00103584c040300900800c3e1941541e2034031021240320b040301d240203080010360152045001c03141003c0b80200b8021030b58405440b505041e001400b000b0300c00c103690b044c000c92422020000740083c00240440407c4180c100410301c1a210f001414241c011442045210248840f4080082d030003400340c607000031440010346048000c2c0910340070041d058041c214102031056404643c44098881a45840240000980200c1e80d01e1009210b0800107801c540c0d00640603d00c01c0e003103038401e888501d04485880c0d080c0010942100c0c8282c0b0740c02110380d95821410040d092940b0210700034107045504505041c60400420300001000300402d100301d2502c0300041059a03950b0341641c90341700040449042c2d1134907459459030b03943c62408010b0f02041b55125085030612140656129140507515a1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 711066223 1250 711064973 711065023
    0x1507080a030c02150f0106030b01050a0207050603061c140f03070f0209180f010506031b01020a1244150d0326011d100b0c01060b0406020d0207050102 66
    0x6004202e504040710031405064003a9441c040c045015502420080720426a5545442000780071140f0074005681400710a02c400c8000540100e0094200c84040c2e0f03816580356a000001201c480028810a1118800300003c0701805a0b221101071081d10f00000c8402240100d1415030351f0307000e1020020b01c02511041c0d030400501f040042e00d0340241410090540c02d4400f81c440c01d090005c00c510110f40d9030341d60b8041140e94035003003200c01041d4440c1d00d0680d444100c4040001d403a4102400040c19500b0041c41d52401d4602c07038858056015030341002d1a00702e41d103101000e851b40b00e02c400324000b0710351a04100c403c0b244100740710314002c17008440613101035a914020700c07490340d580380000d4050080e12000c203500b10503291550101900c01500c4e880040d810000f295003448a82c0500f180d03803110190070811040074488401e4151080c48003c16214009101c4880c0035003465040403501c5c150101300003c0031034002465a007000340c15000c7c0c0c2d1900d902c5000480e92580000032141e40d01360790132042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 711067473 1250 711066223 711066227
    0x9060f0604091e05040f0615050d1709060412031d060301061d1e0a1e0512121303020108130201080a020a020309100e0a0803130311040b03070f051507080a 68
    0x4140389402507420f00c040029003100714046500440e000d503192200854000c0400859109100115800111078070030542842c021640d001ca14000050107810f03d40c50440043c1c00c40001c1d550000e02c004c0c1001e681e15141c40342c003500603403280350480c0864441c01d448000503990202e0b803502d000c000303810b8504503840c1400c1100c2ca0030801c150b4841030900c2648815458683c030030b2500080424603419610a9080002d020340040315a01c05e51100504031070541c9100340d100d05040c116541112009180120442c080381040c044107415142d41d04001401c400c1400b40c85a613800b264000d072154240341e1707504030580007140c00601000340042c07110030018048454a902070400e070621031044904240040b00443c4042c0d0040d03d910b008260405900e100c540b400b0100003003c7c201700d41c041c0d030610000d0b040903100403d550000400d03140c102d4146000e1511070740d01c50b00c01c01c1801800ca51a0b1950360006941e045094000d02c0c0c0110707568880301400361034400c01c582e441e66102c1c800d60301c0e20101500c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 711068723 1250 711067473 711067481
    0x60309050a0321090b100e0402030615130203070f1103070b0a020f0705060c091908280b0f04110312030a02071a0a1a1e01030f0b0409050c09060f060409 67
    0x514040304007865003c0c0c0c031801c0a803041480d00307442a1082e40817420042d49807901c1101c0c03903200c0b0100c04500030800005807804104da40e00300407800411001590f0803400a017000c0024000b55072100e1020040264069100c00e099134500880d07254011480c144022044d02d81c40f50a00280250405030041420b00949034006c005204800c54164284800c135034820b42084420307181c00580c41c00108121400d840d01d40e110b0b0300c51000081e403c00f141d80c901407416031909544001c840c02d101c0c990360440011803000c85100c2e501035000958040501d804503d02c2c06680f820307501030700d03258013006e218181402d0004a42091100205800d811070340e90300d902c40c4c0a50300046080360645462a00e01c200610444000341c011420502c011501a41040324500c1800000360720034411000d040380000c0c030f40710300d070055900e42d1428030307010583c00c40c00341d44140500344425003140c000380350420700030902c030010481d444c5070641241e544c64240c60320020003441084071144d0a901c100104010003d054a82e84 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 711069973 1250 711068723 711068747
    0x10608070e13090b090d0903050709020702010c1a090f2d01060b0c152401080603011b0903021305010602190c0f030308010e070c11010f090312030e07060309050a03 72
    0x982d01d120202c0003a014281c4446040440b031103410f102c2400f041940502c6591a40240740c1b800c0207420b840d603100d01382d4a070383d503110ba01d00042d0300080010a5920480c6104070098000340c40c460346101d540e186241c9018201c0781038045005805030702c400140d02040d0b60510241e004030002c00c48c0c0d89100900b8800c0c400284a208075903032802c0028110207010040c104503540d21010b000603400c440a01d4085400080200030113543e03c0d2100d6400c47c0d140c41c2c1060604a003860058441c2d503a14004c01c1c0180044040030682402403500a001e081d48064207505991090b240009070102c01c035000c2c01500c1081c043c27040540c00806c01d48009800585d5481142c5000e1345c01030310019036402140d91000ba054200340d000402050040c0401411001e003d0b40065a5240c07003034001c065916207094092105034880d04100d0220300313200e06076100e80034810103180c114400c1c03102e8500c200c001030f009014407208a00305008a4100094040c007034481d042025800c400a000781c0310b200c2c7c8c0c0854903400800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 711071223 1250 711069973 711069979
    0xf150706020403330507020303011a120c1c1b050f07021e041508120a170114010306140306061509041d0601080d0203040506030a021c0e060c070317060d050307030207031703010608070e 81
    0x400cc1804215000b00700e01d00605040700401e0b620600384000180c120241104202601c0c100b0306591000c050043d484032842a00c4d140082d114002044024803510071440c0c00b0394441c15241c00c038082e4903003100d5000c0707010000310741c100520300f00d100d90903010041c0c500c41c0c0c101c140c00600b840035001c58440c000388211030b55440c02000281c00d121400b40703010741c2130300302600030650145003a505507054810480070384460441025540152000a0f80d50f030401030105008008403400c5c010000e0b014029240150030007401800710b4084522546141450460a640b5070310a020000071400030103e40cac89142c2d40d180d40a54a4641050188a126071010f46403103842c5d6400c01981600800c0a803110f041e1040556001c205c00a01d140c3e181c0c0381002c0540f00b0390801c0420412100029080881c0c0030741803111441d00b5801e82d0f6100d0014040382034a00c400391a0f8000015640200340e070200382c03041a24466140503c00c0c510b00044000c0500003402104c0110f01d54401003800d40e4041c80903601c04e52802 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 711072473 1250 711071223 711071227
    0x5040c03290d02040b0111031b060c030c0306010e01090b04030302030d1508100c2006070315050102100e1504030c0501050708010302090a05040c05060d06030c050f150706020403330507020303011a 86
    0x491500c8c50740103550b4005c1250b010a030510201c8401d000d52138112020411060a504045800003031074400600301324144480f617034141e4140e901038007043c4010009001c005484a581f81000380d225400483d105036514a081200d00c900c1e511034140c141aa1140b0004001003882c19000600501c00c8000890a0241510045500700e4070b4002041480d9101c40c05840d003800c0281c000340c25207035680009a1040104031092080780d900240c00303003005a40eaa40465505868064241050b110030f060b40e085410300e03000c200070b0640201e0302410f058403810007041281e683c18400c0703501e00030a0000951108461000c110002d00c540c011580044c010003020b031443c0d0303844001030015400300b00c0340e8615980300d8104100384800c140d10320000b840150303017a20441c0300ca00c000403010520410000c0b0301d488081207410a0200c03d80c1a9409075510044824400b10580c0c40a54070007a81040c080554443c03440d455203114840c062180208081c0d00250300316403c1190f50001d8001000d07002e180a181 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 711073723 1250 711072473 711072497
    0x1f060b04360c050403111f0c03111203010501020d0903030912050f0a0308070e030f031e0d0608070e0108010b0a05090a02070b040b01061e2705040c03290d02040b01 72
    0x21500c03408942d4a6151100e0395a14954908a066090312401c001e102c0e5903000509050305600e0006d0100003400c520742250000207034035041d56025a03c020076800b80c418900714428401c250300085040e40c600b43c084889113090fa81c011184120503000c010b0000710040810083c4003904103c0304242ca109034140e0318001c2c40003900d589014101d060a8000070042002e1140c0c0a13013041c0d40940c0341c8015406410718519030ba018a54030711440c0380e081c802010840d00c50306402c40403000d50b28100c0a540c014030a40da900d01c1c4045d40c9048d40d000e9a941451140c00014a400052040343d100e103601802e0540c41c28604420881002d100801201515400300000c000055003900001d00c04c80c07040c40082c14a505242c030041c0510740c08950f5003086090280f441c5134003504040c21103074100501c1a400741c0c0c10844188407400c0c10386d40c0d00007a0000c2c1880001c024041d01a0003281c0341309821101d4200482c89804031413000e135840d24255070081c1e40c2d510b01c07101500702900804140319043c1050034451207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 711074973 1250 711073723 711073829
    0x4150509100906030b060c03030f0a09021804020315010e06011206150c0506100b0f0306031207051b01021b01140f032404020a1b02030f1f060b04 64
    0x1003180314040002d00c40850612550fa054410901e20a205568650400d1340c004416a50307484064882e14820b103190707000a00949150704000c42040c8e02600d81180c80c800c0c00028010f922090750200e01c01d00030100442c0305024002490b6049030a110700e0921182c80f1100107482c051040541180d004d40c84a0010035201da032015040d00001d00b1342d452035413009540c101507040c0030000e0080d0040b0a8510401c01c00c501d581d00550b40a580c214511640e251203400000340f400a801800e00600180400d0079000d00c080421b101e1011422603c549503400c141e003004907226010107501c0d11f101d40840305440074031352003003448005403413600120a1404843c0c030750344040703074100310390303284010340c0e020b403411448840704070342c002407040588040d030400342c068002520304115034a11034031404c50340741e0000640d0740c02c0290041003454a4261581080c2a100c0e25034240c90301002e40b40c0c154282000040c240c2d1440d0100c5003200c204040a21541c05110207020105800400905c082c0d007a070461560405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 711076223 1250 711074973 711074989
    0x162c011202031008010f05060306063f01050703060609180e0601090b150703090306050723041a030c030a0e0708030c03090a050402070203100c02030d020d140c0a0504150509 76
    0x20441c9003581d00f5103890501c00d5400d40e501c9000c1d2258940c00c09041c40115100041c0f1103030050f001b10765500b0791001c00010b140160b20003034a12004044244450a031a18990300d0441303041400000074010b40d90350303100a4040d5050340c803519000564082c801c1220060f000460b032401c0b1244800450b511b42c07001401807410000780c210f04030319951215240000c2c54000c802c10404000410041e0802107551005405400345110241c052038440c400140e266100e641c02c0000303008641030b207200d1013103004462059908a4010703c42c0b01e017003203134205011001020550381314080c008005840c0d6a110f407078030006400d142c00d81d01168403600901183c810410b0010b821030050074002140c0358041e444c10815146c49a5100354000d03481084000b015807800f042100000090502c085074040c078040040307107140306190003803c10078408581c5071700301c0100703030004100840c0d503c50109042c0c49402003004c8520030201000046241040200000004c4061507006c03480e01d17003042410108030344c0100e1400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 711077473 1250 711076223 711076231
    0x703140f0108060f01061d01050d05070903201c030915050c06070f0c0b1009180b1501080403180506040b030907150906050f21162c01120203 62
    0x2200c0c8020060050207000c101c11a40300981041c0d0345029490030f8400b900b44a641040c20000c00541e00e0b280c0950790091040b16000701c03004604124602e080c28004011311684e00084032001401d203000d0b41e500c007000064540340c210040c180751a40e83c1320f01c0100c00d801c40300c410840030311906107400902900092444900c508081c2c4036655510b002d039a080342885c6000300b0200034040c14014689541e0b0380040d211a2641d0b20141d56840307030b110000c1c1d00b01038510a0340486421414540800190525040b1031101030b0312895406060303466041c141d00b003951240040c90f00044803c00058082885141501e10383c4049240d074080701074071000481c485501603085280030b0007001003441420303c000c102d0342000b0114521507680003003403894024029440c41c03060108200307010030506502e12583c8211020021240483c04850f224012880c0b4541002c0b03071f1074808140341c2030441d003186000704034082d038101d03c058072956070540c040d02c080361115210394810f04104d0343c03d0f40c070203003000d562000f1409 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 711078723 1250 711077473 711077491
    0x60e010b0d0c0201141609091826030402090408120a050f060a24021204092408030a03021605161a13090b06071209140423070314 57
    0x18a0003182541d5041d50400b558140071a890904821400c4010341150350300443c8001440144002ca490100d80302c0999401203488249402d9407a16100c220703d0b41550840c1c4140c10f80e48482c400c0d2802102810fa9181c10900031100400002d401858030580d9140c2c01403117621b50781d041c08091340d403052501d00c00301c9908000c10340d10000c1c8005100c4c0c070789405922035012514502440e04050018180c00c2100540b00184460100c007110068000d1120340982c1900080581d101c65403070824501414600d040c0042e15101d03565543e907900301541c0048181ca020900642c5401a00c80d01180203512010701625030f1007200c0789a00c0052001d01286140c030107014802e030740e014100a500303114048a0a00900c05c0c040c208100d20002e00030050800441d40627203400218815035102088951241e11801441104c0750a10241900d400c000d00350280c401000d068403541461205100c200c844003403089400081e10903e5840901801c0d000a81c400401c3c075001c204400848001450b051060340c540f00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 711079973 1250 711078723 711078727
    0xb01050d02070602091f020c040506030c030a050604060b0604230609041401062c1905030a05100515032a04062403050601081b1b060411040209060a0c0204060e010b 72
    0x124074580106c402c2c0409202c0209401101034a02c00a951405004030f800e000e030f81c4a1000881583d000d0106550703501c80038054440150b0545440c58031210300319801c841c51890320740704050307504184d02540e080e00c99a00407105128088105202d070340e40c20800d696031040d020044071105d034039140508101c032001401c5d82c14865040840c090000910380c0000d2043d01e9000030410800120202891819003055507030780d0349003503240c03584541c40b01d10b90001034041c8601030411040100018240c81a801e05800070042d41c1c88010100101242c00d0440581c542e0000d41800003d5510780030f402e0780301d40c0e45103a0144a805800226041d20010741c0310310806541ca00076103000500d024012070848082d4038081003285000000640840000f4020543d071480f00c40001220b030b600881241d01241800c1c8881c40600c041808894ae0b9070000c503000c071020007501011030690305080c02038640740300000342250300b07000100a003180d070800d8030581a80c0c441e0721050002412450040c0e201c0c0030705185a551a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 711081223 1250 711079973 711079987
    0x40b040303110c04200708280e0906090414010962130306091511090f0a090e0c120a030503040803040206070c0f060f140405040b01050d02070602 64
    0x43c107061800700f150340034508046041c0c2c00b03066210b4500e00c1c0e03030740e0008840381c8404081c18002424020501245031028540001488400e80b428038420302102c0d030b64070107804141c182d042c08038804050f1001030b00860300f0800b14001a400f1140361070207010000000440e080700742c50f145112040b41020b5003009c450b0b4445060415044c0d034406600140c00350b402c0c00e051120400d01002c240080841c040c029404500c3d001d80c0b00303002d1003160040803980180500650b21b03820200c0c02410032000441700d0807500c503809020301c28a40185003110003c80e441c10300f4400785405104141c41841c40e8176610607030300400400d002a25116405441c0d00c0100281000380c001e50501c0201c07141d641420449074800d1146400082d0b119046a5015034003e6406459484070b20119201e4000c0c100c0c001e101110090b804210207503d10000801c4451315900d082610400d0b610642d500754100c00c080c030440c08200014402403c00350400b44508106241207480c0100381050038040382c010200071541d03250006101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 711082473 1250 711081223 711081257
    0x319140f07121a0603060319060213090e0703331a0307080705220c0305070e0d0f08070218070f030f050609040f06180b0915040503070f0503040b040303 67
    0x14a000c4219803401c00c4984054141191640602d8030011310031a00080094000d0301c06006210b19031404a41c141c030f0f0f881c090701d800e01c0690488603603036401181062001824407024042c000d01c01c0160000703041c40e40e0458480000407492074081d40107003810007504184011820401c4150303000400b00010b2a6406140200c1e00d00d04040c03013651180d40b148400b80150343c404600f20742240c0c42220b03030364000c00d554421b10425201e501d8004d1046403a18011507190342c1c254000c907114104a41d45c4400d0360f20b03000c08001003117404400140c1268100601c94000070140070082480900091640c0401041e107406440a80c1b01180c80d0320000707481807180311343c030790701401005a201d20b034030380620040c0741010206217070740b400420240a22008402010512115a103c0740e40d2075081c41301c003280000c070383c00c1c00c2d50b518105845002c1c040c410b14118400b400342c5809005e00450307002c00a13520307100150315282c9900b031100c0d0041c0e031b040c001003200151510000f0000c10045100313489440604e1000c5e426 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 711083723 1250 711082473 711082487
    0xd0b1f080603061303080703150909080a0f0801120201030509010f0510033003050703090204020d021c20070c05090412080f0c0d020d0b0a0608041203090302030319140f07 75
    0x580720011364070200e14000640c00c8209250f001c243d0785000142d241c05584800d42080c440d1341700d929218a041120400d02041d00000e0040301959180d0881214140d4400c40d4009024421070b0035042c42502c40c4401584207810075508290f1440c00801c1c0700c442c0d09250001c6034801d0718116106019403000f0010020700400708052400108600151a081c60603850350f030009042c02001003650310310011301c0c80f90103a80031100716600540115110940c00000783c00070351040c07080c0e0045050b266041103d01040740100540c080c03409800984084084d031080c401d079003085508039000c4220050210b00358481100d5940320b00e0080ca400d8122800184016051603009800d0600c0c0303002c802e08203c42c40c810402111010580e03500010b23a60086081100001c0041080003540f00c01c0418000440700d5010311403d0040f80a551402c3c040b441c0284154200d4504220003009a0020b00016000e000708200e0869860ba13050008614500c101c583c88000c441700b250890381e42002c6030700340222541d000070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 711084973 1250 711083723 711083731
    0xb10020607020714030a2001030e0705032d16210c0b1b01060e0702010b100806090a020c0a0501050a051b16030203040810090209070504030201050d0b1f08060306 71
    0x203003045061400000303403108007901408005160f030581500f044c1d14208044414241c01c62080381d5500100001c601900b0714664a03a80080e003440441c0c1d00f032075030100d11030003200e02c020001d2015101d485411420911a88100308070111b803440d061011a400380008111840c0b181c0b44076400c541091940ca0100500d0540b00f0360303002c1c00d5100c28000650241a05040c1c582004510340c8800040c010800c0c400040b4004011b0755081c18400100140170181950040000d0b400078000103060800340134440c0042c1c461540025525000300d0880c0c00c203c810950041c0210b4005443e254001c100a444c0c0418003a048541d40c0d03540e41004503c044034482c00341c12082c5042510a512280c54051a0902500c40f0b4190b0383c20f880d0140500b01402002110000c2940d001a1400701a4504600000f040301d100300340d00402e440707400244668859400c03101629416100d281c01c100c10001da1030010024444020780002c141040b506082210301080d0145c0714042c0d84240c0146003440c10305040c60b202070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 711086223 1250 711084973 711084977
    0x602370b1f0b09150d060f031a091f020f030c031e07140f09030d0f09080c0d030318051009021306080c090405120304080c1b1324090b10 60
    0x1c1402d001c4035010404554042d5000c5800300812000303a40c10218601c542103801c06010702d007500c0060300300d80c1c202402c0c040b280a0b401400c0540d40203407001d01240d200b1070b54125590041d4107543c60404440c505440f00802c134041c01070802d6a03101202e07580d41c2c8191884a40c0140100400c0081609170504400580104104290900709941c000c1c0003d01c24039020070440f040840e8042c001c100d80004d581c00220010103d903601c2000c3c402c043c2084456411000004051560218428200050140314548082c02c0c0c00d103110240d4404400a0108880100118801c080c01d000424010042005944010031300000c0b4a50a032041082d41d92aa01405d100141030200402c03001200ec2090103a07500161400a001d6031103181080c2002c0a0480b50070b030b01031010043c0b000f40242d00014050f40011042180c0c40c20240a68142c87c05002c1276444d0390160103800280380320724564210212100000904014409400102040100c0250452408290f541d9494032083c52b1081c0802c001c2d4540d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 711087473 1250 711086223 711086281
    0x412030819061512020f0a0903030f02030c0c0907120e010501061d030a0816050a2001030b03101a0405090d180b1815030f0912040602370b 61
    0x1216100344443c5009900c240070620f01c0c103100c40c00450301180c0800380460841c80d650880601c01400d581d41d10f01080d400105051111810280000202c1d54107000c102c004001c0401c1c200104400590003c03c088100308107c580820b02402c1c81c0100f09640030351a0011a4075070420744020402612940300e0901c0c01c00a0b0200c0790191408200302107455000320b00e0310380d0341400f50b8070a00c40c01044a00117000384941c41c170710000e1000d40700c0648102c403001c485c012501c0709034000460560741c480b03180b00d0349a004020a00210161030f801546000703907005605801c10481030020b01220f6003110036001a40007400176481050380321480540b01081d804070800307010308046a04800e80209100030b0410740c0b4840b00071707005648000002d122030805072078a5036685840c0352801101c080545d41c001d8103109101022100c070320b1440c1030798180c4280ea40245000f00e660f003c4184407040403080e8a81f02d11480219103441c250b6100c040743e05038081c070300d01c0141e0b081804401821101d0340c99039242c0c40e628 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 711088723 1250 711087473 711087479
    0x30a060e06220209031e0106030b0a0504210e0a060509151608070c0909110307080d0c0201051806070b01180603081c15080c01020c3003041203081906 66
    0x80541c00003a0803048000584400701e50001c02c1c50058851056418641106c01d40c0c405864150000429680304103024101615680d10000913210199001040e0f00d02580c40520400c52078042c03604240040d1410008500c45000442e42c13034009a0000000110000740800803410310464255610200b48122850700d528882c2c240003e02c65801c00410f1031400081100a20ac06015070601a0020074001c009a1075a032504156400d000b2440900178002c01e01d00094401380811003410880d40740d2640008078940c0c0c2d004503142d60200c1a5a1880c4c00c5e00914283c9a46408024003082031291f0700c000e403a54100240c10368240304099142c40840d00300101840010310701000e40781c4558200039080c08040b50459488041d00e4445511425200303105d00002b000000010844000b41c0c1c00e13005d41d10740120396014088244081c5606010320b91100c018a958110300a40590101d6003100036241007603103848000104403400081500050032101c203001e02181008844000c03622480c4041060b945 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 711089973 1250 711088723 711088759
    0x1e0a060201090515010609030b07090e0c1801020a080f0c070801090807141207140c030a1104060f05090c0a20060103030906050304020d0b070e031006062a020d03050906030a060e06 79
    0x41c0500005148c00412760119400034010103482c005041c207c1d81e00405441c10700012041500100c0072000c00c1c1c404d02c5243d66403940085080090250040a0b56107011005440d008283c0d018247d40c0c0120320a038803000031105400c0c03060410403841218407550310200750a16404410507015064155005a00304152013200c0b1002ca994440e8443d06980d00d54410407441c50400d20a104000c1c5c01d40104855a410005018004041243c2c100c0b0308200e225107402019030144810701a068100d1321010100c2c0092000802a08403e01c451030200781c0c46801c1d48500350b03d58008a03280c0d0f5980c0c0188018420183c101408201800300e80c50101c0c1036140640000707400c114090406401030302400042a020740c440c0746081003009024003210f00e010300c02165440101101d1240c1000aa5140380c600c0700b245154400b582c1d02081844038080030307205a0200000f00031904801c5051200401c41e01049494090143d40b190114041c00540285080d8208000c048000e040304d22070b0b03044800a02001d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 711091223 1250 711089973 711089987
    0x180a0506190305041109040f03120c090b0d0204182c060610020708070803040807060c0210050c0a02041d010606050a02031b07030203010915060b16021e0a0602010905150106 76
    0x70034901d00030605407282d0074010020348110000304d402c5162407040209208010000d010b0040c1319550f0001070b00403052441c0226030160035100002000e4410400c045040707507001e0711141064420040c81d1594824400422512003101c090603281c071044070f600d0780a64410801c4005016002502c840d0000c007000903111a0014103040c410840760110301542403082127203601a00c04207048030f00894640c03606a950b41c00505c1806000c3c401c04002080180c8a002d41000107580038111054402c60302c2405d860300e0f00005100b100c188038220411025956034023800a1480c846100300517002905804617080d0f0300b0b40d03045001405000c00024420b681e0020840f00c440c50603090440b001607010304244d00341469644003a500d0b600b003005442c14024489003001111003014820800e40741da1349100b11842c0030300021041010090303c081405030411010381c4e9012252240ca0003900d03620320002413982040b68000d0300050390340c0c845a9040010030845000200051880c4030020342c504180101f440d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 711092473 1250 711091223 711091267
    0xb0301121b090612020901090e0703080d0e060a1b020c010e060702061c02030610090510030b1f0201020903010b18010303030c2a15140109050912180a0506 68
    0x4206800307051a86000128991400b4040401c0284100390baa0940e118800400da0b10591040c15141c000080e00f4010307104419201c40a200035001f598915202d04426402c000c1040d1b051039114208100861002e1105620812002400041206412148401c0c040740095440159482020005416a0001d41c1f5800d0481c0443c1c803941e4408a030b00c00f02e80710340121218905030030060000d0480200c041e40103980f040038281d030b020300152030720301040301c00710111710909070000301107075008200d5440ba8200603020000902420030704c406110342c405c030100c404044040186d602240700d504520b407c4c090102e1003030b0200d40400200410130112000103c042c4001410705035140c01e20000e41e40203540d00141c2c0f03200f080c014210015004500900e0401c0000d04884404101e450482400103a11983e03550501840d80c1c1c1825a00389045500100b5014113100e0480c892070000c003901c1c055190045c909010304034205603808000500b4890591103681002d0310030603003409400442c40d0904819025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 711093723 1250 711092473 711092483
    0xd030c17011e050301020f1902030313060b0109030f0c03050705010906141e0301030b070e120c0409030905060403060209040605031c1b170307020f07050d111f02160b030112 76
    0x2420140442882e074245580841d40650001c1502d44440c0746406c0a0106a10071074004401d10300d0078101242c032403004550045800000c40c0320000072510301e902c481ca00d00c00c181440280f4589a0320b40e038081070b02c0303004200c60701e9840d200c2c1803040003c18040399009141c00e00b40088200c1c00c0c5003028013605070740303200990303c4400450410084120094182c020042030488150303030303585a0502e401040d0088880a0200b40c0109000b1410305000c0c001350f901c00f03210406401c89072904800c02005d0070404c0c405070204403079a000882c1554407940140011480b6800c016a03d8258006010070707a03d05611441c070940018240b24244000d091050f03d94440c14a88100c0000407181078003070090301a4009400d5101e41a0b05011140a13000250b0140c1104d0b000c40e180220740c07071041c1d680d03040540142034010003901800800613042d210100d01c0014001e11446281401c00048c4100340140d612050041c0c3c064000010f04442078550382c005031803d4415586191f04000c0d543e10b0311a03000364018a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 711094973 1250 711093723 711093749
    0x15070803040627060507080c0f091f0309020415030b0c0309190804050103050a061a09030a05012a090b0414180a1e1401030303020c07030f050d030c1701 67
    0x200500c0d03a1000200d1150309815680280503200f44810255040c0c10403500785141c43e01041c00580541413007803056032980580e0740b400c3c0216000600c00d030000704040350802d035908a40c8280d42076525805104c03003029540001d03244464010801a10190034a0707011550a0344c0060001c143d0600401d03510500c040250380e41c946602d801c02d032804035585080050f80b40501c510004008500c030050081b16406d9030180300941394054104c0c101c82103031007003036032206181d12400c140c0c05003200501583d92005054554480c2503031110760030344005088030043c40d0059880191030780e0f441044065040c4940c0b5054411500f0003136103610500c92800f031480c0d0064400740240c1160fa8801d00c02e04401c1c0484580300990800c005064081e0080080e041d8101d4454603803030f40402414803550b403441c5400107a8100f140d10b1600e042d0000e5011941e0441d8034020400d012000c940390a50142c2c0c42803040008040c4400ca02c400201150003650002080148505404850340d028152043c19078802881802d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 711096223 1250 711094973 711094981
    0x5161209080607030c03050108160510021f0b3111270109080a02011e1e1106180a020f0a2105011506120e0a02040f0207030e15070803 59
    0x28885203095800081d15104150400c00300c507134181c1110307040e0380361902c09015690f01d032200a030315501c00c6600028480c80e1035030708020398540240e82400c0e8040c02c4c01580c0c4821000048025140701c0c040049a0241d102d5500701c0081c10811940c031050146d42c44401c0b80450640d00b040d0800746800208011030381c842010f120448a01000c0703624a84610b5411074528070080d0090900d010000505030108559150000c0c2e04030000c00c1090280f60305a454104150340005908210801d501d031400030000c40b2890360a407040c01c0e00311500014401d03240c1110140c81c1c2d4040a151020041100c40c014203641a0041200710005495007101c2c0d0448071401d01d141d020012807e041c1840d801111a00c200441e100c851159100c0950881800b400080c051440086405507040c02c0300d10030400012008034558500100681c04441c0c201c00540c21340b41c1102540d0000b60a54281589111840d5070004c4d0340410190044400c486102c42910780381440000092158114014860042c242a90020000b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 711097473 1250 711096223 711096227
    0x60504230a141f0201050a060f0f1e080109030c0b060f0a03240c0e0312031b030709030506010e07120902150f0c011b090b04080601060e01020c04141501051612 70
    0x1803240d090501800c0c40f002c0c550304000078040c240a5070001805454180c01049543c1c082d001c45098a0040803429280791030540481c84500c00c1c7c001d8101c850201c4000070034000d4080c00340084041c000d0391507080040310784c02c1801d9840340c09400c0502c6801c1f526400442c5d070302e07002c40e841c0442750172a031221281d02102312001400140c0744079240095141000403842036402041411001005408603005042c1d0403111a402d48019600c5225400c004c81d484408801000011948012586005100f0a54039600d1b546000e500383c01280c2c2c0d0805d450200f11344254030042c04e0f60354004024051140a40d0368002c58050710705000c21b803480400c0007500395180c00c4201c007200d080c410520020040450003052030179000300c3c94111900040d01c0700400054101c0c119080e2019100c5000c00340c001640391150550b140c0303040818450541c004c10710550b180e5500c500c1040c10204080603500ca051404504403d00d6006040e41c3c48d0610038103101040340700b101f85c0701031140198001007002e400c202090b01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 711098723 1250 711097473 711097489
    0x181403100b0303070c17010e0a0b0402092802031501022b2601090c0906170a140a0e0f01020a050f0906070c030f0309050909100c050c0304060504230a14 67
    0x201411501c24905c0014a04155a02204651070414003c00100c9484808141c41e481c0e00d883c0503083c182d01d1400300d0098641f4076081c075005034140b801c03140d000d40040c84bd102064214405c41040302d03404800c000030852070343d0b03442801c10000d201501c200c1402070800405803a0550511701c40c4000d07038200441da10f0246907211041c0d1954100700100d40d2540e03604040c00c6409014546207541400e59912029000b0441c00c01925240e8941c41c5400c500491080740c600f00007483d2495580d118210300b4401e50300705d048940242c01800740404c84000c458070403071030581c0f0485d00da01280c0c4100240700c003641e84001901d040e0749480600503501c0e00e0341400107015018a20000d810b5611a042c00801c01801105110049200b03443d002495135503a0100003418400b02c400c0091034118940e1101005600d5100784c2540c12301e0b08005050054042c51039103990050340088001c210005002e02030000d0107401e42c8402c0c41080e80c040a81c001d4000850841c245034851040d03c4003241840c260142c1c0c1c0c1e13080d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 711099973 1250 711098723 711098737
    0xa050606011409031b13060e090118050d0804020607120c050d020718050a0f180c1401051623160b0c030912010b0301090606030b0f150d050c03030a181403100b0303 72
    0x5c010700400d52200f2303005c0f0000b0f500740d070800034941c81c140c1c42c042c031501140030f4403003141c0c1c000002d00303400b00c210b0400342ca02c00f000400482c0d204c10100001000101d1000c44076401c610340e6a40c0080c050100d140c414a45085440000195808003c1c01c00444242178400040303610f1006003c1a01c1d1248040c150251000d9200c11103218102600c1044030540420b04070744290050510804c819507500c1d0b1461240c110b001c40c1ea0002e94108915071081101841e0722810700d105000700c41c891118441074400c031018880514038907800c42000903502c01c21a000f000054083c2c440190b02c1e020503d02803558905c0b4080d2460300034a10700c1c504103a90074081d44000c0030f01c100607000740401801450b000005265074041107483c4585480410324824038001e4003403050500c0c2070301910701c4180710304110380941d4500c0100e40b80e218043c0d070302c1c03101d4601384040c0a4507101c5443d49400c00f02c0000522200600940014920845000010050342d40010304d24900c1c1c0d03559076000490b003a6400c003090440c0f040301c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 711101223 1250 711099973 711100009
    0x9010224060d0f2003120702130b060d09051f1a011b0803010b1e030601300e0f0f0d0807031a09100302030606030d0507020f04020403050a050606011409031b 69
    0x5010490800d84100401c4c90803c801c8041c0c8100086920594846018007800650803900b1182c0926030f8038095888041c038040e00904060501f4245005c2c8000d4034201079044900c0d0300401403078001100c48055003401c003802caa80c107100e0000d1080d1000d03104c003000020b203410484210030111016070b1200e13582c0303010354002d840640d40750f840303003402080c0d54072540124205200340040c294800006400f07490003260140c0d01c2c0181c8140500c41322840d91209a0400307072450140800745440c000c94424242500d1511024104201701260000d0900071450801610b0b134001c10007a184881d4400103180c1d0061042c20b000882c107c1c0c01d404099880c519607130150700407100e0b03c20f001256a0103490030045a1003142150b043d07a03185c03000e25440d003e680503034001241c020b004260051400840405401d50058401401c256a0761102890301850500940d03554010b80d0a002155030300c4030070354207072a8005224918000441d404a030740d030003d4207400c540300d2040a01c0032080760717104000010a50229 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 711102473 1250 711101223 711101243
    0x40303112b0b153a0b0f09040b070c05011104030b0103021504030f17190e190b070f050a0506040b0426160c0b040609080c0a0b0406050c2109010224060d0f 68
    0x44c03a0900510407000a0362241c8988030202003180b07800480ca034880c50b4003540c0d441c1c0caa03e507a04144e448445444003103c2a540b10800e5910f544c1c00b03013020340000d500030040a0895451030051111022551840400002b0304000c20b2001c46e0404466486203940041c0405d000da101c40e000d9070f020300828420340e500391204901d100070f1035404032113203c070a5002c480908811050010106400031a0f10031020a43d00520000010400d00410746815501603000d403100090a40c1e03800e030600c48100e5007144e40105040904c018002071030054100703500030160002c02d440b091702c030358031443c013515408a0a002402c4050700030007140034034903801021f08100e4071307032525110440903180c40311a0281c3d1015104d01c0306200340601c1c007490f818088854110015140c41d08003c800ca483d1352041402c0601171161501c0310085648503001a07141d8000701007859100c4c20040700081c14210b00700410352000040d40f00c6017400403401c403022070f006581242c101c043c141c40761030300300c00ca0002c00d0300240c00c512003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 711103723 1250 711102473 711102577
    0xb0c09092a0d1503060c030b0307140d0507180603030215060a0509061f050c0c0913020420041d011d180708030c06060301051806040303112b0b15 64
    0x10780d0030800b07025031940c500380501238107036050550302c100d90301c18204119109085684e2a081080c4d5100b03c5c540600b0545249a071109000303c0003080540082003440d035206030030418190b0510083c100d203d884101c0d5401810001c0c0091940c248078082c40380710350281c501066455803001d02550840a001902400c0403000581c0a440340e004002c0c85211401084171500d000c2ca0301d03441d0301d4030601c4100d10a480c1341c160b80e02440001c080a008c0a000030144034047d502c0e0700e01d900c3c00340000742003030400c04035084540d4920304042101a400320041d11002840744c001c04150206803075100d1400d4034081e24131521011418508003066003c1c440d2070100190b60001180c000c644d0320f2040b01e042e80288036544400c2059034548156100c1e1110a4011001140010b88603820403200c5101c0c003072045041510b070410011030087c01e408904c030301106000002203219614040c40b80c003050b045490b104001505001110903224000c0380e4404100000e515600c1c6044004071450a50081110740203c140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 711104973 1250 711103723 711103733
    0x11040314010b1f090b03061818070f08030717090a0306150803030705070f0201140307020604030306091a0d08070c0308042912070c0b0c09092a0d1503 66
    0x402d442c80540108815070048410003200c9001844401d02c560321441e106261084668180c0c0002d4501036104003100d0b4949124001028824020004000d03001155025921400c2c40c0015035030080000302240303d400c200c2c4107030100a803066a5044400d1910782c50400400c1c1c05a8400c1061540d440304102c0d0000c020302034658000f4104010402c0021010340d11921240e41d6400112806000203108200b03400000d510802d8541442d803043c1410000040552080c50003600100d4869005902940801060540c14040c803002408819020031050070749200320b00104d4108492103025000900348081003203032640459001a4208001e10700107612890032810b40d6003e0301c60001d0050885056802001528030400000381100c02164a4402c070f00944082c210300040c010001e104480006070041200c07022007510401c402c10025540f94a0281003140d81c0d03d01070940d80c00c4c146445112854541d00344103109900d044060302c03948502585842401078208601150000c401e00070002003013003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 711106223 1250 711104973 711104981
    0xa03060b040b04090e0601050321040e01183e0d0207060e070b0f030105150c010e0c0a06050c07142101050103031b050c01050d02210702060619091104031401 69
    0x144c410301060051088034012190b81d40420301583d40e0640219007003d08240e039508541c1c40740404d584005003002c0d81e803544500c80060981c0015000071000c0c031801000c0c8a40c1c41000f07000b40680d82c060ba03e120411031440080744031400099003111030b64907400071280c1c4c6101540c06038442c0000940d40ca44403407411001511150134440350502c100e010100d90508844162241480d48803031007401c680c60002001032036000e02d0118204250704001c1d50b00e01e21001c2c0034034080605800003e28400c841c08061104c202c0070350f880340c030400005110b02240d00340041816412124411001916445d5900000703010706940c0c0311b054601004900b01c00181a01904118102c0c0d0180c0c50b0741c0d480d42c10054034415090407070f20005003160082059145998000d03809401075041140d001428210841c1074103c0811a030100103003001c00e40820070500541c1000020740c00070090743d103030322803161400c0c2001d404400c1d805803c1c542c54603903084141c00f03102c41d002c2e13500458110454400705080090713082d00034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 711107473 1250 711106223 711106229
    0x180a080c12041a070c081b09010f06211b08010905060402030106051b010204170c030f0c09010e09030712030e06012103080a020712020f06060d0c05060a03060b040b04 73
    0x74090012100c2280308a202554102c4000e504071040e003840b030700000640380d8420302c412140d2000714180419091410015404062414503483d40e00031505000c10944002c140d002030080340c1c2801c0207011042e440b20300c0c11000b141c81c4003030b00303018041e40d6400d5001d441e45070002041c1c0812941707401e01c12540480340d00d040700c20520301084542c0301d110a03c0281e01c424081d80300840c0c810800320311202600450080d80101b144001420035803501c1403032034042154041102c07980e10040800c44989420701c00030304200646c80007801560b0403880811040441441601e4450416000198080c4401d104849000b58450094450140001400307001450b00c48000d07074040c4588400804c407a0400c0c0c1600c8505400500408561555940c0460741010000c04128001d50280400800900c0300191a40e00049a40141075144030034400d5a15001004100600c214210b2010501090a42c8010800d41d001078071559034030390f0141d209502821036940169122480060b00080d001d90510250082d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 711108723 1250 711107473 711107497
    0x16080304110301091a0712022b050f160516030c05060615250204060b0408210901050904090b01150906020109050309040213080d03051803070308010509180a08 70
    0x84031181d4040c90700301c4481d004000c0c8080007181c680b1841403215502d907580581980f402c100e410743c0e52442e0a00340e8004413015080c3c40c1d0f4804c1d074182c054500c140940d0101c401e0344020801468941580c20034468090000d1100c01407a020241000740b1034000c90310281c01c940b0801a400c0b806190003030a5001c0e864064410f4090b041c04613a0910308003020b2106618082c011508103034110108007143c03020031031200034800c101f524200060701c46000e00c034010007a113a03010f07441d40e161901940c241030321003841094136904100c81e1121070049800b40c038001c240a182258840c207060000c0b034014000080040c110f01075840001840c0e20f80464041c0c29600a0751301e144000e5903486043c2d0a030b600c11603008019030024070000c02a410030754003401502c0300501d046007200d546c420955060107890050000001c0d01c5100b000245c4a00b1b40e140140c80252500840c0781100a4130000c2c01140180a00d600c203280070400304500b10700280a1503820b42e8402c0590788000518948610710390700c10055002c0e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 711109973 1250 711108723 711108743
    0xe01030b040b160804030305090a1b1a042106060b07050a02120c0a0e060d14062a0d0b01050d1509050606160b10091121011202040902040216080304 65
    0xf082e20f048000e200b0300d1426a22032000c103480e01c2c0c1d03058020700390090496100340320b40010310012881c110171180051440490001c0c94904082c0201c007025240400c846681d14200010003d50940340d90f02c007007082c0d08280d4091840481d15150001d48003640c0000f0000700301149a505221010841c0340400e8400c85015800e07030405002a0b4440d401340f031189070300c110000010840780f4140e90701c065000000030480840008a50380e8071714494610300c5034480300c0d030180c4108800c43d814050128074031100301c540c0040e0325190364001e0205100d0b140c007000e070307894442240074100e900034003d41c3c4040c080b2440500019210241601c0c0788000c0e4030641040c207045c10049511403c0100880e0342030422031010090070322854131420f080302c0e0042d00004254501c03000018440304148070740201240540050b56403803401c04c1500e013004074401d81400c080d25a65004000300030030240032401700c9a0581c0c003c5102519800094028001e40042c4103240d000f0103d07140401503890011446035109541c455 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 711111223 1250 711109973 711109981
    0x1150e0105010e0d1e0807062307030e0a1403070b100e0103200613061211180102010f091a01080f0303010e06040237080603030406030c0203040e01030b040b 69
    0x14010810a20545000c00d00b007507100035950500442c0c00b07080030700440c20510ba1004204651642c008880400d807020780010444004010550080a001604051050300b9118074001d84034401c81c00904901c3c01d02d541d40f280501d48141c103001e070121064112508070100000d0f0308406803680d018180489541420f400002d100d0702c00301103940c003034505020384054141e0075582d4510445121400f11241c1c00e428200d45106652104d00626451080b0304500041c28034000002d400e40c11900704070301041d420322a5040e03041c1c0a502c00d0b140107012021440c418404182c00607401018518488445141000018014009440c4009010103103800c1550500d0780d80e606100c2d100c010050030302e041ca801c100700412582c3c00a058240c0c0040e0000c00042c07400c0c696035825040e030b00003d0346c1c0d9370303200c07200d84100c0808001c0002141c2e02070300300d030910707008600e04400042e032203106a0190005240e585c06d41c0003c03080c803c2042d60003038000c83c141c0c14035550310783c1018060103004803005c90704018107038002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 711112473 1250 711111223 711111239
    0x20309010f05130611160609060f0902011707050412060e06330a120f02040c110c101e02010b0301110a0c20062701030608072904080115 60
    0x32920600701d008810906003d10350741d1801404604084009503501030000d20803110b025039042d260640b00703440000f0b0884481c0781c1300d0709640600c100203c00d680b030403420034003613600130600100c02c0070091044050340d80d50780350681d0f1900454016100211003c10300034104200303603201144043d2030307008484040d911180300b10050310310300e107484620700c00c000f103c917900720701d929120f40000744001c01101840d51155661840d010554805542c00309610b18143d040d41014854070b0f45801c030fa490400d03040c2e4401003d09540714014505580501c1e0055101100540701300100000b2400a081901030381c0c3c80b00000901070441000382c0751095190140b04100008004219030402c0d180352641000d071181c1d5220804110016240c034811107045414900b810f50f03804009004030b01c10710412005002041010a00140c5868040c5040c107191800521075a68002081001c5aa43d0404081c0950615101d04400c0708040c1c054080a07001180204900318190480e2442c081403400c2c100b8950703621090303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 711113723 1250 711112473 711112481
    0x4180218091e0a02190804030f050f1b011404030903030e0910060302030601020f030a0c06060b070f080d0e0d05032e0506070609080a05040e0f190902030c090109020309010f 76
    0x40a9100d03040100724058075098070b0006603000c1045040142001c681d001c000d490003ea6a1600c0d0016410380200401c1507008207441c4080a00b0389003141c104545001c01d81020310594400401000c100c8100e0f5429030001d40100182681c0d074807803414642821b20300503103000f9071408201c2c00300d109010304d20003a003407030601203114280d49082c40c141d00341740c0203040c0e009600c05082c844c118007440114007100c0360104000c2520740f180c1d594a00810780b09082030030481f001c90b00815031412080007243c021800e8a0000741038150043c020698901d484403007680103140c440e0b58680540030b48500c103100e064100b400741d845040600704900707890744980c01040d4510b005121010344403080800a02560602d84080d1500390711601000807200900d413030b85001504500b58001c0010070000e0107011034000103d00c160071041d1345041d61020705000754500b100c001840b64141415986070316141c190b40d800c0024041212002d0400417603542c440507944081d50040303960804c558246103440411480c1032103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 711114973 1250 711113723 711113731
    0x20190302030c0405090408070b04050f0c191a0403120c1208040f0b07020106030b010906150c03020d120b090a1401140d1b05030f070305150411040e030418021809 71
    0x14840f85803504100812907961409401030f030300c00078140321003400180b110614a0041f8010001066a40b41e51b030426498040c040000c0c5005414004007030f1001e01d00450b0480540304c208020a501002c0303250541080c0c06907074806440f040c0f4883c44100b005130041d2010400e40d00440b0303014002068280240c400d2001a60700506403010b03046000c010901c892031007904115284000b241c03041d40d944800c084100e0a810400085556010070080d18502821103148406c0301d00b441c0c41c101002c2d0320701a4031441c074a8040000c1c0071507010007034828241d03640f0005107020014150750a46c02c155000b00001c0a105649070502d010340000480c464050322490200b451000386030b001c07110899501d11844a0002e82c81001036800308001151558080c80080c0042c00103500070100107155040c4507203040030b0914081202c83c03070f01b4184004600d2008101c040200261004964481300f902a14510f115903445402d0742c10202c040680c1d40c0c00781c0e40083c19a027a490004400301c02c03d04080000e01042a9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 711116223 1250 711114973 711114991
    0x30d0302070f060902120f0c031501030c060c06090c08150109060503250801050108151506091009080102030c0c1c0516060605060703050d0e0105061c02042019030203 73
    0x49800c00084064204504c1503101404040d14441807410040c5407084001c0190790a030440380c0c812099007400c200131201120800e800c031010354559201c10f411811030b40100c0e07041150040c0c04130309201c00c0e5040b2400e00c1d940030740704024080e0b858003400d031905005080300d0b0f41d015a05c400000c01c00100d008200585400070007414030850703146613100000810850324240c900101c00e00080a003803c3c0300790f9001384080000fa080c1c0300e8100006620445006101030100c941c400031142642c4c56500135104044025582025680c1c00d14500382c0780302455500c0303401d841d070001080000741c4010350040c101040640d82201c10041e41245400b1a0900c49000c5400140050040340034a0210b090b550100d0b0307000380380c00200c0d9034031403000c12803907031206a0a0300880c00000c0d051152041611818613010401402005182015800140c0400300360180700e02c00b05e4017000d4a0255600d65000d8096a60302204a10303a0906004410490b6041681c0c0070100c0d440b480c4401c203240d4040c0c000c4903c030b5208030b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 711117473 1250 711116223 711116243
    0x8100b090a021305090c190f0c0b0406090b070e03010c1d21070b0322020a05010f020c0616030224010e07170f04020a05240d0e1605030d030207 63
    0x542000083d000003200100341c102c41c81e0001456140c0c010035034010f0910340b41d455034403030008645040c848241840403040000078540700ca40c2e141d101c00840007140d031202d03400074151200c0c10306030040c020a0102410503000001400081a042240383d800380b03030207034001d21017600e4090081e203500d0441007041d080c80ea03070030310340c061140340866074040102c0356884542c800c410a00c80e01c2c1d180006580183d80245800824060400d02c01ca08050113400742400c4001c0714000c6074042002004a07108540c117010315a00500c204900030f0160301d00b811405407845403120128040d41415003004007040c0e0240c001c180710341450b501c0040070921052100300e101c00859107030035010481280000d1201017000341c00540341e0b000d460b0440c0d910703002c0c9141d481109020304181c010003034410100e134441d9114440c2178512075088000441c61a0350040813541403510b0305a40c07185c8002501b020000c1c80c040c3d010f54100c00700d08241411099080d80c01c2642110250b2071414000c0c1c04078803079010301a04102078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 711118723 1250 711117473 711117481
    0xd0c051203060d1a060108010909021804060f2f0327010605040207031701090506011d040e030c1b040b130218090a1d0307020105030414070b0d0608100b09 68
    0x110400030342d0050720141084200d0b0140e0b885007144064210b560004010600d402c1c00644d40e40450300502418603144100040202d41d8000340708503140700c1040307104107460400102885801da00100002c68003407003e220100403100b440d410260011104404034179070403440c410040045080d00d1040070a01010b0384070b00c99000744036617a01c0d51806490200e41d01c5503400320351a00d40780040c18a0a101e5294814108104580b050361040160440c0756003074500820008075aa001c0111034101e100540103204400c21803010801811350b8851961561100041d10701c0203900020302c103035a01c600c140340040703102650b00800040d0f40c24880c00c2c991240300c40541e000d40304050b81c02048550360700041d41f54101c1803040483d541e030a00702c80b20540182d9401101c1d2640020312492184103c0c21009189441d03415800680140800740c400b178140c03144803c0070080000204081000b50000c44506034660741a41c1c00017001c2c1c0314a004d030803440e010742c080c0580a807485015612640310020710f14025961 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 711119973 1250 711118723 711118753
    0x1060f06080901270212010903020c0f0d050a050606100212070204020c1501060504050f1507060203100306051f08061608060118121109040804061d0618030d0c05 71
    0x9406060302c0c686544c0c403031181c40c0000c000d08058002981600300c10044011900401400b044940c50b001c04590511074001c0019601040701e5095142c120344200060040b0004079181031101a001000d44c8141c214038414000005612441490304490503407607560111030403a201c6140f006504a140e1041c41204010701d06500030f80000100ba600b141d0354500481d900744500345083e4803401c0440e0f03000405000604040c2c1110080c2d2800f5101405242031000c42903505200f46040038010f80d1740030000c42c0c00c05030340502c0103008540008081c0901c0c00c1c19042080300303103a07508002d07030041400500050302890114001348100b02c07070400a6a0b80170480d0003910000402014181081036030301016284103603603003800c4007600c00f105100002100c14544a480b02269000d0302d440340d4100c2040100003428141181c096443e6482d10f02c5151035441840c1002840000e0182e80c400d07000300b80d41401c2c0b018083c80b404e240034114111442008a00c4080c2e48504c0c1c0c404001d8126081240c207201040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 711121223 1250 711119973 711119987
    0x80402060d0c08060a1d06060c010902060f0d060914042612010e010503060405030a050a140403080702040f2708090a031a062b0204091401061701060f06 67
    0x140050065454040d820705075504076855002800c0c042100071003071010310309100c10040c0c060300d28400e280ca140c10742202c0b211000d0750000c2c1000c0c07003038000254002803400c0c29040f002159502410140c0c90768800c14040e44c2a410003011000390034601040010350f903e49000740090b001c403a0701101d150751559224520031144002e14072544140360b1507501c100d050020001e080310340c0c40065080e17943d410903d240d0080700d0180c3c0700a100f075126a003440041140401241c2c02008141812a42c3c0d401c098403c1d0381811403542c40103039642000c2030000a000c101e00050102d5442100d0401055032042000c0d0301f1103c1c1c2c1040034002881c800b14051441c140c590303071801c58500a407140d80c1001c0548000401c50608d9030000c880f8900194800500c003d1420f000b90341090342102d04918240361641046103030001d506010408103560041d15003952210361203a0b038125002404a8100c0042c001054080c082c9031041e40c1020a00348614002c90704180f01d514281c8040385002c01106242c01800c82d035003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 711122473 1250 711121223 711121231
    0xf0c0503060607020a0b0a0f03182307080118140105100b0a050c030a020a0210020c030d1b0203010603031e05030910020702030f03070f020f0909060c0a12110d050c071208 75
    0x14030a1740701141217503402000e010340000c5036440c001405400f10f00101940c6013502c0c0344070100d0f0701071500e00000300b031080707102c2144003141603002c03480d4500b03050180703001880d510282036035281c6101e214014101d80b141070300f0b17280241040d2201101da040c0e11401ca52044800000d20307070341c000081c080984c2c4880100a842c88500d003c60921082445583c11940440400030250b4449c94005085092000c0105501e11050024041f09125040421384842540b10400d041003100c01e040c4050008a10038080720701d0b0064002c001c2c0e02e86030716024000942c1c0c0c0e040100c0e2000c80802ca06c949904c5001180c1c86031528601070701c15070384c00c0070000020350450041268140107400401c8040c00b4208064943d041c0160f8454818101900600c1100c0300c00358055401404a0b00c01c0000300711000495580180c185440b45642c1c1c0c221140c1200c007034810900d041e54190a00b940e485141110401034115241d60302010406c640720390559403d940300c0c152004220f202000810352055001c0c0c4145548 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 711123723 1250 711122473 711122479
    0x1060306080c0f01140d0f09020307510801031b0b0d0203041a04051f0905030711150706020d0605061201060f050415110f0f12030a090507080a05010f0c050306060702 73
    0xc6c06030300602c07074050f224010600b4040b2070f5500d41e040254503003048020001d140e02902c03034110404a400184e030f6070302d00b0101c00c00880554101c05034109144c00d000e2032a241c1c40094101d5106100c0f0307005003841c40070f10083d221214418000000d1000f000111011200c00f989010702e072440424036a006504001d00c00c1e00c244140138480c0c1021348081000604c980d1149004e05440d0020300d0740c42c00c80d50100c240b00b0000a00e08400480050b100008032200180c200c40700104001c2210000750380382c00c840300001aa203101007800c3e010032000390060044500005004d004094413481408418007660b81c010509060201c0100f001074010418403440c01c00c1490a030b0701d0651148607141c45020100c030703000300140000041074038005051201e00b14595506000d0841c0b0403007500700c25596040c2068802c00f800c7c0000101d2510340a65100711314160344407042e03480241d03442580940b2a007002c00256410350030701010101c1a000c4e8814080480030a40710b141c15903e0301800d01c02e194000d030004a030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 711124973 1250 711123723 711123727
    0x1302121612140d090618060804060b0307150f170408070305030c070210170a050124030b03070306060602060c07080a0f0e03060c0405180103050a14070e01030b01060306080c0f0114 79
    0x100501030024600c2c454058880c980114034103680100705804c1402004482c1005500c240700023584018010307081500b0640c0402e50412000c002400c1404035804042400c980301c40041c09071f80c200034041c4e02076034240c54074a08260b00d68091141c0f0b64080b103008010503420029440084d00500140d5005046c4a0019041241c50b03408246803078030130b039242c2c00402c8040c0f200c10800d081d0100da02d035019210030824010f9500d440d09440d18a5100c008c1d000c2d8103a9112151148140300e0390040d80815402802c40b1207069803418070000601545c0110001400b900001448141c070900031150226071141d9540d00d01824240215038816121000302c04000150461190554081028a0081140c10151070ba5981303010f0800841c0244030540d03c800c1c58084004001140002c56441e4100e500000030521a42c01c04001606054040c1c0000800030000800072040c030190102e413506030346441d1401c0040c4ca448450490ba070ba40f420f0700a0b5404803081304030503029440340d007a408200c81c54014840c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 711126223 1250 711124973 711125003
    0xe0408070b1f0308040e01150207030303020913050103060608060717061903051c020d0f0c1209030506040303050714180d060e0f0303060418030212130e1302121612 72
    0x200210320180c0c8182c13480440840e05100c2c0190340b125250051406200041d400d842c440d00c081d4072a440c40c48082c0174140e0220341e1600d07a40302c20580409000c6036030300030005507840c0d1401c140200b80a01580301d01e0300c1884001801070f80a1803540050407017294100b4011781c0c9090400800c1c4040008103140710701c000200100161040042d00c20590208950420740d80e030f01d5030001d00d04103401d03031000204411105940022504010b1680b401e03604020f2120402c2c10f690700a840d2150b503503000078003502c2404100018183d0583c803081c01600ca96481398511004104060044e0180881c0d01084407810420024103107040780c0d045520b40d114200105a00d54004071103801d012039501c45079003680001041040c90718280c81030002c07030241030903604084071281d10006d41d2884c041000d6554035100290386528003079051600d000030019600c4581c000d00d0414416009480f011000301d00400168003501030441d80440c10103a010040003215155500d40030003600e0b440d500e59415130707440c00000048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 711127473 1250 711126223 711126271
    0x150703020c120c031506100311091c0318050a1211060a02010c11010e06010b0309070807060906170103110d0c0e0108030909090712022b030e0a0e0408070b 68
    0x11112103000e4040801c3d00d805044c2482035a4a14064480c1620308000d0701d503451509444c401403e40ca40050703040d41c0031180103041d01c6401c060070340c030550300c051a020399801001809091481f80d81c0e03c8512001008058040000302e00600d039000007a81418000c0c140070411050880d070003010f20f0321102c1525000304020754011508000141d44a902c08284e40c1d8010300c2c00800e00420038020001a0742019030342351100d00600503520601000404182c1c8200e041203514041c101030801d031507001356641006400801a4440c50020560910200e201c100340b00351076504990300b04101010941502d000c000b000000980219402041c542020803010f04201c004c40c041c00084004554a5076040200001404018401740140e480360341c0c24031a411440d40c100091560650300340101105078078188110911042d5406510700f1a401d14105066000d0040003e1110030740b0005141900c5a18206c1c049504840141054408000c0e040008840ca00541d130302900d0b424038110300010030016 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 711128723 1250 711127473 711127489
    0x20a0b0a1e020a1401201e09060409180c091a030d09140414090703050f1908030406020f16060f0b0612040807140a030206010909020112050702280b06040209150703020c 74
    0x5007503c1c804001c103401d201f5039454080700240e0341041e40c00500b411846030000d009441b850080301c2e8190f88400a80700c0b108035401c0c090404562145031842c00c1500e80c1071100041c00180ea6140d808000c1c4103141c9600e080c082215400711402e9500e000900d42401e0b002c0107208164021a030708165078041e07440b0042010401c045c0214800b40181021600c0c5040191403d03a15000c82169a0406100400110046008822826485030050740c0b07a940b0380c1012002802842c190b2100482c0005107030003600403010040301e5013407090700100000092184128121080d410507203400c41c1c004c0002c41d0340b445145401c1a40f040c441d4101c546000900d44e00c0c4000b2004240d40700d030144c0d10400110041640620000d405465288c00800c100d941c0c17034000034a1010100d05801c4803965620120301003034800e204c441c08401816103041c0010800c503029088500782c250041d10b44074621030100380d50703140500031a281d00c5001407018455040ca140070f440301d680110b07002c80c107511910042d1240f03034440c425 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 711129973 1250 711128723 711128771
    0x20f1005061003050606042102090a140f010f0b0304060e033c031503010608010c0e04060f0522020d0c080603010b010801061e020a020a0b0a1e020a1401 67
    0xa4041054244881800044200c0c2e0624209050900781084200c0d1078040595044130300c509507000a030100160306021050191801039003201b5801c0130010322003103035001400c0b0341007100044a81d550300d03003202e11305225084c0140d00303003901449000c1080401c05070255030414011007000a03000b03421082c16145901c24101e0203400c8000c0c0d441007070741000035500c0441c07440210105241103501414080300900c0000d0403c403e0251048400c607054509610a0000d0007a40000b0806856541c902600d0540d212041c40e12840c02e204020444021149040c800c951b0040d005d4000340504500c1c0300900040d65041a59007a403e00c032200a0510f1809418121a02921200e0050604005160940720b08414050600c00350000420189602500d0402c040018140c000040d41800700f04034200110703001c001c0d522107030100c00445d03620144001080e0700b10381ca403a1183e1520100c0396417003414000049140141e003125038840d002ca1104840580c0081040e40000741c403600961800b0301035a400c50b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 711131223 1250 711129973 711130003
    0x901060e1009050102030703030c0e030f0c120304030b01031727040e0c090c030c2802061308190512101401020102120c0f120a02180a150e01020f 64
    0x122884032582403203030307003240e44200d6480d01d2280d4600707000002c2d41e00d00c1564402401c26a490b4070f8065442e1040c1c0c1c0b00c001c4950300030103581141c2034030307a0701e81e9072520b1901c0801d10911390405a50f87d03e0b08004201c4080f07c1e8000140d00b03103686140c580014241031400f000400c05400c00010b940d09440800c41070313590b00707482c3c1c0082c0ca80340d07010144001c961441c040001030b45c0c00002011070036503c0c0000c441e400310f4101c0e041c0d070740c960b1030401c40020350040020302410706c0f00300c0501a40c070207010f06500145030415401c8a0190b070f5010001085e40c0047c40c0044e00e5a0410489040525203441c10b81120045600302103181a02c401e03025889850105c0b10b904120241a4041c801d19070880c0d440001e400d401d00c003d40c103008001c100b002c0c0e01c0b031014060326940400041c1c8d0002540e548001c0c0c42004000000700c820502c4e000400c0c0e0080d600110703043c011003010400300d90091400c05c0d40241991541d550188404000b50800c1d51000700b200d14079410351180300c204400d0031008114407a0346810301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 711132473 1250 711131223 711131237
    0xe0114044407050703260f0d09080c0307240504020901030f02180f0403080f06311112100b12060f1201020c010614180c1c05061c030f0c11090106 64
    0x1486d48105184032803885010030340c0c04200484100c900c4030140e500b01445c10100240c00c17011482c0488a5100750800c940d6280404a00c040038003c6014009010340812807494105030904e683c2c00048620440c2c009602140850050012039203180c89840748500c05083c000d0008101081ea103408802103c070260407014a804100030144c1c41034030603400400b0308565444a013400e9001035030804075822034a44c0702c0c004e0000c440c4c207241039680030400d0303250760368040141110940b51240700ea448a56441c40001c07000c40400c031882d55601c91481156002c95005042010503c3c20f501a1400a4446540514085620704003562006074015420080a000607921464100fa1909480683c1d005d2400000310b06c180d02c442d07441c0c49201c6000707900039110ba07a0240c0d82d04031100788a806200e22400540b40502025170f508003c070342c84940110021119098025030300c5a005c030030106203090040005202402004440b40940c06101c50540702e04c0d101c1100c0c04420000c61000d003402d07801540082c6c40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 711133723 1250 711132473 711132503
    0x50711060d0507032306010f02160b0304030906090f050603180607180504110a1416081e2106040e250b160b0a0e0114044407050703 58
    0x14172038901c41c0c0314580011183c6440940d440c002d003880050603141070050b402503115110380700384455003203994404040c0e44070301d45450030b81c041d540040742c040300030501d105070109101e80120005411620100e01d0341a40c0c80c201800d01c12240c10240c0381422030040c3c4561509091014000c1341e00c528042e51307440841e40388143d010710320103a0303d070f100c14000c1e1701d490101c3e000d036243c00c0c0c211103040c541810059080084900401c0281c0700e5608070380301000c010800754082001c2d4100806418000d41c0b8800d801d0300c6c80c03070403144180c480e9190400880c0c900800760742a0392081c0e0a0642d0240004000103131040546444505002d5146c201000d501001a003111244c0e01d0035203400e0150480d6039a440c240350224441c0101a010442d000d00305585000000307515540a03080f11b201d100c0d07040001d01035100c004051040060003901c089459000c00700000040820701d0b01000d0000d0008000046803035844d1030700c0b03009060301c0400301044400c10001000452010402d000007035118850541c0e900c0c0e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 711134973 1250 711133723 711133727
    0x110c15040b0a0b010203040b031e04030908010606030b0d03300603051509100f090c0806090c031c0e06071406010e090a0c0519050301050702011a04140106050711060d0507 75
    0x14004142c1c0020a1925081c0951640e001017502c05a50360081d1a580c0d944484840c0e14081e07880c855241d100c0c25000041008060f4048115000c4410600090001903180c0d541030302500c0c04544202d411030075003e0040c02280c454941d001c0c5280e4031040880130000c030a00e0820031000300220040c4c07102d07108d200410400004000d201040325000e602c0309514101108003646803150f14001e40c100326100c0e401880e044205e513004117406544031403458041551140c03520f0300d038a002c039100a22030180052001240c1800728100308640100300d10300a85003080d10b403e440d00d41c0e040300d00f42c0d0411010311240300003030383e80f0781d140130344129038801070049601d03118002c1c441c4c000c000e04da00010781000602c80b000072a040300034401d5400440c3c0c414046103000748840c000712180d5118503415824603040c442015010b51055266407094500141909519014401584d400068401c5050409001049403600c15406044514401d050200344080164001811600300946441429540c1c2061100c0d144d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 711136223 1250 711134973 711134993
    0x1150f090e0606010503190c1218021f0509040501030f200a1a0702150c0f0303010f060f050403081801091d04111c060606020d05030118110c1504 64
    0x408004401d000c010503000245441d840094011070521001001041d45000703203900107245100c0c0401c4c1088000c03641c0b1402811114900380040420380380140c044c01e404043c22480b2083d5030060804842a080c00c90801c0703130010f891001c901000030500103090280d03664000d0500840c01001a100d8004084c280070307410310744a0f000030680c0d021030101d01f0165196008058100c40030080004020580c0c030780300329914490400000e42c03014022540180740200e00c4050409031100c082102d03003810b1012400c5941e03200c280100e1a040104500400c451792282c00250b4047d5000c0c03510b982019500d5950b914682c20000b00582a400c0540402c030895901c00d20300001040044442a406400c040d60b07281103050140010303241406c0701140c0003d40c0c40301c845502c140121604d40c1d210f40b00060401302e009002e03134060140140180550403100742c2c422000d80b4181e584c1c0e00e4008a0300024001c0035001818031246250301d582c1d041c85481400c80707040c041c0c0b4010410250359445246041e290054400d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 711137473 1250 711136223 711136229
    0x3220c1e0f051e06031f06030c020312090a0b180607081e0a021b0102090f011106070804031209060c030f0c0207030305130308030403170603030403031b021201150f 72
    0x250a100100410199000060200e030790070b0300c07890850081000d2a000007080719003081e800520010500ca09004a6200002e14081c0703110100c51441c0c48000840a40e270444030007400603030061081510401c4400202900850707040110b8940c0030329070391610a5620110742450070401034800082c01e5200500030503500c100d107898041d0561030b0040141d03e000b032003030405015200030741c1c0000380285120350494031503180c0308550340a000e00b0f071030100d4040c2d0300290f070180c0581e0301c0380c20b280020350051a000200c0b0052402500c03690313507485011604040c0050040d01003203030320508a950080325200302d92036030f40940004904100c0c081800b03810758503070b4482150020300d0260000c03102d65000c00c8101c00d495051415580c1c2d000c80c0c1156184410141d003001d03004200001c1400304064014003100303606014020384150700e6030f0321010103440c0d0045103c0600414202c042c0074507103450f4100b481540510040048804940c0c0180560031a81e5866030000ea40361890403d004d120040b181e45401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 711138723 1250 711137473 711137519
    0x20d2d0b04141807050a090b031504030c080d090602070b011e06051b070510020106030b010b070512090d06090302011a09041101030b010207090c0c0308010b0a020601050603220c 78
    0x424a5a024002d55104018109949440703035541120280c00284440b00040c04000e044001060301c03608000f0080134540701c914424480d50840e05010806440340603ca036030591507014645000b070f10f58022941c0510300c006203403a92025484001a03542c805048954003070b04146c0250341c1094954507042c03100800e1100c041108640820182e91302008a498281101c2d00c0502c3c003500030100b00340381c10a1500038a034000c030510703072030001190f0542c08041120b0080314007540782e998070503040d5018801c0b01d00203440b0b6000003106003104e031400703401044000006811076103090160f4644404444480e101100141d4462031a2070403490640d58240c003a4004030b6500d2010f04040d070340c08018190398590709052580300d1006456030780c004d00001e0020701032410b040c0565600106c0007400060490070807004582140008540c40300c560059820502c080d4000b011181d090a04110b4641c00c001d003251054014690b003517a5500049480a480c680b040c043c400c3e025003404451581c1301d000800d0300c51 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 711139973 1250 711138723 711138731
    0x51c0515100c0b0c1803030708030a0c050f0a0f1b201c060b060f0403051501060302091e040605060d06080f06070221070803070c02100201050105060d020d2d0b04 71
    0x1000c10003500c20260002d1413403021940d0740c1c8142c03844182800c188a88207070701d8000800d612040c400003200442c8520b0a9450811900c07100a2040c0c5142c002d01e040c61460a00034001c004940d07014090105001e003ca0604100441c01206030004445e03090310111a502c5c4122584500780304843c80040403030604442a00c080004407101e0798294004041c054807090700c4040981081d100d500840d1150340c041c00d11141d030756881e400c01c541ea070581c09a00262141c0018000140144244260303603aa030701c0100040d0140301b01340b6210b06a51054040c0691041c1d071540d00151903500d2600818000600003404981c2c140b410301c510b4182000d410110718241c00c20720401415660205403010f074604c80f00141c0c00000f100e50441125400780c2840100342000010601c444c25401203c0e41c600b80d442101c2030809200c840100b2403c2c1c43e001c1c81801e030040030505c2480110440e07174000c0c2c05002d002c0400000c0c83c200d050420240030031140401061461031002012882001d4003c8401103101a50180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 711141223 1250 711139973 711139997
    0xc05090f1c061d0115031106040e0f09101a130b090402061c090609052e091106070308010f090c080a020a0e18010501090608060d03051c051510 63
    0x80a500103040103000a9803882c01c81c03d010000b042250054200100802010b6000b100c00e4a1058050005603003240070308100440c0c9280007412a8141c1d41c0d440c2d09038800e525070140b070130b0705000040c240300910f01800282454866482c441c101c4614049101d11400071401d405004c056010f10a00d5201c0e142031449045054842c0141e0940180d81a00c94590780d501105e04440e40da141c03c207168080303600b0203140c0824418244c128a100c02d000c1c0341921124209150006504076080300d400c94070700d0002c041c0c160031900b0ba60042c200c41d03001d5401c600d0703c0c00d0a440085d0040d0302a01c4101c01051691005020018221a8071009002c400008203e1a40100009012580018400c5080c0d540000d00d00c136029100d20500c01c080e0303c019000d42e0419000082ca256024800d0040c980003940519001442030300c41e441c09805004040d0003181d500f00741d0784040b25283c2c000507801c401d0642c1002400003035aa144652031249140c00b88490b01c0030501000c02c0714025101102c00100080242a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 711142473 1250 711141223 711141259
    0x280509160804020109090e010207020f0402120106080705040302120f0c01020a170d0b04021804050c090a17010e100603050706080115080612030403050105090c0406060801060c0302100c05090f 84
    0x204600600d50038040c560707030390b03d01c01240c0c07048160b0070002c0b02500385003104081c03034015005032401501c2201c5080141c803040d400d201c203c1c0211103040000000030001000312a0007250060b4000740c10f4904245020380301c0c1c001c42d24801080407100074940c02101c041d1000501807290038078101d001d10191110a0603512108215003c0d4011309108141c0090b0a40e90100903501103041da4a01600c05c0d0340780cbe07600201c4100c100322340e40c3e01280540d0415000840d542c0708101110702000008050b19a05401c0c925481d44e00380040d00e892025640e2440010700c8440d00308901204407002c3c0e00041001811864441c1c1894656400702c0f040c03009020040c4100c41d0002091421058a4a03050100340c3d140340001e0b03402d107841d0f250380c4058080058007000f13000040d04800e109100c0c1208445060410201340001c440c42e40c4169400140500018480b143c0b003803101420460080c41194074200106103804100c406060f50701000c41c500240c0c50000d41820a403007607803000300300c6211034116011202 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 711143723 1250 711142473 711142501
    0x201020d050c01060515030906071404090b28080709060e01092a0c140f1c0c05070e010e181c0504031a101202100e03010b280509 57
    0x340410700c000410b8104020000358040300081c000140000350605651640100983c01130302c445001d03014150004000701d024900c6008207000401c40140b41c145000100340041c04010710142d031101c0c00703080580842040700915000e01c91a00c02035405c0e1442c10741d02c0c502e0024590b00240089081020402c5115031a1a0311411034041c01000300d823031211019030505a6002a6441c1520f84801c500c0716542c9038001e03003403c05140b142180c08440280404020380e0360301c01400400065101c900940340000389000d107242e0030881da040140404140355912420446250440e003030440142c001000200da100c07401a400080160001c402c0c200745c821107d450310b00407200100240124035188011038070074422a001560040701d031000801120350440640030782900e02c1c0c00d00080141c1e0120b40104031501010340981e008095602303002c550f623016600280300c0016158155a0f5001100751610380c54090070170210010780e80e90054003940b50610804078036800c00c40c041c100c00c2d003c1003514980002d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 711144973 1250 711143723 711143743
    0x18011a04050423010506030f15011a0408060103060c171e0c04030c09020d060f060e01181508041223180d081207081e0a0b030109050c040501060903020102 68
    0x4001c50700d0340d550b0421020350384090390001d000c2c09a4001c8060641d00651010740540d07003c801340c1d0100c00d0101469995204c0855003003817801e10110040000c0c112082640c0c442c1480036104505248d680d0380714600300002607005072007080c0c84564102440e948100100281c80302e0304000202c60402030781190094000c400c90b4000c0b0340080c2d02054803c0d24080c00c1e02c0045501100c0ca00243d6200d199030006504003202855007541040070118180c503160b0454011b9030740d250341d0204840703d25001100c072000240411420440c0c01580070400070f841d00702c030107c03158154660307075602e0038903280901c80703074004114403000c01ca80d0190724150086e602c080908a040c84400709529880c031152850100442c420f680d81c0c2c0030701081e40700700170000d446c030260154105c280c224070b4207682e900c0b04c140c1e04440111100f180a08240c1c40040d80c075000609445e8129403046000500c0e20300388408682150501e01c400c3d281644481c0c0e04440314900390040c140035040c5844c0141c00c451030741c0d001039a500b034400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 711146223 1250 711144973 711144979
    0x60614030f0912180a0b0403050d030b0a05132a050a030b040b0306180f060609060103090c0305010204140f0f0f0105181f1814010f0c0803090618011a 66
    0x120200c1c0d0403034420001554031840d822802541c035500303813444016851901e00700740d025402054000071100400400d4078205c9030042c019002441c45d0380c008800622024508661051300c0100220310394031b0300c910030392041001d40c00c000b904c4000c8059104510211b0314000b00303008404000f1880c143e0b881010b64014460b03074140800c05404410000e230250040d80d4515802d8442e0700100402c400c4241004c901c8110400103442903d803064007007680310340c801c8520a8100c07243c400441e056510036403040b5030050007a0048070b0519203d694980c2039034400d900c0519525a816440072482c80c21542000b1203207011940d0106010405012401c11081c0c540103074180100411085200e1072560b80107144c003c0018407100d115225503441c2550b480c100d004000024221042d501c00f8515040301707040030f84030721550b940006809403004403002c2c0098010501000b000c2c01401d00000e2942028500903070000014054070315142501c40d1560700080d81134005a0f0504168081841640003032681104c401c3d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 711147473 1250 711146223 711146251
    0xe0f0a0627110f030106110a0b150d1515140f1c0c060507200a1a040b03041202010b0a0308070b0c041701050601180803030a0e07030206160606061403 66
    0x11504018880d0161440d50b0410000750034800512090007107050f00c2007911245d10384c04802a806950703904107000103000c0701040e03010a84010748000d0548400d68010402c44203070354203640354800500311419007811245c076440030a000440b1074440101400c0c00c007814201300340e4840d0004d11114405440180131703100711954450204110721742c00c10f01c0e40d0000c180000c0d4030b565480051007544400c50940d0302c45190110f8403501119030f01c07001c030102c60040c824584c20f800d0106800c20016100300001c00a032081100149086560018500c150b018a81e5001c220512000103800d40d0011134160f44503220300041400042d0582d02a03a4480d60461104400b07982c400d00e80c510580300d140c008881c0046044407410074008150061071280000383e840c0c1c04000598403401445a180d030241c16082d410610020328440c4403a48a046502c0250040700c0000b03a0f2900403499a034040e00708143c030a10500008001c0c400b903130080400401a0b480c20000c1c1c50203c980000d050300003e4202640420a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 711148723 1250 711147473 711147539
    0xc091205100504061104060509010306050d0221031e04030501060905010e010b070c0f03110f031b0108060d0c080a0b1012120210053c0714130e0f0a06 66
    0x210398001c0030311066000b003580d61b841d1501d03000b0342560080b186050009080040100e000d040041c03002c0b5503030b607002d0581c40c40301c81101c1c10010a0705040e88030340a140f109010070f00141c0100c03c40d050b030b43e803141040340790780c0c0d410740c18810f0a40e20190003042101703041200400610810741c49036411a00e045608685410071490503101c1e202e0154820f1002050403640072041c094003c1400c8080d100071104031032400c0f640000d040c3c580161040c4c41a1404400b4160095540a80c0003141d0144004007000008411955083c00325145a084110160300a134a00e20411441b144d03219003040f1100c4c05200398030703c2c4c81007003003500c503003502c00500e8011038115500d5030a008000f0381e041260190814022803601810003c0a103528174841525010811000000100220428045564045102c21203030303403411010369002c3c0e03002c0301c1c403092454100704001c802040c0c6280e0501a154423140c9805a04042507d601084405049942c51a2a1140030000300c0300700810981680c03400050502c888403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 711149973 1250 711148723 711148733
    0x12020d031116170303060121090c0f06180501081b04030206070f1b0b03060d050f0609010219080f0a0507020a0b04061b0509090f090a0611220315021c090302010c091205100504 77
    0xc0310b084000c0c0f2b00c18032404003084007d41d59070060107403402555500d05079080d8001c0d40c030b0044010b100e11404a200c40f80410855003003030303503401c03101c0320340c01c2c8103a142554035404200c2e25400794000340d4000c88840c401c14200100c07c0e0011701140310301d0624207a0242000581e114a10028014620a82d404001e4804005d4240712455042c020101521402c0c5020030040e03011b544606103c1c2c18007001010024280c2d405403118900500c080e40740103125070b0780e8801c102c004007400b6102405500c90f00300381400180c0c0c121907080c030031841303604007041413018290004290078041a03a541849014000300030180c440a07902c962014214015405588486071000e00300402d500c0041c040c03606101065600c9015400103203034100c421039100d04201c920005095110046010082201c40b4410311995507070051303000f4140551040001d003511801d850028022200d03070201c101d016035111002034a51940003003003c00281607000f5108031808182d52042e0f2038421508075074640300e0b41d480200702482 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 711151079 1106 711149973 711149981
    0x13081f0f0c0c110f2e0309030f0c0c0b0403050105090706080c12102103020f1b27180607030612020d031116170303060121 54
    0x340d59590383c41100c04a0508261300040303014800d0040e6a030301e81840c6090703544489107022080c030021201703e070310182d0f04118241031401d280f00740801e411846c0401409841d207001c00399a4007501d0081039141c1c0310380045490035408140842004015441075004400030021151394030741d1184201d80800c422102000080c100b80604007002030030012030790f00801c40c0d10301c84c041181c5942e9071851104603418000240c4038903426001c10725806100401440c6d1942000d00840a0108400c074201208562558001c1e0590509544160742c148502c0003040d03000309050496050216501c084403510807648180c5016480c04641c00318000d05c84c0c43d0032600300780401c014220307040d020010008002001a41031104550041186040c10f000003001c50340c038000c80b03180190a00c400e41e00d6020a01c0c00014035a8030070010720001d43c1e004012203044000580c8420b03941e41d964182d0070050 = true := by decide +kernel

theorem cover : BRFrame.Cov 710971223 711151079 := by
  have h0 := BRFrame.cov_init 710971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 710971223 ≤ n) (h2 : n < 711151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
