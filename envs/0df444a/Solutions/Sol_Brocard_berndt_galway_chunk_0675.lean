-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0675
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:04:41.800277+00:00
-- url     : https://prove2.me/submissions/3ccabfd2-1e5e-42e6-8ac3-8976e8670d08

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 121223021 ≤ n < 121402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 121224271 1250 121223021 121223027
    0xd09080d0e130e01022a0a02010509061306020606030c03150c1b03070309030b010506130b0a11061e0c1e0315040f050703240302040209040207050313060f11061501 72
    0x440c84100c04010800442c00318003c1d13000b50b01150100200340b2910f6803000307010210002505444070084050482000e00360700549113034002580e210741c07110b81801039030b4540d80300c450404000c043c107034020807050400006042c14407403020480c0780683c1000c00c130040310048c500e400a07045400d403948552340f0007000f41415440780c41680d25007094000051180c040c154043c80941c25a0300030803912400d40d80c2c2c0c1e400c001841c803840b00c40c00000d40c84030204218a0203240302400d1410100d00b00300380482c801558190030440c080301e600c80b00c0352548e4030040e00030b1209007010341d0000880d08001d2401e1350b60002c00c0340251f404034114109800000010307941c541c030551040b8915401600070321141d15803183c42c3c000b030f02e812500040020301c0d009400d05040000171610301103960003250640700506540a100181d0700170041310307400035001c1201d0800030380104010b1480f200045500400c60f824407800820030503989a0030000c04c0703100c2c040040f64010201706030350010f44140203404c504034000010313 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 121225521 1250 121224271 121224289
    0x70303030b10021c0c17070605010e06030606150906040603060e0c0301030209190b09070206090c091302060f091f11010c1b020a150216120809060d021201090606020d09080d0e 77
    0x1809011480f45810302501b510340949100b500c03420050045a0701c1d000080a0070008840c41903055020402107005414114a20b8406080d189034091030f08850b1804185160b209510850020b95101d10411440d400720680c00d400c00418258585194074680001d5504400500384c000070503010300328040555040d922000f003a14024042c03046510742000d000e501c2e9803045071403081c1da0048a1490702d9514041c22080d102d00003075080110120104d40030b10046812810034088500401c000c1c00420703035100340e0042c0310aa5a501000e040040f0360b82c00030b02c030b038080c64140400d0ba0f0400c2018002c241d003050311100c1110410b4418640703c2c00b1800040e40041c0954042c1010b841c0c000c4400e0419903020900446455034003050040c041da80300e50300500c150881c200541450707400d100903000d03403030900c0c000c1c401882c0e500c5001d41000b580d540703076552146082c1d00246d15240d4444040190715018040007201c9900d50a10303448103440c0810403500d03003841034400010489061552469a9140040c7c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 121226771 1250 121225521 121225523
    0x6170c1504150807020f010507140703090509040c15030c0e04020306011704060510080a0203281a070306050402090a090c030e070e0403020f030a020c06071e05070303030b10021c0c 79
    0x28012a0842c10001d01110350680f491001402007492261034a1170501400380030f04602c0d660300602d034850f0a01000503800c601c00c2202000b2403458005802d40d03446290781e02540c000d25240c0c0e07496140444501d41807445040b454103241c2050001c0200300c0c3c000940c52400041603a000d42e49681d6007004962080c05102d2816500203160b0070301c4203100381c6a00c010301c10a035078110512450707119030000b6914204080020b41c0f5600840382c02c6020310007a902c880085e4541514003040c00225528a24030500001c074180390220003d0400081c1a414000c0c1c0d00180010741d002c40c64055404e000c5200b0715081d000d5810020f80718945025120320035400700c030a0010756000e5031010b50f124003001551300070030345050b4014441d8680365501030802008440e915481600101000c5004105210003600b1421b07040e40e074203415040c91940d20204c40028060b1920440150145a08514028046446814150b0301908140300000d4820350001109039241c00d034100007111f03007e80c20b0b2044420904c4200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 121228021 1250 121226771 121226789
    0x8150118031b030203070801020c0a0204090c080303070c030f052104080f1606050a02090117060105071a0603100c0c03030b0d02030a0c090c03091a1003060218030106170c1504 77
    0x80b810b820b802c24a95400680f40700b04c0c141c80509039116070041c240e0141c010002055040b0006410040c030341a481890164850b031040c03003800342d858403030900310b800460305d40002c2125078524004044d40814040e003a00034070700303125091880b40d2051105009641601c0304c11001414080303000d201030b10701500e851103800c0c000151307111100c2d501c504040f04150421100c0030309000100d43c04121174000e03241d4003001030b5035426907000c2e24400140d23002000341c19581448410810003000c01c85c86103224515030013078241d00419050600c00c2c580381c09130002740f445d0755625240000c2200c0f80d0201c40a082e80d5010b203404190001410700180c0c03100d03a201c200070b500d480389402503030400c0040000d00040b00e0b00507130100310035400b2075015030607144204030082000450158076400005600342c01c0c0d070040940c40c41c030b105068484d035610080340c2c4802c411405003111018030f0925841d0074020b03080030344250b0750491203440a050103280c1c1d40002c401c0951146001242e800840c109920688008040f190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 121229271 1250 121228021 121228043
    0x40c090e0c120307020306060904080f0f04030215220b0a03020a12060e010305060a05040b070c1e0309051306030804050906060d051003150b03340e160815011803 71
    0x240b1480c2d60f640981e00880c02401240b000500900d00f10344118420382c2c1041881d4a8062840e00c0801c0302da10504400300c84540901020000d030311000c0d5010160540045282d60310495440105440001c801ca82600c1980074001400540740e80c1e400c0d5500c0c52206d0801584511a0380e81c19141c20031141103103681c00349071680c00500440306085050480f03020301c0955800c0d80320742c0c18100c01d0341c8048070050106503d08010401541c4942d002e401814045c85520500c0440101800c0351035855070001d9002481c1d440060046107010500c0914401d040c22007007145621b103a8840ea22401036202e5944605480d01c0011501c0e10780c102298152031400c0f400300858940002c940c403d4441c0ca000036101c18543e81800c4108a4031803040c0d00304020010000e109841d0380f001c0d000503455190300303007400e0342040406650380b050884801d82e01920214001080924000e801180c000081c0f8821104011510051220b0001509580700c00a07000f032a02e1500c403508503540c10700700e483d0380d400200650804 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 121230521 1250 121229271 121229299
    0x120303040f0201180e0a06060f110c060307140705010509060601020a0b0112020307051503160c031209060b060c01020909090706080c130b0c100f020328150608100806040c090e0c 78
    0x581d100c20180c8595442d0381400040d41c1c240ac58011084c0c3c00030100b1640040c12346000c80c50428091503001040d49003030b02001030100b00e6211560402c01e41141c2c103131345030310a020340038009101c20f1383c0c000020701c000c2001c0c200903202c28080002c180701c0c010703484102aa0b19401d5450031300924000d06000350002000712403401d209051a0b004a8181c040024a40c5814071418401c82c5409a802d4041e80d44a2914540d051800000c0400401c1120b907680e172420410a2529180040c0c1110170008000503107440d4131034240148250300072b01000c0e560f005200f043c4a1150041c1040350440130894906840300b6240780b00105102c00b94100b05101030011509214120001500e0001d5140d014030502441151340c41640c00c0c1d0005503a440911080c00c01c0c214071605092101c1c44072040c0b4010041078a89085030151541e0089802000004400c2e40070460b008603e48020402803103080c0040405180c0f548410406103624068000359035240c10b0110305e100010002510721002c010040e2002e0340032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 121231771 1250 121230521 121230541
    0x112706120a0c0e010909020a03061a07170310030b07020309040626061603021c02040609031407180504050c040608070801150806010911040e070e120303040f0201180e 73
    0x8115030048180b801e0000301c41d0101d210300c0c111089080107841d03c1200e981003c0311540a500812044004c01d41e546c600000c090300c1101d403024490b0310b4883c0952340c0300b18508201c605400c101120400c815010028854081078108500f0200e0307800042c540125221494202c0c111300c12020030b15400b505000010814415100248600361044460940000f41d25440c244c0c4a060469012034000c602000700c1c500103000b41c0080c0f41119050031100300d00603118013180100d8003d500a04001001e0402c24000c009188455040c21f414010003440902d14241149441c0d640b1801350300741282d00c0702701060411200b08906911204020401d01c01e203916246030680d21a824440c4449545c20a400007601503540d2280303c0a54800d031028010917030030109150080c0000e910508101c180c10000001c0c180e07200781810b409100e041d9282c20042c2c0e56a0100050111550b0b04a40c40e07030010018000000e01c800c2d54146981e50a080058280009254100d148401d59000c03170300200301c0104010703050701 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 121233021 1250 121231771 121231807
    0x105040f0f0510030b10030c0c0b010e0f090a080f180303030a050f070318080a0c1a04060c051204060902040f090b0907080a0209190b0406080102091201112706 70
    0x290741d140c0440c20600d904606a59800c0c017401d400c059240e044030304040c40794100e41001c0300c0c1c504000c1442c14150703031850300c0c451099001000b44009003003440400034000031080e8100c003104008011804003622003105a12802e03400f841e4070080002e00803400d035408017265601c550020252a100c0c030b1700554002c003404e81210300c081c03078480785000150024001d1041c0604a44000403110010705196a080e02951200d00315031300b40328444454000140c11070303000410030442000606000d09041c80e0400c15148400c007130764180b1209000000628920070455640150046d4010681030a00c0c00803600800d00ca03e403856405007004c90380418050158103450044502d00e04488023030b90750708052512100036100096006c2170072004210380340083e039450540101c0c90100044d040c3c1c0c2c007c0003d011140c81c0d500c901c00c265004651649580f03055010b1001c4440c5090090144240980e006a83c03071003807005a154940b4078445800c45410785c0d5405400401002c1d0465075030f540108070f1186104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 121234271 1250 121233021 121233029
    0x60a051e0f01140a0e130c0f021002072d06020c010605010e09010302061204050f06071e0306050102030405040c02030702030105040803010e0a06150f1106040b07030b0103051905060105040f0f 84
    0x100d01c1890605501c0f070f101c26122080c07800e800340d082900c0032030115200c200c0c1d08010b40c2d2101c1a080240103560451003020038010b441c1d11800d040c4920000c01904180f8a12a441100c0f4414403102c404281d4101403003050f8400004031140e8581c54a071403904405410b640a40218030219800700740d004d05500c00025520302743c03108500c026400b02007069a01c024040250040000d2107032141522040441d55040b40c8038070107036000340038016001d902d01170088460100044c030581c2c039146d0190010703400d9590016189002d004150038140040c0d944e10480c4903135801103599440c01c00b5064820700582d505158000c0c02402030f42880c0c104030183e9007003800b070410058000d03030106032103007814400c034003c5500700c0882c10702d181480d100540d8036600e034200b01400c0c8406070708101c1031007000740280341c80790f0710881e201c80c80c90800303500003821200703080446d03414185000306100c00001001c0d41c060481c90140c501081a41d641c2c40100d400d40200c0c1d024101850010a000c100401d080c3c0012080d2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 121235521 1250 121234271 121234279
    0x311010c020714060c0a080304030c0f030905040e06070206150607061e0e030406120504080c030703020a0b0105030a170a02030f03040302071d0601080f06120a030c02030d0203070b010b03060a051e 86
    0x110040f402040710700e126032840504254444128040000e10400c09994414000d05011000311642e4844401c040900c130030031000258a2102800f0320303c4c05100346003518810100420a41c946800040c9d5204806030102c160402c1c156802c0c540359968600b100d800d5070b4400c0d030078407140382034010b002850a0300000c40c00710310f130600140c0d200110000069804031241655002404900c514160700185000f810035200054204103516118074100700510340240302c0e50040401c0710140c05c11401c15035040c0c020740d11907007082034141c000c20304101008200d1224002c2e440c3da60609400180d14510603008001c410b4400441004141500419441c0c122009403100c0a5110705d11070f440c0c4070410f41250518041544000410300940340034410540c054405401d078401240502299481c025a0200403030008031b005100500b103040500c01603070380040d14002075042102554031503c114105028041140300d0100000c2d01c0c65880d01a20700c004c16000d420040c8020340700881441808a00440c1d0303001d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 121236771 1250 121235521 121235549
    0x506060303030c040b1806071b090c12021c06030b0106020d08010e04080d09020312130f0302210109021011010b09160c02030a06020d0204030203120f04120311010c0207 74
    0x241030100840307101d02d65090b680751030141009829a41d81e045840c040c00420301c48464410701d80c4400e0001c01036540686055551142038010068408005801c600701990030031107030748281c6800c4001d0364003e040500c0096140c45c0d07400300c0e080003100e800100c03e041a0522000100744108041c40c03d050320300681c2a141660f501500580e07403108207100b00f0641d0000c0d0ba0020f0701260200300503000c6404010030218403014607800081c517000032142c1c0030250b0140000c2d650187c0300c08105000c000c0c100c074a20340200914540000c0c0030703e140c00404c03050b480d1121038106c1800c08298406102264004d00b5031129041d030711b00041c51040301505000680d882d100c030004407403401641491090706000b280001080e10b5074421504050b074000200d8044c4155000b490014950340040c000c2c0340f0f4002d000503251465401050f02d0b00c40050040e540e0700703400300b204001c400529011101038402d06c0c04241c0324113100c1c0c074003251071645961100c0c0b299480c1c1442e5503c1d05034081181c0040b03c82d80c40c1e072552 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 121238021 1250 121236771 121236781
    0xb04140702100c0804021c1b05030c01091206020903070906080307060b0f10111006030f0330020f09090a0f23160203040b0a02011e0b0306180c060706090506 69
    0x10455503810f0f040000b04011500050062034070726241c419000000c6101104840c0c02d5036510030310081c0418488403190a0901489181020806034006460910300510320900e4241e1580205c500e00c04043d00d4941c0000e1a151a62030410906000384529002001303201e42c1c45d2400c17500ca030001394084546038141280c6060314545001c50741c0700c40720010052502c4502c0c1c4101541c5011800c10900349500804441d440c4080462203104021401040b92410501a03071400034824440020303055400140e0b800304502d00402c0da518a100b4050742800165210060500440b09004a603001e0b80d10021034010443c444405402c2028600003415080c0aa080b8102d4102510b10458048c100100f030320b10000b030341c0e200d100d00c004540d10300d41e070060724035003522200c00900541c410746503000076039158421807403005004c001242c2c81000c6070000700b002c5e00b40640000c0e00c50202521110289e00f4011070f010031118103210b401805940204034a903115110f14101002d02041902540c1900130703800014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 121239271 1250 121238021 121238053
    0x60409140a06050f181b12070b130603020309060103110607150e01110c0a02010e0a050306010308040e1f090515120109020108010b031005010c08090301140a0f0b060f070201030b04140702 82
    0x81e2641041502802c08110204a948411680c8205055011041c08442d02c107d86d014440d1070702906070503040644c1c8141d1850550781811596111104045c4100104001c400d00030980c54103407503008540c2002001c038940060601d002d1541e0280c40e1103401c40c040e40300c9c103206a20003004400396500030b000b60040b50701d41030164081c040240b989034002e004c180c0e00640c820741d0384100d055402060503030a2501c80c0701280c03a00009030000c81d07141c0000070302800300d0400034600c0c1e80d1003450064405031013503040710450301c070740d54600c240c1071115261004100c411400c18029500d550018008034640c0e040034103a04d02a1032a00f1042c1d000c15020000880c0380f0300203004070b03441105680c1d0000b03030051900c40111018140301c80d05030303042e035018031102000d42e5080c068541c06c3d21603504048464103010503194115402c1c1c0856080343c0d032800e03400b02050788803d0256402c2c0640c05040720740710401e500050f4080d00e0310780c21082e0f01504d0000c80c4035804505580160103000d85608440a00003048122 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 121240521 1250 121239271 121239301
    0xe060108070612060f0801141f030b04110409030315050f060306060a050c030c0c040e0d0f030509010603050f010f050c0403170702010c1b06020c01090608060409140a06050f 76
    0x30100e29000044180040d6008403800c500443c0ea00c0c8000644503650404a0030700441d030b41000c89943d44840703444019000139409030b03810412281310007882d4514030590a141e00744a01c001002c12450000240034030913101c420303042c1e104003c0d2040c0541901031030014024031005901c0c25002030703600000b28150a05200180ba10740014090070310f96241c83c000c0206640110380c0c3e500c100035003080f02d03010f80d60080c00902a0b01508070010030000c801d80c000c12050358246000d02c030484d8484190140201d60015031106400303447d060008007502c0301003005000d00b64680000c1e245220344c5a1200800205512030366002d0801d900070403150302c8500340b00301c440c032507480068013006c0c103000d90360030740031020b00185105441414010030b03540480c2d4a03000e00366101844503031101920001004042e40601c0050701110f401d1810003030007070416901521403900030b483e840c050340d640c0d0300d50302c100910011401498014403048030100142850010042c18040300c1e040c00001003203001c07501d50729080e900303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 121241771 1250 121240521 121240529
    0x6040b010f0b09150405060f0d0c1b0f03110706050714060402010c03080903070209040602070c1403031e0c06102301080f041104023106020606010f0c240e0601 70
    0x386030b140c40d0140f03041045250b01221003600d0b000c01040700040301d6440304010114036100004441e22408805080c000f22486c0030b9100060003205d05d0400488804200b4038900740da44002610000401030138100c0340341c030510201901c144189000401c640d504500901940c4e8450200449404019101c194544400b80d0f00240850b1914401c0800a4025100329070310014510440b8242143c40d00003500020b0160781c1a41d00c168002000e5081c41011041540a0102807090180141f00880400d40d2841140c1412064007419403075803c0e0941450100d40265090030200c07407807401c0008404440740510310661801100308100c048185103004904c400c00f0f04141c443da2070b2651541025600844024404ca81010f02041e50001a6490f0700c09001c2e80c64071020001a484106207200c0c1003a000c1403228500c405603000d003001000e50004026511110a00e844040d064141034244c070341c00082c0000400310032600d4803201e007a04840c0301c0c045030141011418041824510840c80c1c4610f4207001d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 121243021 1250 121241771 121241789
    0x2031311030712140f01090305040e0a090b0105040e010612050d080f16080c0c0a06050a0c0509090c1b0703240e1c12091101031b09050f0409120206040b010f 69
    0x601c0e00c00301300c03c1544540c001000308145c454000000144a085074040701003100801d1010078140710f06142c260000d98003000d54001040003c21a803203032104401d0503c01c0901c56a00c50407407025800007900054010070801c503000d6400246464055155142010784000044410340007640380400c00a01da40035612040400c4840505648100c80030070006141c0700780ea400400c00351038400f0003000110007040c000d48000a45040088080083d40d10000500007009010320a1980d0359079103e501d241c10900d4220060f503940c41403c1010b45100d0b50030305480050241034000804d204a414000056100249008401600903030341d040c21240c0c80c18035521a6440144101000d80b9405914203110040e400c0c11504054031024680c26500c4e404030882e00850310b859040070b50358241c05204102540c8a61005c01d4640c050401007200505208142c461a40d83c40390400d540c81d40d910140400c2c0c0c025042002c03411000d180655500da056508658540c401000011503084908141c025121040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 121244271 1250 121243021 121243049
    0x2030303011211010c11040b010c020d120207150e0f0d02060f0702031507020a060b13020a02031806040602030f03040c090216150204061d2106010915050108040f050f01020313110307 80
    0x1047c03100074030408a015043c8041c140c540005680c4920003181c0941c8580810410200c81c03600090415005501100404141d240003a201b10303040100c02259039015550f0b558442c0c018400210703161241d20000e500304200140b44081001e0002c001c0c1150b034001d42c111205452035034020518104101d40c08001030b0400341c200307000250715410900311004002e01d007440c0103007202d12041c12a400071501c0070150788001003015002e04c080d0001e9445000444101e828580782000183d100d20038544000302e001070000004040121548a1401810103a2030131500e40300044902442000074040685844850142c500c61300b090718000c44058070b89135551440c2d03110b414400c0c1100100340c005290340c002400d4031403024a010b08141c915010b420000200b25651402c80020708544244c4040340441410582c18405640c2000c10305400960020191801042c1400c0c564103100032040c0f0130042d54000800d0280e05542da00241010b0b80c042c6200d501d042c4215400c250b6a0140e2f8451240481025 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 121245521 1250 121244271 121244303
    0x71103150103110d06110405040b0a03170309011503030302030601020114010b04060507050c180f241309120f200604170c0a0b18063102030303011211010c 68
    0x98614071000300000341425071013104540d50142550440c103041d510400340461308220518040c020300045080980d0340394001811a00c1d081c10024240000510200c000004a1014002544050407500a401903400310035140d20300140658401d03102d17035005600f4222801d0010402c483c005040702d50194a50780f401c0d1800034107a405403c162000d82e110700a45c42c80181c3c80d1104908240011010000f182481c548001c1c502c1c02e2010180184480e100c1c0b002e11001c04460b4a4217080c4000c404441005a0100d01400c0c04050b1040900060000344009122100d2035009103100244503a1501c800c0c13210b40c250800a1190300d2610402c600307652262000c82e0126071b903000d15120020900e40c0107440c250100115030b241c04003880c4111030510454080001010030200300352101d414440282c00c0c03600b03180b0003000b60814136814000c070102001003282c0c40c501d10b40d5580e040c0300741c0c0034094945960f910501540c0340c412000050707032495070166100c01990320071040c030070301d0b640e204c0d11124003401c03c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 121246771 1250 121245521 121245533
    0x14040209100f02070911041502060708041704030f1103010509010b03030313030302070b130201080606040503210417060402040f0908070624090207120216050402070501021e071103150103 82
    0x12402c0340541c05a5840411015010300072081041034100340280c3e0740d458084807034800103100c40780c0340441d0014000e00120550282d080d5800036003140d90400031a6034103101082500c0790385e10040441c041000c2c030000708440c01c200e134030b140a400c0707008101e907a41303540c4102e084c0d0304402c4d602c1e03604d504200001094110300702019007009009240050801450b85e481418206c0160703400c080c1041944641d000310f681c410412a031000c410f030b07611402e0030710307200c0480d9443d0074a020780c500703040c917030f0b0407012240045a0585009013544094002c82065962000391640b5094600340c0c0143e01345400c0120000d0940a40b421095210b80a5440c01100e610b50344018103500c01706541c007980808401d811280c50a480e5070280c030740b000300141e849005182241c501f600c00d02c00c0c0c0055400103014260240f81d0403800e101242c8080c0c40c05680c800c9585011402071080d00003080380803c84d000e29001000e1140c0c0a808114442c809109814440700704047c0d546d029074087c9030700c00340071000510000e09 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 121248021 1250 121246771 121246787
    0x61602031c02130821210a140727080c12010f06141e060301140f04090b01051905092e1403070b07050a0f03091802041404020910 57
    0x4141400604000039891010709000301540824090740c04891340d20790401c92109000e00c500f0602d940103280100c006c08007900b1a24242401c1c4400d07105000080c07002d00e50b90003400c0e203d0900d200146241c98035140c0640345000109885000c2004a100c0e01d02d05c0364604d4a000a440c00e00780104146945082000303403004407a4640800c1d5501c90480300c1070001140a01c40141c203507410f4980e4040112814456050f03494110407014100c401d180080303548402040701d06680c548000c07898408403074030104440e2200021400d4000380b8000703c060502500710701103410707680100d4a1800d24040004400120071241c05016800100b40d80403e442022100c030408180ca803609208115000d0034280502c5d0340c5850744101e2510541c0c1d400c01e50545800e100010103080040420b03410200c968481070341c3c5141d004401000500f150b40000c040c18000c0629100030b0a01083c00150f940f07401d504200650010f11480492000121040000307141c41d000380e0300b059502400105008041c6801260303da0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 121249271 1250 121248021 121248067
    0x30b07030c1d092d0f06010c020d030807050903060907030201181d19022a010905030414030705100c02190605070b1f0303022503020108010308033606160203 69
    0x1074031003e89400000146144101030300582c515512917207000d0420485041d03005202c1410020441403140041c0e40301d00e4082002d40c0c061618411660701c6da002504d5505c074822800d42d2500c180e50070020b44260005421054a20070380e254140e43c405c14517228508500b40c01390201504000ca044480b4561481c02c1e41d500c000700d08030500e6000e07070090380314040ba1700002045c0700d904030500100015a545141c80c01d081103054000700241c031126225261240551b018a41c03990744002002e8034140e608104000261800429580000310400b0002e0440d03555184100d0295404aa05020a101360040e0000300c88040d00c83c04c1c0740540a540f0a2000705000300f0046801c55020a08080140f824064002551003034005003101800181103484440c1840a404c200c0c6610210a00050341e00c20152030449a000c03c2040d1680c442000c10000001e9000340220a5071100c030880081159561118810b480c40c0000e03a040d54071040ba000e10008681c000070740241e03008020101d581154443e40011071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 121250521 1250 121249271 121249291
    0xa0b0604021b0109020108090d0e0103020705030403140d030605041a040b03010603140d080903040f0303050a030609090305090f091b1b060901060f0602010b0d0b0603031201030b07030c1d09 83
    0x10200e61102c440d0700c07140c4884680d900c0007110215604444c149401441d82c200500100910520003403900594003a0070381016004100c0c0320030840304100b0313600515448100082e0541200911aa80d250070b0b00c00200001c0c181080010b55080c24812085050300070710040d90503100f0342e414000500310042c182030701990780706000004100c4000982c40444404400342036080788808009040600282088910307806c100800c120303402059248500300c03030341410070070340359400c078001a00140074a40c810b40b941c9040121003010543d000700180007a0604459080c90021260203009854800f00e8041c507601004508a280c483c50327200180101d04800c500d02c2c05444d580e4440340c1e0509100b40c4000d02c49a441c2d41051090b90343c0e10100301701034a82403000304201c40103103000811142d07025401400000c02c00c1e012403801e80701030086131555254005c0c0391109594901d0601200d02040b5201c2e00001d1410140c4003d9030301c80d1148030106208520b542e0030a00c1b0400400c009020f01400c1e0031380b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 121251771 1250 121250521 121250527
    0x3080318060403020d0f08090a020d05150106051c05101e0902040e0a242303031602040c031112180f0606010e0f01050307110f070308031909050a0b060402 68
    0x30380a007001090b10552180e800f511800784101d43c080c00c84a903ca40c3d00d024041f002040011070000000c03610b0403950110741e4225001d20b6814a10304110312941c049110915480000c284250008014060700c4070000c0340400104400c042c01080b07400036210711420070401c120800a6109507000000404400784140c82c81554071000ca41c202d900c03a40c0101c03204821141000410031041c800c2c9181c0c081905240e9040c80c84201140d0681c0d0114010b1003154104104010144401c441c41c08038462006421281c0d42d107602d50b40400c0d9003490410407886141402d0340b0a400ba4841c0c02511920048543c2590402c01c0020440321424001050303555030440321082110001300802980e80200c0c40403000d0f254504240000500010f00c00c0d100d14003e06005c140828980d82c02801c0300c0e80b2480070f251003445103080401e400e0030312040c1c8046007194884e000d03010040c808801e00a40c0107a50502c6172441801c00f0884140a540d22176001074001c0d00040d01c0040892203803601c2d81d50107a8028070040c6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 121253021 1250 121251771 121251811
    0x9030504081605041401060c06090602120408030907060207060c0311190309030501050121080903070308130617010b090111030909010308180f0a050f030c06120601020d0e0604030803 80
    0x1140c10103031801e00b00c0c100700080040006061a100f45081200c03501d00d10112981065405480035a08210040c4126030340d08100301844200d90546c0d6146090603664a194106402c00016030b030010350b01c0e400c1d00e000d038100024445000044040c1281d64640b541e990581158600755540c449a50b0805101d0080e10402d840030402e261007440075500c2610b401000c2c0b410f50504030300311a0141c00007186020040c8801c08441001c60071036604c1603000e07411a50314050310b000300f41840c01d683c2c4010300740c4c0d102282d907025402c800220ba409a034425900c4220b403584042c94100001000e02c214400c8080c00c02c82c00000c1d511482c980280c80346170000b1640303015000404074054444c00da1090740c1800d0082168070440242205511011004aa0b8810041208070004103a0340844c8103080c4176000e020000c0c940b03030310140714200c0d40d000000d0038244c9a11000d9039598140c9000c0300c81c41e0041c01582604908a4000d00c111780c85440d01070080c1d4203240c15030fa1459820362020f00012400780b4a00c541c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 121254271 1250 121253021 121253023
    0x50303010b040f06020307030203030a020c010b0901090f0f090803010506070c180603030f0503361605010f110303010905060f030d030603021908100903030e0f0609070e190903050408 80
    0x250082802041e040d90b103a240c0003000140500503008001190410010342c80484e0340007003541c0c3c100130400401a07640c100ca115a45c010141c00e284160002a424000200000d859110312103007004400c09028030129910004102c444212000301500400e000601c40350a028002d4445248950340c3c030b803611070321420000080700e5051071480f010f03600d6480c01e200300743e0710083d20314100780c950034140d007981411a0001072051110341001c1401456243d200264070102c029a80c00200590a96a280d000d0100e9600c0004550003030070b0120b0700f0321041d4401188241c60025010105402035070541e402c010143c1c000d0314000d42a940e0003480c4001c80304850b9014010480140e14070f03140058400d02d1481801007162046030501d140441210082103c1c682c085080c6040307503090300380010440d10030326040d0000d0803140141c580501c2445a501c00203600090303040e00641504040b16017803642c502c1900c1c2d9004d4101c4240140903004070324803002101d140c00164030070344241406403d040c0c44a990f5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 121255521 1250 121254271 121254277
    0x3020105030c0310120c030201300b010203040906090b0f090402010807081e010603090b01060503010506070b04050a0609150501080102090d020d02150a0e0a08010e03070b0a09060204030c1d04030e1c0503 89
    0xd441c44179407401b04200f1582c01c4030100c1e07110703242c4101c980185445c2c040c3c10395201c0545585018210340b544080580b41e8030900449001d0028000100400c0b912190000020800ca007200d40c0201030700022000d01e0700c0c0858510340705640c16519006940c0c1c6100b0229820b1002070451340099405c8091400d01c1510117021501811040c1e40010301000103081981d002070301070340b041d01404410001400141c8421045039140c5400c5001a1001c1c1c48615201d890104458070180807546408181341c100610340c640c01801c050100700600c241d07600c4508079800c0f0b109403c401903010800c10a040c006081c10001c0d4202c69000828401c3c001c0414542180940d21001c400d4000426a240440721407038204e00d80809070a140c030080081c60785505010340d0f01e1040b00c10140000c2c0290340041c03031b4405035070091859903a1000c2e0654445a89181114140c03006006180c01208448403003d00503140c5000f4070700c15501a03442904410f01ca40a108600d080350344503541c2d00581da101000031030400c20007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 121256771 1250 121255521 121255523
    0x904060504030e181b09040204060306030b0702070501050910110f0606040e0a0506040311030708070c0617060901180f060e09071a030a020310050d030305150a03020105030c031012 79
    0x4503461409240052002c401c165500d40f00b01d43c030030071005410b8640400558030420510118203404d40303c0c0c0d48180765001e280c042c00d5019000250200b005603150304080e08607032040b07034510710644401c0c4040c1d071075030110b000d4903000800c240103109180ca060307030112040c548141000c1c1d0159055140c9030b0b041808480b40001291300c82d5080c4000d41c01c2078442e61707074080ba0010261012141c1951466120000a04040d04015507001801d240d1641841180d40003648900c08a540d01c9051600f010b011955128690104440308000c0b000000011003c911480c0000d05a02440e030038020302031484914140c0d920341a40c0d031903c3d031242da1a001d104d03c20203002e5031480d210103860310301952413911100c1d4000e80c2080040b940c402d20401c0e1500d05aa0b04078858510150f20381d0f0310300781507032218082a0310442d030000c9071002e9041415010362001d0f008211441400e40b410005400384612401d26220090004d40b04000192050703400201450b0081c502161405007240c0c0e5444d03e50b0b816a40d004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 121258021 1250 121256771 121256783
    0x1031118040c09120b040203160303080604020d0e06090d080a0509031b030d0f09020f01020a0f061e0c08100510020c01030908040b3013020907120204080a0302100b0d0318050904 78
    0x1b80829880c0820a86041c4001d12002e00362883c159a4002d0103028003a1100b40280c0e0003054a1805040c81d4001501d8101c602c400c690040c03500140b039a565207400c50707040001c00c100c10080345042400c0c2c01500c1c070954034500110310301103c517035115a1b86109000f03e955240002c0c00074840644c1d40e40548500c0111540340416034940500401002295220090f8155401043d982002584041146401035044140012000100b030700d9122015004480e4a1409141c0380c1200c0400e908400c02602800a09900c2c90707081e074882080c8403050000e00c21000150740011203261496200f50028100148500a117506007036035020090103940048204039561409244007148403e0b00c1c400217076003e4889c200e090080d00300301d03006444000d02185c010303004813200c1e0005003259001c0c815400449040d44001c41d51255101c910320340312503041c602180107001da0303100c0078071001aa014440000350000e0250002c040955401c0d101c210055182c0d440d1505a1100050350350340710941d8620a0b80542 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 121259271 1250 121258021 121258043
    0x80706080c071b1d060f0a17071802040801051501020601090b0112020a0206060102210a030b0102011d0105011d1501210614041805070509130c031101031118040c0912 73
    0x41300b10a0800109080d000d00d400ca400e207015942d0318454281250418811083d0f121020000385080c084107803c45100d4400340c4006803000b01d10342d40240308840c0040001c00054481d40e607000310b1118900c0507140161700000c018010b0f4101540030909035001414034540101400a204060b178200042010140e0004000c01a4a5805000c0c5440805000001038100810124558101e001d2944401c08042e910402c1507403030b034000d500c006410381840c1510300f031808802c0002400390000740604181c440701c21800d040b841c1e61a06c4110302074190036242003812200c00c2d004407500c001425101c90344034050b4580e10580354040c4100f602400c8182c00801860401c0720510080d196894580000010010380210206202140290580d80101c0700c1884548441c906042012445800a0031000204000108101c4a1808544141c03000c2e00c0500c8421441c0e2414040d502948102c4c2140c2000e110301c1c0340f61861700e80e02c40803035036206041201c0c60f80c0d1140110234030204011412181c1010507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 121260521 1250 121259271 121259309
    0x91806081608030715090f0b041707020a0302040b010e0d0b0f0606042412110904150509072607020d090b0301050a0e130f120801080706080c071b 64
    0x38400c2100014429611030355042c036012115980388541d81d0301170300441c1d886104140681950704208242ca402241e940c58580f100c0c18528040030082c3e5003201c101c070540e5050144100280d05840c00b427030700140300d032801038659006c0c07101403c0e010381c409040001d8070084c41c216650385808040d0361400380c02d2212462521014901c90700e07a025000324800d00b018007042111061588004044610319682d8454094203414180d940040075440a90404e0501d842011996078281c041c0281050880341404141c80c500004403c070b2815015858001803614002403490740540800c484102c240340008034072201030380300710110b04425a650701c0160000300f00c480c80e5a502001d6000908001860107145514010000e442c801661140c10b9000c44100c000034a66a903114841d01ea16070080440040ba000907e001135140c40b50819160100d100100080745807000041d0f00c2d0107444060300d500c280c6c0e031112000c0703111980003e40700325070700358080868607012150b211240c0002d18054941c0d41d51034001d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 121261771 1250 121260521 121260523
    0x203071e0e22060503011d0c0a03050d0c0f060216121706041a0603010308030106080a060b07020d020301092102010e0105190c14030f010e06010804170a09180608 71
    0xe03854820030003281440ca03440960350040c03142042a140c0071460900400491140c0242003640d000c0ca40c035510b05050318002002000c1204e0044c200e02007550005000d41042001003440c41c0006411940400e4040040c0c0c0d00a00103c00164051048003c224034581c1d5400c1c2681d11074100d192000700300a008404020b031091501c03504500d00d082010903c4101031007809603040c01480d16106607156001440c0c2d01200c010442d102c0b8401610b2542d0b2580c40342041c0b800c6a000f0f03c120f0001403003810004910b802d841c0f1849056801001c16117240000300d408201c548814103400342d03450355840740a10700007241c040101d48040a00000408134091810019003110008102c8031056418801080141e5103199052102c0d140d405c3c80005840109401c2140e6055200f240075a22940000600105c07142c0041d4440c104c8070b000c044907090f170b680c803001101c14803070a44000b0081d5900704074089281c0c1d400806803020040780d1400c5142142c0d0341302481c0300500385800e807000300c9070b440c0f4080c44141c1c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 121263021 1250 121261771 121261817
    0x16090b0f040c020604060c0c050f0102040e061f120b060d1409010911060d021b0307051009050c12010e01090807060501060e0306011e050909030a02010531060f020307 73
    0x44101c03010403034250307011006912a840108001d02103035890135501c071154010400720b1200d540190442e0212a00c0c54001c5000354001e00030741140201940004029150154001d070140c0244641c88007281c1d0b50030010b0b40d40021600c1c80840780d07a01ea4000c0019521884003405490390340c100007207140071450480c545290307809400150f049c0d0506410601180402e0080443c2120940d201540c681210b800840240500d0300c4208858101c424000c0018400101420f0310500400c1500c0b4030030300654202045601c00480242950070a50f5203880f41c0c545a00380d64480003400c000070404100c01c250507800c40d402000100c904030030100c0c1c081c0070b100c854820240900500d040c152807052072a80003a82c2c420051103255000034641c400c1d04074001000300703058001c3c01d02608072005401c22408030f079129080042e00c1c400542c40c00c40001c86a0b10b10a09030155420081c29850168441142100052a5009054403d951180c5181e1010320b82840198401c9016079243d50300800d051005400482c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 121264271 1250 121263021 121263049
    0x1b0d03050a0209030d230307020a050c012a0201090e36070e0709150c0203150c091207210203060114011b050a05120a0e0303031e0916090b 61
    0x142c418041c2c84041d0b240000c0004041006080c690001c0d203450070209541180b01001c401000008010300074030a40000340e02c800d040c400d41c1560f07080c100510045410f241a0000781d800700804584050511402c02042e0b507001d40107140c40c1810944541c0070312405078042d548482818284011425400003030100e0200a107101c0e1021030011070301190722543c405d158040d2211455000300441d2060b03024076900c100810880504042c5000784040180a00d600d0030003c1e4000c2c0100c200240c4083c0c05410414400c124140d1013500780740862041c08540016a044902140314644021881c500c400743e440c25509140c51004040c604a4414141441c0040c0d200040b2a0b154203c6104d03d81c0e000541103c0c00700c0c034000056143c41890601510b0501c5c20301c80540305010f40c40c2001c58401c01310008201c425181d445241c6848a100281540c07840300300c0e4081140c0e240b00b0301ca00d001812610b11140c0240e11081243c0909150b5502103201c5115030344103d07049035403811a490f00e41803491002980d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 121265521 1250 121264271 121264291
    0x90e030c0d111b0a062609010b0108090a0b010b2a010c02011401140105030c040506030708070f170c0a020114010f0f05154807080604020d03030c03021b0d0305 70
    0x3c010301002c18100240c070300030003050215035100c0c00c0c3d08a581c003d0b00c902d441c520394104103107030400f800094024041a16160700240c43c040000700302c41000201e1840e074640c00046001c3d66840c003054a111600001164508000020282e040300e951702d002e01541c00982d413000242d0710b41075280180c2180c144020392010720544000410502103c0c0c0f1100030318881c01e09120350b596460303103206456482290000c0e988800003109010403258011042c0384520b106c0d0b01c0b00d00185e803006000351000415040d280e147c00400030001440c5600c0d0710050803541f0040c0c000818548003950303800b04640c20176004261269800d030f1042080c2c4030004495401800c0c155408061a05065506102031003441e8210401d0346403409410384203400812150740c484004c12000795803040036903c1c01584060302078400524400c0d54000704900307002185c0140950750041c01581001419601034000d08540b003002000d0541c00d00c40256a1100c605098908501e030b400544031148203881c000e4125240601102c0720 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 121266771 1250 121265521 121265563
    0xc0f040c090605070809060a0309030305060603100603023a14070c0201030905071e0f05030111220806010e04150902150c0102130305160e070207090e030c0d11 70
    0x241a04907a811040e64494640b841d552102418040c402d80b15030b92038950403c0000400c900151b600d680059605886603a0910050300e90304104542800162a03140050021100801c0001c1c002c0e030042000c8800c0c80f015010200b11b41013075031240c0e0100c074808140e1030402000717030708807440d00d1165102800c815078944100c4d0500c144c000385241903120740241416034594041082c02010000c0c40001c2c80c030800c0003e12030a1400718000220424070074481d100c118600d0116141ca4107005420000c0b5403407014908001a0800e0360b001c030030117145d000000349010440850454810710044d8042d0400082e40aa181402d183c421001244041c22a091718074010b020030059030350603140b510002800140680320b0f15900107441c028030410a1041d0459510000042041340c0406c0306c40403c02e40c002203085860f50742680d400400ea00b15220001030708880b809208402d86640400704402914007103a081008030060585400320358070415022a2034001140d02d11403007003004205010045918000b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 121268021 1250 121266771 121266791
    0x9120f250e04020f0102010e060901150807080303040813030b150901050f09040311070b03010f060f020303040f02100507060903080f010807050d060203090102090a031202160503061503031303050c0f04 88
    0x30901c1c40035000038070407007810852604030fa1003500302d04255402d032070682d129414203082c603074028080c50480c4002842a842c000407040808258070048560301409103255545541c0c5c0c05203640d010a103e01c4400e020141d020000c80d0880751101c4c0b080000c40f0b156030715120b07c0c2040000b040c4059104921031083c00c40106043e07190102001e800540c5818880048129444554104021604412050725012000048030191718410200316840354540c2000207142c10000c80e2203110859000e80950802001d070801030401c684036242d620068601a410802d83d43d0310201a58070b5610f0583c00158030000340320100d00556500b070b0041034800010130b041881e0a020485444030448060036169020000482a0900390122046008020300102d1126182d00d4103800c00c0400c900c4840042c032852940051a00c5114081021344100600401140d62080c11112080720380c020a40d806000612041d003980f5088510305c0091849070010381041081001072103807100d00c040695105074103021101c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 121269271 1250 121268021 121268039
    0x50a0b100f030e07080a030e0a06030b060304110f0901060302030411011110021e03010303050d0c030225061413050f0604020609011d0303030a06170109050d0509120f25 74
    0x20300380c040d0782c00c01050030580140020301348411a440040e1074001c403080c0c24105a40501d90454202c0110391032844191146030031012101c04007042600a00100302250210b044140b0340000315000501c003004207007141020481c81030013039021801082d0044188801c00414590080c6035000038a0030140322484034041c1a0750302d004180f42e080c2c20780e00107000c544941c0d84080d4860701200c0454045d0750781d41c0d00c3c80c0080c1981e0019554951041c9000c1e04107490610034003c82c0d442c4c2147d440c01c000b590076910350604148100300340890701ba41d81c030b040d40090b03000c17105a058400c04001300385010180190414030300b0310a000041c60341507045842004010b0740c40c1da0030795410031070a10303103402550340000d1401c410021080000d680341c4004001c108540049820440558280c1202c16001012200c03d5500340d98071600020030075081001c46a00b4540300f507010f40340b5403c1c02413016142d01e040c8101036040000a6142d03450940001801d10103007240001a0034441580c0341c6000c0e44589041c0b918 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 121270521 1250 121269271 121269287
    0x9030f02160b1602090403111b180a0b040e0c030c03070b160c03060f051501050909040b060d081209060117070b09180a0605030709060e011401021609050a0b10 70
    0x5568844000c626850380580f0040418038459018210007024200350402801c0c044d0001001c0b2601c3c85040c90007142182422081c20b80c00401130700140310250040301100300c01d04c004181c0400c1c0c5a6460800d502175072140260300d5101c800c20013801da130341410401d150510010f11032090095005800401441042d24100e4140a00801f0400710005e158541001c261440d6031016101909000d034802c44200c0c1948000d0140c20065600e00e1640a11070056a142c022410b0b0300d94480ca500c800100031804c1d64142990001000300889280a06030760f4410b1650040a101c04151403040200840c440080002030302502d40350050105180e415500c0d10780d151064050308164090200704056142c0300d800008000408811030501d60345072901c0e80c04003c01d024401d003071280c414801d001582402a2213000240d489aa851500680c2049010a07580255000c4a411440b410700e001002010030094038010b005a0b15001c034650928146c400182c5000c200c1c114820751001c900307a510b0031341000c00d03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 121271771 1250 121270521 121270529
    0x10c020c0f010c02090c040e0f04050606040504060e0a08071a04080d02070f0204111306030b03190206040b1c0605030102190305060d1b050102010f050601020d0c061b0309030f0216 79
    0x44809003031140004070796a4103d40d02c001e4110390100c040c40094194200600103070703100b06020000301c2c1e80b1102d820300840d8095230050301300c3d0041004624682001e802031640940103440200d00088200baa0324a08000c801d001c0e240c110022500c0d004201e4074101c03800004666008601481c02e0503280d000c4c651160401d20703035003036a0006803142082018052616002d8009000b00000941c1054201c80f81c3d01492002010f660300e41000300e40350780244141c0700c2c0300c2c801400030328008443c41039940700b1110070941039900c50414800016010618001030810f452408400d1b0302d0308a4180c500800d079034082c8c06c401d209034010b020810400c5401c07501c0c0d00306008145000b15894407800c0100303810b080355100243c12085607180d94142d84901c1c103861000c48000b030380200491050200c0d03100842d8810750703c0b140142c0161181342e1415114100c0201014001d0100103040030b4400286c005841d88091800041303611480340380107141d04100c00304088038071070010303001c141e0038404c0c0c03082207101c00c2c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 121273021 1250 121271771 121271779
    0x10e0c040b03071814040b0a030816080405120102090307080601030308160c02040e03030610230a050c030c010b0f01030504050d03021305030102031f05060f031504020702190501030e010c020c 84
    0x1001860f214404d40c8001800319030300003511010780d1503220324541d07180142546802107050101210344c6080441c0c2560450b500030b035050b414992040c213540c4011181c0001912010428000850341b0343e01c80004180c0c091030306d40011b07552640c1005050900c60341e5846032900b9081a001000803e40140030241d000d07819400d01c1e215500315880c1a907048820000107500b0501c0c000e08031625190000045001c0d07102158441c1121054003c200d4015240902c003458028000c0d070580c006242c0d0002030a80c85005047c60f6040c2105500014a1500000d41c041500d80d10b91020042d1750804820702e0340350903428607041c006441e040c3c503000d40d074071800782c0400704040d40012480d00754031102030381c0c1000e428000c0095647c0d00303010030650071400820010312086580e42c080010245004801c80300d04560f0b0f581d0316800d641e40e0032561034080e41403442c0250865020132400c40141c0d00c208101c07542094005000d50b80600b4500014101e41d000c8a1035a03440c4c0c58191b20003061a000201c0202070300d400c031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 121274271 1250 121273021 121273027
    0xd090b0a0204080d02061b030709120f06240510031805010c1713030f02100606031d0703120e060d0c050a02100204120b04050a080c0a170901050406030f060308030a14010e0c040b 78
    0x3d0100c5622a066010411000c60502f4250802c42c04002c1484094055002400000140020421240e0032008003045a80781c1d0b680400c058104500d07050790071501800c0c00100b202805c046140c080b07010600403903269540b01c00094446d90024480074264844041500c1945841e08001c490318030340b5000501400000101d0b094050310800c207114038541c0c501c0341809201c1d95000f010b009007010007410700f0102d0160b44024128000003c101c2c0440782c0180d500c04c58191303444800d03103d01c0701d071000d00c54200700c0402013580d40720420b000d61814111142d4800d59100f01581d0000d04100d4241c48840100f40104800c004200d0680c1c810fa0303041c0e4101800c101d1507100ca1814038507008040c04000d01d0041c001c2030364600010003007042c241c000d024200e140c40002e005403d5000300c6c49500c03820350200c1c3c0144030600085229900141002190800004003c0c1d242c2e11643da00382c0044582c0c1b98843c0c0c0f1034480010b2000c01341144c60040c5081c03508403101c2e0914981d094001d020b00c2c020803400e4032000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 121275521 1250 121274271 121274281
    0x4080d060801020f07110303030721060807062c09150103090b0703150f0b25061517032802190b0a0e06100504020d090b0a0204080d02061b03 62
    0x1540040010001c0700000c56403100040090b40068002105c240c13140c454200310301c0114140401103a101d18242c0c1c0d1981c0590b866401840d1982d00c0b60003e207036025903501404035031443c08000c210080c201d0f6403504801c2c084001d4100b01105914802d0f10007031626601100e800e601d8490104d5009441e05600c049609040401200103045409019019070014024000317096016817180903d00040002d8100e8241c035500c6130803010006200d0004070707001c10416011208001d082041741080b42c02e403640034418040c0c9855050342c500c0d100044054911103c10003d00081003035070008880980701840c200355008868078481200d4003000f1400d6418000555103181c03091103d0420b821844801d101d0043d4039052080060504851480b006450701b400b0384030905000800a201d4040c20445101c1070381010300f40f0000c2e40122814140e1035883d5840a00001c0340031a0710f5216120440c40161264503080d0f0301441e014840c02440155007085081c0015841c0c03076000300c03407940112040160b0f26220 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 121276771 1250 121275521 121275547
    0xc0609030102070b0109060807050315060d0f060903020c090a06060e060901030e0604060b0102100e060402010c0303150b031608010305030f0913090b19050601020c0d0510110a02060106080606030408 87
    0x1c0c9050041100151340f0001c034404038a90301150035135060343d044402041d203070414560348000d56290520125080c1300040d40e00c1c80d000b42400300b0144660608400b401c1c07961748060580360081e8007200560440d074005481410a5032601e544540c41c80f00a00c41103107031250140c408094212124004c0a0000d0101e44590194009034811400d01040303038200c1ca420b05110b001007800440086c0140030b4035082c2c400c0d41c1c0d142d015000f25050315030046c00c0c403034480780c1c0107540c0f60a107080200c040c15107407032134a102806403820701c00081c400642003503036910301801416088200000404240968940144041200003040c0da01e22007821960f50303070b90354170000041d00d84444080340c00c410a040a2000c0c040001011045020b04038003207564540160301c803801d5042d500c0c101c803101c0c0107a02850440318546005048180840d000310243c40900340c511046d2800c1c1c89a0b4501c2c401030100000d1a00c0c1815410010340d0b00519803494195035a007464000218684409040500020400700d004115040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 121278021 1250 121276771 121276777
    0x3090a060528050a0201200d0518060a15120314030c07171b0703020108070309020f030d09060f050a02060c180306040605011a250515010914070c050c0609030102 71
    0x1034100a0540c841d440d410700180b496020054680c010750030700ca1a000503087e852403100c2c21020719003050741400c001c8070180300100303001081844000c00902c1d41d030101368814003040340a806000d41c04500f904950010b842d0094a9a01a90740c4066441465011075480380e81584a1255072503e903a813511038200360790031809280d4000d000d07001e00f5000303a002c4040342c000802c0301552103151780c1300d07240207420007544402da50320029002c0703046c4000088441f031182d8483d00899100616241d001000000840d29000c1007a5940d00810300070300040c024160404141c41d1801e074545821444d1204d0303840001d40301c0b00b015124105038000428403080c01580c2d00383d01c05143c400a0110cd440346414102600541804e102310480341180d89450304507512410219001c00b401d19140c178441d500f403d2000f000390040b07030405907841d001c0c80340c98205c08020030410500030f0520034004151240c01030080c4003d141702034044414850310041500010720701003145003002c842180c00316200c2031080e000ca400381c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 121279271 1250 121278021 121278067
    0x1507050f030a0809010b13050703140c0714030a0c1220250302010c140c150901020c1c0b100503030705030c010c020d0503010e04060b1c030e0303090a0605 68
    0x405400e403114448240040a40400c009654070031405480b80d581c030300d00300e81345038002035088400c0d20030382440300d016a001250010468500050811840c0c6490106000c0035103440240420008441c0207000e04071055901d68481d11014501d00327010890003414074024148020300b00fa1014401d141854080c06506411051418030313403050201000c04552540c82d0245406184d40c1c00040140c0448000003c10301a00d0b41038551a8261141c0c0d20b6003241000814240d1010340300d020050b01007900d85813803d00c09588407031290b41c0c4500a8400181c200040748112500450800f90030a40e84502018003000c020340240c000c078801d0320740c0c01803c000c000340307a0440d54142c400000c80303101704038000005141d00010740d0020411240d008900b240c0303d102c103180343c1000a80a100611041c0d400904c0c00d9000b5109010016030b640010002c6500510400243d00180c59032090b60003e16400090889402400714080d605c0c0c5001440080c44c039440c0b6014001c2044004180040007a2002c054500c081e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 121280521 1250 121279271 121279273
    0x4091406090c160f02130e0619060f060305130f030801031104051303030507020a02090705070b18121b010603060204090e070503031803010902060c0d0f0302040303050403060b0d1a1e06060405150705 87
    0x82060681042d50b401c001c0c2c542c95030134000039910b01c03509c41d00f1748900800e071221040c000da0b440d8640740046004c3e000c060710006000822652110015040d440720040039882521040000d604d141090b228520301807000a0280f41080c041004178001296401d8110381d05060001c1c1c6921030395006c03440c0407a0711348001d401250798020f004030903802c20058410746120b00086105541c03180c4410320a5080241403000302d51040d031804c4008500200507100c0b41d024810303400c3c400081001d1490946071903a0084e525180e00040c203020340012402a1945c21442e0001040c0e283d01c2c01e03000c03d40c1c0384140c2a407800c40380c9800c903c803401c968081d00007901030381d0020200c1307403110200030032240c80c3c0b511445036801081c0e03064880107209005c0e00071340d012a40c058a51908103481e6483d03010103840c0ba40f2300c0070b5002c1c06510f44da10020308c003101c41950b54100d055009402d40b610110301003a00c01c182c2d00000000c007c1e4010465183c0d2554219002e60384251150907050f00d0719000b04a5a0143c080d005000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 121281771 1250 121280521 121280531
    0x15021603020601050312130b0702030f0102040b1801020c0117061210020d0606021b04020304080909090c010801120f140307170c011b020318010504091406090c160f0213 74
    0x91550010310307241602d40031016503103804d5210140541a00c247e4050309241d103030280b0200000542e00c4050300049001509542903010b00c03140e0542264429002070001c0180803820006c888001600d0400910302800204002d151250003c0d00180010400d050581d00d04000500e042d1544c280c00d030544400e890484215603024901d080194100e05e9025000d00d2070014002111480041d440ca84000c5d100641d008c2e0000384401c5c800a544024001d0790308410801940f203081d1a050700c0c1c64807076030030300000e4600c030802c0c03000040c803025042c2e216844c000c403c4c140580200d5002960620000c0d40b00001c000001d8042c004981540600e030400b806015450101d5164610700e800142800a00300000b0070140354030206100c6000c030304403856801030348240176810404410184032820304605040280c2865601d80910083d90030020322000910701060138072105003402c800352604152245001e6082207095081c0d142c0500c83c1003400b420240c250740d2220155102da0011095600b0542004e102d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 121283021 1250 121281771 121281773
    0x403120f0e0318040e030306150309070e0106050c0708060603030f070c09050103081801020102070b0c1303020604080a0b010b0a02030901140d02030a0207021309050d030e07050a03060c1416150216 86
    0x12880081d00d0f0114040c504001c0b00b0040043c0c08400c99220703c0d0020402455543d009030a0511a0802417440c0110320030f40c440410b680d01c2114a0301e00810b110356030f0b10f507249545010030703003000c40c140e100c0c43c5964850002d004060750040259100d9201c0c0006094844816080140ca8202542c1c010f000341841c100001c0244a0658000d180e0081c002d0544010380590800482c201c0c880c403a0701811400080f0041507181551200609107107141c24248141c03d601c0703400007589540681d004201d903170300030200c0104000d05040f406004081c0f509005042070200c40010303440e84612202c0302c0c1042443d2224448540f181e505a0f040100305040c2191207261401e070b824002d5201080a910580303901882404495050280c00c82196210000d08049144203030258040e01001480e1601c0340034402c070128158030f407054410015401400003003004c1d10000000b404040c11000801c0312840f040048120301c048000e81030b02c60383c0c0d201c88024540029000184028040c009501002800c0c08002078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 121284271 1250 121283021 121283047
    0x3061b0a200109171c0203190c020318030a02060703180816060e190306050601030b04050a02040914012d08010e0d09090e120a0e0d1412030403120f0e03 67
    0x240b03401c1c0c13060310a120003020780031000702e4078003400420b40391a902c020308543c1d94810580203150895890115100410b0402622038245c0d0b035444c50b50300050b40081030219083c6145110350303031a10b030103602820f074004440d00400e403a81300300c00000e41817050210180a02440150200e801801400c1c03c1d94901c03800059405e10b8802035100302000550050380d80c2e01145403002050a401d1014615a02051710750b81d1000050700000f440e03035050583d180441e0005031220301540e40316140343c940040c2e407517040006140403107444e0400c0440e40150301c4010311440c802108154003203118010484411409451000d98483c0d44da00308000715400e100700100d02f004009039000051050307890b030307003c0317030f074695103980101c03900080c0110080c0e2001d01c0c4c1c0688801c8040081480c003100340b5103d8a03642c0080085406814210400c60b014001901c0d40d50410500303205a480340c1d030a04004901e0340c20b00d61070040c280116841d4204125603036103036190ba2480603170320000c1c842d20044156511804400790072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 121285521 1250 121284271 121284281
    0x408070b011710111602040b03070e0406050c0307080f0928030f111b0a210308131505070210050108010c110307260702030106091a03061b0a2001 64
    0x203901e520800140c88004440c40c010b1212041e00004c540b41006010780c103807074842c2d585010980c1c00c1655158044929242230001c0e00240408078510301c1c0500303052900710b084403401072440380360700001d0051082541e44050b82581004540d2142c401645844d5116400d1045c0404003031200c0704c608031050f407218021110303c1e02490103615081c40304040d50b482601d500d20082c018142a4008541082c1c0095104907c1154980042c001c82e0a864494060825951a6050023080c00b00c20080c0310040592008045500c10080c101d00c8406402665442c84208021625107071b0f003945039000255598070810400035601d03585a0240a65696000501c1c028540300c076035940010490002040082c00c0042111803841d480468407007a00c100909a0041161981422171024410401c0d036000d40e50901840c5c014000b2640d0010b0350030250030b0303180440c4580410b4a4000d0b001002048004003158a170b2202180c6c00440c015a00c0d860100201c03190034114503801a818030000080064071815400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 121286771 1250 121285521 121285559
    0x1e04120203010b0405070509061b010606020109121d0607080705060c0a03060b0702240705010204081006170607030b01020309031c110a08090103090303020909160806040207020604030b0408070b01 86
    0x70810030f0b00800c140000c1e24000c44507140800c60030484103245003008001011103007006801c21844003c1c154005003581c046030300460040c2c0d1610500c03024040c40d001c045032243c14a090160a583c1050403000103480000f40c1140b0a000110742d52060003460801c03140c0d0f15070b0080c196101ea1502c03a03248191508540c454200107480c0c0000841d44400c1c4400b11400f5540041c80d02c1c0c00c0300706040c070a8a2002034a001114558014030070340000480c01d0000d080a40210405481c0c6540740304a51001c8580300ea0001c11300d084681141d00c5150b0021812030307000001c3d450081600a61040141e01d036104006c542909441128078914410004407004400020740d40e9465048406034890542d884500c888060a030034401c02c003003034031503019900884a080c800d007009401e000d805030004d4080402141c0035000b01c500303804141d0b402c50303001d802c1c1907100c00211000c5050102c55000318a8602842c040100030104810200b0140806042030310590382d80009a45030542e1211303d9030701c2d0b0b2021640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 121288021 1250 121286771 121286773
    0x10320060d060e070f0c0b041e060207031e0c03030902270f0705091318080c0309030c0118030f020d05070305100b01051204020d1a0109150b03010303090b1e04120203 73
    0x101e00c1661003410603189081059450900c6d0f090785031140450b0b80d0307001d08112814880b00ea2201c40065089403101c5c0414003500d001a1101d00070f090242041c4110005210a00103c04440d102e05401145107e085a01441d002550b1f0b403242c0b010600b2004410700303068075002c0b060200c241403412007400d244142950140d0350001d8a449406070741600030561500d07802840b8202d482188c5c42c0c25488101d50b14100303101420071500070b032170742c800030351002c020b881c1d0f0351f00000381c050007e041c00c204090844100b0329000c11240b405030ba00f0251030409000045c00030168055044c2076659901010314032a0700001038468032035807881c0442c0d440e100703940c01040203810b00d0005140c560003072050352002035551031a000c82c0c0d81c5690030400da010081000b19241258407500407412040c8450a6000c2c206204000859140f804100c0c039401201e40d00691081e9410001440020340c02480c1c0c00032103040c018466114846181038041c820354012107290621004075000640c1001c4044041d12140260 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 121289271 1250 121288021 121288049
    0x10e12070c050604050906100c020613140108091c0903120804020109091119050d050a15082109031002030c0d050c0c0706080619080a0501050c040e010320060d06 71
    0x703010f010b103e006511a4551100708000080e401d81000382c245580b000062030070425880c0554005a1143c00c01c5141c0c001040c3c10350300602980a00f030302e0301c4400039402d0904001902c1c01c0d11a1540d00d038000c07004503107010804840703240d80350300590052000e55404480011001d880e20780061225000310ac0983c001605a900000d2880052140c02c914a10b074903403440c40d09024081103005c1000000240081210401c2040c03211004c602c1154050100d2101c04190101c03440700700318000f607640c1c000b0b40884d0408120401403030021000881d108000c03034503080c2c980440c040002d05201c1c8440200185d03500010410662442c40f400030220b0501d04102040039881e80e1106403c6400340035441c5685e940007003010b00c40c9501845083d070707004c00c1c0182902500e10941009810400c030b154000c000ea68005145601081800c1c002d0a9000003c414281c0c10585817031300e2810414018480904540c17142d0303403403645138941030b10351400c03820018105035603800d045500c0d0b40040405100f4120074140d40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 121290521 1250 121289271 121289279
    0x1052b1b0807020c0105030402011403090f0615010207090c0e0607051f020f0a0305100503010603080d0c02011b08071205010e04140601080307081315050a03050109060506030711010e12070c 83
    0x50440c9a0040c2090b0f401041d803150b000005603120b81c80540164103204413081600031100304a0001c42c07003000c214015000c1c035090107565518208bc081c01d44102c8400c0510103410300e90f400542d401c1182d90224001c41c05200343c4000352080f003459440b0f0380e00070b1070004411040c0440000c000c41400340c100c18900904080100c1c2d04105d000b10800c00e64665800c0002041051203500102d82218200d1484120280e031800064210340042c0d00403a14183c000c1246907800869214035200b510850000703001246141c0c0354422142d05418140c8140103405000c41c3d0f100c2e00c5080166040d018801c0e003040716507101d500d403198481040b102183c0c840002110301c1b0940001152a5040355841030003141000da0603036a10582d0f410030860f1480d85c0d00c1c40301c0001200013944182007407a144036222290385010325980103040e5541600070714012400c03c4010010382d01e0b9101180d500c800d80c4e28245500200496503d809000c2c4040318030628032552002d54410b1400070000c001680c41500509040c0785d171 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 121291771 1250 121290521 121290527
    0x9060703180e012301110f0c0f06070f0f03170f0103020310090302030f0903031c020a080c0403050a020402030a02160c051e03070b091206070503060406050f0d0201052b1b 75
    0x400d01501252201500704c4210030084010904008041410301c24803281c16401a9803400030f40c44240b00389944175040d14001c07820444001004580203a07000c2e407070300c107041e1110407405456500c01043c41304d50742545014140704e00f041e05002403004442002034245001c40c002d4207182800141d01c240900d2030840840704191207071010095040d000b9600300398242000303400c1c9800010102d81c05003c1048500352284903400309030841c0384c408800580710459901d00401c2a5030081013103425600030001880030880000c0c041030540d5040b20003580c1ca07510008802c010303016900080d66181c03c51105101000303c840c0b8404150741c02650410020650520414070750f120401150340c064000000a110110760600200451a4090020030141a000095500e00a011505000054004800c0c444ca92070a07004040003400202c4903400c04000c4c0400040060f0000d001c000e0500c8000582d621300040d49040e5160104a4007112064050b80c1c0140c000240170700d0422342c0c0510001e1900b20740c820340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 121293021 1250 121291771 121291799
    0x1030b011707140a180507030c11120702060d0c03060302010806040606081603020f0412120f0e01030b1507140c0a0305150c091c0303060f05240906070318 68
    0x4108014444207243c110107408180b0045000c9400464400e4041103864114076502803011410030005070302c1c0380c0404002d049680152006c0304002801007008424200081c080068080c01d140d401d0307aa401d2440040c0407440740e41c5809543d02d040c0683c4541140e050380c8110116030007a00d40041c0f0340c0d0382900300400c480780c5001c0c45011035603c00100702039402c00200c070000741044e42001498038451a08444c030542041c1d1051440d002011100000c000b1140d200c0001e4070083c0c14003014150342214050215108460528101951840c21041c9603640510504034a0350450482ea920111820f0a60031008980d014003c41e2140b50107202c00360910000c000c4c1281c0e000009045200481d2000028400340907041d031a03022014042c00380d50790342d01411444c641d100242c40008800e01854040c00f902c50503802045001c03070105040010780c8400e0802c01260600d000c0c0c10761100c1d69818840310a00920444540245021441108041d004650045040c101002070b003a0b4a5640e903600320040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 121294271 1250 121293021 121293059
    0x90210030213090e0c0d0b18010c09050f0a1502210301050105070b07170f0601120b03071e0e071115090a060b03010e0610090c0201150b0c03040b040e01030b01 70
    0x500144010001204654803080700111343c0003e44400844401c00141c101c50700c01015140c2c2e08240c1c0a1010041c201e030400011145030400078480300061540240903005240320f4a0700951091081c400140e94981c09140a0820003800705c40903084010000d5552003004090701f001020035507142c101c0c000503c15281241c405039903082c034042c919a0f40003048203001d002002440034105098542c0c2c809510118407512203c45521202d140c40c2c00010001d00c06505a0b0100a181c90004d0000d030700c3c049440020781d0110190401410091410109040303c694014503540c0840014002001e52040c0c400c015aa0300704101c485443d41201005000b00d002c0e40e0b81813a40d40a2442c41000401640124a41071801000040e1035000040e900d400d00d80200d84062100e004c9060600883d02c082c030032000410318520080040c80e83d81411070f0802c0781c15000701d49410102040c0401042001c20446002c2d04244d043d46888507640d09140c00d522200380000c48004002074000701e6906110f140406102c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 121295521 1250 121294271 121294297
    0x1510080610050705100b130c08152d270106030c050c060f040804091a13060b0706091b0b070213090b06131d0604050c0f010c11190303030902100302 65
    0x3540c200703148401040304c000d03403c0c6c102a891405c5840b1540230f200b60500b5101c0354890041500d011816110182e4013107040034414500c010248103210034140c003041d5282600301c4103104408001e00024408035070210b00030044000441e0b00150001c0da0310040b412186207480a000c0f410010b01c0a035818062200d40828551040c4000781000b00d03a04115900913019014070340c50507450b520b10000341c030749801081c003400301200c68080441c200040b4071000c104002c1000c000c00d13810088043c95521620001a213107544620f00e0609106886180305982c0b02c100382480d1400350354000006040c0c000302d070168442c3c581d20496110445580c00340c0e1071216848800248156076070002c00458500218040c00b01964444c1c04a9110705100b4080c040f06020030020f040b14034042c607015190900100340c0a0140060782c65100e200d90304025400c440640c0455003581c403407001c4c400301d03030001e240701c1c80c1424810005400000307268040c0e21203580315000f41c2c1d54981c000c0c0c42c1d03c4160140d100300d01600c240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 121296771 1250 121295521 121295533
    0x20d06030c050321090a030c0b121f0e06121f060905060a090c02011b03060302040e010b090705070f02130509150c04061d0d11030f0c03030706051510080610050705 72
    0x34103807241e0014180c0d41401088082c00310b889881c0c5c7c4210310910380112715421000500d143c614000f0509040e4807134001c07100e00036042d40c1c264200c210180c407032007102c1c440405200894038a940f5000410340151445040381c0c182c2ea4003400d1220040c54580422601924040c00401c0352400c1e8013807544282009008203204038030b80300c4441700410340d80d1b424000715540d924600d0070016008a801c56080c071150b9000c144d40741540100b01c100c880c100b0b0005016031502030b10311010380350505019803100007404c010713842c3c0645040c100c14000c920304000394000300920020102c81d00907802140226000012034450685c9800e041d0b400e08400d94610f0200b030028041040981e01c03910490f190800c02c00e594042c81600d110108141c000b108100b2600f6442040c003038040750030200810b07624040c1150080a000801c0b80100391a40b0608001800d001d84420020340241e015001c0700540100280c01d80300b111020510041508109481452103076180c1c04001e85c280f4421426280780356084000303428 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 121298021 1250 121296771 121296823
    0x20325020a02010e060705031905030a0605041a040b030a0501091208090a0f0228030609051c1d0402090d030306151103041509030215070c0b07080a0c15020d06030c0503 74
    0x40e142c1c0000078207c0c0d4501c810006554865072152187c0043e10482e100c444d01c0341417a180c171905680540d0860340c004e91921107a26183c0d603241c50a104811025103000896460290200e418070703104540c090179035070030006040104000e045601000d010113540f5148136440c1c0007441501d0700900c09000d03008201810b1705c40054900320740101c80c801c946c803c01400d0b500c284011490580c1c040d52041c1c0b581961040c030030040c08024803000d21122040d2060301141070010707001408a42c1540303003418403a508e807021120603482c1e0b54120348014100a000210240f29480d008024100364011104a00011035040c202d00740203039882e058030b10008029600b050308011032030b249106005c008030104010980000090785480240b00365620481c0b08055072401d15050900d124502c80c0e00c509040b44081281c540403903400001c0e00c004103041c2c50300c0b031103040f0a4244000114000c4404141e49440040c050101c1ea600758000d00880307103e07110b08243c2c59030b50350425840340046960510090301c7c04100c64 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 121299271 1250 121298021 121298029
    0x1204060e0a09020a020334050609010c081b0705010213030605150405060105070615050d0b010906050603071407230d1403040503030402310204061d0a050103110d020325020a02010e 79
    0x201710760075080110301c14515861035202240e087e02c42502c0035004501800a0000d0038000c00c1e6204015041210b81d6090140306000f0030705011001a002c85000308105081080a40403a01110365464640958a0300c904104004000a645002d80c0b00341150302c41c01c1c44d0419000c0c042c030440050712080d00f0500c0d607445034009400090b8900c800340351000c0c0007091969400c40d60046140c001e1044415660400c0003940807540c5171380003103104210504c10425400d601802c115803400700b030700c01140c882d0380904d040d001d13184050418039142c041140940030104d07400140203503050025034400300d01e180c2c6035010401910007918044c0094108000080150510413103000c440e22240c8002c1a800001140b480c000101480d980145950002401c0040f254440c0322030b641c2e0700f00c07418a81c0e29034201e80e001a070a652107100b514141916a0071010018500c0420b840e003500415109658a1810b022898060109214a4602d10701030780420404541700081e1400641c0c0e06844200c0f08809502c100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 121300521 1250 121299271 121299307
    0x10b01031b120e0102120610140f0f0c01053309061903060203040303020406080601111e10020c03190813111f0e030601060c11040903021204060e0a09020a0203 70
    0x82121a03160b0f0300c03100d400c2900740300800545183c02410801070520b941007106410000481e0410008490f02e0084444000400c0314001c0d0100e58249603200608649480a40540d03800d0241d65481d00040100c051405030007201d0329001d2003400d04040061849060078080100c02041e049200c1100003000c60600c0a0514807181e030000001409907901da9505041c0ea004407402c80020f034011404005040d001011150000001d0820342000c0e0f02d20f00700c40350b803201030300c400c00f000003081c0301808421071090005024011345c880040d90b0700e20700344080c0d582d80e80c0000002c1040f007c00840c49500070303108010f624003c070500130303020991009a0320f548a500c05005110707a404901041c01848800381041c03986002016078132203c903250f4400d0201410110164000d034240605030b4024000900c0c600350f0b050420004072400100b1440c0341c01c041349001302100f0a00008400020045500b58200402e02d803070b1001219100c140139110301d07500c8181d002c0c0c07a82c50f0000d6802480500f403803806103140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 121301771 1250 121300521 121300547
    0x606090901020f070602090a0e040317010e070f0c0633051f030b03011d0d090905090304050925051207020a0206030402061605030a0e3a05070f060e03010b01031b 71
    0x108149289e141c0e5040e40b6000c00980c0c4c00c4000c50784c031207a0040240390200e0880c3c01031840784920303e40e07444c216501800c0280f1002c0e5000c104903803058004100007880d408440e021041d030b0b1400202c03484072141c031800f0340c20300e0503281c0c000075420b100003820b8a843d084206c04840403119221680600e120190040c0038207004156140d52a900704e4080d81007515500c46401001000400087c4200b54024010b01c400307400041a1509140400c440320200100b00c60441d80e06903a50310180d034544c3c449886032240c24004c00d034006841d01c4110b03d02d551020181207a6040c8114455103a1079020051b6a1850752190094009100340000390151801c50007400003280d200d5803804807410107a80380c44c11684100a4440481c901d5096644a801c00c10744000080480c000c0c0c6a81d40074902c0c0515460780c000c403402e0b80545d43d0405481003004000d10458004003090401d462440d030320313054094501c80c09201d01d64060361803d80e26601070361280c022240709404492155030800b501070030880c0c0703903007920503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 121303021 1250 121301771 121301779
    0x150b03063610050a0b0415031e050c0603071112032401180608090106050402120406021b07030f17070c051005041a0702120706020601050f0406090e0606090901020f07060209 76
    0x50142c0342407070140101d030b00c01d500c00d0320002000c00c040402c010441c1d21040001000408065040c0300041140090300b80301c0b040044c00740c00007a07040c50420301d0700408550b80c0350081804000c4c04032950b01b140b80c041c0200708200a842e00c4404070850a12103010451700c005000c494031414045092101b0781009100c00180b5041c1262901d5074010786134030140344d01900016120104010727810398203100c1e41028000488082d440c10302100e020744206d80001d0700141c00300f9400100c0480645007074aa45c00d4441c440825669015a20b0508040482701224261580c103000f4450403515482182100c44080d03018440c4000c160800c01800708001c0004910418403504101c04507a046250841f110f024104c001c085036120400d10610040c0400381c071281c44075074054501402403580204106054038803e031102e5008450303e60004025042e203034001010b02c2e14028140702c46540104980c1d1048405480c2131410b0340f12036603068200e11500004d4070b511101446010002506600208143c0400070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 121304271 1250 121303021 121303033
    0x20f03090616021908010b0a030f0b2805040c1203050d0e0c04060807080705040b0a0905041707060923120c010e06090d09050301020307080a050a09150b030636 70
    0x203404114a44c18111515000c04020b403010030a2020074040c1d070391203140959400d60800c0c595500e903040c2200c4624024071134460440024183d5919600c04a2030102c0f1240300000c4840c100070325401800d05480643d031018101901241c03000003014007080781c42d403643d02c1d80c0c5008850450303500202204a030740c1d41c0380d0041c441c103040e480d03a0700e0045001a00056024100862804001c18a01200c81d0b00c06405035040c10354002c0a50f40d00100c12045503024030000c03d0769a69460106444955010180700040d00440c440c01440762503440720301c3e0700b486000100c080030180380b02d9460f204003a400380181513100c1081006000030800240c00b4602902e800414429240b844c040e05000c400c0b03403201d42541c032000b00ca0021390350020103a8010700c0d098000b14550700f4060002844103d0050610106a44440104e4402d0080758032168010303412031000d0b00024140441500078118001e1498403138861100464040308401c240812400c0d440c524561152211078101c0600707400015402d48140200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 121305521 1250 121304271 121304273
    0x5090a0b060c0706031a01360f0509060f0a05060f0705030318070e040b271b0406080712030f02100603030f03111219020f070c090606020f03090616 65
    0x44024204402c500d01c060710499040102c010100c034408110380c14401510610400702c0d0760001240f500b40911691694114035410312078504030340c48440807100143d01c03144001081d070700e08002c081c1940c00c100d80c150019110401004010025803a4490380301d98031160410082c42d290b0018646604130b61112410701d50151038150468000722000c01c0041c0002050f41d5a04e0418001040580030b400c80c05255411301c0c2d242c1000c1050020207030301c1d40411006440c900b45401190b016022000e84080792200c0140c10071000c0729a103030341c90443c011800d0440120340c00740c0101c0c030300041d10400010384642e0141502d0440e002c95984402c0001d5000c2d07006c400340500194026100514046e4881c5010030561260040071110031488003100045c00f80840c92201e01c202c0170300368204101900028503a6524074400b0002e00c5641609c240070030700001d824040017003c1028400329a40c640b010071016543d01c0c41640c41e6105007001e4143c0343c202300840c4901b031034070301e0141410000e404c1140030302c2c0d015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 121306771 1250 121305521 121305529
    0x140309100e0a03020a080d0e030a03020c041d06250f120902190608060114041410030e03160c080c150d090c0b03180d17150d03090806060301050105010905090a0b 71
    0x11703500246505d40094103208107841d0401c0e070315908100154010f161540590310025194a41603000034421900c4032511226145c1c0e140c40108141c420301e05031802070400640240011000f81c80e840409100081e071a03200d02e00980c96041d01000e076440f00400c1c46000c040440c018907001d0b008983c402a013000300300207490042c020402404030f6448141884c2802c1002500450194490034042c2800304000d002400c01c0340404009190b00707a9a41c2c40c0401c0169090300942071070040705069210224492510507440700f40111898050400b0002094581482a841c0d8410425043c5c0000700c1009070001700c00c1072401051901c0441d01c000540010598444074803000c40e03400398101e420b0110510481840c10840070b103440b00050010f281180e14550301074580540c0e034445005803010303000040c03201d40350070011450601004041121145032880d014004514074050030741c691240c0c03400603200c0e06052040034103a0304142c5500384101c0c1b42c17108000321800002e1001c1c1811703032107941200d540d0700c0e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 121308021 1250 121306771 121306789
    0x110409020a020f0c0a1a0d140907050a1a0318010b0402070c051905030d0e060c01051807090509070302151e04080c0a0e04030c140a030309140309100e0a0302 69
    0x301d41d0380030b00155560ba240301c0749000103001e180d52203200c030400200020011411042d01c082126080d440d00d40b4003e0342102c00600880140b03a41000c500000c01c103240d6008a5080141ca0040318141c0c501c6440301800104600c40200d401480442000818000308080d154240010010000400d4004800020509070381141c80220b4041030307511b109014614107203205003516071160004159480c0b13800c0009a07140351a117101c0d800d026541004450a0302c50504490701102034400034481810030988041e20710021488a00a0380203042d400b060010445c0a01030060050130010013a09056800700301050440c4005204003020800610300c120380d86200000000030b8038059079458500d4000b009040c2260540028810001d04606002c5030340c4410219400c1905890160300302015841d0400300c440280307900c0c01c92441511440c408059254008940003403081c014501865100075929549006910006500074011043c000402e4400c10f08683c0c203200c01000403907025035940100b08004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 121309271 1250 121308021 121308037
    0x305060316150e0d030804020402030a111305040b0a08070302060d140a050919030507060504081b03070c0501030504120c111207080d050a0921060e010e06070806031011040902 77
    0x4020311901035842e98000c0341d0441030402c19644096500060b9400500c0c1c0320001700001d120359800f10115060084135480350002c2c0d014008000e40e540c0c031305003040321141014820144190b0821640002c1d030305000901c0000c0380e2144008048040c2554200440c03500300145d4408000d81c1d0301450101d81d840e00184a004e10100711000680c2c0c105a82154145400407a0500c110441d2030300041c0002d5100c41100c40040c2c00c00383c0018580c85500d03092107039106024841c900c0400c0c488401c4c903140030110003803507c070384201d02605050359620015000e1350070494019000b8906442144486c038000c01109a440d445032a440a0405001340040d000b2038005411110340d40c0007078020300500c0c01c200160b0802003030908001d4282036001c9001441020940950850ac00400c00f0034000030094502d4a0310440e8490390a006220501000768001c140000303100754a449201e0104445600034006280070340805409041014900c461000c0540003040b080906030720304000000d01010603101810201c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 121310521 1250 121309271 121309289
    0x4240504031107060807090902130f0303080703050109051b0a121109030106240c05070f0909020306130314160b010308070b10060c0b0916080d0201060e0c0a0305060316 74
    0x1200ca1070030141c0707420038641050040c0100a414406c10030b0304000700800301d405044002d60392b030039071145104446005900030010420404030110406070003588031131050041e543c00708840e81c0d81c0d2001c803007aa8801d0b41e8201c00c0744e00444020354046500001050188004d0506402220301d9968060481d03ca000c2c1d111080000858148420300d000e0185c0c80c001e00703403990000902c0118001c056450100308200a0034080102032020800005101140040005481f41c01c4000d55896136540a00390380c250480c80381c041c070f000141e0404241443d0303000a980540d1041085c0ac06144c50000e540d01c00b8540e000c1182120049100140400035282d010754030420300c60f47c0342c02e018a810340c4032500240c504003005c0020380e0300344956075121494403803d941240c3c0c40c1f621074540e000d8050400c24000c0c407181c440014500007240c81400041d0035030100c00245d00801450781d40e154501c150070400c0d00ca1803a140d0040081ea60f42600c1703500304540010008041d11100c00307840074840703115401079010060f8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 121311771 1250 121310521 121310537
    0x1002090102010f0b030606062a010f0b0105070b06090901020720040c020a03140a090803130608091603110105090310090b011203080a0510050312030426030424050403 73
    0x12a507030a029201c41114040d0050080070100c8000070307103940004041600915022070081c0540c4c441e8103600344c060f2046c5201194a0380680b800703074080c1010400c4502c010342044010212548108100d800c0203400030310702e80290319131400308a00c060001c5c10b040f01d0307903400384034140c0414800203500c0951400181c0d5405c031300ca60202400142c030b0807920100c0940d000080c400010982064122100102c000c5902c0e41d2041085000d03141d08580b40c10054645c80081100c07030a120500302c091003946d045443c1c000c06507649890459884100c3d0340714103080d03403114804100194180c90340c03500b81c0c00141003850400100001291419503208034901c40703142c54120390303014407405400c0780e80500003000c2804141801a240640040c60140100e417220740d460700082d52440c681d55458000c1d260040c26200d55103050a00ca41150700292410350300c04001506813605103803901d02140b45590030310751240c1960b5954032050118001c4522880c15000c54803000d038009003052150b0340c442c9101e80c50b00d0788 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 121313021 1250 121311771 121311787
    0x80f0c04050105031606050a1205190e0d020307020f030111070807120f0512090a08130f0503010b1503130c0f0801050a0510140a03020d03020102030f13020f10030b031002 75
    0x1d40d20180d01c5540207400011580152004102111094a259040c6269110405541250060401d41c2c2c04500d446c6000180308030310b2140182040f100c08d107050244156803400c066252985046035039a00503074800c00c0f42ca0014205030902641240000b4000240e031104030550542681c0304400880d003c40c00000d41100704040303075108815602c15444c1564a00c015804050400e106069800000241031400529400001c06c048015940c0c010003180c0c9900071800c08801e160a14010702241c69440b140110300da040502c107c600801009090b64001c50040c0c914130321b507500c0504410541c41d441c42000010409a1560030014044600c550704400d1418504a01b11000901281003290900741030090003020007442c40e01340c80c80c001000e00007079105000600b01f00c0299000a411013400d00c550418585c040d805140300d0614450a00041e581c0c070159541408810349000354402c410f80809080c3d802d140500c40c0700f8914501b00014001d1848000030701c0c10940700500506a5000100a0303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 121314271 1250 121313021 121313029
    0x20604020307060305061c0212010615030b19060327030e010f0206070801180b181e040503040b0d06170109060b0f0f15070b01030f17040b090d030504080f0c 69
    0x500209860318040117142000d4000503c1e158120042003112151100d075035066681e90301e6000a0602103130020041c43c0d035190f02c0e40c442c261100703d2500c0401e207030012a810030b04103001e10180b000340c0202c0352448030782008000d03001000f0310301c2e12418500e01959807084500028820308a554002d8031407019186600c4d00050010000d000b002c000c540200c2d092003c8290000d021300e06648079440d020048143c0f0541a100030180103101030f502500c0c15205910780400c807070703001307024800e04191150801d00c02441c410b0300c04001d40b00101107901c00c1004100012412001c1c0c64414105030020403001d035108031200401400c00a201f1941c2d64a80c800010412640301d601c1c81b4036803d8812740b507100011030001b0b241260300c01c04030740101302c081c0072181e90b40d8004c02201d5101c3c3e40311900303800c00c1d6100d0911098020200800b200c00d0034034000031001075240d502c1a507041b0340f0b00c0641e43d89000c944100340a450140b0080440c140003003030001040300a404d0050a070040e00000050010000301130400c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 121315521 1250 121314271 121314283
    0x504050901090c050306130f06060e03060f06030a0809040b060712170912030405070b07080c06060102011116050703020405190f020405060403030507030e03060c07060b01031a0120010c0206040203 86
    0x240c00040e142c43c030041c54454002c402e40758003050407105040b01031580c07194803000e42a03140c41242d24034a0043c000c152940c01100c5000e1101042e421281503503180031141c0c000c000c00b500c165505034020006440005c40d104010f142e244800b820209055841c80c02066151b000391404686900b028408204840e0f40824464180f80c041101a40317542061303104213443c2d0b0a01c24881040480000005080c00700c1084850b00812031a4091075491400c1d0814903a80c2e000246406024000c40c0007080c550342c414051600300a8070004035524003000d5404104101c090030700c0490f101d00501c10008003595462203094441e00e821840301e907010281e070b9040401c44150901712004148188028400c030f44500081d20705032641400c1c55940d81c101804c0c00d1301d0a1020500382d55041c803072601084421000000688100362060390705100719110200154281c50b40c520690640e043e01a000d99100c0d8891241441100e94011b04a11180c00c0ca0301c0d464251504030b1341040250348040300f03010441c01c4c20403003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 121316771 1250 121315521 121315529
    0xc0a180b090411040906060b07030c0311030a080c030601020f01110306030c12032203060c09030314070b0411060c0102030a060312090308041811220b04060203070f060b100504050901 80
    0x101c11407505941e5081c00c440c43c24038a50140340e1703e0242c141042480d130b00010140c83e5049090f900d50b611490020001c2000007c05c60015104001d1000d249800100352400400747d610f840c2c105654001d10806260801480c2c00c0c1148546200240001001e1186852000311250007540d030f0b26005050501c0c1c500c041101a00078150203070007034481d2078017000351602c0c007440303104216201c4000f50b01c06c54440c0c550f81002e01120b01c1c1014217118240c00c05501d50440388603886906030410009203002c1d10b40a080c9024001824030000100050300e491503c5d9181500100640e0030003200105150890f001203400568541c4c0c3c0d44401d0060100d1001880780d0417005140c524030b420b05560309d500f40c50080c1d100d5042d02c00c0900201440d2504250050140f050064041d951074140c0a80c2048140b800a41058609511041c011480524042c116003d41e0525001149010003568800102420070041544e804c1c1d65214180103582c1d031040115602c1a50381c0d155510b85043c6003c102c64208180c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 121318021 1250 121316771 121316779
    0x5090307050c121e01050f0703060513090203011d03090909160603050405030424030501050102120406080c0c030a09210f030c0c0b0f07030e09041a090c0a180b 70
    0x18030000548001410101648182c60081d4103072800003c8034681408400804840d2039000d00440c8948015800035200d0708200e411503520740ca401000307070101d60460050350b8000b070b601031720748000ba103460300440c0701544050000681d204240d0500741404640c0f81030049150000550001c0d03900d42010010b40000c0c41d40003400c12064080c2e42c04c00060410300c11035081c90b846000040511a080c4240e41c0105040f003c0c207030201c1c03a000e040000700d0300b846403103c000c03c0c5080c00104a039440001d426032a44403c0780414601400c098050710301031780040140b600241c0c00c220b00040c090042c0b004d40158452519200c0c5044d00f8154140410700c20401c101040481800030a00491500781e0001c041d65054180403540040314202502e1103d8584c0180048030030004001103071803c181c0007001481e0081e51071910f5240380c0f40400149841c00e0740c015000305544c1440c80004005100000c2d04001214205c1d1001c0e0ba401000c200c508a003540403030a800c110090008040000380641304a40400303d03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 121319271 1250 121318021 121318027
    0x2a0c03070911030103120201090609060203010510090302031209030106030c030615140a090b0f0409031808150a1e06120b1612020306010507062406020303090d0507030309080d0f050903 81
    0x2c00e030245020511000c0e18140b050700a0144c0316000b944800035130b5410440a01140d1198100000654800e106003400b40c0e9841c152492900e100e0324600055950040182545600038940407074940c00c16010303540e265590b000004009204254040003c500c03e040214807004522145194200e55522440c004d00c03000d86410005c0d680c02401100b50740c8030001c0080d0350030b6414040340d0040c40c2240401e401510b01013420040c940c00000002404100d00200340f48162034642198444030102805625050b0100106120072007a410120700c4012900d02c141816400c9641c1000351021035002d02c400007000d00c1d500050000400800b40c2c000312810380200c20002c00f050041a00304040040180140e020010400302d0b8840c0c1e044803041c5402c42e0b002e00c0084040041c60710700d82e400d000b0403541c294088100280507400070003900d00c1845140050400c4009140c03040c2c4084d0f001d441d01300c041680d28401d1400203029a07000e8240101000e60000c3c08250444c4010102c3d80054080301441d4014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 121320521 1250 121319271 121319291
    0x40f1b060215270703060501050f0f10110a0308091e1507050409060801020316090303140702060409020a0203031504060f061101060305030304030c0b01050415030201052a0c030709 79
    0x10700000107500c03a040c02c054550351140811100d6150548811109202c00c11401c286000020900d0650740501007c0000341d989408014043c172160a4841d00500b00792041e0350189801c001c0001008041c0c01c2c040300c012045a43d0604062002400b140401d846105204075040b080000d803001340c0744295a140158100c0f03401ca50f88002c01c0981218850000c000582c4c454400e0f0181d03801403001d11810b00c110b5448894480c042d41017100d00d14034101c00d41c8492a9400d1141100c0000c5a8041d01c4000d20000524003011039680803090590300000d041000127480515031000b4042044154051500c6c0d0908071a4501c206a409001c94841c90600000380a00c00402d0f00d000126406410100122070743e031000702d4090080756001628138000803042006040e048020602d01e54400e8003840354607032302d44003080112a0b210004070300b440c500707020038001940a04000e2000005180c0b4140a03c1d0084120201c01401d1024000c61600035400c030348020b080c10400d1101401107032105200c41504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 121321771 1250 121320521 121320523
    0x2060301140310060603060e060609090f13080d06080d03060305030306100c1403041a0c0703030f0e0a030c090c050f0a0c0215031e0105010806030c01081b03040f1b0602 74
    0x4103001e086003507500d08a02840c1a60100112101900c06480c18041a0303580c10000d0003c1501384a20f660b0140480c001032070b503141007411120b6101c001441998079480c0d00800d612440c0c001484a1085c1103d60012000b007030a0601400180c0b5543d2404903010342403100c05801c1100e80c02840c0245414203500f800012804002d50b54040300545210b152221000c0040710104410740c0c0242490302000030303412840e48084001d0099450320f1124504200540f41004a10300c030764060303c2a076404c0100c0038400284524000071100e41c1510b03000780010b541c04005003502841d940111f695041e01402002011413a0060840c01411b0342006400c000c00c0440c040320300d108005d5004200039040c45e1902c21503440b4043c81e0401a520280d00d600e078074003810b400b41140080d1000c60340c2200034100000d91907100d080064440c2c00060044c1c00c40303120001c019982903101404111540501010400e01c00002c03034007070740c030540c000c0070b00c1810311065080880b4503007024204884480c050340018003011390 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 121323021 1250 121321771 121321777
    0x2010506090106180b031801050c0a020d050304080c0f0607020115050a0b131701050403030b090601020c040908040b0705010504120c02060307080c040e010b07050c03010b1804050106090509031e070206 88
    0x4030070305180d8081020403413050030324416500245181d80c1e000c8240210048892102039050306084000c11454540e9000c030780550146416040040c0d00859400b0620b602c40c101031a0058414100d040c00d00c0b0301d00900c981400d6001780824000c0d40100d04001c00d03190709002c0d03806040a40700c80401f1140c240710100d40000024010702e03110300c4000a011000d034509240b0000280300090003008124031002c6d000340a044c0c10344040d40080e040c00400c080500d400b822003405081d050f0018003c4215900a100c00341503000c00c291407481c000c1c8000038940d440c180042c024140702ea40000b0303035450b040c40c04920b49407403e2183c20402402c40b5010005844490440b500404641024012540c9210520f4158815a040702115550010000850342c4681000d048010b1154080d00c00d030186041c01d140c00c80e084809a680d000070348a1101c030071a0041c070102c030b40040c05080041142c9840310f400c40203480040d41c2c8159181d20006454005440c90541ca034520200300711064034210303213900003540d940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 121324271 1250 121323021 121323029
    0x6041203031a03010c020703050d02030a09060807020114070207030c080a0b0105010c052404151401090e070503010908031b0403200d12050c010e0a080403060b01050412120e01020105060901 83
    0x181c2d1442c08200c1c01c00006900c40b1400d000a00030f011520140750025101d13041071008a9080c1704100d01c1d5015a80013200740d52210400b5030b15400070380d1528208580100d00940440155581d039110411030900790104644181c40a4005203140c83c038625113440480743c0740d03100400c079410241140c0c0001e0900c080049c111913003464103030b80e050503d05025040c8000d54480d40d00c00101c03040c3c00c07404202012587d61245000b000300440b00200e0400301d00654142010900310185e0b403030018401100302d43e200c113036024040350803603445685600110b0b00710394a20320162740317602c008405c00c90308101809100e04410418079040703041501c0d540e40c42800080200b04100b082c0b071800304140341511100c80071003501e9048211000250380c44480645103500c504074001a0b0350901c1b46180081200081d0b0740012540081d21600e45891a01c0d90401040c0d41c8520310304115041100241101c802c03508501c4860184d884100c9540701600003130031900520075103505590610040000316541d03e41b0480c112 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 121325521 1250 121324271 121324277
    0x320609090c0f07051b01110d1101020c01050108071403070b030a0f02280e0307050310050705130b0c06010608130605040503091c050106120506190603080703050c06010506041203 78
    0xa84540301c954200d0302a0391801c030302e000004151403003884000614140400c011a0304842d000210100440b044003914100e103c0790b0b4480c4030300c07032a03042c45140010050340f400f07070005003003218204459003036603c282d00200700741d0300009040c40b107918901c669501c2004220018000c9525000046206000c0107005075080750340c0790a50402a08682c0444500b1207254543c00122144c848030502c078060f1130080310f80003412440c5408028100001c0705802d80382e00800502a82080c041c0c8100a410020094020054180000106200300b451020058a48003403566160305055000600d4140142e014400b00018841448051541c184501408035082000070520b0b81c2c440c00c0031461845191200c40c2c2000001e00c20300282d00c50340305c0c02c140c02c0e0304c100b0003803041f07650b100e52000310040c8082c00070300141c000c207000c0780700500c04c0020510008040c00c000700b40075a40f522408401c2d0403450083e40440c1c000104101c1c8107505019660243c5400c4603414101400c0010840c09031850035402014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 121326771 1250 121325521 121325539
    0x30f04260f0714030312040516080c032113060c05010f0b060319090804140301140408030f0403030b06040e0a0c0c0302030405150d050406090213020a0816050d0501320609 75
    0x3c0e40e101071080310745801c940950792020303080c58600103a55400c00c241d50280304206150201d02445d01003915240032000500a0882459000e000d410b9400b03095200c22181c0750401400041c00c5268420b68010045500c45e29032148860030958256007410400b80015443c00c1e4a500580d99100180c030340001c40340d1a200600864080000c0051581d64009000c210000c5000610000038550711028141e042e002484040703580304d002050300c0f809583c01000c0c9603050000039030280500c0c590310340c040e00901d80414041c2000010400300c2d445a0003900c6076100c10f0b010085489414040c90200c6541464002c2c41c2c1015520b00039220f02079801414424800781800c0b10004907c20195440c00813a904104011308044c500038000b80f8900e8012400340c41c0c2c00e201e0b42c042c100b25109903206d442071a101c0d000c0a595a0694500810700740c4030f1031041c031500303120071140e042c031500c070301400303061500c0324540c84040040c10740300e0546d0901a482648160118803a003030303480321811b484007440c080d5400c4d03503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 121328021 1250 121326771 121326809
    0x40b0601030906050a0507030c0c0804050f03030d0c0810080607020a140c12070501180605040b090406030f050708120406020a110307080a03080f0f040b040f05030f04260f07 76
    0x4042c0c00681000390071541050144001d070301031035003e00d0089401e03490801c06441c001805640c2110180c2001c0c28070342090200b0499801c10100c01300d29110024150780c43c004143d4620422500201c10321030010b0050302c100110700c8103000c801d401914008006042900c1c0c80f0701c0c020742c0c0d00700c0010010100000d40110115051003001b0000c59014020041e84001c81200f0300255145124030031680014030143c2016441044054001c00b43c619a5450910309805c1c00c508200d15030100e00260341107691140000081074040c0d115011030751090014001413481e04020a26141c00320701500c1c0f0580041004014258000400c0c4003020350248440054015140003c0d0404400c0c3d401801e82e070080c6c8801c43d04169105000510454605150402d84e840d01c02515409000854000b401d000f0031501080214020400c2e5103601e6100382d003220300e4002091000040c07038010364008184440d1848005811150b071841841480d07070824005d0041d01400700301144d8942c614441d2100340000040100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 121329271 1250 121328021 121328027
    0x5040b160e0a030f06050705190507030903020a031a010509090a0f02030708030a05040305010e07050f0418140705010e0427050a020a06050408010e070501050d0b010e1002010b1f08040b0601 83
    0x300c1c4100101030303104083c0d0340d080000c50f22040150446240780f40400041c21a07001c6e20a403011245010700b51600c8500120b0282e46650081c4400c0d0144920721a0000041e40d91128640245208101e22403c4080d200703141e03120300300706802682c801c40f91030041005581d000a1484200c0c0e402c10701b80000202d20380082401d00c90f66400651407400300107408100507403c5002803040360f1040e00200141001003209070b80318003250045542c40318040c03101410516003900031a1440ea02d50f40361124140e02c650b1200d0703509004419500709600300000800c400d6800148100340c003e0103941c10b200410202e40400c01510000390094050b80614040b0301c1031142c200000380f201365010b00b142c5040c4e51140d50280c0180c000d4410b8004542c2025070188510348007181d400212034068480b941040c1d510040b401c0a0100e0002a038100f140300382200b4525650051000d8100c0700c0740e0000520410f81c003050000701801e0300304800c006034000a950440c0c66105004607409500130f039045895840304070040f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 121330521 1250 121329271 121329287
    0xe0a1e06020412051c020d0519030216031e0201050c07060e0703050307060209041b1218170a0f05040e040305090d02090403032c060a0b0d02030607020a0201090905040b16 75
    0x500b00c03c0e5000d40f81c400f000301c001803110140b1103c062001e60240400c4007265201e2001c61103200083d0300b03014091548132a8040704481c0d800381c0c20050700384250744c0c1440c11440d0318003400342c00082480503080b503a183c1030b6003c0848984244001d100e1454040c800007014845e4281c018002a80c0700f4207621110340500c020f102441d80582500da4604086c10884069006000360b20310a620b4003142d010744085d40a4100e5410049441e03040310700c58803201c600010813500c05402035001c80b82003644001190200d00400d00c83d01e5200060b26040301290003411001201c1e214428800100000e01100d00450344a9501c40d515250984ea6400ca080c042105444c0750300c0c0080d0095040403c0c001010b425800c100c44202071203084298042c0003204054103c01c41c02e1103000f41b40c200c0400315015011a403c01c441c00040904070215000c00c9502080c6480c1045503104010f0704904449402c5690040840c8001c2c4202c1c24203101c1c038100345d1141806140094031840200e180e02c0b20b985985801280c036 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 121331771 1250 121330521 121330529
    0x9150402120403030905070b09010e01300204031101030203010305030409020a0311040320010e0d0b0c07140313050604060e0402070201030603080d06030201080c0c0a03050307050c010f06030203010e0a1e060204 92
    0x1554002d003000e2a0140140c50000d00455680c0a0b6600126001c0001c0c426241600c10503035407192051541401950090000303d10142d2100c0481900201039400300d0940300c0040310b440b00142c0e541d1550400d4041c0c011406102c0741014010401000429000019101902c050303450040c3e07150b00c914420b500800e40008141c56804004c00c1c008240088408114070081d070800c01c11a07070012003401100c003220280e0900d503000c0052140c2d00c0205d042c14500326032100140d00201c0c070300a06a11030400d1407844020021141e4400560754810487d2110007030000c10341980c026007082d040c0900680101c59114515004a5000c21524150383c42074001d80000c1d60031116407070b5141d801100c03e50161250740000d0b404600488041041c0440e06000c5030360200c030031005400c11400c1c541d8200e89540c409040700003005828031040c20240009c0c800c03100034122a400000b07100340303181306050950b0a0700c60700340c1d05600b03c40341b10004940c00b802d14220815010b5800c3c039145403a458440d00a00540d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 121333021 1250 121331771 121331797
    0x10e1f0810020405030c030a080d0207030c0b0903070309060f08070e0f130f18080f0702011206081b1f03050702030705012310140d02040e1c031a09150402 68
    0x12001c00107403158001c00680b94150f0a507070845504106140d0b03141e6010400424422080103c109980c8007036024102c0760f8840d207003680e040c80b0717651104444c240301954806543d1f000015410100350b004001c10703000b4140380c00c046000f00c80001c00500440c030010100c0007802074402c0e03010540d03602d00c0072490802070002c045c20302940840203080d0040080010b0481444d141c403801c0c40b40c4240010919244582c0228074034644258070898881617004010101d043c08540c27014030785140700e1030150f8409801084001c1c00c400c441a01c00d8100300180805080c02002d030800c1500c80d9042030300860f010800582000715050f211a2812403442c070649601034255440c0650764000500000d0306080748a001c14a1100c894031640e641e01d400401c04c0c489c4900f44400701c05078505e10f083c0049280a498001000024000c41040704a420700f50f10380411011030b210130528035092a0180300380315040364490340001000c000c3c403000c181f4400e0090301200685900c0b5495a5003135480380c04071110724a00b00d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 121334271 1250 121333021 121333033
    0x10c020904051c020703080d0f02270301050a090b151903051c03060501050307140d0207080c0d030203060d080306150c030c0f0a02010504031e05060c090f0306010e1f08 74
    0x2041581c3c548201d0001c10b0b4900040290700c1540754400103c0700700780d0b500821032030314200403003550400900312843d504a401d5000d1110007900300030071582603070704009002c0b00c50359201d120042500311003000300640015803038201c0e480d01050003603202d0750744169075402010496054800061400203003640300c525a2040e05808000c03c80d0206807403001c04a5801d8040280272004030580954589000c0c880c002241400013540b8544a0803411004041d44100e603445c0c01171140401c41a680880c60964035034000081052b003c61003003010268852a92034118154200a000200780c00c0517401c000e403a40c0e84c0440410500d6072001042030500c00e507421190fa6501a02c1e030750039240d401104400d6158003a80058102c1030b03201282e0f0360310182c1d05035951860a0308641e00c5d011151240a40b101d0104a42da11800000b40d041281d940180081160306403206803a50410529240c1c207100700c0d010f5001400100028580440c01a4100720010038440355000140a07503000d4401c0740d40300c4070151141c0c4c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 121335521 1250 121334271 121334273
    0x603070e09181b150a0318030801060e010305060f061804060e0105091f1a09130203010f0f050916050d050408030402120d0c02040c02010b0a09061401020a0b070e010c020904 76
    0x220250300342c505010040c3c50002041c50302c0e1843e440b4002d030016810a032041d40014912550100034101c0341200c2c140000c10302141d034981c5005d94001e480407008140784c3c0005026841d000700b07041d508104c0900c0c0901491400d9400300d0170034007a018040380104000b0481050804003070034400b0080b0009001007109654581040704049000c3c8502402207150300080b0b840894804402c04203c1c561441e0350038030078648049809000f500484d1800844c0b0240140c90f41942c0d8208030700e041c00c4c05e040001d81c503541813101c1083c800180e6844000c070080743d420300b0402500c802e8100b070f502c000001d4034854040c0030550151414890050b21499091400f03007004200402c0a021350f024500954015000803a001c20055407081c05000c1240443d003040170038001464030780c101c40e500ba80c0c03520001c01c0c0700f8801004104150a9500f080090640f600300034000888000c490500c0d56000744000c0c500404291540e00103607001030001c1c42044421440400c00c1d074020400c0f51801e17a8041c1c5151540d26007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 121336771 1250 121335521 121335541
    0x509090c060f030f01170a0b10090218030706090602120304060209030f0f01050609060d110105040b0d050a0f090209010909020d020901080102030a05090705030d0c0c0803070c090c0513050603070e09 87
    0x801c1320355a00030010030001184002c0d160050b51010b404031001801895143d80318035050480080c5007100300002036101040001c0e86002504c00001420148100358a0000406003031404c10b40001d0200410030100300502d44c1e00107501180e004010f020144c2d251158100400070744544e03038043ea01880b400c660240b504400292003800705034100c008002584600d0100310316000d098071642e600c80150002c540c0840c1e0300007040701380410141090303403500d6940e0481c55481e401003000c5040003036460042103c100e07581d0080340f402d9070084c2402c01c503000c1c01d5400282680010300591456640d074240e5041103484642d0004030b25074004103017000944c0e60318809400f0394000c0700c12030005814200130444031031000070000d042c2e500c000c01030a144820310000301e408050104040e02c0d081c04080001605a800b4002480414000d01c0c9540145003044c0d507403800d6403000b02903070080000400c000929200da03111803209a40301155004c0c1e40b519009021210b03607041d0160945d10002010070300c254449 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 121338021 1250 121336771 121336777
    0x1d03010b1801180207111011060a0b0310050f010611010204050603010e010519050306010603020c01060e010305030909090c0d03110c040c1e0306030f080705070e16080a0509070509090c060f 83
    0xb020016030043d00005800081a030003190b800501041c4a4034801d049454042c2c1c488900003900d16000d2035841d0b9000009103006016202d044070250340d0301041f01c3c0380c10103000300498400c0003c410300050134190f081d048520014481c41081212a8640703144c000c00a4040b00c0c020580144841e88a58440d55040c00b030480a1041d280302d005c0d100d04003607207540c441d10b101040303401c020f018050681c40c00d04143c01139841990041e419540e54840810310125010134940a54000c030011078039030308020180003090401500209165000010341d58841c0c0e00c0c10740954440e40d051070210300c0c0b850440d90f8136146c0400ea200c0250701c0703401d008805006a60203000300d01000c003100107c20135000782640030f030304480ca10300001e86513264004a4402040d003001c02003908502c550110b8108a5403001c0f45000254191080300780003c01d4048800025030000c94140c000740712010400003401c0507100669a20410710800d4000d040b000000350040c0d4061082072250500503007555030f01c10b0000c00c1030409074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 121339271 1250 121338021 121338029
    0x10e03030a0f1a090c0705030c01060503060619060c0812070e0a17060a020906070218062b1704080106091508240c0f07032d1d03010b1801 61
    0x2d1401c0c4084540003003500501c901010715802c0094a51030100a01c02c0204004001c0000c07504100461400510100000e0101d101c4200000a41d80d0520080504000300945003c0c40703080c0040da1843d00241c60810807049844501380b01c1e40b15645031600700058040c0503c01566090544100b000315a00305200900140c000c655200f8050b85403414200c091800100301000c0e50720800c0000c1071603899078000c0001c00c50061246003084c41030f40c00206c103c9000d0b039504040c3c2d02610103000391414050000b103800e15100d420000007c80c2e000a244075050005006060740c4012a05d991184d00f418041780c2c080c203c40d100a201d0280c4800102025004602009034030101c00c81d00042c0c120301c042640c28a541341d1110502040d50074184560a00001810b503c5400c079081182110a101223001031403858801e4503070007124040344c00e0000c000b45410f0391035483c213401c15104003070312075000c0d83d030294072400f4200d400b40f0409048042401046001c1c51540c110300d1000c00d100c84c0200c8017940504803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 121340521 1250 121339271 121339291
    0xe0604090e1c02190501090c0605180f0d02090a151203110106080d0c03050906160b0601020c01081807080a0b041b060504060509271611030405010c0f05010e0303 71
    0x3407140b540c0a60300b10518111240c0041c0c2104a041c5907041841c1480b29225008030004074601d001a2144202c0790159480500442c40005950200e81c0100e0b084640c401811903036195410079400c007140d00319001ca04001d2080c1842030002d8020720460344080780b006000021411403e8448402c10303d40386803403105070702180721110b14503240201409554155500c1001405c1c84a045000942c1c0740c4511402c00c50a104060101c1451f58035240b0290541c02242a4000550910341c00c00c88905503001c1c04081c110741255006c1031031a60001d88090b000710066a0707548241413450100c6042c0b041c642c102c0401405115a20b01c284a40701da01503001d50300882c200300311f03420003480510241c410340c46038801103102440108070042c05032002e80404d000242054849507413203646140c1200d148003403400c42c41c01e0138040c0421102406292044c01c4660708059240c044040956035403130103940711b55810801281c00e00307020020081d50403104254040001d11a101100d030710a40c5a0f0400c560a0f610 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 121341771 1250 121340521 121340533
    0x60702010f0b1005030606071403070201090e07020a0206090613090c020127020123030403090f06030605150a02150702060f150d030e03010b031e0c0916050306010e0604090e 76
    0x1d10480d91007038100d003040062116585500b010300583c3d094200800381a4050014070603080482c10414954802e00c8190002d0f6a031404544000341082e40640c110800c0615a02c081201c050740008900704804d4044030075030744401c0700320300041c091b00c540741240c1c1d803c0c10070310800101141190007200350f59805170001e1040d0305818203850940c1d1007440e5039009040c040c2e140700c8055401540c0c0ca0030f0240380310b03081c0082c0180100d036900d41540240c0e000c07000102c00e000104980004108000060070140c901486034a14007400900e0184280105291001d0001202c500c902d0003000070800500e20a940e0700450302c0c00300310103074440c0012203080300c10107400800105480c0350f068280c82e080d03c0c010010204000b054504071381c0920400c007615015941c6103640f402caa5010842103481a00403034440d01408111228141000610703840c180c0140300b041d0134400241d169a80e1140d846660349016902e80d0b840100403910074ae03040c0d000680100c000100403600300400e0300246e40c84e12000c0c0841d20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 121343021 1250 121341771 121341791
    0x5010e0f0405060708090a0f030c02040509061b09030a05190507050a180209121f0e0c03070b0a09090203100303020d0807090611070e01090b0108011401020718020c070806070201 78
    0x280c1010112001030581c2c1040340003801c401c4c0281280c41d0403480403800c5860743c0c2c6855079603c000707141c080d0098011030106203100c011843c00e07018280d84684030101400683c109002503468524141041070702109000c100102c190b101009095000742d040801c0342ca007040c94554100d040281020140c620307000d00440880c0c01d0829408c0303070080343d064042d00070201020500342c100070741140ca8482ea019010a4080d40a484204907146000c0045110540c1f0040380c11010710807213104646011003500708a540c4600c42d540400c40c1c100322206070b00050b6403078065034800c0710788007466004403039002d2001c400d00c940000e2810f000d1050301d01c01d800302e800b00c040340801a1143c000c1286c031503000541a103c140605441189540400030655048a032000d40358a40d07000558000d070443c50a0560b9000c40780115a401940e8030b0060a40c42048001e0380441c8000039141c0e02507000c3c4400c1210703000c1c11002c0d9041a80d04445040c00c4840a90f003601d81c0381c5d919941ca8480669100c40150300f1302100351 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 121344271 1250 121343021 121343041
    0x11061513090809010302030a0e010f0b01030c031808030912070f030806010507020904021c02060c0c0103150b030c16050a0b0103151a210303040b04171206040f020c0102040905010e 79
    0xa01140d80141d01c2c941000e00c040c00450103980005c2c040c00d0f1301615032a1080e0f240b40c0900070402000600c079000700d40d50072400c0c0014100c8a04012060406081c440c03a43d04904d504600311003440d4020184c02e94030780e180b95140d45003000d189000500b0310b40004500d02481031090707031110b03454030940d5819032903107e000c011200c0d40154880030f07600201410201e0018030780f4100c203c0425400e1340755100844c080d900000c2032600324034030244035078000720411b00142d0382c0b5203c0c0f02e00f990306100f404450320741011001602c6000080c241c1c031000b1300c00180c1d06c464150701c80225415580c882c048a910f2945880c00e480d00382030a110031030b22886440090041d1003454001e003102034018052035050040e08104000d001c0210303d000050010010a881c1c2081d04180004c0d0b2240740500591541403c041c0380c02665803904600c06a5a45800c0c42200e800c02031507402d031500400c0c00c56001c0345443c1b10b502c011009100ea02c01d040d0180d0300c001800600b0241c01c1e00a80d04907001140d1001e05661040080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 121345521 1250 121344271 121344281
    0x8061305060114010e0409050f0307060b0a0902070f140a081c0f061404021809010b0a110c21101505040b04090209040209070302130e090c030a05061611061513 70
    0x15408031740c0300c96106545017030660000071058014070464030161603800d0311034150ba02018007502c100b0b07119002c60138141044e882c440000c1540800c01c500d488640e442c0c3d0640100c0c00c14005001120600410620281c1003144d14051a003050302c0c20b07640d211039880412548550070411615504200021498000500c0b40c0011140d054500b40d850306c5100e02004000c0d480960399400e100381c402c0226161345c0780c01e08024040d11102c041070b070f0340e00c1c1c3e580c10246c07907403018142c036070010742c0490300d50304d030035256501c221481c102c000902008050072580c6075800e1401c00307606000400d291200003072180c10400d04000844405171410407500d408001840300b40c800906c000f030341101a200104005090032124242e01c58020300d40181440d0103040e085000c04030350781c4202c9003415010280006d984003171081d1201c4160803401400b5068881c1d45080d2191402000c03500c0307040356000048043c50044901600558103035050312034a181c90b00c0744002e6043c0c1c1c801d06a000d40506010320810540500c10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 121346771 1250 121345521 121345559
    0x703050a060503030f070c081015090603030507060b04020d050a021b0a0f110a090e0304030308010e0906041106160b01030507060c0804090902010921061a010c1506080613050601 78
    0x180d440c1ca45c02800ca402241d120356411a000030615400085c060010302c8140781c01c040451000c00d04c40c499410281440d042608080340541c9019010030009030081c007200d030b03201d41c041004119440d00c140094000d00505103488201030809081283e610300b00d41c018090004003400e40300c0200b105005d40c0f6a11120783c20000d0400032240d40000100c1e42c10205540380344001440030a03185e0f01d032b0511005650501d11344208a07440801c0503c01c050f0440410b43c050096807943d801c1c03502d84100c02e207039141e0001e0409050010303018222041c07912600100c075100c1c40e00009440d500e11041c0740003c4041e8007481709540728000c069000c594248242c1104000540090174a030030141010803050081045000c101c1c1446100c072000a510000724480c545e40c0503141204050042c4070342008029500f82c2070b84441c2c3e0202c840d411285680e0040e0100c407500d6008001044890340854a180040c03000707800460091082a040040005003400744030b0f00039202e402520160390b070304d0900301800039904007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 121348021 1250 121346771 121346773
    0x90f03070209100f08030d061202100815040e03032e03030e03070315020d05061210020f070501050c0406020c0405010f0510120c050a09050a12081c02040b030703050a060503 76
    0x8280400351a02d420b00541000c000401001c2c031a84c0d0b216a07507070002043c0e0002100d500003107041c03e4100c03030780e10400d07004011084c14002c207003400c1c0c0e0026500c83c0007040c0340c0044c0072031007000c204d00410030700c211420104054001c00c40d030300250806079525081103901103155010550782c4090802000b182c10b082c00c0040010f880c10504554064900f40302e0b100324160103101e1b039500080400c050000220200902c42801070361024074000490945000615140c00f4500010320a200140c0008116001d000303e104010388452102c1d107a43c0c070030b100c3c11101400315030070402400103054032900100b0484902ea02103d510860840038001525000d2092907030408450700100038030b0801902d01d0800102e9840c0c021840d0b026007000000300c4084544203000201c01007104510a600440404003400c011542c48034001d140002c40740c91075440d540010800100030440303040041c1011200302035160500c0d0b0964407281c68040c0b01d01103401c102e440800081c02c11001c40d80d4070030f842c4902010744201038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 121349271 1250 121348021 121348027
    0x80102040609050d080d1b08070206070f031802060f030f0a1e0504031806110c0301050114010c0201090f0905070e120a08090310090c0f0602070803071502040305030a0e09090f03 78
    0x4810054405110181503401e07042c1040911306c40d9007144141c00c002010301d1003801084801c46002005d07020b000f001042590320031800d0140c015048a002411040546408508140280b184182c10782c9411802508a80046607641c80002e040c0061407181c00c0322180c00700281e079050444001d849154000c9100b107511030782e000703a8101194002640c054041e041880448400c400055500b0340c09911240c0041c01c1105150b044010900c0183c20115086009000369414262480500c00312411030320706200c004003102045900500c05440103042e0b1181802c3c0740c2d0303690024034001e0f09003201d89500107807841940000500c3e220304603019040e4248002c0480800382d540f003004074ad00403d080c661500c0b81001e20b0101c40c499000301109584140e03981c5030010301e8044a02440100c40d00000f003950000d00090191f160000103469a03a500074641c3c0d41d0082c00d00310300600900c00c44d040034080b800000f0b400081c02ea0000d16035801e220f005d0310341103140e6a036204500d44542c1c00e440c02400c1341e0420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 121350521 1250 121349271 121349279
    0x903040819200f22050603010c090909140f01050a060b04030327180e010506040209180a021b2a06040e1e070c03020f0604030f03020c0f011109040501080102040609 72
    0x1900340142c40141505030082c1c0e0100018508802e14000030a80c1e01d0752110380b5840754041c0c003683c0e0300101e06030001c0c0400d41d40c0680c01360400d003090007480e1801b035031a000b1005100000c0c1c0c031490003540ca00f00352060420545003450203031030210b81d840c64007414030400144110301c4104980880380c056580840040000c031240034a00914111541d40000a2001140325001121042040c21040400107400034a40d02140c2c01e6031001001c40d0b106600c1880b8100b141d0311003685603240501c41c0c240181080d901c0d0100e02c4024080c214140e5580920704c070002c00c20b5140051502200c44050403c0141c1120401540e1203221144080070b403c144184810403141d401c40e40d005410081030702a2051641c03414036854141003003182d44000041d8002015800d040c0c043c850b00880221070000341c4081d04d4562000b421646454403000201640003808400000003801003041d0b402c00d400080c008100b07050030030310086e085008518440d130f14050001540080520803a03013103541c1a2100381e601490 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 121351771 1250 121350521 121350563
    0x5010c02070e07030c0306032001090e0c091309060504030c0b181b0d1a07110d05090f0102010b0409080a021501050f040b01120908030a0f0e1218090903040819 70
    0xf4003175560506072a0702e000705c001215005160480020b18a9030f05282c00c4580004298403890342c0142c010007070410a000301880b074182164042c800c143d40c9068030161106440c0010040940701802a03443c0c58240020140d2241c03440b46028003807040104591510341151a108a5200c81c00d801c0d50310542c030400d485080c01c5078110600000803d003101c2d030415911024080120302031681c0300c41102600b000714241d0000c09a001c0e504040c0c0081c41500c0807020090818822400c12030310030b1812485070340c02c5038405d4004090742d21019005024400c410300d442981d541004010300094011503414821031011a0f804034125a002031296004182c148203000c01002c0d0006a241003122546941d070b52429075005188515201d06901e0b552450103d041008485845c203101525a0401c1c80150301c889002412062500e01c03004110f81e9820201003201504c0b0b00050303515000800d04007000f2181d0000b001610460340824250f8030b0030f0383d041048103514100c0d040c1c000c01c1011824210711034080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 121353021 1250 121351771 121351781
    0x7080103060c09080604111002030f070206030a020903010f0b030607020f0a1415070503011a040e1f0f0e040b0108070810230109241202120c0409030c05010c02070e0703 74
    0x7042d8141001c01c29143c000d001c0c1800740444003510b203080d6024024005042280c1c2041c151f032410b101540c01c10080c04265070580c800d8041c00b034480c1c1d901101107100b501e060b034101c50301508000c008200400080101c0d002502402c22900d201340074010000e0045400410317280680e041640c003500c14205543e50799141203d13002540501c900c0b07400c82e20310506d40400340190050b4410f0719095129032403c2007102018074601d481000201c1c051004100c10b050703a0213402d401c100c03440c400502d02d403900408410400c080768004070903402d20580c0003421480c0c1d0340000d802640205031101d841d1780c03a0f1002076030380d40942c0318000c00b43d8800b41c0c03048455084c5038401d64003410110800c0b6001c01c00701651131070160081c0c20500040303544182c2c0c000c08210400b02e00c041c007000c0c50008480f940c98680c406060414501010f402000c0c1d074405610028810b02c003c20503244001d000700103110060400501048126030304a07031075840c21203000300460001604500b190f0102c1c00b002066034903008100d000e02 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 121354271 1250 121353021 121353041
    0x9100501050d02160b1f0312120f020d090204110406090b0c0a0210050309011415010e0604080a0b1609080a020d11030f0f2503120c0f1b0902030708010306 68
    0x10340c0c244a41d039908061014100001307802581159103505086c000c041040c440f007088803a030400c450303070700f000080c0020440d6442ca13500350030600c09600c402a1440e0190064000c020310710341c40061085070cc0a542c0d03020203049070080d0350030021008030380300325580c80c4074502843e004110742e0042000100c40c21001000425840340036039401c0142c036404039411135103000018004c650044100309460304240f18200b0503500a1450220b01c2c2821010000c540064038107043c10418190300508068490310111001401d4403401c4a90301046801c20b094215010386a1506049000b86290304492007140c080f026140510f018001400b019030800400700651181114100c000b01040b40d038a58083c880d000000808901030700460040d118224104844560003203103900d400000c0a13005c0804000c1d4100383c9034850300000401c040c052080d181e015070810b008144203854035030802088941c0700d0aa490012000c3c0d101d02c50380e1a40303801002c1e03000032580c000c002542c1000404c0841d45940000c0401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 121355521 1250 121354271 121354297
    0xb03012106050c0703080a140c0c0312010803040807060c08030a1802030a110a170a020d0302030c0307080901030c03060e34020f0606031204090b0402090406090506030c0910050105 79
    0x3000306690780d981518000c0b1900c100b85080032a4000500d0380040f8803031b90000300f042040050312802c442807004240040e00700c80031114085035071610a90100100d4110a5030080c2c41c04040d0303501d1007415625800b41c028840c1d01e0003074510000300b143c01660381c416460341c4031240c5811036841d148003600806400c00611a6980c16021070700c0540c505010400e0309900442c0041da103d0f6400c014402c0e4076450b80c0c03002e504c100c083c1c00890a10720010030480360b040d42c102c5001d01d0020f11400d080b441c5010710951030740f00340070003d400d80070855120001e1030051001c0c0c0b03043c850030b09a03080560072161688101415070344624001070b400d5207042c40505038402081050f81d0310310319000b40c840990041c04610307030150b400168a2039028400b000441d90048003200200700ea00800e140303210140c000d9209102c0c02300c0c0c0300c001c13621300703a0384039015a01e8814001e0300820081d603850f1480405400c0070b9030032a01034000e07109034060f5824000d10071031007511450444032006e45010b0046580c0d6000100200b24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 121356771 1250 121355521 121355579
    0x140d03200f040b0d090b16020a03030203040204021306050c070b0f1b0709050a0603060b0d1a09010908030f0106030b1504050105090112090f1a090a0f03050c060703020d0b03070b0301 80
    0x1100f00d0b8025041111100100103068201c0e890440f0070368201a0240b140005144001f182c040e0340001e6a404040d4545070150716500d8074400710b000382c000c202c117103000b09900d50404201958440301a1481040e0700080300c800d666108508603c51040f00c09108602c1300400c109101c02c18104d041c5001d0440d4141150f0259a94003007010131100144e41c000c40c8a901d0f1202042440a940641480200c04542c10004442c0596804003001501d9481a04020303561000441c2d522085d441900402d07003203218070342d492800501505000009000307080100e4a0031007540f020381007000e405054540c0368003040e86810b0600b030040d203964000a0102d4100000d000a0000101690140103040c500c25208100d0500c202d00d000c07019190f8402101002c401040304224644800194603100590448003550700e51240742801c403024842daa0141900d03100d00310500c040258180c2c0100700611005c1c4041008106010815813903040c0e902c24036000420610040c4010521143d10102a585100070500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 121358021 1250 121356771 121356779
    0xf0607180e0c070f141606050f0a08090708010c021c020606013006090603020f09040b0109090c0504020c070e09030c060a05070201020c16050a05010302040510030504140a140d03200f04 81
    0xc082000000008176030004000003001c020b030f50354150040d100c1401c125092400c8501100a5405440404001c000101c00407689140c000e000e108050900341000f0311980b070300b42901039034803a031454008a2800d11100100d00b0280701080c21401480140d541400e900850118510301e80401c45082490011541034a8001d0306e541c030400d8000d0a1040d404104c9034994010030940b5003e501034507020f4401c071010030002800b840b809906480702d401c40005c0340d40590501c0c020000740c40d0001030b0814030014172044210340c002402801c85a241744002c2c555a919080251a4014070703200c0052584844003061558480b50416940300b80d41d440018100715000b0745492510303403002c0414030215040f600a0180d030420307000050103064282801d5240c42c1c07800700800e41200387d5503914010107503078101040030882d000e20110240343c001d41c1102c41c0d8800e181445c2c03000c5684071811864610849251403c602d0183c020100300000414205001c40d4403000d010140764446004961902c0301080081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 121359271 1250 121358021 121358033
    0xd080904110d060f1806050102030304080c030d1a0301110418052208040305060f01031a060a05121b0f210c04091101030c0309020a260f0607180e0c070f 67
    0x800249500e00000c0f22451600b02d03416003003417010403201506401d0620911240c1d8000040720b82195000c16540ea5403952040c0300c40c02c0d0300a0b80f9480e040d1a041103030b28505c00130311030a0307180303040c0e0120000c00c14210748807440c1c00d4501c00c9102d83d04600e8082d0101c10180150355000d1680002d01c0d00030400d0848580707240301c0100a41c0f1800b1142c000300400c041c4180407040080603171020b8151600720b0254110340f110401c88401c502e84403550001240010116242d1140f150004c0074041c00b0320003011039014106803100510442415941c10020404101c0e213020715240d010b4403006065080200d04901c0790b01a00d0044c11840d102da0300c20303030304140784680746c5200d06400c1d02c1c024103842c82061600c070001002c0c1c0b400d058080f4201801c042c0c1d640003584e140f00c10101101d802241c1003040045007140d017412900003603e040c217503001c1c07aa0120740c1084040361291048182d0344d01c02d600008882d0b507503030b50303d14180114111008010000b900d182c80f01d4008005803800707001c0b40c0300300c0e11142c0d40700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 121360521 1250 121359271 121359281
    0xc02030a061b11060714070305090915040e01090804090b1f08040b06100f030b0a0902040906090606050310030f030509030105180709140c0304031b0f110d080904110d 73
    0x2c8469440081169419a500008004940003040007401e00380c00c0540c402000740c241d444100000038400070700902014014802c070740e552100a4071903105490300c0c00040304080c0240d0821030180f42064200d00a1050610400d410346500004950808bc00c00c81000700809011760055004013031400c066080e6980c41030000c154120759515030480746020300d0066407107240a0b02460040403582d04042e0800d030003288a400d51281c80c900081c0a64440d0300099200c1d019a0111068074400100851514120b0304240250b48054405001d443d54801d0100c07003a1004844000349190310020500008581c03640001569002c2d00e801400c00413202e002074211041600c00c0d01c0412a0b10529410000080c0111070050031044410080000c01c240e2207607440100815203003820000100150805005d03003070f040920f44000200c0202c0d0500c0349046103d01035016800d45080f2682240c640440c642141d1404e5020750210010b81014005418400036098081e101ca800920610103504c0b612054812 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 121361771 1250 121360521 121360541
    0x5031c030e07032d08030a05040221010e0c0a1d1009110915030903070f1403040e010f0b1602060a0306030503030a2016120c1725050d0c02030a06 64
    0x31501d040841041d0300f1013440800b00100410340381580c2d000414003860690b603120758500400300380b80d03407140f0010b41003090083d88840c181407400d02c090401e440551183c1603080b4100d0456408424400421060403220f1054031203501c0c0e0344601c0c01e16480781e0344410341c000b108a5a800010f42d25060f20606590348840a1380ad40d02011404030240c0ca03240b40f01a540c0c48540320642d1030741c1000c50300d0036124460001b02500c81a10302e03040900300071122f60300e031034003421103000e4a071105d407900801c810241c0c00780705d4074000041108000c02d4a8030000102c90703210a031250070f141e0301071139031b0b0a00c202038001c48204000c1c95070791000000410002d200640c4150101200095440d58103d50080b20050400041045207006e00043c42c0c078004002a1880c1c1e280c015603441340078a481c070700441c0c410802c20002084103d19440300f174034040c2448045d10403000455a0a180e82a103009042181100c03c00e02510652003520840945030080d060350004a0025007691900652504c43c101a6664008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 121363021 1250 121361771 121361783
    0x130308090102060a06060e0607080913020406080c04120b06061611150705060720100501210302071e080f06100e070e090a1d06100801020405031c030e0703 68
    0x11048501d40e4184041c81c0d001090b0503041100d0b5060100050005419045039400381e04006150010f015140081d960100402441814480007621448005c1d400070f101c1d603004107110801040a060503801920141c851030401e403001024103840303480200700080e2150b500801d08100c4010514410784600401d035006000c414502040300082c425940c901c811043c038464414021000029008107031681c00c040e180c84d180c2102003182c1c450b07404d654a181c8050003284a00052000c0319400c0d50071240c101e445880600448003080e00d40052940104000140140c220b80c405200c0f04407a00074160034a81c04200001ca610340310701c1007900d0304c07041d0342c52000380703a0100f000c01c182500140f52050207003840308228140d500341039001800341400010744030310414203800090f01803841c644c04410901d840e03502d1415812458110703152a08000e0340c1c46600700e00c29003404251410140201e80c200d82e809001490503d41d91070070081c2042418002c0410140c80d80c0c4244412030342000640040c500650b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 121364271 1250 121363021 121363027
    0x60803030f10060c050a080903190c0905070e030d080403020f030406020f1905030a051804020f07050c01020105150d0c0b0307020d030c09030b06060702120102031305060603070b0405100203130308 86
    0x2c140c0ea10103900960240302040818804a40041d5010800e1034890364401045602c0e00e2005000038100501221001c400510095202060041500110b0116036a0703440c100b000e6200c0086c2198884800c07200e40c0d41540c4021084990203200e090000d42c0700380688141d03081e0081910f0b0040c29070340710b0b03400b020040e480301a0454600401703010003d182040c3c907017240804801d55a60700e44a000d03d041c01070501c8004100300002500c460440003113010010300441d520000740d0712014080c1c00070706003500d0340e01c100c01c08500355500510643c7e015417442d03030001380749008035004c000d001c1e00484000c580b094114040025440c06400c0039500900c0290084c0540ca0601c0000a086a40454042041080104c8201301140482c002c090300040c05403032003645c4e04818008114200505200c003400b40d0b20000820010081141d80507030f19500c1042913540d107072590820182d40701030034091102d00c1d00c81040100658a03180c4640c0711203550900503a400c00d40f501c0d070070000e20b90701c0f5482074501c00000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 121365521 1250 121364271 121364281
    0x8070507080d170f0601020a0816020303041502150405030306100e03030309010506010f05030103030e04050702030909070f1206050f19090e0303060112052401030605060d02070c080a03020307020f04060803030f 92
    0x280042035800201c4e0116503100345001c1c80002d6940c003442c0405415070100264403c1e044600ba2503203441d04da00902280d40d9107a0b40c203080d0500044040d41440140100c1810403a9a0481e00140307028513001801103085440f503008104000040c20b02d00e030244000d81e900c403401ca413030501c0a544101c100400024503031500400140c000c42c03084500b042048801c02c0103000081c1c200a04401c44c40041d500007400340c2c3c482509034614070031070b80100d80c030440000410040030350000c1c0f4814040c44030341e18088004602014401500c42602515500581516840c0b10604080c10401c007913580c0d092403039442c0c0da920b14207a0100c8080d0707900000c2c00e0f0000000c00c585940c101104004034070721080108100e103405c80340c00724204c1c01c442520807000c40340b0014424030780c031a401120240c400240b030141e0b901200440c0360020341c440c400032106070140e407200041d118808104c203159103406401652a00181d9400c02c06001c000c0c80382c042d80240c1d1500d02042c1c440f130400141d0321501035604101c006041c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 121366771 1250 121365521 121365557
    0xf1c11041103071d06040504020c10060f03050304030f08040f03210e0108070e0a090c020604060608010c0f030209150304050c1e0a0b0f0d0e1006050901060c08070507080d 75
    0x7880c608182140e420003e00c20741590003481050100c0456070141094400390000503050f110b1944032640c482d001050812484501103140c441401c02d51808010791591590029081001403201a019070014031040010855510060341d03414400c0d04201d19164543e40c001f410b183e090380003500d9103034070504405a03141c1104090302400d000c0c1e0502c08803100b00400000c05480004101008000d405510700d1000d48032000c08a000e054004014452005c2a0000968903032080741c2c2945c0b4a8100180020810b40602c10b070601c560055645000100c1c105d03c00fa070203580103000c00e0340c0003480854075448040407040a035000e248210040c1032641ca20700e00f040480885680d2803c034141140d2030260039603489014210131584400622601c615803d00d00c0700903405a1500c00300c0031030424200250900c00403070302e007544911004041140c80d40319001c3c404101024091800820400ca0580d400b04075030102034085184981d04079000a03458045039414a02e00e1000c4001041103c050030244001b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 121368021 1250 121366771 121366781
    0xf040b0c0f01050601090f15020c031c090e0108030a0503070203070b0106030207150c0503160314100503121603050702061e0301170615040203071103040b120609090a020f1c1104 78
    0x2400d1825174002e44c01c00c0051f00c040c081e071707114a034a4408003190030352142d0300034400464403600090944c0c50f404134141884071000c41e031494001c0019016000450302d1850941c8403410f84030000021401c1c090788090076038040e0f10141649055104c28421900098040c2031101c0c00707003000ba50003507240d5000e450954018110307078441c024004e00f00280117003550351110039654000710440f071144200c400208180c000f0100f003100e035150403d0700001c200c0c0d0480603406d00700c12228180c1c1143c100c501000c02c1101c25000340400f0024040101c1400c50203e07200f040501401030005201ca0710f4144461001e5880301c08815458035401d901200400c130201c1e21440e0b480341e000c49903010f410f941c034050281750f205202d0811518492580800407507115807058142c01d0300d650400003165170b9141c442e40c04c1c51458101c000c064110700401400a03411703060030011f240c09001844000c080145141c0d0030130201c80e28001520b0742000380c090300090183c4555208140603401424045603a20302c40c000e0000340e40e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 121369271 1250 121368021 121368031
    0xb01030b030a030e0d1506170303150d060e060a0b0301060b090a0b0f070b0a0f0b01111515060a0e0a090203070c1101020312040b1e01050d03050f040b0c0f0105 70
    0x140c506008035020741c40202d04856826031619085001030310f40c00009004071224035001d444524062452000003010307070f0165042c0c54443c1a006062580b0f450313450f80e01d1104443c42480c19207124803106283c2050f80c28203a07250710800010640b02291080586441d0080300e01a40d40c1e43c40b260000325508080c80382d48040c0041700040341c50300d62580d021031510401031040f01000c14001848164880614041da55040d510000c0400c01c2e09003000d501d03025000b110324403900c56240c040880074960180c402e8090380441317800a40101c03025070300d2281061500030040003581404030300c1d01c0f48030f60b0707850b0051601c6602612012400c2c4502028000c0850460700403000d001d00c10010b029076941c11480210f0582d81c4489501803417600b801c0101c1c00c50080304c500342c02d0800070b5028402004041c4c0300d0203118266507070200341400a080040001418288900c40d0084500814000840e11420050681da000c100f90180381c195294841c0219521428161100343c00c54a60756025010a02990b5004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 121370521 1250 121369271 121369277
    0x21614030a020718110705070f050d12030c030f110d060801060e1f1a090f0109060e060d20070b0a06031a1e09010204150311030106080402062b0b01 65
    0x1200c03822001943c0e610042c05881d6009440b510500c443d84025000b1445984500009540341e8046142180d51030b8102d000c0c0b0681c0172205800401e00b424200c8401c8031081d0402c01102a0710501141540140107014a107004c264403003191940310600c60180c41d4518440030005a540c408403028001190825001403003564106981003001d0310304d000c4010382114114071360b509540c907071009040c0f400045500c0684080103202c1107411042210001c4c105854060341c110355503d92540044a404400f0700038030010071111300720701100b0b04141018081d80c1c00d03400c1000426522200e2040c0c4c0c4062844c8040c4844440068624100f10030350750682e8001d249000300380134050955a841400c000e2503c05042c00140d030000041d00b00c40e003070042c3d070760201020411400604111030b41a020354058011681200000f409081400344039215000c1004201c240d818256424560304652040c0007810a0343d0000b01880f00070303500509070a90b035164500b8520740d1a509000381e030b1210141c4034040d2059040c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 121371771 1250 121370521 121370527
    0x9110301050906010e0a0e010f0303030c050a09031e0204141e0c0403030f030609020a020a030807052a0319021018051b0102010f020a0908060f060a09051902161403 72
    0x80c0d4848203602c0381c21500c2400c1c40e541d4241510040350148601e6480f100403506500d00008400380303038400300d030207481c000c2d03800340302499270500d054030184200354000380082c400f00020000314918480022400c03480d010703800070200c000c1d000142964a448451341d004103404060000600e042d20902100300071040389600076190181c000e00703050140d840090140190483d00340321991007a486080500709078501191648040d020080d0303a80b00030401200442d02000c0401c124030702460070703200d00b1020070400c0402c011501c03088100704400d00180220522082c0444222406403c6252104826550040c0000b102d403417001c4081d0344000f01c1c4104000000c0d0320502c0450800301d21041c0c042c01c41c2d152051103e00030170041303004018210b20040c5151011603411a0349501c060f050341110300581c11202c540d1034411080300c86060070740d841580490007000c1040b030088150400d541c8000c80d403400c150f005404c410501e06990002107040d86a0020b807480c0c0041120071003150000f50108001141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 121373021 1250 121371771 121371779
    0xa0305011403070602101107140a0501050a0204050a060c0807050124060314060607020d080a020a1a070905090c04030602160510050405071a041d0906130f290405030409110301 77
    0x91112811030404180307d4403030b1007160814600104454440c1d5026182d42000096201c0f0640c0b100a80300040342c907942420082a107000e40d40c0261410740d68001c001c0405a86000743c20340e090410120201c90303070403040c4019008200300b8840c58036050040c1c000c0300c01c03050035101d03413118035403003904040180361610070b0240003900d00e0140c1c03e5210405a40c00e0782e0360480b900004645a400560040c040c0f800060524445640880c8408001c0d106602c48503940d240000c2c0160a400b040303070310000154074428100320070f10f09450100d0700070780c4400e0070b24030702a180d444000c00d0b45e0003501c0d0008158806590301e410003400b04215241081c40b154100040d0405e682e503130382c440303081c3d00c1200301640948500b48214101c0004560040240e02d0149003600f00c501200d0303190311000c64a08150780601d03400545142c0c507030503040f504580d0050100303e10f1003550b5030790310801400100b120000e0000c1a120402c2007510b100f00350190b40100011a2920324140c201020389042410400c1d80480c01d100402c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 121374271 1250 121373021 121373023
    0x70b0c03090628050c01062103031d03070503040501141216021e060f010506070f030302032203020f060a18021c0b07030b01090b120a0f110a0305011403070602 70
    0x3400030300d002c4481540d500e05644500481107000440100700c2d4211000a10106030403000814815072210028800340b40c2c0c444140c18903890440d08103009030700101784080000c0c03003540312101c280d07119241808914400c1c00340500d950400d8004031580c0c0e00c0010244103942c0c201407217400b0700004000b0306151418851a0140302c0c280034154514880c10207040100c46c5000380810041540c004080c400031240b40c00b0301a07a544801d0303c01c0450100b40c0340002c05c05d0309021040310100c68015800200341840c903a0110f0003507100a00c1e9401e00d8a880c1d003170303000b01e000c010917080089009900409400621415242c01c01e00f01601b440026458504503140307000b003e80e2502c04240d0115022214280f408c6094060307021909001480c4582c07420400c00843e0305640525509002a83e842401c2510f07806c2e08942842540026003909902030002654210207400c21004102c02210114021560346182e50054014182800102e52550018025184800c402042c031510480080c206540307000d4000e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 121375521 1250 121374271 121374277
    0x2f16060e010c051011090a0e0705190c0b010e040501050901020a12090809180a0605182a0a03020d053111090a06080c0405040203060c09031212010503070b0c03 70
    0x45410b11040d61205030034018244864a0304030462201440b1001a400f0040c406074404c155003441214a440082912500d100c003980c0300303580585500785010303001400480003000440000c020004055841000200d0400c80380340241034040302e01c03515040a2030102c0c20b540d001005100207070700c140100d10f00d080d03101500104004142c100003842c580b02c1d0600707441500c80c480606410051400014804c101c44d00320441c844c1031240b10030048903441e4002c000b10454403c0d12240c48074001004100089104610320000c000140f8909080700401c0222110356000912440046540844c010500c070540d40100d9074048440c82108040e0102c940c118200945602049a007032129100710750200182e82d407003540b0120780107280c42a503280c60200900940440c0c0200c40d004c0c000d820f0780100c01d0420303004060060354001c0c090652136640881c0a5665007140e0381041d41840703480c1c601c81182015400800ca204100548944698141010700d0b05d804025404131440c40810054168004000700507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 121376771 1250 121375521 121375547
    0x30b12120a030e0f0727050408030a050c120709050a0f0e010303110a060e03091e03070e060103090606030b0402010e01020604080306040c170907090b0a0b0301050405072f1606 77
    0x3000921030528202c20380713800307911840c1e00c0051003410303804a64003804130301900b489054080442e901d9050f803140001503131070548006204075010701c0400c8040906030070043c1d01501151001e81008900c00d01804460070659425022030b40c0000240000d003000c914400c00b03001c0d0007100000081c1707414542d01001c10f051102600f00188414508100c0d08180145130101c0d40041c003d20400d40d204620689961204444078030450088012138580602c1c0c0c03c81c08400751000f00a828194901540d90000b124001c0c215410140c0e20300c09100060481d1103010044c1d80104036030101d0345003a100141100410070155419544410b04000009042e401280e80c171590541380030640c489000c4040e110b17540c203800c490b00381d00f40040801091100006d105000c43d021034405000c000802e8041c003841540c2801036400d031640070001400182820b40040e82c20132010314051010740508112004d60900448942030550100200c1d841508001c008030300300f0310f02907504007032840d1400101400349000046 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 121378021 1250 121376771 121376777
    0x70f0c02061305030d05180f040e0a06060e01050406051810050d1b121e150903020303070e0f0f010e1309120f0f0842040f021204020d1e03030b12120a 66
    0xe42e235241929143c01c0311118040d41000c50354010300501d0700300040d065a000b5052200c00510000805140a0060b00101c981c058020b241081c8407050300c03802020000c2c20140900b2062070300150300c1e101c01c00078502250062212100d1a985400d003c28030040d10340c0005d80000300d119800340899a05c040e4007110360a10078400c201b0030480e00c0d0004041d003560020502182c9820040c40526070003100a52040b0340b941c2d03a140c1188654002c208521003884107507508500c5112041c4510350040c54088038041c4010074a4422802100c810002d1798140b4408860480761400010804d80d04201c41002140207800c4c1840208038021004240400041440b5101d2800d0000440102c0758242d034400268485015210701e108000c500c0c56880030482845405103252a211440700c6403180b00347c41241000010703501d08e0351901c1c3c0800444c04c01c4d54a00359502941d000111074500c45040e100108944251008a280c920000401203c641d43e0402c0458a0b00f01170030b6503001a8425040f14419810343c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 121379271 1250 121378021 121378039
    0x6090105190207090903080a05181c020705030313150806030d0f031401150e04050c04091112070306050f03061501030f0f090f05071a03070f0c02061305030d0518 71
    0x740e0891429180390300a500030340c0b5018510041c990f024210b42d102e203500c0f0600f44450340747d50b070001d081d0070010414824640c10404d00c01804c0e2201d04140d003d800700c0b620440e01460745400c0060304507403084110002080240d030003003000c414061002c581c6200d0310700340355503240b500c580400e444034542d10744002040080380701c40840500070362091359501d102e2004189107617180e06081c1d400b03560848900000c074441d58800140da02c0c0c80d0065620940003e01568148ae04c1d140d04000a422038042c00e80580d0418499080304029803000321740f1825440e81c01007641460305003404210390745021050301a410030f404000c00030507501010f0842c940c080c80c0001c2d1300d41040d00342000400d110010303e1509403c1244140511121002c611601401042034419840d0307140c0c0382d82e004442540103800308420a000081026000340c12903070880406041205149045900041840e07000340c844c80c0d4601ca5105091200d400d0400030061007001d02e003003141c60014a9040042e0000403141e40314400c000710 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 121380521 1250 121379271 121379317
    0x51e0c030f19060204090509060f090321060a1203081501030e0a03080a0608030705070e07030903020712020607060e0303100b09010507080318060403120f050c160c3206090105 77
    0x143e0441700241500c2c00104018113051303a045071502c03030a4580c3c00312560b2a40c0462040080842256030000c0300080f42003060944080717044c240e0b0801041e030303039020780d00e0000007401c0c041f40140b42010324460f40d60110301b0320701000b1502c2103c0200801c03c0c109803404902c020550400a600d60720b041c0c00d03040c012019034038040c0050250150340c04c074018500010802e0b4040100004e001826103440f004a40345982d6a04412000c581000714054010b0703200c0e0301e081000c06401896110703030a001500c00e621b070006640703d4406440d5140041c9600b984000100826540411050006801c414129030b241900b02c0000a00c43d01032040301601c86130000010078680300e12850560301006480d010798940d4a01760070090900300040070794182c0c17030742020100d28182c0e045208052007955880e031940e05015000c290309011038400c5004643c0004002400701f09000302c412044140380030740e051750055900344c501e0048001c1c0b40c0b06049016203010310622805a03006015210a050304c500c40959620340c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 121381771 1250 121380521 121380533
    0x60801090b04061502010e0c09060a0b2809060e040606050d1e050a02070c0f031203090f021e01030f050609010627060e040b0108130210020a051e0c030f19 68
    0x43e50300c140b40348010030721603038200341e01900074134100344030340e02500e0040b48070794240206800201c0c1e0b1030b90b024104480502030b845144c0094506844440703800c88019511210501e1103003480079600000c6800d000041120550010009503c40400d646c10b0004c00d00c2c0540140c0b5a01030000c02c401680d490b80200c88190014801d00c0894008070f203024811801c008600c5c00017544040c0742643d01150084003c540c2c0340810145c070084030303071041c2070103d0301d405074800706d0061412100c2290301a030ba40900d030003d81e071189403102c15100303003013451042500f0240000d401c0313070070b901c60f5120060f0a101c20800307107561307401704141150100c0c20203018001074600010420809c081449140f50f00404012070b6040d4842c6455031400c0e000c2ea81080548039801c0155004201142c4490907105101e604c0001403e00d82c0403520101514011038510b050307596a041e0900c18103c0c00301582d120782c002181940c44003040901a404815405807a05c41880e01c0516155440e40e0599403051050113080010040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 121383021 1250 121381771 121381781
    0xa0b0c0c0c0f060f120711150a0f02040302030105100602060a090201080f04020613120201030f050105090a09020f06040612060608060603130c05040c0f0f02060118050903040909050708060907060801090b04 90
    0x410481e1135a0381e80b41240c606200f0002c15201324002035221801400103000020704040d4040386816203010668545641e04058144c60018052007a02030100000584003402100d001ea002c4124000055060410007807a050000b007110020f64202694030000d80d07000b0b40440d4000c1104014901c4076a2a800400c88500c40c860b050800c8401944000440d604c80d50780000f039283c802d9905018440c1c134182c600c026100280201c95005030b8a002150404056900a088940c4050568400031501900241613500a43e2020020518540c0c03d0300001100d071064901514290601c1507003401c0040c081001404028007403540d40c3c541c11280c41c140108001d41c02d0050500038000c0c421403858120017401541152100c002280301d0208175002c0d1400810300c54140e9104081c1c10100f03c0c2c61500e00b0001c0d000107441404c40d40010040480c0ba000d6900030403202901403402801902d18101115180c040c0080007030341241c010f02c10a00206070701030026411a08502c0001c030781483d4040000e00200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 121384271 1250 121383021 121383037
    0x8090a020307080f1213090b190f0504050604090c03020603070507230d110d0f030b04020724050601020a0201030509010b1003050901060905060d03050307090b04080a0b0c0c0c0f06 79
    0x111a06500003034000c0006100200d19480e001585d68030603840e01e00c0501405005506240c20b240740400780728080565104840d4030740001c0541080139134440040390035a00300d0308818804c4041034024030507801c082c02000d07040f1406860030000f110050302c07a0b401d030790642d01000703106a50000106469034444c00503201034942040d11400d15541642c0c80644413006103200102c240181c50529030101e02076402201110300d80030152200c89910340c0c0444000000d60782c2c1c48140b59481c100300b00c0c1500c1c0c910207484502d216201c6e131000c0001d038a20782aa21a02069081946da050104004030742c4d03404100980c8281d420700b4042415210309202c1d5015066000006820000c002065115241c0c0350300080d000b0f000c1c1c0710003044a0384c0c55440b85170940c1e500319a0541c12141e0104154000b034812001183c0c00311061600003012500c0d081c447d20150b00c50b602c40d16442d401940d080c014004a880d81c2078200da8101011882c042640e11910b41300c84204001500c100c1ea4809440c4440d00d4800c1150410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 121385521 1250 121384271 121384273
    0xe06150301092c07030803090102070c090902040605030d09030201030902060c10051501020a03090b03041103061303080609060d0b1513060905100303140c03250b07050f040608090a0203 81
    0x960b1a002c007203005025440c03c840f00112200218010007000001020b903c00350071010744103103402c54a07800d031954030107051161950340c200850302c0407446c480c0d03105018180d04580400d1220050040109480741904058404d4000b450f030960002d0b040f08034001140c1e8282000b1900040d9400016098004e02a031152980566100100350110680c4007503c03a40244002104c03004440004995070f1003c908001e002c14a44c500a11250340004040c5611030700c262803d4000122980119003401010788103001c0728a1300554000070160403010190f8080d03810344010904d0f10b084000500d81c0d44030030302c01802d11481003020035180c0180400b140703404100600703102180f0702a0882c1c2c6000b02042c1c401c0780d140074078080c04108800759100303204003102d030199100002182144880581c6600980c640c1c421403104000314016241e50356850001da40d00790400d80c0b014076860070001c070b114000038002070400c001040a554642c0b006e00c203072002e0700d9040c90030f15030950710ba41a00b4682181a1006985 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 121386771 1250 121385521 121385527
    0xd080a0b040f021e040506070b04020d0c080703150203070f0c05120a0e04052a0a091809120305070f0e27040507141c080909040b090f07050a0e0615 65
    0x80c403401e600200790b081c1081c0b004c011400c103000d032505094000c41c018594815070030825940400d900e00461794005000400c0104c8030151a651421074807640d601c207000942189004100f44840b1009076401b14001c12401e6146287c00440240b42180e261240c1c42404a0395400d40c2c140302c1cac1001400140c45407034080d0350341c1d8000b0139005882c1003524580360f886141440001030b1003191018036800e1041900c24013100c1d010a540c41c55256030010350b42d0000304008440000f4086905100030107000e00710440000d03520322a818070624101c900e000c2841410308010503c04102d900058154000003e4507046008003100c4000030707000324000d0010740c2104541403030005503034008040640624031402c2154140d41e03035810100316442000c0b40e559030201c40d2002a14002c4280000e00c07214610030485c0c10701c2d01c004000000d004103030130340c3d003550400050800c110141004005030040304460710028041d080c86c00b0005000b4a282d03015001c5039582e4200842c03855100d02d29034292882c001082652 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 121388021 1250 121386771 121386791
    0xc010e01140c0d0339050913060e0a1a0a0303031e0f0605030705010f17060a0305010504110a06090503060408280c110a0e13030e060403030e030601080607020d080a0b04 74
    0x600340717040c841d28030304198045000d1110b0b030403070300e110740c0102000b102944c42030411400d0300c4a80010b105c0d5030b001a10400341d203081041c40e10a15028000d0500c104415040107070b10b180c00c855491040031032350038041400c80b040e0759403003020200b280e40c10b15011460318200b41601a042081111540e00d85052245c0000b200d1425001b50003030354429800c48021a60b1030004480c0e1010f450004004140c00c5044c0200307180c000a50710703521a00140c410400c1e04d6488e030380c0d14212182294261524000003c02c40c05601d881500500100480c1c81c00c0100f0700c0c14080065112000a01700405003500020071a000501d9003443d003400710381010441c4030f403501512001d0070100307590400312595510304203041800e10300424920182d80e00c0440d071459a80d036504031080f50300b480402c00c0e014806c1d2101c0c81000781d40c0f0500104051486076840001450980c410b02d4502641a008001140c0140042041443c7c3c00681d500c411515441c001c201901ca25030710500a00c01a04665005402e240c8165 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 121389271 1250 121388021 121388027
    0x4030f0b09030c0f030d0c020312070309020d08030a090b0a0b1503130803040b010608011a120411060d0903030e0c031507260f07021507050901030f090b04140c010e01140c0d 76
    0xb0020290301001d00500340487c404a840e1710413111034800c00c2c922440842c040d00e110b0b500c0003041071b102610001011025403140160b0b46c10445491282e40d850b100c00908001074102000d03004412030009001c280b0915000a4101c00d0100340c00584440210009049804d22480e41102c07980100150369030707007850f04003407061040c24010000850185800014000c143d1640e10120402603881a400c00714500f00c02c0900140280c4240c0d0701d04082400c07072a0b269107100041c03141007106c0c84001180d948600e40982038507035022098116400c00d0f151901651808a400200d01078003000f0072943e56100c2c0410340b00c00300c802d40c1c4802010000c10781445101402d080c00c6001d41c01d5010300201d150380d001412070b540c1c0303190030f014030000c1c1c142c1000c1340d480ca005401502c3c281105050106403102142061022074402c0007041d600c049054003400280a0651120342003070201d10b020b01188800a40007908854124042504101081c04e0240e40500c0710003d4542045240094954a6180403801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 121390521 1250 121389271 121389277
    0x1050901210c330801050d03030b041a01030b040203040b0a020901050408030a0203030601030e061015090305030c150c070506060105030c070f1b050109141504030b01270204030f0b09030c0f03 84
    0x200d2070406240d8101508400000c83c10040714903692501c210382e00307080500207004180c035000c900b81500c8800018495403180182c5408041c2c140050010000b404001000c1c6d4400ca500d0724003552041080c04041030300c101100e58810704050015903114440001202c20b42318032b50042c9a2030002098010102e9030110013540103d40990382840400f47c20104503445039010703151902000d2082008105000d0b041d0200c0d141e491490401c0c50800d0b40d40c1d1152425580001c100082c00c0c0c00c04c1140f030000141c204809030300030240300107441c2012003540d40e80d580e0b410058100d5051080100c00104a64142c00841e0708096000c0b41d82941180c452801020404000c4103020b40300e5080301001c03601354810018001190660299290405603100500c0743c3d07254294403081c0300380c070100b10100101d403c1c070007038074024480c6800b48002852003800315074404120340340c112101e42c0100010400b08244c01850b0b0100c581201d8822010744445220350310b58810b0389582c140038003c0c5003445003d01008009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 121391771 1250 121390521 121390559
    0x20d060b0f030a05061507060204030c090612110a170a05120c03090d05030403080f0d0e0106030809041d070902090102060f04030801030b070306080303010f03060f0501050901210c 79
    0x5000664865003028800d006080704880d04500030b01c0020703904225034125540024004d0203101206c041d4101d81d10300c0743d1102009030341c0e09800080400400540402802c014245088200950340c2058040c2c046081480c101802018070f5081c29031031999481c92100003002e80341c0d4241b40c0c807035903c0e5550348c491002080948042c00f80d0000001d815203814102c030302c5200d550018501e8071314030300c00300507064466803000e4841c1e1105101c0880013450050040960300c00d18540c490701c0d844040c60030800c0d540d4484540d1041d9043c8a01040018480d0041d1041c2c80b01c215001304801140505910382070386400141c01d107511841800052142c143c0d07008120509080e42a101c05585024200d0750244007aa001030029103080c0040000c80c0f99030007000e41000c0c2c54074002c0740655590000e01e207180c10030381100565102c000c2040040207118410340c03070fa0b8038035840103120f190700d48400950810014481d51181542d45d10446020300d8407110030580a43d403113000c01041540301c0302030307241804074600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 121393021 1250 121391771 121391797
    0x120e0d090612090b011503020c0d030204170307020306010b0309010b0307150e1503070e06071a160c12050a020307020303030c090913080403030f0905030105130303050c270d05070902 80
    0x7040c1c0e88105100c1c0103c481458121000c40410b901c0e11041400f40c1400040210816500340400e0541e40f40920596440144a550250b2614140006004100d004007840681075008115100040e20081500750461744190a10758aa64810f81128090320a01d280103915000d00d0b40d005c1041940c03010102000360850f510714031054071745e20511806d42109280c5c48101c840510000b00c20622900100200d800080c0c039060034a10b165807040c003408554031604008206200c00c201071030090030004070754a0300910b0411103800a40d184ca0381101402c84040c0200f02000500300f20b40d6000304211905584c0c050116980c901e040e0110246c140c101a5100c1c0c0300d81d8400303012480020340450240c00d440d0700050680e160500e1a507017550b5080e031080c010024030600380800102d681e807e20801c2c0c85611800804004078840d0700c0e0040440b04001c20b1501d02a4050045286241700c0381d005400103c081c1581764000721f075000c001640c101c504031000b040c42c421440c02203031003142c94014000b4510b0044c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 121394271 1250 121393021 121393037
    0x50405010c05070305070602070c0f030b0105030118030e09040c33090308030c030402041416021015060c05010f0507200102090f06180901090902010801050901080a03120e0d0906 78
    0x4400c40d1503100f12200600001d100b4014400807032032550090101601c110071580c0e81940d62401c42080302c1d455403041e0385592a900040283d0b04080c01030706030520008003081e0400d00941d40c080d28003400d21010500403458000010108682d101d0710801405144075001081e44008000411480810080741c00301c00444107400021030051040c4000d0381da2107407002d400c4d503880d500d50f420720760801030090364015166003400c0316101d584c0c0082402824448140703c05440c104e20003a00d09288039040003045850400c0903040c28840e48410019203000785402c90640c0701a0918501511031a003111a1151810042c000309542080003141d4078a01c00c41d2401c6040c0034010a10700f02d009000916400001410011025140510003055040200075a40700148100070216003071645c26008079200e11382d00c40d08030040d507030803e80c041e00511b42210003101c2c56040c40040d40c0c031105420001010300c1480f0404408030b4480342c20005218241004480114800c504001c1c07240b0414820705002c20040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 121395521 1250 121394271 121394291
    0x903070b0901140a0309061407020c0a14100309121106071809090807060e0106090e070503072c0408030a050109140c0f0403081602121903030f061805040501 69
    0x2103080d81ca29a10584424204008032440707090982e0112401404050307a8000480c0041c206100e0304012107520844500541b6210310083d00e00a4584034980c07042c1201481008402c00450030a15158420f40f040c440c89120024181c01401c0e841000030b1030044e819040c4802541c3c0180c6c1000c94012200c1166025218000155000600c0365404003604641a40c144180360303140d001040313403030311840c011450910541c55031002c445841c80d184d8081d035103800041001020f1402229422100b40016100d01031500c1e000079510307009807044580010b0303600600c0500f410030020f01c803070794200449900582d00d00b500d8100c84d2a4801c4a076248000c1c5000004190b0300464426141000c1001484107002d8450086549841d04540000701c80c2a901b04404800078070024090583c50b0115044107001001c0c0344100081d0500304d180d03420290b0300c185d280d042000b40c81c140d00c200ba80e0b05814006240400c400511026003c184c01c0031050101a5000c1c0c1030750030131948510b210741e0240b0000c00602e040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 121396771 1250 121395521 121395539
    0x2003090c04061a04090b0609060a030c0f020f031602060403020d0305030a1409060601210204090933020906121302010806010e030c041109031905010b0a031502030723090307 76
    0x440043c0c951018107010a000960b442d0b844030b48203004c010002e0f030610300e01100040c2907600560788440040c0c1c40d0b212056007250003030300d41c0f003c02c04e150014042000041c034015999000740000324010121400042d41903440c0c21040b01d0185401030910380421100c0c0c10050203a070300a40b640c00d041880c0c003508020700b180000c20300d401046800050149a1990001101c5103411590084219600c4039109041c0480700d1002300010443c54402190941c9542442e0398044040403400b081001c0b00900d90f0581b0b020645072886c8084c80c1c40e00107884580d550042500c5010b8008000015600c100c180f080c168071070340d005609039100760380d1200540e0362880112080c0c250041c0300d0707070103901035240019203140c15080001d8a00c400c42040f400c0107403000c00a4a01701d036119030641c00084100300788061040c2800740304160b400030740380014451310303581d202d076000c070a03079040070002c00d5010000c50314142c440c0074614a04c03c443c01580800c03030134100103240340d036001900c0c0c541b191050310f50000b00d5083d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 121398021 1250 121396771 121396799
    0x6040c12020d06051503190507051002061308070f0303020306241804140f040201020d09140f120a0c05040e01092d0b01030804030308090a0210032003090c0406 70
    0x10307000c0d000c02d0300c00c602039940c2400342c2401342080c1c24464541c0d84062031500d041010007005000c0d40442100800725040c07203800e040081c0c10060003072107440103c014558002504075044404a41d0005602e09641440c90590090f80c100500000c401c60050b0141a85600910b00880301100e004000100c400c1800e400c0d003040380d2807650b80500500c03071a8048d00c041c009080c0d00c0cad40058008580080b402c060040c2090302200c2c0da00340b450452040c4070641d40d042111448040715414030114150402d002501c2100280d9525846a10001d003402480d8940d1a500710318110100d080350300070a440c1c98001030468540c02928011841d04058601200c01400b07482c82103508040c0c91042900ca1881e0007065040d00f451001c0340000d207071071440020f08000c219900950141d60070584507421032130024070940c8042c00d25140c0740d02c8000c0c01d1004d42e50350f15a031090441e15050004061400d00c544c00c52240d06507a81c01000345001c001c1100f440d101050810040b031017104c081104503221501031003054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 121399271 1250 121398021 121398023
    0x10c02150a051222030f120e15090d170604020c0d0306060e040c090b07020d020616020f0427051c11060c030f0109270f03090b1e131706040c12 63
    0x84e44074841070302282c0170b22a801e0070170010b8a03100301e5039410076484e10103032001211402d02070303400b641040071034150b0860f0081e048489040505071000110f0740080280070200301d031184110042c400301d200b940d00c5504596a5040200940780c40854501001d4001d004611440d07010451043e900318240c42c140c071901da054a580e1b00c50103100c9042101e1500e66802030300040380c11240d003c80407400744e5a007101401039070b104a0000000301d007042c41440400080d075542035008a040020110010881c060340f0080c02e402118401d503c0e0100781171051411902d00e42000c244041c46051402081d8007403003102c0302d028000210358050f29000201a8140310484030f208001018400501180005402200118094a10310180305503200d2410401603c1c1100450741903110036040000c25802041960007003c500e03909500345907560403071110300711f0a50084620308100140a28401c0e03006520b100107440a420035005140c0300881590f03440300103940544c0c0304001c070040003800381d40f4811010211 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 121400521 1250 121399271 121399321
    0x2070503010528060b040e1e01140f040b040c17100f050111120d0603110f0303031911030703091a07020d0305040519050601060e0915010c02150a0512 66
    0x101100814440001802c4030411051329000b00003080031040010300041c0c00015649101c034104030400b103c590501d075a4404820903940010006240c2181510344580382c2500c100501c5410500010b0081a80807900c40d4030624141e0b1803e21958442e1003c100c1c1468405041e125403126200803401d01824820303030b4181c2c00020b41c00d22495105a5020714141c2c0c0100888182d425004036114468100c04005030066959240401c01e00120308a641c0494000361075a8506180150101c5c0d1030703200c010240055020600711100500d006980000703100340010456a4590030107460003030103403008403415070351100b454010100801200c1900382c0204c6540d001031200c03560105055001d040300410548150080100403200c101803080401c0c0c045d0f2103400a0a241d604100c805000c04c600d481070300340a0203004040000341c0d4844103103e21190400d003403100b4011100d100042c5002030324040c0c0c040500700400c0b032241040d0410b021f01541540c201d00e2500b10350324007101000440d1140080d101e5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 121401771 1250 121400521 121400551
    0x408060606090102070e070c030e0108130b090a050a1b0f0f030b0c04230a0605131403010b150901031b050d0f0b210c09040b010b0f0d06080c01020705030105 69
    0x16500d000401000c0c02c05060041d01d1801d030380c0320002c0c40b010104036280b80c003144101090004140c0c0c04040c0d91900c2d502406c0100b11420400710503d0650703407100004016041c80300210302c1e00d41040000d054400d82c048100c40110040d03140036101c05100d04102d170600070003504086000022500c14209464401c6120f40f455880c58881c41e010341005040c1c0c1e1000720b030401001c0b40d0b10a03141294000c04602d02d161606c2c4810040501c03601503900e5209004220040c01502070882c2840d81c0d0740d00b240c040140c05c1003007004100c0040d00501c2c165458030342c40540c0c150a190480280400780c0440c070001d072000c0000c0040d084074092100c290030f1109001860410140c0359101296010002910401000041440d0f00c42d000c00c11054425503030710601802c01220590061041000122454060390314801c0e5003025903440d1855101070140b400d41e0107011443e0021042200c090301c00c1001c3d80c05090084a650b514055200d43c20340400f14014054400c0105641c24140122170045103941038040c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 121402877 1106 121401771 121401781
    0xf0804031220190321090c0305010e0604120804050f07120c080309011e120f020702030c1207060c0201050c06160810050105030105041112190b0105040806 68
    0x2d940d4803400e442c00803444110544046180c1c541070030300010b0030304040030920700c030450f8154091500c3c21440c4000d002500c3c040384201c0f8000c1000300084440f5402107500d604040360043c2044822003100200c45100f03002880d0f006008400b036862031484400c1c03607828504580d20809901e44156224003c1c0150310580000424541000b907151440003c0060408140505958074080d400d146048034507004044801550201d01d07010400c500702100d03068025008000240d00a105524031135165080104c0140780c90700b01a4002c103101840d24800702c80000c0c4c4040228104107040c40f260742d85100400c6218080c251b02c160f070080b26404114001c08d141e0004002c0d1840701d00c040030400c07050341c06c201142c0c15901c0a40d8041080d00360940b00b25a244106142030009442e10001c210f48001d04803410702860300080b00c2403014000c1c4000440f03940c0201d00440c54990040c2010503 = true := by decide +kernel

theorem cover : BRFrame.Cov 121223021 121402877 := by
  have h0 := BRFrame.cov_init 121223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 121223021 ≤ n) (h2 : n < 121402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
