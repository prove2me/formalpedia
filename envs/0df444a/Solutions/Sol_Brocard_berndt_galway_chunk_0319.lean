-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0319
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:11:16.767273+00:00
-- url     : https://prove2.me/submissions/f175d3bb-f6e5-4542-b8af-61a7ad7bbe50

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 57194248 ≤ n < 57374104 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 57195498 1250 57194248 57194309
    0x3041e03091a070c0801060609050d0506270105010e06130b030604030302030c070804030b011508070207031b08030d0f1506140304050a0c08010b1305010b12070525020f0a 75
    0x1408180c20882180c4502c0c2c4c030034032240c2c0314036041d941d503010620149038042103440150105484c11103610000f0340c4d98580c0d8400046c203501c00f41d40c40c0b50000d0104014103007003030300c0604098024482540c440b900700140c12020b6aa50b4800c0f2000d0080e0b1031078040c10302408100c0e400050180080b6900c0f51400e4001c0d520003444035094000030000391f000070310208080c0000d1801000411010340c1403035940d42d00a0b0f00b41e035402043c049040208107215038000381100c02d40707600c1a00c00060025404540e100011280c005400c2c134000402c0b0005000140d0340000f070840501001889100725003001044c49840303d00440c8006010b9000c4801c031f6016800085030014032810407120219810780758200d010100c0e0300011a1651290b514848a00d060582500901c0b014a020031065140074100f1400e8460b0b10000c00c00110342c1d0002890450003002030310040310712000c940d0500c145404400a17003c10b405000ca1241010800a82d894186a110310059404800c070700c00340d0307030020601c40768280078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 57196748 1250 57195498 57195539
    0xf0c07140304120606090c14030705160b130203120406050901030510050603070801030303061d06040c0c0b07050a09090515060708070206041409060306040308161b030503041e0309 79
    0x402c000005694501e040055816405071600080305c1d42414902404d07540405002820042d003071500828803036a00040b2038101c031040c11300c1c660fa027002202c802c403141c030484809015040c2c05410000c0c0c0600c802d0749030a06c10b00c210191408404045580e101c14011400380c2000107005000140390365000340d108035004038060844a681d0b0740d4a40010b60140c2c0121201000140c0000c010403c050301402035401501c40d0100001906442d0901c2a440c13a00040c040342c42140c40703001c0ca4820358000c080510419400c80300740c034070a10740448040e24683c000070340700002441c9510b00041d00c80c01f078072545e4001d03d00c850900c40041c02c0c50003001659009804203980d544420040346005948400083c401000741c5901050b046102c07108100710307518000c10340e42c0640c0005041000080e4800045035011400440010010003040404c881000300b00036a0400306441c07840c003005160300000911b104d03038411341e0703811001c00f688050001402d96200c070040100c1c1800340c052000c0c0e20704c6080842c020f0b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 57197998 1250 57196748 57196753
    0x2403060d0213020c0c13021914120c0406020f1903110f03031005011707140f0f03011707120302060720250602072d080a03090503060f0c0714 62
    0x220070104103012a84070601e907108690054880c80c840c0d0400002d40071201100750400c50424110000352001d2240c42c129140070000700741c0700304502a644105541d1010080582b0f013038646030070100c001c0540c2c410b028031000f5100d00301c030b40a0341800c005460304491a520004050410f01e50b5010380b0045040c04012901d80900c184004150504001641c401d0340100c5003400350514000015001d514044884000c0450305c00401101079000b40e1200c0004140030106a614207610540c0a018000c111064a0350b620000001540c0505425940c0c2d8006541080d209601e540c0d0b070a102c0d810020700300050145c0c00400c00540c460740200924220f1481d0080001c20303d91707a0551040c20140380c4642a600103219170500289220034100840141110f40002e1141034188201030039401032209200076a11030000040e0f040011407441d0000500a00003244c000c158180382c082d24841e418010280170b44a9400040d64803043d010f48140542c00c002441d030306d0140e590302c036181c000d8140c006180461 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 57199248 1250 57197998 57198019
    0xd0207080909090109211d2d04061413050702010603060e0d090f1a070c0509010e0406110901080406020307021507110601090c020c060c010603060513022403060d02 72
    0x54a40b401c8142c8100d115400000b6100754601d00014140240c40c48454412010500d81c03680681001a80700c150342105141e0541300200c0c00011024000002c109940e03200e0100b00e4150190203580c0341428010440313080c04a01d458282407511022500da90a9020395180030140c2d08000503032280350407240300d10000c16029100d84551050303a484020105140d404542c3e9100b0403a40300f02c1c40c4002d000583c91040045240000440405850544107176040f4070018a0204200140e10410010080904406055030b5580d0845400140131581990501d003800c03a94150088004104d81c0981d0058442d01da040d00ca0341c80b50310003900f00034840b000b9413150b110f03030000740b40040040500c500d05558410b40031034820340b951410300506900c0807181c0c60038209040301068010a01440d600f10559140762107880c522002c60150420340d00c094080341c075250502c0100741072138540300c0000d4002c2e51455200080c10b02c41c607004103401c50344024401c400b0700200360f5603c0c00001160701d01e03000a0400106 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 57200498 1250 57199248 57199267
    0x606050402030c0c0d020601060f050a030e0f280215091c080309070515040504050907180b0f030307030e040e0a17120603030403080304060209010507060f060503100e030d020708 78
    0x300d90003960003943e070407804a8003015260080004680f21805480030b0f101c2d5514020000e02030600d40c07c001c5060100115640d40039510036400205e000e01c200003100e0030001c80702c0c0040c1d12040150920f22031400f1703003100402103a0400c40c4170b524450340139200800f05080107800017104d801c00491180e0082e40c28884d1901940214070080d01c881c05041031542da0304004940700d150120550004d8012013980d40d540c6031030190003050b01c048650940700410380d40d8070319981d07070f06000e83c640100c44c4081c58610207000142d603d0b031120000910a07646254000310110030180d6900940700c0050000e030040c290043c440c1850f40210040e081400111201d0004a603a10700d1628055006008151000f0510410b16040707a030206400c045c040e005503282c80c3c25a00c4590080c400140040c040c42d80014403121942d02c160221241190031040c200140d612180403140505150711410348a07103e0400d03803d855070f101c0c0c8503900302e84010900440c0b500c076401428602942004400760ba049509012a582 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 57201748 1250 57200498 57200501
    0x30306080607030b01111501050609040204030c060203040501021b090601030911060403080306090604050c0307050a021204030b0415060807050f0328030807030207030813020a05040f1a191206060504 87
    0xc2c0c000390714041890440500014400c207011340d46030015600c4440c0c0195540c15000d0200d0544000396031a542d03541410740818040e12031a400107041c81d81010b00029110390201c040c1c81076071003d0b400d480000603003c44981d100340303c07109810360110102c0c0109803950f000c1e0b07200b001400d1048520340384041e03030b400c009680340c1c002d5481601c06900010400000d45446180365502400c11901082141041d0040b48001c1c000100b0000500800042d02d28016000b0003540c1c60034010b45481c66550b0f40c0340d290002e0800000d550440762904001c00c000001005801b030b10007612107113030003055024544401c22403504140e5055a4041c000c0b0f00030078400d150b0007200701c13080c0c405a40d03010400392140e1500612401008005070109441403001c4400203074040101900096003040080e000c202900000316a981940e000582c8103240034a40850b40b11980c0140140151035106000510b10141c00d00026820824a510020380400400e210341004201c108406501030100002c80381d407079801180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 57202998 1250 57201748 57201751
    0x130c080706051e0c0303040206030c07050714010e040605090a090602091002010c020d030c050702150d0c090f050904080a08091207030c230606040e0c2806020601030b01060503040303060806 83
    0x100185000586400f03034803c07158050b08108400c20418035260941c82441c0d02c901000d0320080c8588030000100383da5842e40802e945072a0b40040a9a202982d68401907104903440840940815080501000b061815204440c21a0070150900760f881c1d4400790385100070191444119660703079003030200da130003a00c510900801c0d940c0260000a040084244080d1810001c034007040101400c020300d01c811190302200f03641040d42d040d158000028450701c001f00c40e901030600104a20351410031544141680441a1802c551142c1a0302c411140c0302c03030a1042d0050100c1e00035061140401c50002550702c0748030155805200c1c1d00580d8100640d0801101ca99032001ba02600040c1005003224140000c2907801c64180d030329000112030940001000945818000303102500c5941e4403c086612500c0911560030821002002e1442185405844205094501c561402d00d28000700000c154980009640fa040e01d40120000d1120f80c40d0950480b42031780001d000702d0404d6242c10000414820400c4410b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 57204248 1250 57202998 57203009
    0xc1c0605040c09060f0b22080102161202030406021506040603020d05070e0c03042121051008010b010210050601020c040606030f0e191709060a080901050901090b130c0807 75
    0xc2c010140b038a00002c00307030759080d004491210382e800400c100031003e0100311220001014000c0c4a040707900c2921254104140d0701494080d400040c1c0c0b903c030140480c8540309a544204071007006540140d0302243d42e40514001e460250f403021a0244001c2d0803604020382c4200020004901142c695020038074480341c000c0e0840e001e511602051141e0b03001d0541c81030b070200800c0142801c40c0307407548410b0402625284540001580c202d0840403c602c2818507003240e054406204000e41d50002000d002070030f08542401901080703a00c0441d840c941070240d0b448407c01640140f06101c008440c00c030041c000a0f00142c1584503080001d6403944407809000020240c0e510001018040400d4610985039851806a46030700000d030075210111106d00c085480c590410384500a184c09141c2c0b5070114400c1c00a4540d1150b0041440c011040d400390b0080d10681840c8000d0010b615850100c0d800e03104034240040500000c4000560185007550480c20650300450728465055511146d45081641c15000b8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 57205498 1250 57204248 57204263
    0xd06080f07080a03050f0c011103070c031202040308030615070b0403120c08060a06030c02010b0d050d1b050d0804081b0106060e0901080706031503120201050a0b040507020c1c060504 80
    0x1a1000c04080c4503100052042c4005021122803541e0b0080092040c40c0300e0b1814a200880e03001e0039103900b541f10500c50045800c0b1640c3d41d0600c0a0041c042d00c0150004800142110b1644a444043e034000e96046079403004040d400c41d11524208808201a2100b400c04004140203100c003180c0c2805080f409240a5144c954810420b805403c00342d4280348001c1e000c3c048050240721041d15603a00050480e04a4600041c0c80c0c403c0c035030100c0c050003c83c040650b005500017001010710502050b211300c12046503c5400341c0902880303c4002c074507065000640960040202a8540d40c001c20001e179006110321642480c2945014210403040d4800e20003d005a6440340107018990b00f080c2e507103c2c9210102c0b1180350a41c03400c02c0c02c50703603440c55014810070542c80b10185445000140d0707204011f542d10910b40c0581e1084110300a0003010300319944103c4a0400620000034140742c481d1a00480d0707a07501400f50700304608140620b800ac0c072407800c010781c41100039241c0416a2441081d000710701c00c580 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 57206748 1250 57205498 57205513
    0x602070e07030b032e111801030b010306050d121b080702010e01050d05090d080c12240603040311060604020405010203120612030412150b0306161403070c060606050913020f0d0608 79
    0x51030b001b01c1c3d00400a55141410810140c510b41d590035054522a07402480d000c1050b03071601d00100d0152043c1e0b4822a001002c5c1c7c5d0682c0c00b00300e8030302c13003003140b441442c1e0310303d03c0018840d000100c80070340048019120050801400e0050b5201d0503d400c112041810203615001141c1c140b5000c0700e030219a2a155904503078081501158090680358000c07421010075814114240f8040d42c020b5405082c0302a06c2042040c884810303140c1c3d40011001c681c004100c0c07a260304d418103015001240c82004541c86018201c0001d001340341a1003500c1c11f4841c10781c0118207010182e000b141d003550018068035442032070b002c05002c0c125002c10040024100d41c4001a02c9a443d520304910607010010300101d40c917003026070b00302541c2c50004032954407040300e89504460b079500c074100307403001d210015803c0c103402ea000040003400c5400540025046201e0f01040015a41d601c608807200e014001203550b00400d41c0350421400d502075006071a1078035111810700d2a1411180362071040310f85692004900d60017a00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 57207998 1250 57206748 57206833
    0xe04062c0a0302061b120402040608010c02060f0105030a0b07050a0306030204110405090a02090312071403040e010501020c10020c130e010c0801030b130c060f170705130602070e07030b03 82
    0x215068020545e010722070095180c0414044d00342c01440c00c0e00304007850a00c0050159915901710720014101140200300b103402c0100700a45070003084803604480041c0c1d500010346420002500c10b07819400806a05098035040001c0303a20782d00c01e0600d0000c1585940022015a80300d118461042200d6403419655501e041c05100420b04c0007024803241d54414800b150641d1070200c0c084000a0300a00707a00da6560040c41d11120409120a04070420301c80440c0100c1d080c28401d6416050b182c090702142c043c00f20f251708001c80346802c8007a050040c0c006a50502403424264800552402e58900100b00015101c6020782100c0001d1012070004900c0d200401c00e02c12241d13a00703504400c11403100c04441490b81c0b42d454445042c1d02c640d40401100a4032444068833070029a10340d015250380280207810413000c02001600a10050b90510000c0c4100240b0780b400000c008013220b84c2c00821090310780d105101a8010104c446c1d805405005081444041c00806c0350844070f282112803010f1364801000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 57209248 1250 57207998 57208003
    0x812131703010801060501031802010c020d08041409010902090a141203070b0703050c04060512191401060f180b0a050705030c06010f0e07080411030705060d050a0507090e04062c0a0302 81
    0xc6d80320b68145880c00680e03c6201c0b400000d03000c0c0f010b0302820101c0d014102031001c1881801007080260403070b50b002c81c02281740d4415a0303070f1810007401151307148070607601c408101b1304a12403a032102e640092000410407800110802000350040300a0680c110300b000e80d04005d0440d4041d5104a4a804450b01004911a0544540d542080390f4181c0b20b0704003420107001425510440c9110a1101509400145920011501c0508002415a050048424041c0c441d19030b64000e0046a02141003c1c03481001188641440b0300c90002640022a0315890040380c14000e1b03005840c0682040010004c4030f000c94020802800d811001600409a96140c0000324011041e03942011038284804070612021642c49420386401642088880280c3c0810100091070500c142d0f0004d03800040200784210b59040690103184140c451400a010640c3c40c10f070200c40803036030742c000d08555420010210340854a00d512418080c100324000640c0152104183c004020321519034840701d038402d000c400c0406506 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 57210498 1250 57209248 57209261
    0x9061805071e02010f0e0d090611010209120105091213060e0301020c0a120e0108010e070e010e120c12010e0a0f060b090103141b0310020906130603090b01120812131703010801 77
    0x40c41c02801d06d100138103074008c118680a1240504001c40400c2407909500203504a50711240014144030b01c28988505040c0031701022a5140a10701440304807100f001c40d088121121211010900c4443c142008000d81d100d541c1e270660150950b6007030001c01a80d9004202d000071181c081d0b40e500401460807140200484640c4c00502d0400412000405c210072512481a41059031420041c03804401100100c514566000c090769000800c6c00d01d0010950000ca0590074280058030f008071242c9018a0043c261510b080c01001e05030302500707150000c0741c0400d41b8034000c60300c5003a01040040354480000c017448000e800a0b5030b134a260310010a40030314100015000c032181c500620440d0101c41c0c00080e102c520341c41e5030203180d076000a80302c1800d0355140210340c4c4000040d013031641d15a440d080020010180000120303058403a003400481e110030908444404103511182280c03034103000e040c611941440c0a403802c440158038004000028204101f56110415031002c069100c0d85840c03900d13030a6408 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 57211748 1250 57210498 57210521
    0x305030421120c050c0405070302030907270504140f031c0504240f0f02040510020f0a030c0f050a03020d0912020a150509061902010609061805071e02010f 68
    0x2261440390000341c1000d00c0225510b465042000c000c071004d0403d80d040540100d100b9500516140411005942560103103000b01d0480c3d08848030180c880344030030720544441c190300b43d466800c003888000641c0396801c0560f219101c2c0c14008580e10030075100030700d008022442d010b20340e08041555044600c1c00440b09030607aa5600041c026814903807a20340d021f2240c1e203000850005040030b0138500c510b1036085126600c08001c42007100346109017018001790421b0142c10322544c3c80201010512f440041e0003c038070fa220502401016160365000d8034501128181111b000b5401c82840740820001e000a40c0d456000b42c01904510000340c00050800c3c806402242c0d0003494402ca58001d61500d007100400da56041e020001c43c803020700e0f8141c038a40501c00c40d25900c5030700041d540c01040b001003125901580b19030003d015440e181d5040c002a83e01501680303120301c0c036400b424024520503030040d640012450419580070080320344030f103202201c941c0740003006d83c1d10b900009224079072620030f5021514 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 57212998 1250 57211748 57211799
    0x31606110d08040807060506040b0a06020606090c04030309151209060c090b0f040e04060b03060c070311030f0d0b12030307050903121905072a03050105060d08090607030c080403050304 81
    0x42e2513a204103060268801c040c110581d90800600c441c0c4541c0d100d102d003808001c2099012548c0d070300009648035021209140502c82c610041028000c10300142ca0690b58542c96840d0201c0c00c00c05072807141c03a43c49903c40104880d02150240d0780703000f88550212607004210118000c055014080c000401030750040d03081910030048502a44050300540301030f0740c1d0443d01d456464030785041000c050103920300c2480d41800745005005003015100c1c010010702c0d120f511914181102c2c0380303185840340502c0c40f104800600030003405980001d00e070700642c807444004110360b01c04000f000c00d080ca107400071100c540110300000340c2001c0500c1c0401440b1007158021501d207150120000441c0703050300c02480d401042c44400b14400c81080008074030b18200c108510529100041e824004a000821620040d034165183c00d02141003410314803440c0748056000705055181c000214180f0042d680264001d50402c050004007400141c000d07030082000358054401980c07201e0401c03910841500380c0c0406003c1c1030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 57214248 1250 57212998 57213001
    0x510090315090c0503010609020705061005100e0303070b0a021309090210050c0307081206091305060403052d0705060601170a05040c050d0605180304120809031606110d08 75
    0x50740219022441c0050a10102d0940c0c403c1ca80030701e01c0242a0040d603415424001d0101740ea5226501400200b4041d004507121070b20740c8140e004001c001405000d40299a01c42e40750010f030f00a4212502480c000740860340f520201303440e4002400026211040140d40005918044031034000c0ca41c00a800401c404010317040c6a6030008030301c45172486034103040c044080303020704503000140141d60380f080d080f00040e503903450340552000b061441140c001d07201e81c005001003002c208819205044c81c950004c0182419200d989003507680e070b00100e0000d05201c0f90101c0744c0c1c4aa01c01440c2e00501e0000850070941c9541ca6032801a040800003006503040100c48247c842c2c40310005102d464211064030800103158680e0300302500c2100682c0c000d03d030044104a01081046031640c4454443d07a4803c0218030106031103500551a44918803807441c13040210718480000c201644010708400e10010304079818120403a9040c849907407940c2c044404141c0e60314162034445001e21405040540914081a16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 57215498 1250 57214248 57214253
    0x5010201020c190203030708030108060604060b03070206040201110f01180c0603020903030313060204030f0f02090f1e09070f0807061107060906080709051f030f050606091c080d020405100903 84
    0x448034807400711444100f40c85002415500d080c01102e60f5240c20000d0302d07a030b03903031030714106940c8250503102240668a4042c0005401524005581c0103243d80d80c09007446443d00d03001122185d0040141501d240918003100181d180c00740f04903040742c02c0c0140f002c11104243e0404a000040700e034044030925004015103a050340d0302008803940451040782c1c00c03c11206a06251000380280d030001814440b950850303009010200c1c0303c001d1024800c0701c100701c05960383d10f005480000259011403d001c4087c10441402c0840c9102c954001c100c842113500d410743e1510315105040c0590700042840d0401501403200952182020044c4a14140180040c1c1d02c0e1010050154401d886a0f40411800300f0218405500c6850b84500030440207150140504141c0900300103e00304103144400329142c41018032032048075010b200e200d204000d1000d410201100c0030304c5401c05545a00c0c90344442038052260000d0310300070107000c9582000d00016110ba013028140180010500c41c41e009120109004200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 57216748 1250 57215498 57215503
    0x306060604150f050705030310080c030a02030d0c02040b0616051b010f11100c03060819020901030f05071a070b0c03040b0103080d020417030309070b07210c08210105010201020c 78
    0x2c504485240429000c003a001003140d941c0603011001301280000002e010a5070725507901d0a0a031841300003503c01042c810401c240d41d650000100a4058121018081303805002d40f41e041c0c5203d0000d44045820300044000541c0d44c1e02c40303c00e223410502c1e102200c0c0c080c440204501d181c0d007814440728144c04042a00080d12111109080108001158400000c0800c1c24842801012001542844070801018000e4050503c030300810340c482c42340b0074140c9500c00503d0444e030035181c4c0250a030b4202d40d00f181c4a5900c2c2821000302500c2910503003800048040d003030054050001840d094103a1a05014900321105000181441c449900c040c414031000c150401c1d0400c1c1102d03440070720255510100d481c45006409140c0c040390303503440d0354005510b0b00d18020000b103118074022010764910b207858504840c103902071580c001d0070407100b85203d10745044080030f18000780b00c076506140d920b10402c0d40c0c42c1051039006501d26a407040c2c45080d8408a5404141c085002d0f21090009608201c1d160b00e0155 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 57217998 1250 57216748 57216779
    0x30403080c0a1718090601030f14180718020d020906280c110409061104080a0b09060c0f0703030902120c0405090615191502070e0705040b070201030203100f090b0306060604 76
    0x20300c5841750001054070703a1b029902000404506035018001066180030704c00b0098821103100c007501401071900d00080c100402d0110544403c084a4011442c5039240d020080d0030503000e88018a50030000b1001c81d650f131a01800d0381c40d00303c11104260290a01d815440d01044800c450140048070000000040030860f541250403015580018090b21a00300341e4094013101011001c405030000c1d0118862401207030b030501150241990b41c0e420b441e910105960362604a4000401c9002400100c0110354180c000b04090f0340640f8020800140b50303000a81c0a0392108440600ca5205041c1d100c13083c2058000d5603403000c01400606045e28019603806400740e08002060710560240c44101c42230301c44120b070701002c1c004007104218120403940029513903030440d00681050304608e10000f4030faa4800e104484c140c41151000301d040003120740c010340107501301502c002d1200c0710029010a40c0380380d001c00207000304201c15000c81d041c00384406060030705601610543c01000200014821082c1840201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 57219248 1250 57217998 57218047
    0x301030b010b21010605070c050d03080402010f050d0609020a0807030603030813020301020705010f0c080108030918071101110a180e0705030603160f0302011e0f0809030403080c0a17 80
    0x45039101d41107400c1c543c1d40b410b00c46460700c41c40d5840c1d001140880d485405080c2d0b075482088081d01003500e4204100c030441520800030001a4802c1c00200103505c1041c1043c0e43c4009802c0c0242048a54030300344055410580010081e65800314024a007143e005010541101980c14204021411500d0051021100408038038008079500d956004545007581111040c60700400200503000810f01707000040c0c0612003040000603003820000ca40d80710040100c0c3c41b2500d009049200781452403442c400c840702c00a264005000150004914a0101703024040131613040000c0d45594101402001d00914005046803008004103101841450066003080341c000c0c0361820902e41700c0d9151000240ba101c0d00300e50070703409001c049600141e58410741c2c0810013076a00c00d07210094009088224a03036070312820039004000074000d210301005a030150410582100c00103003640d20b8141c60361911b882c0c6074000c445594151340040c01050030701c070820403201e65041004207003d1038000305c4108103e00c1610ad8080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 57220498 1250 57219248 57219269
    0xa17100504020c031204060207020f01050c0c13061502060403080106030605010e0603100b0c03070203060a0b0108061002031e0c06070207050315100905070c05010b0108060102070308070c0306060b030a110301030b01 94
    0xf810225141001610554082184500d06034501890100040c1d00010f000300c0c01816000312244041d8015401e03280070010701402000d0786128002004040c00a41a24800030340e40d41c1804601c0c0c000300094101401d044c1e800400050929240051011f203050b8010700415180c00b0050259a90290076142c03607800440d60252240c1f10020441404022a400b9410007140000c1075003280b04040080e086141c000c40036107480c3d5031420f04400c00c0c0c54103001c0302da002541d404006111072030024901c9080604d40e204036814101d140304203e0f500c1900c5c41c0450800c2c0ca01040b45c055401e410407120b03500089d2031000c0d212903031814000c00e9650304540d41494000d14080009061101341c017489400800b2032080c180310a042001d4003411000d608003050303405500b0402d10300200d500400420b0302070700c41a8010041c0e240b8644640d1310b5500310307050448410000140000c0460058040d20003c0d10040071001d540f4203003c01c80350100c5501d1426640c689a0034001000400d031424107441c112884400e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 57221748 1250 57220498 57220507
    0x203040e0a06050d030c03080c07080301050d052e1a01050a140f0a08010e0708043306271a130207150b120601081c0203041a0a1710050402 61
    0x740000d0724294006075004400e10f01e5030003d05030701c01985100301d8041c0c4c0311501c40340c580404054462060150282001008000401c031f00e080c1400f0710703404540154291402015041c1c5191000400704d050040108186c000c1e80100d08c00a20a0f074022000200e00c1081c002c0c61000040d10500859078110709006140106a0044a10f641107460101c20b035003500b0f560f45050781e4040c000c01420700450b00203440c01030020385441d01400100340110f8020741006e80032400d07101c0001141809200e003072425140e00045100d83e058501900b40500188200010680c4480d620040f05009544400d0101800c4c1a1035404035503005600040d0360109589803450f5010102155000e031040c0034008005000d54882100040c03d00d80c45140070000440b40070f88140000820307941d0b120402e015040b0b444c2c00620840e0303900c5190301040c1211184600559080542c0d41c0e280f0304400050006c2405109070019255006c00d41c01940c0030f182040410002c20306007821050b21000304020f00030b250180d6030004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 57222998 1250 57221748 57221761
    0x11031009111c080304121d220b120c01030b0102030703080f06010912051006060c08040b220e1b0c0a02010c0503220302030d0201050c0d05250201140114010203040e 72
    0x2030605034101e80124805550b4241752904564211481da110030004100c0180b000c40c00070819881014400010490160455000a2400760650008031010056030720605504a40c90750031284901c7e803200c41c054650382c01000009800ea0310300c02e11490454004100741000642c00002890b080084200342070780c40c0e5203020050f034204510380c01241c00141c09445582c10800005a40741c003414556000340711a6944907800d031009425003030b008001c82c10501c0306100ca903030004050660204101c807400d001c0b50020614401c02c04498004031850620034041114081940c0009000c0550620003a8074090301d0f40d024680314811440f00a04200000711f010050100030400d0352130484410210114040c1c086113102a820040d1008a00070b024188010422a0040c03003801e100b230f44080c4007a86030000400d00365000703040051a0200c01c9011042c808000515070744c1c1e103031819881d90000034040a078011030310300100701644480c1c50000b031070fa01150140d03408019101186d0905480540684450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 57224248 1250 57222998 57223039
    0x80306030718020304030e010503010503030d0203060d060c090e01050d02090a0b01210e0f0706170403020709050114040b120d0c0f02100e0108011d0103030c02030c0d1103100911 78
    0x29400400100442142914a01d40030b034001e5014900c80d0301c9150b0b01000c0c61f001942d80b800f0901c11541e15400c140401d21803564140c004580c810703c024070750f40d488041a91a0401c60f0284001c4900040501d40d0501c0008440c55a203409407001322052030015a040c1d001903661580103110800261310385007294501d9010b51310101040e01460700220a45200c80c40c080010b00352000021117502c12080b030049176100c08200380c000d440c3c1c0b81d43d40300707501941c0850030b13415510007034002c6017180704501c00018403002501c40c86000c0c0010328070031040c811b0404104815545902d060034403a00841c454000a400c000130b91429024032070620168144650621902100d080f0070060f4110712945400300c42d0a9000136804030911098903009441e0340c98480350f90404103011041d000580e220b84c01030001c28011280e8109951000b02111021200c01010444404610200711101c03224001c0d0000c542c078052041030060241c641c401c00c0300c1c014075101d01010444001c2010f019080b0860701100b0320260 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 57225498 1250 57224248 57224263
    0x70f020310050123011b0b070507080a02010c1101020a0c02210303010f0302040c020703030f080c04080d020703210e1c0203030f03040501060e161103090a03080702030f030f040308030603 82
    0x207403008001d1584d5440c0281c44c41e00303030714411850b644040c40d40d0081039802008104910840c024080030008215940d800075614040c00301c20901806008443c0024018001446102c50715800271503821041c01c00900403010412000d0b040e40d00610140c44030b0b951188031500085c3e011104060401c07886010003420048500ca40f961034040017001184420040c401401102d2080d5010001003000c1c4100700c0e100c0c400c2e40002030020b69400c00b1034041c1032045041c903070043c2030300c0c011610b010b030740d81c1100e40760034000b5603110050307040b501e020070505c00030808800c0007880070700f084520481583c00c0189403084040e6282d224101d10b1003103403412400403405401e66680901100e66900d50001100c3c201d40040300c0c00c0b070381c940c00c0110214603000d04081c01ca000b240801485040345442d8103013641c0d90a038140f1a200588414082d00c0c6182e6241d0b1b4901000314055030900f6a180e03860300516003001e03564180e2402503802001007440c4280c035a0210360403203401c000115144e8440900082c02d1514 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 57226748 1250 57225498 57225523
    0xf01120b100504062304060803030c0d02090d030206100503010507090b070507050405010e0123060d0b030c091608010b0a020c010c03050705010507080f07090608070f0306120b040b0703020708070f0203 88
    0x40c000e80401da081c0409185d42104503106103c0391540d84660030441a510680550070a40d0810b00200b030541d0072900c09012070940d41c6a01500705440c000100da030703001c00100c0075001644586c0c2800720b0000d14103062070262005900a0100d46070480019202c4130725803160408841000034000c060040a120030006418018000d229550391a445001214028081d10288149400c600514048041a4902c121502400707143c1021a02e044000040c581d201505416000307802610301c1c40d0355220050380c4191181d080f208196221440c004144c404160408070600204102c80d118190700062000c14010003442c00003449001032400b26224010000002c08560a0030280201950025901c40c49030404040c9100c091381d035403a0860b44400c8500c10000816140d4000c101d200f4420722090070016210300f400b05000350350b4072000d12601108401a620405442c0a1004002c5c0864070250441443c1c43d00354140900d9403a842003c4c400e6810003040030901d0a149021510103008806503480c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 57227998 1250 57226748 57226751
    0xc03160c1a0709060f0207030f0f050a0b15060c0601030206090a030c09020403150207020a090e03040803030c180a0b0306130f0e010b09160e09040305070212010606080f01120b100504 80
    0x40c07601041c41035200c0203444100c00304000410102c1d07850312403258510700345515801000c0ba140385889403100151403a0094a0110301412158049103080040b000002d03c9a00480700c40d03d00702d01202d41c03000c0c12070708240c841c4500700802e40007400300041c0c25044d40d13011581c0075591040300000520f00b0312550320003441d440c8848400034090308141d001e40200c2c3c0c015020400c5643d0040c0c404001c134821154001e500031100002032200d840d01c1e0348095120240d02d41241d19194490b070301145550011100740300d03030718400100c080400c000c0c903400b1404103070300b07446c41135141d4205064940e2a00005111501a4500b00f002031100b41c2d06070040e050107180c2000070891044c1144243c1d01812591b580701c0d0142c3e50a0000c500c6030500c64800c043d500b942d40d60b650411084403002c004181c40c0c0600150204031081c400b20000d6654940018045c1c1c2102c00002003691a1800103454000020141840404c400004020501000e11484941e640c8801c1c52000340d0340381030000000c210150880364016 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 57229248 1250 57227998 57228023
    0x100e1b0103021b070303080109140f040309090908042301050a0e0402070f050c030f0f030901030b03030409020a0c060c090303051204060e030301080106030302010b0603060a0314280b0f0c03160c 85
    0x2010070314134180c034043d40d10861242e89070700d030010545100c031450b802c164045000190211924656568100c0e01c40c0c86e00008241d500c660400603034080c100141c44041e00003400f00180c102002480d4500c2c0c2401a0705480041c0c042d0000e059806007600c00c1c400d000255034410311a640c0e40d4121110039620007181821041141000e41d56100461855400380c440c003440440396500000304020702a0f0b0381c10040d031130401c0e4071004402801143c209280c00d031000b80300104100b0fa03a80054015032056a440105108217400c000d003d8a004103400c80602c2443c0905001081e44502144d580c0342c0500700c4041c0ca40c8a902e41b040045c440000000b100303020200010030700c81010f4114804480c000c1e8003e11445c0c0c0c65104100b1035102c180c4841e64425680002040007480e409074041203081e540040e19401c82d000600032201481081240180d00f8030101c05500700070617030200f81d40103900201c1e1005540340c0000725101a01c40a00040d50842c3c400c854110a207204065a00d15103a0101d240c4284 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 57230498 1250 57229248 57229297
    0x9091f06030506010807080f070f0903051506010207060503040510090219061806021501060804080f04140a06081b16150903030c0c080304060f02091f02100e1b010302 73
    0xc090948405000030000c60108200750307c10341c0c1250103001c03001c10b0940151102d550640c0d00750011034a460604c07404400c0000812000d2281d200c2036404044130008074a040000281410080c3e00b040052000500178403021403000113911420172504d6200181ea907500d1b00000da041c0b04920030500d0841d100010201e10f99a0250084d150b10300c00040303000000d51100070603626080301100e80c0355010108030040140511440d0000d801034003d124061510030261030494082d030040d00901547c80d0710100e148694284012001e00034866460900e8846c1894945410601d4540c2c41525a01201042c3d00106100203a0128102030340000c140611000640300003025004044094010074034010311214402d000e281070454895100918600d1555030b552200000c110604220120369403d101d04c003145e4403440c07003140d00d000000700101d0411102c44002894480c14030f81c1843c6450415041686800700003402003911074880c42300030700611044004800a0285004078150b94501004c180e01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 57231748 1250 57230498 57230501
    0x209120705040b062502010e0a0b07030206010f15110c04090b06040f020301060c03050d18080c0d0f05090103050a0f05010b031914040f050a0804080705030601091109091f0603 77
    0x1200c0c002e4a0900455000008100541c014030301e2502c13a0384105d03000e003441c2c1d844280c4110342d40e0388141800b041c03403441100031840c611201e401403514548000780500903d070b010880140148107440325210f2450030a009030710840b90481c0e0640c02c0c4484500a40c22011007444060382c60708000e482044004c0d400c0c10039280f03000080c0c0d80c5a0280c4e00d80546070784400c100d40201ca050b21955121040d06490a9a0444043d4401039000b004035554000f00808035403c0c14030b4440b500d0203030205540f10020307d01400d00b008604101d040038491010406107820303401a0540358401c03000d0034001500c0d942c12019201400c0d030089136210b8185003030004280340a80c8030207540204821901c0001a994915111046520541400c1500c01142d000038001031030305200d18011034071401c181d441c0c40f003055541c44000d821035003180466401c800c1d414807083c10100025801000b01140920800f20181500f0640340309071060217010740001c50018240605c14070302c03450b00c2c82d6002c8403280c0d46556808004c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 57232998 1250 57231748 57231763
    0x50607020307150b03071a0706050f0a0507020105250201060b0d0617070506030c030408270411030c04152c01030b09100603020919080601050901051206130303020912 73
    0x4070f00c901c03c1c2084a6008a851264000510300075001786400c500342607801a5000403411100c520b50310401040000035058080d807805091511070009544c1402503581098520090580f4110f80c90034040101c0030b899200e0b00c100101c14540036803c805105407049002d4400751704603142c960b4002405800318681c3da8003810895030408841c03c01c0700300c0000950b032242c005208180d4401002c0c400b081c481c0540000554220b44aa501c0c40e113065a0100c00c01c420090b810001031103002400a0299207003054021035114034072102d001c910303501d45070354200b0250203580150207015140d20400260140a041d980040c182d02c41b951910764105d043c4107017013282c1070a400314000703030902803070034805d051007681140908450480c00108600b4094110025041280c98580c400c26215001504020b6031000102802400000d4117a42d81400d05001c503606061344001d0154003080a4400c1c51180030030499040407040700300d05d00809075130a084000e03025070594294010207840300d15114410004813103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 57234248 1250 57232998 57233003
    0x7050312030c03010501200a0309091803170402030c030a061b030605010c0219050a090b030106120c120c05090705030f090f0c060904060f030503030114060430050607020307 76
    0x114861030003410004918002074400c0c0ca80110300b40018840385d8001d00140a00302003c3c00c0c2c0d81041c0031412601480c001000b90141e012500000c02486044428060210380c9454400c240300c040d22503580090454a404070200c0007046480040b03402c640d800c1c001c41040707450040441e0a6000c050030140000c050440300e40b481000a6680380c0d8116000713008042c2122016150147daa01050b003d104d0807903001c030745c00d40c09440c102c0008242c96494182c4074000d005421000540402080d0605003100e029402c00504800d0b40d84880000455980d05202510310020343c562441c0c646150003c0c0341a0a0b41101d6400300c3e440d81000600c56014029500c00d07483d20401d41c010b40c8600411984414a0a4141c0360540001d0700848944c00d05000601b1100c8021b08000b03801070380c52403c05045052608119a00d81002004018075120074111440b00c0800702c03034441c5414505058019404241c0b0794100202e41d00c00002c24540322100011607956802000b61440c614040304000c0d103d50200c0c004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 57235498 1250 57234248 57234253
    0x91f120e0a0201080103032006100611030403021f030f0c0302070618080a0e0111010c0306060807030506032a090f011707030b010b130906030308070806031615031d070503 75
    0x3a40c80c004000a0000c60180c060311025856400c6850407179102480089046140390440480e11049208108042c401c00307050103a420010300f0b000c0028141c00800180349580d40c4280420300150780c4041c1d503101503201c0c00450380c1501011100c103501504264112048507861308a01807013080c0c060f001000c140b40724000070442801d01490303031660454072000185c0340304810301a8280807805025a60318182050411401d40c0c9107501407942513a03890188640000d0b00c07110104807607a005005d50703820985504081c0110700d04180425138424200d69452403c882c0c00000c05a980d0403a2280c03182008041c054003410b1070181d0003070344440303030038030a40e000c1c41907a01003001d145030042410700546c0e500502c100500c1c3d1030116030344525000021641d14000d10380c3e8002581120754800c060046200781c41d550300e24503001c3c501404546000f00b50901981000f07000403800e41c90054181d041d2105011025064081d000c8110010007840f4100003e03c900070401a1000400003110340444104504 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 57236748 1250 57235498 57235511
    0xe120115031707051e0705060309010c0219080d15050d0506070207091427060a0c0311090d0f0303180f0204050705070b0408030c130620060601020a0305091f12 70
    0x14404083c4500701001c1d205801c0201c41c1c100004000c81c0d01681d11682e05c04a4011a89400026480754000d590062090b9901e40b403964280d601800030029a8550041c005000750703440e200c0e0000e601ca05150940c0095541c1821103000105c080c000b030160002502d912048070041c41e01642e182401e0f0b070303508094460341d4400074400c4e003c0d0159454540074242000c1840d201c0640714481003545c100c0031040040d0524801c00d1015041103031502c10340c00c0100101d15001002070203011220600010540b6802c1040012040d844031015100402da001d0394103482000c00d42811401440110750800352610503003001d00038014802d10001115000302e40070407032070321404070540d80c62150180c010001c030301d00f4001401040705070014660081c540c1203c2850709254100302410440030360000000300f1700f45038126285500310312010031001d98210013803600c0e00b80000041e503101207101d070050800000280907605915010400c0100302903850018140654100c4040c101e07203011600c42d4003491034000e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 57237998 1250 57236748 57236783
    0xb0a0314010e010f03060b0f04140103120516080d090206040b041d0906060913050102121e07080604090c030611090111030304030801050d030c050607110709050114010e12011503 78
    0x14020b43c122060054024900792845e0b450701e000d082025034507039003d4041503030040d80e5115406142c0c9a80c0386134410b9240c640c11031400c901803050b001240810010284900205202c1d505408024190030803619616018520200c4c4050034040ca00207401c90004a00004c030070100c540035006075068140c4041140011042448a2032811034129400b0340c00760780484d40a060110f903603500525410011000c0035900d40700c15003a030303001d518900e0b21002d81404002c0c000507502c40c8a800e0758140c90075090f0b2170806160080c84984080c203407902c01c076943e400f07000812144000c92801550711200c18418000e040070050200c2d04002d1001c1d003c900c00410035100c201d0003004032071082d507040d180d62030540d0800090042050a1120440900004400ba80041242004030340e00c2540b450380e994100147d00707a8980e0410720b841c0c0c0103084d441e05010040c0000000031003014021442031030401c1d6003800100001e9081da103a442a80c07036a500c1c210040d80c00d100d500c080035080c0d0b801101c4d030b08401d43c0c114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 57239248 1250 57237998 57238019
    0x80c040510050402070215070b15030307110915040614091308040e06040902060c0c040f0911090402060712020d02150402060307030923010207050f0a08070311070b0a031401 76
    0x3140d01801258006805010a01d4682d01425051b4009400b2541c100020f1460f418203500c8032606544401002c0100205912005941d9020000560186080a1442d5161403000c1643c1c04414800e40d641400103c001e1903401c2c0b41d0403140c01c002d00600156139201c1221207002c100c45036240c0200d2100d000281300c405a896000302ca55805020b09142a240c40901c0303204000180c03129600c2500c6e034500b840944c0e43c4002401080445c840906a0444264100700840f450010b00140041c1414031410106942d80c03003001f5200e800740c0b130081c1c0c107689600c0081d030184a02c400040000e07225800008660f6400900c00c21104034035001ca48004642d010459000403003210001d612180800000b8500c600c241c2000c210300c0d00c0340620b62440300c02600c806c0b03600b600c0c54000090351781d40400e1541c280f040030801c040c07a0200c0c1c04d003c1c14004956407500e040c1031056090140030702019849007401c5010400400009101c503107492500c8564a010040c0900044005280c00c071101c1000801e003494003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 57240498 1250 57239248 57239251
    0xb01031101020d050a080a02090402070b070314150607110301230f160f020a140c040510030c0b03190603080903010f0b01020d0f020a29010602010b06030f06030a05070f080c0405 78
    0x65161340e400c00c05030f403804488509005124140880d02803107400c5080c1c5440c005460075034841c48490505250069004040390000c0d560294000362000034000e000c5c1902d80b5602d0640c0061b50560394601ea14100301100c1d0381d240c920319406600c1d04150898400c008404660303000100c00b0392000d682c50700c100700b245441050311850048003816580340140d5001c2c0c4a034040001560056548500c415125a02c0c07011100082c008240c00204044c022807a0a2103800c1e8010610304000301c50600716214024045554007503546aa40c000010811007a52030030b80c11545404070000340040e81d100d117040c11558020001a601940c2051080c1d41548201e010b50b40b02d282d4107a00070585021300d441c1c00c80d100440c0400050030750059518402c04205403901100c02c1309020311556003003201f1000032300c1010328142d20103401c6903d0400070202503039502040300d40001840003000a561201e500286c240b00109400800a10400304002a03050003903012108072000700d010b44407840100d40602056500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 57241748 1250 57240498 57240523
    0x909030306120a02011725020c030706020106120204052509030b06090f0601050901090b04090b01090b0301030b040b0a060905040b22020105040302040c030b060711031002120f070302160b0103110102 87
    0x14030600d9081034442e424420341d204066909a00781142c800000c0b01f0340b402d0135030080300140c0008425a945013810001c40006208a10003006401d00e0010101d1500699100091043c0d850f00040f601401c0c0030640701d0b003d000f8042c1e610050030070301c40014003462110320045a450442078002422803130402c118030300c10000001701c4045a941c4d007004681541c8000d0059040c0035901c480880d0711401b19028002815010348002460b41c3e485001400100060f404403000c03400800040c00019010201142c01592201c075505684d12880020b0f409040a900300c40603031840c080c100010b1101c1407803524064407051091503046655003000b00e00c00540e14001034045a01000200010b0038244c0c0244081c8846140000d01d90044100180c00341c0e202510036240d401c1c0c8044007101903c1c0a224001c00360940b001e0452034401403802009100a004021380404103685000444690180d01190844d10881120040c1c3c16001d2511810800080c00b06460003083c43c0c680c10055400050140d40104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 57242998 1250 57241748 57241757
    0x20f0105030f0604420e010609060f0e04050a1a0307050a0e1f06020d0801090209010801050415031b03050606033c100603060b040c0504230909030306120a0201 70
    0x42c3d520302808050f1040d0711144104881d00800c00d141550081d140812a09855204080c00d1440c0301e843c2d13001d08200c1c4c0103149081848801040410740210381c50046540504009084040080c0c0c16070300e201100c10429001070818040140c2041198042d0101028850725005402004402e146c0e44030254000c0c143c100807031030000c0c048819a0f0408982c410818141c82c2d1809000c03141d0081c440e41c1c0e03603010b18050303030040d01c43d80c100c503070400c40141c00f41444103c214108200d55000074500001840380c076000c0c0d03584600c0b42c0c4030350400003d180d01a6401982c00d2403000d20071074003640020190b2000782d034240140d20100324149000f00f10010320211041002d4202d1000c00b50342c02e1218814500f50104c04141490b0840d0b008042c8140c0c99034642d901d100246044c81c0d420f1a806a0b09500d051610442c504043d45200c95001003c1d10142c030600300350b040c040c816462600e02c4405424100e1075101c4c05200801401460001c02180300f00d50a8402181200e0007801b0305981c0c04102100a0105 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 57244248 1250 57242998 57243001
    0x6030f01110f0d0902030d02030c1018020d0203030c010501180b0f0a053003030f150d12030608060406020a021216110114030403020a0c0b040b030115030617010603020f0105030f 78
    0x15107441c0b02400740050100c1e00052001c1031580020310340f00c019040700000d41c00114242014141c140041088000400cbc0103000d80604d10000c410803040d80390000744101e0407007502c102591820001e0320b80205480c0d0003046196150140540c407012030400070f001c02070030940012090304040000403036409019000e200030509200c03c010759a092600e506408842144e00c200620054401040d03c1e002140007869803420140b29040700d80d07000810b44a5640d035400d4030185284ca0741d507024401d07240c00001d5030120f110314440072005007915030700ca41494031849081c00300b40240784d40200a041d42030b800715110301d00d0b0450180070f02d025003150500d44005c02035050300440c08060740380100420503d0288112001c8401945031508140d600360010b0340050180000c00448001035000f501302d80b031500d07090070718040c4104914801400703a00d28051000060b84e05160003038001c90083c00f48040d40101490441442500808180c4020386c411004545841c280c1d50241080f40c4c012085425090b40a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 57245498 1250 57244248 57244267
    0xb06010c0b0a0506180c070b1503030702120304090c050c150702120a05120a020304020307090b10030b0a0506070b0f070306060509010e0d020901090c03061d010e040804030b070806030f0111 83
    0x1020010007050b005181c1045820721104101e024030b00c5008120001a00c2d0b080234186500030580c01010100040340181c007403501c80d0340020942d03103015030440b040580c09110185160643c002c2d580403001039400c4c24003018200b5000409800d401b851141196044003801da4201d22200059034200050780008914a91460080c4000c04c202c02507420840c0c034001c40b41081005880040f40c6e001080365011050104504d01408140010b01c0c60075001e20154071100c0009403d04040d2046000740350b51a00c04031070a443d000c401d600103200081542d078403213029003400b20f500c0c03804403180003c2c0148003001a004501911a0b403050f107440e40d4909040c80c006800540700310b0f2602d040e0036804842036002c54010382d202c0d240b03240a4402c540011030252040070b000b0f030665100360403181c900f404074840407149102e0000c555046404030181402c0c140c441c0e04011802d0f11aa400250109840034200907100750080700160041e402a0201e80d881c15a01c1462400ca031040d4100803050304003048020301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 57246748 1250 57245498 57245501
    0x80d0f030e061003030503100f1202041a0303030106050c1606050c070f1203081801050103060606020d02150411130e01091712180c030a050a030305100803030103060203040f0203060709030b06010c0b0a 88
    0x511250300c23800035034280d0701d030302400e01c000d40160b000703135a110f08100c100411402d080c05106a400041c420080c400c0809800007910790205009140c00c014011402e007400d220100001c0d0b07186d946011f00040095210f2070b0051456120060242c2c843c4280d01001405201810b0b00358200c032108072400c0d08070310503580c1c1201d100c3da000e045010800300c801c540111307100080c8107003070003075109600000d480381c58546c0c003a0911000904c900c080d03401c9204030140f210b0440c4041540a5404180c1018a5003402e0000e010203181642d2203d60614005c40403e550300f055010303081241c05a41d281d141e28406103802c0507148a0b66100602e0701002c6c8002c19944c000f0a84901600310410f005da50345045c000000c01e15102400303100359008c0e404a5100c800b490307098400e0070703003141e04016444a80da044c420307583e5903413106100080000c1d600000040c240541000d08504040e0300800751811810070000040076102140019601002400081003071980074148003402c00d075000640d0a240e58a4a21080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 57247998 1250 57246748 57246751
    0xd060b0403030e06031915090f110306060c0f120904110702010c0b2d0f01050301020a050a180302040e010504050709021306031a040213080c041505060310080d0f030e061003030503 79
    0x14205125221b00080b810818010080224882010340b0700e0689004a5141038581e460f0b510440d00f850241e002c41102c84070000c8950000d0241c8895540750780c864601441c0500083c00040c9a001c0c001a050111a40e40024a0102411281408070000c440b42c1a0860700c580705c0002e0100c0d249061000004d40ca80040640c403110580c600c5107070890340301003080c1c00b0b0040840040c801184038204103181d0004400107000d01010f138021810100f854001401302e105848c83c071418042c160110034003546450508102855020344184110102503956a01910b420764088413140a407040100c3c030b4103100d01c2902d401030341c61f8003800314041c641001a00246011200412555003440c10030041d511580000e00101000c03140d00c0d901c513440d0848850500d410114000d10642c00d15800144142d00a0200706c1590800c40c1c0700e90756900c0d4810303082508681c0f50711421030307409104d55100080707401c2800d400c008040c07901d06101c0480801a50303900c030801202ca6000d1000b041c4020b1000c41c0c41a80070710b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 57249248 1250 57247998 57248011
    0x1b05070306060620010501030305030c030a020f040306090b13020f040b010908011401050117010605070602090303070c0305280b040b0612012a0206070206070f030603080304080d060b0403030e0603 86
    0x6458458407034072018151071454010801041540051200941003030b194205404001d000070070a03075045613401011480054010b551506000c40480e01e8150143c1c1119014a51618000c0e0b94a50703c2c40c11101405c18018241c0c0c0303200c894000030365071608040c2d0750240c0766401041d05110502c0ca904200092140030310b4541048089030f40482d142d0000d02c550450300b50783e0003003102698900800186402401100c284240b2103030001000019004800c5d0f541040c1d000c3c40158866600b100864558080d40e44060105101042c000091100c0414400d240ea0303003006290006801481508014422031800200541c11820018000c034800c4c80340d170354220300024036444014160410303850075507804815020850101c0c88030300410108010f40903400c2c0c10613001424042c94102000ba494120003450001403000200c20071100c94440e500c1400615400b00c001d40d140d09080c1800800d83d003000d0f001100d00d0717240c00d10108202d01040c00fa01c0032294155240102400190103002c4650000b4010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 57250498 1250 57249248 57249253
    0x209030c130905100f050108120a030c0309080d05040302060105011107050f0d08040f0501020c100509010e0112020703090f170601060f030b0603010602030a020c0901120f050703050304080d020d030c1b05 89
    0x900004800703101140c13070402111801314200c01000900422180180d00240380c66010902000307440040505075040e102e06030030001603100d1089400c0d809081d040d807005000c44c000042480001c449640302c680030364045c1c0c1c202d0b01240e8132000156034000124040e44011780c40603204102c607150511901840743c80142030440070101e10b0b50340902a0300581c02242e41880420b506019559040044010802d4111000ba9511800410181440c0309114000b410001305040391960750340102c144602100c0c080108550350052402c004004000900600e10740c2240042c0019003001c111460005e4a000c140c0079000c0c6034a0403c0607108001000c000102b4151180c80035139460f03486002460003000150044c60b514001d69a00a013400100e4054620030b000741801813005044400803c80d955038401003c05150260703040c09858034455610043c007502c00040cac08100c03d100400c4091000c1d00300e808a4034040c1042d20b040e0261403c050b900800074403410205442c442c02d506442e600a80074009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 57251748 1250 57250498 57250511
    0x108030906130807030311100203010501090504020304061407050a0e0f03030301060f020c06070804141e01050a050c0f0c0a060305040308060411090901080102040f090b03060a05090f06100504050106030209030c13 93
    0x25181041111740c0140c02143e14600c9880d82640103000c1518854103c0c0d40840c07866040ca030028000395410702903180500d602000050030411203070b0054038242d1080040c03c44034070340054000d100394080a014000a0100200e246090400b881401c0311010020090b40c1107a0030188200e62000d0440300d00c40c114411518050455121074009004441c080c2180c10b58a6040202a146400e80074581074014280540b40555000b42c3d070129000b00c500901e040399032400c00d80e20485160160100c101c1b03e134041c011103208010000581d01c054944265403240f1480e40d142403c4d801c96804a074040c0104003000002209481c02e60f204a000c032651071901d0341000300000c0814100c0809030420381c0183c1d4001005d01100c00d0a5040780002d010a0800f0b22404164202080c1c03104006413801c200a5190380c08076804030010300c0400b01409018046611301e14024084c1084802c032845014060b524003000414074521a00888010505c0a1b00520f621a20201803249001c1c00c09000e00b9059950340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 57252998 1250 57251748 57251759
    0x2d03080f0a1b080d060602060403020a030807091701050124020d0c080d090605010e01120203070b0d020421030e04050105030a030c050106090f15050607050a0b1e010303050c06010e010803090613 85
    0x2c0c45400e0710350103110010b844e010307800041e80444170141c1008042d9407142080000080d03001803004c125551605c0c18264545a0603010350b40c0c0100e80d0826243c01c512012004850041540407038103c0e0074031103901014800368030f1000d045815001110740140c1001e07100d90280750050b140204114071800e021450300d81b0074282c0c00115140281d04994160325600100880c804144015000d4081c40f07441c0c40004000d640002ea03520311741d105000700300b0740204601c913504940e07030306503801032140050385000c10801000743d1004010818084003c18820080380056040611503103041c1c0f031001d401440c90305c0c51510180c03040b080d0040300310340940d201d5102007002410303400307510604252442c1c04a02504000c146082c6454079800850294605014130360100704001540d6000c03d400c030030f1102c850348a204086544020303083c41c2c104050103810000007010b5000c00100744801d44901030310216606d03448420b0240c0020b06ca510f920b031303005110824442c03800d10002d0424a02d02c0c40400c2009582d107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 57254248 1250 57252998 57253037
    0x9010312120c0302030f010f08101d07080d031103010e01090504020316060201091a09030412050309100c020f0306010f06030c030605100e18070804030f03020909012d03080f0a 77
    0x2e5200002c0d8001c070900800f5269541d010380908050145070074801d003010300c0c16a40b10140d06200c058152a0f100d0b5a421000240d2810900700c4000261000c5980342d03d195551038011100090000345054071840384980c441d402d5034144c0702182040c20417a460030702d00a01a08000d00180da00d402200d02a008030344016030b2050040c90300d5000401d05440360300384405440c0b000944055003030200c0d4104010240084125030a4803c3d056401da001443c500f06076155000340c14140340c22800c1016080c040320740110300140c0c07252007294604484400300e03045c90344074002841001c4503100390103400d008a901075008402ca044480c030300000e0442d03076503000a0a0084103111640407038500c03141001203050403800700034403286002d40c201107400d004100510000300204058200100810580a40d5200340c040f5203c2050050015405e56140c10261040990000703805500b04000c60441040c0f0211901740412030760041401030500200710745440340c0754080d001d8001042840030580038201d991 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 57255498 1250 57254248 57254261
    0x1804020316090f0f0908040303111501030602130801090f060b011403010b09100503070905091e090609011d0a02130204030804030803070e120d0c1407080312010b04050901031212 78
    0x802d2408100301c442d031080f100032181440000c150040c01d045e00b14020078207120844003143c0d41031610b06030028001802d103041424950f82400b91000c508000010301815130050115075009281c807000d5156030700030003030803103401060050021107012941404140c060f888071507a180103040556114882e400075881c564400d803c0b501b0030850100c2c1c4002282420030724003094003001d00340640f46060412020b441d43d0424850709106170703540d81c00680d0303290115600e4101110002802d051b1800c0c02c400c41e941f95442100c0982c081d41c40e09102c0d0607444282c01c0c2c40300b152000030004e045282c0d0503800b407042030714207001d448880325020440000012080e0b4002e0008500801c00c982e01c908001c607004206190403102244035840860354400c455a001c2511060947d80381011140c58600c0d24041072001c800700030071401800388440004140c02c002c402408801c816100d208075981e29600a1040d44c0a64014035400410380300051000510b0140d9510758445942800490810800c0064054520 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 57256748 1250 57255498 57255509
    0xc040e070315020301030b0a05130618170f0405060723062409010603020d060e1501230703120e010207240501050603060609011b03020f07060e1804020316 68
    0x11103401041881038202e00d080880c14484420362955240d6100e003d8a2200a80030b030b02e20f203a840000c01c4a10140422011003150302840c240a024854413004100701207181041d105900c80d02d901d00c1429014004485010208110326030602e8104828030030550001c003400c44030000d102d1071102641c5854072891183c81e106000811161400d55200051045102e07648808040f14804083c26590f41740041415220981380050b01d400501c2c034510701a0005511a1088100030403d01c22801c8050070820890b1800380ca0702c1c030a4445002d0202c0c4415501980c04c6000c81c2e0502090000074401c50074000d09600c00940850a0400144901d089900080d411900d00b0380c0345010098100c4100b000712000640300f402006991725000c08241c1c0f500c80200a01c1c0b0510f40003418040c0c60303008844400c4103020804098220303200524029594210101e18100f40d8480c05800240307070b92080c40340048003100504031400ca480c6c40100100f8054005e00220303811700680660080703400482034082e00421 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 57257998 1250 57256748 57256753
    0x40306020309031306020109030207150c061406010e180c0a050f130306060e060a090b0d1e1428060204120f0b091605090903041206090605220b06030c040e 68
    0x803502e42942c00000301540105c00b0759052154010110b42c01043c07040803102941800804940f0302c0104594000c00d03440000c2941d49422218440c2c140313140312191040c80c007a243c030f104c041c004508001001d0709202c44075008a00b50800150050441e601401c0c0c460640d040c400c0c1051040700c007030f014640040700a01c0b82088074041c1001800128010000101120300d54024142884004104118014080c20611603210100100c103a1100b4004211030b036040341030100d4001c048000d00f03031f8084104406940d0311022121071000c0c24408280c3d0544610407911603800003001c0c440c090741e0000489070956480d5400d000005a480503015401c003100c0c829880c06040e0840d9290040d50b669000e0311601c016803061002215608407414408251041158200c2840c1d41e5461102d15602c601d0304a4054520041140d038104081a0000c80c2c07194819601840203941d1100c07a290f07600208220304103074032490301e940001b050340001c500da081100507042e2400034a810f0045030503111082c20101480c0e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 57259248 1250 57257998 57258007
    0x601090515040614042c21090105041206090204090b0702010e03090a0308070c03020607080706060605090f06130e0126030405010507030f02010b0d06051510050a1404030602030903 79
    0x414200c58007410054040320100905410000c03083c807090510038041780281d03601d802440740802184a0041d40d100e0886a000d0100100c1e441e05803a844810202507284403400f01440040e180c09050b900c500c041a991503007010b1802c010710086020661040e150b40d6a02c2400b840540c50f5070054609090040c003000c0010304114200a00312007200261608542041c007800e0071690b21003900c5022650000e03074076925030303106062405910800d9407009510110000f03010041180300c2c0060301034240030b0002041040d68848083d00d59206041e8459031000c1040d85103480c41c5482409441d401b030903640b101b081700c1c0d1149111001e085081c0c00103480b02200c86101c3c580422444810100d588d0f58002a6050130b01c3c150001e400c41c003030500000d00780701040c40e81040c054400d5001b2070010600520701415880c0c203040060003020300b924140340010480103000c000e42880c2812030401e1100d40c1d078244c42d08420f0403084440501c121458060381c4c0d01008008003040c1c2e90700285000c0c4804002440d42c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 57260498 1250 57259248 57259261
    0x902070b06030604050c010507020411030702010501030c08150609040501091208160309050a0303020a021005010b09040b0303122202041103060f0d12050f1c05010f0f050d06110c06010905 82
    0x51001000c0c18807940c0143e0800c0b00043c07001c03400400c164000c2c00c0c05519001144001809002c070210a00d900c91008400c00824660540180c2d040380c0c05943d030040059158075034191074032801089036400030310030800701e0690b0400c01201e5034858007440001405c808a50350320348000500c4a81080060180418404000ca00ba020b10310001418103007040900b5555031100c2d201c011828001e4145507000c14410a120b00900c408100c1d003030000000c015035a1521080a102d400100b4094084c03440c0185407151070170000308640000001c0c2034a650316a81f0390190341d6032203090001e40da500c07451203520680107071a9402002c261110100100340c407494800c00384201c02e50308130301d60741c03260084d1207900c00802d1842e02c0114024150b440c0c01d6640b040240418040c0744505200b002000301d44958084859003690700071816245540741c103442c9d4a960780c0c80d009103d07540e03010746640300b0503410143d000200d2130b0b400b441028006403101030500400395121401c2ca1002d9002411150310b034410000b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 57261748 1250 57260498 57260513
    0x2030f01140f091b0408070609080106140906100509030114090c09010518040c03020d06090b09010507020d080a0b0d0c0305010c1e030c02070308190212090f10120204090207 76
    0x3807040c26520642c01c00088800070704050f0002d0550300c50502c3c40241c80c514043d0f07480482c0c0103042c03050112001030f6607030743c402408d4016a10810015500e04000420391103050150b44003801d0004010310718680707817503042020f011035020b00c11060003000c002002c1180c900b80a01c2c0a030041450050040b03240240741e99041c5070001806038841c050040c01444280d450742005040d640c80d80d06a0705007a1394901e03180d011010103401c0650301242540318042004165040580d840b84940494503007501c40d400390600f038800c01d40300c07003026070404001a50400d100b080b00c1c0c1d50020000e6008515018900040740741008684819078524000240030300620800340550040200686881c0354118580503800a4500280000008241d110942e841d2114400c01c4030308003641d0003190b07030f0360395044e4504103107a88070351221114058054920514407080542003911035868026051240e802c0950040000103900c41c21a14240240b804c42e814011032148090000703441400401640c03400e05041840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 57262998 1250 57261748 57261779
    0x303110a0203120d020d0504060509010c0306030b010510050d0509210703080105060c0c1f021501030c1e0801020a1d04020711060d090203160314060708270102030f01 73
    0x903948440a020016100001c6612420ba440c8030056200c0302c042150002900c5955107a003840380c00c04d8141301c12700c81d40d540701c9405040904001c00c00381c01e40c241d09a00f0364002e4400604883d1501c001040141084240304120030418039042c1d18000c002891b403011a0010740d4035606e1507020601c0f00c0e80450b2410340150782203100312081d9040001c07541c0e00074805101409954020030340070a103a01c01c00c004101580040310020034001c0c054005400d516510b010101c8118014402e11001d14003405044130b6243c146c0b904400c100c40e1050600131700d04218020038180340383c00f01c404c1d040007821040030700c00381c054003009586036006a060740c4e1403841c0c00da042c40ea201c2e10039403040180030300203104511401400c03001030740d0345034590f000302074040011b00d8101c8011b501406001c002045042d1108881e0013500d100d00c080d002c03181d00007150643e941500300c400340003140d616008204101500003420440c031502c0c6100e040e41c18241d150607426604262060390142d0111001441902e0540c1540c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 57264248 1250 57262998 57263027
    0x30c02070b090402090a1d090601151202070218010b040303090f121104150f0e010801020a080a0b03031e0904050c0910030b0d0c030807030e030c0f0f2202040303 71
    0x1040e145080031500e90061064440051003568000b4191000303803101c004071700c001d05403007600c29a03814480d81d00c0400060110707280b8172540192000860786003103029800d94080c0341a85c840141c1c4901000c402c000307502c032640a81e8058030088030200c03009005c0c11030700e000c0d107039882c80103444500c2c41c6405010900d2031307000745131100b02510040c422210000c0a0300700c10b40d00001001c074007014010118008020440080d9164010004003088000c42007824030121a564800c42140d6a80d908015080f4003c0c250f03000700081e02c0030082500c03d0601c0d003200e89101c1004054070b1601d20001583c40d0422085030418000c5280403030ba1070b00e10b180500c5269440140d45040b42d2a1400400028090b8140c0036190820306039541c030105400e490311004100c0d85c541c000300c020210b54403402c02109035080190100c00142e1145070b4084582008a052024460060690b007246c200d8042000466107112402c5034010003452113800b880411010018000002d003540140d88034211b080040100000c1c0990 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 57265498 1250 57264248 57264253
    0x408070506090c060f0a0306240806040513080a140307080403110a080301061209050109050606150c15091006060f020c090c160302070308030702070906080a030f030506030a0501090f03030c02 84
    0x101c208945130740f81201d80b503242980c00c3e5607840a81c0d64040d40189055000b14240043c588503c001e2808101028410f54220b5250046582d0b58141040305a810441c0ca0140c00450b55100794002840607018203540003850900350302850b5403101d1000c80d9001100c10a0001c0e0041c4180410305820240c14180001800302410030801c071a15018000d00c0103100e04001c03c05000304120b131b0740169600a8417a01d0b400b00003070048030004d00b800355840d0015a4030302c5c85200503061a01c04046440100c8034040c56080c05000000e4901c1441010180020555602400381d00d20813440702402c8c2c4642c60140800c1e455004c031103145644004d242100e41d40c44035004025110603c20f512500905540541d06a40c06074082e840032490b00724144007043d800100034076408014003454940108143c4150350b46c19104000041c0c0e11302d80707607542d840c2141024004c1841c1c42030848103103100ba00000d604c850060125160031a032603895608541908400342c0340440d08500f10400c040e41809840f100070351a100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 57266748 1250 57265498 57265513
    0x3060606020f1506040905030d05090607110c04090f020d0b1005010c0309090905160806160c080306011d06040602010e0114040b13061d010b0f0a0f05010311040e040807050609 77
    0x10215a03ca07803451103410f0b65806003000440c01c5d50f40d40c1055584640c04415651504045910758001c1d08047c0c40c4d421241c000c40c0700040795580324124449002980078000d00148208000b8080101443ca0090780c103800100c0700140541c6411240c940078910490b5140118540f0707405503503580015800580c10401500e00001c04240c0c046120425a2011940011902c80500d0051302d4240d4100401200c00c18400c0c000400200200d4550321a403803090095450000505046900600c171181c0209201020f101240c00707944640049100780c00820000c4000c0383e001c50015140d900140d1000c00180c0d1100c40f0841e00386402c0c002c0202001c2444108549410f2540c0d9232055107a0080c400004900c892424400f408510b42080304040b2504485140c80313207014403041c1c080c0512070080c2d4050900f0f584a041d160030a201c0400407101c8482d81d240c02d0754240710044022381460030048889500502010072591f42119110b4021072007690003e641d400946070072400c002005010034840d0b000101c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 57267998 1250 57266748 57266773
    0x14160b0c0f09130905060403050705062d06010e0a0f0911040f03030809010207020414070e03060709170309060c060118020304152414040f11041a0f0d060306060602 72
    0x19121058403c0720071021072944058044018010030101800c284949001e07c001e16400c14000d04082c1e02031001d407291986e4503072111060404580180c400800e132000070303130062600d0001c0c15800000516040902d0200075002540e9a501c0d90031030b01c19002414420003021005116200002c41307400c50300e5042915041c00717070030a03510030320002e420711010740001145100b00b94101c070420b550042081180002da12114001d40c50210f83c9140400c2c0d016403d032001e1300d00091194403903682661101e07a01400c042c21040c1c44507600b200141c5a00c000e01171000300d0f56450000d4040788045c10028038082d03142c8200f00c0f440c3e100a1800416482c81000ad020108002500f050341c21450b1010101e22050b03032038034140c00103010007d001c220f80110b000100320007a1980000000c24411201445816902010b102c111100032610b12030101041004010901002407444901d100c44401c081c20604000000040ea40c00500c64618030390769400e0510030002244240380151010f440100015561030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 57269248 1250 57267998 57268027
    0x90203030a030504031701030b04020901050d050a0201110708010501091a1002070b0f19110c0102030c060114010306080303070302040306062102040504060e01110904060611060a050714160b0c 84
    0x140d0074101034032440001c0a041c001c02d112922040c0c8051040401d60b500d00f004c01080c1403d8404030710600c2404000206841e00301e205105143c1c0140c041e10300702000758015112404070002407810707402650400a030302c803828810a8020202a0000309a801c12510000ba00071020315100c0c1c810107000b1802d10340658001008802d80310350702041c40d42c3c0c0310104c004e5030084c0282440c000a2850007454519074a0b403103000031882580302c1c41200c1428144000581c2c4078080c00e500b04c600e580c00300004100700400c03010512100a011704002902d151100301d0705003140c1c02220481c0100b90002002c00030420140b040c0002008000240100458041d16020203040c5441c00a40300300d4641022a081c0700c801c1d030106100b010281e0007006110b8a1b050aa004c0c3e8014041d018400c914004002070290f0064030410300010309031012f40040c2d501c48400358003c003000f0f01803c1c00c000306100140e0b4250750a6008081c04503110100c03255148861a12020307400d002040603020076418001c280242e8400e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 57270498 1250 57269248 57269257
    0x606101d03100e100b0105090d03120f02030103030c0c05030601060905011d060313020901120209041202030d15170c0102030405060706180b0603160b0d0f0e0d050a1209020303 77
    0x40390a80c9109004920019181c4454a034964a030946082d5080d8100000001d020403801401c140078042c0a25410040d00c05d8021242075030303001840c41c1003c2c0c0c0003a22449400034a0194200006188400803021400300e0300709070000c50203c0c1c1e07810984000e108071041101c0050500f1001070100d0740c1001c3d1300401e0f40403613105103818019071442001200c0810440c20519031400b40c500c54482c5017603a00941d8003072100006038090702a2000100f00100521a1034000d40c3d000340a0a0325a15940d41c1d0346e021095807081c54085000501c08200d03068002d01070303c0d22a01c50390b00d1220f03066003804880300c0d051003010f0040f803507644140080003540e40c000c010741d8200d42c01200d130b01d502d601160501034083c00c03450400d0380181c005401c800040007a11100c09000700801d5040b00c0c42c5400441800e100101c1601505904003000e00000c25900f8443d04144414102d50304041395040703030b80d000c2518042c00c1c408140081000421240540c5901114412055084c001c0a01400c06c40742c011079100d118 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 57271748 1250 57270498 57270527
    0x70c0f061d0604140f030a0c1412060417040f030b0a0c02030c07060f14030f040501060e01120809040e010c02060702061506070b10050d0602090a0609031a151503040203060610 77
    0x19031308054015070311071714080e1402102030182d44030503203203242000c0100107600400c00320f01421200d141050801c04403004444010740014030340780c3c460351500e4040f050351003181803184100f0031001c2400c06a0340f0f90400150b10521080c007850811000310002c0d0756011039034030219070050220190700b800016081044601a0800032001009100c040f5011003c024117691091000000d201e000a01d080400e881640100000c104103500ea119941d03c0150070711940104030341c0c0f00038400124070740800401c01003400400c0042d0100b005003007242540c454001c1c1c000580c0000d400c00c2002e580501c0b03002d501410394407003845c0c110020000122a40a07200c8003500f041d80010000381c54030b000c80c20401c05407100038611031900d0200d14185020754040b0314400d001d60a080b100142c914083c040420659511102d5024200229042107260b44402441c04061150302214102c454440e0808003003074200c00511159a8901801410300d0990003818450055401180e003000c001c2c3e01c221880500312 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 57272998 1250 57271748 57271769
    0xc120406020d09050601050a0f08100f0902040501030f060b0907020322030c0305061006051903020a090504020a03060f0b040e070f1119111e1203070c0f061d0604 71
    0x211142440c40003805a01e8606642602c0e20b0910814880c0010f14141260750840c3c3c2c80c3d00c03050f01d03544408070742440c522070f10a07203a000c142d0041c5606640e03085086408020350380014402541d80004040e100280c2c03055924081c2100e2a4050201500900300300182c26a040b03103107410301801c000d41d41e00c2090b082d1248807080d9540c41c02d80d0441d05100d00000e40d00a0f00700340340c003034070390501c641c03515010340f101813480c4950880003c5060040c0c040c0d0355440d01c80300345513080300003030f80090b00654004055101000003403140440e02e0341d580c1c4060150b07200d03603a60010341c00c0d0030501c0c2c424046140b50040b44400a050100b00070340d500101000d6031107602c628024407150894401600d0910001c016407219008250b00701141e5006c0c8016090264080c4000c441caa107810703c14403490440798445482c2c0720403031440f00001c6040c5201042680290441141c1c038000c80d03901c1e00311921001d0740040b0900d00c81000100801580400c0c0e440342000c030b012074007070f907802c141e40016000d2141e4854010b40c40d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 57274248 1250 57272998 57273001
    0xb100f03150e160f0905010e060d02070c0902090a05030f0309041d010e242505041e030b010f0b090d03050405040203150405090a0b0414120a020102030402010806090c12 74
    0x1d2103481c080701d0080800e48248102401c100242e00124000340c540e5a00194080350741010061117200380208a4034113840c3e040b030190000c0184051644100d400413a001d800b001003000081c0c1180c01100200041403005840391031080c101700242c2102c0d40320343d02c6a44160004c0c06c000d41c0120072a545001c046400007070016801d030041c0d03511204440c26010310352a0540c2050301c00c0b00800d0b1000e900d81c2081500d10401011b4045040700300c8146c3d446c0030880c0750746154881d401e0b00e0700210500b10740c2604107036040c41c0d51140584000320142460340007003840076104004000180c01d0090140c40f8543c500720710f050804c100142e06e4010507444900c205030300e40c0004117050264040301c1c094600640150350320300c0d000403140c0c583c030582c503802400703940342c440061260031f00070070f40d402001d03408a20413005403035030f450703810046031582d1a1241d680201850010041071070f500903c149406500090f0700c80c94a0700016040f1480204894007d601d840100301585e1004401c807403440c040b07011b95a805 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 57275498 1250 57274248 57274271
    0x6010315090f2d060504060e040b04081b0a02040509061315140a0905060708160806040b030601061707081006050d0908030109060503010b0609011713051b03010b100f03 74
    0x600020a401500c40307010070891440704507140d102c9400f454004005004071030b80c0f8001d0108503201c41c852507040580c0c030380c04940014000300704030f500580075021840c1040c500e00040c074110720690b910023016a0100d00090f04504141c0203840c0c0c04078074540031b410146000740846168800d0040000c3c448611081c1c03100c64404a40c0c0b01110842d1a10044a074070b24050444200500b200320003a603c6100d10300c000b540d02032080c50741d684240041840c00a8100b420501616802c001030072071070340551141c00c1c021060f00d0400076580244040d5658030340155569030b501000440213403044041101c580f0401549449004820044070032901d8042c1d5a0402d2490000c01003c0300000142b480000100005001c0c3c121b4100105071041240208811a0040100302684c82010040b40c0825052446400c0440d21100099403004059401001442c01640c0303890500d05501c00c1d24204090560340100300d42002d22480e01c0e030803020340d02c1d90400c41d025180a0510341c06455144c003016202d0040c1c00e00d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 57276748 1250 57275498 57275501
    0x1051f0216060e0102011b021002070804030212250b040e04081b031801090e040209100305030d02030406061e0b090103021b060108010b0a0e010e04031b050d020606010315090f 77
    0x910800d81d241256146441c1c50300149208035205485005600b059102038071000008031421070b40700c6503002007080c204011210006508076110580314103034148000000b58943c0d40880c0c1c50803000402070031011200e40c81408000c101c440050052a60548042c04120701810442d130664128500f902d680f41d88a140c900d08510a80c02d10403109613928a50429031040003003d003080c00c001d00c01c5086080d21080044980c074000744199500003088030082800750805c05100303908088228910f40341241c9a4403050314540c030240d4184056a030000400c8180f218621490000c0e103072100040300280700c81010040c001c58607005469080b200012941c1050b8000c0c0d048900340102c108941501e004c1a0050f140c43c1d0000344a89440c039424011490590300c0c245d20404140c3c1e54000401045900341507280b0041103000300200d0074000b0284c0140800c1140041154046109400420303440d01d034400c00a05081000c0e0245051509041e494002d0303400c0b50306810290342c242600090300c0d500c02000c400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 57277998 1250 57276748 57276763
    0x30507050d23011a0301140d0f1202120a0c0f030c0c061215050105030415060f0603060801050109060503070e060102070902030a0b0109050f06071410060e090613030801050105030714030a06170601051f02 89
    0x412101100035500c0c10800c050ac504030038000142c00740c98000a884140284034800c07951a480010041046580002c0030103824816041c00391411301d031031b403071642e03181441e04074141c12000c003041c1213445031041e40714103001d03040020b0007041c0070880c4c5601e0711001030803034080600000c2032031004000c160780c096940e50000700101b0071444a0308149a4030400a0001c001500030405c003942480004201010300b40291000c66030050002d040c0c03076180102c08411000050121811030060541c00103440b403071400910b000742c0d0065070020704420f00b80c1c0003400103031603644000d019981c180130840143c0d403404203842442c1e400c4000c1703010084244071298100f40d015092881e119241c0780022800b04c510f11107403440341183c17004990703444d10380f070740c9400c032003442424024002a404801403000754880ca0140d90041d60605103c44200f9a1a4070f004c031b08d80044460700641940c4000801003940d01c1000c0040418861001c2c1c502035040002045003280107101400c00348400d01e452140e0b8600c20445034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 57279248 1250 57277998 57278003
    0x52806050901060819110703030b0d11100504050d0303020901020606092401030908030403020a030206150a1401020c04090b0a1d070905040317011e08150601030507050d23011a0301140d 81
    0x4011003c2c008806c40c0080d044800306400003440c20103c1844d9042641a200b4156080f2034000c1c1000b0f501c0040144050b9141c440030b04200f428800010180c070361706036450203184261030260304c406040b00024036140004010a00c107220250901c6600c50b020b09031920055000c2e0001c0c4442e0b901c03940180d001e0050410010301d80ba00002c204018141e001c1681944c892181e42550043e880301600e25400c0d5054072601680301b01120004c002ca546081c9001d1401401801560080200c0c540000c040b189201000e070744030500c0300100141700041d40700d030480070a000c10358020700d101d0040c0019541c11841c000c01800d01d0b47d40002c40c0038180951081210303045422034100c03249d0784801c0029400940030b00c1d4141e13040f0002a01040302c1001051440c031007004000e0700b80003903440a0044024100c090038a8040c040b0802400d400e5811074090f85a0300300017800b4400c2e0810103018503a50450f030592100174940c0c01000c00d003240c1f01d1144e08036411601382d02c00c2d104400502c5000030301001d00c0807200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 57280498 1250 57279248 57279251
    0xb0d0203160e0f0705180d020607051006060311070605060d14011b0305040206090103050c130303090807060906050706050a060f03050607080a0513080c0a06052806050901060819 78
    0x90845003002803051400340c40810100502d075403601041c4448a41c800e54004010460a00402e9400c0303002d07003118000c0e10300c01454000004460b402140c107a50141c031090b100c0c0d804c4000191280543c074002c1e8001400145002c1041c8009801c1e8804a801251b600a000503103840c0401c1050303480f984e04608060f0401c1c80303900e900f006000c1c40ca00811201e0000301e00b1903103500d60342107072134024031400740b0442d005040c15141c03610610045005110041c1841c40c42c0b4000d0043c420416402c61000c0c0140d80b280d21082c4c155401c0c580c00528201d1140e00000800100c1e4034140715841c0c1c01020307101d1340741c0d018001007410703140d0300704403400741c0350700d4112203130394800001d0010500600084940c010251364032a1070564840c0c0c0f040350180c800c200c0d003c000b103116035440c020014046038000c1540820b02c1c410769168507800d0b034440095540c2590041e0a680880d80c0d413031241c224154a581f80c0640560f01004801c2c5040b02184128005108038010700540b100086d0344401d011400400d0031041000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 57281748 1250 57280498 57280513
    0x181c03110c031207110f010e131e020408071a04031709100305040209060103060305030913140406050613090c0605220602031b010504080d0b0604090504050a17160201030b0d0203 78
    0x25402413038120900c1524051000d00044001d428031402c4440c0140040e503504065094070824000d43d0020602403a8040e03540d80e502401d00d0207147c07072426410604010160384c86140250302440d01c10300750003d03604110314907074034181411628106c508a80c0e0051151151044010000c44c40b80a0f151090b90441c4ca040200005994035500c118803a0b40b003109c0341402d84c0c541e00011000c4411502004202c0d62003001840e90b00c0c82c01e5181140642a4840040f40322040c0d103c48051468003910121030f5a91904180107681c40c00580340d0f034001c04610320070420702041d071719150f910820620468051020006002128400c4040c005800c0072414501e22021650340c08000e40e00c1e4041d1950042c113861401103448a4801801611301442c0c20041c0345007490b42c3c1500640051086e03041c9254006401c110008140a0070b010302440345020b80c0180540001908250f440144009001c80c0300020402c0404500101c202540f8940354081c600041c00c40b00c05004100c002c0040c1e00c1c065032500c600350 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 57282998 1250 57281748 57281773
    0x108030310080610030215041802130b070b0103030e0112020c0f070b040608010b0d020405030f0604060b0402030403081501021002180321070f05070911181c03110c03 73
    0x200641c0140c1d41d070450001282c0c2d40d021090b84070340c0300303603100c48140241081c20009403405190120030040012101c5103071070396901c070218070386240c58400d0400d90707000b00b200c060b12010030750032400801008080314078244040ea211607151005002c01418000a40b041d240564401c0103040c1c0542905101155074889141c9003641c0c4122132401e106c1148680d1101242e0361041d08103842c2190f80c0d030380310f000c0264201010844980c11080c95030001a43c244000655541c0170071101c090391702e40e203000e002903080c503003030403001d071031842e0081d60185004205110010703a01240c079a80c000e03411242e4540485c00240101c1c10807001e0450040183e002044014644990650b000b0880f40100c0031100120902d10090f03111407400380341c41200800900c0407402040302c5c60400c0c54071a01c910152a0b406440e6000002220b107481041c4911000100394546010070105465001d0031040740c2c410382c0d80c038040d9489900e40c0c045a00040030494901d01500d01101e04018900201e00028251080c84c20200c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 57284248 1250 57282998 57283003
    0xc08070615050604180f0f0c05040f0603060e010e0402010309050f160e0408040b0315040603030e120715050703020709110a0207060504050303180f031005060a080304080a020d05150108 81
    0x40110280403815041c00900c9142003000c032400c95407540d040c810305500420500700106282c0001e0b003811611001c2a20705444c06200344c24844640d41c56090300c507402c08031551086011a013100c418185490000d200801640c04000d04640d90702d10309080541e83c07880120041c0c40da03108000c1c545c1c071a0000a00000c00c0105428040e2200d0340e40d002c000d40e51f20640c41030344103404e607400b4082600c1040280031825601c8010350b4481c8080011101c1c40344580302080844250340c2c800e40015400504046007460711340018540c045420008102141c1428480302d110512490980184000098080c0400d0700070300440000b072102030b07002c0141c0060404007003100e0784244088801070288280c04543c4501503010f03281521001f4005500700502c40c100d00a000c0c03506080d81d907004c0d0401088003050740d0200901c0b868180440c0d4081600c1c2061028020207030100c0d006101703950401d010920100000081c0142100d4046035134081c2a55581002400e000442100807183d034011400400c006100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 57285498 1250 57284248 57284261
    0x12090c01031103060d0209060102031308010501050a08010b09060603060114070605011e06020c101e0903050c01050702030307060f1514030d0c050c040c050d06060c051b09010306020a0c080706 84
    0x1c1e00c0a00401c0001114064244800c43d890396203d2401c50000000d400c0c4001202d900100600481b40f92170090748116906412507800400303143e458800501250402c001e00f032001303240540090041d100d03004001040d4040041034180268070120000d00541e125440180791a921070184903541c0d081400c0100281c0402d009011280f49540d420101412036004030104403165540504a803644440400041c0401000032004000062000c5042e450046015025800d03145d203c1c0251a4594a40542040038840070f60703042c880309005110168402000f140d40c0d0680c00900058040c020404910080c92034020100d942210002e010815040c102c0c0075a0030920200c040fa9031144552000321034a0121a01c028110741081001e148607042c80d40020202d43c20a06001c2d04112840010508592488c0e10840005541c440c04405118050180802100e20350145500f00d0003000041100000103100040c503840e400140e41811501c02c03503820689070380c8800501c0da280040d040240c040e107003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 57286748 1250 57285498 57285523
    0x2040504060f0f0b09010215160e190603050c07051c030b030109080d020901020a02030d0203090108150907120908040f08011803081909020901030812090303070c06020703051209 78
    0x642240440c804032816880411942485150040d160411004d03040e541c014034140c606512600c056000e51002d08243da9128100c54049451511500d020041c5010701d50041a130141c0c1646802141c2000003090b40010398800d07090106094a610340718420900c98880054150b01400c3d1600601d4034691112680c144016a005c0c02203110701c0d000c041c00c8440da4000204036407020088070200e005590081c08940e40140155294070050f034000c84e05103100405071030010703000003504221660301b00051035007007118500c104294002ca10301055444001600000500c0290108580e007242d01c2c4e0051103005520605240c3c68950f51b13000c2030030007440c501524055500f04480c03036005400c6003106000c019099035407024070781c072036490312005590407034800003605131149503070300c0962902c4412074021031150160302d968680910b0018520440a4070102c0641c00c20806d01540e41ea01455240303134507801500059031743e0094542581c00781b00c1c8188040d150303c6014100410820082040c004501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 57287998 1250 57286748 57286751
    0x2030c07060e010806010f0309060903050301090c0e03120c03070c0602010f1406030718060807030b0a0608061e0c040905070c0c08070302062a03070507030c0e0402010206040318170102040504 84
    0xa480300070965142115404090016900e5070004410750302c2129496400082401c0c00200c00104c0d45400055880003901a40811700010040000c040d8074421601c000c1355514046e41150030ba0f400007138881c0e00c0d051240080100c04241d02036030003014002c84003010740c08400c012406070341d07184c060b0190181c40c2621602c0c3c1e00d0641d40a8911080002c1c552003400d006014000c1e19050a07414410700120601d04040a907803281c010030409000c0010401850140742070030348030714007804550180c070b2203608200791036000081404006106d01c00ca1141c540e00c0c0d00d081152544c0c8108030b43c03080d40515030143d081a800c00040c07002030f039003105c108242c05009040a01c4407949070800e1564801072440000d4000e0002c00c1307890040c11207035840c100d9007410300c3c10021060b01c01c4203100385142c1001c08140e030315400042c010410007400e5800f990040ca00410428843c0c41c0c05d80010351502c40007040030f4148800301c400e5001d6640e440b030310a0081e0041e800220050072818034864000d400a000d050f0085 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 57289248 1250 57287998 57288013
    0x105030d08010602031204061503030201150f1a0f1603052205010c110303090a03200d0b18160603020406080c0c030f07080403060603060c020c010f020c040c11030a02030c 75
    0x210710075001c6605a452540085107415600c018000c032030030000344140d5050f9a0790640380b034030300c0d2005c41240007035000b40c4c008201d009103180141c159042561081b61412041d0030104180c480000200c154507640c43c2000d81c461703002e030301d00c0001c03407080d02c5070800d00110100060040581080140c0b201000d0004141103031000d985114981e01030314000e41e80411414001580041c07a000b06400c9070100103001e50b41413002e01030211320520850b4000b01c8100ba040b115182080c1c207440009000c40e481100e050141441c19110314040b240040d0580b060a002c4101d40c2d028044200002c003500e140c104001d146c955980d501c000c00941003030180000107100000401c5048201030706441a044030308010310715120306602444595480000210b40c100c1060000201290309071290000543c00381c100400e50f42280c00e402070800b0034484566040c000b4208040358070079030026a540d5040d806640000c1c00b1070446009442000c5070b40840c6186200001307100d0f00307d56000c030140080c0c102400444892 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 57290498 1250 57289248 57289273
    0xe0a05090a0209130201020129150901081b0c10020307110703020f01031d0303070c060f02032a070206030907050a0e090a03080a0605060d0603052509020a021c08010503 74
    0xd0710003100019500c21840400300e003d00c00d003030100105140c814000010842c800100580c0e03c2da0f41c4052040300e8240108030301c200e81c1004800e003100020b0043c1c400d480c0c02e081a001802c2103102800004000c0f007444c84804900c08128112000c8040a00c11203403a80445103d130400303507004032814030010b500141400c440c2c0c03d0018a6009030380d0f00902c500c008440360306c01103004000c54003010582c0c0208020351100f070b17801070000310b001b0002c3c1e954202100d0f03d1828504c0a6403100010100114810800c001c5124406004000d96181c90300c900c51403000138180488440c01110006980070300004244400e0082c0094441d003220025200114501d5503400b20501403d41100d4844085e000070030740d800000d12840000780d0262807101c000a4007900d6002180c0c00340c010342a040003540d0b0300d11080c0240b20302001842002031000060b080041030151035034110410ba0711800380503680215940e10000d000b40300c0c0d19081c10140d08511402024400001c118110a1041c14000c0c0200b2524491 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 57291748 1250 57290498 57290503
    0x80c06041502070b04060b010504030c030b0603060708012304020f0f0d150302100c02030a080409050a05010e06030a08090301061205060709060f08040209150a09020c19030206010b0706020d02040e0a0509 89
    0x410580002d070034444c941d034546072600646104040e0f141048010800403000506819200010318001d1000d100c084c5032074014103260010103880d400c203124a040040001c0000c0b0010f0034400c419001c00501c00c6143e0710040f8002c0c1c043e03914891131a08010540c51042c00c05030001d000d0841700d5040034044448500103400301c102980c000a5080300b0745d0661030940303602488135859a14405011948450010380703810302a40c00580103e0550b90300d070380c18047c54903000c1c01f507240502001c00950a00b814500d0000390b40d05040c1300b0052881d10040351440b001c0c1e40079401000141203149814070030401c1450819201d034170031114500031912000b400300f0709600c0b0300b190fa160003549854496907900d1300d40800018210083c299543c0091b01101c0c0600345c4c490600c02c1000340490784003d82c55495070018107040c01c0c1d511042501c0c034505125500042680003d041e4116940080420760fa6480c1e030504002074420b83c2d1f040c24460340001000a03107280100b50b80b900c00e4001840411a03500c40800654 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 57292998 1250 57291748 57291757
    0x2150304030207060c140106060c051b01120f0e01090309030201020d080f01090209030c21010e03090a0306050709080102040e0103020a0e1306020a0e0306040c060f080f0106031503080c06041502 85
    0x1c0060340b010100b0b0140500449140c00500d01035000e40005002035413480b429909950880302c00181a0100c030000c103e400c00980b030303450201200d40c0b041d58240d81d0008241c0085e0161034483c280e00e46102e000c070070115070702031180c10710900000c0c03082014608000d8480d004610040f8014440c009400c540780703205031226401000c0107a81d0180070707481c0800c61800703904001d00e101d516001d41c83c1060340700d640d2070308904007003211444103414030300c000360929003100d200c10780000c8250804c10600340541d40340b03040c1c071054941c000310014480d242d03454222806030b0309801000f8a5840010041502c1008600441c1224070880d0603c1c092911207812320b0001d103040e609070700c4140c4108480030005605402810700501c191400c0484c80501c00c000030318240c4155030668000e910f000c02889969401858a0000c0320f05003401e0516003000c6028284418051080c40209076540048018038101981403200458005c45000e46500c0742002c180d8517410161412211440c1c1d00c01454103c040d03a00170769 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 57294248 1250 57292998 57293003
    0xd0b04210e0d1401020307080609070e0303071e0b1014010507030507060e0c04150306050601030c02030403030309081908100503070807050103020d02070605010b070b0a061a07020316080a02150304 86
    0x8500d80400c1d106000340c1d0022980112604845542d40240800b0248051886004955242c0e0881d00b00702082c05401d90018100300100528009521119100001102c5581c7e50207104564449c202d09142142c00c600142e0007841650450140040e001e040344086083d1884000100c1001611301700645a0348500b00000b000b141d4144400c3d80400c040d54008082c890745403007940c242d800303400006000c903044024031440360b078040d1006100f840041e214081e8000e0003800c0c104440c40d086e0b40c0c0a943c3e4041c0348002020035441d00355400400049070f0503206130f1f001c41d003484a515841600c0242101c00110b07409111038105200002d864036000903600d08590140014001175801d24004401a41c0640c00ca03261042d000c00039400050300d1480740b54020480c001c21136443e0701c5d0361325001d1800203000e0500840f0f14204032081c4075a81d41d0720000d942203125101c0e100c0d82c484035031001c20304144080341031000040c0419030000e110303200402c14600c190f1013202c0380000f12071511000300f210301060780c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 57295498 1250 57294248 57294257
    0x91b0f030c0c0f05010605130617070b0f0a0210050c041d10180605060c010e101406061605060103050d02070b04080d0c170304110405090a0b060f0105090d0b0421 71
    0x5250100b01120040c030f080c14011400422002c1d114000308501c203040c00510124a41c2d9140108400d00107001a00402d402040c082d191851030030903810050301500e407822008603000192055aa8000c100146d02900441001d02c11032500301e021000030340007071142d50107181c4160500d040741d02c0ca849286120b40c100d1520000210b0800d41c0800305110034041c12203003556100e0300440d103955000054a8412000e0001003407901840e003805007000e12a240c41c00348541440c0700c0c280c46140341181181d0003603064409a4503221102d003040d2400c401500050081d0103120000300c2840404034000241c80c030140c08403007049a07a0918041240724a22480300d10390400508014224450025002c416010340c044400001c2034a1f00d42941390300540c1c088507c40d460710880c03080c030309090007050b80c040201720180444c008940c552100e4030000400941c864590304580c2d807501da000328152803000320081c0488620380c0803460300f061020070941d400d803801e0700b00100355070250b80302000c1c0c1c0301d28142c56070f603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 57296748 1250 57295498 57295517
    0xe0a0507120b0a05090108010507030b120c06030406180c030507080d020c040b0105190e03011d060a0506011b0302060603060606030106090e07021c0e0f010302040602150907091b0f030c 81
    0x140c000600381a82c0099100101c8980090980d07a43c088250181002d40c000080c2410310f440081c1c12103c03d4050240180403200d40c1d00c0015001080341c43c03011130240c135183c2c2c1c1c0303503958078250000302598140d0f1280700051001074018042c2e003002140589115404a030105621a40010394841c0c0c0c001c1d4020059000d0403c440c10342c01c094001a40340c0ca03060420908004680034124091844460500c00023a0140036070440c03442c090140018a207407115081090381000c00c00b10b500c07200002d1070301c0a1540c40d4000300380360781d1180d40c201c5460050050700022140b124031b0002d451f148140c59092203481080b000c54018a01001141d0407581c803030304c0d4541007a1034042070110403200280060300750b0258040f00c10307a043c0c04e481c007284100c00f00c1d51420f010101c01c00402c00c202c400448890b0416206101c2031115540000f91014260000c0d005100c1c41d03032340c0b486405e20b024030542040c0060303030411011400d03800072a035249100384003d884910b410b040ca810220125084807201800240d198003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 57297998 1250 57296748 57296777
    0x4050a050409080705030a020f0c010504030b01170a1b090501140f010c03050c061005090a06030c12050f070602010c080f070806040b0102150f070f0203030108060106050a02070e0106090e0a0507 85
    0x41c081a0250b00c1143c006081080c82e484503400c41d0000000c0d13401603006282c1c0f05030005c0c0709201e4045201424200700b418a400c41d128003801d0b000500030003d0350382d21942080c040c601c0c01c200d8400c0f0306510000105152080030415072070ba021724420796030320321f08000010400d02c05e4209000303040f1401604200301541110011181401d001800f6400c0c080104039280703101d10700344401c13403040c0d100320f14405103d4946018000400c000900b816503240c6040c00900026103102d44c0282155078501c030300d0140f4101410024109003400d65a07208520413002e000600e980c064010a80e8071615840704100c0341e86640b919082c07550219000000103400c80300045281c0340c15401100e913440184120b0316039100004014030700c5034042e1580076180c0c0014003000b900300e500620703004014030144003443c11549880040c0d540e565040c00303039a007408000308400055501c01c000c0440144005c129007956540e40f0000509464018016a8a4000c41ca000100c00d03400380d00540f030003040a40da0b034030b10300340d000f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 57299248 1250 57297998 57298001
    0x7080d020702010c0c0305070e0c072a05060309100b0612060103020a05040819020306071b1415010902040305011119030b04020408120d0507020106030f0f030306180207030806040204050a0504 84
    0x7080d049041c480081d4501001c600580f40c03040c05188160002c006540c00c2c91400424013034001c000004649040054a0014a160501c125886e281808202c03081c1c103180400c0407050525007003030381c0065020081201d0b0740c80010302e2003000d4048840400c0344848403000d110701ca201e103a260004840661001c00d115510a50040641d010180b5250f8103050300c7d665441e04003010900000c41a00e200d00035201035142c184040391300000141081d40c81c2c002c2843c0310a904009004000e08482200d03280a810340c1c805004400070a2184003c2441540c1c5440480b40250014081610706602e4113000b40c5000301660100c03181d440c3c0c8440d48141c072150303800b000c4010344100900305403c15000c0c44005180482002030140c1c940e18408965243c034020082601195801807070841160b040c110108080352036041d000c11059008441d032070040354141015005000564001f07000940030385608220702201e94042c0001902c81d079501d00350341d1500e034104000d03801750780209a03000c0303030490303042245290130f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 57300498 1250 57299248 57299257
    0x7021e06090a0308070308071b0b04060207050f0d0905190e06040f0c0903020411090d02012016030b150f0d050a0f1a130f06020702190303090f0501030207080d02 71
    0x10304040c036100400c800304a640b0396a5000f2504854049110010141c000c10041c0c1e006038645013005a02203503c6180c00c00c3c0d040708070050000b0f516080403405100e4283c04589546401c84110b0302c56144000e8169a01c105034500308000a40c0c000000c60341c0e1505500c0c0d00281e004000310b460b40c1905140140d401c492000e000280c0c00341d5a0690390491200e140208156407200c0e88521608038518014070043c0c500c14039a00c000e0a07010021410b881d40d030300703240380107d0390203203000b409006441c200350401600c0c0804000c00c6100340f02501c0b18644d0000e0304072040c0d034824501400262110402c6407611140c030440c0030b50044c0c071000c00981500340002c06c5010b032802141254ce01000c0d90300c070400c005101810a9441540319030401030030800f00c0e50016007220042501c0392094910381c503090340d00a08171400034052900041c0d100155550707401031600e600842258941039039907a140181c40205244240501c0c51001d10000890758041d10a4070911504000c841d45440004600040250311 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 57301748 1250 57300498 57300559
    0x4080406080613050c0d0e07030c1a040806100302040f020c060606031b040e01030c0608010b030601080408090405130210231e030108030c1605060d0c0201020c030703021b0102030702 80
    0x314100142010043e40c02040c3c0600491035501c0da60740a280154825102080c100302c1341a400110300b0000180051000300c100c42d402440782d5085029070403018044d1040394404200c2d0721551060042454000790320b02d0840c0e200300c40400028242c071000740d0907400f0b00402450b45403c808000740c441e0074038800456021001c1540e041118114404e1780580381c0140d00940039600002005000b0048040140300c09042c150401c5201907251206249503840002c0c02d0074100160040402c080040545c151440c007c80241b05100502c2c020744180748800c0e4100d0700b0380c801c400b1541c40542c0c81d805140c2084e0150400a0b0200c9190319207241e100d100e501102c90ba400c1800c1004180075900e035407002035030103005450051a40c600300d19400c0b902e45440320304441212071404500300280d5907224101c644030b800200001c10761002000003a0700901450100d84418080044c4103403c1546c00304000c0280000d02d0100324424a40c4070049a80340654030000790041160411081c646103610900d106c0b814 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 57302998 1250 57301748 57301759
    0x6030411060d020a09050a0603050412030b01050702040f0902090a0501060c17070b090a030305150604090c09090c030e1504020603040305030a1506050408190c0b0c0a060207080c1005040804060806 86
    0xd070300e0180351040b684241c44a000203406440700b071090f0b2800d6501f1800400e41440c00b40058101616142d42d80f103100c0d1162024035540d6004100281d0250702540c0015800600401c04440c580083c10090101d1000c1280304100c448005400f1489a00c2042d045c1e07541540c610010908941c5c6514560f4080707001d151040b04244042400600002c036200c5c8600a5500600011006441c016041c2c600c060007494608030081d0341d00449803218801c0d1030840301c200b1804a02c140400c4030079550000d064112001550401a0341d00495405800800c94285503008440c0f4903d4459410300036030307100b0344000790300060410101c0c0109114002031034016070200e000007142c400c0031f0050380c000c041c903a0146001c030b0004181009040d5042c00b00003070304c1140708102e007a40c1001d503852004070341c030a001d00d41202002003408a0a2103080001d41d4800d42d0040045544440c0c604103511180c00a01c80c681c070030703c5032004101000c01c20340100390140b60701920b40c41c102070030001d01755624035000b440b603034104c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 57304248 1250 57302998 57303007
    0x1e030f0605040c030b011706030607081305120a021006050a030602031012050d0906020c0a050402030702030d11040f0807060903080904020903030711090c040612051f0f091503020603041106 83
    0x41e6968400c00c5461542903d0006860205c000050040280d07110303058100f2003e0b00c00c00c81991808200785da446081890b2025055960441c1d0510180489001822520a1740f4600744080e45084c02001c081101e0b03022148000f41c2110100160b9101740a06900011125070410000750541c01840e000406140c00c404150346411080741b01900707500c0150744030f41c40a038000d5261a0451180000341c40207201901c24450028086850301c2d5040c890240200d40c00000075819600c00d02c10f0701c0030482c07800f02c18026030400401c10484e5402c24001c006c1f84150010002540100000f40c1104441303132920b41030242803454030b8128054101601c90f58010760200700031010340d64203100828000788580001199505060309003d0f034580018054031001008020034000b2540045010010068441010403d559a400c0d0484842c0018464002d1170004480100b0b120300303504403510540f4036030705041007200300d211008810185d141c031000c1d4000b90200041008101910920748141d1000750450f882e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 57305498 1250 57304248 57304259
    0x501090215040e010b0c0616020705030f1f050f0a0c17011e06020d0225031a01140d0f03080a24030b0604090503031609090507051206011e030f06 64
    0x1030020507480a0000d00e0016041c44401c0d40d10b42581c0c050942000803a0070034000c803c0c4241e40c1c06002e480d410411203940e01024505108021900140c6005020f0301c2c1c03010806d01500c1e565200c1800c120101001d50aa600030402c03061144600c40ea0b188101c074103a988070f00700410000e00d03090684008001d141010080319048658681c4d000303118851204d424595291444211030a00350000d03401c54100c030070041070442c1d00054a2050070200840c10200c4901d0020030041071042c0d900003800000c41c10144c1020500c004403441c1243c10740101150368034025420482c0040c4c2102d03000300480f0914070480c010070721031143c26602141070100002e001041d003c5c100031096860340c80c03454140158109204209801e03034a19085407080d141444150b920340e440c1500da0200911440100c40d00c0b41c410038095115000901c0284454501000381d0b003001c0b5802001c960002c02c00591220004011075160f510a11041c600340c40f040151041002e040c3d007040340030384428811149015281d10000c02c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 57306748 1250 57305498 57305509
    0x1203050d0c0801030618080405010302090609150a20061b0d050c0d0c0203130308030405030f0a020c21070b1e0c0a020307120803040605130f03031a042705010902 71
    0x5552a80d1110b600b40d43c55881c008082c2d0380200c0744011100c0c1d00403002d40005440300162000e4940908001da1540c0500f0041100c5000f0042d0195115581d542d483d8101d4840b640208162450340d6102c4820400340c2180000c000700d01d070083e0400c0d80c40400001c0345529070600c48241222225521442c104480076007906440307081c1d43e4056180301c0020a04000b10840c1703d912100815400918108000c40315100b4040c006071001608018000001a04000e01401243c290055400d14561a031a4103200250749041102034913004d03d140340d030b00c4070641c8203184030b80001e806c03503600518400d8100841c8003074035003086d4040a100d0003040040002034080360064503c02c002c150041040f00c0540c01010300e414016842084c88036542c43c0c3d9035020843e1101220741c401c0d0031500228850300c401c6000d52080038000400380903403070320208240030954982c00c415801e55640800c440c00703400c542c04100440f81a02600544201898000c1103080715051003403460500400000a0096254001c0fa4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 57307998 1250 57306748 57306761
    0x118231006031d0c120a1a04060b060f070f0302120c010e0d0509100503070e130509010c0305060a1e030f031106010b071509020406080d050c06090a05071203050d 71
    0x911a602108081c000c042d8940700301442606070000b44070311102403421960720740200310440c80c090110740d84042490502002003143d02c42e404160800d0440b01e00d00d0b0306054500a80d4200d038681e05140c0c038070348145040c10603109000c2c43c040c40185040003c3d41c3d44103200112071021003e500491005c42c04841e42071001d80081d4004a00100e000701c1d0040b034841c24a203403c0805024410107100944440d02c0b05582010450042d00705075031b4070744a4844c04e0312611840021168450b0105501046d00481da410150041703c8240084c00010180c0305c00345c0a80d01d00720391641d0001c2c0c200104000d141c080804407900480042c283c86003940d143e450340000154101e10540204940743c0c034a0300d1035402080807a0042c1400c0711801e091030000c0d5a900b0502e08160242a9803a0b03e800200c03043d0b64455002c0c030020030744a011540c440d04101d0300a402c5401805819406010340c3d00080c0782c000e0041805030f00264420098924582082e55460a40d098030a06408102d400c0c00400d918030403d05c20340 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 57309248 1250 57307998 57308011
    0x20c01020702040506120a030507110405070509041407050906090d0b0703090507080a030203042d0906080c04090503030106030903050c010e070311010f02060a020a030b1801050a050306011823 84
    0x2595484042c0180000d403031010b400e0600503202141d40403000070740450400b50306903142c0391155442215041015030b03911010320140e4007920708003c0c448031035049030040c110a04151014003c9400484003e540f69200700d030325002042c41048480040e1900710002d201c2c100e002890060188502d48441e800001d0459040c0d0102c0d82d21070030501441030030400306009181c14001840b8108459034001d48034095031080c0d11800603010140d416042101c080f0401d040c0086c1076445070f02e40c2e1009020b0103418944100381d012701803008031400d1400c141c09041c2c541900b0200652443c0d1800108400400c0880c00643c1040410300100040d103400303000d40040a560b1130000c000d03a50850401c5004031603108000c41c144030b00000b04119043e0040b034860fa00440141d00103803600d01004040d80540340000f02c0d0b0b41d105a462035010850003009040a050380d10640e10850000e0700c0e00141643d80c4e000380649143c203601803104a001540300c1e040340b07401810304400c103642d61b815907000586044058608 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 57310498 1250 57309248 57309251
    0x1a0d1503060b0a030312050a0b09090105040b090111220f0801090209061012050405031309021b01060501050d0b130203010b03060103050a0c0926120301060e010306210f0204020c01 79
    0x10001d0002500510030784800071550102424a03541c4e029180c0224014528001511000020701e01280350388000401d080c003500607000e91800c1c00c6854000d02045400b110012007400101e840090140714840e401c1c80311017002d03031602200444080c20074415007016006000d0411000c18001c40c40d07428140200303140000030a65644a104008207501300512260240c00f030004885280c5900400f0345404c11101e150019503501c407400c041c1d055108170844080318400c07290000030191841c0d07005050400c007420080d100c034903041e42d00c40d003aa442c03441868002041403015008c540c4041d8400d13140d40c1c00c020640e000e5a00d21840240c20f98001b42c0c010071030301c4000b00c10003125580500501c0d41c0a002e4a4041003003800c108030103058620580951852014074049200300c16034800d00060341001040c00722440307030440c141e444115034000d0150380002401c4000f80b41c0194041c0c0200e00581d17646071450201c0c00200410000241030000782503c65404c3d40303032800701685452000782090850b4a00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 57311748 1250 57310498 57310541
    0xe0c0d0207081b030d0b010f05070f021216060201060e101a190807020613120f020f010f0c090807060f050d1503200d05030d0b0d0b010b04060f02060603071a0d 70
    0x19074108442c41c401c0010b048c00034441e00901c0c060f07800320488a240307501031018242c000b442c0c000309a010f41d488401c10154800d044006d03812644cd0607000003107441d568000e100c2030b9100c1017465103480d0305031803105200020740381c1440450a403059160864188420440c04c04105a403101e8503080842640d0300400c2500b400c0c008065414000c80b0750042241801da4016003040ea0360660344c081101d0140700700f00340850004040380c400d1108403800c2c007104000b80010510700c40c40c03034004c0c40358100303a1011801d004400a590b21011038072404544458660185035082800150354039881034451141803035658200d103d100309070348880700c040c5004155001ca00c450020311854000c545001c1c8500c125800c0f606d00e800944000700f02d4541081180010034080980700210b00701e1141560010441d1481200120b10203007407034050310272101035994601a100c1484001e98894100760754481d0103401211003401140d50003402074178010b18032001546030450099441781247d015000c0101801e54101c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 57312998 1250 57311748 57311767
    0x190803100503010c1403070207050a0803130e04030905100c050a11040e0a05070b070204060f0905070807050301140907120c030f0b06040503030d05100302120303100e0c0d0207081b03 80
    0x404001606099008100b2506890001381201121414001700c1c107000000044005109002e40c00007080c0141540003115100c01260ba100d0704141c0900010340600c110000d0384040c000d00341805a9010703103a40305070b60f0900d8140301c82c0000002c00241401143c0c40c9050006004100141410380204c1c6845120703501d050400056449800c80c1059941c420144500030490205140e011581c01d811681c1e070b14902440032401510190b842001d0800c040c07513000910405642240b4801c0701942c3e2420a213a071088800d840354002809151015940043c020140e41400078050b40c001c1040e041000c0c4010368a2400c0090b50001140900040c1e02c1e9850009051003d00400c02d495004666941c203140c20321340400d035a03010310394102c00b0241d100d9010403484250b040810001d1034028180300280200303808915034035482618050340d044074209001800c0104901c80038054000b042146182c0781c01d030b600d8040650083c01d01500d03e070300c040005000c1d0340e840c0203034040c4114608000c0c6840d0320590 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 57314248 1250 57312998 57313021
    0xf0f030807031b1715120304060f0512070305090a05100902010210021801140c0a0b01050916050405060f04050904120f03060b0406030e010b04110408010e0708031902190803 76
    0x640140f4041d025040b05100080c2c0c111181081c0c458025442001d95581d000c85503441025107080d0a0b000028203018003214000400280169880c58940700e1104e1259a011241c5d4070942843c2140e00d0140400700d0801c5219400440e04000c440049a001d2045038583c641400110840d2880e003981d01d0006408550301031216620a100d5903604605040000c800300400c40803280301c1c03904100141c820301651070920800d40740601800421074002100c0340c03400100400c001c0c05190312401d00c9600083e07000580e03840081b4040d8a036591f070b0382014506424007069070012002d05407040000d00012a05481e19041d440c411400781107206403032090100003502c454110310059003054140102400400c6090046074112545441e0005400990701070301401800710803441c035806420100620b8144001c18040c0090b1044903000b00024080045521398400c020f120b1404540c009001e1030701c240100340c1c0c0b44c005051450040da1004000d028105030520000d941c00c44012102000744103100507074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 57315498 1250 57314248 57314261
    0xa1703061203070f0b04021302040b040608092b1202030c07112b080408010203090c03070501020c03070b090402090907020f060109060e1b0c0a0f05010b01050f0f070f0f03080703 78
    0x1c040280d440c01d681a162210b513190b4209000d01592074060200d01191521081401700401aa038119100c64442005003100d07406071250a00081c480c03800716a035400f0200784601c103112a0f455800d400100309289401c1081c500030704405028003080810211a5580000c6114410180301240e5801852808900c4040c000108501070148003503a80ca96640326032100062140450f507200326183d21b8900502e0f248a543c0001c842540048207000600e82e000a0b024025141142592182525140121b0380c800c0e070181881da05034821101006440091001400094005000940741c0701600010810400059030100300582c407030030f03103000c0c405418441030340500001c0006202d0303d4a00040380342c03c0a000740442d00b40b581503400690746111070400301c40c81590172006490102e202c1d81080000d080490300180c4c1c444d42064100c10480d0301c42c00858103846600c07070b1a2820280e0845481c55107401c104412152140144801ca000c10841024218400d100780e8403189945070102005064900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 57316748 1250 57315498 57315529
    0x5060a02100c0507080406080c0d02181201050c0a030b0a030602030408030a05010b0304020d0b060d060509030a0207080d090b070606031719081b0d060b04030b04170306060415020a170306 82
    0x800d102504c0028260422541241c21514040500341c840d0400d81c04980324541200c1c50f9541f0025180001c01c418030f18100603803000b21804104d440c5000c190b1800e90f80221841800c00c0004c000c0d001d00c5d50f0013940180c440c000f02a0403000b04903141e5036200200c2c0d0042c2d4003034901410101c1081801c80482c000e0a01400c1d80030800e0b4114241a4042040e0851240f00200341418100c0003440c90788408008031003540c0c00010910040c182405c8a507147d6005d51441001030140417404070ba076040000348111841056910446080d150100001c003e400034a0221801d81c1c03100750000c041001d07965040e40034448420440d42e500078450040320107000c1366400405011511b802c0111284005404150b4000d8001d00944d8540081415800821007604404800300c000324000c4144804030118910640c402e1031485a12949441e405506010464907194070071420041885141400c0d000008200a180100d441300e0741199a401c80344070208000042c03001010003000458941002c0036050001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 57317998 1250 57316748 57316757
    0x30801051e1507080702030601090c030f02040302330d0501060f020c0102120c011509020a021504150f0605060d1a100c1b030210020d02060601050c0303040b06060405060a02100c 78
    0x10aa800b1405a051092104816100c0801c0b07480a00c00040121011294002c1c2920415a111031074100104900d410b90000a0326200f8040c1c3c440b1158803c0b1020f0740c4d00107110880140151170180721f0304c9800700100114070080400700380011004409012051241c50000c0707120360400c2c034003c12105c0795542407030840d405250030b0516a6000315a0404642544a810b6910355035149040d0241c05200c0d900f2421002d03c000008107500d003980034015402d102e45c01d0b903110100110211403481000e5130f010b400c502d1a440b1141041c1207540c0800100640e032400030680c0c0799100d002a11580281140480494491095509090a5044d20b800440d02152080205005806c0081c00e250742d400b80107103c01034801088008100743d011000017540d001384280c800601c90980203441d000721000f08000761241c000410b0b145c2d0f01a5041d00c03500c0c04850004d50459407640c8524001c440090310343c907003002c0300700000705443d107031b0b10000d02188890390001c2802031440d1022200303c45500003400c1c01c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 57319248 1250 57317998 57318049
    0x2031c120903050405030d020303060a08010b030303070507020112140402040f050c0904090206040302030d09090c0201020403030503040b0403030e030310181a0d030203090904140d0305061f0903050a03080105 91
    0x8a420084240121140e4800014003829a1500740d0b09480b864201903031501c01e0310001d1180395400801184501c0c42039664441c0329542d10003441c262501002c0c40c551641007400000c078214800d1000c0c090039401407620061070455183c0d00c404a03446200c0304003280205d10200000d605042c010700c20341e00307060341081000f4500b15131009001d00030441041d01c0b030750305c803560300b004c0d543c58206580245800070141d4009802c802c0c0003030701d034001c0c0e4851a00305a007400c0282c0103040c018401d031421030b500b546409144d55919a51a031114100802c2101810ba407000e41521043c01080513512452201308104403440c10800700c00c1242d0441d016000d442070510f60800d460b40103d01c41e504940710180c40c00f002d0250702e072030264198054000c0383c0c1e41004d12001000b0900081200396620b49078907100307591040c0012081101556400c40390030b90411540000e8420000414900c880540410f10303094012603203a0765103038100302c0d490506034001000100180190302d0400c00c50071046207003e100c00c192 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 57320498 1250 57319248 57319303
    0x5070e0108070c12051606060807080f0c030312180105070302130e150d03170c04140f010801051201020d02120601020708194701050a0302030c040216020a030f0203 72
    0xd03940c000c140780101704e004241c0d0901901c10300c01030594140c0c4402d05002c0079445141840e500d4080d4401d100582c440c02072540030f22400410000810040034000d1854003d41421480c001c44016101e203150600d14400c00013120f00038440c45002e448544d8016030f84e10344050310108500d080e90042a207a2111900344003040c2906a80f0750212030003941c16100b20005da04003512621035000480307111744090410002c2d2000b00310700810a0310303610050003d820540f402070000c070261071102507012501c240014403652514100311000f060829002502c1c141e0240e2585080ea006080360210780e08404003070003695030b014070040c0003a1504100414403120784a002801c5082060409402044005404880100c000040c10366518500c40c403100a0301c41203407003001a114004036054011041030010402d458002582d9040781d4004004100c18248542040001d50141003580b0340020f1054080d40103840304a1807030000c600600030302200e171055006060420b02c01810000079440340325081c2d01c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 57321748 1250 57320498 57320513
    0x13020a051606150305060601031a01020d0c060b0d0605010f05150a030906060e09030d1514040b0f040e030301080712080711010c081803120403081e0d05070e0108070c 73
    0x40e41200d0a011220301c411428140000c0c440c403140e603180d0341c40031240030051140000c0c295009130020790301044a10013003000b8140e00f40028901500503042f540d00f013100030f4410500f00c00c8260154a002030200c41400004000541c1018211082c0b43c56000411040580c85000c400421095805854030518406c001c03d50713104101d10310050555035440c420a100c44c540c4543c0243c09904000416030801ca03000ca50740b81c210106098a6a00f010f0a0494140380825503104580c0221040c0303894a00a50400014201031b064054002c04500d6031498036580341d0003585400c48204000e50b07078a50400d80002d0030002290050b8081c82480f94601000442440440705e060341c0000500401401100049507030180b60394015200e41c03008101d09030751010450000126034011800c641e0f168506a0707007840f05019520010b0700c490000e0014244c0039105015860300c01000030b4145150598003100c1a080700c1d0240c0c1e820002401560440ca600e58000c040c1c2900211582882c0c1d00d403c800d95075030381 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 57322998 1250 57321748 57321757
    0xf06030112080408010203010e1801090b1b0c06040804030302070e15060705030d0f0522230a0c06020105040c0905060a090f0212040f0c0f0812030606040b0307020a0213020a05 77
    0xc9001850310006007803003202c100741e80107008540d00a65695039034502d00040c10f00309544411011203005400d14400d07405101e0a010390303610a50135005940d03038141c821825a0304004a03101c28000304030b4004803040510225200c0ea1207149030a89550950074021314095140e040112000843c2c001d0100d94010040204650072045400590300e40261509904502840d014a040b840c2025041c0e030072444140c124030320542040c12480640261030140d42110921024080d000072103501a40f60003d60340190104080c074403c044070840002c1783e43e04800b040f180c1d480040140d41d13400070b0000b00681041240028002020144020708040e000070b034101115201d060300e4195034a6542450b0181501920740a59403803004640e2803510741000800c1c0025442c0c00c40b00c80804000214030540a00d90070426601d00130024215600b0401c840c2c02e085c4d2000d06020b5005005220005001070580000c520648035540a4401c10301d40e84180b29820142181449405005005118580d58803d0994 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 57324248 1250 57322998 57323009
    0x403110318040902010915080a0e0d0e191703031b180108090106120803011d040506010e040804050406031b050609030c010c140a031106070e01140309070801020c0c01020106050f060301 81
    0x1d208683d500c0161348803507a80c0c1c8420880c1c402400c2405180e0b42012580744540310140c4140040001c002c001900e40900900c010041410000340d8040d500341801c8803c0a0283d20740c0c1c081d1511b0b1035034500b40c00307641d9000d280b0b801c581c0000b040100311504000491189032a41c140c00703060a102c900e40702425800600c20398100a000b1001910405003500448000c01c211040c9150b0416241002844c940c001d001e06c04c450003a802c400d0a03450041c030b0320396102d60740103000350406074240390f001045075034050019036000000307000c04101075031584078850007581701e854090204054802c0314444800d256004500c0340c20148000d0389662804141c0d0800c001c000d00e8035501080042c03606010300040e58141052505c034500c2c4060070190400d01140e0b0340301400301261001da071241e000f02c1c9c0c1f84052480841c00207207202150601200240c02031a0800000001d690341103450384089422a080403010040c3d6030300c450341c40304440d6028403030030000e03000a44030004015041c0011540511062140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 57325498 1250 57324248 57324251
    0xe0c06030601030515060c07050102010e070b070b100b1204060e0d02060703020904110d020903060a02070f0b070e03010f05100503060420120304030f0303050610080106080a02091503040311031804 86
    0x45c511000c400040750604d000181441d4554401d8035006a490140b8001c043c050361803c1b1521000b400002103503000c48080b503000c54600a8039035201441905c02414070030900c008028003040055101d800b0342000c03008404c104105150a00305407040e0742990b10040303c2038001c090008140e0b40d01081c0c00b64429024140580d0b103450040110340208240300b2044070504020402040c0c13541c09400410311061701b101120704503190810840b040340301e01031000f80303100203071424040000c4103880d100360300c07a0485c04e0500b404000c05c07001c41c2c2903842080f8510021503a8078100941d94105440001c05400e00f98014001031a0035601c582c01d50800d50301c0890b10b528000904c56041d41c2e40540c180c0010300000640351555624540303229074007210702c81200400c1c240030005600d4104030072a46041030fa2039444e00d03966480e0110681c0d0034030029007801e400307030b40030001e440843d00d660346030b19188845500013903900d2a01f810024040305030201e54030f009130020009080381490070080464840e030202c50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 57326748 1250 57325498 57325501
    0x4180f0b150a111504120207080a06090204090f0c0521061308040302030703120f0309031b020105090409050a02130603020a03080d0f0509010c17010803070f021309080d0e0c060306010305 82
    0x4058901443c0e0b00d00c041150b1043c00c1100c01c4841c00d0f07001907070150784a42c000254440c43c0a900b80d031141c0e140d021b07440c0240e0100c4c1040012880503000b0452403400940000f400411941310103c40c0041046c0076660690350300c008220030b00b02442040c810351450102c005200f03040220460303c0312006000e044060301c011901c5014403a5000880b00216030050407070742600c0c0d81e881c00a08850b600030342d600100b24a40010040b1600038040c50049a034141e0340e240006241400d0540c5c560b0a0501c10307810403000340996070a6403201e11034207040e07a005900801e1804814410050035101e101210b811150400030100700584a213145002601d0380400f40076200e40280103220300078400196036800450030013080c0494503806500442e42c00b005d503038a1503002d40c0540480b43d4007034000e11a42426501c204062070110307a00c10030640c4003a00c000c05030b041140b40c3e1040403040d00c540358030a490004000800c003268a40a2280081076001a80508030115060000441501000348018103043e02c560 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 57327998 1250 57326748 57326767
    0xb300c0d0f05010b03010905070303020c01050f04030b10090c090302090a18080d1104030605090c0a030b1504020c0106140a080d0503040b07020c041e060b0c060402010509030f0304180f0b15 83
    0x100095001c4c28045d00810001c1c600b810b15035a04c0d0024402500540251500e005440d4030810443e8000911142d0b800e141074074590314500c01404c021f0400c114030040c0c030400301d000da40a02a000c80c840060351b039218210b04500410540101c00381c1a0f100051415155009900a2014141683e40c1080c1041c0c1c4a0183c42d0005019000307282c00e840000e00002004810010039500950080c82da0504441c3c4640084040c00181501400003a141150500010700b40b100310740d40c03001031201c020780054248010042410300303490640e04038004003075084807206800d050001510004210190081040b05030081000e082444041c0018084241580015085174020004070021003405402041192030365405d0004040c10411100002c50820400240c0c4101440c145c9880c0f407581e101511154a840c0d0040d2290ba21010203507070180144c08a05045c00e80620252000342880c219659401100c1408071080305c0014600c4111586020b4041d0026101d1000d1001c0884203203400d207603101c0461 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 57329248 1250 57327998 57328001
    0x60105040b03100603050105010305150906010203130801060602010c05040608150f0315040212010b150c0111120103060b040513061a120a051902010c03050d0b300c0d0f0501 76
    0x103400072144400000700b4000d08485002595003140c40d25a0308201710390321280118151a001c1d0b40039820030000c0e002c0102c3d20700e071901d1896008401401103a24062500b104840502c01d6a071004020765074400d020440c0725020b00a10140d89564a0580e251a09240c000b1b014000c001d010500e100c0201c2c40004a662541c0c141d1355095040142281c2c46000e130b850510a0b0000112400c0f4014a001900c04086080500803003003004001050340e0000000500c4441c2c454000d01d80d04140da41d210002c000340c050300c0b60020f000c01c282c244100d0f0003660540c10800140d840a10303403240074a1400040241020501e007400d02c08035808040890041c10040b844461541c41003011a07008441d2441a42c44100000e030500401d0320a20594400d2807151610304a40c04002c003020f80411154440000000c0c800c600410154486070000035000701400040b400f03080c104521001c1002122090083d04a0380d00d480080e01414080242207141388000451040320310400c00038203c245000400e010800c0c00e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 57330498 1250 57329248 57329257
    0xb190302130b040e1605042105100603030c110d030915200106060909050c09010503180111090111010e0316050a0227090d0c03051b0f030d060503010203130b060105 72
    0x282c00c03521151203800a018609007a80e010b6152000d58900803811401241650101c560324000301c860031903843d80d003210003a10408122064054030801222000252017108085c500a603541425403c00c2d00d040341001a034118802d10072980031401d540029031128400041d182c092042a00c60031546000740c2e01c140c1007910030a50a010804141c0c0041d00540c44801100d155590317580409039603c210004440090712400e08508042150171101c3d4002c08c0219003180034031941c00c4445020a410508480200510425618002809010310341c1d000c040214608500c000820a030890303450119500d218803400344400c1e00300781030381c1ca00340700007800201885500542012010700e10020550b40b5142580602c590316250180490081480040c1d180002d2001e6101c10420b890180c400303030384540040803c0c02c20280204200088410305101124682d4200310055444011000111050319190303000305000760700c10300401080000d1054400b280540024415446440d01801259180714 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 57331748 1250 57330498 57330509
    0x61128060905030a030f060b04030206031801110a030506060c06010e071101050a0b03120a0807030b0616110f0d030e10050f03010f06120b060304240c0305100b19030213 74
    0xd800d0500c010b0100100081c100042542d404100d4640d840c410803040340d18a000d030340007102091000b8401820900010354200720004e10000b0030302840300c0424207444104611011058000c130b056070010713405001e42900f107082107840e41e040807812110340340d0740c0c101403203103420400074200418405030140f041c03110403180040c001c0c041490f00310700c048003030500101942c0c040d208000d02c9200e1241d000c03094030800e42070b6660b000c9580d04c0e00700044028201c0c000c000d581c01007081040040c031703840302119414828803488414403449200401c100d4179030514811203016454072040c00c0f00181e071191600102c0d46046580c0c15800b01000d43c00c44003805248038024140c1b00020012a420b120784001c001143d45c5a80c642c406041503002550035901c402c028182c2140050020400158a00000021803060104a142000c0c001c106400c25944030a0354480881d03941d00c28005030f03e84145500c00034203102c107045407030110402c0349030240d802c1140080040582c089078901e030740c0340282100001480d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 57332998 1250 57331748 57331751
    0x2040f0f0c090e060103050c030f040c0e1e0c0301080307030815030f100f0c0c080a020f061e160206040b070c240f0b0303040b09030c06030906010302030706112806 72
    0x7900c080d002e40841c15a00450310038032440d100292080d0301c179026480c8503000c03240c18503082da1540c04250320708100184c8101c50b90100c02c41d0211b5200c905000d001d01c105180004200d020702429400020a01d0240503452241c10401c0103224021000084581403941807500c9290f60303a0719035000c1924040e855020b6854000c5150902121900144003840703240c0500c820402c00e418800702d1402c580c0c580c43c1000202e08104400ea01084040c405043d80b030041c2e0060b141d0104034104083d0038090200c4040c0640344d8009a40009890354800d0140e2081a1034040390059121880207591101c00030300040818241000060b9018071a4401c07a603042e501c007244548030003225021140b54411b802440026518002140c5600c241d98014641c01100203006540b03044d0900c80b05480c0341d8802c07650141c040c4030780441208103446450080d403154000c1c0014004650540c810182415141d1b40541c00b04200958030301d05000d004101225500d054038044006c01d04a02440c064003010031178080c0086 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 57334248 1250 57332998 57333011
    0x20d0e010e0d05070c050609040e01060b0301080709020c0703020d051002071101030c0804020901230a030809010306150503010b160f0506041106121b0f0408071e030f02040f0f 77
    0x9040540007003801120050645180301c0403458101c0359805080006403006614600030001400d04400070500100d0141000c106107400f8060a401d48000d50301ca220303050400070040190050500c4080040d02036070006504e000703e03035140b156481c509070101070300c11510410f041c030030400c0030854601440f401c6d02c402d5407200114100951034134000300116010908112003050510f205070340c4544aa640140141d8188c3d003442400301c094400d00c0800e00313262940318910902c59840444003001140b08a80003596007055800040943d41c45a0103050f1030b010700c01000400b80d1700a4140c0381501c00301d0039031540750912500c0d103941c18a40f00c0005080c02c10340d664824148240842c40c40d1040c1d0190f00d02c3c07002c0151450078440c83c1e100b201500d0103034000c3c0601241d40b07131003400f181c011035080324800d040c146582e924815405038400e610116a41e40708440400c46000c00b404001000c000100b03141100e1403458984100412819000911407036035101000d0721080e1582c450002030f4044031082151 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 57335498 1250 57334248 57334271
    0x1021308030901140301030209040311010b18010305070b090918070306140f090303090d180509090a0b0a020316030902040609150305010509030a02030a0f050f030a0204051c020609010e0103020d 85
    0x4a6020b901000e000580740004484400b444504990481781d0240c54a101030703032280c0742103c000034a130300458855500d6400e0f200e266030703854842406682525400d03262030352442c40c215242042c0c2d039201c00d07105074040c45090300d26a20300021a0788014070040020b02c4244018603a030406800f46c10080c1410320b0001c5900003103280030f44241c800c902c560b610041c282c5502d1200d60303590104540f005580d80c1b1100c2880160741c4180000b60503075100b8021207094940758400036000d800100c1d0000d56590000300b091082c4407440c489140c006d11824011880d42c10000a0342543c1140344060a081c140c4400c40501107440b2075002800501d410b80042003040310100d1400000c5955110566441d03081c4008100c1480c8048101e5030340f00102d4004518050f1400410344e03824807417250b10010710005125000d00100c1040c004c0d849042c1c01000140d9a034140030420002d041001070440071111034450074001038a03694101c0b0003550090800281c42084c0300c00480183c415030445016440c28074a48020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 57336748 1250 57335498 57335503
    0x70201140a060510020c100311040305010e0a0b070e060405150c0f160f1202100c14010b100e010801090f0603080705011a06180607020111031308100e1c0201021308 72
    0x16140104c40d0b40d0100c12180d44200e030381ea490000b04560221b0781c160410000c1307009502030804011800c1c10103040940d6616000c3c21201010340441a03500110201020440040c1d80150b07c10810304002d4a242d0008000c1980c50050b40203941c00b0701c4c0f0012083c4030701c20743e10003a19203400d80042121341180300c03124115218404d2603983c184088a55801003a008440301010055500720100d5401c500c40c50740810070740400616a41080c040100c9202c000f181240c0e4402c032081092500204907040c084040c0002c00249011940c00c11203402915401c41ea8410300c59411900d25010208410018100d400003c0c940d40d40020709000b80000d003d420032070107400038220810304d00d9100802069240502c02e492050951a030040d0b450282c800c000b6150410180500900614081c130820aa862040f4595801144004007810307140c17004000d107040c2006a1604840e0001090000d26840c040c51581d42d40c90124442c0410300010b84224924401d505540350750141a4a480c0055505c4101c141c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 57337998 1250 57336748 57336761
    0x90605070e190b030c070804050604030c050906090c03060405040302010e0d03050a0e0703050a03050c1504080304121107030b0c09030105100906050f010e09070e0406150e040e1203070201140a 84
    0x2070081d403080c2814040980b0501c00c03441202e240003070075481c6956000700c5010b5580722050071107219206000102d056212038001e8009548102d086201c0d007810b01c001c00c400d4100c004c0503544518010303030400c0b0003814401c4c00e803504200241c07404100e0f074403240360907809081c89840c0348d183c40c400c6041c00d2840b44d0b4142c20803401a421700030104880d2110f8660682c503203007203000c06407140e03103c0c5058600280c0300c2c1e0000c081030448081584c0340481c000d03500c0d500c0c148041d18140d4092001101340300074480c8400f4010040c268034140003c6502c003808102d500da0f0076a00c80901400c44040008081016220495040a6005000304643d05d0302da89000c140754081d024a2014504e010750100311410200c2c403404000c03405859642c1500b410300d0400101800c01810302c1d0800014084003086074a850051001908040340885034a02c1001402004015181051449a410a01c0d086030420000c2551184191140e2882d9640d03640c045050740985905003203040c0da41c030200e08109401100c1d50108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 57339248 1250 57337998 57338027
    0xa0b090f100b0705030f040303030c02060f0708010512010b090703020304050f0303061f0c020301060609090f05160c0f0f0b071b120302030604090f050d030b0a030c0608060409060507 80
    0x465548404450940221040351469502035159030103000c1020220042d0040764883c4048900c0e001c621070a025854100740d20031000b01e5100e5101e41501c2e601400b069900c000001880c49840c6843c210007429064180306850045d001d002d6020034402c000e40000542c82c401411040950412501c000c0003035000b00c405a40c1b42c002c0803818620200c0100883c0c0c0904001005821a001c03507140b000c44100c001994002400503540b45400140c6081c040d5030000d1041381c6414080500d0801c5030019205131611008070baa2811042017a94580d6450300c83d220f1074640740046048940f45048014400903800152854607014000020001750071a032354410700c05030740c41922544103c54402802403100038010300c0c2404035206204c490f8481c1d4061503200500030004038041d41c40392120030105005002c00e6510307402034140d910030f0700e40601a0002001060340e049030094a940c407110b000e002280545400c0141c05008609569110b07000503ea0720340000301003100e0304210380081d000c260302041c90b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 57340498 1250 57339248 57339259
    0xd210501030b06030c0105040e040b060a08160303140c0304090c05040b040f030512030601080402040504020a0506070809100e03060c03040609080414030c01080108072904170c0306160c020d0b0a0b 86
    0x4a141306c6d441181518102c41e0020b14040ea10389903981c500030110b000901094022911010029151130100310101312200a03010100f441429410005c207249596101d0001251040020781c0d01c0007000000c581c122811901e00154000d1000022111807003143c2c0840d08006020030080799020001030850b04992044084410030100d1035040301903800100c6400740030681501c0058054102074001d250f01c5840100000a0a40c131180094a20b80016800382d070078483c0401e551003d03040107561251a55800d0801c0341c0500c600c580060703900c0c00b000300096544980440031401b000f00b19000705c143c007980640c00d16181e685a10451101442d81c6892900c00d12a6003440750040d4082c04900381640c000c0005882c09038184040f40490301c0b24041508010b0013420b015100b50400c030750103880941400c1c002241c010540800e5140b5003422000110710070781028041c8081c801402441011603007140c104460007005900005010f40c0071494090030055640041220000c81c640c0586000c0782c044a8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 57341748 1250 57340498 57340513
    0x4020a0f02012306040e0a080c1b0a030b0c0d06030f030509030d0819020702010e030f0d02070614180d021503071202070f0f0219030305030402040e010e0d210501030b0603 75
    0x50300e242e0751850b142080f01100a00c008601e05050540100c00e9503c00e4004a03485d0394842d41c1c600d0100c1e8041800a00c494002c43d0301c030001c5025603001c4c2c06c00e4050440c2d1501c0020700350345841803058400740184c08407020011318100003904542248008541041400a04445a082c06030a40c1d1090015a100f4003d0b180b81034001402080f03040d002d080c018a020282e40344041c200720095004802c240c0c14461a84601c0c0002ea50410010326091030040280c0300200783c0b110007034581300b11074200700c040c0580b051012150758070b6001510f0030600180006031a14100e8030102e0103074400040b010350000081c20221100741d50341c600544c040e130110366680c900004ca0361086012130151b110000d040204020400021601103164103081c603000a200e100358039002e105400303c0e68030640c001c8003c24408005c1000750703e028030890302052400b000074001101110909a15419418031700e2091019003000024072031202c040c101c0d06038060840400584d40c403424032051022084990318880e04c101c00c2c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 57342998 1250 57341748 57341771
    0x60301020703020a060b01090b0327060903090409020a080313150912080a14030f0f0a06030b060108180f010b040c0309031b02180c0307020c030601050612040501060504020a0f0201 79
    0x2080725101a059406000b4002d01d603526040a0010f045080341040b4902c10301184410344840154000e1000c052a41200710244e11443c0c0b1448100b40340c5a43c54200b0001c200c113044020007102c040420403100011500e040380700241d80800c0d150001001844040345100003080542803103015a06c58448160b608440070500700e41030034143c05100b40400011000400080c403443c00303440c00b10030900b002e10415240e418010307402e40080340c0c2c0032140d0b80e0391400c0c0f00107458015441034205185000600c20542591910035080d2009004581080200000918500000036050301803c4880050304e65848100107002d02822000440b01c0c440d51500f000c442810f8000d03c0307440010360b031689a2010300e882c2c030303030001100c41942e14060340c00420700b12032a00910b810422040c42001034502e01070302c80c20400d00003494800c2041c0c1d1f080c00703a841040188526503444055440c840d030412102d0031182c2d100c1c501a03024100710b50003a60000e001083e40e1b0304207a00038407032011107403060b8001c000d0655140c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 57344248 1250 57342998 57343001
    0x30b0a0602070b0c0c030f0601150e090f040f08160c050a08060c0a02010e030a050a120903050301090b0d02040c1e02031602010c06090f032609060708060109120317060301 75
    0x3481a00056448070400300803040d180700250050300114000d079200c459503400800d0510f28585600c00664102600602c4040280e14807a0360350780e010319000d003000b010100403c2c4900e00c0501800e4502d408400000c0030040d100304001c0c105584104456201d5001340e445110018440004440e803005804000c182c6050050070341084420200042c600764580525016070b503401248800115501c480b050035180d5000c0009006603c2c15941c2c01d0b903681100d1200500c4c0010403940c0000203814040300c0301c0440c1c0d104040e40e05490a1580001e020aa810300044040024200003074100b030030320070030050080e0404171000c0b00c1029a00702e031415003241c2e0801c0f61280b2950f03285400030360b0a00101400343d4880c0c607010703120512400d80080d0000080c0c0700e0303104080c1d007102c0c100c0009801d14080000c02c0010800034100381028100b5403098142200c1080d216480105823104000d0a0400035503da883381290400070300100c44006024080c40c20000c10a603000041041c00a4080d800b066150405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 57345498 1250 57344248 57344269
    0x120a1b0204060b0301210c171509060a05011202370906030308070c0b0408030423010608010605011d06070204110706050603010515010c0b09011e0b090603010606080406090c090f020703030b 83
    0x111f4034034981e400c0141200c03804000701138941007441590150041c0c0c04490790360b217000b07040180040809160801100c0b0030b13518141c000300b00b030001655400005881d008040e040c2070b61278081c42240c0c444200c1100c403041140c0c01d840300000c02034842c0080e00c0c0c49190702000940c1d0090707803146501c0c0d4170782c4816034500c00000c0c0000c200c0750290300000c0c0070402100103160454030407484807044594120344010f040e00302d11819080e44e55695410060420b0074410000204400e0030615101d0340704045030419121a058614080c40e40081c0079002c540d034540c0a040b10003019820952550b07000c1c10054000c0c4000c0b00c2c0c0a0081d86040c011a11030081003080c40c008810580d00c2d054143c1007517561480040d0090f10802003503403113a900564190341946e241c1c0c0180800c400004582030310b402007100d02c041c00340100340240d250020074821240c0c080c5001d0b5011360400004207024045141030030300c2d0301d0344d54000c40c0d80c2850200d03a14100700880e001004810300a54051081442c90020025106d44 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 57346748 1250 57345498 57345503
    0x1d01050906040e061816080a050709090504060b030102030408070b0903071101180806010611070b03060d030f0c080403030507140129030109020307030302030a020d02120a1b0204060b030121 83
    0x20302c010040902c94a40c5654031080203005030709010794000a01207281d0040c0d60705022112410018a82c0c00c0d8130507a0550310608445080c4950b04018201814010282c000c4401c41902e5500280500280760081042c50a01800865480c500307818000620b40108c0350490310b10034500049440908000b0136a240180c0024101400c40c07280d600540d406803021840040444510800040b1a04140309250003407400752a4055610b00f0316820509000e0b582d00304221003e0103100f40691511030380321400f40d13654142803080c0f00410049040d038503000b0207903008010000014021003090741c86005403d039140719000040320002d01121540c240c0b5080301c50503540c44440c142203008100c250002c8040d03500003400001e04a0b03404e401103400e005582d00305502580c0300141d20250140e0412018051800a102800e14181150914121485035420349000c10000001604080c0c040c0140040710700c0e80108208041607641144190b41e400910650684401541203039680c110f10b400500c80056 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 57347998 1250 57346748 57346759
    0x21c0203040b07020112050f01061205040b070c0c030501020c030706060506030402030604080f071a060a0509040b06190b030a060e0603010908040905100503060a05010504050612030307200109031d010509 89
    0x905049400140c1d411400f0141d0400680100101c0c2901c0288a698042c008038030f8040081d43c14184041d000000c4070700c24845580c40c120401000c00c01464031903800400901c0e020745c0c1070584c0d0038980d0089450b03410150031544001400c40e443c14002006101103841040103008a6a07a8002c20906000858000e9090b82140d00002c00144201380100101c0c59032041241c2400d100313441d1960f0b103082065610081d03221800a2120a00d4104550801800300b25220319080c03815944009001002404041c05204407051001c1104032194040c8007600f1160300c0345407039140c00d2420300d02901152043c40c940d07114130008500741e4141805034407005038024140c10b1416141c041610000d20000307140050001c2c0249001c00c81d541c05205d11401210051000b02d003950600b006c00089400107044241305d02d055903007417280090084262503200b403450420243c01b1518054400e40c09103e10102e40d41540b030180040308140d0406800307aa41055103448540311490400152041d10894a01d217a104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 57349248 1250 57347998 57348007
    0x6040c05040618050601180b03011806030203120708070b04030206061003020a09031e06020a08011404050103030e0f010e0303162003030f07050102040e01090c030507020d0801140a080d030507021c0203 88
    0x880c3d50841500708006240603401d0721014003d141102000e600451554400000100499980d00c04c0000d41c0c1000041c08200c41032540e40041c0e6600c01c0321101e6600d0130340201d401c00c03e02814005690040390803000c40c0394649814500252500707030803070b60036201c2d400a0507000003007071292090b55002d1445841c2c1942c1141542c42e00a0b2102248e00403890040107404000c002071540e0001d07002e0710010340c03202d0302c0650414900c460612044041d6034029850500100003103a031011204408001c1544da1050140049004a402e80a507800150301407100054228203000f00010b2650010b0040d5a0721512108001050004040b5884915810741c0180503110300507038114024175040b0701c03800c0010319195464101c419006426801010084d545c0c80c8a140c07010341601030300358014014805450702408508010300200b00c1070140220310140d0940641d030729140e60280c4800303064402c007290a04e0607003c0008003d007030101c030914014000c0000350440034003082d001c0307004081d890b006103061 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 57350498 1250 57349248 57349289
    0x100306050f0607050307150e0f010c081b07020909100606030b15131503060f060201022109010b04090602090a06090e0f0606071a0601081003020d1e020a060206040c050406 75
    0xb030b5006607000b641d5074041044608001520408901d44425190001184201495507114201f612048a40710a0f90420320030023209980031400c01c1d4800b030041ca401c98101c400c107110b403010303000d08070f402900140c542040c803d141d48001803492170461340c09801d02c41c2d1622180f00b00c0584407500c5000d6005100d240d0040c3e507072207d10340904a240035103185d01000c556503a410a075031024a41600c0702099650106000b600c01c801c2c51071028144a00095240040d801715100d00400c0c0070708160403601918000c100071400030341120b808550010005c1c0446016810004001d50021402d40e1007008560000903800f405200500100e400361014005907541d000900c08440302c2c000c000f664089020400200010f103511b00c1005011458040c14981d4502035001400409001e00740b4035000c240d0301e00410040e902e041c040c0c50f040e0b5100720039005a51117820680e07003818080000039030103022104003050555000544a00c21030140c540c40f9040d903924030601084a0440c0030790051015086074000f003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 57351748 1250 57350498 57350509
    0x6060307031404030c02091605030402130605040c080108010605040519020a020c2709031c0b03030904092904080d09030917010c0305011d13060908030c09100306050f 73
    0x10300c01203504001c00d40e00c02c200d11096501a0850301140400c8a04004c1d01c1541028031585a0104080c0e40005024954020240090100a0009100d0045907211484455880d0401001000c014009100c00c6140d01c0001d03008200c24001d07000319600c0d01c20f00050502d4180901c501036001c90843e400070b451072191703200c044d41c0448111015885101c0c10014a6100c84013a04400c0c0404406c0356161440c1c01c2d883c0c440264094002c4000e54801c1c000c3c0c5605080190702114481c0a005000030000b600c0e0700071900318000c102d00f6541c402d00d01300c6860300740028504005030042d0203100395041c2c11212800c030200d1200c159405001d074003040c0f001c4000e60942c2e40c803c2e02898060f00300300048907035802c4614000c1c2012000c0312420394480008031202070705402110302600c020021041e250390081001e21008100410100180d2000b41184050002c07543c040f101c3c898022400550b03030310303000d21400503e601c0700030064010761003071400c250058424840c135402c2d104014642c442008a9008018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 57352998 1250 57351748 57351751
    0xd0903030b0f010e0d06110a08060f09160c050f06100806070207060c02150d051501021603020303181203070804032307060302030720010e120a02030306060a0c0204050f01050423060603 81
    0x44207695101000c40e0507c0c280000381014100640c0c840301c42d841d02d070302400040c14010013041c0c0140c20400c1030100001c00644000300740d076031506c2e0201c802c400601702240b03404d20412181c030650060005000d040364020950a059801d2082240e00c0c42e141e00601b241c1c0c41c110703841400d001904520310100149010944071501400310904141041000e9101c2e0044071410784005032074014980e100e0f501540c05100e40300c44408402e5513580c80780d14640120340c481c0319000c1c4001d5024080360000c01c4584d105010300808089038412039468003141c0c03030312100c65805408255403040c0240c0c14a44032180c0d022000e0b000ea28a903002c0d10106e0319140003680070390401f9003c0310500540c0c04405503240302c000c0309091400780100012411054002070301e030920840d5034014649000801c0322807403245c0c0000c102c0b81c211100381c4105907120700b10b6074111090001c0741d02c000e5101d41400e0511088110304c282d4581620302c1100c003080400e001400042c0d04a880c00d02d504410340c0114005016440d01d6405107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 57354248 1250 57352998 57353003
    0xa080112020d02040f0906060501050f0d0b0a0b0304030c11060903030d0e19050a11030f0d111911010306060f0c02060304060b09090303010305010c081b0c0f01020d0903030b0f010e0d 80
    0x50031400d440f68002016903245d1070340c106007585d07143c40310024131441c2e000c3d8030010902820101d25011081c81004041e100b411140c110894807200070b40036944915298000500070020429140c3c1861715004007080b2000d94266015140e5050018452a0220449204030380003030080d4600f01039654032002400b1281d00e4000d03035000e42041491000c01d0340030060000d92080c07003d0111440e1030300e0031056182402410070301950110000001c04800003441c1c4990180c541003a9800b4502095514505901c0503101d420740340d145100d69007080b911005400c3c0118013600e042c02415180c003c215100080a0b80480001c0e000b03422130707005424440003c50700700d0300899001c0741841c154408249100c03400c4c0d54031041c0380d20010040041c40700a1080340284c90a600e00302c1001c0c2005641c0004540444207080902200041c417600312400030080010740c440340703100075034841000d60040d500a200740c0c00e00b540840d087c1340200885140450645d041d090050319040c205000900030b0024103050031008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 57355498 1250 57354248 57354259
    0x103110d0c030608030406020f101a09040c08030a080405061501050d020a12150305070b040b09100512070e0102150c0f030709090f02070c0e070906350f07050a08011202 74
    0x42218401800200702130311f8160000c00d60310f40d0601c0c0301c0303291000d0b14001d0b1352401e2420002c0101c66004901b41001610116066040b039115810f280007005920341c0841c05074400003409034030003074100051038891801801a144a1390f226415025101010301e14140050300401c2201407441259020740000c50035440d1652228400c41c0300082201c40048103450a4440d1410030010400100b10b01c50242a981d20040d0400d440e20048100c00c4c058034075031503c2403034003071038451489101d013069400c0d9242c13034035800740302d81464000600980b11220420703005000340c0c00c26502148103044064011003400009a103007406400d84205246c101405031020803020550009600d61030b8010103106159a01d001681d485642c50b22400c10003550f4010303c10b07003d1400c20808040e030004480812214281080618040141c000d08500640b0340c210031929042400d05440120718500355910a203483e094a018546035101c0c29210f5000d00400280020821001803108a5400d480c5501e4184050403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 57356748 1250 57355498 57355511
    0xf0e03030301080303100f0b04060f14070609060e0a0c030609020d020d030f08060a030302060f040204020409060f030203010f2d090b07020c1305070c06020304051203070203070506060103110d0c03 86
    0xa4103680c030070380c0840c090f50720100a01c0031144960085800414008083d040924541452a61603000310b00c0380100f800484803008039568007940f0030007130750030051000d903940390620301d80b000c000d0480c5070055544618064130704044031400544c40380d5141d0054020040d10746140d442c5005008000c404a0308000c44010b040010b80740e810961510a109031612a201c0440c800010482c4a00030482440740c1e00e51401000403e40200d1880d42014021081810036903550000c5000b0b44510361040440038035244000915601420035801030380d102701e0007030103a09600d00d0301800f603800f0215140e503480078401c0d0105000341040d0580384546400000840c0400a035150820345080c00c503100c6016810020102072545441da50120840740003810030403007810710800041024440b40c1c0d00820807030f800008a0140241007080d8401803181d19603865680c5405a8025102d802c1030104945a21804000c00c0715903009000d0b200c448000b14076114100900d07a030005020381840d0004100f81aa102c1c0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 57357998 1250 57356748 57356777
    0x11e0b030a1a010608090606010f030e010e030c030909060406270e030d0c0f020d02060a091b12140c0609090414060c0a090f080a03030209060d0c0e0f030a0f030f 71
    0x780b2801528801100000702c0b0b40c90500c0203401513070002e1034884540c1004040100c00d030b8010b00307500104011403030005008001e6015890051030002006441c82c4408a014003561700000300034800c400050745d880c41142c0700c0000303100580c0c0717441c00b444500943c8200395904035014064000750807012181c003c140282a1808a41141e01c25400c0d030710103c0d21910f84184181d044480303104d8841e03562006054407103a04038001d4640c80701411000c40039464900b01000d218640d0740d820140c1940c03851040213140c1c0e03154500c0c0aa0364030358017125800c5521a140e50b5007600491000d100840c09048185059070719400c001c0318941c0180f0898140005041c200c0703004804020861098807524011580c81c1000c0d034025140802c2c81d0b204800701c40c0c00c0c0304288400c40d00841c49402c4140d00d1b050258407910301000040c524065000c443e10702501d4000d84825103a40300503c95002d0308142c4035000300b1030300341050603100c0c00c0801c0c3c081d001d21410708003040024465001440104200d2074034151542403103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 57359248 1250 57357998 57358013
    0xf0a0902041805070806010215060109030501060b091c051906060b0307030b010210091a040807080f03040201030f060806071409040e06060907091d040813090f050702011e0b030a 78
    0x25040400910810800402c80342d03450301c075603070b04001e907420315040a1508800013940c85004904070003c41c40302d9008100c003a4010a0140007547e07004000303000480d1690b4049159400c2411420b1286020361048884980140d036103040302d0390044082c02d50005109444130090310300c59021150955100303400140303074034520060b6000d540141e40106030708031590002890718030910b2400700c0d0140307088103100001e40c128020b6884070801151f21100d0f07030b131281000502c5009113107010381480c40c00207410107100105e20045104a100762420850740501d801740f007084400c940154261503001c28082010030303004454071207403d0b01241450303240c18032000104080c2e821504c00402981e0180c41032120510b401c084455005c9018034003c5800c905d401c065440310025000d00e04090f1180300045428000c00d00203c6040f401c002d01c00c03d5005598040e01c0c0000c5c896a0503100a0a19040c013023030b900d51043c0100683c0e519480d038403030b4810107900c010f217005000d020f5205500d032142503010340000345803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 57360498 1250 57359248 57359257
    0xf0e1c0501050708071b020f04020d05011205190b13050a0804151202030f04030c0309120c180c0f12140c04230d080a020109050a0b010602070905060f0f0a0902 70
    0x36000101e80342c105102c0140030b010015081c2021310100e03000c1d10490744040c280d100c400c80d4040391050307030055180012070b000b840341d500c060300410b0403e0b001141c0c03001c0030219180c009100d002124a4010702c580011000d07072801c2c01c01400c82c0c07440700200d1420981c0f41c100d1140d150180084ea00580308030343d02c40b03943e42e0142d801790031048410b103a50804e0345d81010501c904c05002400551031840d0032250b0280600c0002c0c0014240515658140c00b41441050b05102400e031000104500c03d80302d0030038071000d1980384605c52045400a0040500d0341c19801080f8086000c0e0300d82e400246603451040e540a500201c050703125540e241600741e00a12510b15160040e0080044160b440d424500c80c00650301c11031000c000300d0b0340c401c544012a1740b552a852002c03e50040091030300d90644880803405007600c14005011481000030090611021028a5048130b00c81c4e000c5500860b80c5400310020307588112103141e030208410304103c00a0414a0150b107501e10001e212010040d240c80700c0204a0300f2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 57361748 1250 57360498 57360503
    0x312090d0f0e09010504110f0408010219030e301216020303010e010b0f0403080a030b0f040c0c061a06031005091b090f0f03100203250f0e1c 62
    0x14100620036000705180240a103180340102a000022001c00e00c040010b00c6194050740c0e50340c0c001c105030b0070650151224070140000259403250383d450224040d401c120240c034402a05500300c819880e00034420a800741910902a00f45038920032140080426800464014012948500710b14180804020a64400144841c0c4a01c0c1050480c3c0450002000406419940708200602c511022482c480c0d04507040700c11b1140c2d440040b0303e112070007400340d50f000502c100c42c0810040e042c95090f400c40110203409030754501e0b14103d0401008151611000e440001c0b075102425a40420040d80000602030959001c0038141e043e520f0202d8210b0740122044032003042030f84400e00240c0390480f0656009600310b606810b445940c210620307128030802801600c03800300e14614410ba07480300740e05140b1410009041e100700e0165107a00d20b019500403124a43c01c0145680b88100b815605000401c403042155038854400111503815110002403d00d5a603014405010980d1110a1001d250034100e2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 57362998 1250 57361748 57361753
    0xd06030b01030b0901050f01090b0112020414090c090105040302190317030907090c0e01120603050304120203061608160e0a06030207141f0903090b1902060f040221031209 75
    0x40c554100980c41480c00b40013600309034102800d00400070303090405a815030350000c0002407002103c1c00142c824005d2140302c40c04030b5002260008205d180002080c00e401001c0e2451142556000310b410b2041c450031889601165003440280058281410700001b1091311000c08031810f9200d0716113100e0b2740040c18518403c01000030030428482800d11480c4014070007481d05101c2814a1000900003a11243c21141045150400c3c0c030007803405500a00c0081d81c0200550396990345a030b0308056420100e0364143e002c1d114003401310749480080348201c0441422596100c0498035075400c09206000030340a030030100300c00000d00c030a040e550041610000c1509403070050b0380303a0703051070464a00e0140ba1100b00c03450300503c0e0f03c0c505000d13030281180f1402800181c00500a00d0a20742901d0140440c0c02c03000700e00130040740380d544807000400e800c142d036100c41e0211940b6039218601000c00581c1241c1c0207400003a4000e200052083d22581101011200c00c1540c2c01c00114020046d203260046030b000703a059 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 57364248 1250 57362998 57363001
    0xd18080a0215070903030507020301140106080a0b01050910030509101e0b09040b0103142107030905031b04050612011a0f01050703140f1e070204060b041d06060d06030b 74
    0x26010020380d030501102c500810010325150310050301201480c4030240c180034000900400f150b800f0352000c81500c00c070340407203801540c5a800003450740c40c00721002540c4034034080a090301076014000b0380f4244c50300100880a5900702d40c400320042c11000c7c10100300c0c0d124510310301ca007803d40e44c02100540c925a440301c4c44901c540c24420401e8a9451000b42d0080071244107000c04140340041847c1980e030060702c0d0b8415004110700052826010003e4125083d50084141288444920042103200e00903030303440203020345903410940c55000300498440c80041d580c0b04001c280c101500300990082d0300421081220800c1e94002c0e095500040e02c516004114070f6040e809880d264400440345002868002e0410030241e0b40a0108202c00c0074513004140c012130340c00345d10700c0b4108c21600c070225070110160034590081100329080e00a840200e11035420074030081003814404080e2012910007030070707210440b466550180d1a206000c0e2403590084820010b07c1c4580b201802110b005512a4019104a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 57365498 1250 57364248 57364267
    0x703080a08010f0302030a0b0705130803190201020c0a0f0203030d020a03050a061a0a030e19030206010f0e1003150609050903040e010e06060415180312080a0902090a020d1808 77
    0xc10105030400d450400f0140414809030b100062803107211984692290a552103050f02915280180d64444030403003a040703404100810048058500c125115a544054280c059426400e0303009500030181590320401c208008226218208110180040c0c2513070710b00060700c00c0072401c5c1d81c01070b03415101180e110010f20409043c284210b60041c0040b07049100e18030b14003581c1417440d109103810761007050340702e0115100d82c18060100422401c030003507420281410914020707484140c00d10034900500669100014070a0200380d02c2c51054100c3d0444203071035400c650382e804144a4288050251555071003001c520700003036203d00ea0090a503100255102c0d823070060030500440c0f050f08a840c00c207d4805c00c0c004561100030030348041e12003e040044600141030800c484106000052280070003241d03100009111842039a0040c08a07a42d440b041c5036030f614003401d01a9841214025004203105000840e811003940c054100c1e4050090b020542024980304c4203024101c400081e103404400181c00c031007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 57366748 1250 57365498 57365507
    0x1202040b030708070e0d0b011e0b040303020a0201080a0c0203070b040503220f12021305040510090303020904050c0a08040809030a0203031b0717070e0a02070f0f2604091d0703080a 79
    0x100001c0441b00030041034401e56030620304070010300c5a01e000c0c1c80401c503a0300302101c10840a002400010700d00c1601d950352400d00070342d102051182a4080350354080400d24111681c01540021091a0025031811480395141c140074100108141c0c0c00340418444401c3d100d44000b006031012803c1c1c0715078800a07040441d0540200c1c03507a0721580c040c8403001e00b15001a1900303d1465040004c0c03c2c1c0000380ca59642c1411030410805001150180d1315100f00c4508054055000c1d01914500fa1400c1026944409040700d55114294064000c1103c2d1000900050300b40b0000700400e080c050159801c9000790760200749160000a00c0000091200ca201c2402c445c040100a008116000401c00c059100003103841d15080039001e01000e01002c0b000190003804075804440f032042d0b020850b1175036080d2a0410543c030384059001210075a84017041e14604212030a10b10000e912031036002407a2a24008180b4002c0c03400004003922461035000c80c042000d02482100c2c0218040d44101e590f900c0010b50081 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 57367998 1250 57366748 57366767
    0x2040c030c08060f0103110313050105060f01021509070b12040b1003170702030c060d0c08010503030a1709070f030804060f02011401060c021206070201060905090705101202040b03070807 82
    0x101050725100c50301038110b40c042d007810340050003601c84091040d01140100c014140300e03c241e91407400000b01381b1400c10036128030107048a006030005c12450b122803023044034180b20340003060b005901130303111050705503804414160403603a07640c01c40300760275078400005046800c65050700315401100420803003403061181c0b4095201440030080302c401d9003581d4a00703101e840518040179100700c010650004544041125840c6094010b148503114070001c1c2864000d000601101d20010700e030350000050b1420000142c42c0e032004a40c46205860403070400c010350185000382904a1032003400030005168110140041c061805041c60659850500c40003500c1024003d03166003c6a14189605002241040541d03041d03030392914081280300014000070304c940e2041c440500312401013105109010b5015031203a421284100d605011650380d40d0038481d1a59440d20429800c09280c00b01890780d6403040c180c51081c82c91260740182082c2c0c96802c0001203410456421000c40c0f4050b0038018800e802c2412032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 57369248 1250 57367998 57368021
    0x90307080703120c08040905011401030f111b03090607060b012303010b09010309021504180e0a1707050a03090611010510050f011b08040905060315011206020405031501030204 77
    0x1c04038585555901c280300c55002c0303001c00400800b480d101017008541c0c411107004202c0c40c7c5050220b940c40c2c14541a60290076000c0602180c0b03041c2a0350b0310904a07000d405003096624140c0da0410300345c2e00c0e5407508010403100001e060300040112101c0340c0d8805000e40650760040304001080040d11713002500e041c00b0760800502d10711101902581c440d0410b800c07281541c2c3c62008140d2100803400058002c0d01080c44020b5011b42c44022405c0041c8119000d40210390b82ca0602c500e04000d252551400c8500041c00c10300183c00003410580440c03800d4102e104c40c8200e5044541c41d0146540b209030405c08241c204a00085245000300602e40d03218195442400344280200081c0c00c04e4181d1402d4640c4912130540580200740350009541e0140c0c0d9185507503d4150014001001d0500c0d02008541c041d00801800501e400041400d90a0000e603000c2d001e1204050344480740d0802c013882c03c0542e01c144080701c02a0702044045600e4605012815114020ba500e000d0194150320420050320002c5441 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 57370498 1250 57369248 57369253
    0x910080103120516020d050607020105010f0f0509060117010b09030c090f060d080408150f0a0207080a080a060302060a03020c0f01150608061201020325090f05191a09030708 76
    0x144042580041040007000883c03c28507511116a050442c48030700d0810041d612148540011080c40360100c0c00c1c41c4143c03941e6000b08801d03070301c500a4201001d0603000d0700b440c02020000c01c1c40305047c900003260b0800c0e014102650019a14149039200c000c098002d0b0407203001c003142060381030504010400e5041c508866042e520f20b080501c0d406404d800600c85807080801c202c0351001e2114500c00c80e009400d068041d104540404004600250750030742c1d01046201502000500c030758094800d480c08564010b040519161548c0802c55100c54094503541c0c20568403000000180d50300b1004014075101510007503114200103582c541001c4952403916a10713414001e40403100b0710341c0300c810810340700325040c40720240d2144404104880a00c3c43d13000e881d584000148014044c05008411000320380103485c004103580ba030310443d5130030010310480c00e030040c80d104244034034500b03000d0f00d2250514540e40b6100c003c3d0b075105030218002c21241c40340c2010314002000d00392414103100034400360194100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 57371748 1250 57370498 57370501
    0x19050a0b0114090d050303130309080604020a150203090a0f08010f0618270308010302100507050601090506060705070303080717060a06030c02030c070e0f0f0708070302090117040602091008 83
    0x42d204400307444080c40c019100103801042d55a800091040d00d030381003400c4a481e890a05062080704204030000c3c2c000c0380010302c0005030540c0000f03c85108a90242030303985610300e802e0f0314140e88891b42d080c034000d5010a2151141030f031180c062240040001c40030b883d030254500454207003194949680d00d164941880d90500c40d1400440f40340c1700440d551000000c2f4002045011101c2c1c83c4083c00c21408884100300110915070300c0302c01e45050720f000701c07400750380110020000d464611400f40014516040480100020b64050b0320040e8800005070209103020240e0362004d0818003160801c90101707000c002030002d683e5010001e69408580b420040200f0700341a80090a0404a849490100740d00d9003405072401d84240140c401c0004007804036060a40c072885c521144900848080d4050410040043c00001e0524000d60094803030752108002d54862200c101c01940c04504081d0501104a250800703265540040a01c583d028103001038440c404101000024220340c1d0b00503081160120 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 57372998 1250 57371748 57371771
    0x903031a01140d060302040213030614040b0106140405060307021b040e0c06090f090a05060405060402121501020f1501090605010203030f070e0d060e0d030c020601181e020319050a 79
    0x8505480c2c042900140c1501d40c0c0485000101500e82e9410007500300d80080746d0440031841180f281c50940b0f1003884140301c085543c0c4a0a044440e08403406044a4601c2d8010013071540038101c4889003016030070750030746800c3c1c80e44049121030f4426902c80005a00c840d880c48003844043c0360340c6115420880f0140400004480d103555503901c040c0105205945c0000d0405080d40d501c03d03074135040c09001c2c2981000303140407003500e002000d0407100d03a03024070300b4000081d0152400740300719044804d450701005100d84608268045d0004400407050541c41042c000c80e0607850b0030409000e51400301034908200b5814103002c0f009481c0f190b880316041d54420700900c00c181410981c0349901c50040e20307210210411540004256003b81140078000307e00d0901c10005040c0e0108064802141d00c1e1070600211030304450491713842d4400d200d05461004501346900c1d154840740c210143c00c02085130001820040403d40400301da00c21b550705500ca41030400042d02c02c8007207014155002168001c100540c40914 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 57374104 1106 57372998 57373007
    0x20d140d15030606121a01030c0608130605090d020c0402040602121608300c0316020a0203161508090703080f0c0601030308011802030c0f03060d080307030903031a01 73
    0x2051b80d1103114100c4001c45040b40c0d449440060700500d4042c088500c40d6020f4050009104030010030300c085092070145c03c6c0214000d00240000250341c544c060320b08045034600c0c6005070300611080050b960041110107404d40c000341c5155807054426091603203000c0c09a802080c01d84081030681e03028441212220442509400816a031400391001514680040344c88108a0004000082c00924500c1611102140341d00480b000740855a00180c1045888040c07031782d00d003c6010040294000100c40100d45605905220324a4107041040f0754441c00d40b80009040343c0000541030000b400c20000710750380010000c007920083c0d616460020f20b400400e104111940500311038828000509208580c00b032100311400c1392400110344803101854100800c5142e009040c03406500100d6828001144122016540001c20b240b00d442c010b01119864007004020a07550201c7d1412039070003 = true := by decide +kernel

theorem cover : BRFrame.Cov 57194248 57374104 := by
  have h0 := BRFrame.cov_init 57194248
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57194248 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 57194248 ≤ n) (h2 : n < 57374104) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
