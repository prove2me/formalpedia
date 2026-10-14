-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0763
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:38:52.904322+00:00
-- url     : https://prove2.me/submissions/7929e93a-fc02-4a97-abc8-a1ba3c667363

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 137050359 ≤ n < 137230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 137051609 1250 137050359 137050423
    0x106230117010e04080c01240b0f0708210118050a1107020d03021006120606050111060703090201030b0d0303050a0507030605060a030b0a090513060b0f0612040317090c03 75
    0x14400e45401c10076440008003409410421120684009002001001c03030628800500c00710141301a0b048e0661100d0110b420b124220880c0c0300104000d69460070203001e5a1101080d0740644004d511900e403d124004020705e841c43e015001c5c0c42c1400001e8101240c0e4075a03107040360b0000b0900c0100354100906e010f10405030350101c448560301601c5105191155040a80c9042c40100d25098035600e02880003070303002d444020041006101f80020310a15a0b51001180c1c0511070040301c2e600340d00b142c80840c66141c003c1d40301c240c15601c1814040f400004100002e1410341c100c40064002c2038031141005000030481c4161a0700102c01d0030100007060808002c0385490051640303031020705680300002e0300c403a07458802003401030032801070520041c0b07402c0c0c154000c5c014103414111500703400d00b03041c5540c2c1e20781403507400e00040001c4c0c00c083c03c0014042a0f0080c80ca000f0f0b0098040c0000d0400c045100c2d40649002032080410320014880c4000607801d15140060040039400726144001d06452140c901c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 137052859 1250 137051609 137051611
    0x90e06060a200a140a1b030308012c0c0c0c011701060518030604050a050d090506120a0b09250503010506041401090b12150d0c090c110106230117 64
    0x14400742c80145840c1007044610300038555202038151281c01c0c1e101ca80c492400901410b06a1151010854504070400350403172691b824003006000c5029800144595000c0c1e0001c00400781422200d0a104c2c0f800d820b0658115000380d4090b800143c00281d00200103904115203950b2000a02c2c00c1e1b0340703808003154502881c88040c01036004000d000500d2400c00b0300020229111a10000c0c140d401c03d040501d00950346220803507007100c0e070340103100d22110114020306002c81140e02c050032052500e0380c14840c5800044c5d00401008440da41c801d600d50300d98032007449151041c4d596550f103002c00b08280c107054140c0ca1003500d01d9010424100014807a035140c4c9001c0e0b8040303c020f0240482c0104d21b070f20059409940c2078000305540174012414014840b00840513a000d03400740f1354400a502c1c5151305101426083c0800075045044040082000382d615038002d0f056001036282050521901c4da41090a4500c40c1e44818402e011720310708014008002060000b908209080141041d038440403c141c450300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 137054109 1250 137052859 137052887
    0x90a030305060402070209010f030c06080702060a0b040207080d05180a02060f0c0705030a03050a0305220f02031002160b0a1b0c050a020a08150601031808090d020907090e06060a 78
    0x78881c40421060303110360301510f0203994010705404d901d68482e5480e0720a0700780d910080c2c038581d062482c000b80c0c00740142005805544240d014260507a651020340c9d01401801440c281c006600b0440300c0c0100c0c0d40c10000d0018290329000224241c100700c0d00201e0720305c6c440300040c3c805800241080c401a44c0b182c085403251031400e01c0f001d454950001c1118207000d040e500c06034040c011a0311141c100b6500400615510401d51000c105944503019640c01c8010740302224002e040d01003a110012880d1040d49596083c4020200c034844c0342c1c14200ca000360b0b040043c944c45100b909034400e60410500840c8103600000d40b02080000c6000c10520303141096000001c00700b40080c0019107024400d092000c1c503803568010b080012600c0e514505550341c1c401d091240b002035034030030010071150b601c01c1c086c0c00350a0b40382212920340924030b5110743c101644280909540014503030303040d40043c8c41c0d80841601c103050a45880209501e400305058100500804403442500300300f1603940b156411800c0e90807900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 137055359 1250 137054109 137054111
    0x304020f0f0a120f0f12020f07060503070507140304060f02010b06030601050f030408120c0706050f07120b031015180207021e0f030a110a080a0804090e120d150b03090a0303 76
    0x503880e400d00a94404c1d41c0800a04084402ca03d0b500c18000f06ea52154500d5819070b0032151382e005c0340c12502c0d40ba9a490b0281100141c000c1011514061081010f010458001d120707001d5419200400a485c0d030340250302c050f0109191000d4001060740a1048050401d0184c2e07080d49140340150000b08244900c50400c2200040440403d091049900c144d41061860000800c078608100e1185040f0380c02260f8101d445030b0420000480c180079000b007490180c0099214a40c1da0005602d80390082c210342203d81e0b070103100d0100e41080c2018030780515001c19090001080c00c03603044c04000d0000c1441161070045150041007002e0060301e400c5490000601e619240802c1040074400103803c050010f070f4869414071444005805012040c59a4600c04100f140c40a100682d41d40c0c00c56101c0716244405400000d0510041200908070740060f50b001c1a54401d51310286c1ca508441c6a0640003051502e07000c41c1e6030310b00610403c105001d200c01600300c441c1200e00b107180810899907611b4044100034105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 137056609 1250 137055359 137055389
    0xf06010b040b07050a050111030a050c0c0c01030203090a0f060203010311120309090709030602030a0501050f010c030c0f051c0915030b1f14040602010203090d05071208060d06110304020f0f0a 84
    0x4c803800b0303c500b84040354440d000340200d49030201e0704410360b041500c1e551542c3d490103011030b03551040d020480f0103141068028000040b0840c0054000b50001020704a09000720000c403000540344014400701c46205103001a1a9415424282d404505143e0703024028115010040191b0800000b6195845000c80e100e58850b900c102084900d540c855100030012400031051096418070303500200d0503110169a04440c000c156001111030700200310000d8041400425260049003d01945581031809942190408001510110030301c9107013801c2440000e00000051040482941c1c03852800b0300030327203803d114282d400400503500720703050000c1c00410385032101e20345101c40c02055018420345001a955440d50f03a0354601070f020398030844580b982c9026000c03081803614042c4054860300c0744c104c0074030421050003000503030312500c001d0720280d400070040c0700c4040012190700984a4000315040d1080d100d090500c14000502031b0740707241d18401c0c9c404062101c0345e80c550307030200b00403240c11403880c00c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 137057859 1250 137056609 137056613
    0xa0302060d0905010b04050112021002031c090804030b10090501080a08030a020a0201061806050405010918030c0302030909010f060e0d1e031e05030402130902010e101b0c080f06010b040b07 83
    0x14030343c176203404d60894100800007414003100042c01d510180241c522079000d075468502281c60744035084c0c00c4012400c0034440c4407403200301503009881113442802218030702074582d02c80003e96001140c402601c41d09600d0b080c001d05a081c0a114018a400b10042000c0b02d660354400d40c0300d0000421408003180d0129850301c003e4402d400100050940d100c80c5251400c0c04900c803c00350079030740911405207061000000708c00415103e108482004010308400c41801ea6a0803516604420380070360462000744945182946c03481ca00a000301786403070b01150b010340782c01c81c05804030790889a2184240100101c940102c1c502c020039403030b004400821004050745c540f6003618846807100007054803d054004030540c40b03030803c0065000718022a0048407114000000178241c600c5000c0c001c1c001000a00d00d8a5a82440c0e10181ea840c191400d02c0904401190a410003124102c0e0054600501081040101100034458800e00348281d20140c02c081d81010542036061103a44940d031040400003607103200b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 137059109 1250 137057859 137057861
    0x20408150c030412020c09010608071b050a08070c0b0d06090606020313051c0f0c0f050a1d04030c0501050f0a151413060e0a050106020705010806030a0201080907050d0503180a0302060d090501 84
    0x112001c4010a0071f8804c0d616075400a040103021907040c1d0102c1c03181640c101c4150858910448403d07409402000b0356543d0380d40e101e080b40c006070422100d0048440c40804e07480300d9900a031a84907200d08000030840d141903582d40546001b07600900c2076400801010a01c41c1484c000541603030780c1521000340d1926003070246007200c254400042c1c448800c3c61301510800c080c00b18981c0407123011005843d03115072204104842044036104114841c41006a070400300441400129031241c00b90030001c034594001d807622401e41b4070407107030b00312880940d00c2003240e204c0c2c040c072452100b001001d44104a0500300f00c1c011171407010f2181c5980c801c1c00b590390801c1403c095a00144081c1c51b034082c9480c00f6003040c0300d402024040030300500b00075000b036650100701d0354801c0f0b072050310981c0c0c000d000301803154064005452008002c0c9c54090940030301c44003c00d503074544581e10340099100340c009680c1d450001010f00c01e9240d81c01c00d80c0d8403440d80380c0003c0001d03139181c10a03500c00414200000540c4d0b01c5e14030b4424 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 137060359 1250 137059109 137059123
    0x5210d0509031b0a0614010807141c0303090318140603042a08060c0a05040504021c1a1309020a03020108070c050105040c0e07080106020303070c050a08030406020408150c03041202 79
    0x404100c2c40c3d00b5484901000b081d0704894611450042c88803c10480da50030540100340995600399214030010040711401c01064003c040c0040e2440c21011200c0031000344684c000c08041e8003181c0c9130144a800c2542c01807554125800d519400754101e402c10600070180c1100d654068410b0b28040042028030800401c400905a0441031002000c000b40804442c45891403144240b10b00825002540800420b0b040303980326107040d41e5180c41d00b03042c601000029003014030700d190481510b4a501e40381511a20903080484240711514800d12040320800c08090100c400108105040031031000068540d01f041d00c0030b690742401d0908180d80c1e10740044038000c20a26002e440d030b60904080c4000d02281c100500142c0b45000100030740c40d514a50b05a03401c040a10615006038000c10000c0e8005204038065a41c8500c19000e0380d407099240d403034080454200340e0701a074003c0e500040c2040384040400c043e04452a2098100e203072440c181e40300000a0000420145c035206c000400b1480c0c0c1403082c0000c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 137061609 1250 137060359 137060377
    0x6030f0b0904060912020102130e040318080705100212030403080601141215040510030206031009060b0c0c0a0803040920070b06093601020c070603020705210d050903 73
    0x14000c0c524003801c012004d852a0784c02070b0f80209031601c640c00c400d84107000310b403d202c1046185075081850161410540140140f06904008151000c80d10f9003481e15060401404c8240003045090300300800c00090000c21100e4009550010036102000744554064941c400d426040004807643d8203001078503100e1000740c91541e026000520090b507440703a01c072039034003c000d400c0018203403a1041d000d100c00c54200723a55000c8a0f00c034020041005161020003160307c80703000560404619600c14028080e0b58881d0440d41c0c8070342d008100c0e110b421404011070383e00750004594030403c0c6032602d180c29459202ea03000d580c2d40552180e41c02049003848014480c02d2600d903000241d9070b0030b980d080c00280d104050301c0c1785104903e5000803d000c0b002e03034400c107805160103925506814114200c14074203120740c210345031002e540a0222864007a4280103502c028052a2005660344502d45402e504050803d54003003400d136000c0c10342c502600d40700c1e01500ca4106c400440001c1c142c882d0b01400303182d40105440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 137062859 1250 137061609 137061619
    0x1030204050a2702210a0e03271912020d020909160803030105060901030207050106050a0303020a0507080607050313050705040f0603021914010c0611210603010b0a06030f0b 76
    0x10f6080808240300c681a2a8044030000750031003500c5400c16441841c4135a0310a070b182250b50070098084449a40e0030820206c00054105c54080c607450079500030813404100c0708680188030002d880d10030b9a0481c1800115035141c3e01050100c0c0700e0000307200b1401a901640d02e8847c2c080300715218420380e80d403803e070000c040003400d1400a00c0e443c0e440400c07903804582403245100c0022000c02c0041942c0c140d83c80141410300709400800114020b4118417026a049c1d900c80700700003956111506400c000e0f6001f540906451015424000c0c503024190b407110440360301c1001003003240c650181c19290802d01407900080042c100f810031320b2074200c1c03a4119a501502c0c1020010120f80c0540c00030b011a44240ca08030380c2d01e03c0c0999084000a154031952a04180000c2c41290940c401c1c0c3d0400754441c031401e4000f541040d40e411195040d049194110034800c074100581000255041c1c42952040045000303103c810140c2000c82d29005a91040a05050302c0e09851220303c080c58021951100000d06 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 137064109 1250 137062859 137062879
    0x306070f021f06090b040b010912030c080408030c16060813081e0c0f010e07060507020a03060c0e0f120d030e100f021b0601270e0105040302010b0f10120b0103020405 73
    0x4016001070a041c0b140d544820b1804070907500306d0a10b4000e4010005050319112045803810b2650861202c03045c01c118108a4070a5001000500319400f5102402c0c64500658071601d025481e1480c0c402c0f1421401d040074030441c01000026440007126610030309510414481c10494034050b51180102000c0c0b034100c080e240808011652008061710052507010110b52030700d004912558207da400e0780c40d0f02d901e604402003d01203a40100003c00505101503c1050700c280e0300d8480c0b4003281c8a100d0080f00060000102d80814901000104910502103840b44040b40c803910704213a43d030f0214a9507906158580307140c422111001c0c020312900002c054001e001a0a61380d00c2d140c001d5120b101e00c4405142d403090140381c840000142c00303060315080038102810840c075203c0000301e03464580000b400c07036031a0702505001e01004c0c09414003991190b0004246440703d84104003080d0080664035001b901d4860010300f02690040b09000e10520000e80040c0303410340800120041e1080b60002504030034805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 137065359 1250 137064109 137064163
    0x61602060c060906060a0305100b0d08070503030f0f091906021603050706050708010f140402070812061509210a2901060206010303090501031509061806140306070f02 73
    0x4542d1500c1064580305844c4c540e81c41c1c404100d4032003020301001d40a503108503a80c0d1024140e940c0850359058006001048001559540c480d50b40d001100c00c0707569400110a1085183d01c03001030b960801403034001100d8601c1e00c1019166141410003000e080c20a24030010018048180c1c1258a440c241c0f429040c0c0c00032140c00c2c0600181d000d081c003254502e02c1e19000a035030520900e0058103036030320400004401c40c81d0031041c0f508684040700603903000d5403c200c6000083d407010b0091101228134031500ea403a280150401810b0904d94404540002e410862018180d61302052520b18405049010001001030742c1c00600d80003001000a0022003010f00300341000000c5550810310300c0049218208982c0c80c0d150803a2108001e20000b070100b401050144800d42c000c0d00412101203040200a11607541d0300b00440aa0310f03990710407a0040035510800e5200320a0f400741d072000d030a4880104614020040201e95158001002d00c420401e81c101180c040b184240950619112100e0213155403401c28 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 137066609 1250 137065359 137065363
    0x4061d1804060e0316020f04060302090711012a0f0206010b0a05070c091109091e0c0f0c011b03110304211403040804050a060c02090703020c03071a0604050c070c0302061602060c 78
    0x844406d07480780c1d4240107210a140f078075008020a480c0d003d8021050754a0700d0105840c0d00030001251400c6540302c0641030141d12040d017000c013002010080d03407403207402ca840300640b102e40a29821800c40d001b0400500c50613220400300c1d5103283c01843c0860b551a1241000e100079110394100c0b42030603051460944900038500040c210800c0201c41c1c101032916082e440b0f0030740c81800d81c180d003601c22425000400c90340714071020b8405806502e402520300580c1544981c00c660795218012103d5080750740c80000c8a0b850301c1242490f100c0c400d14646035041c01d850342200444007003c10b001c568000d01c01440842d12480d522081c00d004403809036100d0815140000180e00940a001d010f00304044001402912890403840c50070303001f40c0300a040b0f4607000c1049000e544a420b82c0c0c040d5200820418000032210100700141781c0060b5160003460a00c84204070a03180058450101c0b94014001440800c841100030400c481d81229059580c81400ca02840d00e012440d0000e584a2004510004181c41c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 137067859 1250 137066609 137066647
    0x209091c0906091e0605130b0f090127031523090f070f030807080c0a0305180a030b1f08070603050103350c100905010b040b011b0b100b0f04061d1804060e03 69
    0x2602c0303024a541203543325411200e51358126514030040e80740c0401c003090300354414501c2b5a0051001003502c0d001c920003490410006503507859a13604600800c20780d900140880c0a00d039030500c2c06031154500d01800f0001050540c00050f02042c800580310040040702000c54460400100589030708520604000e880d5420503000300c40c0e000341e41038885555140c40800706007943d902030060309183e00c5081c030f150314410f01c4038590baa0300e241241010400250400102d401003c181c4d5010409605614000d003020340406442c0014034500100c1100f0b021a034a031103482c1d000580086900e5a200c1c08e0160301c2c18001c0040c11440134a0040254103001d410b400003051802d00342c40a22802e807a082c0115001d041003860b03094003040042c0c200f800651000c04203a0400e003c5c0003010555919218a8a2113610000b204241000002030420809410000b152000d07204074aa402010441c0000705043e4090031841600c201580400202009010713803010345910703003040881e0748500341c0505145002074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 137069109 1250 137067859 137067877
    0x307060c02280e1503010c05030c090f03060901020c070e0403091502030d0f0f2003010b070804051002030a140a091401030e0706020f011d07030209091c0906091e0605130b0f 76
    0x803d13800542c2032401c1c14001c480a965160b60340c1d5103075a0f26010441d000340c0081c900340b0382c00700c00d2a000300e10310341d02041081d002d42c200c180016510360301010020702c1c0c00110ba100c0d00b000c030021020040031030782216103c0100c2d0398242241120800c940b000701e0a40c480c540c114000c482c0f402400382c0c0c0b003450580c0801945203041e20208480e00349440380c07092040c13841c01d8140c0149810030041c40140c0d85080549005c0f031244261904080d10b03100003480070300c59910754400507840440e0003241359074452181c4100c030305455001072512082e0b0100030a0708016024150228140402046450348a82e000300000a0800d095840c41034590700000d459640c5158504003940c2030203040b4541d600980b6410315120120402000c8462869092059403c8002c10b041c08500494103c0b40700d0b543c0e200b0b549000b1055030760303403160340c1400d0000203480070780789801404404900d03809034400c2e0010b01d00c1c2182074030780714181a91192820317205580442903030f4000b000c804070041951103c0e00b80800291040700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 137070359 1250 137069109 137069131
    0x50304021201050609011a0f040308031e0106050d020304020f030a03030e0d02030406021911121005070f0c02040515030f01020408210a140702061801020c0307060c02280e 75
    0x50700241400d00380e50060340d4040e449000c03000100302c200d0102c0c5584082c90185660542848d06a11881c0f0703298204d03920940340e0490004c2085003c205500711034071514402e6241c2c02c299410580700920f00d015041812441580c00004902176548102d0f6902c1c00160040440c1c1400050b480c2c010b000d44152104240701d84144409180c500c0d00201c20740e015079145070b004012102c40000c0d030009a840c10a000e884881d01e1814241c0251101da46030000700399010010800a1082c490440032680c004240100700b00682c0f4000d446a41d00070030382642e0580450703010440c0d4550140403060450001c46a0382d00d407250b0424900284810f40141045039822015502d0f600d000001d05441400304c40002803120004102448a25000d0f4980c82201050004424140a21503003c1202e50307202008040740d80030603101280a80d0b904001c00f0041d0f00094001d84031562034200050a180c0e10700324002c0c81441120f03c0090000d229050103511140d5806400f40d000741c0c0c82180c0409101c003650b01e40500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 137071609 1250 137070359 137070379
    0x2060a0f030623061b060c07120e0a0b090f09190506060a200f070603020403020f0d0c060c020105070507090905061303050d0203090a06050a0b040e070503030a08071e05030402 77
    0x4060842200e075100091000400d000c038148002c0158551042c00c001c404444d4510703528940304c00810000303105034440040265112003e041801250003250130109c00c0200c820803844e91600c1d940c9820301210807840032191520b915000040d03200311a100c1c0e0355000b80d034440410109802d015403c01c20540b0002c8100a5a02c0324801d111481c800c4d044403101241d2051044c5031402144000c1217125120341040d190070400c04403c00381015043e500001c0060340200e010b0041d031501c01807071038084600322034040b5406e10750784e18003003800200d119850030b20416010780e030256400380c0300f250072065000d030665000d0354550b840c0d54000c00c002641641c03584196000141c901c00340c1d49030072496581540315a81403a03039050386940603500c02000c1d40d1550143c680041e001440c84e0180c5400f4140050001c1840d00240c801e02040b10038207012050240c2c0b1a1404000a4402200300d41c99442d8038a401c5d80c0540d40c514054500e041081d901128043e001000a40f10030b074000081e5000e68401c549061030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 137072859 1250 137071609 137071619
    0x904030801051309050c0108180f011b081003030e060f030a05010f08030f070615030501050a1a010203040b030604021b1c021b030d11071509051002010e151302060a0f0306 75
    0x44070404c410045c07241d8880c41d4042c18540c0a10728a9620200842e280d0411086a002980c10940703415448511070b034544480c04640b070790081315030914090a20346480a4a8a029000f0180515200140034000181140308007074564908840320025803405c282e980c0d007040400031004100910508000081110011901880210403101114507424819082c612280c540d00000c2c03003502c402d100081415000080010301c01e000d820301c134810003040092081c201840b0305d20a491030300005c50441d0420002441b500301041d040d0707a04a00162001606c6500181080c0b80c10500d4510300307602842844845058021144c003040e600d1110380d401d44416542d441040445140c0c0700960355415003050034071102282c401c07040b440541e00c800c002c80e04459502c510041e124101c040c021000102d4080060215007000e408a080c010294402045403252a50038151607040180d401c1c003c16104102040c22042c080c4800000240c0003408991307103c8034000080c103415105000b11020900740040028 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 137074109 1250 137072859 137072861
    0x1806020109080301031b0e041b140102070612020c0111030406061418041a072a0b070530190c080a0908040e0103050a170316050a02030909040308010513 67
    0x602258454a10750030f603401c6580c0c9100e0140d00030003000490b10203190026001344000321240c0190300485020414032482022003083d03000903040546610745801051075180d90010b9a1800c464107031034600c104010352070306040a48200001c1114a40c01c08420079080381e80c0400071405140308603c1040840d9a940c248142610364031411030303001d034030400c0380d102c540a900308075948548580c0c4c007484048000d040b00c0d081d002d01919503800040100280750f1003000c90b0101b48500010806e440200031400703540354528640300402010400001145200300020590318420002c0880d100350303684040c2c006030004200a007103c10f080c04800c6403240c8000359104d445a1351401c045907a032419a6030314402c1000160441050455150601b0440050104202070304240a175102e0000741c49100e19505080100d058031106030804142d007081171000080140d4600c6400c03a5082c10419110002d015003a41540034a041c02c3e90003c661000308030401d170f803005803079060b83d10071502001c51101502c4908 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 137075359 1250 137074109 137074121
    0x30f0d1701171504031205010e060102070506070c06030b19060806150a02070b1605030c030901110607090e0c0705033f0109020c33130f0f0c0902040618060201 70
    0x900c1c0f5001401c1d0080c1c0c4509410503030764014000e0070446a404482c8003c602211026481460703000d00784028444250380c10b01c0035034002c0408a590a081404ca52178950f23500a06200341c0040c1a62000070713110903201c2040d04115066034007000c0004554560010300601400c070383c0c1034811501c1c0d28140603056030074000c0ea0710003241c1c0c0c0e000380b0780705007408080c41c959441a480034100144000340b80340015400c000801ea4401120007860300d50491a002401d0841c0c0e200c2c81d68130a8001c0130800254540c800055401c803070740000c031200c59032102c04051083d0700c111440a401030100080109040ea02207802c06003031811020006501e00c03103500e0b012880c544803a806204a02458010000035085070080c0040e810440c003a034003003818030803c00302050008041c4545603c102d500070300402419403007030f503030010340340307010b407a030403803541e4607a48201d54102000300068900c9446d001400314000420b00904040e401c11950f9903124000503095800452400009060780f200200b80b0074030601840d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 137076609 1250 137075359 137075399
    0x6030406090516152102070c03120903050a08090d060e0604020a06021b120f060f0109110406080403031e0c05040512030408030906390606010305060102061302030f0d1701 75
    0x360051312150341152012000204001401014003540000c00312520003014034501c1181c149140514520b0503130884010199a03600340510f001d001c00100b2008900d0b6010680c0c00403003180d0f030b42120b0001407401c0315200d10241c155840d11402d1701e480200021118060703030003103928024003a0340d400203c0e5986801e07044444101448078038642c42c4c0c240011511200501035040e030b03280162400c1c42a02c1d0040440d402200a15244010000c161241c81004080850310408510b0241003980150002001030802020161b8a02c0c14400711000c0c0014040d0340140280c2c18440c1c0030a108008100c0d40250040510801d1091510721000c1c0c4004100c400715060000518100000c0308200280d9812030840001000100035032000d00004c10314a000104100c11210940e003c8007030070003450640001c207464145441e0609004e12030382c0000c0e00d05e03840f02d80390041d1024241244003090500050f040050030500c1002210610290018695951a01d01c0a00d1940b01e030b83c1c5401c10a00b6504001320 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 137077859 1250 137076609 137076629
    0x50934032f100c020d0b0403050316050f0702130912020102040602100504021f05071505150103090b040206090f04051801051003030c121b051b040207150203070e06030406090516 78
    0x400c0190f00030124203503501c0c0002d01c050204d044c50388810f0031804081f0360450002e0740000c2013140d00c90407071290080c1d020091518a003000c64000b1407001030b22800c10301030b01c200f1540b82562311001d07840c0c014105580d40841082158420110f019010707402600481d4054011001e100d110f070340e40c17442154801d507001858003191800114220300c50600800c00710081000c00c2100c18041341910b240d030381c0340c903600314400103c0d0301d00f024000840d0b6205400c081d04042c00c210f0702d10081090008483e4010760100c500c81d5564844d00e00180c10a5685240b95405c0f90804040110070000161075540458400c07000784501e980c0e900400c0c140312000d000c000d010412603804140810b4010180303004030034181c01e00c00c03c000c0102c030034120948003034030b001c444036880114460410140501d135040054002d41e02903092045c00d96410000041c400da210009603800310025240901c101804000441d010302203a03075a0515081c1040580080d00c8240d0b41d038802c84581261203d040c2d1404000c480745008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 137079109 1250 137077859 137077879
    0x30f050c030c040e030f09031204030b0601080a050412030f0b13060f140a0312050915130f0807051302090406030b151f0804020103110a030e060604050934032f 70
    0x12002c81b950041c0f800076416228922000c46407001181c020405540200e03c2c0c0895071410500040407504010094403809042000b4000000d0018004241562003410301041e00c0100f01d040f803004146040e002030344016a2400390040c0000d0394408001e5914a602c13408040391640c41100e10131041c09445030700910001000c0010454181410540c0d14a07490030510382440320740084d0801010141c2040c2068002490b8007080d503602d43c41034001e0440448071030030146004c2001d80c544005210f11030241c0d03007000700482145140d50449e600076800130010807240b5160b0070843c0c0550000c4a13040a83d61074000000110710b48603c003440c18600300c001c00070040020700b80480304890080c004a060580300c007040110284540d010300720858181c0d800141113030b22000c00d01e242c44e0018010600452818051010030040450b5201909482e841a54544501c990528170110040428040c199198490202c10800e10342942000520a404403001810404c054088a201400da6003580018054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 137080359 1250 137079109 137079127
    0x30510061707050405060307050903010c020106270e010e0a020109060903080706021605010e16061d060a0504150f030e0115031112060f06030607050c0303011e030f050c030c040e03 79
    0x881c01d00c0d8009498500f071400c0079600c002140c42c542060300c110340454400b040114944c1024442c010107031500c0e100038840d05180c4101044132405114100c40640032084c40d074003a01d91990000c401c0e031031580300204140c0d880c410880e6214411881d00300d0000e03041180000784944620075090642e600031400514000ea00d0740d03001d001303510003510781d400a00316024410200d8801c0c4603030720b221040d1202909005007064017041c03000313685800c50800d01460310a0f581c04648403064a2440800c2038860030b54403c50340c401990345019540c4808809040c8200052030254410301346102c6142130f840c2400f05040014803c0d00760f0b660b000c28010000c040303036810008101d050407400c0410002604000c40008030110840c14001e040761103041860340c4005110303540c04c0401000340e119002c1d291180c2041c5801c80c400d600da10040c460441440c849040c01e0031040b005100d04c0d8019540500351081c501c40302c0c9882600c1c0c04000c0c010501c04d006021840c00c0600b0140508000040d40360301941c030707140000d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 137081609 1250 137080359 137080397
    0x210050c2a09130312060305030403020603100302210715020c040c0909020d06050f030f0607080a1107060f0609060f0e0a14040b16020a02010c030815030601060f03051006 75
    0x1005505412081d42248400340c0e4a481e8407190150100c0d0690540c0342c2d403681405401d004020701500a880e02e08a82000443c40110594040c0c0c0d60403034041745c2d00e446a000c000c11742203da40004e0740c8000751b02d81c0c507007008206010a9450032454415103052640d1940a0885820740045510143e00100001c0c4954a0194850b01a03c3d1841c08c009000644403400d603022070b0011040c6515095860005201c02d10b45981130302e421001c02c03402040b0703400181d480b080d15500080c0c03105003030051080c04910346038032030342100600c01c03414030712903403119914140f1502034401c40c0c100400c04c5151460204807050360f0700400d81510b00741c0e010307000340510b0180e4980380d038080103081155a41c2d0700c00d82208000c003400600303405280240045021804e00c1c5440269002300c03450660207561003e840c000040c1d802039001c012003501400c04040384c2d6100c0107520301c2d02d0086510b40e5414090740340042403003a02b11020700d4410304155820042541c40d01c1400080c440075010710000b1407801c40000d0078107507003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 137082859 1250 137081609 137081653
    0x3060d02060706090b0108070501020106090c17090102090303070b061f090b07081c0c0908030702010c0b1909080a020d0203090307090e0a06020d1406180708091e0106030210050c 78
    0x45402c000401d16955110802004000c0e0007e50030381e085100104415070342409010b01510301ca2a0401440c601c8400190a044501d0800a40c0c030b004880016400c21081d81a9039004e8809025079690307000340c1c1b0f000710b40a40300b1502c840c071842010440c82048082c44680145100494580000e801e040088029482c2c001c028110f0b10a0010004121880080400e60303410150302a408030700c000e420040a00394407816000100241c2c03041c40201c000d80ea0011544007410303000b42a80104d500d4116040707880501030404071202900b44540b0108100c1c03c5001407101c1d00c403541c299000c0d014241822130703c03441100f41856041d0f11aa1091110746100d52101a94043c200100d82c12075400b80e0b0781c1d806031b03080206075142e095540c0880b10595241c0044403039100b88110b40081c03224240703140500075510050480c4003089030b65400100105000c001074624558100030092210b448626858041c10082c04120301604085656040f81401070042c2c0303520446d050060081c850540340f50f0200b40d40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 137084109 1250 137082859 137082863
    0x90103080c010902030a0b070f051c0c1412240112020c01060512160504020403021003050a11121008030a0c030c02010504030602030f0f090d0918020d0e0a1703060d020607 75
    0x16031283c0010041c0e804002502500d40325000c0341500e4500a580a0700348040717510b8910078800100315400c105050281c7e048010381030354400141d07146c0056400c455140d010310500c103603001c0000310381c03502442c0c7e410f030b0ba0710454200c48040070b500107402e00c0012540c8000001c902181c3ca15820710390380c00302500a49581c2c0201400040c8407a5201c0000c0c018440c0724484807140e40011040c940703580401c007414805008141d03001d6207410306e19408034814200680311031040541c0d5070701080e8419072a41000303000181c2694211f44950303032161801c0780b40c00c00340c03000007039000050400240e00c20048180d4881010580390480b0155464400f03440c0850320140480c10010200004400110103102850183c03104011809540c50546180e07014003001500c0e130f0f1100c0e441074802c440c1c0654400c51a0b0156581910220700c681c00741d044040280c05069504112103007010758040070008000340004100d40508003106186242e503041003880d20080c0c034815041100d02d0044c00140c1420001800028 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 137085359 1250 137084109 137084111
    0x706020f0f07060c17040f05150c041e030f140c041e0c0c230307050703050a12090311040506060c0105010306200301150c03020a0b07080105041406090103080c01 71
    0x80e030411154080e0394051014000184004503224080c410365200b030003001c1c000c500780203c3c0c14a80012240710340e0001407004082004401c00c010400a090120a0380d47c0a420507403072050508404489164105014200540d100d110002040c4808442600100c2c0d80158101e1b0b001196a1200c08500d20500840c6400d40308240654840703441d68411014110b00300118429040c105811642c180c0e084000d2100402c27050518480104011080a011136280b41c00c1d101d0004c03d102d04010300b503010f00d100160140c068900f0000c184240804c4141c08240b042000d1002e015078000c0c20b640c00c901038000540010f000c68031071243c0b828154401d03504107100a099038100023140312002d0035200260812171742c041d11910003000e1140c1d8400d210342c4040030810590b00b03541c10084184c0c0844072072150841040405035000c02814000d0128185450b04070f06d0510091070081800f401d101420300c036480c010382c54207013040d003280d014511003402014028550101646151103200f8240c103c00810701c215 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 137086609 1250 137085359 137085367
    0x100501030c11030706051008031207120902090103061506080c04030602070602040b031320090604110702030d030c0206060409080a1409040606030b041103010303020a080328020c01060807050d0206070602 89
    0x1d1404101900040d4458500881d051507d440030701440142d41c0d0100c03005a0040c4110404109041e0500ba40b00419142c0031000da11940d81031806840c402c24041d411039072400001c01440015000081d52014054015a0803699580101c62491f0f040307800d0403050100380f005000140c115002041c1442c0034050160805407a5000c01a50754400d5843c04a07030344e180008902005170725443e40c083c881000389840a1104220080340c40b06c4e100615052040d1340d5421640d844a9005041c1d030140b51b0080c040b903400d461032000c090010004885100d0142c43b88500150b40d510b41809200807260344644d185052002002c0e09882040180e041520200e1060001d00b03a1750311244285001407413582e40c0801c0f000c24180c1480101c4101101070030700c260040005002103900080c6041d50306903c07038407560b40c1e42d4a0707066114500f15a407101c41e88803104110888c0034400b094020b801c9408014ac020003040f555064000e50302c01643c814107800261503402007000d0700d80b000160100c80d014041c094a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 137087859 1250 137086609 137086637
    0xc04061214070e01020f07050a050d0609050f030a030e0c0a031509060f0204050109050402030c120421090503150405100209040609020f1b01020a051608070614011706100501030c 78
    0x80c202044450b000040c1803814101255a410000400204900304c05460610300300008510042818000c081c09101010060740400500e94043c6e002d5640103c2503031501d0b40310948058072070b0300c0700f2a1030000904001080f07011a101240e48104407100a1604041070300e16075501245803c44103580c81c40e265903200e9400401c00c980550009a00a220f0043c2d441d4100000501035070303c0c603085580281d10520400010a482c64100c034139244031900281c00b17681d1030b46080e03040079142003031540c05030031f009020780c40c81c81d00240c412054460071015a1500c00d2280400c0641d800c0444024086501406030001c241e48164001d000380d41014001081789519070444005a03030003154200380002c00003038078000000785540d1050303500c25004001d51804145480041c900e0044051003500c2c1c8001d900c44000700034400044403903107075110030184070b43d0920300d0340041410401d100c2e0209000c5566100d007091207011031460b1084696001d100e060300e0505004400410040c60040305107c106504406 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 137089109 1250 137087859 137087891
    0xa1d040b07031d0303100f0b09190b07050102070b0a092a0503060f01090b01110c15070f0c03030305070c050a080d060f080c030c0a1412120c010f140c040612 69
    0x44211000655490505070341b42c0718030703410503480218002c0751000c2c24401c100581086400e0480b00711003070024008500b8444840011603448402e0138034000890100f000010b4000e811840c0c080c2081420951300c180140d0150745812030000d1000d00300072407681800110002c4954106405045c030f803030030750b1507a01003403400d4002e079149180d115000d0010803903650903024410400700b084c41c04a000d104a1014240d5440e56550302c10f00c41d40700303950110308181c4444180c80c5070b10340041c51030301520441e08200710b5004081c001900024100000110550f004070180c1000a03441002070030004840d031601c1900341c10030044d43e4007803903c2d85000501781031106c40038800780824201400601c801c0404041c40c0214580c1a9401120304140821200125a45000d880041070710a0710392568446c0209040061407810740d40f25a00125014500b80c0d03056122015851031660104205c50345440c0c0c9040e1180100c80785000020204028461340b841604a10174a00c80c1070350100d651007031090215 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 137090359 1250 137089109 137089151
    0x2010b21060105010e01050a030c020c100c1502130320090115090501080f0106030507020a1514060f0a06050f040503060c030403020d1d0d0201090906090203060a1d040b0703 76
    0x121029040c0325900c0c0400d0521000b0300400b024201074031400014000a0094040c11421109055503090b4595032280248115608c20000502c2c02c21490b0040c078004d02181c00c14a015203611900114407200b181891084801011626240401c0c1074659542c150300d4803d02003a200155811090808a6846100a4501801030b044050041030655140280344508550001c0d0420000b4402e101255011096041c11340c0d0940c0b401152940d01e00300140e00d40344100c1c6004151981502d2555130700c8400d9440040c009070ba440302c9403202c0c3ca68004100280d8015240282c0c804071070042040242d00035001002c586450304041402c0940da88002420948201d6000e96017250010030042095410b02840039a0034032800d20700b010b0800c03444000c070600c024454503405032100d01820019a030080b1b41c044001c2501c03c034144000e91b21510100007a40090310118090a4180c801040c000f008800b101c0c42040c11821600d1295203e8480b0007412a01400800c00d02d50740c1c191184060606518036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 137091609 1250 137090359 137090389
    0x3070219150903350a14010e090312070f020d02011b2105040302010b120303091b0111060a060f0611031e070515040308100803030f10050904210f1e02010b 68
    0x100b070582815000c48943c05004004407400c41c42c000e446e0441841201e001815516003a80d00d600b2551124240c0d0f256101d420202030070b80d00340008000c5040d601000b0701c148140d5550070b071504034030304201c00d0703081e18401404c10340c04410703488081594070301c00c90600403500c5800e070141016078501038450f07040307841c02e40b0280d00503511803c40c044a801c101c410715103062503160085156140440c15180c0b104083d40802d03000100b468510701e0f050384a80701d0152140407890030f442c2282002c0a540d00100110302c20144502211400080d003140140700b1a0351404490000d1f501d0440c400381a401e030800000c00700c0e03842010901c495400f0810401101109907266000700701c080c200f504001d840d412000740020080c0340410350501c0180d50100c00d40e40c02a48040d004140c3c1e031141c000c1d0000e88511500f00c03942005402041100380190b1400110416028040c581000308070548202c8154814280c0a0042015651034140700c82c10308034541500f401e280700020fa4043c240c00010310030300e006486 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 137092859 1250 137091609 137091677
    0xb090a120506060a0f050d06050c1c050f090303040816030504090c080403110303010b0403170c010903210513110312030a021305040612030503070c05070b03070219150903 75
    0x70070507281821381221024003d000175030894149045d00007002040c24031001056a42c882d408220310b100242c5c10717a40900e4009c101c090040210000090003010110780030483c2122200104080c081d0100849010300d0b00050401e15020044054019059441508900300701042200040c2003482d40315990405200740d4920580d0304040c01c0c0148018035140300700b41250820001046000e61000840b400c495119442d06500750060032a003400c2d00076075080c00400c0d42001000c03801c1651090303041b40f0a440c603440c0440c4520041a8090031604203c502201034203404803d880070a80e481c5e08410741e0131005003111181c000b840c0c01a1680e4205484882d55142c0200f50030b1a00125104800c000d8001a10b08020709031516640928040d0040c4000d02030000010200f9000d40c82030b0700d4500c21640000865542c030750741d00c595a0056001300c55040060040c14101102c442100c9421020a900b01140c401d40050001c3c816004242e0a4400c80c24013141c40f0f01c950312055140042000c50340d01e00c1c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 137094109 1250 137092859 137092861
    0x10204031a1e01090f02070503040824010f1a0c010c0201021c02030402090103020105030c0403050a0f11010314040b0705040e090d110d0c0605060103090f3002070b090a120506 77
    0xa0355000341800361003560809584140324818182c030a42d4581114805500810b2803c15400c0c2c40703009201b800d0340502136000c0041c001c00c00307040c005002028410724100c0180440100801c0c041e000c282070140c2a42030001450400401c403200c000c900c03412904d1841d0a280110442000d802c5500a901d00000b50350042080f40d0030400b0410a200c03d680c9041c0b0941c9185440d600180360010f05010007810705c45c01002160755120340300251406150302ca003c82d0340c07200031800e01e0454144c40a0046926030b4084001c003959500c6806403107400c03014403032402c1c510340300c580c0c41c2cad28000001009001000030901002074000302d1014018081c0c401140034003090703070898000818059031280002203941c00401d64110342c0b42e1110041840c82d03045040004e95440b00e0004801070142c0c4c480c090080360040801d0300500c403401c03841007120400c0501000040340b024101840070741d0040c001c1c20250300b000704204990400b400c0207140d6550f00406a0101545510b55010080c403002c0041e41c50340d20500c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 137095359 1250 137094109 137094143
    0x1101030f020316020c011103040e070905030f0102040f0f0b0304030e0f0d0c150503071e030f1112010e071d0a03020607050d020d05090f0607060f06080a03030b180f09030c01020403 79
    0x80010b440001d402e11f050b010004d10507125a55900c5680300701a045000c00000508041c130400180000d001e0040550300718480e0008964081d41090007451003034840b12200190707410704800038400b1107010703404050541c0d840fa01d066a445c100d000c15103401121340460080307a0307030b9a0802207020381d1140395180b03102824416400c00e41d5030b40740c02e6001401030070020f200b00c43c0d8205860350a1a000510380c1c200082855004801420044560451071401c100001240c148136001409406900138019a86aa40c401d40c00d081c02e4800d917698004620308080c0b00d80d00c4c014008400c994403201410641d141070341d83d8089034190b40f00b61700640c2c0c15005899000d039070365818082e170180e2102e1460224103007005400001d000d09820384129124400000e00c0004021003078201849100c1e80e200d04003c005d43d02c88829880308104082100080d05c3d2014861152801d40c0980602d40c2140f20b00d1181756070b50750f850726801403014120320340d00d110a01c441808010240001c2010b103100e00c0703040034128110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 137096609 1250 137095359 137095363
    0x50a0f050a0207022107150801060e0108071407050a0206040e07090e01050109091a030109050f01060603050c0912071e0303170702060a02030a020702041103011e030f1101030f02031602 81
    0x40c101c4000301d0700400c01c92003d6544c0b4003c0e425a221003641e403207a003d28254810b8034000590b0f0240314030603010280e901172242c210541138100c8001b034880041008150004541040303040f80c5007004508650360035414528101e01030100c562203030044403501c090300e0700050200d401c20b500910000c0040010405202d03403020307000c4000d00c114a440419541414000f92008030103004020006da07035100100c844400400814941d654040c000300014880e40c2046522828800c0540301551b080503000a900e5100c5d100f4688034400c80b030811070070038402404000c40180c01108912051044c040d0228100c400162180b0443d0300b00f4410641031465071130060409001e5103c2006c010503030b4410451606d40105083d03030710141d642c40050b50303903440c03e124000070700407100c001e5017251900a0201c2d22041c400c0095040e04d084081d42c0c2041e01d445c01402c1c644504c54000200541187ca00c03010008203012035608004205060201310010085004e0080703070400ca0318403800720000b0491940207501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 137097859 1250 137096609 137096611
    0x52113060b1005030a050403052709100b04170102040f06050717040506030403080a110f0705061503030d020304060609090f020111060907140303040f030308250903020402031009050a0f05 82
    0x5840d01e074140c604903107000d005130100514240c6540e84842c0001d04152040342190060700083c04043c9546880e600c0b03c8206400e290345003800b075400000402d001c0c05a080500c41103800143d8520301c3d00b402c00d0300980c1c690350035560290340da40d0284808900491001d42c1080035100c681d49045d292007090a00350210101030040040010007044141f0150701e80c0340c02c4030341c46605810b21411a13228030801900620000b40580b02866010803008652580b9900805609001d00304407041d03521000c8060440740c03c032a6440b589a44100820506008540c002c4e652140c020040050100e40d80c001a8080d6101502c5c11070f19250b01407034503005c560300030308038109100c881801040c03649008280260386200c280942030040080c031501c049503560800c103d03400f426032559070030022a0b4a15000c0d04940d810b9502441052105400ca20008072506d00340404a1040d03445910740340c99a02400001e500c081c2c0301840f071822107903000c6040c00c003038081c103401580c1e00c40c4000707a640c2b55224140b0840e04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 137099109 1250 137097859 137097881
    0x1b1c0e061504021819090216020a14010f0c1e060b18010303090506070204060902070c050102072c0a0b030a1407060e0d060b0105070507060e010f0c0302060705211306 73
    0x100c14840450182c3d01082c0c0304d0729920b4180d54140224140c081a04082d035060340c0454041400001c1d003001b0b4a41480820304200d00c20340d200000c0986800b40119102a50030245000402c203400904c1034912800203801701034060500d11044007024141000c541ca00f56030140c0c0c01030f417aa4208119810800511104181c0d03040a514003541940d40040849440c2c0c441c6a01c07610700030490205561322030384008001c0031580002c546c0d4561602d0301c042015224400c1c03d002d8020385000041e4000a00c0038101d15440000d540101c480c10019020060300c8060810003c00e035540102928907107042000c2d8201078001d540d601da08200020182d49040302c2600040104034a5003501c541c16280d02241c440c880ba401500070030710b4107030840100c605010700f000c0a8114441c0b00c00010b003c0c2d8000105812191082c0d0384d140003140618070130b80c0c1c2d140c0c0403440140144c0c4484001500f285c0301c0e402404200d199112031020440c2d80480b440c0c281c80087d640305230041d074042d0b0018100a204d02c10304034085 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 137100359 1250 137099109 137099111
    0xd0f0c0e011403060a2d0603060b0109181d030c070e01050109030c030204050a020708071a0a11070b0919030206010503010507111005070e0907030506181b1c0e061504 73
    0x440c00402003501ca600241c0503e01491b11151a5508005240045000c40302003080701c02c003c81d81d6241542c00b40015200503142149441d00380660f03544103078000c40a031040003240312419484000031000810040c880d4480f407a00d048645090050140001d00705c030700c0c01c10020413030642000030840b100841a40075a0511a200b00100002120304402e2021039030112800100d5035500074074940070784603400008004802c0025244100240b20015001c000c106408002899540303d140300308460806154414058090107900c00040c80e6409240c3d009200d50141c4044807400700707500225125860f0200c0140e005500140f202c0d040034030800740c0c0691545040140311451005050326104000328020b0466103900025642c280210450542c50501400b44105480c7c0421f00400500080d03c1a9114ac95400c400c0014041031081050086000b80c0e9540f805046001d400082030f803040d1480c0940d9081ea24007000d10030340621802101503610f0001d0242842c0c024402e081d1201c250b40c0c210722035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 137101609 1250 137100359 137100389
    0x50c010314070e040e0717030706050a1103061002070b0c0114061005310b040303030f05010b040512010e06040308010503070e0103080d0b01020109060635100203060d0f0c0e01 77
    0x116808185082101d00a44d000504108248419410000180c00c00d54200c3d00c2c07134994404d0000004010a41c05005800401094a580303146c5030030380b00c17058004a00b000301031010820034500342264a8001643c1d00444038a580d44141d40052900f00c5124001e903a55540c00080c00d0242d208102a840942252014002c2644480213082401101d400240c60b00a102100c940405106c16003404000b5680c154484540c2c0c45000c908950312030700080340003900b00b140b0704001140c280503c90598281c521700d81e09040c180000e0180300384240503285840e40d25841503c0c0403410910145018900954035455290304080506141c1584c551250141c4d40328000108042164071b016a21284021500410888001030040340540300004019015074640800003451032542d07200c9a640d02010840310398140c0b000000200d8100013240a1045a00507420589900040c0d074003c5d035100388014001e01c49d045540e02c0e138414204002c982100c0420500702c081c01300b400d810340682d00508008100c0b00034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 137102859 1250 137101609 137101621
    0x1119080114180a02033409090b010e04020c0102130306090203210d0c05040509150f04181b080307121706010e01180b22090b01020601030b1b07050c010314 68
    0xb50000402d0308030083d0b80480405c0100f18035008070046034401001c03001d071900180c03802a440d40e04000c2c450300442c40c0e0540c005500708150103825140e1805071601100300a400d01400003941c03000e00129402c0d542007003440c2c8a5107410101e800034501484000807018144e00c1418905050240c80040300810303640b0318620301e41000100e030f0120405403404605c2605011040c2c98074026600b009510504003020007107640340c00c0a801612050460b44410118400c03428882140c103c0b1b0140e818110500d424a00846c44484065500740205034800c083c623075850070f0b29804c6402c112000c45503102d072100702c0507181d940800102240001e0701a00455030504030006001078101d00000c030b051000b4401104038150040c0c61210042601c4003810b5510302118011a407844031900d1204010701d11010042000004342c8500c64001c00306800610b4682d08546490440d0303503009000c64160349402c035190a4800024002d00203c40c4200300502200484200241c2600c00390082c45050740c0310b200c20000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 137104109 1250 137102859 137102899
    0x609060e0109090519140c060c070303030509070b04030b01030605010f14042406030c080f1506070602070204020a05070605130201090b09030a05010e060108060a05090604061119080114 81
    0x1c1150411803001500d901039103015030800c03074031a07010040c0702c0010f910201406890409a90310700640c0d01501c0301340c5428410041310b03024001ca00100791f84450300610001c0d01907805240c0003008902140d8a030356484d45480c00d00d03801a0011181850710100410421003503009250150002c41c1c003500e40310381803080c40c80710b11084010301c0d4403440e2110312a10b00c141c0840c22100305e0100707001c0d11703441c0b90751910405006002542c107100d000030150382c0010901c10b95919154000c82c00040e0754901c042c000420000b81b41c1100105549041d400c000400043e44e403480104904410764075001d880311a54140b100407500c00610f2418941c52050320400141c0e40146a5010f560321100034a441d070b2901d0380030038a81071102100400940c40c004100745801030000e1010f0403504100d0446050b6510088260140d64060310030342400e0b4042808540042c4482c0c1140b40a03034440c501150400860a5600c0302242c01900c0040c085054180140310070070701d5000c4a001050151241e8003640a00143c0b42 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 137105359 1250 137104109 137104111
    0x709091509030507150c020c0103090503031f09140a0c031407080a020c03070f06050601050a02070b16230111040503191106030c0d0507090e06010c050f030714010609060e 75
    0x22a8555510754030400c15008000341d500d2250030103007401404030f2042c000e00082031030a030030401502c15628403501540c41703409140d41495000c0040c50454a44050752001100c5521112290840c09040800d130710000e40f048040000f9459404081c50420012986c00c03220030022480805051481ea112500c42d03000c102a0040c2507854180e10726613034050040004d0040040b10b54881c0070000c1d5003003d02968050820b4100e020796010841340d00c882006403003c0c4156803030716001d070b0000e40b82089440c2094000d003502e1a8946403c0e0030005455849442c81c180094000240c0003a1070b4085210401c00d2240b08407400e040003501b441c1606100000e035a91219052240c031613142c0c842e5010402064044240d08040301414180d228103014050714a690010203c401d4194a40b10010b001c152090003c00221280300c3c24004040c0c0b02c8000450f001440c6105c280c529109203440c10404290801c01410218060b543d00501e0400da41e9041f425105240e20008425042c11000e002000c0340203021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 137106609 1250 137105359 137105393
    0x5070507032f070f1406090310050c070b010806160f0e0f04021216080f04150b030c100e1e060421020d030e090a052503090f030f02070909 61
    0x408000c82480c42c454414840d0030508030010300481c280050010351a0300c01d07000f610308014100880c0400c45d0180181d60155207021545070713001522074074410703040d40d00940d00004944000c61601082d9115490342c00820b1b0300510195014078100f1044d60540c1e0041c3c55802c2c80c51070280a0303060400401410240165203d5101d080c2840700008503998560480d0b00b14281d000a218192405445200180c03102c0c0c08044041000720000800c860704584106104590103602c004040040401c084010705801601942510a0034030340581030b034422100720200782c495502c50305408142d80234003001d0150403a4013150020740159101d429a54081500c0c1506c42403084003103820311140904040b2803a2210180d0403c500d941240c09042d8400588806250295a005031a4941e00340c40f41c101c400865905102c041070541c00c072003c6001044c000105c084610303020039203140d40d403203150114080140c100c003c9142040c041443c184c0500c4150000c180b00e5404000c803040503102e640700b903140c103140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 137107859 1250 137106609 137106647
    0x40b0601140d05070f02060907120f0206090d060608010f09050613021305010605180303070201170c09030111070302190b0402220c0903050f030f040b0307110307080306040507050703 80
    0x711056803400c07601a1040746149090500280c1032511018040084480b0f41c600140078100c00214803200024440040b21044001c205980c0781c3c0d03440f825403040c01c084040340e008004001c51000c5540d203106a002c554054180050064035219203242120754010100da03009042c0b2071000003040e070204801d580903511644c040208007407031001514600380b52002c080b25514007400444c0036603004004e42501045030f01000c10101d02d0030205503403030090a8000b03000031269150341c000700c00c11808554128542c1c0e44080c2c14000c20301e0000e4291408140c48190041000c1090700030726504111068541d06100c2c00c0340c05504003900c40b01c80030200200040e004a030080c0100c00359440c0e130854500c4140064404120030040c100340181070605921081d10248100c9030000740c840000f03c1112000000108000d150034034042140115410060906051041c030300b2004051100600c0181a40c912034410142e5a1030400c007000212200030f000c0780100841406100c00094002443c11100405020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 137109109 1250 137107859 137107877
    0x30a0803070311030103061a010504081902040b0604030510060e06012304051c0b0a020c0a110f04050408031006080114040b0a0f1205070e060a062102070f050114040b0601 75
    0x140d010308440300b00f030100003038000700020a1040542c080d03441c903481c034140f051400b01e5541c011905e5002d540580d26180c0c000707041c001603000c035400408090900c080d101080501c04100020060b400a9009550382d40201281c0c50190749584107080c00781c0841801580c0c241010000248040c4100c401641ca91551070f4407c0640d5084d00b056500420000b0014903000f0504400c3c8140c10301244011510000c0310404162142c10754004d850314070312004003e05a070503c507103800d80c00e03040c40f004030350304503c01d000c110350144c60740c0c050588035601407180300340e0760f04000e083c0b201c200360181e0083c41000218401030010710100d0f6240210180100c0b00400d001042000140c1c0a50440d40860a1040170b120700240c06040944441c80860050003516101d43e03a42c240760f40d50301e00c1110801c5cbe01c150300010a100e00383c010b4260080100f02115145000c6840c40b2150b0120b0344400c5c002c1d9010428800d212003042001d02440d0780f40100e280c220105e50a099640c141d1071207024001e0707030502c0b10b910 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 137110359 1250 137109109 137109121
    0x150207051905091527160e060703051903020306010f02010504050303060105070503090a03110415030f02150c010c0203040e090d080a020c0111072006030c19110f07050102010507030605030a0803 85
    0x412101c0026070041203082c5d007403c0e03907128903600403040c1408400591100002008031160044003a1500c20584400e80c00300042c03c200704041d4000c8108405025050200744100041030f02079603141c01e820b0700c0041e0f40c0d00b0100c0000d849258038095040c116070401d410000090300107c10740e60499400e0078082c1e1150b555180035070460050084464000059a80010510007130b1084403034451401d540030460350304094100c0940001501011f40030101d800403032001814072002100044009003856030809038161f001e1404d480820113072400692012900b1b00450740d045e003a49812248138001020400e414010280500d44020916403941d94040b0341045164002e41142d000700902c204000d50740c504c203141c002d21a4821741e01c1021003544c007116500040c2029802c8030300500700701c014941002800311011500482c400c01502c02c0100703280c17845100042c1001400d01884900010b0320103542028002801c40304020848000c046c148902040035450200c1d90b40c550039004400f5a03a00e541e16 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 137111609 1250 137110359 137110381
    0x204020405180f0a020405090112031b110901060314040f03050405061209070b030f04080c24040302010b0f0604030807110612010f06020616081b0415020705190509 72
    0x55009682000a0400d00c49110140d82c2e2214480c101550164a40fa141e611080d0101d004a00640c1e800039400c0300144117140c100c9019441c82ea04c170b0f01d04010560401c030362521000ba0034600440341814a00c01c0782005284c03c040b0a8054201c1e0b20382000320046012000d1003690014001500000d84902880300341031285040b14003410f80a04890303030341c24451800303041300c1600b15040c45182c040c084c3e01061080e090381c00c0300d000e6003040b8082082626203840300c480c1c1d42c4c804256112544640900d080c4003040c0810102402079101c14414030501e00346c10041d007500c11400c4400d204100f40c420881c115a10481502e003987d030085241911400740b440e00c0119500d8170302183d0b1b484500842d00c5011410a0f005131341c107842c601c911441c14555039032402e03a0f441505444164030b0f19104440f21080c5485034182c194049211002e100a5510841c0300307030705981c0140c20042681d9403844819041030b404202007030080c08180c4118458080313004004240e80300500a05100e0b21648011619100c02 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 137112859 1250 137111609 137111617
    0x3080615040807050307140a05060315130903080702060402012c0604030503130e07120203040510050903030a0b01050c100506130f0b040612050c0402091314090c060a0219020402 78
    0x400c0c0025a03486480e100035603075501e03031842024441e118071700011882406016403400d90207c0075104061580c284000c100c5e01d03030001403080c0f4290500100d000c030156250912412203042c035807400107921313480d0308005100d241c000340b800007591300c8a400d000042c0d900a0806001007616070784400106903090302d041c0c981c969050000e602030404a804801e1007000302c020086a4441d115142c00c4a95030389a101500b0422503050020501900d00c072005a03220f034004541c414850b5094581625440034614122107003554681d410ba40040b0070044121540d00c10140b040000b400d00c682007a0403100310940c3c1d80804500031608540301c0b0081403058542a46000075104c061009021124503001214010410403101621941c103201001410b070590b02c1003012096002070140010044d40014030019600c020341142e0044c0480c0f51014401c0058400d0b150007041640519440b420308003441071a01e003062040c1032048800b00420181250000b4903040c960780700301e5045000891900025000f405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 137114109 1250 137112859 137112889
    0x604020d0509071e060806061b0a06090203010609090807060c18030812060906010e013002030115180314030f0c0c09250c020406050a06020a05010f0c0c030806 70
    0x2041c14180041500080b81240a03034550328409a4800800b0503492203000c0c062003060041007140e0045441c0b820444021b004421003000200000701c542d82c0041d1070509600410307130b0b1855540341a042103180c00c2c054070006245d40342092000030074603181c0d1100341c4a0514000c00c05030752200c09100c49030103503010034a00284244001c1c40c0941e00c0c10204581c0d88860307818614007901d08006104c0d8030340514401d0203004183d44000b00500c4060041d11154030340d00b00694118003400c00301108a4241161800d9020905000f58980d454110303c0100010240b41c070f6070500c2415020312000d8061785a0407021641c000c40140740408003458410300b5440381003580498040000f8030955009400969440340c0c803020b65001c0f002c0c0d139900203140d00007014040e410346204601e55a1241d020f118078000d5030214002000003442e1541c6400141c00c501e2a54480c1000d82c020340000c0303003030001c01e21600d042e994002da8280203040d28550003e1462640810040034000c0140c0850015101e83c80301080c061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 137115359 1250 137114109 137114111
    0x40b0402040e1518130317101703030103020d0f08040e100e070f09350a2901030201051c14190e07150215010605030f0105100906080604020d 62
    0x90b1a6255180402021a60302402501480c005034080c20011034616540416489000c004c2e1201c00c890108440003810542c100300848a01c1105215800146401015501a803002540c0f0f13003800107400c5203a040010129070814001000940c075111a461001540414000c1c075403401c615020501d4007071034004080e0ba00810782040a40604100000d05071032424052a050740e40300c40b41106d840b080b44440000160400c1030401444003031114000110260b01240c0c2501c501181c8108012414074001c0f01d00d0ba48905030b0303003051241e07280d4969080500c42070236407010720942100701201507040c48000d04004000403850f04284001051540c1640d007214140000160140440c3d04a00c1c03c0d1038107180c0d030070400c0c410000746000340300c0d40705080b900c04040d044080c81d001d0164014481d040c0c800c02135004509103801c0b103103000d0b8040d5000e80420f40381c40781c0320708010380303256a600700580005026180070440311103060f40010b0b071034003220300a1504210355900c10021030040c1c02050030068400b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 137116609 1250 137115359 137115367
    0xf120a0b0f010306182d0f05010c0305180703020904060f0f0504060605010e010206012c0708012102090f04082a010b010e090f06030a140303251409040b0402 69
    0x80000700e80d01604036401410b0922000c1d058a046a003616a00c1000403d0701217003041400040c0d2040300b15101819100900b0a07029026840700d8071b0355004510100d442da55900e482c0070361107416115171034000c00140c0400c1100d2980144180c0c0d00c00f01404080c2c13083c0d4a03100002c0410101c1e42081400350741818080c00546410b541640242c50169011201c00341071050110311540700303000311303051804164000d00d040e0b4a01141da244032020700003981340d0506800724581a600d596030105002d092545c0d16104a17625040d42c0001218454418031903122101a00f500507035078142101342c2140340c08030304968a407550329250740ca070710070840c0d0f68070134003c0c1850351141000000900c0d5001c1e81c1d103000a0050401460046880219240840e5400b9041402055103400050050360f070003480a001c440200115413540da10a512402225409500000c00c1001c00c4008074400d01041c00c02c524810013603a1056405446440300c0a024000d420010480c81079a0f034440c1c0200282d1803002c1d008541d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 137117859 1250 137116609 137116621
    0xe01150305010b030c0105092416080703090b2802010905070b0913060b0301030b04050c03100c1101060602030306040b0307030c06020105010f1205070b0918070503240f120a0b 77
    0x203000d800c06024030134094003081c0f0210354010001c40707450302d4005040c15410389c95102820300c07040340e000c1c00180501c828884520801c2400c5450354289024219136601c54100e894004d181c801c05800802c1c10401c14018085002100c0c00b045201d80e1111100d01b6081a5449040340101b610603070150151003802800940041d811005050b54042543c01e14041d40d11100c01300241d43e00d5205880744110104010008a524500b801ea0014405c03030a40e00c860032404006441c1070304071803110040d159248445081142c1000c0580e2004184100070b21a191a0802c0a92a8000106903500031902c032580040e07942c0d014040a00956407000610601c0c0391102d1009000780824011520f602c41928000b09080d031000c84040d08c3c0c980c1c84002403501ca410100400020707002184c4440e041420880c0043c41056440b118038850318031640e5458a81c6801c0b905d0340074106c0401000500c89081000440742d40d1184450403a80100650380000c000c0d5800158628005180c040505007250b84014011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 137119109 1250 137117859 137117861
    0x30f0a0605100906030807081c140f0a0e06011e092301080703150c0302070b09010f0b06131203090305070602010c0e09060612180706050c10050105060d0e0115030501 73
    0x802641c420100d000c40c2d039202c2d503a0408903441400043c0030b1000a02601001920b2000100060b00c0d0f1410118001c2d04017000c0c40c01610483c8070034402c030f20419810004501c50000310300780d01c00342c40c8138240882140040e11070340351801030080c42d82100c08642c0c0345001d49506000040203104a060811100300c052044840e24100f40400e070050140030000010094400902c490559030031036010707840c00d140303001c840000b44505014842816000d00c10240403d83c4054041c1c032902d00e040c0049580d44402ca1850200c0d076145260500ca450103010103109440325520a0003695595281c882c40b082407030400790703000d81245d40010201c1c8600c40c0007003810b56041d002030716aa11a521240e0700c00500804005c1640d00440c1e441c4d400260600c98592840040f41005400c00400b103403410416450b52a07242c24002c3c950000b41c0440d00000d10341c400213008000f43c80034550400800c0055506000014003540f0035040040f81071515080f00c106018000e40c0003245999164a1800e0265a0391415038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 137120359 1250 137119109 137119111
    0x1501140f072306010e100909060e010b01081005040506040902061908010f06080601120912022104061b0305090316080f0c090a0f0f180b0a0204080a11030f0a0605 71
    0x140e501034480e1112441001a02c01c5002c04034001d0040c0500d81c0c01d000841500c020001c20740e180b210080c07240010405441e00c2040c003100e010740340c042011041c0e40c44040c01c0d038046e1036080b410800c0503401c010110624441900c243d5104840204050300c0c0c0c1c0000801521080c00060340c412800940d1300d503408030b0036554110491140e114101240e82e15407112410900d64450328000c900c100002600075807050b030403031032031a40104000901510a0720381010039041d8155520142e0300c900c801d0032007a90b0b050950606204c0751a40c00c0e14107030800c0d00040131088525002d544140080c2c18010805001e1000e40e050484041e041720414160040f000445030034600c00e4101d01e004095030184900b00c0424101480c0102601255080d103888903140300405400402c408515a01c80c041c0031601d00a0143c4030032081c1c0c03030075440b8843c0c165003007a08881801918005075981f04000c2048012008540348812580050919808402210100e41005150400c01c080781c00f0b04030201003000303d10b40c099 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 137121609 1250 137120359 137120363
    0x150204030b090a0201021e15010b09030c0d0f0308070c05030327011814010f0e0703020f09090705060304020f0409030c060b0d110411040b0310060e04060302091501140f07 75
    0x1141d190420310030f864402020340607005030842c44e0500c0c2e066050018000325100104d04541c00010110a001d140c0380081e04040c0d92480700080314134951034100483c4401c0344040341d000300000d0203036460840c1068140700c020140400310000034074442c0035222550400d904581580d6892510b07020f074461121405004892158138410111071740281481400b5216081541e09159040f003a1a4590410000c15903882c00c0e40d22107003000a010b01c5801026074070352038040140309003425481045040412080400c0c052181c0304104000c2040018450701220400d607001030303980c0c903030380081360754403a104400d50b4100e8241000b010030142e20280c0d554031f00303004c3c0751300300a101001e00421030035401404001d0141c843c1c10713065180914141e4462015590300d142442d140590b1002448400c3c0c104071841c2e5011503071403104102080d005842c0c04e0700312004840030072559007198001904400c01414004071140c00400ca8141c507400307000300702540c20110440710344603d044800b20607c0d5108006c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 137122859 1250 137121609 137121623
    0x1719080d0c030905030324040204120b010611071a091c0303060503011a040b120d080403020609070b04140321090a05030105010602150901060b0d0905061501022815020403 75
    0xc00386001e4460b20900c81016404805180382d03485040b841c80358070071035100c04955404144034042c229034841c8001c000a01882110701c0146880341000884000d05034864414031074000c2400d041c642d0b01280400031348035000b0101000c1c5605004038203d0f4004d102089030404d00c11211400c0c82c80741014260700a612954052001c561524207147c02d0f28240030b84458480c17940d9203806020302e401e400c5040500c0c8050031920310720000c0c0b0040c130300d440c203000203400214036242c040c03009066041c03000301d52022030140140701c0203182c07a50030b2145100340c1c440c8c020101409444000c07103a405105100c144207080c402d407080074032401000800c6920000e00f40d0310681581900084506042c01610704036074907070b009010074100d0100c851500420080a400d15550380f980c012900c181520081c083e0048941000210700048d803400d0303450040301a254805008000e03601e101960380c00501c155400c041240e46140514505c50004000c20b004c890040480e5120707400030b000382c082c6502410451303004440e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 137124109 1250 137122859 137122871
    0xc0603010311030d0905031f09061b0206070e0901030b190c08190509030315030a0c030602120a09020a0b0c100203190b010f0507060908090405040c0302150a02071719080d 75
    0x4e0309448811051191a03056003100009510704921082e0300e4881102c030f03c0300461501c01c81e5841000711422000300840f4540840b44140b19141c1c1000420361004690800c603031081644c0c07000070300242e01480003c00b2003d4040001e01284d002081410302500c1210701400700c0d4000340b6020b00340340c904990103c1498190803000c000d200c564003400740100c403280003a52075034840b40410801da1103031552264143c41141a9800060654110f0000070740c080c2d40010f1711405001011480700704003800031491503003010355071409695054101411600d4044000c2e0b0345441da000300c141000710b9000740044c85d5101204006265448210200307009561a0301007041c0304400300190b56480d860200c0c000016000d1122500040c12607121803402401109001c3c1800c2c4803c3c0002c00b501c0044500700c074a07582c040c104000f10f040903800e00f12441c0452202c50b007403440c110310095440c00c1e0303840358640c40140b07004e2040c282041401413540c089440c2c26240140c00403401c2c070000a5001d10805401245004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 137125359 1250 137124109 137124133
    0xb030f0c01140f040504050408040806010b03040c05090106020c100e0a0305160e010602061302040b0a060c022407080306040605060403200108070f0809070e0a090512030907030f050c060301031103 86
    0x11a03c1010018042d00d04090811060000030200141b040f200b14804000200714800c00b000801d00805495840701d5603481c0c246040d1b01504160f42c005030241301c080005220381500410607903002c0d06c082d2500540d442000c0c008554039243c802d507194222005140204c207001c4d0105100e0f80007000701c100d00018039520203c59150346000d22540b00145c205d174005c02d00500c04451550780e47c600084c8045408001c2100254414038558030200200d06108088000c600300303c0100c9429800c000e0920306500204002000c20748a11100100441d000000261044d5115400031024010284c80315403901c0d101c1c5800b5070b003002c801c0f10f41c03e1010148498144658816501d451145a040e92140000c0164480580d04001c01030029452401100302c041100ba0680824922400140c0d1340032502c1d002c0d50500e58200860000e074000c210104104200d03024a000900004499000403548050030640c00c10904055000c904594800c400000010921044100e6001c040c6821001d07214800544 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 137126609 1250 137125359 137125397
    0x1109030111120601050a02010906020f0405011b080313060e070b070c08060c0910030f0c02070f0608010e1b040e10050127061119061b0819020d0b030f0c01 68
    0x120708003004400b25800080c6039544954090000303409079000200f403425042d5609400c1e078100f60a4a0320030240807074200410741e40011151034103c81e2003240300031119142c4840d0031510006050201c402c8299410904000e200d9000000f11940c40c0242c0d007050f41c490024003120b6018180558648111040c041101c50340411464010b0103505101d81c9008180d0f4140901d108500b0a00c3d003d00d07540741500f1040441901425201d2181ea50252100c10300744090720204034215080310081040100051202008800700d554004e403500000e401d801700d804404140500c1107401c00c6045400d108188800500d9210000064500980301c2035901344500d0b2401e0550040703545500314001010004008180c0120340b01c400000e070340710950301204003d22103180c4004240d00203d907260351300c00c00c40929407074032403a10101b800580b805024a0400c2007400103520001d032007107000c1c107900041e81d4854080c0360340014243c42c009030541d152210810181da888000002015021400081c90507107a2484 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 137127859 1250 137126609 137126617
    0x60e160207060c06090b07020c0103050a11040504020c0102220e061c02040b1f050d0b19090510090e010f050c09060a1d180a060b0901090b09131109030111 68
    0x5600609001d4a84001160000c803182001e0f21500e07a00c1c04000082038040d08140d11688145d0000c0c6034200004000500300d400081c0315084080c031f842c882c280d11014207004c0320708541d0704582c0561030310b1411540c64020711030380c5030002850403561900522500c0c0e50510b44215001c90040164555031802030000d03903041241d1602c20303081107820800051900d940510540840a010408102200400d11208034010302d182000300d05c010403002c0c3d0242d150b024810128905849001c3e01c2640d824004400304154040c5d40b00407510b031000142c008118070600d50080a680c001441134940860b0b03100c0c028420074072405a03182c05d000c0046d00c09030703002007140c0c64020050082da01d00b130f00100003182c0800c0c0e0708080340351b4100c265646070350580e2680c181001405100c80b41160324204003960a00322012039000109100e010322811081c0d80e0801081411a00c103900c829566072141800603a020600000d016091440d2850f4918030307403d0207020708820340382a4020415900102c10412013401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 137129109 1250 137127859 137127901
    0xb0102060601200c130e06010909080301030f03050c060109061509030c090e0316060c0f020a030f0509040906060306020a0e1e040c050d0c0e36070c06050a060e 70
    0x2c0b0750140c2120703900c1605103a950703800000180d41354050200b001580c6200303001010040161282000e00c8140e005001082c01040b0000d010805d2100c540c1d11001a40014880689180f81d0025500203041c040c40131a02900061400d80c0c80e00d40c1c444600b080140300c1030244450048101e007a240007640242e030910181e940094441c52a5860441c5e010050000c410152000380002d012420b416140e16010300a0b0a20881c004942d0788060100140307141000780004085610142548011940000c88601c50446918140790b80d0020500450b028120300540241711516058001040c429071f54094021402c02d90382c0c55416800341000c002c0c401d003201d0000501658414601449440c02f60b1080502d241c05080c801d040181810b8074030300720b5201c00c1c24a0b0102d91090031380c0006182040034a092401e02c4c1c143c000040388245841e004a40003850a907030300036540b1000c203091a000302e09034001d07150b0248051100b03241c0050120054036a40c03298030002900ca0b40411260032a40e071034140300341c0d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 137130359 1250 137129109 137129117
    0xd050a0b0126150a0b1206010b090312040e07080414060f10060306031a04020d020603010b04030b0c030f13021906120e01060b070b0c0405090a020a120501080c060c0106080106060906030b0102060601 87
    0x10722012040401441040c400642c00740606c121000780300d105000c078900a011002050741c8170559a0145420582c020660141d807030003c10040c4000c13524034001c141c100f00c8a24101c8100e60f150b152110418801200c0e502d03842c801d400410000100003403810781b1803110960742c0d6511603904e000982c140d60319400014034290b00703000214548541c138103c46900078001082c0380d00e04c0c000340d00443e450780d0080e04980544100020284144041135044540181000c0c04503485c42c82d180a040d0f40340c0c0ea014201400da4100107401c00250f41c0c4500c0c1d4401304c001080c0440000a030b450344d02804070f8200300480101d540c10600000c0304120184a004103c485070023647e45003103160781da203c2c3d040000412119008000780004a41a292030b6640e41c890640044016551248040301806280201107040512401c1c8001440801c0010a01c403600c42801d45265880d50048860309001d0403841c2c00030702c03184d0701c0c00400207030555014020004860440d2010882071010710012170320b41c04111000b50100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 137131609 1250 137130359 137130361
    0x110f01030c0e150409150603050f040309120c05040f0207020405090703080a1407080a080f0a0504080904020703021002030405150c07030203030106050a050c0a0303050a14010e04020d050a0b012615 86
    0xc1c14480404000c3c0e8080421030b91403c0d131a4403d1500b02c0340c400800c000181e908207400d000a80d0144600e54008405601041a615242d03a00800827141030051980c01810384035110200030201d2061400340c00010400d00a15101c80d02c2400290481501a0f20990500010a40224001c185e52007a690008050703450309001890642e10003052200d40d030008401000401c02050120b0040c01d8001c95540e00e40030681031030b4100109943d40035001c03881b110715001c184400158504100c0f182c03401c060f603015894200d00c0c1026170801c00400400407081e030001003000104000070500010a00801d07903c404e15480341c50861311240100103000700541e200300018408280580040d00041ea1140b81192410708402940303424901716040c01c4000c03d07140c0052000b611101e00a11075280c0140d80d08024562500e0100d10a0200207000a80120250440b82060017001d120f143c10b4540c101b1103100c1e03107594a02c540e940c0fa0310b600d5020b80c010003145417601c2565002244500c2c00655003800c003a55 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 137132859 1250 137131609 137131637
    0x2030405061512030409060e070503060d030e04060302060313020102010c0810120206220906120201020c04020a030e0a050601080c0f180601030e0d050c120f12060604090603110f01030c 81
    0x600006003000325801070900603d090b040c40e042000300003400b4800c001040c254580b03c410107445402801c99810700034240100078590f100e4400bc0072445030185841a50004c208010070001e054a4001a4000c0c90000420008100b01818515064400c0e0300070451166251000c440580d02551a41010688524100500070f119110b0111f040e0000341440d1500515a4003030f0440c40700e50040c425419a111800c00c42001144202401440c1030f491862010507581d000039218900ac0c0e8030588160782c08250100060f02c2540050550b0300b030a1700301c6c0c000300c0c56424902ea940500b4482c00d01c49216207420104a805c001038400f003a40c80c003802d02c01240001c403104000906001384594101513030b4804254400380c0800654065803840c0d220300d907946900c2e0503001e003090110382800808080410004104520a1080b11040400c000e0040459143c010000c1c000b0301c40c0307901084007141412000700074440a080e181e83c00e01c00450b52200d02c0803400005600340ca21103401328010482030492410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 137134109 1250 137132859 137132881
    0x30b010308070c121202060601080702030d27200411040504241d010e0106050901082d06040b030c0a0b090f031207140c1f05070605041110030203040506 67
    0xc003061080003c80700450325118405030005008a00380c0783d40806211120b6807035010b010740c0f03400c81c900f03190490140c603041401070740c0c0b4847c8a40070414665501031500e002810520b071459060328050075000000850704006c12080800d0508000d50342848400d4a801d141601c00e1040009480d02050b083ca45810200b2008000c0681c810304807000c02030600c003581c140207000202030040d140c0d00200000b26011742c0001c0840503080406205040c0c0014040250010159107400009203084151039681135a0091086403024036003030f40704100401410031812401140e84281c0c01500d08105116001040641d81d003030f042d800d150807140c0a14140000c8c102000282440400600f40c401009581c0001c24a05a080d12075440c03081c4000c1504400c101e0406a001a9241010000c03d003076540e580005103210201c02804002500115000008901600c151400e80e038218030100143e03c0e15081520349820302100c114031400000c1003426400303001c3d1081e6030146402500814403540e034407036144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 137135359 1250 137134109 137134117
    0x140304020303090a0e0907050324040c0e0901020405040e011a0103020d060506030420030d320c0a0c1502030304020d050114090102130f08030306100905031219020601030b010308 78
    0x81d80602003000f020741c0503111070b40a0320080580c0c5008102c10b02d4402e480768201900360304260700c641c002c1440c035001c8500e4128003070348070524615081c3c140c0c0c13245d14101550040d40c0e440002381e55081c4013000040380040d405442201c0040d2030a000614520316190308035284a10712041100b0202e009404951007540608031000b102c817000140140c84000142940e001214102d401c2140d10f285030003600c00101d4000e56124081d00100070021a90328084c01d85200b203600960b80c45002d000d00a820a01c0583e18000c3e107044000083d6142911040562070b0041d0b031009446101c0480000181203040a02d42986009103074051429078880343d007001400304418100340c2d81503484607031101d0480c0062030900d005212000005943e4101c000060100301901d5000d034442004140f4104070b162804001c07294008802c0380c0c4020f03d084c0b00c410540d4800b0042d0040c0390148212000440403140d540c0051208d0842001401284c2040b84001c0381d41c1c56090200034010054480100b0018030b102c0050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 137136609 1250 137135359 137135363
    0x60a0b04180207051f1d1b0625060f0509030a1d04020a0c030905060a050a030506060c060910060504020a08010506071a070c031706030d05130b030709091407021902011b060e16030201140304 83
    0xa03034a061270300c030b4121050076405507007181120a10b281d1601000040d10a038015602e80d1101405280740030721009480c1c0c020b507240d98047c40103040a81f640102150491901c800c002032007151a40e81c0020018006811568120302040c80f611001c955480e0850039960081040d6481e80d180404a910071006054060001c1e500503006000052030780409020140c424108140184000001c000d809070030790b00c0310352040307006074410000703d0b503196400350846064070b50941d0340b25641d090324941031041c030901c8400f14a08000007018090166440ba0880804900030340d0782a52012034000600b1408005954055059000003442d00145000710003802c0620101c2d2a00c40394155603058824007035008030341d8180019007000f0b09100c112407910400c6003209a403100036045260000700a5915404c0029455003420100300304000c6a12910f46082c02c000c1102c95103c1d400000d2030501c01070310610385081814052810803036100400880f900c0c080301c2d0141d440c0c003c010920147d0000720b034005042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 137137859 1250 137136609 137136619
    0x6061e0705011a01020d0309080301140d020d1511040f15091a030109060b091311071703061c15021c0510050108060a0b04180207051f1d1b 61
    0x100c802092081c400c2045070008032201514182c00b090009040c41c020380d1010045c9450048110046884182543d06444111720708181c0349425000181c51135042c820002d502c02c001c031007a1010014103101188041c040300c01d042c4803905c0440711820240c00b990046501001007901308001d04c008ea504401c0c00000c00d4148205102e44480864030820701100c2c0c0624550000401040260364621800700100005503803076003801c0002c80015103c0101035600c00d00d0079100c40e01031020204040840300c00d82c1d0b100300707040d0b00e920f20000f44082d190000c89001d4460340c2070144a00c5480c181110110003a41e00a0004c0556243c208142c002500108278080a04d141c4034902c0d04801003910586000d4070480c03044141551400d0001051070740010b0106020b004015010800200788034142d40139034100000b103502c0c24903802ca141000b4050228060a1407103044810303c2c04200102e08442d40d50400c00061080100c820092512030700c103085c2c845030030b40c030002ca0726440100e1a0441c640361040204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 137139109 1250 137137859 137137867
    0xc070213200c0d080f0c03070c050c030706020105060a170d0f1704080c060a06050d110d0f0c090c0512061002070e07050a11010605010c02091005060310080c010806061e 74
    0x4200094205490300402d5a100b04495045150000400c83d400b400320f880d03054207890007404a951500000e02000306104400030f50707104000c0e0600216101d243c000d002c44414a80d41c0c0350090103090700350b5070359004074030b80b03007000c2000b48035000c9100130070100200a0192361910403003110071410350717080901006034101e44803146602d203500d000e00560088901585400100d00e0050818101902c0681a81d20300402041741d034a8001001c0045d83e00b154400e4040c0b81440f0109042103102040203202001840442c01040b19a91003141611140a410400110780c1d0605441910802c0d01d4406110b51103c0004c0a910b8560702140160915206403140d640c0c5d0313496080e04880c0150740380c4001c203201240040340c1c164031602a03640c01110100902c00b8514000001c1d01505100b44041e000740b0115000650b82c02c07101454000600c0c0183c005581ca150050701018003900d203025440103400b0310042034405610a08081e030240358018038031464140b070f42c1d400030320100701103600d4013420900b0702c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 137140359 1250 137139109 137139161
    0x7030e040615030b1008180102040e0708011505030f0c18040504060e0114100e0c0c0303090c12060601080f070306080a110a1215022503030b090c070213 67
    0x401804020600d8440d81c1e42424040b0344003030240c81100008501401c10111760402ca0765010b0062a041070010107034031911a06d010005001e4402d40c2c002d5004407800c4405e005825901c40046c504903600c0912401000f6101c00e03003104d05100c1a03c00307500e08400040455004042c0c10014004d00381d85000240201ca154000f0500b0384004440542d00d4603500e61911925850070b010760f000302d040700040d1200c036181210000700740b00742a024076003180300c01c0b0000611940410302116070641101c411261680b030500c0c0400d0b52410f0421146020720326107064000b03191000101d05c1e0003080161201c0f0010340e10000d441c88242c90080c820030070107848210010700c40d403092000c0c2400b10300440d07c1c400101400c01c1408000b02c002d0f4002d00611020034000008070f07418085c0c0c140c4a0802e0040940e642809601072143c0003c2103946501c207043c0307148007004140c0c00d40c0c05a440c00746d00340c60020b9190785444400016000d0040040d400440c50780b01d40c0ea0100c450f600c40080e0b10102000c0031290700a40d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 137141609 1250 137140359 137140361
    0xd02030d0507030f0e0124180504050a0b091f020909040f1502040b0c0105060d0b0c030a060302060a020109050f030c03090111010f14100801020a0527130b0f100504050607030e04 78
    0x42e0a10030165500c444001f980180c020901d0040301042c410542081d20341000303075a203081c00103100c0400c240c1d202c0c0441c0030000d0278040310506a401185805ca6403e0442c1c0b17154a030400c2c16681d200c1020000e40c0e003101d1102e00d00a64080007002440031100347d440d41c4600e0060b2007070040c01c0b14844000e0400303001c00e2080d403000e44098400c0240710760700c403604000094211440981054440c0b015000c8520014150002d5035900c020040c0c5500c1d126111101094060100382d00025400780f0b000c14403401c180d50551003034a1a43c064400c8510207030741c940031180c0340d103d0204090025041040070500d254090715528814411100000070241c0d00c08642c401110240b0116412217800401404014101800d03c80041e0403440b00031840d02c61a05400f500130700c110b11525101040806014200ca82d050035070102c0c544018004d080380b2003203101c07004010004402624031514518040e11802d060000103411041b401e922540d10700fa00b440d017003015540055900301c0c200700410a00800c15121 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 137142859 1250 137141609 137141621
    0x102010e030307090512031204020d1104050f0402032401060f020c1507020306010603060f12111002100c020303011a1309090b0118090210050c030f03010807050109080d02030d0507030f 81
    0x1544c1d02c80702002c0c01c1104100907170a5502d403440203940107200c0c074110a840740c401c05412517411034082c0c1414141d4600f5212054507030350000d900c030307103484200588001e1002c0c2140c4503d108500f42d6502e941c3e000583d9146a061300c102101d003050100040c8500e5009010440000080b40121003440586000050407407078188500740310b01c000480c1003011800c04102d1640501045e04060101606013148411400c216205245064060300d0400f82440001000c200411101505043d041a807011010790b6900c502240816041d2501e110007214510201c1580c1c1612800d00380001d40a070702c400340b1001900411220aaa02d01607500041c03204031905c07444010354802e032403410196160644420369041c0c07141c1c0d241403c41c1081d48010059540ca20101100e05040c207195454200544075240b070b5019092814800c08000400072a900b14001400d004a030001d0381c1d5250100d8403040b18135103c0410180440141c2d0062003042c0001c011a000a544129180303400103517205941480303010381c2c0c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 137144109 1250 137142859 137142871
    0x1060509100f1706040204090309090f06030b10030201080f0702010e1903030507050304020f150d0f1a010f08010306090305070f060b01080108030a0926030f03010e0907150c020102010e0303 83
    0x90550300411005801c2200d84008128039400d50500c07142010703c40361a40c4000740024070990b90f50300800d081600600722500503010004080003403182100e19540103000c02d01080d10721b12564000582945e014100c2c1c4001d070307581079546081c40c0e11000000201540c001c0c12500a554840304082d41c104010840c109a04200c800a800c0c032510a040207400ca580141c031a008100301001000050f8a98041d4601e1055040c2c03000210481c00c00c400211900404076218150341c2000c4003031098191581140031f07042e61401825541c480e04100654420036549065004151040b00400101ea850b5022200440c024200b840ca8912103603512400c034041c005040703507180c1d59a5034985480d6407142c1200c1c05440741d00e004600e0300500c05006010040340d440b0f82c00003214030aa00315035040920042d90103001e1041c0490b40c45a240d03003100007150308240036403c070307003892140003941c0d00800103444401c42d201d08014030000f0b0314030340e02283c0352454844260b0540d902e03690762500c096800c00c01180701d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 137145359 1250 137144109 137144131
    0xe0f0607020a14011a01050a120e0c09011d04080f070210030c110a2d05010903020309090705040315020904090209070807020f0a08040504020310080a03050d0509210a0201060509 78
    0x40210310f45038500415004000855a140040c503090340c3c0c840b074a00c684240d4003402c02c2d6454250503681112440c24820151821751300384181d14001110015415001c204112485c40c540c1ea01c0304000d014400880480c0060580f00e14007103801b00300844d00520b414803200c07120038500100c41d008141c4062440c40c2541c00281d8440101c2daa07a070340007000070442041007003e00b21800161300d5285060a21212000020303650050030086050000f4100c0790132544030f0001e010148050902075140e40095000c40c1c0035141100000d0204d92048d0200e40039a49d00400346800c903400d90310140025000408880e07000f41e91003c0d050090380c1c401ca6014800d44244d0388010080ca000c03000281000040b4060340566070111000b20001046142541c05440e401d40d001a201d545640400784203c41641c0045510302070300000700c090550140081a07070110a00e01408070b83c0f075220b4400e50312400c140054840c0c0000c0810303010000d60410003070040c4120b510010400316180d0001805880f000e486144103e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 137146609 1250 137145359 137145373
    0xa022203030c0b01090b01020c1e0a09090b130c0b0a17241e040c0c0804080c0102061b07030c260705010b0405100e0a022b0f0605010c060e0f060702 65
    0xb180b00e03c1d10302d01421407079009110304805400080d682e0034074428028411416902880100807182c41c1924040800605c04c20110340c0e1810a40001c160a403400e90710041410000707081c0c0c7d1001c480082c1600c2d0b01050785190b0b036180921320305240d0003100756242002036031000c46400450825540e0b0040506c851024014502c0001c04a0707070070f0840030018000da0051038000e04680c2031130030550380d16000b07403000700d868007481d00c04541c020000d481c0100b0304080071401080c00000090b40c03107082042a021a06c16031200b805501d44c0c00c0180380b181a4000c810820000080d01ca407601140d01445095484d15106241420348444c041c1030728a810080d8010078828140442401000160030043e2000c2015007000625459000b442c0d0003203142c07000c040070200e80074810540c102c2e098010400141107104000041c4002d00418050503010f4040c1803400e51401410701d0700c40c0000f2a281611050011903403980d41c50b01034041c402c00c80d1040d01070510140000c1405000700752040320719601030808 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 137147859 1250 137146609 137146613
    0x607050c09010f05010c02040b180c03041106030c07060f090c17070b0c060112030e1c030e041e0e07050d0602090111060601081816030302060a0c14030a022203030c 72
    0xe5154140d21503c243c01050f28100140d0f42c020103070b5001c40790183c8005c20002401004245a1000007032540104400d010800072112a000e002e0f6000b01e101b0541c0d8040821000704000842c04240c5041c171703040304100019070008050758031a40012a0f4050080385003030054032626240480da50280299021481840980904c02d205802c054002c0e407000030304000117844481d680c2c1c0d205004100280701c14000b00428140903a1040460440c0108a450340c440a204bc0745a5246000011400f007030030103140803039500d414043d1101da0211000710b500d562515035825005402c144401066500800c0004111511800b80c00400b0303c0c010135026a90301c0c03411000505a1128840d01601342e00714030140141a83d012103125001110103a45d1046187d503075070860f085c4045500703045e0144554460020400da00400d24610400700440c04000d03d07985400b05503010030b407510060030f0303200042002540740d40d419806003044450313004030410380c19040b50500f500c0203c55002030700030582606401f41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 137149109 1250 137147859 137147869
    0x2010204060f0c0510110708071a0604180210090b0f0309120a05070b150d031e02011404020d050703050613122a02040b03070e04060b04050603120310050607050c 71
    0x70b51520740d490429070b108416181c094442d5905904c80f07160a44404d0340841c0351142405940c4000d421200c6159140803620f02044441104429458100141d1002441c186050321031714070300e0000c2c00c904034201d1003a40e0070412161440201c81c0e0a111420802041160303100d80502040328040c40c0042d641c3c104580702d175103014030b004403c103255142004100080f07548841030b90310b44c2d980134003060801d4070341000c240007044620080301e4000300411080014191300113500d040c04601000e4071a00c070b07410078200300d0a840c030911494236009102c201160042c00c0003184140d40324001c0741034a120300c0d103d6480354140032042c4c1d01c500d400c81000004000780500d00ca0100d26005880c28000b9184100500100980c01100c1400004100340030100055444540140c0c040c0f210040c00d881e80f0980b911030000a1920640741511070318501850710619007003d10a030341c0035040040c020f0000d103061b401d0004c0340d90b20051415800540d0181d0016007074503a807000d0025944a80003804506001c002800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 137150359 1250 137149109 137149127
    0x307060905210d050c041206020d06060813032003030f150315010612090606080703030306080102040608011206201b0105010b0a110705030703080405031203060f01030b0f0901060201020406 83
    0x42d00c06481404200d00e1803000c41100c0440c0460000482c40b6650401150b4039401150b20111442d20142ea40e00c08005403640141400c0300c031a4020800c981d00d0340c03011141e07000112410710f9072800380c00c00039000c20b002e403440802c0504072160503681d4035480c84030982907400644098074690700034010f20203080a03116180c00c0140040c0e005060194401d00d404e054446c06204002c24008044003915413506682c001d09071598200a00340030050341c605440350b482107103100680009141107030108841c00103000b1a0112011603807903012507400c0c0390812181102d030500844409a507041a902500150080c00f2024000c00407400e450345440000a00d80381808407148240d645009c00500110b40c5840c1900e1036511240b6110f50041214102c9518109440c0c01003581440b6104d00081082803410040064640580c1a2601c5018000c600b01d44c50105035074040e4041e84d0080807090708e51080e40004903c1c60014211211845c0d08804180301131000e0700103c0060b50001028420250400741c0c0e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 137151609 1250 137150359 137150383
    0x30c0206010509090a050f030d1508060609060109030609060605040b060705070303050a05040e01090c140703020604030e04020409020c0a030818120a0302040f0f18050712110c0307060905 82
    0x14440044101002911540c050248a01c43c040c18000b050030032000700308480002e681301086501003001550261703a07940140042d0000e0b9400c11030044580038210020000700c49022000305420b4030b0301c0702000030f2250002c1a003410401c0061002002c14824000c8244150007100000340c110f040c0b17014442514045103105024040800c024000650001030301411a9003600e41184c490003042c0c0202c41621440c1d101206401c4003c0c008640c1c4a8030ba4050711603e6404e45480c1c3d0380c40c002807900345203402030050140260b00f182001030082030055420000621004000514140c2c441241e038040341c0049800311030542c007022070308080540090009400410b241030350f040b0744403c0f080003540c0b5140c0124043c100d02000c1010100b00e4020f4042e207000d810b000c100c840c40e0546a20110100002c1d9110303800c61007840c4140509c182041d0311030180504001c0d40c0d610304030007030f88803c0c2018203015071001d444c15800b0030050400306803d0000e00403162141c8004035820486061491816030f4014403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 137152859 1250 137151609 137151611
    0xb070b070c120f080604090f0b040203100c0e0319050d0e03030708121509060307050409020d060606051201140f0607020a05030610090e03030c0a0c031b08030702160324091403031603 80
    0x740002088000010b0801c8c90b82c400c110200d9a81e0340d00c0070908201c00e290310302c1038441c1064521036032603800840c21034280c041034084803034600b2100d07000c148458249401900301c1d00118003400e512486119075041681c4003808480c47d02e45280e03240d81d00740d40001d10007400c8190942c188072107038041004011048a0844170001c5509000c00003e480344400c0c440c1c244103e0390b4750b00e042c1c2192901c210040e20b940d0400e50821a2507554000603101e030384011102c04803240c1180003c078115040e001191001900a085801070009440034880309501c001d4003684d21584445000901d60fa040014030312800d2100b0609641a01e080d50080a450102c4035411945e0402d1040003141000e01080c0c40c10f29403d45401e40f1090079608003507800480504800b20000c0381005e1400a000c2c40d08020350062a450f8202c2e01c10030070100c111110038000f03000003000803410390b0a40d540c02c40749003485441d2034507460380003c102c03c11795500c0d0365240d2070b14102c00b036a420202c2000701000c05455a1400d082d101d00b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 137154109 1250 137152859 137152871
    0x9090106050a1d090703020d0b06040905061305220515150102070b0702030c0d1505130b060d1a07050f0d0b040501050603150d081b01050103020a0f0b070b070c120f080604 75
    0xf00042d00360303400910440425034041080080c445107500250403544c0c018000e60760b81ca4413518010302410049481034090400c000f20b40150709603610030203101d982d1540c1c190312140381d92041c40d0440d480002d0155514480c00040034540741f03034070b91290b00a10043c00c110f240b240d4004000f80c1082d91650003a429414140500000b6032030104031210301810031070788015143c40601e410138402e90584901040b4604e08010000b04000404150018a00801e41d4405503554030b400c1000c1c0d4004900010000d0344041d200821200101079070766001611801c2c000d00b4402c3c004013031209134201185c00101240c0b2001041e0950505105840c09071409803141480c502c0c10101040c80c90030054041c6000d411814902000e114136a001e55403007003d0002c42400c007000c44044e250203440e080c00240d10030640e06078000f8406200742440000c40d54031185440c1080c05545514050005c010182810320121140c0200001c0c24000c0300c24880002da00d440c90654940c21000380003142c020f01041c0503900d011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 137155359 1250 137154109 137154167
    0x905010906020c090628230102030d1109030d0801090f2f0d050c0711120c040b15040807061202090d02090a0902120102120a23070509090106050a 64
    0x440c1541803c0000c1d039400800792100d4010800c01c1e080d091800301056554400b01401560007400da10032501c1160ba18a28500200d50352140f503404454940e001d40e00412001c449820aa0018680048054102800c21560001007402e1103804031401c40014480801407002429a2050b459004200d030320410191a940c070162421212881015550022140204450003a20030483c1d41103601a0018482c50078030f403600b1082c5401c26281160071078008507100a03d41441448220040f07544001014814140b00500005010f0416550341051003111408036815900d002040201107050003403032048c0c03900381e0080400030501e00340d20000d80100042011551502c0e200c0c400310750111222040c0391124070b0a035004041c4807400a4010a0510340000120019800360004500040c19039015503a916144004c64808001c11400c1030008013041c4025030040c11210b81c03000d0b10f828001e10b0101075030002240141c0981c0054002000011040001907000f241a405035440d040148050719800d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 137156609 1250 137155359 137155363
    0xd0e0105091c1103070c06081515090607020303040504050f090715080703050703020c07031209060201060e040b100816050a0e06012010090b071b0b060d020d05100c090501090602 78
    0x1402d516070070464200c07041240c0d540280100c50109910802104100359512000340100500b1070740040110311000b030b40c5131203040c07106507011200c440724121807514618000300b040a030480d00d000d0703800d44810f0001040706d417100c3c45054000e0700f00311400c010034070b401a00245003000680110b20f54000c0f03036408072441a08004415081082801d000c201070351040d0040700280242c90b0420b1462080840000900480420340080600740340d03140c80d282500e4240690a90303400348074041c4103103918400500816042151131350404121808400034a5a5110b020315040c1c1412002020003c851030400c081d2510718510030080c142c0c81c40c680b0041c40d1040018104502d5180700b59140150b0701285114000188203145426000c5c000030411320469090a00031704001715450000b03d014840c0b20344184030f18003003403000710750700c000c00800d960b45200500c4441b41d65160120b0700002580c4042000400510000e0b0100314102070000e840c1e501902d00030040886540200d0508c08140d100b1701100b640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 137157859 1250 137156609 137156653
    0xf03070204020d18030c150c0c060e0a02060301090f1b0509101b03120b010216060e04060b0301180606080601020d0c05150c0c0709140601081b0d0e010509 68
    0x488006884041040c503c41c050300030140c00e05452496950071000b05070700800c40d440340c207004000186980038124003005c100c452050419000c22030030740c80c8400140d0030b60402032808a501060f100c4031101d59010420f560000e03000a44900c1d110130443c0912011407280e074200508000b203204d5400000d41c000f400c41e206080103a801904040e6092000798060184e181034810498070070040c0305070505000300150b0102030a9402c040c1810300385030180d072002404070060756000c4003440429113041d0003500c0492100d09640e80064803000c00007a06400d04000d54000c059102446004c2d0b040314003000d08440054000c081400411001d0059507680000c0030b000c1a003a6040061901c095400d00b1882c0c01c0d51403c0880c544084581080132204841c0060b10050301c000c4112049942c5038031811040e140032041d640a8030ba0003100040043d031242200ba9000000b0804241e0b240001e20603003110f503031040006a005585034550f50841c00024840c0d01d51162040c0003610b100d0007964203852000c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 137159109 1250 137157859 137157863
    0x2503051e150c071b050310020702040605040b031f0e03040f0302280b1c0207140d0801060203030406050a1503060203160e0a060c080d0c08161d0405151203070c080f0307 74
    0x40b801444e4212100f4103620806408000d04544110340002480c2004e5400000100e024a0034040001814241406250040300005020300780e00c60028981d211600303420598038a409444603407054407480306000800150043c944510550703800e600601c040043e00854490f0f10900c0c881c030716906040808890810782c0c4900c0490b5070794070800c4c00c030f6001c0003806103007807914544000360620401111400881d655070700d90b41a034005071003654003901c2c060003d11807800503070801c000040003c0c03c6a40159031001d450503000407800800001d516080ca800c1c0c104960155000090006010385010140c2080b80039160260005200340d010a005040380e229600c14840207034080d1040001d5002956400f0098030010000036503c4000182080c1040e02c0d54000c104840c0502c01c100f611a10651000c0c02c1e4040d104008803a01d0720a02c801840018800c4564081d4803286050031303514124070003031205a050003540c440c0218200200a1981740e806070b8a540c0c054a030303d0a040c000031040d5010300d9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 137160359 1250 137159109 137159123
    0x302010302130f0b07060b0a080a0305090d0506070923010504031103120c0115120b071809060314061518060f0a0902120a05092503051e150c07 63
    0x11602e0b9003442c582151508882c0825007141000310710309490360060296030380204005d0029a825100b40039401a075405071324003a811504407800031038000c9004040105001d00448850308494440b24104401514200002901800200081d01110306c55840c4ad110b40c4400c88030051500c400030300a03201e6884010800c0807500d8000c010359a003401040703481d1550405460f42c81c002030044900070078100466000240010318007207124000c80c8143c0c0c040307139400039410403240c44043c400e842c001c112859900c140c4901c5080881e240140f40140402140f04002c0880320686649100d800c180f03000b085940006190200e1f0b520310b6544a00c440310302035101e141c042994892202040100318034144031038015803802c00003c5c601d4450750040042c408034039020725a03030302c0700720300c01042e62801e41e081c1400358042410134103042440d02000c3c40810989800c00304542e940d98a69007414100800540c10700c15003a0640385520b42030005801020b01e0b0100c8007001d20300304142c1c2016000341301002e400c42c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 137161609 1250 137160359 137160367
    0x90b0d0509030d1b030606080114060c0a1b0608090f060103080f250501140405120c0102070b0a09050d032009030f0a2603100306020c100e0a0201080f060a0302010302 73
    0x40042c8111502d400c4954010300152414400700e00580303020b19a0740f40041e1a22000007501d0344603e00300b80c1a01d00c428585615080036104218250704a01c0b1090514090303d4007102c0055050b0384941e03405803014075580501490094081c0202400a00841080d0032843c1c400402c2240450f40c0e606496010700445d461f05d500c50302602c3e46010300003032960502c0d24421040e52815240f40d0b00c0c024140b044009110000c030082c003880b031040040c0d90082c010740c0810400000f01d400d141c080c14046003c40001400c2580035280e24000e410f080c0c500710f400e59942c8060382d0500c0380500074080210300a08092044030b640c2d603e001c0c1c40380900c80f40c10081000c04201011540d9040c450315001034a0310313003103514450f00d41c02c100d01c1c00e50885034514160b640d1443c00345554841c4e0010342c0d1054084801c25104035165484240281d8802300350040c0f0741c0282102101030342812312500543c011f99500600c3c1a01c0288000b6011071806004221003520a4040064985d83e01d08044240c1c0c1c0d0a00c1d0250325 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 137162859 1250 137161609 137161621
    0x106210b030c120f030307020303191b2a0f0c1d060409030e0409210e0a260706020307021008040f030e04112b0903090308071703180c01090b0d05 64
    0x10815036010781c011304c2c0400001c1c02150b0303500001440c061524901c0300704844060240140441c1c600e0516045a00c51401030803101c9030040c0c3e100d014079484094192503510b0f0041c070b100003003511070300c1c100e85100d480340904041c0b101c0c5aa200014080d03d215180003440e07030400309100301400500c09840f8603120a0303448101072051019070801b102c045c0043c4013801ca14503105107100f03000c1c40c00c22100c603400c0004132400c0e446528000e683d50400340020080d64100620450310701c001e03148400d041c1d6100201803000c4c403401c001c20401001290701458842940703104200350f200300c1501c0c00e010800500140004101c40556100c19141e160510317810303100c0c0d84408103005c0e2514003841d00e074900700841d140403010150150159011380d00b0542d00c100981d500c0404080741d020350000340000d048900c0510000d5014002080c1d502e0203244c1150074900700f0b1103403600961088032900760384090382c0511142c10700104065442c8031024200450114100301d801071003030144109640e0270780d8644011800d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 137164109 1250 137162859 137162863
    0x24030309150c02060307030902040b09270109020303161721041a010821030702031b030702310c2a0b040b040221061302180106210b030c12 61
    0x2c0030660103401a03450385420700c00a0300404403004168040e50401c295003d0902c0e1980246100758062040040180c00b02d45150105400340c032079612041d940c541200015941c1040070381402146e80002d55005c020034609543c501c0c4c400b44401c98401014001c0d0703401e00e00e01400060f01158a0340d00b0603440d0b0364904012880200e10364401c019900f4103c008107030b40e113002ca03001c1c1c401c0503c00011800851510316104403880216002d0b00160001e0044903554216000e410585174000c0d0110390034210703150005100c0e818412040c44104681c521260400d6843c106014428140071100f044a0840440060070b00074403000180c1c40e4464098080c03040ca07201001e440302ca103400845030805480c05203400c295074841a201a4800d00380001d241e000040f00c0c0140314069203016006e0020381e2910001c1104140440700200d03030082401ca9040c6000c8024405c9034020701041d40e82c409245181c4c10100348032000c0050505000e0300b000030811054a0000d201038000781d0969001e400c0450071a2454 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 137165359 1250 137164109 137164127
    0x2060405131d061b070b06040903091a03070801050d051f090f0804080606030f0712170a0903020a060201020c120c01060b03043e090901020405040204092403030915 72
    0x2070407021502c15000b40110000319240b0461488461a0b80111462403904071401180c10060009003c000002c0443c00c00e900446e55480c42428103555184c0c4501d10b0402680040aa40114030300220070040000d501054a07070040c00c0541e01d10300399040c00c0d10344503101e280056064450705031000309802c480d0700e00c0c1d020a107904d4003c8008400855180b0b4080300c0c0b5030182c450740c1e1140c80b031035000c603c403850702081400d40c1e50900002050b08510301421700c0c80309a501c07081601d00701313242d20400920061450050170b03800c016503101000c1506600c10802c076a078550b04075100316881400002401140000e014000d2000c2c0c0201c0c680b1030000306076a034050310643e007006062100c00b0080c00f00300486915441c0c40040740f50001303c0b000400c42000400100044148a003280c99138441c00440d083c00c44c0c0c065000381c0e15200241c0760585038400705050f64481c0d402050543c0d9070301e03c040030707000c070069103909003d185111040c0380340c4c6903450040030891b1900649500e0241420b5401c8128000ca50715 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 137166609 1250 137165359 137165381
    0x10080606031f0909030e030105070e09010317091e0a080d051213050d0f0306050402160b040201030e010e03040503070801150b0c010204151101050612190618080403140a0206040513 79
    0x42c085001c2c81c2c83c0040c1b01d5600007624501230346c200004959601d01400f55407014180252860803140e10356100c1c0c0c200d02d090107003024403140d41040561101c2d00d80c03191041821520300c503070092001866041c800414460b07800003110f81c000100e03190044d0707440805c8502c1302e81c00002c0380c030564603030480f1442aa280803d00a08a200b040c000d045080c0c1c01140b01240c0036a151000c111403541c54042c00264414942440f0401e0a0400c01da00040e0105103495000303801850b000035850004441c160840301c0340c81c26211990300214042026203001c01241d806461114028004004c100c1e9108940c041c1502032040318000c003241c000d12002017581078a00604075142161450405100003400ca091034021400155080800180341410807415080310110408000c02000300c9403140e0f8039000c50840302c11076a26440e952401400c01030a15554036650055030301f603a4851441ca4031a10f00a100c1800061940000007284090707503e000540c0d0403135506841c5101039441c68010100205001201 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 137167859 1250 137166609 137166611
    0x1f0b03100903080106020d0f1b060e011118040212060907120609020a030605010f0e01050918010b090f0d0803010e1b16050609030708030103231b10080606031f09 71
    0x1e002450b903c220240d0403a0019000c0d00d9203000e01c070343d080341c00321400d444420210740b0000f031038017113805141e40d0898510b0064400259120f2064201401d481022a0000c0300400100b04811980c9110300710070043c0404803411841c1200002d415140b200c030041c84544102d02d9080015140b60092150072003a1603451400c0250396101d00c8444000c1d006506410f0019103004004a003650040382c1c5a9885640d60b00c660040c003c078040112a00da00000c1260740010301c02c040f148411181e811a54040d00500c00d00a13100d00340c00342402081d21803212168800c3c500101120082000007003260305480c40480701c8040c07642c8100d0b1260480e05804c035000c81c52032001910582814409914660b95407003a0b040e54503d841e07410300140c2c0c4c0d01400c1409010386034100f004100252410441c0701e460780c140305154115120b0362000d1814415080560a16810213045a00d0646448001a2800c26580c24910507a04080c8045030240c00010240340d18140d0000c100300500c2c204004400042004100c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 137169109 1250 137167859 137167871
    0x206040806040b01050a080c0409021521090a0804060f0207050d140106090209030d1206120312142e030c170c0603070f080a0b0a03080901111f0b0310 66
    0x440d1a0340700c0040310182c2e08442d10500102d8980b801d0f52458040b9103400c0002c055429900081000410415404a0340604c2034a1049100ca080101500100d00303040004081d132000c80d42e008030409030042c00e903030316034209815a10008212070140e41c1541c0d243e141c0f90001e80700083c01a882c0c650f244e008280c1c082c25000440b0100248048640010b03003003030340288400b03a0344d900350005900511200b80d515420045080803400d00c1003101d01900b019683c40418400c0d03a9002003244644820802e03000a01202042149a210b0303000342081d0041821602703d45103486800b01e410b4002e580070713407101043c03006400014003c141d01e502001c1c503000748540381070300d680e443c8803110517000c20f942c4405c500604d00b05003840e14201c010303248500c100341c544140c0c46031100302c119007442d0010079410b441c030b546507403240755903d42202040107984100c1c406565020160005030000300d040d00b1007050381d0701151000f86280380030b010111a40e00e035100046145501d840000341400761090108508504d081 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 137170359 1250 137169109 137169119
    0xf030c0d1401140a03030f050702030a0b0106021c080709061103091216120203070e18030309010209090108030306180a0f0905060601091a03070f052502040b0109081b0409020604 78
    0x1110042c100c0d00c0f02c0c110407001d89403a00034401d512007a44005408640042c0d00c042c1400e0090009200192004040d2603040078655602844101c080e001040164081e00312003803034040542d2040c1c40246c481c142000c491811a0000b1710703140c40d60040302c0810002d0071581c11015010026900342c000c0050503290b41002c8040d8050303680440d0307600d025265220b00400100c40f0b0181c00c121110940250280c1941801c00800060420016000c0b280601941c08015502c4005001450156003104005a5100c03070300000c0050050307042c1c000000f9a0410020f00c10076649000c1541c441028003400e000711a40c4080308040105018203001c80d07040c4c200410b25007004004100c00703120b14401d881c1c9401850319507062180c0809038043c5104a040108045203030342d406441c00d14000422442e18505e041c2c2070100070007050302170320003030f04025191006000451401c0d000ea0000c010f402e1030305c0c88407245044800c036590785201803d03036240001946e140003652915003113644039a801500d070070781c3d036541c0e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 137171609 1250 137170359 137170391
    0x609030804030e0a240513030804150503060f040e0f0a03030506040e010204050d1e0f0305071502250203160b19030203060603011e030606140a17030f030c0d 69
    0x1214102e0009844155032296032600c4070740e10090381e05c2c0400c03000d8080b0264501d9064050701c0d0080e401480002e01688091121500500c00954802e016041d2614a801e0240700d90b007810030042c405200c428020450582c860038440203207810100da011440180c0c0e0242c2c1410f1000c612580390007401034041d024213141c0c058001601490003540d08001038885084403508030300907806140d505c201c0109801c0041160428090507400c80d00801620180444d65449a0320403a004114003003440440d0b01000c0c4051a03a8041800c0b8210206510b84014221003242d451071950401041003242c4076140150f45040081072004c10003a80922003a54564862030503540102c185003241460b844a00d4800350b100380242d90042c0740141c40c40c3c0c29a4200321409425007025481c03002103c0ea2102d0000108544d40601d1005206c1c01d03005a00072180c0c0303018444441c6490300b00b21400748820381ca019a4140c000300f107686450542420603100e071280c58034000d82e4450080071100c0c01d030410300507032645180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 137172859 1250 137171609 137171611
    0xf0303020c0405010b0702090901061206050a0c030c022a091812090a0e04081608300a1508030703091d090d081b070b010f05060c06060f0a0306090308 66
    0x69001c03a520242aa4100400c0d26000d00681d6203504003031101400504150107029080b01000e4001b040c52030b1108003c0700c901005103025100581c8520905c0003001842c418114920868a81840460200c4901035035035a109207811906078a6061440d050032a11590325000d800010103819603801c00310141c0e203276040c02000820701801091003401810051178220b880c0f901028060180a178035040202c90039000050081c0d036030440803c20045102120039580c0010344c45150f4054682e071100384591500d2180c03210b007180707080c0c0e07101f4503820044d41d4400b000c0d449241c5200104054040c2e0065212500341d03603010000511020822804042d00003107040280d44c544c10414090030703100e5410503218901134078008026044215036041c000e1040c0007103a4002ca80780507503e0140b02450484d141544804020303101c0804490050090039000804440282000c4410a00301001d00642a441ba034028203c00c0c41031620703150100d80d07500d4400800c0c000b1340e04428100602d0003142405000250 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 137174109 1250 137172859 137172863
    0x8030903010c051606151203031b020714061308030403031101050606030c090d050c0a09060e01060e01050301170a14010e0706210902060702060309030a0e030705090f1b040f03 77
    0x10800c80340b501800d100d0401c1c1d4090094890940401c54255103401005068208514290829030240030500480c10306400c0390880c401d0350005040c0b80064000080059041f0f1700307004540103290100a0f5010350101c607024a00120707011903a0320022404082803c5080e800079082e4040400c0020074150800d40428031070081c540288402da4940040000b503102c110390740081c04500303101c00300050400b0580700d68000d1046e0100c840b214450300009500340c640d0b9004554079070310b44406000c0c840080311131500400c164100804c03400d42120000c1e005002c14090b004070455809040c0c0c5100c2800c015251100360804032100a5031042c1031905c1c0a4101d105840380345204540700040e0083c4501880d140c4902118003003c40700b4009075088004d0a0f4501c410381e07010340140a8240075a840600441c052281c50740116a10340721584c0c060310004402190520a4000e44030070003a80c1c85d590f005544c00441140c84001d40c0d910941c10140524034100e420403c80c4001c01c011413021a030182c1141501c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 137175359 1250 137174109 137174111
    0x3030f0f091f020f0c0d030c03030605041b0314010b1e0d0504062715020d0209030d0804030207240c060e070e091002070818060d0504080405011b0b0f060a050a0803090301 75
    0x40d84480c59036503480307030110229006a078a0003111b02192040ca030081080340300b0725010410030740d194002415541d4546100d2a04041c1c507030340103000c1c1e805102c1c80c00f0180711401c102c000c40d854591204800c1c00342c003040c0780c04c4004081c0b044a0b03807000c1ca41112208104210704000300d007454209100140f1010f1440b80700c4032900d803109101d000088a0307002900758410b01000d1040c5407010b02c80b001e5003041d1600100303c2e4007032140940c1a80c050200c281c08031709035a154411403815003002031400d080755003c1c0c40c203012a424482290740400003041c504c0880d5040103000016545032031401800c0401c50320a045c0a2004040b03500301044022a016508440c1120381c5424691a204200d214a0304010040e0703004101010801600224255403044000c01d00c90800340c081100310196641200c0446901d00d001405000d20341c1c22500b003c0c0011204045100001801d90301c3d2440018042c040d1407110342858000340441d074954100d0030103000054503110807141e41d1402c85907640c008042c450312075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 137176609 1250 137175359 137175373
    0x3090d0f080f0d06060815040c021e06041a15010c031704060603060608151803130f1e05030c010305190c0203030f151005070501020415111b03030f0f091f02 69
    0xa0746c03154441c2c901901d00c615444840c11850010800102502c0c0710300e000354051000a007845078181c0400c0400c440c065005005246840c0c6001c2c4401c0c541a6480b80554a00030280004d00c0d80001c41071030341e0402820401000e0f00181420340da141d10700d0700f2550444030400c00300010003515030012402c0702d1280c5014440075840e01e1440f9100c103100c1910811603201440080c050000701c441c24194061a40c0a492604144280c1140c0d084041d411105c0b41c2004528100001e001d44144458800d060440960340d40f8140030010f41c6914145c0401c9040507100c901181903441c5110000020761078544042000c5549010043d40700d41085801c0c84480310410002181584c0400300d01102043c01001e0302e106d0389e6401401e07a4142c00c00078080c1e550303640c2400042144040310404501d00f056540340c096010403a0b400c51450030340925560b1015603c480712821070740e100042a90311310782801c0584e40c0c803140c1c14220103620f4001c2090b00c5a01900c858400060400380c003035886013101d5180d01b03580b11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 137177859 1250 137176609 137176619
    0x504061409060c070809040b1002030703020c060f070b0a0e030409060303090f03050a0b040602070b0f060f120601051203070501020a08071b0308060108070c0f110103150803090d0f080f0d06 83
    0x44182c100c6040140c000704005920009100c10010035003800020030009140130060301040710216130420f824050380c0005401800c0c55010801c02c86c0d0071608a9000785001c040d16070244403401140b1009200b81d0681d004a43c1030800c3c1d0304411258040101202d482d43c2d9904207400c0030348200d10095000c10942040070a040c24602511130a882c2c001000f0410b09103150b9441803a03402c0204142c3d4220340c00d2240400013528000381ca4028520071404803c1420030f001040251080b9200842c45074081e101c07503c613a08000b00c0c5060442c0c0742180c0300c0081070103c43c07085085100304d88008186510014600301001c1d04070110074018855a81e0303482100018040f400c101c1e031a0b021014001c0b41101c80012101d40c820200340350f00990919081c6190006996092244002e40328201d034010010103428005580c18814074440f0f02d40f03082d5090b1598030704800c00340c9a00c6441e02c041d0040354889012014070411a81e6807140715400480d8945d00c40d40c0d1305c080002c2d9040300004002c09400c02c0d00001d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 137179109 1250 137177859 137177863
    0x402040b030d1d06090a120201052b050a0b091506040e040804080706020313030605070e040207050105010302010323010e06040e030f04091a0609040b120d08060a06030903051605030d0504061409 85
    0x1400c50014040801041c1080a04055407c0304a4200d0410504114240480c2c038010502c0060540e41090030048540c1c6a43e100d0607100700501c2500b24510308681181c0360b0766540200e41d04a160b00c2e20000d5901307000f00c0861041d11554201c9c6d04c0c003400b40002e00c000c122808000300110740d80c510a480c40f041d1644412a102c2c8030340c191040300000c002106101007907080d40b0040d007042d02424010700b415681408102a60002d503c15200359540300010010b658150080b080102c50b80750042c490350418581c080484c4106008000740c0000050000d000303a2202e038802a1500c082c1c50840741c8441060350900401d92150040070741983c180350300c6144880240b62a019401c070000c02e4281010a0082030200903c40d0200040e8040940d82c88514030040038051b410090030070b582c0c1d00845290410600a11030200d1b80040e0815141005140105e548402600d50084004542d0701240500d41022851401130011a0302c82501e454184002c000f05070f448280d030390308408140e9410b90b5401001176 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 137180359 1250 137179109 137179117
    0x3150f0708100b09010309020d080c070e060a090504050312010f061701060e01030c030f020c03180d0206030c1321030815060301140319030908120301080c0105030402040b030d1d06 79
    0x4003801c2d00400c0148140f402080c041c1081c00ea040c9000203604c1590740004000a802c80000e4504110014010342d00d09410720a04018102c5040c1c080d06c241004400b0803c2001c00784500b02c815a9a040441d0401c00c007030086400903000100c82c1a29541c6030640c4070030800a40c4038407004142c1000ba00d4000da240804000d040703810702d48520081c24141030040d00030380b40750403d8104141c1d540400300500c144c648050036140307110800960b102c5007422000d00d120402d84c0b20040c818074009003508010b0b5507482c220784c1c0c0242500401612500e01201d000320000017074024403808200381084c10170050001000301e075131602035942c00d000d90700d0b001c14107000812007040d402e1b0801010801444881a4044103600d01180030342111110000c1e000310300d40207041c11600302c0004004040030003c1400400c020083c41d07425400852071949002d1901d5901c850b0124000d040c01000f00000b0250760b5140d00c16144c482c00902234a01c203008a2000415043c4107040e103020b01035200c1c01c250b285090210580e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 137181609 1250 137180359 137180371
    0xf141206190c020f060103050d14130504090c030c08030702010806040b090f0603030c010203090102030915010e1b0405041406040c09060e0603090708030417070e06010c11040b03150f0708 82
    0x50400918a040c1e41018028920811007513128100c01c06110840812006008601881c040e02940c015884000d010100b020000d0306400d40a2219001c1d10082e032458000f200c0d000c580c0003900c0c160324a84003030100171a03480940302c07040e241d5000450540100c010081d89100f41d80d108a01e40e00c01e005c00c41200c1c0081c03521608841050300280861a0b4000c50302c2d0400f6000b000c07a030070f140207112000c0c01c2e60300456240e040360f50084203100c10150708002c00b1303041d8602c0190004d002d6041000c0740e00a8100180a03542d82c9500800c141d880c82d1681044401800c0040c01c2070142c0300d07090f000a920f40d503040d40c40500940c509600300b449a13100e10f180d002680c1c00c0d03607280c8650f2840b200c100041f5401c00352034804107000740140054600c0c02000248004c020088400480d410409019401c00f41554002031000d91401c00b0040160391101c4a44039603640440b455003078074100340100b0014040040556010321810002014400240e40094440c58908011011503680c00b001120740e51420760b00c2c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 137182859 1250 137181609 137181631
    0x20301030503090d0516090614010305160e040603211d0a0b0906040f0314060a06050f040e011b0c0b010b090d032006040b0906090d050f07020a0f141206 67
    0x1c075409a1601002c0c0d080701340c1c040e408032031100c00c0c4001140b0301c500d4503038007004100340e4500040248400001816221400034202000207180209800420000e2800048200710104a03030301519500e52344101c01842e04580300c99501c1d525400076015800003044944d021a1001c0f400101e60345000729602c520304130242451401c50719103030420b81182c0041c000603601240510000c51205070000f0313160015802164a591030317040b00c07403032607080580107045045440c0c20200e0512503a120040c68200d030000076500040c0302104030382c505d8014040c00b8040c598112221140445d01343c0d1106103403410a018030076259140c2d036a150080310a20405c0c0f83c030340d0001614070302040031900626881c000c0a10f0500350400e0f04011140f410f090200844080b1078031100340c420700c0109035003001896445003105004000258040d58080c1c440d000d1000d41c0c90300300320005420421522403a004070010315002440d101040d4a411041944150840e0302d075005444080d5220140000011902d0040900c2d2003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 137184109 1250 137182859 137182867
    0xf171c1508030a050901030e1005041704080a08030601031b050406180503070902160506041a0f0609040605070306080109060212280f0e0322050607150e0a1704060210020301030503 79
    0x50107480300c1d0880300540d0b0505523240c454801c405400e03c81109080c01c1208001072624040c544072091030007600c0e61035240541440240031070000001d200d1002500030b1038807034a070340c0c4000040703024024208540020401100c9610702454106003e0030590710942c4460090102c0344d15458042009449001e81c1035200402c104402d20840c0d0041442c6c1012200c00c10040c0201c0d22100e01d82071090341d08071f400110f0005d461005510404185420030094141c0e40b2803810001c000a0712808041c0001c1c010541c0c80011810042c000d600420040182100901c100382290804034000c1d00140d001400c0d000d002c80000d10b1070070310040c40380382e070107021411000c080c2007071255080100954080341c200184d0341c0c040410380d540104041c2ca000340c001e29910340da00c400100040c0c40f14140d5030103140514414408100000c054198000c00304445a1000a410071519006880c001910001030a00c10950304c5000b03015640384001c000b913034a25001c4035254680d540d0104102c2c4002d12014080e07800600c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 137185359 1250 137184109 137184127
    0x1080a0305040b0a050403020a0f0f170a0b0903190905031c0f0c060f0513050106060906020d0503130b01030507080c03340923130206070f171c150803 66
    0x4805404010213501e007071410180ca83d404200c1119060300005101f00c0c9581040201642e20342004026066011950005441c04594180c2e40c2c140d090f001080e000314000000c4031f06400308155a011215020900141503d5840c0a8109581402814020701490f20215144c0e1110510360031000c805a8802c07101110103031044801d003842d013104032039040d00e0302441d1040070114080c0500809030000d40702c1c0500460b00d81a0300311680341e03001c0c0041c03001c1c4817820000b29402003101800900d850406a680f60f41d0b000f03407440c02c0303c6111401080704074003034000310501c13100240c0b840540e00482e00715608030659000705035864020010b03014001100e880d036000700c00d8090024420040300385100daaa1b20b0b0702c0d07400c00d50946001d11160608043ca4030802404d00b40041d5000b03810103080484852131540316004034045120300c0d20043d003100d500c1e442d003401300003904d07540a00c00422000902d4031465031034030070341e16803850f506041c00312428110bd1041c0c4a0013120210112002c400055180001c1c1c2c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 137186609 1250 137185359 137185379
    0x1103010c02281703060117010509130f06020d0b03060702010e061801140a0b100e06070b0c0c010207060207110105030702070e060a09020c01020706051e01180209030d1701080a030504 80
    0x10400c00c2c0c1000340c029032031200140e11010110803140c004403500742c0302d1400d4000107010080c0c0246604003541c0c00001000f4544034540c0450700500c154200140884541c1841500d8208000c00242000e10010b07424900d00400d902850280e00e08605440c019180e1b0714080f8240c5500f044004800c1c3c11420101d800c8411803540305000d04440000801d0b90302d0184070040d0309250407902c0040c001c3c1c40b4850742c0c03050718000e40c0c901c0015155003400b400c0b00d4aa080030441034020403200a0180f0041408a0003011512059036015a00c100095641c0d65031490301c0d030302035000580100c80c0700e241103024a02540c003c0c0b054901c1090f1940c0100b43c07042c0b5020380341581d05c9001e44101d8200d4000030011801e864240010404910420000b5a4402d01890950b04517000200080b07030300a145280c807030421034840b8070740b4110344418540e10300301008501c1e444000d200d001403055140c4074001460071f0704c9070064840c80f03440020b0815012503a070307945550354861409942c01400503004210500c82206a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 137187859 1250 137186609 137186653
    0x305060f270d0e0a05041e05070f140703020f330403320406110d09050310020304031202040e0907090b01050a2a0507090e010c0f050a120204121103010c02 68
    0x20043ca2140c94a0b82c81d4080381c110340e0b440082c1e040207041003400f07c10f200701c5801015045041c91131300210402d2400d02c01400e40d01c00404d11805024005103003824103100700000744941204c0c0301522605040102e8980c8100e0301c0115140c0700c0c141c40b078284d0000703409070160316202d650140c44100c00d101d403c0103082c405850b00407000e00c1d0f0802c454008d0b01d016403598050000342c40380e901c0b0164003420450078146081140d1f07484030100b1041020038400c60f10301050b6100280700164000d40c50b034440d407a09890580382c0110400d0b9803403011070002140110310440501503240f000607030390040d13100d86841e4141c07004080110301240040250a44207441059019650036a0320201014400841490b1171444450071003035855a00010302840004610301c9041c0801c0d222200070041c0c2d41b5810006003110401c0784c203600a1203c08600c4040450203540489180010345104651f202d40300c620001003500d000c5800d4840b450944201c0b00542014800c3c020030701003a030010002d42c03070020394070380d132000b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 137189109 1250 137187859 137187887
    0x603230109180b070309051006061403070201020409020703120b040c08010506070302070504051e10030f03052b0f0b01090305100c0216090c080906040b010b0f040305060f270d 77
    0x4410b261003008182d103602c1c824080e00065a01050f43c4525007405803410519160340301a452814008104003900041c90391901c03500401c0141d100e555011003a802405a0390100c1202c600000c2e4a008055200c42c4036204030891752800c01040d180c80c000d020403101d4050075080410384400051115252400250111a11030b104454100c4c3d1607401013416900c0030b5a0210b0648088080b2041c80c4500380303207555010300c0d04020164030300d1641d151000f0b00725001c80090309008000408451814407440c1032001c1c0038100030a80c0030a4410984c240041001c0085050070624001181c07000b9032042080008513a0000700824081030039409003c010704081e41005d080d071190040000201e007070100550300801031102c00059041140e04085c0c46000014180d01094208000f0480043d012958081c1500c401050242c0c07124180624020948101d400242c210b205103020450340c050305100c21881150320711170100d80f44100e0003400800c10b1403104005101c6d04840c060908107032050324190a020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 137190359 1250 137189109 137189141
    0x1090b090f131a011d01081509040f030e0126060406050d05030a1202160f05120705010b03070b070302070905040809040204030b0601030b030f1e07080708070603230109 74
    0x10a00291106403001580c140950300c9600301c01c00150083c0080600400030300f0100c0440c0d50000c18004107100d058121130504c0410804140d8015000d204007180d4074014103d0b10b4a81024240342850f801d040c3c00c00c0300044d43c80d00c0070681d19403040b013a000010400c2a0700d880ca510000001e103e403002c00400f0903410503600e83c40050280e03036045150721014090000346035918a0241300420400380914410241d9004000f40201c0c01c0180450008250300506c064860b03500710300e4641d08200d14204080144213020851900344a41907202c4822440d080701294a0310750345041d869058002d0741d5000d0056040307150304008013100b83e00040d500621407110b0f14070f03018404000a0498006400a03213102c5655400c219095030540325010140384110001c0101c0c50003400d40981c2c0e4584110304a03140c0d11491401c00490760100000c01c080e000e00401d80b0b500d00e849030401d0f41e513007003070303210382c400190a111104440d09098015481082c260f0012081c4580c200940d2002810155200c10100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 137191609 1250 137190359 137190379
    0x7062307081201120b0109060308040302120f03180301062103050a12060605070201080a05190c11010c111207150207081902030414040509100507051611040509030901090b09 76
    0x110340c944981c180a408000981840c02c0050300b0b1170b103240b0105070400283c503803a000d42800816004020380302240e50444160b821031914000d5035082041c0130110315003a00c0003141b40252a00340030305007040050140c1c000c018032035450620340711000f081d00c04104041d11721842007011921440082c01894031318103103d04603805003a501012107503103034850800907001280510131580c3c4405860342010500e0810702c8982020102c901c041c21084805184080d80d4503420070101d8014002c82c0f03920f440d080c00802c112841c01c0406040000d2510083c03119024100707003040410070a40566031529040346900058803107034a03a000003988140340a44031171350103111244010042d40028240252203901454481e407420350707a0b418485d90030081c148954180700c1088001400001c1c805080e0321a2800828aa118030f4000c0d61280b20781540c0d6070384034110446c00018000d02d45170000e0800f8050703800b0030441e903880317123000d4490003401038290019400c000c04025000246000d801b5000000b401c2d003800b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 137192859 1250 137191609 137191627
    0x1a090a0b03010902040918110f0103091505040c05030307030c030e0a12050d0305070201020406020a021512010303020a03020c010903020102060f04150212010906050f060d050a061211030706230708 86
    0x40340d04241d00005806800142c20300c291146c50152501854242591150403012503481e5000440d0503481c10340510f4004058452503842034002d842d00c56046882d0313002e4048010700c0e80000c0c14003194140c071031407100b5000003a41e080000884040903015514111040d001d66811a00074000c815a2584041160300201d480d030440103100d94021300c19030050100c0e040401001e010344000420240a5907c103200030040907130046003814000340e0440e122a05070f40c0c408a03246850090b1402101c0c000350340c0300040105900010b8004001c0c1c06902169401c0382c00b48011144204940002030040e007002c1c02003845040340205080d005440f801d0020000c100704400b0750201e82200c21260b00e03c03c01000108000d0883d031180401801050f0b0f603408040181d20081481c1344141e001c1c4c800c045585200081034042c540e801107018066014824003561a1b5040900028101e000158032a010344100090018042d050b0744000b230b1502c0411032015140b01400806030741002c201a00c03550010415404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 137194109 1250 137192859 137192879
    0x3090109060e0d180b0d02090307030615032609040b042405010e0904050607110f01051003200a1203030b030f0601080f0105060a03060f0b18011701061a090a 69
    0x1003080074090090003840d01c0010000c1004014403003504c6a4541c28070140a038044400803150810505070b030240e502c1c600c3c040031900d0800d0325130020b0880e07842c01030007004c030414a44075101100e0146800e681d20031b0b40c01ca00d6150205c280c2241150b004c0d01089a01200d0030075030806c0300d1030b0340001c2000070046c58000f000700c02e011708055510250700c0b1310a010700c015070300074440301c1d4a01000d598180031450103a40f0300d0b82d00c400150012007800003400e0089210201005040900c0e0a203000074080e9040c45040c0c00b00c48032850000301c1d036824080704401500c1c028030499110000e8000c1226891902e0001ca400d0745040d21704040d81019252100e800e056181040020715403900b40380104419850298aa0700304446090320702801c2c0d050600f4401c1d5540e0701001101980d800800000c0c1008142185400405a500d45c1c19040740f48860020070b51b64129002c50304841c951904112034034030b5900c03038034200c0300c80c0e000f400003580400781d5203d03003005000090701101c20042d00510f4420f03115034880c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 137195359 1250 137194109 137194121
    0x40c0324050a090515040e070305010c0305010e0606160b070c0606140102010509060f041101200c0102011b02070e0402210105100906080c0d030e060c030d0c0509090c0309010906 78
    0x90040d442880c10846400d001c8941002080f81d483c040005092101c041710104440b9103040b48500c1d02d843d095035445005020400003954000000c002c030300c9045401a010304401d02c28400b014041000255580c10500201d8918007248a500030480c1003954403000d101c030000d0010000c01000f6410380e400a800346c419000070301290014110100707401d000080c00d60740300901c8480c0680180041c04100a400c000c51038215a0011450109540300c0d030049a0700003140509030301d6241048c00d007410700f4a0100340702034004030a07030003170000c526100ca005410040350b50581d00164031564040104d03480c03a0043e690803a1000702440749504142180740c030b003000c9500d00301515955034400d02ca41221208030220003003005540a10103149800318a507110070381c290700c2d140601c0d00301d41c010003058800c0f606415501001442c05480c2c200b0708500d107a0301c3d0411741845900c28600110308401500450960b9030500300200b820740b413565002c1082c036103904060078580c480d6407282081800204a400b9213 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 137196609 1250 137195359 137195411
    0x1b0a12060815010504050c0403120f031e05061008090d11030705030720030d050304020d0507050a080709060803130506180d030e030c0909100b03070e0705120c09010509040c03 77
    0xc0502d5410301c401c100442e030300034000c440c0644c030821040000910340040240c0140441c10015004010f0407000d90280a401c20742204800d0318003030f000f80c0c1010642c80580107000c10340c0c011590464030b42059500d03420a80e00c0310b038a0303440380300b1a02d80c0a124501e0021109007520581c0e042000554031140f4540054004403481e0449d00700a0b000d51010000280e03105008900400030900c9081c005031161001500103800340c0f441c588584240b10b410031030704d40200300250180280703030790711442c1907120034040c018103076881d003040030004200b0000000d460400c68055844040c4518040c1000600d80c07101c444003180091f1254003850b641e03030b0700803081001806919641c004801d05400c0508084008104505c190f0281003413281600000554407070200080f00c001400500303560010349080404da00c06403000e8580800c1001c420303400006407e40008000c6405010744a009036584140030f5400c089000035024050b52013503152541102c0350f0b00c81700e8100001c0e9031710440c030f80c00c2c255900a100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 137197859 1250 137196609 137196643
    0x1f030c031a0705090d030e04090c0b180d120c0f0b01080d090501081314030906030408070b060916030213171e0c090a200c0706081b0a120608 62
    0x90780649070321460002d5200001d480d1051600e2107550001e03a5403001c110010b01004444403481010351201d500c07591902e6007010403480283d03601c10044809a002d44d0700c100d07910b404602040c0d07050902051500e000c962011903588050b0116804a4100c1c00401090f5111a0300c071104ca0f0100f40580714081c040c000c1400900400264424081e00307014040d0301090402c40ca200400030030f0402c1c0e100394829668000a040044071020f210b0a145015203180940d1165000050008000070349005128192040c10f550759680d84180400000f00c0080b510010205885440c0d062114400e5000300004012034084050f046d486000d040922019030072515001e6200c0082c002070071002c107203c200c4c00308800000380204400c442c007284401d840178040820141d20394161030401c692041c1200b080002c0712400d6504c4007000410f0741c1d9180050311030a408150210b000c141401c0e00e68040d40b48010510002c54030b0176000c01c9049926458041041c3e84043c1e0315100403408040030301860343e280880b842 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 137199109 1250 137197859 137197883
    0x210f060a06050c03121810150503060408040303030b030114010b07150b0d021905090f0f010b0a0804030804050f120d0f090203190816060509010c0806091f030c03 71
    0x400e200064006400800c00e0050511100341d000c48000f003207400700e10703501e1200b1403151a10040000b8100c4050120002c030302402e40118400c803915484486200a80b000d100901680c800515407981015038018019140410080c03012070300030b8004040d0a140034000107801d0486203260000cbc0702e000e800c445170450001903690180705250030f41c0610107141c1201045000c2080000600000420f14028000c1c3c009d2082d030803414001d081010000c050141009445140c1122031484100c3e00700d40c00d10044441c4000410268080c03401e8554600240c0c5980505440c1c0380c605584415009001711209d01c14104110304a04080c070149158a26940c4516207030101c4401d40c81c2034400310300e0350940162902c80840c0269030000b034000b03050200781503e002254028180912107125403041d81002d0120340b08107004101e400e0740507500c00c3d10201c000b00b0405075851403c541450303060301d00329400320b003100109c0d604000180044100d001d20f00b4560f444280d803544c03070004c8000541c0c019102500100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 137200359 1250 137199109 137199121
    0x3030a03293316021201050906011202060c0111130f0308120408090a060e040c0e0f0607050f060c0702040b060306010806100302041a0405011812080318010f06150c0b0408210f 77
    0x10000f0b400c10850700021f0000d03181280569079035400505c1003c0b0b0300005003d00d44295110002190101b0346503000900151a00750140c4040307034800300c40104540340180340061a50001e5036210306981c5e0000c180c51034440042004021000080c1c016106904104903200c0150f403509070b640700408260301c0780b480c0300c2c102c80d0800046070860040801880566261a15960b40e000a00c401410044540c15114415400c0007440c2c0705510f000a0402d218401c103002070500342d20040c0020910845d800d000c55100722050248500090301c07400c0c080380ca0b42003c81c0040c90800c240310788002181c030700141803035543c0000c0c0c401000a02e4010034440780000e020f002d1542e2001c0d21000400b1560b140d0b050246c80c001d00d5040d1039483c108080c03c40480480441d03909107049034100300e003441207c002d20004035a08114002401c262240704011104820403010007801410b004611b25000f500551840da266100c4003040d900c800d14200902910f00032842465680c1c4e4000c0b8014000040940301c60302c1e050b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 137201609 1250 137200359 137200369
    0xf060a090903270b030f130515010f0b0a020a0f240204030c050405060d060e01140711011a031510030819030507030216030c02010e03030a0329331602 66
    0x7000c018209560f0790202400b4241c4400116074201c20a00d10703924090392043c030b40b525100b10509006126004914000b85140c00c400f059605079500c241407035450540e038000d601c015101d08003038400035810050b84000070811801420141d01e0040145a0003036468032042c0c80842030b941c1c0c03a50740c0c00b13601203000d20500000482e004007401c070a030703010070050800d4800200201d10040000b4480c03500c55105410a80e0290030260000310310701c80341c111904010342c01a000707035408510380d0000e605e0702c01d83c3d11000700300076603402c21941c003d005005010f8059042d88013031540106540401e20424900000068040c03000b4030000400318083c035158840208010b0640d0006021441054014400c200b19403481e60341008003258182880883c10308240b0041e10798494000c50103a15000200b480800c0c40e03019080000c0020030302c0400741840d100320b00c650365101064003c65402c0324582c40c0a446036005240c0e0145800c0344d9400701a0003110150502245601221f00c1e145036407200300c018011418a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 137202859 1250 137201609 137201657
    0x61806140103020114070501110304031d040b010509010327080c0d020606180702250f05060403050615060d0911040f0218210304090506010f02030c03030f060a090903 73
    0x200811400c895141d90002005070901e06540c0c1865480092094100002548115034422050030816120b14040c100a000c0030081c4034000b8001954110414051806110310300c4ca440051316040c0c184000e030340044009110b2401c400a80e6072008150b540240b041c04d40e0741c003465104810340c50b540c00c2034822690034000350003041025503001105000059580c00942803010307034010f9040025aa61900481c900b51010ba20141c010840b0110070601e14500183e040a4460515a407511b8070303940d109000d041e1040e840b001d000c40d04544080342c5010300d590720000e03100030000d0100e424000b0b0610164210340c0e6420f003c8131a1860743c03201e0440360a2600440d41c50002c0c948003141400c0d1600282074841d2213040f10301e4401d2003560700c28800b05049603028a103c03203c54084a441d03940b6540c1c08070040c4816074025020880b41d251948981c0c2c80001110f41c0c40c03223140007460039500d0742106072040f0070b40641001d47c031106c40540410300b42d10620840110b00d0082c4d5910f2031941540c40d00f8070308012 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 137204109 1250 137202859 137202881
    0x1a030a1b050d290f070c170a09050a06021209090703091a09010f0c0518030123010e0c16060c0c02040f0b0411040f060c08070606030b04140601030308010608040f061806 74
    0x404010134101e40300d140300d03801007440c2003114140980c0c0c0341c08224010f04d211a44180d401c04a01401515800b000c080252070003620b03408241611020705a80c0e400041a00c2d0301001010059880035003001487d0603040822410045010045903440344008031501c100d8840c8645d8030000c104a1180901941341e400f04840001c201842034000300800c1441a0304500108194541c0e090015407400d600a201c011301c1030800b000215410100d011000000780f10301c0380640405c001240c0000010f00448100302280c1c500c40c0700102003596620040c01908400b90240000071801d01d002da03c56001c2e000300840746e50000107640c420141000116a030810030004910000d01040c0401c03c851006141650740030f003000c5000e0300180c60043c8540c4140c44008000509240002041010400703110740510700c2080e034040f0185540c032140380d072581c0074030025000521900042100900480025401a0044e1526078580d00507032a8a0b090711101c0050a5203681c4080b06407080c00001d100b035403c610 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 137205359 1250 137204109 137204183
    0x403150c0c0b010506031b0307020106050301141e040f02100504051c030815060405060d090201091208090114091818010203150118080115091a030a1b050d 68
    0x21058482e15001041401400d0144074000082801d0ba060090f00c01c00c0340d40c1070f1460030366900d06910024080c081601c0381500a40c2003402001c884d0302c02c0e2001d60712580c0301000c0c00c0d641c0e085010714040c00d054064010784542d4500105403000da100d0740360106d900560f580f6011b54884c5444140000302c50b03420101801e41e80d2071402c42d00025400035149400004070302002074804c02c481c00250041c0300315441564040340001d0039038104451a0060509103000b42c90390110329035901c0d00d940006587c1c0f08000c08a00e8100100c6400d580540100301e005c0038622500c0c0e042281e090f001ca03020121302104a03840c2252a020060342c440b00e00c07000141c040301c5a000394298244141c0c1380900019a5003914140108100c0e210000d26601008000904204e8002c1c02007288034840b40b07030711a1207801400c000c0e90404060714090301c0c2d1312940940c010005001802400c0b4143c03150750340d0441c001e0000c81403c0f00d4080c0000d06660700100c0040103400741e0b80c80c0f05001c0b5081c4603c07008040c9034082e04021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 137206609 1250 137205359 137205377
    0x151802070c08070e19091104020a0e0a1203080c0313080304081c05010806060d0b15030312070302300610140c060609160804080702040f1a030106060306080a02012001020403150c 78
    0x161000c0b4000d000c0d42e01030b6070258446540d4101070b83c642000b0bd02c2070b5001041c03002e00040c60040415201701d8540aa107e5401a8a070390780784000d90310003200c24520705414003141034005400c1c2d100640e40140154005400c00796411400b0008448000c40d2035411510740c001809400c80920143c0d80181c0100c03004420381040760fa400d50b403031400070a28100b0b240980a9600c40c0d4034280304681644103003101180e250300d48100050700039000003000c118000c482030001c200321940303c9980444000c04a11000455480d60700304940502003603441d804003c1020303604210410344174050311001020001401d00352070001e082c005102c42c001d100c0203189000718603081c00c80e60450202034101c1d820030a06039031507405002141c050910441440b03001c1c1d00d019180380c009144c0480454040030111300900506503900400c405640700303401a110140c21031070b2607100640c0035680c26800c0b0702180002d400501c958507203060890700a584144c1c0d00007100780d0804441d1400d4800d0354082072a60800c500c003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 137207859 1250 137206609 137206613
    0x303060623070c080f0307030f090612051003050d021b040203060d020907050c0709050106020f0109030219060e0a0602030403080c0a0915050c120409151802070c08070e1909 76
    0x2240541c0080301d0810740000d45902030118601100c0083d00841045424109042a01603601c1d4043d210030781c0041c131a80007404106204800080807076070701e96182004e1080300e0011400402c0b01800c0c20711100700030540000000c40a100360002d840107034019202204a21070054003038044462001e200e02c2c1704108000300e541c1c07000c80c1c18401c560165003031042580c1d030040540c1c0500c5040107074140c0d441021030000d000c5880e80c000178140c85169080d0350b1018000c040d000c4c01d03520b1b00b000c014050381000482c2c0c009904100200d14041e406940c000c202c0a1a401144d0306103007000c10243c66242d00002040b0074180c00c14080c0390400c510071542d1303190180380c284c01814401c85000340404d0300109061801041d1041007a00c10f01940351082e110302d1f098440c00072001c0c0d441031091014aa003407608580d00c0c0311810284204035606078000e649035082000b48180254040030b000c40703200b03d10807030102d0040c06c108103100c01f400c500281100e040c240080e03000000c0340414010041d15081688800c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 137209109 1250 137207859 137207897
    0x120b0907080a0e070b2b0e0a030e0d031e050f030109020405010201181e1401150504110703020a11031f0603110901080318030c060c030d0501120507030b0919080703030606 75
    0x600480600d40822417500500056006109a00f910846d4100300c0000707542c032000b040c0500c40798840d444640780400d02106000000b4000640a00031030001000c51807102080011103010200e0307454032a2401c8088151860103800a8016203607680e03007c00e06100a50702403069600c50b9040d1180c000d4806820380e95a40c2d03c0d40c15418a44181e10542d10f11010807149041041200e5100c0d8000d026500f5600c43c4402030300028031039588150300704410a0b500c200c424048840321505a4080e02c4292495154009070740402200e040d05881805503000c90f2001e88040502200d180401c08141985141044003d40301150581442403005100401a1070300000c110350008125440050070850721500280c203061103e804990400d80c001540852031a02000409941d800c3c0381040049907200d400f507600e9034410050040195120100610215503441c120f180d2020b885401c40c0c2d00c500e02501844a080b6032507004807014940400d0200c20150103018100c0a1310452514440131004642940 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 137210359 1250 137209109 137209117
    0x61c050f0127020a020c060f030402010206010906080d030e15042a0b0d09150204060c0c08030a0c08030c07051606120b01020715020f0a03170f01030210120b0907080a0e070b 76
    0x5034450740011389600150003070204407003003800202000c0e128170a0a91400c965441101c1c1240180104000410b40351403900c41d880940d10600300078076a95140b14419801000004d43c0e0040ca803240700c2d0071083c0822601c2005216134412410341140414100e01b0000d1400d0810710341920078a000814041540100140c80e40702c07920031408680c00010341808849000c0c2d541030007480fa800020045902d07900500c0514505124001001c07415036500310f01e0740c590141c19945800105a006601c1c0410618000703543c000000c1120249024425902e1900e0445000ca06048841100c1c00803c002500404100c032604141d080a04c610841080000e448881c580101104c5003100c82e0001c0c2040d00c01c00451541e0010381c1d0071102786160740e040103070400c00d0203140004004d0b10303c030011710b880c220f020704c050480c2d42c06001c4014065141d1001c1c1c030301c2821242010201c5650308841c510303c0c1d44000610b1b000e004180c844000905021500030b0580381c0e4040e4860099000c40c6042243c10660b00840d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 137211609 1250 137210359 137210429
    0x50402030a03080402130e030a0908070803041e0b0c0705010e060328021c0902030d050a02030403060921030e070f120f061d0c0406060e180402061c050f01 68
    0x10b003ea5a961700c0010b150b51254005090300525152100ca1803200000007001000040c0c2c44402c101944d0300309460382e8001500554802c0d403c20700c010400100740c44403c02c449040c030505ca241c1d40b600c0e0700c80302009400401481140c0d62100c4020446946c1044c004c0840c028240c801c54a90b18083d41c1400e9030702d0710304486401c1d01301000584030030f540869069032481300c100ca141490719007040d503215000e0062070009912031300400980f4800c085c001d00031140c1d6000c180d00518241442c549401004140013a01516080e91a000c003c103a1a5180ba044a10150790b450000700c00d0356000306546442c0554105041ca4040201705004010792020602d038500c2e4800b0500004040600d41007002c0c1040303045014201c810f40c2c40b4000c41d02c0010940c030078136000589082082d03603501c24048500c0494003010a0300000ba0b001c2007810010005061030340240060070140c0361005003203a9454035240340e080308040941d079800780700c1010101000c0b10300501e02c00008224104009880f4075440104142c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 137212859 1250 137211609 137211617
    0x20705090f0c16080f0403050708070801060324060b04080a0b06040e0a0206160506010e01031202010218010f1e050403060608120f07050c06031015020f0d030216060e0a15050402030a03 81
    0x500200000780e4211035420322105146030701c803030717488c58108d81c0c1c0c501c14002c0c40c0550140c1c2a010800600510401d030440c0c2c0c00c106000081c0000c4035001c00c5c4400b41c100344540701510b648000c80c7c06803c100017000204500710007460096160304002046100141519120701c0c1050040f8884040c00221100e0300380c0c0468805079100202092540c48605260380180b1728010000001400030250b071301d05041343d000e61840c0c0c01004030b81c0740c102e0803846501d00a41d503c4850481500e19944644202e01c008222400d00b4800300d00c10f0100409484900c10501000030b800090500401c045030081000805501c0020204a40c905511408c14041c0140003030303000c080490f040050040412aa14001401510007689c0b410441000d003034903034240c01707040140c4c0009208010003903c0003800519858280700500404d20807007008501030740c02460707003130500b911502080c2d0114669204a11080f42464014605a01c2034076104803407901d5101035442062810f020030001da140800c181c809540d043c58 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 137214109 1250 137212859 137212897
    0x20901051302090d05150901051605090120010c0f0306080316022101020a17070903020123030a0b0901060c03080408030a110307021617100b150a020705090f0c 70
    0x41e051000b4012440526488450b0161200038020302255802c13442502c424800c0c5555254807070b09090303903825540c03081543d582c0304001c81d01c1885800500b214000500d40740313810801c00031015500c500e401d0843d13180c0342d540748540c4540c070343c20008402c0e5913034140c2170a00c00c40b41b800038070644a000309280003890304040c0000c8021580d40c2d050001c100210306000c808041c40f03001001b8001d4104a55072400f1400d40f60390710560010f80c1144500c2107100da0388401c0c40d236080da401101c0801404032180c020031712446101500c0b11882000d144603e00c1c010700041d803a80380307a042011515040c1d22540c1800500c0040c41d0120747d014412039401900f000b51556261603070124240142141e11180325202008018080034550100e1801583c01c030680790440c070942c88403443c100a01c0040c0b11102c1c15072013083e0050603c2001e0b001141c0380700e0000e104041080100d00800f20301d40c490100c0b140180c21040c41070250b89402c84c052a040404162540303082d2804404801c800d100760481088130b501104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 137215359 1250 137214109 137214139
    0x180307081006180207051009080409090f05060c09150a17010603020909010b03010620070e04050a03090b031021060218150903031e04050a030c0602010b0a0302090105 73
    0x611801000c440302154462110514254000c1c0b100d80a050b003061000b443c010b2016205000352122960040058140c01c07410141110007020070840c11629808280301c0095801400c7c8205161180119584014000c007480d0081c288180100803003c0d00200380300b02d406a403240b14008440c5820141120b9940440c10382c1516a00c1c0b1000112030461954070000ca80c0b80e915401900b0000016101c041f010b0b40c0300c0000d220a80424042d201c00140f0b428010100c08148080c803452010600d016141116202c3c040c55045c8141214240e960307911404100d420903a0103002e41c0300810b0010466811820002d480300c5141c492440354204240c0042044280c0c07003955200c4402640e4807072403c544c0c6030f080c42c40700c01600b6032490519100c5d174000840071a00d05500401c440f9014130041c061450100810007100c911011710164120300c2c0803c2c000401c054440b5005100650300540c081217890740f40140003420364081c0c141d004d0241c4614001040180c070303002c226505544080f545500d9003e00c4c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 137216609 1250 137215359 137215363
    0x50c030c060c0405210309060904060f03030807110c09070503090f0a0302010f0b030604080304060c0903050d08042109170a2001080709080309060304030309061a010e0a03081803 78
    0x28102040a80c0900000c1c84001c048502c02402241c005440031003c0f20140c81144482004507034030400590410400a043c0c0e15000b4002c002d5100002c1000601607240c0004929058541e082100803c184c1300c1031108c501d0304203440201001089006181d4980c0107000308084910107440e00c03003806408004a407010b6024040300c1c10590038a01102c40032107d504000307020340362140c62800c0140c6411145011410045201441203070040001451600e8503a80d50004000c08032040042164441001c0006401440000003018081d5903024080c10142002900a41c04079459280350b070140903400b22558010300d404d0304440c220034a46281146100409080655005c001000c3e018a100380f84108070144c249160382100c20b0381d81c80503a6981590903107401c0ca650040c0c4069a1060020703803443d01e0702e44000d60b0301c40d21038a07001c40c48040030b68401c01500c3c1140b51049038428080c60b81145035a008540c2298442d080721000c49a0340f650701c171307650184a1a0203022806005815809036a101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 137217859 1250 137216609 137216617
    0x7140f0d0e0a0b0c090f0d05010e0303010f0f0506073507060204030c06030203040503120c040e04050607020d020c0604030605060f150406020606010309030e04020306010c0804080307030215070c03050c03 89
    0x440140a8015000c80c400e8482000040450f145060540444d60f100440c4090358000803000e400420201482c42c10005000c02d620b4040ba441d64843c0458400d8200500107540240202c94580c001c0364240545214049000d0708000e000708024001d07d00411000c5095000d400c040e00041a07a91200c041600c1c00900540b010701d021400001b0b014040181e40d500410840703000e2111600000d4076003904805910055a000e040c1e688140004c407144001e0603e5250010355144034107103410b0b078404201d52400001c0320f095950380c00c6401000710140c1c040c05081e82150f217500c0542286c00031078001419600a60102803c0166551300103000b81c0c440300384400032000010070325010181d510084102aa10900a01300140110400324a00b5406401074128460b4107445071a402c803d5281404020b40004100c02d040107412008100030841c1403000b80701605101c03010b59907400590a02078078028089800d1124485803104004007590300403807103040a6454500140d03182c501c0c4078410704d5802 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 137219109 1250 137217859 137217877
    0x1e0309010f02031e090105010f17070f06030608100606050d0903051b030a1119060506130606030e0d1e0507051e06040327140d0606180501080607140f 66
    0x301c00001c1c0f10751620f62550070b0079010b04000c0008081c4d0317600c3d800d003401e0f60401c0c40741d50308d0760700003080c1440160680c18540100b041290100e4840c070383c1d600701000d40c03440e1740e5000c6404a41e5071013042c006c1581c180462000d01076403d0007880510700c2c00c03030f0003020b80c490540070071445542e030901c1d00300705445101120040790004c003a8044010700f01c0c1e60702c0d8582c1e00c40907409010603144881040c8460020642d800d410000c03c20f59a40d200042e1192000b811004115030b0740201110174010840c5818401c440284c103250340c000446c482400d81c1c0500d403550001d0040240b0100410301c3d00e20700810808450a030315036180407501ca03260351030814684500b000c540c44292100c00d56400c6c10503000110148218040d980b131044104c2c80000c00c40e458040050861000082e8450601c84030303014032581e540460000d8004e94800156844010440c0c105402524a0320068018486000d04600649026141020142099060020000d03201c54a80307030085400750380200340d6800038401c3d181960310b852 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 137220359 1250 137219109 137219111
    0x80a05151f02250e250c030908030c01090c05240f040308030c270907210e060a0b01030204061b0f061a101d0904290702070801021e0309010f 62
    0x803043c1e83d01103148001400381c80d40107401c4500042c080c4500301c8010110210700510356a50340d00221046810580e402020b40c02d00c001d255001400d000308100918440b10414000904011549000415520164400c0303108040c5441c00280d031b00001418410b15042c1c0c0a1039541d43c031001c041d003000354003440e44040c001d82804010000d803003800300000d0200200492103c0c081d00e0000f00c0c0042c010b01014803864120000000003418980140107407411445c04807443d0300c03012680003050003560388642c15403405402010912961010600030304403102c000342010740c2001d04243c40140080092212040f810507810442800d0241a484100c1100d401078820f201442207002d00030f4810000c0c826a03402a5203a0552100c980d03c5040b402d502c1d00b0b403410022004990400402030400c3d4003070803c0c5d50040d092104030900b0880d241c040b03030b0b00344c0081c9134800c00c1d450304040207803c1c001640d101d1125640100310035082070000c50580c00200c003120010f16141d85402b41414010300c5180300f050707415 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 137221609 1250 137220359 137220403
    0x21b0102040323010921020c030105070f0315050919090c030602030403170115050d0209030706030605030609070303020c041e090b1f12111807080a05151f02 69
    0x403000422295084602043c0c50810b84042806164200d403420040545080340502101011201240d02c85c820303a803592046542c245507074400603003128000c0e00d1840202e40c00b00d40c207003201038141c05480700f0384180035030001c001d510f060042400600000e1214181c100c5204400031009840e41c0b0040b00c0c00e80008a0705802912841d2802c002c1d402520b00303501080d00d5022800000a2508070740d8103a402000c03140d4401c400d001019206504403c40c40c8808039000d109280d01d985040103100c0090119980105805141c42d0915091070b8014182304c107240c0001e501800485d800151141040c101a100010820b44406902114003411800e1040481c10150390101788070031052454000c0c0c00101c1080303040b90000d40140c1101714035204183c55905ca9643d40c002040e0a020b0420303000401501c90044080b4004811059010440b081e00104030910300f4040f43c2505803107030035404500d0311101c6d8502050080000c0d51003a9400e51000140030400c516444148203012890201030325803251407203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 137222859 1250 137221609 137221613
    0xc070308070f060608010504170d0b1806040b060f0a0e0f060c0609010c022802040603020904080307030b011d0907112b03060b040b0d1103070206090f01051009021b01020403 76
    0x48900484003a15200d04144c008520100184165802180e10103110500c074503500c4030b50040c03a00001c8545000c0b5a5a14201c1955110101c140170b00c0c24503e0703c13511a0b403400c00f0800048411041c16140695801c1c001c039a01c01003184d08654904c1c103641001c440c80e00c028070002d0005251200000d400200c007081040003200001030450082c2040d00c0284000c620b0303564100e0f84c2c1ca0044410820041c240010014401003e43c4840d00396070015001042d519165004a282d50b001501c04a4134820300004005120342d00d8460000e1170582441d003010a1060b0302c0d42c4c0c0700da0100d8005494411a1640301103440c0900130368004400d8840c074020b983ca1a80d401c1c130307240c0328000f01d00f1011901c1c440d03096032601101d1181c4102400d66010001882c1032604108456406801418404581036a180c945c2c0d040c01b403400c0c0c0070f0752060003158001e0004d8076081c8981414601c51510210040c0c0c10b00081c0400010700c80c81100907256403410058031142d0002002c1940c1148841da400e803940b0004001c81 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 137224109 1250 137222859 137222873
    0x41505030403110c0102150a1506050711090f04110120070305150103050303011802040b040e06011e051602041803080708010f05010914040b03010f0203100f030b0a020c07030807 78
    0x7214900030b40352800c4501100c10125240d10089881e00d00680090410720b01141240c0d030f4858204c66088000103001c510030b20030340d40c205030607040305000c150007241c200e080043c0c1d5031000007216015500e00341e030303800c010b00d07130707814540028000a02c06030354407403490000d91040100c45044003401c4d0140c48240b9074441d01940304c00050105807400c0c016669203051300d02450880c1812250302000a52544c0e02c0e0440701c907640310328200b030ba0041036020800000d0201070107000e00040c2001b019031a01501f8040000f42c4140421f841d1844801c000070442000d02d074100090303d10404502c0b80d0003080d4049031001600801c0d601d500c8000041841c0c2c02c02c000c0c0743c0d005190760301c50740e120b494620b0f45ea600c03000341d048807050741e100301c50004020304024440308124003480300441c5000f44c0081920750311607001900791550000f8209026a02008201141c60741d40c40b818000c0c1122540e03141c0060860321900301042c070040c2031320041078000079512420401000204001d64200034016100d071040d1034449 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 137225359 1250 137224109 137224111
    0xf1209250906080f060a150305031c05090a0f0b0a0e060a05010801050708040b040305160b070804020f0409081204020d12030e0c090c0901080c19030905010c050a0516060204150503 79
    0x18103516140000c03603e000c0015444114207422001000c45580b0b80000502030080c211040b00b0b11601c9240c0040002d03000c0024242e130016414212020170f105040c071000321800180348807010781c800b5444d000030518150081e110582c00004c0c0000b40c2c0d40e0154420301800f0214a00c4c052031040d03400b04400030207658032403416218040000e00a90b00c401c181140d1964050b078000d0464029140440c000900540003848082c010303d40001808410340c4906100d201c1c11200076010840740007c010841c60508598000490111400c00c42c00c102070325224010b00800b80481c40e0309501e20003003829550380502c3c41800715400001a101e00020540040c05449a01c62130348840c13190341200072491800d002600d11809140510300d08140b1602c004607001200a412051302c3c110400c4105800200412480d604814548001c2204082e40c5405400c49030040d42c960300b0400c080c45140b900a03030100840740100381f146000c410084950400740300a2040354040207100409100c0f418050380c000c2c01031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 137226609 1250 137225359 137225369
    0xb040b0a0f0810021905071b030f0302150114010804050a080c031c020703050a051303050d020a03090f050a0302010f02010e060a05010513090503030601050c0a0803070302040e0109020f120925 84
    0x40d03080945002c1090050340074a26082100d901c8640700400e10510075009001d10301e02690344000d48c10600481e0502c2018950004d590b04110540c00c082403513010090121104102d5513400859071500c0910402201c4544009041140d4000441c0c02e00c4400c02c000c800c01c5410010761541d800420b101c1c00c0d584d51000c0101e00c0064100c4038040000c1a031417007668020764060f201d41e85000e50408085849502200392504440e5580f140803002c507100300021214038070590000c028044550402801843c5650b00100120f03500c0b61003440261038681020003220782c2820160741c09081c07110168050721500d038681c2c41c203211f2402004403072909a00054102c0d24280c0b40850004a10440b18003a9000e5480c090300c10b500130804111075501c201e00030b040c2c1c10b16285c1a20000d100a540351603442d8400d40301400040c0e0081014400880c0f0500c100c2d00400703246030110f140c0084124400a05d014000702070711481801400184200010b0064416014010b8515000412504510300000394036007e4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 137227859 1250 137226609 137226613
    0xc020a0503100b032505012f1f0204080a080c03040305011103180c0109032a0b03150a0e0403030f0f0c0f03060603020a08130201020a1707110f01050d0b040b0a0f08 72
    0x1075483d4160050000c5c1d403d24010900107244030b814007006540c508080051a00500c10000400006094040c1305200901082d405014000c1d620030b80050340768221180284450710401c003c00c40302c0d100007204403a440d44403050a0712070116100c40f0342140603951014015508120480d80b41c0d4a01d0f60095110b1520908018500780c605000740d0341d5500007441c0b10303000c507403080d0701807001ca12104284a40d910486116484965111aa81e88642c0f607940c08010401000700501180100d0701c01104441c610a45400b04250300d07000a00a86000107440039041c03654808c80402504042e070000400e540190f0310500030305900c544000c012001c040c0c1a43c1c0001d240c2075000c14520721034002ca4844072001c0d0344841b00d90301c1e81420302c41003619003002203041d40300e10340c1031500180c1d003288002c02c0e1209840300c041c4c83d20b0847c00c06c0c144132500c643c003c4e440b425002c1120710f880d82e0003174207076850101405400150307800500d01247c000e0980c0b98015a0019421200142120880400b0803d03100d001003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 137229109 1250 137227859 137227873
    0xc0c0611070f0b0a0c0227010914060d1101020705090403050306010809160303120b0301060e100f12060b010c0c08070914070c0201050309010b0402040906330c020a0503100b03 77
    0x10b1108566a2400340404a2004201ea0010503104005501100b40002e12035252205424a1095000c50140c540081d20195100420651025200d8114a5080301010515030b2a220001a805200001008040c640580e401814a0b4400c00640018240280c00d212036800c040c00c028010b41c000301c80d018001080c071030025414200c0072628000300c1c0c4020b00b4a40b240d500f555002e803160107582e44521401d81e5910b2031207940790780174001e040041c65071071a92009801d0514101c507000d82260032160740103190036001c01c240321041101403007070b41d040000091850005401204c08849142000d02000d20001000c5001c40002c6402c00840322103100400c2018112000706d00c1c4140c08880b00008604010b1904000d540035000441d44605014000130f901064036000904a0304950010900c41c0e83c1c0304c2c0b0504c0f000320380d142c0401040000b00c01101182da408821800c1c80341c0144014002c100e18120500110340361301c1c0002000c3c000043c1601d00d58080031800354028210088902c4c131910441e8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 137230215 1106 137229109 137229119
    0x10914060d15030c0807030201091205150f15010c020d0204110f2106030606091503030409020f070b010e01030515070e03030a02010501031b051c030c0c061107 70
    0x900e02d02c165400d41c1001d0629209a070402c00503075000450600141c1e0300141c010086400c11011412092000c0c0340490400408000140c02484003d0502c8201c0c092424101c4c4600b41c20001801848001c10046880308002e074070180d0450710800d528800b41c1855081081c018884d410a180b0b026800c0e58000c0c01903000003030b202c0c1c2182001d0342c82140c0850007012650403c07002c45c002d1001c1c0c14000c0010b0600c11300688611180007801003259055241402a00c00800c0541000c40d07d5082c240f901c01e03000d038000c150465031062800d0000c28407038480d81056050303941200c0100300c0700d44040c13000b412078000608088180055002050300c0c1c0d9030301700010021402243e002090952451402c10b02e1000081c6171040b01c030103840d009000a8440c40d445107007020b0a44800c0e00034210504080d03500d080c035107101038501040d450010aa003508010b540c0b8010340344108480017141e0b12 = true := by decide +kernel

theorem cover : BRFrame.Cov 137050359 137230215 := by
  have h0 := BRFrame.cov_init 137050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 137050359 ≤ n) (h2 : n < 137230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
