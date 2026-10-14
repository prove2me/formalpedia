-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2153
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:48:40.612757+00:00
-- url     : https://prove2.me/submissions/473c819e-d526-4d3c-85d9-73c7521c9dbd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 387050359 ≤ n < 387230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 387051609 1250 387050359 387050369
    0x50d12050d0e0a1106210c070609051c09140108040602070206070b0105010311071e0609050d0f030c1d0118080115030204060e04080d0b0307050a03030201090303150b1c0b0612010807 80
    0x21781d04018904036051035801050005408421055000c80c01c0108147c0640300c0c019400340f01408810707240d14005031200344d00d441003d28620a25800e50260b03008940c00310a940032807a00210701c0c0c100341c0044070b0a040180c13007503650303580c200551809611408000e003c214010f00074a0b0065150000050840b4400744401c654242d0030301105000904520107006044000340340d01d6620160341c14120003c010307001000b0310070711404204d17048858210717000810200003600c04201c0d1110307a20058881e40d203003041042c071f11003050458240340d600640b00415508c00021402c2c0140341c582c0c2403103007110300d0202008409800e0210800840c6481d00465000c0d09064521000e1800c05640f40c4009000e01e4462141c165141e210040d640d1b202000510005d15006114040385566414064000c043c0014150006402c060b810411613040c00d0016003104d8101746020310344038510704056045034013802c441c00050388499045a49503504d6010f00301130542d17402c903c4210751600c41002d1401483d0f03400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 387052859 1250 387051609 387051619
    0x30f0e0d0215120a1523092e1412070810091e1212090206030411100f09180b0303030a020924090d02010c1202010f15050d12050d0e0a11 60
    0x1800d100042401410101e980c4000e00d042640c40c5c03000751440e940d06c502c070b0854208a10104010b00220b0101d000250901400c1910380b503a0400410304110404c10b0003032400d11003c9481c180700c9428940244046000d07a0402c0c1d4862030f880e900d98070b04080390784403846200c40c1c0307aa04c0c21041c00000d60341001c2041d10f142e085041c00b54039036a03d00628032500801701c18009000c5050800003a503401c0301041c658001c0242d0364915081c0b51124105100c2c080c03aa0140b040100d111080c05d029035070b0420300c504141c482d1440395150182e00b603203e107110f001c00e06405455803643c0c442da03141000a113001300512440582c1351900c0a00b03100210228201c01e904502050b1803150b00049010304035100560180c0307010408a40900060740d401c2d9110130010310200340d1810305030b16143c0c10344c4504c1c40100a001d05010343d01a054080c8983d00c81d41c05030720707403290032850554001944000d00b040d2107111814500e080c00102d1442c40102c40720414190326540149484508101c0e4200d0101d017000c4007191 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 387054109 1250 387052859 387052871
    0x240d060906050f03150c0306030a080301031514091f06050409080c0f0706050703200d08090c060c151f0f0303020c0406060e120c0a0807050901080a030f0e0d0215120a 73
    0x1144442c5c07810f014211b000380440c0007002c035181c0e40b070500c070420300c032030f0010701c484c2c0d503941d4070325140591200f032000c0e00040500d051a014440c02c0030b002564040c29005008003124102c0710341c2030107402c5107108800c0045640c0c0d0b00c00503564486010780380c4643d0040c25800d880e80f17021101c1a0500803515a400710a80000e030040c01060b4204050751880d03600751510f11102c0000f5211019041e9490031400769500c1040c3d084a40c1b1076108110a109c3d480800c25142c0d03e09004c41404805d0184d5860304a003508400d803007202d0100001c01940d4480504900c0b242d0651390000404204511031300400e0f00d400d014502801856010040c180114205440c104200b6142100082c040c51000204034071450a03130856919112003000440c0c2204401411005100d44e1151099a100c40c0740c03065078003c59103030000050302c03100804d00c200c0d495015281d10b445514ac151088840c0704404070965409004c20380b001025880b410740e04104c815a0031550382c1c1d40d0101d0315402e40340640040c40711180c039041072 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 387055359 1250 387054109 387054133
    0x501141f12240b010e03030a1205090c0d050d030606020601031a04061419140c0f070606090c05041707060f120603080703030902090a0506240d060906050f03 69
    0x8880c0c9412204141c44501e10180c040c640340c0580c00301c910038040703141455071400c2a0151180c1c05255201c43c01d07200d20680e080c0300310030f054a9000d06514080403501c007043e10762680902c0d401907940503008100341c50b240c05592002881a041a4209550b9940f10b088001c103440c0d01486803001404841c0003e0482d981346541d5880b040d82c08424051500d8641000725041144640003c07054451306000d901c264607101c4c100c0c0e0042a4002c5002c0106401c15500d10201000c0e43d0580d40118200740d490b525101454003000c0c0b9682c07203844211441a134038180000c07402124030440019061640c0d402c0c1e43d861400c00d0800b400c240110f04605580c00c0f08008006694108842c20050170322400c00b5020082003150040c0180031542c0060b0148500066400401d941580010f02c5c4500c200d44a0302c1031b07261214450104d86045988541045c83c5400f18081c6000021715030194201402c0020b1602d00800f4109058502c2c40c3e0000302c1076900c07404144194545000c0c4c03541e04c2c590907402880c0c101104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 387056609 1250 387055359 387055411
    0x405030304030507031209080306011706030c1c0602040306050105090a020a0e040e0a0b0a050907080f0c010509040b270105040209060d20040e10090e0303060922050114 74
    0x6000103007030142c0004c0d8403042500a0484141c00b11508504000881d240d00303112505d035004239010342c001400d01d1203100e010301201031410300442e40900140f1180d01c00c0350034000e18516134202411512548500440041c0c0b460008201552084101113030551400060001c0711a001c1c22040c445801405940c1c4143c0c0c1c002c00104541074205c901042d268064124281401c00c0f0303090181c65010158100900003006d6044a0f01032140c1c9411100141d6840c2d14007519034074a120540c0b201d82003005031244070341c0300340042c2c07101800003070000900c504903400103a481148002c0c2185401942100f80029000444116004000c240c4040d86000030b4038000400b640702e00f443c1c21388842d030303586400100360403d001d0303400c1c600604019280e65182c4030300000d1140c050440d281144010400d10114031a199402650f581c02c1401008600b140c6454080203c100402450320010306508403030800e0108d20754000302c0c0c140707014000010750000c1c0c900364542d0b20100209a503441030403a0140303074a240e1074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 387057859 1250 387056609 387056611
    0x30912060912020a064b020d0e150112080a031803030903090b0a0507080319090305040e010803040308040b0c1f0b041d1207080d14010513090c06030b0f06040e010e0f04050303 77
    0x80d02c8514022102100340d140d041a80300030a1606c030744081047c001000c040d84c407071030907010808101c41c400750588040c0c50008800740940350b1118030205900c0300007400d400244c070102025080104000c044a4131140c26202007403004d40c0001d859034156801d064000c000c50014006240d140d42c81d1144226004d0f04e035118140c401002004000002080e14042503101d841d480311001c0e0520500585040080c1b0301c0c1c0143c0989002c0103080800024485400000c6404580d0f200890301e040078a02102c1301110b0b00421000e14450040d0794a20307050748030320703c5c41c0d8850f0307076a0300b000091004807001030000b02c49007080d02c80112866607030124941680000d1800008105101d16136540c10740d45420a0716004503413220300c140341030528017654003c1300351049059880940d09464200d07869103c4c0c20544602c04c1d00a026410182000c3c80201d01c0b940140103440384c050f085000d0882c1140c04160140c1c016408260821204001409078140350844182c01500d00302c6210000d0030103441d250344a00c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 387059109 1250 387057859 387057941
    0xf0201050c0a11120d050f010b030417070318090203090c0409020609060a0203040b1305010e0418030e03070e09010624020309040c09080d0305090105090307030912060912020a06 78
    0x10204840c440f02103040168070341d6070b40c08918094941d0707088070050002d001c003640d186602100781c20010408022800c1500d01c1141c22604002e000c800c00d9076903891a5200010950400a000c0c5880010f07079124910b41008001075200142d44c1d00e03100b21000d051240e03880c1c205c0d10583c02c0503220005651080c094400703409084641c10b80d1440d0092060b840d500c51948101070030301c00030a00c1c5551808501d603200448400707885506204a9070410041201c4200829407120340145100c800407900c100400003124001800302d40a032510341c1200802c4034811540815682e460300400d01003084100c1c0c5500d052030001410051201c3d010741c02075202d0040072081030003203a40d50448c0c803065100d488060700034083d076016500c540c900303804010060501122020301541c03d000120310500000001c5880c0141c0640e900103000d42856445841c1000c5140140d0303405407500c5102e0f0104580050750182600c0540017070681c4900d82c50000141c42200c1c045010008a030302419411329404603650000f94 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 387060359 1250 387059109 387059117
    0x306051804020439020105010b033601140405010b100f030b0a0306060602011b1b0b09100501060c0b01051f030902030a060e010207020f0409050a02130221070f0201050c0a 75
    0x41c2da801380c2c51603200301880b004400041004c4030301001249800c8410984895a000703100584e2101000c0c0071a110903101d1145002c940800703001a10000aa03400c60719900003101e00f075801c180a105402d41e148120380081e04494001031100f0000e0074891420382207410b0f2441c040c000313034640014248115102c084400d242c0c40b0500082c0f1503840c903040350051079121800b080400d4449100900030441e00c220302b1241c440e00060280f00340d0013141c1e980032000814041000342c1d0322659411000d035002030041a140d1092041d107100840c3c142c040d160180001381d5940c0b03814181401c004401c541c0682c84140a20407003041562511100608006814024180410840d40034030100346001100c2c0c1c4080c03c100c0c6030a0b45208424010f400400b002c9000311154410340d0a00301c1000126481068000d180d540000c0755000142400f52010200b201540c4005007041804d4099040f00307000c50b91042012003981d0100a01c3c150004850b110440d80e0348000c010030325200b0b900d4107040c8203200d03240f8140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 387061609 1250 387060359 387060371
    0x23060304150608061003050105060109050a1703040b0301080a0506150105070f2f01020124060309020d08181c201306080303041a100b09040b0306070206060103060518040204 76
    0x41d10041e08080014401e01c000c6809078034003803c1c0c04401704000e000807501c40d42040040303289980302d60925415071b00004c201d0380300c1070700d006403842241035085180241e41c00280070002d2042c0d0740303101540c0200303142400342420400d14601141010320040112554951120340800346982c00820346825681c41404110703415524240240b20905440c0e69400000c03512802e08421504440340b461040b0007a0002c1c807800314845ca82500041502c0003c40c01000c200708100100e034400d400c031306402400070b0300c102c501e41180d88503915143e1141e0244204402d081155003014107204515280c0c4015820344485190280d5466558040c0351040c080c0c8450440e0010038140c0c3d036400040c20007100010030402c051656a111551241c0040f02c1c25141c00250311951061010240e00151040200803642c0d20b099041600700d040b2f42d005040c200340c1040d0389010102c40303601e040110360300902d080d80040070207180441c0010245da40c030340c00950003002040404114001048040b07074100781e04131008209 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 387062859 1250 387061609 387061643
    0x1240b030a02030705090916031808031515040806041109130b04150204060306050f01020706050a140409090f0b09010c05090d050a02150d1a1c02030709021323060304 73
    0x2180a0842182d500c88900010b112601c800234000c451406940c0d2020f02491000c1c3d000015940f00c040d5000c0e0804804100149403140040c00342543c10030001e01019022049450003201c079045a00152840d9001034141300c2805075040f03100f08000002c41d0111620315000c800c4030382e0303000005030041803a08424089420805107402907124441d9490b02191500d07510351000780504124800e55020b40350481156501d5480881e801d8113540072034451a01c1c01242150450381c1c482d0898482c00c030300e00d06201c04030301d4110500545200c0b0740511369007100c0642a08241d03c0c80c010260203a1070b26031606110500141d0000180c40c54603e00702e4000c0301540c11418528180303900440000c1d4440c1c039855142e5036403d0080054220556080f2013009504d82c40034802d0304580004c10b81d958020826400c91511101312200e54080ca48090190b03440266141444030507030700400c0d1307546040b02c0688018001c2000c0603600200c116402d182c00c03814ac005940c0460040d120280016058040824403411 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 387064109 1250 387062859 387062867
    0x2d071e060b040203090c01230405090702030c01090317070f1b0c080a050102030115020304050a180f060f1701020403020607030311281205060102060606030a060503030c01240b030a020307 82
    0x81c400740608255034900c1c095402d161200303140308409010842c1d1741c003091810f40020484100c980402d20210340b409040408025950307600510480c114881042a40e40310304080c01688695403207500c0b015201144155100e0800130010100410441d80c28126401c0c1548080e84c0300026032402180e156803070301814915035100058201380343c42e1180002103400c201d0150f000354101d84110820031120480d80c40700300e889100c2d40c402c603984a40c85030070601c507040c036000440100c500d07454030029510382c000d9415000e81d016680421805030513040300b00203002310009001d41c0700300340d10021450282941d001a445004010024040540c0e45140030011410740c000c4489202407078180907013001d9004070700340d800b00c0005000c80000758040003800460030750303000e002d02401d0160040d01c45544d40344107100164000418980002d41c441000242c5920240014002030a0f454004070310310b20358030202c0450321b010b0401840b00b003011420802600d2a100245c0f0b0f0451241d40025a0701d80b40c00c0d00c200d0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 387065359 1250 387064109 387064121
    0x21f0608030c071e03080301052b12080c0c120d15140a171c1806080609090606090a0207021801060c060605030d12202d071e06 56
    0x900074800069401d80341e400009003201100d000c0c3d101e07200c040302d10038944130182c6080c2c84001c003000001c0c00144800d113424410480c0320748a012b454021548286044001e2803441e0b032050f2491b481c1002c80301030b1035900c00903040d80074440f40e80603464a0ba5000c0b016a41d40759a0b40b07a41c18041c8042542c055241640c3c00107058440a805190742e59238950315166816545018030a1088503e0440090b400140f0a846203140701118064440c41400c40010082d0054030894007007004072142c5c0c032409081c40c00d1110006070003a07a0b6100b90780d2900001f445a48500600711000390b500c814100107855441e81c0070300da800b9a0307102002d80c03210a035102050740030b5080380c820700c0200d002e540041691940403e1028035207018440c00d00400755038501389034541380d20721190800603856070107030405c00b030464220101c41e84c80c80c2c5d03c0c1003c582d001d003000c1c05180c02c800c41d000680023854105041030032000e1004050000030556407450429a991401d0801203403801110203c5100519101400481d80c080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 387066609 1250 387065359 387065369
    0x10311070209071d0d1205072a0e0907030c1e21200109090908091005031006090b03010510021515030d020102030f06060c0a051902010e0d0201021f06 66
    0x40750ba541080840134200040c1c07501c4000b001c12000c210904d061809195924100d50084807009042d004070708110740542c4000d009950411b500d0034002014002c00c02c0145041e1140d568000265040511079070341c08901415a0145034417040041c00458159028a021145012844d9080e000c0000d0000c20600d01a44031a18803001141d00342c0051806044c1a55824403c00e08040340000c1038104840c601108901e00b80001c2d014039052000004a0344000315050096a0640c1020b060400142002d01080a6107000070f0012091024a040982e8008050715840c20140e682500b403010003000c90005200d11442a1b0078003030700480146c001d1103019040e556103003060240b4a0300c0201881d140151541c404e00030300c50301c0482d418051040c401d6034003400c2c03e07814600140d1180300070058160484040c0c84054060b4291810001d0410860f20041115850041e40ba00e02540005040c1c84007010f50309000305000c960500040c0e070701044803802008010b50280d074006800c171b0510010460764000b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 387067859 1250 387066609 387066619
    0x4050a050d15140402011106040b0a0b06070501050108031305100f0c08040302030a0c05100f0507060b01180311040c0c0201050d092901030c090b10110a06051e0106020d0e0103110702 80
    0xf010600d40c0c00c4001c80c400c0d4000e0300e410003c1030700302190a5039500e003110090442c054070b40200d90a1261500a60140200204010300304a00c949415085510031303402009594000a0340e03c2c0c05050741092a80101402c0311403460520170800083c111803581d168120400440d511058204101304d402e4901950b009012101188500e140c004207908050007080e120f080ba603c00041254800e4410702030403800d542d5014207060301a0f545030064800e080300f060501840c2d07040e81c4044481c44940c1402035004180c8410024840b40900c0b04682c41d41c2d0f4800100444501e030607003d40d0f0010100d940d1103100b0840010910756500305460b01c00590800f95403140c50118440320841c1400e0740c400d05990080702400e0b40d80340d0700c0247d0421175081c640e907103401c21006e40f0400c607080e000e00c204e60080100e850070395054034006d030784500440e14201c5625106001c290742c0351003c3d5100420180c0940864001080c1c03a440349400505040108189581015100d40310b440403c820903094804481d4061b05c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 387069109 1250 387067859 387067871
    0x6070f08090f0f030a0f0206040308130303030b030102040302060313020d170c0f01090c1203090812120609240a05030307030c050d050712120209130501050109050604050a050d15 78
    0x1421209941c00052440d12503400355000041030b02d402100c40804000082c000c1c15901c44030b580c0d000341c41c01000400d036480402804008003141e218030040181c0400f141e4811340c20740c10b502c0c0150403030343c0b5844c0880c001c0c1e10611044c0300503181d02d01200e8015042c00c614900e04481d500c002460f4507140745004046000ca02d076040094034035180038201403400c02c0c0648040204034220507080f0344c2020006003801a2800c0100411000c41251660090080c544901010303241c4105520b480b0812500014400000034000c0703c154800c01016040401200c00002508040e03c22000c800007a00a03402c46007109520280304e80e0f01d1402d1600146405000c0e07070380383c00040c200501280c0b600314007600d9501a200756045600e11a4040340e03582030340916285040c1c46013043c00c641250304500400103540e401c21011805542c0c2d00b100c1207622800400210380ca605000004043c5000317540700b42c0c0a03c4043c04103010540e103442e03040301034a4090340c5140200e061810071003444040318000341c940c10b01c0d040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 387070359 1250 387069109 387069113
    0x90901090515010f081f020c0709060602100f0516120b0307030c091b02121b15070e040b0d0f020a030f0501060603320c0d02040e09010507020f1b06070f 67
    0x1c01a034103c1d82d400d50000800d030b44e40c5c0180c0780c607a100036681e030800e584a2000e41c0583c0c5402d03405000314841c0d85085551f0280c0310200941154000e40080016a02003001c8803142992801400c0300011841c0050085050140900c503125240350840014850039202901c00500180d000840360180102120031207556402c00038170000580c01481c03256428440121400e80080031f200780c030100e05d40c0c020079240003001c080c4003080d00010a0000410308229040080c0d00f4100310548038554540803030042410a40f102030003c280b0b03810704600460030b00c2c1c3e8091a5680b00e201e02440d050b0080040d065011075440050b08001e05900001d080182e040c8920301803100540c440c4042e10b085490800090140b144c080300318038007070308a034407504005000800e14400804c0b5074513044840e051002d4140f0800320950010707038015800941c4500c194104008155409000e016040141030015002700010f255200d901c46a5501c070f0031140c5422801610b0845e1100002c80b40040d41006d040c070a00d8078a8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 387071609 1250 387070359 387070393
    0x15010c02310204080d050304020a03031d040c05090102070618050108090f0303130c09050c030606072607020301050c03100e070207090c030606020c0f030d032016020307120b060909010905 82
    0x180a003146505c14080355520050162044034000c0d9002400d242d1058610f0b82c080b9146048055a014807044000d240500360300c1c0c41c011410880100c1d22002d071640104000203191622960200f070400119600380241c3c815041c55110036600b00f031a140c221990ba0409048c9440f40030115115240300c004108091900c505681d610700520901807008041d50360709101090f038000343d80f854204103007080420f20502e0305000600c062031245c80800f4484018615600c0880014803003180307240d40004480046103408e200d2070340d020000211150441c01e01e04011000d030400d80c01064261030414002c075120324000c004817402050003010074040145403042c02405480c8138030441e40035119840840c0e180745011380380e41e1481d80c0083d0042c10441c400c490100c000d01050520300c0d0a1500d113000700324414001000615518141d1041e02088a178244103041c41d04201c0d50282c1000a0312034100b0001031034405d40b1070b801101c2252803945a4856200c2d0500625103010024098420341d0040b885e8000c2e5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 387072859 1250 387071609 387071617
    0xe030106140d0c24020706090605030a09020102100f0b0a090912030b01020f190c0803070203100b010311070b0603070e04050303010303030b0a05030a12030c050a02060c0d02070506090f0615010c023102 88
    0x84c0d43e0960707464031b03610501a00e64540600a40002c100140001001440c882c0d2001d8402130052040f100c0312406001c881042366002a5951401620307034840b0050750a01524a800800415a00704100d28550b00d44808502c17403000b0850800d511901a0b803003581c030800c1820b48071256602a244508080c051030070507528012401c441300306480d0700010300900044192012250043c01500c10707201040140002004402809814103a075400d558240303805810141410034420f0318542d600e800d0441c101482c20a081e0b02006101e4229000c0000140300801507d044a40c58280031036802040b000061041840e504440c0d0144110341c060303414024041500021002c1e19103040101e01c20850381200c031707441103101040150744a5800700d166911041c00520810420f40801800c058090755428103208003980c0c43d101c90752285041182c0c0c0c00c01413243c44d40103040700b815080030429290020700304460461703029200b001642c0043d5140880b903c20440c1d0455886c80500b20086489040320080d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 387074109 1250 387072859 387072929
    0x31309050901061502010b0907030b100f0207080106121406010f03112215140102030a08100b0c07090f02190c020117011509090509030405060307050403050307120e030106140d0c 78
    0x83c038480860041402b9104415080101910004c0c86490814080d40e00309185d4118030300b103201310b88002407140b1080c46510003400d0488502c0804c269282003414148114222200c0943c01c140010001e000442c06584100c980c00404404c5500445c0001140040e6080f0881000c1204524034450000e071035000e41c2401d007000c3c212144d69038071402c00148a1080540450141c0d000304260550540030f54101036102240303045d034981103a2075400c841c0ca0b6410800459401d03500c1600148031032082e5005030701c80044540401c5040001c1d80c2c03145840101d40c08400f505100950900034250f9100300d0180101d00495040206a56903540e1800c524101c545515000a919200c000c5203800c1e0034064180210a41e4000350b0805040c0420000143c1c4080c0a000601004100c000006442840a00006402154078094444190314041c0403d02000380e42e52003649040428030004400580b0b00103090401d8802c011010703100c0c0ba10804000e4680c004503000490113600300351100191801000001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 387075359 1250 387074109 387074119
    0xe01050102191406071e0c0206090f0d0218220203030a050c0316051e0a0f122c0f0d210e0d201903110d0b071d03031309050901061502010b 61
    0x60f01c0917412030707c144088000035484001001801800e2800818140008000a0051103079181c0d69000030f0f1520ac02007403111100b40100104000c00c0e071040c00009400e040c90981805180807030340065103a2060440360b1301800404121141a503504000b134614407500301500481c003c681381001c80d6186014268410348000751410503448881c04940240120b81c0204541d24015540d80c485082c011311034046000c0050510507021344800240c40c0c11020041d0288103105103080000340801083d03078110030b5009841070000ba4000a02c2c06411800d28078805490a210003955001210a05070762180c01d944402c20040c80c0c4c051101c00918903220040c100c0382c034000380c0003080c1071080c00f500c111640c900120320320034200082001e80c004100d040780d0041840c0e4100e4455520700c00d01c4041520410700140f5a82d0103c00c0ca04900706183c480550202c1c02141418000190f10034144824002d0116054460020541d00c20b02500901c0c0a0014107003860800c50150314000d00074074521340394070f00c0b40c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 387076609 1250 387075359 387075407
    0xe071403070201200901081603021210090605150712030e010204081507090f03030f020111031608100f0504090809180a060b0702060304020105130302091806010e0105010219140607 79
    0x1c1c00c04182103885c0300030180c66580c020b07603904014030000c500894105080c075400704007500c111705001c68114810080300c229581c006041c00d610008441d4250085401800d0140000b0380e0301000400b5601a00c0c0e00003001c45080c0b041c020102d02070845c1c0c0380316101c43d60020a0104290001040c41d5070f10282025040d4500e544901c01200d80ca02d40d44588020300c8910401400170030700c50399a6142203411400007281808000c24901344603070044905800d01549958403080c1d4592164400d6040b280e001c681540c201d0610124a1800c90248070740c503c02e079030f140b0880c0300f00b200b5401901c25144004004004200994648071030310001100c1003506a07150550103e4000c0e41d20b02907881854014048904555465005441c1640240c0748040700c00c0006a001005a907094012441440048210007100c03062811151030030a041e00301c042c60038410001070010b030340e00150002000117550b6803075291010f03909040c804807202700b52041090141d0000c1010542c0c004980191201a803035049240b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 387077859 1250 387076609 387076661
    0x10c050f070e10060e01050304051228020f0606041e050708090d03110d091b0f090f02070f080f0c100501050a090b01090b1e07120206100602070e071403070201 70
    0x3e4104a01a03000403c0c070080882019511074405998098411000c68004410b00302000d01705820410050680d540c403908240f0b0070311120002d01c41c0544250005002c0380b003da6a6450300d03640001c25850060b980e030580300107810340200841c1400e00107110200314a04100d80004c110706000ca464604a1140c2c0314595047c1740b00b44991803845c07218840143c1030141381c0c04054003410303024400b65000e01e500c0c001050300200c203000990050400c0004205074900d880f0708601503581c8507800c00b00071031042c052000450b00103403501c0c3c00c9a501108a40d900c1c0243d0301c8094490181030440c2020f0b1041003852000344050398455410b81d041207a8190000d80e075240400141c031100340001c2d0003d4040d410802500c0c0105019103c40110f411b4101284d001c500c01d50003058101100c00e403811390b0181111030466406101032500070166411901c4090704048001e9560080e9228001d950780d0300b040021011b52040c04c4c0c0d00c0d408001d0010341503880c03d00c4d0000034080d08000c106d0b00c40510b107000790072074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 387079109 1250 387077859 387077881
    0xa0b0405061012150815090c04110409090203011e0911040509030d09170705060109060f1a030a0b090c0d15050d060f0b030a0c03050c0103020f18010c050f070e 70
    0xc0498159035484580c02280702410f40a80038000c00426503001e200c0001c01c11401c01d2104408180d039440140c4480e1400110541c6030801600320755008501c0d1640c1400188a0042103038103030b0300c1402010840c8541352003c240101182107120284802600c4280543c2c1c0d000d0300305500f080c0c094010252001ea14000308001c80d101620071001c240e01c100840403417031a1580042c0c0006005200703400954501e0b4440701c1c55540080740803201d5822410062100707036550f1003580b01820b902000526203a04010b295014a400200401c59442c070100000d1080c2c100303508421701d40d0001802d016010700f4054007807400c91b000001408900d9040c228800d4400306903c040c642140c500402091803c00e064507108000d0403c00c0c0c0e1940003070f44644100b9001d80701004003861740752040c242c01c0b0302280345040190410200d54812410140100b00d419015410203003030780c0c40b1020042d5400242104040181c41815103490300401c140103940c04000c881c00045801e0741260204040c40202c0c1d511490224 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 387080359 1250 387079109 387079129
    0x16110901080a0302060a1e1a09090102040f12080a05030414030f0309010b040b03120f07050114040c08030a0e040f021b0d021612060e070b030901060f050f0d0210020c090a0b040506 79
    0x40302d10b04000310701901500031a003100045000455400c8d510203410004070721405011103503c0a2603400040c20040320840c400094020244000490031080540d52030a4040c03045079178a070200704010010034107105410368414404041c0c00202c03583c03a401342d808524590401c071813040c0c040d40380c00006401400e00380102800404010b001d0207482f14102c0501c5030a41104551244030401403001d01d000031401d20948100c094010000e136400d01d00742c904481800c650307410061507030b0014052400e615404c00404820007400f00d030041804c6d90041100f8000713028030581003100e140525110a80c110000c00c080b03070790038029800ea40705607074405042c1c85014000e10800014141003840c02c4082980e56006400d1a00301c0c00030350346c8596441d00c04811070b400940b191049a592500c0402100340f809030944020300c1c0590b07005142c0118140020b40c582c040d0072002e03000f070780340c0850300c0b454510902c1050807150005102c0c07011818482803003002031042040a5002e68500804226140303040c1c0904 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 387081609 1250 387080359 387080381
    0xf09060914010b180904050105090d1707050304022b1112060105060c010e07060206010e160f0c050102090a0b03060307090605030d181a0c061b16110901080a0302060a 73
    0xc00a40e920f09007401c00694000f0040510400c1955008025551180b019a01490062001052601b04446c8450401c00c15007404070501c039401c07081f40b0082c400790b504294403400303e0034003a03200d036a0b50001c1040b00d240c080800000c034400152940140c0883d44000d542d00c2d004041000c1e1001700071044c4441d0382c800c07003040b2800740d200c42d00400062400030010095146501c00101d000c0c4203610499203410000e820000168101600512000c02a004640e500085494694800440409000e801000d030080b41c40c0400082c071b900081801802d4049070307101800500301c00c0080d51344440420b0b40360425640c10703210340602d4500280740089401414143d0700020301412210113a04025115100b150007140c1d00d01008070000100c0070b000a52601200210070304840d540c490500d6982c1c10502e0082111940c3e072420303400607114001200c00d6a00e000040300750007010000c039040040641c800328055561100000001092058010030001c900301e11a80881d000c40e2943e40300002a50110020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 387082859 1250 387081609 387081641
    0x120507090f14040f020f07050105090c1e190611010605090408220803030a050406240504020a140409090308090c0904080304020402070f05010614180412050d02040f090609 75
    0x1082c000711000b10300000c84541d00400000d0020708461004050360001d201e00302c00a207010602c4000c5c00403e0291a074059401409050780d404141d002409a0503140c2c080302c801d0680c900084201c0d1900701a1510600280e41210192507440c2401085640c01062114195003803c00c0042c66043c4520343d40e0240303074415501e41c10700810140340d03001c0c5d18100644060308a240940041c0800c810700095002d00001480890700389010304008054480016007000b48021801a00c01c50b9100c268041c2c00f503c50032600940e42d81a400c07000c0700d0001c901000740700550000680021404c68079840302d4502d034401e0b140c44049580e41200503460f105c40706982900441e10710002000200b011006550007440100300500700240c03a00d804407003134803042c01207610b0b0b0355500f414428444039040b00c1403104030445074018500740c1c5040e9440b68280c050030050412003402604500f0750301900c280d45080c054000110b440c1d5a45400500c805c4c10603110306d000301031030001c0105400e5428021540c401c1c044501c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 387084109 1250 387082859 387082889
    0x1905030909070c0609050c0103061715100512030304020103140106050406120906020a08090f070b09040510081917090f0f04020d020429031303080c09060a12050709 72
    0x14085a00700040046040103042c076219400580584582241140214020300c2e0880980002400312116904504030003900e2202c0084403041c001031410040510380d580045039110001c01010143c09030b001140c1c8406950340705001c0d40c00000c061403007035001b40d8007480901c1050a15101d0010b0130b0103040002002000b05015050082c44c040300450041c80002030090070941340c200483c1c00042c0341f2000103000000340484d000d0200f00c0d0300441c0a40c80c01518007580380040c0381c80c40b8418162aa40101e0329107001480c40c0d070400c0c403550010300c504030603200005805002001e88100201089805000140d000c007014111401900c4150a018186030300164400b000c000003149112079144d4001d400b00004184282c181c00500001d1414030354010b03440405800e103a008030307025003c10004500500030803202464400d2076040c00c68041c1045150758403111802c2202d03104000345590080390000300d0381042940010005502c82e1010010001c0762030b0380e10102c44604041c4140189074440d11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 387085359 1250 387084109 387084127
    0x30a0f06030209070c0201200303400c050a06110114160c150f020d0b0d020901031e0501090804051c0308010b0a11011410090b06030c030606070b04060608190503 71
    0x70003411710f4036005042400100385100c86021005142d1510100150800b20a20284800702c031604030034241c00d0810880c078004804000d0444040140743c071078581311910004030900c00b0b44c03004140902400780407035103090b85601018008059011b01903246601e003100c130b03403030303040440d56002e000e803171154114041c03c000d0b440125102072031050140c1e1018441c419080d80d00a107481900450140b00d0409600e50541e9100c41c07044802c1d4042c0e1134002d030340c1c2d02001001655411645c9040d02c0d03001d82c3d10b00400c00e40d09074040c030081d402c40300241250700c2c0095240900c05204083d10071140125010920f00e226120b003d000200c410400501054400005002c05039158026101440584c0381440b000c903a080f0f1610700399100d2050030080300394881e0074001010840f00d001c10151020410900c507015070480450b24500c4010314501c56602e0100214003141da0345001c0300c01e50794201c1101940303030505080910040519109000d024464200320f44c11114440d000da468154200000d5410702d8808 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 387086609 1250 387085359 387085367
    0x14150f010e01030209042a03060b0a0c0f06060b040e091912020a020303070614180a0602211608160e041a030a050f1209031b13020f030a0f0603020907 66
    0x200d90802c2c1410740a0000e03003c5a15244195808050075411140c1c807481880038101518a165990340101401c0c00c02c00c0c00600c4c1d030641158004030070384c64040804d8841d400c01403800800300400a181d40c7c24000006500c000d130101030015100d01c00d10203403280c0c848001c041c4e90b4011a0100340b2484514024560100d101c84960340723a005000e0040c0c904600d2603500080c2940e2204404036180c0b9656141241c031600740014407a44403a0105400031580c034107414090b990300101d07800900701c039000201e904a186010501b101441074498580505091803c0c04514560214a100300001c908000080d116400c00c00001a000541d45801400d5034480b03013800054003941902040906088075400c0494400b000341910190103000945014040c81c6142802c11040c009100701c0540103112896403680d0100707507444240c6210091030201a61840820040c010552018403400e201080743d600b00031111004610801d43c00c0303010401c0c0c0c200c940404048900c3d40c00083c8d000641c49001814103801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 387087859 1250 387086609 387086627
    0x21f020d29010e040e0a06021213020a0e04030219050c010206060906060405211207050708060c030106030509010e0d0207050103060b0f0a083c0702120a0302070c05040606020114150f01 81
    0x80a00f0200394005822804ca1911001b0300084501c139500003110801079001c1c01c040790300310203203c0100c01416120f40008a4444c268045d0030b45a40e0410007260400d8000c102c40200c0c8100680c0011440509003030154403220044034640c05070042c1400110980740640e00903105030760040c201810541040c00740616000c1006034101c00f0590005800750ba007104004154034a05081c903010380d0b0702017610305030f0700742010359200f29259406542401196034401040d01c1c1900c034a40b40c0007844d983c0344440300d40034020342000300207d400341c1c2c500d07030050310f601045c61402e440c2c0c280c80c00e11030250340c1c604614241c4035103030b100c00d4070000500400d480103100c4d1b60a070b5003144415049044041c0b1440704046151032a550200c10201446d41c040401c0201c801c0c2582d10400354000382c040032000d405050303407522410100104050380004d00004110f00b1107400700241030301400412039162210303800380c02489114068000c50b0030280000fa400318400d44460564040035018524980140c40103690001e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 387089109 1250 387087859 387087887
    0xe130203030d110c19170a230d1812030b01020a14060406110c250b0c0705040b060a020703030807031407090e10030203070b03040201021f020d2901 65
    0x200001d0008a4280c05521075003c40c544509564020b080486840c1c60441301041d080160100c075414042a01000c2d14003059404010b500d0340c80303030000c40841b000c514268090f031143d03141c00400b0b10106120070140c02085d01e2210200550103540c0d52484074103a81160051404911801ca000307024440c0e008500c0300841030040b9020003659584080c40100a1030401415070712000070002070228500601001700c1803401d07124508194101c1140d102d01038010320003a0242511080307400e950100307000078001c02c1001c00294482914160710740d22520301c0e1241c039226504204240c0b0071864424201d40701004140c00500816245540a94031480020210000d00d96103542c41c40b04040ea0b03040040c071071020780e610026400c1c00c00b540002082c078040d0230820580e1000740d0510050702c002403590f00f41c51019a00da5201c1c2c0e21440101c4c90214511400c1c3d40a03035a609141a007441a60090401840054811311090744e1580c030000f441c0d521100c1c6074080152840d403002ea40d502410b918a0248 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 387090359 1250 387089109 387089113
    0x3020d050115060c1703040f020f03120a0306090c0504080303040b0907050d1a07110703060e0c0a03050729040e040201020124031b05010e1005130e010e0702070e130203 74
    0x941c03429401c4280300043e4010f0000c140a96016001c2010b0821150701e40d105100c401404d6060a0303c0e5a481000202d900a00039802806403071042d42c0c04002e940c05489600101d40d9841501c040020054101c0784108200c0a09003400200301d6030040b0155410350f40a04025411503880c2c0d08c40801d6440054601482409074850210303c5d920744030071507000c09000c0c0d58001a500384061803054040c400a000c0b01c100b140701714841c4c50200000c00c0700380459812000114581100d460074a00705401c00030784551200070072100200b00040403d241c4100c0b8150114956143e440d58a80b910390b140d4000c2c501010300e42004107004d640070b00d0806070b400900620000850182c440307481d400d50f4811544200b000034903107408104200c801c010700b0368a0029400e12a1805107002c0020301880b0316007200e907100714241c40f0034514091140003550095901c52543c118890f60b5070310116041c030707007e000c1d0072085541d07600040d00b42800050020304131241881c00d451a50340d000410070706035804100481e418 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 387091609 1250 387090359 387090371
    0x406030807080d11070b010e0f04080a110c1f09060219020d1103120d0605040e0303161115041118011e0e0c28080a090606090e10050a1503020d0501 65
    0x101d00c9030000b03803101d60700c00e1705c6006c0301d94100b1030f44d250210002010003807030b4402d220800000860450640c1c0b5203441c1030610009600400364240c0c2480205860550808010107080c00800d02c800089080c6903015203640c144151200022a1034007000c84007101c1e9202c420b4141d1006003806e0603400c0c1c0c0c42d800b500c1e1922100b00c80e4130001e1f0034942c0010907094a46008903144038165941c1c800c0c100140001ca508003d80d45103065000e4490000414404843c54048600d07041c01d03004011000b0be10109000b6034003020100e031042e00a091080d20103407402d9803946078000326814440108020401c01c020180c519a10f0031a000342300800a11720b419076070425140c00107400d04c5001c0c10074040c1c035604001680380c04660585800220400c0100c05031202043d9115400f180c0224485400100c40703000491010070342d00b0490301030225a4403603001180380070b1a103d000784000c900050006c02400043c4807640740c01746107400f41d80c600d840d080240a41c80c1c03010001494464903203242d162180e0300120300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 387092859 1250 387091609 387091631
    0x21050d02030a0e071e090e03071202030a0201050a11190323060f0603220c0f0605070b09060105060912011404120201050903040f05040e0106080106090b09060406030807080d 76
    0x16a0402d0700d40403802e9442e03e4200c01019800d01982014250701407441003c010489140803c600c074620810300050303034480003203030203200c01c0c0304031812141c001120790100c150318140290303640d0100d4241d000551904010032aa62083d0103003044d06640e401060741403044030561109181c4c0201100c106150740e405c203c02c0f00310f10a030307042600c0c107a00070564043c0345002d100f8410400d540d6034000340300740c40810401001080c11000c411650700080640c1c1d423070310341524200020690607040001d60245900e030028030b0310390082c01440c109110b45402d480c0c584a800d02030b0340d41c00b820b016140d80f144041c40340c1882818000824240800c1074070012503000c04521405c5c3c40c81a0030b641c02d07641101c42001c000d158075024083c098000d8846402545864500168002c84600b40c0c01106d12440d20341c00042e94408094110b01c001d008604020040e080d0b803081084001c0c040c0101c00350140180780000f0714540340ca8440c2c0760440c1e0f003200309180f500c0041e9840200981c001c20114030030701d90303c001900c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 387094109 1250 387092859 387092861
    0x3020a021608010b0103050a02280e0a1502190b070f0c02041a0102120909040305070201030e06090106080c0a0506040b070507030b0405100b0f03210f18010311030421050d 75
    0x1c01006510000200c0e100450300040a5400052804c08800d00410541c00300151400ba2400c5503c0f800a00880c5107000300740446211020812141e8044485500811544100b50303949115441c01e030200d44602e4824131188104040501c40a40b5500103140012207846c000c0081c840610514589040303514041c3d400a81110a800454189500f65944c4054256010488401c5030700c68540348504104900d00040e040200081c40181080341c0895080700310b9010f80c001c01c46000d480006d642c22454030781900c42c001c0406c1e10503950035104403207007804142005c052a5040d5100135003624a0030b400c00d403810705e80d07074000241140c00780b0071200000046101603c00a0040340310700302610215001d001ca5105442c2c903000024803400103100d0b681481d5070005881e8980c20b126010991410300440b052451602542008840041d800600c0e100c140c405101803900240e0701b42c80400c25021166035106450004490080918041d400c40401ca05080302c0d142030301460501c1e20916007413444a41e80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 387095359 1250 387094109 387094153
    0x306110c0307060b0f12030901030f110c0c0f0a0f0506070f0506010806010e1005030a0b07110d1707170c1e0a0507050709020f0f030405210705120301060e0103020a02 73
    0xa1200d0b0b035038480c4e4011500e0511401c81d2038004c01c541c0341c032071603001c142010b44900c1403010080c1032583d5241c610300300f0701090308604038007808184d000340c58001d062031043d1580400e0401910410081d5441c420343d103410341218050b11403000d0b0030040719042c2024084950b200310700c1900d00300407024045000410801010f0301a00248000d0801e40d4034100d0540c2801d14042c00c103021401c2112418070150b20300050410000d900107144101c00d80364124241c5248894440840c0f145c010803444004040d040481e51030700140074941039205580d030040468406403005490101000d0b01c002188081d00c2e0321014000706130f01c00038800c811303001c101c3c2c0004041e0300030700034500422000724a8005110781808624001c209500082d0301e0944800d0400c415071213030f1003c986680b40c0c0440820140f000402c0f9541242a40b14508083d21900300c907031107901e070014403049aa51081c000318524a21102b01624120355a81e111500311218040055010b5080040b0400c02c52156906050300f8400c109081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 387096609 1250 387095359 387095363
    0x1201020a11070909030f0e040b0402040801097d0703080306061606021b1c08070309080c07092304080304020405062805091608010306110c0307 63
    0x5480552211620600b0144940d100d100070610303042c12280840d400c00b00d120045038692401c1012046100c000500524134403103415001071000c40d010480403015800418102d003c1c80b01301d50203041d42384603030540034000ba81400716100b40c07108040c011407119000900041da5203c84102070501c0b5200700c054101800828404c20060104c0d409407400307800d00d10910588400d010b03049a504640b00c0503400e2101901c09401081d0014004001144406d80349020a0b0f120100755521412034820020b0600d4050801072580106132000144800004880c03607904c000751a0064656241071050b00204142d032001c1e05d458408007c16284e5507420b02c4800003030032584000241400700606182070410010071134080030703d051414070008c10381d28004d499000e50f04907404030f0141c6d140c0010031030710b0999001c030802003403404980d203903106603e1000d030040e18800d5a514100b6604c000090859920700306100c000304209400620100d4856000301c1c480390302801d1414546a110714006140d82e01c45007007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 387097859 1250 387096609 387096617
    0x30712020307020d0806090915060f040504060f06170604030302090103091209090510050603010317070506040c0911070809100908070303170c03071b050a02060414010e090907141201020a 82
    0x28031400d01e4000305c03003640150042d07441e5503440c5050340d4000d40d900042c3d00d451034007000c401e0003c1e4040d41c40901d01450284043d20178483c0d4102460908040c00300080c84260030707414070310041500c4d05000b4107a01c50150840c001c002d15121514160025405088070130b04054681046171301088004901c91800542540c4181302c05d4074214130101201c81c050b10010010200c2c00e4200415901d41c015a8192900306503d442c100200260111113846101401400c40c0600c1c820081441582c0b0804022200b031180103104a107000c0242c0000c5100e0180300030845d440a204103160340c200284012461074403030500385803081d2a03140c4039150448c5684110001641464810007001c1d5a40030f0540040c00d0f150310500707500306000d016080041040c0362000c03008038815030100340300381040680d282c00e40242ca0380d60b95584034042540e41d00b00112409001ca62000300b00405424190441441282c1070406000064200442814002010001c1540c0a0340900314001c0e43d40081c401452001c2c01911 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 387099109 1250 387097859 387097873
    0x2707173004292a1903111c020a0c050103060b03070810080f01240e1f05092509060806060c0f011a0a0f080709180c060801050f090c040b03071202030702 67
    0x3c83c0003403003082c40340d105099422624038160f5951441071144182a8036050072404c20303030484a0903103854001d119180d2101c1c0c0e00644c0465191f00450324090f480d004085000810b5102d0006600740c0720a4410545038200820000e1180c0d882140d0300c40d08041c1c0400d40920140e50f0b00d0f0324628081c1c5d1400c02301e865955410300c040d0301d84061080c001004c1c20340c1e290308003c1072418036003c40110340200050206030320b54440e107003851081c0e1500000303460b00030614491804c00c0b05072404030902155846942d0310041021600e014003500d074480481c3c0c0282e440740b41c80e0740d801d01481a560003221196015106040e44550f10038000c3c0030300d490401041050541020512007002484111070f40000b40c544a41101440f00001c040795440560b141c520010802078507050a00d0490082c6100181c0301c0308401d100070517a194005101030407204115860040344000008106001800340c03221548060100710400c404c030080b002440d40b00c541401c0007090800b1400701c000c04d9074003c0b192040140c002e04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 387100359 1250 387099109 387099157
    0x1020c07061808060402030c04022206050307030e19030509060904051509160f08040311060a0e010501210f0201020705060d0902010f08270717300429 66
    0x40b200d02e0003030041a0042140f42080d4001c603894202c0500b038103000702d40014032036078800c00c20340700106d889143ea84499003160355a40c0044c449e40054a010b0006401c1412100205100044480d041d981c0c41c0c0d008055022640d80c292000d82c800c500311500300344240080c46a56440e0320610b0700c00e16110360700c02c814080040c00c100165800404a00004020343c4c0401d4840354052003114080c030883c02c0209158131075080c10750701c00822801c407003100d1007208200607000742160800c1044c44110710003841944d80f1400001d48414250b0340ca0200b1315403413500d0401262500320742d244490b0040c015540340b9511000824815881062106103240d16160030200311b590102c0c00090301711207454506800d003800d950740b8070701072550075410f908507a00e11090781c031074082031000c0c100400501c0c2140c03e0590120843c583c07240072015040c07100245000310b05080d03a2142072141c001c2e000d100010741c40e141c140030650011644050210030340e000b59071b2121101201c200700600b41c2c40f01140c503512541e2680 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 387101609 1250 387100359 387100397
    0xe151518100201020c0624041803121a151303080415020105060609060a02010e030c0d031503051c0e15030412091809030507050118050f1515010201020c0706 69
    0x4200c0300045a00c1008150411700000c122039801c101084905802114016040c5c10b081002c51901a40a807030800d60510740050b80e05c4510056120b910b41da0318030140f503400b074022100d40e40207101342070110300745d04212440c00351a445158009010032509090a2202d002ca080480d42c20440700003000080c14440240c404080500d0a0b0262000b031103a8a40036011070301e02e020f09011035009883c04500001c905000b9000800f080205c001100d0300e602408110070740c0c407000140040e01080c54016040f8044a00440707003025070742c0000041c07405030790803440406906624080b4208001c03c5a07140700143c0d5412402e6042107440050440e240c2c10b083c01c002e44810100038080050107001c02c0100004845640b0a690703006c4c1000001883c42003500301a240ca21a24600030720652070280c0070076201500b615807040d954016804c461449001c44a09540e4041481c07402d81c2c050381f020000740000842070307062400c000040c40050708082e1250395061400b21030750400070105001c0d40c0c28040394221 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 387102859 1250 387101609 387101629
    0x1201080a05060f01080c130b100513060c0f0201050307021929090d050d0b040f020403050c0607050309091308120612120304020d03030b0303160b0606040e151518 71
    0x150031000d0303d055162035a282e40d550340201300103008901c4052207000b500195480410020401ba049041e00c100114004155030302c240c1903120380000140c800704a5510987c1c40c1f0558a6000b09642500c0003603400540d89500024581c0e4114413039141118040e00c00e101c2c3c1c074025603110340d0000c12010135010801c1d800310044640004a03051903802c0201d280300001b02e071450700c44182010740d5510b0f200300010000d811103441183c0c10504101d5600c0c0510042d6000f0000c9038021010f80310010010410000c0910841001500e168403c0c800c55105180420f4180d0f0404e091a0600042d040301d03503204d4504e90002c0744500074290003981081050b00700700960905031400b80c1d0181c40200445000130040303004c040c00c040d014411161003682010302982c00550316101c01000c50f500d40004910009085e00301e00c1040301c070388241c4004030b103417807c0c0607095074180d8001d80c0240282d41d80d09074030705c2003d0f0b00621109a0001d2a4685040c1d025035101c002e04041d41e440c40b995100e411880240036245030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 387104109 1250 387102859 387102871
    0xe121e0f1201091404030c060e1e06070c080d0e0a0b070c0203010b090714180d080703180509130501090c060207030b0906100501080903071208011d090c060c031201080a0506 76
    0xc10620745070003129200c1d4440303034171990608205030914120b04007178000b01090b900c3c000c91441007510180c9142c01045207046009081e204030342081e515a001160482c001d100002d08a940500050a110010760000112000454119030100110381c131840401c01c000d032542e5000c80c5a0711250825401e081c0520516588150b503100c005041540d0010001501128256280c25011554655100b500302c10100e44c004000c0491304542c00906220340141d121030000c03008940075043d0200d4500034056a00200c40005040810582e035a050a03074100080001c110b0701c41d50f80d0026103000518060024000c0c10325a40281031503825851b108040101c041c0540300194005010000392540c0c001d01c46083c3d030381c00c0c6813038442c0d03880d4812000e10390b000f82c0000800410070b65840c04000d6a0054005040300e4669642010203200d001d14a000802700355001c1d80e554201004090b0241000401001151280d208a0b85001c0c0d04a0f4180c0210500381c00818140d08090203040a00c0303170801c016a0012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 387105359 1250 387104109 387104111
    0x809060615031504140702031c050910020c0109060e0706020d0c02030d1812150606030c0212130812030a23060f1203160309090e121e0f120109 63
    0x3040e0311030000060b000c01000d52042441c03e00b6800d203680c0350f6802030140f00e81d01041c44416400c24940194490f002a0360401d42d442210340c590103450401d000300307805401010b010b0118a00311140050195200101244c8550b484040e1000001c41501c20303c04a40b81f0b00b4060300b00c81e82000002800d2034660104003007000102a040d02c0540d034082043e4107269000e05040b80c02598900c0c1c4945516840c1d4012180c14140d12420780078030014004944200309100010841180c403540143d080390010011100140d101c046010000c00321400141190782100c0c425804540d51150000d25004032940d07542c85000001c410b01c00344019074000c03400140340301c00a031420701c4102040340b2a00040100442e1003a0340c41c3c110680342da204c0e50b442c4443c20540d401501d80d201c2e10068404034034000110102c0c0044c1d000d040009084001d0f00c9600f000140c1c01c409070030000350808c05490240c1140800c1e10740c2400641c64074114a100c0d200502d440d80d581072400340c03210300654440f082d201c41640302003149 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 387106609 1250 387105359 387105379
    0x8160303091d0f270a02010201231b090a0303050414010306121e061a01120e0d0806040b090103030206010e01290a090302120c0301061508040213091208090606 70
    0x19000a840995001d403440c0f440f4006a80c4201410180200703d1203469114060041c1e4104206000700381190034500070b8000344850404a21400d0141c4001080301025500d014042010000510084151801c10b130200300e0400310401c00013494080c15500480119100040800c8903109544e4015444102400e00300003907454441c4440d020105900004c02400d50801c4030b0700c10741c3d992400840f0722504460204003038111400344402c004100020a40070405604818001c841356004a02e04c031180c403005031009006107141030b210140081c0c5542c1d0301544079040e40e4450703110300300d02600a42c06a8020145940360001005140806030080308501c400c0c8011a1000741c10414200b0460499200c065940c60a4407403c4442c050503401c02940b140c200a4030507800607000464480d0f00d04210000c0003201d650b204a140042e00000740b0002280c1e802000401615000b06017041290712424080307114151a038486031103000607860034010601c03800c107101c4044c0041055580c00407041e2014582 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 387107859 1250 387106609 387106649
    0x31a09090d110703170a090909110102011407200312090d0f0302090d0201081504060603020a020f0304051e12120403060b0d050a140313090b09090619020a03060816030309 75
    0x42d025810005c01880880043c1246240c2d100d84c0601004180c440410420041d0354504403420714080716542e801503013400d544449904000758003501409960711038080b403030744c1580003c40201142c20001c42c80e000901c111042c68100042003481404d03a00040c01030314145910103131181252048407070800d881441815a140c603120b0408210b01e409003801e110302e9450501072840c1c040540031080e046070030501c0001d0029019006404045065004d6420030294041c0c92503490142e8440c1a9011612010360580c00d009521007801207080038140080c0e115140f1411450400395500c1c034107041000060800521503184209501245c0440d0460310740c01c000e440341c0c1e40c0c6010040c00a44168114805c49aa06408008540078078400700f50300e0f40704036510128400141080c11240707006001a00020b0215080811482d20401c0c00c0f8001005104400c0c0c1004c001350410b045600600d543c8000200340f03021f08000022858a00880002c40c0509500d00142000344d03560110000c00b40b44221042 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 387109109 1250 387107859 387107873
    0x907090e030f07110d02060a030c08060d0c0311041104061d010801081e0c100504090e0102040b0d1a0904050604060f050601050d02090a05060a1806080105010f031a09090d110703 78
    0x15841c0d410641c0c5540340c03484400003e01e4040e000174001c0d4448000180303003100541541100354884941e8440302c146035546800e000d04c3ca503082000a02e48101000d003400000c0050300314465516010f00300103803810300c1c800901c2d103039803040d0006c2d004910155615500b1603500d010502c0421801c1c6030001440d4549003046030391300c01006483c4003030b2404600180d103481c81081001d4408100410030140001201c42c0504294014010514174a042100c0c0310b103e118140219002c88100845083c5414a100d04910040068000d03000b903e2501c0a10b030015a0389510919002e03038003d001401450030189008000c0300d510f90122811641000c4c20088113a0704802554442c0950081c00740e0346400c4103000a56214498020960040c0e002c510355001c02e81c17110004c5020f01021281603141070300c404040e80c00391424454a8002448401803045051194000d005040c981c01001c0c0c800146000028404940c00c640552543e44114003444c0120741c401054541c0b90800e10141181ca030030764941c60 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 387110359 1250 387109109 387109117
    0x10350a180c030b070c0501020d06090e01020c07050108070512040b06010806040501061d040908040f1e030c0303120e0703082a0a1407080313050a0608060901050f0301020409050907090e030f 83
    0x1c0c11548403c800180024060601d1103040359002d00219a1840351100c404010501e034020310741298a042c001000e0340005100b04c2d440d19200500400115150500440c0d2040004000c0010010705200d0700c01514007828100d400303103200f5002c0e4903403442d00400050030124000c0520344540d082200400106810103008855141540c82c61010000d0b2000441c02030040581c1c02032004000060004150740101200026100c000c42a160501c8204103000c02d908580e01000c0e0282c40203680800c0003038002c07e44150076128410002c02c8440346504880e060070355607881601d80001c0050150015503110310340210300340a806510102005c07115045a40d081c40e4100180404022046100c40c040c0401100000340740c2402142c1d40c0d000d0300c43d0b0398650a03aaa20860b4028500c0000c0825002c0c043c08804d03210f0711000d03100c4800c580c642410446200c00100649400d9542000081000e021724007810b4806e454003401043c01e540b1340f801043c00c940c2c445208504642090191007500c40c2604111 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 387111609 1250 387110359 387110363
    0x40f03030b0102250305070b210a06051c030305060415210b19050703020c0607140c1009020306010602010902031c140c01090b06090610350a180c03 65
    0x41d40041d04005030703e06001c1c0c2c4c28054040f00c94032442c6040200741150744085d24466030540707050300e540300100c80244c06100c801a000741d800e40246074440b01001d00140d84100031708030104047d541c840210f08166190b024904003440b20756031201c2807641502032607400c104251b03001c20041c801c0c828660700000c8203009482e0040c403080390050a90030742669140c3c005410980e40d88060600c400c2c034000c062044042050f02d1030520380006c0155001e8426a6041c00b4840c0280c5025500c1c0c400882c1e0981610300600c83c0002d0a01103e0740300719003007065581c480c421000001e41428140101450150140e0140f002c5a04145603100181c90110b4a40040f8811070700e0300c001840e84100590302c0762000150015440404204880c03981815040015014024500c000c1c0584618091191860046804d140c0003404440400c0d041e0b407182c1e84179a03080202d0540d5801c41580210090800c4e580b05888190b0b0b8081c080c00e021000a042c841d030108038403101c41c0050000c0c840d68a40700f030420385d4840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 387112859 1250 387111609 387111611
    0xd090f0915030203030406050c1c080114120102040602030702041103040323040909030f030c0807050a0f090e1303080109090b0406020705010b04050a0213060203040515090a18020a17040f0303 84
    0x41140c07a1429880d0320300c003440d402002d40e9140d50b100c43c0000c2c59a0444021807040344242c05140c0ca1b5021074406000804003603035680c280580c00c0013010f000184407440c1403500194201c03600051900d00307101800c00b91003980c0c00742d55600f1190040006544181c039280001210410511001940003800028100b40901c0141c0c0a8890906901c05a0155a10912000d410402440f01300355118007503482e119583e4404100b9910800c0c011210000204c0e20b81003c14020012044001d000c0d08191041d207006140c103c440940b500f8100c11109029075048441080b6101010100342d0485605805044440c808002e0480652901114410040c0010700210703070014011007400340030f420070415040050028026810600400c0000354003150220a5084000c4008604c007840842104e0440d0b5000744032422000004820030115800708249503030101610303070005000b0181410b00c0306281045040181c4514442e0300241683c0c3d46587c020080c0c4842608000026100e003080090a40d05454 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 387114109 1250 387112859 387112871
    0x206010f05090c0d060e041502090f060d02161209210807020a0e04030c05011104050303030a05131e03020705010516030e03070b180a05090408040905071407140d090f09 74
    0x30900f6000d1050040c148011070a003400428a03820305920035004030b00c1260480342c120000310105d0201d0003000a0305a000e2070a1b2014841458280d01400c414400002c00514004604103210100b040d0044201c0d19507032140c2d80081c18613000040b400081150034074203900f0040c1c602e03541d0800d01c0310320401040b0b480003264034429500c0364000c420141038003c541c030b421400c107800e0250804100400844156090000000b2155220000d440442d00058011400d40e01d41201c1203014101c002c141e40d44064401c42c0801c045140c4410300d866950401001d88640303121030034020f00300086c1c0d42005041c02400c001e0004850508030000d40310b1a0985425042201c01c0d400190070581c00e43c0c4603030000040071903480400c4109188480c11000c0841e0f401c0c0c2c0301075503102407040c0780c0c0c03085501400f041c40602c030802c000d043c04d41106078031110f10324003c2c00719800002d0f141c0d100d07000030000b500c00340420301c402e8111503020000320000140700e0801000b090300c2c00000b40c80c851113501a07005000c2d1600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 387115359 1250 387114109 387114121
    0x3080711010f020406031d0c0a050409060b040222060306150309031112040e060f06030f092b08130b16020a020d030e0118080a0f021206010816060206010f0509 70
    0x2501c2180520a0310100f50341d2507a0b12800100640a0140201c1701c4d1044201c03508841d001c0080c080c50a180007030254060030380303000100801030070010390070f40b58942c0711000c13100c05540e00d10040040e081c1420084030820216054030042580f590490001c0c50f140c10300910101c80070901d2010001d549180c0815002744500c1c00b101c1d13010100441c0c070100c1c8100903604420920000142007603480080c044030550340d5880400c5890300c0d2030010150020700800202c0c0d100703107183d8000c940c0a40050111000001005180b581d120026407440e51200d451038059007020381c0c40300a0907081256503070400c0306400079464881d500c5e00e000c0d0a28502d0520600505103050091203a070000d00d03001002543ca8241906000e068103038880c9115001510ba1440c807185008803071100e10540b14482c0052040241c29581e0a02088140500340d0b40401c00c080b035541c0c0e00108001c0b850280130030001814580c50700e0034009000b000180c10410654000c0401449803503101c482c03c404450040700d10089a131140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 387116609 1250 387115359 387115361
    0xa0f080f090a0b1c020405090a09051603030801090c0f1e030b060301170f0307050c1512100f06030b010e04050705300106031a04050c0f13030b060d0308071101 70
    0x300c1c4480e802c1101c000001070140300c201c001d041848044600200207800d02c00340b040c02c900c9a800303059071140c49140480d401d20040da104020341881101150b0240e64041c041c1c841090042d481200068843c60040c4007562a50140c0c01c403000250400d4215078400f00c0000d840c070035104c5404094071200d06940c5041c14030941101d80510005040f0640d6540c5400d002038100d18051101150b520919100d00d001e40e2002040300d480c40d030014050700301400c20394100202044400d00034000024140080c40075200a1001c030b5029050300c0400402003490010650000d200c95800203040c14a270002c600041e0b600190035070000101203070005030544d12400160780ca80500c5d4100b424460300c52032001c1001e4610094a4042c5100d07090a0b43c01c1da99464089095808040034480030900d8425049000d0905811a44c0c01c080c600040c0c83c2000c4504100210640044082400e080d0442c0001c00034450001080c60b080403040d104102581110f4802515500c0c0180603035003000b202001ea031110b4502 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 387117859 1250 387116609 387116617
    0x518040f0903020313060c0302060109020f091c050c1512270709060e010b070b070c060e030403020f1e090c0d0603030806031608060a0b0307030b0106030203180a0f080f 74
    0x240020421074045a800c0095880d00315214002c80a000284d0200b03990b4010003081054a070300d0740c010002030703003090001301c0a9048801e911003020800d0080506580c1c0c2c50049100c4080f8420408400a042d802c000385403451405005005500000b400c150700000001210f80d030f1071122110035030b1912001c0c00040205e02c94060300016a68540c142403c0c1000440d004048541c42c0701c6c10301030782d910382c50380b20f25400082c41507001300901082010300291800309244d501122500b4203042e032049548443c0140c840400070300c150b80d000041c040c0110f150001c0d80e041c84d90415a1010007483d041010f010b46840080001ea200741105c4000880360342c1d4000864069803e10340092180d150f0701c0ca0003800b801c2d003c0c0c03080cdd1702c2402004060390310f958009211004480d4010020030030380d02c0d80c401c0400109500031120741c05000d408008004230b010b08648500070403041d41c1c01680e91070003011440c1e500e8002e0740d618a9035001842840082000005030200300c0d60400700443d0382c0c8841e072120300d580d481 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 387119109 1250 387117859 387117881
    0xe01050c01020f0301150306121202150903031006030501050307090b060706020c010f0522030f1803080a09170d080a061e030204110702151b100605010f080106051804 73
    0x2000140f102d29140e0b1501c0610b04980c4255403007028030b20038002c1541966054041d41404100f05843d480104103041005844080c0c0c600541d00c0d0364071300000c0403020032011648000d940e0300c00020b111440c1c0e101c40f505402041d2a160801940d4140340c0045e850310228844c605000b034036039441c00c1195680808860110354098411981c490f44130000c01d000c0d000d0240020f50407031810000500144101c0381c04440f0510896400c450408669002c1c1c54802030118103408010707804050b040c2e5146c1610310000590300031102161161280b01c1c1c02022a2103070b8100b0180c2580007003000345205000500e0301d104440e83c0c00d00403201c0d55002542c00080015600c2444044401203000340c030320f10f158220400b541e009a03003c0c080d0350007070720344404288203168000f5009201130221080d80328500c070251003212103e5140c00303038480905141ca403900740307042e41c078444031541c5580070846985c1080780032000c600305040041c0290700d0140080c000c4c2c010200300305419403100c41e40d020165295803050700c241c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 387120359 1250 387119109 387119111
    0xf02100e1c0207080d0f020c1e090a0f0e0102030108190b070806042d05011e050f0310060e1f060504122a030212120405060c0f01050c0a021e06070e01050c01 69
    0x19900d1750091a1322010085403003d4003031610210464100800d8900d0307081d102e10603601400ca050000d000c00703050300031f0600314165518100300d01c021038540140078a4801c144009600c2c5e5041071010380c1401381c50880340400c860300a20300030000c1e0300005500da01c494a4200521640c0c0c071540454050f0451004a58880b00913031000e90a809412050124200120404010581e2500000710b444200504d1400640d80308010822907460030250215195801409031103902003584114025580300750414200904050b0412103403000000b92018201c04130f80c88022102c0c540b10703020b0854448c90240b0540c8650041c42102480704000c11030030300c1c0075080540f025901c0720040c01030510f0581e0004900c0340f042405202c0358201c0015100544995888866280514001c10081300d075101500d82041c0c0e00503140b1400140d0380030712442d031040143d042c506e40d8840b00010300a0401445503110458202c44030311070b0744504c0c000030314a0f5024201c0d05207603601821110050f580750203030300c000b99415 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 387121609 1250 387120359 387120373
    0x11010e060a061716170c09040809011704030e04230c09030c030c090112171216051216050d050a1d060108030f1c05070f02100e1c020708 60
    0x100c4a01c2d03021070211400048079041c0c4120b0390300c0c0240c03107407482c01d0000c4030050601010310102000680039100e442c1c0d04403c944892080c00080b07440000110303010b071500c01c000300da080c1903560032020582012200030000700c0c4515141d0740250000d41d0001c442030046a80300064078101c0b41120b00ea4150003544107030b000c064904520340680e01e5100075101400b034001e004600d660740c01d000400a0910030000d08508c0240e09084414030780401c4080152041040c00840f21308031141c082c010310300f1404400c80100d403887e00c08407560074510056000020440100f12010040d6a9112455004005280e091050019071041122540101e045400d0031500c0c1038240550500640d0280b2118401d4104000c0c03003c143c40c1324251201824030500030650020011600300c800818020203aa000c107002681c90050310000303c0d0100e51044540d0400719000501c4420242d4040002c0807185401820500c0000e0715030b10510303203a01d501c0c0c040d016010340012070065034900a20065020b489202c0450b658 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 387122859 1250 387121609 387121621
    0x905100b0c0c030c011103073503010302010306050901030503090f060d0e160b0309070e0604140702030706050c04050f010518040c020a03180609060516021c0b0609090d11010e06 78
    0x5070001d5050243c440e01c640c0008441c10b50040e800702000c005000050750511203035440f040c025225001e0040a940821034034001c1c401809080f07501d5030400d003040700741c0343c1d0305520024080b01c030150000c600c510100c80040000410000c04c0311007004081d41c050702e14288100225000d0f01503810042281c1c0d04140c0e4610094a0010784440041c42c031a2200c0141581c800c2210300f1440103440a500c950414007040c448400311001030f45e0004400783c80004c4103401c000401c0e140b0a81510608010381000681a007405451f006c0d003904610509000d51030240f814002451304088682c400781408070104541040710660004511403102c0500700384204045000c009480d104415811030100703008181000340f18401c001c81030b06030749058a07030400541c20500207030b0300c64010304001c9140b0940c0c101001c005840d1016072602084007258071040d010354610b4502070003000244054090324400041144031140004c428100c008d280c103202061004568906d03014080b50306a048a46c400e000900c94 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 387124109 1250 387122859 387122863
    0x16031817161703040e090703050105151003270f06060611240402060309031308160603050405030702011b050a03051201080c0a030b07110106030f0201090605070c0905100b0c 76
    0x3030003140785002650140e01c0d29541004210503002440c00d5501c00d0100307006202203041d4050f04910f2000447c2c039040e079690364080c2514400c5955070f0740300888041e0b228950400000019403101c850400740114482c03803900d141e0502a07031080100011003041c00758140400410105a0250071501c240b000e903481c0c1001401445481602c00c2c0f01e0700c245a07009200c00c030102d00020192640c08c125100d15102e0707400300030240d04040c00640c03907030108010038100001150841d4006000041c060445c107415450225809581540503c051600389010800055008000c40e00c030540d090800d42610490102d5040c080404484014828404c0901328028140c1000240160a41480003500705030380321b040a6840d119203640441c1c02c4803081e9424000102c205104640c002d201d41340c801401c2030201640350a4803103540c410768604e266402864159680441a0005040541401458072032503a85010790a0158803034014125660004101088450b44409000742070140d442500c40d44020b0b8443c3e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 387125359 1250 387124109 387124123
    0x60d0305030601092c060105120406020a0516030809060901060f09020703050f0d0b0a050d03211814070f0f061155081b0604050706030e0316031817 65
    0x80e42d0b00360645e001035490362040044480c485852900c0d180261140e0740c0e07106c043c4d00040c19030418400140107a61502e2041c50988803001d000e030395509000c1c201012142c0c02c0c903d0180020741940d0401409000c03c1c00f102c8034100807984562030041c1d40e0949410100c031075002d00381064180e40400a00901a14103640104808600848010442d1b5039900d0401c8048801d14100401141040000c40044003003a0390003058410501c1e408141c2454290708100800c8804500303d03a69480341c60440d00c285800c00c0420040c1c81000c0852480a00303003a01a0601540b901c1090104041e9007044024884140070800f440c4600c00082c202015030344441800344000d0b4649625036580c00081518064103495511409040400301400e0007a129111400381e075014200343c411043e4420041d16040c2801c0000744e12444c0501f01500550703041050040654402400c100c140d580240588507908100d241244506603260501c290366900c126154a40f9000981c400c100354504021480c580000c0401c1d45 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 387126609 1250 387125359 387125429
    0xb12032a06091b0307030218040312020a11120a08040212151015021f020c0c060d0509060a0c080601031a040e0f070f120602030403090305030f190503060d030503060109 74
    0x203007090040300400d16680317120602c4040d600a504414000c603083d041d001c480e0b0054040e1410881c00c45041400000703a0340030802d080d000904034003141ea50a80180052640302c81c6440c074540c03030400050300c002d12522002e88040e106031621064507000e030004014040c0c4007542c03c0700c03442d100c0c9880c0800200200082c1710b403e0740074030b003031901c09500b40c40403444001e40e6040d210081d130300c280405c601034000d4200800451180c466080c01d071025590f640c0250100f00c84400c07011500d0303d400c505c01818200007520740e1100d01e052040041c03020340c0044c0800e51245083c6030006000391020410880305218080c01c5401ca480c0a0300d030041d02d1000308000711a41d030b8001c11030380600d69446d501207040722240301d4035180070b00000b010070010f400c030740046070003a001e460f1001c1c802e0b4aa0716080e085a10038006a0081040061050400124202001508129400d001e421403900d9030119511a005000c01801c020001000464981c041c4148401808010b450f00444010f01d961504c481b08a000391 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 387127859 1250 387126609 387126643
    0x7080601031e030f12180b06150415050f071b050a170a060e030405150403060501050901030b13051603050601090f05040507030b07020106120b0a0b12032a0609 70
    0x1400e50250b100440d00c1c80d050b900da40ca206070581081c1044030740c1c815580000b03000c0354035582803009100f400151303410700034054140e8540c207007003084c1000300c8110244450010244180f104100c03116800113803100360006070030030960b00c1140f0075184003030344101070f00101204605205508892120382c07032a416940c0c140e031040e0040382c8500050100801c0081009507079032021001e1000104a50000d45010003104205d0b42000d4039200040c00816841000792410f8001103002c00034090b26004560041c241615940342650454960705040f500c01040801c0070b402d084241d50400004011320108000407042140c8015283d18146071141401e108407a00c0d84d0801c0481c0741c60301c8107407107018000c95001c0f000300720051442e07a940700300080c01003881003075560360840058961418410507901f10712a200404803441c04a504800700c440d492042e034000c40700d851550f482950000121410403011803003003004514204e05101e40b1210007443d684841c003414090024054002500701546201d80c17034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 387129109 1250 387127859 387127883
    0x50601030b0d11150c0d0306061d040203090c04021602010e04112b0204030f03271403010b06070308180a150209010c020d0b090106060815060a02030c0708060103 71
    0x10044058840000180e075110074200c0d0308000080408507400ea0070390b00900603d16010b5034100765403c036003040e4011651030b049038041c400c00799454880c1c40c0182101e07040c8501b101c18100c8103200310000d0000b0345400389a0000100307080c0002000103c0d0f00041c014407d65540c20318803001e900c0c6900609007240072882c008060040751800c0c0c000c2594000c6000d401500304200070311030048075443d200740e002c0c00190784038400f000c00b02a0b00081000d10b0240d62071501d40c40c0903140c0100b070820040100c2c2010350070012115807802c0f0080451045928080b07400040310340510009005040240c822940a000010180101a00052458881e44200c811250350724035404003140c40b08244000180381550449100e2201c40c07003580600305100040c5070051a20a141d07005c10460f0b014820300342d5038000c1681c01c204c40c2e0381090140320003821103460446228100b4061590206a4815203070b03214103030114061440750320070025141d10300c100302c003160303035607a6038241c0280c0300d520038001520072942d804 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 387130359 1250 387129109 387129121
    0x3200303040e040b060604082b2d03020c01090b1501080705070b100314010516090302060715091b1404050603030306040e070b0a030501080c0f0a09020702040213080307030305 77
    0x4401e807012540050b40b1110181c0e11a920302c54036440043c511903020074248008034410604001c2e4003000b0320300d6514001d684e11140c0c20f03144020320404120041105815100c854000500c4180300300d4543c00c500146d005c42c402c4025006402441c0c00d113581c0350f2916151b1010300440c41c2e0254020028030170b0b43c17410018440c004440c1c0100031a0b0380004108104004800608000c1440350705c0145003c88501081e101d070b542200c2c480050f0610b482c030b030307440b001880107440e02c0c00068424030788182003186015142da80859018060303840c1c00b411080c100070480b0a00b074066000810744a9100d0002c4186403c0c003070f482c0510604a00924081c81101c10201003d4102481103600461008008500319030750740c030400019250341169424140168080000d500c10b00c0c8002c1c140070f00140e1004905581861000c910700584165960711a14561403402040c3e1200f089800c190307940d60801607542d1015001284c003a12818040480e40814204001a1540040302411505110340d070140500d454503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 387131609 1250 387130359 387130363
    0x41a090a0e040f032d0203030403020f0607170901141014010504030b0610020a050f0714090601050307050a11070303110114010b0d020706090203010c020105190501150522032003 78
    0x1114018900b5102c50740c0100403d01030000729170090007501c00c15900011098284181c0310282c0f00781c00146c0c0c40130086c0403c06405101c42500d205c00c5100401d43c614088100514514100b01e0019416010601007001e2388000e4100441c0020b505190101c03606140440c2c0c41c4064140c42840480040c422506440758880c008840880307801c00c81e000c02e0342d01c5460030023003030042c008028400d510a020751440001c009000444600d60044085e00c40745240501d4800501c1103c0c0b1007502c1140000e0801005030b8001c42525009503980c5000360701c420200400303440c052490103a05d026403080c05400420503a010204451003000b40000b4001e809040021700303c0d02100703000b414040c0c44280f000701e1580103598064249140074076408107200156802003821030740c2109003100142d440700e04002c000c0c4003070820901a606a08400c002c158500b0040b82c032250400021a020031400141c0a10120181c403080b4224012500302054030725aa0715040030307400c172082d041d8420254149800a4907180c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 387132859 1250 387131609 387131611
    0x12033a02040e010b0d090b07050415030b090f04050a080403050a0606150905011d0a0e1806070e04150801050901240302010c0b060114040801020403061b0e09070203041a090a0e 77
    0x42d25496520300d909140110300c00d070300600b07a0fa80030309039111800c0f000720366a1803416001d15001c0c0c0341d1550319420030444000b91041096080e083c075003009403141007a1107014516520500390360110070280c485103032aa04290f600040905504408100030003032050100d00102c07003d206500c2080700d16030314441142000d40a02144d808110b0b0000108819405491001d1440c0001084000c501c031418000440103c40b64008501d500000000c110000f8001e4039030060000d6418010151442c1000c0018041c5540f030b10007a006980719600a9624000c220004000d420140300901161514050242c020031201a411020f84801d004084040001d1114242130382d0301a5202e410130101512280c0741188054546410404a6181400d2041c00700e805003000d41000d030300150352149503003821001d4034042c03960b000008104040007080f4503040b0f884a04c0800003924210146d94840105038194022a80442079413080450700844081c1d020000302441e20b0112054000780c2c1c0c5407000c0c0542c0c400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 387134109 1250 387132859 387132869
    0xc0309010c0e0d03110708030c0c1c15110f0d02070314030106090b13031202030d200306010309060906020d0605010810080c0105070c090c0c0614040506010512033a0204 74
    0x10700b881d03a40c00840c0c8104440c1031052200006c855550340d41d100d902c0d141d5803090b144808180c01000500702c0d00d10b401c01e848105151444074480307010815444850a01e403a101050101c5955000c0c880e4081084030305641e0384054940794039898a02c0c000e4410007070f42c05010b044001402000031001102e12260a0303d05903006a52100c09507400e00c0e0f4400d600c0e07803156454140b480c0b2400000030020301001000002017850b540550340361002c2144420680c5c00046003440a140c100510580c54514481502e50200c82480c02081d42005414200c0c010081454040c10349400041c4c98900d0564540001d801c4400c280d85400180c0d440901c80c00c44032049001d591350f96042181e42d06c10359031060016018090042e44001840c0ea95405000304a5104500c2140800c4d04204007030103000300d49c401ca91009040d12858841482c6c159201c54a03201c05000c1c0c544524120584420300c0700c01001610382e1149070041070000140115051072107840d28015220540e144c401095440818034020f540480d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 387135359 1250 387134109 387134119
    0x3011d04030e0f1f0203070c12050c0d0f0c0306060501110f060109150f15080901020c15071205011d07020f060f1b0d0b040b0111030f210c0309010c0e 66
    0x86402d402c0040020b0f064030310360b034000c45442c40200008080041c3c8141e0b101140c00455070344142e441c082ca10161664801c00c402e6000d0031100021450204840d6030070501205c205003d0442031800d40b542e01500400600f03000d040c00000300400420307a01482c103890090b21015004100c515400e0313510389409540c864a5040600100140c5616820029100300c04881c00200541c0380c080c0411051040e40c0303da851450400b0000b03000d1604150115000068080254540851a070700030b81e545d003e18480c0c035001d032002000210110b00c1044943c159040010040c0550b503540e22000780341030300d000401c1072660151001320b0400f50001403c8510f8006a4015010302e54803001c01c120320f920014158100c0c6038076a07818024a010700300c0200780c5a450550009542c2d607000041c03004840d41c1d000c0443c180240740d03030f1000394460300206503a4807201a400c402d990307000701d007248a80c01400141424000d0144010702c48c030020a140914802c9020314003c000d40103880008455984642c1d881a0300303d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 387136609 1250 387135359 387135377
    0x512071505060a03020303070609030815060304030e040612050304050301140906010303080a1d06100611030d0f020c01050f0708100f050d110a140102010509030306150a0c0206070803011d0403 84
    0x31034481d00030980c0320300e0080c1944030350ba0b566004241140d0117074400702d41c8207556a08450030140c0102c04550804420381425041c019400046403507480041c01c003500344086a46068003a558580040b0040c1111004280c00c0001ca880d0482c4d80e601b041c0201c070301ca9402c0c00150308281e0800c0400c94410b04103440100b03160b9181d51825161140003038024000d054642c0c042c0c5591041c1005010440184400101003a2401c10454031003040150440c80401c120b14106020110f4000280d920000340f2150001d07a0b05a100a010020700c00c542103034000d5400c20040000c050f0a33000c580f0f01c50281c648600c0a1a502e4039203003802d02405000d07050070000b0600003800b03182003100c40c10f44280d02c920541c4041018800c005083c806841c2d0055100940725050302c401355034203006240e00118610002c0d82181071043c000380c1e0600404c0210541490007141c140921031054a511100c26005000d0365640c203820308008403280d100b4026210018412940d140000b10310025191140350982c0d0f900c100303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 387137859 1250 387136609 387136643
    0xb031f0614190e090c04151508060901150c05060711070602070f031112151b040806010608131709010e090601020a080313200a060801030b01090f0204081009051207 72
    0x211001c0038100c15414410b450200405c0c2c1c0b950702c42c107001c851140800524691400c5072841c513500f00c51041c0f8041141000621a864940c6d103000350559041100e00a90441401c1084443c3d00160304080e016128500600074101d401008a1780c0c007424040c1561b006540381c01050ba82e524080c442d03d108680381502c1040418a40f000481004a00074803802485c1d07a80c0e01c1d85441e00c4001400c1c0c030040c642c8101070000562400e40b0480f50303c1c0310040c940b8201890f1600507500c0700814800d0400340010007000a0f1114401d0600402d6158811032101900c0200c0300c040010360403120000d4003054014080c01d203e440c0c142c8001e0f20903c0164020f12488d24203a484000720f8101500c0310f9254002c014046002030701942c0700d46407500685240c0305e4100e40180030012a940190701c41c4051150440051000c10002411103064441200c40856a44a13103070038840217118692061005024285d400500700c2280d8108100090140c0211420081c00d0200b401151003544030082501c0c000c004020b00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 387139109 1250 387137859 387137879
    0xf04030207060806060c03070302060708011a07020402030702031b060f0708190911040606031a040c051b030415020307050f030a0f120e030f07150b060d0b031f061419 73
    0x4e400940070300075505001c3ca1551092443e00030075011005a0040e0007002411540840034500400c00034429484452140f800020b0354824000d02034003441e00040081c601c076000f00200c4900d00d20500394051011880c00d03005071240300a8038404840801500070802d040d104400f080e000740c0205c0e0748030100940c00c0407400c004041002c01284d50b020455001481e96a4038490400100040c0d1008500341d90015560109001c101c4502c4e4803461405400ca04840d0b40b0030156a0100048942c1c4d06002040180346490360103a580419204107400d482555015408006002c0300361040044407500b0000c0c002054582c0103608032000000c038a0840061f90318441c10340300c501c81220728000150b6241c020174107801c40c0d0000000702c2c1c905200155140c00c102d00707601c41e640c9a510401d001c0280d10103650016a540c450712040004180e00d4464a402640c3c06000d88140d1620303c9008801c44000d10b02d02d13038043c241610a140b2500c1103100929850b052103c00440300004050307400410505182c8144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 387140359 1250 387139109 387139111
    0xb091b031c180506031006081605120411030a1a0708010806070e060f160212030901050a030b040b030601030302012715091509060902121605060306030f1b090f040302070608 76
    0x2c1c5146480714000245901c0e107000070341c082c0c0400403a1024031410804041c00e00b0001070a08000a401401c600d0b18042d4000c0555888000401221856803642d09101002c108111012541030050400403401c008603030380008400404164405070580e0b40b0308090310901004d2144000540288001945840c1700d1020b20380301c1c400061403d810010610740e0421a90804400103c0c0d038140c03105140290302e01090210384005001004504c0d00c86d03500002030050240c0391005040c10388070040c0d01c00640c6e0301d400c405922a80038085032042d43e52070500a018045900b1030150300103141c1021503450300500e43c60a0210342203040365003030340980d91818004001032001542d14000c0480c580c101c003501b030700030365000e40d02900c004140050640104070a0140345038500103140e04c4103038912084000b103004d6404a1344100c070b16540740d607680c1c40030034240704040082144034080c0983c040d88948010041464850080c1c0382c4007001d698414541714a140c003070b900030340560302844e03007000528483c082607 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 387141609 1250 387140359 387140387
    0xc061d0a03141e03040323060a0e0f030409090c0e0705090103090201120c2a0309030b0a1404080306090114010c0210050d06090614060405011704050115060503040302100204051008090304030b091b031c 88
    0x222054a41c82f00c0203400c58126800c0103182903114a00c400030b1002c508440b001030705103203900d01c0c46030a240001409500c91800014145921101d0030419607000b003000032003010844109000c035501c3c401006055040c0c0c900690220f000c06100710b404032603400885112a64551101d45070b06003140c0f500c03004810000c0c03a58000c46d4070303010a48030a043c01c050641c0224800d1801c00e407641840020440801c4050b00002c00d01c52440315880c94980e40445c60010040d0141d40c08a40d403040c007142210184614420740100504004000031641450742c0400100d03500703440d0200f80c0c07041c1201001410b125070311419000800c9411044040301e6103150568000c0d10807000041c40c200c82148001e01000c6642c000e001040000c020007040c940c062140c80312080198004600c2d10341041e0001c0c4070030b40025048820042c460001030a201420000c880140d50400b00305141480c1c24100c0c90b940b5000052078001e03081c07071031541100d1811b00042a00c4816041d16091150700000d25040725004541481 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 387142859 1250 387141609 387141613
    0x1c0c090803041a1b1507051602010c0317131a06010c0b0a020d0c080f0901050403050a0507080915040810020403021e030312040c061d0a03141e03040323060a0e 70
    0x288440b400144c461090a80d44a00103420004544030208a00500080c4900103008040114001000411690203815036090918441c0d58409040c01c8a007a164454906d030900340c0322092100d8031340504000159a441190800305010401301a803403003180948a05000c20381140f004d0002400e00c05407070358405000c1c00c005042554a90850041c0c8040500d22004640f05109000001c101c048915a10680100c002d100c20300345a5030080592181140d0030b01084808502d00c4200000c4008aa0070940c009003540b40411041100b6806036002e4441c0c0d00c214443e00b503100f04201a280282c03011207400420301c8010000100590780d071350075a909082d030705000403c5180b040054080c00070b40114081e007425022642014005081810103000d0341208125403c0100c01540e5203002344d00075a60300c1040e500642415106003441e041d20000000d440c500762217211a69203500001810440b80a460301e205800540e155403010440035004d51042038004034001010303066603411401080d030300a01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 387144109 1250 387142859 387142867
    0x1030b010f172d01050c0a11010e06150112110d0608151302040e06130c050114180a030b040311070b0406050a0e0303090a14030d03020310170c061c0c090803041a 71
    0x110f1a08656045402580d480c00c081801c90314181e022a100c1c3c2d520b81580300130090b050308069002e40e03800c0c004192040481040c0010f070785603441034102a159540c6004180224103071502c0d05601600032800030504507103488030000e10100001042c600d9810182000c0030341791288400d5102c455104002070b40c01940380da5040d842080c04200051180074542c50a80203103e50745041a4280f07040d034400b504108000c614264100c19102c1103403262110100b160b0031110510007c601142c1495202034140e00481080105054200f4250000300300948217441980340c4810b00007071030703010790b00441d00064014440411804d024500180d0400c9008003260b00b8210940001034292440b5002800327000714007001c01285050400c882000510305003801d40c03c42c0f805022115442856214000740c8a20304140c420711058180141d6901c030101a08250307036244d80b03806002d1103c001810117100c2500d0001441c00382480780e081103007515480030145150603e0800802c0d5415600e80d001051210300300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 387145359 1250 387144109 387144193
    0x14090d080f0703020d0311160203100905100c14030612010e010c0905090c040e13030e03060412271a04170a0c0e0f07200601030b010f17 60
    0x50003401d4014103034445255a5002850000d081c0140c1c44071540616082c140000e801c102000f09840003030801641d020b10307060203800001d242860100c02c40c1c1c1c01618240c0c2a8003400310104450102c0494900c2c1401000c14200c030484c0e26071031280016000031030274400705800d460004042d2000c1d050350ba0020804603207404c1d840c0e0031242c0446075480072030344004081245044c0b00d003901d5030014003100c1840c2482e240260003026000000e01c103111072200707205140109401280201c035480005021601c8a1905144c0081440c50070858180821195400071101c1400b14040501143d84001880748941c9400c3c04245985400f0201d520242000c0c84041052100301d1405603040d502c4000501c0038009034100118000851b400901c829541c240402c45028000c6880035001001841d01000c84908030380c074282681c0402d40d106000e8040c400000003800303944001c4074107885100d5810070301259604c0303885681c600340c2101803003160040720965405c4108401034010100c898032a4408040b102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 387146609 1250 387145359 387145373
    0x402060903010c090801270204090201140403060605120f0a11030a15050103110a0614030a0209060c010b0907050a080f060d02090108011a06072004021303030504080c03030a14090d 79
    0x61000c400030b9441001004015002d0041c00c0389021f01542c0081c0c0d120308405034684c2c1d0100420702a00654079000f501046900c02c0089420510b030100c04961290b8480ca000006410681b103890300c201d040d064cc102c0e07040c90100d6801c28165506000f005407147e56500d41c0d070b1143d00d00c0c1c2041d915001d5010b0280108e034140070045420911004006000e40c110302c2d00061036454032403000e020b84915072041c0111034001c0c02c1c901c040e400c0c44c89825126070303031780840c84040d128506a198203c1400320310403a14001c15041411701d0401100c8140d126a24800f040301d07203010300c411520000e003d101c0032402400640b00140c1e001400030780300000300070540d004280071080aa008911907956000194000c0d50340342414000820304481142c07070b0110b2915401800fa00c903000d0401041606e0041d03108a41d0340768105e40062540620441c07a0a80c2c0381005081038126100300341039806121288041803030040b080f280c1e42c6026403a14a845031415880c0500745c0c0000a0300c0b600300052000300000700e812 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 387147859 1250 387146609 387146621
    0x909070f080a0204150503030a03020d021b100b01050306210307050f21090105040e060d0512040617040c0e0411040603060902010f030e100c02010914150903130905040206090301 78
    0x4681c000e00000c91648184411201c0301103c20380d020f1820304083c0081d0b030303000c400c860f544035880c43c015031078060742c0c1c00140003445800050001c100c0c2b040e40c055055400410680300070851120100b084c440c0318801510607102c112039090b48a00f940c0c0381407030145d41122340f42442192020450f8103201c204c0d81e4040c5002c61384c07003903004564405072150601015880005583c680380714070660902f42200c002030090701560084c2034411407444001015138403440d1180b101da5401008a40f00c200300aa00e05c00198854000d58000a0965001c1d0380101c558102e994010740d840046030f030150b850f16058040514014004442400340d1043d00c241e50380e0307240202c2020718081e0000107220b860600c0090205a01c01c01c00300c0074513050903084440f01002050381c10b501da5081d00041121009010304900500440100401c14010b030420003100e241c1c0006d00091072200080310600c26102c403403141e9906d004040d500950000e4040c000d04c1444081d403c00c54101c3d10141083d4140030718080041c0c20340344 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 387149109 1250 387147859 387147869
    0x2070305090a080d0210180f0b0916050a0302090601050706021305181009051801090501020901090803070804050d0c0905070e040c0309030813021801062102030c090909070f 76
    0xd001c640c1a48514007510408001d00884004000413604840041d4132502c1c50854091415074480240c00c0f1503c2404051841030352000740c400d206007140c40e040c2c180d084240c403040741134815116440c481c545c0100c2c0d43e0003581c2c1c000340007580061440e803c102c41b280b0300500c0c1a0400009100c044000b030310a0001e400802c4450781c412541c1401c00c001c0c4a421219117041852800880c801c0c40028810243c82c80180d40700340a020507503941e60700009000c01d884655260701c0d586804016420302c5410b501030320405000760f0702d12100d541e4542c4829078038055041c2c05400c003401004200070500c0d0642d0046509031003080030803040740d03603840d9040840341d0440c1c0e0080450f80a201180081c40c00f0701c141d08009406050400030f01c12103440085c00d00d04020842468070020031300d82019136603240f10ac0c103000e8400c44081009580c4408005120061191110745000364280441d854000c681c0242c81c40345a0049419003407941040800c0f80022014140c0150303030041440c0401e2110740d40101d1b2001d88 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 387150359 1250 387149109 387149117
    0x405120705040f05040317090304081905061803040e07031811210a03030203090a05060403090812070b07030f0b06180f120a03361d0c0307030f0f020703 67
    0xa01d410240000c0d10720901d00e0501091400742007000203a00001c155000c40e203041117100d240e6951081140c611312840c0c0000c1030303e100d2084510b0000e50281c2c2d131001c5051242003a58020b40361603000703184030b401d24280f12040c5c3e002440b081c00560750010000754080c06a1074081000c0711003d10441815480c100b00703071804425885d0030412400e1820780201114420300d0b00b0902c141190039500d84940380481e000f02055000004511403000401076031040c2c9400805a905504240c0350203010594640b003081118081d003d120443d07900080199460250401c1a81180e969114002c5000b090b86c0540074070102e0740e5aa0441403070f100c41d0050121043c01d56059864801441d041103119100d05181e20701c02d00508080e00306601d0049018182c03c0e50506088002084145d407030f10140c40c94210a140d5561943c902c0216121400350701812103d00300a1884100d400550300b40d9a8941140c3c5c40d002e124080010803d0300784650310003078801a2401c00001e414003001c500300701307907440110264009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 387151609 1250 387150359 387150373
    0x2030c043305090115320a0504030b0903030610140a03051f030c091d0c1507140a170c0a021309080c07060e06120105040b040e01050a0c080a11160602040512 69
    0x9411810300002442e86c55203c0614241144164041c017101802c00304901c01c000c00d100e4000790150303003910090750f40035054501e11301c4c1011100303541c1e4204640c81880b80580c41401c22149002c2c20002000d100f6069840745401e40c00706050f40a020050600d112442e42c2400e450005129031411201a5103d00d0b80c01d22428903140a00c410f85080c401540b00b006140000c04aa4140018540b03403280e0b402c0e40c20b030000c0e4464a8012140f030148490103040d140c1010204070710105e02240200d031413880f03200e41c000d0051001d04034150500500003031500316403088074624003503c0c0412a41c1e40310704612402144230101d42c1d8400071a60080d03244401d076540412070900445401800414103080151031090510103010529210301b1010b1007014011503030381801900f151200c0d04500003030842800240140c3c01e100c29008010031801c0700c504000380d1404042032405001d030003160318600042404038100780541d400010246040c0d001201d6950303080100040988894140c0e45001038100087c2c015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 387152859 1250 387151609 387151649
    0x14040e041e0606090b06042601091a06090c04030f0b0910090f02030c10080106050c070b0f03040614060303070303110403060c110601150f0f181202030c0433050901 72
    0x40c2d44605d0b01c0244500c00912003448103111604e061040e90707421161a0340105c040c0c01e60140180119640a820504031030001c01000d44110545030054405540b0041e0742d0b650120b1900c06802075000c0109000d600f14000004038070001221a08041200c040c1c46031480700003019400c0392141c000031151862003400200a510b4184140032004000342e42c451540e1054000082c440c8205018580a0101c00f242080c3c5180301040848080d00b03000480c59910861032107110f02c03c0e00202c0d000c581e428104150844c00d404650491406158094004e6003010615942a030140ca031401c1c1c240c402110a020000100340c0b240505020485203480300323001021808101e80c14030005800007070303610446d0940b03c408217600040c540b10001061501000c680800a000c41e40385e840c0c59181914028180004500c48030101c41c0d241c0c481d4800c400325800980c4401c14082074808103000340c0d03a078416400050341400c0760301745030aa1001f940411401c10f01d445600141d0485000c1e0055074000d0409207810301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 387154109 1250 387152859 387152861
    0x424090e0d05040614090d06050901050615160602071203060e090307030912240e07050f0915031005040503090f0f28080a0f05060714040e041e060609 66
    0x540c0084802405001d1044400900300340314512070a81000240850040100914170545c2e10b0300000404054060507281031080c007a140c1901d00d070342294600303001b0079024a04201074031000d85e4034811150820409600800f0304d070883d40700980705180c0030080b140000d401d180c203103051056952400943c20b070400946c105401001080704045500811080c0d0101c0e40254070b0310101c601032400f1021280326454000002000c90f2400401c901c0c0050100803c200c25420032041ca0706074004565455039104204900351040084291b0440101804901760300c3e4008945014400b01604884103040c1c50480d00702201e0007180e0640d00b40d0000300e0a04894544100c07010040301e0119840c141b2400040009080c0590464000c0c1c940038240c180d441c551100b030044e080007080c6900940d80d01c3c5406003011594801e805004a41e1070048000190200703009000081e00552050011400c09003080a140400d04005e4420b480344051900201030807401004080191403183e880400c0c0103151025206c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 387155359 1250 387154109 387154121
    0x90801230c0c03092b050d0e04110d0c020115030809090f0402031c18030f06050a050f0109021309050a0f0501092304020d120507140327042409 63
    0x8240e0038041080b800d0b011000000e440d01c41208030b03094861020103164003030000060b00c0144580300c00110901c801e01c507020480080c60032554440c100d408016000708001c50300e000e00008901c50091180000200d0150301006000700d060000160101d0160001c4220680b50340c400c880700000043da080281c203060f0b40d031680040b03217911042a54113050b030029443c1c0514458160840454900c02a5203910400b0f62140e6407818247d4504015141c0c1861000d514401c4e2041d41d20b90304081c0400d030381583e58840c8031721807a00205042c40c16400c140590000c2d602c6404007040b01a03840f0004184a00b59105282c001c9d440508000740000c0000c030318000b40d41050380f20300f41c00c3e842c01c140d5006004203081d501d140400b1a003900c00c0300d40c1d59480002d2a260400d040035240307018a01c41d41019507082802400704a00404c100700708601320002031035591144440700120340d003140034000c1244900b018400b448100003480441d8503001c5e2214500b80302500d00744144640c2028008100c020340c0c0f0b00c80c03c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 387156609 1250 387155359 387155371
    0xf06050403080a081005120309120f0703030c0602130605090f1002060604020d021309050601020601090c050904020304061d10231506160b1b121609080123 68
    0xa4106071035610340c002203000b284500d5003030007030000015415088050100f4044d220060980c000c094504030b000e5941d1f00041c2c4024000e00000340ea40956a1000441d059400300c0d400013400a241159011610040e88100072110301d07030203001c12440c9015280b020350140c00f076030340c0d80c0342c65000304000c1225900c000401d0f54001d0100f480084401e50f8080b558507801441564056a04e4400f000003500910840d54110203400b601580421412841c2d0005402a00c09908481150740c03500c1500342220071307020310800451803c208081d040c3c2050b4016580c05401000c0015a02c00440a211342c004042101901c3c04d400401022808094078440c82208400600c0106844848403107602250000988100c02c8070518180321035150362000700300c030f0b0b80c2c1640c600460901141b030702d40f070782440600380ea01001d840d212011520014003080203988000f15040030481d2940c44d11000036520b03e0805051204011081101040c1c0703500c00d0007403410b0140341d11070200c0ca400c201c16082e44010740c0a404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 387157859 1250 387156609 387156617
    0x51b061c0911041406040c02070b03090304030c05030303010e070e04061203020a05100b0603182103100902030c070303420b070f0602180409050309040b2b050a0515010f06 75
    0x2200070102d070254113859011005a030006540808a83c0503803030b01030030740e00003048140000100038024001001a008881c41005215286070b211401c068070b03030101b4002d28810410781000900414403c100c2c1000c1c100018200042d0b02c2d840e858009940a40c1080580140e0301c01c0c040340042000030084003500004200c000c00908404030700194540c40040e00121490702d401002d50107140042c80307100194110720003100040a1a401d5a0445030001c03902600b0f44854802c2c009504101402100e104113400761545d4600042554107800405e041702c1003840701200301140745904810325503840010000029080303046400c4406600b540c07286900865110307841070200000003a2400071212010303a00c031070301680b1180041d00d01121200008040e0384c3c070900300003403a8103010703000c402858065402d69086c40000d01d51018088840f0f2400b0703c1c6411807c00c40064034802e66641201480e01c3c2c0f090042c4e402006039911203500e0500540382d21581c841010004020360005480601c0092809040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 387159109 1250 387157859 387157871
    0x213060603140702161701110a0225050d020603040f020604090b13111e0c010c050406020c0307030305030a090f0b04050c0108090703052a040f05090d0c051b061c091104 74
    0x40f0081e042c143c800c2100503040b400c1b1521040700e00390031140440036a841925154000020f009580d800c104201e1008040111901c0d02c0d219124141c50003602c030051b02003500ba040c55824400c05520090080d2b070100345800460005a0341d0f48000c10042803040c030041a070b49080000c11140c000d250001c0300d03c07180ba215440412011100c00d403113034050f0032090642850036552000c4c89600c10b00782038440d17075480c0c8222007400c0e0341c10001400c107031480d0f0342c2260a42d100c0d10081c1540c0341154000900407403414000283e080500c1e4105403821807240c600e1114a44166480800c0c80c02c080d50304039803c0d0006082c1d40707103550f4800101607100301d20100429040d0f1440d221144c50b00000c038855420500a06a09814880390b13000049180801400c00c00c030001002040c200104000d0352046014081e030b462080c0f50500c1980c41c02001034118004d0402d00c007518814000c254005144581c0000040c400c10008480d40401550f81c80c1001d903006c500c04c5094506210302d460f207012860701c641d01d0a6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 387160359 1250 387159109 387159133
    0x1106060d020103020903031b1507030e07051005070c0902121e0c03100b1209070b07110909150a141b070b04030e040204032001050a02030a0c0213060603140702 70
    0x10a612031440d020300f0700580d58800000031a040d88203d070b00304420000304242c40e85a0107400115601901c03c00c8034000d1098803070160860075142c0c03422283c91075038480c0000307020504e00100403050aaa040c10030a142414503550300da040005903010900456000c10166112818010544d41c00b00d012820304001c0718040c880c4605100c80038010b04900f201c0407000034200408004c00b90081c0600704442900c494a00040031a4220708899460850140e00000591a44000191001141d001500002d424102014401841e100800030a9584030b104541000c8544800259005070000300003c02c0c1e02103a510582c00a84014006071614285000f016407402141401e58003442d43c007001400c05501da60a0499180c0104c039800c40d44203200242c0002040141501070700c07104008808244980700010054410b8001c0780815005a0403c100407605a40300b0a50540750070710007080c14840699403008a4102e4040ea000301d0086541d5030710700324841500c0e010507503200784d03030744014800e0104070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 387161609 1250 387160359 387160369
    0xe1f14010303091a040308030a050703060f0f052403100e0105090f01030803090109120e0406050607030203030f0c16060203090c0906030d0507031106040b100609150f0203120a020901110606 83
    0x24441d00c0404c0c00e441e0034404083c50707140111001035820442054490819407016801050103940d100080303403400320001080488010a030b0120348920b008034643c94a0101848000c0380d200e0000030754816041b41c11014044040003071030040303424002ca4600e00b4201260b40341c0d40081030b04554420491442005101016500c0e02c43c107681d400b8031503a41303070746a90072070501400c0c900c90000c12401000c0403880329981d00402c03400c0c45000c110790034801289d4420074000b544c40b8841001d4016007081002440f0b01c40c94141e2245c028020404040c42c101c3d80350300008400980700c42c1146c855400005002d0810703c20000b48107650401c5030000f646040400c0003a544a100340316200c18018046002e03c141400f8004040001c01c074801551010315151820410b0700304122543d112003000350f00b0110b820b41c4108844c4d004e07144003119440e610400703034400355109569400100c0c1144010810b070314000800c03100c0c0e180209520540540c07984100d00000d0201c40d5015001c1005a05c95000c101c419914 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 387162859 1250 387161609 387161627
    0x90103030c1a0f01090908090d060b101418011701090c120b0d06200c010207020a0b0a08071d03010e0c0a08191e0b090705010e0a121101030e1f14010303 67
    0x11030700000b07044503c2d2401c103400c1e001c1c0d9090323a64441d0100403420300b4002244c000c1e40d803081040315290001c446100069901c01d604003145171102c0f4080c03107084404504101141c0070700700d050500d160102158103000c040004240c100c5403041f41c807020342241c25600840340c48810001d559007845001e10807404524040d46d6100c014006546640d030010803110390b00c204460182600c44810b80d0b03948032403502400717540020300880c000d141d00c0d000051000100415036001141d25540c0641039114500d00710782105140f040030b00b500c12060000b8003e65000d100e079944810040020707001f21100ca00c10044000130030740c488106074104540303107003421480030103c0c9001940003400d0200040070304140da54118640e4001056500000c0900c8401c0400190f460110b5034240d0b2100340e20a242014440f41402600c81c0c02003c0b0148694400051408007940204030018540000c0401032031a049252510b28110603400c00b400040b1401100280e00880d030940c40658086051549596030060540329 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 387164109 1250 387162859 387162869
    0x6060f030c100e120106050909190f1e0506090c01050426030403050d080405010b040b090606031509130b16050318010603080a090e1003051c0e090103030c1a0f01 71
    0x52202c14040618007914440f24503030806801350840300d4188009070b000342028043d5500c43c0b5660400244000000100c07890324860740341e9000428034844d940c290410102d5001200c0b5610851001c0c0495040360100e40c803224013035401041c40d810445503140c20a9085034000e410000108000d001114540448403042d80a01c1000d403036103003031135003007500714099904000d10b00c1c000c4428103071405500120040c040d40c041c10081102c0d03038180d004c2004030341784800036a42014640f40012101e140a1025551002d1801004195995a43c0004411900c1121041c0640d200c0903a0700041c02014410329a10001000440350072024a250290503030000078081c1078454611102500e55010a4200400840d4000d40040d00e03402994005007001059020703000700c1e00b031034500050000712100c1d01c02044075001000740c041d0078451000801000c01496117031b000e1104905159809480c0d00c00e03942d0003580680ea410044181b41d2401501e003040202c510320381c5454001c107000c4209250352707285045503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 387165359 1250 387164109 387164119
    0x11030c011d010e1003020715020306011209031b1407050f09010e0417070c150e010c0305090406050603040c15020d08150d050303070c02241e16060e06060f030c 70
    0x4401c0126078252040c02501c2c0c100c08200c003c1000242c15401500070648603100c01c1302d07454000680c00c1d00701d02003100c510b0b0006046a5032802c0c0004036070700504805010345007140d40f0b1010981c4560446a8184045500304079840c03030304150801c2888100003408048903210500718000002a072064018091041400a0039021600304180307030103189149805c8417480340d20345109017405ea0300d10501e071142d0340d9014014000c0c541c4040c41205051750141d41619248001c1040761402c494641040d41e10a402c165501b0000c11790359128406184100e00c200440c14820b0705205100161707200305003440d815944050144002107411800444c0e00c803800b848100d180303a035141300092589011020142407804000248810b0075071004984c00b02c00c0c001c1c0c03102180c0d0102070360b50100d0f040225101140c801380600c40c41d80c1c41c1161036810041c81f0001001c0608043c1d10658002604401c21401c4419540d40c4440c0111508103104030381d8000070407940303032070b004010401280d15280340440492240d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 387166609 1250 387165359 387165407
    0x6010b0f27030708150c0d1e0608010c0903080307180f0311130e1e0a060507030509070506130e0a020c1914160b030a060806070c05010e071a130b030f0411030c01 71
    0x103c7c90760381c403d8002a0030850215005d018442c0003d00030311342d60240350815420714103c40308040c015000320301202e0740300312404d10719035841c601161450f45408006080102982c6d0005001d44e003000014091802410032a0007408200204000401e0540e504042d10341030880d00c010003400440d00355003c04030141c5182c1d1114501e1011400e19080031030048c2400d00e4002805891941640590311444480c012181100c1d100da04010b005d0086100042040600d001e0510021800e1a103103900084100342c05410052044000f5060072014a156156150307005c1d002400c1c00703010301c86072401101750800340c80540c1b1340040c0c01c507541c0028014001d0f0b4940000c00704107d0701d01940540d0003040312034241e03551424568001800340e088070406654540c00c0040611120002080c000e04650719414080040d45107810403500c04e402c0030a0007503061030030300b400040070010f8000843c41410740041810780c070b1074146070824003030400820070342c06580b00c40c042c66020303604440340d60b1003494000c0154051f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 387167859 1250 387166609 387166627
    0x403050f070b0402041805190809090a05071d0d03050304030e1f021501080606090907081221060d03030f0f0908030a06150206010b0f27030708150c 65
    0x2520941496284104000030000240301450a44501980c4200c0e13003070010342203040202442d0074560401400c2e942003450a00c400302403222140d8030061180e1009801c11700c0e040002000310300c0c200c030000c9a840d01e42042110f2198032041c07510350034890742d12400000d440c020212b43c5085001100034180b10000000c1000e0500030355040040540041c00b80070340c00500c119a2480303466400c440310147c851039548100301303100c03144403038140c0e5a80300040c140c59440c0810808a41d0300075004141500500c000407510010510811030703c0e21920705000d64819500800410000050481c1600000240c06212280d078501010003900b1380c240c42c3c04180c4103100f81d01d4070002e068801542c88882d1410800b4070070802c1d1074010794859180c0801c1003000654920201c0d0412419416400044c1c00020051200000240151010b00041044c040c03c0c80c5100b00c4659511004000402c0007000242d0280e503149000c0114402410110001c0d10120000c105140e10ba40e6000d04010900030000c074003550 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 387169109 1250 387167859 387167867
    0x50a0b060d0501020c0a020a23040f0e0d08010e06060711010e012c0a080102040506030103030807200a0b010b0406020703062012010e0606091005090406050a2606010305150403 77
    0x7800c590042d0003190f40d00c0303019041d10750701d07454824100d00070311178a10300050607190508107007240070300401c102d8501c5815100700710040501c4003c20660300da030b91003038060a00d0104246000170310144c580b140c803541009174004040b04001c007a2132080e5000c001000010b452203081030340f03000c0282420100c5241000040ea0580350f1840e02e600c8090303400030010000c80010a00c404000f2068a0882e2055242c0d64003500380d1149009454018004200400001e8400d9201d03582c007219519100c05a59002c08140c00940f040001607402944040303224414450464031403801050040f1043c0e10f042c1c50000003949803e8a07120151819580f200300039200440f9220b10300921240031180d40d910f03c007199101c40f08010038052500381c0640d0700c0008486040013021501300d0300c1d0040400340500310806044606038030202c04607030020384030000003515840c0c0580e9400030b0003600f1080c10310082000b00c08a01d00c0701000030314015038400310040000c544045500000d040803e01000c600e69a5800d05903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 387170359 1250 387169109 387169129
    0x90d0c0201081312090509100f0b0f090904030e040b01030e070512030c010615021212040b1f23011d060f0412080406090608280b150702030601060c050a0b06 69
    0x1a10f0b2007013102c811113006500c80c1c0108140c450490f9000403680319907905031501c003a01e004c0c03c0c4418000e48030610000c030110700a4000e44038640f4003a4502030050010691071507040d2800c40208110740c03c564010b2515000f5802855000c3c602044610080342e00c05540c0c00031440b803240208006400c59106003818811540c11020690081c400940d1312075241800809a0030174100500070f0485210070019100111500c0c0d002544440c2035544503925441a41203010307240b8200030400102d55010000301111400080c000f418003d088000c04054020098140030444c1c0c1c100001d0301038000014000b04030400504c0d605881030707920f401040030517860364801e82d00704220144619a203d401c001c8148020402c1e5040c81c0c0d2039100141c4c1e00d00c82035a2661007a0703507019140707603515010b03000131045501000c2c100d80c134044e001c14000b01da0390200c0c0d1942c51082041d001074000064020542c2010840395004198074680301e03058803403a03195030343c07940030501d00107006a0030807012039420354620f4403807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 387171609 1250 387170359 387170363
    0x30f0501031202070b0a0e040b0f03010c030b12070602120702030307050604050a0303061d0a0b13020d02040e0c19180e01080a060e0c030304030602070602040308030c12090d0c02010813 81
    0x1002996142d007802d1a510030501510401845860400308008101c0e034182ca01010194840e00c80d45856070042001a05140010680240042c01155030a503000d016031000324030340d42c0700040c1d805070080030711022441d0b00007070350300c40d500c5040700b08030441e0300082a140a0500a549544650b60380c130000c0e085228201002e8031501c40d500a01052100115201e00e61522030744003001403541d03070b440100c03d801140040710103590071076000448500c02038101c50480f100080c401c7e88a03603c1a012101260889085200c84550115041c009101748151040d0054a5441c0840c02c00b40c0c008903803103540080c40991400c0050244d05003113244c40b8811018060b1803181080d040c030f581c47d009445d40d0340c00502400c0c1e68060600102c194ac503078000c21036003004400a80558585030031921018080e42c42450301300c1305e0a03070800000002c1105800914000c10303200d025190703508141001a0300d06200985041c2d03485e0400442d1090040c1c1220030418101d80c2070a18825656400c451410011005000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 387172859 1250 387171609 387171611
    0xa03060503070b0d0f0b19090c0c03080f10091104030c0b03090604140a0503120f0f012103020705090c0a021002120109050c190f03110405030604110a08030d15050f090a0507030f 78
    0x200c40c3d1f480f8120300710a0141c2d911180d00304100300a0341c1003140d80100005001d40400c160501155841b81c402d10302644c00300746085001001f560321900002120400c07520070340780d603101040a100700702c0f40603200d03002007590000070350450405a8015480d02c0c40078000034158050443c110500207000e001284855400c032040c0c81e168501d04444034024281240e0b04038009100c440000e800d0940d0f900d90368180e0b564030b4090b10003040600451801d103940c200301076095108003480044c1c640e660a1029108021030115aa103402104074040d01c0d2000d0100130240c2107005011440194418001e05070440d10010000300c0d60b5116114141081d100d110084418030040e00e00352440140c00c1040701700228076903502040f411170308103408180d5024900440798503070071400c0820701240c1c03610310002d520000103141e400f82542c0c403541103155912a000065649440c0d51598040c40c0e41111060b005180c1610500c3e0100368190008640d248000c00c07034250340d40d80e8004038141a00c2a80403181c0c5d0720395108 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 387174109 1250 387172859 387172879
    0x1051303080c0c040501051c060b030f07030c030210090e0606090406030203241e040204021e07060e0106060e0303073302120109090302100c050d020a050a03060503070b0d0f0b 77
    0x5030551500100f0043c580143d040400000f443e080442c0440318a41e040c50003c1c0d4419900c0d0707a2103000e805061030030307680b620502c002c0308050380701440042c0046218850a11340c540c038501c10b011171040c20520380014480104020030525100000e155030010045800658421405000078001d0141c3d0b0000794041c4200c01c8040104010040c16500c80b131a40400254907990303010480d000b101c03001e5820a0442c10350000b040040c1030035005024884600c0f5189031102494003c500b08540003900c0075103240361a800a803000390000c0c42001d000d045280703031910a03440c80d100071a0341c174440c00308001e05800d8040703400d1214080e100b000d107000101c02d80c4010301c0500100a900069086941c09130580f01911000240c80c0030a803040c081c0c881c0c3d141c1c000e440d41d09090104ca100401e80c2d4a80c8a05000341004810350105041c07005058036445030b1140c90315110074140007400c83c2d0b125040305010740d0101c00c050001c011032000b03682880c0b840303000c003044005150701410007901000c8855074000d9402c1c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 387175359 1250 387174109 387174127
    0x50a0903261803100c020318060c12180102060103020609130b03060703020403170304021c05032a0105280c02010b1005040e1003110d0206090d0b1e0906060105130308 73
    0xa490400c42c107002c404907559003513800d403030104452810006001580c020010080210030480034111035030801800300e410442c0f0121750500b0a01c0442d4008143c0400141e400280c048040c03c3c071000e00c04c284000c040319130441e40441d003a4810720441a1003140b4281d010002003045401603603510401906a0b14541444c5001902a4000d030008a508000c07504500785a04940400c1e2403069400400c1c0550780b0b4841914100d0016a08800b078a80c0d010400240b80d01e040200700d4005c94011a40085141c172101d20b50040c21980c0241c80d040e420b0301403414098160b4040c806001c1107403c221000501010401c4080c0e0040101d03500726900064242143d00c5165044405402114215030001c0340c10f944200030042d0304805030000030503549000d00c402285041800718554120700c0940340c54509000040060070008118004551268850080002d0100d00b294545105404410400107505015410325215940208454104003000c6034112041c0340b207058641c000c0d6000610156110020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 387176609 1250 387175359 387175387
    0x216080409061406040b1b01051f05060c0d26040507140118060f0302040e0a0509010e010c270317041401050f0a0c2102010912050a090326 61
    0x64401c441c0420310300800015407900c00e20b1190031945004100520740360800c2c41200b815000740c5007514980600c140110141582441000d000d040011a1480840060b41071108280030310340001c0c1c050081805600819100018402c2d04c803151810056480422501c0001d1400d0050740c0c0b012040140c1010b21080c04408501e43c01a556110f0008403090441c400640390000c100a90015000d16000d080105030b114180e455007030200c61401600d080c3e40e640c400d00180d40251071005455a8440500001c10400d104031500081ca40c0001d024030300c00c07108003070040308544181504400f003000c00c0011685005000102a551050400140258082c22014541c0144c0640e1020145181c0b40000940c02007042d610340400e200c0856180048003842100d11450640e821140c01002403030010443e49410704400300c00c1c4017903000207590041414200000b0522000c0201802410048895107960160246060b00d4100c8003089c94118031400c01034046000f90380024261030b010034000c15039110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 387177859 1250 387176609 387176617
    0xc0530240a0b04090203030409050c1b100606090b400f08160b0a0201110d09050106170316150501140117012709020a0927020108010315021608 63
    0x500301d81040401c0036601407104454044a010703506604c03e0008220345011500400c0e40007000c00c1c1c0e118203120001d150382224040c1006800c0e08cd811a050f4030b00103403401d114480041c0943d00d403440440e40b070000481054810150f4a0502140030812642c00401140001c0a06066420144054500c020280540b040940a200c00c040750000001412001c0080d42c680c2c281c40c0780080d0b061252609103410a99801f00d40f0417401d42d506c44940e2070608040601030528100000400b0400c458286030403800c50b4000e40081d00380d1300401c01d04000c42c103000400e640b420b4110003c110b4200351079003010a221280c00d40354485141c1003800104484050720300c4800014030030f880d2514402c0240284903840e60007401106031119a0a5003070a0442510b88803640456000c100050200d202d6000f049001140b030b041b01d9581c1da201c00703031081014207500000c0c1001d040000e002410345190345c0000d042d10300600c0007902c02211080c0351400c28000740d040b01c4080d00301295030f0040383e0700c074500f01403c1e0300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 387179109 1250 387177859 387177871
    0x1201031a012403090204090b04120905010206090705060f120a1505010c050d031d060a0b2d0d061b080405010f153507030c053024 57
    0x90100000500c22044890745041007101c004048035195442d0000c074001d01c038a580c16030303015480310304920210324514813650142d80107030308090710005c080c5405441e00d40720340d01050455010030704001412001041c4107003501d4044410340d554402d6031005104034083c290280c4070385801c0c40e081c0300318241c0b01c0d404400c031401a1050300b81c043c0c2d5901d0064402810200c80504103070000407100804511175844001107450f10581134034140084042c4a142510480d224901d071036aa45040d8041d18142c135085000c408410020100401e1200030000c402040030304a5010340c3c0f010072020100043c2e80c012149184010109107039a04440c030b0000c1a81c48150303010340d0320f54038040c14142c0d0300c4c00501804988060021080c04402d280400c0c0c079003200301b050741092040b00c8151621381807005100c800428003030400b000341a01e90460400070320800444d44440c1c484c0c48000c16680d203504a0b83c02607288110355992444d210484a400e03d17040844e20b803400100c4841c8a0300b401146021180c00c1c0380101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 387180359 1250 387179109 387179153
    0xa080304121815180b090409171209010e0a0201021002130518040c0e01120809030a1b060806010216050d061506050a030501050a030b06090c0d14010314011a0d0602120103 75
    0x11401348143d0204036040c001d03840d4000b420424a0354078240364000701c95207881550700705035010720440940000d40180e004091100454404c2c04045d210900070701e6041d425a8015010010117a40041c1d40c55031451040c403025600846c43c0c541c640000ca94030001840081c020500d0040700140e156071a1008a4080303543e001078200200340b03100074134178490681e1841010308005082c161940341e07441e00890708640c0e061094044880c005842260079103109115503540070384180c00c00501828181000745034038115030128005403041584011908201da00654011b035010700c841c1000130141800c1340c2c0c059840d0017413082c0010200c0e4828001c180c2851b8035681003002d6602c0d0010841492814400544088004004031351103141850119400c00c10200315240b034010904030305002c1c0c40c00c000211812840f110300410a11600e01c07401041a010607000308500c1c80b000c00c16a030040c112a007014058480000340703004100090781200c640c02116048055a580d4a1400b080e003c1901218a0590 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 387181609 1250 387180359 387180377
    0x3070f0905130809010e030307020409060207030f020303070f08062404050a0f180b01090e010803042d030809010c050f07050406060503010312031116230a080304121815 74
    0x302c02039031140320b00306a01c601c0480c902134110004440582c10022010b504d40001c100c0e000040e56907214802d0900e10a080140e16081c00e410013610f440c442c1c0c1c008101350b41040041010960784070060117038407481401d103001c00e0f4030382c800400c1d025011302e403041d80380c0c10b42e15100c0e02d040c80084001c1c2c800ca031001c55500308103544600e640c0f048500c9a10075807080204000340020709820f03a0f0003c03000858180351218003243c1d03c28080610700c01c2030340900655000001e00307101460940442000d013194031b000c80074075180000400002038450b07105c003410f00032001c508148179a2094a040017410f8006007218082185c02c8041600c5d50518464148290700e05040062114020b0307041d07034101c9400c011524003041804800750060450400043d0070701d1401c1089090410313000c0b05002c080703409280c4510680d00440030f0b54130800c40e9100100303402d50101c001c000c0050410001c880c0d10a500c44e0184000203100b40f42552188000340c440c108040c2512004070780603080c42815004c107034131541c942802c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 387182859 1250 387181609 387181621
    0x70302040c020a08030c030c160c090b0103050906072d02060603061b030c0c010b0402071203050c031b09030f0105040515010b04060c120c0b010617100501080f040f0203070f0905 78
    0x40c503241c040d40181340000a000007465040b0070742c0a15480140134503e2494464000c2030104501440f080454640c503000f101400711180e28400c8419040c02070a040005091100d0155510740c00100104e04000d004140082070502c2d074550203021442161f04400e10a61403200692120800c0740ca03980284034482c000340c1e01159000f04100808880840d0500e1030b240c4092a0f5144d9100c0b500d00d100b959240c6010060984440c4010801d103030180c00c0100910400a900500b9070700e0141003c114000148144110124000221450041030307000041c0d844090402090600b003900440710065440e000c01c000502c00e002c5484d585510741000300d0401e03a038903459608400c1c000c500400780061000e108a00000b481c024010300380c61103508240b9202d440c0c3e942c80119010003604032000040c04011011040101d0038a01500420107440800b6245c0c14600000c14021000344101c100b4481304021a00b44010800c00c6184250080d05030344031261500d0508445004d1449070303d00c1145400c0010710 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 387184109 1250 387182859 387182863
    0x5010801020a021504110108070e030a0809040c020c0310020702120a05010603031209030905010f020a0b0123040207080706090f0803010806070e0f09010302043b0606060a050706050c090909070302040c02 89
    0x80301307640c0081104900621b00d00111030f810b01c0103290b801031000705004c4001c40d54040044041307851103004200d50390f01002060105803014007000900795806607420901c6c41c0e9000c030354400f0030000854010384071601800010765410020458503400d0140300c08603001d0090642052068034000d0312200618035020303400400321000030384040c0c0022113003102030260398401c03120881240304920407100568030079141c801603200203911401c03528401c1030102c512154103c0f03203509048001c860440c02d09076035071142d05c001c1c460300200404082e5a206103a08110a0340011b0b170465400080c0c55449603141c41c00e00d9a55442a5454004207010b0581c0700c03035034035042c100d02c018848050800c40c426440d603030070f00001d48042c40d92240c0840501444054480082c0c00c19490320900321180303001254500b551a081040250425018210401a1100c0c5540140896404c2640450005000c4d9500e05955002e4010b0740181540031f10048144074001e58001a02400d4a001315002c000b51540c0c41030982e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 387185359 1250 387184109 387184111
    0x30f0408181323010e01270c030501050306010f0f09180c032411070b0a0209042a05040522090c090e070608160503041a0f1f050604121505010801020a0215 68
    0x1745a0700020401404a241e160707070405080404105002c04c60181c1060ba4410f03079214070700f1607002076030f0380c3c00401003442c0070885140108194180b05101c58106248241aa501401480042912103051409041d0a0f268090400d0740152040c3c403125203034603001c940075000c040040040c80c100106840051061711403c0d041c0c04980e03484a02d08115a42c1d451030b403103802000490300542c01e22000e200c2c2c2c1c985002d099005100740d16071307100403041e403d86001715100392903000041101c00e020078080c2d0b0b00ca180350500000ea60107940c001981400350004042c0640c250020404160910001040303c410342248120402410070b603841c2d20b8403100704848040c4100c501c10b21400d940c4c0c20702003543d03002d1801580c2080c0910030306255880e59201c014002030007925001280d0b5100b00c108524a85180c14020f04140d0750146211540d18010016801e802a801107504400d45a800d00c000c0120854071007801307250140050140390b035501c0b81c0328001d400018042e030150007001d501c55003640c61b03111a5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 387186609 1250 387185359 387185369
    0x60e210903191703100f0b0f04050d110418021207080a0f061b030207020f090906010b0d09020303031302120f030702100201020c0624040902130203091213060f05030f040818132301 79
    0x3400d051504ac02c112603c0100c0100b40c4e5031744a03105540c52103485500542d03502d038540c034100c09036409403881806442e442200c8510510b0b04421018080200f01041400d40c1c260008400640e55600d41441002000032640107600308a01c8882a480343d9099000b44c801c0c980216140300d030f2a4032074020b00c00038503401c441303905968010300700601c01c1582e0480a080301c0000301c41c0004031071529a0200c2d01d542d00070344070091140c2c0c0451880301103207040d0240d050030110040140c00c1000c188481e02d03541c1c1c020080c0080c800d5000d09005181d03141f00b54142c48280c2c102000300e0f200c0341085c000748002d0b0403170400850306441241c03030410203e0406004014109502a04258003050142050b00081d0009070100200c0c0c0103205809103014240406403540011910701070114602c2e000020f01148019000e0805101c814001c20001c02d5404019a03440f64100b80100e03680c1d40d00140345107814103094000c44e030110703415103403e0380f94005074009003881450403d0211110040055810491401d02c90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 387187859 1250 387186609 387186637
    0x1050f190203071e05071a0f0c07080f0d091a0603280611160305040f09050105030d080901150303200106051c03030207060e210903191703100f0b 64
    0xc0c41080c0143c2408800300450725142450034503900b0364800c140c0407d003417801d20040f40340c5824424034059004103150414007040d4440d1610b0b0b460f41c5c1d401140d000303825009680307040c0850018140110358001070441603100c0800c5000c02080c1d902e00d41c0500060b18400d002c0e204000703910f60a2040c00201c105014110404908109029a20700010340030100e00140396180501c00401c0c04150b201c06144454071075261203480c0e07414407044064861a5500c80d454070703818070004010a4030007003030207100242103240c1503d242d503505141c00d025140c0c0d00030141030080c075804000305056004420040e020710f0540142602a00c9801807400d0f10001e00031164055064581c5540301c800c80c0d44981d5420f440390401606180303480d1103c000700c848004506040390484035107101c4c0308a1b00b40c90000401c40e1064020b080070440c01c040780d81d40c8150340812020041c101c0c5e4010030300103400c1c00300c03c00b102c1108d1000e07903d10b02030520503101c81e007030700c90030099060521001c01c3c0001d249054031803244503010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 387189109 1250 387187859 387187877
    0x1305090a030e0f0d170c0105010806150d080409020304020f060c010f0501050405040b0c0304050c030a03030903081006120908160f05120f030406020d0e0d0207080706180608061201050f19020307 85
    0x10b481440c1c21056600e11511703c4108007500044100380580785c02800c0c01d00c09088249402e154001d684103085019600ca40090034036400000c3c0e806040c1c0307050302d85d11000180c40350342c5c901c0811a08a5890380b520350040011401041c02d8005400c022a12a40030708140190790740e071401e110079142c0070798008240b00d8040000070322045811010303581c0240104115440310341c07010042410b160000324140c0000e0384400c5401c09254111540540000402c0c00e007558180c41c21000030494003580c0c221180185e2140250000d00000100765400300c40c80e40d0640f42c680545107000020445089070895460040d824008120100d06080d50381081c0600c0c0542d145541c0d03a034541000798070516448072055503e02e110b2070b20450801c02c5000a54080d0000d104440c284960a07280001a42c040c1d0300b0070078940c42c1000b4141b07042031080116040c5043c0022203455403c0003030800d044c50948604158030b000c00f04a4000c02c600307491030151808800c03400002000180035026444119a15004108850 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 387190359 1250 387189109 387189113
    0xa14060904030c050328110d080615040504020d0218031c0f0c331509020c0c0d0c0306110901170603070b131401021c0e1305090a030e0f0d 61
    0x18410b040e100302c4c01da0b071404001c401c14050320085200d41c500c2000510603295049500421080e011034046401401b00c0e0203000001452068002c1c01030b03006030444800d003418060341c101600c0140c070000740305640350b407038501440000b034000a40d89980141d0914010006041c013084020800b05113510400d03182c0c40300c140a0328120844403c10041240350484000800c0c1107401c6240b644a00062403038418100d00002041c0100c946c0c0c1c54514240380030a075001c1c2200c140362600849100090143c4c4a034645070605040c801c101100e80d4008038a40000c45c100141c1d191044141c92103410b00304000d840a9a0350361944c0200200340c2c2c041600c50200382d4401a44080d03440c0c0c4107900404444031952110401ca8964024600c0c04034a007510071030034001c3d04100710048130711140030700c024900c0801021a0300000702081003260b0600100c60034600690301c6409425500a64012082c000c50400c44030081d034030a6440e00136000110350502c1d0360894038084030004503100000384418121115a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 387191609 1250 387190359 387190367
    0x1b0b040605030421050904050718030b0a0e011b0912030c0f0203010b03030f0c060105060a05030121020d080403061a10120e0601080d1211160303090b0f0a1406090403 73
    0xb40084e5903518615a190030b54140351403040405030030f1a42d0305600c50324408203120646101a01c80401e0245001c0c8018110074402d03030044c01c0700d410501c42c0c4120b80703506181d0742c000c14454495101950030400404010103400c05d002600d4030003544c8440102d1f5032000030060300303444c418000300003d480e44100750204001c00d9502c3d03907041c001000000c01076103450000e4a541d00046c00c0d40401c840100d000001c40105101440c01490181e07002446e04281083c02800d40c40305010f08007410100b00c02801c40c000021440000083c0d000e405049030660a0a002c1c4441c5c01501c03046408da4100000e810f0554100c40410080c1d400242c80b49075880c03440b410549220f042c01c1d581c103001641e41c2d0044143d0f40d008002c038038001e200c0d8030041c0854100f0148000c242d0100800c00d010500d0904030700d402840d064008036007036020001d40d100700c41505861300303c0103808103010203051801c4100a01c14010104015107005036640101000b15100844007844007440444419510004600014001c2402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 387192859 1250 387191609 387191611
    0x140f030c101a1306140303070203190f1208010e090109020d060528050906250e0604050d050709050702011404080d060510050309011109090411060c01181b0b04060503 73
    0x10611400002c031600d10007080074075038003161118a0680300d00d0204039980151050002601064000d1890010140c01081c0d680d41c003624a440d2010340150b1001c1480010b500c6e50191a0348440315190340c072801c15009103240c8081c01a404000c401c80c000c03030295003051282c080050703400340541040c0006038640000030503008248a001103002002440da10f4000f12441c0c2540541200010f25420400034041c0f80c040700500360507162081105420304002c880c10384030540c0d0110300d41002000015008243e02d40190b501c655000f44018049104101020406000b990240b517010003040e41c1c0d0300b40803826540a00c480b0304020710004041030200d5814001410700b034800034804902140d0300e40200b1028070055009800089010040c4490088280200c910a51090070440d00340320100000950a00d4050700040c29420788003030410054079500c0958101c1c0c207021008100202100c41200106124000c040b10302005002c0c07203485011001c0000802c0d50716500c0300c5d509060902c00c0a80d01988 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 387194109 1250 387192859 387192881
    0x20d1101020c07081014011a0901050405060d091202031306030509010b0d0f110a0e0a021c022b05010b03070c050703080d0c260c0706090b0103140f030c10 68
    0x5002c104521003001c003085402d00810741a8020b040070700550038807104550a44000062041c2150010020f561751a012298030b50080032203541e0700c1d074103000107803840c0c4241e601c100e030000c80104d003c103694441c0d03034450030449010b039452140c0b005886400720b860740309540d200d60700d0048032801402080c0c442d90026911131750130760001500c43c204d107000420a80c4d4054084400103418103c02d41000702c1c0c609003580d0f1079825540010010300f000951058186c000b4406084280e02043c0718802c3e005a0340c601140804100045690305e07200ca02c0031144098082e110501c01c10039003120407040180d0b00c1068122120906a5425500e411100301c400c0c11f10741d134080d5190302c650000480801c0c5080001c0c84024801d010006c0c254540d2140545030744680300716a211034841285160100303400740c540540c083d40c2e5081a56660006141c8200100304d611005490488000f0010040003800c00000c02c1101003101103480340e0040b90713003407582c030b105a40080c2035a03040343c80c00f0510081355400c4483c07146 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 387195359 1250 387194109 387194111
    0x30d090b0a0f03110c07031e12080619091a0909060f0702031b010506042a080a09050f06060f12190303020c060f060406062f0c09010e0402010e0a0303020d1101 70
    0x51040c0d0f1401e0341380d0401581c10101d9044400304100b007060703681e0000b107422014140311102c58281c3e01c42e15550f20f14460250305002d81c0c00e0028840380d039400101d40300a1884503031000d000f034594003254010500309000c00f1100e403218102448a01c2c0101c582032141a0180c0141120346c1c690f0780b0890341d03030b1002e0800029484140044100701903000804881c8a11178000040c1c10700d0120204000d0f1000c4406130440128040c41c0b038200d070781c1c900d0010855880ba900307001720a9101c226454004161841f0085d00354083e03100d1418907c00049001c501500c2d040326000d250355070440420401003541043d441c1c1d00d0b4015208031484c4101c01050251240c02818018100301100e4451800d11500b100c00c01d0408445208001461130f1510501004c0c10701072074056803e5844a0781284c00e5050700c0342c000105c07004850841c5030050100f1203c1c0e41003402400d504042e5a540d40340440740641603408a001c20b10b4030003418291306000d13a03c5000c4940544c0205040d0074502010f0314641003100c1d41882c19 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 387196609 1250 387195359 387195371
    0x150b0d09021305150607151e090309050405060f030a0f050c04050f061f050d020f04050307180e031602040b0f0916021c05042706060e030d090b0a0f03 66
    0x15075580d18240c0030300502c01c00040380510b4600d040348030745503090440c2c40c484c010920003d408203040070b442003000050060000f440140c0403080e021400c0d01c00341c0c10441c03d418000032400700765002040348100c400c02c2d03506018680f555003c0007400c1e0841f201003505581b0903411000420190007400481c03d0181094039a8021264003190580700c00b1a0004a003e00c0701c000d10185080c0801d10480047d2982680b0032403804c0ca0a0044c5103208640030040745580102e805a086640d0004440040800a044419040d607400000c480aa1401030301d2100314030705060300b450044044100d07100d00c11050a510300344295542080020050302e043e46400c004441c01c80f80c4180c886a80e403500030b4001d52110000c0180ea00002842c01c0f069003680084070001d46c61201c1c0036034111065905a07122000007000800c80d03003407409060710003440780d150745078100140000e0880c1c1102c807110004800740c00b07841407400b10071720585210f032013413280003100e0b441000383c0803103d0702c1081000e042c0c050500c5c02081c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 387197859 1250 387196609 387196613
    0x1e0507080313050f06040201050315010e04050f0709060c0f03030c0c0c0e150a08070e040f060c03020415030207051b12030c0d091e0e0a1b02010605040501050301150b0d09 75
    0x203a074100315144410011681c07640710901c8002c0010704e00d44000240204158903103a80020468080500852002c10315041e086110380c3c010018094850743c054002c00003898001d1150801c04000c0c1c8080d03002c00c01490000c143c80b880703004118441904900059940306083d601240144980070b910400c1000c412580d00000383c104241c03000504890458808034281005c0a007109042c00b500e080c4511201c500c00c000500300442c5410885441400441c0c0b241e440c1d0a01401e480d8141e80b0080030a45400d46000b6859019030152040d034990340d1040c105142c03000425812440f0f413040c085c180c0d41c0454103c88020322220130a901226000d844d40d4107110070783c6046451034015180400d6070b40c1091401402283c3d0101d0008002c1c185188060700d007100c3d5140c0060188400d010782c825405159000400c840c60075044803004c081c0340c0c10309100035054680002d00a081c1d80c0213143c400d42c140f4000040b185414062040684200c1c1c1c150302c12549003040e0b03103c039035000c0b038401a2301c5c40e210711440380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 387199109 1250 387197859 387197873
    0x4150b0d050c030105010909020307031104020c07030b0412090b1e040b04062a021011010902091603061a091207050a030305070c15080402060304020a08030d0e0c0d031e0507 76
    0xc19148200000d20050382c0c40c204040c25500305170442c541003480c1c00004409645c1c0001c039001125041103e402ca00441c80d00800e000c0c0c820850218035600c5041c4001040124000050340301d40d001c7d10260086801e54042201d2142c035520680703220203002d2040480309004103025600001052035036920b020796400e41c0c0c0303445810581c03264010841c3e407140a07226400348000801414403801c11400d59440e5940003e459150b25144802000078600074080c1101c400d602c0005140d8006003100d4007031501035940f0341c02c05281c003203071b000003070904200044510003a56076110b0640e6020b54181000d415409100350260900161802489107000000c1c50f510b40c10b50400c05940a540d070290780c0d4649040115041e003a585c0000034903c1a94626202140d106e00c0098206178110b840070b82d80d07142c82c0009101500603400c4903069000020302c3c6030800c01282c0c40601709900c02000c0c2d403602d904035003c000c075808003881d002c0c0124084101801302d4050000c1c00300c0d088802418841d0070904070b612880 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 387200359 1250 387199109 387199129
    0x1e020910050901120f1709030102030f0702010f0b10050a0504170604050d081308030a0e100507020106050f062a10090605010b0307090e060a320102070e04150b 70
    0x481040d1554405004500b815026107014206081c54071031048419a81d0100981010201a000c1ca85070100480740d408800304881031100d0050080d5224189146046030b002002e507812000f562921410414804143c0181100031380c0080c51040031101501c01038034251711040a00e002c0040030800800c03200b03060780032404054046401403440e481c0619215262505100300e10051080050802501040c0da41386440c80c19807240800c1c1d203903158440030001402d0700c0801e410f5680556201180000d04990215100712030543c002c0c00400d82c0e0f0000d01008aa90825468209c4010000d07011a07950041c040d1000d501c0b4007820411100c00f07408028104514401507900b015110300d0308006000c068041c29000d00755040d492071071414200b2000d09414881d101c2c03c503040080704c00241c019070707480d40c0c514020140201041052007041e590a61040c412075802c0f0080f05044035020aa94400141101aa4100c3d107940c18292141e13102ca40c2d004080c801402c00850f15040542e03040d40755200300d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 387201609 1250 387200359 387200371
    0x20a12020d0e070f0e19020d0911040f0c050702040b010c170909070314070f26011703072409080a021005070518060d060302090c04030c08010c09031e0209 68
    0x2d40c0b0340100c4925810110b20790700000383d06400c800c0034481c1c0101e0202a90b0807901802034078003948a41035208002c0e000d5410050246880c01042c4014024400100c110503641290304103e40300380001001d0403a110304507030100151003405500010704042d03004003012181410b0403441b03444195108402903488081c0c213440e07103c001c504032515080c40c42605800c000c660809101400c4628110f494450005042c03101704401313800318844003401501c1c0703002c107500e022500302a0115141d80138850084284078243c40103289181e101040c42c00481610506540001040443c44142c58800301581e0740b00c0c0e001c03428664480340d0400181031840142607940d101e40190640300f03040f00b000012030780021300e000203200b000c025070442c240408500140032041110710603240c4101d6aa007000030311039a04025001000c41c0309000822415001070801c8a10414403205810340700e82c882401c0c0c8883e00100d00105214a200740b00062402c10200c00c0081100212494400a60005180782070140ca079 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 387202859 1250 387201609 387201611
    0x20f10060f210f150b031b062803090302070503010b0603010506033c070f02030a050c0106050904060b03060a02040f03020d05030909040309051002030c0d051c0921080910020a12020d 80
    0x49050300c2c10380d0282021515044016002181c03510001c031000503000c0c4040c511a520005080c0c1d270080034105119904803c01305e4800814408040240007442e00c540c058026114420b00040e007480c0501446101d00c0c1d0192205013940d00e000e007802081d80001c3c1030b40c0700c1c4510300020204583c1041c81550480006140c6c04000410f8200f001d02e850a0007400360420030081ca50f180c488607800204481c009111458500d0f510312070740c44254010556900815440300104081c042031000c2904070804169088054070503a44808030030404a215a105864050b22040e0040002d46040105a01400e0042084e01d10303160707032100082e80c000001c41c0c00324007040e4046824031080c00c1c8003001c020301241900040d40340100f1010120703503071071000031300c1002c119000400c4105003032220f0405400146c0d80000307200e000580e150558580d0400c46083c210880b0303c60340600002d214884c07040c05442c002016000f0013618080e0300d0f000c0d502500c0b103c014081d81400440000b480351004061500301960 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 387204109 1250 387202859 387202883
    0x70801021603030f021e0919030c06031d0705061305090f04170406140a031404030206071805100c050c060c030301082b0c020a090903020f10060f210f 66
    0xd000307001c40c4e42d041100c3d15020b20500140f24000101c25002d031810001340716a03511446002c0000c2c82d10001c03841d40c0c400c803040401c400000c00954007240300540c0c07020b40301840307a8440c0601100b04072107401d148444a610140c0308004500384407004101d041c02d24040c3d42c61542e19040401e0540c0300950307179080100340f20000c12003823003101c55404d204004180e0155103441d142c5903000701060740342003400035100d10000e50101c8040c000d030720800e081c038481e41882e080c41c541070801a46584c0101e0b498070201d89285000d40000ea034170701001d016144000d080107011a0076050854100c030a8010465692003925142c0b025a50340202902c450400040199940d40c1051030f00703420052050008000710710100940f215003030040e05000a83c0e13215141841c0300d520140001070200041da0f100b0614649807119200038550301246000b1100300d0305040300c01400c000354200c2c0448050741b00f0040000300c0c200301445030755102c40d1209000b0902d403426440341400e40d2190b841203100c00b41e04840018500d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 387205359 1250 387204109 387204113
    0xe071e0f090506040b0f0d0b0909030703030614090c13090204140a0b03070816020102160b0105040b121e010608031207090b040302030d111c030e1002040305030406030e0708010216 79
    0x20790a0040d1205855150900386070217240d0701ca60040c508243c203010400f180d52025808691b03c64003922400601010a504102903001c0d142e5100200c2a0000f038101603010a444a1400c8d20800184000d4180ca5280c0d9420500140e990080d29102c03050320310348400041c0d81d16160000e04007604e40380c0c3c62243c4051000c02003003030411841c0e0014003085014000c00071000d400c02c0c4070f154041100807000001d4031820a080b40244148601c0100d4541c00c2c450303c00510940300001c0f8165441580c0070481d154441040080e2441d90911400b146d610018100c424032840c41070700c007030742203010f4004203015840f004803e0540d04040a07503100600701004000b40160702002d070000502160b4103851400e0300707540100303486282c1d0309110000c1c041020020030100d1810003007994144840294007000f055003c50043c05015840800080d52103042c14003000380c4024401c0b1021170350300800842c500351401c04140c0144c000d9860000d014040c100000884803030a0009001400d146c03401415860030034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 387206609 1250 387205359 387205367
    0x302030903160609320d0507060c060c1d060903010b0d1a0c070f020616080d0e0f010e100510180605090a02070b1b040801020a05030a0c0c0c0e071e0f 66
    0xd540820701028082c03180380085c0218543c48000804035901c81c85103024104003060540408940040582c071030384000141d0709a20428500750700d403041c80305004e800c2c6d81100031075450851600489201a000c00348a18914041c4010300c80726101500203e02121003000107181c803622400b05032013030400000403030300f129140201c041c0d001031010300791030810b0b1060303d42504d0185e10150086c00341d0000103c01189108003450850803540c41036010f41d84002450802d0081d040e01c611044e054855240c4280b203002060141d031a580c9072001c000d106004441041101404002d00461407007040911701140800d505215140491521540841e0f83d610717210600c60169001840f5180440c4148008800298074032a05034015030000c48280c85d01c030050051549612481d4802c80442d84005803511449030084d020b14420440040d081002403181a0705603800c40c1c5010006240b6084000c051004111403a54540c000501d49800351601800c110804441c0c096801200b0103d840320301259102e40c2c0c8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 387207859 1250 387206609 387206627
    0xc020a0602070308030a02071b120212071811090d0b18060705270307060309021306120311120721020d082202100309150204030b060d03020309031606 66
    0x10920041c041a85181c42d0b04c070260001030a003106003030300080c080e0180000d115000c403e000d02d4144041246130f03074030a0fa030140040b410040740201030f4090503000051001c6000000c5850385c055200d400d40302c6a155400070000d801c0760700c06006051148900c03a860700000715403c503209110011040c2084000c0640c41014417440c034000e90302103401c1203441d5900000361002c04a8404071980c01d80e45000c0d407000c40d0015054461b0709031003208000200c15074550005001d840c02507918000e2480c1040349101628101c3c004d40c840c14084283c1c01d80007030310540385940000901030644170302031450310814001d503000300c00c25a41030f03100744500c8017030340070314240d0318085101c0d8001080f0702c0000c0e02c00501103c0000f42042c06084203c40d2210050100b240c80720f01c220360003060b0854400c01018060028101c5400603103403548000256101e9608034821a01507075040480881d82e07540d08801c1001c0791580b50b20840c114001403100e40c6081d1800c00c0420100c3c203502c0000340c480d500748840180341c00c0c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 387209109 1250 387207859 387207869
    0x20703180905070f050d0e0604032609030405240c03030105040612020f12030909011d010510020a0b0415020c0a0b0a02070320010e0d0206190b0303090f0a150c020a 72
    0x124000603c02c0258010301404158211418055140c0345d10040e0300000701541c451901560251508000c101503110b40366403c0090420245001000c1080403d1716020080340c80c1901c5601c208008d010529010800b01c500815016a40300d5140002034909a02c0c1c1107527441d5402a4004001407002c0c1c9064040d035405004500d00c00c4081c1d80305030300003805541ca601d04c1180548904980200782c028188101e0381540c9000e400e4800c0c55035520005100c80c10a07260809044e410f4800101d0310345000c01d004c0310f076103c4990041000340d0443c2c60b210b12070075002c3d01c00c541c81c0d941c040701d40303036a0340b03450015102d07503c248000b50a02201500709204807600080c284455144100820b0000981164550402451910b0400615403800120900601207140103805620412144080c00c2c0d600103242842011800d24503101515504002e03030503119030615059241d0418850a001800e0800e41c006460000500d9a5011659116440d5002001044020001ea5282060400d41c1010090000204 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 387210359 1250 387209109 387209111
    0xa26071d06180f0405102c06070f14090a0b070209060603062b061404030e0a180203070c0b010902041706040506010e180607120c0906050405040c020708010207031809 73
    0x20512201d101500240400407084030f150100f020300c18100200c01c0700300c2d00420204030340714096868a110158210112043d4080b068940c3d81034200498010b0099101d03440f660f034070040545080e9010300c114401c080c9a08001e101201940d40c4020b442c00092452461803039407404280107124140c2c400900042c004c1b00308100348142a21042034114903410001440403e52042c001c2c2c00c6000c0c4088007020780402d0420403c1210b400f1258003141c0104e2194484000c0c887d00e0500b803210900061081d035043c5112424104071120054000390b9010b041ca01c4c00141094850780c0d180c00481003a0088040300381e02007020b104003490740e034103100c07111026001401d8518203555440d950f283d05000300444100c003c0301042e448402804c44801e0b4801000640c0e440d850603070801070514820700d21000e681030401c9038008104e4020b8048105456160386d5980c07505003003034144406001f84a40b41c001314070480200060000c000c0c405045150311a954180b0114040310001c8540245c64000c24070f03407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 387211609 1250 387210359 387210379
    0x30f12090714040e0c27010e0c0a1b0501060902090a09110409022101080c01080606030405070e07020a08040e011508070512041e03020604050106080c0a26071d06 71
    0x11100039200c04042c008850105000351061000d0b81041e0b030160039680c008264136221303c1c40d0042c6c022850021440d56020400c5681da954401050707801c10b03101035021080400203010341c03034400e070f010060804441d40200d800e444070b551941d0844185622007e034044c1e01150482c542d00d4a5a0310b28020308200c50300b40a11404604031201d036115034410345100355030001c1c08050082c504801020141c44180030754069694440042c4d4550300703a01240c0b40000c010600188462a041060704e0080b40c21500a10f02c0c1382c00d0a140c0c8901c0e52010303000600b50f01c01d8180007400140454010800740c01078410951040d49031282619800721f900c3c0307001d000c4c07291280408c00002e078401d080c0c1d0307641505044220704036191410151010410780c40c850002240c00d10b144000d242e00021518040c9101d18020001c2d160b45102094558801c3c000060740700c60013500030002d44801083c88484441700c02c00602c1141030080045c3e2038000b0580c4900d40c1002c40000000304815203003100e541c40b540031790b064a69 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 387212859 1250 387211609 387211619
    0x81201230306011403120a090509250f02011107110306011d0a0504031b080711040204061407110901080a060c0203090f010f0905131509020403021f02010e030f120907 73
    0x1c42c2014007500320890782d0081d0034440c2d954200a640c21a55102c0e844940c0e5400006000305848013501809000b030a082c404180c1071080c41c90100c40170105a07842a40308140c2083c00c0350346080d0b40c60000115902c81c5d803035049660050000309000f500c40c80704030298186083c00e040c2000310592044004001c0c00001d510801c01c1c5500c40f50340032603030032000174a40e0b86030710f030540b860070032450800460360a4185403020030019074001d140700c80c0581c100b100814080030402050344036038024900051404044181c0001802001d01812481000b100340242240f90100e050250241d00000240d40850441014800c2910404c401d03190340348042c0d40341004030004902c0b0403226441aa0403c6282d6070000c031164400c0080030003400c001094510f031506c40030080130282c03d0512070311001e01404c490000e071000d401d10850b0101ca80c06000c680186440098010031160440000d4055549446249034048010703c0103009032002200f4280d00c0d50401841d480360403038010001d0306503602c042403d000b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 387214109 1250 387212859 387212863
    0x20180d110d08220509062409150c0106031a1e09100e030a17061309170c0a060b010f09030803180a060c0e1005071e0812012303 56
    0x1050310036140e01c0403210180c541202e2911811069407540440c88414900c24440c50355000100c41c000c0f1042009512140100520600c10b04011061000f000c51141c86103001403000e0b0401c03002c0104545009a0740014084480c2e01100450040340d640d0301080c0100810940d4107001c110f0907803c8501d55281c241c4d41c1c00e0200250301003001c3d102c0103110004c0c585e00c0c010408100b201159000c20b101e42c0039074148031a0359400804280c4c01240d039404e1550389080d9205401c603c01e00004100c0c003000c014000c0c01000601107180240c40904021100712080750f02c5000410403410f038480107280b201d19608040c1e04883d04c41c0c14113410010121140850b040c0e11102c0d44058a0300174070099542c0c1ca810403520035000c6100a0044540501c4000781c00780140340d807118042e0a00c3e5222901c0c030388205400c01119400410310f044c0482c1040c40f80c000440c841d22072410341c02e810903481c4030034616180c480302c0c101c0d0005034188000046001c014002c480310411445003850840c1c0301403034078802000000e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 387215359 1250 387214109 387214133
    0x80f0112060908070210110d031a1504080303102102030d0f1803030e130e0604060c03020702090a05060301060603180311070f060507050105010501020d050f0d20180d 73
    0x10307181644540301d180c00e0245981c11141c00c2540109000e29a1090350000b8105081ea00d01a6080b406086d4100300340f10302a018404501c0c410790a0140d500ca0f02070300b00080d0300040101d00a26140074040405d00510400040d03003c0c00980408043c0c0500c1c080a5040e602c009240b801d01b03045000fa1a08011b880010700140103081c2410810402c1da03610004541641011485c41101040800d0010a06402c541c0400b90a032058070300890310301c0112000025215081104911a0301c640006808581194420980c640003481e025150520715000102c00c0202a511201c0160340c0e80140551403900b40b01e11001801c450806110b9000144d0b081d07401c0c110810800340c18006051001408034000380640805000c1507084c0000040e20b07540002c01d60f80003c001150340b503203802c0000c6010b6000042d10034007a50f4550325146480905c0f006001240c102a07c54880141c840c05c4128107c003a0025625440300003404c00c0c0e48500d103a00030b8002d031030fa1784100c0c0d50242c890b030301c140c0307000c80c0c401d4480c0c0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 387216609 1250 387215359 387215363
    0x807080d080a0b0d0507090605040f020a0804030813050d050301091409030a0c020f0d0302010b01020708120313060b030d1119080405150d051003020f031515061315080f0112 76
    0x43c208a00ca004a03488800f1210020918001c3d2807000c42c01005c0759000303e068400a5030304101e030001502200089110314105031001c03031340410004000034410384e03409034040d40c03e40c800881400d890380d5403071034071403801c0c03140d00070030700110062160081d10302c18000740d0750101c403040281c2d042a0540c42d8a83c0b160050820400211001c008107640314211080860000030741100350900250034024020016012020300500a18000103480c1c50b0010f0009a100c01c80f0001070b1440c1c81e5512407212074018010304464031525103140b010150740620020b4005805500c694100c02c4d40d446030141081c41501c103201c1422003040e411408100400c3c151400c0e80c42c19100c80c50050600f100503203640c0111000802c005042200f004403c010842c40300d402c492081d204001c800b4000c20400d038440f8010440482009031500010b0240d0301809000280c00701c01504483ca070025208c00c43c40006196003004040300020100000341a60110040e40c0c443c68103075101050b941446060b42000c0c45078000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 387217859 1250 387216609 387216611
    0x1d01020303150402030903040f08060403031103091005040212010c020a17180f0109030206220905011d06011b08041802070c030f020310021c0501080f10051b0a0203040807080d080a 79
    0x60310300d040800440d4007509c00130030340592050307030b0780341c040c2d541c0104071821000a4141203001d0350392450318066900804405014101030503a16408000903c802031041c1d9001180398000d1a4410080c4601c0c04480d486501500b900304407800c05108208000c12982141c801c00c018401141141454a016844088444050140071440102e07130400311500b010707500410004103000c0f903403207203031020020254002407051959600c1c030f41c60044030024480c101c519207081000c440000c40300030360a40e0000301410000c450701660000e4440307009454030304a45884002600744101002607a040603010400f02e429407030601940c1c3c2d89808502c40340f00060601c00740e030707024504641c1c003800628211b007514901151650b48200d84941d41c400104201008145054004106040081000701104c10702200805203c4038564103c070040c40c00800a000e000309503801c5c00b2103004903100030003828035294000c544440c00d00100e6030070801554040031156100041d100e082c16004810194840c0800c90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 387219109 1250 387217859 387217861
    0x1b06150303180126090304091104050a141801061d0409050a03121b0c02011115011e08030c0309191503020a18090507030b01080c07022205071d0102030315040203 71
    0x70484d46800c04500350180140c00c200030040c190100102800445590460601c004c503254500e204003489036001d01604458420000c1c81650240a044441c0302e0015042812a40c0c02c4083c1201010f000c1c2c0004d40028681c114820342440d012441c500e409030121001c105a1510b0b56600e6920300c480000107090105a00c4000d4000c240c80d8403280c04c141f12085040d0320540040c070000c24160010380220302007400c14181d0440b02200055503d0080c0f643c649421103642003891800512201480d00540703000c8203040410a03020902c042c1c506c10400c40021900c0f01010000c0060608111000d4202c0c914a03000410101d003210302600000715503401c0050f81d81940d01c0301207880280f2001c1650542414bc0ca00040504070356100e944035504903501008044003007401168005015158203501040c00d000d07040251400b07180381e50340c103071a84090fa03a4601c1c840d60080d094880448000d0301089804080102400c0d0703185040d0322001d006d10140d461460408a840c1c000304240711628091a4080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 387220359 1250 387219109 387219137
    0x402032a01480b0f0f0109051003200d0803060306010b0a0806100c080310060807020106060e0906010c0b09150a09051902060c07080c030c0d02060319021b061503031801 74
    0xe44140c0c000f50080030411103440c00e4100721804140940c4c1000103800400000240c001c8140300c0c040c0207981140000e0b815614584412040c14803090340c5071508801034601082030b6a6001a40503510712807843d56850303181220406040280590181241034400c1113881d0341182d2210180790701241c1200c0d58100b0176094903080300e06044058004011a03400424883c803040d070210700e034003110342c5a51a14401d1f503401c0c03000c9080c1d5a42c4d108604c00b02d00d140141050030f00d8207082542d40154189000308400c0c54940380c1c400036480c1916502c40c0c0f43c100009504641d2109078141d5805001d0520600903030007581d64990752006928189035900321a400c0c59001c40d80c824040760450f0b00b01c68111400203450340318030b0b0b03110949514968840c0c452030b0002800350600340002c1034000d030020240381c00c5964150b00e504040920345000901c10341c1c200050841054150914420290030b100203102030318045004050441c00300d010305100303500a001c004400e2958140c59060190207280508074403c0341c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 387221609 1250 387220359 387220487
    0x30f0501020d020d0e0610050f040509010b030a030f020c030309090f0a090602030702151e010605030c07080a120c08010308030a020a0507021008070f0903030e0103050402032a01 78
    0x800d01d100002e400001c01c2407000c0080d03005120000710841c142c60141e114200d0509000c0721511030207402034501c1104030441c0c03802d58001940316002e0000800c5c54038054000a0610750800c100320007050310b0300044e41d06c040d4100081012240c040d8000c41c94620000009104504010401e0720301c424440c0c001456200c10360421005158000d105540b42d090001e0041d450f135094245041c85c150b1000006208072519203c10f82d0414a005040ea0f1144d007408002c4034154801018103c140e02d080201030000fa50210003080ba07100107581d00225402d02060a006031403040e0301c890104500e403401032002c0703480e1000316a08119499001a81d80c845541d090b6440d0040740c0d00a90f0011200d0410b0401d107400c5020b40303104c0c40c0b5070b0b6640d0f4401151840b00b0b8803807600c00d02029000a011524200e0554080e0780030f95040703800201152046d405101c1981214100038a200c00f4644151003c41c8042d600400c8003c03600074032110400c42160303408030b0792103d1000f0f06083c0134202d07070024500036001c0178 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 387222859 1250 387221609 387221617
    0x60f0610030f090b06180411040c170c0301031101110c270903040e090d081605070609060c080709030b061009050d031e08090d120204080304060306090b0603040c030f050102 76
    0x10304041807000c001c55007089403044c0821901d00d4007a10108298a00e20981c107507142d489a0b40c1701c40c29401d0600f1902c18403008102c0c0c880c0210502c2175100d0407101c0c150400c600315109aa0800c080760340e17581185131050486940071103403810301009100e11030b10348001180035581c0c924151084031502c40b100c08801d045881e10301d1310900300e04401d4240140c030040030000300141d900c540700c10105502c032800d102d5a1010707808000310020f22540003007040c026805464403114039003442c1c028201101901e81e00110740c2c1402c2c2c11100599110303403141304180c00c400455031201041c100064114a561503e0b582e004c40244043e03c10b0049240071010580175583c002c3c05040051f1503609443e6444c41e01400716505100441480742411140301416881b50030502e104102003000b610900c000e013030f0250317029a4064240f0b41003a4080c4400f02d2061002c04c0a44010b100307035500424102d190610000c215441018140d019003010070030000400c0580e2805400c50740c2c8100440d0038942d10782081802806 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 387224109 1250 387222859 387222881
    0x10f120f0c0c0501270809041d0309210703170c070f291206010c051b19030305040b1e030c03060f0a1a0702060c011b11060f061003 58
    0x2191801c000811584000749018481c400c500030002c80044202000078000c45941a1904024040d007550000342410081c00d1983c03405000402c82001c40c1e00c005038504088450b100142e0720201b0031010524000c43d011000929207903005003150700040b800f5499070340d2804040e0210b9640048140c0c030a07510000c403103008845600b0785040320740307409401c0d00040e420702ca0000c1702c0f0b018414814202070358240c45220300001d240194608012480341c1c002412000340781030b05001c4ae461159000c52814450009480800f100c02090020050104285021040d483d0320003460744c03940600000c2c0d0040300311003c2da01c2c00120151504a0400b1b50980000c1c0b41580b1240900044148030301000942c014500509040707075041d250600700ca040c020311000c98031480485544444e05070140c07401d42001007040b0742c006403400e40740c0041c1d02a1503003960b940001c035034284d03142c5207030100c4803a601646100721940488003803c8941040b40c0c8802075642c028010903c50402d4251a0b5200343c001e50098080d10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 387225359 1250 387224109 387224111
    0x16061e0e0d0501090309060e1c02030a060906050702071205151008030f0316020307020306012102030a0b1e1501180305011a030c150d05041a0408030a1a010f120f 71
    0x110311490700c14042c20f1144d800b2000702e50024400b240d282c1c0100c042003840350b0b0290010141002e044846800150501c0c0b059030940688000030000c41c006002c0c01c2e02c0a4015100800d007401e082e1300c001d00d014031a41c0184181500440ca17000020340110302c0b08201b8107580041044c6491700b850501c4001e1180d80031800900c0300040052143c00c00d007024512130426503d146940680c019020783e00c034410020000c0d4507801c81303401071102d4a4048154184120b03018500c0b040d11089901091600740300f400d007075410121030010403030f01c0c20302c1040380911a40ba4038039454203810f00300148030f0312280308501d95050010140324642c0308c881042c2d45000071a040b80c021b0112620503c04e0200c41150700c6400e600a01410071041c659040090341014201d1703180383c0d01481e040182d10090003c03c1c01820485410b842103042c814800c58110384140158052107449070350b8280410b008007218101c0c0105881d0412640e840a59030781c004070740701503105030360800c0600851101a040c004001c3c044180c6145 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 387226609 1250 387225359 387225379
    0x40302010b0109351c05040509181b01020c040212100801050903090607020a0306111206040506181e070908011a10050c010603050a0f0516061e0e 64
    0x1055054010100d540c0c02a01c402c2c03009030700c4444880c0d100c1c80c00c502c650004100c4020650071120385812100b90a0340d07640c1603c1c41100c100c0c0d1080c1445100802d083c0025602150610052400c542e86540001c18980c10141001c0c40c3c900307140e240c4105d8014421070008080344100941d0080c0092030344248010700440d510303544000804030003942a00e000c605490340c02004200306405200311401f4a02c8000110305140d1840b0800019602c0701c50100d800c51010b4000200245c501c1c0034408150755402442512105155030310f1a6400c030051600344282c1c01e0909003d400e48800a0801c0303200c44607502203450b9666420f20300f00c02104c41e250a4a4403144030f08100c0d400b80c1c00043e010a42e52404000d011110b004800348030400d0b26407803410750060030b140c4120025070141000b4194603c4680020940310303a03d4880c203042c526a0b50040d10080c0404820704100501408581a41c910100d20740f0716803410a000145207003100e04140c0817110310541003010003805019051100d00c0e00404003000307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 387227859 1250 387226609 387226613
    0x503040c091506031b08150d08040801140703020405010f030c05190e1009210c0803041e0501050c06010302011d060d0e060f011202010c06141e06010c03051207051204 73
    0x102c1c9449400e0000f80342101d1070010306030610004c0799090079680c8441c074a4036000e00c0c981d04400d4000f0782640c044188600c1000040038600a0300c0100102e0000040003142e0504151411000a240307104061040109000c1d0b03a0b00800302a101e5030040c500025042c1c010740301600c0794800c0c40700d52400060803031002e00c030709075100c0c541303801400007a10b0381d85800c103d550080d90026000d0058a07160060040001c0d108203400c00d803090028044c6507502c003050b036112045403c542c801d411540e1702404507065441c41c81400001400288000c0c640140390050329a15030b5111001800300030704000903014050020204040007030f540040060502d55941d100a08002c01800328000c00c65183c01403c0c0002e444151582d9520704032000b0b58981400c6c15520303170044400c401400c00840b0581e1f80c40561034640404130b4022403103400c4115822001d079140f500d1491074140000c0c04c0301c1c104003600c5003010029501005551044c118020160607984a6a4080d20907000d400031051a4103407900030441 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 387229109 1250 387227859 387227891
    0xc040b091315140a0806131b060c0b0c0c19020102031e04050f06160b0703060e010e040b090708100902030309090415060e0106050702010509010201060f080d08090a050705010503040c09 81
    0x450703018a050301e070202c3c090410b01074007044610440c1195046440014682c2e00c2c0b034019046018494103405e86450310344800410007000980003600003a0030340541c501048030360384900760400340600b082d038201100150b586656112840c500a00d000340640d00c44110790003002510240d02d900400f66440090544018115410030702c40c40c2c0c810014840600c10034100041180c1401c03448a100c0e05010702c42e5141d219084801409d0f8078209965031b00005142c000c14050a4080c2c82c01ca07014107d1420203051040c402c4c00090654501500700107010401aa13001401d202c40d15000740d0040341c44449400028150701030000b046401004010401040003c000d81034800b518055804000d020b480b10f0031590481c0d400d005070404200200040d40c003642c0900c0191100450502c00440c0203929020305000702443c0742c0c403071070a540c404006d2008440d003009881e50300440d144014801c00a103902d410703130b403070140341318403814014000007040510021040b10400f81010314024000320340c030604212 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 387230215 1106 387229109 387229151
    0x1005071701170a2904060203060f090106080610090f06021c020714040e0316060b0112050f0705070c08011b0906080f0105040509010209030f0303041a0c040b0913 71
    0x14400c00f10065844d84260303c10100940c1f2410300390240103840600c00c140c24842c0c081c40c030062280650044103581c0c07110b070840d00100780b400030800907640a5120303080808c8814000c0d2021902c2c40d000aa1000090f1481c4003113031031030300f4000c0c0803070b214011360245e6440c24000007403092191405800c9080d1400c1d9801c02d4a1402d000141d403c440542401000c41c2d070340740c8400c074002031581c2101800c0e40f2401c03030f04014040c605d80200980140003004000c0d0f0184107012481d1014806100050405091240002c01651483c804007620b9442d40b40b01590018003007142c04507840d41304541143c011a00503441c42091303400c0c00c0400000d08401041c1d841290740c00e20407004241c0d402c0012880410403840074581d40d052a003448200b01e403990030864409054401801b01d1b08036504106c07805c231981122000d40743e5a1560006030301e882c1850219021509141d8411980e948001c210 = true := by decide +kernel

theorem cover : BRFrame.Cov 387050359 387230215 := by
  have h0 := BRFrame.cov_init 387050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 387050359 ≤ n) (h2 : n < 387230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
