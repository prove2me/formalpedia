-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0020
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:23:40.218903+00:00
-- url     : https://prove2.me/submissions/b9e233f3-1a12-4a02-954c-d84a7d447809

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 3417273 ≤ n < 3597130 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 3418523 1250 3417273 3417299
    0x30c040e030408012d150f120201080f0f040605060609030601080a1109040803010b070201030608060a0c110307080403020409020604050a0609060206010e07020d030b15130503010501080109080a0e0d0f0303050405010e010204 98
    0x4c00e100c4150340e40d050462103580076100a016003188448507c500d0b49039295110300280b02242203001a140314001443c0700302d04104980282c6000c0703c05801c0e038070f4079500d000107443d0007441e01d03420203014081aa42c2da9004c1040d14000d00b00e41024014607103240c103140c4504048444000d0150102d0340034400002d5042c42181c0c110703210407580c0c2e070700c81b0001d100403006041d0b00c0d4480d0140388071b8401070102212040e4000120142551640c00406190441080e1240500c02001e0030940c0c0c00d210070409400e00d41c008040306e602c0200403038900303501c56002030303401c030302640001000564201050104980400459000d0441000c000c0e44500d0802130080d0f58802d0092500201034580b0020320154a1741e120701081a015400b895854000c0020240e10540b600c0c0718552203503007044000681d2030410f00c1400d500da41c00c088068540342c110881540c255140403c01a004100003203a03d001c1100000c0071044c0a200f41d0f40031410341450300303206096940d250020600d07a44100400c108100c50035030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 3419773 1250 3418523 3418601
    0x9030d080402030d2102030a0e0f070b090d0606050904080304050f032506060803040b07021302030606090922060902010f0809030901030906060e0108070f06020601050604050f030c040e03040801 85
    0x54107421582c281e111039685d54803503029040d112400070041c4554200d903a007041082c9410031041b5207504500c8400a07503035825621510601c0b40d002c01072081e80341420181c00d8100f41c01014042140b542d640e0100c2e803203c204480c15145964013100b0b000421806008644842080c540250300f80003034131858014001488040081d09004c40c010f0408008842e0040f40051542e03405403600c41e41e407800c003950181c2c0010012445100250b07141d1069031414030969000d0711024000d00c4c20a9180e80074002a4070000d847e1625200c540c001920300206e10b510f00040f014820305010071040f2103440054504210303503c00c0c10511500004021075044008141c507842013003481d002c038421003a0b09000005018540047c1c480d040c0396800800c220744001661411200c540c464445007660f01c640898440380d0078003030640e000b50200810015850861841319031600020207480714202c4a40c000740880d141c55030317074214a40000ca000c1002c450284240340c0300d09401121622030300300300100e040d003402e4048 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 3421023 1250 3419773 3419777
    0x50901050904050f0714031203100501030b0303070506010b0706050c0702010807080a0204030f0503090102060c0c030306040f020d0213030b0702010606080406020d0b060307030603060501060c1e02010210020d0209030d080402030d 100
    0x1c000202440030401c1402e20701201074055880c1c49444001c1d24050a503103041050203032040301c4c200440f1420040c01c036032040030015030b140000c03414040110080c211806c2c603294588820301c1720380c000c00c80a1080074000c0881c0005c03d6560301c90361034010142d0301c005002120803030041c4550340c0940d8110001036805941d41c40c2207441651030400d458000c0c000d64001608409010f20000c080002c004010020304a0980880310b079a03848180d2109103104042294007244c00600c082580b03424a03801c001c0c03805114140240c14094030440100407a00000c1d13003c200b109000000b0010b004201e00e0241e049017452000303101c0541041000341803000c0c040e00c000c01c07a035400101c03104c41c20190342c0544105500140210b0303032402c04d40e41c0140900744a02040c0c41891404000180603402072400d2500c095011488211501c106a40c88107001d944000c1039040d80228504030204100d81d00c014001c0c90b900000c01a15400c0c14424503240640d071916030f00a001500d01407001503a1300050091241d1064 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 3422273 1250 3421023 3421039
    0x1e0a03030c090801020a05030105040e010203060a0b0a02030f03091b01050307020d05030414030301031514060a050103020a02010e03030c1209071a07050309030a15052802090d0c060315090605090105 87
    0x182408644038842c541c02440554400703e0306101e4140c0c480f00a50480e1003c56040c000308000b000064201e1000b03584540d417021039100b0801040d001c480251240b00440c1c01924240501c0324400070300c0b0f90044500d41010342101c000c0c0300d002100450b40c842409002e01e041c40c25454007003070103966240b80c040320105006001c0000390800c000c0e1030862407540050b41c181c3e5100e581d02e24040070307040131940442000c98204007200003802da200180703d104d40300003080030440920780f400540095101500f010110754a40118100c8420100015806082199419070350b030283c4031100e0034a1580500100c441d904258070410040402c3d180c00c01c0500f040c4003811340d0700c0d002450b01d03614502c14000300a4050041200c03410500c074160001d80800c51240d24148602d540f000c04003a0081c039011030122414030413602482d8594520b42c041d02c840040034001105170005900c03000700d001010351044000075100c0d8403070601c480d80b5408060027404149820f01c030850078400000c01030041401068011060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 3423523 1250 3422273 3422291
    0x10e03030f070302010213080a020609010f02010b090411031005010b07021c120c060c081b3403030e0a0305070807080409020705010b0f01020a0209010504090f080409020307021e0a0303 81
    0x1080c400c56034242036003180503a40314000d15010b4040c1d004107900001011080314001500340c03009c42c40c41c6407a83d0081c04207240c500500015101a095a20400c086641e5580f10645a0700c5d4200700078003c1d4060020080c1750f44c2400d0801d480e102100358500d807d58100b0004010a584c10403c0d0b4510640c101e0302c61042142120080c4501c8541e008060300c40c45840e40d0355000150001048220039015200501c19000c1198007950400d00c180c44a82c0000c000804031540c00c03143c2000b1740801c0c0d801d00d0341c2e16604200d014030150101000003001905c0008601001c04058141c852002c03040b20a0020f01445200781c0c5010702a0b014001c4090b04403580000c0c90000c0203c82e00450b4042c0941d108115115600e90034058001d100030541c441c0604000300250301e0315800000c400810036402884e05407203a080c0010700000e81748203001200c0900c0511201c00000383d002020f131000d480c000030010303141c1c074210800a150801e181c0f52070b41e14003601c1b1040e0840960100b204501d094060401140441c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 3424773 1250 3423523 3423529
    0x3010207050304060804020a090203040b0414030405150d0605010c050303010608091c05070605060301050c0d020702040f0504050a0302010606091208090a0807090207020a09051e0c07080703080108060a0606080105010e 95
    0x106a240c0140315000000e00803035415040f5000c1030244d4000e40d0309403002d90310340e034001040784020703140502880e0769031001a00044001140944900d00b210603a410640e481c0003080200c5103000300801194408103081505451070300c10100100001d185c07a926019041c1c4038151244818003514003003100140c00228180c2040112190381c0980c00c4000701100d080390001015608206811a41d81d414200400c8117490140a147d01480f92071400d00c1c60400000c4c2003000940c8160000c9800944640300315032402c00300e1103103a22a0f070291303015002e05101460000c1c2180c120741c024905200c12402c051120107269591a402c007a44200b400d503807058613800041c41005158000c1032103105128001c100d01c00b0a03005444854404d480d05050b80b52901040c6003039030021142100c0045688204003c0c5079400d104040e001400c260440707140404588031088a0b910030701e0143c02003002c0344010085004104143d690140d4190710402585042c104020301c02d03507061040d1410450a48244400e13a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 3426023 1250 3424773 3424777
    0x30b070c0602040f06050d0c030e07050d060b03030310030b01120f0605060103090b0124090503030a0305060a0e0a05160201050403090312050418050106080903040b070201030f0f0203090c03010b1e0906030102 91
    0x3c1c0759407204135281d649a0003069a48480c10b422601402e0080d03d00c4980d000f4065842c45000480242030880d0501d014001d030100051015150b41d0b840300320710300c020344040c0011406040340b062412409800c5007068400c040c410b03481808480005070b44500810390f01112007417980e82c010741c0032a40343c941e280100c0c094034201901030607860500700001010300e581c544100c0d800c0281480356141586207802541c59400510501d0f406420402c0140003c0c1d1003640705541c8100c4c001c0003144203a880b407480754030814045603080b501c569140e0511802640c4100386c048045000d2009100510f0242d400030104415444000d0900390706003141901c15002d101510054842d50244000740c51907a070040c406003d081c82502c01082c2c160001c5441c00c02d001c03040302e0580e440700e10300c3c615280c0640d004400400c0c0c02c4003400500e659801d0b100a1044a07400214000d128410080078401c01100400d400c442c4580103880c880c0444e44050914410201c07544410001c0444001c0440d903240c0c400701e0f000e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 3427273 1250 3426023 3426029
    0x402090a05040e0a060c0306060503060405090708120909010b090619110d02061503030a02060c0307030207020402070b090705010e0a06030207050a05070303080403020601080d141804021801030b04020301030b070c060204 96
    0x150408590301c0e0700700360000c0c4e6a540340c0d00400c02030041c000405400c0c2c1c06c80e40316016400004404000090f44c9040c03e0304081e402c02540c0044412031961681100d061070300364030a500c0510300010f4031100c91f180446983e40034001e000082d52400b80248009102c41c41010340e07240d00f01090055012110340210030b4454403000d030200796145140314281c02500c5850440d60000c1c24050f001e00d0040a00303001040d1070840000b90003e14190316401d80b18541500000d0014040503001c01410005840707a001070b020132403265034607140d10f09100b51400e040c6030345600202d040112180d030910b401e548001c0501e08844c10341c02d0040c0c3c3d5542500b030082c00c0c401e40c040b018100d40318045000040607448021140704d68065801d441040e601c900a82d134071807443c6c3c0c85460000d200310201144134000c9074000c0414106142c01c07048d08020b030401060680c2c0040400451043c542611500c0d41d50701400b504c505210112801c524541c11075803594082000030308810100140000207104003c410381c111006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 3428523 1250 3427273 3427279
    0x405010c03021f0204050301110702030c09090c15030106020606040b21010213080606010f0201140403110a05060a0605030c030106030203030409021303060207210c020907050c0102130e010f0501020706020a020402090a05 96
    0x1490383c141d0010b01c00b0f0b501510030b40e4007961824004c0e9901681c104140c40d0001d42c0100a0f25041d07a0300d2040000711100075004800301e000e83c5401c0c81203640d6031032000024110b89a200d0b6207d614214000c3c0c100703100101854007441c01c0020b01071007a0b4031000c1907660118000c0700b0340018881c0f0700202d030080c02844496001f400e00000086800f850000c3c0c9223210305401d9941c001c903100140030403800d035425100201c9030340c4240000300300024001ca08a001c10158181203a160b800c1a840c0c6500c0c0003815180d4000d0242d54020a124508040c4600003140c007041c1c2c001e0008a2455003c259a13224074031490ac680780d40840d40c0c20021006291450003950045d4003507450311480c0c105240e00c03100104201d010840c0382060300390028010009102c41a400500075100b82d0384020082d40e9a070700954400405550800110b0007001e800b0042c2405006c02c0d0745406115030400e003014003500e02503000103065602c45c0710304000c0d03198006020449140d05032809626917407600003141007000c0c25040154 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 3429773 1250 3428523 3428563
    0x120b040501080102040e0903040b03010311010c0203011d070b04030b0a0b0307080a0303050f01062a05011104090902090105010519050d020f0c010b01030b0405060307060309140d12050703110405010c0302 89
    0x682c0c03141500580252000b007000410a5150a000142d49200d10f1103601c0c595081440100080f80740c0d280e000600c2001814844800c62613640042c1c00c46540c0d042002c0601680c0171704919407042000024081c09642084919040c10758449640552008018208060f21042010065203050042000070031017001240c1d4102140d190180180000702c6042c000358100d00c0c00007070038910403800354000e000b1005140010702541203d010500f0040d00c0300740c074207640f214a00d800d0740c4114401440208201840040c2d0140c41d481001005001030340181e040020500c50b141000585000941103560241416070340d80ca460b2100801a001c0ca200d10109542c02203428142c07200190810486075609a0f42007007801c1c0c0e510304010480305d090b41c2107509648116414000e0f140258800c16115006508481c1007107080e14a0f145012000e014020004055000301c4080382c4803405840d800c81c031107007001d1002448030303115004d4030f0183d40308241c100078021150740c080c0b60003400050084850f14034a21303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 3431023 1250 3429773 3429779
    0xf0a0305120301150801050d030302070201021501080f06160503180a0501060b0c0d0309030207060c0609050a06020702030607030e060f04022718030c03041208130303081e04050d120b040501 83
    0x721103030002d105071107074003207180e5101c91228440da10315410b03030f2001000d444d103000064504900075001818200d0640c8a0007004142403986600c0c0d4900900d444030017065282d526412850600801411002c080d000940040306116080b40640e980007422103203614480d0b484128140c41c00180c80d030044c1c029403034035a0209440e03411000401e041950ba00484501003034503d01101140c00100c00580141c21220042c000184120030540b4040e000380c10214442c0886c0c0c49080c141100f1510442e05c840d8001050400c5007428030000ea4008400d09042010402ca01d204545034400148101c105001c00d06c005811980c8294030180c1c00000b07510301c40200400118800c034854416104050080040015681813900c00021592a140309001950920b03152085440441808480494030000c0c00d1204e405021605441c1c20000c6009075a19102c2d403c0c1140c0030350030310248000003510b0790202e83c200008110000b6480040802901c0c1080b0402d451090000050001c0600320b640070741810000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 3432273 1250 3431023 3431053
    0x91a03040201030b030a0f060c050904020c010203010e06060301030f0f0f06050708010e010b04030804050f0a0302180604110a0807080601020304050307030305030a050c0c0a03050f0d0903080405010b040c020a020f0a0305 96
    0x61881240700381c07410003011203000c0030159152418a0028030303011f401081400042c9181d00f000000807681c5c104203042044002c0000d050f6005a06181c105130740c084010440103170450b44507500410203480d01ca1071541940c885850072858900050001d44c80360740340b541080051001c62014035041442000300e030820413801440c000080c40b520402041110010034901950340444003281e0b07020504514142c0707448144283c0d045205003842d4044a240c10000150311030110204605100c12051584c515103401040112000040c8202005900703010981039903410000701908000f950500c454039a40d270000407440d40c881d94001507010300420000004140c0c200c009540201001c500c00c0c0069940d10000401a0090840b002c4080e84045003e001185c0a82c0081110720010190320b841c0126000c02d5a064038070914045000031143c2c8200420300a007807007482141c20084409004264039910025551488000040d02c070b0451003a8103d00c5a81c4c46c20180015a404826a49501081030f50 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 3433523 1250 3432273 3432277
    0x30405030a030c0302090102031213020901080303070305090a0803010902090a080706020d0e04050402010e010c08040306050c0415020105151201090b040302030a1d03120307020309030601032102010513080307091a 93
    0x2001c0880e00703020025401034028001c0d01c01104040c0d00a50a1101c440803117501c040014280c00303001820410440003580f6440101030182c0102c0004590701d082c8a00020200c60005001d02001c1c1c0000e081900021282d504490468070201009a1141c0c042d400003050102d86900200091243c114001412500441c2c40d817081110b64035012420020403042c00260354040781c0003400204006181d40c3d01d90701808107078045500500c1c0c12400c0ca52259100340c00c5480aa0f003001260002203401c10810f050010700c003ea11116200a00c1641045a0b068008072040d0030075a200f20f5050110b550146030943c00005a2500408100081e080030b050294495000b02240000a13074090301011400b142c1c003009014482c0041c000308054200300182c075005801c080c00000071808200200e964a54080010130301a50041c903840c444a60350703071200d1010700b000f0b107280030959051800f0486aa060802c0304200c0c2908035151655079901c81000329107062031900450010400044c1c0f40d03500d4011080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 3434773 1250 3433523 3433537
    0x60222030b060307050a05090a0203070c0c030b2e09020c03090301020409060302041103010803040b0307050c0d020607030501090605030705062203030c110d020f0d020f0307080f10090206041208070803040503 91
    0x284e515580e224014040c0c0d115076401516004043d1a01040445900e60300443c3d000c11a40b500f08000380c11aa9848885801c80d40140c030460540c0e424888004c1200e0038408443c400b010416006616060309010206002d109072981c050340418603c0380b0711814422174404a074014001c668460711003a0f0000186054002a4000d5180c46d01300b031500225102128142c8007107800030343c04d2502c2d040300300031030360b10061440007008014441c0b15015502040203611110294000e4400d6140c00b110080c200c0302c050b44440c40f11400c18030f080006031400300b0000c0544e1415520b07180e40d82c10048a101d0400843c103044030342d981d1564000018154040b4402003403600c00c404858280d1804410090040e090300d501035407001001401300703071074039101034000501d91003d4010020180b2290000b400d00c005030340411301942100c0f1060501a0081c80308842007040040b0412000b6603c1c0c0124005005500a45040003800f00c400300900c44800107423201d50703900a150941c1c91070b10f494016100e0f00414 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 3436023 1250 3434773 3434779
    0x1e0908060108030f041802090405010306020d0b030705010e060d0204080613050c03030703080a0902040b0301021b060603060708040f05010f020403060c0e01020615041518022502010c060222030b06 86
    0x280c004200340e5000b0045039000c05070b02c00c12600b030500701900120f005580d441c43c000758543c200305441c11915140070340d80c002c501071140182c07603080845c80a41600e049000c4035101e5004014140080d0b170700051a580c07200002d549550300c50b0300403d0500003d10640d000100e241c071407501086000f95100200c8419180301e68159049005c80e002810b40c0c174002c069000380820001400241c0100182d4084203507140010400318508080002180c00c99000448400e201c80f44040ca0215102081003a640c01000aa000346014070b014031004014203c081c200400e256084a04401408000d4109001d102d0f500350007155202d680f403901d20003d11118100700c01181c40b01d203400c3c10340c2d8004500584100803414044030410144802c0200800300809403802c050141710022490505000442d0041070070f840300160b0f240b10400c80402c04000000c51807810401e01020000141d90081c40d1405c0c0d50380c0b21501686490000784001920303c8195844031015450030030000a0000264034980190300035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 3437273 1250 3436023 3436033
    0x7090b011202070803010b030702010b0409030503101403030f030c040806090703060c02010507020a12110303010e0f0105060a0c03030507030e03030702010f0608030403020d0809040209090108030702010201050a0b090403030b011e0908 102
    0x11401003090f07004468024004040500041001d0b100e04030046074070180502c000103a50b140000020201d37540b802040d0000f070000700410540040002c4c0000c003900c0c00344030500c2c44c1140c07136001070780d42c0c8500904004507000105c08129200707010415180908596001d0320101e10b08045c0860750764409200a5445a0a00303101741e079a0350040c441c40780598a258041c0c8001f03415525039403040000040c4400c00c10001c0ea2032030341310751000e10144d0b010b002c0007400d00806013401d000e41544d030700d07068200b141b10f54010400e001d10300e80c102c0300c4540a40d0740342c02d000c82c46075100d04040d0010021000440700c0740c000041007021165066010f00e144c00c401d000100000c0d5201c0112554a002d140002034004521040880c045200400600403c010040c0098a4a600c600100d00c813224280c0c001200e5510100d508011981c0a005d6150b000b9001c450030030950400d1000210b16030000380000d0300303046d40c0b0142c64505034840c520f04c9406201402200c403070040815001844490b0078070450300c0c58010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 3438523 1250 3437273 3437297
    0x506150105031509060a0b0406050702120d020307140304030f060209030f0609030901030905031603020f0607080408040b070614090c01020105010f0501020303010b0a030f090b0a0c090806010b07030309020307090b01 94
    0x49042d01d0041d2403c4008a0840c406001440451400641003d60140c406000041e000c20341c1401440a00021755905884118600c14400101c0450440845030341040c00f94410555002090b9032101e900304c220000091082d04505045105540000c0d00c1c3c9240d030080c44007400140d40003000140780580131a03080c100c0ba20219512100190782c1034aa84d0410000c0c0750319584260009000140070b002903900c0d200d4040c06e41e461107030f10410200c02581068420704c50b00d21003481140e81c00007203814040900d14160341c07a42e200740b04c0c07030103034004090000c0350602c1402100e60001001c80740e00c420310242801d100d40c80c10303910307400450014010360034100003050500c000c140f520101e510607001035040d83d0130940800c00c1a00459800c50405507118003400c5030100c40d0003031245560107600703421240d00b00140400305942000951000b8030161031420803142600041701d50440e070191040030349440c4280f03000c41c041e01440b50084c2d0b142c442d1200202e8076400583c4215040513090300d40080d1440f0f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 3439773 1250 3438523 3438527
    0xa06030b0a11190201060503060103030206060907020303060105041a090a06050309071202030c0105030417040605030103140309030c040e1905010b2706011b06090308070201050109090b010302040b01051605061501 93
    0x350303442403403080c10b00f030160518601c05002400301d000c8142c0000b185558495020900d880800d038401c5d40107911040a0100a080080f0301541281071032001e1440c1d46050380010b00503108520074075006c01881409500442402004c0d240c9003400100006640c5a0740e22000748107404c25120102c0900507000c002500c40101a142000c0580c0a00a40050848440191041d40000780b00381c50100541c2d4500c2d02e8060281c00070405810680c8510780c880d4110704000c1910841c2504040650703204006003400e96400044207401004111000300c2c3c180c0100760102d04040b0400c000301080320721241d04808001041d0030010440e24180ca06c1e888117804001700c80340c41c480d0b60100da03c4441400022640b15403040c1c80f164560082d8404a0030050101e07a600b0017100e0001c00150001703002d6400780070354282c3c20f006540c01460f4000303050090030742e203031125030340d1a80610009101e40d90715042c034000c69000c1c50a4403880000c0862a8803c2c07001800d1a50300d500d000c592500b076440380d03540040306545c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 3441023 1250 3439773 3439781
    0x602010b010c0b0a02070210020d020106050a06121a120a120306030b04060504030203070b1f0503070b040b0c0708010e0a030e0a0b07030804020f04020c010b0906061908040303060803030a06030b0a 86
    0x1001650740303141031005501c07501800729000e400c06441035000c00086e00075894820210080140d558024079080c02c0c40c2e02c0003801c48501c1e800c903611480b80c0b60790410040d64070052001c0d5190f61040c00194001095041d101180e0100040c6a0030001101d00704261020100b01c8141c040d0150764289a0452400c03011001c2795660300000b00020501c80101c0c011590b945e000e0381c1d00c54071a00480346480d409448229850b002144d100c0d691040800e092903005040760f01e900024030082c0c0061452909103000e0358124001d1340940030450074045080040d485c0e0410071840103100050013003140205a081e60745d25403420200c1035020448500203009581045e1045ca011140d410081c1030800403650740403540700c14007800607a4402e2000007125010741c0c441c40141a00300c680c1000140119411047c8005524020259032150006018078058807511281c0d0302c09902c007901c1c24100b06c0d980c600e01a802003107103800100c20740c40040100688081a5031003070302900d0040c0d40d103081d80c1c4da4468000d0262 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 3442273 1250 3441023 3441041
    0x201030f0c0219030e0306040b0405010f0e060a02130b04030302010203010806070e060904020306010c17090109080a02090403030c1b060501090b0d050c09060103021b010c0f08040b04030804030908060901050709060201 95
    0x10f034052010070301036807180103c485901e0311918183e1410039610001038070b041020340c0c5c103a80d41d42c992420f11080100902c00c510450308492030512260200940b07690301d0702c038000e00614150b40c00242004115021342c1030800038184028904c1e4440b80c0ba810024000d400900074007015208120110304e1542c000c40042c5c40c0400c0042080d49000251814000a50400b5000d20b040c820360092120010349198010300c040d00e500d0001a446440034400144030301003d40c48100300750803d01d591000740c0c5600380200e07885505803e001c034000000d42011550504a0f48000301d491a40030300c001d041100e2600120304961400c00b0a03c200b0820900300200021b0411340140385600c0401881120700f0041e64250703000805040040c2000f01c0704a403001c3d41e62130b04108400c103035910088000007940082400d05299598a40488540341c203070b5800e480b4880c09403001c0c050200c2000020f00301442140c800000c2d0001d10255849820030801050103403406407003d1003c28018180031842c2072051042800e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 3443523 1250 3442273 3442277
    0x9060c020f06010302041d01020c01150b04050105250203030a0e0103060b03070206070806040f020d020408070e0405070303030209041104120210050a02070e060301110f2203020108010e0702070f0b070201030f0c 92
    0x320f6440e5a0030040284894030103000c01d003201c03d490408090080c406403420400e0040041495007143d4030303880c894030a41c0c00c04045d400080c801401940d03480780c25184696240300d411400c41a60750340401d40c208000a00035494440024500e209a6006200c0480031400380c8091110300c1d118010b061107030004681c1440183c1c05840003400f501d110f4000e058000001a00003e00400703420300c008283da102e0000610036030b4001804200c0703c4410070500005007000084241c4031b081a9036825181c0c10b03c8d1101a08043e00861280080d1350340b0344c0501d8002602070035481e40c59030740710850101e6075401801a031007550241d50b0f00901d20b01510480784601e4260740500810b90800c2e0851000d007002500035500b640d41c81da0000c8031140d04900410f019846c400d42c098403080d145041802014560300c003000ca0078441041000143d8108a800e415202082c1410009640c0c1d084124604451503000d40c0c1c80700b0180e00e0004204074034034000c01059000380d0f001d109414059011340c0c01c3e55072001c41c0c080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 3444773 1250 3443523 3443533
    0x20403020603070c020d140307030806060a0504030b07030209091003060c030515040905030405120313060c02010c1203020702090103080301060e01020304030f03050703020f01051015020c030703021201060509090109060c020f 98
    0x541a10500c4102c0c044c520040001214640c282c960b068000c03980008448690701c0005d040c000d040d0444089a4070100407208585040240107000785a40124030000300f01c40c0124000c0780605000e030701914035010024154520f10300d0002003080c1f43d0104c0384001d581e0f4519081c0180b2645129015482c8543c0582c100b030b254a10015081c84000d001d20141034910b408103010105060755120660002d0b410300c030004603100c0d1301d05100f1000031303c155808901400000341a03240140d03000741c400705811760000c4568000100b40e0405030061320920a000354405011800402041720400185050324810741d10300010610b14401681d882c030880c08083d26104d01000f0100000b4415030052108038800d00c1039a0010303541e16401c60940300d003030300d140c1c00c0c48400d01414400c0c450100e0000050800501c0104107a21103900400d895141c20300000e07000b0300c1d4110a12121501c01d411840c01414060720289007031500c0c500e01e900030100700904541c0c40e8100810381a460344001580c001c080d182c080904 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 3446023 1250 3444773 3444781
    0x80a1503020f120a050106030201110a0f06020306010905030f0a060c090302060706020f090a080105010303080604140601030b04021b0102070c05090708011502100608210301080709020d06050301050103080d0c03020403020603 98
    0x110140005000b01544014620640780000c1010300c1200ba901d8420400881d03d00e06510024042807100700400560341c1c44400c0d4138010940c10310140012503080031005980707072205001250b00c041c0c560071580e0144148601c1c100c01050000b451500c0a000300d10400a07080c207200200c90380389152001130750005c410701452000c91190303801011145c0e0900302c4a40341801c0703400030441da88526840107030f0b940d544000401c20b0603003060200340d01c0306c01141c00b00a10f412504a00141030005230015040580c0c505884a40b500e41e94100d43d441c0c1501c51001500c2809c0c1c40210b4042d41c40b001080360000144200058070317050054415014010a03212042160309102605011200b014482c80851244503601c1e45840b4003449640d002e04109009040003031041c402604a4010400c80d0380c0c0e070a101003004024092021450780150360001c1c2015944038079441e4103801400301504040d031b16520b04000042080b41a900403e01c0c080145414008525102421340c01c03405076104c06900030174204009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 3447273 1250 3446023 3446029
    0x905030c040f0207060920041407030e0c03011a04060b0f070305070c0f0e04050606010c0308010519150818060702070306021b01050a0507020c031f0e030d110a080a150302 75
    0x180380103402c0c80b80010b082c85074680b0b41e5801e440f01c1d20b0003a5100e03110442504c41ca20300740c190f034415120341a01d090181c0c9801403a00500108003d1141c010140d84540c1c0002d201e01c00d0202d01c80c8500c0c002c3c0280408810b0f911105149180d021404c0d11807841c060002130008209010b40f1381102040000b00d0a18006031400d40e400e13403002a0417500100701e0040400c41108408800d80541100c100007c080e280074500a0301c0e12070301500b03d40c107114444d010040001e910280c003a054900a03a0500c1990648020368600502c40740c0000e041d010190b103e44005070361010b081c80c4100561042c1103c1400e203c0c0006407583c500740c96010058210b400e0610101d5481c0d00201101c004010002d01c0980032400d81900719581a90803100352500d450620610550420207200030181c124060001802e03c032003200080911742d0f00d0700051584a070694018541e0910507100004c9000e0014041010752202562507075201100c0324000c503100d4000704c0d8042d4407034440c180701c03400c1801200d04035070705640030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 3448523 1250 3447273 3447281
    0x604080a05160507150806090c090d050304081b09040312020304030912050d0306090606020613050c030d0509040c050405030a020f030f01060e01090c02010905060411030a0c060f020c010905030c04 86
    0x340c0092240c108a100d40b650003000c000d40080e4001d50281c48064188136019451038117482d80c11041003441001e00a890355509400c41d0002c4041d607402e5590100c2e0008101c1e01e808941001d03050b4000490006008a40801c0c1c045100c0c0c500d88a0f030607410710342000c003e1b000360b050720301500180c190300c03071400c031092a80d00464010740642070000e13105035a410100504462500c04441680040d00c0d02c5c070000f601801610041e1002e100180071460820200941d41d0f00000c12822044070403002003014000180009011103802509880c5003102c1d504c400b50080e848049454080e62820340c02d60441c3d8131680030350701640e100602400110101d9000c1080103102802810390501030800318042303c1000744948030050904602d0b0303442c690b151114050444071207030f16400a42e410b00c881c050000e4070215240d54000e510410801c1c42030f540a001ca441d044d100e6070003c0503000c40480110360b094102482507252945a822a440583c18000450784410036228071601039010301c10b0f00c4424039007500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 3449773 1250 3448523 3448537
    0x61d07030504080f0304050309030708190201030f0204050406030803040308060301020403110d051606030f0b030c090612030904020f0705190302060c0c12030106030204030b0106080106050306040f0905060403020705040c0c0203060408 102
    0x40900d0134021100309100d030940c03003035400302c90715480082c5803e8182800d02c000c0d0020515030010701700c803000f003807c403000d07400001000030304040d51211180e44071192035054802904010f0002c01080791640342c05000759005480507004160207900141040c50305000b10f4080d240d00003650010369046805000c41d400460000701d4103402003130074041c2364042d04842c500003024a680c0c0411218038000030b40088a042608040c020341141602441d9900c0d003060440d00102e040c0e400440a03289407000a0a40c090400416845170001a04d034600d04140005070001c0c60140041d207407400c009125141c0f0615004000401513080a0700003802d480c000009020407244641c1512100320b4442001c1090754000d070810004650301280900a00004410b01130140507642840c0ca043e50510002406900000300030302c0c4101e844840b245a681c1041e084000901d0303101c801c5509500702858080c0d00e944c0540a82030040d89440380c011541031180c02481c0350240c002d809008a0380320750f01d031800f40e40d00c016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 3451023 1250 3449773 3449783
    0xa030609060b03060709060f03060e010e06060d05040302060103030914030705090a02070c0f0801110a12020a0309080a09050301050603010b09040b0403090506030106030203040308060f010f030b0301060902040f0306061d07030504 100
    0x240e201c00161010304ca4241700d5409951030811841c01d001c405040c0c2e03184804000d04251600308240410038010300a0f905450b03a4080841c00c0707640d41d0001610030310540c400c40c4005408c081c1072000f09a000240ca505881c030030f885464001d074903000051071840c020110710381d1503401031500f04502c0c14040070305a00200c0304c0d900545422030584071440f086002d640600c1000000c55401c010642c0c1c04e00c40c021400c0d5560050782d00c2d110319428000c1200c25803440e418403807a07000031880c1c4164000d81c002d1904d00e0340030812a0300e900c100311000c1c0c111749440c80f0b00c5010f5401c05000507a90318062052240c0d03840014443c8405032140c1e1602c4980c0e0400620840c2030048105012682e1350300c0002540c0200b955580140e503e01c2c052400408840700940780e24000c80703a04120b4070150f0303000550200c5501302440e000130a00c1c04000040c3c0500800c1c0d012040ca24800500402d072203030400031740c01c1682c1c02100c00b0f01c91203581b40513030000f10500030800c901088542001c0b40c0303200e21903003019030058051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 3452273 1250 3451023 3451031
    0x90d030e0a021005040b0406050c0c12120a03060f0b0c010c02010c02120c01060f120606051e090a0609020307020c01020c060a140c070803030c040305150c1c060902070605060117060a03060906 84
    0x6d0804100c0c030342c001d4004c680450300c0410b10702c42a403000c000941104c0b405445001220380140d00c51640c4c1ca2115050b400c4008010800c1a00903220f0f40c4a0b8005000722205070b4a07040d5242e54170140369014801200f801d50804a5041d1081d005001d030701024407043d030003000c0e10354151040c0581c640044448051654980704009040c1c8a02203441024001c0e03120044000e01d11841d20744100d800e40d5002030f0280d80038245c82c13040c00364a10b080708941032064600301407666901603000e0003801d40b0380040009500c0841800041540042e000c98003003804e0302100d5010b80d84400f005141c0c0a03894001000556030028176641703c41702400b030070840c810b4500300c41120340c0785c003001411900121034000c61040040341c1081484000c00c20440350321010302d10780c0f80606003210300348403034440c00c011141d048404921040001480d98000d000030705000c80d046481d95800d26204010342001e64000f400110300800071000410080c0b0030030b0003030000424108030302d455541c410001d442803100aa07042955 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 3453523 1250 3452273 3452279
    0xc0204240e15030c0402030901020c0609030d110909011403030d02070303090b06010c030806010e030a05061905060604080703030c11091609150504031713030605090d030e0a02100504 80
    0x406103203150300c11103510809100a04090700e03440790040040c1114002c07008080340418a40f404203081008803025035015940c3e940e40000140644a0380618485074402c00c4100441c081c0080040d00e54248984018000400d0881c962001ca004c4c002c425503020741e034180100113202c800001803280c0c41020301070b603051039000407140341260405c071400c1e000700c0c0d104d0440c5000c001d02d80408a52008007400c1880000c80781f45c80c002c2440c2401000300b814801920801c00b441e5404002444802e81e0040483d105440e0515550f0140d40100b0320010b0427030b0510b130203c0c0840c9000001d030303016a99030f50010000185141c504498200e410301c816100d005a0145034085522031504d064482c01d01240c401450084a1100a15110003a03000f03400341c801800038240495440f8085804a9811a101c900c040980804420040c820708500d0022418149400010400e29030803c6105919100a03510307981031011095054548081180e006e640200d0300800040c81c100c5c1d54140301070150b280080c202a1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 3454773 1250 3453523 3453551
    0xc0901020a0b0108071505030103030804060e030c100f050603010606120903051606020703020c09060d0b0402030c030f07060201051b0304080c010b03370209010b070303020702040501060906020d03060311010c0204 93
    0x401303802441454101000074412981e0b00c0302413011052003850704514542c0f43d62801001d40d10060320040c999a11942d251500400c02c009031180b8a8600c0301f95070760300808041140061260750f168041582c20000001d001c1c1c030303061207030a044440d6a2602d0201504800e40d4400030a50b40d541201070080a00c04055170490014001040c0d61041800680d104010b06019141c500d0000105209803010000c1228580300c124080d2031030f44d841702e002c44030b90700d807440007074285940c100089070107100d1040f04d8a014600015404102c4000307030020020391702d030144812288103030a000c40a40b9a000c001107000901c601c002050940c0c00380b4000908046480e00190501c2c11220102c82d10488440c515402400e03212060300c80c44050100c02c0318040c42d20340c0441c41e40101445038a60865002c103800041c10300070740440342a1503000f04100038940e11090f0180c2502030350f001d21001440b402144001041c060320581d0162500074644262100c841e00c0112031442c880182203030426142c14115081e01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 3456023 1250 3454773 3454793
    0x1090b01030b01180501080706050706020f030a050f0a0603022b021002010c02010e010204050a03021002120c06040c080307050606090c04030203070f08010e0d05090103090c08030a0c03020c040204030302060c0901020a 95
    0x2520620038280b07203515000188420880307046030305002d0b51802c1c00420840b10001008002c0b1822410320035292821803c2c410001d0084d550400c251840c0001000007800e010740c06984203003c024038041c400d4032100701000c2140d016000013900300d5241d141100400c0c0d00070301c025428030b01003010348900214641c0030031820030400300b40002507915140091826a02030040c0c1c180307003500c030300210b09080c0f800d00010261308039440003902480013282c20048041c82840308910000032a800f8903506c804501805966050444050b14030030b0700040301240c01c580100403250300a8002c40204a15140c0c1010083c900602500d00d8a00c07400c10800080142c800740080b00003040f81440b8451202c0c0707010501d60a4030100154141d40750032907200340c0030a94000c015034070f100a084c81c0c002400c4000d440e101403070702803d0704840f01612002c0b4040b203003581c3c018400040c04d0712035070070360303200092880034082640a640001000340e0011000103150451850141142d2036051044031340004654075030035200c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 3457273 1250 3456023 3456029
    0x6040503010f05040606060c02010c0b09010204080303100609060e010c060f0b0409080d0e060709030308091207080a0314010803070803130b090703050c01080c090108100e07050a0e0f060901080901090b01 89
    0x5180c0f54400c22040c80658495140207140c28141400b49125070360008026400ca10002030640000901103030715200254140d4014201c0c081c00c980c1d5900300104604a4034810b8814400069401d05011a000b803082c010030f9005001a118907120314016038516001e07280500111810503074800940d140c40e5160302a0311071f214041c04405070389458912074001559401c100c18256a400481446555640080480202c0340c042c60440201e0702e480c0800c03401c000382483c2618408002245013010f0003a924000e00b80b403100d6403020001c01004040014180009126240799a001030201c0b0340402d580000030b551000da8100e0755514a11103644070b034145041580c00070501c1c0e001800c00e0080050800089021440900301402c162038242120030b068400d070f02115040002640c0412100000b620070315002e4801d546d140003151a0090000b002600300b4000310b0700160320702128181c0c0c0d00304100748942c440d4024100d180790010b100f0054801800c09040f000c075540d81d40300d44002141403014441e0103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 3458523 1250 3457273 3457301
    0xc05030a090806010504180305070609020d080307080a050106020706030b01020c13060303111b0103090201170c0d0605040b09060105071401091a09010b0915060c100504050d050703080a0207020604050301 89
    0x120390511410070716160f4141c002d140510b00d000310701c40300104144006490640c0c149000c558540e070510700000904040e4900035041041c00412004012440e806144200c00d6aa6603201c607030340d01010305083c0d400078450000960003808050050903c00d8003d446012811300403a94031107035010205035015041c00100880f156925418000c0551200c3d10900200300007008042e09481450704031030541c0c00703030b415906059407100c00c0350459029110801410031016406401840d0850a0310030590008419108080c0703044d030f0110b1a232815200b9030849001c090034805847e030781d810040d0b5569202c00b0040c0c13055009444c01c4070360110309000d001d84c02c40c80756071009008022404281c05540c0087d0207508180d061a5240b0a161280d0390f880b0351104441d004015000c2130340000c2983e2b07204000c6842007600800340c555804e031400d81c1000e8090380c0f046044030880c60440c4411241d900511100900203450340c00818410411078014000003400140564540b41d62030000a0071190103400d680d10f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 3459773 1250 3458523 3458537
    0x110102091306080601080703200414070c02091b071202070302030f0f070509010806040f030e06041e060201020406140a090b16020103050109060503070b0313060c0816050901080c07030c05030a 84
    0x4041d043c00d000444c0140b941d44000c001803421551100c0031401c03502044110107401c2000805a03aa4175001010701050000b940084c900700030100412092441700241c3c000c0d4802d10110f40e00d580814020b400c8030130081d080e80d0500d0010382d1920403c1100010500441c4141500800983e509106241c03000c82c2c6a8000e02c402411004141d0070f200c403a5001500c1401c3c078100411440380c0126110754007960040d08070b008a5854501039840140c21421140c000c4004074010800c100c107a582032644004003580080d1040d84c90384101d0903440340e4010700002600004407105000740520207444607102c0350401514144c1c03243d403000741c2a002624105007401c1462a000b05550301440b80c0340c050000c049090200030f08140c0400e503645403510560204074170010000b012683c4144190300305960080062002c031100040040000c4030a0b595554441c4c1d0b41c0c0043c4041e0313801003086032031010040c0c5582025948170b000e07050450300140026014840400c14000c001034082c0001c00341a002511820 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 3461023 1250 3459773 3459779
    0xc05030f1501060203030417031308180307050301051003140f01090c05040b0109030506071b0503070303020703020609031306120e0d0203030a0c0801030809040b03071a0a0318030906110102091306 86
    0x180d261001a400f240554204000b0710000c9021a00c640d0080c0c1c1a070860301d5920746030050b03291120b10042c0c501a004400200d000000500521030b000b00900c0110b040703944081d01ca42c20542290385c180c59408800030311031020000204145580e0500524000903921259104660117080d2002c2410440e801a1006400c0c05546814450540c203d4070030318102c44014110381e2680d5848101620241c140701001d0092140d41510384ca444140d168000140c035101c2e421840c000e00a50401542100903004400c002210100c0010585440110311016003170100d10b0194151640103510440251064071520000c65042042040720340700310555005640c0e034548810a8401c803004160a241045005001000800c22400039201c000e00c04030360000b4102400400a890403040b94041e2012464401c1c0d08482c13048071031f014014102068800b0703c03c0e40e03180d111040d403550f403201004000c075a1848003072142a114440c903001c4009407000042ca0041d00c08005500412a115000b08481d252a801c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 3462273 1250 3461023 3461053
    0x3040201090b030402150318010905070515070f02130e011b0905060a0203030c090a03020307060c06050c070203060a05070e1903120905030706030209060409050103080c010e030f0a0302070c05030f 86
    0x800401211842c1421418642e0014a01d04d1a011090707030103d0000c000710348202a20640c031110b41100078000c00c5041c0540c60001d440d8202849803e12809513802c03001d80c00509003003210f8000e03034001c296005102840d03003040104005248601c090582c0c403031108500400034403c1c40805001140110700c200620207000b01021981d4210500400d0705100c0441c0b0719400009403500000c0455202e900c1d5510103000c00c0d2010045e80c0080e6061044000c001400c03038011140360115030140f44203101c60707a60050640c010b48201c071b0340250160702c502e00149400b50142d10080d04444c0074030b49503640030311120001d61910248944800703c0d800304202003080000180070555142d03454105030310050b1070700c0d00003a25580107124000034140c00140b10b440981c1c1c0d060840e806006044020025942c4a04000e010b641200e20321400c0c0b0761907c507106070b40c100000140c8841e090201091854040c14101c210301035000f01c0c03c11607007882030b42008601c540d008c1c081c403101c07008004010400c1d05098200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 3463523 1250 3462273 3462287
    0x510050702010b1c020f060307050c0706020d090509070908010507091409060108010303050d0608010507050d0b0409050304051306030b04122307020d032003180901050a0e06010c050307060203040201 87
    0x104015a03141c401810308540300c10150001031006541e0844c0c00b02c003540003180c1d100c460703000440d500c41d0000080003400740e00600906859440e81c000c58144640740c1c90282d0751004d900c0b10110104074443e9080019140815900e544882d46181c103110351980da10800e400d4460950715a00401c1010b201804002d14107005225500400c5450015600303014001030b00c80103040c00084d08004001611018601c05900144020807001d40200b1040c91b1508006200d030304010250048942402900b45591526010b0005501d030002c02441c0b400f480c0000f0845041141500c130020304d9100d4100001203000c10034400c0c440c5000d215802c00b4051403450003400c26071a03805209602e61a21105010a210401a00c98a55064035213030b4050541e41410f881c1c282680c1180c0c142045c500c0b070410307008000800940016005195001040c0094604111380c540e424040d90b5002010210200817054403591140c0e002034041c1001c60401c00c130b40c0ca802c2d003180c0c42100d05a8030365400000b40411035904c498 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 3464773 1250 3463523 3463531
    0x80a02010b151803120703030b090106030c0e06030901090803010306020909060306040c0504150806070c051b010c1205160b150604060e0906030c060c07090b01140406050f0405040504051005 83
    0x6156510000ea4040b48050740a44048404001c000711098022514200b000e42c951007581582d00340c40ba402c9207001006000800780050046c4c40c0c4000004146000740107140d084007064649855041c00071040c8a04e5400c01804200190340750301c1c445020038000001140614081d000260b9148015000e0094600010b84080e00aa0041c01000301080c200015002603500c21500401d4901040741b20ba540381d082a00305801c03900691080c0a426600701150668462040b000d403041c0380100b80001c54024041605240440d4104084c100044c07061000400c461000d070424505200982407286880712140504644001810023440001440c400600503c078a01b2540203241c1380c204030340107083c03210400780e15025010b080c001c115540c1c3c00b80702000c0b000a02620341915500300c150810b540d41a00d20450303200f2840e200e10302e101c0c4d510030020b00000b40505600b80d4a000e1808400b10740039406503c0b50491540c2c140800b0519a595000380350046000d0001000c000091006560490720060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 3466023 1250 3464773 3464779
    0x711120703020306010909020103020d0609050402010311030601021906020f03070203040f09060b090d0f060203091510050102030a0f11010501060c110a0e0610020106050402070308011a03010513020313050703080a02010b 96
    0x903004100503030b000140c0074151808440041203401842c80141d0180c0030320708501c4051030814601140c070f00281d5012500c50b5000366000d2180b642c16046c001c0e41071100781d441c00d0050308140c800241c94520f0401c948030083c0b1424005150041d0501c4448040d0001d840c248010780002070104404081e1040c01d4019041182e4200901407034004d010b011485011511030141c6807061081d01400072010a91802e0ba030804429503486c9411034074561103040040700e6512400011021502c02124103045074141c80301a0000c5260a010300c206030340b0240764458040030410340d48140c0311140c00a020f4503000701001d4554442505607440c0010484007920300c0c560044014100801c20a40e80ca41203d402110640d03000010080d0000d00300d001d4010380d00071300d81050001807120708040c2d03c1010181290400c4408411421103084504900d1000b88a4103030b0188000f1684c3d418401958000c40e0003c1190440042c060515a1180d0919020368000c1e102604e000c660190000e40a00402002c20382c11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 3467273 1250 3466023 3466033
    0x90706020708060609040510050f0601200730050a0204050a02090a090c0903060501030b010e0105010804050303040602130503160e0114030714010207030b0103120f0305040b040b07090b071112 84
    0x90b458641e612001400284604000b402150030300809100341c00c61402012801e2183e45003c0007140c03c0c516064805070f0026141030f41c40500007070950940f440f09012840a0903000d4a0041400500c0300460008a0105009801180404058859101c03035500c2400500b0000207503004200448100420304600a801000310480b195240c640c0310f001e0314400100010800b240341000c9421440e9500014940c503d06400481070007000b0034a603040300e0014440001503a25000111021941030340c000309658014008200040c41c0340d00604003c00001941c0100d880d0b892001910f40f0305084441e05040604c40700901481080e403002d64090101d0030ec80e201401d00000100c0e0b5030f403603288110380f00c81a01c070481038940c2e0300c01d1041c1801076800244040481d40c40b410481d928440085403000404c40c81390015614500030b00a0318401c5420050b0088241d0701e0340c8640000c07800c001d00d81c00802940741c0c40441c1918103500580030113802203c51030080d410708002c1c440c150680030b080e0500c035801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 3468523 1250 3467273 3467279
    0x303030c0503040b06090901110a030b0a0504060b0304060902030a0c1401020f0c01050a03051005060417010506030106140f0301060503030c07080601080a020a0b0c010e0712020102010513020609061b030a02060907060207 96
    0xa001c2e1305402c050240c0d9240090b503a0000d0f280d0041c228486000812580020512307603181d41604541d1a000d0200c5541782c21958840c100001c1358414441e600202000b400010003240b4142e0081021a0003d0182e6604c0c501c01d584640f50f65132160413422101c40960712040a550f0304001000724100180028050b6240b0b100000c1d200c0d0054034000301c02c258480c00003445035146031501200400001d480140c507640c5807071104003d491004800051907107008002041071a05009100480750b12009907501c03460702209012040040710075142d050b649910002406840c100001c02c6900c1d2078601401c2d049060400b10707418100c06a010351500c2d44400e040b1800759403104418821511200029030b6204448120b49002d041150021034550242841c0020392130720900d03120a01034400d0b4000c01c250394608404054200c1401300180d00840b003800342400c030b410050014a20394104c0342e1010300b076030200c428491840e441012141d005030464020701c4070b1200100312150207000c00d800603004c8103007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 3469773 1250 3468523 3468533
    0x210503030c0a030603050106080c030d0807050405060702190308030a0e0307050d080421050703080a020720010207030204060906030b0f090c040b060702040f1401120203030306040b01050906030901060303030c050304 94
    0x406007400e04141c2000601070034190080c4d10200007158088024407846035240c5526032900c20007044a402400b618440303c0050340320380d544520486054580c1810b10381010140b20068005035030403a003083c03201d56020b5601c1c03076034800c0d07400652144242c10b03600d00d00b107007a8400303441c00030009440300c0e4828084080080c002042420b10100c1e1444c103a0101d40d11030501d103450685000000708540542180c40320b6860b444001080e10364040d0700c4065040c5c0340e51441200b00e01c100c540c0a001d40b9694410030344c4401007661990000c0005104440905440e50006411500c080d4001c01c01103598500c00c1041000c105001c6602500001c0403171001c3c60500b440f42d4481c07003030070013451165a480600c1052996071000790341c0d0040d0090401c100008071305208400400010000305c52982d01200001049600d401c000e10701a94003401440c115100c0e5818400944914189903041c40410701c8841c40644501c00614810700240c030000c01d00e07900c3c0d420003804640d2131001e1402040020420003000c51 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 3471023 1250 3469773 3469777
    0x121d0609160e0a09050a080a0f0305070807050327010e070503060903090105030c03280507110d201c05120105010804020904080304140601060201090c0506030103110607050106090c0504210503 84
    0x50303c00030b001300c3e40b1081031074a030381440c1c00000003e0032000007190f0b9400096008d4851100208240c0b41088640c4903c002626203a000725051800150208000740c54803000710700342071803902c041005800302c01c11800c14500f9a041c00100b10656404200d0820540c902041008d4004c2c007030700701440c40c0a00d0800000d00740d1000924288410708000041908010103203da01c80c05030140500b4402126184901c3c006048165900000240e080000424024000c5880b203007510158640305000002036488250003422415090000d0140070501d0000181030034a40e11115a07275500c2540c0c850307120034069280d0006070003042c10040c41d0002c006c010307207641340e0311500319421402c0d05483c1d5071680741000240340101d00c160f056028030000051541d405410a260003880b0760b030309109058481b424132015010074400030f0060300010404070020706086e0000c03c1c403540550004100c0076211104482070394220182d141c00103100040802c100080c0c1185115a103229140c0e03405841101d072145c41d524 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 3472273 1250 3471023 3471031
    0xe010e01060f09030501110301082b030e0a08040f060801060801080d05030408160b1005040209060702010f02030f04030c0501030e030c0c04050705040504060806070305090a0b0403121d0609160e 85
    0x100411900151540d0f000d80308980085a010009010866428a102980d0340080c450300980b807148000840407100d07012150040811004041d803120149904110b0260400407100c001c0e40c040e40c0c00310000b060010340207102824290500900003850841c00400c10b14050780540e04010012005000d44000030660140d0501540382841d1692101d00f000701c1603200d42080364081c0c1d100b140506007000200c8030414480d1010012a0310141c2d03940d01840182d2240c000d240d0303480784080000c06c0c0150301900d03d0000050661040300c2c10903c1107106001240e010303030010b03140000303000b0081140e903900d4050122034800b120095424840201c11a03941c074000310a42d144100e8076000000c260354490f0081d1802044011b00600040d0781e00c4800039100e80045e40c3d1407002034181400204442400104c9010080d40300840d804142d0315600c00311901a01c401c0000b04030303911400c444208031801c00822a403507080c00041c005608001001d540750040100f01c0502800549000300f0009102c28145c03580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 3473523 1250 3472273 3472277
    0x30906011a040605030a1d0c0a080a030806060a0309020907080f070e090a051807030303020405030706050301030512070602070b070f08010603060b160807020303040b03041109040c030f0302010905060c0a02070e010e0106 96
    0xf25143c0c0c0d0380c01b402500c40d001041c0d10b000c0c1d902c80c03403540c941e00028100c11000416519800c640307850b42042903e03551518005004110f41a010501600b0540c00030201ea074040d15000419070322907030024105074010345205002550321018030071007000c69204990030484c0c90074024070302d1140c2800310384041c0c4020040500e1075660340018401308200315070510600085800d440300141c0340d20700980250450f00809001c1c2c450790704007080300b0b402081124140c907001401020141d10300003601d0516481502c00b103038101e800307025450004000038080782c01200ca50700d8039695040510b100030607480059003d08105409c100081000014600c00c4801804091518500450340c5081924a521030f400e0300a405210020b40003500007992406140140d108854807500310800c3d030f007080752821050b10040e00d4151405002c00000c1c2c000245030307004a110b80008207140394a9100e450034500d044901000e06040098106282d9506209a1016000c0d001074100070303505190050503c2c2c8014000c2c802 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 3474773 1250 3473523 3473527
    0xb060904120c0515011203090801050402060405130204030804030c05010e01020a150903090305060a020901080907060906031a0a030501020405011803050d050c030f130311040507020a0303020306040605030102070503030906011a040605 102
    0x81400b805224540b5003e210382c0d04c0203481e50f599050440401c500034400d8002480c881e0300410f0a2078107000e0310f40941e8000301503c0c00c050404c4200100b00a000001d00e5006a0820000000038242c1000c0c00046014007260018030385800000742c0705492050100b030441d002003a00100190744880d00504010504000080111152405850302d044c150400740081c4200c80420140d1040c980003450309540c20380e1420050307201c0c000d580b80e6660f4640a01c0c4041015110144501d41c8664404c4004801d440c0c00411242c001502289055210b80c20a0f1510b940002e0184410b503040402c91800c0c5440b2105000300d5459512141d40300d4103c0c0c0e990307800300a40000c0d240b100301c008106803603110404090310380d0788840f144203410362459240b1080f035406480707070716048803441c1c0f134440c5a00c110712940141c480000355580c11002036000030045503125a0300c0001054689007440a802450300c41c1c001542d8900700100da603842c140050344000c0070400c410704045103c05100003503500b155141d08004d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 3476023 1250 3474773 3474797
    0x12030c110303120f01090b0303040303020607120204090c02070905060d11130b0a081b060301080d030905010e070326030603070b0a0302070b1f0902040b0720090f01030b06090412 78
    0x30b00b54842d111a280b280440c074024002561150301c3d88038121000c03290208100c074805001d268030703406070b0700c40900507130002c8000810083c000c50b21054200f102450040c80c142d00e401d2408215481d000b8500016400f1840900032034240388a10b507001074003141c102c2584103041d5290b441c0000e21560b00c50103914038290f2030303604069a0300010b0b1803150080070310342e42c035442e0700c661035848000c17602240046105100741d190030309013101164182c0713032248050002c075000140e042d400740403140e030101c805640e295a9600440030602200e009588a4034450891110303c43d0300c010502800d05007564250380030014030100e503030002401030856920b429143d40f520315500e425030090040c001d0180c00e03a0040010881e1021001e6014004606049920072119807034441c03980c22401680500b000f100001c00c5440d0202d8184d94260b401010360454811210700c0c00d001042c21b81d03c054441c00d50085005005200f0000c00c3c64a81e90b00c071000340c07140f880c0c525080e2109000c849080c040c803010720010440d08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 3477273 1250 3476023 3476029
    0xb0a0c020a030215070510020901080406051801020d060602100212040b0406090803130b0a0b030c132003010521070603090f02030d050a030c0305040203121b0f070504050112030c11 79
    0x31600564004201c88203060746500440403662140c00304446c1406034101c00550780c05144256180c0d05010ba54512469540d952148000c000c05002e20642e112041d000106140090004012a480c0c4980100305680f8010000e0300e46805078103090101801070200c00510300c080c001070780c1d00640107076800e8030340c5d11030781880e070014a05400c02402400b40001000029488034004646552250701c0b150340f980e0701c5030b0300c68044440c410b41c1c555040d004a111006240783c0b60350008003140e40e6560010f94038550024290004d88100483c0f000a840880100254034024143d106400d540c05400c642c2d04003904040c0c0d480f40388501400003415035a44090003841451202d5082c040d03800380480f2042c500b20b40001e026500109400000a414130081125044c40380c0561806164090010715860034640b108400725085241014269540d86400d650000c100300200c545000c1300382d0181c40c091342814280010348405070008000003200c407084000080e03203d607c81050907005001c1982c6601c0349000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 3478523 1250 3477273 3477289
    0x30c12180a030503010510080f07050f09030a06050702070e011503020a0c0206070605060f100203041518060801030201080f090303070c08090d0b06030d0201060501080705090316030605070f02070b0a0c02 89
    0x5012100d00c070303400340c01d010950000300030b505a400856801c050002c080b0f6007251020f030101d617440803040d00d410110318a50b006070090821000f800032128200341c281008a441e00349210019a081038803141070082080c0c042c0081e901414512414141641c1420f8580d079201100030442001c040c0c1c0010395003040c503c5180391411407079000f0111580c500041c20120013030541600c00510840c0070224049480c0760115039080c090100e40c000d90b042500d04406400310b05580300f150400e12101d070482c04440c4127100c0688028240540b00c00900354114000140010001010850f0901e00402841800500001500e03071040b01d601c1c244540300401c0c548048180203442c0c0e641c0c0c101024039404002c10802401482c0b0800058003214003544070014100d007a18824070545000c21032a00c003298000d840b920040901c0034001c2c046803511800f191240b0002840750b40207481966584050218a070391180d00800415031900c0100742c194182003021420307100700104c140a210010389040115218516 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 3479773 1250 3478523 3478561
    0x5040819090306020c0102031006050405030d1b0203030a0c110901030c030f060e01050901091b14010c0f050714030d030606050a03150510020109050706080c030a05040204020d0c050406020111030c12 87
    0xb10564584079031031742041c040e400589001c0140340b9210004a9164424002d5400320740c0020002c06503c0d90020080d1004000740f58440749803d414030040740940c03001c000600240226581b42c44149c54203060130312000241d41e074010700c503050820041000c0341d100700d007000c2038030f8120114081d0381c862440e00a005085004208900c1d500340420031203a180d0651100400034003581400741c4848a04854024000440c00b900d10801301c04902005254440d081c1c1046c43c40c82076840300c09180087d110031346000d805501100d499850350070760f07407840e05043c401e00310348502908042c00040d003003e6024189000d481d4181c4105a03545240300d80700264821014000d00c006410300c0c054114022000b406030104d81d07003d980c940f003004c5d000a0035601c5000f41b6441918128402801c41c0c603a08240c401030300700908141c0c0d2041d004d1000905028030340c421003c1d401740d00e8440a030345900c1d014001e800d48034816072091080c5018420001b41450004c101c41010710302c9111a501c0e5517031001100c003030f40d08080f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 3481023 1250 3479773 3479783
    0x5040b0301050f0d0c06030501080d09081203040507030606090b04060b0c060403030c0201090204151a03010b160303060302031906060f030203060a0b041d010509010f0e03090907020102040b16060605010201050408190903 96
    0xc1700051115010390110b4140c0c1c12602c2602c1e01c04812000c20b81f12002d6071b224401c032941c040000c80003401840700156070000e01c01d03015100d605680740c80c0c0e0006d4540a404ca154213542e00ca503002043d02c1d15100701002805070310011418410124640f40c1c942d0350040006e400e142d2030f101d91081861003948058081c0d5802070040045040c5240c00150380305081c060740e0b07029080400503180b50300c00e8030256412504070301c00d00c40c0f0b01a828809aa00402e02d03032811000e16440e01c0021005035014400382203420f0245c2110042e50100341420130a8804644c0084070b425100101030000d600c01203081540280141008a688440c55000c100148040750941c5d1950046240d0b841e412141074008900801c100760080c420300100b0300341941200c5d4cc003248240c407075000f04450122800c0540b1000d5100003580001810540d4075166000a81d20010001088142c401950810030800e0f104006c0640300a00c002c00080ca4261340d03081051196140329001a0a120361280c2a90b1103640b001000e95404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 3482273 1250 3481023 3481043
    0x4140307080301090c030204050a0623030a050603010b0a05010f05180a060c050601090b06030a0f110a021e030301030c050d050304031e0201031a060301090e0304090606020a0b010605040b0301050f0d 87
    0x60400790102c1d00280150b04403d400e042d4403034174682c442d00945042d40c0c00105a64030041c900717842583c0f10100022400d2020440822080140001c100550302c01c2c20310f0740c008126072a0880c2094212460f5213000d6118000143e03050100343d9000e841110003002c0380c21315581d511400742d070703002000540742c480356030001e9003a401061207503001c25007120113482001110f00590303c034a1341c1c0f025201580d00403078008405000107840701615800c654010501101d000612020845222020340d0001c12140050303441320a047d4a002050506040d000300801c01450955040d03685100404036681b08240c0b082600208d81030a02c40103004940085034403105a620348000e040c0d0003c034210580200343c0c040b0b4903112407414080414981c0040c1440000c1c640e0307255030b00b02107031030300186000045900306110911010900e102c1a22410000c0c0125070020f006400091800840411050700304008104013880100f201c401a0019030741518401c072034000d00c50024001103000c6071016000503100d9220 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 3483523 1250 3482273 3482287
    0x3020d020c030301080d0809070303020a020d1407030c060f05030108070510111501030c090b01020a02040509071a122406030a020708070c15020c0a030609020a1d091009021305041403 80
    0x100045050005919440d011855500c42301c03015251400d0788805005a041084036078014a40054000c800f41c2c8030304189802c0c1c00c108090305240c80010340084907400941d45e07080c4042e5412299055a000d020f243c01c40ca59030400b2440e580315240c1740314540c01821205655000c05002e0105403018405c40421903460308a100d074aa08182020322090b1400b83e0040ba0101d4504d140340104600756106030002c2640019075400d001c001d080081000b40345005044000c04e80d0141901060b290403c0d2403901500c6000390109240c9144000e00900c0c0403448441c820b02054910460521361010100c581d1070b01e940d2aa6903020181c410540020401c0000140850400603000500c1c000e441d281d24803c3d038101c65401c82660b5030a0f4071041c059014001002c02c00c0040c5d0135411007601e1600c0600980ba0031682d9410655154a100b000e506051040904005401100308100d2010042a6006004024003030b00405d8908190111002210344c1f1040082d050101c0150b005880d400c0100841e40e460319 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 3484773 1250 3483523 3483539
    0x90a0204170c0f0a0b0a0e1507030201020310080606150304030318060f060b09060906030603010b06030906090607020601030b040308070315060203090102060a0603050303011203110115030219080c0103020d020c030301 95
    0x408070056100c1d50f40c3d200040440d050580c1244165400000498646007803814142ca6a8040f101415480600d1900744520513413514081c1850030300c650009a280d00f003008030001a0b140b0364001d1591030303104404120340740d914900410230380303000f64192980e01d45660500b10094140c5d080084100901e9119a604100c1c0c02e42c42500d1074030010008110440d120411a00584504840540c0c0140c0a010350344032460100001d60300460000c0002940c14102808a01d181d0011912002c903a041401040380419041c0a02d0340c0c40b901600c0940419810b41d62040c1075008043c20150400102d8030005040c50b000e58040d1060418070401300c000e003907a50400070350701d5000780c9a00f0300501a50b404203410b6078042c00760f079098030390203030145085038280400380101182c904001c1c0e00b005000101420b604200b0b00c51520301da113426051612540c154018000805030080810b50100708002080045a4001c00c000304210401d1801580d40c4814110b20b20280c042c00c03070030000d140400000090605 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 3486023 1250 3484773 3484783
    0x8030408090a1401020f0d0504090b040b09040303060807120503120703140103080c070807120f03120f09060b030d0f030b060c070803090405010b041a090612070906120903020705090a020417 83
    0x30ba0241e00306c1d00104003504401e40c071145019000c402062050100303028142ca15007041c000f050001e000003485581b1500000c800d220160b50a8001c03c5e83d641050114400070300c8011b000d04400400c0c2c0c207407002c0c0ca5a5240c1d03644200c03051980540011004911038910980090340c0022000203c50180e58407400c28000c140e00031200d440803407045843c00140e0030701c08110b510845031010280b180710758150711808170340000d002d0128100000710f40084800e01c802d201d29000d00606200008810100f0314001741100c00c0300030014400d80c0844804001c40398070401c2c03011091b03054a408241301d1a00d40100310a800b1790611a030035401a03880104a2400010280c0348880b42114184a04d90303031a03410f03145520a0340120700359042408161807458111000800702c2c2080035002c1c41c90f00d09074800c46050f0f6201034407210001401910201b0005600440981d8560507080c4104420340c510346c1e0181d511a074500c01c06000701031190014240440d01d9069170014840028005145a02c007800c83d0303111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 3487273 1250 3486023 3486059
    0x901050702160506030105040c0302090306130203070603050c090409060b060f03040c050d0b070f05070c060f0206010501030b0d02040b03010f0e1e060f0703020310050307060c03030605060909010308030408090a 92
    0x180314003400b8108a0a0301440401102d201a00301d07881c5900b008240301c0944100480e000c18160200000340c081d0f20100a0544030baa806054010895078030302c101802c0a4407603200c0350816007001d043c40903c1a400c401c44000b80021100000c2c890308500d0204060068486005d0b400754020a403098414111801548035a2190a18944690300c0d02d040080910b1000c4001d4403014103800007841040c0034260406100704a130900d503041c40401c1d5078502122827290080300004e104031103078011003501004070317501411007400c042c014001d004020508481c008580a481580c48a14910386628203511a240440f0049070501a22060603205a4bd0749000d64030111030107103580085c0c507c0e00300400d80a010300600418420341d074481c84400c401940000c0c1c03905c00040320300d400c0001c180d54100001c000420090300d030302c806004581005402c4071015400140540c00401140c0c415580d030704480c034113595000c0100ca403607403114108207515014a1118070740042c546180890911110380b242600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 3488523 1250 3487273 3487277
    0xe010c020418150e0a0206160803010906030b07030905100209040f020309010b0a0e0402010e0d03050d0e0105190e06070507030908011505040f0b010f05221419060c06020304020f03010509010507 85
    0x8451929803c881c01c480303031185282c1c5150007000c0b07420300601e0b1040042c544d00c0c2810b03c0b060540703142d503161009039510aa100c1d102d01e65031000c0410400040100d80d0360311069a0804001e22070090301d45640710411170590865503507000904800980d2030398804480c0a1542078115281c5c90103000703da00800d480080d1500c1403000aa0010703280c010140480d103d554107a64042e0300d0405002440001052410308401f402001e203c2281c4800b490720501c400d802407680041400d00303201181c0701d8613150001185144a0419000c0c9003841400140350b500010203243c901d07500c2c40a41011944c502080d00445241d500348244400710070042140b40c815141c003124100908440502041c00722108000d080d804610300302078000c91240600040c01e24034004a82c181c0c1d900d258056000b40180954102d140c01c071038000184640c5040c0310040144840c8400310303100034141050f1001c2e14544060100601580c0c00000040441d01c41c0c4840602e00c88018009010780d040807030080f4042d05c000c50302040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 3489773 1250 3488523 3488543
    0x60b030901020c060c160803040c0510020a02010813020303070803090316080408010b011e0c02011803030c1712010e0402010302070803010608060f04020a05040e060f0d030c061103070509010e010c020418 89
    0x841200300c80c111511b002d5607481680c80200c466403130f15265000104181c4051402d0040060240c07140551201034a60036030191601949600c005820307000301a081100c0304800000c88001601c0c00400c4a801e5604040f0781c80e140d41d80c001900d49540304003814400285115000442044047c1c00500140c940480080c0040700070040119100d42a60352140d003014400095070056034000d024000041d801072520180b00520183c86007076941c0168011000240d10400710001d00441c0000b030365058410100c950b142603000070203c00c0300c10040c05100e001c1c010510214085a0090b41190781d400e9208403a80e80b01c0d0b03900d01000d0006c2d00100d8659024a07102c858910061805101300c2e0068242502c80504203400e00402c2609410010569500300300201e4040304296201c0390403050141c480d64901f100c01c40a4a41041600e025144c80782d258401801480308003900602943c4004a0030300c2c3c900811445030300102d50401018401a411070321f0000d501302d4a01000841d249001e000b042241b03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 3491023 1250 3489773 3489781
    0x9010b04020313060209011709030408010605040207020603011509030b040b01050f0109061e0c050a06050711030406020d0f0210150609060203030603070626090105180f060601050c01060b030901020c06 88
    0x141d00c41240c00f5802e18915071281c0001800c03030341c090b10b541607040c9004000d0901d40e50a095804905030b502c4007280d8004030f000c1240080c240642c80240c43c054806605004407580811102d00041c090720303140301038280c2c2c41c2007440e10170224a0011500026010300508081c14050703820842130040c1c0780121076800810700c195003d0000d05084900b203a03a4032900908091035880c0e1080789080760310400401c04040401b243c010405e076600103000d51400a114103103488058210702c0160200141070f00244030800c103454020490411540c05c508040182e00c150100c200e00389034140b18039030641e41ca0100c0b10240c110581000034180d410544655044a454040590fa01e00084441c03e6260f0b100b0441405560300c00e28003218003000e007031086001d030356454166034050031088841604580d52401000f1075200100310460100302520b000e080004a00420a41c41380002000c0d241806070010b1005881002507014000612080401d00d841e8209000040e0103035110072015240791042d00042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 3492273 1250 3491023 3491029
    0x801060219140307060f0b030607080906060105030a0906020a020c010807050708031602030c0a0602090a090606050909060a08150603060703060503061302060708030a020d060602030f07020f030703020a030302030309010b 96
    0x141c619500318070503409126615a110706821100e44a400810f0000b880f0b20300c0052000c0c0641144940007800100c4c1c104074a070141131030190000c00380000c008106c81809254000416020b4015100f860310304d0340d0b903071982c20200c0640140c80c401400300c0d2000540341016540412102c101d034800341d840d4031413030711031a100f140c8a000d030345009441e8200401c0824013140c900c1940c3c0901628030b0058900f019000401e0605252520750f00340e4446400280350c1c6030915141039040050042c5c050100016410210300134002d0181820b0540115402d0011503066680c01440c0001003041000715000c1001074560380d440c404058440320300034410b40c404105003034064060082a00d5010380104500c0d41c070804001646440c08105a820040402002c0701044040b4002c0d40300b20940329015940b41141e06016080310340075444082190014400c1c4015104424101c4842d40e404403442d40940581c0c9000904010007540f0080d0300490f0341b00b00008040e00840610710443c06840204060100c4c5024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 3493523 1250 3492273 3492283
    0x10c03020903031213050303040c06030501060203040608012102120a060f0902090408030a0207050105010902030103120c080414030f0102070f03020706080f0a050a020c06010306020912030f09040903051c02070308010602 96
    0x341580c190414420b480c50a011440e04517813050600c0100c2c0ca803040c1c00d480f00c0341554002d0b0b8042c2c0e04e103502460b052101942500030180188800d1000b5803800340303441d00c02403070f0280c1801150115110403c40c03045105c0081d21519085400810b2141412940f003c020307036800720712100f01d58403410401d42c1742450b4898030491061640180ca650f070780f583c43c2d95031001c0d60b600082841d09450350034805240030403400d10032103001c2d12007003000603070369419810301c20058000c010b204030401444008540029420105541c1194040c42c44424407070328040010b410b140102142180310b40c40407522100b80800c00982841d03281c0070340c01b568543e0340c680e44100c5030b058003166000407102013900070455a082e00e501081c0e010803121001410003130518441b47c1402d40a030b0094070b5098021034141d01921f004502c074898a41c02c03100842c9022121120950b01d401040c081c540b013140d131041c0182c14540500b00711410043c8489001c003984e9445e82e246802508070f81d03c16070010705400b0001c18218000a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 3494773 1250 3493523 3493537
    0x3010501030c030612020f0d060606080709120510020306040603080705010c090b04030309120c030218060907020705150702030307050a080301180203060105090d0c0f06030e010b03030a0c120320030405010c0302 92
    0x21081d00d05c80c85c64081c0032403a0308100713005401115a01d4040045600340c0300ba1070140629035100c01041c20540801000b03541c0c10f8001d01c4103100403c005000142c00002c0f00c03c000c81a01c000942c90740e43d8200090020109030f84040c01c8030a00040d140100030042d80081c540884e6515144070603a211a0030302c030310b4011030200801240c5032400611009480000585180e481180100003807500e03540460412011803070503605801c44403003841007034079200194a510007903510040c00710500c0c1c20b000805120a40c0040e0684000c005104419501d0a004a40b01c060300001120210001440c03c181d55038403d10403044501c211814030700c414400c0d4001c8901401c0160359907810018900104004034a814100312400c0c0d01d00c5400103000c02d0300e80c41581c01401d8944001070040460910203081d50b40d880503c3d8469042040686421a0003284004190f80c00252034041080c1005054000f4101d03515035a11a90000601c07075100420800290b11940c8603034000c0c40780d45091042034080e4081c2038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 3496023 1250 3494773 3494789
    0x4050405090114070c0c03060c030b0310020c0c09040c0305010c0507050d020a03050d0203090106150e09060d02063001030804080c1801090b01140a02010b030d080105010909020c0c040e010203010501030c0306 91
    0x31004c5071580e4410588100310500501c240d60b010b0340e8a0751417400300e035600d29a03000480e4507890401e819250078840b02e00c00c05c50f45e080c158500a1000380fa141c0785c1007241e001c0d0340704128031000b10f41072020600c840310145038001c0003009040340c000c00280c000e412422080b9407038840e03c0d403280540361010880c2644143e05403203c0303040c42d4455100f03c1c041e4000400d0b2128540d1b0390032000443d91054007a1400c095940d4544140300022001400b0b41010010401030144271510400320058586808454031288180411082c6c8400504034030300400a0503448500154190008020f0095100090046070b070381400b00c0d4011900c55003800700800c4000030300c032041710070702004001d5808a60002c001000e014504602243d03040c1148400c1c40d0854500840140e5466200741c009080400260700f01e84007a0504215a615000c0003c04660044c0113854015402050204445008100901b600390f4003d0041c031280100e10034040c007c1d0024810140040c0c10814101152802440390905450b440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 3497273 1250 3496023 3496061
    0x3020601060c06020702041415030c0904060b0d06060308040501120c0903060f020405090a0b03060106020a081602010e0919060501050406020a0609081201030f020108150d0201140d020c03040504050901 88
    0x241c06403403a6200b82410369840e602001001c00681d21807082004446407807010382481d003410b8903141d2030301103420055070081d8814054003480355540381d2035980c440c5d44804c01007129011540810b41c00e580c100380091813241480408004c204c005005882960f0b020380c0e410155006d0146010151a4001d85010210300c80105c1030022886640103084d1200303d00c800589842d0380c9001007002c800040711310442c200c3d80e40c1400d100d146070a101d100d004101902c0200403052494035114400d206150302c3c10000d0b4210001041164010f003401900c1d050010301a049030f151034101c03005901314420403130458924105001c11507600840c283e405031070080d401018070074201d43c0e45000600c0c04141c1a52203440600c0348500c00c103104c1c14070b6806103210b10f0417400e0903c4148000350410001a01400361500e500840c070103151100c000d454107003a02442d0126204540201c0e00c00c41d071150050f00c2081d80d00005140b043c0c1500000108110f034403c4d02c0070801a13864050040c2260701d0030441c40c403c00c41c3c1d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 3498523 1250 3497273 3497279
    0xd030209011b0503040b1305030d02070503120304050a020402120901240306091103030304050703030e0f090604090303060b180a080d021518030409230114040c020309130617010903020601 82
    0x12825140140314800e5013128a025168032020303440e50001c0c10308540c00d40404805002c00e0406110ba51780c40d10b483d00003800d155003070200098441d84015100444040d0220010b810322038104900300c0c40c03039000303007086540c0e10044100d4841d5610441e0305441544c00c2901070003040c01c414854801c0118010200701c407075402e595410010303051114090780d81105106a00429503002e10056000780c0c400c00c001c0003e0b44c91460068140f240b102043e601c21b101c0b0608511182e101e0703650161780318100302d5000452408510b4180d00824640d080b00602d501d01094003002d541e09609129001c003801c40d6801015030761015032642c0c5508000c502401608803000d044c0d11440041411038000480c90100f04a40e460301d0003440c0b450300039501a0084907200d240f1109222102d15181c081064010b020820560620344842d0603080c541c000700380159079407807105014034130038420b0342e2002c0c10007040b01040b03180b04140440034219074010000c3d4882d0081e160382040b80305200c0c0c00c0002c0d034540c0150001b680703 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 3499773 1250 3498523 3498557
    0xe0601030c060c0201120501060801030b10050105040303050d09050106090e0c0603011401030506010207031205030103030f0c02030a110f040213030c0b0c0705010e0d0b0405010507020606010c030903020f040212090a050d03020901 100
    0x19035983c0482c1804034444c5205a0300465014260180c00700756200f203010740c59801c241c042c1510107405010b566040e80c10a20159a01c401118107694160074503e0b034803682c121080d40240210100a413595182c94000300700303001d25030802016800038074100c404035981c0d07000304907103840b00303210791100c100c2c840400c100740794001c0d000a0b90100050042d0f40c41c2580e6500c1d20110780c440054000c00250700040140205900584038400b00030581ca41450101c031140e0200e55910322421010b086400081140c0c4060760728043c0c0000302d00d0380540295264003814002903900d140ea800200d66141c0c3c0703da400f01c0c1b402c2021060b16400d0304c418005003103241c60000190f51458201c03005d150440101203a25003c58a00340b00d882c000c41c40780000180521740102c00034140311000e41090304200310000c0160100c3d80c4890910140c9804a0341d04018008000009009220300d0103508800581e000812082400c0803440c298071a00a4003500c0521900460890803031065103c400c0c04100010b40a03003c2007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 3501023 1250 3499773 3499787
    0xf0c010f03020418150f0602061603090203100e070503010c1206050108270a080a0e1002060702070b0c010e0d020d0e04050c0a030207030e131a09040503090d031704080406030e0601030c06 82
    0x143d01240280c405900d40c1016a646c0b0b80540082c2c016900c11030610003420007402048084000c1454200171790111540003940741c0d8589001400c64503210302108100010a00006000b800000e0081000a02540d400380034212400500014203152000001e61940200000b511420b81d401081007800c0300707440100c00c00315912410044034420640050001001c9600800301f000817602d40c3c001119001e0100a416103206d4601f10441d08040700f4000341c00e4002901d00709840c100c0e4207007529142c0704c1085034010702c1042c141500d05c1c0308401a251501d80c01044282541240d0340c2e5044121490509100c103580d010303523111034a0402080400d05041c400d50140520912900e0300c001c00d8100c240005136851034400d00c4441d07a55942d8020022025500303c102900901500d0300140351916441d115280e0250151490203040c1a1007070f50101481000c4d041480b26240c401d003010380c00d0038105041d05808c03500074100400d1415a401c03140c03050000310755040f20703031000d00c90400b581401c20480b200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 3502273 1250 3501023 3501041
    0x7030207030602030c09030c040b03030d090f0b070302040e1501050a0c1505010b031005030109050705100504030501020304032a050705010f05070b1801051303020c06090a080f0c010f03020418 84
    0x50003803010100000300c4030300040d03010721007182500c0d40b1100600101400c2c8038001d9403003840b45140c40030310405502c0100a0301c001c000780000000700030b8207034100300314091000c0c94010944189501007051007501035001d48203031400d0b207481c1c0c5611380c0c0711074a02d420f040079142d45a011440511841c0000741c070a44041d0400c0f0302c540e4520210301d62403012170040e2802130300b2160354024040b08010801d010020b103c2d0041504400911040400341c40f59600c40d0298021980186100e03081d0035036040c0590201c81c001c42d84000215500e01d000d0030000c1948400440000e0625841da090b200001103800b402600d0300d40000160150914050054941d24036500b000400d21005000400110381c603107044074816000e1000d01c1021501c044461400c4900040044070300840c1076480c40301003a400601050040d0f401d8403817079038074289000003071410b03203003680002d68510441d145c0c001c01100208840d84042420380b01d444000c00580b5042d801c0e800360380154104c0304c0b42030411f0031909420350010050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 3503523 1250 3502273 3502277
    0x7030c0504020d0b030a03020a02090c0403020915030109020306040302010606080f010e070e01030605030a0302070504060b0408070320040903110c06180108060607080c03030106120207020a05040b190609170d020703080703 97
    0x465032040086801e102080c86c0c140d016030410341c404807d41c141480368903480f10300e810702d403450513040d903000925010020305050601080c0c400415013549007540480c0c00c1d19001012200203240514000340a45100d01622002030040b00100d800a00ca01c070400d0306841300e40d220080c0c0c0d40e44400c02122440740c0410010304050700e0300c5c0006401e031804c3c000000700d20f0080d805412480c2c1414244415103015500000c03a10004000800c84020082005000d176039000d03054400040c2615888000d0818071260780b0f90140c90a1903000030140c00040e00c00384521000b055a80c289039540411109002e8003600001c550b5150054041c2076200301102a1b2280e0010134140c10080182c07680c0e1035641000210109641c00080180803180c5c00910340c0201c07100c030550643c9060199408512625036511855000382e40342c05e00c10b481da0341e82007141030700503961850451066a507010010040c0c5141c2c45480710600a5102c206d4207008081504480a03806400425042d8910b030b031a500107134048501a01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 3504773 1250 3503523 3503531
    0x61205090705060f0409050108030a05090d080d060b0a030507080402010504060f021c020c01110106080316020f03010c0201060510020609060c03040203030403080301080105060a05040504030c0b150405010b1305010207030c0504020d 101
    0x11555584005040701050044c042915107090242c0802140c0068102d480d480c4e02c148070308180c45909c201107070440d0005580c5602103c4141c9003500c4603016401c06201c4007803c00c000442c1c4070b020030000d0688100e0355034040c415502e80c628190346401040d10040e0004508210a0245601540801315503100c40c0c4100c5480c5400031840c5807841920300d805100507044049031103000d60340302c132003407180340a030308020441c642c50300802958922801c04074192802d0f4800c10041955500291444075440180013030020341700300c10000f0b000300503a00070144280301e418846a5900d1000507514880c4100310010022501c407001c100c4001c2c6c000510499141c4400c20000c0000f0f00c00c0c101a60003400d1400011880d070415808100400e5001c3d042607000e9071415003004042540700c00c1c1c005203603030440c0e00d2100035141c22020f0200360743c1381068150024200400001c040044800070f0101100743d1350510040d5441d0401240c8420031440050240310380207006110b00d01e040d034014403000d107139031100103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 3506023 1250 3504773 3504779
    0x70b0c0f040810050103020307080610140109050303070b0405010c0e09040b0a02070807030306060206010608040803071206090e060f0109020a02030f090609040501120201020706030606121109091003110a0612050907 94
    0x10b0b24014107480e5403c041a00c4600400840c203080101d00040d00d20038000c2e11940c0341880c03442001c00c400307102d5070042d0043c3c815410703807e1f4083c0320940060500507003541e0713072080d003403c21008032202518103c600d581b900309003079542403003078554114042c0010b019043c4c1d501c0700d44906000c20300240035100c0756603080040400003000c02d002040f00324400d880101d00945000c501070f00340a4140d00003401d001d004010080096903420841e03521100f44d0400d008040c0740c260100d4000d00a54000c0e448682c6031004002c48110001001482035009041034071550b81c80c0c3d49480181d0190500c11b10240e070050012030032014100c80501f5241001a01d00d40c100313130359580060705981007a80034925054400c1802d00555030b041c056034000d0402400d050021034601b410040103a0f109003040c05209a807807501000c040c004404a5144100080001d03180381401c05018151034414401290261500c590f2481035041541845d000c84003070b511200c4030006a052040c6c05410020121003803805140804 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 3507273 1250 3506023 3506039
    0x61605070f0e040308060114070f0c050a0801061403070f030213090203160504181110090330090f12021c08030702010f0605030d0302131203030b040605010302070b0c0f04 75
    0x1103401001c400b100b4500030709241c00d0103441c0b41c8000d002ca604004e8810700000322485610300b191901e681c4440041d11909460078400002000e0b03810090f0700c02810800000c2c00740c0150095000e4901008943c90100c811408040c1e6440b641c1c40340000c0350140300300403c05482d080310248015601d6007404540c0480c20b500080c24107040313051030030b0a6004180e00b8015030806109a200e60b881d810300110402c1440e0701d030588881c49028000c0c0c81180c5d01e190a050340c1c2c0c4910b480f4401103900c0781c05400d0071508120420005056842c40024103034800700603d18242c450004442103c0d902442100c056041844000c2030040c0000142d81184040d90501e8a00c1d02c540301164665008072101912400c111800a094030358490143c1000b6040401c1485581e030041100b1119540e54100143e540c0491b03c040000c21019511102c4403800f1103501c0e105240d05600400310254007154100b01c2e407611000190100d004244010303008c41c10b288006280410304800504208400c108020305059446a003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 3508523 1250 3507273 3507299
    0x10e010e1906030b0a050705090f0603070302090a03110111060f060d08040e100303030f0b03030d0902041407020312010603020423010306050604060302090301140601120506011701030605040b0903030606160507 92
    0x200e444481308004c00c407200029100d000c0c5c2008051a1a514000661001400e64085c2c100014403401c1c00002082483d030283e4101e9211000c06001031b079110b41da0341002b588074401c0788030480c0031545401c140c002d14500031030303402d00c500410000c4110986a2909000388950100030465618604000c0841c2c2c40755080341c21886160051001d04090f421460001c083d43c0d03544041000d4141004802d01099070f021080c4d0340640c1c0101000500012240001006052150320b21030b180a842010b0104e65503002c00241400340d19086464966641d0f260b048041740705230b1040c406070209900c540c5549245070b00c0c0e200941b0b00145000b2030b8590701c860001d0085d6011740e010390040b903400205440a420f0a004a44c244000b070201141c40c0c1c500440040c0c1802010861041c4003a0f540e0000f0303c840e80550520b640202001150948035030f140d1030510300400058074203403929066600020611100007040381c2c896900644151f0806214003038207032070403007103400488550080c00c0001c6240000099 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 3509773 1250 3508523 3508529
    0x9080d0509060604060501030b01050702220204060903050609060f04020609040e010509030d0b04020a0203030f22141005010302010906050a1403150a0b070209010323060406020405010207050108010e010e1906 91
    0x1030881802c0143c1044120b07005640b00340e0501d03050500c1229243e0300b000543c3e01d0903405580080990110303856002d459040a41542400c52022402096855109000d807003501c0c807480c100d4901d43c85155140d0796810b01210860b03241d02440000500500307115015201d0440c01502c04900c01441210345803d40383d040320441d00c01d60006c038034409103a2070b07170092051509003581d0441ca032900345000203490384801082c0d1625888c64402240003612042c01003800c408400f410095240110302d0100e8401c3c5507131181203d644078544138080074442a12803a81225816140c01066529001050301c154205560030b1040c020401140ea1809071001d0096101c2c111048451496280c10410440700700915081081c400300140b240c2001a1201c6c5401c505403038101907040a000060071b100440c6010840080c0041d000d400d051108001d16600688240e8509070255002c00d52104011034912009119010030301552a0040000000b08140e003500803000e9620700145207001000103060b0f950baa8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 3511023 1250 3509773 3509791
    0x80702090403020d2309040b030709090b010306060e1302040b03100603050303070306060203040e0103020402090d0609060e010615140310030f080408060f070203220f08010f050c03040b040609080d05 87
    0x96003004660305c40c4543c102d081400081452900352603500783d42900405134401e0045075907a1700d00580e0b56041051000400031400300384104ea11070f01d048421900c082c482120520708082c40441c1140501e4280c901c80d440403000c1d007440401503000c001c05030194120064040c02641d0308510040114018800518003480c0110b0340c0381170001008044841c00d0f489403046401c244001d200d5800e107080c842d81140d80440d00941c0324052180043c04003102c1e01001044145089140000c100450708a07818450b0000c000300304550342d40c1d200c0320813402c0c0c8149903000a1072540c3c02140011556001d55000754400c00c8030080310b40c80f0398400c2c0c100b4050070419a5040f101144c20009141e00f040000d03480311460380034a0003400c0145020f07540e405a050074000c01c0d0a0034149260500c2001e0720500103250020001503230743d50705e0245e54000c002441c08998040d0400c070001340ca4503244000c99004071351151083c500b42e5201d8440800625001104840c0c491080000e42407e007114098540034070100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 3512273 1250 3511023 3511033
    0x303020106140102010207020a0b0a0201060f060e0102011406030a02010305130b0f0a0b01090b030103020d1403040620010c05070b0702030702060a08010501030c020c13020a03020705010c02010207050607081303030908070209040302 101
    0x2000030b20302004107580b00c0b64110380c010414500141c0790031240c82c003100d0030100f01d0794884440103000c0c2d000d08110b4020041c21602200000340080c2e102e40c00700c80441c0203070020040020721b8035aa1385a144100ca015405a021201e80c00055200f5401181d100e2003d503140311a61001e075882624040d415284025903c09000138002c5e514214031611840040c24280340c100c20f4a003120f41c01c254001440060320a484171555803050082440e02d5401c000d0b20401503070303592600c030003000d010303800e00c10300030f030700600d016940509034030b10500c52003115001d84e8031440e08211040d80c481d407210340000e050800314003042c800c1c2801030b21040080c0400480070384942c00d0660400380010205c586180c0c0705411580300c901e0301c0d42070740c40b40000c0c41402c103218803001d6903891006000313401074400d040300140729605e419088a1003550645c090003502d40b09a0036200c042d2600c0d6007c035000301094803034440c031092034441207000034081d610222450b48038196040c00e281094001582245040b10142e01503000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 3513523 1250 3512273 3512279
    0x203011407080a05060102060103020402030910060f08070b0c07090e0f070b03150102010c0c02010509010201060314060114090106090b07020406050613050907020102070506040f140703060b040615020606130e03040303020106 98
    0x510060b4480f141e120100194a40200003e503110011b200c00b90040b81d000010403910b007810300801c09190096401403000d00d03078410300088110308501c80c988450084402c080703100e0141c5403c440c03659802c1070050421605003907001c1d0090180701c124100c80d00c03400c00c0d5100c1d0518240103e100800540c40890f8a0307150030502c5000fa5071100712001d0440e4504002e5903809500312903030b03035038068080c078005032100c40c00c100507801032810760001f1380810301609641800703200004246050f01c04003c001c88905441400703200c9aa4070078001c10010511100c014000007085002400206000400c0403400300c1e41c03240890241c1c0d0040045200070700d1100010f0146042c42d150399504a166403000314903050f180d4940f0340d03c40b240504014100c21403038994000f4480c5039502200c1c2c03160800181d84010380c0c4d03803034588010702c42e000300513003c3c40c10400001000509847c244440c40300c00d8001d02419500c8604126404a01010303e0180325a00e92005039422010409000a1442078000254a40c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 3514773 1250 3513523 3513527
    0x703050d050405060a0c050304210c050102010c09031511040306020a0201060e1005060c010f020f07120207030c031e080a050d050c070809130b060d0b010809010c05090607030504030203011407 84
    0x50803408000500c5420001007003152a00011110a8201c921b0500701d02089858040d0551082d548440e8a6011040f13151025016500e2a410454443d200212070a0307030302c0c40168240c5030008800301c00705007000c1040010407a0058904a400384400c2e00181c4466180108540c41c0c01640041d0f46050b800301d400c2030302d1a0240b04201c05810303600200308280c0341551904541403040e00881c1c0c0281c102140811480c5000d4100c400102d000f05400d40d10b4240c410b072003000d95080f0180c2a1605424a20003005c1f841c004038010042c1c90304000c110070418115118244980160a101c2030b00780000507104010402c4440501810921366451599941d0b4040280e410f882000d814011000c4c0304014a80009581c2c00445203000c43c241d83d1010324114160043d00100707041200d16420450000310a01d804d01c183d40f0403641284241ca81c3c0485444144d012403c8130551080000410001c104101d550702d00380c409030400b1842442c01610345074496003c03a003990300c800d580c0d0092140303d00034419070356 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 3516023 1250 3514773 3514783
    0x7060806090a050c160807060c0e03070603090b0f07020a0209010609080c01020318010e0a030f05010b01110604050705041802061308070503030703080f06010c0602030708091002090307030206030604061502070305 93
    0x410b280c100784010305200308078030113a12a82c00e098a0410015180d8020030900205842d8860f4009004020440c0f540c0e10181c041550b425a0900c00d009a03800071801d140207104d0402c0c041d0f04000c181480f9a21328a001c905010050900d03070551003015010300040e07a131030421138060100c507554503840c00d01d064640d0345416003107a10541950818069580e0001d052000c032807032070b18246440742ca00022000401c40c1035030315400c050001c050501040c024400150406010140282c1e2a00780002d103800c0c000381c5500b0242c4000b08243c001c24802c00803450107800c80c0a2040246243c2004900c540e4005072035948108407000d9015501c202c02c0005103000e12021004001c1a4042e51400103180d40003454800024111120f0041070307004114264800e4119502c041e0340042d04658908092401501c80041103626041c5d601c00c1e8080500d200070300c0d00a95018210190007021818215400c103c240c2d08024130464209643c0e9100280078429804c1907118220160040e049050660400c18140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 3517273 1250 3516023 3516031
    0xa05010605030a03051608040807090c021c0e120111070f0209160203030103081309020708120109150314010906062405030408040902071103030d02041e05060f07030e030706080609 79
    0x2a0880f0f0a4030000c2a00300d030880d080f032086560100e245c5c4030305181c90741660041da040441203210b03a050200d08240d03583c5c00004003140940845011886441514202d6210008414000350380d41c40303442014106a00e40c00042c4940e00c00218035041007400303c00281c2c2085605a031241010001703074003507045c102d80542c0c0104074a091a00d000100d207034044d580303120611000b8002c590004251031840801e030701d11070243c0404001503584e00d81a0801100c2d6803c40310000102c120101c00004030303050319118143d81020700080000580346035071a0b1044800b4030004c400c189540341c12500700090003034400c80024100c9640210200ba0241c007420122418600e900c0b01071150070403d000c04601d40c80145d0703084442c1d0b100c001d40c1d03607010352801191403004900c1d45a054800451000342204294002e081500c200c40068450204500c1c48000d00c1003e910456800000803c800304004a00c00e0040c0b0f0401d00030700b08100c41449a10200b480c04106070b0049000602e01c9003403005134902400d1207a00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 3518523 1250 3517273 3517279
    0x109050d0c0b010e040b0609071e0f020c010201051909020402090d0b0702070602060907030b040809040c0509010e04020403020622080f010207141c0f0c05060901051806040b0601030209060d09050a05010605 90
    0x1902d0301d6986c01e04140b4000c1e081c1803091040e800010359503442a02d06901c0e900b1b440c654403042462400e0060300906c00f00744000c015001d003800c083d815510501c202403040c40e010405241080190800d0030007040b6001c2d05036007054003003003d2030403034858420319070030360f4868084680741e40707082d0b0402030400b0810381001045410a40c280401c0035000540030090f039800401101c00e6444900d001d148501c034621415400038105250355500ca50050040c00c0040703000e894440c114011102007004900c10f501000707501260501624076200540ea511081c0c40240b900341c1d00300c058031601002e01d4a0740410300032055a40000702c40c820483c3d841d4035403020240300c400500c2e80302060091828aa01901039450800180c209501d60541c454071030002030075000020313100a410140d00240c080c09080303d01190b62581038240c91056080050610302c9141c025002c4052600c1d480011006584031320820340d8440d0061058801420380352154001041c8240010300d042c030721503c0c4c02400d54519a000d284 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 3519773 1250 3518523 3518549
    0x2030a05070210170a05040b01050a05030703060507050403080c07031101080603060a0507030b0402040608011401050a050f03040809120d030e07080c0402070507080d0c030306090b0a03030e030109050d0c0b01 91
    0x8164011050721205a81100c0085078144401001c032007902c00d0980720b8121059040034410403804550015004034040c90100c0000c1ea01c1d00217118040c00c440c4a070f15016070244008201040030355115540068003454280c0c5066540d440c0d42030a42c02c24240800306400c0130b5420020050303c90341d8651080ca0a09052455203048800251200c20061049003607503100c800291003e40720341d0041e010904010400c54540c0d444010040c4a510f00340141c0d10940f03091070701c0901c10360065045d0f0b441c1040070b5458502d050079800f8583d10a400240048070f480764203111201303a682d034104603139070002c003101c00400b060b001d01c1c00000c00b41d9081000011094008001c00e21a09001182c43d9004001c1502d002d692a145440c141c0e03d000d6060303100c3c90345030140c4503001804039844030065000c0c5000340d80c103115858980901000303c410300b2003140d900854103041040041c0c00b0791003260758480000c00000c0d00b84019101c003070400307920003d60b0001803146041c0904000c6078010760340c054145c01450709 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 3521023 1250 3519773 3519787
    0x30a020f04020711060c010204050310020c0601050118030210030b010219030203090f06090402040602010c0f0e18090f1509070905090a030302031801060e040b06010c0f02100201060e0103050c030105070203 90
    0x508006201031003500850b00001d5520a002099050302003480026014907910003e6003010741c005d400900840e0321038084e803d01b00020002030b0090700c8403140c5c0340000c1d1096902c1d1030010740300c2801d141501200908040400000b44c0d44590f00800517851035200451603146881c00203040280004000501c2051003081901081e070000c10385040c08400d64050360301c0d0010b103001900c50f000e2648556801400054045441c40c0d064109542048a03a20b0b10300e070808515100360350080b0a5503d0a0f0007070140940710a8454140e80c3c0310b600f0501c46003da501148507200c0701070070800200b13290340503000e640f0184070303a91001300050b60007881161020403450038060a0030340c40d801c17020b402808040d000300c0800c6200c0002e2a81c00440c083c0d15008000302c076079802039044205d008450a441c5940482700040f0b4550040014140c030070f0340020031141a24003942003200c1e500c400d00300803085660301c12000c6080140c1c029400d0180d80210010071807040441c1c2050300b514002400d0744c0c210340041c0100d07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 3522273 1250 3521023 3521029
    0x1050105031317040302040f0209040b0d05060411060f0c01090201020715050d0e12070309030c050609030a032109030504030c08120a0e061213020301050c040501120504050a0506070206090606030a02 87
    0x2c034148582c002041c1c0910a141d007810040c90003560406035202e440c1008410900409600500313490f00190307402e115000c000303c00c2115020240c840070300550000d50008000410f8182d1450b000c480003401c09040640000350455aa008107084801a81d0345000345070540d80c0420400e0b00801780c2c42800f440703014180d07000402900a580e01c41440396111004880300c000305000541c14482e88121680e1a243c007820000c01244140c4000d0341d500410150108542c14a0021209422805401402002c160b030f50700b11100c20300c4070944d1002401c1c0a90030340314600180545120540603695850f2214114103000d010161190303c5265154030940d400c0810540d560f05980440109040c500003021001e40070881c54802d294955080c2010b8500300800c40d100d44040c4120340303000794002c000c1d030303550a503c9181030b1140e80145404181030555817880307501c240d00010307801486507050340c4466059546540c40c0c84420358001015800c0b8804000c141d107420442c29a005a0880003800c0b45113650b004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 3523523 1250 3522273 3522301
    0xb070507050915090903040b0a0f03050903070201050702010e18160e0303030f010b03130602040e0702011b020606060714030a050703020d210207030201021b0705040b04090804140d05120a03050105010503 89
    0xe52400f5100010014030381417000d000340c5000300040b03d8401c0d034400c00c80d0340c002c00d1076079010320140c04a03140c8401300d40100c41c0041030700d980650607195140350141c01e400640f0a040b43d85c4959902c01c0040c1c00d140c64003043d00f80d860b4043e04459060700a050407850004d0300c1003002c3d15001d03009074428001c001044024801c0541107840c10074019540361036030700749481414550200030381100d00000c1c1c0040e080320110364040c42110554001c0128031841180403541c0c9101224410060340300707801241652429a0041080300e110710512690080103041190440c3c110101c1d0b803000c20710115814090640502c55481c8802d50b519009240701701d10701c1802c05003541c046030034640390b030302040103000c25000754101c8003a445200e289088003c0090000d6648400600900d8080c80c1030114034412404d181c0504451a07034401e074280d0826040200c464416281c045103241e00100d01ea400c0c001007241401900010700078018003550b10040c103000075041d12810380c010f41c1044010010010000003a002c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 3524773 1250 3523523 3523561
    0x100501050f0c010501270203041101030c030e10020403060509030703020604080f040509040c030203010c0512011403070308030c030402100e03031209011e06030c0905041a0a14010b0705070509 84
    0x24503a44400604203218100d01402101d244a50710340350002c83e1a81d1101000c81600c0030751b01d1010030045000c507442e020382c08140c0c0d00902420f100c04100d005503020350002d09001506240c00601d04145030031542c900b01002080e0018154000390600a00089002d0558480300b0b0300000d501c0c0c446580e50003561004020f0028003c601302081c880c0c02c0c3c1501e00d003110014040101039005500302820802c051140c68030089109620300f180c0e07184180d009000341c03010900c00044500c0240c0c41e00e2005081c80340442e00c0c0c03542c14011200040002604070001d0360096680c019000e8482ca880c8c07041c40550810407040d50244800d0003c1059181e90002c11503003000440a411a01a210b100b0070902405194010100700c28a145081080d00e800340d005804a030301549210101c00d83c0e070600d440464006640c00742400c200c000c1e040c42e284003a540b03a503401c50f041050014118218841180d10150280c11090784420002114028444100105805800107d50020741800d0404e0407000c0000350700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 3526023 1250 3524773 3524777
    0x40b040b18090901020d0b0307050d020d0c091118030111070f060905010501090b01030609050702070e070504180603200a05100302070524090601050109030605060609030a060c1403100501 82
    0x10411240401d580c000700030030802801d001e031582024115540030f50880c1b12100c000601e032114490591800003442c0c0d0444034007610903161490103800303004090414000c2076680101c2c1030000240e41d07085114140c055032080e8951512126a603c4210030007980c907540910980c140150009040c1c5200704a900071a803280301d410324120546080720244c43d5140300500554609400043c11145580110030b10700000d0742c0070002951101c10000440b04140c4c0c1c8500140d1003c4000c0c01054040d00110b03400c0000307800c0a034100740e03581c0d040084460381640550052600c901003001000760750460b41074070301c2d15051050307049103000300400d08400951007032a200e500a500200c0c8002d000b64110391800da040f40070380c1d9140303201000150320001494000c81000000034001500c0307040105030681031340c0d4140d56a0750154516202c2401901003c0c0504e035214104000d01c442b241d40c100580b2907803a20841021640c00c8860602400c051150000e100d1440030400c20410481a401d40c104142c900c24 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 3527273 1250 3526023 3526027
    0x80a05070201090203070326040e06060306010c050d0203130602010b152506050f0f0108120a091205100e010e070e071803140106060c02030d080403050c01020403060212060105040b040b 81
    0xe0822405444039003000b0f03426003d50036000c4140265013003000b281401d1507008074001c0001c220321241d10f104e80d2161003c40102034000c54524500a0001c40d0405014500000041a5521814105029100f418000d603000051003031584501e00b01e4540100024002000b41c80b110901140742c0301000e00d10201c00060005000c0a0b641d041e001040035200a41c545016528061419000412080d82d40044035608040012543e01c1010940c0b4140e442d00e0003d0318003800307003c0c038204498004000c9582407002040c0e01003084e204035400511820300a10044c60317910060301151303086400c41000d11219904000729800b1841c000030b804021102481040340c4250b5980e942144c0d401d211120a128500c04104000240200f400d02007a44c050b01d440204009a0b840c0010790b0308002c003c4001350550428850640e00b5802500304503441070080c10214600251004001c6c03c91340f0a400417903140da80820034424100091200c5580042d00782086880d003400c201c1c20214030b0044c0c3c41032800c40400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 3528523 1250 3527273 3527281
    0x10c0209040615081b0303090307060305040501090206030702010506090a180305070501060b0a02030409050901060303080c090f090903040806060603010806041e020a09050f100b0406030209010309051006080616080a05 95
    0x16500480c080290340d4455800f29440c1c495060312119011580140c104009407400e00c03d03e00031085481100f0014010003009140a0041e400350100170b1040d101035581d4035214001d601e40d01c000318482c0002c0e5000042d5440d001c01084501e2001412405800d407809841141d4485280c2d800c0300003503058105261103d01500c1c0c986e0140109421170452420081b42500340d40d60000042c3c016190014002e103c035981c0c0a08403822542948070103400108441c0205055000c2600145a41e41d4041d106031003018464000c55007044007910400e4450303200150401102406114294004000701d0b2542d24551600c03280e159243c03800f030405881c042005141c3c0030b400402800d07000120b81d01400c2181059074410000c001018125062403240c004080080d8141050220030404e607100501200d05040c01c21000703d00a4004d480c2290506990700b9940003c02d03c1046202c0f80718004410218005052031a0142080c00142402041807280038200144a4000000c0f56126240c12000240355075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 3529773 1250 3528523 3528533
    0x8011706090d0509030c1c170a02060703090f051618050405031801200105040c0501030b0a0605090303090a0b0901020d1403010e1b0a080601020d0c020901030b042a050103050c0702010c020904 84
    0x310311b069240d8459902e5070b05da0501c2c207400c0680411380d402103205807100328410308200e0043c40303032070500401070300030b8000070790744a020780d10103440725000c0c0d103d41c0c400701c0460799014a0080d07070800c00540e051100c002041a6242d1200000051031440d406100d40d040541c0c4081c3d490080c410034510380c1c0417034038003002c1d0b9922982c2e01c44500040c03240980d4940710800e08560080905070b40c1078070445400c2d0741c0451294001e01405d2441d42010708492a903500e841001c0b105a00000981a0b160108200881480d076030501c221000d4041d43c0c036142c2ea00c40e020000a4a440d601d03807000014000710401040494240d10b042c1c0f41103a5550b004001e1568072142501c10b0002d0300b4404004030200402c2d404c0202d588207665911400081c0c0803200c040c80709417016180c20300700b40170095004103904010b0000954100c41e06800612032411070b0000d418200c0c05c00310031b100300c000ca8089044414400c02181da454022075070080b624062030780c904145500000e290400c1000041d01690000c000308040007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 3531023 1250 3529773 3529783
    0x4020c0303010b030601090504060b0a081005032401060c020603010b0903070306020c0c01090614071407030204060b03090c0616060203060f0a1707050405010e01060807090305010501030308011706090d050903 91
    0x900a01901d40c1c9603152018140582c2098600034005010780401103028101480366105441e00d0348122401c012481400715850703803008002d440542500300f00021152010000128207408190058051001c2d0306100407107a04140d010004001d504a001c2c0c02584421342181c5c190350120426547c2c4941071808a847d1510980c00108080c0c0300045082c0804408075000c3e01e106400d982c3e0111305590b40400700d0305d002c11802ca1004003101081148001003a0f182d1002441c3c141809540156079650001000c40d68198003040040000004004400009029030013a101041314894200f400443c4020359000b18172000502d41c42e4000045800d5944000c1c5011031803000a010840c0d007521601c1521640c561310402c103009200d201400f1600e8a8035009050580d400644209596860204211900c0e1000b608000510142c0400440494002e000d01400780d4066210680c0b0303549011403524064050446404141d0021014817040742d1000c00c0c0c014906d2598179142d52030f0060800028106 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 3532273 1250 3531023 3531037
    0x1b0602040e0403030209030d02120d09061508060106080127020a0512040c0603060b0f070b040309120b010e010512070501050307110a050703030807020601030507030305030c070b07020604060b0a0302060405040b0402 94
    0x7032990404020406905800a211010094043da03601041910302a60f40d82d02c0c0c4080200c0300c0106001291070f98104d40d0200c071800380601d00105664040a01c2c00c03140d001c09402c04800380c0c0000340107200d240e411084071401406041c40c408800c4512805562041c1405158094a00d0f000100c000c020342c828800e0710350001c0a01940d50090038107203000326004d445446010040f904009002a0000300f4106071204190f58007001440c00d00e080d1781d4074203141030040c4201c0901560b1680828840c0c140c10010303070081d208a0140003035504249030240d8018050348900d216194044820344400700201d0190100d40302802c1036a120346600d0416221159403018403000c0e84a40191001844400201c0d0000c49002e5158400c0c0c0703803200b00040782c94007000d0101070003c0d03100203400c000192045000307540c4901c0c1c032620b40d800c00c040e03651503071a034040540e498030040c4c1c405000d0006210303591050781c00800c4d044640180702d174513550224400740a24842e161003242d80388560032207500d403601102e520f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 3533523 1250 3532273 3532289
    0x90e0406020405030115030201030e01090b0a0203040201140c1b10020319030605030d0507150b0d0311010908030718060201150608040602070602030103050d030501080312010306050403030e0706020705120303071b060204 96
    0x34142c0d11b820030301148100f444240c0c00241050301e0b1045444040c810140e0179a04840213007901e50324418031001950020340104d04011580c00030310202041c135409084502252005810000503400d80b07407029140f241405846401e0b43c1d60746210242e000400c444a10307881d0b0741d45281412a5903404d074004c00881d0b00040c0c0500a00251100607a403000080002502c10341c511408800b60b881200704803682440780c140c20802141e4043d01082c082ea02290383d28000d1000410b01450b2035176045ca40c1c1d00207880001c00b10f0342d5614041206041e440030940640402c2c07000f0000328090056808d40407a984c4291400d0041801c007140500c92640c0403208015084401035599581d2032404540d6a4940300740d1000181ca032800215000001204841c10071030001c0c40301003140d003180c50314402010003400840070b0541e160a146401c2c4004d2102d04001c00fa103070007070851180780c0014061000c4442403503540b942c201b0001c00c04001c5d00400070b41441ba281c80168009802c02d4038211000f84555003003010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 3534773 1250 3533523 3533531
    0x60302060c0307060f09050304170120070210020a02010909090305090301060602030c0d03060303170705070b0f1b0304050d0c0f05070909020109080105060a031106120103080304050d020a03090e04060204050301 92
    0x4080d80700000510216205410070400e110000c00303c1000c0701d221100041164208100c00c100340070841032036900c9100d856000044203501c0800c03107040e01000f0140c81000c01c60101e040d40c00d502d010208100c1d0001240080c6c000b66880d58002000503400f4000d41d000141d4400e480024540301d402600c6446a01034002c026031038507070901950700d8012140c44000391040780b480040e028828011801180da151311654103003c061109040c0c1442d000f061202000001d10490b008155200da0050103400c14800e1200c941c28030050001036407245445d0180518008c1007804001100000c007400300c0c10301440e0600b041d600524054001e941550344c050700c244a20758010682141039441045001e2007600c42030209940c1c0c0c58100d080e10400c8880c0c43c1c1c041e03903141040000c0340c44d80c0000202404000c12143c0f40030142480900c5070002a0000c0e218141c000c420070041141c208410443c0003040c0c0000d140c42d5460b83d44c011700000140c06440291040e00000c54200701641e0144c501410380200244 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 3536023 1250 3534773 3534787
    0x1030b0a14100806060d0807030e01050702040c0c060501090603110607050c060703020c0306070906020c0f04020c010903030603021503010e0103030c030201021608070b0106050a05090105070503090301060b18030312040b060406030206 102
    0x80710410300780501ca020780611300100b00ca51501c6c110300d01c07181c1d81c408410b5003031045980f02503e0320100b50f070348641805000c00080c0010303580e6119052f01100d00b0789660400c0c41c001cac2404000c03100141c000a43c0c1606d021001c2c00071464100c0d001403a070030219845c0b6a500103d14242d03007007030354407070034a0382050b0017040100c101600440c02001100c015000c84107665102c9000310341c8910705218020142e007184001c04172900780103071120141c6c08094030251504100c0c0714803a08545100c074081c0c0c00203558170402d004510700201046250102c8210032805d41d41414103007214240180f10040600424041080030075001b9015244880c04510610300300c3c070341038141140181d014090444030486010700108056006005554804c1c5466580500f0821501300644490707011490a4490341300c2800031804035a0300340035107009001d00080658030b4600031a40380c0060348861204501c00d0700107018210000c65800f460951284d0403501c21012a11078002142c024441a000a500528005408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 3537273 1250 3536023 3536041
    0x20307230f0708030123010503010504051003050f0d08060a060509010c0f02090f04030e0103050114061303060606020307031e0206060d060b04090501021809010e1317040f0609060302030f01030b0a14 87
    0x3070350488000c0d440d10311035080c06d0105509007060702040030b4007141d41400103010174105688002e03404003814030f20081750340e260389036989061f02e0080c0c0a4603a50091006c090307450b034000382c12600400c042d94000ca801d03091040284c43c0d030040080c0c2c541000880c00450082c0300400d0b81501d1000d0300075201009500f8015442841504205c03004d0b004506100c21442039540f0078480d0301e040b90400c3e554510034403131460400103650722288600441c04440c20022000c1407a038414000240100e400543c0c0d40ca50601d805404503030b241403075100901000d0300e10145e80350045075042d440502155041d0134143c0601c1e0001c0208140c076280d80d005441c2c20b81030010040158024a144c1c807031100500d4130083c04104000d0b059000340250040c8015030801f040b416090520780c46052803107080110f0410300c1c0c800f60382c040d541280e402000360305040d10003004482d40010041001c0c2c1a54a001e61070362400c01c1e0407181414041c03100034071b00c0c22100000f48196220f0303845940d9155011010740024100a558 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 3538523 1250 3537273 3537277
    0xb130f06080601140c150604020d02191412060103050601120207030c200303120402030703020312040e010902030702061302030708010603060e070603050f0f040204110d020a12020307230f0708 84
    0x409011401c10000d51078420446030640c4c90340d010060050400707034005c3d2901c4280030030247c003054002d502809036454496141c0058041c004201801c00c900031711030f11000382003088901144002c40d10400502884900a002250380224207003004240340c0c40d024012100c1100740503055403201d1010980d1820168020007100072180100c50001c0400040150021030070408034403254503501c00c11000d486080c07881e0000398424001020340e004c9990b6500402e00304850072031040b00d103000000c1c09104402c0c061050501500d10242c0031800c0d89403089019583e031001402d006c07410070754000707890300315541040000c1c060031445000f40f1905940c1d10b4520050400c4561486803406540c00c0480d001e881f0f40304091082c5a000310384c3d44161604084541a5680500700f81e0304583ca0300c1c1c1e4800e420750440010090f6401c081c00c0181e5a1701d50321801040044001000401107004109015046520112496600b081625020035540200042220318400d4580f040c8400700d011a14405120348440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 3539773 1250 3538523 3538531
    0x40614010801080f0703030c02040608070303020703060e0606010c0b06030f07060e0f04020306010e01052d0c0c010905030c040c030b0a030c08070905010f0e0910090503180105070c0b130f0608 84
    0xc440c076050340c80b501030a803182000078890150368417905007000800d00c9003807004103990001d03200051003611210110704180040c0c00550241e809048108204880b9116000d50b100030348000c1d10700c1c4c0c109400000c21320166410003504076001c60300480c410307550a101e19420300041504a4500683e01c00c0080c03c40c80310742440c0c038410340b02d01e03051020609250089a21810050b900d100c1d083e0302110064455070041c81030a8800b45500c803d1428103520040c60506c0085030743c42c0c56441d4010520a549407205440f8440e0401c521075404006584000801c618031420443e004550415456400c4006120500f5495400850500c3c00018800003585400a0380c039880140c0340240d803141480e0065500c03c0c07003060728014980c0c1042008039580c1c41425007101c5560199113010000c4502c900030380340d00c05402d441d02e80001a09415507a400250324511400030708140d81421001d45605915445d2407154200301440060660f04d1403590001c0080603140c2e81d00141c894584441c0c0c003d0540100322 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 3541023 1250 3539773 3539777
    0x603050609070e1e070c201203070515090a0203010515040606020f0a02040902060d0203040b0a0c020118060e070302060c0a1203020405030309040c03020d2306010e060a0e0303040504061401 83
    0x100031942020340d503180b078803a204507010810205504085105151310003403103013040248503c802400070302c1000e0381c030044a100000100c6901c400c142003004110704612003010650040090000146000c00c482440c4840c07010007118564499001e2400c00d488000001d5055103060100300351071620924000024905031000c00c1091307220038099980c2c05040219a05581c8100c1d1400b0051030a83c000300ca080d44003a1005040254000100050707030820b5a0840c1c6401e2030008224110255100e0b500c120070140c4003c0c080c0f00d4075944904800150300001500c02c0740c95540c18031200c03100b04219401154060245560b60842e0f044168540a0002e0201e540d10005001042260b00c02c2c0241c80c19540000d02451508a040d420440180390310190181450740034014244103000d50700c1942c07180c1880c1d011502140c410364a01590905004085a06001605c9415121901c98000391140c41019040080384010042c00180c654080c640c0060351060600401040e80170f68001204030050003030b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 3542273 1250 3541023 3541033
    0xa03020f0d0804052104090c080405010b0301150603020f090901060c03031803080601050a020708070906050102060901090309051003020d09060b03060f071d0105040b04080106050a0f0302060f0703120603050609 92
    0x60300c049429030b030192400f0b0460f51121320410a54506150702041800303043c0b0010345455642d82e46070013915026090780c6e004c104a5020001840003e0050313200801089000b00120010005001c3c11141d050007280708056020410181503454002120222580108165029039495034014082050813070210002414040d005a02d40c60701d1510300b099580c0b640745c0c808a56034081c01104c4940200c2407100441c4100e070030008100c00184004030240c01400400300c0d0007401c00b000607143c100302408100c19a1f1510700c0c1302d40480d502520700410343d10111886030000c1c170b40300b104030b003e40500f0000c5910f103842d0800c2c1d0350401940358411504401e05409440099541010303d408059044480c180803902542a584500502440c01d42d0301410506040303051039210a00c42e000b40d0025044280729a40d1600288024548415020010101e003a04a09401c0c11680810041c0c0550000303003148903004502c03402014041d20314608001004401002155501e00f80300750384001c20317501401c2ea8062 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 3543523 1250 3542273 3542293
    0x3011706040206090108090c0901080705180105100c030c05150420030a020103020d0905030403060606021e070501030b0f0402030405070303080c0a021905120301030c060207150c120504080a03020f 86
    0x2000c2601841541c00616150820304000015141c002009090600d94050850010540d95900201e41d02801da80030003440060309100912201c030b0700340401c84822071042d50042100b9500c0203800880c400d500c0c900503424200c0f52030180c03241054040010541e0203451404001e41c022003030814842c50254843c0803000411070107c151246038a0120754064000d05401405540213800604260750f400d900000c40019640703c280c210380203a0000c6402a8a600081050b242c1c100070210540d9200900c80516801402a00d0390360041485021305041c3c42c0c501c40040766642e000e01d40758801000e0320940d80c0303151524000751141c0e19804202c0c0461448000b04038143c002409540c940400c540080034000300a000c80c12881e42c0800d000c58a03882048444440c3ca0038500255009521412482d1881806c115000e41009450380000408a441c0c55000c0d003007642c4103c0818030726402180140b60400c64000c00c88442c410b94011000c544035280c4404100f6600280b5110102050820b850748075031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 3544773 1250 3543523 3543569
    0x901021e0702030604030c1106071a060109050105032409040323090a05061e0a020607080105010503040803160c06020f07020a050d02030604080a1205070305090607030516110708010e01020301 84
    0x1001d001030342540c000c0c0002400240101e0810251600440c10308a140400800080841d481094100c6001d0b0049890401202100c00059000807003424000e21140c1030100081c80c0b03000080401c620300312000d5040c02c00025400040c0ca03200070192104c506803a20342005060010100d00c0207442071909403042640454020545515400c01480750001c03070f01d84030801080d50800c0568004044a01550182c0c8050900050045100c240c010f4039140c6443c1002510700281607001905001007041000f0000b126242101e07070091400051280c81925240e0031134000d000b1078001016280f000a85038501445c50020344511380c42103e40a00581c3c03104280220008901c0009415a00260100380003800b208060320041e0464038100e40c030801000f184034182c50050b514000401d99803014030081900901c4840d40c0714009060500960038000f07000111030b51401802810416110b24010808509101000083c003e100c02804008082c4904e54000d510030310a4103401722242103014030b404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 3546023 1250 3544773 3544777
    0xe0a050601050301120305090d03080f0a060b0304020402180901032003031923040308031009020a020c010f050c0102030405010605010905010207030305030f0402040e06040302010506041107020f060a090308030901021e 95
    0x206942d400e0070f603440c01c100311034444e0465400f00c003442020300c108105500e8800040c00000d010390780c0c100c0d460804c041801c0801c2c40246c1441e032031030b0900c0e605200c10b103d20012070360416810340780146d80d51052440c482c4a920103102440d0311aaa004c000014401813445400304030400e11100718440959900700360f0b41e40318407040c0e9180c1c0120707910445d07802070040711801440c10015464081c0030f017840c00c4d8007090f0ba00035082221006000b1061158079107440769240040d140c088000c61614098400c040d46d00d440340c032100307410819102c0002d500e25104070b090740c900003d000029910b03410076150a80c060502802060300041d1071810004141d0b100003010401c8030f03019200c051840d00c0e1050603d0450000400a03a0806c0e200c3c1c4410400500405c00d042c410790080c0c0c000501070414200b00800c1d680480c0250740d81250a00c042000360ba287c0300581000c1c0c0c82240e0a980d07854424105441148060f80050105940401040752546e4107400404001803070040c0b8121209410a01031058 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 3547273 1250 3546023 3546031
    0x1005070c0c03020d050309060706140105010c020f040903030b04090c090b0303030606071115070308040b0106080903090607020310060f1401050301060509060c011e0606030501050603010311090406090203070f0e0a05 94
    0x80c03403844410000f60910640b0f04903002d0081d0306076880c00540c00080b13081035020644c125056540c8566041a101c2c0d60840140906000d00c1c08180300c1080e80c0000c1c0c0210401449940301e555a00d400784101800b0b0341c811002e0840280c010301494031903003025420b441e082c2c41407042c010308040c0c0362860751501200702c078442e02004207541d0500300d6684a0140607440303800704a81104c41c060300e40280c440a00b0160043e07a10aa0fa004c6092600e4502a03181003010791203c1c0a1140400038002c0700e03e4048240c90907801c041e50140e803540c41c41c0c00080c0c505004500c01041041c41c0000200e00e0140304600311040d95101c0281d081010945401115240320910400d030001d1428080403415181a50007024188540c50020400d1111220007910340c0b01c0380b1503503020469442c50100207191301801440c1c0101002c4070080c1c11503141d0f48401c1030041e10342c0412481520a080000d080049590050003000c0e0081c084540740d0b61a00710905051505025003010b00540c080041e0b038a00700c07030140900c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 3548523 1250 3547273 3547283
    0x50604120b040501150b030a1505010e100314010308070302060106140306040513050708010e0106080109020f04020f04031704030201030509010e0d0806030106030b0a02070c050105040f050f04020702030f1005070c 93
    0x14040c40d480707203109204050011201d80d501c60388406083c00c0354003002c0300a004009415a41c0741000e1500d10b049a01c02e118680f0b03140e440010800450b81c2041d032140d941d0b06d040d070307104040c0c02d16044c0c224000c01d5066006011a4501400070051224484c080c1500034840d03022209540d032104d0301501e0021082d03528548406082001840e0350520360812500086d080510340034000050707a680c0e040801d2a00842c0d41ca0303540e591034200018090107000c00504455000708506007164001c80c06070380c0c0140343c590042c1c0d00007401c0c801c060041002c50307006542200666280d80c40010109540c1e910a01c0160b00080c03d00d40803071a5080d0600c81c0c10300851250000f00812000100c0942d1100741c010800c1e5415545d84da070010200d0604e0b1001c5204000c2c1c0200140c4c1c0d82040d10305043e4031003058216070304201040c041800200707aa484034100755401280c528110b0440c00300020041d205199001303400d8020440c8100c8103420005080c9074245072000240900d6444440803588001d50400c0505 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 3549773 1250 3548523 3548549
    0x20d0608061b0a030f02030403020c01030506240f04120303020a0801091b0305040201051b1c020703080a03090606050a060509040b03030a1d0406080616020f120304020f03011506030e0601050604 85
    0x4609507490010903c20350341e0700340824911601c115140890700b085405070050713045050700600a41e418400d80b980b0440407a0b115494001101c00d0041041000c1c120882e28400002c074240003220f59015600103260a104052200c461807800030041d40004107010041601e400c0003085403462030068456110061241d0001c0c89400c900482c0508005401a81030000c100304520309864140c0401d0141c03100440281050f42c0b5a000c207120250104610038210b40000d041400000c00e40310896044034110319010411203001d0510b4001032a056104030380c4420499800140c982d041400751400000440741000540c519000340354491242e96002000a0710b0002000c550350100c4103240520340740604005041616404d06501d0504140c46001401941564400410ba4100507881846c8400d0300945031220300301d03041c40318a00002d40000d01c00c106404d0b90b81110740302588002040482400c4c89080c403640c0300009030040103031005504003400340c0800403920707003010030494044581c1c140510b1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 3551023 1250 3549773 3549811
    0x60a0e010c020a0f09150806090303070f020c040504030305060102010507090305070513020d020a0e090c040e0c07050313090605010306050f090606071a01090b1e010c080a1101050a020d060806 84
    0x107840d500c404108aa0180e0b000b800071aa9204001100002c0c014400f00040c41c45079104c4074410380d1500da400282d066001d0f0702004554079000c002c0d2504101a07040c842c1103800e21000030b03420b140030f02a0464205280c0000c00050580c960043c90040c0b1003030b0020821526150400c542e1190783e808007800e030341e0084108101506100b0114514044c0c10000141880911091802a64848031941c000a400c00410600918000304c1c402d40080b501c80a0500d41480c1c522441600030004155012440f8007003407000500c54240111f58075400003502c00030a59469103c158003c2200d4017a00d800646888404036813824442c03030381c031840b00300244862555555030082100a40c800c83e4211005403550210300802600b03044200c0c0a48114a00840c40b001c0c00001e20104109001000607489940000c50312240d070040c4c0c41c0d40c402038100f0011940c41460480507513403d0b4811814010a6103050100980c04905501401c0c004007452410701459036614038450343e81405481d40345104240e1440c803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 3552273 1250 3551023 3551027
    0x161106010b0d020708070c03050706110a0609030309050607030c08010603060305060f060d080a030207030e0a0605070b0601030b0d0506011502010608030a030f0b0d1410110702060304021206130b0105060a0e01 91
    0x2c0e10300e00020110151800103641d407101400c0e080720720202e402d0a60500144104042030100c0f0010741028608800403d40e00c81e40300d50703075204a010107088542c0e150018401e04d8441e81040ca0811342101c11540c0314204440010001d0568200c802c0000d100d48002261f001d20902860f07080342d400a00501c03040c2c540740751038180703880064440759100c081e6002c070b02c0000702500040c0c01d0741800c90300d0050700c80882e810b0180102010324842441005031200500506400c481940d4400b0340ac1000d05400342e90b14801a8020f02e4020100c07640b00b40c010007407600300800090000c0c1a11006011170801d038404420503802e950940c05000c5031a0001d1054850240c8258480754000f0451800411004400400b1401007500200141e035445013402d210007131000d0801c9041e50419582c0c408001924015580e040540100c40c00248140c03000004030f001d55440d50f1244554031092025100c0d60306000000389681d85805004482c4003161100010b414900780043d6000c220083e103408038010151401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 3553523 1250 3552273 3552277
    0xd240b0a0306050c120103050303070206011d0c0306011101020c010603031b0b010b0a050d0606080601030c09030308010605070507050306010e0702060f1303050c01020d0f0e0c0d080403060e0f03030c03161106010b 93
    0xb030100070743c81844041345035005d07004064002c40c0102d000d16988d0404141c000d0602c00305801c9107110284915082d181010908000c079440483c0318030868903a1140001240c5a0a4001c41c8851540c0041141541d031072040d84024102c0c0e100b910740c1c56001e4450350400060520811000d0400a440401000f0045030140140343d484880e1400794504811100f070117040382c5054005600180d00102000310950f007603c55100c40d007100741448071507a459070f90002c00e400e07814041c4204003d4041010300c2081810040507003d400d0080940b42c4560711010140c00f000c104452400040c4201c4000c10b81304400401d0141c045c0f201c03400c0805070544c40703850a5420380c0c02241d46032129913080050600c1440c3c40d114024014200e60008105c20184006451500c1074842402c2c5c07245098070180070008030004110b5007120361104010607131040451402d410240c0d01d84e601c8045000002c2040521400c4900546c804d103881c076a140701c2c185861004031140038840422107010b034080230041c44210307172000c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 3554773 1250 3553523 3553531
    0x8090102150405010b01080109140703020904020f0415080606030c030112020d21020d03020c0c040c03020f0409060504060e0708070c140d0c050c0d0302030d0b03010b0d240b0a030605 80
    0x1224032203601101e04546903103007240c040d14641d55501c4900669a8051071940c0140b60918042c0422813013005070319007207140582600c050603400100e0074401e446507010340700300c1c0c0c04522034503440755660f4600c074202d00411980000082c3e100340c00a1150320703007601503c0c05440d1345669107056038201403c0b900c0e0811070040699202c0200840030001440c01c01960f624410300200c80091140e0250010f80f030000c13541e5400d006d150045c400d0001d8104000341c043c41c07010b011107011502c0c4100f81d44c2603000303209203d00c400c510440050049131501d400d8104e034040f0341d42a01c00b081145c1e9615222007038200c0c10b0b41d008001401c503002048406205090712040507008655000d002c00b098501103243c0583c804030100803889941000c014048140603190308140d0648850300e0a40069030700a407244901c14401000c01e64a1015040c03a0305c00354007801d9102c84c00340061102d25401d003001d9444599108545840002004207940c0071006402081400000a028103030140e00b19956040a440014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 3556023 1250 3554773 3554777
    0xe0307060f06090c05070201020f06090c010c021503010602070315020a0e0111070e07030f0614030703080c0c090415150605030105060d0b04020703030504030207080304030503030106030203090109020d0c0801140c0304080901 98
    0xb0340c0850036103001e120303c0f014110301e61165544d40ca4148006410306000c2d4030b0203405508140100200d6110103c0c908082510074a41a02956001d1001901c50824030a480a5060300403002061140d0001078050659004e80c51103600c40014070b03041c40691003202d9003400010100c5882060a50248415200f1081002c0595008548070b400020300d500c01118480000f9803218250100c0071418030034500a481980e40c1078011560510120703135a0b0101c1c0c800101300701d10004140350303840d109000c0480310400080641c4903905203401c00c0c59140c40e01007010304400303252803500000f401507100d51004450140e100c2da0700b103a107408200001c940041180c9041652101c102c0192a030b610700c01403202381e00c2510006007074101400c0003442e210585d004180b290344101b0041c00401e000009030b07030440e11585001341e038a40c0c07400d00c050301501c0c00ea14002c1d08412918490720800c481104904140c0341d00d0802006528506040b1400d03240040c0d500320021a02040802c0120f82d442d0003c0134014018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 3557273 1250 3556023 3556031
    0x60c02030a0203060412090b070c06111501080309040501060806150a0c05100504050708030403080304060203060a150309060c020a030504030210051b01020405010f03050601050a030504050c0a0f09060503010e0307060f 95
    0x6038003c2802c0c094115001c0350300541c0d61103d461015000783c40c4a0280c40d012130003c0c1450000d94a0001c00320042c056a42070202c0f0300d4484c0f180c41e9080080b10007a1500d541c2002c0320b960340c0c0e05c04940d40e0700090301c0c452140b41002d001140e454894201c1900c1000002d0581c042c018521115010f03941c0410038034010031604d021140080b400400880910015002000541c1d190500340141401d17042d40000d441604100b10400100d030a210980341c21030342050300165241c6541000078004080365003c801c18407036040070100200d41682c4049011401a602400705800d0007500701c0c1c455800b00001008154188024000341c1441d07000c0c042c4000d031501b082c034644a141e4903a040c000c800303404000382ca603400007030a00c50380d40e002d9840c902c00b0000703003011701c91400c0c0540080c115010b807485a0040503940c20014041c4070f400c00104c403030304038040c108000082e103c669030030380c0c0c200d076000722850b0b00e040410025a5040521810303212040c020041e41c106003890392100e024040340c901c0110081d8403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 3558523 1250 3557273 3557293
    0x3060b120c01111212010503010b0306060102100509031308010b0909010e0d110c04060b040807050402030106050d090f120c0501050903070203060c0c070503011104090b1203030a020a030207051005190213060c0203 93
    0xc8103004200344240d040085d4500d600d041c08040c00d56100c2c0e15803d0098208000b03104a6980019650050448a00010929070f64034210b1510b940181c0401801c80761440000191900065000c0c000300c4105991099103544c4024015003603440d00a14144940c2c0840182d10101d4444d4103080b06100402064514164070b0303000080a59803a034000c007825980c005000c006170304080100c48010002964290f0071580740c032a019142d070141d01566480907440712072140c2000868031490a003164040981c80e610030081d10f0040040c4020181100c40d58070380b80221303640400020a44480300e5004000780003030b55450000682d0303030b009001c03140384a2166400100b8186d03004e005510b814000c0c11051b03601c0d180340401721820b0b0340851040c54040c102e052000004000c0c00b0080320343c40100702034090396806403003004400910401c90083d0150041140d0381c1803c0f80150032860141c0e030151914141e41865180103000ca2086100c8404d40080d40c900c104200e601524000199034001026140302400e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 3559773 1250 3558523 3558553
    0x312031f03020909030306090106090f0b0a02030d05010b09100306030203030706020903070e0103030c110607020109060503091011030702010e0d0903020904020d05010507020105090106080c0904150605180103060b120c0111 97
    0xf05440c204c08641022080251500301a191140100a1b500c0e2070100c461a088507000d90446500846142c03040019580c10103034001c0088400003180d1100401080da50760340001043cad044610f41c81d01ca20100c18007440d88a2280c02400c003600c0e0024003452a06026982e46030095000b1003506400d07004900c0006074652007855090700071070203034941e484010b102c0d01e000c05140000c140c01390703c9480144003010151340d0080e861405e4810a04006a072601c0d4003001c0da1404242d018414290307030910306103a040c00390b5a8050340c010200b940084c4440c2c252400300507160142c00100d07a0010f441c0550401c09841e20440c1c081e0818009008088040351030348a41c1d0941d9021104400540e444000780074620703000344142402080900e0182040c050000005201307440b0140002d400e504085045011101d0a60b012400a040041c10f030b41104a220a604200c00c000f4402a03c4140c94042542014101108250b40c41002d0310003134401c040f014001595a4480c0b0012841248214285000449 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 3561023 1250 3559773 3559789
    0x3090106030f0f030305160c032001060b04050a06031e050606120705090a050105030106020d03051504090b040c0509060f041802060c070f0801020f09060703020a020a06030501090b0312031f0302 85
    0x94003a80b229000c01c1c405040c01740c20341310082e00440315000c0d0301100d001d90550080d040350030141c1c9442c0c40b40101c8120708240c20b510000780782421080d403130082d00043d0401d001c07008000b110810358250341d0320380c1d80d00c0d02035040b40c1c00d544034809581022560000400503550100790701400c000d1800f42004040e510150940790f040741c1402c04544c000030f016403d0316104461034014002407804600d558109038000b500e840100d200c0c1d0b418143c0b00c1000c2214040c005d501d0b01c84104014208020701c0400d4100518050403d5031306403000c0ca848a1701140c181404c0c0b252511400e405444000e135014924148030040940750310042a00700b00824000c0140c2d112001045200301000081c1582400c0400042048416600c8400107a02c100300c2024054100c609944241c0c0d4111442a100c058505060341080f40d9014000e510460000303001c02d225404cc0d202c00d05a40c2029020040844050149503032449031060b42c0540600620000f03501d00080b60701c10f14001c0141190540066881d030100c0e0441d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 3562273 1250 3561023 3561053
    0x3030304020d151104140406032a03050d0503040c0b0a0f110307060e0303070e0d0c1707080105010801050a0f1401050405060a12050a0308070504150c0f05030d06030302010c0908030f0309010603 85
    0x1134400024100142c440c100e80703c4195803401c807030401c45140345660b5842000c00044203004280401001000611880c2811030010368102058a030600d00c411401041c2c0d40c4221005c0341c041c03210380d9001c104c62440c0e4096654115680c0c1f40c4800d98003401c1000c0d64420414a64034065100c2048014001000c1e4004e204070701d40e00000440c3c503802d010002501c0d007002d100c13415006640d00a601004201c0c03035040c2c601103c4821840c20b82021584282905107500c64124141d690b00306400001d410a055101078172800c80c0110401c5031824202154041c6d5501c0c030350601503010a02d00600192030aa80215041a001030100d20620750f9901d0368015002e1922081d980340e00016007030800d05400c000080d83c4040c3c0340c6803041c64541403c0980510f0748540c0c4000c420401b4007a02a01003005698100320401c0e0031a0860381ca80302901a0040544042d0100310019424851034000150003004000c0a8030003d40265080100c84400d0500a40000340005190b6484601c0003010981c0808140c2c18 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 3563523 1250 3562273 3562301
    0x22a0310060305010b0102031e0306030312090601030201031506080f0c04090f0603050c0901030c06030c030207020402040305011a0108090c04050901090206030f0a050c180108070306080106120501060803040503030304020d15 98
    0x1000c2c0c40c41c01c24908503030148500c981950410818142485d51090480820000710016180c89072035040102c0e185000344051948540b00a00c02c0c0f1020070000503c1504a9100740c0c0c080c0640d80005040443c5040144902ca020440708030201d1143e00015021650005a104980c0c1c145aa25014441694441101205100c0e80d0346814018006e082c01124000e5105035054200395141d0740ea00641c0d20924443c4000b05540d4a4540c0340d118401c4c0c0481303502c42d4000300b0641d210354803414034a00902c2850030b1000f508200c080030004650081c0f07412407050030b800000d000b6400b07a407814071002d0180101101055565480711034010b955a40c051800707201c07411825003ca240c140224021031760042c00c48440600e0a00201e02d00048010b280c2042c901e0a1030503000307644880341d064014140503009401755508000c80420300450702248108168010f4000380a4560360b00201074480c81036004032070301500304100240c09410b01c03404070000d4510030049140d0008115040c00d0031234030035034203103e9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 3564773 1250 3563523 3563531
    0x11030d02120105030706020703030809070302190602010b0d030203040909031404031a07050403050c01120e060c0901140c0601050f010c050607020c0a0806070807030f06030206070605060108010e07022a0310 90
    0x748441003440c518058a0254020012142801c001a665400303d10005007046208000545030500c1480100000e55020781b00d01e486120413070805c55212142d014460040d80f0305002c180040c50031000d9081d1070394240e00076502d068149098000a454100000ea0070b01440c0070307083c40c0026980005100031030280e10910003650000408001082018007a04200a0144000d001007680440c84110000c800d0070103080d50740403907003110041c0480c1d43c50750354075000c0e04c020441e60340586001000303826802d980302d05402a1501010f419401034054101c91548a00300610660501d0941d0523454101410415071024855070340034900201240d8240041c1c10401c950041414101d0014010301170400103001030b4581007038001c200340c000030708034010151500d00301c1c400d10400354488000b454000d00b81503070b40c024608081c0098403017616102c1c00a507511000280101152441c3c43c0912000d81c0600444d050031a810242c0c1103064101940f02002d07609143c2065808005c40340503001400b07000300b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 3566023 1250 3564773 3564787
    0xe0910120809011818050601090504020d0605030705060f0301090c02030919030b07030207050303160e04020c060105090f0601020607050a020c040e0d0201050108030901050a18030209040f0605090304030f0b04020111030d02 97
    0x41c803058001c05200104c3d00c0c1c0e454144403298002040c20704500c039032107002a0581d40d00c40100c83c20802517000710382040c40010180001c4603550408410313140250216140d490b0740d081401650700c110441c0f0301c200101840144149140c54102d031004600510490341403142000015040700e049520b07000d01641e02d001c00b00200300881c0b60301940813071103007003c508000786521560f88920000301090803200711644c1040d000c6000c0c0139500c0e282000540210b449000030150641c0c0c450081c02920300c548410400250f0307040900c118184161010303801b0f08400d4071414000d8070382e50804d038012400c3d0701600f0b1131081d064507075104405030041c1005c01012064545a0b0103401c640040c0c203c410550000c01044941766003110072201c3d0030046140102d0003c0c82a18034035031805c0d403500000e6100c00349805001c22300401c552905c00032800342d4800c018a4460760f00b220394a00c20f0344001880781d04460b103204041243e40c04142d900c1401814039101c8651041040c0e825540004027401000794041004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 3567273 1250 3566023 3566027
    0x120103050c0402070305030a0e070e0106020106230609060d060b0a0e01030b04060509011403070306050709051e0a030b060607140609010617070306050709080a030203040504110304030e091012080901 87
    0x499001d4401d803021868600d003034400030500c0c0300c003c0072045096200c014074025244c0800020b0010100c5060495003541c40741c0000f8003800082c072a00080c55412a03229801e0120301400d02c8882000419051a1100900620665400944905410741d9640c903002500c031070144024a801e0465550303940e807840540700058200c40030382c04820f010710303c0d00ca002d01c801d44481070043d0650780801901f5055000d403c0c0001d2810f0300b5504020200703402d00e810f2009681e0408259801d0316001c13540e15091036003880c0c0068000c0410680740c0c1c3e00c01c405007400c002080e00c6460584e0080405803501d45000040e4171140380c25164101c43c803540303610110070081302d0b000c03e20895001e44241400c044046040300401d40e511002400007819181d0303102d02090455010309140e50042403500c090b500d00400c1d500b40a91290031900c500d038043c60904030000b04008030390782101d1190740c0c507440c1c0600400c1d00d24203000e070090004000e0400b5089400c00404c01708030304541070001c10b100b40d501030340c0e4031000000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 3568523 1250 3567273 3567283
    0xa05090a0e06030a03030e030702130c0f180902030703021603020604030908010e030304021207030506010b07020102060a06050303070f0302010b04110306030f060108060f04030e0603010b1806090a0603020903010204030812010305 100
    0x7456105001d0010b10215940104004d148183c06140105409442c500081d06600c1042002035003c0d204d0904007800c2400da40040082e000d0729140e6411980d40240c0588001c00c00300080300078071800c807200b40a100d446034090b5420004074980103050035010410b07489203000d240c1080e005a44407400b0002010341c002c05982c003805124000340840401d140b502c641d2170001410091040090990902e00664104007000c01942c10600321021075039100300500e400e82c058074050b0b0040c007078007000418010082c00703080210f075006001180341c0700a43d100c0d20802c10390020118119500c401c1802d1495a442c06003e4401c40c0040c2e600c1c0d580c0c1051000c01d45803020403c04051b594103c42c0040102140200720a54000084220340441d50307a0751400f01c41803031008141c01e40c043c00110010421701e141c00c000d0101102030400745150b8490f4482008500c0c02001070701c1e03038000c503092001d10001d4465009884a03840180025040603201da5030081580c000c00480d4204c1070711140100300317004042003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 3569773 1250 3568523 3568529
    0x60408011509061401051b0102070b07030e06060901030b040309030803010906050a1202060307050c030d050f0f090f03090607060f090501090b01150804080708120702010e0c060408070e18030a05090a 87
    0x38007040004c2c0f0300800c854199135244040c41c1032060200f1000b91190050a005490a1802c002155500f48074a0010140300d0280d480c4c200003403600055488282c1c0018440d401640c0c014244140c40c1c2c0b07140e80742c5c0c2803940001c10450400482040c0000054031801c09180604414003001c2995403c050a11010010592111000d110480320000c0940c840c6012641c003c541480c010769202c0341c1c51075803880c0d0f00c950050082c04501c1d0108101140e0101c050250099a00a807040c0c02d81c4c81d14500281c2d9207040412012580e0420020760056140071001401ca42d0301c034203004075020346080c018804030fa03810b9800340c6803039441c5d11045080110070344035240500755511445490480d900c1c4000c0014000600003132007a540003c10b1418421745c1c3c001c1c0d07044060755550b00d440d6450852402070192048020521580c4608004020503161000a4170260307410180101041480e200c824505000c01600c0507a04410030000c00030034003c2131004015105294032047e40c0c45050200b80110035140e0380c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 3571023 1250 3569773 3569789
    0x909030201090b0403030c0e18010909050a120302040f080102030f0106030c0207030516060212030108060109110d051503010b010309050606040b01031812020c040501050f0405040312021b01050c03040302030301060f020307020604080115 103
    0x1d209c03800c2076098100b1280c156080304500103503004a81c94250b161101d4000301806d42868210044142585070300204181d03002c8102c0c07040b94030f40d980d0040b1300740d00041d103d640e002e000030401802018070a03405000d40c50983c1c81140c4880356680c98030340c02d2584e1903584501d039060110b001d00407e9010020010f00c420382c0307840145150314250140e03407030b1041130150b01095901d4416401090f2104010351300f510707041400821881c00e0502c50721340d080d5164000c2034000e5007052800340c401d40c000c1c0b285008141e040310150042d6a0303081e081100904910340301c1414180d075402e410100380040c56100c185144542c43d4940d0301869008041c1c506003e031600b4034800da0614005103c41e45070841901401c1c81c059402003140c0d112458242c0301d041103044c031041500d01c04590340c110030410b104594040c0e0100c0008212a8640340c061003040c3c4401c603400350150380104010003086106440051802019105480c28280b09500043c900d5210342d01c0189582c2d1607030200300a0b100080784c0c0308020721501e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 3572273 1250 3571023 3571039
    0x6091104060c140703080f0306031204050f010c020301020714031308010b011b030e060315090a050c04050d0c0503060705030f06010801030201020d0e120a030801030b0705130909030201090b0403030c0e 88
    0x10040080090040703a4004080d005401801158100f00308203940146520130100d40c0c5035019400f041c1581d400455000303100e03104041c40e00101c40902411074054507005850300441001038801940d0140c4c1c1d400e800c0b40c0640d420000c05010075810322098995400010141d9502e0220122600411006070000c0c4181d915200b108c1402d81c0e0045e88050541c41070803100c1d24420303010300f0140d600c2c82c6285915500075100000b082aa540117041c0d0070042c007030440d1200c9140c2c440d07918100c21194200c9017122035090800c810700c400d20307041d407032952000d22a0602c1d40745140c60380042414a00266100b102041022090106501c2d060001c1a031002e000c1c43d103000a90324540001356035010000c100410300620b1256107660b034603900c2d40008258410b0048030340c0c0084600e0000c025071400d100c20382d03401d10a50081881c4910610854070a1540f20000d656850f091814000043c0351013074080b403d66682d00d00450000d80f666402a1259020340c400240901c65014040c000d0350a1100491240c0d001d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 3573523 1250 3572273 3572279
    0x1020303010302040902040f09050609100203220203070801060308031005010f1d040e0604050a0c08030703090605132c010b09010c200a090f0615020309010e01030209060a0306091104 80
    0x4008152030440350110f5002c03d200c1c086001140040c41090008041d80c1c4c20295100240030000401501940700310044959450701034000da0120f01050700c124040b16a14404105802c5200c031480d04c41d94001000d44d41c07050350ba40c40903821150305a100301c90340b00001c010000d000701000821002080203082c80034032061800300081800204403110502c04040451704a603c3e11b03070703038005a004650402125030500341801d02d1941c8160500086603038030314040c404520700b40013009440c0400d40c951100c01c10315007028415a01c9411241d2421614940c0000c0000c0d4030707241d07818605c0d4420704038504040340500e60920207040b0b407058200346c0a04800300510015039078000174038003400390044003030240c0f401081d2a1408031110b80c1740d240e0340b080b00071501007504105603000c209030b9109100c0400c0f02e55991801504094580c40c415005078000380075520055010b0341d0158020801454018a4016080b00240f02a0400700c20754001a5542030148000c82951040c2c60107011011492818103103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 3574773 1250 3573523 3573527
    0xe010905090601121107080702040501050a03031205041e030e03060a05010b070f02061603080f060109060807080a060906060c110409080a0f0513060309020f0405010803090609031204030503042301 86
    0x81c01401c014100301500c00d8103048040540d000398141e00c00043d00e95030300d000505000780c0581001a0691046140000015140c80c05012010849900d41c45480703060070405071400083c000100142d400400c0c03c01a07004a070b8060044c949454420b85441034070000381c405140c940400242101001c610b0040180b01581000d01901c20440d40041d000d0b00c072001c01d1021900ca401022022003c4901030404a402c058202014501c51040700080310080d507690701c01120b00309903500c500008100d00300c0100324198881c800702d950101000c100031800b165aa40240129900c950245001441441c868010081005505405660100c40034000d04810351500308251081d00000000d100d040402d030f07500d003400340c003c1c0c070070100c4003d1118003016136a1301d010340070784140c0a040b031103000f843c8985552458203124490588501b24015804c107592034007845141d900c01c030005603051041042125000800c200140007440c401c0020310b4030b4514040b0080e14070f004462420b010941090003004544e6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 3576023 1250 3574773 3574789
    0xf030301120302010b090703020301080d02010603020913062003070f0203040b04050108040c090501080a060b04020c15070903080d0b0306220f030e0306040308071407031b0302030f0d050402010e010905 88
    0x8090380c001003403078046032406a00418462090300d0700101907508211240350194007075812244034409a46000481c00b904030f00320f60721400000c2d030010300203000c50b4903402c00b00d000c40002c902c5008000343c526440c40c250b8144242c55071012407a0b500c0081000099548403050b0041e107070040c001981481e04114a40c0da06000718020241001b52040008052000702c0020200501c140b40c3c0400c15540c403010241c1e210b00d81411301340c031254242070101080c1d05140c400c5a55120440019102222040010070140007001c0e015074200406640b0120104650b00c000740b248100c0007800181d000414030502d401c241000b0b21082040480501003006000350010f504400f5a10032018216640c9606c3d09582c0c2800c100c2c09c00350544181ea040004050f001044580142020340b140030400035600e100078454412004010b0010f034148510503500108542c1681c5800c0c032a006490070300740c17100e03140e0320a50001040e101c2d03015200d00a002c150b50300050607050648080c03030a60091410030011901c05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 3577273 1250 3576023 3576029
    0xa08040b0304032106050301051005090a0c0302041503020309010e031608090a030606090e060f090c060f0705030307180f03030807080403030e06010f03020406050307060c03050f0408060c03010905090f030301 91
    0x100c500040041c00b003501c40c0312040290348281d00013403141010201140001c1c0a02d0207600d0207586002c0200d0b00c19085005841e007142c1c0001c01c070100d80d0741c0c0c1c801381c1030250141d082000141074007844046041c4480c45211201c220180c1d60041e101d14007505100e0039251074401400641e003040000d4411040c291441610060b00180030070f40d41c4070f0aa01003808154164005007806150201c041091040d541206140d416048202c90860301d4a5083c16188201aa94084941d006413495100d606141c40901503202c5071000c40d6040049a45809055600c01c5641d540060107210b160603001c1c41030003c10025022031102a1646825070340c004e08035a1024020b142845200d0000408041c800d80210788140e41103800c1e9083c07540d5921080c00851640d0000700d2080341003402c04980381c14005104421241c01c3d96406100c0703507403520181d03419400b1340341859401604210204129008201c1203010f02940701181d83e0742e61500b80901d04507480500701c40c2041e004504210028100002502c0c15 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 3578523 1250 3577273 3577289
    0x50402010c0221030304081b0c031e0a060204030602030603060c090901050904020f030a06020a0f020102120403050307090f0f030b160c020f03010609110a02010e0d020303070e150c011506020a0804 86
    0x1184038503d115582c4519041103110301c13803000204010821030b0b84170141c0005451800c43d1004022111221522180d2160300290942d0100910440d00e0184001981e5610040019142c40c43c0050b12070b03e00743c2e807040d0000d6030358031340000900040e8117080228540c04102040aa42000b000c14005400950188200ca204505145c04203056585200082a1596004084074104001803030068007079008400c12001064440303445040d5140180202d82c40486012800003040d540e0b59000e607071a400c05081041007060601021850420b004241e40c0904004e081c4500c0c03092946c60041655100101468018141040300301110b44c1c1210322248000e50480e81c4000100c03900010a004028551001c10000d051840e07121064101030000d00b4000007a80c005d0151540d019038143c2d42c1e052240031000180d0041000030307690b0f8400d18811340c00000003050b8550000902c04a144c0f16004400c0c1301c1e489940d10072010b11b800d1b08010000005100c0c500292003134005c1c548070700070240034500c22020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 3579773 1250 3578523 3578539
    0x70507020f01031d0604020f010903051f020702030706020303270d030b011e030519050c040902090303040f030303290a09020f07050703050a030906030510090207030c05010c03091104050402010c02 86
    0x185a0f0198000d0b50140c0c500e80e0340400324143c6040210780c2d90030155002c1c1e01511407098010059446201ea12041e81d03007240c01800f101c0c0880b0794100ca240c1c100c00881842076400c0c006200140d400b03018000041946600450310307400c000380312440301614840103074150300d000b001701d030701d031280c0800c3e110040c006a00b00000e50204030801a2048980d5007981c000c04880794100304076245c0c2503809103000e05481d00c01415454202c0f10b0680481e00107460b040445507091100f040361040540052190100103000c4e6801c0c02eaa541c80d01d541000280c000f00c0c00b198581312042800a03007403444008040121030701180f0034076100d0120311041514003503042c109400190240c240c8403202c003100c42c69507000c000ca038140d6a032818485c3c3c54030044c4100710002140c0031400680345100f07000d603038003a41e07040320281507035850041003c0c001d5000180c100c0c01d2100084000000c503500b071007050103950090300d003c80c01c4c0d00c01c0d01e4124230840c0c8460045118924000c180710260764481200500305505541d040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 3581023 1250 3579773 3579799
    0x14030604091403070c0504140105090903070b0406021903060302060412020607020d11030d0c030806090403020a05060702010f060905010f0902130305060403020a060b0121150509130b0105010807050702 88
    0x40141c5101c010103002c008010404109070301d800401490380354043ca00f00f03001310303898500704002c4d91101d40c3c540800705a1301c8018070003072410410040d0000420001c80e03190594503965a007500004072030a403155680400d07907011030500d425085201210500d803c109481c115800940540114060a1003400014103d40c0440d161201102e40c401e4000300100303002030441c9069007410007449104c60081c080d0a407a803a25501a0b000300c0ba0b111352607181c2d082540d5034041030014407072005001f07030114482d0f19202004220180044d500030f020702c0e4004a0651080d85412040d0b885603401101c004d840c001c0100315120b640c1440c0b4098600200340560b4942110a14108100381a0000380003130080c1e10a00c82015000038000d080725201340c4d000c2c42018560030040d0342e180d4030782e05000d040d6020b803007071221251141d510110f041141021f9402e0641c2e1154040703803141404071207400c0d90030140349001c0141300000d044280101024078040f5418500020003c056010f0610024000c0d84a10121 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 3582273 1250 3581023 3581029
    0x51f0207020a031401060f0f0603050402011e08010e090d02060f0402010c020603090606010e040504030804020409060609060602070e010e0702030f13050d060207150e0c0603100e010b070b010602030406140306 91
    0x240d100980051102005544904201c4401008641d00d00100d41c6441400101000112152403c56028640510b1168a008001e901400c40240f04038104820420718218407070403044c004058051076a108141503061142c00200582d029000034010340c4440d20f500b42040e40002c0c0d60b0f61080030818201201d480f5480140c0380034203030210080d0702101c04810401d280c203001552602c1110260384d0542c1040a010600084403000d1300c010340000d424030b00103005414030f50080c4104511541000400710f9841c003620302114840c2c1c10000044e00f02d504100480072401400b40d02601a410451956081c420b01c0a940c03803249400c441e03400080440c80341c080110210482c401804080c0001030545e04a1400303000030351020b402207420350210000e500701b18205104020011000d80000c0400c01c001c1410002290002002500c031005054008514a000f05180030300070681921050b4541c212031a0003074030a00160080300c01c6610a020821103158010140200d421741443c03c150341e51118804 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 3583523 1250 3582273 3582277
    0x30f03091207380403171602060408010f0506030304050109050d03020a060507050c0d09060203160c080316020307080105060604030201050a1205040503040602011a060d0b030f0d020709060e04051f02 87
    0x60000301c11008030b00f840070f00e1104012035007500070381002080321040c88100f180740280d00010306600b0070031302445100c0403d50b0003003403035091041030309900f41200c1d03000558942c080d0b003180c0d0a40c1d440ea500340892f1142030241c150020000c5015504060400000030150007291207524411012240244240760083c0131002469400c58010b101500c0c0510001c0e0081c0c0c002254a02103109081030984101d01c10840c08046e160194041c51800850581c101081c42d0712180c140c607060214600000e944008000404005224018042e03d0082e10700400d81001c805038440042030741014200302507036855038200ea0a480e42424040d0301c4084500c800c4441e484c202d01d400e001280340400740801c2c0309001015108407502c56009115030041c402080c0c0181c0785c20030744584c00071800e112881c000b60881d009415038200140403111403c80e40d2036220300d41501040c249025800045003400407200c1030140f100540108412090281099511990b4036007581110481e1007040d003000002000580d01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 3584773 1250 3583523 3583529
    0x20913080d0204080106031104140c0306030f1b0f090112020112020702030604030206041b06080a09060b0303040306020301050a090207080306010f020705060408100507020106050d06020307090902030f040201030b030f03091207 99
    0x18110f444546606606000740000e02080d244008000c81030003141c5005c3c015044985404104841b154031102032101681d080540701c0c581c14000c90145041c3d60200b041810801d0088040c00840d007040c1c50188107000039005076284c0600c800d0401400030001095503940c00c56420302e82206140da01040c21002030050103402907050207980188000c0c15800910dd5008a0040d00c501c1039441d240100b2030f0a00c04070f4030825001c900040005210b5040c45d901400c0014028034000c100c0f078010300c0c0082e0440d88140c108a0b0b5480c1e0100040c4800d041140500015284001003145000c02d152641465400010a5141008806000f006a8078428081c0708020b1001400f916101c9403070700c00194440e40c1400c00c025000d860140010045881402858120394000d002d00380d4201e041e45a00029500003030004041c09032106000031400c1c030903c0190f00c6140e042d91100c410b0305140c400101501c000c403031090f01c032f54091032181c02d001c600031046490b0034104441c0d150040d2220042c060406140d64 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 3586023 1250 3584773 3584797
    0x50304081201090c030b03010507021b1203040b040609080c060405040213090f0c1e08070503041406010f030201080a0902090604020702040612060603020102120c1e0f0111090102011802091308 84
    0x1c000000d03041e46603007100d4034100480d10284800d0340420145800c9500807503d040060b4000910124140c002d102e0081c0700c08000703040211520350280207249113522170380c0700101804000508021041c2d00070f072090080d01c0140090007410313400c200060194040e5000d0240300b40d900142183c029000744840c00000c2080c00d2042c030088a041e01203c00401094403d1004a5405080c070403510201e00700c5681e200f94151945000d1340c640703c02c1116280c2000300704452444804004545040e820011140203218291300c05542c0ba09510005045540107000c094541d81049000300048ea24030084651200f02500c0058072203a0b176000140c0602604c0d07000c640c1c2d4900b081402c90a00c42c0d030341c21000949000307030211781e00502d00b88000c00e04e03441640e0b0f0003400c1c2d0304401040d913007101080580c4010b8107070340b004984030842d440e0340140c2103c2d1105114200103600144100b09942c0a0062060302c1c001088910dc100d40c0c1c54001c01e0b00b103030b801400e011003460100b285c10104080d03042070f076020b4a540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 3587273 1250 3586023 3586057
    0x2070c0602060106110102070206030c0703092706061704080901020102040302040204030c0302040e03030702060601051e03070306180603020102030409090303060e0f0601030617030d09020105040b07030905090612070605030408 99
    0x103040065201d040a004100001e0b804e00c00005541e6414000c070f480807a070242c0f1031443c681d5020b803580301d2908032200860801140d014001121460305d0320502c60310340b013a08442c0904000c41d80e602e0888819a01c044140581c07600301e0003020449a0201d03620035002440c140e41d882d6800700403070081c030070b0b030b04025401032000c28084140585820403078260307442034a081100000001507a641d03030004540650040c1d20500000710154420400b5110020340e007480420701d00200070940c402e9400c1110801c00180c0c0e100810860b0b02016111042407000090041080a04540000b9200d2181e402170801040c3c5580c494410180300f503000758010050310b100c14100342004007400d00f20001c00c5d2580783c0000d050650206250581030340302141e1044140c02540740090701704d180e0340076040030318060303043c00720500002904640910081c40000d200740d40d41c035003031410941000441b49010308400c0c022032003048030150704840011200144c4645080a680b680d59620b00b4101728440c01085103208825 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 3588523 1250 3587273 3587279
    0x8061f05040302030c06030c03070309020f04021813060506040e090f0a05030a02060a06050f10090503100603061401030203030a080a0b040204030308010501080f0c0301051309080a0804020306010b040311060d02070c 94
    0x3001001e882920b01c21810380d4a00203c500400080740410f540c03001000b1802c1000c120500d009a00007181248098800c050400761382000500320703044070101c41440c00000070304801718a01150600101c001103034040150300d0518020074964003481c0140045110030001040c00f503d020002c140d03007030034650100c81d20b840765482e0203503d1303411102d00800980b081c2e0010407141c615500800c0309499018040548800b080300800151400d01c41c0d41c8018040580804500d9032010b10800760344440902000c04c0301e0385945064021220700301078803941c410242005000581d000b0045407140c08407846c0075142611144101c0d8020310907045a01c0e07105200003400410590481c885034102c0d80240c88901c060380d1202c1c1c4440b030f0050101ca4513a007100f0f0820044c0540d03e01007001507920550548005050a0309988282c110390001214401242901c0100300c01c514080200502516500c03010a08092a65845120040800002034441c0c240488c62500040c11075054500080c1c01041102000307035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 3589773 1250 3588523 3588527
    0x9090a030206010902040503101a0307090b120a0206030703051e040303200702101d0d05010501031e151d01050703050601020f010204050612040303020702031c0e010f0e0108061f 78
    0x240420480c098041e600000503009864800d580803504050061b011040140c0030702e000500003140c880d203203000410034404440d1402c0010364050034411500040880190040224084140044203100c2d4400c0c03030502d00503117420055036048003072804c020400d521925660ba80e035041c62000032010341c58640030002410b03416040110b04030034122096007a5140d0b55a000b070030b8070400030003070340211000820101c498429045106841070300d01d20360b680824070400007803070060300e280d060354687c7d115001401402500030b0313181c83c1c1c0b4850320522614800d8990341c1e62b2240c4090108051810340c0d8507020003010150583c49039040840307000810035403601c1036000c0c0c001c1c14203550030390040c4180d101704940b00a0500c00c440036100e00074600c81c10212000310b60056118014000c07400c240c0c0034040c200050710704201c10140c034200c20702610714243c0104801005503002d6070380c03641005480c401034802c894124082e001c0cbe00d84e0270719050500c0d69613000440d000341544200d03148a00360100c0e132205090313 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 3591023 1250 3589773 3589783
    0x30d0c03170403020a0209070908070602011a010203041a0a090b0307020a050d08010501120e030d020408030a0311040e010302040e0a020a06030e060603030a080105010c030306050301050a05180a05070909030e0909 93
    0x34801d488a1441118030390000c0d60740300e4100d9000b8050780c4810340710000b600d40915515404134151800000036610382e0440c1d410701503654411000351703440343d0b5400c0148588603801e11003500c0c01c2c401141400d25248141c400d90300c2d00c0400540c085400036504c64281c1c4620203050240c2500005542c3e2410041c00096480e06400415103103030154815880d582441703440e400d4100c8405070b5074074034179003100c40c4441c0041040125a008074030041000d51004111400a44002c1600002660b11000f0044015013900d1500070000308001003000b00f40001e4411840c60b5041d2901920002000080c003a0098540513080001952068180500003080740d40341e0414002c1f40c90322000e450007603c81100785130b600d01548650b0404103d1110050bc81540319002d81e00c410303402b07440c01089865881c400302c1e08541c01950701e60381154440013042220244584020342e65000d00c802041e038495030b5141c05031201000d0080034415600c2d200800141481401c0428075074400600c40035841c10249c404640e50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 3592273 1250 3591023 3591047
    0x8060123040e010e0906040302340e070f09050a060507022701090617060601030e0718020909090d08010b090604030206030f011a070c0b0d0608012c0102070201020a02130902030d 78
    0x4d042000146a0b40d5020071118000c680c10380090103105214104039200c0807903603036410458006040654020000741d01c0311801025035803d0340c400c5080c00e0400900039208022031205100e21000700300300c41e4551442d504121045c501e4119140e1105200041d074941602c0e54507a0082c1400c0c032507550100e0303002d092a049804c945000c1041d180d0311b0102140c41c407406581c0712000d4101701d000810650203600100b2454042a0a43ea80706c4d441d0ba0f55100c40483e030b0000c41a0140c0e0104141900d41401625541c010a50703000410300000c030580020300d052814003c1c1d5100c0e801c00f040c8a00c0546a480030348000c0c4d640240034940301d1810b486000c80c2005d00748192060a2100d00c04030300c1d41c1031078100310f42c2c0d0140c121007401521800c05000c0704035540000052480f05070384280c001250002131082c90406010823500070405144034611a102540713508810350982d104121400c0180e0300010040c10045d81030702d180001500c3c0c040e591000b070064060180d050701403107010842266200070b584c000303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 3593523 1250 3592273 3592289
    0x7050406050102010915090305040b0309010905010536012c0606010507050304090207030c0218040302060105060301060905090c090402220b03010302010903080304020409120c05120a08060123040e01 87
    0x3a41c1c8100482c241c440201c0c01078840850031010b107100700c00c0c0d90000c1801e5400303030a105203096507407103080310305500c21501c000c40c0703940d0360b2103841c1000030070700410b900903081e40c1c0e40ca0041c002030075a80042620001e01a4900842501c602c1ea5902e02900806100100e011492003156107584400d0400501031500701c5050080b000002c41c40c1d80504103866005801000443c105410220560025030010038140d00b486400305020005994960078074100c818529150741003414585000ba25210040e00645e10400041c801030041c251320007503260444208a83d081e0464494007620051881101d840c9500300380002400800c0c101c0b424410a1004101c1403075030078066807041d404070745000c2808024006620a00200f01045890020b1070708540010130001360641c5e0ba40c0d4241001d030311500a4000b10f040882c0300300500c602400a80c0f11985202c0c0014a88240386c04020101d51009080341d0600901c3d01e420613031110410348035010803050a102c20380da20b0301c42010024240c0d0034412020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 3594773 1250 3593523 3593531
    0x30c020f010e030403030507050a0204050411030c010305091903090801020c0706110a020105040b0a030e0d0e01030f05040f080304080d050a0204050a050105070b0414030c0303161106070903020d03050f0309070504 93
    0x400d080052140008001a0102071400c0509660f01202c081e400b81e1010f4419100300c80070400560703106d1159600551040c1c01c87c41c0d206020806041c14908101c1842c1d061618080030844480070116000c0d801010280000b070b08040d0501c2c055440f080345410044007580301085458125000280010660b10071f91240f904003a004a4120340d581404ca2000380011000e100c10002c50f00d50300c001e070440000c40d003804590b64401c1282d9528244c20305078100006003180e840d529065070980f042c03442d4071041041c04e02c00c2d86040c1e15402e000b403101000003070498000000203014082c64005540021820190030710480c10100c03c484081d4000c0c1c000e040c410000035030001055801201155070b42a4045500241c03a600c5484038840303103690702142019400304000c11403000c072052005611400602005400602000c040180074030440e00900f0842c2c0c1c0500d06006801c1c3e041006502241c0c0e0455400d50400e03400d107421690741c040c0180d880100c24011085c0401d050011031040142c403001c0d20700304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 3596023 1250 3594773 3594793
    0xa021207030f0308060f060a08010612090816030e0d0302010605030606010305013204090605100503030a021b030106090c0809060a1503020103020702040204050303030c0d110301030b0a020307030912030c02 90
    0x54840c4450321004121008020740c040000e40038054559000d90001d01c000f486004960200720683e2240c0d14030340014101400500203150401d21075412255101801c21009200b07544007000b0380705500150004c40b8070491b001003010311600a03030015101c0a40403070082c0c215850042d018042d60300601d071203801148001000340d4070078400c507812225140c03a4a42600c0c2e0f26204d0141e0151900c84400c20714070301d81c007500417903103542c0600d280b000d20030030300010a07281c00e4185000c2d9038541d800007817203504100200c0350055800134030303050141e1600000fa4031148800002074010080ca0b440340480c18189404031303c0b52500211100e01c550140d00698003d0f6452011820864100825075401c03510507610920265100350b003d099010300c0a8401481e040c4c941000a207943c10481e610304a294001540719080c00c0c04d0301410b81885940742000e07007554115604c0b400044070042a2110840d030200025520b50710035041440e403d81c0007825004248080d135802400b41c201c81d0800c80142c41046006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 3597130 1107 3596023 3596059
    0x70302090903120a02040503030a080a0b0d030f020c09010f150201060b030f04020111060c030606070807060524010801050609040507020f0706050a08060d0b010306020307020307080c0a02 82
    0x6544034084000410030b0180c00400304d004030360050008201710344001017035442c1c40245051948580d900e2251407001407100089a40d0b00803030b581c01600515402c00e00000644407907a0035102c40032050303014080c408500384945a04160380030400c00c00c9103011080000000c1d040e10020580d281d44140c07002054100780c1b1141d003038000134800d105c219a049201007051011900140c14289482003503055240130041c0308034003900c1e0000c1c96004000206e81281c00c42644070fa42005582031001c5000a1210561030140c04d190100b10110b11540c0a003150504840c0c1c0100b40610700201041400041c3c00c1c041c242a080d072080e0011685003107070521a84015010b56030f1003940f22041c4035001440380c10094451401a4101d640d150b000c581060034481c1500e802c4080540c0e0b035115030360120300d18410034101414110001c200612101c1c400b10385041500d000703d44e142c0300c90940c8030078 = true := by decide +kernel

theorem cover : BRFrame.Cov 3417273 3597130 := by
  have h0 := BRFrame.cov_init 3417273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3417273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 3417273 ≤ n) (h2 : n < 3597130) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
