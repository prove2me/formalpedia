-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3119
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:43:04.105927+00:00
-- url     : https://prove2.me/submissions/d0134761-746e-4e0a-a8ee-2478c32aad25

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 560791366 ≤ n < 560971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 560792616 1250 560791366 560791373
    0x9030e06073f082703030a0612020105030106031a040507030c080108010501030f03180e0403030b0f0102010614041e02130512120f0c01020c0a0b07090b0705032506140103 75
    0x203404152038008648480342c03203003920448000c0d61000074100f40f030a03058030760f034445000141410fa4070b0010b4030488003880c2c0c035104050003c081d50040c2d00f800410000b103a6174104940801005003c0240440c01c02d000401c61940207a104550403100e440c4000e0111884038000740480c1d80440c0e422021a40c0e80c16208009a40322011501410081c4001c201c6941182c980e0082107405020040400ca5040c0010001e08501640200204104420303242c190800f4500a0054846102410b00480da90041c840b030942c8140542c030100c41150030490b0103020782c1c00034040030301900c120b8160142d0020003040360076061803000780007001204000f0240036040c5010400e5000c0b203042d07078003150f0344049010010b9004802c21a8000c00d040c040040d950a0505200e501901504204078918090300d2107481c01d0125081d4198420502c0d40c0e9510000d980303801750190240503108015242d0b030b0060016859048000484289621080d604842e00442030340e60791050b07038104a5007820600c015401003082 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 560793866 1250 560792616 560792663
    0x30b063d11030f04050f013507031a0f0303070c1805070801030b24190806010801060f0302122d0601050108040213050601110102040e012301021009030e0607 69
    0x1e5160481c0503600d0f24000c0c154044440c012400b4541c0700d0b00c00e58003075907020b0303020340329103040c120803201082031800c10001144100905400c0c0361030b200c06070f84001081c0512a100d00900001c24501c1c0855201100007880354059100d519560148010815030b00403401c0d0b4000d42005022003e41d2011901c2404502015038401400b0013060040000061000442a072503c980c4068148404041124404105056140e10260441e04000584000d41d00c203d00c00000005803100c04080303407080c3e640c4500c203a00300d40e5948604801ca4005040c240010700d44800040b2481a412048488220000c0c00b101e0080342184142402c107030340c8500d04083c0c208240421030040c002420610907526068011130508004102c108400360390b25400507040d60301565003080c040c924040210f46594950346103042c452400c0c002c00386041004000d88500c0780c9c0140740c11003605010781c080d00b04880d43c07001c3d51015000380c01086040c007413602030450306511031031302a00d10140120108684480070003965600d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 560795116 1250 560793866 560793887
    0x506010c021f0f1718012711061914160807020901060e010f08090304080f070e060d11040902030f01050907030501060b0703050f0c0309040c0519110d0e0f030a030e010f0504030b063d 80
    0x5804240020b040500ba0707070700c003122b94072150304001200f0429220403601c18410681c201005140c9c403120380d814400302d170003e000c10f58800e450310302c0d043c0d07200c5500340e4003a1900035046000401c00b02010000c180b00d00303603030381d0840c800034112070409407940919400c06c0ca1081905c00c1c00d5004036030030811020945ca00c1c5420440980702c603401c3c042c5c40d85810684440d0550380a010341c1c0c4803441d203c2192000c011243c100d0001380000c020a0410050903500e5505611041e245582410400b1903008040ba04460b23005905071910340c689814201e5150341908001c113102440e000a003c0c440c56920381d400784000c07a0340c0c0f6942c1c0360303a5160440c0e0a890001c9080e0450003c2109209a0340c104040000f040e4a0100107410302a01020381e240c00140d91907042d050098141c002c0d0300b41d0200b05a001a00502d00368001d80722108402a035580448140c042d611010b40420500408030b1040d0030500810b9048000b41f0860ba55803100d00044664500040803218081d101d03181100c2c2c0b00315900c11324864 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 560796366 1250 560795116 560795119
    0xc09010f05130603110702030d11070f21021903081c050402030c12010209040608070303030608030c070608070c02060c0706200705040506010c021f0f1718012711 71
    0x203042002d03091002061100c14080d2806240c0c1e900d10840705015102c003520001036006003282c841800c0200018081840070a0b40f01c054440c8410106500007a00021f509807000400340c0c0850048100707241e0344051409400340e8002c01c09050680580c403d03565624041c5005541c2d030f556130385450031840640c5c50b0400a0948a0b4504800e010050f0780c0410f103c02415011030320807042c100e0301003295009115200920303038810310309000042c400e0300228030401224000d8030304000c07881c1d5500c10b564a9206664000c09507800c0058107001030750007107200540110262405e9015001d050f40840d4071540030400000441d4044901009103039444203a62069210b101c0d80242070925a107040d0359590005d008040c440ca03160310004000f17910442e20660060b800901c1050b82207042201500401000b03010303000000c4140513a24030160003000d400030200325103070100f201c80c1d448000444004480000f881029520780c4044034000030484800d021200300340380e07800128540f510307110340306000002c240ea = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 560797616 1250 560796366 560796377
    0x80f0d0903022d041503020306060102010903081b161a01081207060b060f1c140c030402090411030d1110050c1b0a0602030406050601081003020f13140c09010f 70
    0x600040c0c58058101d92040242c03001042c4208a1800740c202243d558965030341c1040c84d10705d05000c00400c1000d202c044a0090341230300c0032511602c00482c00d0720003040c8040d0204a80c40d0100e0004100e01c1c10b40705c25122706e160b071282043d0501e02504140b05ca001070588898420b5800c0300203401d40c0007941c5004144406c014a91659203100e2801c4c1401100000340070310b80e94220481545c4c56102c1111219800c042c2401d6480840b034402d40841302c030042e03000c800a031803c03c41105504a0302d034641e000d100f464100e1402c503901c560821000e49070003803049440c0803c01100100c80c2d2020405502c02c80c41a481d03120301951103500341440c0182707203551540140c1c100001e0115811001d001c486070b01510740031814000030619142d924028240d0001040a40300008010904c603069006030302844c02603a41c844c2e0780d101c03018040078507030761404082c1d4881052080c135a503504d860303103003103001c1d9514003400710b0207101c0284d0900c03200308210350100c068180011704903c00d690026a801071445e01d0b0400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 560798866 1250 560797616 560797619
    0x50f0105090d0302090a1203082e0e07022d0f061317160c060e01021b060d1e1a06070f081e0c0c0a06170f04020a0f080f0d09 55
    0x7150390340c18540441030038543d002030740e904980c0f507142e540b40141035403600078841100303036240050240701c046401014003500b005015180d0074a80d0180007a00d00c505086c049581c1c1020703020600150050012015441100b44070101d42c00492004200742500003004100c154000d10b8007410890745494140b801c1e042801003002c19034098400c0914590080c02121342d00c800c0d0780d181e00c1d4920071014000041003c10141d4000c001c003d582a0050315516520b0728402e141c50001a603403141340042035401c0d500c4028030b44000e81070a0b405041c01100942c001715500c0104442002d8007048841c1200d141c68843c05565520598007543c03d038442341c11748403d841e000d400e4a40031200b50007507500406009000441000c0c48040c0701c451030244440da038109994071200381d02e040ea9a0a0b0480d485c0c0105080103000541500822021141e0f2100007820f00c069961130760120f5200100400480e40003103400c9020502da004240f8090241603018005c4c9030100103809294604480d460404017041b0b0700490 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 560800116 1250 560798866 560798881
    0x20d020c04231302090a02090a0e040201020d1139060f0304080a0203071e02011818020904020d0e0313140607031d0411090103060b0c060c07060e010606050403050f0105 74
    0x2030794055591114800d400c070388440c0000f031400031904001a504c42c05202c280140000c0a43c000d01000000301c55003001d4036518004070304005800c880c06400350300a070b040140d4850041410205a8440c1010b54250305407a02c01044011400d081c400c0c00c080285421403a044110b0303606e80004081102d0300f13030038450200043c92180c0300083c4000c040f0003005c070742103041078020000e464000ba400351810300090920384004410590458040c0d00140c0c96061b00c2e1000c4410030440805d5070540d000303841140c802d8600c002c000e9484042d0664009074200030740000000320784a41412403a03d0005107680306d10390a462502036a450b0481c502c0358101103010790540e5a0308080700c0a031503050402e42c040e20041c01c0c18442844c4519049034000b4109847d081c451841c0000030011034030701743c900b0130805440e003280465034060101001c201b0381c0514007203100451440040d03c1c000384254004100304000142c11400d44007241d00113404580c0200d0306108201003400f0100d0341d4401440200150300c0c0c03440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 560801366 1250 560800116 560800151
    0x1e050c030303250504050d0b0702060a0b010f1412040308061003020c03030601120e0d021f06030b1515040e0610050c1e07051509030f070f0e0a0b10020d020c04 70
    0x1c3c5500070070b1910b4003d0701100760140043d43e00521005056084d0b0201904008810400888100c00140107080c00666114090701c10300d8006081a5149030160300b001c14150360400d040c01000c20008014851400d40b0140c01e40064401c91003650f940b180d80c1803680c01c1c0030043c24100c800509240c018406038000a5000040d01d40c0103000340781103070b01140c4c0c00c0c41500c01000c000c4001e50082c06020411040c072900042e8107004402408441010101c4103101300c0100c44c2140401003c2a2049001c2421070840300081c11510100414109904546104040560303006d40e10008050003243c04000c0146001d901c051074403555424100d180100c0d0031365480d00d506210309a1004401c02c10649405403a0400442c8060440580f0311480c0802d1000e00000741e030001e21002d442032040415409200402080800c100d40c8610741c182c103400e00700200607414000003450400d12a0b515000801e440c1e440e50b0110401295030b0f0094001102c0ca210024103004065420502503410100303010049035081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 560802616 1250 560801366 560801401
    0x70c050a080d02070816121107090504060e03030106022407051c06120614060d1509060219050912031e070f020d082107120203060d1e050c030303 64
    0x5607a00380d490340c007644840024056030801420f818000324603a80300ea180e0f404c1c186502801100d5200007000c0005084984030801000e0403502e41001c1000c1050074020b400458000f8820315001c944282c0031820340381b8540007603000c000103030b0042c0f0b142e50725210042e4004105503d5221528000e25000c0c0300034007540308151b1000c1211418950007c811800d80e40003070090310102803655041c00c15410301d60040c0032b03a400d80c1c091200c00c047c0440e41034980300740d5820a5a502111041042c5007a0480310000d01a5120a8443c19000c01003290810150304003040340e80361607280c00d0346440310041030002501c248a41e0350a540c0c4204140e801810310391010003050001c1e10394032035a8400d00c0c5041c1c61500d03402480250003810764a06801040507840141c12401d22200c2680d00380401070105401c440d509407070010201d20400a0104d1002e40c68000b96030180000d0b050300c142d650282d9400d00c07140795169170881d07010850300c111020010107110728007015104400850850400521003003452041c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 560803866 1250 560802616 560802623
    0x21091505121302150a03050603030a0e090a090b0a09050d0216050d2901060f0c0308040b1f031104060602070b0406051c062408070c0b060a05061b0105070c050a 70
    0x24000040b5034088501c64040c5095020780b0340f00c003c0b2040400000103030440740315400170030b0401d000102c40b42000815502c000085a45405105641805101d0000303030151180728015221204500400c2440f042a4018211408001102d9440d81001c500345040c02e40a0700454005894800710034030103420b108165081241c01101d80c0081d4a0318400c3c001c003004119102e050043e8815203880780c01c0380b00a040382c1d13140d00d03134058440a1040880700c5001804000b0080380c035660101d400310340d4204805900c4a4140c841d021351081c0c11070410f44003903465004417036564200c29600454201405440010403040c0000d2032058103010018107030f40501c1c041d4804000c80480c1000625016122001400f80306450400819464001d0071400900c142180000c02c0707524466900950320a914040c856035842d610500c1107103042d070ba4600d03a8400a81640c1d03101003a104081031680c3ea00c0000c001001c05940740b5040103854180c80c031f0030369a00801035000c0c04103140340e041c00f00d00046101d04050390f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 560805116 1250 560803866 560803897
    0x504020a15120e0a0b06030d0207060e01090e190e010608030304080d02040e04050c0307060908030a0e2205100e010605120709030f0614010e0108030a030905070321091505 75
    0x1100d050465100700c001941c100c0150503ea46000700d01408160988418040c44002ca0640c3d82c180c14140d4a90748201c440740141e004500412a03280b282021500c00b200c149894901c10307544160b4060000c0381139031481c0920481000992590041d441441d080704200c20080c403aa91802e81491349900008001038117003000044c0200081c23901c1c0e0304584c060140001a0a080e0405041460b82d03a50700080090291041001c0811384078000c00c4003c1c22502040002c40c84c216108500720351500124407040c2c1c101c00f000c11013010030710701882000f0700301d04c20980000d185d10700580c48680d04050f80e8448102180080d005101c1141c0c850100c40c01032840d01c044480548442d803040712a50001d0b800503080c40c4000c42004c04004080c0c00420300c08111b581e4650550b40c071140340414600c0c00703124500256004026914565001e80c2000400f00d01034000d441c942941c985a0502c42402c0e1000820940d80488a404005400c48006d402908c0030440030161142c4190380642a44103c8100b108001c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 560806366 1250 560805116 560805149
    0x3180d0210270305030405010b0a0e04030c030c0605070203070501060f050907110a0c06111509030d0903030b040c0320040501090b0304050f0a0c090605060c06010e0c07061406090a0504020a 83
    0x450300102c10450a886804000303004030034107008029400c255000c4501d5420085014a50301d024100001562511211550207403503d0381c0660b03001756100e030110700f481a1904104080350715807148500c00c2c1603a4000d1a528952443c045085400c10740204448003000d070010b11254649080081d441411424440340c0303030403082e00b11841c0c11200407004114048024000c110594040d444000e240c5506040750744c00160b400408421071000c8549225940c428840144d54100310380000540350b000b07080000303414024601044c1070782c403404207050100c0c0d290607280a03d49a040010a682541c0c1e6003040c0c10035081c800000d25400642c03140d0b042e41000440464288001031182c15040c5408800b111044003407460700f45500e580324031540d0750061520000044508108080304d60000c90200500150b80c03d02403200b500e80c8002d0700715605600c0900c241d90000341c0c54070680c80c1d1406612020f803142d00e003400401a82c40c2000704624806070400f410300c00180c45a600c2c2e02c080d030b0540b500700315511 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 560807616 1250 560806366 560806391
    0x7170309070e040c0e0c12070f090305060115090e0108060a020a051c051503030a210e192d060509120414040e1c0c0201170c03180d0210 60
    0x180c0d00511150506038090204000c020402d001c2103402c02140d0141c25074900b080c1c0b42450103047d18540b180c042000019082e90b00c5106071504136036580c1400c06480707490f034990760b1034401d098100c00c843c440e50340488126140c018400c1030081136603400081696042c5680c09840f201301900b0070981c0c0c0d80229066401318082c5040d9455101d446036139240480700f914904012340f03826600304544001d103d420104900b4044116091602207807a549070154203050301c441803900309160503461a90300d4510246801c800c0c400c402c4031002880c8000c002d81001e0a012903841050325915090403541d03240401d1110b00d002641c040d460b081040001d1b241c1e01c40e01500d00f441d10310203081600010000b0081200480305019660740c0e04c05407010030501c1c102e0070780b0581d45c40d00d24207000c41241040041c880b0070f51040c0c000d0341c1c0c0148185480d81e03c00240040004d640b150903280350760032440120410027035203049481800c44080e0746000744005040c480c0041d490700800b00751007280548030071204290 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 560808866 1250 560807616 560807623
    0x319030807121406040e060c04030308040c0503030c030a12061505071401050106020114060303040f050d0807020d0c05030c0d080f0f041814100f050919060806100b07170309 76
    0x3024801c1d42c24803112906503035103000f8402c1103d107103100e180f07019221603044100080007403180914103030f600c2c5014107588007580c45600c0100115041e455071500810700751010310151005e16074140045869082c140e0016000080c004141e8040354640725003080905003094540311200c1c03860816503034811907400c021800803625100025150b09080000817034940c1540b00d4403840c01e60b200010140e4844000b019143d00c19032003181140103a40100703022916081b0400c50b0810b12403075405140800a5003c9500703200d5610054428041904d810031460031f060000b0052084101c03001007101946030b0718104140103c03811300001c018046125065501400304440240c1440300b04a4a0080290414809041c4076000b00300842104800b08030b421440e0070000301512011803000e01a241480e007404542c8100420500503104e80e0292050080500d21602d006031442c1e44c003908041c90004429441c03a00603a0086031b00c4541001400c0100d101045480246660116403507900e41f038110440c2d19 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 560810116 1250 560808866 560808887
    0xb0303090d05010f0c08011d01150e0a080d050706061d04110a05121606051e0702061204120206090a0b01031101110d080a060b0a020c0d06020408120d0b0319030807 72
    0x4255141181c1c5d00c214030f4000b0b00030390483e46031407030500760903072070722000070000d0400e214900681659501e10703103404d1b008070b802845901c4080c00e681f03001580d40125510b04034480c40d00c1301c04100300103882c0040c41050f00036600908843c800110b06889070303400070441023800900191850b420260090003070360755803401c2402000e00400124903800d03a00c0065403511801d01405284090b4000300151080c066016110104011003a14001380c80780200000b05910045040343e1240b020003400c00002000715480e0300480c0949001c0c4202403100e00003034503004c80900f106041d81d02ca4a6100c001441800d00e05064035407003481e0103100c80d44a001620307180307549907060782c042c01a07884943c880c8d80e12181c654030421685805100c9035903604400410792050106400041e0800d103100840340c03e0071440699114821a8010b24255841160b142408112030b107a0f041d842c8009411080c2010a0041158201046000d445079511a854117802e81c8442c0d64024144080c401c00503a40d540594203461 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 560811366 1250 560810116 560810141
    0x111605010e18190f0c12051003020d06050c09060a020f120412200405040305032202062a010c030603110a080712031209030c0b18030901121107061d010b0303090d0501 73
    0x10503a1409180031b00601110340c0f0b089a401d20f458000381070785101882080c101ca07005440440010010b0b2201c0024001c0100a00c405400400907902035444031001041041c0700741d4041c10035030201c1c807001c609086180400034139540083c08140040d081c5580c80c00307030b01a07101d1528420445100c0100d0b03400003511040c00c0d44a441c0030100300c02e0541100065100e4080d050541c0d0000380320840d0200081c910007030194000c1c400384000a030401c0c584c43c074a80c013460303124005a079802184008070b01303491600302da4500007500c4079010810090000c0c2c1c11002c4900444400d0f0141d42801800c9607240520b11814000442c01070b400024136001c0c40d2040c08015000c48144109929818003034001003104c4030840d0552070000c00203000c3e441c0d203c0c00c4540079502c000550702d8441c00c000119140340b00050b018a22903a03515681c490a480100142011751080c5000b11f07403102c5c220142d030340c001c131410409506a4140b528400a69802004480e106082229251500855400d20a004110b00910741 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 560812616 1250 560811366 560811371
    0x11101090b0f10080606010503040f0c06021f18020103020901180e1512060114030c0406091d0d02030301051e0415030209100602070b0a111605010e18190f 68
    0x50003401404101c003442400c0344419400c0d82e840301806081030042c940304414082d00010082020b641c400e00043d60410b001d602c140d0511b40300ba0b00c0c1d0318a0350405500840140c2c0c0441d844d49000b07000503003200302c01c400c00b210400070000307400341c040300e00c10300f54800030304060740014082c20703d84c081c2c0a2408203015900d4141c07209501c400030607000c036109881324440c03d003801c414400d20f460036450303c601c00080da00240100d646880d40c02c0300642c41301c0c2c0155500d805200084021a1600c0c4110b0000703122655002c5488034503403130aa411003000d00c81804880d00605140000d0b6500001281d044800c26500b441c0414040300c40100300d4076103402070aa0080c1072880c9030001481c0c5075054400d9a008803160384031500c802e8008c011100041c8503480158108040811000e0492000360403080c001c0d082103030180c0c8200b0f1007c2e0a00000e20b501c2844600710940a0000e9644a4084c0700618010f03554070484030101c10b5407070113110005020300b8200d039020300c2041600301a504030a11b44842898203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 560813866 1250 560812616 560812631
    0x60f1e0405250b0910050c120414060405030a2013020d050601080624070b16081006210e06070c031d090408220f09051f05060702011101 60
    0x440d242d949078184504860b5140b940603403240e88003102501140ca02d103501528040004050004480262100e035081c4942800001ea8008081c0011010b140524940720307656401e1241a01400000342c010780c2c010300c828403007130055841c001aa00710300c41e0810120b0354882c0b040e035210040e15000701c00c15500318211003114041c0b04503c0c1c02070075075050913200c1031245170b0b203480c01190000011284564010303a00304507040c2c0408415400321241c2c4031081928509000b5440d0804400320644007038188007200003001c59030540c41000250408100d41401030200c0c9400001014808441c1440c190b902c0190703465117540782e0f1075004420142000c025100c1e2440c2501d401340c803001c407a10041d0081000c21082e02e2040b000240c0060000d0002070000c40d10340c5032611015003d4000c010440056a64122403800310a0004a0a0010010034132000505410803062900703441019025985000b194401e0030300054040441c0000d07035500740d412a032a45494001291840e40510707207038a29501e00f0f000e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 560815116 1250 560813866 560813873
    0x4031107120b180604051c0201151e0e070c060c11070e2a0f090a031502071e020f190905090a030f0f0207061206051008060a060908060f1e04 62
    0x2107910691a0003815802c88100b03405083e04c1e1481214000c0141e0410030024200880c8114403418015507807000090704143c0d001c181e0304060031a0400700c40790300d04080c0410340321000d00440000d0012290001d1007810184c0004e0450b4075100300040c0a00d4450181c3c0c1c8100c3d00c01c0180c0c0007071461000464111030741e5808910050603043d00d04907403a50a8000c0ba406100161000c090050b102d41c0c581c07450034400015441c656003101030441d6002c1c05030304c00040841c4025940f007640b0001030000580c0c500c124a01080201d020704c5c0180c20b01c03815140c01c070002d0703500c80003684081030065418046413004115029846482c90300720044c051b14240c240200100000703400d1000f00d00c0f9440340208410151003d8a1094000d41802c005a0125009000840c82201c2c0e10b059030040c80008a800b07901c400c0041c4003224454a50310009034698200010f034030785a003040c8000e10503030809034042c5040c044559103555000b45007120700340f0f00402140c64400059088030744100101441103042c205481e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 560816366 1250 560815116 560815133
    0x7170711040c1101051308071b05190e180c0904061107060917040e0109110f040603020d110406020a1403070b040f120306051c020a030b011403240403110712 69
    0x41c821102d62a260004a40301902c0c640148402d0300301c0804c1d230402095a440307540505150352150b0000000320340014241c2c403420b00003850940301e00c402d04044c0f030801b0203655400c60f006008202500010400d03500080c0040f46004441d4015112554141d450b814554003800700e01d503840c84604400200e4200f4400d8960003a01c10511401000b03003a2044248080310074000c0c0d0145160f07500b010b40041111440c143e05c48201d10b0300c0480801e00380038010921450a4001d548840086900080d880c00301701c01d03038407a0000165280004605190034040000e642c0da582000041c08202420390411008400b002034a050644c0208140d4640c50a07140002da0020a001c04850003107000d8416980a400b07400303080705441000d0301102404c2c550420341c03090103011000c166000300041001001041490314070700d0191030403a8180f00d959200c90181403034a144d4410345558145a40c10784070421010b061880c1d040794240ca0800c0198210f440f80a062840590055802c0c20078250000c080250f00b8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 560817616 1250 560816366 560816387
    0x724030b12160b0c19150603210c08040b070f020901060906201f1d010b0a0512030405012303090a0309060806090703020a03020c03030103061b0507170711040c 70
    0x3540510b480c955542440025401188100203180d0824201e603402143c4400c0c07840c04950140c1c8881d1000001d64000741c044500b59042615405100000b00d036981a580d9417808900c2c0c02d0745048110360070540c60794005e0740a10b0040308400c07100041c510050060343c803040c0411a4000700a1005540e503440d02034020400381c404d48002c640041d01c1d40c0b023540411003001a40621403005060840201c02c0c22540120614142c0e410241da00c403201b03803c001410060a07141e80020000181150f0000c08000803c0e16550185100382041d40386500214004416101264000c0c01d001940c6420715003ea0f14a81c048140048000300210810000440c0000d4000030355019844108140351240300444400001b11070743c41d08042c501011540e09442580284502c4409180040c00c0c60040e004503800c55200307074000e484050f21030489540003113040c078543c02c84062130f0038698603283d880c0d6219600035140d80ca502d00600004a00c5105000c0001120302d03103500300070800c000304c118070354000d007410005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 560818866 1250 560817616 560817643
    0x60a090f020409110720060c01020705010902030c0a060509040c021c120501120b06010c0c120803010510090e13020102070506030f040b0a0618150806180d020724030b12 74
    0x108800d591081c0c100c4001c40d9030003600300d1b032030654603882d00180f2540d0152036000550400301c01c02c05801b03a22400e1001d003042034425000807a00c50340a0042514211100b07c109100e0303820005e08110850b0840101c42080c64295030109510780c1c180304c241d05203c280d021600748407006c1c07080000356a40c0a0b204d400010b240380c80810290340c1310a20f4900c16060800014034070500c07900400d10560007a090503031040c0c441c40c5c1c1c02135115144d009c0d8501d100302552044a17401c0c00400117000c140307402103000c0c4d030407a4035142020a291504044401449025100601040d42c070006581075910034440b20014100103001d0703d69a0070000380745a80e82c00b04450595482d5084400704000400a0060a0845801c1c012404d03040d04922040002810280b1000207101b02c418400110b844040c81600d1040764801e0030b030000c01d00040e0075a070415401146a8003150441c40c400e106040340c031448211110792100d01a100c1c80c2c0b07002400d50007414220b50282d4003101c2043c109200741e5000501600080c80e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 560820116 1250 560818866 560818871
    0xa0833030c28140a0306090204061e0504050c03071b03170c1b06040c0626070c0b1510050c01021e0417061e060a120602040e06091b03060a090f020409 66
    0xd5070340581070320381c0b0b1180c0c03d2903215805680400100d5010b80110300340d10b0000740005441555608001619088013005551900b0001c800b045545820b22845030b0002d044030b1868514640000e00500c0102c03204010700880408000002c149840f514002c8282c000c070b114401ca881c103103c01d0301341140e041446100c441c0ca12481c00c0680c42c00020502031300881c0c0c480501c00c000b50500c081920840a110340e481ca04842550301020202c00442c0300d60300690250321080345003026404c192000f03030381c001c00c407000103452044441c2d41a00d40c850040c61003d0340d80350007030b1902e090151050182c401c5076240890b13103070701e5407280121201840017042280e0400d07880c2c4109024400705c40f0307100c030421608016100f090040550001c00c4002c900d51744102d00800c18000c55443e00e404e40c95032421180d040da2503590104042c070203482c0329010140c200d20300316103c003c1403030103030f076032599800b080311202d50071381c0020010517180c0d01c4480600c00a011850307400d1101d4100c0c01001d070f000790441d1080805460 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 560821366 1250 560820116 560820119
    0x9060f0503010e1c020a05060c030105010305062b0221060a060602010c1b03030615050d0f0902100e1507050f0d0315060503060a0315020a0833030c28 66
    0x2505103d010301c1e450012001d4500b0084c0c91050983e11816040000c0c254000e107400d0303c001503428000103208041c9a44c20340c0d26941001d00050440b480100800d006e00340300d8082160300741509440100341421400f038a070391460f80d031011844d021020010300d40c070340380f60300e9544a44810200b80d15220b1004444200017165481e1012401c0c1c0c0e204421807800b180045108094444140e001c1c0b203029400b038140880c480e0340d22074030000c5940000c0c4107940010790208001e01c0740311b0355016000718002404410301101103150002070060080940300c000344903125003032802a403100c1600c4541010807034416074484009013070041d01c3da403201e48005030601030752032010440b90003485818081d40501c03003010080c509207402602c803680044c0180794407195042c00007000038114503000c200d2103020140980c40d8941410050100200501044280142d40c140d00d512010104100d4045003841520744103140d10840100781020340400e4901d810a0300848540c5c040860a05640410b407032103451100f009 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 560822616 1250 560821366 560821369
    0x6120311011a0603090a080309070f0f05090604020c10061e170307080703030b06030411041a06030615070614180c010c200d12180f1a0d0609060f05 65
    0xea0600c402d012812000740c501034801e0030b191010716448403c020490703911261545400f60950030031105001c065101c654140130040f00840c0c0c1100811b640e000c180c01d402c1c2040000340070010000c1501c2d010f030394041808415844d08226445907102a181d042000d940c441c046140c8030300e83c410038104465280740b00003c2c000402007102c280980035401441c1800c480e0f0b6644c0040d6403101b0025420581c44080c00304090341d6407801907004030300c0768101c01c125080d024140030a0350b14803000030b0050090110010b100b610388000b1603500c07040403148041e60003001c14144040c0d010300140600400c1c602410078130105000f1000c68040e04c500d10483c2401c500e903114240d51410300051081c005546540448002045c40c2400d094050341091210482038005001c02c9004400400c1603e07218084c0e8440583c254201c110004580b0004001802050808001c0d41c2424102e120f20312505410b40d45554804c204002500c0c124140508180804c81c0d0f1041c0590140c02d0b2030040710a200000040094035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 560823866 1250 560822616 560822621
    0x9050603100c0207140a0803031303181413020909061507051006030512030c0706020a0e120604140c1e01140403060501240c02100e0d050610081f0c050d0612031101 72
    0x200d1f101c8000641c59503842040c0e480750080c4020080b403e02c0461503143c036003006140a11006082c0400000c1703010441c903000c018403800c61140c0301e4500c5204205280094a83e82c0460364000070513140b4000c0801c900584100f2031149020280140c09450032282c80c006040d000f0004581c09982101c1c5815502c9840c0741e0503100680d0080c2c00307182c0400007840082d03419000307040c03800380e2800c16003004803056011030b1034800704190100b83c5030054810003041002030013508404a44000040908110060104040101301c0345203c1c802c031400d02a29040b0381c81407491101168a0141c0e0540312a80c03854804050301080c012240b2030480c802d03404600b110b800b1440588004240e076144101c0410ba0203200400c82c140054a007001000c11a4840944a0340c040f803841034072030390040c82240b40c000c2c0000340710200c64000c0a0b84d0b40002002ea070341071040c0990860203040c6080c1c0084e805810201c150b5062040e0780340103030f5241c2050000a803100c2c0c0703441c0c4500224041c0c0c4400c80210200e032019400c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 560825116 1250 560823866 560823869
    0x902041707091e090204061701020702011101051005090a0b0d0302030c070803030705070602072d02010801050a05100f030b030d0512130c06030f0e030c061f03050709050603100c0207140a 82
    0x20343e0b03c4649026100406181c2200d14454005000010401d44031781d403050140202082190075603400142c03900031941d01c50003d1000001c0d100003006103042600c44008111050300c110b6100b1000c440210311030072456800004003800007800001d03801450700d406074072604600e88010250292000c009081d40b004001c4a00c2410155605850302d5455541c03130009400101c016142c5800c9034080d030183c1d8121164000a01d01840e0100054052a1000400006050300031a000d2040b90204000c3c545648190030714041d858203200ca0206c400000407401411300100c80c81d40340c860182004007003500000140040300e200b54445001c2c0d40d8054212000440301803004050340340815040000502c60380c40400c0c1400041303c04035002e107050304843d156410503e01e007016071b00000144008100800007003010100315120500f0140d1840d15026240c1e12944600341859443d600011203d07034050000e441c0d022a4a1810402c41458807402540d595442c05100242c803d0302d580d2908515000c0040c80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 560826366 1250 560825116 560825141
    0x70e090313051203090301050f060f040e0a022403070c0b01060309050a03050d0609290d03230f070b011401091815030b07031b0801030b04031107090204170709 70
    0x1d0445240c00300b4002d9a0060a110701c01c07a00052250100c0e6035021f015031405143c200001030b980b03043c0a41000000c4074a9070141d0310440ca48040705a43c003078080360b01d500480e01294800384610184000421400c40d440903038a024000104101055421002c81403042c1d00a0300040d12070303a294242a021203842d00d401602d10740c80544031100088c4524000d00350701d2511600440d1a075560341800f4140ca041c03404162189101c407100e0841c81c000d8520031b039003c0d042110040f82d00300603030301c018010508090b12041c203034403000f243d80d220103040300465078034200c51741401e80d4500040c205078a050000380130380f894981c030000c81805158402e0100380203843c240070181031580c296103441030051501c1050740b02211070308031001000c1181520f2300351103002c0a44010136141c03164103042040442068542080c00362120051010500c4080c0b007a91141d45424541070719151008140d14143c040da2110240c54000100403c1d43c1e4018440190301c080c0701c008442c492600c495040081e6012100d101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 560827616 1250 560826366 560826397
    0x30c4b180f100f03030201060302032401031e080a0e010816020d0509030703020607030f121a060901020f0609162c130507060c0b2401030c0e0a0602070e0903 69
    0x1000d0350300c0340207400d400a0b011000891843c0d555103203018203d01c07652050740582d54940c0200150b080034408030481010030445601c506001d203442181d29032060001070105800d11345081c01041c40d83c4c40701d18290f1b0b000813119882d42d1501c1e20050024201c800c056000032083d401080040c142840a0103805540c0c2e0098188025254400c841c5504050000d551511840b03200002580702d280081001d0ba00030380c0d50500c1c0580159001c1c0c00b0202c4000324030449480c0050468080360400b1014118900842d01c4c0c0e950b420180c00100d01d440381100c018207580c003465041c00310700c103800512044801020002103d5a65640b44059840c01c2e04213100c903560504400740040740c0000200055000502055204681c601500c0319490704800d60008400306910b900e1050034002425080e9501203034821400d400032800e0051010700c03202da041700301d0600d0f4407030440b4070003103015040410b0702400c003400d01541d403a5100c900954454961107080316080c03005010450000c0d0220403541e884107500c003034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 560828866 1250 560827616 560827621
    0x1051e011d0d152f120c090a0905010906060c02030303070311120403021005090a1a0c0903010f0506011e0e01120204080f011a0103060302030c4b18 65
    0x41000ca14074041d00954024480c000110005440500d48048200c0050002407450904402e220b200f079041c00000443c40020a4a02061150001210040900c84a0420300c94980294020f61402a4048264070008401011038206410303403101b412039492210a0040640d1924282c503404060000a5059042040001c60302802a00818650355a40140d20315042200400010300d45040d64210300580050020030068400c070301075140c10090020207001000c8a03a51442c460b190200d030719110340c00d958800506101d5802c02901e04c0b800c400340080c0314144c400e004039401406d0480301140410104c200342185200300402d40c0c00102050344400071405400b40040d6a00030000b019006156002c120109040e00d0910800650101c07060011074010803400503022880300c010680c90401d40780010420140c0e80001c0c4000c4002c009a82d0200700c10402c04e160b000a0340c003c14034500c00440e0300c513858031040c0062148011906000b02031410541134604010799a03201402000345912210701 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 560830116 1250 560828866 560828897
    0x12003011502070503030c01020702240a030506030f07140328110619080f0622021b0105130b01080114040b190507021609021603051b01050a0501051e01 67
    0x1044801d9a41c0c012100035554510000e413469120705814002a50007081c04070850a0180c508800c0e0322810300401c1036180d00c07000a031304034010341b1010410541c0b82d8011072401c1d1014003901000d085000162a54503480d048203921032204062928024032641c400800c0407801129001040380244001c014405200d485000d175400f01c1710902a40408100b00c0c40304200d8001c140143c0030003d43c2c8641486141400c01c904207070800401e0540136191144032038281c074402004980080c5061300e030050710f5406400c0080c4001c0c5469414180301e43c0381005102c1500e4a614032550624441c04d8041c4460f030b2180300f243e00b611880c9040c0c0209001c0700000c07400103403403080180d5000e441c0010b812000d1340380c8102001038410540b4444090b8001545500d22907400890110150041660541c51710b151141d0308601a64443c402500b04407006c240743d40b51040c0808103584500d0954000e10080c14001c507001c000300001e1040c1c038410403412100d11071050401100e04000703c0140c54104a142500c80c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 560831366 1250 560830116 560830139
    0x1d1f060b0910031e0603031211250f0819030e03040b07020609090a05061809250902120a0b011e0810080f03070309051e0d03121d01200301 61
    0x10781c41e030b040c0b50b00c90108041d6003000c46145901a8000100420301515508015006111003008a81000d0074480352240a60702e00080702d5070021040002640580c1030a003840c01941504002030903519451241c0d02885a11400703401c2d0740d04c0307d8607040d01002ca8400c06030708a4520724407004054005010820403035044030080e00813940064580c9140075a2f800c0060034070a011074100031040c1e81e4909000050a018000d100703440d0b039000800c406428188082c41c2c2c0c501820102c121400c80c803000d5160f5107441e0080c44401405d048505548480349407290780c0d502081110f0803101a85090125281980301e0000c501c8400b0380c0903c01c01c400c0708607044c103e5812100810340000c1114110340018461401c002c0c9040c40c1014201941d201d01162800600e00e42141d0300c098030400c4210401c199058800c40100441d8504403840623844505141c2660303040061503084040754079201d0f0510b40c10b1415024039400744c41c1000200159000761030800c20010b032400042450100c1840107102d40301160 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 560832616 1250 560831366 560831389
    0x406051e100b1813060810020f04120201020a050613120306030317270601030c1403030a05032221020607050706110909040813060203090907121d1f060b09 68
    0x3801e0241e0403800030201d040d44c2007100d00b420001d0303a640030410200d9410300c078540b144204088250318216404504e00e41c03900450203a8150034070b0106091046a00811a07a0b810035440030a071171a034604080491030700400e941c8240c0d85862117034005d0035514072030312a480581307500d5140c5400610041c0000c2003640703001403a03d960b41460582007030241da0200341003850001641c0c01485070b5819131404c8840b5030807035031200d00c1416641344400401d81e000300942d43e8890f4540341c0543c40396110100c03030490781061007420b01e24480d440c03071000502c90744048462009802211a9118240080c0205e946a03411602d83d4002281440304500050341d80d001151381c1030242030010b00b42248140007071403030030060310221661a030019610768010902ca9045000304a41c0c0041c43c1000403840110b0184100102502f04000004046c002802201c2e8000c0340204402100514010035880e55255202e071195408100050380e440c920391515514020342040c0c4840700000741c18941ca403824800e244040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 560833866 1250 560832616 560832637
    0x120c12020d06020f04050102070b070f3503150315130212011401031b1206021c14060102010b190302060f0c0a0305090906190b210406051e100b 63
    0xc1801e0003010915900240c200f40d00640450741d502d511740300c0003a1501c0713801e9101001d0258240204804101400c1e00c401c641c94114100c22240c00001400c031a40c0015000e0150a0032400803548060b4012440036500c52039911007a061000c00900405503145a4841860714501c10140020380034010380103225880d0344082c000c03d42c0d18802a0500e4291141c0010b04001441810010001d120700c1105d054440e0407a600f02001141c104100300c002d0140800000d0440d82e000035840381088445a0f5100700d00300c0d084030811070f004400440000e100c0e402d540c0e880c0190f081005030b0145140c2441000c003064800280c0a041d58510790031f0045a41117800354802c41401806502c0c0107000034465414464400d035107440d41c1d0341d000b10821218036005040d040c010506840f000c282600e800a100c0150352100c24126141d2100c100e650050b004224a92040315051406201c104070b0590045130103107d01d425101c0c86c20341c460750703920030f58241202c1000c0c04610303000c410801c1c281280b0040c820345c0c07035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 560835116 1250 560833866 560833879
    0x1113020706020d0c1e0503061c080703080604061e0302090702160f050102060c030f041502130303030501090e030304080703080411150d110c0705191a030709120c1202 73
    0x2054460034120b07003010411400711904d5621102c0c01c1680902843c01e80b1011007540000413604c070074010402d01009110070701a5491035220400071a202c500070032403075402440c1ca503650070649401054901c05550b42405103007003c40110f038190440c4003d00d0b01801300c0e4020701c60300b451030f020000c1d10840038101c0d10540c000c41d220080707229107030030000002d40f240018004400786084002458400000c2c204096030130305000b80203402d00f07060b1070310781c105820040681c82d035501c00342008020710540800b007100c02c010013000810590150030050403640c150ad0100402030340d001349a6140c0c407007180d00a00c42d407010800880001c3c050380342181c0140c05003030504012480078000c107806621182107a0003680300031804010081e0703907018050b03810140c1084135051131010000c1c9541c0c1c100e91b015a6110b088003000702d1000c0c040c080c1400c4010400e05409826032032130454404081d0788141c90040005191600115500c4005480c1300e40640e4000c070314031061443d2010030b02c10300b000404100e0344000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 560836366 1250 560835116 560835127
    0x1110d0e040b13061d060103050f040f02150307110709060303052a0d050d1d06011a130f1701020a05090d06140408030105010e0d0209040303020f0409110d060e04111302 74
    0xf081d80300c0c035005800002010112042d14130f024a4048000420701410941008204003141800104141c0c01582c03101842c0300300c20b038a20005100b80009981681d070008040108040c01e07078418205130031101d4682c1507411054840d17110006980c220b00001d4003141c8d081107403035100303221592a008262410b0711081c0c0d1507100d1076042c0741031030350030512200051030104003100c0080f440d21641c2105207880d8001b40291041e0200c0b81d40b034110501c21030000c00e0800e064242403d20130003c540c0c1a00c4090400c609135a22118502c02544950261001c4954403a681c41c5240405100b29240f070490b03034442a0400000c0740400c0190320412008a83c231030384601c2c14076401c042c10a00c450085105203e01a200e40c10300c4001003240b1040c0c151548a10700d14500701c03000d0b840e00b044c001d801c160146800744e81c581502d041d0520303d100e03a031f000050303540c40d10440600121180d0094018800b40080074482e240d610b161420701c03960300740c40c040c0c84085002d02c5000c203490301c401c0c00c034004850381c0005420718 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 560837616 1250 560836366 560836399
    0x27040b190e0c0f1f080a05011203080115022803140a05040308090609030115090e03070b0a02071a130501050a020a0e0f0406050406080a02030712080301140d2001110d0e040b 76
    0x704135281150126420b20107101c0525541d028007805071050084230b407030214903920000c11600041c03049200c0341410450040016209220348210011f1000824155490341c440e402c072445980c01007580062a14880c4481d01d040b81022110036803490395600f402d05040d80c580d18000d50040c12950781c041d01c20040c4031000d840c280a02520071603640c1c0d454142d01c2c0713045042c9050b0703200b0040c44050354000b00219030014400214158200030f4114005807240c0403072820103881000c1c0103021030a8030111041190344250106000c00c0e6501c904006c0c41070303850f0094807070168001c0c1001540071030070820450703038141882044801707604801480820116607135400f24045030440c0e04503901d19004401c100041d41410071030710000304075440002c11216440e496421860006001d244501070301d900b1080d1069507001e45c090485600000380e080510001408000c449030b9a10095000c03950001440c8000b6401042c5e03000e68412540354441800c24179800c0000414030098050f40c04040c008100e00e81 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 560838866 1250 560837616 560837659
    0x80a030503092103180105060109230924040b06030a0903030b1507140c24040905070c060c0801061d010207080f0708190c0527040b190e0c0f 62
    0xe40d0190301d03c803030303807410315804500040c20f00d60800c506176030601041c80317080c0c2d81c06070101e4112031101c03882207107880c003180021130003c201c1c41940d5485011001481001007007142201c2c80405000c8058505055030f800f4003068584801d003080c0d00c4034090001035800002074200b82400b038424600040e0706110300d80005d10348681c81181302c3c286071001c1f0340380c070800c01080080285d91000c4001413003801503000c0094055080b055403030341e036100180403a280300301c403480c1510081d042c1c84000340700300d00d014100240f031400465804c1c1ca08500304050708a90324040c52486041e40c45a685100b220080e4062400340808840d0f021070440c416100001245401401050b90901246002d03180382440c0424070b80c0741c000718005251083c0030f500006c2001030304030490711007150800d4502d41000d51524481d5002c481c45284007140714071900c0208000c2203124021148145440225542004000300400048036401002e04940b40e00030f2042d4540c526140f400c07454401e070020240e050100789091000c88 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 560840116 1250 560838866 560838913
    0xf030809040f290307061805120f0601030f230c0f18010e07080903040b0406180e091e01090807060504020604030c0603050702011d030d0504030e060414040b0a080a03050309 76
    0x2403051154101402c14a800c0c080c4e04010003940c0fa144080180e5081104400e030041d08c5054030860390301d02c1c001e0211800340400622000d00b072068608943c1d480c10076640c110001d80c811104250340605280c2080b24200401a046940400801c10713540701c182400001010385d070005922000100d00c1a500d0300c6207080050103801c00381100c008078105000007811542000e4420341b03c03504284814003c550604041e030f4200c58003854003c598203003901000200301402e030404140b00200c40200120040c00141882822401141c00b04410019986150072500c4140004000003030801010000c40c0c0c1d15000940c101d80000d2065251650f00d031b9a02c1e200381c046502003400f081c1c8460400c48516020300ca1200c02c030b41103400580d4030340100545940c9a203e000300c001e50a551b188086810b1501c50440440050030103019150788645801320311001060056003103202d10306101c1c001a4506100c20100116400c003001041e103544c0c40d94060344e00c2d8000512144140c460781500e00790600c00b4082c40207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 560841366 1250 560840116 560840171
    0x6020c010915060609060c0303050415020c01091704120204020c010e15010906050f100f140417250e041b2403090309050103110d1407090f030809040f 66
    0x14148490308000810740c0e02c1d1307034004810300c0100b01d0b04018090b0044081c584240d8940380000381a983c4c3e24040038801a003081c1e1420f90b51011900717400c180015031040391201d00548040c01060007145c002c0e1140c0c441e0b80101e407812413200e40248010b0030143c020f0841320b54041d001043c4440c2009959281202e441003a00c0e12340c40c0600100706807a03a5121744c20140c0029102490141d82900103d40070402c1e0240080400c1502801a105284564003400e41e003080022501d43d229900c22241246800d28400f1141c580125060094004041e52400125808120015440034500303103100c06c0c0400010b00035155407102c222201c403004a50101c0902400854034031494607003003114070078000c080b9803000f002450f03d00300c45200820341045002c000c88400b403901003442c04600c6c00c03802d13060003840186414030381454881c141851030000141c0c0320b000b4940c0c1e160b040560b10300b00502d0034045813101a0264038100800001030403da00028012825030070042070721851740b081072003070381c040410a4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 560842616 1250 560841366 560841383
    0x504151a1e2a190b070c023006091011120108061b16060c020a060207060b030c010c1106030c07050d020a02030607030e060112061e0c1202030f040f06020c0109 70
    0x82201c2e1a11600c00a0501c0d000c10003071002c0c1049400d0681da104505002074034252507240012409882017003a00d180c0f40c0d0240c021241011051420803040e0f082848407030384980c0c5030350001000c0e0780000d18203104849003401817107209a00c012180080c5255405000345031000c00c2412460072840c0265802040c86030010043c034582840c4205100da00380981032803c41d4204504c07441040c103400b2401086800400000750341d044642d090345007044050006003140e002280715801d0003800e6025452140f016800c0c2c0707080d0800c403c0119010f9112040040225241c0c0103182c20031304050340a50713071025a00040c0d6290030415210381740392580e00c0806800582c0f108950f1000c500b01800810b401a001c2c0c1005c4c40786640c8005c0c10b503100e03001401a4501071800d440c0000c00e002080d00681c0c207055000d801d0711545000310f03100e40003403e1140c04010100d83c00b44008912101c0c284200c0f88600000c0809941c203480e03554620f00c1c0600301410641d5403a070248618141c1500a10501c050b1903c1400c49 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 560843866 1250 560842616 560842657
    0xb0919022a0d09060804020928090209070801080303010315061a03060a091808030c0d0608060106081024170a0207060b1801050603040c0906060503010504151a1e 71
    0x590b141800d03a054040410110700800c00c030b001d0f08000b5058015604403013540d910350301c0d0b600c41030003140070611410082905100300741400055a1000c903903140249c40695580d0340c8e00205452000f401e20684000d039008000400c04100d100505400400415401103074850355844020101d002101e20030080c06400014400145418a814401060212414001c0030a608654141202c0e1810080c198000c00400900b08416060031109a05504203080000d1a20f07401c4a03552440c09014010120b80b003031010401511441005404a071100100d400c070001c50b030202c0b80c2c80c19025071001c4041c03100ba86120120010700d140c42500c00c0304c0c4950010303254202420042e0039903014543c598003960160340d05401800020f1001415200c3c192299952034484e450440c810800503413001d1205843e015000c41d055610900445c104c0c0d07411501408910800744400f060018240302c3d058945030315804124204110381c0242884a03070f0706a1900369060900107902c1c09510011110146e914032054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 560845116 1250 560843866 560843947
    0x607030f05090f0c010e0a0b031609080c1e13050a020d06210f1b090906050c0901090e06011242090b0a15030c02060a0b091902 56
    0x5080e07841100c0500503e95080e980c00c02d00c1e19100320703460721810448002d41809054465821000091100105096a0340361203002040c04a03400e0754002e002030004880003c054100280b50314804a0040042024400000e151014900304800958110b4604452515039082e58841c003031040d00d08031400343c2d5445000072103508072042070f040b001c0042e130319802c00c045440706a0740088803d544081c1d0135152100710704140c48509c085101d4580c2010b86054081281c40850f04011885481044180030710385414510390300501807894071a001403c10007003003010707510f4040016004801070405001100e0062044c0040d140864641240780c2034080d244240800c4070465090100c81e110f001602e00d0792500241061a2102c0c4a5411a262203026445041c0c3d00c0b0081e95009044500f8080ea00500d0990040c01502445081030054040d030f13000980f031400c0c203000380054420010701c1c1c00d2080d81d80c107410a100c1680400c0c1d41d140d01e03038240000c0b440c50030001540d09a016110ba8161141d000060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 560846366 1250 560845116 560845121
    0x9050a05160611071e150c02031203010806070804020f0d0b041205070b1b360609065802090a06050c100501090f0e0705060307080709080607030f 64
    0x1e004100300900500f100b0101540810f0b8442910ba001281e00e5a007020012400052036454000c14890a000941c0342d20380d0741c115003100c0100b0701c290180c03184e40c8101e00403947c00e800240b2544e811504480c0015000c01c4c0303c0d000080e40688001c081d1640c684080000c0340340c50b103040c8011140d4100d890140814803030424106c00c010702c014642640b412040d40c1d212030000c0c002418241e0f120781002c40c0e0344a0320f05540c003510303004202091088256050f031800c0050850440342000d80204615600040b01d0400710210741040b0000340c00c180c903010b80e4499010701ca12a030051039943e0280240f80c1d00300e001500800281d0031030b40054550802102c04401c0f00340350000000c84d00c80c0381c81000070986640390b03250070004440690038183d0b02c0340c803902e2400b81094141201980354521700000030510401c5544054241c1c0c0048201b0000180703210a06662240240512039100001340006460300d44240e0b2400e5201d034092400f030a2140e40d0340a440e03d8480d0075166180469254101c000e0001c0161 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 560847616 1250 560846366 560846369
    0x90605090307030215040f12030219020a050606100908060907030302151b03060d12020708010b0913110a0f03081b1c0503100509041202061b040b070609050a0516 71
    0x100301552808815035030296175201d00c9072101c01910050380000b803d000c0301101808009400c0802c1ca507500f074040d000180250702452010b801112005a991109840040c00b4001d0320b61000003804c081c0c542108100e94588003080e21020811507140100712080e050040318000c0c12000e0042100382d0039450041c0c1401c900750001616840101c00f048000140040241c0d03c10708a40c0070a0303520f4030340c0000314070700c02d45000d030241c215070904072510342c203e60004500040b1440d250003044281684410007858800950f038524110300c950349080c0200e0007007500d5002249004008170422a41d42e0600503981c6070543c01981c0030100480c0240700c040210b4144c85152803080c000e40000c40b0510101180c014202c0f10b13000411601100244903040003422500140000401c01003103483c19113080c0c14030890032000c0030010b0160b203001c500311064810041e121a900c01030902d082c942451055581c6400020068501c1a1141b000f400450803e00810100500941c0030f00901001242c0c80f10601c030700ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 560848866 1250 560847616 560847631
    0x1209060809030a080402040e03070302280c090c0e0a090605041805031c0e07081c050a09170102310e130807020307051c03140406120504030c15090605 66
    0x4000800a07100408030841d901101181803804c0306445500116005050089040d15148400100710043c03540008025010341c8001c003440300100514403a0941c00030221000414102c5400070501504141c0d804c4100079040915100001c4e09601b0001030400446620030f20900380e940105102e41c1c2401d0007215581c01c8260311264800c122a52081d9582c85084503202c107034000000c801c501c0c21440d403c000c00a01c8410215a2090303165003095032109055255100e9035003001e030b84818140c3c080c50648001000e01e03245c0442c06441e00e00c9070030745010314200d0300d03296550070060a4039002e00302240c01c2501e00e07038204503c06110325440f4410400120b800c40d0303060b03501040c20013003051034910300d541c201e030360141000f511401d5510102c3c0ca0080b80d50000c03503106000351400803182244400c802e00b010b0180c0d440040c551814440c0c405188640c1c000e410001c2d04c0c0e0312084000509503002260824800c0c40c14240b005180d840720801c81001d06040000f042d20380713492005025490007020b8020b400e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 560850116 1250 560848866 560848877
    0x11070812030f060f130f1a09130812070c02030c010e0f040b040b0301061d0f13121701180606050310151e020606091e01180f0603120906 60
    0xe410451052400024800044500d000d40003d1294441910780c2c400c0b504080c0204642a00034003050000c0c2a0614075941701c285010200032004020340d00000b41c0c5500038200c50056120382c00311000072040600300380c1e6511001c21829400b2260350f8042803080b045640c818403e03001e68410503003002d038501c3d0114101b21001c0c0424000e0350f070707054468081070021280094003070300e20b40c04a40900410b50b5915410352800c500000c9100d24034100c0354481c124628a040b032950f8000c2d0300c0c141c004003a00c1050100300089404400542445591041074082e424240384044810b01c030480d241c03030241c1000030055a0f5500d804c0743c0703040b5405050054040b13424024214035054070b40f0500440340741319803116a60422405082d041c042e03584203070b0244894140407290300d604000a5a100403d64606014160030310000301020408128402c102c100b49201c4403180e481c00070340d0050700000c4881440a16690682c1c8240c01a051080200551141c09a5400b844541c1805070002c00782c1d0380190f0034080f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 560851366 1250 560850116 560850133
    0x6060f0d050d031d060c03060916020c0103020d2901030e01020f0f0d02070f06020403150e0a020f0307120302060a0b01091206180821011401051206030f06010303110708 74
    0x70400304480402c0815883c00241420702007020203002078a00c04005650302400043c00807092400d4001c500c0703007805483c1c000e103948035540d0385620303480b5980c03403003005030049031380c040d01c9611a40003000c2d499040745c80070815403260f44441144800c400440d2601d9039480d403220170f00356054061101c0d800382e545c00850501c0f10403460108140708800b1441000c0d18001015080c484080e81551401500a0100d00c080041440e02d40001d500ca8001503440d0108030085101c24a6507006000f546c80101018202d00f6050794240901080f403040030a50601940402040d01030041119640300c81c02940200810b0511070140d0084881c040044d50420440101c203215020319090f10301103c0764440d0000403a407451040031a8030350300303210009200c404001001145042d615040c1c00600810919203155640c0c1d84850400c08020300744103d01280d010b0181c500ca03840540d9010b0751043e409010ba41d00082c804043c1420319000360001c0b03000ca16201c5840c40105010010100600301c26402030a181 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 560852616 1250 560851366 560851373
    0x1050f10030b0c0705011b030b03010b0a061d220513030801120c0510050403021305390307090f08030a0c1101020313230906100c0f1406060f0d 63
    0x8405900025002d5011100868656407840f800c554019400000030400303031240840071003034811100381120000f0308140716201d01e032406100342d1a03404001001d1b80585854a441a9000e46080403c010181c582e80440d103440c1c0c4800c04c680582e400c1d0b00400710740703081c20011444c0490341c003d0b01c02c40b111030380401013200094010b414141511200c200300f030f82c4d401181c5003540d608660794000f030b608841f804649001e0190400003410603648202d45219240324454188011100100c0303001c0030300403000c03486070061502d000d4140344040389081d0900400541c01034107071003030b402035480300300040c400030041080311201c002c0c00024001d03a1001e1440c00c201c54000070301a00c8504070241852601c0341162006a00810413101c950680700c0307100d10101d56840d08820041d41c0e07042c00d1800b880c0000c503100c4040c82c04070350717030391140300002c240d25000c04a481e0102d030381c20340407a4102c40b030569941c0c6500100718080b004c1003510502d43d000341100d00c0c1030002d10031268403501d140b900403501c000c1d084001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 560853866 1250 560852616 560852641
    0x20403080304030813140a0b0a0c020a110d020a030c05040b1806090a0e150117070315020a020304030f0501091e080a0e011202041805131509030c02060a0309030201050f 74
    0x2d40c1614100d01e4989940300b9010141562410080c0012043c0701d00302ca440c4004101b41110700e00400582e074080d600d0740003d60554001c114400010303080f0700e110000142806940e114801000b601081a40c0420760200d03500c25400d03001941c0851507030008008515143c00340300e041110550308405400030000342c40722041d2000d06111b1107503c1c6480016100d0781203500560042e00311008070380301c1c2c0d60300340116001c0c0c2c6428001c802c2500096011519400320000d408011681d2000d5881a09a400d15070180203421000e15003003103020401c40000480c8841600b0040140120b00018000200f45002c5644c04038005d0811103400311840c00340045a83c01040e80c0b86c00c0384900301041c140d0104001210300ba015408007591403480481c1c040343d8504c0c4031014a0700303283c10403010440760302c0c2c0c12144013440ca07049900500100060346220742e00c4d15146c01680029100c1e04245003030280690004550f900200382c50310000760b903001e00005040d8240645034100480411101250401c0b0780f92444 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 560855116 1250 560853866 560853871
    0xc0709111605030d0f020c060106031808180a060908010c020705010909020d0908180f0a030507170f1504030810150302250302010608240a0504111504180204030803 72
    0x61244500350030200b406810b00484210f4620490204081d58068280070025003000000e0042d41c030a080011900901920420031144d2921048000149843d42c5121450744801d100441560003406942600e0700c420203110f01620135502c640800c03d0034040c507070742101c108810003c02c56001d180308002c141d07000610350302510b051140160b40c0d49011a0441d0144c540000000c00300100015000254007104110603a0f0303404c01c9816007800001030041008058250002404030b80020a0070880184070b5002003882c600c9460a54040f41081012030b414a020000440d050304861010072080560100101c0da0168519158100040c1009909424102403010721001d055000640d881020540d0b0300043c0a05c607011072400b500c1c0c440b0b14009000c1c2009100b02c100510400740700f680030302c44d2480403030780c41c0e0b204022480d00c0351b0758421030b400a008003910599002031581030124090b280e004007180100c0704a0b4203650780d1450442601c00051030001c030f103000c2c0e502c140418400240c10204807034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 560856366 1250 560855116 560855137
    0x120a0e010e010e0d140f06010302060a03020a020a05070303050a0e0418260318070b030910090f1a06100c03050d05070905120705010807050403120c0302210c070911 72
    0xc1c0c0c1940306005980701d60f540866207074030001084a203010000c065054181c25001e070b00c113a40074000c00c1510169a0381d82800300a602590a02030b503a5014445d41c0a894600c1c0184111031410030ba0380c403440e0410b81260020380010f000042c0020481f50000700d0400f5001c400d9800300000c8202c8000302c4c07540d96032040002d012a043c2212000442050004038110b600f60164030b591702c0c14510584070308680c1c0120318619502406000060407560941524401c2c5200c0019085030031031b074588100204064501110a0001c400601001c550081c203110b220080c032103402100340c2025400c0064141c04031182d1010000c02d00006000645d1000607104140c08000c00400c440d281e0107001c1d10020800d40180b9000345aa594001050030001071060448500781c8070380000c2d44920398201da1a125074000a0800380004076500000c80c03160103440030b420f010f40f06032000213010032141054280036440b04080a140400d042c1c0c04084280045001001c4681042000444910042100f07004624905 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 560857616 1250 560856366 560856377
    0xe090c0f130f0b0604060207050a14150703033e040f0b090f0d0c06090b0304081b0c0616021201020a02062a03040c03140a030207140f21120a0e01 64
    0x107074907245103400201c0d0f401c100408107034840341c5481000f5a40c01c23003803003101c0c481d00ca80781c000100c0c45190350100c0e100304005886c00540741c880c5100c005075540003040490805944400410700c1c00380d51988551000c0200b0305501c206003002904003920310001c88000d041450401040003005c3c0403002c07010455251562280d2140120000a0314220b1903480031900500d0841c010001c001544201c80151a0140c8880d40d52503190341c0e908840d404211030003400351004012044a00081002e01c0194910030f000b00d440c0910080089503840c2c120b41c03061038000c2020001c8204524240907040c481a0042008504002840400035501c0c400070780080181e907156070207a042c40414843d4004421013140d078440d60703030509152561040120703110582c0c00390035540c1c02504048010800c445000d8143e401404030b9801d041050344107503c0401c003554001740781800f9081c25100c05442e111000b440d982085d100c1c201c1100e07428200b401032070700c00c400d004040054440c1c039504a80b4501d2144020f2814 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 560858866 1250 560857616 560857631
    0x19030c0c09150807030201120209040902040f0b030d051c18050f030307030506061201050105031003200f1014030a0609050a090c06090803090d0606030803010e090c0f13 74
    0x54501085020014018994039900460303110929000900070004059008880c030b962154141e803200901c0c040240003c40302000340c5403c00c030750b4002d450b411800030710020b400800760740041c00f16030300744a000d1805034071484080c0d02da00d001d00841001c940c05040c01d525006181001071210180ca10a10b01266506c40240104d4400402040c2e40d00382d0110898102c51800b40c903903643c94004640301400241040300142c80781c10702d403064030740351340c40980035800590030f240043d07400d5000100a00c1c1406256071000001c503103120354600c0c4114000c40e0119040d4079000c14403517500008101075008064009660341042c0d40101008509641100d903251240ca500207040042c1c281603005c14441400e2509004014500d46c0c80a01101c2c0718040314010141d80305004d44146825115140040d0818041841c82e8149014100810b52143c14005501c1d1b48a0352608190380082c0c0042454480003000c019585004000d86113002c00100c520041c170f51f5040f0000b4903d1850181074181d1035484414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 560860116 1250 560858866 560858873
    0x109151e050714011b0e0915220605040f0e0304090b130509011d06070203040b0c010e0a050706030e0102030402060301030f02181509010e150d1518050f0f19 69
    0x599032900d900c00c4584121405220203180a0072036207200031240c0e001d400100007620300072850206d5088014150039130965404004900c50540e0140d0f040c0c0200d000440d8a011031104410300070301c20708034076001844030300301030502084892901d480310745545030407036120024000005640c11101845c01c00b0500a80c3d0304042400c98102d4042c0102443c10038040c40040b80d4190400241001c2c400100c0b80811040504590340f40c4058600340f02580003080f0612000140300700034010502c0180001c0341d23211404804070b26000901d0016942e94210280030712060342c0c5801240503240302d0000035800d40c01d103a00014400e102c18800102100c140882190440d210110f101c44407490344c40c0072204901d440ca0300d4400310008a413038180b055401d44004954980a45038450040c000944440303068105c40c1c040c40600d800e640021f90303420805c408043d40c50007071401901585115152642d8900066207025450560203c2c4141400d4110640192131803000080c011003000790303e100802a80d4071401e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 560861366 1250 560860116 560860127
    0x81003022211070c051c020a0909030c140c1306050a230a150e01020f0604020f01121806111c05100302041b09080706080609270c0109151e 61
    0x41204104107008070700042800303001805002291016a446207418043c46c2d182140c5030710a6100039400580403406011056590303014400307162107402d0a00c161080740e190310403003403040c0e041014140c3c0000710301c0702c0d2810240c1d1440c00010300a5000d200785401c0030001228200c1034043e012a038032181195610b00b044d403140380000303001d018150f0182103803520420034100141d400180c0106842c3c0388070070300d03d500c0010f440c200c0803403003c003400c23a5032215401c00c042031151401c4141040360040c180512040103201c6c11036030f4400e6002d000721000782c1e854808196038913818020307030341001888a85094011220300103c80500c00100242030703a1003070506000c0c01d8603900044e4101d80350105148841282c0c01c1c442c0828400345d250000300503071720403026585500b00e01805001900c40307000718515050a10310160002c0d03041c401c030040021441100c0d9030f400c2240c6004401c550202c603440603196041200f100281038840b001d03184004120354068080406414480c0c0c03a105008080c4000d1032050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 560862616 1250 560861366 560861381
    0x303120f09030c020102010506061606322a0a080601050408030408010603060e0f030a35060103050f0123040207080307051801020c010e100c0503040906060810030222 73
    0x420849941e050074028a400c008100403400340d8a000e011039014680001a101104400d4240c42220401035480d42c000c0d0407a5000020031030507402c00604248403808440503050640729005146140010b0584064040840c003050902940c10401031048030501c22034501c1c28880c10100040d445030b500498151003641d10400590002080c00f1403100c0064024404503130140d0024824150041481c580ba00020a00b000301c0341d1080110441c1e5074000c0401c02080105100801034401c0c0394a0000c04004203d07a000117455418030030040d07203607003510a80d900819065025003840d03042540094215454050a05500c8403501e000b1b42c1c25603071901241c1006620070032454680c10b20200203807540c0c00180000348040440050601c1c1544000340c401001881655420040c4100c1b80511040b40a2070400b50104900c220903074001c01c10410041c4014500400001100c51510400030001c04020307044094070501380c5070410243e80c408441c2c0c0c60180d844805115492124182d030002002030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 560863866 1250 560862616 560862641
    0x60618010c1718130605010c0213090605070503041a070f11011e2304020319060f0c02100b12060a022a01060603050705031014010306030503030c040515040f030312 72
    0x1a1550b114000010000c0f80aa402d607030610b52400343c105008162103480c01128002002d8080250140ca0000c070b40c1805200400000518100c16807135800654404a6894000c5440002440100a90030300449028003002035118814105a04020030b5520035902003402c000401e49014800f08007076000400e00e1603a050342108045a105840019141130844103c001542c02080700741d202d00087e64610682d40140584440c40703003070007084500900c000007520883e50f60100710503050186d20a69801c02210b400a0264400c1c45d8111015100d21030807d6003e90350580a0400a1500148290b04892500000760310751a41d11b03243d0100d1060300d40300c095401c1000d0101c41e2a03c106521081c151117840d9401d121540d03458400359031500c400c1d1340080461005580410000f010502034441100d0141750228443d9921b449052858201352815809000c0024041299190007903008440d000144002420945041340d03185589030244009010700a04503c1d00340101c079070380e0004041059 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 560865116 1250 560863866 560863913
    0x20071a0f0409050601081024030605030a030c0209010b0711091e04140105070f0e0111010b030a060f0b2e1806050a020c0405010f1802040b03040503030f060618010c 72
    0x81d1982c54001400b4107a44c450b01088060020a4503d5006d85441040c1d0300c044a20a83e5502c034400c04c068041c000d0000d500c02c0654800380070440765824000c10b8487c9000c1c2d65248030440c118010040c1c1c082c010790060500010800c803480024146488050b100101240d090300555a4004031001065404142c03800703881c8207008000401c007460700b402c031440308840e008201a41d540300d810b54081034500307024800302d405281441031540c450703020b400b101803141002080029001c8046444c111001c03404652580d151100032890646900c10032401d080e08403040c03091800002e003440a0145031061450300721030800075030300d8154003585040002840c4200c1440e00d060b9100c1c0c0040040d04001c0c1840014002c140004c041843c0c5402100e05031036451121401c0249080e0070180c1e05c580181c202085107401b844002080c105800c0030394072860040020b0360342c0703160043d21030008250080c00c15100780c0052047c02c104600040d004400450300782001440701c0c4150030100502c004c00e80c140c480090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 560866366 1250 560865116 560865119
    0x706030f09170a08060102031e071a09071715010b03040609150c080f0c0f1b03070c050a0608040b0c07080d110c0f21090a150305060120071a0f04 64
    0x1408000d0041061940d00d410b13841e25081c004903100d00c100b803215035800e0103d4084000083c0000000e00085206051001c0c40300302d03040b01103030780a504862240c0e050f00070341d004101111101c0c82888030f080308207000c0d0814280c0101c0c01700034100c060084401c45d800c0030002604100307082c0c0c01591519040340300300c44030100c200341c8240502200e244074400142c0c90b90102d44e900d8942441603010700350b480740b80350410304600e0681102e50000c0b00000c2c1820740c0a00141403d01c401d000502600f401841c50001e004c0c201010b104c074200030b940c0b000c070030480b982c010440440c0784490100c5c0c003c41418903550b41d680d0242040540d44c010a100303c210305203070481036280e80d103070b0780002c1c94000d1075a001d131030b100041000c0c0182c503025030100c407a114600c4421548121401e5000400310880010700070200517480b4032240c00351862031500c04000c20f0f0385209122080da004034182d40007019210110a42d150451505900c5505a210345000345004504e0000040091402e03038188859101010b40c640d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 560867616 1250 560866366 560866403
    0xf0f041e050325030c0212070509150a08060c03070c0807120c0506100e130224030703060b040308120403031d0a110402030907152c01020d050c0706030f09 68
    0xd5003ca0000051012403250700180c0c419514201d0004a405440b1401048a1034086c0011489100007032696030144643c0401c5503901d68115a004100208400042d000c50500b4002079030816080b004080d8003180400010842d11400c907a4000e5503840c00d00e00c05540d0746440c851500400b000108840807000315040f034541e00c212005050350107401241c4203511004a4a80030078a2401540071052030000041d41d488111030964450324406051048041e18508010045c01d00f60302075030241080008c14089003691601030788004c2c0c40c9810b40c591a251640c0e5510726548100d03540c026050010000207000e05000e58001c01000c1409040303001c824808601c5a500e03005051422600c980782e4400109450030148240c0c0e210354400c00062038102d0078801c041607109c02c1c0b0b020140811800e0a80c2511003600351b480300011344541030407082c00e401e0074000682002c4020290400b006405e110560068400043e200e00b2500b940c10001444864003081c2d4003c0e2005000141881c01d1101c08800035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 560868866 1250 560867616 560867623
    0x918160905100605160605130614100608060a05220203090a1b0b250203011b020f0606060f090d0507080303040201081b1e090307090606020f03030f0f041e05 69
    0x80c900b064044541c080d1161400e403400d0140407021040307541da14a090000581c1503100c241c000d41442c421070104907841e61443d041d00d188400214a003a021401d00c110160580e02d00005040103041600d040d00c1d0920228260214601c2141e01c603170b20040c0202d2840000840c03410000301e140a06642c0c078901048466a51300030200e04a8079410758024124228000d4100740381907030b0103c4095031401d0784912004c080c003a03424031f00d210050004020400142e50034462004000d00d1912094003001104001a0521401d21040101c503000f070310801c00039945140407544141c0250010070340380c1c1c1d600008101a14107925008016103d5580c0c04298800d00001840c4141d02c01d0340c4d20183ca40d901c2c425500c0421400c0c1340c0000d4020300740454040c40c5844c1c000d1080540c00b0168440c10304a15100203890940903900606a959483c1400e100700f0303038140040442d04007058025491801c12128003151014020515124641d810004c01c082042d4004001000e107541241e02e1031010351070034510349 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 560870116 1250 560868866 560868871
    0x50316082107120b1c0b0711030309070b0903100212061e1008071404030f050c19120609020d0b0105011b0b1b041a0306040c0323060f0312040305011103060918160905 73
    0x42403020700e04829009001080b03901c9482f006c8060b003581c9281001c1928140c0080c46110740c0b41c01402865450300046201a00c2c0c841109041400300b800e285003444071600a21002c2c40c518201d69100d01315603211607503100644140c07450034030704550724180c0c222a05904a400c0c40800d0400040c000180a030b050030b1a80000c1c010002e41c1c0340e840202d41080341d44201a05418920740a05100700008522880c0c014410b5004080100e0f0200742c9074001540401404002c58289000800610203564000c2d80c06c0c0c22800802e14560780d801c0b1640700c50141060092421849a0004110000d01ca503484141c900a180c00c204070340300b07000310a1303501c40142c00482c1d178140501d2404c000800c2c254401e004107034400c000d600380c005903100c8503500359514910040080b60824150140d6014036102005030030851003090f81c0f46500e941c02c500d000341c00d507003103180081c194030f5051050208695440715050341001d001d090040180c20700700e9190341000c24a040000e4201c01c40e8400080c0300007540c11451 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 560871366 1250 560870116 560870131
    0x50d03030914070f1a04090513110418080c010204030f050607030b0901060c110f03100e0c04020c0c10170f01060810031707050316082107120b1c0b 65
    0x110109890a0b08699405440c46180700104902c142000100c10320300b4000790300c0281d4000d0074502901e4028000545100380c9405000440300c8141600307000c1c483c101d00380c85113000c803020b111036004005110345000c030312080600158000502d8000c00e42d400d504990007141e00241b0070441ea103030740c10302980b5034201b10b5506000c00e0500320b8100091408104241c16159030b609c50800b2000183c841100da003051030786917908043c5640e01001c00b47e408100301c80382440820380105001902da070403641429981120503009a006204814141d800410341e007000c803900755488215420380134400c1319600402141c1e25192065403041c005c0d91036000384002e0681f11941c0303440e005030f00e03104500c0c0d442040920005c0c01040c103a0b950302000102c104010240301c0e02410480381096140d03c0307001040c449201048a405000007040740b080381d0b542c0301c41e05410003030030040202803401c01e90241519013101d1035101c1c81f60343c900407185a03a8485950303120b902c144004244001002d40b60030b408440c800d80f54407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 560872616 1250 560871366 560871383
    0x1205060c030f0703050a0b0d050d0e06040b0a03020309030403200f09040b1513060806010f050d0308010b0702151b01050901090302070311180705030402041b0813060204050d030309 79
    0xd40354103044040780c1c0100c00d10b09101c4029580d12800314024040941082031041d12040180b14540da0480140b040718000c0e0041c010860b810700f009083d8a00070f407505401890f0a000401c030b1481144240d07207500405042c09a920390314400180e0a520503904000d0040c82c070b8078020b0100901c1c6009850f100d0000391035005460203d0744c1006070410084600820b074007541b00005d0246003400d410f80c0701c046000b8000030a0031200d04032810658001d0b41000440b03074070400c0104041c51000c0700c5c1340c00402051300d03070700c414207115200200780030014000c501e40d40c0000294403045458049605203080c4548020340d072140c041c00030b030407524100080f0b07800700c640c02c0c5004502810fa040c400e603070000d03034150014070b01d40d443d59860300700c80d200480c040e41e406900c00089051414501604501c509056030f0740c96a6840c00d84104012150b0009a0050613551050100b0310300e80c002c12680e8208910002c0110b505c03031140f900d030001e80715541046801914150505003015016000301d404d175446000c90 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 560873866 1250 560872616 560872621
    0x306170106031205040b2a1b041a010207030611280e010503011202010818071203080c1c0506030c19050f0607020f01050a021c05070203010e010c020303010510090906120506 76
    0x21241390080307001e04161800c2c200801020310211b41110640c504074810205810341c045a242801c141c189280980316015444030300703100349054800c6421000038003034215138156010300000d50300d03480d07030100a00302d959507004150090348000a0f14402540c4852386903038603010111080c580504da1200d132000c03900a0401c05031641c042c40590b4140c43c820003a1a48200c0c45400458004801a201020302115190455030000d4103200d00005400c0d07084031071006800c00e240c01480700b180101040c00140e400c2c848040c0950b40300c0f01040c041d84150201146680b150b0001900b00719034a2006a8480d0000001003401010042c0d04c41c1102e20459001d500c0210301424000244030b0000300960001c41c0d010004140c1d0b02460280c00711200c07030320490700050f45403181d082075800d0b800c2c00700d00416004108081145400d01581103140c0148000b4000d412601002039941e000600030188998204c02c0850140d621881c80d0800a00201c071f404c0c403a25648084601049582541c01c0c0d80501a8000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 560875116 1250 560873866 560873903
    0x90305031c0513050c0613050d0503090111060403080714160506060301060b0711010f050c030c07090c0e03060601050a1103120414030708070204050a0e06091e160312030617010603 79
    0x6051210f90f00040588004101281000b4050740280c1503840001c4241001046a07119440d54404581c0702e00c0c000d559800500300090100e002024061885511003000c10000aa03c2941190014828186100001001610110705000e8078401d2a013009090018a0a01c0303800201c0d9401440c05030300800078980c0b280c43e4240300d8864004068403c0c8100300b00c3c800715501c035080c0180b1503030a174075100e07042060104030384c1c0c1181e020204295440d4402c04080c800c2018611445200300d116007454440300c2c5001c404292114001002c890500401003090001d090244032820544042c0900340c0b41d840140035246407040070152007d0f100301449280c500c8042c0070000880d10600d030400039850405086074200001b030b0900a010300192515042e00508a00040106a000b9143c190103062000c03240c2519105190340742c949500d20b80d0107024510f5180b4072400d000310a581e0400a00c00c0c000004040aa01a10066008043c0c07140141001501010194041002d482c8039111042404c1d95914 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 560876366 1250 560875116 560875141
    0x10306080f06160915030b040b040501120308040503091309050d0f090b0f0706020c01020a120c09090506040b030d1e0f0504170106030228080304081507090305031c05 73
    0x103010780103036100e84049071815190a505528883d81031a01c00c0c0b80c203407a00c0280c03050888082000300400c0d11800103100510b00303801030348041e51003603404201e198507080301344600808022014080c088014041004d108040c401c650124030302030203c14913080710440c490003c11031800250307824004c82c10201000b503c40c00d0082030a80e90b5a0781c2a8409040c00b51004a0b41d00c00d8240c0910040d0030414180000d4041c0040e002c030240c144001616030740401c0f00a0a164140404002001e25040b20058010b0304011000c0688000c00c8001500e55201c0000c01e0080c111a14529490710412110a03d1943d2003803010b4907101088401c603004450000f82a1800b449001d450f05c080380d0103100500c07081c014144440800ea16103000440c000d42d40e5008200b8009504460280c48003405281c141c844048200c140010140c1d04015442c280c0703002d034020f40700d800900c030281d200c0a0740d50219500034420903600c0065900401580e0b07458120810446200072400d140103071460400000480d0f00c140b50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 560877616 1250 560876366 560876383
    0x3070b030c04061b0206041511011b0e01030605011b24050613050f0c03040f0b070801140306090a0206090a09020406020102090f100e060307031401030609020306010b040f050409030908030706050601030608 90
    0x2c2d091b541410b0500103e0900520040000c00401644038186034a50000740035080314a00000700703400a55110103001407103101e072011514103150400b0020001c0d6640146110714100b180103404007108118a45110015031122801e404032000840070300010046512040c00703850111f891103240349451141342c0a035842107a407460111404400100503400100003075034014070421220415111355515040400e5051b100b134800902603800600c2106000c000c000283e00c3c04500600c3c103071030b0119001d82e42d802d10010003030103044041401400c54540d900f03800041e01492109548503601c40c40001d0003900403109061203040d03001075034149400c2c0301e86421083c3d2040d9070740d1a44085580c060081c103500c043d2102041680e81c1203080d020f2101c4460050213948a0103000c40c1701843c50042516145040e000303900180740c20003003041070304000c454200c206c45045e1404a07950141c1c0c02e0a89040c4940c0d4059800c3e8000001c030a07042009035030100b44a42002d0320304115568460380c00c2070391031584 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 560878866 1250 560877616 560877619
    0x6130b060603070e042408030f04090f0e0f0d1d010503070c0c090903080906010f06020607140d020d2301150509030a0203150132010e03070b030c04061b02 68
    0x10000310300356040c41ea00559000700d09003040e2031204c2950000c00c0c00c8070189184800202eaa9404844010700580030110040041c03100031418103500c021500043e10841c0704900b038880d9220f81c0c5520380d940c3c58212800c48a0610140c031200961707100f4003a1107240c418a0080040c68020f00052032811444207002035400603036030941595106101034841152000040d1100216403000003103405ca18040c0c203280c1c83c481d58451040e81001c1705442d00d03001f0180c11088070340700c00c0c80703050120303643c000358042d8401810300d007060102d004800c2203a503d11a0311803101646000141420060300c1d41d0300042035880d01c103005000c680d0302c501e02c0e190450b0000c0c0038815891640b07008020590b807040c0090707e02e0203c0241a28001204c03980001e1400881701800c0d2218000007004000b0645c0c3c01010303000002d00c0440290300d0500800c2208062485101c08030705001e244804031003152810803580e400b802c0e968241503601e04000803d0240b540245c8a0703c40054020343c00d00852080001e40c000c3c410760f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 560880116 1250 560878866 560878883
    0x1f0c32100204030c1206062c0906161b05070b0a110105010f12080f071a07090810050a0213061e1803020f180f0a0617060c090a0b0d0e0613 61
    0x504d111585c801c40ca0b1902a03400e19103820020903451b0043c0300892000b141c0c0d01030307486d4001c050a084454008010a0240190414402c014400c59502c0d4030f412000580d1030700110800d85131048120010300008041c1c081d108245022600f0042c0e20010082050b454071040002c94240308110700b43c1e942400348018a0711040340405c000940c28882c21015481070104504103001c4d01c09028068102035410348541c110710191220b656a510f5903241c114661340350040c1c0082c200501140d440003031246441c091981d50300000c02606113941503500325506501000702c42da58441c4010035030320401039035190703182e1030341d540380b034424000c107255600f00740c8952100c0c50480c80c54003003080380d10003031007150340084803c0d9601140c04030410043d4461844c84011030038506044860038110341881e004400c91024420b5a100040400500c5075400800e149116684036000408102864155400110070f0880407a40f82140a069041000a002004203d41c241d58a03800710340f0392842c06040c040c21600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 560881366 1250 560880116 560880119
    0x10218011803050303040c0f0e04050307030c0807020301240b090a031b151e030509100f1803080414061006081f030614061f0c32100204030c 62
    0x140580e03500069000e5003844152050341d43e40f6810b04541c011a03046039002c020000900546c583d00b04400c1c040c20302c61410038068505907490598034811500b0107070034000003514003410010f05c07501721142c440c0d01500074804040100340e00f090040b191303844490031131291301c0080350186980b425900044002000742025500d5a10b41c03804131000201c5a25442451101c04944894442c120008080c0304d80d4500400d00401105c508900c21005110010142894280415000300203400c0c6e04100d44160700107101d0103010203a20081c408035103d58034000d02240201d0505800181a038841c0f0f01030054084502c103905616916200101ca8000c05000808400d10040d40305040480e403040401e290b25a2440523a24a030302d20361480d0740100c0349141c8032403541e490701e0345002c0e40d940c202c201504c2d200002c4008a5040794801e80410801d001c020f40c0c00c06403002e03c1b003402071400000c110012035010a103440e134440e0280074040b0100442d0341c49909886075182481d0720846040341c1e000301d0a404240e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 560882616 1250 560881366 560881369
    0x1020c07150212130504090b1b13030b0c1315020d0c020108010311040608010e0307050f0d020601030b07090b0d020a02013912050903030405150108030706050601180b04090b09010305060c090d050d1d03010218 91
    0x9070b01420060548006000245800ced00c49500f5001070842c0d180200d020748803200001389000068035800040290035407450700181d2700300280710f043d2540048000c040f551040040303002400240d01c488415802c112146442e1a0048010712080b402081a130f00074415401d100303951a10a900c488005030b00c04001040030801251095812050514000340e11303903038680680070203030070004105e03503003e81c0090207058541e0240300300301e42c0c0d446100640e840e541010403501c0c01c840c41205404a94000c000316002c02600c00e05565400d0220744800b0441814035100c02075481d00219000c40e014410005030965400d0800c1e03450b412200000010352030892191f81b42c0b809410081d15050601403000804130507400c03009101000f41961b120103541300c62508550000390303004440c169018508800060020400114105500c049049800d47d035504451000c43c0c005220414003070202e01402404028196121940040915011146101013105a02014200d00c00c168500e46c0041e003240f84100d69 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 560883866 1250 560882616 560882633
    0x180d020f01051b0d0f1706090a11070213140f0103050c100c022d04060b042108040f060305010501140315150c01020c07150212130504090b1b1303 64
    0x24424901250f0760100c0002001a00c0c003c282540340c404100510944815107074044014882c0041c981c14180260801c0000725821000141c985019141c81e0140c510101d00342d007045828181c0d0190540c0f9102c08501e90f00c81c01401081c4100c58899005004210340f80c041c440c2d0395040e00c0d000f8025004144520080148060790302024001348205040990050303a42e401c4032460031806810a40c0e10017010002c403488103514001c000b0f224030314010050001c8240001600c058814078000c960b60403402c550f014401d03402200c4018682080003030301103241180140440304542003914180581d91721074005554066102c0751000781c241c028800124900d034090b05401543c1740c080e00200480c100d04080400943c0f00710418072240e0f40008200020a008211002c010120710711441100880e902009450310a0224088031400780880c41c0500c0304840061a401803000030801c20240c629490883c0040f503003144d101078184202c2803d4025943e040c02212081146a540c0001440c15603841c10300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 560885116 1250 560883866 560883877
    0x41202280603230a02030f102105070801050c180103020702060d02071401020f04050102070f0501090312030b130e0d0c021309032f0709090804060e180c180d020f0105 73
    0x380e40c1811003d821008a1140040c0c004d0708464005a038034640542071641c8048013030b01d06243c0d50000b010803c172203011403104d540200842820040341001c1410100c0c5080b4158015100e103510388024403184203024002455a0b030708204807130568001c0e03035005404174080e105011b50050b034104070202c1e4424003940104502072042c1c013106002c408140300d850890300500a003410711400024203102560301002410001c000803412a41d0280c02c0c10002004281948000ac204401094040d110103020390070845d002000900381c400f50640302d03502c801c01f402e000003001c6064040c045221361160304c2100c5005078103401810160007403a10003035181c000d01c2602c0007901088030007920000300d269100300800d2480e0a5820503032400d880000d0300c0d405d086c000e0b4004e8440520705100900055182c5058400301d81c46402d02c07106451180e4045001c0c45038014a020b00c88181e40300f0451001c2103e0040c1042000385c288240d0f80c20880c00c00c1c04844c0340d0a40c4d01a602c0001250071440e191b204500400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 560886366 1250 560885116 560885141
    0x30f070e06041d01050a020c0c06280c050a06150602010b0d08090102010b13020306010f2c1c140c1905041a0a0e0a0b062b060803041202280603 63
    0x107110011a10b041800c4a5080e10b85444087d00000c914001120810400003001021285d481c80c000c5000003006e42d501e00e810301304e002041e915080a14440c01503c100b810700d86c00100f6910035074903616180000b821202e00481c1d80b402c0d82c59010610324414418005c80c540090013483e5580f0480d1601c80b1144c00400c041811903480f0070000e41c094640b00741070801711402c0d060240e01ca051000014090b070340400981c01c10405040c01404102c00300300100d410703441a510600e01105602c4012511540300c410101c414044422100400c100e4620380510b240a808d60940316590781090404c0290741c0300100c43c1a003085008000c2c007040c035166006007414041c9404420951549502180301d0101d954807a280b900240010031401000b14080c4084840e401c6400a02d8281c10081000d0501059056200c1c406039080c82c0d42c4240050b9802070010702009821280c50f01c2e5610001d114201a41c80c080340103030f458215428800801c2e050203c03242c086c2c01c2c642d0f5251420300200b117004003e00180103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 560887616 1250 560886366 560886401
    0xf06120b0a020d090c0905070503040b0a0221090a0b010b0f0d0b04020702100c0309060306262a010e090108060105011101180c0e1003170c0a050105090c030f070e0604 73
    0x6810081c0c2d886844550741c8248a003040d17492a0400703040444000030241d2090003002c204200002c2d102c4100d403a4081550180180c540311040360450888600c03001c01706003a6000014410401000a46c104c0000e00c00d15070040035071780321440705049001c2c1d8180d4162441c010b00caa441d8035411a00b0072042064081c0c001800c004094000030803501e828003120020071260340410041c95444080c14000d414141414001d40d031500c0b560110440b00c04045c000c0004d10070040e043c900105000a4540034130a005120344030014041000100d02000c220901003400d14111380d140f810000c0c071590403a107040303010307280c40d07840c0c0001911020040c0d40b00300010f560303c20a40c1071880c00240b003024001d00030106070010505100605580c3d11002c0c110b00e0005d550f1500801c0003481c40c04140d91001d006041c1c43d500c4039812200300345403a00c03405000f401e55007000c08000180b8000640800180c0040b01141d18541c12000c21035160800da0007130340401e105080003c1c0040c14540c1041c2401003418812 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 560888866 1250 560887616 560887627
    0x51e01180807120e15310f140306162606040b1807050a11010e03190513030f0f050303090d02100b010801030605090109050706050702040f06120b0a02 66
    0x1182419040000c088450000201da84018401c806002001400003401c00c8902c082101e80060fa5480050409204440b80000c0190f068000003001c800d80600d00c10966103405010704410b4034412403030084601210145400003070320300300044a2082550050054882c9880e411f80c9038800050300b404100510850b408901d10800156182030320543c900300420f074403814800100300586050340c00c0540b00708045c183c5010a5842641242c1c1c0209550a2140c0d46500e001030035035091050b805030140035480d04c0d41e60303034500c000840245007880c462890261280003841c1c1c1551140503034010b421032901d00040c14800241041c0f078a11645008540c00301c007034070403030780c80380d01d5588211f5050342c40f900300b0700900c105550100b00025440006001c03d100960110b00000e04821051001030026034540700401c891040a60010891640150540b000c803501d81030041c01c40e40c0036507804c038084ca01d0b0414498a00300e103445035100351201c080b40e41003101d0844c1c44164075000041c0100c424141e08010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 560890116 1250 560888866 560888891
    0xc0a0504030b070305011e06050316021c230304080f090d140c09070305280917031005060702151305030610030204061502030f1c1e05060409051e01 65
    0x641c43e229140540e004291581007083c42c1c2c0408001180c4a40c215038015401d00c800c940003c03e907607000740321034038400d1b09030128030f800c900e810821111810412031300c000008007954403540d00c0f0089100708100b5076900003a1040c001c101d20045401500c440300c2400810b03003403000030008242c4120700500000c2d240d80c0340d454080812800401c06070041c1d00c900000484c81c2404079201e40d12806605003000649461031a2014444915880031280541c044d20009a00002e9001c004516000040c0b070308090301c2000c0c60301840d401030302c1c02c103c1500c00710030004c4c4501d00780c0e084400e03031907004e40030b01d20405900c400803a0035041419080036a0f1891132000ca1036480810955215400031040b03606264550b00500084031401d0304104041448800c80100244d00002150303090f210201030240e960b15a0541c0000c411003040c260a00a4207021000e0081d098224a414141d21110000c1083d44c9170340b01008201d410b5140d00070815005803084000d014542c08802d241c0211035800424501e000f4013 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 560891366 1250 560890116 560890133
    0x30311011514010807080c1605030d060b0c06010f1208090d120203090126060d0201050d020d09060e060910051003051507020d0f0509091b03041208060a0b030c0a050403 74
    0x1c0001d50b50210201c803000e041d6030300011203500191141040300ea50705101e049547c1340c0c85424518261100c82d00d90000030020100100c031980050300c03104200311070312030500e01c1c4654068103681c034641c4149400411841c10000e040021240100011001482240e58030146500040611607129510710300074404589260240708190915501039941c0e0301c2c4080024080300b0041703009000400e60800780000071081c2041080e040401113841035a41140c0744012609482800e1401200c18000704101c120400b450308107400c0c0c20302c40c1d441446607040c06011943d84500c03c49594034264441c7e00008074244c0144d0045400c844070000d003166140c0c41e51101803600344181003c100d0842c0307a50400c081c803641440140a840414580b01c600252850b000408074003480c2d012500ca00c2ea04d80200702c0e4104291107103129045400300c1c041e01c038682420311400c480503a030b40040119058500140d807170326000d44030300e05680c9080366a80c04c0d522180510501174001c1c101000501c94100030201c04142c424 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 560892616 1250 560891366 560891369
    0x2071a160b01051c05062703040f142b08041505130b07023a14061810020c10020318010c020c010503070806030c0a12030e03060601090303110115 64
    0x341900801c0354580020b0006000003070751204200300300d03030075000001a00410029040005507448110365900344407007841400004112404600c4002000035003a65444411750840c0c1402c81a014003400042c24010758490014100c80d0240b000380c40301c01036030324440f0900c030040e014440250400da1100420b2031121101c01c00380f03022440c042141910701c41c2034218071001d4000358601606240140e808505000c41e1301c4248000780900d12400d0403482c840310f1414500d542e106406002101040c1040300b208041b8445007044c50107035400040d5072103000007a0807504070b0034200a182c000500b20f0000c0c02500100620b014030300480700c0c806500c0140c0e001550040000c001c107076000100d01026107085a15580300710040d904141c1c95010a61781100c10b882d4041d40909090240b40d031600006410807400088096001d50103007408030b4000e40c1101c1098406110b500e0740032000058004050b51003c0440740d090004480e65024030002e44100701c200e0b03034116440d0012800d408541d9410386880241d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 560893866 1250 560892616 560892623
    0xe090a0b07021612020a0b1c0c05030403081503190314040f0807120201020c0103020c0307020a2408040c030f14030301030521030708041b0902030a0f061502071a16 72
    0x45011141031000d8060f4030001d0042010f08000e00d080b07580840d9406003288181d800004000c2005c40d0f0440300740c0c54902e0078101c0b040c410420107a038080701030480d810555041e40080c00c403400151107000c1c00101001c803440010020303c0e0000401d000d036440f003100345108604115048034039200100c10040940050681440c11014150520040030300e0022240c0c0201c1c51181c501d249807001d42d8000c54038003074003a800c0c6405a5590030718034810f40b440c0304080c0029003022100000003030402400701c5d0840f035096805200380413002030303060444003000700381e4001d00f400e8020042000000c034942607034074000f44501c110301010f804000449003075410990050701c1542008a503c1c0b0003003428100003104204e525841c80c2503042590b0000c1081d00003c200400d2001801b41042e0f0300c50302161180000e0244200c2550740340b900d1412440604032200c9120381c0b003414076402003840356042801404066503940203201d160b1402c0030a0000d4814464615a80e00c400c1011080740444200820300a80c003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 560895116 1250 560893866 560893873
    0x7090c03020906031e0601021b01050a090b1201060e06040f0509181603020301050f01060c120315031115040605071e080d05041115070b060f040e071502160e090a0b0702 74
    0x2001107005c0000c90020002030440d048411081d907061404000344101c10420310700b0f171380c07181c2100c1011350742c1100350f402940c228040030482e40c54141d1070614840c16200c4594803045a40c80708410311609000701c0c0106c83d800000c2c007800f4461070800380010340d405401c010090405032101140141401c590001850383d00354000c5007030007503080901403150444800004124191315140f00108103400d0b0100c02030101e090440e076070107601d1090f040145454200580d10030400e41d680360219965507180403107801200040b840c481140b422600340d408a41080e21910f16103103e0380e072107d000c841d2041d4607800501c28200313401e021402c0803000c1c007101500c1d040001002d081c1403c24070b50045503112658070400d80709140754800783c4008140c031030040d44061a14403940358440001d000a034800c8070190040d00c0c0101c44582003500241c00011500306143d584802418000c2c201d0f02d4181a2180210b22240d9039020811a8086035545501400c12415a1207810551360341c005060320955903400181e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 560896366 1250 560895116 560895151
    0x6051b0412050c030d080c0d0e0105010810140105011b1a04240603030906031104050603091510060e0d0f0204050403021b09090a030f02120d140708060307090c0302090603 75
    0x2c0410034020007400440081c0307065040514010300c1004028040f91030b00b071010400c542e80152641084000d03d00d000000e2129686034103006036101d46050810070f80c513003401e014030390000446000074185c4006950303003191b90b440d403980074414401c24a812640d00c0c01400c050111411592861801940b19012295000300c01c2041e5400d07040c991910846014501907041001941109960080f5081c5080110b0005181c0e40b5504250141c3e5001c1c54100c50000200868540042880d8100148401a0000a0316518401c41500d11b840c0242004103800c48903115041c9095500d1030191031269207c0c01528002d41e001c10b05031034042e0b8048000d41d0211429980d1061600e003603018142c4151415010307850101e03400355071085c4029014003449221000c1644403442444101400c10801034219601c4001c40903800090107030b107072109440b80b4180003184c25584202c0100c1c1c007903400180144040b5091040305802004100c803070b40c083c0743d401c10042d459500c80c03038095481046036440da4003414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 560897616 1250 560896366 560896373
    0x1519140a0b03030a0225050d050c030f031903180f0f0b01060f020a0f0c0302060307090807090903050702010311090a08010b03010509030c03160c120b0a1109010c06051b0412 76
    0xc0300d154000074801c1c1c105003c140072469001515441e042119111500b070700380346c5036070000102d03c51f030000c0b500085901d18090a001e000203224000c200c081d005c0310700720000b001c8407640380e004070310040e402c01d110348003420300b803d10035000741c0c004d200007030320404498409659091078210010740440d69054114218814082c0c0b0001e03030350042c102401c160300da094000000a40380c011413400101401c185148000600404041c1d020207154050201079803401d1400018100c2082e6209a1070b0520603001d000c039100016014006440f030b0303d622041e08068259005401401c5da02d403917118214424440d01c00240d0b01c02d103c0c04002c100c2400000741034030801041c1402d56100601f008045d91003005601c1c500500001251300650003051034402e803002520f48a002d095084c1e21100034848001911010720540c40f504900030701c06514100700c2c0c544840c1000c6c10314000c4c3d0301034074041b81c0c0c000040d80106180d038008a500104611070141c0d1820b6a095250541d00036030410710200d4584581002007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 560898866 1250 560897616 560897621
    0x21911070602010204151d10020a050606030a030f0305150916081f03140c090403050307020c03150a020a050c12070c0902030f01060509010e030f010b100306081519140a 74
    0x181c080740c402545082c1c00c004511502c400011501c03030810a201c405042031b500c062a010a549000a00722084c58400b104001c0d40d8088006051350301d40240f03c049034603850001031001075560b00d505d03080301740d40301e1000030303801400300824002c03104040c41d40403030300c1e6031326100d80718400d280b03200481030445036aa000a080c2d12004102070316014844407242500000b036404401280e5221a0b4806012400c00075941040444c1307964507040b000381c0c0240801c154010004d1880782403198203d411030000d003401c15581308c07000940411010b0881e008550860260f0700144418089424554a0032100d418114682855207003e4080c3c40070100e20b210801564892550007441a0003040d8114204054030901c080d40c181314031014018000f482d421164011115072290040090039165800d025100c441c0c0a4820081264800c50503002180c181a010384070305020f54001400070403a01c480603407000c1281c20043d2544400c0f000c407491f03c5040c040300d80905608a010700e0086800d500b4280e404000303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 560900116 1250 560898866 560898869
    0x4030f170c090402090d0b010e041707020f04150b040b07050c0907050d0f0b04020d0501051017040224031006181d04080c1915050105101202191107 65
    0x220240500600049a000d0402d5501c59002120016030714400e4000040144800d00e800420f80206080006039411001000921882c002d10407802d030103904209410300c51107020b800a502011511b20001d450615502c41d50520300000c010310207042e19042950619041540052003c1400003488000c00a00340303c0c1c1200100d041c0ca00240b40c1c108070401614034010b418411a0075542c9030050004c000690300110041c03074010b00300315a10180c0a4200e00036000c05d00402303024401c032043d4048407a118400d4400625541000090703103850726401c11440d5008000080ca03498689070440000c0784000c0015401003103500502c64421b841c3c07041c003a2130098035036102d1440c2101302000300042103094a080c501040040c171810350030b80d61413800c0e400c140254001c3d15081d104002c038140304101e03042011403000340030b410440c48200f0703102503103810346100b40581a004002c000098943d5801442c501080d00318140b409400d011a20811040e80c103042554070300002d0100b4554a03503c1d01c10701c180d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 560901366 1250 560900116 560900147
    0x1b082b1d1006060c03031515120509030a270504020309030409050907030c0303031509020a030b18090c060d0906090b06130c090b0903030f0304230706021f1404030f 72
    0x42e24601040a4400c10345540040c050548072101ca06d0801b00c880d04e001d001c0c202088076001401c10120004000700d0001e90b080300a10301c1e21022030301070700c0f000050f519a074002e60f0b10036401300b95018440807102c0b0204c0c4000c0c0401c100300780206403940e03a80003035440b4003a402d009584461034002400280c1d0000341421006812030003007400401c0c40c9036410400d884c0c1500703010648820b02503036402e042c0143c0d4807190515202050740346c4c92551642054003240d4040752101e80c0c0f05d03c0328120340c20807181034075594403e0340190086c00241c20110f02410305c00071201e400240c540d1160b1200c4003560724604040b64501c1c40001008084e01d0050075171501100305400800024500400c0074050b01424000e86180f001c01080d5148156420407c030742d0006504006140c42f0b040ca4617020b202c1c1c108528000041e0400310425404480700042d01c00102c0d022540106401d003403101481070711101040c040303444540c4540300c04010500600b510341c002c030712a42d0b64000130280d0701c1d002410460781103500c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 560902616 1250 560901366 560901371
    0x1003020309060a0b100f20010f0e060c04030314160b07030c02150402120a1a06012019110907081605120c0327030a1b082b1d10 56
    0x91045440c2e960102c1285c820301d0138084a5260705850a69489440d0050040079800441d04494405c6040d044002c0c41d00040c4014800c02c0d00401c41d498079a20200e5101121034400d00040000c80e00c0743d16203440100310b1440c2140b501c84410006650008840016913070781c0e41300c10a12810f49d1780351094140e50021440a4640c0c0668000c0d0004461300c058006445103086050300e24070010140141140268405220010040c40305000c0c640340c041298100c1c017241303050000c455181c0c0c41020007030075003d030b94010304403910004040c00c200000e807410540d425a40c1c0301184451b42c036035001040c01900161144a20344c501225121020a072030844681084018403100c03c101c40800c5a60360012404801252030383c1d2900e48452403218422000840382a03222240100e107140800100f20491460351070009042d00c2e0103406459000003040200360050821282040031810085c26130038030305105943c0d481d07220712240d030320590b101440c26600c0c8041c1000044d92040041000b03076100076403402c05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 560903866 1250 560902616 560902631
    0xc15040206071b12032c061903150602010207020a060e0f011d06160b0603070e070309030210060b090a0509040b13030203120c071b082a1003020309060a 67
    0x3169890003100300041244034100f90240f905600e01d000c0001030440d2156040360780500e07060007070142d58495410310148000d0961014003031b2940c0c0b809024040301901403480c4c60001d03524540300c0c022281c40d5008242d5105103440502c150810f0704401031149500260703c40110740100700c0b0260141d4000c00501c0810040d0150946a02c601d41c0b0400d0002d080824116503c0f058145040601c02100c603482180081c0e13881207400c200580e45d50090140b04900d186907540010305030b0f5800e05006000b18103010324001413001d486900882c41d12440791040e126255807405042c1d00380c40c4190032408543c231000c07070007600c20f0800d00704040081c1811106105203081a48648040402c0506940e2800208403113407401e060080040f038000b40c580741c961a090386400c0400758a5a048103000312200104843da002060b06030410100c15650010050030844d0320046c0088003908011900000190400700805441d980f40c40c60034015200c15100945d0ba0710b007030349040b81401070003045207182c14a44102c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 560905116 1250 560903866 560903869
    0x30a0804031a061f0513090e06130809040b120706080603010e03070b1f030b070306090c020c101803060608010213060c080915121e07300b030609030c150402 69
    0x8119000000002d05907110000329074003141c40d88549484400200b04014000887d088258062410700b62000140c0e503150311100c401c8100400c80d6900030703294042c1403000081c1842c0982c4194038214006100d0700c1207070700018549003450030562250012401100c00c01020741030030300862603031143c4a805103140ca0b003503640b400784004000c0c3c40110081d10881e00601c9554082040340069030704901202110314041c8030050140105005440700d840c1060441310b070541c000500d0301e9507400010704a40c4440c81c10103040300c4842100c0300c0404088a01100000814035520510700504200c2001503a51000c00d040e205c1c10b01c1d0789911501c10400c0501c0218013180c08002942d98214080f41c544001d95200030310030446000c0e2004a0000381000310920070480e0300380f5441568404000307526180b503a01d03014191044030040102d2046000c840e042501d02802d84400030030007180407a0b0001c0c202c801500442d1400400b1100414280c1c0000348000313000c00308004000080c26444510501c0703103050b07030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 560906366 1250 560905116 560905129
    0x16140f0102150702030f0c06010311090103231905071514030f040f08120609010e060f12031905070605011e0311030106150905040e0d200a02030a0804031a06 69
    0x400742c4690740082c8001c0380c0100e00c00e0040300e840351440041c19440c0d011f0b0016032510350000b0b02c012140f0740109110b0301c602e0b080c1601254100c981045590660002007298030708145551005c000303ca01400d180442d0f9a0715800c1c00703010f0540140018819181480320807001881310400c0042403040642543c4501207884040765405440740c207213070846803602d15100181d801010710080006c00042108468490300c84d040c07610400b012035120086036a5690001ca00ca10b054800c00c1d08080070003008501424400c0c80c1d5441900d00100326403a00340404420341400c800c081c8004005040000c00030f06018036400741601504e86240008003048603c3c050800b480c443d840014001c250508010302c107a90294003000050809116007200314803880c2d0018039504642c06210f2142d0b14252200c003110f000040d100000e013400c1c2d1a05550308a0100b0682c6e8071101d4091154018440c0e1000d0b1401610248022690b492041c040b8940320760a500c1c2000c03030b00c5080c0c8003904840f00c0e2582000415619503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 560907616 1250 560906366 560906383
    0x6090203040f120e030d05090405070306240908030304080702100302090319021914010f021b01030e2e0507030504171c020301080c0a21150b0316140f0102 68
    0x440a0703e040508540540d00c03039419600341a418002d002c0946519900100201b41c404800c031020032490f41e0f409410b9048a009024030118003859102c002c0d08080920120700604d0400d040203490385075241c0d01503145600403101240c41303000204009045003480c901c1480324100d181030550505c41c440c40400d1340c0e082d00c6070307012905000d0501c1c804107540300d03000ca483d2030014444600030303031a8441c04403407002207107601072500080404101016552020982d04841e0403414140700270521148011009000c014103420301c2d0b80100b01c1407a02001000c2d1041d03800d16003a200c24820400c1d0341c207004045580c010304100070b140c28a010030002941d00940c40d08003059a604a81c3c4520405003000941d102d49205400720034800400445c01c2c1e180007613a400c032000101c1704103120545860800316101c507011300d920640c03881140c03503c0004000302841800c0c440c030600b0000c0d8803010000000d04e0441ca1482d44001c0c1c1031490002d105890050b10180f080c407100f56030f154000981c13140001c0d5624000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 560908866 1250 560907616 560907623
    0x3075405180a0b180405010c020f010c050409090215070b040b0a050f04140c0301060b0319060b0d0b032811010e01050703030f060e070915020a030c110a170c0406090203040f 76
    0x843d0000303c40743c1e5410303104440c2a500c0102814141c40d15181c907030700800a05004074094850944006004d50050080350134806103a51410700f86840c090725072002e810040d40c202c0e44010054010b801010b00c500241441c42c5c02416403102909240c104288558406412414014101003c10801d91100049d00d50415489984c00310b40d080364850712410084018103842d03065081010000c0c4416200c8040d500404000b84481e00440f0b047d5410307001c40d42c0318420305400d914244050303040200c07698003501e107101d006015607200d10002196084d0380384440004410802c0114520402c0c003e442c408240c3d5407000b0300700340340b01c1c610078800a0214010407200600705510758000c925050703201e421050040102d150401424145400d002e0068112030203945440440002031900e0b0902c001000f0941c5070309600d504109031031503103902c444181030743c000d940c0101c1da018000442c000701c08541a034045020000d0201c01d6050420041640e28170340c00218244c2c010301c10700c40031030000412411120361 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 560910116 1250 560908866 560908871
    0x70509010302061b0f07080c061206010804210908010b0103050c03060402090301140c09030f0601050117040602130f080c01021605040c140f040501030b030303075405180a 75
    0x1901d06100c03448149094411100d17002e0340c01c015207001070014040058036021782c10341e07061700b01e007400f40265406401e0f401e41d249220000822815405000265001405000c00c8100305001c0c02d104040300349089000c1c00000c00e212070811241c0c1e005e10802ea09408240717420700c06824803940316641800054036040c890303a07000a2184955800f544402e002c0c044510f07042e05540f4081101c20150307002200290f0081c010074142000000d40810514185c8405031540903140201034500341940340c00a000f2180035a0030804006080860715801c0014620301038024130050400003006c0c00d01c000b0460090541d4880801d86142181644011b01070b105e05940008a80946190482e40440342c042c0e0b0200403140018101c1032500c03850300034130035103100b030300c05004a401c464141940ca00c0110b030b40e9400038218085169488004c640b1085079490361030700c0c0c0d03080148a100a40c2c1c10360400c1d444c2010002c10950800c2003a01c1d0682c44500504045807508182d8610840c0c80000d0071300101035091156 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 560911366 1250 560910116 560910127
    0x190911010809010b030714040b06040305191a0f0106020f0f0c0f030a151a12060f310c060906020d1101020708030f04021305070f03050415020309060f0907050901030206 74
    0xb000d6120580540004003100c0c203869031a0403201000d460f0303c1d8202d0065050082901c60760404104032001c80364040014035800204101044450710041c900f1290b0380f0300c10b045419102105880c031360090607820040a440c2d45481d202030300d0402103020881d00b64100301e2403142c1c2054081008885584160ba00505515415000904025402c0f0004040e041d1060601900c10fa4950100000b1303c0310070310850744000454100a21080c2501c02440c07a680301600280c0f4038a248018281c100c642a1200240321041085018005903062216210015080d480c50203000080c01440d0081c402c07414003660035070401c003009480d154001020300c1440b540500491200c402581100d6415030007846098490400302529000810706031001c2c1d101c2c143c0420308100301c00141c4a6103003d01000e4956081d000d801c001c5c02c4c0c2c05000001e0060b40c1454006144601c008c60900040d0300c60811303540038207000d20f0f01114010100001400400302c503485810306203c86c1d1510529079043d81d40407a0f00e2910740 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 560912616 1250 560911366 560911381
    0x1c0209100e0f4011090d02040e0a0501021602012606010c0c050a032010090515040302040e0102121f061b0f060218060f030610051605061909110108 65
    0x15850203002c0001d0107004030211004a140f056031486105000b80030002140c5030030626401440700883e0300000142680e030040c905a40501c0a0004600540c0d035907607255201c090890300310008200c51a01c07580703064400c641e4802c007861904000400701400c000d01160712009074800050605062243c0d05031b0ac05c09020819408070000c150003081c1518440e1030786002400182484940182e244100c550703811140741104041542e03400a90720910307418500001c0085a040c0b401d20b01900300001c001c04005a12a405001c111500d0000056900d00c00e04c5841c2403100e500402c0c0c000034440d50000e9003081c1c07a010304513008450661805c0e0359000720000d10744121481c41c4100034003807050801c18404012080c0c000d8038000c46061070000100d1016428050140714031003c1003a01c6a0030000184280340c400391040f07240ca00c902c4e10900f000744200040ba83c00e031000406035130581c000c2c010017403495041c0689004040300c0040c00d110040c5c165440010480001d601d081c107000c1000c0004450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 560913866 1250 560912616 560912659
    0x70e0901080604023a0201030f1802061608210603030307020322050325080a1a1b03040c03060c0509030303040605042406081c05031603021c0209100e0f 67
    0x302e00100804891041c000f0705000d0054071170714402ca0200e410480f14a019803070900c00c00128005500c0503050105855080201d40e0340101884c2d10720310082020100812080809002c12081e1140040150b0340c50846044e040c0c100141614031907801001004101607020096030f1a00701a034007104c2c0e02c035550180304500e40c509600100e4151254803840c1004244808120065500a141c440c041d82d454815050b03d80b142914044c00424880103003080981c3c2c01e030364041e804240241c040400c0441544c3c984240d03442964155041007a1131000d00034001d481c0304600100c0362600b0310514000785000400d84038040240040c0c440b958400020301805040c0d035102d14004184010700d1258511081c4104c0104294001e20025100c5c0d10f0b003074030104d0052042c000d05c00d4100d80f1340c82d04541e940e68400b1801c101c0c00710703070208160302401a01050200b8802005488801c0d50015881d64841c80c107010541c50709000810400038807540d80307000ea44907144c040013101001d40707000b0b41c1403080142d013245 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 560915116 1250 560913866 560913919
    0x5070e09120a030207030f08070e090408090a06090801050705030403081914102402030f0a020106030524070305010f180207151b02030a0504061b020301050f070e090108060402 77
    0x18544000202041c0b0103030b0560041019034407075102d110f40202c0c50002210388210484031200843e1303039001503100f186841d072900c5600c64841c00000d40740144010100e94591110f602c60008a0314420040c4039644080c0612036000707241d407911900707514140e20004c0000c2e0004d4152000c98080b9441009480d0954004070116440800c45426604148070440b413901101e10500d41c10075400403131551503505420369070700724034101c1d0300450600c3c400c001c905070281c3c00802c00c0350540d940c0d004000000750091200304428a00303c622544482c90031907983d912148000c00407810140761100600c4000d00c9503141d441030740c220340610710501e070f414201c40c0000e10071030320090a0710b02c020841c6480741d02c19400c4000380160b808000032491140c0d0a0a0342d80340980d25200011510601051148903c282c0101080c144d9580745e1040a10440d00402d08403a001d0315850580404001000f5489070000942066480c09540f07000b55580f402110765283c02c00600300a00c40c00d40b906110b40c009248541c0b520 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 560916366 1250 560915116 560915143
    0x216020f061210080717031206011713030305060f0d1203090c0b0703110307030f08041104020703021b010c0b040609032001060510030504050a1401150e0a1805070e09 73
    0x40580c20b0804121030403a80034881d407142c2e481181700104011104031140012603503008002d5003400e21590554a501e031009007010b0410112026000c0c0c0703c4c440040c1d05019030b050030048404444603040050980741c004156070b0007034024406441064586c0d40d82800500d4010300d51200681d0300d040c0460203820303041f00c054024040713880041101202d5600405a00d442a1110420116003504450726405100009408110300c0803506044601640c41240d200d0302c503283d40e0b20b5119014001030100d0708442c00a0340164031400e103c1a41582d502d603008180c010908000c107421545940b03075207045a00500040082c0d464500314010940100940c4d4188078644050385103220341040a28000c01d51445a94403441c80a6440c8500500034800c1c20702494222002c1e10001719646c4be1140c16501c011500e501966842c440f1050078680000c02e200940101a0030881c04d040c03940001e030584041c1c40101c0f079039001090340040000d500250700c0742164400d250509c107942d40e904000d802c2002417894a0b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 560917616 1250 560916366 560916397
    0x150306041d240a060303140c01062304061413020c100228050403080301090506030a080310050111280c0b0f04180c0819022101180216020f06 62
    0xc2c0d0001c801881911209440394070506603070340e8000400c0292541c5220240100316100c0f02d402c040002c2d0402060381c10101c40000c40d0003941c811100c40c03201420302e9a2034858190b0b2042070741d103203010b01400c0010240b0442d85203c0783c0c40c1400154846404000081416a0006209807661000c1c020302da441072039960704640b118500d000b04141602054100c0070b44c01360700f44404400707030f026200352000d498010f08003504580c00c08454100400000c1d02d0f1641c90301c078a00014002443c510f000718491a0390a882800d014038020014003000030050034012260047e002940540382c1b400d0850523443d241074a05904551035007032000595409400002010b90f00295800000450000400403600b03013204a0109801d0f201600088840c1c031085040010507440110b82811a90030006a1035864041d0040c60320b000b140045820342c002c614070100300d5900400400c401e8031609804800c4150301034081d40740520a0fa10511008900e6400034410004c96841c400d45131550010340c0c41c40414030200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 560918866 1250 560917616 560917633
    0x10605061b0118060207050f01020a09030206090d0b0108030c0c120a030f050d0501061e1818020405030a0b0106030e0a0302190f0501050a0906150b0414040b060304060207060b150306041d 82
    0xc074081d500224003071f2128460b10324069912541482104c0d400c010030364528440d241181e080001c15030100f141e02d640036030f9074074140d008030b506e511a041c000d110080007103a580103800039007030130b0141400240f88100449a448010083d0110301103184a61601e070120303845200350310690b40303070160811010450745842d00100310660007424010341c5880540d4018214091003408485803402007060480310313844e038082000b42c040950f460300490558168003504080c1c917640800d00d08028040241c070303645400001000007540502c00c916180c403c0da0090600360074152170180d40c421039900c485403120070000c0c40c1010b000401292011f6181c2c407000038401e03418107817071000c041c06140505890861034a2641c2040d2016108850111000420650708042c9005850540c03040b00034030b129041911001044070300c0e03a070403001303611592203071000580b10704031810840b044a840405d800d0140c510303640b88800403600d84054070f6004d003007201c0120700071520b4165400c240100407050044c0e03100d0b9451 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 560920116 1250 560918866 560918873
    0x90203061807030b09060906060712030204120308010f0b2a0c0405040515010b0418051815070801051e060310170a150501140105070c030b010e06040c02010605061b0118 74
    0x700c404e040c20215035466076500e89808200300c50710203030707005580448100061400140c0200c032040c0c901d411030800506159071252102c00000c400282100041c00480051006050000d00c1d00c2c05048072040c4942420000454039441440040c0e4150503810200b842d128200d80030402c800350002c0281044c801c1d82070911b0500c5c2d541401341282243c1c107400e00c1c004181e903441081505d08448010324042c4804030200e00050080070064100100060031424106041c0010042c200007814034601c00b40d80b030310341250010703d00f14040c1c01c020320800d18585e1a0703944031604085400c0042c001ca40340b50b640e40b140848041c84031510351205d001c40e2100140c032962018046014501c20340220411180008102c0d400003c441d024010680005601442000d695200d8005031008521414080d20541e03281c0d00c5009070302000740d20450780e03600718108100d61420f09000b00a41080e9500003841001d003000c0c005019400381144400c00c0203450000d0000428003500328695050301d42184031028809403c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 560921366 1250 560920116 560920121
    0xb07170c1e0d11270f01020d0f0203090a0303090e010605090d060b0d1505070311121501051b10060504020901020d0e0a0506030f160801030804060c2406030204060501031509020306180703 82
    0x11462400031144c01c900c01002d04107080c9460036590142e014025078140c0780e10544100d409210604214802440840955203885019501550080d1151003416180054103120500160040030400000740b148522a131100301080b080e4641c0b2240c0422110404000304480c0078281d00b01070b0500c0381014001c03900e8083c03035001901035261560244140750424610303000c24464000040d09540d85100011413180e14000f103440c44450501d031041c03911100d015290341d0111070300340c030307400e02c0c1c0007241c0705403880d503007440b440d00140800c1d1400d500740070f1000000b030b4035403110710480c0c0d00703020105d18081c800e640c0c0d2181010103820028580e54481c2401c41d074031108000100c0341881c42c01c40b00541c040a4070b014281403030407258441c5150746801e08060302142c40c0c0001d101c0c100c80b0040c00e401440446400c1d001100d40c07440701480f00060941c91401000207a03245035120605040c5410308542801403072808200980d220250056601e4540b04080307005401c40710904040400c2c01001e100035070354580c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 560922616 1250 560921366 560921407
    0xe011e0c02091b0403060e0c09100e16020d0f030e070617011403030403060e010605120604060609050c07230607110d08012304090b07170c1e0d11 64
    0xd807002002507482a031081c0043c1000e14010080300c009000400000f0301940200da00e8660320021340c0c001811803004140ea41c02e09550100504000200034004024500c40d07030ad9016500040080034100c000c000691617002d0040103d0412001100001c40c46000c0d0704800c0f40c482d004002c4030400c1d0741d6003100804120a410783c401c002e003800000000e13000c00c00c8403d070000c190011f0286103401d14658400b40145040c0f5440946552580000038159480310040f41c0407030820400b800032482c0c5803512404881003a003152082600d0b010038030010940410641d802d00340d00110480c4284481c5421002d0440340b0400c40071244100d0301000241503100300d135036445104120441e50041201c0740c040d1003d0409000c1c0c1c58403400c40b902e82000c881450050141c082001030070010b01c0c5021500d5a002d2040b044400c5400301d070040c006038031314100d100760041e8030058004165040c84050492010011514108072003000b0020400306109941684007840c010240f04116a940090b0007416001102c1d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 560923866 1250 560922616 560922619
    0x7020c03060108030a050a0c17160204050702010905061902220f0f050f0409110307062a020f010807140301080c0109150c0206030a020405190305060c040b04060e011e0c02 75
    0x2a2000003e15081c0001540c00b41c4007140c4945040591030642112420034440050368103058005821855a80000c02000341103010f00010001c030100307005000c2942d002078481e0086a240c135000c2c90110f200800d006405c000e01e601150705841340c40b80721602a0007440551040c4e220201400c48100c02480f403810b0480d50118048010542c0c0c1700c0c400045910300e0b103e8039803c040304000d880c8003850142d001c5070340c0d980b14088480d4125040e00100b864604150404004550b6071f692040f1265a50710480444901c08003c3c2001040e155011529004910f480316061052a07004500e41c01d0292140c03000c40a0709802c03203902da41c1d50741d0301590703244112080341740450400321012400d480c50180d41c10042c907854840e02c4004c42c40384d0a000c1150300060032000703001c0e070900c404a40382d950759042c480380b00c50305450b8600d4182503003042400d08202601d0714030500300030002009140c0c0b540e41a41d0803036180341400301801031042c005a4095407201c0d1000d4918a11208048a82e03030814182802c1500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 560925116 1250 560923866 560923873
    0x618060c04031a07111b19050310020f191205070503071e050c0a06021b01091e0203121207030c111f06090e060412080606030112020d0b07020c03 64
    0x29540500c009074440c60001812105105101c03011252030b030400c054104140e0310340003c807103000708913032810710030303181c1c0781526001c0c080358021411b00d000c0155100320085c0c2c0300000081860180000da40f9040f200d40c600a50f5004241d6004045801d030941e15a0501e44513414802c51051b5801040b12945540c8050030b9860314010a149600c81c4041d01d10940f17244d00d44400011401c0c0b1140880e20160198908200c400c2207010480c101c1400441c280501c501000340e11440e500395082e401008810b500c015984c0340000c02c00110720200a4041040a56040c82070742c0081800802e040c140c0860000e5000c2100003008101c6030031241020f441449a0b50701001146d8004800312765881500c10b8001c0c559018a40b9000d843c41d800c0180040d000140c0b038005040796075806601c0c140d440000c1208800d401200402c4113101480d44078000542d950b1400301d2881c03412100050783d60006000d60404070b10044001c0c0115141d4941080a036a0008002c800c18600341000955805e142080c0b0f038001e02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 560926366 1250 560925116 560925121
    0x2160f031b0308040f0203100e0d030b12031c110406110d090b03160306081b130510150302072f0f03060a0e030412110a0e060a06080612061806 63
    0x718000140521949039a03a0760644d1140c0c0c4803520702c1d03c1e030a44d05a90500440d8003804441030f95125249540100e03501410030300c5900d482c09000c90364050443c5014401d5680200c040c08408001c41c2c220781c80c070141d07698010740350b034102c4801041034502d4010201000134010817202e4000868000c4c1c01c0c00f400c12285489140c2100b1201e81009110f00e003140b0038248017141d07184c0c01c1080c00802041c4503190010352a9a90944140b41c000014806115100c289540701900d017020030704800c1e40c0820060074805401e11801c41c90441001e0300c240394840781013003060745d03a181c40794046420903a00009030410b443e0240c0b060f5444050440d20300c104485000c4c0d0300b8042402c0c0220b4104101c0d10040190100b96540e0200c0400b4000c280d00440290100b0030001ca2110b08041019200c64000c501c3c0c48901c1c81c014003440b040c0300309030b00030680807809882005095a030305580d200913946a85007240e0940c4854000c142c2004808060301c440f0301980382000982c03a214140c148600303202c8011510643c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 560927616 1250 560926366 560926397
    0x2031e0c070b060f010302090439090603020703110d0e030d020c0904080a110d050c0105070309020607030c0309090204080f1c091211090103060b09010807120209060402160f03 77
    0x500c20060002e0109208000155980c5010100c45540f050706040151404841c4000502194aa145c10f40d076020010012450200c0780b90071141c84031514042c3c0019a001814070213441a0024402c140c10150000b51381010984686084c00a910089040322400c644981c0c00bd081c903a100402c82c3e000388178071400040300e54400034040c0403048000e0550721081c0c030f5503190f6080c01c3c1d02501491051113074082843e00408401c0081c81c03400c440c5030b40c0d2103440701c4644407070600b50b0304040c2c034803000c05040c581400c000d40d407144225142e256240c20142d6403840c03245000d850002c0182d002c60a4a440890002128480400c2142001f56120103484200b007000010b90340030f02c0c03409039040001d406010180301c001004600c0040c080e006919600e400444d0708000380501109800031103e00303450340c81d000c41d03a00701201090702501304074020b0300c40e0604003820b60541c080a003070040c3c8204a950042a21900c480e4100c0700c42055800c61008681000d0030000c3c2d000b0080d04003100003815403035845201c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 560928866 1250 560927616 560927641
    0x9120a0819022b0e0604030503041505040b0123190f09060317030403030b0603131103430e190203060604030f0311011d0706080c0a14070602031e 64
    0xe110852480800b004111643d40808001403082d00000a0f41c6004c0a1071415040000d02c1c802e030700c40e5860360790b203140914041c46040014110a105d20f400d1209000008031541c480700d0540d000f1110b207090800328002c010410b034502010b1550440d031842c41802c4042c036010000029181d005130700303280a03035030b40c10040111200d034030014000f52002c0000b4080050800003c41d0045d000703150200340764080034005411035109480124a80d40080e541808005040074042d0060f24110301406140c01d041c101c80f10130140c14140b035042c0f01c04d18481503901c0040c400010003c07150075602000140d4980340d240b180f4103410b071602c00802d80c021940b1030841c0210300032203109450180840b42011301c1c542e5071a100e0109110100c1c24011001c05c010701c8081b0034420b01c080400d140c40c10140c0ea180c458840f81c241080d980089041148038410084c0c6c6601e00011203944800c00d1400504800da034142400281c0518140140914000070901040e44410940c40c409000c030710440c4822500c0750030314982c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 560930116 1250 560928866 560928877
    0x3060515090115090e011811191e031b110a0b0c03040b061c0303090c03060e0a021302070503071e0c1502060109180201080a020408120c010f02030402031509120a081902 74
    0x20301c044c0311610f5447d2415400c90703404011040380c0e0310305007090354004002c18030845024038005030756010055000ca10400030220f400c0854141001441140403080341500d42d000400d0051288414aa00900e6010403154a20036044038502d501401c04da003110318698000e98050700c0c03111036180807407201e262a459809462a10310010b100c404a55507085e40503098100060b109000101800004140a0b00521300062010340141c402902148108010304035110708400c00c07280706000d03040000e2800401c88400e02c1d0400c410141002c4039410000c1c0e43c8490b20801060307081416000141680980e500204544540d000c1d1100b503a00c504101c41143c2075070356070010681940ca0a034001d0350250ba00c05030004210000545000e4407480c4080ca01402d000040c0b825a00c00034810341042400c8c0304040d494207100400354554149500003940d105c0512480824010b00e0501281720004104081901480c0c01c2c0400c80d21044c1c2c07075001514080c0121807480d286402d00c0440001c0e584280308582 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 560931366 1250 560930116 560930129
    0x51501030b090a0c05090904060903020f011109040b030709020c0307030f0816050a030b060a090302040b0d080f0d2c0607031e0b030f0a05010518030702010903060515090115090e01 79
    0x100d0703643e00c0055100180410f200e03202c091250810015409445049440d445980180008118440645002032419030bc80910742d002c1c0e403400c44034001364404601150f041000844001c10072104220000303082c40241d41c403100d00d10b0300c0010700e8190604044007030500c09000342c60b054007001480c0d07010f60b01c0c41c404803514040004802c20001116004801800400c140c80ca4000b030000c01c6240030581940c403043c04000811030300c650800071490326026a0302c0c00e42007a5805c00455000c2d9444040ca405600010702c000007003c90344980600180d402412001074405140d420040101c42002010f0002c21a0758858002d520008140d41c0c0030f809001011800060000361081801000b0002003240c1c82140394180914201c1000c111020010401c3c014058400051603042015400c2c52190b28010800c0c0759410074024400540c2c0c2101e0302d4012660801e10100c1c40761f903520b100c042e80b0000980c110b0350010380e400c00231030102c00d407070810321404844d51a40d10708140c13540d1108540300402d1203002d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 560932616 1250 560931366 560931379
    0x1051e0121020103020a03091208090f0a11091b071a0903071a07051309050a0c140301050402031009020c0706020c010221090303120a1b03060302012010020d051501030b 74
    0x41c401944070380d00070036500c0072918002943c0300e404d075202c141000c05e201e40030001510400600150400c1030003402c0c3d0001900d801006580c0c0540d540301844121126418480c02c2440000340c00048c204144180f806801100384c0d079a0303002840c00e0100c032031070044081c50800c0508002061010000103d600c02e0f0341098044005581c00e1841c800c00c140002c007036070300304a0244415000c0b2a240d400043c0a806e0f00c580c04100ca2402d0342d0003100f200e10180420007000f00056503182019802c2040707a05450080c2c2d005690380c6e480d0040e20311010f280d07510528156100048800d80d148010500800362102542076a20b203903980001203a982c0c1c1a1410240703100c0010070210b000b001604010070b070210011702030720308010901c0b1b054004440110344c91120580c40f8840c00c44407045d00114461480441d0600300000d07425500000c040c10300e0034165210448004914a400303e004200d81d0501c901264802d6558192411400b00507120907180d100032680000a102c0166020303000e0310b8a12503003d05407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 560933866 1250 560932616 560932679
    0x4050906091b071514070f050306012a111e0f0f0333190f1b0309060614031507270501120608072601051e01 48
    0x8015032034002400c001c0040282c0100b80004182a401802c0024081d10f469030004242003210015120000701085c2c8035444a410060107075000301c06884000300a2901c2900e2707695180040c2e030004102c01e651446d07403110150a00d2803050030001e2204042c402c2c00c142c0e2040c24101c0c10300070703d0b82901d000030b120050100003080f65800d02c440d40140e200e000512228801d40080080b900b8002c20000c00c0034591000c0991902503405082640310081000c0d80b21003003481c088580104180310045800c80c1c0035110341d5144010404e54000d40c21000400d00007801d41c21108030003800400080004030341d41814490001114110303010442c500b072034064042d195003d1183d10010000034010980c2081c81000109210000010189041c44002c1c0462492890342010000761201e0452480c5040403801c0c1281840452008111501224020751300c4a90404130040c10050041400b01075402c1c0c3d602e00001c01c00d404071036003a0240750041d441c003681e03003a90701c400341c0910075100d4001824030f00c1404c414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 560935116 1250 560933866 560933869
    0x30203030a050a0c0218010e07020c0105091002030904050702010b0307050402040b070b04170301121502090a030803100e09100b030d020607050f0904090f120f140d0e07030311011104050906 83
    0x606550a140c07600c01e0000550394000340c40200c46503a141d139802146e200610000c07105040b00c9820402d5030000309070320040c4070002010361240b00e08181c065481c1c41c42000202d40204180d89040000034014400b03442d091500038000d100081d98940304c3c2c4142000007420b03040c01d2085078156183c0300345c018540400c07502c0301106c940c400341003141c2c411780302c1082c4088c041003240958041c00306d815a030b442000041c1031140003405443c0d00040380701e00c10895010103999411084d07007203d80c4840007549943d40c4000c07554290495510040c00304282a08110107003c01050f502c0172110840c04c2000941060300c1895034442c0c2807116000903902c02404281294082d0000c1c1803010303d150203e5280001120100e02515401141120404000c40d503440400c0342034031a02d50500403500d040515811042c1000301080180484506504000a01d440719000c203600804100a130b84411190442d0740c070714008140c0e61020700742002e0380d440e0207140c4960000c1f8104072011103400600c1c410040e00c1c0c540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 560936366 1250 560935116 560935127
    0x90e0f0c04050a0902040302030c04060503030912010f09032303040b0c280818010209030a3005130f050906011101090c0b22050102060c0a020a0506010b0301061206030203030a 77
    0x610200c0000c4007444001041d40c0c618840c44007400c0c0c540c00141e00c851440c41030619002417402d54a01c100d04004080c46507450020983d07040150448018104070f40c4201001e0040c03220b0404058401c0c140f520351006e0640008d8440c0c21101c50082c50100b0000380148401c4502098400501101c0c0c4880880c000440c840040d000101c03820034082c0345118459010758946824080c1e01c03010a103601e04001c04e140420a00105c0121150003d500d4025243e001a03103403108080010f04980c0351a91048030711054514141e0300894000442030f011a2642c0058165000b0b4420881c043d108404040783e1004601c01c640c045070130151204600d5103840f001580c4640d20302075082020341d65882e8520104040c0020f1400800900340340035500c10300010304802e202407411a4041c9402c08150400450f41d0010b0aa80e000c66a60780160305c800e400d81c0300300d0134002002c04c064458840d0030004a9001400401541250a107844a100c1c5800201000060303c4140c4001395240c3c00030302c103100003a400303031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 560937616 1250 560936366 560936371
    0xa0c14010516321b031e103318110702030d050c06130b0103170705010c0504050a0b0c0a03180f06020102250c03021302040e0a060e1b0403110d050a030804030906090e0f 74
    0x110580701d0124900610000b20365000e0a101c0610304d48c4414011495500985040000c4010300781c51087c03803e0a410740c0312010103550441d240b03503488800640c20f108900580301c0d650303401019580010003109006103142c0010f40300c18028000c00b000711f000344c04030540c12117000e0b03070100903000a43c0c61074407421122003072118035840d020410004100040e60a204a21850089846e00ca03221402c1c2014070040e0310b860380000e40020020000103000c0b0100140381c55140d40c1c140741c086074009680495401c034180d6a44609000307000203901091494045d00070f80400c007000c0401c502c10b10103031304200c400c880d203410b4003401e0787c51403910038805801c5c0151151011552000301510b400e44e2000d4003282200201c030030200b0a42d5407102840900c441080064121100042c07070b81707440701e45210115181c481e034030000340f116482c0c00d150105520381282c03d42c04550402d0942d05a0107150401a008000480b001c60000c1c600c10008240340e801064804181c5503c0000c42086682d0121034182002d4003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 560938866 1250 560937616 560937673
    0x3030e12060f0a0b04140118020403080f0f0408060702012405010e100203210a0c030e06010b0a0216090f1104120807060b0d050a0c14010516321b03 65
    0x300d80344c103c96510307280070340b0703e42d009801502085580344c40383d240c0b00f615000b000180514010401000030a510b03500b035031400210112302603a5000b02c461205082d21440d440f9190301e0103400b040007220740c0c065110071a80800d8601c0c800f050380b0008042c01c1070864502405002c0b4800d25140100342c1032a1020080c480d6850046a280c80500500a089034000b1a407164100110404120710b540080c01020070100172412f080c015500407040300d984036841400742d0f40001c2c1c400b2415180711807080144410310501c4180150200c0d0322940d65102410515a091100506040411202010190460b4112040e258255115100655841280780e20180007902c003c1d0319502c1440042c1c1c2c4e24000c01c92168825001810010f19601d00980c04216a074485a940b0b0480d040d00d02c641d90b005070850b5038683c4140426080444140303404c00c0280c0a50021121410b132803c40080b42d07142014030858142c0e40721080785c000401e0700c2c00c07191640e101802d03407503010b070803e292843d60317079280041c062142c420 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 560940116 1250 560938866 560938871
    0xb0409021c0617160303170c0409050703020403022e14070b01080c010f02060907030222050c090a0806041a040c1203020105040c1d0f130606080703030e12060f0a 71
    0x105002080180c0e50541c1205182141c20300c803140c05000308011809404a1108000c02442c5ca0350701c3c06440740c100c02c8100024081000d00207621000d0100494020b8a5184401c01c03541c03c18002c000c00130741240c00120f0250900420071211140001315074030703104140c0c2c0b1194a01e110741d40c0007102c03104c218509075194000c050003e0400241d080e000b5178041c1c01d080000f400b40c507584d100010f000240051240c01075410132014411a59404500c6405598068a0b010480e50f000c88480c1ea241e8036190800003c01e2801092149440c0350710000c01141d28100c8016440c00d44662455458550581d4000c2c1a4988921700c180e00401034209543c0c000d000e848000c2c106542e9484560b01e080c401c550440040c1d6445003088100221070a2610140c41402c548108009034001c40c3d00c1c1d290006011842c41154034000110300c110480310160b815688010140281565600120380d01d9410b0f001c100c010400e8a082c01409040c00309403001e0300644a002010f0a0b2241c50101d0620503014210f15800e54 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 560941366 1250 560940116 560940157
    0xb01030c05030a0c1a0d0f0f0516021b0a120b040c06050901082202030303130c0902091c0c05030f030c060f040804030605150409050a150c02030912070f0815100b040902 74
    0x4403034400c010b5812003082d400318a03100072320703044c4040316001007440500c408140700d50865035034005010484006e9071045105400e000400160200000d50310160451040031a40030422280e520b00c0c5018a100d50610401d880c1c607488152203902034180b540f40005c040350001045074442c4445900d480c961030701c84604e0300c2840d0300401e0540e80210380d616030300f6088810413410402c80440001c002c007844002141000d8402c400075182940c0340580c101504d40700d84080c0203000081d95400c00a080040890b041e03290f0300c83c4400c0d01e940015001c00c0f007030f004250010744407000f190000c0748165030019104e46014215500d0340b000300030181400c0c13221812002c460200b501c443c0b144881310390048004020f13480c4d061401c100e021001000d1165460309084400340541d400006403203480604603401540664550105450302c0d0840d0f00c0a030b41c03612120b100040030000860641500003418154003200d035502081c41442009500c16003d200b58100070400c00300c0440e50140007814904200c50802d05c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 560942616 1250 560941366 560941387
    0x509031c020d14070c1e060320180301050108011a1516110a0f140d0b150f1c051b0a0303030c0e03010908090102010b0f090c1e03040b01030c05030a0c1a 67
    0x310146d04503924803141c50b13081c04d40030b4041542103001003100703146c284100b254044001070044a81c2e81c80f040e00c0344000c115030f00184a01c41d442e01080740050000c0025694500c419170103410348110011075400001000007550410b00b0320742c1c07495410a2481403410750040c800240b40390ac0f01c901542c4440c40d030031225409a803607141c2d42d03000303220791038980c8030040c01c00845014500810a5040c8540b4007111010006007511a540398000310341050540041d030b183e40441d580c48039032082d1070390048840c510146611544100b1040050181d011100d4107414102d0040f144802d4420380c0f030b442154558100000b130312a130082141000d551500c2712545815402090955a40d6030040340e10440200e8640c2c035030759091140c0361082e10101d550000c15485040802c10301c0d4000307040b40075000d00014000d1f0301400a40110b00c1014001540302760b50345810708000603030315002c2c0811925000301080015180c680011040b00c5103801841ca003003018507001144504000407088030f59011018041300800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 560943866 1250 560942616 560942633
    0x90f04050a0c0b0901081608190204090504060608070509040f061d030a030f111602090403140f0301182901141803010507032016020a060509031c020d1407 68
    0x1083d094941503210b41d50b482c005000041d000781418942000407044c0c034805a07005076459000b0010100810002001036664000303403089812070700b01c182c00c0000f4003081181315130003c4221a842003e031080b007500c96082280c40c907001c0c0c5001d007614020309008004901c1950004210070300500c0107040f070000f40070a50741582c10400100c800300f03079241d440101c0c100c043c1c05414251400c0100080c640306120300c0c80035150300001000381c0100a03900004041501914000c1442000c0304142501c3e6038000211002a5109010755154a01d14107012444da600070b0044485a21034000d4082d402c0c0c81d00340d6202180380a2543c241c1c10000000410044d840044006000f04020b000c0140c0c21065454145400d40d6030160101007014500441d5503004843d00e42c5007100c0f01156040c23280e0300d0503072004150281c1d000b4900694003260418002614035080402007807082419020b03148885016441150304071901114040580c114101c0340c0c109502c951a25110582e0390941d150400c102600c48401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 560945116 1250 560943866 560943869
    0x16180f02041814010503010b010f0302071707080c0f0a02060414010e12031812060f0a090206160209130c0b0705030f0408060105150f0a050c0c0919140105090f04050a0c 74
    0xb40c0664409010f100541c805407100d024150640003400759604030701c0006c0c20b008103c417940080641c00318041c0304002ca441d071031038441c811204803d07071a4101070404a21607441b50b843c1503240c1c400c450101581e0301000c03c5220310716400408440c103003072400101f0024000d071004854100070310428070190344c1d0348404034141c0003001d0740000d586545040060003440c14202101c03510a40c100541c0b0070900400244065101040046140094030380000c204082c2000380c0d0b00961003840403412520340d8040c01c071a41c054074001c4030034007000d458001e45030200c6010300c04081e100f20a403040071703c84c2114000050409501c520202d0f0f280400d05000c061481e04190001072158010000412003407900c107030b11314400443d07503d04501e08815440400b1075031240f00080c0c0103010001c00c0041180000f48039a140011015000002c1464001c5c0040d00c16190703098441140e0f403404000c1410001100840350507548044c20001e581d03241d81001c0312101c0401002102c89200340100540000c00c54500e007030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 560946366 1250 560945116 560945159
    0x30f0903030b040b030a080901030c0c05030f07061b020c01030c050405090907052803020f1807020d09060e300307050a0b0609041a060301020c010e030c16180f0204 72
    0x400a010384100410f450b52118042c0c1701c1c0c2e01034903044c004101c01104403000034009080001e041d0048070700c16200c2628141029260380404503c02c0010500c010003025241e104000070490108120800c02d2800020b003901c0005071701944000c04c082d4080d9110443c0c50940c1e04042e070601e551140020b09100080f0340b14240c60300080f500b04154140360748200c00f1044480710001400e400148096070240551101031f208840c00012401c0c5912400000c0f0b0409440d62800a81c914040c00040d41d82d0580c0401480040d08518001484522510a07081c00140050180100c58029040e29280360500420100c061071704402c9040200000c1008015182c4510060003c1c00618103061581c1e0320000d05290040302c4110070000042c00f40d246082c1c0040842c2d44019079600ea10022a009000d28010366006607c0c001151203410300000c0030306051144001100d419040410f01c0b05007814581c411842c5004840c0031001c2032590a801140040f82c00580050610f5a5100507070f031900106400c20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 560947616 1250 560946366 560946371
    0x50607110c04060902040e070c0b1b0d02031f150c0b09160305241303030e1c031e060303050306010c17030c030a1d0303061315170f0606030a1101030f090303 69
    0x201f0900054220080d84101a41804001d0032402d0301c0b07251000700000c2c10100300c043d024156400c4048014242c070200c040e503e008640300e00e004011a9004035480c03c00c0254941e61400006800e0314050300d10424641da5a10244400d2a82d43c40c011064005003000c0898006c041e903170440241c1e4640d00600640c01800107000005002c107095080340b40c9010040c0c07041c0741e584c01300030f80c140b051621545200d9040c40d0004003400e8940c042070402d210b030740c0c6c16040100b061440000d216416042196011000c441c080c40702601c5140603000c43c2c440f03100040c042401840024401d601900c5540e001030300034002d00406580030202c60300c1c16401140d080151000101c140904114644500c800ba01220030703518410032148802e4a80d01d01004040b10310500ca0380c1709100b500d0b01103400540c902100001c40300d041d0341e01e4010555000c4030b1b00e80304000302e10a1300c0c2d203441807500004155004400250180600840030b0b11000d0a03a04103090a43c1071645a03504070130705180c24892002ca041c080c0d50300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 560948866 1250 560947616 560947619
    0xf0a170c07080f071e0b041a0912070603060803070b01050d0c1203081801090201021b010e12030c1c0807050f071e1e110904020a120b0f1003050607110c0406090204 72
    0x903140d000d1380316a0344401403085001c060103050008000c80f81519043c03440d1200c08415408d5030305042c030403202e4054000d401c800da000591900014040181c42e030700e4806101070758560b401719075240946400a09103003204001003106061540085554034041c0d00004442ca03191020309040014a034000c60019410724200038080314100c48045000410000038480c7c05541c0c1c0000303560b1411400d0034001c43c01580c02c0340920340e00804042c1c0418001409902c0100302c900031941d241d4110010f081011302070f2603800318a03500312154066202d5041c2d110481e003a01c07082c204441940203c458440e80e00d004225001c0810000500b17416603190403810000c0304015450322440141c01c00c004100c1815071606240009130320b000002c0e6607500142c40000f01c6903154000646030010613400048031140541d804020300100800880c40344051508020300c40d04c46036414203e50410340300c044d006070003000100703600600c03a0b03254032219200281191101354800300041d0486078194000300c0360503400a0b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 560950116 1250 560948866 560948879
    0x6070203180d0807110a05030d0c06110f120403030f180507241124071106010e13140d0512180601210807060207050f0a170c07080f07 59
    0x11642900c0c81c1940c442c142c5041598a04103a0300036004020607040c0c01400b01c4a83c3c1d11404010001020001d080750a11011110003400b0a608604c06443c3c2c01e0070003d149031002148030844180c07882510303c062034015056165a4070f400040c0048003016240c80340040c000c2050700400300700848002030f0000c024900d180030b03454110103a0003051101701212071000b2040c0d0308003000c001050b503070034076004c3c2585a1500b00d00b4042c800607900500c9a80244012401c4686c0c08814412006500d8811941421900a9584100c03d11440d0124609000040c074a244026169503201e44203070700110404076480c51190500d0300e1602048009000825888000c17060007541c1da81000520400d0070300d00c1d8400010581341e000c1401070040c1f556082c481d0854140c0039040c03a00707031140c0000c0d042d5110184c0b8504200694403c4105030744520854280168001000c01c4030035000f540255481035222651002c004542c200004a104e18022131100190030603052100303160070380740c0070301426940d0300b41034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 560951366 1250 560950116 560950147
    0x3050913021c2f040509070e191203050f07021f02010b0406031a071e08070905010201051e09010204090617010518031c0204050409030306150e0913110306070203 71
    0x142c550640b2820b207032400808410201c007030310203107441c005840703140790050000b14003522030f6610440c1c100500d401080001640a21003262030783c0700301c40b1640260b4199016070b122130414014101181c42d1960040f00183c01a00207084464086440070700b4041c49400003150b8281d0780d04444416500b00c004140740350f6081c0300d001050b000c200c804110780c90850b180e001c141d9190100c0400c22030301d011b000c0381c856400342d04a00000720224661301240c01058a006081c0c1c038040d0b070032002003100e489010400c1c0d80107000f0f5074883d84280340700c1e50304200b1200600c0100b81c0090510075543d5801c01c004100c0301c80070700611000d072070204400d1440036049002d071421100c00402147d82c013441d01101042030600801103e4505039010b130084092105010729400900c42c036071205502514005c5d1010030150107800c840c0441e5103000b01040340e07440c00d0744295958074000030720319409400c07a000a0000703103070446100301d074038054150000c4a682030f10205c0d24041007600c1c2c20340940d0011820070030110011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 560952616 1250 560951366 560951407
    0x601050105070b040215070804080a0b0c041d06150c01050103020a05030a0302100506012604063b16060503090c0f0f01030207050a02060418050f13020d0305091302 72
    0x2860003625005072510ba1840700e0f140980024030074401d403040090240802019a10001d40212030f0b60f07036039a91010340305e950b42000b1008a60445075480054644100c0005036003c950518003913900ea601c02444c0e0b0405500010010340d84000f0103012804074440140c050405041801c00010b555411401081685031455012034401e0f40310700ca400e07000030341c007140300441602c86d10004201c43c0c0300c400058a4054201600b4217480c140d0544a0309103000104006005a0040c0e108005a00449030400085c00360740e025403d03002a1001c680c1c0c460041c00b902d150080e0004025a02d401800715654042141d60782c0c0214002440881032200d038260911038605401c42c1295034030000d084000100350310201030507045040c145d0126011080c000280120a200365005050b5030b0f585844298140341e50b1800ca420040c8140b0304400500341c40610240b01d03001c1c0301180c40c0ba00102e11664204880700d00d03600c01c22420030406214070085074071190080325010803624009030b05e86425840340203803c0b004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 560953866 1250 560952616 560952619
    0x715120f02090f010f0c06050703020d0f0b010e06280c1a0712022a1c0306030b04060c05040b030c09010806031f0c091805040b09030304030207180f0207030f02060105 73
    0x1000300340c01540c0c480361035074040f000030300f045845004910410349219248880c007520003411b0004100038694160700400c05150208010018040544082c10480c0c10600b10180410380c4c02591242d42d24104015144a02c144016141a0000f04003000781046040881030040340040304030004101c02001e41002d0014900e90344806032810300780c000e141e85008401840d0050380003829a031440c0c80c1a1212811540d000c24072072000141c912107950303842110700c00f60410b99a1a2034402c040780320380518801c45c1d42090030a0b4898585441e210000d0014549a00c1844001c00000501400ca000990f10415690400d680c40d54515030000d407800c1c00007040140302b600102e1803140c01c503101407110201d10703010110008820201600540d034110f0300c4e822882d01020041150b00b209180e5420444c0300d50321400d0828965100c00040c40c0c3d8030300040d18000d01503040f0090910418080d174805107127043c88418007094040b502040c8208a902080d4150009141400c10b154540c1c0c04004060040c01c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 560955116 1250 560953866 560953871
    0x10e06030610060c020103021b0d080610080609100e0c03010e0a112b090b010f09090510020c1501030308090607110c06070c050603010e0a2315030715120f 68
    0x180b030080451480d429006203824000c1048800301564820790641c0c000010380002c02d1803010b411080c2d5540c4000381d8100320b000a00c0b500010301c0c181040c503240b104081068440304031645401042241c2240c0040c034507138824407a520b00003411600b50f20080d00a624080c68141c1c3c079414070b2032003031002c0c10051180c9405814180c2e0058100f0f0170104403210000c0b080104100c001c1c0c1d05483c0c0c9640001c002480704814180740f0110300b8020156041030413503504141482c5003942e074109000c00d40e990554040c0c865000a0058245606035400501c0070213440c0c419940340d0280c61072200442c41003a002a00080d10304410080940001c0040e640c0040c000d051802c42040c24486556607100680c1c64140034500100312002041000c000d07942c040e0000918554696841d8240798202c0c09007112a00450340c10611100341064451040100103592600742c400d007070340c40903007145080c0240d000d19900340c0300b030f1140000d0500c1580c0b540d00c0411035a0b51600700c440e40e22604d4005680388504619031191 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 560956366 1250 560955116 560955121
    0x131b030b01030308040c0b030a06091a030d080c0c0714010e1519140a020a0302060a1401170c0409080405041103131101050d020d150b09090a2012010e060306 69
    0x80088000e181100d501d850306500075038552405400f00d070460350003038040c01d0002c01840710340d40b1075030440300c140d0344e0028003000109032149043c2001440c2041c0702d41c03d5003003540c1240310b0038031400e1040e0f4410301d0401524580000300c41c46c07034074101725503002c031000851200d1108110340e07101154035030900301151a1507041000c050700100074455aa001000103112003070404106004103165440182991728454980c104c01d0000303525a4440f01c0120b0050182c2e400280000d051031041c0342d046101a05d0824051b801c0a2204004075014039502000c0d00c20102c1c0c40d01e8a984a00690203011f01c5480706a49481c500300900041c0c44200380103540e808814400c000c940c0b20a15800040580c100f40c1d5501e0b80c04411300141c0e0300e8442d244a100c9402d0000440c07a1103a040740c1c0212190080c0d03482401445551903030050100d000d2100056401340c1d4850109102c104250083c48c42085001c0c081035a4013840d0180c9000360340454800110210074000401080e00380c41c00c0207078401e000340c0143c005403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 560957616 1250 560956366 560956373
    0x50f16090b1801050f030109050a0809030111120408070606230a080706170717010303081504091515120b0103050f030901083111040e0f0a080d090803131b03 69
    0x940b05010352030090f840e210100c40c17169400d411104100f03821200796202c0748481c0c145036240e5404200c0044c002c2d803d085201041d903a140080b2800f403001d01e0f020090940341c6946441c82c503406041c06407040c03615400041001c40b003c149203518801c4071004514000002c00034058002c02d9640614406c1c0c128650802855401690240ca007240b0058407818942e2162016282e58900d0702d0000080c61032040080200358000030241e00981d00c00c0c0e40c2201c408620302c1000180ea8050000030100345248001100e810a01e41004100043c04109280995103c81110125525043c0103541140d10b4400400134040d0600020001c001080042c500d003c03c5540068030080002e131912660044000c5090b2129143b44d05401506200704c95401503000c06080580300001d0f41e050f55803095180251090201d000003c0d80248254a40e015142d41d25072911000a40d030000b440402c47c003078072007484100150901c0000c40c410383e0103444000e94140c0310f05042c0c0e0245c42c002003094880d039043c1c4050010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 560958866 1250 560957616 560957659
    0x5090301060e195903120f040c0302090a110d0b120106030c17070839090c090307090e011b141218010e1b041b030504050f16090b 57
    0x1400741035506158203039a6a000d4280100200b00300c2d400d4031122040141c0502c40100042c00d42081b2542800c41d25198118240c40d200c400791030042002c8500e400420050404031b00450f0f02000281f070000e11441d0b090351a00381540032110f400e94042d07940c0601195898041020406008020002c001ca1803c1da5642c01c8082c02c0c5010f4595800d614800704150603070100039100182580320300b0b0b2250a078032800e1511f01000350b1442404103008064514446061b68a5580c0b4420001000820300d61204984081c0b950301090081c0c0d01401281c0d030100da044900e002e082e1034064142d0000812240404007250203840301c951a9080154081d04003001d81d0444060700d1030301c03486035030005d41615080c000b2800c00f20309008814407542000b2411300700140204140031040045240c4441000584082000b11400c2c0e501440480c070860f0503e414080c070952000790b2181c0720340300f12901d229680103c00c1c60100c00700705011820700e0203031050001031001c2c000c000340e028003590440040071005409100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 560960116 1250 560958866 560958941
    0x30209090a0b031006061e170411010201060e040f0506060a080304030b0a090b10030501050108030a082d010306060f050d11011d0604061d0f0d0305090301060e19 71
    0xd01d1521501d070b881280e074007404458100744000340c0401816540d01c1c0090300444118183c0000407000100c0c0700702080c041c440c0700c0c05642d009148940196510b60b1006050172000c1d40c068115980d840d004140b00c5404000039016600a601440703444403a854000d14216000b441300f8001c0650b004d080203280b400005503000d4a81c4046040343c1d07039543c20101c4005110050b0040c11402d080005d11020641e00b0f2010320591740288000d1109a880e11261a500d100e0740f807180b00003e000b400062540100303c4184c003020004400030441150545600c11085e80081e0070981b0b10b07a503203d00c00c104a40100b61804001c080c01d580303003400d50000da02c4400800207503c46060510003142c006505600303402001d03041800d0010241600c4644601009041d824064031002c1d040c41002459211031a0540b91140e0154000b00150080c0b0300701d6a007103546800501400c0d03095925003101060904444a07070901c1890740003141c450f442421a0300d0402e0351741d50b280ca000c0248403800b44a2000400418080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 560961366 1250 560960116 560960131
    0x1d0109020307031e201309180f0c06021903140a0e12010c030506040e071a0f04060804031b0b0106050a051b03040303110606030a230a080a090603020909 67
    0x585a55901030b090700908400c40d490310720300022102102c14140d082d0300400c070030143e031510511103180c1024a08850320820060b0305c1114501d00b0104040684d640110340d143d00c8011007115803400a030b850360400400f0703040c00c03124180c0c8810705024840d4100580c1c0c991801103400c0881001d603e1307d01528050720340034442c038080c00c00180e00840794083c0204040c1d1010180c2400100d290242c0498002c02c82184100f0005c3d0038500401c0b0545450701419800d0a10780d800303440464608a4142280e0040c504e500003051b000340000c46510100c1c1014200512090b1240340003440c140c82c00a00c1c120b1700c9000001e485c07000b00890400b1803010004036064444078100559140d440c14000d6640d1302a5041a450302078500801c00c45c240000700142045034401c2c1c940600241c0c0c980c4900e0340b01c100071108540c00d68061540c4030f010076481001c010a405484940045805650b441030741490a1420242c80c061000100f0b042820f500c5011140100704a260450900c3e60481c00101c81480103400803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 560962616 1250 560961366 560961371
    0x1061b02030c2214010312111203090a0303140f0f060105130b0c0d020f0a0605070e030a050706110d020c0f151201061d03060622090f020306011d0109 66
    0x18000c64400b0402c040d05140000c0a08000030428140200600501840340d140e007802c002e1250807411180071410b06030b9902001c1c00c140c06143c044120380c001c042003004541881101c0c1d070600303104c0d01c0310010350040d1880b10151140d40c080f801d01170700361111210100e440b00111410401c001c2882820750360000c642003000d01080c1c50b5400100c070203000e00202044210714400000400724080001031101080035000d0302c113101301880050761036076940040116290041125480018090b900030b9500007401d0412450110111005c20b03d8000090301c1165194007103041400200c2e04103507111381c10103000004151050324103400945540c140e58946008508180150140e0350381d0568944090b14145d032910b481c0c01e0b980f4003500444100b031040328045001c400c05c0034061001e101c8041c03203002000e401480030b500c465050050b0a0044d070395180c410800c50a44542a802034010b4040950040c1032894496085004060801c603060b84605d0040310b0102c0e60710305000c1c0243d00c1504564224000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 560963866 1250 560962616 560962667
    0xf0d0f0302030903030c01150503210c070314030a0e150a0c171923030c0a0201290103050f0f0106180509180f120f18040204060905090a02030106 64
    0x1c0e40355000d07116000b0360502021840c036055410540c03104c0e114211205541c0c0301240c3d11005d158076101c08241c44200075505840c80c20115070781c8402050815800c1d000c60724600d07030300d484c2c101c0661101c4030840116000007680103283c540c0f00441002482089a407580c0c819015107000805100f0b0134005400d00c030041c141c420138003079810400c49155000301d81165684401c9003080b004290b00b41c0c9010b01141600303040c0c82c4030640d4910008101401d950b07031186580c50305c600003050b54202d10b0f504021507480703c103584108624050310300e007000e44045000c4981c2d00004005000d55030010074003100300c641c1800300700b120814400c03410b044800509100d616605050a4004007c0c11074022503000808071081c044640b00021168030521180d400b070340d030549415001581c60300b885211082c85d01c00309004c0184400111001412000b99421500d20b00c51014408a400c0e40c002c0d84c000c102107072101c2410051414406202948081c1000c011880d6604110300079041c0780d0800403030006185007018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 560965116 1250 560963866 560963873
    0x20a1107050f120321070906020105090607080603031e04091a0303041a16052103060d15091707030f05120c0f0702030a0f02040609090c090f33050f0d0f 67
    0x440e080341d4551744044260080c0c500c00207501500a60396000010004c40000a07810310621503c0d00498100000d04196210003000300e950070405046594140801c0000024001c003158403940224444094191140d02c0c040d03a1a045a20b903031280c2c8144112800c0d04020703035901200320b41c152448540c00070424040100c41000e9405950412030504421004040522500140000a191007110084200309003120520b14900064540c01d402840741e1926000003a205040040b500580100024082526488010903000c1c024000b150300320740040c4803000d06500500600c840d0289013000342c5806804000c40c0f9004100030124045003a011900c1d8440d9503044d02280c0495400034212049000a410228110354100380106c1c4658604140024010300c2e0780070384007000341c20000031305a0619204040028144131420000f2a80d9941110188015a240e4507510030400d43c030703110034626a101011400107840d401c000d00c5034141080c640070b40d41c0c030301131200607050348607004c41b4001c000b034a07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 560966366 1250 560965116 560965123
    0x120d0608070303030b0f0a2103030b1c05061003120e1302040803182205060d020301150e07050f030a0b120118021f2a0c0603020a1107050f12 62
    0x308040d0107800350340000010326034503801c904c103404011985151104501300c10404003c6062007484e601030020341c0d0941401404241c001c0c0b0b42c6000e0b00b40424588143c40000d108031401d0000414400302c0861b1032018804104250383d8410f030310300c24840880f4207640341c140c8103601c0502c00b2800c0041c6580c99414a40ba1350b9078000d0b116148a0003591119114039205480703411580b4910880011209080f8040c6002c031604044c0c00d82c1700704100309070401c50125001500c80107010340d8003c0d6000c05007000685091042d00403151401c151440300c036041809075070007a10050500c4042103024401c20b52815850412070740c100140900006100c0800008505582407900c92100349520705000300160078048000302051078822a4000a000a0310b189003a9030307036800001000280300c501e0b0b8121400c16914641817221901c4004205003d08c035a10a411a040c54000d500020340101c0c80080d2a0b030481c0303035151000b25070405450480e043c04042407513440c603808980c0c411038a96143d4036100c0c4061 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 560967616 1250 560966366 560966369
    0x1020723070801050c04080f1506010e1206131b15050724020d0605120303040f0f050d0c0c0501080f04061a0d060902090618151203120f1305120d06 65
    0x314002c1c004d40c41c1c0765006014580244c492000503000d00d80d6a0b14080f10041b41c986910040a004001d46480f10b0004541d800400c10034150490619203410b0100d400c1080760034865103600380d5443d01103a461a003901c07824041c035099101504040402d02c6103c0e19007030008114901460000c1d2100e12500303141100314080c1001d4010248140b40c141850181c0e90006c05122500180c180a0550f0328010f1115560382da410301c4405d41c005201050005015030054400c0d00d0003044000103258042d100c1c1410200c1480404020581090009080220312144840201000d003402c60143c50456a000c3c1100c0d00100000c1c42e480e51144100d1640c0c0380010b00c4100400d0140009180105610b491002031203015400e902c544007400005e5454941002c070000c561800000e000360540311385841c03070440a44040c030395901504a81c03000c0c0540e4400c0014201c64051100100c919081401d00c1650201000d41803101d90030151784001c001c00c41c00910200d007640c031241d003039a40d550b116409070000c0500d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 560968866 1250 560967616 560967629
    0xf03030305040f140d020c0307060203031f0f080105190908070303240b070b0a05090307170412260901050f070606150215010503190b070903021504170102072307 71
    0x2507020346006014000740100210342c3d582c003140c0303204480c01f04241e0344981610802c00143c0c8104006101c8181c0c010b030380804032a840c101c191040380c46030110315198041d50405034141e07644004102c69040340d820f107944c490311070b04000c0080c1c0c00e440c0c55428151159110180a0588900014203209115001d00600e50b80d82015003003c0b548607818031040f5480100c0a0350503040e45000b0514440c2c1c1441040c4c0600d2800000750314101d010ba60740d00142e00995484ea0030302a040c080001d0300100f0002c2c1c501d00620400c1c0003142d4041940808851204200d0240e005010a0165a9090340c11008444455118204407900c802a0345054000391205030020082c01e9804140c00c020705400040819802800782440d4419030b0f00d0310b01f4075a40e00000030740350065410320b01151010485004103036402c25010700e0b0070406140c4236004070b06d4640381c507103005019000c0080c00f00806a00031407840c51101d141e4001b54546005604d4500b0803207000761407481a83c004400c1c0c5a0748040402c20030005001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 560970116 1250 560968866 560968883
    0xe06030712110903070e041407061e0905010504090e1e03130e25030f050106020313050603010e04080306060d0f060504060605070b0106030e03220602010b0603010f03030305040f 78
    0x818050040c41101c94400c407071440c07802c2c03107107100c841015042950702401001d8003c00f00300f41380528500c21803c01074025a81c007060307003207060034581c0140600c3c0c018040549860841e00610041404090240144c0104220540e0014440c0340e03804801c8508850480030041751442240201c2414850011802006009840c0c840c100911010003c0c0098070100d0b000c80e403010341e885000c1d54541404032500c0c10030a0808010070b144241d902020a82445903290004d51540c440810208540082e0040380240e80080760aa0079800d0f404c8206c3d0107450107440301030855140588d05046450050f100820004000c40010001d498a0043c0c1f11002d48081c02480b50603629010352000703144d03d0161a0040341404c00c0403807014058821228160b91008003010541c0c40c01c14204c004002c40ba8020920b030008109024015050906e16a00380030114211440300345000f50207402c4665419016004640c103000403c03410303561250800862741c0504000c03d4981e1189001c5070040b0b2000d500a0000c0d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 560971223 1107 560970116 560970121
    0x70302031003140c03060a141314070e04060501091e0c02120a0305160201051e06040b1e0a06110c1207090509100b011707050a0e0603 59
    0x1d00c0c07540c031a060054407980c031041e506215030803400d450740c020013004042d032405001494010250000400c81c0300c03054890801140c0c0000c00d4001700b40c04c0d030302c1407000f8800001440d500035181c4c10b0a8031000d5490b05009507020909076000d5071410314250002c80c1448140c07280070b0841103a084514426410440c40034090a00107490000f1401040c2c41c3c40700b945541700c050040d410344c9440c0894207107465246100e49501103002801168105824480030010031840d941072245103882090311952440041805401c011400c03d400002003030b2150503541d084440c0080d018802c0707500e000d0580d070305c500c00ca446034080f05144000d80c000101c000100d18040b0794a200c040400c90a0740c40a070b9550f2040401c5440c21161400c40c0d40001030b03401d140301c10300e00c9460421102428017040d624985508280740e0b44000f4031000500c4000210401d803240258800d04100c407000308040e42c1c070f2 = true := by decide +kernel

theorem cover : BRFrame.Cov 560791366 560971223 := by
  have h0 := BRFrame.cov_init 560791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 560791366 ≤ n) (h2 : n < 560971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
