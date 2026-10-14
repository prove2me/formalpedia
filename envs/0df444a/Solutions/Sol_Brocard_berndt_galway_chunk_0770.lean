-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0770
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:41:11.866992+00:00
-- url     : https://prove2.me/submissions/7ffd1e28-15c4-4b09-86ae-abf6618a2ea5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 138309352 ≤ n < 138489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 138310602 1250 138309352 138309361
    0x2001090f05070501322b05010515090a180b03030408070609060c03020c0d020301020f0a0309020420071509140c03070801020301080703033f0506030c0618031203100e 73
    0x203c90202184d1000a0181420300141d514815a03542105071910035a03100ea08400c9031001c2c0340f13041e81e17031400e00004000031f0329410a0305000e042c2041c00002c0301c1090080107004056280c23038080800310742404038140c4003641c0070b40130f107030141c0501c800099162201003070200700101d000c00d500007100d03820f84403851072036039801041e1003105c004070019000d60044590100a400e164413074030200b0348008d000514111540004130004c0d0414040840001d81d00c044090440c01d00384100d450a4181c800c0b0042200b8100d0036111a0b4460048000c140010400d503503103803802641c0004000503440b030002800c00440c5e91441e43d80e03940720910144203100d01007000a0304181071013242c0c1611501d1016081c01800c40e20b060322400610340a002c41d41d00c0701c006010f202c580031407113001080b10b00b10183c414914001e142a0948101502d102e100382c100042000c066600d038022129000005001c22515581050001c3d04040c0e801203c8240240c00004000440c0782c4240e1100c2541c2e24000c01150540741d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 138311852 1250 138310602 138310637
    0x705010305064c020601080705030a02130603021507150903020c060901050d060605071b0b0d05061305070816090b0d02250c090609020a2001090f05070501 68
    0xa081d144550003402c031015140c4040c1e055940c0040e01480030075040e100030100c2c1c00d50f0b64041860b00a049070001ca149000315819070622126005102050041846909100c0000d4407294502c0009120b145440d18000b421075445e000b9400840c0c009010750500e003418400c0c08066400b03d40204c404a92030002c40b0001542842140403a87d0103500070089a502c0c00d0501055600c20543d0b2410b000f0280041c60400740d0078042c0303e029040c103a54460b110f02e007170300e4001048039000c1018109415044d000340024004c400c295507000107500000719580c3c548102045d040600c52100c0d454071803c04082140b442d802c101e200b8082c550300d150f0031200c0c090312036003141d081440340208c1c0000700040001c800c04031801e40142004980da080c0c2c1e500074059000d02100002000c140440c0d12910440b02089070004621440e402004085c0003907181c8000a0001044034500600c0301c0355442c085009049400700960001041030f6000d40315449030001c0d800d08540d2103030340d84542070016510310b084400109 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 138313102 1250 138311852 138311861
    0x105030f0103110f1201060302090112030e10050f0a080103140a02030309060a091d06040f0204050f040915090311060106020304030206030411010e0604030b090c060309070506071a160207050103 85
    0x2054521180c0540c0d080d03946515082010509459000040310a04c1d051a0b0b10554541a02c0c1c203820b000007512451803050140d4104140d008400034001d0306507020201c3d410090341c81c3d40c10401ca5250204a051680584450007049502d00300d412006c0303968841785400c1000941a2401b5101a004030450101090340d0340e4905030000390183c0042c4140311043c00c0403405001518504e0070281c08258850404550641120482410410ac030400344100c80c10288980d90f00c2c19a5150294600360505c2c011030361180380c224503680156502c500c2d00c018044000c1400c042400a0300342170059400ca0308004284000d0111260058065a40000f8415000004580840742e0180c84107040d170b80c95071210316040c071546c440d842c1400080780e1507104039940d00700240b028511030f802c05407141c18104441881c01c80e40d02011401020100140100c1032800100d1004540301140d4550b5244d41d13500c2c0518402e0f00c1c10400c038107000004c00a002d000d40302143c120b0310740a501e600b100c01c260340e2a0011000d44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 138314352 1250 138313102 138313111
    0x1030f1803031d030a02060403030b0315060621070908010b040207030207030f1a0403111c0905060a0e030304120302150f0402060304060b0d061512152d02030411010503 74
    0x38512440c200006402900241200000b080841410980c0c8100c2e0302d0469001c0407480c030047e00400e04110806425204032054164280c006007144012000028011350707019004c0da1158a020802d40b452047d245404040c40700d604040c055581003400c0080c03c140c80354003c2841c59428004428210304040c400c0c0c07006150154010091a0700e591035651811030001d01c1506d03003051155400c8a02c050461410780100e00c40c2d620100240707168000e06052400a01c68520040031842000888a1380700030000140c4004542d195600d09a01405460302c0d0028140d803505030101040020315815030b10203101000317000740c00f44e40b18003889607142c9403c1d00c0101d8003000c0a000b5040401d0150401c50701031540988101c5000401481c07440002c1c03003107100c104048071001e0311070b8800300740201007a00c034070000c200c0a40207250b81085070f40c4564203060100c4001c0d4030955545a4507481114004580b409072040c10059143c040009842d40f01940c011503058444410300f41d000e1020354481c0b001c40307114 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 138315602 1250 138314352 138314381
    0x6011101090510021e0c07050f0f0f0613090608490302090d0c031e030203030c0904090b0108070609050d050d080c0d021809070503091507020a0f060b01030f 69
    0x2883c1c42e40ca4020000c0d04221500110940350007412015421050000c01114501d02c00806290b440e00b420800340b140340d400c0041c0510b6103621204a2170b2169140340200e000701f100c2c02c5882d0b482000c400d034246450743c0d1200645a0070034000260349407003c144000b898507058482a034003034030704c848032915440001030b01841d0707136181c401200c0f98024040c48034840307116440d0152508400000150400c000148203503401940c800e400c000304203d092907400c0d290359803130b0715100c4107040340c030040d4030390200070442d069803000014502e0580c0c1e44c0d80d00000680d03900800682d07041d611041d880d41c0e28413030341c00b4034408500d002402040786c0c0340c80e0702c90340310069001004000d044d07414801112080030242c0303044100070b401d000c0440610b0190010740000c00f0791703c0d0201c6074190320700c0030040c08400181442c5c01307000b41001030052640c9c0104401034621500912a002615640002c901c1d0230001140603101c81d1561507000100b1416401c442d44907a406d076030074132210601420712400ca60505011000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 138316852 1250 138315602 138315613
    0x91203020c1203060a030605070e04150501020c060706090206040303020d03061410050c12031513180b09030f0d02030402040b18071d0d030906090e040203030306090414070e060111010905 82
    0x359074400c0c02113900c500c02a100d80000d9a44c1d41c5c0e084142c5405580640128103040e44001d6241094070542c44c0d28031030300d606079000700d280c00000303911011000741c110300804c8002842c0040c4a00c0d90002064150b0140040f6070311079803810001e4271160585041400a4201040011103a048030680018114020b20f1446d030010800000d941943c07207600c403210240203036968440341045c5075025500c500010341049400c03620303d00402c00142e0300d58488201c2286003911890002d82e5110000c9203091b48818010810f8a901004528501500c6007509640d02c0004000d000540e5503009036000f644291000d01c0110241001c0202440007040b0b0305060044510000720294822410000702820b0001e4012440d203204000c6241811810002d40c0850340300c43d01003050039404456503000385072000c080c1429003071940c0065207e2102408140c402c1c0e4140c4041014000203000511b100c0040e10126070b1151f6070750019100c00081164503501003a1040e8850b604040103008800840764440060070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 138318102 1250 138316852 138316873
    0x60a0b12120307050306031501080d02012301150513090605090106030209010c0201081f12050f070308070f08040905090d020606100206040b07020a0c03060f1109130902040b060706091203020c 84
    0x503130580000b403609906100761640750b94510701c21040c243c040c011002c080e2249020004001e82511f1903001e0040020b440c1400f00542600b80301f9106040d208801c60012111841000032507072402070703d0030f00d080000f42d40000605101560300820403202c00365811503017a030369450140c1c200e009502201c0d0201e40b0041c5c0a50040d880f82c3d203800c1e031041c0210740034545040e48071602400300c0c0d215008520b502000504500910a00b0040c24407052030040003000000e0842d0781d005024040c0d007200038103034101109a00300b00600081603c2c09000c4565041001d4134140408a980b084d00d021000094020300b0040350580c02c145070b240b2080d49a9800500068507250303240040080003d0840d4214090011401d0024010012550055001e4940440d40e03104020b2000e04450b4003001100c1c640d0010003034035509440d080b80301c01d801080030100040c4c0d440700c3d0020a006e020107419250b8001700000d190000c11615501003c1694040c00b03502d25012142001541240724404000c50380c0d501561060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 138319352 1250 138318102 138318107
    0x118150806031c050c060a09020d26160317151509041d0613030c030e040b030f0106140d0b0105240d062903011404020408060a0b12120307 61
    0x16002032019044078070480c00242940301000c000142000004c1e00001e420b40584420450141c0048003c0d20401503d4400c1d0300244000c60380c00d0000b88129040d18280c40c80380000f601d41260201c119a440366030b8200064070011158043c3c03412008940000c2034804082140b031642403181c40b540804013501b2081604100124030342c6141e011400e03c08004450f400e846500030b0360403031005060300352283d45040032886d04141b40140442c9840742c0345203200340465404480b10301d03145d405040c12011000d065020074050500200050303003500c51051546100e1381c3c1540800d041701d948000c40c40300f0303009280800c03403660100c08000e001e00a45c01e005009504d40060b0091403149a83e0012030000441542d640b055000501c0480085503204c108005002c0ca0480b008007550701006203c900140030500d0300c007140418000c0440c0d00003c3c0c610050180c50300d904407130181003400e003141c0240c03070405040d1015142140c5000d004c1d024a0a070040c500c580000d00c400502110b030700303030750131503a482908 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 138320602 1250 138319352 138319367
    0x11160e0a0b060c030d020309060a0507020a120c020306010e0115050313080f04030c150e040902090103030f050f071b05030d0e010e18070909051006080c03040317090c011815 76
    0x307a5600042c100103080200f1030400c01014040509900940c81e45440320400d41408002451142c049092004000c5515070104040d03080d03903404003080700b1400742040d04a030781c0192050002c0d0144a01c20012031141000000075040f208154480500400354640071102404180d4400800305c00d07400700400040c044001824003520f01551356802c0943c1ca4986054102c00d950091500c40e61140303251000c10381c84030300c03003529100640b0f0511084407258042801c204c0140305c0601007143d0b1090703405019125404451018035056130031619101031b401c0c6004812148040c04440030058080061179040200e50300002c1000364403544a01c020400041d40c50403014021254002c3c81464400c00c1143c0d000700070380c0120300030fa8400750024207004140381112009012004a0002482c00700300c610b5000c420660b2003608207601c6034a940f40d500d0180c1e6105284045003011948000c10004e581c000040e41c0704080b00240e80c2d182503020301c50704044c070012060080c145008240b2503a41c0b030480c000ca91 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 138321852 1250 138320602 138320621
    0x105030106242106030b060406180b010912060b0f010e0315060619020d14090a0902070213050f041b14060705150a0b0a0e060109030b19050711160e0a 66
    0x10088143e8401018202d1207241c4a071440c2d450a075900e00034418840e0401056178081170660741003222a00704800f44220070f000070214410746485165000440e4480c00754440109440c907207060a5201c80d242610280c060021030900071840040244032541c805c100c2c0041107400600074041c0500346503400d00c3c0c51540107043e5a08140100001d0780105c00b20802440b8189555019150725080c01400030800e190f41441110440380520600c8001c0d038079035058070201e84440c41d00581c0d41c071052001c54100d10096201c546410310b030404010f0300b16403100440303205078843c41400120840460101c1180071301750180700320008094030010041e0501e90001c0c2a110b0160044803861501e001041b14010411500140556120154a20383c0c0c24a2101c40010f00004016a69a49003110000b03001c440c1a01c400b0300303140d54a4001c9118a4100c1e03400224141140b00180003a04d8600005002900341da05000018407482810340b0790440c00c0f0485100365200150802c1caa07881d02040140035001195 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 138323102 1250 138321852 138321857
    0x90a020721020c030a0c061101060308250204180203100c020307020d0219060504061404051f090803040602060105090703052710062301020a150f060302060a1106010503010624 77
    0x26032a00c0356400b0040710a01c60f206c0c603080d0890b40d05064004001030380754110142243c0c10200c080c000240c50409503a800400c100f0004e5400240c2e40491180f50711280f400b039042480d004200041036440c0400c078598038000e504441500d03000b0544441100d180c51050001a04240856001460540c0c1c0c18403000740001d002c41c0c00e040b42d410088056085176070141d400300d0340008003017101075042032001040d0345000c1b568500f054a0070000c510000000000d180150160702c200320791403405412400017404004080b02c2c0c44035220300f00a17541d0300d000e0080d544680300b90ba000502191203030241a105800d41c6180303042d1500032841c81ca0380400c102c400c081041c01440700d1030030030310300902c40d0f2801400f00258040070100244652480c02d6008060241190060146100803960000340340002e000c9042c0c00251249000403024014403050300000c0d401f40b00002d19041f00c3e03900031042004081440140e0700700344d0b626070404d4203d0380c803441202d504c01c213481032110490030140c80c0350840e100f0a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 138324352 1250 138323102 138323113
    0x70c0f021003020702090a0902041503030804080912030c011a0405090307060b01050c0a1a07080717060402040f080a03030e03090a031502070f050601030b1609140429090a02072102 79
    0x550010b40008000c540900f03086030b0b601a04000d40c0b8003804bd01a1306101400107081e0241542c800424540c0d0081c409420300800103860582500c442c000c5c03100054031041620b458550601c0c4490281c03503c060341013603e0303019180040c11454a4450540600e00e418015458456560782d2940035040480f161418028103014105205906201c00a00c2a119000d40504605940c03140140030300058000d108119040f02040790060300074101000085450b84008055517034100094040e20840d0000c1320650030641c00091600000181d04070018401d44041c04035910701442c89540340140b0700156030001146008201080b01043c5245610488810161501445441d01521003c1c88030084072545d001000410074841102e840c5500134210b80161401c6030240c1c0002490020b45005482503181c0940c001d64842d40ca6900140383c003000c210700c1c031750080c8036200042600d540c0c8001e158001d40201e00002d0441903c0d108507460035a2100c04602c2e0714442e82e0104a0313060300c8443d10fa0540c4200c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 138325602 1250 138324352 138324367
    0xf0807140705010f111203160201050c0705060403110703080712020c01020c090a020906040e131a010609060e120f0f0d08100b1608071b06020609070314010b040207050102040509070c0f02100302 85
    0x1b99802140720b41c403a0440d401081030103410017805c5603001801500e19982c240030050004801241c1c5031f03080b54140c13402103401191907603160300b019195030006210190004084040144c240304841440d54681c00b6200b0940c200b02c01661074802c3d40b0001740c0e01840d034a00007000024654007230142c060029080301d040c01e403286000302a0740000e54940011113a0302c500c6030208031b44004004507420f0070140f50fa0b419450700402504080060160600b8020101c8042c035940d211203020311950340440045540605201600035280d43c0080440da04034000d020842c0403080c0603942d0107009400e50300416040500d0041c400ca4680c000c0c828258105104503079560101c0c4443c4080e00e003142c01103e00a900116240a09841c2c092940c040e00039500101c04202e06484040750101c03c0703d0f0000c0100d1485c01c1700856450041210200c860707449807000c178440c0d0034018150302a009561042e2121201074031495015124001503e0004028405142c01b1f5401401c1001e0110315040c5a410050f040000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 138326852 1250 138325602 138325633
    0x3010603080403111801050d15050411010816021c020f0601030302010213050a05030c0409140d050301030c060e03030d0905011407080406050f0c12090a0f0807140705010f11 76
    0x82a88203690440300402c0c24000d02540d00400300c40c0840844611445e03d4041da400e110f00710052048500c64a11480220180b100b00200c000c50407018840402c55441c013031a141c00c128418652990000e0842c00000f80f624084000620344844250010010761900002c940b40d0032a0404014003140036426040d281100304008480c0a144260005030f00c46a8210001c40c104125234845072286180600420044c0c4000c030b181400e203c402c0d03038040b455005038201640042039140d410f100c54803880500c44060765201001e981030702d10a5000c580c00aa4400003213403241c000d841e07000c1e03040d0401c2103c0a003c002c190300c0029450322440c0007045c0e410a0f44000f11744020f08940500c0451094020441003048900c64140d1041c10101107000a0801b45410320b514001c00c2c64255892200c0c4004c20300d8000108580200705520103424075980005103024156034001c0c4008880e48a0521000e048080707002c5160070039580181e484400b191030701602200c482c01c003400c40440501400303460076404503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 138328102 1250 138326852 138326861
    0xb15030a080a022506030b1504060c1103010203041a1306021902010c0207060e01050c0a060f020a080a0608120723030901091e030b0603030f12060a0806040203060109050907050301 79
    0x2805a481c9944440034050003905100c80c1824069040c038140d0115046444002d40303a50960b0203502e8002400886400401c03140501d40301660410710000c50001085644039108100c810710074079000c1c900845903030a0500b40e00040c0c5009040701c402070710852112494909066002c41d59004281143c10141c031b820b0200c0e4040c0100201c071640000309124240c4d024000c0d40c0303203020741344000c0c03019900d005002001807050214042c10040b0005403e83c1d804010040e58500c02e82040302040804082c0d0a480c0007944801607240205840e000010712140091084134100c43c003010181000c0090304a40441682c81088103d03440d111000c4402a00707006800e984204030941030085584a08401c00900746441c2a40107041c21200c08560b003c1890818150000f1680e010400801749d407070780c0001a003140113941c0024064500400d0001c41400b96003099801000140d521090060302c8204054403240b040782c02941582c0508010011002e0f113034400ca0b8410b00100c1030302e005a458000003400c2d203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 138329352 1250 138328102 138328123
    0x150207150f0515180613020903010f0f1112070806040f0509070504050a0e0a02100203120408040302100503091c031d060a0612020d080c01060321080106020d0504030b1503 75
    0x50341c0c81c0c1c100141c10b40c80840f4902002c10880e040100c20030803407034291002c000104075038003642c3c1c1145e1403103c0c0f840350b40543e422500010000c0c080c3c0601410702038014074415004c05400c07070600400484119802c42190880a01e00c1c68038141030307541842c256041c4001034030941e0440c0e91440c0d11000398105c0c1c0300b55402049800c0c041d003081c510344000c110640c0e1014088641c0b243c0b801944c01ca407881d00180f00344404d9810303134400311f1a07169000d0030380c15401800043d1880e00002c008100401110a000f4401e4a20803207ca0102d58002c1000325041c1c0401c4a1a2020398401100b165607a502005a1035502c04146004a103001c0e042006000e6030320402c59451480e0b00890500c1440ba000b401003c026045038807594501090580005001e0b40c452540034000c43d0001481d0a007140d02034018030302031a0030074117000d0541e10001d10b0103495011101d407080010b040800120300c541c03000c1950b41509a81381e0302c280c00c160942e255150003810140602c4510008a031b8203100e251010321120214 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 138330602 1250 138329352 138329381
    0x30f120c030902120c030a0f2306100b0301030c0501080411040c030b090109180209250f020c09010b041806030609050102040503070f030302030f0307030b030106080c0f04050415020715 81
    0x28800184103000c1c0071a0341c100c4001845d08641d03010159503c1c00035040c02a688c00090012040407542044403000780c0c0c514404159442c5400b1072a031102d4009015070040000a501031a41750f0b0743c40b49029a13000a000c020010411040c04000c50740c0300f42035035070f0854080d40e888e51502c8454070005040fa0502403907000440c0d200c0080390a00e02d44850b43c1801007030006010700281031102002d444622007220007d21034116035010680c100b0015103542885411f0300040750340c9000030200601640c0783d1402107401882110b29140c5141802e010483c1240e0b4000d0100c1c0c1030904000c081050700d403100583e81e04003039440c6e00c0080441c40b10301418a0440c02100016600c45c2003006250800b0080c3c1c100446032a8018420400617500104440050080010b01504d94903283c504501400290156075499801c0c50700c00b08510501240c0300000050450b660702201400c6420301056038403c49001c1c0c5240404c0004072031886054009040381031243d940000702e0701c291483d150498481001103801c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 138331852 1250 138330602 138330611
    0x905011115040c1424030c0c0109030503010509010b1207030e012007021c0b0601050702120f100e01150b0c03041707080c01030908070609080d091a011a030103030f120c03 75
    0x130b000003058055076800800e40d003444a03030304281404c440c0d804001207041c4965a0010016803400c11000030ba40b08502c5a030000e002e1b4030313000d0500411541081c0a01407144240b600001124a4181c0072141c4007129180343c084a40e072482d405500420320030065501554803103609402d25601003c00303501c00c05140c0c60032034840c2441d0050242c0440d440f0f4900450307500707501030280411140e03c0c209a0020003482d04a0340ca00207840400c5800202000407403035445104118101102c000c52640e002e0340d030020041240700c0120b0003203401d07100881c20100440c42c424000f4071890350484024005440084222032a00f40e480c0c00503100c0c5c201e140e005030510b030407450742400007080900080e0407030803003440e051010b440d1a40f508400f500c01c07140002c0409036071f450042c040104940c1038a61702080f00c0f10800ca40109400d000c1400c194ac0c0010446d001c07a1100007180c9030035a2101d070707211000c0040b1700030300356800d42c2d9041e07800d50560301313008041c4a8640103001c50200d850207400c05040f02540c0114 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 138333102 1250 138331852 138331859
    0x9080706020a060e0609060a0b0d02120604030e0f060a0c2d0606050102010507210608030c03091507050d05031504021918080303070e15040e0906090d0905011115040c 73
    0x802c0351180084e07204903800c058280511420001103541d040403541c200091554403d1000680302500303090700035046210078078000000c0a020485d10310990003030310b550103400407001c00c100114854000303003507124000340302c403240e80343c45030364031200705480741d00e01c0c0000e070f43c688040c2c1c414049040c6054486444c4010510704118a030f01030140144001c0c0000d012600f02628040d00388241c0300c940c0d0f038003d290030543c002004155000701000b000824181d07590b442c1002030042c2c0f80d5105203003940c00750380000c042e80702c8000c0d40e004488400ba041030107411a54690741c4119172a500240075211904024100b9050960381c0384020010020307486041400100e4500004d0140b210b0349038081d00c410380c0d42004010082d40401100d074028054503180352215000c00000d02c8101c240c0603031080301c00010071b0114100e5540d0305146d01595500e81201d0741c656600382d015594050a100311000036041c030301c00300300e59409100003003800e0003141d041d540e007103100f04622540c5500448060700d000700e80c44001c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 138334352 1250 138333102 138333113
    0x380d0803090d030b03071505071a011d0411040902010c1a04110603091c0201020706061d0906091c0c080a1e05070512090105071a0a180b070f09080706020a 68
    0x42400b401c00d040901007405208000f80e112040d510441003d407000740c01503804144103030211411140e100c0120010f05800140d10140700c0024081c0803c2c5001700e807000b1007407a44180c0c1484c0309650002040550035120b505000181c03980341c20072030510031604148800a10700c555503000c282c81000001701c4034030703045c01d01d8403400c400320310018041c440070400d00407241c0010031444199002c041000401081c40c10b002c138028812210302611491400d0800700708100c40562002c0e03181c00c6030681d0030094407003030041c03626000b0589004045500c0001c20062003180400080f0b0802d4003800c029541c05401d807100a910703031040c0c01c000005080310745021a02c40461016200680389890100e0811140d80c0e142a551130480203500e45090340400c0d1900d590b03206400701c8048940c00401113040402c0c45025603481403040d5041603840781021080807101c0021a01900070640000d50110580ca0f90f00d400d441c8111860011001c002044002050002c1c080200400400a545c001d020300380031070410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 138335602 1250 138334352 138334363
    0x20915160213051e060d03030504031b0809041109060d0507030b040905010203040627060b04090c03050f070914070e0d060606020c013c0507050a08030106030e01380d080309 76
    0x400da4080d90342c0e002d101740c0f9118922645070440c2d00d805c0c0000e02d80c681d8242034440b07108102081d07000614440e440c10411011101910700010141c0c1c081c400311858403070329000c5006142c0303440e411180500101040c00f400d40c0219802c09118200090007400d03d03c04181900c002c80700580d1969000000d0004000c110f2160484000c0c0d008000203d50b501280c001031200141e04c1c3c0541180e890f032808000d25030b0b03542d10804503158890244c059036503581c5403444d02c0328550f8a4141c104c1c01421000192444107000c0c400c0b010b0f4000c0c0550300306903039440040c2e5800c1c01c8070710391a810800d0b50a5240010741c0c0c070320803d405000c10750000c1490380341c0800011301c10380f240400056000300ba490201d4050751140c2070742100802800414003c1400755404494501a00102034078501c131340f00c4180e0600150b040110306a48060760284080e202e038510071400d0b5480d00ca6003c40b608540d503c14000f2009082e00300400c000d4500002c10128a0503000915140d01d409007541c00c04400400d00801c01c5d0200603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 138336852 1250 138335602 138335641
    0x111030f3d1404090320011407020607110703020f06070618050115050103020c07092f1308030a02280203030c010209180114010e0a15020c010201060902091516021305 73
    0x1d0130721006034556001041018903140c1c100c0b810b42c80c0c42001a80420a4008140d003002d034400d10805890680c100940e500380036103030308001c0f903005241c0d4004642c012814000b940e40180410b02c0210b00b03042484000d510498095903140c0d81c43c135070443c0c4c0150251050381114012400440d61540400462128500b10b4bc03005050610420403011800400300e2400110307030501400069440125441ca001c900c0d2481d4111000e0302c1a480c0000351080b400301908000101103c00d1100a0300d85580035524410341c20642c002d0380c80415800502403080b0108018440c4054034141c501229a006c00d2071504084050340e2180d40101341210305003084400b5014009040310f401c6243c0d4035040e80c9050824505001504100c1410b000501a48509200700c005110460840d96240c00010780252a140c040034200c4c019401c2c8400060584494020703540e10800042c04099480d043c0c19002d04554055600d8a03105804290710402507520b00b004030b20000c5460f503002c83c452404a6065520100412 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 138338102 1250 138336852 138336859
    0x115060f030618020915031e060a0e150105160507030b060f0607060b0402070c1d160906110109020301020c07060311120403050a1701170111030f3d14 66
    0x40104190078001498403c500c00f50300c00141c0da8440000803d10040301200000c010701d00000a11003880600c034511117011000c103003a21480e031188400c0000980e52071085414050340c04022440c0382a030880310031491003050420038548504030380602c1103a80740500c00e83c2e1a401c03040f4100309100354100c20a034003540403900c02810032942800903080d40a1664082e0806a5988a02d042a12164100c1d04000c0d00034052040340b03552036810f152800c007070395140c64512079400003085500c1a2455280305040268a031080160704015080342c42c072142c02521313082592903804403800740c2c030b00388000c1c801c49a10307902400c0b086041000140a5904080b40500440c400b0001d26080c140c0381240c5541043c0d04d407078015596400181c0440c0c0b06002550204058049240000b07115521280d095a80c1c5041c030000f0300c4103000c64155200c5c9800304481007810581c413400051141982c454606410794021341201060340d04410440d6032000c001791a0080c1c40d250326000b80045415460048600c40c4202c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 138339352 1250 138338102 138338111
    0x903010b12012c1507030b18160206060f040b06040b0310050901080304081207060f1a030d1107170f01020c1011031501050d0608030f070204060e010803030c0315030115060f03 77
    0xc8400310f0351350801c07540040018001c0004191443e10070380003105071541c01040c500b0404107407144880f1003002500c140182500340ba24889030300b400821414820078009107062034000c2c18000b0310015142c410030305035100404010104080182501841c010b4040c01d62040301242400c082c0848030340e040e0000c140541c8140020801c1020003c1e03018294403c0700581034039040d01e0f1070800c1c0174040a051550400b4140390780041b0074031000c44100d0030110128116440445880c5c002d481d81404c1e82040c0c41281c2101c442407080280901300306403070080441c211440c800012100d80e003207030405407014081c1d4000d840e40380800a6240102c07800100710000b800c4c03031400d0a05050701c60742380c0b5010407414004081403681850100c2ea00940041c040d42c001c0d070703a984141443c0b2194541c00610103d00c500d03c1d2103000b2411810701880c650503141008025031440d1140d07848698260001400709040d05030380d01050b890340d1230a0107450100d144a001460038542444005402081308030b540c8020140b40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 138340602 1250 138339352 138339431
    0xb07090614030a0f091203050a0609060e0a02070f0c14090705030115080403050d150504060e0c040b07020a170a061a010912020d0501052d040f03050903010b1201 71
    0x1031070100d070341246001000140000c000201000076010b00007010340b810312041040c0b2203198240c0c110f24803507420103004200b10b540318211181103840030f006054401681400007042009954010054030340200b9140b86103000030340d9103000c0540c00c0d420545e10401c1300b0b9200019409c082541540010450505505540c18a80002210250440003008011840012405260050040301c40a0321131800c140422180c0a611403641e00c0b0a00c51140114604000024170000469a00740503070040c40c3e115182500c0c00403202d00e81d420003003080e80d010146510020781c00124040c20400c0c100e2440203801460781034144001201e03146103007000320b01c0703203403218501907a40001980c09a44086240c040f4200341400480c45031403a200c130061030766281c601801031300102d620074006280f01c1c0f00e41e0218080458081044900c2040d94001c260203600c103004070000307002c3d030003a2405c448054000200705a42c9000070f0702005050381c5042150359103000884440b180d01c8200c40c191041c040e401e503584080b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 138341852 1250 138340602 138340637
    0x1031103070c030c050111040e0903070201050f031012030806010e0a0303080c210702010203091603020a030213090204060303030506040c110c09190c02072c1f0b03040b070906 77
    0xc000c190408120504440740c0406024488103070101c0d0f00903008100414003c510080310340c0c03242c06603040703044c030300e80004441030000807c84100c0c0340d06a4500d800e001c0c2d600d6558101d07410240004d14405e0502d803010443c0340605524a58450183e80c400d021401d008001501800341d03081c0c0d450140c449190b0a0000c6600542c20b5a08103443c08401030341c8100d0a40821150904080200b442e1703c091402d210040368150090341c003c0104c2410f50710ad4620f030300390301d5a00302100c1c80020341140520b6002c0025142c00720841b002000548008511a44594001002c0300c030507410490200f50b5940030320107130342080e1185900040d46414a0280c0810a06001e80c4e07800c2100c0e041c40c0b09210000018151400e40c8021b4021400140b40902100c1d00700034010b910790aa901564151081583e030121034410100746070000f0490b0000c50a041d0b45918010940d4034518502c054010300f0b08100000c8d4481d01c120003184100d0140c2012030f0302341800031008069100f65445030080081b8400a0b609041c5c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 138343102 1250 138341852 138341857
    0x180105090a0605090609040207120206100f060806040b060703092102010207090b040e06011409070503280b030d0903060b090603060703020702041d010e0c15070311010204091d0705010311 82
    0xd20600385241c072040c8110010302d240c840c03031b42150340043c004240c3c0010071605924148200203550207031140740d034400e0780c1013021383d01038130a8a84103480404102302881c010700c1c2d82c40e00450081c1c03000c1540c0d1940004980154007000d0704500081c60382108000c20742e070100040c0504001d419540c0d141a00c02d40000f552002240941c054003a92031104045590f920340c01080c202083c0801c2c0c0d10690395a0b500040178400444c4001c0c0259441c60008000d507205400310780c1b00e03114222030300b1050401c002c00d000715480354140d40840555259001c2d41180d40c1040403e45e00c64550780e4014116045241c48000d039004a030a031402000007100b8012256004140d096010b4164030b00140c46801034000100a40694110f02080d1654038400510200e8190841000b01e65171404460f4100050800d00030013a071140045c48540400703006182c00030340b040d541914800181800036082a403074858600484491010986480c00302c01041c003a501c0050100000800702401c0c2046009450750b40055640b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 138344352 1250 138343102 138343109
    0xa27060215150315090111070c031b080106080102040812030c0318010209060304120e010c03050d0c030f05010f05150f030606090d05010509030d0e070b1803030d11180105090a 77
    0x1200300c0020b585010030b0031200120300c10050813240244030820740f50f01e20704030503903060410f9403c02080e007070052034610813a401c481d0700240316039100c1d10716144c1401c11810980c90b540c1140b100b1600095a810900508000d0300da8003000603500d500c0e02044d149803460004240d02030030300600400c850100d421050b260311410180d80300c0b8444120380101030086c450302e2845540682c0c080203000901c0705500381c0c0308048107681c03548402c5003680001910010100704004000035020004841801c8040c0c001800880c02800d001c00c4017844076205405481c004d070405080818010740400c210b2520307020074241406000203040ca4008228800600c40c0700040c100ca000310b500040440c5180c131030120a00e00550841c000700b01a0521014858507a4050000c4255060500c0742c5203080700404900401205c00035002c2a1070070404040e0251506403401c0341c10b506000c24000518252424040c541810108402840d074454080e94012501040086650b04015081c0070b035400d107840e9011840143c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 138345602 1250 138344352 138344383
    0x111040b0306011404060c030e03010920030328080c0309030a0302070c050d140c010e031b0109031a04150b010509040e0102040f0b03010f060807020a0605040c0302060a270602 77
    0x22642c030b5400694011200021a00c4c400f0000038000580e20344c80040c5501541c400d0b90350548003c0000200f5007650314900000d40101100e8060b8003010f22465002403281c40040c0a9a091a5111000108001346e94680000b060101244500c186078019152035000c1e0046c40c1031429801d082c1c40303403036890003050305076002c1c140e001421805020381039500d20002c0800030000f1704030309036501d0038103260540b03520803901501c2aa46248015801356610341403031000034000b444811550089180c02d0109081e85505000c0d45480c048003290021710b40045442580d803d22095060030300d801c0d031a040d04032030081ca03041e2070b003180d62600b6a030000c2182c440410460340070418a120a5005009214541c8140420503118800140c22202e8401960480c0d60480c0a4049140d44401c2a100400e0032a03100c030068108070f29000000d07020303a00c00340d001070140001c100308075140d60200e170044d1711041c0390001040d5001c04120f460445401e000c412400d04101c5030404c180f0303001029556444804010a9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 138346852 1250 138345602 138345607
    0x10c020135070504030b04320307110102010209060d09060e010c1805010905010504030602070606080303090a060501080c0609060f04050301050703020309010b012c03011b03020a020d08130807030c050f0c030c030111040b 96
    0x340ea2030100b002c12051f414070111102c110301234142c80c1d881d0300264089424420b4003072404982c1d0f00601c00e484a031a405031480d443d10b00609441001000320fa40100c40c02655090740c0503264109100d2011b03e81241e88540291507200a02d20b440d03440035034030080c1080100b12051000340d0f80082940c0859074420009a03d80005141100140c00150441c1400d440082304004640d01c0018030881c0050041c50300704050303602c801d1a56181e03007444171240e8008030308000692940c180030740241000d820a81040741415103480c0000e00396042036524900090b008030501040520030b00c624a030305c54003400c2c81009024440c5000d0444c8005880500301003842d9a8a034495490a40140c4803d020a0703261194408070488007034000d422080da800c0040c442c2003d00302d180c60061803007074007600100c00000d8010000e5501c0011f907a001c4a4124104050b0107110000204100801c869902c1400c01034003a90001505042c036140040c1c40840c800e81c104514401c03000f0004040350141c6400456555 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 138348102 1250 138346852 138346883
    0xc0b0901020c0d080301050a0e090a081b03030c0d0501090209011e0318080c070f060203040504020f0702040e0a1514060405070e130c0905010518010c020135070504030b04 75
    0x3420300c030710342d15950b400440da0040c0c0ca081000e082c000b14141e0b241121104400e6454100000120390101c461000580c0203100440200e138501c40a40039000601c110803c9001004200381d09641054545d01008a4040350b8a0380400b211b000c0c00340903041d034842c110308028241c07000074050103240e908841c106503800f049100780c0744a0341104514124042d1403602c80c510b1071800402c143d22621001c15140111280494a40310b10b01c2c0600840308660300550805040a0801c00290b22186007040b03400400c11180c801a102c0e401151031000341440a014002c4003801c00f000130380b00c80a052015207251440d000e510b07652102da8550800c0c0c068030001600d0780e4414069900b0182624856400694009042c480c0d8075560010104100180d0782e0902c20343d40c0d040191101c2c041e284c5200501000c0d40f038210102c0d44503005111400340149040406240c1d40409499000e5800004416072841d00c1c2200c0e8820124003c8036030016000d01d0300070b00d02440d5842d40c0f480301c2e2002c1c000520b2004c0c14003030301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 138349352 1250 138348102 138348107
    0x181101030e0f07061101060f03020603010312092106150b040306050612060415180803040b06041116022d060d090507090e160608060103020703020a06020d0221040c0b0901 75
    0xd411015012048607060f60f21080040c161441c00241e0700280c1d030800102255400d0401c101c03000712039000c0c0c24241180d084d40d0700d03000707000382c1c0101075010030070701d00380015200003c0d07640c0c080806043e01e402c01c209901801c0403002c0d100c4000c51803000c0c42007184104240304600d0111021a40c1042c070025994031980f00080200340300608a80310b030701c82c2d1b00c20b0100780100c2084440080017815004c0124110800c00840c903001b00e00c20140c4800030504c0000d000c07030217100c102c55001800a00c0000c4503000302101c070780d9a4000907011045032072403141d040114148030240100e6541400703000c8000440d0f400d00ca400209400a02c0e034050000850510308200490f000500c2c010b9000c0195100030351a000c6840c010403031402d55902c140f003001c1481c95694000c180070303010341d40d8554850078560345407001034020394014001281184103890501d00450b880f840509a01031200002513510f80074101140c1901802c201c003810002203841c00e00000400440d103070400c556500600c15100c1c038521005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 138350602 1250 138349352 138349363
    0xa12060b030102031e0f0c161103100c0906030209030c010f02070308041d060f01020d18030f050f0705030f0304060e15030f1f03020d11120312060103181101030e 71
    0xe40350598004018000c240e6280401c100b43c1d0150f426520f8101d91360154521221402582c2000d410780c0c04011401c100710036114282d1046002d52250000404048042860b003401126410000ca41e074501010700d099005290a000308140c0c5001d50812440f000040d4030b510280c10958140030545480310030300b030b0082c00424010740d0407102480d255940e62038461540c581103000c41048209a000141d07152410614019203440107078024682044c10210503281c2040d507441c000b80100407005c001001440c05440000480d01c140040c00c00703401540c001c507280ca60f0a8000d0f40c400e81010701c0d14a00c0c40d034000191001c0702c0319454001128425880030a203a100c001c1241400c4400020070030100c209458000c50050781d4004099146c804440b00b01c14826000b400000c1d804010441380d0008504007640c0c4048902005161883d5180e02c410030341c1c0385034030903400403c20a0b001000c1040f150f8161040110540c120f00b543e11024401e40c0d90014604085440c25040c559103122811600b5001c002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 138351852 1250 138350602 138350621
    0x201060509010305070312050304030e040b0f0d0303022101050114090103091403120604020c100203062b15050f0604180605011202090c0702010c021302160f03030e06060a1206 77
    0x12102541c50f0b0800e031707859020302d003c01c0d1446056512103080b1144102d00b101c0c4189d42595400c01510704490030040039211000445600081c000020881c0c4e036203043d4502620381c03082c0c50060360348211032164110a64001806e4058200e59401001241d8010300000310100003082001d40e10301441c00141d000305070380c20026015444011042030907120000090003480e0b034500405066680d01c00411040e0b00c41c03240e26103241d410074a02c94500b900c45801441d0400c100425107540b41e980811103610490090301829803100d4514000d034207210421010401400f850203090106251441c030110809101401c8a8040c56403101070025030400a4000e14206071703c1a01030203d560340301d0307003d41203001880e8140d2080c541100869961002081161120703581070310780c0034482a680d02000115414280700c1c0403815001c1019841c400400c0c064082c005201d841415605041410000e04581c0a2541e84d81240d0000c4184509a524030040c0011140105007001409000d0f10300000500001d0301d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 138353102 1250 138351852 138351859
    0x60b0406050d0b0901080d1d0d060504031211090d03120e06090f1f05040c03060615031b0806090903040f12020f0a06082a0304030f12060803090402070302010605 71
    0x200811100e40c04801440944004101404401c4041040088100d8207100f502e00c07a600078040e48019601505c18039078005040031403a00500340c0003000c29040106020115002c90752402040100b40c0c0084840228030443e010412000450001c06001c610070121003030320451700c140e808020184901d011040c0e82c4031180042c050701d003640c10421341e03800d0140c40c400b489005480c1102c8889400003410a01300341203202541c0f80ba44020944402000c01034415100158aa540030002c84c3c19401004000e00804a80f0720303080556000003800c031011900e020b1031075811481c1103035006500030891500104116054030710f43d00c0b402c4086196200302d078002c541e0a0860580010302c0000d440c02002c074507009075040050920b80c5410810500d003a800380e00c0c007062204000c036900d030210198110407041002403045103d80c064020440d203403c102c82c1140040d0030405143c039000d90000188400890054040c4007403401c00941a4a80c05001800c5009580c007180c507205251003500074400901014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 138354352 1250 138353102 138353107
    0x6090203031804061703030115050c0f06010306060905010b030f0a020d0f0e0f03040b0301060804030c060609150b0a020a0305280c050f06070f05181c0506150f06070501060b 76
    0x8081c140004042064054803d0380303030042c0000e82e400114104280e031108000514603680c02c00c0e50380c10101843c01b41d80c804004003401200a040402c126250a4103c1c0c140105030030340c907600d4010160b80c00d5030070840010b82040010009030045070240c0c0d4109420000801d5241e4030802c04400a000d50088202d00f075046c41920141000e85501107600d0001203000e540c20360502d00c00f000e0380d0f4071451250f0208800b041004002c1a07111345403250700248a0300e419142641203440d40001d560707594000d52041c550303030b10420f520f080b018030442d0010100780b90348a0030310f0040400692580103001000e400d2040016005800002c120300e07a901c80c010003a0781205896a240d00207001481c406000c079014414800d001c9085607001030a00e225808660701c1d0007142030080000c58041d0003022400340c02d0050810101c0d0070756640c1519540550301100d2640e0340301154181a86001006401041346401422078130846031101101c0700401907064542c4e681d655070510f030107801000c0741e601ca2032020402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 138355602 1250 138354352 138354367
    0x200109051c0804121e0305030601140c03040321090f12020a091407080a050f0112060e070602061501051c150e090109060c02150a0507030e0f160b180402070609020303 73
    0x2509182045c0120030895102075034840c2240c2445a103030014010450500018609610500b00103880214170344516082c0302040600a246170880d800850304505013110701002007000545400c031192280c608420304a02d0700302c690359412040d00801c0c1c00c40c4004000e41055450f5108490000d00c0d4070031007040100710200d011700308440b056a0541c0011031850101da01140c1601906004500326080f107091a4685084c859140d0100a0219030301501c0b81c0303811040d4101401748000800d2940c02520302c514011034000c100492861420341446010700c60720026000e81c42110040304000c0030009a03228001502c01c000080c1c0e544510900c45082c010000b50300f506400520384103100b0142408a400c0d44602070f81c480c030f550540325502405400001c0c102954035001f040d041442410001126810600540e0034602c0d80e81c004c119a0b4001218030703464664500158004204400d0090704000c040750410585c21800d118461040e42c0200300042407000c10b07032005100c164021f00b146d50312510b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 138356852 1250 138355602 138355619
    0x110a0b0105030105100311061b0307030c1101050c06010905180a05100f051905060a09240b03010b070311030904050406050f0934050a0b0403200109051c0804 69
    0x5007401054060350900d0b01150700441c0d000d50060540c2e5110050f84103808464041c030140d5080b0043c001c2d034a0385d41d80c000008a401c14401003021600070364501f00700c17403201d0405468015801c04414100700d000c01411000290100c0c11605540305c181020610b80c0f078020035006c2445000f401c42003d40070f034545010400400040c0360140e4062000140b009a180401810880b481140c1c00d407140b01e816059850014810780c052036100400400c2aa075807501c907842e20040b500b5803c401001c046040c12020400c200d40c2000708001e020b4034203414503641c100f241c40031182c000c1a034011f091000c8082503183d030500501c00d907103420783c1c064000c104a252034140307503019020a4862903184922100881d17411440400c904031054003541c40e0351421020500b41e2034110654401c0c21003020007a44d400718040e5507080f10a0020054049844c0e00c0e9800c1d0b04203c2504d2004e0403115030307500740d281c00d03a20035039030040400300480d2004c03103030840da2140c100c1c1d1140d07010152030402070200200081c01329114a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 138358102 1250 138356852 138356873
    0x13080c0304060306050301060b03070c02040906181e0c0b210c0304060b03011b0e060f030a09021c020a05060c01150303020d02010c051309020306010c051903030e0c1f110a 75
    0xd1883c2d40900c03107280e80d0004d2501f00c9506001e400c040c02020000160320f540900950640c1030302c05000041d030021a51244001ca84401000e8600e0703900c1d4451070000c1c000700c0c401c0012071041912415420300b000d50b030f4a90000e48984240080080085507001c00c03268202d003075444c80c19901c0484081317480c01921303071211544122411240c19203042000d0750f80f13080500c1150b04401d00d0010b40031902400c2d01054030f1964002181903802041007210b2034aa4000300055400345410341c1000c01c0c1e440c03da104002c5184103010b01c0048070084003a01b280560f480f440e292040301c1064442a9464040400c82e030b0140002d650040c0e800080d000002041603400602a0040000c1c1e5000700170030a0a07040c11101840b50008240d00104800701c00d00050449900542d005201410000c0c2103200d00ea45103130503e204004840b0010a4113002c1902f4580c250107201e203107588110103040c241c00c85000040100940c50010b1034449030781e0307058480042c000e240da06100f00303007841183c02c428103524081e082513 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 138359352 1250 138358102 138358109
    0x1005040b060909160519090905010c09080a08040b161a040512090904020411130914010605040b0a11010e100f0b0307030305250b011707081f0513080c0304 68
    0x1074031100006210301202041148001101040c2420041c0c989800c00221b442c0c0c08200031420a070113000052059000c3c42601c150394816800440d00407054640034041401940c86680300d074100e804641d0002e00d0442c00c65050707801e0444e5040c0c842c41e51400c0707481402240100201060011490400e031412400602442a4804e20803103c8079240a10201e1060040c1071030650412103050114005150603004400c0406882c232401d070410035084080c03041001c540e4000075080f5541c2c0156070320103906d9010240509100d0511901d0240b90003014170452091509030b008011040e0045003900c0e8080d0002d40311280e21400300d600f802c0380d5486481c010302c3c1e514400c841083c90094000b016042c082181c0040fa501a03d4090a080c031082842540814540710f104403002100d0f0342c040012083c405d840d02030000c010252408905840d0610303c0c00c501c50300720444130b0303000c44107040c6401803025192010140c81403011070543c0360f81480214000200c50000d1140401091001c04400004098001c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 138360602 1250 138359352 138359359
    0x60306060303180603040212030a11010e0105190203060f090109021201080d0903030f12050c0711040902061603110a0302061b0a090e060d140c01020d050c031b1005040b06 75
    0x8903140c00042680d20302c120344200080ea66000345810040c60842d002d99400760028004009001d0711003201c80c215070086500b14041811219151550b00091007400340c03504440b4001c002c6801e1031580d01084041c440500c00056800200040b1242c90b9020711429030340e0003501210b00c0396142c0c1c2164020703410503104400240321607800082c7e00312001404040e1000203449180384a42507450443e803100440001c94240041c1c0034803000d0340f190b00c0c801d05c2d00c43e005054050752160180d1030411303005003030840f0391407286081440e40005a602c21040302c044440443c800b005903503261800741d610316501c100c1496280100350000c000e0503004200c4a10511852003044001214012940e0b1540030b0300d180788000802038003007805944007900b540354102c02c004201840d816020350340c044c05c21040d061038603400e41004103c002c06d0b50301040702940c1040c040c1041400d10003c1116a40c2e00e019076450205043e84800c5d05e16082d072024071424007282001e9034103014030300c0e0605103108032203420b59000c1e00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 138361852 1250 138360602 138360613
    0x10030b0a0e060f0406030c0608131b05130515060d0605030a0b16080405030a030207060e030d06081603021c02010903020603040b0103120815092502010e060a061802130e0108060603 79
    0xf8070389007610400060300e5124018410090825208860010f402031040604e011501d954001050300c440b0000c2c0c064084102c00001d103402c00041c03080d00d0007080304c080b40e0b590401091140e0303050703c501030302a41c280907640545c5500c0c1104049000d0a442e520264042c001c00b00b034001408246800c50344070340781540040c1100c050a88080350403103402c840c040c10307641092054074401803082c0c00801c0114052130300801c02120060003a41154400c42d40031440070380d01d641c00c102d00c42c3c0c1070290007503040103400c00103061803860700400c21500c030040715a0460f80d100300003d021a07020380d0038500515000341a050700c070b240a00e0720001c0c0340001e00080e140b800340c140b40d11011501c52001c40f4404c2c2214254001c40010000601180800141040801900701c0c85208281c424440c10707070b800502654008612041b0488960342440005803a080e510340c1000801e01400c2c0c1c07140410301588800390001640d85080c16091002c1c3c1d500d40c0c104c4a80c4080882c0001404400016864000e03403040b000d0305c0c07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 138363102 1250 138361852 138361879
    0x13050402101d150d0e0c1e01080103030309060603080a020a0201020c011b060f0204080102041203170709090915020c01021818040b0a02070f11090f060f0d020d02030105072006010b0910030b0a0e06 86
    0x1c41d9181d0000c02240010107030727401400047d110b40c010343d40d8684140e00110f041d0b86c07030313a5030070190f03030410100400140e000e00240070a644e030400c00e84480140a0030f104485807840201845070480e80c41c00a8201034030b417100d5004644460f41140c006151681c001c64071507446c1d61003541003040c100820350000702102c0840d4003520203820098011002030b21201c80342c51600084501a0a0350031f42540e5003080c1030a0504050300c01d0000301020310b800c8000607645d05000a49036480c4041e4146030780942c01040c40703c07681017050f0442542013a00651801c0780c5586020000c0040d104034240144601d540500310070030006a6040c40c800c04004441034191943c2e60415511500350031104a0350143d2015003103915824668100c41c906400946060341e2210b10343c02090944405550070400240c4451070030209440004a0515240030700c00640030300e5140000c03e1465002d007012103482401c40c01c080142450080c0e0184152207405044040e0255850415600341d610480d0740d01e024441f1107a018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 138364352 1250 138363102 138363139
    0xc120809031e100b041503150c170a0b030f0d09030b0c0306030d0e010219050a02030601061d0f0d0b10050a0909080f0d0b13050402101d150d0e0c 64
    0x3060300d4181e00900704040945034000141060070145508141d0b1505511002c40d124240d11007c0e6000340c6565030324948013400d4000f154618925036041143c5000284000e07212a810315410607035240000c19404040d00c00a03081c40d4080c10315072103d10550380720034812604140c10a080307a0003881e1a690540d500c800a82c003d03c001c440c003039803582003001c610450a004003200690842c041c070456011100c0e5040414226030003040c10360b5141d11641c003250461900f00701d4240985503a00d013225121320040c10450300e0542d82c1d260f0310711500d28080c00340c3c0d2986a410300c0d000c41a80003552042c160400040940001c084d9004450041030b80940c0411607e40d103009080100b42d1000c10b0519120000d0305891540d00071441c04803801b515003442141039a240d458400030b80040c83c10001c2e8900306841042203001d265030380f0909214400c0c48140300400380111041d0389001c25034003000e0380b14011403803180034410825010117143c50308007a5008094005000c0041c1c4a05442142c00d15045603805d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 138365602 1250 138364352 138364393
    0xa0606060914090a110406020a15090b0c0307020a02060a2003030108121c0204030506070306140604050d050a140d02070504060b0415020106090c0c06050f010315090c12080903 77
    0x60030b2841c4029503200c215400c2c0025071a1303010034164000218520081c0245000354000ea01513401a48540410000d02a1011196035091042141002880303155650303280b819400900c3c00b80144800300000b170b03115009205000c60650b000f8803c0380d650110740c502412844c005c021102e0b02042c24107c0d458800400800c0302d058906040050502d2407145522585990150130031064010000501e0300c404101d500203400070310b104070301a103000e140c50b12004013101c0056010038000d1292403a00c1c4501e0720b40078102d40c00e45200359a180c1d0000201d00b412882d0080b004802000024942401200118042281920b01c030b07141d8292010940d80c0c40c100420b4491500070000c0c00c40e0b0400080014080400000840e070001d4000400d074903550700d103804200c4000e000303000c0205038540c42c504100100c5215265214441d0103003184d441d415500d45040d880d8102c004020b41035501c4a4035018800c84162501c02000b2404003007012041c42d11703040d841a081040d1690080c80b40e009003a080180e031504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 138366852 1250 138365602 138365609
    0x70b040e220809190e070c0b150f09040609020901090c0906030b0a09051008120901080a0e0a17070b0a06031109041a0403050708030a0b0102070603150509060a15020a06060609 77
    0x30340742041c140fa000c100a0b003411507000211074005110001d07990348031070840c030310540d140c0c2c42e12254860340c2e040001409000408844180d6646001c1e40d00c42c0d92038140ca00d44003407041d40c281c1084c1e84e80f450f10500030300c500c000c0030354000c00540002500d0b4060fa04013800201041d9941964103a0303d02d000d801341c412500816070b00c406031440501c10305040b50b001c16407181c040303000e00e201c0c03568424490381002141c50504512640006003064256086814550002c99080d410000d001c3d000d00b046440702c1c0050b100605058030010030440340c0001760b069600940d00481485880c0c20b040400c10010202480200c03801d8903926112070f100c3c5001c0c1420b500c030310342002c58104d2840480c01103041d4054003c2c011000c0c404188460f40c04152040b025600c00c40700c402000444144080c00645821125801502014188114265036150102c0850104c44064810b6030309a00c031070380000c04004151f0072402820301a1864144400d90020b0003e00c0140180400c100d42c41e110481182e002d2032500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 138368102 1250 138366852 138366863
    0x5190602011505090114011e0302090f06090916020102041809020406090209030a0809011701120212010507090b0705070503030708031f05180402180c0904051e06060c070b040e22 78
    0x6004001d40210002000b02241701450b100c003200304082100364401c223800f011400005d602180001090030301c501c076a6071803101190070b2400c01c10310100280e800100184200c4006000301e102c00c4040b4000d4040c0d6005c3c2642e41e040003480e83c00044e69000030600d480c02648603034201000062039805a2088605002015010f004d42a007035885410084d40314141e01070400000550071f0603003800140046000e0044d100404101c00c11070700400103003804000700c06025915100500100a801a5102d003c8946d12014561a180e0a040c010f090840e01d5000356018040003400004004045004601c52172038880e030201c0d00001c0c4656000408860300905802c069150011401506d108044640c40303480100260900d00c14401d1900c11034030705031744156100d0404a0704070b02614107405502d0f071050440c0c1d00d064103001024040d035940b0702d004d42030314001d03c0e00003402d8115545c248040400b60200c04e41c0c0c0b99a0b5995000f20340030f41c2034219003544110701005030398010540903654074600b198005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 138369352 1250 138368102 138368119
    0x21014010b04060c1e0b090114060303090f130608060702100209090703020325020304080d0c0f1403041a0703031b0e04020912070816080f06070309030905190602011505 74
    0x850a5138074040385181174030100200a6103000b000d01007920000000c0c810030019943e4140204140e007951110f24940207102c04250401c1602d480010aa50407904222104041c078100840403804c43d1800caa17000b0891804c00c400443c0071080000c0403805030117198200c03540071000f000c07064201d010b0711002d0f95215607c1404140001d200e5009182c00c01e1800b1a40c03000c0f481c0040e009020410086118005608042010005190103002d070102c3d4500b181000c4500d407107140da40402c1e080c80c69078000d200400c94132060710a031108105441c0501180c4034096650303c4c070202c0da107505400000701180024142649640d040c042500101d105809503140c00c0f003862055010403000c0c2d0403d0008507048510075a01040d2454104000d80c01000842c001e820028180526002000710b9038004084982c400095046c1c412000220705a10110915000a241055281c100d03038215107648200d600c0700c284034482d05650039090102c01150a00d4008000140b0440300d900c204044a216059110252 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 138370602 1250 138369352 138369359
    0xe0603070b040905191803030b04091a041e1113060b0306091b04090f050a0b060a0806060d05070503091c050403021903050a0b0a0507050708071b0510021014010b04 72
    0x5421880d007100b584144000051001182002106c41d400860140e000418920324140350f0988141612071106580c1030014500980321442154409071042d6000421078000a046c08460752107051079a00e42060200c00d100300f400d020140c080404482441644404100600c405141c4110b104540a09134018119903c400800811740402003a031250390380c0e80b0b0109681d800c4604004c101402ca4a04000f5840c000341707000204641e0010700c03441850340741c624510210394030b404c251140b9494501c3d103110680e0310b08010500c203015508041c01c000e0300700414010400d4011000d14481c00d07241040351036502c0f44d8080c0241d140a0b501400c004a441004144003608028004907466034411076545106662541c401d8a4101800420b649940c0b04105018100302039010b09a0030588514240e4241030341c030b4403548000e214010000300107003203800307c6071803a0040c98041d400601d8010b00a0070211510301e0040c1d1a00403080801c1c00d02d40c503110800301020170390070311079041c0c680032125241010304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 138371852 1250 138370602 138370619
    0x3040602070e330306103b0c0403060f0c080906010f060e0303040e1005010207080f06220b0c0315040504080d020c030f07030c030813020112021c0f02040e0603070b04 73
    0x241c3c005001c107075401014264915460030480306000b1040c0144003d01580703001401401c0582d0645114000a07009991007100b041d10807110001c0140384051084a490341d4101042500c076641c03008180d6824510f0103250441203501200c4008900e8903084215501c0e1004280c90f04024000e00d142d240881300b044c07100b58800ca003852004040601168035190315031002c440c002000702c84138a1105d203001428413465a05000810041140d0300089c600314181c0012507894400040003068510080d5070010460b5054660351650160000024440c5023090707a50384019610403181501d441c060305074004110300b054407544c1e1056402c03040c183e052854503410000654081840000c4510040c0300d00180555184001c158951186d00c1c0c406c5054460b01e401340012900400b40d00400c22071046100160f6007000603c540c1c0c4848800c0180d85801e090704400201008035010903111b0b1901107810f0350340a02e0f42c010404c0e243c5046003140c041d6104010196100e409009132a06501c041c44200003052 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 138373102 1250 138371852 138371911
    0xc1e0b0106030b0f03100b0a080d0503070c060f1b030506060a0e060d1d030403020112020a0519021006030c1d071e090e0c0304150e0316050307020a0803040602070e 72
    0x10303c02000c1d0300f11060007400180c545040c10340100d006a0350341c5403011540ca445181d00d4020304005000d801d08c00e280b02c0000c2d04a0000410307034810700221104c1101000620380c0950f810010241d001c2245210201c8034403160043e00140c580032070f1401001c44c1c11403501e00d0036286c4a50746940c44a140042140a000b1160043c480b5450320545800481e080c8403400f01245d44e400800034001c5d510b4500e54000102120203c845100f0301520401044100642c0003084070342c43d02048000d41e50078146500201d14080d036200d01c0c009400c0ca041404000c00101600079021a05891852140544001482c00d80708006072901030208180080401e1403148400b03c850343c0b011207080c80c1801c6507503503000b003400920896510445200c004104010401c0182c6501e5160958200400a5039400c0301c54940d00e10030017001d40c64010710400100c1c00c11908004070350880703a000e840740d40c100780d07552041d65aa030080c0c01103e0140c004c595010400c20090400a4428800010000500c2c031801c2425a0b540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 138374352 1250 138373102 138373121
    0x9010f1206020d0e07180b0d0210080403020f0d031e06060f11030409050c0901030e070b0901110102040f06050403050d031118011b030207060e09010506030403050901110d0c1e0b010603 81
    0x39141c5844e1502e44c0014003007840101080301c100d50307502551a00080854540da4001480f610468410601584440480505014040c02d0000301030b2600d060992800c40f40b044904d500e4425807500d0145140e0607081621004401c0500300c07040c4241c1c841300c3d8182c4525000c0d000004200d00500150b41e40301d45006251809401c082d207241a0b1600c2d8480207881003140d95803180c040014000c04507503454402d9040900881d805881001d0a00101980034424406150304002d030a0040003080b00003981100d0042c0280c10081244a40e0b462001d0001d070440c0c80162514043c80b4400303110b29000380941c802d0b120800f0200c524100c035203d07480006600340038802d410003040ae400381c02407940b4142107500050094008103006e51404200800220001800c2c600400b00a13004003c10f44a81c0180d036005035050500303a032540c508a0040b15448220440641c0c107100d600f51b0b001545800c910383e8103245006001181c0d88140d8101c0071a00384581d82c10040c0760380011001002a01d200b0340c04600c2a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 138375602 1250 138374352 138374377
    0x6150c050c0d1a07031d0607301b0908160504020708250c09020a120c0201110406080709060f020c011103041a0c0f01090804030308090c10080609010f120602 69
    0xa034510314181141a600131601500421ba44601440c2c03e54250345400b52501d006000030206803a1140008003e5411401d649000044601c409602c50b00f481007100e070f894412450030041c40d03000c41680c1d090440c08405110200e540400e0220b408480800c400d5580c000e00020440c409107408203210007540980340680e910380043c4180d44a000b05030862003000303003800a0780f030143c101c5428410180c40d083d5000111280c41000205000358020103000c01f2101c2141f000240003c0410042c1e01619246c4c0c60342050300c1d0300240103e245a00309000d1805504503079540400c00d52104820340d003501038200780c0b101503481802d6811142d84148859408070780403400780e0307007000d5451101c00e079080c1161a00f941641d00c0480c03020b0b4050000c00ca04110940d440e402408800141e894a05192013075000c06070030820164000f9101440822a440d109500600a01d4001280748001172440f4810744000e82303da01c026000152880c402035484e42950317441c040c410a200099901e1200075171000d07030035114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 138376852 1250 138375602 138375623
    0x30503060103110d05090c010e01020d030e0703060204030305190e09010308030711070602031209010216080d0608060f0105030d080103030203220306020a0206060a090509190501020903060a06150c050c0d 89
    0x4008103d4020307214900704100046280d0401140031414a05040144d5040002185010b80075a9001902042e11541405e00084181e040f138842800d0440036000942000d0000500000301940b02c4020904031110003101041288001d070102ca20a002c2440c084c0c0c0b000c43c00e001840031403c420001c50b0840300a0900d41500b031000c0c0c00303440c1003940c554040400b41c0c0010415503a00f02d0b036140541d0b403100281000318074010001512240000246c00e0182401d00c0200d01c24404c0c01c6160310040141a0b4441143c01c1450403c100d801003002c01d001e031302d00034012071050107011405000001c3c181e079810b0300035608101206241d00402d418200c1134408a110b01c08000001c200300f88018940301a0690140c01103240100c28011607043c1a0310050900f4545403c10003228004181c0c94145042290348190508481c281240a070062001560745402080140155102c065000d10200d8101d007103844a0380080301c00a540440c2d4064002d02507420800c0c1ea000c0c01d2900070803409040e4400d000110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 138378102 1250 138376852 138376871
    0x1b010203120114040e0c0d080a0c0b0a1509021e030a060506070c14030d05070210050409050a050703050c09060d090c0b0c061005060403031d04110703031e140103030503060103 77
    0x28071030030707400708824400b85424000c150509000c1c1c01881226400185015107141010443c491b40562011304049404141440011f110320310503840301c0d4003c481115582024528540100b1256104800d07444c0e040e10001540b14030340c000c1d54409506502d48004914489000c8081540014110742c88036a6803107000c101c0d42d4a40028101140c040c0407400c2019051042c40c820585450348407030f1107540312100f813150466004007250206541680d1000440b40c403440240c441d801a604100364940c00c0004000c0c0c480801e90050b0f06c82c0c60303c1d80d0306104944030445020b40c01d100741e59002c1d0700702c1000c110f02c1e9800d842c150040410385201e000461156070b510b2141d09400d82108a950603e90008414007003903c50170488a40a0141220b04501c7c02d0724541c7d000d00b0b0500341c40c40842c4100d101e5003541807140d1396a4840c0ca40031240500096030b4841e40e14006000302080d144007070806898800146071244203114140c4005505100c180c00750f400c6450a50b62030f007006203020304060712285040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 138379352 1250 138378102 138378127
    0x60503030c0109110a0f091a040c02010906060b0307051204020a0503010c02060108070e0c030a0b0d0c0b0d1a0604030308090309190510020d081306090206040608061206091b010203 79
    0x20010788500c003000264491092400740e4180120914240c0b25812400701407041c0c0404400000450700303078120000d1103028464468060034030a4501c158420300c1c2811040645406402141044d4451802004080d07101e059905a40c00141c0b070300c1e4000303001030100340006100807040300d42240c0010301401c0819940d00019081d2000b20100e10300503048031004116000007004040f0241903100d540520b01e2401d60341002040c00300508d01d98245458800605140d02d03070341801202903801c003980c1e900680c0c076805c40681d6540505101c406452401d040c2d8a0300b0081c1c00310007d5616001858989818510345085442060140c4510050b020801c034501035951030845241c01c15140099102c0d54500d864100710201103d03c01d00019500200300482e80d05601000095000511880c409403810341420504001e044501c0020f4002c1000100407070809d401402842c401d030313012512501c6909071081e0f0b00752244401e40d094086503204040303c0e024850746c501c02d102c1c40401841100e08041940034030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 138380602 1250 138379352 138379357
    0xf390605191713120f1d0409121d0a05030a0605040503040f031a010b070308011509081e01111602060904020f03040c050f010c0b0c03040305070c080601060f08040b0f0a06050303 78
    0x1000f4001c9070794a0fa000401c032400c00700945440050500c500d4250703058101400e00800745282540010342e01c2011003059869511070038005410048400c00340d002e00b20094038003403a80c0101c03c2062041640d100d40361a18036003840c2601c06c050090f01c080141684e0b01000b03800094001c6800e400b0a200100c2c3c80d940344001c031802140511301010301704480d9807141030f145030103030040c0020f610208526004203400000f400d0455030540d806034a42c4102e040121032001c21600040028054400420346100d820300c15a82000000310080203403181c24080e200740c174441c0a4007028145c3c140b054000141c603015002d010404000f07000580b034801c14600d8140c007a0320032102210413500c4100240103606103900444250b103c20300b8051030356000f5488206c11408008c00c00701a469001001504140c4640b00fa40c503010b6104200703c4c1842d80b01d510285c1c0b03801d401d01030200000d041c4003062003100d114510355401a174104901000c1a11410103100c51550000d0416651584407a070015940e2004c000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 138381852 1250 138380602 138380611
    0xf040213050d11040f0c0c140c030109050606150705070e0702160e0f06091005120c0d052103010e01090b010e0a06020d0e06030f010e040f3906051917 66
    0x110902c3e001485010003048620101c09004081e180000140e106900f241c130803442290010b041d07040c28410412082e15000e00031080c03a80550924000f1401c0240002d1000e00860013110400c5000018941040803400f42000290040d0321045c000c0003090380381710205806c1605072068901e00380d00100ca055840c0c00b254000c1e4101d150500400911100705c01071030303400c40401c442d503a9490511040c4196581c01074081c2c14410380c180c01c3e030407800040c10000d4614000002e04a1041c101c41403c0140e180e40409000303032034004a883c4c183d0018400b0408883c10380c0c0307554501e200c0a90805085600400382c1e04901814001ca5111180f100c2d605c3c84514402005641d004051038940d2800061a1882c0d1182450017028240b042c04140c1c0c0340d0407122415940c680c140407400399102d060400c1c080c0300310880900300c1e241c2c01520143d01c400c41c00b007400c52241121907402c0c0011000028168400d010700c1401c0c00071b03d052085000403901850300d2204188a40781c0342030121841c101c201d9140c0004d0300c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 138383102 1250 138381852 138381863
    0x30102180a05030a030806093105010f090305090f0102160f0e0c0a020a03110a05010f1506030b06040302101b112706150c0303100311011812170a0314090c0f040213050d 74
    0x102788008000e000d000e0b1180d034000200f810b03c10080313076076130140440c00342c00c11071841a04010315014031a40300f0061002c075050149100b80c3c2c401d65650303419094002c140554400c00b5409000948248050012642c01c0c0c10603500901007410a620300300d41c410301e0b484c42142e07a8024600c040001c0740007401800c120799907100002230030302d01d110002c0d82c24444071741c020400d0504000c42c08116503a244155811207805490081800c3c1c0034410844103e02420181a144003001950b00103200706172543c12079000c82a1040d50009500d1001c521000c08103403174020500030180300048050801d0000c01e007400d03c4a6488904003a00c0c60842821500102c4507648034069003c410014000d401c03290310320090003070030714011700c00040c0348081803800705000301600907144240c1402001f40c815441c0c509011803800f000d44452911100a0140102108a00c2641d1005011400403800802c445620010040500362207260307640c24840a0b400002c0386441e42054000c000905850340090b03508828402c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 138384352 1250 138383102 138383191
    0x30b1b0a08010e060a0302010801090e07180e1b03030a0c030e12160e010810020f0d02040306140108010c02070e0402130903050307030f05010f0302060711030102180a05030a03080609 80
    0x144070f0704a20000400c80c038800c0182107002c00150342c102140c6415034611103000301c0c0b01140c076140342d881d01a103a4040300c0201c2546403012042c20342540400041441c1d00240c51b1100b100f490b004e159101ca40e85402d61503002080741e0324449015520407000140700c1c0c02c2050104400c1d0001a41110b441d07064403540350001d078400c0c07404050702c1680304090011400c480c1d0080d414581202e070b0381c0c22848100a8425800601c10580d014040e09031251282040d2040d95151346a150a40140401c0c20210100c0c5004000100e02444103001e0300b0000c0490342d000780841d5140040d12007550b440030b03209a801c403002055141c44450103020340e04c0100e000e03840d42c1d946d80c101040010300f02c4c1d06140d100c0342d2891a020050003004510720f03042c011a03804641040d1142141c0c10415088400d96821641c1981300280740406d07807428221403c548030b0211580c1010654941c18140c035400410f40060008050000240484c64042851500003403502513516050440030400170700c1d0320000001c01c2e1501e461 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 138385602 1250 138384352 138384359
    0x2010603080d090605090109051c020a02060a09090506010905102003040f0305061f05010c14060a06081002030c0307050313050a06020d0b330d060b0703080906040804030b1b0a0801 79
    0x1c0d8003a085d0866146c1008000074081615155207034242e0b4401400c40700096002d0840305032080201c3d51306190010455a42d4942180c0042c0c04414140b007010507050410300000d01315070242100d01e0440310090104184d802c0d00700021030b007000744845406038408080880e80c2c0d200c0c10030401742000e13007a14209116641e041d42407607480c00b10000d0000341e11051042584011074140030580c401c641d020b00700b01e003881c07169140442d400400c2e01880c2200303204140c20402c841c4501c4e00a81e0032200c200c029101140c29640c000c0c0300fa44030441e07110224000401c04150264801d40055600800d19012441030605985e90a42030142c1403000703544130f0b5000314801c59000c240e48101504540304560400d9081000740c0fa07a40d510820101c800d091071020b0040034004c020380002c86840c3d40e28418100702c440c0d1118089400c0d500b0012040d0001405000052142d0000190340790242da00460300701c0c01c040c95a07407004641c0c1401000340b01150145480f4001150180d13014003550800c039111040190304 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 138386852 1250 138385602 138385613
    0xa030f060909050c1f12020903010507091e0b09131805070e060a080a02040f020408071e1e09090c090f1e0b0f01050d061205240c0f03060102010603080d09 68
    0x9504036590301c17903083d00307070804060002c0003c5040501518104109881c0000c00014001d0103050552034041d402c0500700b000503a0300601c5141503941d4581003103c081c0285907032004190050040881c008010000c0d407001d803404e222511142c031a807460200e8181400302058004000d49182111240d000700c00c00d00170b5000d27802c415540a41e01780c074070002503454400d09581c0c0e00c0b48014003a01481c1d558017900024005601154060f02c0e000044503100b43d640d40e0b5000c0c018011911101041802220100f0300c92007240740c0350580c045400b949070956007481c40c0c0a00a0008a8048420030707242540000d07070b242c450203804c40c403410207480000c02c40315030320403031a412591080044040346000204c035030607a42d00c50207881400081c43c019485640115888004100d550401c03000c41d81c100c02d451040100c00240c030001000342e10502c00584c0000f085c400060001620141c2c081141400911007079561000910707404801440041010b0b541c90b01c0d2080543e00c80307824000c4081e22600c1d55000d105 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 138388102 1250 138386852 138386863
    0x40203030d1506110a030c2006181207080c01111c090810051612020702030105040516090b0306071d1207170304050a050d0f050d080403031406010909020a030f06090905 74
    0x84c4044090045142c40b56802004143c00d46001030540001e41c01031891084900040c054000d0041d29143d501da80b02c840209061184401c1c544c8603c101da103800c24a602d004c90b100003182d1184006059404e42000107490724505d50a81c00250b1203286004100121014141d1140491a07140c0540c2c050400b660385042400c02c0f030310103010354103000c203211340650a8007403e21100850b240803c081420036100380e000c1d1080c004003030f50540c201814041840404582018941d0219035507500c00c070390310f85040c3c0c00e030b801801c82e0561540064000840d0180512406445607503036054030826440030070b0000c0c0c202108100000d41a41c05003400740441280102079089408800d030046041520308030014a40d00414041da43c0500c252358011001c00c01c0e0102641041c41d400410b447c100d110f2034400404107401164103030300007810403c0800c03c1ca606056024010380060756a09062810149040040e62080742c1000815071749469109c440c0e401c0d0310a03040940220440170503031244a04000c0d1900c0d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 138389352 1250 138388102 138388127
    0x706021b2b05280306030c1e080f030f0a0e040c0f020d05040503030405041505031e0606060702010e091b0c07080705030712060b0103090c03082107090509040203030d1506 75
    0xc00c0030460440d0042e042400b621500010404a0f11403d4074000c00f240540000d40c8010b1900407900004220725604030032640201c1071507203482c0d100a0360380c2072907070303480c4a142c01500e25900b0400100d541c1e44c1180c401410b180f11203050240c401c15849000c101110240040e00000844d0046040c3c0b1440c3c1c1070045030165015483d246080c6801c2100181c0c0f01c4c400e034450188500da84284000415030340f02d440100805004003030700c1d03c1c0072a41c08103c40816020101d00c4142c0280400210340b85402400e4900840d0182e4901605284600901450b090003602800f200100202c1d0903112502420050072400b10070405000451b240010035072401d02c4d1600007a10a4121590901409005a018025058000d2000f084900c10200141c0050907501c1c1701070400e030132180c0c000c802d03c40b01c4030003051522840806a08424003441849020040907500400007900c416810072880c542150041d4000b400142600d1a100d0040301c0074003215141c490038000401c0e200c0c0100005a0070201c4080407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 138390602 1250 138389352 138389357
    0xa030501020a020d0201060f050f040e03030906150301060f061211190e0901030515100819110d0206160203010f14010609060c030504060807030b1e0f060f0706021b2b 73
    0x207048c24000d4194801250b07026060044a8176030812aa0b80c3e2190402840e582020042c0c95503420201034a1342c0f103540c200e40b460182c1c80745c600c29440c01e0405100303440c2141d084920103c140c1e424000b00f01e0ba000380303001e400c01c1351a850310918554844d0324001801c0480b500b0401c0c00786003080407000b501000302910503e2184212034010070208601088804402d00390400c04040360b41c0d400f910154440041d00031710307822710a040000750501491040210f403103000c1e061102c1c0394810003082150040c1200c0000350051001c1c49454500b901c141841003a0900c020000708400c1a070300a408203e8945941507031568030a03400400046400041c1c9070040c140500d095142c5008a45000e032843c841c0d44104010000041c0006019522952007002c110b03a00909043c0d11048140d040d9140f04c2840c0f64007441244000c108082618264048444e41010b040c201814003802d0786030140250403101da01020941c170626500d18168052005005100759800b842c01c074103203915856503c4001c40d80d1150305 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 138391852 1250 138390602 138390611
    0x30e0604120e060c0a08070b0a0e100f060b030a06090606050f09100309140106180c0905040e241506030c160809130b030f010603080301180b0a030501020a020d0201 72
    0x200d0038090000012420300c2c01c25440c801c2c0103078040380c010302c55520002514084c0300e2004c400c00c551903004000c0b05010700b011401e0364880078041e0084800b80d03e4641c520764851121b02c42e8044040d00443c02d604140540041c00550714207688500f50310803509080d400750386640610841000d4459603020742154035105090032001c00c44101d82e48100003189100e9200517948951151003600400c000a40c0031104400340a45034540303501034449409038070f90b010948543c08415a209200312801084e0076039a2045191818007440700030109625802c005000e02505140c0d0046642c0f54440300c0e00707103402c800407039140c40701d00720a00c4000c044145101c0e1000f0410320682494200c142ea031111403060805552000ea494207105a115025603203030007030200035821042207203035407020080481c20340c2a00c040780030244041d8200d82240c040100b2090300ae200501a42924941984000c545841d00103040b01c800000950306240c01d070300407100303690001621a00d00c2d6040c0840741c1410b090b40021301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 138393102 1250 138391852 138391861
    0x1a040503030a12090609080d060512030a030e0f0a120306060507020d0204020901030623090903030601091502010b0a030605060102190210030902060706020d141f14010e04060e0106030e06 82
    0x1d4076441200c2d185010021140e00b00b00301201c003644050a03081c1d03c071900700080c2c021803030558401c0e00550081e0f04001e02c2d1400c0013400e410000884109408500090b5142c4120030360190020a0000c41450f02031003103011000d4042d00400541c0c640c0750241100d40002c00e2080c0d40201511415000b400030880c080c0a03900068555500082c0c4a55040780c0c0541c492022400490041003e030b1701c0086207104141400c0c0b4003100c01f800071242c04c6415590040d0503566180da0590701e1000352001400605000b804001d91002d04080203441c030380b10f2001054403004a0001003010301c5540090b584556a00240040d568040195101c0c0302200e615100c02c0070081c1e000503504140d100c0c2c00d00e09040d08c8140c46011580c4060032111159807006003151150135040c1c0708001041c0c40d801600d042c803026400308014200102440c0f18445106102a044506140c14642c2890074010060705004400c1c141d51011342c3c9174003800b40600880c085280c21503141c03040c01425181000c1262055401840900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 138394352 1250 138393102 138393109
    0x15050d0e0c090a061a0c0c0a1403010b0103061202091806070f0f0206270709020711010806061215010e060c06161b020f0f10020a030e01050405010804020f040e030c071a0405 76
    0x1014007142c00c00712181c948504c1b94100d4180450303c50001e5210201d500c01007145040c2146804246000b0750080058652010065040322054012a1840501da284074801440c0c000f880a5100751001c10101c01800307650342d1316240c00340c140d955101148401100e043c1c1a5440724409030076002c1403005040074186601100890003540100b1000319800c440035544819040141c0001484240c400315540c8101d0b083c40b1a0303041e5002c0f07203140041c0c1c0030b002007981d03460004251021092803002c40800d0b40c88402d0310101c42c16107641e00c0d41c18400840c1e5074280e541d83d0a405081d8821090001e4041403078070b1907090034400400270341501400106c00200100780b141000e80060658140c56002000c0d0510000901810182100517441403e0303109503030149901213600324601740702c1d80b20005c0741c0614500558850043d4040c00380040c041c400050058940400b81030003402d405800051501c620841d4035055a11040c2c43c84155844441304000c00c002000c114403a0608901c4403600b03107410b02e80007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 138395602 1250 138394352 138394379
    0x405130f02090c160f02030114040305040909020a180b10020f030a27080d09091a040209010c0602030106030b030f06010e0612121c050a0b01020715050d0e0c090a06 72
    0x280c05201d40e0b0000078410380d8010304440c2d00b104255035102c100080c0d441c0022030f85e29000e404a01950a20344403164400020350410b020f55410b407105030925017040345007002030100117000d90780301c09080710005505103980c0f00c0b4548604503a40200f4a4615a824003125261040d9031004650100554528504003c000ea624004040c0343c284401d04200403a090301d4100000b05081c450803901c03000a400c0c400180380c41c10300a054072900c0b8026510290101110b903010190001d008804610894900e8154000e01005d0414100441040602d465020480e00241c200c500460340d43e0351804c440d460100105455030390b54070014643c56040035003500d031034000542400c1c0500d5444031039a4645405005600c264101d07084030701d0b12440c6000c49450020b072464100401640342c840072421004031402188420517042e002001c81501d041e0807440046020020881002428400d040401c0321030301038602c80084103001426034050010411130302c0c1401500800d01d207464240d04000c6131984810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 138396852 1250 138395602 138395633
    0xd032106031209060818150c03010303021e0d0e040f050115140c0312040c030f03020714010201090c06050306040204030f060903020c120706080402010512270a0b0c071b030302010506040513 83
    0x50301481d81c1c0c131b503120074030f8084003058501014400d00c003000361108200b40514106c03030203903003200c00707507401c07040c00240b0380c9214003269107580c100044011005e40608a140364900c00a400060200440000381e000c503002a040000100c200c0aa0503540301d83c44090035440c0110b4441d5546490348203c02280d880c422a90381d00301c20b02c0c8a4000409201040485000840c0c0245501c0d040341c1d410b10b402034460900e400f03035185c1d05e0300e0b0281c60325080d4814410f21040650200946903982e04120054401d0b8100600d0907900540811010000402d59400c400009119120108000c00b40345006800c3c0440f44501900071810807000642111000070b801c070071142141001e4601e03031658001200e69204a02c1c00740e0b201003c1205100d0101d04884d2050b01510401c10a00d41500390b40881d2038560040e0311019010580c1200820108070b021401007030440c0c450b40b4413102101c1d01c00d21071101c0740442e5100340c0160350b40f101001124145402003961160300941e081d2584810f640e0740800d02e00c94003a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 138398102 1250 138396852 138396871
    0x27060906140f0f03030d020a2a0b091c0c05011103100b0a0e040501030f0c05030708030409020c01021b0601030b0f0106081801060503010501080a0c0e010608060d0321060312090608 79
    0x25842c1000d44811035580e200c01405019070780c0e901e00e20b424410285d8018218030001620249000d414580d1440800d00c41c140b160700d02c490591404e803508100004041c00c0715031075009c0c1c10000c2600501d01500d130702a40180303441c0c5800c210a2400d05600f11051080130703d43c05a410000c01040b91900040d05080e18121607226440d00441d0300f007100c201c1164001d540e0072a113820008024491400415252603218429042c1d080d40c40700c0605807181114421007106510900090045c081160064544422040d0006040c0802c24406142041c4400c10081d041d0300820018000e1049083c0c8403540710010301040781980d450600010700301e1500402801c0c080d011100c1000d6141030a4101c940140f030020000d009a5071204e51503900e410040c10102c0c0c036141d044100183c0180c01140f1107048640f40e444101e82039035010180700814030509021000c01c20b040154001d80c602031503d050501081d400c000910a00318a8030340c1c03658202040581c24400280805c02c20158040e500c82e90244051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 138399352 1250 138398102 138398119
    0x50f060c0a0c030c05030c0f01051b100603030305070908070312050f0c010c020105061309121404090f0b0a08160311060c060103110a0608011508040c2706090614 71
    0x100098206401d04074000d2618821540c0002481307684544082030f03420072030542d1001000708040108140c10548401d020800520104002c000b0580c406000306001d04151940340d1340d1504881c04131030030758208901295031703013081c03005480e4419550000341030300000074011282035803100400c0034081303c10407081283c0058100b40100c0703050305032080e840c04c600091007081c500e40c40290185c00304540c403a0003050040b0068500c80c4036400307414001034200000100240810004480e181520000312502d4401003000044007401c520a4051131010004c000500001701c2d03040088241e81c0d64000002035100f107103102034403103510704110f080301d62284280c0c03508152800807c2c054050951150900c0c0100300002040c05100120043c2080b0102e684a0413251920070070ba9100000707000d4265501803004103841030030301541c03840d50458080d024040740c2547c0c8501520030820300e42414000c0c038079180100d1140804d00d0184801501018605010700c80c10110401ca4440b4000c040310701c200c151 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 138400602 1250 138399352 138399367
    0x50607140f031f150f1b02060706090303090f050f151501080a060503030406030218030102040f090b18070e030609011109040b0a08030a08150f01120911090108010905060907050f06 79
    0x1072201c82c0000d0004c5240180514210840604010801e080100201d0314649081240c10312500da1b103441d01360700800380c90034002142c80d8200140314205c0c0032400d050b5200c0035200404d03031901a40480c580b0820040c0b41015100c10501e0400300d00741c1c6104040e04c2003c003405800b042c00c2030f074080c0f40c0300280380c401c805a940c00d9080001e07140ca03511054141c00002404118194140c00414030009807421100d01c40e5180e00c06e0500701d110314802d8000604a0078014084045c181d0000380c008040144624081710f101c1c00103000c032030011303683e9001003a074054140010b03043c00d0085940c01100e02d4001c0007840b1a008003002144103450f05244150340c1c030f120f419003941e10030804001400044c000c6a88460300c58801a207801d038182c541001c0c240c10300202c02802d02d030840d02a030740f8880607514681c41603544004034000c0c040d055012120b000180300c40718503079210550598002d020680000c5a10041401c0c100d08194016254503000d4020501c00d000d03544548071b0001188805031015a501c00e030b0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 138401852 1250 138400602 138400651
    0xc08070c110604080106140a08030703050a0c0204150918020a0b13080706081b0f04030204090602120702061005030a0c170f0105040f030f02011a1002070305010207050607140f03 78
    0x2124162030b90009003c1400303e4030300300550015082e01e0a0003815090318a141c410452544003a2141d812a0740c410440c500000b03201740f018114101302410b06100245d49070307002900b42c0e000d010711104202c1e114041003040503160b000701c1801640015040b044d408040d004904d04402e42d0003481110360700025202514802d80600e800140f4086040d00d407501e8803642c00402e10301c01595060700503841c0500382c850009078030080720078000031443d2503460140b855003840041d01207020156515582800407078400f03110680d900d0300c00c60303040c0d024040038a0010b5400c0c08820b165040300d03000f0f501104042d0001040c090004003561890b581d0525400c4a18408601c1c0081c89030071661326500300003c1c001003084010403180300d188640c49403554116024022401c0302e17400302c06030228034445030609185040480064158400c244150382805449817a0710b070a90b44981c81c102e03643d074080c00c1001900b42c0c0c00810480354410102c5890f107400504410300e0355a020150860480e1217000303c407002000c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 138403102 1250 138401852 138401873
    0x3040b07110c150c0703050109050601050a0f0e040f0203010504030c1403041a03040c030c06090f3203101109040f020702090705030901060e07080a0621080d020d1d0706030c08070c 79
    0x11030301e030442d17007401d0b243e143c0305001c0c000007a000c6420703204140001c526480c00400040c195800100102c0700d8603e0701500b0381c0404805042500c008800132905405a10b007802954481c3c2e0007034442d400710752968a0000000c154007040100307a070b00148010301403144011110300d047d0300d185c0e260b40e8998882d420320743c2411015610052404080c0500016003581112a030001c6801c00e01c0012100d81da690700c486042c0360241d04030501003014000020f46c3c100c07030010342e8082e440060201c441c8080000142030489400c01203442d5016004207a9488502c0c081c0503d0120440005040d81051041d60100340b001d440901400d00384076010000450102096008030000e00042e001c42c1e0319410092000b03098202e0943d141491103081031804600c60754086459140300000c0c680050705444262500f817440d82008180d52822502000301e04014515030161072043c042030a158070b40d0080c8440418078004455002a003070508180c00000299000b41d9010f901038058105182c80034010324180340d03801c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 138404352 1250 138403102 138403117
    0xf1804020d090b0a11040e0403390501110a02032d07030302090102100b06160c0909060b0117070503040f020d0b0f180a0503030403031e06090203040b07110c15 70
    0x45280c810304805000341407041c0c0340203500303000c0d00300700d1420700352000d40040c4030750300030484091f0400c0041000684030700c42c800340c605505215105010b80d81140e0310750b18504a0380441d0380c20140e96194003480800c3c4200c052460030300313a0491408010020183d10303401415030195052190742c4d24a22041e49905900001c1c0454152095894045140150003504048645c030300600c500d040d010303101c400500c10604200e200800b03650400310049108041c002124000b2604040f580b0760000d41d0000c03502403002501d100c1c84000ca41e414010b0001030106a000c10558841d43c09e11043c84552500203040300c7c1c0140e046140023a540e41d0500110314101e0307034020000c00780302c08a000c1103011400100c00c107003d26444012041c8400b00402215034544000c00042c3c4035070420004500002c3c003a920000d13105000100080b2810b510005071800c40b42d4591004004940010401c02007102041190741d0000490030295a0080100d1340103a071040c489034854059648112200b800e10700202c20349208 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 138405602 1250 138404352 138404377
    0x512150108011e090f020609040b030a11090c0307050405040914030a121a060322050d02010c09050108070507020d020a05040e070503010c2607090b0304080a0f03020f180402 76
    0x680d40d44185450003000c2c0000403007072844114001614446550080d0300c101d40d0032044403019889280c0030442c0c0c5900c00d10340326038000d640e5a0129696201407000300c0c80180036080d51711905c2c410406200800100500715400500200100a0171540000c1034801b80c40d8203503400200b01c425490121b9100262104c0c4021074403004c00c030082c05591110341c1078281c034020f680c240290300206e2120081c0c8521400c29642c02a000d100180ea403d05443c00c5205184000303030005500c0e82251a81410100c22004040050351500c0407080c0858000e01520001c00081c0382a407400d144c040c82c001d00602031b0304402445100b400c105a4195079500303010320042c02000b0800c010004110869940d154080d06ca0fa0b80654208140ca132055809805050f110000e1106140c0a00c64040c1501740c84000042c00e0900744a00040c0110304e41c11a60b010f107200f14030503a85141e0340c600840d4081c05640004e0040000c250042040e40509108074040c0d1f10b6240780d141c03040d002109400c002602034020061091030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 138406852 1250 138405602 138405643
    0x618010e0a0213120c051002070501050919080d0305070e0f120c0301050a1a03010605010c120c050d0905010305100810020c0a0210020105010617040206030c030a0207020406030b0108070b0c070512 86
    0x413807980c12200c0340c00da41d11650109010942d204144078400150980080168200080410655000f4401400e03110001058074914010b8070f81421550045500f00c40e40a07844426050903403070b014810250003602608000c04e4202c0b00c00001086403504078609030082890f0340b0780c003441c100200020445a08002c000340418503101819400405c40041c581c0c8068240d811103035014201031041609441c2c0695403039036407200c0c42c1c40d4007003580382080b02d00c000c03c5661040c03d00401c00038420060152016900d031102c4618110006003134500185c40000c140c10708850401c041840043d10300b540410301000541c80d03401c102c40c00d80c207009031030300040c4d00042ea61250120456040d4040e030b05a800d582c803910403103904020203000a820445000390020400c00102d0310250701d490255034807003074000000d8507040f141d80c0403030240c895a40c0100c8000359036000500c15200140b102c500642141001c0300e0130300300300500c4d15641c0d81183c8242801111030580c4d01c50b00030414441d80b100891000c20308032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 138408102 1250 138406852 138406859
    0x606100f030b0a241b1403040b0d02040518090c1003150e0412080c0406120b0409050a170f0d050c0403020a0b04080d09051f0905030a0b0f0618010e0a0213 68
    0x240aa200c0342c020340d0300522408401c00078203000d001c600c400c1510141e4405920812565011b1071140b80200c84071862009100014482940c10010301d00d03000e0b00c9101507125031400c020b00403020309418620403040c9000f405c00c9110a40021907802110084890203014000850150014108201d600c50241d0b030080c0c0100e00c140440041d076018a00c900c0c52803089a003401c070700301c80034881a02e01042c0d031201080204145403061011400340204d684000400c1c51150300080c00700d8412420450b40f03034111218140c2402000c52201030803c07000d481d814078027801400000202d01c1030070159400c0f180d40d43c000c41c40388403c1e08140c0d0051940900700e10001c40d22107074105903070782040c4a07080039403080c1d10024080702d01c01c1291404860001d400d0218080f0420040b1000307800f0118180c08000308050005503e507000c114405985000b0b10b441c0f81d25042c59452400c1841e0010300c0b01d405144194402194403d041d03450b2811540048110002d0340c68541c022800783c810000f140c01c0d003100401020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 138409352 1250 138408102 138408119
    0x10509060601030903080106110118031e021b09040503090907091a09060d1d240a0b0d0f060f020301270606021009060e030d1d0606100f030b0a 63
    0x11401444204120355090780c8000044003598881d040c002c000802050040001d0742c0030780502d54010661400200b0310307031071800003e04070b00f0602130194005101012301044041079001a103610300340c5417024103010502000391540d40b00814042074050041d9200260a0041c00e1060301d01952006010b00c0e120b04107880001c0c000040b5004240ba1603600c22010000708076180c00315550500d014041500300039420488100400d0b604105050b0a141081810b0409809011546a20000c1d9414500059051014041681004040f40402c40ca0501c00d201a039440324000c9901603404840260807207491b01c0c2400190140d42d00b0300c1240380c00800041800303500b54012400a0741e0f416401d451a0703060161020030740e001c9206110268022010104264000c0c0c1c2102042c50700030f0310b011a5007845100d0076895907000e02001d9034100d13940e000000491034404201c2600c0300200006016a00b0108005080340c540c00d0020424090f80c800c00c87c98607030081d00880640da00041c00304031100d80da41c040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 138410602 1250 138409352 138409361
    0x902030601290a0e0d06140a0204060906020f03161703041a071b261b0601050d030e0f0103270b090d08040209040c03050706020304090c0c081806040f0801 68
    0x80e0300d403040c00c2d01c6450030380712200a480304075040d907555038030350b00001d814064100d400340341c1907401d2619074080070301c0d00303c92400b21806a607425100582c5e4602c0d1640081441c5000d80102c02150046680101404400802d503140382c60304d244c5007290200390b46800d01c01c010b8203114030101e010010080000f4860407a2030309031070058030265010170b6030341c1410483e4216034200c0d8141906030750f8400c0c0004614028898084118608041c024500032452003042c5500510724803c2c92840d10301c0c81014107003042c015540100016912218041741580d0050320080709400c03000d00900e414400e103880c07a88250001ea07001e4800c141100440b540401442400c100d0f04041900e2072200b0001182500c074000400c01d81c0482c95907101e030a06d4076113a00304038107090041d2094a108405807000700105800340090002440b0300d400075a03803289420700030300548145d6401d0b0341c20310450f11040c00200b42c40b4011a859004008002c40300d498401001800502881c0c008140d82c419408002c12080d105501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 138411852 1250 138410602 138410639
    0x1106010303050c1902130e0f030f041406031303140d060b0304020901060801180e03070503160506070c0803070315090c12060503010b0f0111030c0d0509010f080f13060902030601 78
    0x2602d0b108141c1c50780d1000c0b0401e0751013000390032241c0d00d00c00c64102909a1f00c40c603002020001503426800c2140c0b00c0600e1a044040742e2a04800001002c112032001030810700b204c10016504c0c02c0c04d40c9072007078444d600d0051362400a414440301c4600e0f1100511050111504031411240821100c0c1d201c46010305690012501280641c40c580000b0625901803014107049986000e4031051041400f4082000b400c032150340072129102c14000300300080d1050020b04080f5401580e82901e980039802d2442c40d00c48080c007030005101d144000c007008146208201c943c011458100410444041c800d10143c3e50002c0d030080080781d00e40900e81076810f6001c4012a82e04410b00d10912080313407a6020542203070208010268010000207a0101550003401c608202e41c405030b050b03e0800c182003813400c2c00c1202000b04040024800a00320301c0540e00009403100ca045203242500072440c05484d68159810041c1c400c402c0d44003030648010800020f60494107150f58080c00351a05542d4070f800c000c004000e0800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 138413102 1250 138411852 138411877
    0x603120815090f09011410090209041107050a050d03110315030a170903162301120203130b2a03060301020403170306040c020307030801050d0c05031f0608010b01050d0507110601030305 81
    0x541211800e900003042d007d81c4005c050f841c141e45c90002031100a42c041c0d1049504907131903145140350020b500e0054882240118060210303008103140c594180b250b000101818540380110321b001d103003840006c0d60350040c000c07280b0300020311700c1c500041d00d400e00724035008000603e414250f401101c4040054100d0030803d800700c500102d44203d12003c00340150162141c1c29580700c3c207114008140c586880003030f0b0410705001086004100c4440c0980c4d008545441c045000c0412000401c229504116445041e07120000c003500082101d441030b806181500e00101000440031400c06e542c20b604490007542c0c81001054503404881000240d60403c035131003441603142012540200d4000300480d45819415510400160709100070031000030082c400603200d0600449010640d510308120b0842c10402000c2c032407101c50a8590180e060302e40640003601c00d030741002c6808a0340d0340c001c404d8a00e0039040c000c5c0490030751b41c1c540c4211440115251400d20a12074800004240340d00040200b10075007091 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 138414352 1250 138413102 138413111
    0xc09060c1c020304181505030706090501120509030316020c100c12020604080f0c011d06040624060e030f0a0308091002040f06110a050313180603120815090f0901 71
    0xc01c4141d850b030007107205162000c0e000e0f017003189800a03160711040158410002c200402e68a942c04240781c046035030001c10100310b0700c0c02c0c00c2c081982c01c0203866141d1a0314450500040c0760600f07500703440f030001030400388050b1500002c1d000994020b102404204401400c102e40d6250000700050464801d80002d84000c1d4160b034119403000d202013040c0b4446c82e08901c1c150b241078a801450a003980c01500c00c0c41d0b041d541d0703121441000c1070942d28007408070030744001000035040604210f0215140c3c110000c82802d00c3d01102d1403907a1420f106070048030741d2030070440034482401001c64200001c661000c0c0c103d014885c002c808050b0842070650107280484212105145001b807454200e1040c0c2c018454040c08407881041040d00ca805090b80d65202c1d401681c10600300c5982c0c452460300402d10705a12614180c2040c0003803100041c10324940100f040c070600045c0d103180c0314545c403008102886410408144002100d00b0032a030901c66103414041c00d088851b180030303040c4070100103007a52200700b19400c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 138415602 1250 138414352 138414403
    0x310110912010507020303040f08040306060b030703150503060604021c06030c030b0a091110030e07141002030f0405040b0a0e0a0c110c010f2a050708070515030402090c09060c 77
    0x1445400c0c07013008103800951458803141c4607040403d800410031107c0341c038101300c080002a03040c0034000040c000f07540304903102d003401c880c040d0540c0c050000181481c4503c0d41c042000b50340001e00c66411903420b980042c0d07600e1410070000c0c40d41c1e01814070841d0301c50810320004200311050710b1a4003120300403c4004440e03200d90007551b040c2d48040d5000350100e41c481c00c8404103450004040d0300251424140010100300305a000c1e0b003415125030044207080300311040e0f8540307400c054101403440841880910f141c012034410900312400750380283c0d0302403a03940c43c0441650701c5040040703028026440b01c6c1e04031454509c9005c8003424094116500042040c100c118507280001690740c04654141c680c12071109160b4012100042d8071588556421203544007a80050145842008424054000307026903030306212005242400755801980145241d90503800d00040e042c0649402950494001c0020303110031038091168003c104484d41d00040008440001201c0080c81110002171101041d1a640a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 138416852 1250 138415602 138415639
    0xa0302070b03010f05011b020d050c090a2c0a0b040c03030311181018080708060702060702120706060506040b0309010609020405010c032303040507090e060c090d0203101109 76
    0x78440e18044c20030b00035042c4015030041405400520319051030003c000e141d034000565a05115001391116001400c0009050034034440b4103a019000b1002444115180800d0f280b20928079040000660494039185170b61420a00c40039003100c1e0800e00c2281c0ca800c00e401c2c07175100ca601a00c07003100881d103003410a41e02ca44c640c0050301c0e040702c80b104402c103032104564140300766400b401d050401045620001d44503807c0044001c000580801030080c983d980c10405068036200016001009640c0000d00b08085a6030024111a803407052001d0b00da00d907025840c250004c3e03c815007143e40d2050010602180d800c5603480514400c1c00303680000e000e165602d0704208101d00c0fa601a15000408262a202c00300c0d020724030000c4941079208450300526044450b0040b25001620101c078184c0100390200407124860240703191060180b406403405084c02d010003031003071181040190007060884504001d56509021008032138402c000c003440881070712003081d501e50b03002d8052140720b18100b03801701d0580b07403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 138418102 1250 138416852 138416857
    0x6030c0a1503060305030a020706030b3721030f03050907051507020303043809010305090c0406090606020d0203120a050606160b01090e06190c03060f080a0302070b 72
    0x4a000d810514064246400c1c404030300ea03606144000c1c0341e110100000003e1042005190620043e405440d601707003810001000d541046029a100c0d8210200d20f030b011032408011980b80045143c2001e0b09a03041483c0543d4030505644440803807102c408030301d000300d0344440092076520b200c0e42d50f000c00c10f19800340c1901143c00a0300e0001c0103038017a090500640c2840d80840d91034416032040381c3c4c10116541d00017440c513803042c0c01ca401300700d2a61803901c1c05104403c51552110b00070702d80060554030300c3c0151958500803501c0d0181016150001709006071010700003109150405803003480096111340d0440b014100b28455100184170300700d04486801c0c8040180e429200e000700c3c0b850100e80302c0b42e6150002c0c1c0005001c10760302c614100402e0140c0752604005404880c4904e100d2a015890300b280320341101c4000180306a140c002c08104101c0150307007140b01a25115860001a10883c4900114000c0419821a0314510200c1002280400e0001040341c0482d00c65070071962019211041d0201a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 138419352 1250 138418102 138418123
    0x170a0b120319080a09031403090a020307120b010b070503120a020c0a0f031404050603130501020408030a09051c02010210151701020409050a15061103071502031504020f042312060901050603 83
    0x6240700d01f1141c101c00721034000390317040b800d101c00721910024260002420b0008030ba10100c3c81e030348a94004c0d01000b04004903580140b0070240321900740302c07040d01c40c0c544911404994140804480000a440025590592710224000da0484070300c2c003070b1490a00b1000744204000e4001c5040e032000b544601003121304031010b951010303210600b951100507002c100c0000d01181224155020300012406a00402c003900010506503952041d00303240905116000405030181c403592140e19010b00003503600000c402020000d111000201c000011442e00b450041582080d4071486c04960080d40c0b282054010b00141c4500340010030880c0c880310b42c0300b01107810383d002c18a031075140c60400700102401103d88031001c20f40c1c9001c0d01d20342505961010f52825060140345410382c7d000c0241300d003100c040c0d00e1410700301e203050f1021840c0c0350b9210250001c80c01a40700d4400003688280b041031101010030300400c4400009001d11000c02c040141031078507420b084446680e01c0d840c100004070b980c1340004154a01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 138420602 1250 138419352 138419357
    0x30f0e0105061503100e04140f0604060b0316050d050703140d1803050a03080405100504140c0109030c0911070503120403080906070504090f150303080a0606170a0b120319080a0903 79
    0x85031902004182c6c450000340269102600c10b1032260a0400511604006c6005040580131520380b512b042400c03149040c04a271701a900c041c80a91400307506c1d10718501030352412a06128010510303c2c02ca0f03e0302a080d00001d041c1c5240c5158000d8200001688894946450300e4060030103449d89010402c40740c0b85d01c400f17401035100304542000309000c2c200141e00940a102076865459441070500c003941c0c0d090b81c08507210707100210181d41d01c0c4401d10604001c80401d1030440311302491f6032100d408150103401259101039076141d180c2410003942e0201c0d0506a8408140ea4459920f14840308410804880507400724601c0d45c00170f0001000440c45522841861701c03060304150825000e0b400600000c02e00700c400c10759508001e144022484001d00045101f40d440004a2920310074090a950305588410f0502c060b4140d28200d15116508503540403030740d91b10025180c5820340008041100b0201c1079400c81c08001200c0707140743c404403c84078000a081c0c46412032915107800da01b08690b140d0401400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 138421852 1250 138420602 138420631
    0x10518061e0402010c0f0503070c080105151903022205072615030f01090302010c021902040b030a02090c0c0705090606071218090b03120408100c030f0e0105061503 72
    0x401150001c81150442d0041c0f500e0303084c502c0030383c0d0303001c580300c41c10407050301e440c1c0c0003244241c00c100d0788078668800b03803030014001c2c8600d050441c004c9a09160b205981c03071150400346009100b040851940354000d50700201064081e041c00007000003092119030705800c42c2400c042c0020402c0c1d02500030015100c002d040e194030440311b190340410041d400509100c40501c0140c3e6203004541d800c01048003161340000001411080303030315020742103481610340e4105540095140e8029020821400c0940c5501520007040d131020410010341010b201c0000203600c00390f64002d000881d0b40c64030181500000b202c1c1114002a2280104040e154084594a6100c2003c00c0740b040041d103401410040c0c003040f410680d4405090060409106656401203071449945d08001d0610f0300d41048841e600202c40ca9040c0c0c81d250070095840e40321081034204806103a01e50b450041461300c80d500000c0c03114140c0d8000c0208901c92421a40030780f10549085200c0d036801502406c801401d082128011104002e9610 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 138423102 1250 138421852 138421891
    0x130207030f050c0a21020609071202012109120906080103080301030204020d0b0303160203011a0a061110060b07060f0e21090a03050d090801020f030c09041d01051806 73
    0x1c4681c2c3c00b406407a109030140046100009481d009012210409a03008403040c08241030004d240c594010501115580803040070490704c3e1040d540e400c0c4194082c42c0a90210786441e100e12990381c07100c115440c4c0744d890243c421050080081442102000e5584e44035403613a900e0b2030443d00540c0a02019004590400c0100010325003030b8002c0a140607c003c010030741000c3c50300080c0c15500400780304420501c400c0d1600c0c00b1071400384030300c11952650104100d0400e1259010906102040c060ed20521059100384c0c10207400400460044001c514000d0003d1601c4c1c82c40030f0816080003a08407034981c10b140070388c4074245241c040e8104030f0000b14000c0880814031641c1c2000441090703507121403c00e080010541d291100c501d04000396008000800d08803c101100811a05503a0b00c1820700b13920600c03841d40c01040c051708580e0000c40d4030506030346480700b604c00079004203003440191490100c014144441000e041d04518881c5880001d811150385141d001251102d10031903c040fa40110701c9510f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 138424352 1250 138423102 138423107
    0x1103030105090c1602030a03082d07050a093b09101104090f0212061f03150504050721020c03040e0c04030c0303021f06030308071110110405130207030f 67
    0xb00070021320008003026040c80c64010900f0140c03144410b8000510f000108520140e84500e629240034001251101d440d040c104081c0c601040580035800300a800108400381512401c5100090310b1880324001c0c241d149481a480e0a6450000d0901401d014550900f00840110200da208084000c09818060003c44642000b0080b019072445019000d00020422008901c120004484100001a555410f4400351880c0f8040140030703d02c141980b080d040c086242058902d408681ea030300703001c07d0b11050443d04503254070450300842c1d0002d2502c000c1024441c0c0c0803a802c4481502d204c0006414480440750a06a01c1802c00d6400f00780d1080004100000028140980c07042180c9011070510352a6030b20380751007114540c029030040c1d108910030003a480e4005041d03081155080810400a403a40d50050301c100d000801703040030310140c40d54040b51981e060080c20301c1e455948a0400003000088201115034029000e120f00412071b0000326142c10809200321510150162640000510b10f031310308 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 138425602 1250 138424352 138424357
    0x10603091128060909060506130306151d0403030c0203090a2709080a0e240703020a02310e120307030f0f050403120501050604060c05030c06040c061103030105090c 72
    0x100200010b507610b15100405045042001520f9290b440b14000c40c980f944140507074081390031041c42048100520144400c1c0758001108680d40a907011800c030744003071070480c43c0181507482001d80301c900b021200790001342005201c0c400c1e803180d10100140c50822400f269039000742e07101076411040154080c070903d9075907900c4404402d04d0050824805c0c42c203081017001d407a985d90046801c010301140e00c0c010940c1003001c80103600740996080726500c1c86912a01405904000c6086501c02e000420b101414400d00001e946950050140d9801806004102d5914041d1000c49001040300d00e580014001113030040758034010500300203040307541907005507400d00d030300140111090580e41e45414904041600032000c850a2000001480b890a4207000d454010b5024600080c02d160100520250b61600244c805440040c60240d1680c080352500d00d156105178900f541d0b4911031001040204140b003400d841c10307038400d41e4840340d000a101404176600e010a0103416030104d5990f000a00e0121941c2c007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 138426852 1250 138425602 138425629
    0x106030201141602030f01050115050702010e062d090301060e092806050103110a090902090f070e0904050a031407170706230601030605030d02061305030906030c0d050106030911 78
    0x700d4543c081c8881d40020314086641c4025422a5150001000640c201200d082c07003404581c2001c41c83c10740c851380001c00460002c00b9191140300d000c90301c11208504081a1036028a03150680702409c0300b4800e0780302e40d80e041041c00c14807035802d052005c0b5060750410130032402000054000d01c6002848cc2007080003400c50800d8418801c104808000032400304d004540c002c0d07000e0074030700141c880e0030700070b01c003040440b500b000d46550b040040901c010303112140c1241d0301c281d0f0385c40c28100b6521000011141003a00d0500140e0100e00e542c00e000c00d114000c01c041034154403a8842d400f500c401d00d52880c485005158018020f11000513021b4100c0b5200381c020a04503114140018403641c2814150340102c601001c2c0344149540311040001558261041c100a842c00301c1c01010110700c07500000303584501c000c1c1281203051501500300c0c10080e0030000d5529194005194540320310300512005c0171908104d0301040300f1030030030000003010b90082c072032200c140e500908070b90450f140f09018004060b04806 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 138428102 1250 138426852 138426877
    0xe040201031407080609010f05180702031902030c071e0311130219140f0405010e060d09080d15060503040609020a090515120f0c13140411030609010603020114 70
    0x281041e0002c03000501281c464003c83c1c0b0380510604194091000f00c6005801c403c0c820307001c0c81c505210aa881640380a0082d44080d10b40c80c060350703082000c034110301418905000307070126215079130301d8581c01101500f540592001100e0a8541e10700c060b020b44180070a07041601d00180c0b006001140341884d100600103005440c0410065260090348100c0e40100e00791041c08035000500184a580240000707000c030384031941581000710020307052110344224070540e41800603900c5899020b03117800060340c84400540d0070030803900f00d041c00c0000869004403d02c0d40c4d485d02e4500c00180c0081c1c821000c5050301c10640d901400c55031180d481c5401080c2400d016130380107520a00025a8040c0390040601c03556292280c00020600042401019103400c2102501d0b5000645061888980098080d2600c202114244111660f905c0e180c0010310301c1480c00d02240503040b0400c02804442c81d40156041e0041c0d044810503940c00c13410a08907441404003e00003510006180c00821803240603204656808 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 138429352 1250 138428102 138428111
    0x307090b0301140906030d020606190801060603050106090f0605030103030c030c050109050c010f0305130f0317091f200c01060b03090a030201050105010c03020303010b0703030222081b0a0e04020103 87
    0x1941000040d4100743d100f140402c148107107800060030116030480e00320200f80c0081030081e000400107511958018855030140d00b601414a44000c0e004000c2d40c0100007890007000440d84804d00107000c0e00c0c0900410002c10301a41000960b01c003400042030482c0e607160f481c10708590840d50211024001200103804211013003d0910124100303100b044016441080140044540d203c0003401801301c5e010b03401e09052070802001400b444140007a15025480b40c079051070b00600d03180c161910112922103001040ca05801c00c4181500061401a0440d11071a51300041c101004180c0070341d81001c0c0900c1d60b1400d2030f1450903030380380c011002d01070521418001090041d2107103500206034104840300f01565000c20f00c41410301d40c080c46a103016203028a4000072041030f03510060755910061299078000940000c50b0001d151081e1f058403075000c0d1031903a03010080c0b40f2100f1040e5041c100c0c0589ca505000d0580e09500d240c82e10402030480c058050401449a80b910340506a85000104140e041c0341c0c94 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 138430602 1250 138429352 138429359
    0x20030315120f01090309052704050a05070e0f0a1b080702010e0307060f050901050f0c07050109060606051c0e0a201008040c0906060516060b030d091706011a030709 72
    0x3030142e2021485650000140d54aa03410014100c1e0b0075544004d000d40b0300070005602010b0b041d041d039010164134040100c3e95071900d10f4100e140c5012044007800e140207161010070030300d0450800b05c0c01503079800c40c1c3d08119100c040540c0110f803400701c90b4a0700c0040019500181e14001c505280d88024030340000240b0f40784003041c0300d04662054004640c00382d62264404400d01d250b200e029045aa01e400130005850208100403850300090b2521a004d040411400100082500001680341d80503001b408041d5640c00c000d0015000881ca228441c4012100000029140d00c01d00804e44540380c020000c1c03800035150a01c0d0744108008180080004038005111500c40b5280c410762000e0703655030300320a0320f8641013480b41001c141e000781d05400d0034174a04105003a449802c1d140400b00200040c00c0d809020702c1d09070004c0424040d46901400340c44541e00c40c0c0b030342240f0000c0840303020b481d0021480701c90885064442809025102d803403668900c0c004602000d44c030107075078005c0950600c103544948 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 138431852 1250 138430602 138430639
    0x1060e0a090f0b03060115020a02010c080c0d0c050c0d0308070c171b070b030415181a2703030109020705071701091a04020112051005060c01060620030315 68
    0x1249803040403183c0c0f00c004150303003410108507650050a0841100305a0307151140020b480f0b0f1803030003010381004070507100c00003440502001c0b25114010401141e8510120344400ba00d14040c411050710207009803001050281060341c26a1740d07156056485140e566640f81041c2e41444004070281d82e100c49038103220421810400003009207030f5a201e2800801300e82400c21510781085500044002c5409105010014118448000041c8a940340104020304444180542c03520510409481100c0c240082e5000c21b151894150103000c1400d000c107820b206400a1003090082001c00340c1c4298004c0004200c0950754ac1d0180c15454031900c165590799584958501600f0315044d10044070740d6542d556182005440190611b40201501505920340307800e40001e008458820a00584140c8480c0005d154003110480d1402503c80105042d4803180a24030300c0740242018061800410001e000489001468422400780108880011031840e80c0719010440c1407003c504045800c480150703c003440120307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 138433102 1250 138431852 138431861
    0x203070626040b0919080a03110904051f050303160f1a100810060501120b040e0312040203010609020403050303040f020301060f1d01050402130618120c090507030b060301060e0a09 79
    0x20f0040c000c1d1415401d100390400e0420303080070a82d060700241801d10400003204002610840201030400107940d11509012485034407a04e010709070320600c0c0c802048080450288014440180400d1489a0584407001d06640740b03d1540306584200501c0c6805c0002501c116440c0170282c450140041e038003000c501100c0102c502511007203c805000101031000300810840f00c078500782070100500c0390030724001c0083c0103100707409000c2c0c00d410b484164024068a49400094040c000d6204403543da4407906034803030302c000c01641c0891295007030103000182c1030b082e0700039107050381c0d08440a149141c640d076035064051000040120303015503c2e04000909010b2810801c402446044800d590340c403c140340b07014540c5416080310b44240c0c410300c01ea1441c0803411040c0703c00e640d4a41000c24a1030342d6030b0307d120414101c59000c3d801c0b40c2e213012040d00401060054070021910141011300558840040507000d03502004605c0d0380110042c4010442e15100c1c0160151720000038080c21071254480e1200400d54 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 138434352 1250 138433102 138433111
    0x60c060b061e030a05060303071128060201020c070f03020303090616020418060c080c03130302031b0c01090801020403110f01030b030a062004031703060a0f03060615030203040203070626 82
    0x2d0040b040001104031030003100d83c0903201301c01a40c40c1111540d50a01d5030714070f2940f141d01910342c1c280d070141d031541c510301d0140e520501007001c007030000d42c4c400000b4080d52008000718580d0080441c00552041e181c0c003048156076004000d582022842c2043c0442900040851410005884102009a19107110741c0c201040c400f0865440401c1d2801c20320240e80c0c0305a90704082141d030340f0401207105100c80c1520740013040c008290f02501007605080f03186020710745035050344242c000c04070310004a0010f01000d40090a880d800c00050303841040030301b00c2c01584000390103112501401e00302450700c0520107100040505000841c0c654801c0402d1070030344042412260036581d000b482d15020b00240e02c00ca111014040700c0d5241c0341c196a1031354483d489104800b03490b080e007c4041100d60351081c030540050031503000ca0322882135513400c05001401c440d12605030642c040244040005200380200e03842540c0140040904070b242c980119a014080100309415500b01c2d101080f4031420042c0b0700340034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 138435602 1250 138434352 138434407
    0x50723160b09090402060912070b0d0e06090a0303020d0e0303130c080318040504060905060a0504030e040603020f0d020316090203060306010603021201060c1a090f0c0109060c060b06 80
    0x80900c8899910440403541041c0310000062001c6400d541c1c599103940c0d0310541c103584603030b1242d004030041011a1000801003005000c1e502c1c0200c0c41080c200e000c2c0c902892502014010110319540d81078039044203580c0010710350003240f02c190202c0c1c040d4008100b903c414000018901901905550030b6420a032031003030054044d88051018000e00f424054081c00c4500080c610b4a4010403403081c2001340c6aa0950049032100c000400344921139004d003020315002000d031200740c40c141d2203c00041400701c900301c0106141100c0b41d60a4103242c401d00055035030181c1041c2094800104001c41e5441c0001c0885c2e00d4403540320340009460901101c00d0052210020258903420010304250500d0816001941058814490089a07002c040c1e2058115400e500b0424001012810703c0f80455041140b1041e220100c3c40c01d0055500d0300081c189100750311142543c3c04440220011150b0034854030603500011142083c4c140410307540d610030b1303800d5036006010b00d10b040c102c01041e840802004846607807 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 138436852 1250 138435602 138435613
    0x618350d050403020d030501140118030212030703090905010608041410060815010b070309120501091703070305061906030e03090d0605010e011d07030e1e1b0619050723 74
    0xf0940c0401ca440c120103d5414144119070500c0340c604800c0082a11a0303041041c4a04410350880103620100d01444d00541803c46140c502c19015a80e03a0180b2021000110814000500300220f441118140c820507600d02000b61216100e0842c074003174000002083c2d00610b103009030309081d14810000181074443c080e00e0325200e0612601207600c8164880c000d801800c01494000a61026086c03047e20380c2281301e484001c86909083c0d0042107414001000160b01c207440c10080c5000ba80510301c80c545e269014405075441c0d038184907480c0315101e01090200300241d003e1014038041d411045005581d0011641401940d600046081550300c000743c40a540c0c5400610900b1000c4481c40e0151001c121020690082194014050840101400d0815984516042c42258203012030b03800080000740e071001e070341c04400f00140c0300c030014001041100d00b600c009241504080054424130300c410222542c44242c4120103a50b142d003c0700040b245401d0240c108080351002c82c00d0001e10401c003100422 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 138438102 1250 138436852 138436861
    0x170c0909100e060108031e07060c050910030e0a03030e120f25030507080307051c0b040b01030c050706050601110d2f060718050a0b070618350d05 64
    0x4550300300142e40781c00c1c0c00060042c082c01e00300004448103009032499174000c0003000c2c040b00000d4012110002c150b14100f13181680c906074004098105a08110f9610301560030216040c1e085824002c1e800e140c9401038840c00c404640242e102c44a80034900040d00c440700145802c001485e030040d108583d00c00400b14501018031003050b9608030850b1644c240e0b410781c001e103440c0503001b030103003070740050050800000082620b440b48041d00c0c6c81c02c0d10142c0c2032080003030345044007000e07004071034415008901d4140c0c1c21110358440c4c019401e445985031580ba04d400b429864038030140a004245506000d07441e6840c0c3e01002007000703582d080540301d80c1d901a000d40043c0001c44a1440c06183d550300c004034084076000c2400c04901242c10407280d0604900218040d031003e0480007003070b84840c1d0b003e4502c03440000c5d40c0c03003040010807034103110744020000d81c4100c0380142107540c130394440a404540481e41c0071800840d510145e624661400600b40c2c1c540550354455900b984c082c2650b6100180c590081c003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 138439352 1250 138438102 138438133
    0x19110c101d0c06030c03040c0b0415020c040b150d0204030b07110601060203130e19020a05040317040e071407050a060606020c0a03120c0206190c0309170601170c0909 73
    0x1481048a40701a12070180c907480010340794080a02070080e0303880c000021504021000c51014028075070845000d80f201d5845400454420401c01d07440c015001d8801c0c11150740c6080e2041300d000c0d200040c503204144182032017045582d0046c2d048903c90590810022010031815016603105d41d213140d44000c041002c49008509094060b40302e581550f00601c050650302200c43c21031001c0d529070110046241e52100138005142044844050070140b00203505c0d41c4040d403000061056034083c14594149102103501d1071802e1050f4810b2540441c9542c01240b03205100b007002c2c4860700b0407416024109400e580b07801d8146160244100c45050303540c142006016014040309001001c03c9a4283c451031458031981c142444401c14a81005890900d407021980c40c40c09071b0742c03282ca0008111148142400000c3c0040101c00c42c1035000c510000c03800546055002e02c0d440042c0f0004000e042164070701504c107803101420324031141c054051030982e80c4480d2240d040d07040c400d44042008100c1201c1c614601d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 138440602 1250 138439352 138439391
    0x90f0411090310020406020a0822060f02011d120a090b0c030d060503030a1d010203070b010906050427030509010504150201050711010b0901120311030c030903010f0519110c10 77
    0x40b0f8501c50b0040c4410000d554012406002e09a00080309a503aa5480742d46481007202c0d104200041405034403010981a0703200c0e4210341c000000f9002003044115480186607401c00300b017005880e607800000052400d525420140c0400192814807042482c0c5903c0d0a01044d0407499424200b42e0000c589120400300c036008540050905030095842c1c607001d1071004282080e0741400740300111060300d80da040c5920800440301c4080e0801c903424501e50b141c4902402604c100e00c00e8602c1507007803040c060b4034402142940c044208003820b0004924416503020b5400d60003031420700707052003014840029041c114094421042e080c0e60300008851406110251000410044071112a850300103414400d07100e06502c24190303800c0341082e43c12341c4940e290481e01907484074a007802a020202d44040e89042c0000a004001001c070001d0088104081c140400ca5404549003c03243c3e0302c4500071004d492196000c41c0171900000788545c503012840752403a00e0407400448101c101503503004440302d4481100702 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 138441852 1250 138440602 138440623
    0xf0a11010305010308070f0201020705040e01020c061602030a0810090603050a020306010603060b180607080a021e0604030806090402041104080312010b07110118080105010e010603150b0f090f04110903 88
    0x74200001d504544501143e4042c105004021564403c0c15000f96802005104001c0000078014801400b9401c6858044d4110a082c1c000c02d05c070301004151040c1c0601400342850442e40d00071820021280012545100c0142c8160030384140b07450045040d6405005002c0958080c0000300300100080c4181450030034140c1c440340406241c00300c1030002080c20400c40714000c550301a10030305020f07240d0028540c1d01c501c10005150060001d44010210380105003030042144a01d00c1c0d074203038150f20b061680c0701e41003100d004001a80e1200018164504060390540141c000740001503401c000d0840240586d125400c400841c0e130003c00d001c403031030b4402802c46015000c0c44240303600b0311140380d0341e40001442d100402418443c28040c034a556400314544100100035510081c085965101004002d4490a0040d00300081c10189040c407142c044003010000c0b14140391005181a00d003c28861154008402c500e0340240c1610403400150f48030b001d00d10074045001e00b000d80d16000756040521384840032a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 138443102 1250 138441852 138441857
    0xf07080a27020604050901080c03070e06060304030c03111b0a06020f0606040908120c0a03050a0c09060f02010f060e15030a0b071b020607030c2924030f0a1101 70
    0x540814a01e0070303403810210380401c8a031003000d4800580c400600c1a01998001641007025400001005400090b410b00d90110540551b9080e5072520038558868170b0480ba80d80c3c0181c1d080000c81c00007031154104201e000c1c001d01c0d18001170806403090600703069880d00100308000c000a4040070510300720f00d40748002e00c0640002c045510742442403070349a5400a117901d2055980e81609020b10285004403111030800340b01d20481403a00c0301a9140d103401a0b0303a048006440c040c000340d2905c180d0310690540208645541e60714524148003203840ba81501044030440d52118030441c1c00003218012000901f40c11145200d0910b4030703801410038104070500742c511a42c0240a040b000c211076600d65a0858528541540402168150000407207003030400290060000607130481415800301303103101c0c0b80748904403000340001080c5520104909404160300c87d030b59800c000c40d40e21486601aa403000b15219400c0038440d244500081c246048809104144d4028030504020060076034035100c0125000d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 138444352 1250 138443102 138443111
    0x203070c0b0307020c0303040602010e0105010b071a06010509040c080412030212181c120b09060f12100615091a030c070201120c11010f0501060503070804030309020303030f07080a 79
    0x5854210200340907110700c0504000c0000030030b80040c0b0901054800e020050202c0f5070303075030341c4800c020700a200c2c50640201d5946840000b0400980460803034024607000b02c0000100d032440b00c0c0210652101a080700c2c103012003084507044a845a00440c1c20000498403000d68500d000e04242215041c500100400c0600c10002c2d201541400a010b0b0740240702c034882d488901400920b141e01d41044507000a504104a18104e260150301540d0b180c02485241002e0007651030000602049944c241c0b13425500c4110927136001c4040c00c04d03145100b6242d01007000c807150710101c44500811111542c00629940d081001c61010b421307003146100004041c45000100d4000046a24194a010160903010400f000040e00420f5a100b0391400d091038040072001c100707181283d0405000d500c0c0304081e8114a5082034941002604684500c504988050300c0360352451b030726001c08854121004000b1818140d0302c40c0c7c61000350b10104040e5100c0c60b000c04000d0101d080050307020b4840000100440216402d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 138445602 1250 138444352 138444367
    0x30e2b0e04021213050307020301110301151121090d030804031404030201021228050a0f1704020103020306131a0f030c01090b03070e0306100311180c1e0304050f0d0203 74
    0x12283c0b00c1c1c0d8810303818521040440c003589886400c40c460014007035415800e00c8411150050f04600641c100d07030300380c404a42c041000200c192800e0b030f00700051442681240d000ca48080240d030ac0d5400da00707a905002c9514000800c00024104412008141c000450420030070003050b0300560300c5080109100c40e23032410649103900003503a07660b0300200e0801c030f014007103100401c20a40c0c1031003080710300358280d920420a10070580101103070010804180019a5086c000c5d041070300616800a0354100d00c010b640351607031550011340c040d50020340f09036000640500100080c01081c4109070404ca040ca80c4185c46a403407004000c9003850000d24944280c0040f610f4044503170b0040210310842e039001411f543c69980300b0700300b07482000340340080582500079801000020181d195841058900c80c41004d02d88103040c3c4140b1400c103040c541100c0c002c100080100d04041d0b060400b405640c03030380b441417040c46018000983d1080e00141d8085030580d01c6100d0200302490144020f400981c03e6200070747c01c0060 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 138446852 1250 138445602 138445627
    0x150703230415020c01050702060708060a0f05090c090a0305070e151008070e0a0303020a061a030303010317190e0405010522020c070b03091005010e011203030e2b0e0402 74
    0x140070700002e20380e6103444200c000d254910f40690741e080000b0f400030400d500d44284081d44400044a600703000601a10001d0b00c9480d003a00080305546241442c6501c8609002c01e000c2d1210b00545076000000040c0f2606190f40c0c0e820b0345c00307030103107104d03c000e880b403589410041d82420f4406400311a07071581d400c21040181e00c442c0c54944520b8036030310300f009281e01d804000347c1d812458030704080c1d040809174801000781900000c0c040069171145070f0412070050018031409001360804240c55150b0410401080441c2d0000c003000010140080780b28a403460780c41c7e02003603043d004001d54005c91580b40c82d6018902d8544101e5004000940340d40c08001d14031a0403001c030003500c007001e091441e4080bd058140f0740d81001024003800c5c19a400300c2c3c1da030800b0206d51b0303039500460341c40d603461a00b8040041130154040c80014100e940440d50030a104c45a560107501910041d40315034031901c40d01c40d0103941d00d00748034841503c8e0640c00d40c4512420045900040c8000b1940078124001c42c01044819007850 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 138448102 1250 138446852 138446921
    0xb010806040f0e030f0a02060c07020a120c0b1605150702031c0b0d03020313080d120c050909010b040513020715091a04050102040e06010c0b07030b04060503150703 72
    0x8008541c0040c0c441e0718080300c0001018810001890743c07201160303136a00140110024001101c40d034084410070303900c021145409214507440250041c040500800117982090909568113204503c45c20420751200d0180a00fa0451400141e601d00600401428003000f40455041c054003014080158640038070003030358030b00c2001c0015040c072000741c9190150400580c8080c40d41d04000341000030504440c20000d503240c2018075610551981000000380c00c0394002258100c0072415124a01c20b5403484c2403000040c2071720314200040c001c081025560341d41d41c0c02c840c28007809001c0c0140d61101d09081c00e0220280c03501d007a02e40080d104001c1c0d01c0208100549204103204580b4010450000c58980140581c480444100000c04c0355007c1c0810008103402401c26541c00000081440d912080110b8003001c04400203042d8140e0200481c44291280e009069202d00103403000c00c0265031540400d28000041d480d1001c803c203e003003401041a41402094202d060340c41b03541001d641110215590b02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 138449352 1250 138448102 138448111
    0x319030c12020d09142b060b09150103020703050702100804030801060207080a080901110a030c0204140106390602041503020703140d090803090a0b01090e07031b0504020a050c0706030b0108 83
    0xc001c1c80e20b510503d940c070070a0f84221b0300d0510a6840d0008245401e070320031001040c004881c61400c100d901e0407182814000701c2c1c4124001c4800550820190740194025803103135100ba8100a010850741025844010071500c00c0e5009a07510b248a2a050600400749003060300b20b50215045040200143c40002910141c00c2c3c3d00040314603030743c002d4500142c03090003982d04141c4050003001c3d508420305412456000b031260082d01c00384608603e242207113103855824028800030032068005400010703a80005148064580280e2000070f007402510f03020164000d04040362199000036080c4020f5000c1010340388103822a060540c1481d869640207071410119007548559550007142400c0c060790f00390000c1c500160080300d59980c03030130104103050b11510000010344000b90f5040c00083d00716110710411112024010103810002c0c1180d07201d002400f501010000014484040460036031f480d072008005410480e01ca8550b0350081030201070401c98035031300c2402458988686521581d0700f00440d554407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 138450602 1250 138449352 138449369
    0xb250305060123130803040906060504030209181f0209040e0609030301060c0501060b040b0a112802010201141005090f070c06112205010e09010b07110319030c12020d09 74
    0x420560f9421054640a103800c4a96120000180001c504030080000c00503a005600c0c140f00b0070740c4800050382d01c0e00c6107100003900405c0d41000a4444180c8610074400005070600361049041080800b000c0d0030742c001090706c0e1590703000030410002d140600c6054080c034a490060102c0c0d15000b005162680014451801881806912001004000c0d80b080028100001406890326150a1594000d410240070f10020941703025200c0d412000004d440c1118258902c03499101d40d07a48802d00b01342030000c0100700e06540d2140d10802202000005d05403191809400038031a452511007008640741015024030340c20203050050021090340300e440c001d0f40d00d400c448003240b0103043d030b04420303210300c1a00346030104c84a110f213844d1550442a03250304100c40e0241d0f02d40900c8001e00041080c641400e00c102d6105580070010100041c24004910800d01c07002030940f0300703001e40440820f0740800c2000d41140003443c402a503008100c903c0c5030803005400700c0d20040280d80188107001d0300f18900c50248049 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 138451852 1250 138450602 138450647
    0x50301060e030f031608070c0803091e1f03150e0a140408090d29040b01080d0522030b09030306040609090201081f050d0803252106030b2503050601 65
    0x34032200300c040387c500d55032108503907000c0380d80d90618a4032500000c054910544c0100d80000150701080f101840901c0001c0c5030864400c0505151013091702c44500c000103141d00e4542030442d403400c09007420010032a007854009145082c4d010382d41103841143c41810303070100300414000490bc4e0b90303003900d04c940ca0603102d29040c0c9189040080c5860710064010003e1a00b8082c145000c01ea14481203014510501119040da43c0b0b6002d42034407000c1c0c90701b11400084040c4244c0825030080324080141001407000181c495450391591035880d030040b1030101580d440041881910709091141368010000107400b00041d001c9603000906582e40600700c203e0301c4518620000c1d0500c428081103000700030040846954090340e15000201e03030401c5070286020b0b012a525856460244141501c3d07904840d41c803a101e82000000c0c007115840020101a0150f54841011001801e03c640c114021b4036013103001c0c0c00040c85a101c80240941c195000c03000c0608100a12180741d800c450900a9203140c20607980c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 138453102 1250 138451852 138451897
    0x6020310050405013203120714010905030a110106060804060203070207090e0706090509090d1b050106030b0a15080316020d020a060915020a0309050909100606050301060e030f03 78
    0x25500303900481d41c424508000007410141078036040c0500c03c4000c0d415640032500c2d1007640c4e03000000d02a01ea0701034024103644442a07054200802510f8400d01c0c110b8000070032070701900e0031502e001b00c0172109640009101c09246030444500e00229107920001c0c800c45041600040100c00d000c0c200803c0540c01001003141c0c1d900134801e900c0a040c07181800c00648009042e02a5240000c3c8541b00124001d800007040c54281a40340c0c502c1503200c034004040007020010b0445020506070b40301d11800d4940041c1d40c0c0001d0b0203000c1c0380300641c006c000350710241c1489a403000486451100b0540c0540449108000000002c415034026075010200400c60382c01500200d000300c960f4000007584880c9000340841c906400903c41e0050343c860700501016a01c6240d003c0e40d685c40010700283c041421200200507134601103244d5039100031010103a1302e0314407481400700b00f03a40f80d80d044800031400200040c04515400100036621280c11002822104501e9004d940c403485000d41641219442c01c9844 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 138454352 1250 138453102 138453121
    0x1020c01141c0501050f090402030a08070c080d0f090b19081b030a0c0206010e2a09040207120210020f03040b060a0302120105010302040c03020304111009081009020f010801030f060203 81
    0x102d204441207039801c0e408180240c0044000c001c24090740e8442d03030200e41107800c1c03801d05000c030034403039940036004185030300c00c603252003220742c01c03500c0100c82e007109440000c034801c0400e0222030294031030754480c086030554211010f008a0707450780148480300c00078000079030315103000c180da00c007804010b003000c1380f261700c6042084409800001e18604546c034000306010010041e82d000c1c0032400b10980c04d54503c0d0b600c40709100903140c01074540e40501070f1140d02d041c0e1600c0150500354049070616455a2502c03940801040c217a8020360b50550300480b506010090860b0140030001540175040c030218a800183c5030707602c01c1c1c0e000162018060900360301c009046501c1e02c0490a000d150000c1400c003042d0104280d40b400b0b454240030881c0200e0401000440003400703030080d00d000d1584260300c6030001c00c0310320502514005550402c810002c42c0c52001590354002c1c4150800c00c3e1803040c0108200031180144081c40301e01c1c11601c0d0402000100400120b102c1c03001180d02c140d8000c0d005662074030383c511503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 138455602 1250 138454352 138454357
    0xf0102030306040c110a05070f0602061b180d05150c03090a15020f0f03090d09030809060c15130317010b030105060318010f020a1209020303041205010603120f021b01020c0114 77
    0x1c282179403261607480414808005222012180920b0b44c80b42900e4840404076290700e400e0365042c3c0d90040c0303003803140c10b09010341025006585204185009485480001482021005c0c505480c550402d110952509404101855205660008451560404841c0c2c10350b52030008201910f85042501d50014850154040705c4665102c6d0441c01d44483c141d4810310205d500580b1800120711480d41c950081034003c000c03840481341c00810050030b01c078846d028452640d0281c051200c0780d0013500c1e9400540710780103141a028040121441c0c00000310303481c004e400381079400e01c2050444030a00040116218000440e81500c00907500c080d201e0700d45507005140c11010404402d819420710500340e00d05020f03036002c1c000f52205981c0c2d440049941040d40411140100382c0650590030810050000d48526641c0c1200030384a4400020516a251030740980c0144c29502100066804d030000302c4d03910350400c000110303a91740030341540010000c00c001070f64030b80103102c0d1503042c05503a4801030440100e4109 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 138456852 1250 138455602 138455627
    0x120d1a03030307030501080d0806060405010507050118110a170a06110c0703050c0a2117040305030d0e01151d04020a090c0e130c1413050a030803070e0f0102030306040c 74
    0x4032526803c240c00081e02402003401032500031b00c00c4590307013a18a84691000c5000c0c0102030700c51441c06050100468243c0d01510043c1c42070764807203000004074a911081285131600850041860101c000100056141c40f03a120030b4684d443c410000c48084004120a030085270302c00d90021b820000480800c12270700960645450601641c5000014000041040d4103da0005c42d044c0408644802d00101c2101042e514428984a0b0441400c0021800310b0400d0000c1d4004079110b0401c0d42c0c940c0c400c2d02e1a171010100e20f40b900e0b1280901748401c0424043d80d1400340302d0000c0d4004040c01d01940d884007042c102610001086642c010400f50748a420f50f0101400e04800c090005070b103070f40e001800507441191941e01603021960340d0800326803d44900f00c3d01e00007594400d01c10483c2c40d2525180c42c3c11945030180b09c510078503c0090103035191710000000303605c1103c03195128501044080c4c200e440320003401c0d015040b08030882640f0b81e03021048a6211800301d600082c00d021030700f0304035a000c00022 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 138458102 1250 138456852 138456859
    0x2040b22020d0b18010306050c030906070e040b040f0212061c0f03051c05070f020f0d0e0a0902031311030102030c0403030302031503010510080f030406021c0e031e010c02120d1a 78
    0x40007000c0784440401140c141c031f000301070501c02c6450f034031007822407803004403082e1000b5000030011030800c9210327100c2068003200003400443d00441060005044410140035040c170030354009122402030031283d18141d070050080302e00003400ea101e60104940780d00c00440c0280701c0c404545200c3e080600031010f9901601d00c4010640f4000c0040c0404402007909440c4540801c60a040c0a2021b62000607400302c0d000d01071001e0300f10030144620946107504040c0c00140e00c04034a02c40440d965403e03101440c422440340141c1a42030103a824a5503588031040c01181c02070340100100324006004a0440d8102c0381d15140040c0d507503650204540070740001590142e415401c200a1101005400c4212002d65000ca0309588103d01d100f108180d90340f1640c0310340005038001003070071006114440e00c003010451302e506060101c4604000000d0130201000c0d5825840355428080c00c1012100344512a100d46182c00101480c816018841c2098056550041d0101c0d498a14810141c451888041111940075 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 138459352 1250 138458102 138458119
    0x4021008130804090c0219030519020f031206100306030503090918011d010b040629040807090203070906020a020109031e0503070614070f050313030302120a0902040b22020d0b 77
    0x1411000003401070321741c081005100340800c0e000301c1c0d610010b0318491107a040d1200c85c608500c813075966600c1118902c0c2c840c15409680032180000c40c1c01c0c001400e0210306034101700118034002042009408260413800105031400c4000d100081c400021180d84910403038080d14282c1c0c1c0e45030386d00c410181d4400c1c030802d15400d101c520400ca542c031a14003641244010002e1002010b85010310046581c1803186902c490010132184030344407111001c40c1040c48022408510b040d8403000441d1400d1000e5100075207942d4000100064031368082c5074003006c0d00a91000d011030702c030242c00090180b8010302000d4550180c0005c0f60050f00d0705040741d0b0368100d60100c203617519589142809401000c5d5040c44400f14042030002031141c5120300815011075245484060a40c0c0720130307a0040810120840403010326034200f1030341c00d0180d0340f0040b5074800d01c00501c020035904201d106001c15150603140d0716010b031071404071b44000c040325200d0b042e2041c03580c400d0040e00c0307441580c4244043d0403141040c1d900203250 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 138460602 1250 138459352 138459359
    0xd0902180901050705070b04060b0102010221010f05010c2003010e070b040504060b03040b0f06010c06090f05070b0f07060e0a0f0c0f050d080702010315051011120304021008130804 79
    0x252440d50303108900701c0300200b010b503482c03200c00c0e40c09100d1140020444a1103d0018000551942c0002d00c008010710005042007541700c2c0c04041c64900983c48d030080303c484070040041803400400d83c00540002c4c0317005a60404240d4408004080450704a40b00c210303400542451901c00351701141121000f0011110265952850b000c11760b88203001d2503026905191000c503c0521310003c4900540d40b0503101c403540e1351002130a450040c0003401e40e070b04001c5c03003041010200b10240603080c841401008112145c00351440c20606d400d20307a0340103c201c0701060040c1d080d40e821000a880143e030b00040007082546a2030300090a0a038440d01c0144034212a5503281c1c117101032024014280c5c2c1447d034125080944400400c42086000320006051907420005500194403a805c54a4001c840c060003a0006480300300150034a10542000400100508a405200141004221035101540280a1850400ea0041900302c0c0e950702081050100e0703200030a01c010704450303403004620b8000c0c04403606c0701d84 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 138461852 1250 138460602 138460639
    0xc090d0b060f1324080c0d0602070606030309061e1e020f060901091a0610031109030d02011a040e0d08040302030c1207030f080609040605060607060f150b03010e0c0d0902 75
    0x400703203588004c0301900340030648074240c01300d00d1003581c1c250002000e440c0340700000c1282d8021002c10071030380240c0074002240050214050b5002951003521041852420a4030041030301180c2801d88040528240340101c032560090700c40c00348a402c80e8283e00395041449401c0c0d00c1e01407040f400441c1441401d082022814040d84102071440c070540d0f040c0c0a400c4003841c90640748100350360241d404508500040c680c103000390b00010116000c204040c1c00d1a0030400002d003080d41c40090ba4025035119805058a40c0c2c940c1415000c0050444007000400c1e66402c42540d5003c2d6507000c1d409020001d00400d00b807500030400d0b510000d01907003c0b038980f441c12454414140d0000041100440c0506001030106809400035620445004c0e009009135600d646800000e0701c0050111604010300700060b00c04184d05019449000b544008081901d607280302d950551010281d110005a820900043c4003140c80160000d40080d4050070460729031a00800130f0000f01440e0785d000354041528107540d030f83c4e4035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 138463102 1250 138461852 138461861
    0x40c0c1e0215040602100902040902120606010e06040b030c0a05070b0103050304030506180a0f2a08120304080313170d0507080c0a0522210b0c090d0b060f13 69
    0x40c42900c1c004098041d200e00300107580078a0140f00017581000210364200d920135400524001c0c00108082400503094010070ba0116070750420b0400c640000d02005036958200129030b10782c7c101590074034a024548420401540000b40c0601c1d5410000501010320502c01c0c415240e089070012018856541e5a00d425a600e030320a00c0102c881c1d0045000240c40d0f0142080310254440100700039009401c8290395507a201540604111007002c1000010700c0b0085180c800564010310340340b00e00a4407403e04503410300e002482411011150810030410001170402800d40307821005400b481901d0f402903142110001c42d12809010640d003001c594120301207101c1e08a54065032140c3c442610303603100c00e40e01d10340a2240302d5030000441c9003004044035005000602003420301ca0b1001424005031a51001200e8142441440502d24040400790091004c8150045e41200c500b0a49624203840c00b804103400d41007400f805094090078074001081c40c9c0341c10320360b48a8428001c2c05144040850a02e050080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 138464352 1250 138463102 138463163
    0x3020d21090914010e01030f060e07060207092702060309150c09090a0905071e0e0903090a0f05010801031709030d0801060207050f0a090b060f0703020102042111040c0c 74
    0x1600304050603e81c142c2a100080c140e0f020f050039407803141e0841d00d40f0700d000012240c0441b0155a0f0308000d240d410000d01800d0003401e800e5016001452400d00014291205440b810718201560b003542480e01d07119100c4003d2040d07040d40c0312500d80c0c0c0c070030740d4107410700100e0100700495007001d008002c400c101100c000c00031242c00b15460f040c99181d405855003115a502fa00400e25440040c09005032104042c030100800f608007800603e4030340304c40310611061404d40341c042c1070f030b84007003201a6985031001405000d0002c4154045020745864002040420103200241c001c09400d8010540000a02c08440e040c1e540581150414540342000400d503070002d1150a0040c024804003142901e020324013001009001010145268100300703032400141981501e0780d500c01c03803c000000d5090441400b51203414041d400050320f840c0ba20440004507107c01405400c181c0c880540c0c05e000031018807130322011b0902652300040d131120002080d03542d807101000180c800d1030107162a49400f0441c3c6000c5003030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 138465602 1250 138464352 138464369
    0xb04150501080d08060910050d08030115021b060a03022b0c05090904020405090c150304030801120312090204060b0c1e06060307140a1505030a0606140403020d2109 72
    0x4a030ba80e02074003a11280c080e1110b500103000c6030007207510761410710581030300511201c2c0080c00c0c02d655400010700c00c0146074412180d070003003c00104100564940b000004103040d00191032460a01d1300c9803407103c00605e101a1182070081100c44d0150300c258143c07181810342c1003100502c400780800304406203104402c000001405d02800c0c0741d1044c41790b01504c5080c180a482d0b03c0c22a11030b642000041d2500900e00c0209125403602c4045130b90f510914080500c10840c40c40e0390300d09142c1401030038690140c214001203446240d03040c001a80c00205840c546040941c0019840001c2c030005021340256845100c0300a004039072480d00322800b050000540032007004803c181070101407890f48031075040340d40c503505030000b0100700700c040c1000540c074500140091004103241c2d03c802501c007011220411100c0010302c00f004200c840c0140b0b02c03908000c1d141a08204800354288244000d540c412400000c1c0610f41e003d80c04c0e010800d03080c0c0c040c401c081c4294012400c41006040041000140e41700f840d12 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 138466852 1250 138465602 138465611
    0x60602060406200904050405161205190807061a060a030b011d1f0c0b0f06090f010b0d0c020106030f031110090b040305090d06060626011508070c0b0415 67
    0x3c074260422401c1503060390f201002403c01c80f4201c1044000d220080c070a603620300074a4600011905025104e074003808500c1c08051403000e040c00d0152400303071034140300d510b8981c0c0d60b4944c8020507070003001c0d0307440558841d03030100fa030909124503c0600c0c000d402006030014004541410400d82580004c10001e0302a690107144051411506007550f4500000e150441c1840038500750641c2003000444550241d418286906001713690740c08400f550442c0e182000c201c4c50818800980741001003207800c40c5450021003419414210351101c81d22030b0071780c0e10049a1f900e002d1a81054001c0d08903d006642000100c0c49007002ca08010b000303003a002100064500070301e03a040c4070606d0544140c410b0190444c43c005041c0e59039640a81d41c0c1e52080ca04260700544400c01140040d425005020142c01940e03110743d251440c8552070a44402e200030300c0c100b0342c4011070040c0240c0e0041d044600c142d05d001d260103c4241c8407481e064a1500c42448050445048036040200b8010000c00814484060000420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 138468102 1250 138466852 138466871
    0x10501030f1a060c030708031510021f150b070c030c0503030f0702060708160c05010f030209010c260304111c020306070305041403040e01030605060307060f0804060609060602060406 80
    0xc04807500202075002c0e51071040c40207038207800c11030060f284002c00b2900312840d000403520b440c00703a500100c410b5840c002c0010340c400141e0812031092840e091a60009140440101000700c1c1001036002c03220441a40d030f80d0a0007468607440304084010111610050303603407400fa013011a44044c440c0002e81d40780380000400100d505002080700e40d08481c6880107410251030350300f0803a40b0b903c0880d050b01e051000307014001c802c00070340d003011101c1c6219111b0001d040e482d02002401282b401c10b2400203051052000c0d03021660818804280c00760300081c240020580c80c00c060b102c0208240702e9031842034010080108008111194811410040300e030103003580e000b0300c081070100d00d10000c000d405401100104030010f0280d0450754015114003203400d109403115078030138a943c10560200301083d248400420a20482e40708594001009502a000c2d0504080c8045c09040e1203414000030440e00d80700042c10b002555000384007600c0c40c4542400790075502c1000954603102a1003e07100c2030328010250 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 138469352 1250 138468102 138468131
    0x30312050f0610050d1b030b12070506040311040f2903030a050415272322090203010f05040210080106120c09080102030c030f0901090506010e130f0b01050103 70
    0xd42c80791030000c00c120310007200d802c01110f40390446817000107101c4d140c4401d0305401903203225800c1880080e640c00105882c60108000440c114040c4001c03079900300d50070a00c82610781d0b10455058942000c0c0c25141d904000021500030401010305242035890164900c5610a1500307003d07000780b500141d24040740f1a040200b5449114148524020441c1000104290704c1c181448042038515810410120960030035030902d0303400b80e8043c4200c05640c0385020721140c10641c01900120705c610308492043c914400204518055000820480c80b01c10640c80440c40707042c1d0480d00c002c0354007070000e1001c84400d01e081c40161030300b524101d11039102c284c03c004d550f41c442c02c1490304a0390165038600140c50800451030051080350300007020040e208030045240c000c24001140030300c440c071001507502e00c1d00107508021a14007070050380032070741040130200108800042032030555852405446607a116841d030340f2040030040000411b084052020402404000301805040354000e880521400c034204400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 138470602 1250 138469352 138469381
    0x7020a1401050912010b13020c0d08190905160b27010c17090604030809030606061c020a050d0f091b081f0603080409050103020301140112140304050a03031205 70
    0x39540080c5050220b400c4510300088520103440709100000742200030980030840124161001c030a040c2d07000202c82c1102441081107442800b0540b070a110030341441c207045081084440e001c91000f039105c40c10b81040c04818450751210340d00b40480308100903503c1495041d280c00c4144021003d401200ac03071140e0203041101e2686580059483c007142c000c066843e41d00b480d01050005034103134401d20100c40b1985034140104055800b6403180d5807144440c40406103003900050045001d8407062200801c08028007909800c074a004c00700240e00c900124030129414060b082100703008509150b000d402240c0a64401500a8007a0766000403c21600035560b13405d098a102d080da40390b103c3c03d122882050480925204000210f2000c0b03021580c3e92211152038001d80c00c2039401e140c0d070f40d0042003140340910640940d81e482841107142980b411b008807a4642c0000000fa02484001107055803030107052046901511004000340c40040d120b09000b42441c0340f502144440500d8031008c02c52081040d4034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 138471852 1250 138470602 138470639
    0x31b0c010504120b090304150206040203010501081528020a03090c06180320060c06010f060201090c050d17040b1b010905030a1d0d030804050610060806040902010c02041107020a 78
    0x1486200500c540e95424680c5400408034401781c0010307c408100d00700060078005c1c05400a50040a003820640101804c6079010f03400003c00b43d00116140c4900121402d10550140207005d01034101c0c64207214000c002080d01a645030f01610004d43c82d000590036512604031746000e00003c020450f143c0700c0545400300c2d52a080d401c0501c610f41c0810014042114581038044c81c80340c80849070507046c012429613004a102c0c285035070010001071040068081d59800105601d1009100c21803a540720040c444502e4007425000340c060b10100c1040c0841d9074500b10002d0344e0101c1325a501c035984c8209410980002900400010352003a0305401c1100500a030400e582d00903024502d0a040510140c8000802d404074943c03951842201d90001c0d07440e0f003042c191580c003e448402e00e034078062070b0103410f1a90041c4070714100e0011010500c04154441c4000b0303440f02044d02d0002da000350600041e00c0000c09004025402401d201642c5410aa01d00180001c98030071b03a03c01180b1074803100c011100c0c100c0c41a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 138473102 1250 138471852 138471869
    0xc060c110f0105040b160b0103260304021e010e030d1806030b0913031704060504022106360714010f141c020d0c0f1106061011031b0c010504 62
    0x900c0010502e4000701b040240280301c51003600300c260b40301d034240c900c260f200395030005880c01030140c4142c00c0300000000c440030907101461072425900041c19201c0c1004200700d84009182c2e14170381c59001e446900f00548000301255200f003d0042c0050103641110740e4010034a44c141c5000560501900896582810040031041190745501d0383c04205128410194200596603605a45504410440d6400b683c09031201042601d03240c01440b0000301a814007000000c000c0c0c03500600010302244294012a004a40c16240c13078400603d40c50000d80b88900e2252103212559040f524480021600111442c031549009c0c2201135500548001003040001008651519054400140044010542100d251203011000742e818a03c03801243c0244d0341204165903681c1160b458507400080d001207d28551a05508220701d4002107901c41c80080c01403401850820f14216881c0d0040212600c1d0880c1c140481707880301485e030001c844807040b84003045118002c60403114003551080c0103d07020381d01c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 138474352 1250 138473102 138473107
    0x160f11010207030201120c050906360d02012d03050402030c01031118030a0c06030911040b030307061104050909030d0c050a05250c0b070b010e161b0c060c110f0105 72
    0x300084c6e000707000c900d0696001c10000b0000c111407683c48a0103441d00581c1840c2c2c401e0381c10b07030088125200c001802403048103803000c280c224003140e581ca1450f00c1950f03420718001c4506c00e911160150011100c1d000a0300c4503c04210310503005a040d40000e129a008504a400b48440710f80154200d03410300da041d06615404002c1101c08031200742d00001c0c01100075048440c1d0340801d0f04c0f4907980400d04d4000e140001d4880d6410010310000e0b2548210f0300001b190704105409490000a07503d00c074002c801032200f512800044491040d12003900c00900c40542004001d28000c448035480380d11802807072041a10308242c2c0440c072407044041d9220040c090b117560345042808501c80c40941900060b0024003005031070ba075000039a84100000c01884248001a01c0b031030701d46000d520b81e120580215540d600400d0420200c1e0100b0441c21450b0200c9040c200c2d040a030341165905142a500c101400c82c142034440011000e0b80591070451440c01580441c46020300c039020080f001400b01109c030b0011f8011f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 138475602 1250 138474352 138474377
    0x2070201080127050f0702061b030a0b1804050304030201120b0a060e0301020c010f0b010905010201150e061c03080610081306110c12040f050907090b030606160f11010207030201 78
    0x20040041c40f800b01034549242c503504441190140e40c000c42d40c1401620082052001040d0104502c0340c220880f0250041001008610462540002051980840d44544180d545c40d158244c01d02c0400041002c01002840c250030100d07540e038000d100c124001420b00e001c01d101da8141c0d100c0c81c014020028403a052041c500b0000701c648070400341949030326541c01c1004024455092242803a0940c2102020406001750341c000b50080040750f00040c15039040031702c0e60748a100040019810f130340f0300c0c07031881b101c42e102c80c4081107100b4000c452100204a08450380014180c01c04d000354402c64080340c0c20068005900702c00c4404403030030b4403204401d07001c07030390590001070b010780010540c1c6600d661081d0074040d1010406241c24400030340e101c00a20006002c0c4050501880340401401c026143d00495052a0f4001045418540b05207818803201102141c0545d5551040f1041342c1118404200e0603000fa017401420721000c030030112588030034490400c42c0780d4004940c2e401101d405071160301b03d0304074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 138476852 1250 138475602 138475619
    0xe1e150907200f070b0c03030c071703040b01091104061b151d0709050601120902010507020a03060b130b0f040f06030f0305040303020c030c2d041a04050a020702010801 74
    0x9488641482409004101c0140c80b107001481648008001004a5120441220308041e126004901d00f5401042841c1e010341e400012642c019030000500343e178500013400e204148540001d284900224000f007400140498050030505940c01000e080182d00c00c45c9030003404500c80c51050748041447c0e021503004803e074011800d0115805900c00d480b000113810700c58411a13110007048034143c0e544c18409a0490000c00c00180a803844160801180c03c0210001c1c0071802c0071a000c041301601d0f80030420445e4410b00c19104a554060802e540c0c00d40c403441c024000c2e080300a10b80b80507070000e543c114990074803401607100300080984078204950004007484003900c007161100030306644425000000400014203801130f01d00940d9400d840c1d90643c80c0007424220403d8050b442940320556030b00603591440c149044100918420301d6104504207c0c4040c0c440c00b000c80c80b90b0041c544603071b01c880290800c1d4001807040c802c807030401240d91201d030321408902403000064000b4003924010300c101503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 138478102 1250 138476852 138476869
    0x12010f06030501150e101106011716050f06030a1b030605030f0601030809010c060b1002030c10150b0304140a0c05030f0a1127040c0e090a030c08030a060f0e1e15 71
    0x4600346000c0050501d84c81c1424900902a07200708981d000c14102c0641c94ad5050280e41e210595004240301c04078640b10009211180518076180f041c5400400b0401c0f808585d4000744c248803814041002c000540c40703001d00103180b544912400303030140c18a03070700c50804040756540c107076544003a046041c5449030004603180c5010701d03800c864182c0d40740d0203500703150303a1140c003007000d8881640115079035419201e4807420a502c030450341c80b680f803c0c6040e94264031841c01400f01a20900325400780c0b40c0da00c90034030a819825102c1d4000d0a80030b090188000d11161074104d801340c03203041e411200e903061400c0116a80c1e04148001600003195242d54484034609403004c0c0000e591012a102d005084c05080040c44200c2543c00b00c40c003c0410a042280300d8400b40e0480e401009040500001803a40d2806412058820001041c1140000c00100d007210141c1c4420060028500d00d0b03420141c0381c000030510014180c58015461001d40708100006803140c40043c45401c5088012016881c19402e010303151 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 138479352 1250 138478102 138478129
    0x1606020f06151801090906110a080a090602040e090703030f020c010e0f0a03301e0c02040e0a1a16021011070f0f02090a05090a020904050312010f06030501150e 70
    0x10007000f0b40c41552550040c0240c0605140d21000032120000d02c0c2100031a54240c44c0c90507110f03c184141d079010303074200c04410743c4401e00c10750104070f45402d413400c40000d00ca940c2001c40c08400c0303075042c0303d076100700015800c1c2520311989901e4190045010141d80c1c0342c2007a00e5042c0080c0140c44a4119820308904060803072502500c0c0c80b40c85071701d950310f0000d104c48007400c1c0c0e0781600d0301c0750f11031340c2c11910341c8080e0b604a6514180310320703685520100d003644d03100f290a4030705c144078218031020215140da621803a20310030390700e003912a034550616181304282d0080c494001d5000038000401d403080050a0064000e0303106400030b10040346400032510107041c0d05030368800055414045100820380e64030200c50024443d40c41e980180c0780c24810000d4892001c1d103043c6c0c445107880c6c10090f40010010f030910402d82c0448242d01ea95849203000751441c840c441a1795412840c56000240400c03200004200340c0304551030900490782c0f80c016018000c68031003580c0c0002105c0d0314842c031f501d0600c120340e1b9500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 138480602 1250 138479352 138479359
    0x316020105130305150709060903081b120406110c0a1d1005030a110907030504030e12010e030a050901020d05030613020f130806220c0b0c1501081606020f0615 70
    0xb02e0b603d8584a042c001c511382c80004c0140c0c04800c224104d640140018084c4c000c50820340d003050304603100c4c0c4400d40100c0c14481d801106d5800740500030a020003000c1e140710203d85049660350744641004100010203040c5003a030380314600039640d00346001c030141015070f0b0074450100710041d900d00085204d03003c080d00030300040940c03000206007920700f800070551140c0520050140446a6805d0050202005005008140c0350070180000280c1c040e101c001c100300210b4040301c44001c00c07030505006203140501d03000700340701c0003a450f402c880c0c0240103028259001d800333903125003981d0601a1890700c02119459444125640c107000f10304030941c00707024820101e00b007523030501c440100380000600c6aa000802c80b58030200c100000b080701d407010302c07803005040300041480020035a903a0f590000709010320821440d003c40c502c810703204208100c11030000c00d0490018203581d0380c2200350b01d07454089143c0c3d138203180414010640714000218000886081001004030b5a990554200e001c40d2a044140c3e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 138481852 1250 138480602 138480637
    0x2120a0c0c060c09030209090d12020c010f14060315040b07120e0d11010e030f070b06151801030c05030705090f03100606082a0301210807050d020f0316020105 70
    0xc01e01903c1125000101c1c0c3c2c8038080e100d07086004110280800800c2d1210316801000421400d580c00300e484000c48560308009a154000b9124060140c20744c81510703030f106450548600d0810105031a06406403d00303600340c8508690010700c0c00d0b4003200899019000c0540e65020840300c1c2d204503c40e40d1042c0350b05500096403031080500d42d082c100032003110400a00d0400c52a01554003e01c103800500603c88010f6190120380d41180102d0b01aa0b00e01820521401000604030389070080c00c0344000c00308980d0503503145281c140c542c401c100c4c4240f100780060700c0e00003c11492400341d0100c80c0140d086446640c2420000010001007148038000181c00d8000d0326491040380b000c601601010780380c10b85694615140074080c0c5564824600108050b00c00e00d854001100300300e0764101c90643e0507541c1e048282603180707014171034641c20740b0200802c00381001585105203c5c0109406112240c9542a501d245140a005641d00d000f150280d64580200148110040d030043c4010240004260210309 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 138483102 1250 138481852 138481877
    0x80408091807020106150f031505030f1605090c040b07020a050907020714090f24060d020901030b0a05030c0f03160609030201080109020408070b0304061503121202120a0c 75
    0x1e51404214005500200c010780a01107580d4080c002c00014118062880e0142040302c00000c01d51030200001c0801d0694462046a50020841100d03001c1c0c94090304031092110346040059a03201003000310100d03c00c0a08002c10b1500c0c1800038180100051410b60303007424182100c010480d030000300b040780d0003104008000350985a800b90248a18171940180412a14100a04400085150300340d881950300804121040c181070035075903046030030071618840c102e07010105d9558524200c009250b004d000440c28402c0d01415400070b103403404080c3c1e800e0000c0010181440841e42c0c0e01d01070194180c00c074000003610b070300300742180e24090300009040359400070a07144800205011a000f010000d000b220b000c3c0103650304001a5801042407000442ca854980200603444d005c003030084117000d0742c1c000041001d110254001d460a54414152103498035034038585150030f0b0922201e10008a2002c3c0b00d20001f920003403082c1c83c001c0100107145501565000c40312402040041c1840003409050120700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 138484352 1250 138483102 138483109
    0xf1c060303081006020120091c08190318080c030706061404052211010c02190810060f03230613020405180a0b040311030f040f0b040b0a08040809 64
    0x24011802a10b4560303a60420034020010009241c01070701c15a030520b1944038601c2801d041060701c01c2031020010342c854882e4030000700c4d200e541d051208550841d840300c01d028440d5900c01051300400f100d50940c012101c590082c3c003a160815107111250b0b03060704102000c52195801040319019400640345130455941c0e4a808652054020040c8484042d44015040c02d240c40350a0704895480003064000c1904100140c1080000500821400c0218038207003603640201e0030b03c03240c158000c00c8031052140c084218800d0aa06100f00c081c2c2d0310a8141c44807002c0c500388901030945d824000c08042075070441e10369a819820001400219400000001c2c904140038060700340a40c860b40003040080d410b5004003c161100a40400d0210031314034030240824000042c0100029400f0380701c40721660752400c1c01c0e1801003091710060194040066031400e4040c00400074410354807100d1002e1000e64440c118044140114040c4080303d4004100d900c844a00070000551300512811143d0b14001c0001d020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 138485602 1250 138484352 138484361
    0x10510110115030302010605120118080d020708070605040611160311120a09080c0a1412120331121b050a060603060b03010e060a090c1d07140f0f1c 65
    0x113138010303559124180110328001a02c5140b4400c0340000f8000340482006040d6109101310009000060010f2080700300c0d080754040d502100c0d0041d035030544410703850800002400301250115201c5d803074403840b0103403034040d8410365581c40181c41c2009070040311079400340c4015050181c13904043c401c8806800301240042e0042001a6242d910003040524001540345000942e41b662482004e203007405011101c5000000c8404200480c0c0c0c0042c222a0301c85e100f4245507014000b009500000410230155040c04103510180d607200321004d50081c01c1007001001e5174031030000f0051a2000c1e406c0400c0c0358a02c10b00804004155602e0005020000d5135199442e02c00c40181c1110450b4a078201041030282501c90f04545c00c0701076000344882d010f140521511940001d000b0010143d54094213400d000d40e540082d009801051410102e2540c0c00c010b005445a04880d1000010020b91010440082c85030695003900c920343e110314280809900344003015040018100429100742000c01c5010209009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 138486852 1250 138485602 138485609
    0xc101701120c0602030f0d020f0702090c03180a0206090f0310020c07060305010918020114130e041101020a1a0c1c050103020a0b041d10180b04050708010510110115 72
    0xa9241030300c2410314009002c02015809082990014080e08113000042c4080303c55107081c00c440180e42e01e6075040003414900071108060b400c0004d0324100048115000e00540c0644241da080c0b583c00e10146804a68640202000075042007003440a880181002822001481c00c000c4c1a240741c80340100c00041282c00243c0451050360201c3c008006840d014400c50b805800c4c100c03814042000078980e162150b0004000080c1044003000f2600010181c200c1070301c040405012242500b19a5200501c040c000141d6090350709102441007002c440d800000c40300e080315806100c42806203481941c040c41017000038200760039620108450003054491240301c000c2c1d101e521800040310750440c01444404074440c2c100401da40c7d02000b05101b00402a00301c5903010364002c0191001c0d130b50f5000070603801005035112a248080d80110342c40102e0098000441003a01078034104141d55528034100c030b89080a00c543c1c0d801001801144541038450040c00740000740d000d0010a949028121031000300c20390790f1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 138488102 1250 138486852 138486869
    0x100905030a120e09040b0712060f0e040c0506070b0c03090a060e060712050705180303090337030c020f0414010f0501030509030307020309120a020402031e06040e0c101701 75
    0x1103800b240c440d041035601c031024005440d5804140b61607918081b0142000d0024028411000050b006081c030b560800d00c080e090b22103060b07100990b202c1d81d00a0034a010313501218074984020021070349043c000c090f52185904503814066a840b990280c50166001503c82042e41c016201c0e1100466440c1c003070150700d550362400401341807500d05070040070000f014403510050f5043c5400d1210041d07204058a80d050500c0012500d403011040002c1d03d54441c1c003060340d8050107285807260701c1406d1892080c200f0201183e1624a0031407054104140e0700301484000c0202d07103c20600805400d00c100d51b00c0444001070000a510303003e034800b0400c0b0f40c209a026041e50b01c1400828402564103028468100c03803040001d44c1507040205002e5120b00500703040ca8044e00c000c0050500c030100800509a44e2900940300b15034074240741c004881800d48101e0030000360b20f41a00401c001e81094407401840c2080c070006401e0b11642c0204021111f130340020040104066002408042c142425141d4024034032032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 138489208 1106 138488102 138488123
    0x10917070302030a03031e02270d051005070314060d080702010203121003020f030d080114150f0a02190b0c030a0f0c02070618060905100905030a 64
    0xc0c1d001950512030500b401d0249034156019418120350007079818030040b044100c120503842051058025a81e2413003d040c1c0d25100c000548807005801842e0f03130b141400c7d90300e8942ca46110b082c2d200c10070740da580d0280080c140d007611600d40c030000d401c0411019460100000380b8801c3c0d136000c01900c02e11002840004680c070038812210a0045185120181d091840b8000c483c8030301400224054050360a80c14024500000d80200c440c4543c0e58141003031382441c46020041c0d4803000c0c0389421080602d00e100c1d41d0038282d030103001c1000000700c19949031110800000d00d000a001140c2c40e07804401048480483c03140f020140c1c0c04196540e03501d60344d13180c02004000030840304001c21059807403c0900e1808a501280840403601280c3da114544a10000304030701054013441480302042e56090100214186440c004981c050a4100002c040c1d0ba0382c0040390824191000031200041d20 = true := by decide +kernel

theorem cover : BRFrame.Cov 138309352 138489208 := by
  have h0 := BRFrame.cov_init 138309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 138309352 ≤ n) (h2 : n < 138489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
