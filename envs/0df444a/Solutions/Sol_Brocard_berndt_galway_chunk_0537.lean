-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0537
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:19:20.33579+00:00
-- url     : https://prove2.me/submissions/00b2eac5-4e0a-4edb-bfe8-38d8e15ebcad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 96402877 ≤ n < 96582734 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 96404127 1250 96402877 96402881
    0x103140307080f120703292115070e0f0904170423040902180907030c060f08100503060601050d060302060d0203070f0207080615010c06060b0414010c05030306150706 73
    0x40703c0d407100340f0b40115080003003000035102107911010074903003008100c680050034a560a0712005d0000b180d4600c0d4007080a03038840f02d8030047e0504200c003c40764110005070950b03944a001030086a0000400c0010441c0755105000c0e06e080103030018032603104103003040e003001036108010b8001c41d101080d4611012504145001901c002d1081600300d44c2038010001024090030900c4441c54866444c052482005940300c001c0f100f01e0781c10b810f401c600036a4411940ca8174000d21504040d2011b54140c03000610f06901c0340d225000c000c180c0d81d07007090a440d552816526000c40d402150341c50703005000095a5944558064601c05112240c0855840d0b52074000c12020b60042882e10822038000080050303050700a0011100c40026100401d00180791084032a150880601085a1340200c00100c1c4035076840303030b1211001150031005c10003d055544920030130550091150b21041e60301d481c3e4101e241d40c05516540038003130b0808099441c0d507580c0c000b0401c032640c450b005070413010030500022001ca2014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 96405377 1250 96404127 96404137
    0x203150a022701020111030c030f2205030304140a050a1b050a090b030d050c0a0b0402040209100806010f02030403030e040203090f06010306050106201c020c03120d0501061403010314030708 83
    0x5002c44403203005507000a007510003400814000d45070400510a110301c02c4011a0361029031202c2c1c90701144c50f400c40401807032070985501482602c42200c03407018404080001c0d03000d1845a030b00c041c03c00015070790054a0302c00405020b0b000384c00c0540e031400880d030300c00c541c148840103061003507071195242c50001e00000c015400044903550307540d91044c440d04040002d030609803110b091141c24a040210701a60b540c000c4c10009140059010200701191100c1d0162842c8143c005c0a02a071001c84ca8002010501c045030703014000303240d00b1000c2301d1060000c806c83e003e894050780c5141070181e0030f101b84006075001030040381691040790025002c0c03500c14403400340654801d2001281d10f51411100402c41040f070310742c0b41d0605005032010340140a000071220100806944000807948082e0340507814100360f2207011390140a0710460403842109e440040080c1c2694000402860340c8a0030115006103040c0a20142c0705010001480440d24001c60b0300314102c0c0840449241035039580c0c50740496006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 96406627 1250 96405377 96405427
    0x1e020106031a0405030406110a0204050a0c08010e0c041703070b0405030415090f180605060310080105130209130c09020a05180405071209170f0307020f06040203150a02 74
    0x2680e1001c0c41005030704000d031482c100858098911034101920340c00e80380d1180744105c100b408840300c284146140c00b88000118150003c20411043c54043c15050241c00c0c0141c1d51400254024004141c180f03026010354080e03d440f04000e4246800c0005d03080000410302e119940520051104100055046011034411480791016503200c504e003d0403400000740c15540d080034000b98020910010305403c960a041b030311014120304071420740b80003031300050000341c100c20b0b000800003080240001118103a0320455031440300070052680c945c44049000c07240520025400064240490040d400e0070342e16602850164504417140c40d51900c2120882e40102ca0040c0070402c0814810740d0f02c0880601031915a000f40c905011a2404140c02071044010105100c0120342d40d5400b0700920100c41c6000000c100800d55007941c6103002511080c05400c1128158018490031201401203000490360074051540600100005910229140160742005052050540d0309003c480c0c5003015001c86078010a030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 96407877 1250 96406627 96406631
    0x306040b150f210d0503010303050304030818070806070f050403020604050d140307111503100b2b090c050a060e011b061803030606050c250f0f090605010f020307030f1e0201 76
    0x110f004240d0600c1c240118502c14002c0c24001040840c0e0000c0459900a501d0f10700b282055030344030280e0250403200c1c031454481c1c3c4641078000c55401d80c0007c055000d9403142d183c401e03181c60b400c44115050711450000030740186062104001a050024007400d85038859801d9108035280d403418545190081d040603100020030901201c00d40c00d00d500300920311001995080c0c0b45240096941000110368800c0d000d200c800007402c402d4a1603905140310481e58049240e662201c5200741c08001741800000564002341110400120f40c50102c40850841d4069201c4002c006662001507a481c003070810041c208031041b4202d01e000428501c07403c4052412101e90500110b45420010700316206038202c41d0502c142000000c030020800907000e074412990020220400d00c1d074808802d04d204866001d228034602c5e1500118101418030706450075500107180801000c0c1e5150011030340f40200d10345801c0940c208201040110340326061040044040381441c0c80784044c0c0c403d60300e68000f000100e04005175 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 96409127 1250 96407877 96407929
    0x9090302030909090624090412051603080615090a0605070809060a05070303150f0b0c03070605010f0303030c021b0f0a030c0603020904061a0f0307090b040f03030206060306040b150f 80
    0xc0c01c101c1604148074024103840e0b0145503164041001803602410181c6046040040400b4841c8030300c0440f2f001d11064400000380d6141403801420710360040e103001b88100c102001c0c0c112001001c0081e00c1d4a60b03030042c249111036203400d100f0707990365118dc0010341c0d541104201f0120561511002840581c0342955038036076031440c5040040481d541001ca03c42000c401c60001c00c440c190585400003628640c0510982d54111004540d01d50310030604024081d07410301c0b00002d20791001c41d07009012a402a1814030819106020483e201d208100c90500d120070500c2d140c071018100070042d01c48091000c0c3c02c00495039100e823900907005555070300003400a5000546080c0380c1c02e15000d00002880d900c500488940c84040c416400c9011b0721003a41d81081c40800010416485400c00748000d0a01c45c403540c3d607640c1c031b66585851036051400194054031840303022a030107040002d1060701c03568100e0300070059038543c10f6152141d44030318000d560f40608800c0c51321590703548645a101d54107640d440e00040348 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 96410377 1250 96409127 96409141
    0x50d09150506120709020a0c0b0f0403090b040e07030b0d0203060907090b04020412020103020a120507090302011e120b040b0307090609060e0f0f041406040f1407060207090903020309090906 83
    0x25580042c0100d01580107040500f02103800040c203003054800340c05015807035030106007040320340d54541c2c000039100070600740c00d022210912442c07041c002c0c0e000c2c1d51007030201a1100c0701001d0912540c800d41034010035807400103469503c1380c0c1c8000f51a54005040e003125003850340009242c0f090a0310300725400d4001240401c00c4640d03510905580b01c0c0180c1d0291f0030545485402c1c82c0c40c000e10003002e4107068000800a80036842401380641221807188204843e00381650000d05000440c0022808038015406407140e00f40c0e18a58605483c045682e1410860f0100008402030305903010070a40080e1950507030541a034044c0b008a0141c40c5802d4006440c0d8175014008068809a82c03210701e074100c0304014040543c00d01780c0030030b510940d98401030303c02c0e443e00d241c0685c200640009050b10b600422040c04104400041c2032020280225014955080c10780d96054541c1035a105050150b400300c80100b000041c1500608002402401980c2c1080c82010204152207030403100011a50050780412500c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 96411627 1250 96410377 96410381
    0x5040b1503090c0109140109031209050a0602060405010c03050f060d06060b0c03190801080a0311070302040608030903060604150528030f170a050405041503021f02010e0d1e050d0915 80
    0x6c1c03100c040c6400e14840140d0000c1c00c840da0901024200b083d19801d161241ca000c5c000c60401403001400b0000c000c3d41e2000001d4031250259800c64140d42000d801040c010711a004090084d41159001c52058543c041000064410203100320b4407070b5141c0b03100182003507400700600003c00c01000910f0b80c80c1a00b403d140c5400507140c1e03c91061121042c0140708010b030024030191015458109511206a0210f03614600041030788000e62090070480c001c6080c0b44044080c0c240400140c045401c20340b1203500f0802a1211005842c3c40b080380c22a04102e2850180002418884001c280c201389510b000d040020003203643e00143c40c01c4444144a0080103106a5400a8004200382203070400b101c0c003d005100748281d1042c1407050761114100044043d10345070600083d503004000206d280c50403000700d0718100400e01d100d0090752800354685005440403c002c00444c0007030380c03009203424104640c441300026001010303040200c03d000da0f05103d1000d100e846a45805450300307210003c600361401007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 96412877 1250 96411627 96411629
    0x102010b090106031e0c0905060706060803040f0302040e07030308130f0f08041a040f050d03050903010f150e0112020913050601030605040b1315020904020d02030412022505040b1503090c0109 84
    0x7101c46c038003501107200b90b07401001c5600340d450480c0e00913514441428036201078000781e000030801d0300000070000303a0010388140240c100c2c0d1080e5001d01640450740b81540e180c2c422132102401095500c800941d00d2030503822101c940603c694200e070001810340d01c031040200a00708089039030040000323050002c070300700b110b04808000101c081c082c48c240c180b0803950440070051140d140650803c2c003a100c1010f0062090b01d00b40d41e0050020000319600c030402c840078090500030440c008090080204020394034100c0d4a05a603000748445040746c807198280080e0920040c40000411440c1e0755160000d6402d0000ca8000c46c02994027094038141790905060540024103500d040801d03414000c0000ba4807140030b00c9495405110041e00c40300803d0100d00a0701c41e80958150180c4000100300401204502160f0079599076800c54030481262003918498808200121980b4401da1401700201c0c60250441042d1940103024088491710403200c40c0700ca504159600d800f940c001d42442c003450750b40000850 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 96414127 1250 96412877 96412931
    0x12d03200a111b10090b0c0106060905010c0209150a1a0316030c020a02091b0a020102040810270f02150901020c0a05150c070b13061b1e020102010b09010603 69
    0x11101c0f0740a02d4003c015214180e40b4080c50542e649219024003403100b00f0018680040b0386545c030306055208a000b0507040c0144008550b08110119407540b00b2602d0921a0381e01600304d2001c0d850b18005481c2a000750035450368010400d160114180540d0455010a110303407496041c2c036810b02d001d880007111580f2800c101091318000100d042664001402105d1f1030701503400c18030075124401d00c00d44080c01d0180344800847c00184000456a05600a20444003485d0648030080c080340d00c0d00b825903140a82420740100d04d0306890310040c901c2c0303403406600c0b442441d050690b60a2a404030f03100b40504001e00c5d2040c1404074514515580501221082c09030484181c80034504203000112010942c1c41c40e807103030420102d4841c050100030400340d4013400c00c20304190b4580562a407440040c0149004660000b0b10359011190311740020b540e050a000d5111440e0b640d50710780c0500d8032510b10125042030f4115074072121703a8a07940e100e034081103010305980c4c6d40100704c01c3c04166841d1030440d001d440306 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 96415377 1250 96414127 96414133
    0x9050102070c0b0d0501080c06090609191e090507050304020111010f050103030806100801150c02040603050303180709020a050703080a0b040501260309060304060506010903080408010218012d03200a11 88
    0x1040641c1d81b07030070842b400ba003006c4804503115015403010603549810464244c20424040c00c0126140c0c814006003500501c002d11406070960b22000114242ca01c1910a0000b01c2d105001150040d809850f40030300f500c898a00000c0c846210720880000d64000303034415000f040c1c003602804103d0030a0040080c1040d0320f400c2414480d45400c0c4e50501c0ea07684402c280c030401c217180302020300315500c80c3c100d480210b03048001c40740c0700e0130070740061030101a411030500e09030700c00c0810007e5200014000c0e18502150384d01c07081d060101945050700c4040c80141854603d03580c81500038101c1d5101d118060184c1018145900b00d5170601e41c2080d8205444030702c0c00b08560062021070b040303603074420850358000e501283c04200c40e1215401650026100e8100403d058800302d0049140d040560261242481e8036203240d1445007003500559040350b41504c441040100b0a199142c074584007426140696400e01e8001340d51642600603041c413410086030058500c80004510095039440040c48640314065405 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 96416627 1250 96415377 96415393
    0xe01030c0804050d080603120304080307031808091011010f0902010206010f050d0f061e02030f06060301030f060b060f0403051b120604030e010513080a0b09030a0f0309050102070c0b0d050108 84
    0x500f9139120000f41e99101000720f6080000c0c15914240195a6407000442280e9280d00b4640303400074083c3c00880b00500000d180803190300c0500d00074900c0380805074000112516100442051041c0c00c200f80304490305201c42c100d25005001003d00c520b001d0301d80380c6e9000040c00304180c0700090602e081a071001140c1000d4400521031651070361481440c1950148000c9801042d52620350060034a03c000360000340742c5006051841c06498008601c5a800291804030540d901010028140020700001c2c1c403d8911100060001d9100c0c2d0107030007610341c010a25400c082c03103d500c2d106030790300c02d0300202d90a80001d01c80e030540340b415005101e0301950480e403903644451818203c1c0c2d0f503000010009810004220400d0b00203074020001c03a2448804440384000084d250514242c0e280a2888211140814500029496040802a00c0c0031301003a9a44070071911041a08801a01c0d0381201680c04e0b55003000400006500c1c43e565100404010500a485043d000b101e0b030102e400503170050910b0341002071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 96417877 1250 96416627 96416633
    0x91a06010201140106050a05070c080115082103190e0f011d010e0c01050a0909360203030301150509120c030615030c040c030b0901141e0d1101110601060e01030c0804 73
    0x41607c400340c3c0d8034074010307407038107218205540d0040ca640d02440c41c5501c1c000d020303112001f2600c4204141c4910204981da4131041c1c1d000d056212031500c6000481400500c0891606a140f401c0c00d0345c070300036241c000b04e0030403580c0c2082800c141695030322501c0c6039510601d40740a41c16810400794140000e1000b0045622000040741e1100f00343e25803141000000200d04890601410742c0401502c904041003182c00300000300d1403004101c0540080c42844c1c03040e442c207c6604203401e95848558090061030842e4070f0000b55a04200d20200c0718410b00405205e402416218201803c10700e1004100a0640c4440f07a414182007101c068642c00010040300c50306101a1400508000074104c03c0d0303400203840d0504c2030118020242031b41e809500c42c83d0080006801c0328034500a0070000c0301102e1020084510320016000740d60b940761980d07000b030015003030307140401e22052000011900604004140180700c0c0c0141d4203100d004d030000e0b4085098103003001d1441d41c0c944105003008005040895a0703040070f032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 96419127 1250 96417877 96417887
    0x80610080105090601051c09030918020a0c0b0a02070501050a0213050307120b0a020f130311010c150509030c07090501080613080909100b0a0c060b040203060a030b060103091a06010201140106 84
    0x401a40c14000d0016401e1200491f185404221a0b9101c200300110806854010005122846064003000e401895050031f2443c5108441098256486c2d200d81c000740c41e40c0f4864640303802410780ca0116400d214100205038207010b401d1142c00a0720005a48200f0200359400c0807010f904654001d40c8641c105021074401e10a64000068100565144907541c444411001e07224203811078034440808a245042880c03408030b03401c02d40344200405040242d8030801100c0500c0307401c002400940c0c1788060f00002900c240d121320742004091081c0d80c40c0c00010114146058410782c0001e003503950300d40041040c48420700445030003d1100d461001180f0311902c90f44054010400b903030348182e00e400c0c0450000c0018451290080000204054442c04800406004610400341c03c2d6000780c241940340c04c0c240b4152003101e10808000b40f104810509540342c03011b03588802003529040c10390350301d164004106140e102900c1e183c0125683c1400d464450002402d480381607102c940741010070001881456002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 96420377 1250 96419127 96419131
    0xa020607080a1506021005060316120507121407060806100e0f120312010f03030801030b04080c01020d1e090209180304170601030c060503040507030303020c0a0b0708061008010509 79
    0x524041e041074071140e0a48004000703031100194068142040002d145401244aa07020510000c0800c41942c5060506496400801900c90448114541804081803440e080c0703400364000c200306e5800d0b50b22200000340c1403e200a00740d40d6502440428981004100000e2000d00300a01d88600641001404901d01d06220a07408092000f500c4506282ea11920000c0d00480382c01080300320150000c41a068aaa22190085019000d104004100003200c04001c3c012a6410342d60b240881e860368440200e68400540301f1240324508002c000400b01c42400900f5901286078800502c92201c000c44102100e100c2c140c01a1582c00c012410b805a82c5481603568400c00004d829007000c5001000706013184900d81001c0700e050b602000300002a8000580c1c903050b031b0302c203101c07080d80d43d80c4807041030354580012900180164007024090001a103e50041c1c0f0301c125403a411615480a20356400044200854071600002c03000c0c400c0181900c3e1424003104400342508080a1550400d1f01044c03884c080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 96421627 1250 96420377 96420391
    0x1e050909070c0b0a0f0906090311010608030306090703150320010905010e03100b01050c060405010b0117042109090e0d080105100509040c17070c06050117031c060504090f06110a0206 80
    0x1e901d00d00405c81d107041d0010f03142607901800412080d03205280141c00c9045c1c2030100b008541c41c00d80082070202000040360702942c00141403001543c0c4072178003203000d0000035624000c80c40744031200100140c5014030352000f442c200442e0031001ca00c1c2030001808515150b000341e040140f030842a00c440d0314003080305161010a0750020400091400040e0794910512a400003071740b040c00100030a208040d400708091482c00d982303007170503626103100d05d8880c0c102c00e41c1c02400041030b8010310300070320b403004150a1401200742410900181e4842050381100c1400701142d621703401420000d14010b42c4400c146003d03000c1115903844232841100003c200740035aa480c01e000d03d84e1160034003000390062401c0500003404a0b0740144030300c0d2108009050004c50707081202c00905190004c40c1d48000d00310304031302c4c40711254019400c090500e1200c500000001c402c003401182e41e40800309558035603014016266004030032a000c645190310700b82040300e64800c00b0700035128052012034990795000c00c0013074000071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 96422877 1250 96421627 96421631
    0x1207030b01031112151509030c030f07060e2e0806010f0504180212180c03070e0c0318030307050c150c0a0804050708030a030506031b0108010b07031e050909070c0b0a 73
    0x40c4040b250f103074244002c2017241d0301501c103103040301c440c10405008260744107054080d0b0f060045d40ca403c0c503503079131449008040c950b0000103052142303e215003072043e03903160b000740150f04006819007903a80e1050202c586500c102c40020203005965004007000c1d81048081c40c008031440e1212000034154000c500640340003402d8910891081d0019070190307620b18140360409282402d000c900940c3c00e05501009243c1d41c040d1006050142ca0007050a9044a0a52140c052a0f0b40c40441c071515592000b000c110000c4c0c00510800310030390301040078500c1040035031038232660b0b005500c00003864251041d0856410f004900c080000e100da4050940d0740d0b140b42e604212f1540c2c0c586103403d038101921504044018400400c00b00c1c1c460b03516400840c090f0b40283c0682e110400450f04c5095020011001d0b28041034840004003c2640e43d8401422a01c0c000c0c6854400d20461180000540045900290000d01d0219840403285880000b15400282170f0500900001d00799544d00281d2500400503d049a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 96424127 1250 96422877 96422881
    0x1182003010b03010c020c010906090f0b2104110109080604050709050402030a0b070804020405010909020109030b070e190503070f08060406020d09020907080109050a140f040f081207030b01031112 86
    0x10310250054880070400800901c81101804002075540110f8013000b0300144c500c01000601c0c90013040c07490161860b80d160540d0003402c2c001c0b030280591203181213104030a1003884040b481d0400400d40703405a0711595013801d17401e14800c00181207003110b13001025240c1040f420b0000003840007a64030206c654001d0f011a07541e40f41d000080c10440c00581c0541000e591404204820b5804540540b15070700c211810011640c0310603e41c4103e8503c00301c02808240c6070314003031010403d0300d00c0c0203500400b00d1900f000c0b1080d0400108941c007504181c1180900342240c014000c03071405000f0400a041c401e05213140c1203281c0703540b1035502c1201601c042d14035a40003400358031079540c1ea0421900280c0140182d419130804a0000b400d1150901c10310345100d10f80320100d507881115000301005803200f600c6a200c035448800c902c607080d060183c0101c0c0c3c0c0380300c1d00e058940000c1500004c2c0035a0340585448d006207240041313001d4266201d1841e1541014a04001030301001d042d07106650040300c0d0040340024030303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 96425377 1250 96424127 96424129
    0x1021b03070810141308121801090501060314010c0206191118031b0105120c0d05160f080727050301050a0e0c0a03080334050a02011820 60
    0x3184098209600c0c500a0b0001903008611503004880300d920355209010f1385998412141c05140d04001c4020886001086010103020342c41d000c4503007001129407051114058888000d084401c60031080321540d4455030100107020020007000c1c00945500c0083c4164410107034000d440c0c40700200060003044151901859010050348442c81c2111004040756440c134858400c917034141c00d5150a01d104c0d100d80700208020486460b4021819071068542074100740200e00303107a00e803107001009072008a030240900e4a003041c160290138050403445080601c00701d42a80014809485030003608244940442441001c0d44c0c0702c0221900c41c90b14252007403d460420050303046103200c6902240d8150308181c1440360107120350340403c040c90483d4080780d0b005031071a0240b08a44119200190512109200240c149240c4400c0d1113800c410f805e03682d4001d020045400c0c0d112a40590000740000e401080c854100c58091080c0c511442032026203451425184d9101006000850489a00e0103003060ba00c1800d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 96426627 1250 96425377 96425383
    0x30c0901050d1506080105030c01030c0219050a0b010603050103140a020105070605041506320906041d0318100c050604080a021207050a0b070503190203060f040207050d020105070e01021b03 83
    0xc1090340c2d649000f007403540e03000000c0c030401d001e00401c0d10a0084100d9402958002e1043c0401e80c030040d00680b1004201155891040d21307035140030398aa000f411501c1300010001b01042c0c0c080e111136240001c455056050000c1e04420764488041c540d400b044800006d41c4c1c01009440720a035103c0d4000c5225640c901d0300c1d90100c281c0c0c50a00c0007881c200007010940303600c400301c84140d91a0100c100c211b039049040c5160852281c0c0101c154002200d140031400e1800e060b00300c5a0b00341281c060003803120b40c0000c1c1c0300d8a5039001520014040c002584449203038a0700499201c61151f1030329040b89104801e44446441e40350240008010140010b403000b8594000d0012140f03044802507507544a407014103100351991440a4125400b88040000411450041041d01e0040c036120440000070300c4025025002944041c001603072200108000384d016549a00040c20010311640281241802c1088083d0079610060078050500c55200300c80106a640014001d00d05002d6441101004403d0070109007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 96427877 1250 96426627 96426641
    0xe0f04020c0d030f23060906032a0a0504020f0a0c060b060d050906060409051c0e0603011e090b1c06021e0712080106080403050306040b0a06091a030c0901050d 70
    0x240905500b007550150594000d00031405000000d1249003140341c480961070b19a080c008003c9900000400ca4a0a00001155000f600a01180c41007202440c41942e6820002d0f11201d14007100c9070100c4c07090621a154800408007510b0a50a211410559034118000e0040041c20005050050b10520029402c00003410001912440d5500340c0500d04030094401155103010b43d1161202089050900e44144040c09422030702600c0600d21200305001034101000d801810014501d0310300d1004e13580d503030066000300f001c11212540710080560f00104000c50358041d03034516191400c070004c2d41d210080945c4e0091032018040110610341d1074a07800900802c1c0d000c040e10b9968040c1072442104c403070300910015028116040f5070319015403080310145800d0150300002040c0801241c00030b40200095900190300800105902c2c001c080820141c80881e8424000619040700821400700004035041c0004080d0080714618034016003401c03014402c042c10300d8100000011900100750701644901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 96429127 1250 96427877 96427897
    0x40c060c0f2103051015111c0f0f030b010e1504030b1021150905010e150106090503010b1008060d14010b090906190c050c0102030a020406090501020d0e0f0402 70
    0x1d82503400c1c00641d40b071521490420002003440d003808100480c1e40a0f054604480110152400b81100301104542c0780c040c403444005c142c46071116203074040c000502c1401c41180c80b40d40c0d11416610348840242450060002c500600d0325040b480c10035170740e105070481d11290040d42d2218580900b040c4031329141c42141e00240006c1698024404200000103218040721030191010000c00312008000c0c1b947c00c004280107000031010284a0141e03e11500040c0c456400340b40002020600000b001d8106055008001148102000148286a08800d186010308403d4000304200404007000c0cd5107158150194002c1c020998005130f40e50359136101100c0c1241d0301055001c0002c046508860181c0451042c042c412104540001ca4a800008615100b015422030b00e5407a051820006c40c0144081924002000010000343e804990240021030003611284401070341d56107424001070222165400460454014401c0c040040b40e201511081e00c0700100d401c860380454240003e0004d1080503060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 96430377 1250 96429127 96429143
    0x7111c050106151818090f02030d0f0f02011503020405090f0f030702040c0509060702040504080f130302040b060a1706030a0c15090608090a0303020d020c0304030b0103050d08040c060c0f 82
    0x8159041c40c64407480001c00f02d502c8490b501980c00654030001200d44c0603800800340943d054107482012034104d410680d0140320090b0803840c1e5038000c06c0c2400c1d4000d044901240990008941181d44034584075000da4551008105a000481f040840941d40e0720010348034948401c00311b15420020b0051481c8007081408943c03502c0e60b00180b10361242c00c581c1d400c0e4400d500d003203a010040d5000b08100c4250701d50003000189480c10070390070000200800341c030649070440d06004541d02ea40c074800007400d0300c40510046180141c51403041005450503041342a0152005120400f03030306411a020781140080c180c100101030b0780344000700c2c3c50944d240d01c0240031024000e41c001a0004107208c0d1084043d03c41d900d13816866221b5030150b030f10260a990424459003c000c001010030322036405070401810203903015140000d024411303881c41e0010340054035581c18540c010401c2100400060001040900b03240b0018902900c0344020741d011842003005000c0390541e90020000d52045a0000725030100d20707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 96431627 1250 96430377 96430379
    0x3010b031903080106050f07060e0109171e0405030c100309021507060c080720070b130e0a0504030813030e100327080901051312110906010507111c050106 68
    0xe038000c1c4128041c0140e020a0201c000170900f80c0c459401c645a050b41000c0300e42c0350400a41c1c0e460020400c124a83c0425565200d04900140c41185003a083c018440405506e540244089080c482c28882548800c200c04010170401910040307002e2101d203034201c5440043d0b00c18003005030003407c44150002c1d4012240c09034a9000070803203011740421801502c08100620b643d06003071354180c2042c1c600001183c1c9040154803083c8110311461208040c0d502074400c490341c3d800c0c0d003010b550021150039801050490090040140019900740c0c44a5084828442810542c5010380528005080100c134034800c0e0141d5024517000c2c5161040d00e03403000c0c05030502001c074101c0040c01020040c0c0d0013580f0520f0203018011403244040c1c09080a0f400c00043c0b03103001100801034480d030b803122480d1500341101c134000042c600c80000522401500075107481c996402d00904000e070f151002824241072100134410580801c0084040f03072400f95040e1080135401d414082c1410880105120081c803643c05e10300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 96432877 1250 96431627 96431653
    0x8030c03071101030b010c0204021309060b0405040e030f12060a0e04140706090e160c0f08031e041a1906080a0b0c04060518040b0406080a020f0906010203040302040b03010b03 77
    0x60a1140c064032a602c401c611103401181654015800a80000c445464040240c58294001d0468804e19003e406107030b590b884011003511040da010007100b00d00810100084d0405002d041c40060300c180145240401140052080303000e01020b8407240820b08002842e00e132a294450302c00380030408000f000d546010701e0700c2c0440c45900701410740c0078094618005034180c020011074054070450700d4289003c1d660340c004c0102d0b11203010106020010120010408240d5001076500030501511800d80d9030301d001070320003114004000e810246480c4900420000c5420034522000e00442c3c0a8807251395107900c12180c41040c00300550085d618075001000904400015803109468802d2410074003658507000311300303418000ca10801c000700e082001800388890900c1d175200c3c00108010000a008051302c408103045440a42210b102907100748092800d52a2480314074002d401c08980310f64140c031703020700001c0d03e070301661200070301841e221000c00c5002da5080d04500300f811005004c9401c10b0312900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 96434127 1250 96432877 96432883
    0xd0f02040b070203010b10020c060304020409020d0302061506040609060c05010f02040f05010207050301110318030c0a0b3301050708040b03070801050909010e0604030809100509030418060e040807080408030c 91
    0x42c0080f8030962900c0e820010508042d201019802550740160a103401e4007002d1106030b601c0100200d034040c0e0303140009001a9120030300400c07114060b174014103443c44c0c9140c6034901094442c0000f449204184010841190700102d4031050b0358203854003240003e098a0100e0250500051120909001250105201a00c48400303c01c4480903400c03500c03600c0d56142410300303c0c1c660b003803071141c03211003000095005445408200c00300502c0c6802c41c0c1c40c01d07981c080d50600301940c40300101c5640242c40e00340801d10b000441003056200100101410305c490000c5241100701e4030854180c14440d02040c141e050043c21415603000b40090358443e592460081c81c0200707580000d0140520601142010424840b8148a8014800c2250004000329100c40e01d058035181c0300144898107500c64139000350190038640c041c45c0d004902c00b0005640300d03400c103030307900d01c1c0403625554044010740703007000400840161148041d00300350022280c558a4005007012081c600c615009030515100010700602c1c294400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 96435377 1250 96434127 96434137
    0x203120c0a030b06040e010b1b150a0b01020c010f0e150c0102070b0c0711011b060f060302031c021c020f0706080a14060f040f0209031603050609030906040303050d0f02040b 76
    0x1a0b42c03c1100141e8082001014010b50007103100ba05004070040c031002d40b112000300103140d80c03410004802c0c207001034214038000d246080c011018201030305200e000030f028098190443e00900280501480c02d43c0001c1001411765a98000c029034107010101e640c490045000c4001c0401458540d1030280ca20040c2c081d5002c1740045030b01154081c00039142d0b54000c003c0e107098540c02070810003400c0ea00c0e00111201e1084110070241c080ca010030300340c0040c00b14850104244100440030500915600401d42012607880f020405400e08008030040940c0c0410240d21500341d59001c01001c141c6071601f01d00e40030001115038514400d500b40131891542109100d885441c42d640203121601001019404201041e02e40c2c075002900c00034116024a403d4200c4810845042d40c01820403103844002490030088107402c04068009510a20512205100003a8400d000704015441c101072400030400c180f21301e00c8040d0421801050490741250307a90000400038a01000554440d9101e000c0c2500c15440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 96436627 1250 96435377 96435397
    0x70e120f0322030c1206060b0304050105250203040603091509080c060c0a2f0d0f17010e040206070602071b140f010206280c0e1306050603070507030203120c 69
    0x700c405400c4009000690307110a49a00c41e003100400b42c58403406085d41e5a50314001c580f80394503080d000c15404030000281d4801c0d80a60004100b500741002540c0c001c2122142c000241c00c018588548480c2d00003003200c01303c4505180c0051180d03440e06084414203000102550b501d407d04850100740404c8501810315406c600341510015281c0c03440c400e10a1041e0b01c084804174050101c000342880350014801d00392032186140310400e100c020314a900702030741e84041c100070441010f44414a641d00509640f007644912440c180a5410100070545103440100003c0c40780c030001810f07508020940d01605d00142e07000080d10300008110021540c0000203020b1001c0b541801c8003072180030316100d156005c0301da4040c4c02400107500d80740d0b014515018255002c05c402d0466600090340d000c020300c01c001390001c1b15925120483c05880c10461903a02c408134000d9800d00b0316509210035642d83d02201d4101c409c4d07050a61b0364105514003030b070450180745018083d510b071b08020010380c041000020418464 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 96437877 1250 96436627 96436657
    0x40303061508010503150612120d0b06070b010b0702030f0a03030b090c0a0909020a03091709180c0412031e021e01020408070302120309060d06080d031103070e120f03 73
    0x1016032000c07594202c092003503643c10390002e500441806000468550800e6000c0e000800c441c2c1e50540c00da107002022410b41070780c6840000e43c007001079500d100f03c04080c04116402c0f440c5c03a4050b21107621455060103025940c444c0003540b03c08550703041149440c001650002d5030707001045c0d810090020000f4200141c01880d00702c0014a00a402d40c08440f02c1e940f660311022421030521583d00025000312900c5003c0c50759521440000c100c04455004440c1c1e0510030b82c65407901040140b0480d007045190009000c6602024400e038040e180080ea025214080c44401010140b42402c1721079111440b03c03400010124110444901d0340031034007590b041141400038045d07081d203081044c205c0c031903846106182c1d08403c0d4188014030f440117016078100201e0003124103040e4a4400a5600d80c03280f5001a201c0350b4511081110080520851000c4009400d040004010107016501d03d480004c01d076004000c0400d044c10040c5d680c0341c4501d10420300740012a00101105030b500340d501d034062000e9415406c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 96439127 1250 96437877 96437909
    0xb040303030612030c0b060f0406270e0d0e0117090312150d030806130507020a060e0102030408030105040504020a090f02130503060106050406080c16060c0324050f040e0604030306 79
    0x21000030280d90351341555044040c0c115030b168888061000b41016a0280c0d05101080e0143e03114042d2070003801c3c1001015400100301c8034880b0784000803d11004d0454104403400d1101e40700401e80c50740466081c14459a0b0104140048820321080b000f00c59a000044003031100c1160004082c007054501e040c580d20240e11501401e02c03000340d2001389150302c8902c8081c480d00180c0308400654210001404558035820340d8420101aa1000c030b868000581c0241034071010f0021034054081040e50345402185941080c1e201e0f600031380310500840f409181c5400c0417070119192440014000c0100a00c00c0000b10514400d08000c0c0d40182070305855480680b00c0852940b5020603454121015a100c0b40c2c0f40519041d13085c2c1c0e03004001406140a10720500c45210049440b010303d04845214450003d0134060f11040a804c48900396003545d001e0720201d00501514195078140e0050b2641207500d44403042200f00041c002e844c28114250840c022a8140000c0540540009081d6910303084594084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 96440377 1250 96439127 96439139
    0x30606080607090807090b0103140411030d140d0b01020f06090303062706010309050f0a050d0306060305100501110f07030614010509070c0807110303070302060106110a0c1a090a0b0403030306 84
    0x840c2c180d02640e80142c1044404001e0f07002542e011001e0758906040124200c90ac9440000308004112400e98124200c0e100c481d901c0d1034144468480320190341800c071585105010381c040700c0d001e08006e074540240d0303401c1c00c55503981c020804517044d80700d0354044030300314034025800580720340082d10050b009038a80c421101c038801c000081500c1640240909001c43e40c3d807400114050032005030190b4070b07030054aa5140e80030809103c58002203000340001c01703c010b6018001800c40c0d10560001c01054500014000d00f43c0301c031003664048030070901c1c10708038041015881c18201611601c03000d14610903641d0000810219070050b2007e0b100340a403608030741c0ea0703610030301034241400c403400700c005820790081d80d001510380006000210300510074140d070341c5402d8011900c2d541c06850700790301582c00440108005a40032040f1681d82d07029401a01941005a4a075481c2d403169004075038200b1100001c650200310001d00f0344000f480b00030120307c100d603500c165915607903220780400e41c0000c0c1001742c0450700c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 96441627 1250 96440377 96440387
    0xa090602071202060d0f0e0d050a020d0309031b050f100506041505010801091e050106031e061a0c0c06160b09012013170c1f140315040204030606080607 67
    0xb500360098842481c041d0703001000b02c001e20106049002803661a5000601072608002503c0e01071155181d60782d440b0041880070f4982500700c0744020805003403a88180019078403808485000341c41c02200325220301ea9140c894140000d45090f41e025100303081c5c82c5892120150846030050100b41c8080190381451900480d45100b07500869020800c0400100b00c01240c5074800c40c06440c003184085840c1040c0030961098079401c0e444100002e0f11034103601c15050302d018100401e40030814080251601d0800406038011928464100d10603011482c1041d601d0248088980c200c8014180ca80e00c81c00791010003154400142c003038400300f0f036407070006120034014400e680e45894a56405003a580c0503c054484c02d5000e059022040c4440d82c500180010b208420440003d030004082c041c4c544021090142c94200b882c0c4016007026208400c0023410303045481a10320048011190f80e5035590050901c41c42f1194104c5950000c0c40000c000082c4115684050203681d0b100e421b494158403025400c4603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 96442877 1250 96441627 96441659
    0xf030d050301050d0602040302090c0304153308010501030b0106080a0605031b01030f060b030108010e03070816051504050a03090602011a010f1b06090b0c030c16170a09060207 77
    0x10400c00c10040c8841d18050003003181c00c6100780005450b09449a004c41d42d06103042e51070602c20785022041c00b0030400f62003071301303400c4805140c010401507103552140444100846848031140c558070100066507006910080044e101c0c180c024002c9507580d190504180109102d16000600b00d0404034100d8916800341800700c940040007040001c6200c0302081034445142c044a042c50b945101e08140c24015018000c0180b004100c41500d940c5415043c0f400c1d1040e002070f1903a6900208194000601008191005650180d58100742050140380072803801001e501c4801c420925003007044200403001444024851085d5030300001d155031918140d09036608104142803414031200c2d607021079481003040d0595504e00345010107818807100040030209540c84000d0390181c0d01d5540800921020300442500102c030525100c2c5140743c0140e00181602445100040407003070500c0d000c05100c20b54682003040e81007402c01542d074031b04090020b415501c1c42d1292074094060f04400042234203801590070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 96444127 1250 96442877 96442903
    0x50c07060c0c0308010605090619110c12030d0506040905030c0c100c0302100e011506030b0907090501080c0c12030901050f01061e0e030a050304121b1a0d09021c020f03 74
    0x4c0616401c0c100f040d40c2503040b03002c040b40c0000082c401d801d605a08016090b10f600565140c0c1d40505150340c1c6400d0130845100c0382140200548404c91108410000459407009004400003e09448007000140500100c103005881da200100300a4030708a00400c00f00c09038031040350059180000d40b0000e48644661801c060096004012000030744809030700100c1507a00d05034000240080090807800021000d500120006a510200801d1070f0500765200c940040a504154002c180341400081420600502000702000b001c1489800b142c03041011a0004090002135a1207143c0715000a00800c02142d4141e502c68500d000018a54002c0c1c0308080d1404100c22802003040008909440cad01d41020107490701403081c13110a0300410703801e001a001030710078103044011405160601a0ba0780404c000f4241254170541030421803d105954000d401c6070242d80d003181c0710350500c400c400050500c2c000c082d400404a155280c41528040c0520828a10841d0308492580c10101419914041441382c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 96445377 1250 96444127 96444137
    0x130e0108071526150405010902090604120c050411071b05061801020f060403020102190e100c0809090405062d060906060424120207030806061c050c07060c0c03 70
    0x300d1802440f88145681a141e102041c10320fa14091103001541d2100301e400081c1400d4442401d05189864000c1741e005005441c0c3c154104409800040d48a100d9403243d1510440c07010740060400403600444c01c020030707004008000b403403450a080e0b40d16900502c821078400214902900c030032407020f2402d40034ae401c045d00803428103410343e41a1082190390700080b815803280464812000e01c2c10001d00344524031075800541c84068503540106019140c585150a01400c0541200a5200c54440c681d02c1c1c1c0d914034260720913264900f00a8a940b06d005010303500f00030540708010a0040001e01940200d51001d100c00510202d8044541d5001000545641d0740c04840b01040d8246800c09100d0340100700248440e28040da9a1486401c01411500a01c07800048190000f043c40d0011032400c89800c0100c0c0551500d4503503940100004402003403076200f034001055200220f0b94000c20801c060154410411441c186128400003a8000e01001c8030114140142c1c1092148240f07039a041041d810346503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 96446627 1250 96445377 96445409
    0x6090f0f0e0a061107050a1230020d0e0f16080a170304050c1305010302040b0108010501050714070810060f06051314010c060504120e04051512010603050102130e010807 74
    0x1070f8a0207000e03080d0401c83c9960040c440c0501281041c450201e14a1080c00717048140480d400000d0b010840d9221000c1071000c0307940030340300b9159019070076000c2c1282201006a441207005240f41c020103078090a25140c1c030846243c02e0569074000b40007408003420602140c102036407810034540e02e0149002c010700f100500303a1030b901c040716080c014640080c4a0010f48240040c288040b4500311500e4025164403034a480042040d800d01c1d116120985000786004001981000700113049440b07030f10001031550034082c4640c1d580712000d002450180c000071040c0d80000303d403001450b000e0480c5000760349505c03100040004099000e842103480c2e00f600c08010340c2c41c2601c4c0009400550340c801359100d044c007a00040c040000341031072184900c1035101c0c3d82089511341e50042c004004000641050f40510300d46414060800c1c903194528001c40001c50b0040040884600c0b52800341200e9800200300c0c1d80042540100022501d401c101601d9500c0c440422680c0d856a440741d8a0780544920807024007800700d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 96447877 1250 96446627 96446633
    0x6090b09031005071205060f0904022701080a0318120228031227050415030206040b281704020f0904080a0216030b012706090f0f0e0a 59
    0x60188031100400340d42a40300e0302071090003a11011119240000c10700c03a03903003404501c14860150040e100381c803006d00011000007c1654400040c001034804d06400080d540800110440e4082c80100001d072580036580d42c43c103507030391807140000880215211050481400104c12100800c0307801042a0103000030554003440300c1d40c54803102d103c000c0c00d2540c000f100b1340b0104030b0503800154413801240800c01448140100650301c3c00d1081c40303048100c042c1141c2e41c0700c2c1885525082d82c8003240c0014203500300c3c60504400c4211588029040003000c10005200d1072450098500c01003d0b10700c40c80356107031868a845003a001180d184011512103031504d1041420702c9a1039a2181c4094a0300d8607169102000500383d83d0100c4088030342d0940007c03038a4030340703905201d203107481d02c04003880e40420750a580d90060090414059849410040d50230b800d05107a080b040e038507840c0164a0700300600f5495403050800b620000301100e005a050948542000303060b80300ea00e0b00c48000002500b0342e031580e66 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 96449127 1250 96447877 96447899
    0xb12060106032408101a0a091a0d0b06030601060819021602030109110a090e030d050603030f0403110f101b0206091e130501060507060504050102040312020d080f010609 74
    0x4150543e048140d4600e00c2041c503120786010080c0c00250b004111403d48a4000780603140141500c040300b207186d846865090311400000c03425101d18000c040742400d445081c00070100c110a03400e07940014550703854010702a4614203031b40200015001e503100d90303803500d000f0303101410706440100c40d0320f440d2200c0c41c6807058103034041e11007a940d064401c04c0040198000070b0a4500030402034440001c08029200c851400c604000018140c2400900003102c00301e45082d103d0181040c1c0140c1c154481001078415035050088034018140c80c041c00c3d032143d4036400c1c41715850041e2101035001e007000c4243d400d040e1070511034000f900721b2117075981c45906450041c0394200d008446030403078000e03034144124000c2c3d507a41566510b1000d0183c083ca40c681d5940e2081040c402003100107030b0b11171858600144a079607488800c558806412050115040e16540b42c0280244100e80c00a07000c1000c0f0b5840100041d4045000705001001e079652800a44480091854404082c81400003241803814200402d8400e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 96450377 1250 96449127 96449141
    0xc0807030309080c01240602030702091009110a0e03010209060d0903090320010810030201080708100b03010f030b09070e0115030204090c030e0709060e1302041b05030a0b1206010603 80
    0x60714000c116410240e8a1500c20703085860500a142d449094041074031012688110035443d00312058141c1c01c1c50301101035200d00c10480040d004d11a40070004051028028080c0014448060304108c400004d508241c00c2d0f400516044000640321203e0f01050b1805000380c480c40c0c08014021450640f01200c0d10b002082500c00890a01c40403c0c00000070581203481281c40d039011810390310b0010356283c0010701c41100100451481a0191f1041c00542d80c044000f07681702009041210b002e880d02d20030764444200503402258080300000010580d02c1d940710102c0d080300d00c12440e84005881d58201552902c00b14000d03541c5000f28031004202c0286c0e0100079148a81d964200103140503201c418220980f02c6e034808510103e5243e6440700710f400d20070018600200407184e0108005400d1145441d0720b03441c041c014150b80d081d0602644259030ba10340c45032100c0d54408602c03070701104000744c2c09031103508221003502c003292503c4010101c50600c3e802031044401180003510740b036800d02c0001c2d0001d10031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 96451627 1250 96450377 96450383
    0xf230d0f0203010c1e110a030f0c1b1503021c020f09040e07170a03140901030219030606200303180a0b0907091109010c23010f050906090109030c0807 66
    0x10001040340903803020312840c40004003581e03603088001c4440300b4000d0204251515001004601e5101e0851050702081d01d0106a9141c81e0909a150114100301c0c1c4800424501410a900b403a05070384003020000441f0301141c0c3c05c0c0110b541031600024099003240203444500c0b00940ca1044100c880c00425401090150194115141000c00d140e02040031205410440c4045921660003072100c03031074401d0076164000c1c1c000c0c02400030750310710ba034024541041c110704c0d808d40c080041814021782e8000d40641d880000801003030080c0700f90006004020340f0f100c1c41942c0c0400d1801034030030b00344803500d0014440000400029440e60704d414040c1c18900300980f841c903006019504010300000d40601e591401141d80d000181541e40c2008121022100080090503818130200b00703140980e43c03c5081c10190703030303004152032136105040c0c21491a03040020350b8500d440e5180820b14500d084099002c1d41c02800c821341180d03c141e82e0a0b000500300d41c00110040c000c28070549108bc0040c24190003402020302c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 96452877 1250 96451627 96451643
    0x606071502160f02040518030a03051506031905070f09210206030f01090f2a020f06010603150b090a03080d0e03030a1424040f02130603060f230d 64
    0x107001030b05608801281442128400d00c142040000d5150a01071242c000c0e0210a400c0159907100701c038181e03a40308503440d6070141500da031b0016201c1184681d1403400240040d12260392071030580d00e031048003981c1c0811010081d25100c046451548500909a0f4202ca15102c02c0071060405041010202084040d26903c590301c2c2880c0c001030700d883d0040c40c040e203001d000801c519410701102c8001e444010164118907403610f03c0405c020540c008000b000c91105c51441c0306050441da500302d040002d15148205c142c42440300009417654598002e0f4038a0610070546481c1903140c00a03009140f060418195200c0490340301030000c00c150300002c00e80c00e6002440003520300e00c90042c007401c5800440d85607100c250344545000406907103003c00f07035105914083c502c3c8420041302d00e0710145040542414001e81c1e0756419003642d195154111101c269081c0382d030401e5a9a5240f0040103040c05000380410485079500001c2e1540c6908508010340c8904000c0d48495244c40e0705000040c2d01017030301500c00170 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 96454127 1250 96452877 96452887
    0xb0711030f03040614091b0609030a0b06030d0503090a020d0609060c021b0405100e0c0c0f0307060b040b03120f090409050c010207060504080c0d02010309020612011a070308150a03080f040e06090606071502 90
    0x7a03800c100b00c103070040c441d41400c2c0c8cd0389040c004040c02c01c1041c14810007402010800c00204800c0819903104180e4116a00c5d4041521400c284006103060100100110300d02120103030300b40c2d0002502030004441500c100312400354203003400705071071085e90348200ea20b40d0228107001040c1700c00429507020f0300104186003401603980c2054078100300c41b403428129400c0015010180903150050003010380c001d032020b0154890f03400100740e503100208480003c4510100c3c4441280c50200101c1e10200c40003071050045881c10300303229407540040c856450243c0b0480c800002ca090044040d80d0448042c44090020118040c0c18001c0d070280040e8200e04055840322404016038070701010f03000c01564140e84204960410311248441020b8410720b0428020610a150000f540710300c1056000116280448001440c0300102d030b01040d850700002c10049002c2244c44d00030401c6005001107641c140e540415a840701c3d000c2c40095003040da006034000070104070b2040400c80d8011036002049805400614207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 96455377 1250 96454127 96454129
    0x60d1703010905011e15030c05090a17010b0a1505070201200109170c0d0e04110406050c0709060501050403060c0908030406030b0f041103040b0711030f03040614091b0609 75
    0x951090b0404042c00d035403800144400451403011002d1044038141e01c80b40281800c45e2144542d5000900c4410145c48040483c00c2d1841001581d000300000707041502026100d84038805c4201008011a2035917282c480d410b421842d001e030201080342c248100500309003900c07880880f041e42c081d42d400d80c11702280f0107010700c810358012085850384070801e0000501140515002030642e00c1c0000201c0c80310710071710900f40402c0022512100c8004c09003041c902d02118040800c02800080c1140d104c3d20342d003c28006405070300000104840c0c0900c8060701c8255859180b00340071111103000d814000f45080c44240000f4070681e1140340454424105245401c0d6514061461548941c00040001c6e4a03124002007900b000c103060007801c80b0886052060b03160304184203401b4000108003425030007010000c0344c42c4034041c0e5003465238a6802c405503079898480c0160000607034004e80b01241c43ca0f240c4a128190404110181406860602d018020010143c0e000049032140c002110790f0004040100f4405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 96456627 1250 96455377 96455423
    0x2160f08090a0e091c081303170c072f060702030c09190e2803110a03080105090109021603050306190906030302011506020705040f020d0f05040606050315060d 70
    0x10700740f083e40c1c10024900b4a0344141440034003007145c03420410f620303504284c0c03a401c0010036074045208169800d04a1150600b11880c2d00301540c04040d0303002a03401e00901c1480b44008154040c014800d00b5982e4584005040c1d509241903a4900b0116604101091a280460040400b940004c00300e81220081d000007600c440000d80e42c80b245101040280141103150303004012020040b040500b1716048005404198801c5070462040c140711140004800c160140320482a40084441100e02004003464041c00c2c3d06400e02406110f60301c0c1000004422101c0c1c000c0b500300c1549011056005042550252483d810150403181d21515080f01c15404400640191000384404540031411916604010b4216540004428401e56a4034001c0c042c3d25000107440b000c44000780c1e40011031041d0510a04000e01881c0035001d6504d003450726080d00024540c200a00960054108002c0555a4001c055407400705404030b5040b40345001c0012064500159400523490165601803201c003c60b02212403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 96457877 1250 96456627 96456629
    0x3050607020705040b04020a0e2404080705011404050d260a05090916080103201003020d1104062007050301020a08040b090304030201050706020c1006090603030305060402160f08090a 80
    0x140d0207250b08100c075280030300500701545000d4404504c0d0103000000200b208a049450b94050031120501502c5524100b0480e0b0404000d00a415280c6884124041d1120014800c450000f400000ba0542e10b120210071642150300080c0442810405561091040816400c14030030309644c0b03403203060300101e025008068021a96407000d5070303030104008001010101400400701d400e2950340711181244c012003041e054942041c0707090715030f00380c10003100f1701c1549103000305412040c3e484801076141c0c3c00d60064807076140081420312204416000e1941940120712500001409820704a150a1048180d2501040d0790f04291101980c41e0300100e0f0999000c0111100010745103420481881aa02452a0415100409035192a02c1c0d900001c0141c024244060012a40003459640911040100c1c2d180d046444006001c1f40d651020100002c20041c0310a801107410140010b26070300c1c091084031844800340d01c2410300030b0441d80368107412072480081269410001c018021302660742d0f0004c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 96459127 1250 96457877 96457891
    0x170709050114010c11060a0302070318062120070506091b01050a030b030703030e0907020102190305070e0d0605180c03030703030e12030a0207060b0d0209010614040308030f060f030f100506010306030506 89
    0x1d40c0d56600c138a4024500d20340d04c200d338806481c00e1a4248030899018007918400511703480d484001d00da118249400921801240e5000c507102c41c0090104240200064401c070740c059003c1e2138055480100c4c494823500b1180402d0391041c50000102200e41c06007010b04000e032981d20300090240b1041000c60f2810300e070758206070049001c1c03186558207440d013448145d50055007032000750308183d02d030300c40c03000449081c03a00b1005043e120350004504601c619070203440c41800401d002440c107014144800200070669145440c00e04418006820320700016040034203002c090700071031174400281c5044000340311014043d031540c0103148421003258420340180d070081c500c0150060703899440d86800000c4a0b050881d503801055405015805665014070450443e906030404411411a903c8008800d21071a000141104404802d01000d0060007461500c030340d00030307941050345030300d0072003019a0b4011002480d00268040c00a0301da100c2d003150010b64001e03006040c041401d50326a9219810140115444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 96460377 1250 96459127 96459131
    0xc04030516030c0b041401030906020903060a090b091615021207050708060a05040b04021219050a02030705060903030d0b010323040606091802060c0c0307170709050114010c11060a03 80
    0x14014001e0240b0f02c0b80080c4003000d0200d1905183c298410500308014071042d06041da0741402c27006000942d0120742c0e00341c2c40201036880b0b900d0800c40d1b030001050028001d6441c1c210900001f851544006000c1c21080708802220340bc0610341284c0714441e10b03074202c1035021405070501c00316803d0f000c840a499120b100344068410309082c05082850a0700c002d0032003d09504007402d001c00f20f078801d1017058101d501911410303100001c40a109241500030714011210760f10070103044040c4180801c058031050720032000da803a19503840d000c2040e20302071908405c1e4035420400c0340440c4910545c4c03225440d64018100421844c00450082d1008101000c01003d2104c1c1d0000f000304010042c03040802802d0010340c01c20420340400a040c041d00c040d50300013030148400040c402801c1d02c0410111100e80310007011200d0145e2641c04071888100c04132100c004512550740d01003081501801a141a2a00c9800d0300200c00d90708001110314a0038140103588044900701102e07041d486900c001c20080220b6180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 96461627 1250 96460377 96460379
    0x20d09050d020a1505012301020f07060e040b10020c010503070c0203120c010c030c1b020d0204050a0902031902010507020d08090306010e010512010e0d081e01182702090c04030516 79
    0x200c905074014a0710010035035440c5c08010710003815030240e1007101b09032070000340da004000351700140d00e000e00c02d2003901d9a9104508001440a9001e9103031241c4100903102880036107019414080000c1891340f03a0405604000d41541207540b044001d15440000d40c500710302100704680200341040d074916848452108000b0302541501002d0007401000381c0d80c0e20b0204200c0440d0040180084400004908815220000c4909655410150300252a0014010800c500741704943d1401414001003c034024010345280b124040c082041c3d9103509501a1980b900e000043e5003040582c10442d80100e43d01c500c144a594100e0320208920f6002c0c01103079650300419414141003141c07041e0307035018501e0941e06103541c411246801040c200368500e44c0c6c0c01d10080035107481541d4003d40b5141621000340c20070318400020800c03680c0c1811f88900540710000c00140000305180505104003280a5080c2d00c0343c1c0901c80010300f400700350a0f034045c03625012503003440e440707941f130318202800e426001c0c078170011441d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 96462877 1250 96461627 96461633
    0x816080d0612030e0123040b0903061303140f0d05040b0103140a030914030f030f03010303170c03060d1b0f15020304080d0302210a140c04050112020d09050d020a 71
    0x100e1040607021111105490440c590f42c01003c1d50750140e541410403056040c9641c1149032440e011040a600120480c0c41c0d54403030790090419040350300c04911910666001c508420300030348a50752220303090b40d5558117100240c0b59112056205a004610111080060000003070081c404e50740528881c00f0070704050352440c2404140c0344402c445401c11500b200c40142c00103038102c0290344c1282d6600181c1c0004220740c000217410102c1d20000305075140000039000c0448410312000310305884c4a80c840780340415100c4007004400c1300407200c50340b4450007040458890303d0010754a5036403900c80c3d80709900c1d0640044425031103503601d17806003807040050308090011000c0900c2c00c0e10400614070003581070510300030322030303075600d41c05001c160500d0b03030000380308541d80384e8040c2c1d072440040d41030b071004110f05100b03007040020841e28084080207401c4102207160105150200c0e411034105948400f001040508100000d500900d074070030b101a9907280700c100044d02031100c03c2c03085459401810315070b02982 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 96464127 1250 96462877 96462881
    0x4120f0609080306100815010809070e040b04120302070c05040207060603061b03050f040b010e070e030d080f1311040c09080706050712050301050a140d05100506040605010c020d020405040816080d 86
    0xd401c5e0030521071608100301c000301d60380d440e031000680c0900c0c0c5202c02c0e403540c90f0b682e8113050b11500300183e150480b40030841803000d410b61040c01113201e440002c1c0a0142890110201d00811000600424400000700a140740ca1b070040c1403564006c040010310307507543c0d5480c6001c851a510040c8181c13104641c4101c1040e80510407241c4c040075840d03100da0207140c151740d0100d0300b5105000e144100702c804804160071134400d00001141d03a101800b194050420104080d00b040000c841d114071501c90000001c1034a22442418180c1c40d03070201c00d4a1803100d00b4410440a420040da102d010040c1081000660600400c03400004118030f840b0305540d1185800c01000352006205440b080c000104010003070b0340c50f00c64844003280c030032896200030840c8c20b0740010321701c10780881c0c00780c034520542a0110582507039521071401030208503420011695079a00540b09601c416402a40c000300346140500541816002160310600c2041e81034544a2010380c0c018040c20650030030b88180801080522143c1018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 96465377 1250 96464127 96464149
    0x40503310803040f0b030727030b070c03140a1101090b100b120105010c0204020c01090302010e06090a20040b030307050606010305010e09030702100306171c030605010504120f0609080306 82
    0x3200142d440d0600300b1048900c801194420300c01d0000c0000300151400b07100c1e81042c1c0c1102c94089155a00b15101e100c1060001124002520b0205840c004a440c2900440030850031030b034181c03500f088401041c40d0035507103a00b1501961061015602c00211045000c0c450412158810140824942880d8944610b1105036410030104050100b082084076011a1041c90440e4000d00c3c0c040742144e81480440d001e07000f884400d005942c00c01c00e900701056019041580800940c82c102d0348280e40e0161101c3d070f0354010240c040c04602c581d4510151000000922140c42075003d00042182c8162602003451030344a00d10645141c0c205906001e25076030b15009243c01410b80420440c0d82d81800081581c0b40d00c20303224020b11070141c040c0c2000441d4080d4200c18010080070b100d20743c0422100703030001d0322402988200c100007409405089001e60292142d00192007040e90740604150828034010b45142c0313440d10642b848038072400c4160001d16140201501d040c414a0055202c1c2412400d00000c1441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 96466627 1250 96465377 96465389
    0xc011a0d0c03080306010201061d060f03060c16020312070309060905010203180f010c061a011205100e0712020d0b030d0c080306010e0a03140309011d0303030f04050331 74
    0x450340345201040c080441c0710152600449103541d20346640005074014102c4e9405401848c1c0c144482e40c96044898131840c0c0304e21070a990006840c80c144080540f609800c0b1100c0c3c0b5200d0301401b1000304500c09116004245101130700b2290305c10f842c4080819140c002c0b103400c50003d010f240c010300019070700c0384418000341001c0c0011070030010094075802e1891442122540a80c100006a2a981e0300c910b0074001900d0308000200041c2d500001511a00070501c071003e80403444000d1000401002c61040030b2050705c004c82c00d1030040f0304100c00d000028402410683c00c2240518000c1c4032681140300a094030b03012202d0025503800c009c81414105230841e1450800c0c00084405040441c4498044070380c0007409286c468501003401c000100080400c2c0c002410070100baa01c0b504c1541c400200800c5034410980b102c3d0b003d07111401e8000880981c034810b10790503400c140086040054007801d4903411038840c006070390424030f5001c16280300c441c1d00c403002c109000019204c00b549148880c0b0301006415 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 96467877 1250 96466627 96466639
    0x10b0a080303070203030a2a09150503091c0c15090b01051f031805060108010c08060d050312100e07091e0812130506210a0527010608030c011a 63
    0x16143c2d0020352203020090040344041d48070f580c286010ba0000c4101c0c041040c800c0303d002650250306000034040100b60084403170894061b5150350f5000d00540030f880c8100c964200504071402d105d035400f02600c803051245018400700c248250002501c0394510b0200c5c120030748000542c000c030390800c030f900500f040e0322090245402e43d0a1210312140c1b180c503110703606442e040129105807110302400012001a00182450065000208a0070010b421580705601c3c0b41d90f40c4c2116850300410041c41c6240600014010ba00800c00c04e00440d400e0340c54140e10800310418401802d64600081c6900d0604443c0c0ca0300040420f0018401300311300c2d003601c0307908043d10850203240034188205c1039500c3d0074860031902d00000c0440d01d0b020f1080440032401c050100074110607150441c804c20b8a1140040c025400309030b400720310004500742480c0c4035203441030107915010303400c0f0303035032614004449040c0d2154810300d03540b01c420105602401300300a0900540d00c400000b800d89460900c000c0e14541c00f169103100b04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 96469127 1250 96467877 96467881
    0x105060405040209071413090b0a0b0408060412091d040308160e090415021201030507060302180108040606080303191805060f0702071214010e06010b0301090209150c010b0a080303 79
    0xc1c41c1c400020b5400b001c182006c0600c211000e4042d1000d0081d02c0706600321442c801c0010500c0107060300701200d0749409403190019162104105882c40c00ba40c001c1941136440140014046000400c034144049010304000e140385845040a10300c91603d0104921340c1c1a41000b40402c0640c01001b42e039000031803081440340510800d8000304440c0d4110500c6100e03e441d0000b0070180305c00e004520941030fa004004640d0350707654480359244550700740300c2640d0a00403c540000c0c014005d00841d004180308084091480440c88015298040064002d0720310035075601c0042008481000114081c805d0701c96602e54086031211048180d56000380b030b0300000c0c109244581c0004000081898120120485206145d610315104924101840d800126030440e42965041406148003448200710ba001000b4004a034010300c540b42d03504003c1c4038442e00003500300010044105a507028046102c8024800ca82c0400c0e214080d0070f2a400c02e160581e01650f42c2e200c0c0c0c0902d8a442c0386010010001400514114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 96470377 1250 96469127 96469129
    0xa12080a05091b0411040602071a030408030610051c05010f05030c0a06030209011112031608130201050d3312111e03030c0f01060605180402090a0e0109090501050604050402 76
    0x1d05030002041c0c2d0540f46420012003070f40d150342146400c0d5904036503c076100c680d45c400007552041580b107a02403050b812150651000c0b103a00880f071189411030000352540d101c0c43c0510051011041c086804c03c4010b01240e24410000b200c080c0908054502c0850107505112900864901d036600a074400d03800715a500d4030030384500102c4800c82d0b0300c609005850b03070003c50041e294a440e60001200303601544404881881d45680618010b20180b4100084031040c07050a44000d0810f440352100e0200580070100150b2160340105100d20805070040f507c412100c0d02264541003243d028403c2410452038034019012445446e80142410703194042006025100d00404c01e20b0302c8110740c0641303048a80310003140c0041250481c801c0016041701c0d540e2184240c00c5844460480401c1d4580d42441000504075115600303580715001e4415140200701c00000405c07000758080400309810002c82e0600058601c0c44034a894020700741c034440417550840d68609282180c0c802040395200794a41810710002d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 96471627 1250 96470377 96470383
    0x50604020d061401030309060f0804030e0d2901090b040902060304060209150313060c020f10090c09020a021f060f05220f0b0a14100f0504080a12080a0509 68
    0x550140d030300c0c61400400e8203120010300f11808480005208160000040640c02100d40c01258180d40d01c4118003076071139108a60910307040d9070140008803484484101ca1825101d00d41f031144c8501099105012100702241d050301c3c0c000b00c4414081c8400004100750283c6020380001740c0c1003140c01b00800011640011b14900018201070101d583c04074040341186c0f07804a5800c50014490b80c042d80303901d40003c4412811180040480d82542890b0813644003030300000740c1c1c078280c0816001074110f000b4000d00c04401014500010350320550404000a401840c07480107118041d5542d0103040b642c2c0140080d101e0711003005503402900d600e0580c0401203807503207410301d02c1516800c131030b145c0800903c9004654484c0c100290030840e01c2c40c0a4961b6038808882d440034025030025070b614100507985044d650803e246940b451f51b04410603c00c1462854840d480740d2055480608001c0d080c039403505002490b0142a000895078240004801a00607820405096100c170f0202800d010301c2c6400101c443d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 96472877 1250 96471627 96471631
    0xf0a080f070c0f030b060103180b01091a1002030c0f0c0102060402040c120f0b030d2303091f0203041a040f1502040306050a05010e070f020303070c020a0306050403030b010e010201090506 82
    0x40d2100032407003000700000184003000070490861800c00c01e0b0740364100f44100c10000e4521038007281c580038842d0f21501a1707074080205650081c5058001d03a2802e440b0602500c440440c540207560320500c2d120f000c2d5500e0314001a858010f5004548a80c16401d03003620306801d000041e41690703c51403400045070303800181e043c6e005605071008603a5020400381901c0c05480050b8543d1b07403038202503031000b04481c1039000c40120300b011000c82d4452030001b0420f03512a01120400400c0301d85942000640801d031f40c00440c1c0090b41582150101507045511450310145405445582500001400b092140281600700c02c00c510011850071800c0c66030310364411070072011000b06184002c0484410b1a4030a034182e40c011600003209104a01e0500a032130000c1c0300902500d1000d03414440811030b51485034110303225400080d0002c6145450303581c000d0b0f4071034450407c2207030301c2060b049000c00060224014640a54884c0c0c0b004240e05000400141a0841e074070030a40c110380c50030581001080000400035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 96474127 1250 96472877 96472897
    0xe0c0102030322060908031602010614010c1e022101140c09010807030e01020f04030c0b0423130908120609161202071b030b0105090c03070e0d02130902030f0a08 71
    0x140800c030704d03044000c2c080350103001d00404808010050f0600500d405002c0700c180b1a030080003910b0326a09452540700340c220510740060307a030501d00700018500b40800e03901880c4518850541e800180c1c00144207600624103e52032035505800d45004c11824001c81c11104001074881c917491900040340c480d14041d2010460400802c400404c3c6080c2c020f610498aa1140310025950703a555100e04554650003480222503a0b00300c40c900242e0001c0100644007924010356803402c02000307800c400d000002d0440c0003a0740c040540c00204140d003869209085001d4440ca80c0c054a0701020b200708260800c004080130300407141d031010885108451940503442c200303682840710710f065258005500174080c070080101241400d83c00d403600d05010003641c0301200d00c2007103210416a01d42091041c0310301d0039111045c22400c00d0020415090240c1c0305614003003030241036000103005075000140580d41d02001c600c9010340c0c598880c2e0541c1002d001d03000e8101481130040014030300940d518074403481307549451 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 96475377 1250 96474127 96474181
    0x1050307080a1b02250e16111e0c03010e190501090b0112140a031b0807171e030402030c1002070e09010c0305090c090106120905100e0c01020303 64
    0x2c82c504030550011003100e0180d2403c45101a62410203503892074140c1c80514010316050100010000442d002e406480500d10500d02546030001c840840d505102900c40a12864903c6100d13401001c01c502c00c4012404800d181550220100247c24002e81c20034440c001d9040c0481445401000070f80780907142c5e904061900b19900c0b600b04140185691170005280c07203015400043c004449207034070008903003e105400442c1c0c4500d509113035540071072400100811202655446901040200441c101c0d000d0411341d80b6001150b0345843d6400c510460001c41e50030f0200e2019003608110661542445100c10324a00d035042a17000207584400d024041c510a195070075400e0b24a07031003032003048010030443c0e156480500b403050300030307000e040340000f00c0e03000034030f4040000c1e03c03170000040c03031304071030f0300240142c0640e03420600304880c10344900c07100c1c0000e00c0c1c03a0b9a0307400c002541001001d4680d40101c0001508040d80004035040c81c1035419942e04641c01801805410a008400c0b01016000ea5520b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 96476627 1250 96475377 96475381
    0xb01090e0a06050604090903090807120f0c090f06061b0b0a05091906020910170a0f021608040e06040b031911102601150e04020705010e0313140105030708 68
    0x41da0098229600032035040140480c0010307000300c45810402c003091003070b01d9120750240ca8042d0159560940d2150307244101e0040d060303c0210329040f4a04201c0e03401110070a00440d1100c002500355a1590600490151307035032820042294040030001096007002003807026010940c560f489114000307024450750035030382c00204544030000c201241c18455000d89040d410318803410108002c3d003140b844240500d50400b601218144100081040c0b044a2045d810b6152145c054840007050702009050b1b4180d402c110311607040000201c083c840030300c1030000c290b41d241040f22803078107800080d11050145081804c8082599000300300b4410011100070051411030171410030010f003000203210690000308001c4414201607020600078624051203140b485501440ca1205101c12401d03c10703103024008000d05201d9443c840c0c290300c0070060000380b0250600d00a41c560307500710340f01d42000601c80e500010b4002d2515507040000b00080c124254418142d1800600207801440f005108508012010340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 96477877 1250 96476627 96476641
    0xa1a030d030b030a290a0207021e01030603050303010803070314030705160f1a070e030f0c040903180906050a060302090604060806011206060f02010e0604050c060702030f06090a0201120b01090e 85
    0x80c2d200003134004103c10311040c136951008185c2e20703480d0010b45c540c046000000701c2414035030007120314a65024221941c007a5810701088400810494640d040585903200080071a4040028601038125040034690355005460040d00c03503503c00700b601030406020b008000909800070147e84820036501c050310301405c0d1030b1600d2041801c1d030903001442800c0381000d0850206040e40ea01e48078180d992525065003500341c0c1055502d669900c080c0e403240c2d0111420038502d0801d40c00032500c6a1103418003100c150100c6c854410709a2a40c1c104c00d010720354034001004207152039441036004204a040451402d50040702080b25486203004407000d12040301d0114080d6480358000d0462071203000350811409854440c010148030f48298210010342c01c201039040112008a10f49001e254070100801825490b48180259504040c100b41d270306020300100e90034003010510400d8801c000840240031040010310004d00805d2200d40d4509100c1d1501e48141460790300304c440076098a03100d90820000b551003075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 96479127 1250 96477877 96477883
    0x9110103020a11030a120501080129030c06030901021213030507110d080c061b09060910050c07030f0b070c03021504020301110706140f0c030103080a0504050a0e0a1a030d030b03 78
    0x8500c0c0f01c0c0d03d10000410700345040c0e01c4544200c4a41c00c640040c05143d03a2410213a00781c2d100c1d01000c0d00003000e02c0401800d84800c842010001c88009002d4544082d000000503959070400c076440c603820b9400041010b5852412002d01d5800000f02245113940c009075103000b44103001b90a8001c204820032840340c807041c0d5031910034081080d4000d00c1e440d0f0750040780d0289515904141d640644c02400e03401d490b0364804208099440d10342000e0002c1d8100100305081105403071140743e0f03000c04d01c0420031012204001c01d03c1210061805441181c82c0b03182c0e00c0c0f404601c51040142a0820070020000190010340d0105140400104540305204035858500001e80142000180150a1780e03000580204020035a0442d14000303c1e4040100240d0b991405100c0042c1c000301e880701222081000140005503441c030180481d0440c1c2c0c034200317041503160004101c01072903d4101d05170b80c1020710200701c0e000d4421300607229480c1ca610300341a01050000d0101e80d80c2d0661142e44400d00d034880c0e0300d10015441c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 96480377 1250 96479127 96479147
    0x30207110604030807050f0c06090613241106070806010806010e04150509160206130f02090106050904050a0b0306070e011403151008010609090f0b0a1e0909110103020a 74
    0x180520b9030340c0e5880c6445401507100c0003013100d15000d41101043d034034101140b00743c1140c03806081c09141060f0b4100b0001d003644603a100c13030401007140f07038046030500400020320103d070400641c51400340e0030510041c2c124a410000c41501e40d00100401111540c0541156048102800c01c130350252118001661043c0c0700600d0b180e002407420041181041200d18004115481030740c20320100e4503815a0610000300041c0f104015900c841d0220308550003100844e40801c0c0075502c908820f4115a0020b407505800fa07002c03500050003c00d60001c149040d12038190441c22800c810466442c10801082d12240010404014072011030645941c2e80d00480e005240303c412800b8940c0c3da80341c5107005c00d8031201e52540050095648808500003d4041d000403030588529454154100b8500703060031002e030404903c1c2d842c4142d00c502c901c1541f52141d02d0110043c0c291041c14407030032004080c01118000d413540c03220303800f1420170320f158012442ea2000071158640030300c0c015a8900a120050700ca001c09 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 96481627 1250 96480377 96480379
    0x15020102070b0906100e09210d020f030f070507050a11030a050105160f0203030705041203110a051b040c0519091d0a05181009020a0906030f0212030301030b0703020711 74
    0x2060b403c00040440108606219812034a02c00304141d4540c2d8070b040805070100e0341c039041c90340b001d6086000c02c580c0614006e4413000150003146003c1c415101c004c00d1381c00821000c1140b84010041c8079a903001c191507682c0c415007070700d0711a0924925850740c41c0d440c10390345030140c642c075603010207528191001c3c000c008001e90003c0c000e00150901c412180080d40079000e2640c0090f001800c5988a42e1020084a003e840c142c0d83d181e061506080c139148135840e0b800c40c100d0034455114500380c84088207009000e0400c0c02000a04070305114181c003055000c02a80c40903100d20719210201040a0b00300c1c0035905818541038102c0ca0307124080c4c400381d07a50748080e0041c01e060000301448080d00c03804008802d00c1025043c00500c9652100c1c005a2541071001009820981019120010074415940401c5146000801c1d030300c0f0b13803076507400c41000302e07103d6810944019034503001c0c200c154100190f0a01d2140075080045245600d16100e2400b0352502914150415400042600030701c210101c3c11090140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 96482877 1250 96481627 96481643
    0x40902030c060708090907030c020a0b1e09160614120a06080708060414010603030e0d06060f0b041403150c0706110313030e0a1512240608011505041502010207 70
    0x1c5400c184000360400791700c4034451501d40001440c164130a000d219480300b0b09400816003421141e6a8031200403004084200c00382c890448200469101c1c4102801406040f0243c500b0058507421b002d00e1030882d80100080c45030ba1403401400500c40b1040b10301d5000304400540503a02d0308030b500070182c1039603805031400d403280c44000300c3c03034003c00f0903035500852003103e11000680306912218242c0c0c440e4400540440d05041c05000c0c0c0b03041003d200350b0010f01c50040014002e4540403e0f031115880c54009035038100000c5404e21980c04000e40f0307600301150032001885610115690800961402020f17041403200110700c42c0108030300c0342c00940b03580d0140700c221070b140d141c49203000d4608000b005c0140e0010b156000c0103400340c140804c5000581d1001403d220307a10010782e8003a50400c10b00344200d60680e81c0e40d43c0c212001140ea5804e903111840d02c00b11111010b180603c01051100c040e00050310414a02a00c42c0d4a2030b0800200e40440302c0005182803c05240f03c42a402806030a101404001c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 96484127 1250 96482877 96482887
    0x13080f0f0903071d070813030807020102090307080c0a0b07110d14010915050105060a020d08071112121b04050d06090b070903020a06050c0309060c01060f0e01060f0806010e040902030c06 82
    0x199090400e1038003100310302c005460b650700c28a01b1141503009403040481c003440d003081035000c81d1180b181399034000524000946040802000f29207043c07026807040405400c800004030725884d040000308014030250403a01d081c030700342d40c440394048004603100d80d100c6c40b1300310603140802011100352552307030500c0002003105032058201003031600d038a814103011192500002140d50f1501000741d07008103915500500d48402800c0003034401c04406013044041c81165604215648001c010301469051014a00ca4441050700d1042d80d2912020b000078106000488000d504100c8000658040303a40445030b01071030812030b0414800901e2202d00c05020117014074100443c40d600054041d040f04e10075901440748550f940401c5409001c0c146200074250010031038450203140030400f4055440003103000041c025039400030640c51540c640c0c018a40390180500400c01207400c01c20780b050101d018240b10003907290a400007070203100001e25040c4a10750b42c00781030003951002c020807854840003805450380c0e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 96485377 1250 96484127 96484139
    0x100f030803060406060504030f0201031a0303210a050603061f15031509020903031b121902010b0103051006030213081014090a02011e021906050a0513080f0f090307 72
    0x380d801210200d006a090410000e01140324004030350440740c011400e842030555543c01107001d007a48412610300036100144917021560280000c0c1041c81042581c441c07100b0181d000940c80200040103031a400f86410304100ca542c402040c103580c03116581401084c0030140c00361058004255801c034100c810380c0d41d900c011030340b9090b5000c035070b890003503112945403250364000030801d03442112640c40e0103410900c0924140700d07000440781038500c1e07248182d4440d40440c041d03e148540090240d44076903040c00e003100781d00355028850f00412001c2840c0c280401c0c5803e00c060390205100b0b10510b810560f0006000821004c1d03090000d001c2d0040f94240c420014840c4a0f0300c01810600704081030b80203250000c0f4841c030f140003800d9824a541a1030700403141301041034500f04994110714110940c06010b240300345e4801040c2c20414054803501c2c0000b854140b0480071011940c2c0100302c002c2198001d1024408501c0b11000d403204201c2d00c030030040d920050940e211075140a9071010b240c0500c1149000b05071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 96486627 1250 96485377 96485393
    0x30c01020a031d1b011404050402070c051306050907081302041b02160f030f150501060305250c060f060e0a060801150303050a0f052703060105010c080909100f03 71
    0x1001010240100911404403d11a01c1c2c1140384402031110300420358190040d4020910426042c800410036800c09130707200d01041c180e0340401c500321091081c0c000d082c0810701d0042c0008003200300828040068034148000314903c042d0140280b4240250800045c0d55080e000307000c00d10241e4082c0040c448014880c44030a14032046115000141c064045100c80003491451000101c4401c008000307082440c40d111041c040c03003001c0301901d400e142001e41400e1210103000e12802401c20b550001001d250203100a2a000031750301600c01200c514500c1c1d5007032954481c2c07088150980203030b400212046010a01d500a01d02c503807100700c03100700040800800e00503642c4006c0c11100000001e02c1600d101c003010300348410680c080200460024050012403510400ba042581202414250b01c0c00506031b504000b842044c45440c0c0c107102c448440c1d1440b03070900307001c3c00b80140f20a00307142641d000191f0314040036025407160341d409481c2030400290043c8100804400034015404001809900e038281612 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 96487877 1250 96486627 96486641
    0x16030f020d0e01090506030402040e0601080703030e090f06130e01060612051308070b040602130801090201030c1b110310050705070506150d140a06020f070203010f11030106080702030c01020a03 85
    0x15025041c00108071a00450000414100581d00d01030290b081008000003908080c00580c0c00a0303803a00201d000300410070000c0d002e090700900402240b403851800904248c02002c03441e0282841c54140b018440f1042c8507190408022a10010b0204104070131034001d1481400402d141e40c2048400598641c0001410b1b0704140743c040c051042c3d560780c0400c1207000c003001000409440303040062201261401c841581c0092044102615051810240c00c0350300d0040d40201e00e05c0d9640d512028119030705803168440003016401c120170881d6500d030a1201c0c1c0554902c010b050ba40a0451000c0b890b03030280080041c500c0e080208001c0c600700400700030220f03080010308071034600c03440010811004542c9028200c0d00d80090400c80c00c0302e281d50f1807200706080c5580c00c5925108040b102070005d05c4a0000d0042c4050304119280c03074001c80d004141c2910781100e0846803441c90206101d0b44000c02200310790540b480c5086c0840f0984401074100d10354487c0c4059038a481d440422171a01075a410340002d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 96489127 1250 96487877 96487907
    0x24150506070312020327060c070f030c0506010f06120b03030a0311120a050412030516121803030c0f030b060d0b0109090207080a030608030903060a0c0905210f15010603020f1603 78
    0x4030606d842c000743d0755206e0302901c0140030204240440b030006001456250252031092a047c9035801103541c07039030b24000003a0003802d91304401c40d40901550f9880180c403540002d00b00e80601450b682c035008030f80c50b40701d02d004000c10540c0340c1c400460005501021200f00c2642c90b40040780b68a00748003004010302003030750201c0e54005241e000d4415a403180c02014010404040f903c00a140000b20a803500e0407030200c0c0e5030145071501d02c6d0503000070203504c80031443c83c00b98401080301043d1490050040041030084014903160030060000d94130b500e4252243d0041d09900000c0790250080103a510100c0e42c0e218105090000400404100c0d506007c0c0c01c0c426110386003030001e1600d03a0740b15600e0b8090113202640603070205c40080d5a90325950400c9001c008176040c820a515240c8000c43e0310044c825458910b011901d155803400c003841000301075106103080d0058207002d184001003080000c030602c5000304041c0c01080700d0382d003820460205d9140c4074280c908403904802614024010078581c2c0086 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 96490377 1250 96489127 96489181
    0xa02040b0c01051b0f040e0a0e01090302010c021e0606060a140a0201020d0606030606170402010e060f040e0106090302010504060e0a090c0e0102010b010504142101020403241505060703120203 84
    0x10b4252043c3c0100342ea044e05c04061103142041d00f07000c4003104083e0003c02030080681c540072040e08a0b8000c0c881e240a02d8001c0c0e00100322a200b10f6806442c02c00c80311072590300b07912001107040044001207101900070754110b600c1d698450104004450001c4100000708218400240e00810789030150f0041ca030030504001c051003041d9991500b40d048030700ca4410240410713000e41e040d00010b0f041a001507442441414001032041081000c42d02d02e4100704c03013462682c00300080030f1000010003500e45c1d0050090389132001c00c1d2825580000c042e03010758030800040c00950741c0c16a9240e03840102100242c104034078201714032403d2140c002e2001101840039400365107451158101780d4810300881d0203580c01c0d50001d5505040311420f02004c1c0040032104107001036090500800c11200307000030310086000e210300c8a0039030b12883d01c1e000d40030240d05030700980c10b00d45441c004181242c101031000312074080350b00355281c40d16401d09071410132403801c1c1000210320000422885003451008009503012409070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 96491627 1250 96490377 96490411
    0x4091202100f1401140111010c0302071103070302030307150b1302040e182a06031609090504020108070c0206160501150518060904021801030c03020906030a0c0e0a02040b0c0105 78
    0x200201c0714100c040c1e0b0011420743c00103104841950000d441c02d00018949526840e049280850841e0b158059910000c0c2e000103100c0240300c0074110784903168500310040c045941c559400070703541c3e12580368001d2000d098101c17a440d2444895100900522020b041d020690034000e507400000d510a0042404c6a1501c00120b2012244071102c1c4501c10341e500014011046840034610003007501494400c0c40c151100048059511404c000d18003900d00c4410043d030030700851001030194541d58100783c001d1490201008003507a8806809500640c0301c0c204542c1192050021800e184250740d00801200c010103d00d0080200560000c0d5654445840c1c101c030b9162200d081000d41900078250b8204041c460380840c00600d071211074150004c0c8000c00c7c004118840b540c024a003010240c0c81507640c0c03803000700c0400a6040c944000c82d80410120050030440e0465a918441d080c001d000c1e0418100152000070180203040d03045030084c00030302085c151144142004203010b018111b951440e88040548 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 96492877 1250 96491627 96491651
    0x5041b1d06130f090f0203060f0708060603060a120b01050108090c01050304060c111608010c09030503160503090409050a020307060503010315050a060902040620030c03040b090409120210 82
    0x1608200c19140303000e2203511003004001c202c555100c00c0310300c9155910204101c0d500c0c02e20a803181103108091a10701c6482d50300406061000040901c080427002004002e680c690100406500c40812140ba03500d82d200c3f41e02081c80e00455802000170000d9460501d010b000c0d241c280103048407426a15607032655200c5c190303291612040c010050105070107001150000d10035400c9185070441a00d0011a2141c085020503d080c1c9106840030300c00d09800c10500c07079187d082c0540c003503040e158208401d4051950b03907081e41c0c074403c50300700581102140d080704007002814411104070705070042003400684910b0401503224074a08600b00e1091045200014000f40a0740549049a80240b60f4004251803401508017500000f00015415942d0b0140454441204c0c4064005003c144d55400103c644120303144485510381380701c074080c0b58403c2c001c28441860001c01c94003510301c410344194684040c1d4002c10080c0080900c0200030400d5800c0d0f10710a0fa50004040402841c14502030000c800700352 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 96494127 1250 96492877 96492899
    0xf05070905010c020f2e0f0f0e100207030803091f0b0d0b07050f040303050c061509150a1715070801080a020f0d05060f090705060906031b07050105041b 67
    0x449150b0100328503a4402000d032400002420003070501414003507220f81c000f40b402c4801c211031459000890403010349004169402020071010f05011305169140c2c84a1210180c1940304461007140b0461944482c44a01031007817000e00010741d44825426142d080c0040c030140c4070f8075544880f4981c40307142001c400c104c55050141e010b09070405400101801c040c4c1d181d00c091403070010440710138002c0811200c4c0c0030401040080c4011030003079484ca0b803141203901a85060a2000c0d010541072001d0200e01503595455010254100c58545402d5490001110200390b6682455104100824007500a0320410f180411068200c0d850098061040d640b4a0707026643c0703240a01605c070341d40e4400c55490300141071071070250301001002080717a105048103507200340c0f60003003c944124028000000303120007548204404d4029090494a4509113a1000003054141c08000c102e00031801ca4084c0b5150404440701c100c50b10301d500880207000902d05410480b07240e024024802c40c09954111001803140052 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 96495377 1250 96494127 96494129
    0x16180b01030605060304080313050607020a030807260a0b030709020c010b01091406090418031e0906020c091b0307030203040b010905040819090518011502030307080408070309050d060f050709 84
    0x13010700d421a1202d0f00c8808684d000104440d000b05035021f0f8900c085241048014450703080c1d5801050003c20f549002080d229018090205000d0300c40e40402034180001e84c2451103103002c656004807039598000010141440650300c9415001b0640041504040c80d0000d02c04e12903460b0091081a0001d801101c5203482c910a9100c04444081840c0591601600404940748000d0010a000b604210700404c44140f0950441c081505042030480070805a046007025002c103052a03174519191050181d100c00d00e14100e43c0c8103940f410009145100029456800308081d0107145440f460400ca005d0000c0d0b10598055540280100000035280c402d4050350b48156030103081076090403802e4041c1c00d20b400319408000d0600101803c045215100c802440900c0070741d8801c240190351500420302c401070115031400045420030002c12207415000444160400e510001442c0e8a10721414222282c2d43d69410031540010445404424031030f10fa0441803c140ea01c03501003005446100040d00c8085803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 96496627 1250 96495377 96495379
    0x5010503060903180d0803180706020115090e030d2d0603080d020a09210201030b03030405090103020d060f060b03010314010b0102100e070e0a0e060f0108060f070216180b01030605 79
    0x10001985415030344c50303040303000040160200d900d0125541d40c2c01642d8100302c580c120700c03903800b1204d41b00b0010b04012040040002c1d000800013000c0051280c10498076034000d60705041d0701c0741d00280e0411b07000c000301d40320440420020002030078003411805011410960003401100144500400308070700c2d10640080b04d50040c8035601d0151340c0e0761044040d4002d0301c4400c1c2804a10720000500c455007500050b492440450250400c20080c070001d801c480c0c8002d042406940180014442034a075494002d066a40484188070a42c00628151000d8038007200154005411f10b02d0001e00784402c20091410b9a00c0f030b020301031150f01b041618908891034500741500582c0028000fa4800700c641e07102c100c440c041001034802c0f00780c81b000211400f4030180d07210310384903a641d14822186041407007030359048080300ea084e01c85540352200c00b950b5400d02508900d40540050b0114008500800000009101c0c04030340b9001103075140c4442c800703007420320300320001d641c14280d500704d0b203604c248240d00a07124 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 96497877 1250 96496627 96496633
    0x1140c0a03030507020f0a0c05040c08040f031b0c060e0a2702030a0e0a0b010e06091605090609190807061b1b03050a080d1a01020307020d021c0510050105030609 71
    0x803054908401400b00039280314154000e440f1403c100c0c0c10180400c2803034601802c40c9088080c038200074801240c40c000701d040d04000c840c20900001446480802c2324a40e09854006007400e4a4068000007240d0080001d00c00303803a40300005002908078810030324690b000c44203401400d07925a0100e47d0708182c0655040107801c8024040c0900000307a000c1c64000d0a0344400180c00300c0864192460921710321829902100c0322001007042c20120365003941e0040302501d9201480c01c00030303031110041c42c126040314107100006c1040e500b0f94807180103580040c6001008421440000034a200a003515401101c045002e9804040391142c000c401503020305100080d13030701e50f0041b075480d84180e40c1082081c41c0c0100e0652407000010840c100102d0004a015800032075840000016110071610721401041d00c1c24038054580b143c1d0307030700030084e2480a60103452030a680b01c0300348005210062030300a103980e5584148142d0741403040011702003000c0a4000400c000590700c1d981010307541c036001c0340c2e941c5281c2c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 96499127 1250 96497877 96497893
    0x1050403021b0f090405031b071701110307030207171207020606061303110a03050114090d0804030c0206090a05040204080a060b030f0c060d0e0106030807050c1806060901050d0c08040201140c 84
    0xc00c01301012036126001d00150380c2000c0d4502220b42e00244401c1000805030f029075002c1c49a48001980c455400141d040200a006039010380c0c03a03d580402810f482c24142d01003444024001c41e007503018480000e903000d80c0c1e0b40b050b103840b911480c54070a40c0e1040c010b11070040010143c0c20000d08903035049910b4007103040380030300d9581c0d01d01c5400404011a5040004584000300041d000d006841600c401c5081549942c50502d10181ca4495200504d80070410714100b8880800e401012002200350155007081c3c2c2c0d101031001090515143c1d500c560f4202d4400107001402e0480030074074074840c0c2e10800003409501c00003410965546145d907070000694020500000c5540f600d00c00030b00e59038001c15404540d8240d0008102c2c210b8000d58130588401c000000c2d00002c000d020312207050a01c00848d8640b1f11400c4403c05003089100c0100320305e004400009428000340c1c05103050750b000f6131502d2024001038640c08001080b0072416a812404280c000314000d20500c4408192100e0402c820002e04103c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 96500377 1250 96499127 96499129
    0x206040506070212060a050610090e0a052205030a090902030103170c0f010509060709080615010e0303070f060207021203250f080a0215060613030f06140901050403021b0f 75
    0x564030141080760301c04244c08040380d41c18000c0c0301481c8a521400380002d00c0d480d10f0320070300c50000005500602040f802c44018031810900c00030098011030030f40b04c0000c95542e08040090312040e4043e81201c4181003103460010041c00100402945000d6034130650915641c502160030b81c0020f0000038440d620810011200c441035078084c2003544515011135508a0018848500719802520581604d07000701080250464101809000030070942c0010041442c09072004240301400c03003100781c10044075135403902c00c03560100309990410350040e114000406251420300020b500c02d0400321b002c0c24041c80c00d001109008002e40300d1900d2114521042041501c60a5210940c41c2c5400c460b50400880010040750545010348000c04079500148030b6102c0201c0c0d628940c82006100a1080e00104014000864103800c2c1c0400c0b242d20514145981c1000e10f084005002044038202e4503180100c2002801c4105401250081d402030b000e0b40c41c1d01028013607000b0b144081064940c4c01200c41c1c581c0d2160703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 96501627 1250 96500377 96500389
    0x180314070206070f0506010509330604090f020d0b09060117101805040c0f1203140c0a0317010e01030c05191a0903010b0909071e05030304062a02060405 67
    0x1030703100070019460259155100f1030408241d0600303a403907500420052001c1d050000180350071000310300501650706a6030a40405404250142d400306805007182c04100f92918001d440182400f41000d111a02d4400f0410000f9040001c80c03401d20343c1000182c0c1d100e4109041c2107401440181c0d01c0e501c0401d680c95101e107013050040d0071700d20303803001c0801c0010b240840036001e2110325400d4140400c1500f02410304020b00360a941000c0049844448108030461990b40809101c031340c10f0400c9040c1407039414907090180280c00a5030100d01136640b03c0403c0580c00300c003410a03011050301c2440c069032200f402561440d024000100701040018041c00365140c00c00b0341c1e0454503000c44244400c0d903101d4500e03010041201d143c0711184180441c1d0b1655519080c003908003402002d80340e514051a001079000d54440141c0304d001609c130129180700c0c2e00615001c9820001e054040c0032a551181e44203401046000740848080404480482c414101c00032542d9543c003907500142800e0034503040c8810010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 96502877 1250 96501627 96501637
    0xb062b05151905040507080117150114010915021c020105100306020f090a030c090e01050910050912190e27070203090a080106050406060503102606040b0109180314 72
    0x442c0d6a0914000440d640e960094500c503210a64505040e03501d410420a05001c030348082410710b811280309000078844e02041141190900c00036084e09100050042c1c60b00101c07900000d080c882411541c000007900003520503c0805500311040b002070b060103080b400c0394400d41e40d801c01301d1720305c0c6004c00c0423640680180494800381c540c4a45000d01560000e400d540140d0300449241000303000810400340244514a10041d10500074402403a210400c5030303c0c0c408620840323012a0b6100d0204a01d41d41c2005140040c28010002c0d641c0c444144603030607680e4020b0311060b0005550402c1703503030311810210416101d032032804000c01d402130204001e401c0380741d4008000320114030091140208540c0c03025050002414140000a0094240814042903404507045901401000c00601020100c41001031045030300c81801c82e030400301d07014050802c4a405207003605203403003048180410b124003110a24100c5a00a070200059803d2500d4410b140c84410f4001e40030401841c8001644603070700300108 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 96504127 1250 96502877 96502909
    0xa080112150c0807030f0213030b1b0c0f0606040b0303030a0504060b030a110312070206031b07020409030806010801150c0305030c0702060c070603060506120414010b062b0515 77
    0x400304803004070755401c6444841003000051a510b0038401c0160305445031484030b0861410075854441c04041e480202009880010286914900040d05c01840e030100c2c180b04000701036000c0d5456903990405a40c6071500803080c2c0031401450b01203091442d0610444100c00302c003034040c50450b6581c1240100138880101700703480040c1c0310100341517669028070a8030f0007184240226a0708121074000d1620703154038405c541c2c620800810607640540e0341c5005882e405122035406424100341090365194030300684000940150805078541d0800d6000300101d40724a0003a0b8495040307a9035040301080d031200b0014444003195040000e800444c2c0b1420007540d210b104001c4191030210140d01040941d4001c280c00c16042d000701900740715046e4540283d070f009090480f4800e007000318280d01d00a00c104041c20040803466541d1801914000a410040300c0e103070010030036901d4441c8192001c204161540c5240ba01c418654541c2e48a41042d01c103260040c400c5807289401081d649040c4188210350351105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 96505377 1250 96504127 96504143
    0x10f06170a0b190609150903080a0201060302030a060f18080a03090318080f15010b0901050711130204140103020f071e05010c031413021311040f090608060c0a080112 73
    0x54019444030f4800a218000c0d00d65508074091070810010080f400581015442d5403100003049049548042410182c942000490b55161942c120030780c0104019413000350180a0366600e90180045039215081084c180b1801340030f010010125800045503034030000381407800500c0410035042c403950100070424884d041081801141e580f49007507004440d84280200d03805150002240c1006000b044028240c40c9842c941d254188141460340c2d00030310118a04015020444c2004e210203a00030800c40f000143c082c8000181001820001c0e42c002e00400304400101040c00001d03510a20032181328000700312000d818101941d444e41d030004c100014503085000000e00300408034200b072056104250007034800040508030b40321003d17080724000740042a41d60b6548401c4d400741e00c030a88090903510040320002203040042c4640c020501450308800000007080c0380c080340140c0c8990100080d107942070f045802a550344488900c040c0b00303d92090300041d5010004104118200001075205842a003030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 96506627 1250 96505377 96505391
    0x14030304051216050d0c151e0c030e0a03020a030f0602070b070507050705060906030a0e1c020106080c1c0803070311070f030909020309190203071a12010f06170a 71
    0x640c25060040350210a4002000d0b10f540c0c2010f401e04540208020743d0382c0c1c415a81651910003545019106002c0d1001c440c4d00a01c1d0494420041030a0307100110041d02401c1d408618002d081050780d580031404103400315044003807032800f9040c08044a60042810300035500f90750b55000340001c030890071a161a000d12017100041e100349074081c4200c3c2c2580e680303515036a1500300076250000c0381e070101e801003000300300f10f03076650300c40c602140c0c0d000700c58a0303001c1600c80214241c7c0c2d1a010f60350070fa281000c22150005a00b490b810341040b0101c0d1000d50449900e03c91520800038000305240c0b8800700d5944200000d0000360280000d560320502038280041c28514a0800034925440b0070812940c4c1c01d2034010f05802c02d500107484001600c5000c90460071490f0044956958141c0101416611a003801d0224210b61b01001150003404a40090856841c81c02c110585a6040010318041c0580c600c40042802c250302d604400031220300c2d58a01230322151038a1400d440344800303004110070540342d01e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 96507877 1250 96506627 96506629
    0x2506051b010504030518180a0504020312030907080f0309030c09150d06090311062a07150b01120b130513050616030c0905030607050903240604060902070c1403030405 73
    0x200b0b6601c11802070304d4882d6981d16a82c03030314910100380702c0c580b84281a0030f11170351605910207644a80c41014140001459121030002034608034a4202c4440034820000800c10b441101261500413517443c0d8080f6a9801d1178200320300d449004651500350581d102c1d17507401d907207443d01c0200c06400085075032440c04184c41410114026802100c000d0301c4407038445291004240d445115441061603d4024250701e0902c6024019031448400f0070001d040f1031182002c1110b401c8000726810755500403c048000000300e00c0c1c032809010740c010341ca800720b034042401420710b9141e070150781d0f15003038001c00800c034040c2c40034201001400041c005c1d0a00c400700ca40f2001c00030342c04004c0e107405503000d011a006c1a0442000003819100f440b21503008001c2c2d0704030204a0780c1c9001031310942045c07440c10800c0c0c803185ca800200b031030300724119420210700107040444410000d51820150051600340c2c1c0a006d40d64807076951030142d1080b40000cc002d0390440c9810000d10303506000341102c00400900340c1e413a01c0d035250 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 96509127 1250 96507877 96507881
    0x1e0b01020f19032106060e060702010903060b030f010e0a060e12030723070c05150708040506030c090d1103100c12050a0b130212100303090e0709030605090a052506051b01 75
    0x4d0590b00c426036403407106000031500092001d03020b64044810600e0000e182d40000c03c2c001c0103100c000c0042c0e03281c04160819a4081c020f8080d80d5503036000800a000403401d0781ea903107020001080c1d03929442c008600902c00c2c030200b20b0500c010030011409245071180c403411601c4905914140c4400003e26031201c000c032060030005d20400b0b0158003001d82d010b04140800c1070000121900680860040000e600081d03c00420b8030200c4004641c2542c0300d54440700c68400c14441c003442c95500200c0c0070008010400000319840c1c0280c0194101c4264010740c0850740b04070340e0301138514008202040d0040501c030400f40c118071380c0020500c90115603140b01d01c0105040e0382c032440e0300304a20b9070003085414160303102c2e40e100c652160202c00218021840d40c0c40181c0b2201c514028150241100d50001e2192030088450200656002c00c0c06c210070f181070f44811f5103469110304101c90b28098144007905881012030510110a040741000d0300e0030303107420001d40303441d80400d158100c41c0c10029a0042290000c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 96510377 1250 96509127 96509177
    0x7080a0c1e0b09010507020d0c0f1a01030507050f06090906030f060c041e140108041103060a02040e101a0d0e0607021e0a03020a11030c03011e0b01020f1903 69
    0x100e241054007074082e141c040c00c0e200000f480c10b0040ea02d00b500b0042e0742a400602ca50325612141010403141d01141417140d811454404003030009003047d804880d1081040d01c0d05812a07000d14299020aa103c0041240c11a0408181540240140304002c003c0c80e10038070941c0c10034402000c0304e00c035640241540341002003c49001c01c500e034000c45d04000e60300440901e244c0c40348658201d004d02070304112418548404036040b090402403c240010100448061010109207004003124250b260544045d0083d510900440080c001880c02140004032084480b1098621100a0644030340590603001090f1308100080200300c7c0e01c403101e130304808206201d651700484c0c403507000c0c11600805250000480d46592940b4005502040c26100401d601003150484c0f20307482546441d6000021000034074004922005c01e0340341d46480b0009074009481000b15140c0d024843c02030242403061001a80c540a6407078044403a60001c070140c2da00401c60320030140358548242412004403d980c044100c0700110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 96511627 1250 96510377 96510413
    0xf03050406090509010f0303111204090b100315180209090f0106090e090c060715021c0b03010603020117040303021b07030c090e0d0c05240406060501110307080a0c 72
    0x100203800d008055001a00c4006040242c410802c1d45d407400700f0400d20000144005010000304015204083c102440300c90611440c4000081c0c403a51901c000300e004044207d0b0180c03080208601c2104514005d005080048882074030310000c1614040121604804110125640680c20003801c000741d600d1100d801c0c0100c000c0e0450000a42c10914013070000c0000703401c0541c4008440e8100b1602a50010760444600c8080e181980c884c0068605034481107041e0340e081038914000b0070b08403030f080b40c7e0fa45181028003038510300740650200c000500d03003240c80350700020340003680000340100c040c0c85900207e50802d10914005103842114222041350326205510404030307400c0000e040050180c1d076851040503060740c0070100846001098203556504220680030305000c410324004c000d005050104c1820240d50010a4001b04ca050201c07074080d100803541103031046d150020116a41d4400c80000d130040d100c0900461078503010341c03118401500081548810862000101c2000400014000b040641c1e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 96512877 1250 96511627 96511637
    0x612090709091415190b13050103110102011a0f06071b150315050a030b04050f120405190303020607080405031c020a08070e0609040f0f0c02030a0212070b0c0f070f03 73
    0x3c21050703440c1c1080540f541690381000d14005116032081002101810b0010040f000541c500d40c00002c1040b012650141d004542d20301400002404183c08031403000310026030007005166410045680d00000703030504c7c140c21580d4030401419a0602e07500402026000e11001c1c0464600c080da046503048968101040090b0701102461410360140184000c03c548140c050420740c0c00c2901141c1041d41c41c1c88003510b0b1090040c04507041c042d0910114008550b6281aa408502c9070b10390340d03c043d8080d00c54640103415402150008000343c00c00041640c5d4140e02070600c2d0f8640300012610640d0141090b1101d0008200034101e003115100c480b42d03840103122002d44c40b1118640d0240200f100203090381e040c0001c0d9a001240c070790b1558111450828200d4000a040001e008038400505030340f58408400d51805000d990b5464001000d4110014150708840307013428200365241844c065104010030340071041c00401c07050303e601c1003c0e118a84500e82c0450034040103071918180035509000590202d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 96514127 1250 96512877 96512903
    0xa1404080a051c080114090402060d050f0129041214010507170a02180103050709080a080d1521021518040b030c0310050703061806060f0c02061209070909 68
    0x402c4a1440c83c0000b403450034110215803505c4d046da88004406180d0900c10442e0300001001c541d036880a40e007891040f0f4204004c07615160361400c00c1540280115501c0100b8a0043c8046c2800400f407000100c1003640032506051405003608414040718908032041c0d001f10080b100d0010007485500c0c0b0803940d030b60710b89400748050031b0b804003403400140c10207540134010800916810420781582e48460001e02e00002c4503581c07814111342c44a0039401c0017441c0d0040803455428004000060b10164070f43d48020450b41120200580140042d8400d1040404018600611010564840401d0700380054919440010414218445a8020004150010541c8406010301c0c14070744039501170b100c001d80050402848400000341d550f524002c2e2034060030786920015000910a4010344010040d2960b04000303c603001c0d44a0300503040c00d010300b100180c80c9103440c0501c1c5e4420383b180c14006401800e504e1420000030102c00340c400c40100350001c00d100355440098103040f213110f502d40c000d0064800900e44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 96515377 1250 96514127 96514153
    0x60f090405100503060f0a020c0307031d040b030d05070606030c1e05010e060906090402090a060f030e06040f02060c0c060307020312012313060b0703030504051606050a1404080a05 79
    0x580c00a058200860400101400036850000711160414212446d160751903448202002c041e11402041d12000e000c041180820140c201000305c40404560218502120340b010600084480155182c0c1c1c0c036074000055032110300e014030010020b00d80500c40c0803540644a480d14001580b039540410075250a0420803600314101d440110060102407a00d14503040c7c086000400070b00071030705414414000014020300c0c55459904076442504080c24460441d6690f01d4003030700c841c5001c0c8c10300c00803034180154513400c0ac0d000300700c0a01c1243d00c1103440285801a80074040c49401071389103407030b4a11540461203400c0d035441e0040c5110b40350507801584c0c0e07030203010406d9007003c0741a88a01101800302e52440c0500341c800c240104500302c02e907941c6000c80c08552140000d8150307a48907070064040021800700385a4075800881c8140d00460441303c00784440c07200e0300040c12192003494001902403140590151140825035140c1c00d0152202d03081035210503c2c6810003107078141c1115554401d00800c031794 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 96516627 1250 96515377 96515381
    0x3020607021b1c0606030c1a0a02070306091506290903071401020a0b0103260313140106170607080702070602030906090a030b28020901020304170c060f0904 69
    0x4400894409002c10304020800b140542c801d094081e4803c192071045030b100040c0c1d90b00ba00300020342151041c81040d0780e03801c26006904050040c51003581021480b0000d60349004101c0c0c40e1400a9401448042d00e1502e41c50020804182c0c101ca610358100e2080c48250041c5c011500039041c4e0010325500c090090465521840c18441024244a810f0194000ba9034003c28541700310b801c0c0c0c0354a00860506500100d023040c3c0d0000004051640000020051000c00300760480c5070f041c8200c205480c0701c1e0f54160030486000880d140c003c00d441c0f901250b40000c03a01840015110040d41c00440d001c2d0702c42d40b0039088540b106180140950044d410861400d45c014146038012001d400607041203801c0100080d103a1165013501c2e402104002100c000e59182c040412004580020b0084010300b40004605014110100d030007440300c2000000c46e442d1300c070070701c02c441813440140c00562600d8a01001c3c05980b00c2d180250600501500d50301c849603858042c01001c100c48402d40d1107540b00e0145c000c0000b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 96517877 1250 96516627 96516631
    0x30625020114060603250e03010b0103050f060d1401020403080729010b07050c040e010f0509160e0604020408060c0706150f0603020c07030c060c0b0121030f11030a080103030206 78
    0x45a04040c00c0d403031940501c00c16241c1003d801c2d02c01507980d98850b0300e20f04200ca60a00300750f100c1d045403c80007003290751103e440d1b5600d99003100284440d412001c01102134540039107000d5071605043c2d000c9515880c00d001d100e100c041c86821a041c04131402a0390600b260090350059406040000343d4200304000842e440c400d40c064104800b0300c3da2407551043e400003505000300c02e014100000d4800610404124401e0142001001400030300850014907000c0c25282c080383d401c4a0811000c04d040a00210399000b00c2448481d850881a2600c403440d101c0d1000038000a800550801c4046806881441600c0c41a940c4400c05552090a80303401822201d00280d5240e0b1a0f119601c00d01c00c000d0000000c1b0110356182c035000d80c448003c0d100c41420f11000d03510003031286802000008400340c00c40054000307540199541000c0e680d90301e240310b0b418031007500000b084040070b500710400280581c10100b41c82445140041c0600d4107411000e01c0d41e40038202038004101290010000c042d410440a0303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 96519127 1250 96517877 96517951
    0x20907030c1704121b06060f080115050f0f042003040c080d050f0d140106021c03020405030c0103020a0210140a1b020705120c06120702010c0f27050306 67
    0x8070319180c03503140c402c1e007949550011300802030500c0400e088a24024007042d000e54001c003040151559485804800c1035451003401441d508000c4141804003140324003104444024020000c8c10071741c80104100079140c5828541d026980c1da141d8848603011882c0b90104903c1428a1a40c80c102400d100351416174642c812380d40c0b944410009117481e47d000040c1c4100a521440890b2a16104400ca00280c040710780904503d0102c0d00001800341d0b4000303a008480481469000e000750310032103045040e40311798044c80b5099403100347c505550b94400d80c020246040b0302c0c8140e07203610002c680c0324000e546c0c50116419142d030500d0180712815202d4442c525180b01b42485129000002c200c002e5158242803054500ca251084001c0c0c150401c28400d40c4460100100b98039070b0b44801400741c40d450002901d4400040d0f203054170b48259103000743e020741088036141e103c1d0030386900950241007540004d070b021010a0450780d5000a940d4504100303807805000a074030000740494003035a0092079040300c3d080710 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 96520377 1250 96519127 96519167
    0xd061a070212030c1f02090d051f09050c10110a030e01030b01090518040312180c0b0a080a0e120c010b150313020f0d080408280b070f020a020907030c 66
    0x110815000003402003d041d80c1600d0742401d5172004800e00024040d00c1080ba4001142d548084104240841d40604c02d084c200c0c285043c3e90304850088040760300228000b04141e0003858110541e10f00071072040c4110084ac9440f0802c19103903800c090a00c0150b000c11400f0500c0240401a5503816002d80702a17002d003840c0c000462032038940011f50744525814084070109039003003c5000d01d4030070850f030a0b100d4031a150078841c2c0d4050540400c02264030800644900f040403101040d50140300040361a902c0c030302d0f681c0058544807214000014566210b28a0840c0b141c84580c041c014051800b41c42c40d01c10f9840002030034034100082c80b8070140484501011000c0030010007101181d50b002641d10250140e03801a0420380071030104044000080c00070300f02d4234000c5800107080340b001510740900c800c012201091401064299036401d90a80001009520807a000561251140c98040600b0500b441142c02142c01c3d0340205040080548411000a0721154401400c0340c011011404480703520b03500e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 96521627 1250 96520377 96520387
    0x4030305071e0b07020105011a0f0706090605010b1804020a020c13090f0804060e010e15090f19050114160f050a02220e0304050604060c0c08010e100b010503090d050d061a07021203 79
    0x880101c9208002450131a000302244803000ccc00031700c1c1d00c00c100840c1e206a003007085503100d8036580c4054002c08007040c046022032030380e031030135042c90b0003a100805044e400401c0441d25403010460b07543c4046180b080701540e104603c001280b10110121740b491701481a0715a00c80c01c11030010095415074030417605010b05600900c04940300e0108002031052903400423a207488441c000900d00030b601108041d4424200303a004181010001928000c480c401d890342c0f00c40140740c101c001d6040c001e07400d2048442c040f10300074001061440c2c88200318640310f001901c01483e01c0307500103090701407400c0d01074444881c40c13070910030640342e144a000f6040000e01700440c2418079110016010b0302c281d002e003108000001d00c00310100011600003201810002c0b00a00c601d441c480c03200c0c0c3c0d842460540070782d0b03d28100b1181c20001d501690860780070342902c00c068a50110300c90b40a5800364032100c07450192665801000415440c0c01485011540905014503500d11040c01004510742948240300780b103030070800c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 96522877 1250 96521627 96521669
    0x6060305040b06100e060c1011040e060d0f0809150c0601090606090803042d14190b0d050601110706030603050601051002030301120602040914061e010504030305071e0b0702010501 79
    0xb9017501d8440c0125070041e03485080300381c801e09003000d007064501107a09040f23040d20b0504440c1c01500640319640b0305150680d0391041041542200050050501000e00c49c1c2e1001042c20b0741c0081080840103000311005e4080301280003e030743c2c0248001941908071100500001c009409070710300900b190b02d46505210300b027a4489072241b08500c6585001c000c40e0141441c031000708140f107001180d05c540800407107540d03621a00441c810707000903e0b100c0c0404113020818074811548041c2074540b402c1d149820841090920303c010003000e0200360601504116180c2075100030421300c005044659030200e80c040c80c0d031030b05518010040e04036174410492800000d601c1907000040d40d04460000d9040075135406603082c8607009100395002944441d00b040c141c1c0c40101600b516613400b03a0b4050390030541e881281224920b144140980d814002072042000b007000c2803040014003d4940102c08001440c2c0701c00c03281c40855521040102c03281200b002c10040b6154081c441e0078010009990a1024120108c2d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 96524127 1250 96522877 96522887
    0x301180b151b07050a1508060a03120f020105010b16030503040611031503120703020c090c040e07031406101e030f0e01050412020a05060c0a05120117070b0403020a12051006060305040b0610 83
    0x5003200c0101f003002c6000a2607035642c0d4014500441c5c0000c010554010403180007030500a0b00307514400990709080002030305001400480b0740c00d041280c3c10041420a0380d4041310b990344080c009580542c0c1b608003807644441d046e0001c502801000b080c84401803007050a250400e2058880041c000406005ea180400d4000c82c0e081f455140c101c0e068401691160160000c074002c030b402c41d0b503080b0911010452190742540c418079603240d0030014900d46070344100412900310b11140450000540868085078400134010005500c0e884604000c2100245c03d4442001c6070480f05200ea100ea44440512050010940001c0b002c4401440688a20402c0362940f56898a0152191148000004401c10a0340c4640191011100464048001d0b541d4980199500c03911801000026006070b85002540d40b0f2111b00300c0f401c4a80c05041c0e0085d1900c0d000d1030905c0d0884460040d99280900e07034940c05081c1c02c501c103030005040c03a030300c0001c0c1609141c248941542d0000b402140140e03400440d9001140d046 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 96525377 1250 96524127 96524159
    0x601050d080a0c0818011b0c09020f07020d060506010f090803040e1302030d0c03020609010c02100b01170c0409060b030402030a12110106060c06050c0301180b151b07050a 75
    0x21120ba6031207120404441d011006403000d01042004110005a81c007008500f00748090f0980c2c8403001c0041c00315941d020904011300c02000c11042c80c10402003e012500a0110001c80d441d0300b6080c901c0580120b040700d03402000803035003281d480b801c200280d80c1108a10001c3c0c13000b45444003019080c09122a0b40b4892402209210214000001c4142007200405003079142c3c00703000d4620202880101510f44585504124054000c2500080b09840140301d0903110010700e500404002c1c19206000700109244030301030307040000f54014024030080c03015009000c1e40c0c0300c58116a40b1480d0143c25012034a42d90098900e066040007400301581d8002400810139030020950031b851001203d060b40c810844050138001d65091080c0015070f29040002c0420060141c00244296918004041820320090080016440d803288003030f0351410f03080e4888510040d010381200000100b81c81c0c0f42410760000100050721031041c8046480881c01444ac0030002d0109486000784d05040100180c2c00c417440e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 96526627 1250 96525377 96525383
    0x60605040b0d062d151205090705090f0114010c0201120203060f040f020703021204050916050c010f0207050d020708030301050f0a17030c19050c01030c0201200c0d020601050d 77
    0x4041125514615143c1c00000280707800f14041034250a1400c0c620805268842c21000c01e050b2000001894a4a121300000c00c60441d964007040003102c1c00c60720000c0401038030307544280c03007800804906c548400d030025015a400104c039495543c540301c403401c40c0c0b0440580281c10031000c0c009400c0184d13006203401c120b0ba000350202503141c0c1e17910000304603201403001c080c56100741000000d942d00e0760b41e0b90040004500903429213150840f411b6070f4401c2c911030791042c030340c00044140006040b041301d00e100302c040701110300d0001c1c0380c45000f804042c02d5a00041d0441c441e250b0004103001044030401000552404900141035605c0c0b074010f26944030b0105101e264020000141d40505075a1081900e20207082d60074400030443d9821000c25690b40c0012814040ba441013250400c0e030324000e0110a41d0b543d81c80360003403500d510920300440141032205441401c1d592140c0d00e200d01143e0440038000c0342c0e2400c8138900e4031842020584c41c58408007c4800741035411250040c441a241e404070b402040360 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 96527877 1250 96526627 96526649
    0x40303080723030601020c040203040c0303050304020d05030301030606060e030d1e20010515060309061b161203060f050a03080901020312130b061c03031a120f010501080106060504 79
    0x40c440344107460030355000140904030b44070003030b80100804444000d18007a400c00c1e803c03142e46040400a1004034802030300c015281680603002040064813400c01103600c144040c2c070550700c100c00c0c1d6030740510b50b4100780c00468080d0740320300701406805e5101c5119000240308400508142d9685880501418a10904404c01140700c0f12203052544c0580003565104940011145808402020b03484c0204400d803083c01c020b0b062a07031021400e107024029a4007810504021b00031580f50b01d00700700d0b1070403c800c1842d0a48801031110714034002c1c000c02c040106600402c1c8207003c013040090001e04540c626000b2207d0840300450601041d1074908140c07003a664041c444e6070b86d1390f90000060703103903006800508481c8002c05042141c2c02010300607491000e07205030000c0945456040c10004c0c803020000062b100036a401d241200407e2184e003103500d0381410085650015401c0f000031504507198040c04800c0342d480409032031b0a480d8244680c90040c00c1c228001c00100f070425000800b14891449801c440d18 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 96529127 1250 96527877 96527881
    0x806011d0a060302030a05011d0f0415020a020a0204240302060d020c191101032003041401021812060103020105070f060b0603010311100e01050f130806090f07060c02010504030308 79
    0x11403200804059a4010507004800780e48000040c0a980304035403003200941004000176449062140721050503400b04e07030341c03030841e03403822100c0c5a9203100420036181c107048040d4802407142d040c0b00134a1503070940e501401c40c0c804a8010310042d50365469212980c010002c155401c500070101040081c0c9030b040314035590710000c40d80181e01a01610700003000c0d9004c2c8111910a440e480c40c1046407661017070f41b0003c698500c581c015001c454032218200078022a10200c80500300c2040011039000d071203042d82d10030b04000c00064508a802c442c401c1000c10741410720502c450300c1c105881d015400f50a0006003490340c11580000c01c5806180002808050b140255104201e156003009a10039005401d40384c0301d42c0c0d242040c0040650201c40c2601580403010f80000685c031030800c0c0100f8840686640340f40008a0f404808203502c1441c01014104d02d0b9034004c0703030f01e0300d081c00f00c0e50090030040024109400d461601500b02110342d40f02c8020700031031030500700050360070070700341c03400c9a40509210b031a036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 96530377 1250 96529127 96529157
    0x60d020f010f11030a0c05120a08010501081f030303020d060506041508040822150e030a1b09110c061303080406360c0602010c020a080306030111070506090c0d03080601 74
    0x940d0040300380070010300001c5405074017958403135032000c4894010821507a1406003504030314114854910040c0020703580e01d005010300d5004102180d0401c0d0448405404078100f208116000c2d03d16420460010f50001080d080310301342401800f0242c01c0869184c3d151030301e403006200e0341c08005422141400078950004040c48801000d5420380f2104024003100042c2d031782000201440140102000001d02c40b840784402c0d81300317111501a080000d03008114102c525100d00d26a0040c010500320000c004050201e001035580c000c480866407060074098440642c0c01d040350030200000c0c40388030095079640c070070008a0350181005803c1500a400018030010034808498410504d8021543d5032010741c444a09102c210908503141034080c11001100c26141e400c12401e0314085141200164084800140411401c000841c0c024100900002e0420006403245042d40c2144105440c41d070880c600700080000244544100d171b500032a815544e41e51955001b42c0001d4004d40102d040080b01c451035506 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 96531627 1250 96530377 96530387
    0x216150618060806100e0411120d0503040c0501020609030715090b0c0a020c010905060a050f0c061006021903050d0e010609020d02040918210203092205060d020f010f 73
    0x103040d0401c0c04160314840905000d01400451040081d544903c0002541e404003880c00d607029549100d007896150b44460b01d481030000d10f803030102a44000700c81501c1d240548200b218070004440f44c1c075a203440b440d10b82030003401c0ba409a403100341990402010401000d102100315211240c0c80004d511038045c143d2418001042c907040002e0134201c2035014000c5114085024004a002d00d500722070300212000d004540c44e000910506401403003c0c0411044e6074000c0e400383c984501002e681c44c3c1030000020910b03260031005e54031014018900d1009000c0554103221500ba11a103070002c0030400d40c6282e400602c244284110444a5a42c0300421a40e0460a400c2080281544081036448107541780752040250701078070550800c6071521001102009104603907061250300070000b6010b04400b13403603c0520342c290300c1420046000402550700ca9584203000c0e804407841441503058051100710801c803c5490280a403482110401da01a005946180740054118000c2c80c0c00341c0182e80c00ba02c241d030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 96532877 1250 96531627 96531629
    0xa08120405030903030d020324010504060e060d060b091003112a06040303020c070e040510090228090c0e0f040c0507140309090105150d05060d050f0d1202161506 71
    0x140c1341c0000a0058002c2000b80c0155004040c02440b00d045640248010b06401c82c00a060502240007031000b008440d0240c1c8400074040c0b8058003092800407548803400845100350410313114100b0200d010310049c00c0051202c15004180d0508000120b1900d101d44000c1c09402042c40442583c40c0d030301030070aa44c0c03484040304521100122111810249400360113900846540d070001c0c46403680000c1c107404007981d014025a00f203c0900300800c000104034019240d0584141e030080c1d80046040c0909046034000007110300708180e41e5a81c00e0400304200251601400d01900308000600c2d58011903980c000e0011001d0002c42d4006034505421000b543d4900920300058100000d14030304550100300440140004402240c0490f0031381c0e210004c200f141a05c000c1c24000034142480309a50604403030380300035084903001b45984031004855403101d150012411080c0741c19003000c00406142a000304081000641c2c1002c04d40c145000d0102041e1a2000c000000d42440c0049404140f00c84c4c1c01d80c0200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 96534127 1250 96532877 96532879
    0xf050906060c06090607030c0e0d020d06020903070801090201021501050619090512010f180f0b04020d0f1110020f0a0b0a0204150801150504141018060e090105030a081204050309 78
    0x10340b0b1441c0484041da05e0703840071120403002c203040610b00d003095841000c1c60f0984d90002000560f010015400313005501c01020802c807940d60703082000790100d640c10042c00006002ca20004210303402d6034400281082c1d228103406110090241c0180010b90b5540196040b0b401b4000225500c2e0304940801c8812220540c46150024010b1207042022001134012140d0050b901d80244100c641588004510340080c03607010300181c030b8004c0e20000043e40902d4103a0400c3c0020300448580e607880d100c00800d100c0102040369034111806024103581082c041140154142c1c0c0040c010042500c41504d450b05c7d050080104507e0400b800924528900d40c141c4002d0000a581850031680782040500540028040c092030321040c010340b661418400c10488040d0786140d409180b04280c07810511030f210009145580a00034561540c80b20540c80214000040000d0b03034440519100c440140110544181c000e140281c01c02c01d503a9000c504078104560904118052199095607281440c074210b0064440d40c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 96535377 1250 96534127 96534133
    0x605060102010b0a120201110d05030103021903020a180f09020616020a03080a02060405210a0c020f09091e011b0c05031308160501031506030b04090b040606080105060a0f050906060c 80
    0x12170700700100c1c030900c1d04481c800e0300c500d81f0b18003070030307000341e66803003624030f01500085080005000500b00081d0403c07030742281030b8102c09a0358507980000c0007502c8542200284c1c000e02c1f90102003260a50140c1c200340450703020100f0041100e900410000e03c80c2d001550070302d1181800e0070f011900d6000403030004503084011140c440620005c02500d9404c15a000e40b414410300da86511084c075464406031141440f06005403030585036a5080d1480c00c2d00d9030003030b40e21510000c103682c1c0701c2e1900c0c2c10303140c410303a100d00150900103c040000840c6508110a10920f0313850188482c000208001820b90981442e090040d500e050f00c1c0b5045103144541c0140400e00c07090007600140010002950000f02081d20308403a0109272a18011002c5504a05942141020a1104100c558060380c0040780752203003c2c00114180c250b540703038842d009030140c80c1203a01d81c0e610710f410001c0c518203210356604500222250001d036071400b40c8443c4a0b42d000c2c01020304c02c0e0700310f0b40032426540e2801e04031008000c0d20015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 96536627 1250 96535377 96535379
    0x703020703062f070203070e09030715020c0a03030f0501090b0d11061b030301090606050901081f090e06040b0606070f060c030213080f070501050f0a110a0602030903130801090803040605060102010b0a 88
    0x4443c1e0590801c003000c90080c802d160f400314040d020102d20310310809450005600700780e842c0d2100c52034131640307601c0c00c1c4d1059401c1101c0302d441e8009120001c2402c0c0203031400b242a4034002d9003d012a80140d010f100207628185610020b0b0b510086484400c0f40c0160684840a4650300080c0c402d109003070400045125203090241d0006010010f0360482da00c82404201d007503624001a134051080021550028507884002160043c0703200900c09684035002609041c41c0d103801a400840341214403050031640044100410030504611040e40544107540301ca0510f101c07035a07200c1c0d0500c1d14050003000913495450302c04100e4403950648200c0c0440d900b107094141d6440501c0382c0c43c1e0921081500302c501030054081895400341040316640d080c0c1c0c90215140c041d00c1c1c84200ca03080d0220128032254040c880306000481d90a001840c06074107080040d590301c0300703007541e2409010030652101003103905040404002c07400d0a01580da0140e0400d0001c2116a11400102d00600c0d48001d0360b40c0c002b5807580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 96537877 1250 96536627 96536711
    0xb040f090b0901110306010f050a021203100806060f0117041b0b0702090610050912100207060b0102060a0905330a05151c030e13021801030b06070302070306 69
    0x440340d0007036855000070403041c0c01000406005110403546d0034003082140da00307028910310500041c540c4043c1407040d80c01c585098170f088a0194010b0b10008040c186441003402040818802c403a0080713030403175808051101d0341001a0400c08001d0315100b006800800007018001c0001a0740019121a031500c44043d0711600281400d40088070103a0003010700800180290901c4086041c241d00c060301c2d10350a241d00d07442001f0802d150640408100c2c01800d8120107010751500103490300e28460301000c0350700c00b16013000902d040c0c001019011400d05194841e00841ca01042c0045016103407011000d1180d6940b80301d20044220400c00c007050154141003080030246d0342d1000c0e00a820003c400d02021140d2000c10003e458800f07000ba910206081c2c4020001e80500400c07441e002c4081c00684400d004982d0f29001ca07003201c034050b0b04c042140c6000c1c920365a81442140d40c005412140b031803d1a095881c0259540c000d4000200500e550f28a0b0104d1000701c081c03e03141362040c0d00f01c3c0b1000000c1c0c0107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 96539127 1250 96537877 96537893
    0x3090b040b0a030e03030411040c020703060e0606040513080708090406180e19110f010e0603150a2c06031606030b040f1e05040303021201060804170a050d0b040f09 72
    0x10300310000680f6005041a404c58048100d174000e98014001d07000640d000010080109200344014040d44604200040001c00a000710610307082144040c194600e00f41b8244015503a0042c801c001c80c501c20b80d03441001403403041c00e0320461364000001d0364031134401c00c020800418030f80c1c014110004015004158050258201d8189400d400d030640f0351703080e5000e44d403c4210813031a078000c0500120a0180013581002c483c103601080052429010600c20000468190391040e15a81d4821041101c010110304260070588020300d40d4081c0341182044041d002040503007402c030f0601d0340c2c0d9074001c0401e07100e98082000c0c14010070070343e4030013210f26039440303010340205049000d06000d00d08100d003004610b2154410f00f16402d80d101a140307040410034010314002e140040c0100c080c9035007841103000c0d0001c11074409000c0c0240d512040c4243c14141002c0002c56141054121004410030807960030541c010152240403054803c0071031740c0450140001c01404011901c5805140703492010028407010b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 96540377 1250 96539127 96539137
    0x2090103051609061d090709050c0307020d0c0c06030510030204062907021005030403110a140f0a050d050d06030501020d021b0705030c0d02060909070216170706050703090b040b 78
    0x105441c0b20103955500c07007150540d01c0501c180c145110741d115245c483c04059000543d84640410203542c099038551045c0f40403074405031004031858030080100420749404012030890007400d405c11000014065031403940c05d0089001d01c004064a0300040b6181c0c031510380d40e00003d960b0007031050001c1511402802c500c0304500300003000c54049047c080c003c1d80a01c4007110300b4140c010b0480c1401c6110306000340c42d03a40c40680102d0820401c95280040c1d8003040c40550745180c031031001201005004c3c0c8685191a10b107410080c2141c00103040d0000107600001c00c40706e080c0301810301c00d032621039051140005114690001e030042d400000c2003616140e5941c000d103102520803401101c1000c852a185549003407a001d003541550240e40043c64034604205007018091000f0050b9280082440104c0c105160941d44100581d102c840c09040d20440201c000020b4000034440795480180680719560300c11152085809104001030140c0a051103039441101420241e0b10960303031507503584a08000340e485 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 96541627 1250 96540377 96540403
    0xa020109230d0c0c09020a0224190509070302040b040e0102190f0c030f03021606140601030501120201140702030c0a03050307062306010f0509210c01031b0e0d0209010305 75
    0xc2d280110b211a001da00c090100a070400e689507042030908038013000941c40003c40e035041d40300740082400314007910070000ba07110021070745150942c1464510490622864565622480d05007410000003c00015150045940446001c190800400d010800030b01c1c2520900708954000507036240030b507000c40803140c0f00305115980c80c15091911b01c000c0b5003005a55000400188003c0b07001c1c81e40a00c00d0300980045d21031440000091603c1d6030310380c42124a090100041a54114200a00e0350380610401e8018540549904030403401540000e00360100804079582c0761030086144000d64a0401804105400180855000f40c0c2c1703a080c07466481d04200404c40d0a1070506c4202d561700380a040c1607500d003281c900450700b40c540f01d0400542d02ca58000680500f000024080400d5960b220a10540a001d00c0c4185859034035040e0703903060070300034004806818141803580003000c0c265100f200c0465200185040c2c6280e80413000050040700740b9003070296000c046200040140900860700c00d140301d070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 96542877 1250 96541627 96541633
    0x2040f0e010204081e0d030c05040b04080c03010f02160b0a020403060204031a06010302070c060e010309080a0c060b0612070809030706090b0702010509060609130302010e0a080a1805150a02010923 86
    0x1807140c550841c43c00c5400045c1407a401964420120341d005e41c100d20728009840c10082d05013078480b0341d0340000743c000c3c0d03000151340d51000401c6101820284201c44090104c06402d515240d0b40b84508840c81800c5140209100080d80c005481041e5590640307014691003d8155503542e030b2800c0400b4104c901401030095414644007241480d8040d2084274116035008000c0030556282510640d241540c0540060506844014950004c1c1c01c10700200500c1009844480745440740f81401c03c04c132004d00d121103002d010100070420100c100e180e52554405102c2c60400b0384c642d1403400c45411405458001131115080103a0242000100500345110348001c0d40200f1080d980d170303000c440c2e0b95041a00d500303400c240d40d00080307200c1c405030a40722104c0340c1c0a400007096804000c8070075803405100c140103640429020400c418503981c0b021401c2d01c030800789404280014240b07400101a1414200384112585000400301c0c441c6000303401090289400c90646410031810501c2c00400c8007445a008007680 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 96544127 1250 96542877 96542893
    0x90305100e0d050c0c040203041110020607020c01020a170f0f07060203070806190302130212090319050a0e01030f090b0403030b100201020a020316031107080114010902030903070f02040f0e01020408 87
    0x500c1a826200500140c80080c261175504000340002940060030036160301940050002d201c0d05c4100c80c0720800740c4254010000c07071038a040001e04000421014038115007040503071201080e803009c0041c3c9101035040215079914050304d04900740d4440d00c030941440070304c0841c1c007405005003070380034604c2500107032255010703035440c0c00070040c0c4203139454400c4d12204d500302800e00240c2400c803010302c200307240c0090051030849441c50b0040916411188a034050f4000070352448229203030307a02c10000c0750b01c41c00c00f64180003440d4005411501e9a40d03030a1304140c0e544030380c0920b2072440d0700007102c0240c00c00e030220381324200b905004014040350001d0381d000c0c10320741c5004e2031f107148140300315400013805901550038402003040889010b0a612016001c00900495901e8011000c1c0090b00c0200718a400004010320450185c401d03140341684000450752051003000000c000c048121007480b40d00028020031404584000340c001c061410511200514000005115400550040003a90703000405c1380c100c070b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 96545377 1250 96544127 96544153
    0xc020a0b0405070503010515010206190b0d0605060f0f090705030a06090606050310080d0507170f0406080a0b030a030c03030c030f0c020f060105030105060a0510110a030c060507020d020616090305100e 88
    0x1c0155007640340d0041c1e2002000074000071110308860a00cc0b009840400c2044403080000c1d00c1070340090301940c610703640e00e080c4005071402207a409078009041d112100b035008500d00040d052140286800c041c060b00000081c0c031001c299103c03801500303000f4020030070582c80e00380040c103540084601d101d000c240c2c01d10105600c60002040c226188140e41c0d110b10301240f030359032101040340303200c0d40300c00b2040240080c40701d5a0000d0080d001030640e90b914140589081042801601d500c0225280250002c45698010076031200300d20b84c210780c02d03080102c0c8a00780c800007200242012184040080e14042c0d007003840301d0f030100b43d40085010b80002c0740c820b0398960f420503007212003d0b1002d9500405a010410681c1401341c407802a540301c0341068050315030000300c12400c0400d00f002c1140007c010b518081c080120131703c20150032a00074070050203020001d00f80a59580e40241200340790b59800206802071501c81e4204802540c0d00c003042d10007180c44015040003401d40a2003032440350007904004042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 96546627 1250 96545377 96545401
    0xa05090c0904110d03050c0304060309170c0d031e050f01090c0806100e13020d02070b1e0a0e010b220605060307020a12170f0403020705150d0c020a0b04050705030105 73
    0x8a40000c1040a9880203d0070091600600c0c901241030180a01007840c618106002501c01818030380c60105440e2424a0b00c900c20800460040030510818094216441c03400540307001c002607075042c00141e80e220440407420302518417811002c003a091a08000e500c104d07032524035048a4405d030051100d0540c1c5401a20444011075109030003a5030f2000c0300c0318507841000301c0440d04102400008982d440d00c1462001c2c0d0740f1417840a650345400103604002c200340d213445154010440b040c1c100250b500300c0740b811012000031303008901c0140c49c0d040d500380200c03007035102c10f00b02c1200a080703071301141140d064034184252000302c46c0c212601c1c0102c0085c150600744c0032207110f0400303035001e040c003405196100d01e40d0310740300c11110040111500460941001e50312482d405103100000c505440c0c0b410b494028034150594000c2e0307002d40c50101c8c4120f4250212415640d004142c000d000c40c00045991b802c03441c00c010712101034541d07801003040c8000d0003804650360b01901d13800d030002d0101e90340b5003086c106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 96547877 1250 96546627 96546631
    0x80a02040e040219030c09020a0212030405031c06121b060c0506010e1b0406030228090302060c0c0607030c0b130b040b0a0e010606050904230c0703170a05090c09 71
    0xe141d040000010b8010316240344204c0c4400d1002c00c0c0381402945a88030803060900075000000c542e907002a08068040d0104805440140505460b5241d81392903580c040c0c9a02601030300206d03800c440c8840e401590510303007015002d0138907480100b689401e603007030032001d05a55021804108000100126040340b2480c50842010b4000000b4211a480d128007110f241100800d0384c80b50465200c00e0441c05d0030900f0041000b44078a030350260700e58040e00e83c052010101c01100313140c205411041101d070683c111030f0000440741c048812035128000408110300f00345038840c0707956010324000b84101c20907802c00b04922825000b03170b1400741c03103a642c60840c02142a101c81e0203004c5d6404507002400003090050360031350024006101007201c0368051150707425141c0640198011a00104100c1c10500341071140d00200c0240800e000201070205903903003140c61f405020b100000500145406c2032601032000d008502001e0070715015585400700c410401460251022982c60042040080451a00040c0d842c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 96549127 1250 96547877 96547889
    0xe0d12020310061b02191d0105030d0f020a0c06090305071208030a0e0c0907200102030408090f01170f040b070804111c020a0e10050604061e110d020c01080a0204 71
    0x100b841c600b00b40707040c0c80b5215a01c60800e03258228090f0000140c4502070f448408500211896412600700310904400450324a24442880ca46100400940d5000203204200c4007442c10320301c801504121089050508045c000b0308002442400010b02075840001d84045a001e042034450043d02c42d03154412101c102c45024207a4102840450200c1c41c080c1d106106009070401140c074444199804541d2203d000c907124800300301c03000f4100d0311950088101d00e080c4180c0c10001c40c80d40c645581e0790351080c0585034945003c0ca120307400c2e400059004a00800400c4907403000442c0a01d40000d800d070240c80304440481c1e000f142d010114a40074041c880380781c081e603400410b0b00200a600d005004540380800810b403107180980100c880541c8030181928054100b01c1c040c00c442d450f2008030800c0c60329030342d88424025030040000b002880d0f0300c1009248192801c1010146410000400711551502580500414018500350740005a00003070a8280c0440a81b1100421350300c451840d4102c0c0150300c20b071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 96550377 1250 96549127 96549151
    0x4060e01080304051903060c0c02010305160203040e070516150b0603060f1002070b3c0a030c0923010e01080105030a0201030b060c030417070503010203042109090e0d120203 76
    0x50006103045c10030610000110310046034000c1e543e44582d815603050a04230300205181452900c01c1d96418040e01d64004c200e01c0a01c07400b0441300800940e03d109a02c02ca8610b10803050100c2c0f400e900c603200302c480900c810818494109040e0411440d60044100100c10755860201007620604088054a2040c04000c1c25419900204000d1003801000c0440340c60071809012400300303210a900d0043c20031410a000300e480d41d04000c41a03010700c5012000c0c888892480c8202c21810000d4100840750200498030300807460449140c01501e240c496600041042c10000c0e081c0b401a03424000006034a0740c090f0b171110301c084044801900c54000c00e0090b25003541104100c4000755010390012180518090b05040c5410034a020b5203085820540143c48040300c4c2c1c0116480c80344080001901a0100701c0c021440c0d410660b66480441194100342003a502120180c3c2c04840c2c055540c95000f0421000705218062503240070a8640241c0340c20398003c80c80d14090451103420500c00e0743c0c85a0b4085d481c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 96551627 1250 96550377 96550379
    0x7020105090a031e230606270109050415061a071106030a0608060108030f090f0d050607020102030924070c080d020a05030402041116080a02070f0f0504060e01080304 73
    0x444040d80403101c22508441c1d526400000580c020060810700c40300346000603091180f42c94103c1042e00145041c02c03c01442603098503aa1602054040d0809800c0325948500ba5452440f800c02143c80b00d07100c00d9114200e000041c810362503410692180b481900c00d24a202504c0300c0e4401100c1160140c00550403d0039102c40c401c14241c030040c88400d0003100c0a03003501d031841e07001407540c0d8000c88000440301d4440308101b1280f0000c20116014140000c003940c200b100303c440c4210396000d20b07440c1c0c600c19081d28181001c141c56000944001c44c1d0454161011898903042c0a4041d41c42942e010310544600100450482c094021030b00120070790381c0500749561982c01048445011481040e510704004000d9031049603050310080603002c04680714203459141500410085420f401d50b03480c49100c0400245100c0c0440c07000f0407401a50060005403100003150040389001c41c00d41001c0e4800108500101e680c40c6ea080000b0101c1c0da04440c1407101c26200d50204950f04421b2045100a602c1840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 96552877 1250 96551627 96551629
    0x212070f080a11041a0904050c0711040902040e03070f02010806060c0a1203060f0806070f03020c060a0914030706140a09030f050304020316030803060910050f04020c011803050a0908120702 83
    0x40255070f410401e042e00b00750302c40705505030b4024400c00c05004810006101a01d0341450300035182d2007803c001a003824505503481b11042a051300144902c1150380e0348052003150703500c0d840b60108103500800c8070b44420691418490419a0074000e03804611401c000947c03500e00300c800c130b0700c1c1d06941c000a01b04004c5540d07200c07085480b0b403c01c03100074147c4454004c9010300180741400000d0820703100410090600c5600a05440d540c0e50351402054010400c8100c82d240c00241c0c1d9400800c1150001003904036410300300a0300603a070140d15190f002c001002003c0c032110380c000c22501c08640241d1205912a5140c520848901e200b004010038100c0d42e50000c00341c02760000c0c541c06800541a100d182c14404c40c0401000501c0c0c004403450361000c002e01000d070602c199540d07800090388070071550003410000018052082401024440c40c1c000485e004405000e4101d02c449507800300a1a40d0a00783c3c0c03a01606d550051020800000d076840400202000009800701c40d44032100350700c0d40746c803030150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 96554127 1250 96552877 96552881
    0x1504080a03080a0b06030408030f070807090509130b090c030708010506030601031b120b07030b010c05060109020d0608010c110d0206070e100c0c0b03011d01030c0521030301090212070f080a 83
    0x303044200f03580c0d88a44482080c0c41e101c0041d0710032481a088256640760014040d0b111a101034115000c0180010400041300e400104003020f456080302c5901c515964410180c0c0c4a5500100003040d4080c0322080c81020040081c501c6000c031402c400b5501c070303136485610306400c8500459500354998051401040480c12241d5980b20074004102000b51954582903595541007036150300701c0707803a40d00c1001c00c00850380c0342c4500c0c0c5010301c00b440d0180b03c030549a1281c580d2030b68103001e00e2010b280c2c0041c45c8485000c0c50b03030100d8000c1c15010b000380104401e4900103084013003074070a030826500802c2c010701c0c83c4901c04240c4900c11000d9840d81c001c46074900050181341d082c2d0102e9001484418040d11f008140c03c026110b0041109030403840c5da940c188651021a0807105198401d0100385000510004400c6000d00045e94000c0d250f2000000302881c00200191060680d883c95010000020440d40d13150307001828040261004114161103980b022266101301168201c00500304c0004a01240d001d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 96555377 1250 96554127 96554131
    0xa090e0a08070503180d0f0615050d08070501060b0c060f1509151f0203120406140109090b0606040e07080a061502060405061510030209030114040b061504080a0308 72
    0x200221454a1510768507440507902880c4103450550000c0760b00c082c0420940c0c0400c03114981170301c0150200c10156207035200032400b54001006a80c44140301880e40c1c05082c410401000004e0038007041c003509041c440352641c08050103a406d542050404106540c1c040c0460340d03e0030700c45c030003070034155940150140c504402170040070710700701c401070050b02aa88941d0200e004500101c3ca01040c2c0c4120001c00188207100c051043d05e508401d00201200c603004030940d605607404d110042070981d00c41c5040e030b000700401c8072102128100cac0d030008281c90305158050700b07269200b40c000085c0e64442108008042c0114800c5030080264200020f40c3c25100f04003464100d80781040100b0307410307220780705000303803145903445d4100503403042d01000305010007003003140e0300402e40d4040f1010b101808070206060520070442007050540000341c50440760ac007540000c5034198081801c8800d4207051801031614030042d6051442140e010340510f10b03440082c411142120210b50007000395807400c0d602900c0791000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 96556627 1250 96555377 96555401
    0xb0712020c130f050105040e0a1e080304080406021b0d060902120303011d0c0901020717030c06010e041202010c050301060c0204020c06040809010801080601050109090905010f06260c0a09 82
    0x303441420381251100904410740728000000890340c03901d100f018600300c81059220a11544c20700504155500000c64404100d6420103003150300324a5800c0c561807a940c8079071000f4552000002040305100ea80f40c05401a50000e90035a28015030342c1c1b10131195103822180440d0300900c13200e0700400041c1d1545c032420302d02c0d1001d40400d1400800400c55811908241c0c059a020400d1410031180c00d414502c000798007400c0c82d413010f8205041d40e00003d41c0c030005401003c4408000d0780d40070104003020025150b100d001c00044074aa5070f10b8500001d802e0300c007a18212404c0300131100c0340d0440e42c01805001299401030340e4090550b840c0440444124502ca034090341c01c03c4d820450310090040500001d0b00c1640034110f6180d5408401000401c4000b05a004000380d4000720011702c42a82e101d24150102c0d0cc4003540400c07070041d0382c10814010034103c9003c5c1c0c4042d01c1d00c640000c5801840b04440d0300102c50420210a8000c0b0410715625003003015805540412030002c18410b000340c0c0ea001d0518451 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 96557877 1250 96556627 96556633
    0xc02071509170c03100e070504020c072106020a021615080705090103060b03040503070c050306190207140f0c010306081f020706020c031b07090612030305041103100f06050405010b071202 82
    0x1c4064082070405e2100d00d00c44000d107440d40d048403800003003008854010b00040c0c1e0b0031071801404c401510307102c003a64007880c90310322241e6909607401e98510784041c00c0141c100e0030840d50b4565000010703580f0070116491035031a881389640083c0e0302c011603951100e40b5046880b034052076a0355503805ca0710765000c54100c505065030b0344000714001030b450b80a50b204902c0b0740b004690350b401d1802c08160080503a48a148039a01030410040d00100c440d556107901d000310031015031903000c4c0e0f192600c08003000040620301d038811400d000680c01e40000742540858001e0704c0c10015151034011041d1154420020704184051b68240504c07a81d1255009003001f6004020050408045e014910300310350003004001242d00001043c042d848a040c13002c040201498802082201d107054201e9a40c0c0c03102007005400e0669541c0010140641008031004605009081d13841210000b0034110040213803224620070a4900180400c407424503118443c10707078454404031750500a1650720304144070025030203402180 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 96559127 1250 96557877 96557893
    0xc0a0605100b040605090a05062502130507032301120305070510020a020a030f08040b0103030e0f040c11150105010c170d0612140a03141308060a0c0207150917 70
    0x18460740c010f007000d00752954030300b03070303640320240c208600d6003a95040103110303420422400e807004d4484c8415041201104194402c0a000e40c00050304a100c46000401c0d018100010044030b1685680254021a5140c03100890b0703aa010f0035082c2c0b5807409000f04546c3c00320303507842d45010901506c080c00107588150308541c074101c019440c0e01d0580c0c0140044401680c806031200c070406401500c1c5c809107401928001c046454580c0316403086034010303c400307001c0c00014540324015880b183c0609102d442c02034000c0c860300302440c10083c016600c07030303076030780348601030303c01214096240501c1d1035040301c00503581c0b510401016111181560010740610160202c100091000030b031460081c0030003002000c0c500403e50400c0c3c2012010700044144489203604032030980f000280d04414090560300001d590941c0b10484e96041c40340b84101c54008001c01e00c51101003006c951070540240e00060091b500351010300b507440c0451035a10082c00096000700e03909420074803801c0030400c119014060044111001c00d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 96560377 1250 96559127 96559139
    0xb0310020d09020d06051008030c0d140706060f0f05031b0118171507080f07120608190c0b1207030b0a051903030206070e030a110f0a1203030b060c0a060510 69
    0x90100132001c4480c59160b1080010001c9600c036120000c2445801451a00c403903446071507141c005810040051007010030f5a010108041800c1d41c01544d44030348108415510707501a40d040728864450112444890480840e180c2030203c1d00084615100c1c0d10780703d012620030019510034000d660344038029820700702c0000d0812080700445903130001c1c8001421100e00e46010315102801e0080130802401220b80a005103400618401d56000070945000c0c25000c450540c40405003a103944003420301c2c8260a6088404d0008440500c2c1441c490f10030b4425a96075020003101074003a644c141405000801c0c0052503c90180c0c1149a00000040a803034100d0303110310006d246c0064080070102c02415243c3c0c180105601000313899003000d843d041454408900d040061b076280c0c08160001c1050b40d02e9904040c15407110b40d100500d29000800c4040c07140d45482048090b40f00d04602900006d00700258080316003040012101c4151010010300410003050720b58030040c000281c844108900300307180000f82 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 96561627 1250 96560377 96560389
    0x40e010e030306091819030f2c0406081519050702100209030a06060303020c010207170c12010f060b0a030c03060605040e061201020a020115050609031c0909090809030d030b0310020d0902 82
    0x44100c200c1c0310104010a414010948c040c5807811105020700000f074122200c03611545046081c1e006034183c82e02c132079510301103030180c40307242e12404c1c052083c2d85002c082581d040e4200c03845907800c989020101014250001b090395420380f17102025800000e9a0507080409030010140c41c0f0010713080380e140a00903500d020499074194000d07801600706051603051580d040c0710242c0140f0891052240300c2071400782045d02e0714010341401d44180e100e42d038000200c81081d0031516070303029405420045180d03201041d01c45039206043c800b0000c0d01e46007501426074000d104540235241c282e0341c0c80c2d091034100500c1e0040c0d0080a40301c140d00900160424040b07500074001081268866800841e1034005250100b4083c038258005501c2a0000d00410545441c00108481e011617403c1e64501400324469041e2504e0f425034001c3d100e50743c1401891002d0024800041142c40c034150116000d070480c4103421412144030008455050f0000340b0003c01415041d00609603071900d45c000020111010390000341 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 96562877 1250 96561627 96561643
    0x21207080709211104050402010e0402070507050a1707061b0f0204090c030804140f130c09080706020a110301020307020d0e01120524010f1209081c0506040e010e0303060918 76
    0x203c004084146604000542071410020101501c0c00c1c001814540e002030400c80d890181540580c3d4081030386802d11004000c0c0030020304001e090501e5198032901c058406181225008886100309540015070358403c14805403040100c00e55580f0301119507640036007000302c04032f05a0340280c5171a140000b058841400a0007540305210242e40d45103015106100404c8040e0401e02c40c01484101e00d545846a070048140702c01c40030000103000d240200291122050750b00401c000b41f08408001c91030303a070000b940d042c119004101d140080c0c00c894041500740c0c4811651000140c014543e00c0204034003038080c1c80c20541050402015a0300d10012a004958044030803100016036900e194603203072122070b0846400b22081c40c2413032002d582d6a4001c1c110003502281a10119a01c03e6490300748540383c41a111080d50381560586900d0f4600c244401a12042d100248a50b2400040ae6003c2e0390521400760051013020103075082d940c1d002d00b0400040001400054000c1803001741d20a030305010b1000c84 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 96564127 1250 96562877 96562919
    0xf07140f03090d0905030307020f060706090506090105040606090501060c0609150e01090c0605090604030b041104180c050603010f0614250c1a0412050a0209010602150604021207080709 81
    0x1104900e00f28000902d1444503030700c018000d400400c42e51004d6141c66103111555036040c0c68042d40d03102c00380740c80b9009020141020305940190400c0c40400031042d04410b0041e401180b081c8240c91700d50850104554080c030a04001c07614002a250000780b0a400010b030755070003848a5290304005003521802d88801492340c800d00d0351b4501d4490100460100010302a010a00c0e00d5403c010300680841e64a102c1ca000240c5044030329800a020002264002d980c000c0010b002807100702180010240c070071001410444414002e0a0082030341d060075400c2d40c0c1216440030700c0002c41403800344140d5406c4450b120401c0b51480801c4030007920140320100031072081c040030000f1394240e41402c00b14103d0b24035030407503140c00b09420415000442a201501d041e100c0c103004500381c9215a2402d14540340c88098000d400164080001503015008500b904c0c203200007400303e250650b81c80081200300d01c904030a840010310300d5408580800d1141e10069440049802c100c1481d135103d449684211200503054 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 96565377 1250 96564127 96564133
    0x3020f03070e0c0c0f03040f0317070f03030618091101030e0c0315090706080405030708030702030706060f05010306080613141009080901030c0f080c0d0f0e03041a030f07140f0309 79
    0x3c00d0080008000b05d400119244002c0e500382410480c80411500142c800038002d900c1680d2140c0034010648203d590060b400f160340740000180c1c0c50046c0149c5501d00c103544e400f04a08000e0340c0b0004032402240c2c0040e600070040c40c41a20b03010015402000803082d030510074400d17200840b00c1502d0410101c000d81034170488600862404105247c40c0c9951500071a042010340c4c81880b00041000096070f808513408080b5070f403240d131910812461401802030207450b407428100c000a050341c03d04800410b40340c00380da00340040d1341c55060040d80c82c4001d6038118041c040802003d0045060800c03030140008071031054034480b1124540710010754005400c142c800343d00008801c0c2082d07030180300e583e1880b002410180301c8a21030700c102500d4070000a00c801002c147c0014214aa0110340d07000e0318441e0319031001000f45200301c0e020b083c0d42e50041e02a401340e500c6080c03690303d21844841c098030303c542488003864585903a0408110761541c00414800315042040c0400301b00e1005081c00b07140304014540c02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 96566627 1250 96565377 96565387
    0xc08010506040c0f020627030d09020f01030204180b0402280822120201020f0409020c011a10030209010e0a03031d01080709060e0f0301090b07080f070903020f03070e0c 74
    0x1004100c40c010080344050200d00800240120b07004076040c4c1e4411942120007c03a04021184c00385404000c15000a44d07001c0003500a00c0381c68640d00c01c25001c0c0c025104013400c50140d00040d400c0307204600890b141c400d40002c071404a004150002211030780094405418140c00342c2c404c0b09510140aa103100145003407501e051100d90288485038011190000c1035082c1c85000341604604100800181042c1d420b00c1451304524000d4044400c804040c01c0b52a40d00c0740d8400c0390350000c1d0060b079406805035080400800e0341242b000030911801100525242100071545c0f0700b40c000358841400c01c2d061065070000c0c0e40082e580d82801400450007500c400d4540c501c0200140c0d40d0000c1200e10718144804c00c000d0043c02544902e074003080c1c842a05040d402800410006502d000b40074480a51540c00c001520342085040e81c40d180c01007025858440054490a00742007818808441803400200c040008202620704000349480d10b940103030a9032146901c48610f8030f003410084803420181200010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 96567877 1250 96566627 96566629
    0x112210e27010e150102030301060f0305041703100f0504050103050c09091609020409050601020d050307110a0204021911010207020102060402040903050909101401080603070302010807022b030609050f0403080901090c08010506 99
    0x20300421030303c00c00d2007e140b0b150306100d0042d200c84036604007a41059500d174001810003110038000400c0031115030000d5220300c1c005400302840103170743c004c140c01c00c8101030002600d810140035039410b0341ea0103000f605218189105210140500900d0101c6074442c6912030100d4070743d40d090143c05042c403100c015075604d0810a200f020380d04054211030441d804102401e0301c0f2075000c02600e41106041c6130820210000c21030f20792034003032000d5010b0b501a10000b980307520302c1c030350b180c0032022462030f51615500b455074400854200c1c01010806400350704543c00150043ca000d44c4001d007554400d045c050304003110b40e8081142e02d64200d42d0315841807008602030240b0b5a082da4610444038092a04004a20f007600120703450350000c0c88024140400c50000c038100c2d82c002d0107400c038805140e50040460054502c2032106151001030311001080c9040004640501d03e801098810f00c403c4042c8210390300e0b5550116081c810050031051035568238440d00c4000b170045e81001e0001c240c00c42c00814203041c110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 96569127 1250 96567877 96567901
    0x2701020a031113171f0204090c020a05030a08060a0308070c0501020601050a140f041803020106030209010b0a1d010311040b0301090e0d090605030907030b0112210e27010e 75
    0xc0c140c0003602d06200161280f001c110510058401002441c0348440c8683c0b02c003403070050340107482c406800c10481c0c40807280c0c80b594083c0c4210307a00d44205110300702e05000d0903600d5054003d0003402d15002048098546409961469045100a01381d1076101b40d43c0c0d01c8441c0e0942201d00f0469550940d00c1d01040032b50ba040001d240508021944c5c2c0e08007929055403c01d24203043d038400741c010383d905640d040340782d52039030700010384190052449105c4021518009000b482c0320300080b403050641b807001140069021041d0380c2c441400f500d41960756408650150700301c5205820a60405895000311803516450402400003040f1005805840c4e50402d10741c1c0f0156000c9412008541c0d1141c04a800440c0d030101c188021907102c0d09115559480e080c0f206414695146c0024241611410001a00618000d6201e1078103001e0700034840a010703007410030150345c0f5501d0000c600086003d161f01401d440c002c0c400c0142c003285001000c15001400a2542e0000000da004d1901072550b441005440340c001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 96570377 1250 96569127 96569141
    0x1061b111819110a020703151d0709180c05010c11101112070c0501050d06090203070903032705060c0a2001022e020d0f09050309040b040e0c0402032701020a03 70
    0xf04000d00c2c186195004000d40d60710740c03480301425a41c0c1c1c1c0c09101d01d96080d540d101707400d118034501c1c071009825006541550b0300d000500c50400e03900c0c58042050110040d0501c880e800039405141e225000c0c0c540b5004507036084a591098601003210035281c1c031996103200c0030700ea12800a4586504a189401081c0d003400010340c4206455031041181e0000101009190003d507002406c04603202e113070380c0c107800c40141520b03042481d4051000040c011040d0b0010201d0086074403a540708104500806158001111311150845907696500c100303001c2807500340b000e0304514150310708680c0406440e0311030a480032054401108001402003941c007255074144620301c1d84d405d116014994041c94110481440311106a00b012801d60102c0d0704910b148558003c40c1b03600d8071150782070000d849281407581e2254491000284958600201200035041900551441c1e03001c0801800004401000744800303580010440071070580303112074103409241503040201c5102a030b0400162515695540a03088940e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 96571627 1250 96570377 96570401
    0x1a01020601050d2307080a110d020306070f05070206030f041403030405030a0f050403080c06100503120712020102070519060f110a0c0213090b0402030601061b111819 73
    0x3100510881e00d030311514004441e4040011800071032400e0030140c4c1c0e0740124103138000784e01034080300003400721000030514220b901a100f00640941c80100704444000c400c0b070002d415421140000d051680942400401d842541c00c210b480d2669075400110158002c451100c4940d62500920050041c4100d05900085c1405c000b10b2550806460340d907900d0003880025020030200700710f00f00c82540f00d042518025944516126199450005099241c96088a035030001074150200083c19190001d001e100e9143c200c040f8901c2c00c4215110b0101c07108860251a06640d020042200000c500b049040c584800d8030911407600c44041c5414410f40300780301e10a140d045d060000d009901c3c03818400704e402c9a00581409028039a4a1020401280307422100616584c6001a00f030305001c0202545840b89108905540d2161b803600c6e8140c1d41080a0882510000c800b00c0306400042d0a0700f4852400d034100070300041e60748180c03603441c1c040800f0881c1c45030558142841d0050aa90040c0100c10080075 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 96572877 1250 96571627 96571633
    0x10b04020708041401020609030d0b0a05150a020c060f271c1727130e03090102070e010605070b0a06030203060103080715090b07210e03120106020a0b0f04031b061a0102 74
    0x1301804c401d81d580c011050b06012a0340e65010070454ce80d510501180100400303040d8221140c0d1040d00000035030040d80000c0054040c40601c0444c0303140403000c8500c0d00c0b10050040f428141c2c6404294010640c1c0d0070391920b00b13241041b230040e0b00d0f40d410034610041103d0180d01c102160480c6040f4141c2240c1d04c0368400c00c0700c014085084041d20701c0460400f09110025843d0800c40c0803000240d511902845551102e4a00f422595891002000070f00520b102a000c81d002241da84c4e40c8403800c003e0900c1403100240b0f09101100006031440115504041a050042a11038030307900000c1c2808020380c41101c07508000100c0d0002c00c44140541c0008135110681085514042d03160518441d800400c048104a20801c0d551420581108452107804555800700710114107024400e42d039038446404040b0400300e01000007541c0c0c0c40028603201c402e031700410307604640d191042007108140014000303c040c850034402079001d0009820403088080e00940001c0b40a02000e00784072550001d5000310747c1150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 96574127 1250 96572877 96572881
    0x50a030215280207020a1511030f0a08090313080610090b090c0c0109050615040615020709090201050c0d0903020a050a120803150a030b0703050a0204030f030305040302010b040207080414010206 85
    0x44505055070202d880303019a071011604800c40000f4031420100a50200d0302e1840803c2158814140b42543e000382c0c0c4039a40781042d900c005a41d6030050440745160010200405e601003417083c061550886400402c5900782407688000c580c4d42101a040303068154484420810090307184100c1c080100b554250812074400044082002c0c2ca90080c88481d180f200025041e06443c0254845a0229006800d0392810309244140c04003071710180613000d00c5507091200100d030100e680c2c49203281c0107041d07400408085190481000c0940903d42040c0d061040a010101855506010130b420b51705160340e403000704a00f1481048100080364100a000d41e0b840d0000344190140004e045c0740703440e0842c00e01a2280c0d0344140410340c0b001c20442d81c642249503a900041003042e4298204d00400340340e20280002da84044082049024501c1301412040400c0c0070000480e020b5800150000d00a1002044400e61600480d0a03030b403100d0300440305080300040801040355130b1002004111001d03c0681128 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 96575377 1250 96574127 96574141
    0x12010b0c0721030f0e030f0606130b09011509030b090607090609150507080c01060e040312050c0f130b040b12010e2503060302090f010e0f070915020c0d050a030215 72
    0x5100d542d5001414818010500c0391000d0213682000c1c81424018122021101c400e61810707105d10058480a02076031841d00c0c007000004860041644041000c4e01e010190b80c600844040181140c0042d4824843d00b84dc01001050a03c840c542c407450b0840000c064a082150380100009174983c440300400c07600441c144110541d01e0450030105d00ca610700280c4036199401d000c0c03254407945414840c2980b03420700006001054440e914403e5010342c4034008900014617482d415240b085860b419040c4041283c1980d5020320406040c02640b4103440e42c08058032409050b40c1c070340c040d412034604c07404003091031201510300403150750140c54180c040008604141c1c400380b2140195010090503c050500258000b9200383c0c8000300954005000d280c16051420a200840e0028084c1c0442c001c10f150000701d070018100085402065156a500d040310301d030034852491901d0740d00c1d90320114003d40501040c2c5960381d070301070410103000e04060219110f841c03030081d02d42902548003000c4007588000300451 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 96576627 1250 96575377 96575429
    0x105090906070912080c0a03020c0109090c08010e041401050106050c010f06080714030a1a04020a0803120a05060a0f150e1507080f07020415030209010902070c1a12010b0c07 76
    0x454000069810003082617140c48030700350281546880440c8150800f241c2419800902c4c80302a0200783c0782c1146007521f0303004d0403041d12060241000131811110040040310b4801800320350240c000c2854504107451030040c3d600f90b40080c0e21002c000740d004951004103da0030300c26a019160801e80812a103454030b000b83d511811070344140c405510805010700c0c171584051081c901080d501c40a4440c0c18412a00159000c000644c1c041c0c0c0074228110012540308000000c032060294120141e044030fa6074808540c0c00740c48002c1425800c1003228000090100181000c4000340c1506500c213422228400380c001c0c09041a0241c132446445103900b086400c5140404940c031480c0c200d80210782e950385000c0800820b11540300c00a410524085a0008049001950006491080303c0e110303c2070740e0f42c902d650283c1c028944042d21b1442074500400c80c000380641d40078500704102081130b0500d00030298120b002c1c0400d900c5007142c1140000c9013a100d00007804000045c0103a020410300c1c0069452940c40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 96577877 1250 96576627 96576629
    0x1501080103151b08070e0603010e06090411040e01020705011a010c29040f050106050402030c1804060510050406170115030209150d0e0105010e060d0f0f0b040b01050909060709 77
    0x1440c82c900030307104015203682c100f0182640310b010800043e014029004202460407100303180080c1c0b080c0c51603c200e05e4010110780c100e410555500075541c0342c034070410080000150003140c025845107440c0e101ca8603103015448030288544001a250000c03030424034203444200c100c1048103041c20500025907a00150002401c0741c00c0442071301003400c141d02406074803510304a180250b43c0207404001c10829504424003080f44104001e04c039242d40c4000340801d900040e5107a48044100b031005040340d820410004805040082005c11400e40d02c41c013103506001d6070030300d003000039034009428401c094010542d0016110309192a68056140924012461100b0a044002c240c2c0008280700281e84e0581c40c0503020506074000c40e83c0d403120f107003243e004040c10303040c07060320f542003100004110034020b5201d4802c04000c1c00c10020b070f8105030358011000d21080412a0300040143c1030308049031041114903c903d20910201005506180c10001d0118000f0704e104040d5112808201c135041d0b01c619110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 96579127 1250 96577877 96577883
    0xa0b0a0902100c03090515040602010c080f1503100f02070203060f010303020a0b0a150602061008070807051909020c1b0301020a0c1709120105061c0803070c020114030a050109051501080103 83
    0x2207000ea142d207400c94280d030300ea86c000d9610018441d501031140c485000100101c072130b40d030020403200c1d00c908002c7d500ca40307044401100c2d0100e0080000c4820305070403801d40f040340e4000c0580e802c0080030f140355800c47e110040441e4440354013152a4085040400c44c4607004100b4089050740d640c51a5802507554050b8100180000110408901a0300e02900302c101c0c4441400a40301469450740340080da204000c0700c443c80640e00c1000c002840040216030305007550686800b130811241404180400c89268400e40070b44074202c28800108103900744040c0420a5210025080010546504c059007000124115100707034410002c030460160480340203403200b540080320070321120744100703a2121030041409094004100c107008540e00503040d8005032007144100d03400407a0b115510103400702c0d160003082c0240740c8002000031580040c0200311880840c2e01c14507042020302c2c403010081c601c076002a925043d0858440005004044003405560f0703008000400135010000008002882603034184005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 96580377 1250 96579127 96579137
    0x105032811060f030403021513080904020a020309130606030605010f05091207080f0606040c02060601080106110712050f0d031104090e0a05030307020a0b0906010f052206080a0b0a090210 82
    0x100010392120b00958100c1c080d04503200e6140d260505019444545145040c00302c0b620703030000030b8641c5511145001c45e070780e086000241012225400d101c000c0d0710141040c01544070074408040f040d6a200b0304c1e48604548820042030842c540000035041c1c5031307550489414008161828080d0f25440010703942070000c116200700c44140b0400302c03241002c480f50011080c40c09801c58141140d5400a5080d00461013036a00700b081302c15844040340c69180550f00e0a0000310054010040c051041303150500398241c51094070703a4130350313601201920145060012526504500c00c450340070301c01130001c10210003460505106112004050b44001d00c514083c1e20300c0156508120700d6600303002c02c012400c241d4464100d0b6640d0601c5180079503a2019007900311035402ca00b00014141410202c1e2241c1240c000c0b11007500300604203c10010190460603005154070803002c003184200ca41c50145000405198001e0301010702682002e10f104200146001d40550506034140c00584540010304840002c0d4504 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 96581627 1250 96580377 96580403
    0x10b0a11011a1c05030a09031506050609210d0c060b030c21010227090a15030b0403020a1a07030b15030406020f070b16030e0606011e120e010501050328 67
    0x32102d00ca1616074030150185c800810b070310590b0341e00b207400c90007500c0c0205610780303141e00704a40050a8408074001c071900410284807107251b605044030103d21001c0c01240c6c03000d007480560700c09072034887c161a9100004604450a1092142c1d80c891098504000e4018060307a00d1803001248150910b1a82d5141740180380d601040400b40a40c140c80d24a0340700f504038034569001401c02004085c0307501c1c0041c4180f000c2c0001c150441c0443c4182100740e1200c03165149a00e166403a0021650340081041d8198090341c00c100c0c0014218101c03940c801c0c41c1c1c10502541c02c1c200508010100d52021715148e01640003400140000c00d04e040540341e000ea4081c0d000341e590421001c10040358090f0213070041080c805001400380005d0030a54035407112126580c200321103c0860101940c82070705403685c43c0424540c1000f04020500881c0e0410b501d80c0604280c20b40704120420040dc40d264511190080d96440d00103004614081c002c4031508205000d01c0310240e03101c82c02c001020a800072000340420104c1c64 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 96582734 1107 96581627 96581659
    0x5090f010608060d080403061d1c170702070506040320040513060f1b0206010503150f010b0a0c060203070c0b060a06140706060509010b0a11011a 64
    0x5480308110340314602030007013426442100f9119504104404000b280107030140e443c110701c14412070064018418441403d10440a036517003d240c010150340c9c81c5959001c5d904200301c0340d0004200311261242030050345031250720380c481500315001041c00014080c00c060328650031b0303444580114101c1100390402c0100c41c003c40754030f032600754002d16841c007042d41c40d800b010740001e4002d000900c0350824800f10511041c2e968805c8010b034003a900520503030406100401c1b05d141c0c1030400801a0508800e103032144801409880200c000105030201084d200781c0d03d9485868120b18210359070706000c500240945207000341606d01d03510100204a45040104224003202d0b1681d40b40d90400d214500b6070012a4021001920180e07241e070f40110392580d60000c00d900030b2416416090307407180581400350004002400c107172001d9150001c29903e030f12000007440100d40c4101c458a24582140c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 96402877 96582734 := by
  have h0 := BRFrame.cov_init 96402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 96402877 ≤ n) (h2 : n < 96582734) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
