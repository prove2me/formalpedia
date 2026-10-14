-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1993
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:24:13.983993+00:00
-- url     : https://prove2.me/submissions/5b4705dc-5eca-4b16-9dc5-02060feb9c75

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 358273381 ≤ n < 358453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 358274631 1250 358273381 358273387
    0xa0510180f02010e1003090203160311010f0207030b0f1806010e061c0c1203020f03030c07110402070204060605030a1a1302071a070503040b010501030b0f040e0a0b04050601090e12 79
    0x181d5244035807900140c00300e06100042212004566514103da49801c010343c0300032500d01c01600c101410400c5030301041b155030003040c1c420f0010650b20034240482c1c00080c00c0102c04030840d05416450128907600080000c00c0580410201042000c0c0b1f443c020720843c0c4441c0400440c3c100c07221b031101c80901680b401e080b8020009000c519081e50036400c00c0c0107074070100c800c010300382e201e102d0060400d4120800c6141203105050402d54100f0081d984662035101640c1142001280d0803014400e02c0300150080d448216596040d40c1c0e594101e07803c10b90f005004208140e5a0301c400b13800d1350030858200302814070744505c0100c3c55005201d04562068010201e0404185c0552010f00940003a081541e03051000c8140071000742007c04458000c100c00c1d101d00b6207c0c03900381f40c07480140310144c10907030416040040c0025691200f400c1c009030040300700c1d0041803030b01203046050314003110100e0250007440c801c0b0030700003406404101c050680e1092401030152102005075980d0380d014443c0a807130300560030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 358275881 1250 358274631 358274633
    0xf0e06070f030e01031103040605060f09010305120f0f0d0c09050d020105072d0303051f0311153603120708130504110a020607020d050a0e030307080c0a051018 70
    0x103d54000204905050020349100201c035110f0041d00200d034210f80f1242c0e24400d0040c18903009100b07102608084a5100656040d5030f035042d183e01d0300080c50640307003130045941d42ca10030b802401d83d000f240440032483d4130350368400a000060404a80707800041034582a002c681ca080407501071034690380607100d5170310305005c6658115822006800c41c00181e004c6003500102d0440c00301070209124000c2d9400304403420846002c506a1485140e00585004031180420010700f01d00c0c0c03e07481c0310388202c80e0b1041814080200c5203e074403a01703450703031100c81d4040b4500c03208045142a9001d003610080291481c4490079090581e030310300d98150169528000d20400c0000342441006102e45481c4082e40303007219644802080685600c1d080d80f048024001c254081107582c10000540d010341d941c80117113003801e030094010b085440f4030303180c81003005521201c2c0d90481d2010021a43e0355030b4402a05640e9104001d00b1584610402004075554040d0b007000302035108083c00742c445843d4070314030004070034982 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 358277131 1250 358275881 358275887
    0xf060408150405010e03120a0b03031603030221010b070605371b030e010c0e1e1c240204150c02010e0910080d03110306010c0c090c0f0e06070f03 64
    0x7004204441c99901ca0f6081d805080c1d05001401035015800501021820301c844448150340103000301c0e40c020707030040c49054041d02644948000e940d0300b5080040c1d4540c1142200206c01c4050f1213000d54002c0c61100000d03890720080010312046014803030401054491a85508980e500044c09a003054403292400c44040034145c003008014180213030000c1c000c1c0500e080c5043c03a040400c1d002001c01c2d5030b1302020b086580d081c0907540300c02e0040d103000c8000141c1040004c09020211001d401c412522000c1d11001c3d45030860202070000f0f000d02c0030104003916140c000c1c3c0c5034a54101101c0c000c5803a42550000b102980256000e41d00301c0307a40c6815a00c241001140e44520105d8160b0402081c1c50b010038441d00c0b07001c0454090403010741403100c0c203400d1140507403515800071030f80384c01c15283c90252000391074400143e0360840824a000440c410701c1d400e00c101384160a81002d2a60307850512511313611a04144c030310782c1940032511008038441d8a0300c00c11000d0f007d000b40240016581c1c210030400244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 358278381 1250 358277131 358277173
    0x50f0c0a0305210403051501061706031b04090c03051c0906020613060b060307020d020f0d0c02060a030905060a2a02030315010302040b07030e1e13020d1b0e0f060408 73
    0x44501e0003e03007095669210b407464080d44c1c60102528280c02c01c01440250742c801103034104002a06c1d803110302803e1031800b2945c2c07112800c0c100c854000b003c03540c2c48083d0b5299003110300000c1c1c21850806145445e0304000d9150465559460a070203403200c003c204043c0242580c01c02c484a40d00a03101340c0e510408400b08481484104a40c0b090384d030070f08151144d8034100a180114610f07030050612031404500a840d181d2040409011540311038420a00c00c0e03444005800d4860303040da06103485120642c4c054020700440213000301039000346400c103c1c81c403545600c401c25100d00030100e2402c0e031a49250b04010803035110744820041c2c00c100000f40800402d60400d03070406006140c018941035540350142c2203030304405400c800046100010b1b41d0300c0d161024a801001c0d4001807031090070651080002d650100d0310311000c000c150003180c60691100c440e03020340c0c1680c0301e4070b030301d5880c8100d07203200202805003488000740300d000c01d8150170059042450580701035803441c03401004c0b801405030a022001d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 358279631 1250 358278381 358278433
    0x612040203010207020904030c0b01080118020d02150708071b15030203130b0a0c12021305010c030306090f050601170f070e03070312080106081f050d021903050f0c0a0305 75
    0x26401300301da5801a1201e08209105074000d075a804140c0d003080c0380500c400b60040e03120b022968101740402176680d01b0800c4511013154100c03440c20720075441c0d102003401c2084120500508050200d40c1c1c03014450000000d010035072098075171910000307111000b0f00001d5940d0103250f41e000103000c520f9032014001d50042d030700580f000c4030f4038a000510341d950000d20b0700704503509050340ba01c03858815616604110403040110b080d004c25400d0140c0c01650440c0121103114980c100201d48a000c428540640c0c020400340024810034030080d405000300d02d01500003504c0f40380c002642c2c55210501007020710b00c80e41c0219500000c0921a85500408072989503102103055454001c84400000003402c841440e0003a8880b900c0d5244550324002c0c019160610040c1210504806040020482c03541900c6201c02d07a5802c440300c035940802c41c000f04050074848071601140402522010080c80000034031010a110002c084603a100190b00511202c17a0503444001d2890b4080c4949400c1034603d07070303d54041c003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 358280881 1250 358279631 358279633
    0xd0207081e0901030614060a051308010203010b09010801091404060b1210050406060806040302060406150b0c0a0210050909130807020a03030c02090601081e15030d02010b0a0509060612040203 84
    0x11070580c1a0144450548050900c903840780000c2c80e100d90f5070107024004c0104000301c12240350700c1c1c480300825440c0c4a400800810030100085450721803110030007600c040e003e140021501c03580c44025042c810381c451008107020860313400000075482c0c42c81c0108400b04240356250b00303c0e0740b42d5647c0c00014208614a041d4004104024070030703a10320420180e400010402c1c008103140c10141880740445a040e0440307002900504204000310380c00040c04c9130000e034040c1c030008046684c480c04161007c040e4200c07100414001404005e01140001d00350a040c1c022900584000281e61095449209001a443d04841e4410003e400008189040c0e03a405001d500701900e0018543c0c00100b40725110f4004401040c074100c00780301075040c034604d203c3d8407010a00700079030a0705003043c0005001e0b83c0120507290080e29400042c00e625801c3c814105800005021203030702c0c00800002174040d0a40380c00c0c8038061aa920740019103890085142401590702400091514108002c80d10144400900503601 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 358282131 1250 358280881 358280887
    0x80f0f16080c1912080d050c121621020a090f060c0206031308070c031205070206040510020a06060611060901090c05090a15090f050601020106080c1011031303170f0d020708 76
    0xf1302041c5502c191500d1007030403000d40c1c4030b990603201c1c012200f02400395001224244141c06880d50703014a41070300010402c0c2c0d0a00c140c00091004c64500038041020004581d90352150081001641c0245c8003509031030322800c10fa542c03034200c0108006854441e450014a03c0044440907003050340c02550822412942c0c640030101680721007209e40d00c008011103185203c0c520070002d02c068a40c44030316840e460302d40346150005c15000a2102d000da405250700ca00340c5400500110b5000300114240241e101d030b014000c8640e030302c0000c0c000a4003a20614407901881002403840201881500c00c80c2d80d02590952029040605108071018001c04200480e030b0303141e480c00340e00d2031002c1100c00100b4180201040d1000d1003072031036050700c001130f05690640e81819818401e44101140300440a142551001600c041a20307040350181320f00c00e05020300307002c0007550501440c0082103a80070b40e40505994031540e079126400300450301c10071009500d41c3c4024010b209981541d9001855102d0082c1e190f142 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 358283381 1250 358282131 358282139
    0xc01050a0f0201180f0b0f0606030604051302090403030b030f0601030f0b090708010f0501050a051c030f0302070b0f0105090105030a11010807030b100e09090304061215080f0f16080c19 81
    0x141300300c10040c040e07a4036030008100408001811581c40d07030142e00c80c102d11007941415400b0a1190101400035841662180f001940b1a041078280c00074203900145964682c0c1401d040107001090400c0c0d02601a000c1e40d4401ea00c10000080c02c00d04a950241c54030105078603a48035004244009401c45666009a400c0003401c0442401030500030071400c0c00001da59450072003001692502070f84140d015100c124070160704078600c40d0754480165050304142c451415104801c50017131240302002490b2010100030b12030304411858519058450a0316034601c40e0341c992080564545552500401880140e0b42030161544144900354006802d801d001c074141c00441b0014804150300360b048000542e4451502c40c60307182100c20603070010b8031b020280d860306042c008020303c0c0300c4025854020940e01c80d03d404440080340c00c800b800800c410070554950710a0041000c0e29030681c0080c060440c03090300c5612450003030f404100c2084a00b40001810000600418454802400551101a0700710800001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 358284631 1250 358283381 358283411
    0x20306160e0a030b0a0b0f06090108100b04030807020405010e040209240402071109060f0109050d0f05121e03061807090b031602070e010e010e100503030a0509040b030c01050a0f0201 80
    0x41c00345100d459a60b40f00c2c5005e540e41c03022202007541c0740d8403074990b00c8587c3c009607c0720421905210001e2810b90b2a0340d503840341481c5009840d40c00468013180016000040c040520701804000388221002c1c0100c0e640d07040601c500120a4601941c052071140102c0d803041000040170700c41c082c0c40d2030307440401c0c40c41d900080d040f03810041f4256020b62056103038200c1392401203030199100d40300f16440c0a4603040d00c0d000800010311409814020070301140390805100c0362020081e010703a030200c06c0719180d1140307500d081900e8024500c0c0e11080116052110b04003010402500c0c032030907000c0c04220032401c03040040d0301c403040040c3c0060b06216076620003054401d0020010b62045021403102103a480d01030b90001c0c90119294800441c01031010f0043c82142140380d032481c1142c62244000941d80c9440e0054189885694007540d410311001170301a0400380c004000d080e40c1041102e04101c6500c14005041e00c40a0500180d8001003041085094560040090003180c4895200004021141c24948 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 358285881 1250 358284631 358284649
    0xc0a03170106050f180415033e0a0b0c030910030b090f180a03080108073002061b100605100f030e01020d09110a0b04081b0d080318010f09020306160e 66
    0x1032a034441c87d1000c10300500540140040d0321940a03c602080d6201e1843c000034a00e03503e07440003d41c07440005034503126903961007607600a84032000800c4d643e441ca03501d11569030341c05007004500503003210904e106201c0c001c0c4180086a00044c2c01c200d52552100c0503114006030080c078a050580c09041104003920303040100422152190b106c0744134a5040142d42860001141d000c15040c1319040009a5013040d21003c40c0c62040402c400c882240d0480e10000740e00d0b026414591050007040080c0c000051400244d5040702c21141c2400c0007031a40310014050841d0200c10150007140c00001c0650101b0302c00c0d800048000b6016000608020400d8a10700030b8415141084d1502c02d11148401d00500d0402c3c140e1000b0a60086030511f0540740c24104da48074030380c9904035407410351038000a043c152140b045e4105e046030b0055099a0b40c0c500b613011180c0c1061041518200c548c6001442402940b207840b0303a00b250354000f402019980d40b80840c035a20489000e814108004070103014540c551210290 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 358287131 1250 358285881 358285901
    0x190318050d030f020c0312091c021c030905030304030804020415090605090702071d06031c050d24171207120e0307051f030e030c0a03170106050f1804 66
    0xd4151040103400042c155098080c0c841401e51041008440d030002c0002182c100c00300540541d0115035941d50220704111180365001d0394083c14441d1700c5815907010490a016245000d40d403801000100320840031155108001030184e0302c20408100413a0013103840541c403a1008102040091190140100f0221740e035115403692501c0c1d44080c412072078108501903000110348000c0202502e044402e240c110444802c440113290101d0220741680c03402d0101d11403401a0600c0700c01380c044c541310700410359402450140f9419280c000c02d6581096500301d07540e01446205941c103d01414148840403025807828070112078030803c4101d601020742000902400340c02081100403004000308041c000b0690000d0451081d0010a024040741d0303903040308a5401e09400d109070540d1804001e094004099030b0402504602c00440d0301c00312a20b0005110052901c03035520281c101d04008000341040b4400e018a001150040c03140030030030b03101036014141c102c80d881642c6070301013065000301d42100c0420035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 358288381 1250 358287131 358287133
    0x8090a0302030f0a030909020c0712060e070e0603100e030a1206090c05120903040303050f0306031e03040f1a030606070206120106030f0c17070f030b180f0c04030819031805 76
    0xa024117150300081c6c840003d00f038200065142c00c1e608004141c4480b0a070007504030401c00e030040441440042e030f00604030300c03401c0e8084031401600c4501000400808440c100d00ca4440c1020380030102c806070064082c0355074003c3c029814801010b506481111611642800341d95036403c1c0020904454014900318810f0343d100c19546400300d0282003480c06005000c10200c0e4000c000c1040040d520004440300e05072009000c9481e40c030356100103820042c41e2607111800191645540c04901c038007000030f10459408820030080c013507480403120f800c0c41c441d419000361620140300003411307410000c00800c101803005110526050b050015083c046100303030030560019030349190000c090000c03481a0610b8200c541080c40c44901c410458400f030550090030202006000c452404e0200d000e034102c04e0704110f00401d100040310200c1c25100d07500a0483d81400030180f20f1002c00d0026010404640c143d94210761050701d0711010f140052000003004c890101016920200a021842c00442690a03144904 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 358289631 1250 358288381 358288393
    0x1d030706020c070b0c070b0f0c0115241b020415080105060109060c02221104030308150a0e0103030f090905070e0f062d16050d1704030c08090a0302030f 67
    0x7003400e03d00101c1c1d401c05054024100007125503840300098040c100c41c086850b050f070b642180043c014081c0101c1683c0d281d80c0d030030b0240c680d80303e00d00c0f466450b040c2d8203214002d2000090f046180d581100e20016218040342c521000402241007006143c140940058000305503540204500b821003880c0b42d1000e90716175500e50a0000660b0310040c2c1a004140b185803440380c070856900051590704c174038001c00480c1c81546d842446400340a800c02128100503d03030306030b151540c90401800001c0c3c121040403100d1807031210002d403840c0c481288001c1c5d034101070b48966240e0840d6001e035842208010520305010b1001c90000746000b2500070380c0e01c47c40c010f507102d5203000044024048100700c1d101d05244220418010340d40b01c041505d100c0314000d800300c09992a003050700c407920400c034454094103800c001890224203085c0040042c50314010308265075283c500240748401c0b030810a40c10707135004000900c42143c2d48041070200b40513240101c030081c0a40101a48c0307500007031401440746200320f200e40050b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 358290881 1250 358289631 358289647
    0x70e062a032a0c15030f090115060302070c09060608070833040507020c030c010f050d06030309080d030c05160203191209120c030605040807080d051b09010c061d03070602 75
    0x910000f40e0120003500d01500300011a00403401a0000808626081e660b400004092901c250060850f11200840400c60142c640c03070700502a500c03814003510302182c0b50200250040a9100b0001100d4041d80c1e144000d85540030708a82520010301045102030001c1c10001450940c1c0c410244004902c08140d841603842200303100a07114000e2051080d5040f0300502c440340c0d14085040d461111003403800c90018000c0d100180c545002c3d084003184803d2904801104064104400006440030b210480e40c42c1884041c3c04c40aa40c90102101c000540074020003000381880b28111042500c01015201101042d0f800c110a44487c0402660380d403001514034500160441a440c000d003071000c0940103c10700644a158410007107100042c1130139502d00002d070502500b441a0340180b58003008039591610800c1d1050050601580c4001303618501002c210318101a05c000c9a440711030603110700d042d410150322144020221040d400c0030100480b1204403540701c00b40010045a4814100147c540d060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 358292131 1250 358290881 358290883
    0x306150d020909070518120703060e10060e010f051c080c010912030e030f0309030c0a03090609060c110d02120307060515090603060103080a030b1206070e062a032a 72
    0x142c40081130101c1003000d602124244d0310480a00c1d41e040e500e2031107209494604525142c1d0551000d03001d80e140052900d4bc88101095100e400c058140f010700c4501e44503590420449400e2007021801d0a074081d0030003c9051545c41c054014101039400c0c00c03401030607101c103843c69001c00e140c8071003a5500c0c2420000c0042d200e00b40106181c8924081004040400042d550381c815803007412601c2c003000c00058084a010402c462014892030140d400e468a945000b43c00c1140d903020351400300f0440c68021500a100d0401c54100f690000459040038000c8405e0104003000d035003045e0f8100c8510800354060082c104014042540704520000c1c0702e281400c48184140044407100b841040e81c84d090003550f9800007005419aa0415005075980402c18000e80040442c1201c0ca41c001121442d0381c1003a5502181d601d01c680c6039500c440c0c2400e8000b60400c082441031880e0b84101d030f40c8076003a0755080b01844444000c002c800d24222868040e146007004100301040581c1071040c507000c1e41880740504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 358293381 1250 358292131 358292149
    0x3090a060509031e1c0903050d0507081009020705160b0711030d081f05090109050103060b030a031409060d0f060501110f190819031514090c0306150d0209 68
    0xc10302d0090350400002c0e04542100c045078503110700c03002c08041036015848154000c00c1c404070101e2070080044250924010703003640c00000c0f08051051405002594803801408190b11681d5400030b5103d2290400115900a400070081910184103100503c404100340d031502c0c0c0081c088a6000303a8039201c1c985808410303a140024521b000f5080013001ca800d494100400b5500207032480c014000c040e80107801c050710300199a00c00c0340e000c0010800020800346c00c1d840a4181c900134030b41071000083c81d205055882605003801400103030706004941c00d0150f0580681a0340c50000d24551920040c48061016a00259041d0080b1559200e04004541c0c010041d00b020b1350b00400a0160700501c0e008942d1101015001c468485400110038070400904008580009111070341003007004008080c01001000c40e4003c0c820a140c03803001c00308412007101c0590b410004014030801480d501c245a403903060b0005440d0517041042d00d10703a800c500c000c980103020f0f4109083c0d80161039023280e4007002030481c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 358294631 1250 358293381 358293391
    0x12021216260f070e060d0506071205070e18070512010f09050f0c04030b0402060415030c02010c050c030f0d020c1f0b0609060d0504150f0504050c0603010e13050109060203090a0605 79
    0x1d8801c0c004540c40c4000441d003c81200c414a00d400400c0c0d50340c4011488030640428020594042c80080140c981c0d0800c0e624992644070a004000b907030348040080c1c4050340303120349140e80080d9072140768803007050711010142d200c15280381680c1890903485200302401170a0304038001d90360240030b05100100b0300c0d00c500da5100f10404014191030030400b03480e100074880d9020280400c4070705c0f00000d0070740d00c480f011a0000c0042000740d9042541c107200050060101c41301200065091604044600b8480c0017562040075580001d1860807404039190b14081c0e116114074400960240b013040c052001c2804911000c80c140c13207002303010310032042c00041110742640c0d16070f1040d107040c051820701d0f80b1980c0035500038040c0800006603945803401c003803d001c00c41264201805007480c0c042c20b00742e4001c0d00814004c034850f004941590018000700030090009000307981d00e02d01603100046108401142c010b4506005200020310a40c1c030740c6030582aa441201c044542d13a00800000c41044000d105941e800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 358295881 1250 358294631 358294633
    0x30f040c05220510060807113307050a27050d030f02010f0207030509040c03090c2c04020303090d0c08030304080c0d23090111060108011b020105011202121626 70
    0x45170a00e84098601c038400340c050303010059191a261184401040f41b48040c44024032030860385410700c0e01c0e080841e0303c7d070741c3c0351400380c01d41d10046021b4034050020340306e00008079103032001000482c414004042100c000c401c0c04212203440d002070035840d06c0001e442158040c3d500e074002d61000180c00790a48a031298200c610340e1040290a02295101d01520500002103402080d581e191403c00c4014100103100504001000342001602500c180c2c338010340340110205103589000005500304509508403000b94050300100001d103064a4203442c0c0c8911284580803d0342202d440399001480c0d500211421a801003001604800450040090300e01021052609403104c01400c20700c04800c2e0446d03081c881d4103030740101e0781c89080c1e8014a111106170100c0d07800c444d00303980d45d059400d0292250350092860050700c6404240180c0c410f01801341039840c48900180c612010b50b090001d5050420100e08280c00f4046407070000c0006050024014000310713000c3d03041c04d1340c0800d03070140c01a407400510900f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 358297131 1250 358295881 358295911
    0x10615050a0f0c02211015050f09060901150507060207030503040303061e060e121516300b0904050d20100b0301020c07030614150105030f040c052205 66
    0x59590510700b00178001440d480a40241d0404803440c601224912520015410034401880c41c2e4180304204040b14000c4403185201c2c4512001d22440103000c0e60402d401440b000010b110502d007490988445420340e1909600d40b61f0316490342d0b82280c206c942c044000070000000d00060552501401000d0000d012030030704140b805000c001416070040c0700d80402d010b9011802d2300e140d0f84484851240c10a40c3c419500705141320304102145e24000c0305d80502108201e000030000c0792003011212903440069031a4030000054091103190400e1f07281034017403415111312414405071034600120780038a00ca03070300138143c2c02584400984044103440048074016003410703040001080000300d0504503940101c000550541345004070380a80318a1003010b140b072041001c0001000603580c44210109404031040c5000c2d00c804602102c15102580b0407400520144041000c4025902101e90401e11801c98607449594032400b017411020660302ca241c004a010a25401c00c1c0d5290042a60003141e02e041198 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 358298381 1250 358297131 358297133
    0x2040b04050c09040f1d01051b07050a1b0b1b0d02061012020303160c060e0604050603040809040608101a041b0f120204180b0d0320010615050a0f0c 65
    0x51501845210504c580d0b260003080302c0d450300e03aa00c080000c3c1801d40094085c100300040c1e41d4041c0400f55030991101c4025510b0140541c0444c0681d142c0b40d03032103030182c5501d14a68880040f8200358032a000d01d1002000750000c1c01d9200d00004107507440b0300f200e00c0c2e60401034115801d41401c01a4a280d000e40d0800c404200400c040c415410050303903403644d94225180c2c1c550000c28614011b40744820560588800110180624001c0340c1048480c41e0b55440d016080c09010700c0054025807046940103074003480410700080c001e002801142d00080c000007401646c0741689480c0141149004000c50340c1c81000e040c8004c00140005074190040ea424442280c4441091010144054a0104100072001420f520034440d86e90800758401240041d51955220106070300c2010010040b0a54a4503040d11100d0500349a8070a5001c80d4054031050341885030801e0100c058142e107010360f0b0080d540da05000c90b0301d0801305c03079002403040103540719500c551989001034425040c1e0141c17002840401c0c1c03a058 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 358299631 1250 358298381 358298401
    0x150108060d08041e0302091305030703080a020c070308131d040f03021e0c09010824070e03060c0a20060c070f06050f04030f09120f030207120c0302040b0405 69
    0x140c01080558084465081c18206035100f4040c54001c10404801500c0d081850b0721806003a80680303008035540d48a0782c6621411203044042800c0c000c000c2c1c0c0080c000342c2c001c680940c0841e580440d41480141c13800c00b0555085042100c2500304441030240460340380c050031104100e0901030101d16500c41411840420358150640005000500d80d141e441500c0c01014400e000b0f255501c0c0ca0b040b01d00c2c00030070001343d02640300e54103050301e24003480c006400040d4440c00000ca041440145944004107001d03403c0d038860086600070a40c1040c04441d0501d819503841c2044402c1c4140048494140c9a00026000800d5070f40480300107924501c50409182a003800842c80f913400023255810f9650b0341ccc96030310f0716005242e0002c00282074140303001d08225004000d40320580c07055101e0b0b680c80001c0713001008251580e00040c003412404061a224560001d01d2024031124014000d0045854003075551060151000809404a0fa101c100c00c80400444c140b902403000880d0741210b003803100d031428135540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 358300881 1250 358299631 358299647
    0x7030c0912020312040305010f05060d020d03110f1e060c0703051204030903060f090b09030408070303051c05012d0e19091e150b0d030f020f030a0c0201081501 70
    0x140720070300366441c811045540400c803242c050850380083d2511503540f800d002e4000c104011310880720506000c00102035207400307621900e04550040c1000d00a401c0c50f00e04035446031000b1804540351244112140450804014650700340c0c10104d200d0001c0700350045007509013030002e454005028030034452000000e03040426218542c0e1918143300803640d5908088980c24090362028103801d1528500c0701c01c088150708112081030180c00c08005c81c0d11b400d414280e484c03246204e072050581280c41c084c000680f08800804d2090109003400d107841040e000c0c231604075034080e4814003810840841a900700194007a20b50040c4036900601c00d1001c0c50298400c540b010010103800c0b10072482c0820180f266031641c8a0070b841900010303a065150580d05400b15081602c2c407083e503401c074480410310140d208500401d800c1c40409410980200503541e0305440ca941e4030300601066014482d41c40c00c0c83c8108001610031046580c0c0d403d0f401d40d030903000161a14002070b0510821503150780032145983d82080d09 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 358302131 1250 358300881 358300889
    0xd24022803110c0c1206040b1b0405040216030815100507061d0f0d09080303060909010e010e0610050402040b040608130f120305091615090302030a060b1219080a03090203030d090302010507030c09 86
    0x11601c0100d00401c80c49e105480f5a41207250300031320220341c00e01d004109900f640c3e4458440d80320381115886403121500d401038000c0c442d50307102911003c0c1c040030b14417a601412000e8424070780404d05060781c0c0003104c0510590b00808a42c0c0e4085892001c000c0410013818240141d00d003000310800d0f04059105440b4030000740501c0c054041c0c10089800010251b001c0320168007048020096402c03010011600c0e26800e40e643c400d24a007440c804134607850a8400c072411a40341d031217090302e89480c1c103800307507501c0a0042166107803a401414040205501c2c4195030b207541d2049800c5c43e10b072042d02d45c000d0200d45001d4069a480e42c400402c59802d007211103030b25400c0d00d01c51520040d411106001c102c8525409420003901402000711950810249400454558004a8080349074540c2c03080c900381c1d0b485400c007aa02034007c0402d24880450010b40003800c4440c040c0c40d01044c802020b0300441c5c0303076900a504130345009075102c030810f051644c284a02e0341c004110b0315003480485401440204446030303c2c05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 358303381 1250 358302131 358302151
    0xf18050c010e0114030f01060905100c0f06020f0703020a0510090f020d05031e03010f080a050d0509032d07080105090a0209150d24022803110c0c1206040b 68
    0x2142c01407980c010b000e2420f050340d00c1980b6580d02d1030200140280d4004c00c0c800c00780401c00d01b00011606140c07001c0034040140b465580c0e46240c19140d161980c000d20100e034165846682000141ca4110301e030001000d0950003074000b07260f20a00c524001d89000680c401c1c01420034604000c8400081100d824100142d030103d541d00700d00d407000d051242c103510032200c00546600244024081c0410540040c504a03507a0b201c070401816680c0083d25119068101e0041081d04158041d400480c028400b0703000f4001c000d1b084030040f500d416a4224401c0d07610405040000002181c8140e03000100444800313085014028021800e06c0f00000d03a039040344010003441103c01100048444400944124174818000d0034070790580010f05098400051510112200343c6c0c2c16540000906594022944d219841d48003040c1700c1c0c21040440f0180030301d115000c90402d0740754010101900d400101038521034000354050403020080c0c000b04002510701d07880d44485504000c003080003042d10500712540c0040070314 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 358304631 1250 358303381 358303397
    0xc030215190b011e030e120f0901050f0903010603030305010509130c170102160807020909010b060a030b0d05070b0d0c0c1502031017010204060806010206100513020d020d0f18050c01 80
    0x1000603950115180d000b1549007402592166070a0b5054001e9410109a50709607a20100d61f1391181e12244030700442c40342c140d5001c0021014030b51143c4020b1100e03901011500d8284202c000000f0f081d0380260b401980025201c0e401402107241c165040d84d00a0305a8891500c10419a6a181d0081d4114400d810724100c100304240701e0f85070290100c500070003a54507080d070700f81e10a2629002c150484001640100c03140350016000c04414030950b102484000d000c0c0d0700700b0b0403140b0b08a0150842105081d001144078810000003002088104050404407420503140c0305c07510001d0741141c09c00000942004145810100441c0c48074420300502c800d600d1015907290742c0d02c440e444018225910203140100b40300b0350303107091707810650160060b625155109802c81e22680c004a03500c0000341e440c081c4c9110203885c1000b081c80d050701c0c41c1100c00510790016080c102010721030b4003282c00481021107201d03100d48140070520914410803071100c82503518804003200c1c80c0c5030241d50760000d0741d840c4e062240722 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 358305881 1250 358304631 358304651
    0xb01061b02012f06131721062209021e0604090f060803030c03040303050a0504020603160221090310060e041101090e0411010f0f0f03150302100c03021519 68
    0x1c0c01590f0a50800002110501c0c1808007038a2000c01024206541d05000c4a90b000450005401111a0004045054038502002089607448640d0107400b960348002c40d1040c840324844981402d01d403121204038001303281c4540d401442802c0c0341c101e01560219000c415000e1180c2c0e40c000c10756058400048002400c544a50507550007010720b41c00c1007040744008130802002c0d07840e440007103124a220340c0d818403058a44030900c80c162442500d00035440002400041d07503e00e81009402d00600c51403045a8141041d90070844800080b00c03008004601c00082d00032076803e040040c005070461010082180703074030380031102d000c8003001b920091901000c4201c0c402540e00c6880080040c2c039051400c401182000c0c82e08500191000503e6808518103a24170140316018060703c1d100c03803009032034800c2444038002c4110001d0a041e42a01210102000084090389441c0c2c2408050b548603180e501c943ca09508010789029080c1c2000d040d580e8024040081c00400f84961071001c4481c11004160b181d80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 358307131 1250 358305881 358305947
    0x910090804031a010927151508070f0e060114210a0207021801150e04140f01170a0206190e041e0b0402131401050706090b01061b0201 59
    0x746900142601c00c00b00c0303502888020541480c0e040341e50140042100481d01e0a0400b070101c031302081d80d02c1c0301d4441c000700c03000301d01d840c1c031107007844174403588005600304400400509111181e0042d11541c0d000c147c062041c142e03c07002440140450f080d0700c412034070b00344000802c981e00310070100f00e1588010810072120940620704140c0c010f43c0340301c00aa41c2c9004a8014025048000140c0c45000c0c1405407200300d001543c4102c0c180c440b000300201082220110659070034503005400e6401581d50b401c00201f0322640c00c0c580b0301404412030701210070352501d07400000800c058030b41100c107034000404600060781c07040300315101031426010303c1e4100c441da0311f416604c410a00c101c0a81050178031a00d1080c140b400d04d40041e010300018810818248028203200490245001e441d0343e44042d03c205200480600301c00e03480200c41490321070b18140c515a110f0f0b00743d91034998100e545082c030900620220350000351910542126124880d2052035070780000b40803d20622000c038080082451b03000c42006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 358308381 1250 358307131 358307137
    0xc0c0103141317041e06050a0c0602211302090106020d0215040602091314010b070b04020904020d0f050307032604060f0b060f07020a0b0f04090b0d060623060309100908 74
    0x90b01e140c8651155030b02d500c03540f808505c0640c0300200c024064400b0035018080c5003901c50f0f40045983d44161306240c2c0e9034007c000e5101c04c2c810f1784240c0682d8041d00c2c240041c469501c3c0b0030820082c00c0048951148140325a100040c0c03c03000c2590084200c1400f4143e001036007030b490503003815174000c1030f4681c1e0a11000a00c550b405450700010340c1e0785a0085210f02c0e40210741941c0c8881001c28003a0703030700c081d119090f00a920340285031021400c0490054603000c0e0101e40c1060004026862440e00d5694540e40c104000c0003c4810341c10205241080c15000041003006440c803540b50f00c090f0f410311000714002c3e907004100070540350f9112500c0b5a9800c003a0301c02080d440014003996542e0060b082c0d00d0340700341c10000f8101d200340041400800c01d101020260b404404c180c1c914141082d080c00601c10142000c080581c1c0c0200f80c0001d04400714581d401030314001e148028004404440f0403025140c50003a50705880d004190402c244032030f0302000680710705420001c9100140b003502030b03d8043d1040c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 358309631 1250 358308381 358308413
    0x111509221d0c0102070e0c09040f020f0703090e06010f1202030a0902060f0d11070507170307080409050103122f030d090605060102100605060a140c0706050c0c01031413 74
    0x1441140108210180000303a107100c0b00d07400d80860700700a17a40c400101003010100c403440081d1b42c003030102c492142000c0c0c2051910f41e42c0444003600740303190304c52010069005014190001400240308120101482444e01d40180c0300b842c010142025510018201e4a46d1b48a9503400690010009004808540c400322a13940c3c000c2c10749654006d180c41d000300580200700000e9001d450300d004071030708140c1e150403106030581c880d0140c00c610b480e12000c1110002c6440032429280020080d400000c0c054000910250000303580009007035055007050115040410414002d0182c94550404864902000241c0a080b0340242c21110030712402c02138254000c407001019054109580345080102c55040307144590405e90031208910811031003001561312a110f00c0f50006400c1080d040c030340384524030030041d00f038007040510701c1c04180e05c449c1850320170039500240001d140410805031000b014814411800c00904e418814803a4840920030000d03400750190490f400440c600c00100036119920a07140303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 358310881 1250 358309631 358309661
    0x4020109060915052b0506010e0f0319051906090c0b120103081c09060e0c01140409020306010e0d03090302031b0906060904090c063b010e04110711150922 68
    0x482c1113940170002d0f00082d0f440750f010034031010180c00503040c80c3c260454104401002401d030100b1075401400355403035400c0156094080e8048010041c60b0a0180c20351651054500003044422800c2040600c082074101c43c02c2c0352410000d40c020b003540745000b9815213420440542d6500c401044000c80202c0c0840042165400c260828091003016030240c11030310200004d036420201890011075401018156101704503506020902c01d0503583c1d1b025545c00b40c0c060404c00c102c000500300280c91005030340d504400003045a20240b003181003d10a4200c0c500445c400c1c3c81c11885602d00094145100900c82d5009460110300d2190540d1950803021003160480b1081814a0b02c0d1800100030f07103031303014820500101007101200005018400e508080c02c143d4013604803080f00800448031000280d0304154040c0d102d148050305506c0190007000240c4c030885030900e06140000c1803101c400700d800d4111003030380820b2192030503039120052030700c0e44940b441d06a40e0054024a4501e4004d000345041c150341 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 358312131 1250 358310881 358310947
    0x10020414040b031f0b120102120a2304060504030201060911120604060515071703270c061305010305060607030c021011010519180c050120030c03030402010906091505 73
    0x5445841d900980745048140d80d00750034010008001ba090740318042d5000c241c240240d00052805c151540400d4024207224405411141190120260310380142d8090722601e540750140420190241b080f90000c000741d00c0280b0079007401c480c00444900031400d040300c43c10001000603055640fa070f1700800146c00d000713001510040c0e10b4201c1d0401038200150031207003a481810300070b9800301c003d000d491103450781e80c0030361711481c0074130700481406025030b0031000d443d00c00d6804140055581c1c1d4090200300c81d150307070300702c1d220f5182c08001003c1e18400313032013207001d502c01f0844032000c80d500c490310004180d0103441328045100a24402c548000300c0844180a6500e800280004440c03095000c5c00e02c0e07440300780c080c41a81201080c0810f0b00342444001003005100c26410001ea500404003003010764810511207941580c411442c500b1a80039002001003504008100800c540c4c11a00c0300014140c24504141040e040130b0100c04c4100004560009000010a0300741c1e903503441c1c08420300c48811031204450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 358313381 1250 358312131 358312183
    0x90806010b210117100504080d0b130e25080d03020a050c0304140a17060f090a05010504110111030322110612010303030501090c0203030429040507060210020414040b03 74
    0x80300c1325220000141900800c000c0d40344443d43d9020752405180c00c44102407800c440c0801c08001010000c100781e8101c0500c500ba1001d50216218481504403a4809020116078551840d6002201c456000007030102140d41070020100004800c8a404003600f0016590150950255854050681c00c54100d00c00040d001c210b000b0b107061ba1007422038003a11510001c54aa280c07201b20303c2c03d0000b807036aa0740c0c80000014541c40010040e0758106058805541160503c0d8032100d00b501d2046400742c03007001003130a001e201940c0c44181d101017900c00760301850450800d4500c807900c500c903008010f942503082c00462802e0201001c20585440c4000704600e0b92240719800213445030b50b0900c4113501081c64400000fa00010600075a000655a40d000c0c502e1682c440c1c7d074250b007080c02c9007188600602c0d26085040b1500b0341c107110501483c0190002c145a500d000740003490b1560548641e000c003070042c0002c10041c0c0d1100c1c00000c0e08101124080b62a4100d4404a490000d50340b032450742e03a248210b4904 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 358314631 1250 358313381 358313399
    0x40f02150c060c07120e0f12060105090601020610060810090504050d0f02010e03040501051b0312090c030a0c06080406090501020a120f02040803030103030503040c15030b030d090806010b2101 84
    0x20804010440c242c032001c0d0350307001040d509030080b42005000c03442d038960a039642c64415030345003820074001003400785250030b080080b07500000c03c03248001c010b80c01440103000e0780c40c0c100780407a4410000d100404152030030390305544440f40180306420901c0304120202d160101d0503031081000e0510360b40b042050b450503042a640c1d33402400b030010041075090040401c158418000da0780c09455030002945040e15200045410b81d001600c1c448442e80044540d5811650900040c1070a00071624040580d060110040d41400c00517906036100782c0c440c05902c40021010b4892404951107030604002584c2c0f2401d2150140c4a180c00003086944009444141d00e9000318203e1000b03501c2d01030800000c1074042d01c803000c038800c1c1c0c0103158071617006000400000c0e01c950011940248130b42005882e8540c2c03a0640c070b43c035030004004180401c0d1580042000c904003000809a001100d103400e200840c60106101e0b03c642042c054426210000100083d40f0003208842281c408240d18403590f0640e505c0c1220 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 358315881 1250 358314631 358314637
    0x6020702040c1d010804021f0908010603051606081b090303090a08070f08010515040b03030c0a1101080c1606020a020c030f0307141c0f11060a050f1b0909040f0215 72
    0x11510450707500042c55840d4031503805e983c81160b028006d003691083c8015400004c0c84840700c1581046010100410550f13000e0242e100210310070401091130707007103a50321004c000b1541c0d0400810002030070100051041d012400c840413031080c0c00065074074450b10003c6800e512540343d0341d5411039031840b00000c03051000200740c800c0710000c50012000944409555007642e806895007003071307465007038440d82c80d5240c507034860841d440c4e006084030710304042c0b00354003030420000050940d1844560740007020079580240700a0f80c030000c0414a145010a903000b0360107807850f0144083d05250b070215005101d075008102c105034002009044480340b40749501314a64a0313104c403c044540701064900c0051f108c000295490742242c01202061050010b0310b800c03504024040070030030030010004024240300c00c05114040c041e204011000c03c0c18540b0701c40c001a05038000e881c04d00c102c003407040b00c00d5900a2a00545d61001001c4036411601e488500781342803003040213800070b503002c41101007422500c46d151000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 358317131 1250 358315881 358315907
    0x306030f14010f180b06120703030509010306060c081210180b1203040807060f17070503061807020d0c0f020306090a120f05030403110106240e04230406020702040c 72
    0x780120f4418040320001c0e00c1051030182080a000702c90b400c000303090074000f5588004068048001c030181c3ea400c0d00d1038600240d200343e0100d4000100d070000e03540e1600505001d021281821200e01280f50740e810348520490b59001a01000140403541741c03214038282000a0040ba808064040a0426090002c0010140041c40340d1008d540d26035a40070080151400c444200f0050b05606107082c00079100d403a02d000c1020308106003010780d00e40e005180c2040d6802801c6941d60240c0382c0c500501485500000f105810312450780360b05c10000100d81c0001c8000100c00b1a00d00300c1601d44291030210015104504001d5150096400f00221f8040000b2140d00e80c030f0144000380d140c180303120010b46107050b0b03112044001682c100700040109024550300042c40e54054000158241d9802032400c4001401124a404122480d044c102c03244d03101c0203515100c40102c82c100400b40c0364001c0e00042e03101c4008a45400c040302400502070008503415104000e40161090125240c902e41c0180301135000d6030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 358318381 1250 358317131 358317133
    0x14040f0504052401140d09030c02010e03070806011205190b1b03060303040303050702030c12030301080717100c27150f020a030e030f07080a050705060c0307120306030f14 75
    0x4001881000c4a4010070604464044042c44040083c0011502042000744010303e43c0400c00071400c0303040c201d118080c0740324043e0342c070112208d60340d1000400d1000000d01680c0b095006201c180a8400041402d41c1140c20050a41503c03040d1340ca455400c004503011008842d028503800d003820b0000204005109005407203007081c58804031418120640410344510750076500610051000901510042c080280005d08645441055000040302c142c2698158855038001000400c0200000c1000c4405808050304040c8008a030034030196803403882001c046006500d900c80440310f207006241e81480d000c038aa01000189001240100c0e0788140c1d48512010040c00d85da5130701001d441280e2540d426142c0b036014000c0c4a03c1798504568112132041c0d550751501400e00e00300ca0803542000628002c0c820040a060040100c2c10000c1c18070081d64840e0740104d80420231422103600200489102c164404640c401150902d0004c400824a03a00001c011903c004582010700c0351149841c042d08011030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 358319631 1250 358318381 358318391
    0x9030309070b04060c06090c03020405310f0b1b0a090501090f0e0403031a030706020a060506010201050402091305030910110c040b010c0f062a0305060603070f08060114040f0504 78
    0x1641040c00c502c507510951340010801100d8900140c0c2c13a4000145c841e0080d285040030b41d4482e00050308845003654081049051010003444900250800354241c0c074903003141001104140d10780e403824100141004002c074450320300046500701c90305880c001c02d5001c01d44660b282c55200c400038001c03800724060f1034081440d0000015291003058003803015680a10600480f81d01c582e58254081c01034800c29003901c1d070307251141c48801d40381049420000c208680c020400035905041403405c5030405400b0b0b5046905010800c4007507210b602441c1c0c2c02c000c214100f968110001e080c403500b180108083d850380500d03844035540a079035001c41e000322030a000304140c40504581104000496502401d21030204107156500004110040010700701c441c0034410206413114601645103610302c02504220003240600d100b40d4070958503110b090f0340580240d52140c5181003015001d07000e03422a40d00c52082000402c00140c060f4810400305400c41841008641c4940e1a802c0c8594024114018640214602 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 358320881 1250 358319631 358319639
    0x708060a0b1b0a200a180513060f0209040f020403031e09090914060a0c080c070c090501030b04140a020f120c0d150b0a05060a03110403150f050703020a080129030903030907 76
    0x40c805c004c1c00c5a8003580e410214040f540c08801c0540802415070100c000134100010100301e8501034400401710f02c07000140d4a10a01041000b00c1d06c0d00e61940241610500c01480041e4200f00b0b0124254988070340d003814200c2c0c00e681200c0c0c484c140d0304030900e0706d401d0030301810400440c1030785051480d0380407094800690707480b40403008880d04c0010220000c1c2c90078000c5800f43e540b00340248071581c0101d500003000c07a02d445140c030030b80740280d05c1200e040c1103180c01c20051200d1082c0084034a1030990141c01004001d40028900c01c1e2038640491081d10303203400707400110300c00308108010420050403511800750641800220a00301c1c80741c2c140f01c01c0c1480c40c900300768909404240140e40008068a091030f10f82e04080340209803c42e00011044d42c20007001c40801c1c0e200050301040110008041950740c4003210100c16288090f10043c00d050050240350b613441d800c1244513054032555010008004102e5441e1000301107418a03031404560004240a4015070120003544920703850720480d048207a607 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 358322131 1250 358320881 358320889
    0x501031217060f041103010f2409090203150d060f0605030f03030109020c0f0a121205150f0303192d02060c0a02010617010509060708060a0b1b0a20 65
    0x120501008489031600c1c00101c1034a00b081c1e5a00000c24040c10001c4d0751884c0311580c4c0300d190b200384c2000321083c0014104008200c0c1c0d01c0718040b60302e2144110700090203441a030180c000c9507280144910541c0100001c0e411a01ca0080b60845950080400c6258690b030b08100c801850075603101c5000504110b00420241000240c0000c000b4401c001903155030301e0400003000035000031007103810900801740001180f41d420060500c03440c0c05201100360881c6c100001070024504481d03a0302e0180d041c041006038000445400322185642030f07a17a00a10009080022b0961013504201002c1000c04003681e01c80039070040c102d0101d04030300b1900480391181e0b0000c007405243c0c5000701c071005900800000304080d42c010040c015040a900011400a483c1c0c0202c030349080042c0d10504450799210200036022004114044d044181c0d41010843e41c2400d0010851141860180045a000010307500b03000781e4181550740c050041c0b41d0150f8003054800d00e000b40075140717814444090070440d402c0c014260300d8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 358323381 1250 358322131 358322147
    0x2a0a180b03011e09060207020306010e0106230927131502041a1303081b010b090106230f0d060305060a15331110060305030a031512030305010312 64
    0x2014140f04004640758100e501c01805031071a00300c3c0c001c0d4083c8582d5005072010080c1d44d0103001402d24207004d640c100a0010801c102d03c0701101c00b10b00c550031801c1203a0806900300c0f11500340c142c0c0c001c0800b0f440303040d00f0300703141544203d800d1002da09030f4101300c21110846400191710b03110342c2166000303032070b611155000d0340650700490041d05280324007036404940800003415001d51034030010561503540e8540f06116013003240550429540310860000c000e1007881003035800303001112103080550401000404030410511842c2100400448920341c2c004190f003a034050503030f84400c0d903a0300c0c4802420391020386041e1104544500c210030100f01c441825003d43d01400103500d5000080c079280004150444c44000c1c24200c20b6102d1400a4038403009002d2160000c3c0c4540c0c681030802c2c044034003030034a0720f01e8049851041d40c1c580031060002800100c2201c0000055180c042003000f580c0403121071400542d40588101e04817841040c0416416812107412a4041c41648803940000082507607000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 358324631 1250 358323381 358323401
    0x70519050901060507021f0201021908070c02150c030705010b030114010e0610030608010f0c11241f0305100b0a0e16050c07031103060a0c022a0a180b0301 68
    0x1c100340103100b000e00c00d0000d04001c40c001054807100360700819065260308070100d107400c0181d40028079190742c50b11103052281d50108134030307210840b4a4440802007400c1011070000344a8071615000032540740514040c0c0d41550020700540742c0d1911240303461402411031a020305e002e0350800c1104c66a240308074080c141221070403161000319945000c00c1040c5030400b0031001d8181a03440740003288211091240182c1030084110000300039111040c042c0c4800300e1501442c0c07035a07000312100c110703003810480c0b203501d080c9003095001c2040d01e0305101c0000c01d500d4011001d2401c00c40c6103000041c001d001801811000c0c882a04000740360604061280c01003003806030702259a2440c0224071994460118256803555514105040492a82d08a8100b2181d035000784e45d0700541044001151074103102d51600200c3c00c80742044071140e90100a900d89024443c1601e40410701d082c1d62204541d50018619260340060103142000e488040050486420302018091180742038141001800e052080300070b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 358325881 1250 358324631 358324639
    0x20418030516260403051209031b031c0302030411030601060f2a05060109050f01030f02060306040908160201140a080612030c0a0c090506030705130902060403020d030f26040b1e070207051905 84
    0xac1000704007480940c0342d502d4002501803280802940202c040300d20504c11082d034942d03015a582c2000c1c10302140c0c03204a035403d42d10a421050041200c1a000b0440c0483c1842d5400d100f0303d1700d001c0746000303208080881d850100c5241c0003902c010400c02c0209044e4141c0341552401c0065440e1401c00c5565505c003400010803d000500e10a00907140c050040c5900260091000c2200d105a696440745c6400c0b00c01c101c4115040d42010004640c0c010b4109507864002d0010700b03007003098012009100d010060f0400d4047d02814440460081c81442191010b003108012510520100e16103004680194421200740321b14140115259140200d03803201251401000c000950b100b030845040182440c2008036807040d02000008010b849900b01062894003d0300c1d10550031320901405802c554071040d01c5a070909c0000358001c0300324089002c10303421580110321107046543e82da404902c070003405c400042e1401c02e207104001029500155000030350303000f50307003488c00300344d070461403001c000a81d020f03203544 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 358327131 1250 358325881 358325893
    0x4060818070b1e1309270b0a0908070b0916060809060a0b01030227030d050708040612020705010e0c0a08011119020c060301060c02041803051626040305120903 70
    0xc1c0c001e041480942d40ca009083e074600d0a20a00000021411207038410200711313441e00300300701038840c41c0e41d07404000d08200020741d1001d5519603160030b001c0c0001040710a94a558165000601c000071043d5054158021440842400d01015841e41c03240c0b041c8182c0040b82d280031000c02d41c24480d02401d8051100b0302c0040c80c450302c8a60307000c0040c0400300710300340c109a42031140030f0b0a680010442c0c5211041c00245103001400c45090508181e42581d00b4000d10004015040014002004503400c07140b05141000d6180b5003603002101a115051001d002903080810700c811048000c1450302054038101c80304040325640320503c0b400d03030f4542840040015001d2103030031603440c060922512448018415610b0101d02c0c03d00052998100303030404400142a4112a401c500303082c880c203034050040079002100c1495690b0020700c0e070710454483c480c141c02940e0b518020080341001c00c07034803a05c13030070020b0582a440d6807081403290008c0c1f02c1035605204000961041100c02e204a9148030405006015 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 358328381 1250 358327131 358327147
    0x190e090f0601030e03040e190c050d0209030a060905030d0b100f0809030405030703030503090d020a0803071b0c09021c02040e0402091f0b091e01201204060818070b 72
    0x459000241010b040c50380314030b1030000d81c000520003030020340450b0300e000d00141041100c441d6440104984900c3d89407034146034400d00c1b6040b000f624012040e546001da940e0703800707030042410700c8450342d4003d002c142000990000c01901002a0940050010040110419070002c0001c0c00360008100030100b8103011070842d000780308a1805a010f070071031080324501503654003c02d1610850758404c1e00024400b00901045043c10700074000c0300c0000d440181651044c0307444020880c44040d001c90144001a8042e0030b5000c0d2079070754424415041050700403117503a500140e00103944400c0010345400800b1040c1d0040fa1a00d2003039a080e18031089180015950f140d0070302041300805820142c0d070079101140c01c100344004404010140042c8070980352220b8a00c4144818040c07200f180305004406001420902c0c4d80c840b021428401100b0000c0e1580c611601c0e1403400c191481c01c41000c4884000380210b40640c0040c0a1406180d00000101e0340d11981c100c1141c8680a501410350604c20802c5080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 358329631 1250 358328381 358328401
    0x31a061302070302120f030405060c192714030c09091005090a060207110a0504230a09060204120201080c1c1e090c06121109040e0304050603010902190e09 68
    0x1c0003d102e80100c86080c0d44441003200180c00c55502d51031300706800000c01040144c203021254201c0e21480c900d40c02c20315104881210a185440c00078100b06918030101c060342503250405c00c40071203080813099840c2c0c0300c8040017410005034280340d02a100d01e0004d04107030305040809a2048100c003000c0c207005500891490090f16000d07008007294415481120085200380c801800050f01c1400100207204900e010320480e481c040d40201c0c49107290007a4003042030f03600e118400190380803081c0030b0869030360340324901c0003401c0020001d4543d51000c00d000c59504025400c850006000341c840004030b6841c200a503c1501c219207817940031400f40411840e001382580c10405142144a40c01184d060402c03002d4000c40309001000e8450a210b503070200309440d000240c4545c142130083c0305110842c1400c494407040c5c4200050540600d585403440c03000648103000b5540500700043c00746640b541e44007240c00c080d4108000d58017080c1010f4031502d40b00e500680203400c2d820f1010302080003c7c0d032074500d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 358330881 1250 358329631 358329637
    0x1a15030a210c0209090d020106090e061602030d0608010209120a2d0803090105160f090512010f020c1014040b01140f06041e05030c1f02160f031a061302 67
    0x7031051202d00d400000050f0b981400a84c031408a03c40180301c8821040d000030300f034442c2a800106102e01d0310910311403254010034496840303902c5964031051b41100c0d50782289148589001c43c000302d40b401801040004041d002800307280d074202c03001c5d032600d585040201e072143c68209000740601003560703e0b00d20f00d002d0b40d0680b1002c0c0720b01d410143c94072244e90301d522140e6441100e0700320050b5540c004005060540e12080c0b400d0980a10302509a442c5920001d40103e03060300516100d00300d41440c646124200350440c0c9154044c42c3e406540340c00741c081540d9614800c01030b1118865042c41c0c000910500300c0e004071071040c2e03000700c2802210f03480e006134401001081952560880c0c4d030182621076070386070f003c0200014980c00c2500b4900d03024481d540e24880d001c03a08814402c1e04103101c880c08a81d262001c104101d01745000c43c158002080c00240d28140c45000607001c00e5500d020002009000b011070740085038001d0070a80d1070305600c4294511302c00c00440c1c145a000700b14181d480815541079020f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 358332131 1250 358330881 358330943
    0x616110c0105072019090c030b0a090b04090510090309120b0604020f120924090a08090303040e010b490f020f130f1404050703091a15030a 61
    0x10391904141c3c004941203190340c2d0035120389000041c07030401420b00351748a900941f07603d0780f8082050138105000a5002d594620401410f1500c68444041d69526a840001255408400c94500c0e54002c1130450160660b00d20940203c1c405080024004444004c04400c60340c0c0401e0501080c0d4558007080000e4011416555500b00f040c02030310308400725807541c1c03409110440010200000700382d42d410700c0304030000c440401c2d0100001c1031000031500002e00c01d1a141c1e2103040e1305d48603502c0001080c03450240354401c07101d500320180000340b60740c1d01200400812204c690101c00c50842c0080340c0610001c047c4543e0700f5813142c00c60025081501c2a607020050030021804035841000701c0c5844d090360014100d01d4a0140009040000000005e448000500080e40c0510480d46042800381103034a2486605014585a000143e009846503201124441d40450191100f0318005844000b580c400c4404086140440d42103500525000070440c07856540301a40c010080600054201c0c3c90780100c103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 358333381 1250 358332131 358332173
    0x150c040e0c0c0609060f130b0f071e090905070e030a02010806060c010606110118051b0f090106030c11011506030207060b0a080a03090905040b1501110616110c010507 73
    0x2003480003448052006a0054010400410450070004825114844090b1811441f44c480e044250700158a4000070ba03804811001b800c030b07103a900e15000355806e149404150348032821468021141742d03086100c58042d182c0015003005240e40e0790301d007944d02608110045601d5480505010019841181120351009026012508002d8130044950945001da0840001704921044000c480c0754244200322410940c1514041240155220141c44010395504020700803c2d0b0f1010510301d8442c00b0040c8013002c005407100013150b1303440b10300900404804d500f100c00206c9044000e0410031050003101340c3c00301c0450004008a19000b4268001d501c1400112400d03516104024810382d91014000000c00d41c1d14050501304601d40740c0204440c403c0e4201500103032401c0c0601000c9044050401c1d80f0040e212241a4a241000c00680d458140003010128901c910f004205d2044020514402c21541d9a00d80104c01c04142c801540c03260001150540040c005200050108000d8070000c402018080c4e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 358334631 1250 358333381 358333387
    0x80a0c090b1602040f020c0718060303050307080709030b100513061406181806100503090c04020a0c021504090b010c0506040f020d0506090313081b040213050d110102150c040e0c 78
    0x7456170140e03000162141754941009104000603001000c080b005003407880c904021207411581c000e03241c1d01001e81000d042100c0390000440d0b03d0f00803a100070207103030040980401850460141766501000b070140a000703445608100c05404402d00400094481a13410307609005d4890050040c180c00c004030215541c603008104210a4940010724000700d01105d848212a2601a041c418081c07250302020007040320030400c0081284010070041c2208204480247c0e494400d040f04588400342018040d40c016a110114444580c550740100100e0300c040500f40078059410b00150340490080710007420319008075000a0010310014141201544020952601e080c3c0c5d64a03550f2906204071940c0046903c002042e5003004c4d1408850401441908000c040103880180c2158034000c940740914015500800d040f11240b0b802406103002e44405403801c1c42c084101c0c100b20900ba5951850207000d40254036004040d008002845445414044a43d03464240350041206d404000201075640303240b003c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 358335881 1250 358334631 358334651
    0x2011b08150411070201021c0e091b0c1c02070807050402030603120703020102091903020607060c020309060f040f0b34080309010203060a211103010e0706080a0c090b160204 76
    0x161044070f2043c3c5403901d410b030301d5490600c00a45084500c4410b800d107d1080754600e507005500c40c0d0b101503502002d0365558030f1500c0e0382c10305030407241020840c1c00e00d004011800c0c941520300010b1052890040941040c6000800c400580e1910341c00e009055460300813840500c02130500da0000c0d40c1060014080320b01001c02c0d001705514942060204400503500010400d00c6494441101240402c40c044d0641c0f03207a1035540010b46a20031030400904154498200013000c500a2087c0e450602e0007400703003a59030801409c00c04140d441405903000c0780039101c0001c1261807c007130554003800c1e48001078460829800032078804040b542e0403050091424201180d001407080000b1350b0188071600700140c0c036030a06404108102c4401d41100b94000500c04074072003041540c10000e4126600290506c50070f00e59400828094424203c1d0071340241309000c400500039034080c1c1000d104800c044006c0040100507002100e040d500c0c0c0c0f007008900d0f082072050f8808038422210400c0c0c0c052000780001511410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 358337131 1250 358335881 358335889
    0xe04080d0608030a110312040b0a09020a1401080a1401031e0206041701050f0405100e07080a0f1e030e01050f090909010b0a08030310030f02130e0606040c02011b0815 73
    0x1e503000b91805400100320040c145030003018828410000320040c0d030034180c09441d10200b5030710061014081c01c00070ba01184030300103168051080b007500a04482d03592521080d60408841002c4000c500280500340080c03001c4029124289010011311040b4150b6469a120401d0302801904000d03035002020b048800141d42b400300400c01003400101c0e240321101c621210600310b4400078075403c0d420307404000b000005040403502c0c0c2d0302d1b02110a00064540b0801c00c0c59440e1407081d03040701ba000e11849449200303006120700000342242c070411003804015285660340001032900f52000740440c16001403c0c01960280d030103043c0317003950b1110550070080140009658505e0941d03110300140d54900e100d00090500c550f20038081c1c0807031f400451460402e007204040c0d860280c40054000b40c47c24401e04110350f00d560200d512002c8445092010724000b41c100764070b4000580703001c1c1c4114a0b2074407180942e07006020b6840008120046403260b04546003003603811711001400202c2c2e05c46141304c1040240c0e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 358338381 1250 358337131 358337141
    0x12010501081902222a171f03050109020f030d0503070309110301020a120509070302011e0c02060706051510022a190306050c0f0301150212191403010b040e04080d 71
    0x104c80c41c804a08840c0d0307101c0740c0203120568071049800402c1c00481040443c1c2054040304050b0320f000503552a55942050000c822403000031040480415140000921405411a24007540200d0b00040e041e6000d41c02c15035500a4074421401049050000400090081d48501c2ca445e001e410407040c01041e0b140028220b03800380d01c070400401c00682481c002c0300080d01c02c255110389018018150705040d900041e15060298400b01c415442100404215910034806082303100e50190502d52076624500e40f200142c50100c0b40102e001c02c2e2072205a040c1d10340502200c01c0c0744281d40141c41c021038004140c100c0c111001c0c41e05101d0040a00c0b040740581c03a12010069020f0f9240c03100e480450a500d404002c1e94409402c400c10601c05110042046800204407070440d00401d03074080040c1d11a1609038141000c610f50b100000c200420102d81100d0038030150005c1c0001a0703501d201c00c02100710244003601013801403481e60807090006000d0203c48105040c0c00c107014410b07450030031075143c0c010b0058030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 358339631 1250 358338381 358338439
    0xa0312180b01030b09010b0a031406070f050f09120105071106070302031e0604140106180b0901021e150a0507020f060f07110a081813141b070204050a060512010501081902 75
    0x2030010804115030f103a00b8040b02d50416141c2c5860a03c14dc20440018054001d4482454506400040d9407000b6510305a0011350115404020310135860108000780030384016081d02e00c2c185c0101d00020325400c0c42803007140c1c46000c01e10100316000c2007842c5011a094002400250015961221440f11a003c0b4680b02e00819441c4c1c0d074003110340c40c8885441d0f9868020f91011a116070184a0b000b003580c2c01091009540c00c1140c50025141501c412942c42d124400403070302c440301d6140c1e0522071240016007100b03202c0d8840303800b00d8100c00018684070390b07541d2088514540c1d800e000030109212030312910381c100c1501c00c1541207803201105a101c104041e40404244481d0b0420581d0303100c0e00742450a0b40400b40d030b0801c10200714000310a58182c2c1002d01c0188400c010340b048514001c00c40d0282016110081d402600c100100d140805540700100410b0254034840c0c120421411010801401954142d80440014110f46195a0303074800004120382402c9a0141401c60141000441404003c000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 358340881 1250 358339631 358339643
    0x110903060a0e192a0f181a130213050306241c080f0408150702060c0702061206010509130605101706010c0201020f0a0312180b01030b09010b0a03 64
    0x410340d121a0580380c9146055010300f6144500000c40206602c1d0008102c002c40f1100c00b0604004440c404040c0c4d00c00940000e00040050b610210b031600520304580110915800200f20040d0030390030f109480c41403400100d40c07000c02e411190301580c4154000c1d1900381c22800039150140c0d2038400190a03d6000c0741e040540c080f0f2400200300240d1055400b14020409403409041c403170110510403400b1a070f1b1500a0003c000c001030541d81c0e14402000c80700144014400e84548004240100da0043c00507a4000b0040c455040401d5001403c1d5085568403940180403616001500800d91040030005024a050040a110510850f03c2c0c11841c07090b00e01203ca00010788609140030004a116515840030070481d07070002da00031401c459805d050300b020090810304514041440101c0c41c1204000d0b00e1095802450b490f00304258010030640c071415201030313050240007000c0b107128090000d24040600f40c281d000340108046031901c18440e800402840001ca6280c2c004e2001c556441d41690048502c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 358342131 1250 358340881 358340891
    0x1905041d060315011a07030c02060a020102030702010e0c030c040b060405040e0a060608010b090a051017070504051602060402010c0804080715030c0207050901150504090608010e2509110903060a 85
    0x85280900c40b01200c3c0802c034040442d203506161852403004a80900c0d2030450381d0029441d4107150050341503a940503402040c481e80c40b01e041d50028007030b4200781c694801540c281803418109403408a0620f009003400b0f0010058080d80310704000140c6040d0012680040c070420022805440c0e40c0030b4040941102002040e0b281d45c00c0c13621800b00d4100d9400305280340d01d030403200c003e00d64540b1411904400203641c041340ca0740311303490425080103460b4089070080c0c800c3c0c514580007410100b042401c81384100d804121503034030100340d49444282c40000100580240b00003c0056014403a20700d060343c05440800d081945501c4000d14040c0940c004072081e82a88100d1020a61316020b031924400c2980b005d0805d841c640400b180c2c079620180121000411100c640b540c4540c840d0090328001e02081c28240308c1c0c16030300c00c3e00740e0003000200da050035280542500344004900800a40c2184401e01c0e031080f0003145004034600007840d20680440d07401c40d0800401c07a0b2950b04010b014041c007084000054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 358343381 1250 358342131 358342141
    0x603010f180204030b01120311010c0801090b01180e0c13030c090b0f030d081f1401020d1707030f0906050a05100503010e0303010e041110020a050615061905041d 71
    0x80c65290031070203035480900400003030001035407900c9054115001d038915600010340d00d140648150040400e070600d250f181c2040c0300c040c1030384094083d04968840c0410011000040011a001c817450260350031003034003000e010841d407034030880c00b550b01c03180701c82c607081c01d10f54444c200c09003014982c0e0080c2c911040840062020008500c24031b081143d08844903a2a081070b02c0110346c4522144120605109084001814003100d100c440002c0030745000f00d1034821030312001041c9a41d1b80c0359007014010b201310b61580c440745001c0c040c0072041000d04201001d542c1e441650487c06001c41060080c1216160614540020020302a183c012808010301282c03c0c686000703041b40001903540000e100c0c3e8140090041ca15601000310f80c1507035864545060f040e5584d0900a500705d0141078813a4008125010b60300700305901240300c3c140c4901c40c030151200790325070092004480c8e8020100c2940030200300301d4040d00780040407021b9600d005904000342040d03070340d00c079200001d6661034940f00001260b408100d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 358344631 1250 358343381 358343399
    0x2a06010e01080610140d02040f02070f060b0402070c0e040c0306020a051902010b010507030e04180f03030c230706090501050a0b12030a0504060c05070b0a110c031b1e0603010f 77
    0x164040946420004c00034074007440c41c08641c0c1c2c1689828040e0303c200046400b0754680b41c120b0b0484501e1000155030701e20041c074010017401c034401c8c02030300c0592402120300342030325003402100d494a8100b900303181040d0a10000c5010b458010341f0841b000303408448000000b54450015013042000e0f620f0716512940d144c4000041521100140011a40340421820442c2e80203416180180c0d09450030480c0580c030800494010704800c11541d200d41034a000325000c101c030416800304501e110340d8040c007050241c2d40040d00d9403070008800700340ca24035940703102c028002200c1c080e2681c0d0f8002c1030080b501907074503110341c0d00315801a1240b10a09480344081c0015081441c1d08940000d4500300942c600400c4220003403450183d400341c0c104000307488415905214042105501a01512039601da40c3c0054503006482e0000c0303941200642e00504400c0301941c5004540603030810010b51110701c000102c034040004400b0fa040030398000300c1020075420340e07036182c1c000070b94064410800041401c90415803e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 358345881 1250 358344631 358344643
    0x504090507080402011e36090209060301060c0302011d010e1504050615150316031109090a020a09120803010e180a020d021c0b060a08030f2a06010e0108 67
    0x1d0000d2145110074000140d0741b1042d020350301858a0501900e05c400d80b881241d203100e20030205031250b640c130342c0070380383c40c0d02207a11402410307030026803101c0ba80b660344000c0c4050380074080542e40c1c86201400100140c9000d02070003031410744240300001e0341005d4080003880000c61a50806000e070754620b051036a480040014601100c070001260450340303850f60710150359030030040504450075a01d19072850691950301c220407011b259042d0090f12032500d0a080d00092500c0d03400403002906101c0e403280786c502d82c82d0807910903100c00303003029030707599030303040041010b5400819410b0800000000014448864803403890481c0c0c41000300507543e52424070140c8041001030500c03008648000a443d0580000050310305150307506440240c850314050002403288200b50300d1020000d1100b081c22000c01404542440c4a600120350f0510000d4592a10342d41d0b031300982480703002502c070400188880d028605076900341c408844206c0ba48821a2081081c20040e080c0d222244e86003403100140b144107024010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 358347131 1250 358345881 358345891
    0x5311505090105060109051c0f03020a050d05031b0405240c03040f050405060324040c0317030619150804020a03120507062009010f030e061815280e0d05040905 70
    0x50424100c1a49840345c1c2230202e80d1004201003108881c080425000313000080205400200b510040400c0c2130300a0f205600031035030664240b0807408541030b00c0489109a1f0155074020705000c608030000c1d484689005000d0303084894440c828800451000320400040c0040d103e01e91f0149032003844c1800b44001e4a0002e0105440303500400300b104508046d942d881e0424154a1607680702035101d50620b0000c0d075500d0b07080a008400c11a40f4a912900f80c1e10040d80145070654055224511011b40c48035540000d0150005580c0c810b0003080c0f0040c401c46095401c2400107044144d125076a80d0b454884800d0350140b0070214201041e0001448400e1003a08414081041040e514400815248d1a03610400c1c0c199814020140c00340302c0040c1c400c0d40f110001c51408011252641485441031040605420101c2c48500c121910300094490280d092800f0f8841000b80e40c01303214021240000030341c00c03407050f4148296501d0f540a01540100000c02c41c00c0b1154440302da4541c02c1841c0c0740241c4000800d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 358348381 1250 358347131 358347139
    0x807091409030f1c060e1906241101020c0114010909020a0611030d09051f0b1e011812020f0603070210051008031306030531150509010506010905 64
    0x40115010000c001c852002e0f60a0700d00558541c1c1c02c0103c0346090100c1102c00e4803180c5401c0021983d894080007071405444042e04d110645211a510001034607042d01614000c0440c01d444464515036401009201a600b4248660900001030040342280c1064040c2c1c00107a4490400d40700390710300e611010380580100030b0241709081e890380120f04c0041300c912620081100b0210300304441da0302030068455001006100344640585070810f203070341341d004441020724a03403414042c1c00303505030a1003111a60103000d0184050760b0b13210140341c0020051003031510305010048581c0141005c0200414019280c0c04001400ea4903450041c01400103004181c0c03401000d0403c1841842d42d000901d0a00100030381ca0041030a82c4c541002c640c0e000036561040d0700a21020803d43c0c0030500610031441511816901048969030302c103110300b00c2e00b5601248041b0343da140000ba034070104c4c6904a08950314014641d480849400d5480c00048483c00c0764640d519943d54403d03c07480c4e42e4803102c440c0040004071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 358349631 1250 358348381 358348421
    0x109030b2e0b0304031b0b0717070e18061f09060311030402010c0f0c120602030f0604050f040602031e0408090a080303060105250506101403031603050a030f06080709 73
    0x4a419082d41c88042d0020707041c82000c0121102c0c403440c0c00c244d544a590f00c560706024500b44032070090412100020404d800000d403800240c400e40c444c25800e560580d0050000d60031800b00d4001010090010708459040416043c400e00304107203943d8100d10b1100150b44440442d8607201008044600d03219160031a00d41c01c0050002503a44086d2407080300da08000c11030f80386002850302e6450b0400580c404a00d240c180c480403028446558061803256142192018095642c1c004102c210380048454001c586041000718001c9211503015590040141c0c04400d50b0701075007211a02080c02c1114110740000300015801c0c0135080a080000041422900440c1103003048000030340320b40a044820521402640c118084000020725801e04058125003620528200504e0301da8100300c0500441c01c8603580c904d104545c42c1400400c45449101d04804180944000c0e50211900e9002000c4036007055141e0b000c0000c2c422841c401d420040261800900c9103910701141c1c08103503040340502da120a0b0002c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 358350881 1250 358349631 358349639
    0x30e0c09070801141f03020306010201150f05011e021905101a03011b08011203020304050d080408070f15030c020f060108100b010c080912190c030c1205070509060109030b2e 76
    0x40706845c1ca001030a041c05a200d40e50040102d0040091440d41c50301d0300c0303144000155920141905605460302039894001c1c99158640c403c0f01e58800804020040e07010b43c4075006101652955400314070b108406403408261100c0b840400d40b020034a000350040c05504841569103402d10500c0d000f0b0032001e6445215108413000903100480501c6001d12444504100d9810548244211005480000c007030040c6907600781440182c0760081d0180310524441d000021413449840740100302120741101c4640c812400c0300000301d001d01002e160450541c4500420801140d205000c0039001e0704da60f900038000c2424040b504429508031180090600c1307540b211180109884104444000d41b051b501c42c0030140d094803007140b4003500540801c508942d00c0c080031040104078a80101142d00034011407900729214280101c200c42280c00040c0a13030700c8560108060300f850300c1e82a90080050400c038510603a40d46601540d160b089a20300410840b207213450424040119444500c00b41106030f9460081c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 358352131 1250 358350881 358350919
    0x60609070f020a060614040b010527061b161203232a070f050906040b04021e070218070c14010b0a090c09170c01030e0c0907080114 58
    0xc0c005004001d40381d010150224020800035000d180c2c0140100084c5d995179804194140c5002c1c010351042d420500315000700c0d07102e00e013034500c04040a13000d1800600c008000c03c0060f050b03000c001b500514180407400c140a401c080d0940d80c400b1410103009000060b1200c1c0c03080a20f03582065190f29400506a4046540448031503440c103241c0354902001d007503051266415002d01c110030310000d03d404120003981c6615107a401756084040d400c0321100c40e12402c440403009002c0c0509a0044103441c0001c0c55031074282c00c511030b18600980014600380784240081c060303040844403824101c1d80001c00a04605060135080100c00085441107428113103508000c141e80102070f0f019001c00e40556030104101400c0d4410f48050304010030000d0050307950a580d0002c0c2401c05c00050100da1140800500111180c804002c118000400361009007030400041d801041148040c011500c074018a001e40e0743c0300c040106004640940380c051441d8074184005019000a042450081000c00700700c2c0d201c814 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 358353381 1250 358352131 358352149
    0x80a06050603010e010c09080d0e06070f0201090b0406110c040501031a0a06050a03150509062e0b0f03180c090a091109150307080f0c040c0507050102040602060601110606 75
    0x2a0068021445495040000303000d020070224600040d4605512001040e030040440d008944862080d2010000802c90995900b500034030420340244080001e40f00041c05c4064045150380705041c01c0d940b06403100c0c0480460b42250704045c0215403c0888010174800c00c201c6450721040440702070240d50305641d00e42c104c215040d0040b8220055000120342034900c160000300c0230f4003019102084003036407401c0110050230341c42e5400032203034070780380208030080004100c2e24410078401558444c4c40c690030b038405040b10f8100340144c0c5039014201002c40c280441130001e0400c5603038000c3e0a912130400e18403058880c0d058090710f00342540084009405915202001540486a000b0010340c0d0021820014012407041c00b140303502000401c01c01052207588040c4028680043c1c0840d1185512090303001d40d10550078030300da00c14be4000c407800c80312441c0540056941e480c0d40c1c40c0517400c1800f95661907003a87c008e41c0001015802c0341d0104149940c3c8054a031000c4002100100100c0c00c2210218600c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 358354631 1250 358353381 358353383
    0x60504141306050c041508070306080604050703030f020c0d1a010605031302061c09150510030c0b0f1612030b0109150c110d050604020f0105030108030d02070f080a08060901050a080a 80
    0x3035143c1e000108056100701c01da03801880721590040189520030401451203104031018400b291034400003040404000803664031541d448001032000c503007180c40c00e0721100001029001184a120410006074580004038004140706040c000343e50340d20090311f1400399a058100004022050040000040e214449801c1e100e8060f00c0c65640d600c41d03401207100440d078145048440c02d040c11104000c00c0f4100900100d4070390350110400654690808099006419102c041c03c501c00200b4180a081c903424020807510210401d010b14080519204040602c51504141d628004000340140b04580501889600d44400d1811580306828100403da42405408141041103454040c0c1000c0115002003241c46150052081c40c0075801450190741d288003c440880c012070070005040d160707502880c1903034181d9274400040c5060202c0d156094000b5008008291a81c941d0420054041891800284101d08907552155003500c0c0440c28802d4190301030340568010182d0b00c02c1008800e0000c5105400d00f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 358355881 1250 358354631 358354643
    0x80d0b1311071515170c0a0e1807060e010302030901141f080319180f0f0f0b070804030b0426040509150a06030914100e0f03031018140a0605041413 65
    0x400030161260b103010606d007002d60308500c81a002288008406030b4442c03180001d070011200310f00203c1e5407903440d2002440b072840171802407041d02503e9030084d00a1948003101500000d03440300407500d0152950003d4601d42400d005424012703d1640d4080c1d01500900344504c011840c1c040800400072080c1c608444c510704010a0154109403c1c3e45d424090b80100308803049241d14035190340b00c001c460000c0e4803e12000005018001030340f54600070640e1400350700004118100352031130b1181c1e814207900802c216001500020741215012903200c540d84000c0050944135205c1d410003090007080728024105074100c11f2143c0500b2000d5490b070310100f0640f80146030104244d401485c1014180541c010722460358001e844400c80021034940c011900c3d1880c040031107168105620400c0e841c0e1105560b9106054440d50043c0144105102c1032980c092180a001801c0c031102c84c810100e0000607030343c00c400729445401c100f0051601e8010700c05900c2e210740d107840d82401e08106646100d030181d80e0003400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 358357131 1250 358355881 358355909
    0x14120304020d2406061101090b0a0e0a0611092701091a0406081005010e090607030b2e1e05090d110307080109061503080d0b1311071515 60
    0x400561a40f054803d01800a281c01c004416841c444040c141074068100041d0b81c043e07400c0391000050203800796050300001c03c0c2e9055221030004c040580028015401248a02d0348800001485403140401d103221540c40b00f07484070b00d403904111764500c6881c6080406060220b41401074002d0031669411501e031000000b44207070304040b01c40360320541c8002e000d900c43c2c500304000030100008201c0148145d41c030042001681e03213862015004200640782003c10b640070300002054540254410001c3c12002042c02c1c1111105007524001283d010381d80c9901d460003040c450000f1a08541c4c4007980c40e007074002071050030300c00c0703040100035010b411481072041d40144961000d0182d1132540c0f4614010280c2a1070007152144500c2d130190948800071102146041e4405400503e0700d00300d4001c5c0e03540f0410642c54001e03442c4812000d802da903265654004040041c1e00e01c017101c24400c80366001e180c1c001d00f46e200c0b1080c0c244854a122180350070044a410b1a009416003119215040151800860003402c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 358358381 1250 358357131 358357133
    0x1f02030a0809011805060901060b0a09031704050603040f0b0702010c020a0320011103160509010c0206030402130204081f02120430050309101109061c061214120304020d 74
    0x1000d0010800c030303011395902405022083c0400406c1e080c0c42000514002d001095a40d100d26101e441114103040009101140a10000d48a48808880340f0803809080d4106902c620011355070f584141c40884254030044c20103010484021a00c3e40c0c0003080340002c12440014100282d10350078244c00080800080784845406103001c944d070800e031034814000070002001c509452048a52094922942c0f650811b40b1030403140d840b0380e045a2304244180d58522000321325509104590708080d10032640100c00440480c1030700343e207101400050460000a002c1610b03080740e1a04078095036540c0255540c0104003004401e22483d0f4684e404c40c2c0d119144018060100180d8035081409007042c20110404540010034168844c002d50b0040311242d0035a400d100840c0d05d52802c945c000c0610414a01d0140280c07104c600c2c00c00041c01050781404441c1e1019100c801040707048403c00d8105140310b0003078403011020311000c0790071000304407440001841150f501000f40c1348540801400284a4018840440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 358359631 1250 358358381 358358383
    0x2010b1c060f115703040602030d0e01020c0f03191106060d030c0b010e0402010f020a0507090c0302040f080d170f0103060b0d021e090702010b06030604020f0f030a0b1f02030a0809 79
    0x5011030055001c5802c00c0343c07151020300c02000d502c2c0c0a40030001e800450402211408806c5408940880c0c00861601e4040341200d40a8042c1300c1c10004603550038418040e00804c14040c01403001080805555986200b80b400040c44904000b0b040800a010310250a8000006000c64004000b08c40c0c00e200c1e807a55150843d507001030504001d00d131302503460000800c08174402c7c0b0507000d6072003601e80e00350030a00360408aa0707071b01360900007810940c000c1d0010004419a54001c1c2850920b910300545801d8880e0f0800b001d0222550280c009a4090006010080c2d8001c1c40368140114625921046051400700c3c1040d0020600000d00035540c2e40c00307011880d03540c0b01c1080c2d0016902520507100c100d03141248940c00844c591881c3d0007000c980001500c02d0b44107225920303142da001440c16003181c5440c0244002500501d5603400040d0080000150305070b0700d8009036205842e51340340490101e48550504c8541c10000d000701010704100411140740c1d40c1c01006442102c02240341011299442455403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 358360881 1250 358359631 358359697
    0x403050c0d2a08010b1807080603030d02041403010509030f0a180f140315060a060c080c01052505130501080604090b0c220f0b070302010b1c060f11 65
    0x39201d426644404000400c6100a82c400c0780d0b10800208030040c1041c0601103500a8546201603041e106c40004101a00482e000c680140d8040d08603410712009005002c12603110340c000c03010040c1c03440400f054500d401d0150a038010807103400b80d800e0000641c0011802d01401d02c05205104110801060802c19440080c000303200148420a1403a52000081a04c00d045180a8001e0003404000c1c21405405030350a8004c1002824240d240f502d0080200c6882c5004481194404820000f00c0d4003250240202d9005400c1d29061031404801c1d40700407000303001e64500c00c0d02809824480481c900304040910b0040350b0007801d0040c3c460b950351340054000c143c0103a00a2085002c0801e002c08a054400a050000025151030030300184940107000070645034440c40c2d82d441000700d418840540d800001d014414424000422010341210016100d8118181950034003000349100109000303090094411400301c01004002e5046024403200c0c003441024689081c5242c2c0030700c4504140c20344445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 358362131 1250 358360881 358360913
    0x1f030207050a030309020310140c070623090601080f0601061101020d050a0f1d0a080714060403021516020a08160b151801061d01090302060d0c090b0403050c0d 70
    0x351220200c50f4600500200414070b004d078001d10034100c4c085000d400c54404c0914080d600900b440e019602c41c610418582e101c58421074609849801c1004007a0303004600080c03080c0c4c1240c88a4441c98010022440d040707050f48040c1499002411080510b480410400d06541c0c091410556000b1001c82d024060b100b000c00030450140750030100404481181c1c404800342000c1081402080d1144401002c440000030702c00c03281d40c000030212400600e030000109000751082a9000c0e800e0051038005080082c200e8081d030158205503120015280c003d0802a444007900324848030400b0b140b0802981d40509030300c024048400040c4d0b032194014025204000503070700807040c0383c8900c0c1c030040710401800814511801000300076608543d0f4904240064140c81c00e580da011114560710320001800c050340510581401402d21001c40941c0701d1400078070f05800c2d90140428000b96031480107004000790f5100c88003007803043c0802e20004070046001c072000783d8106ca02d000459202d0604190241c500320b2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 358363381 1250 358362131 358362133
    0x1306090c021203150d020a0e24010201060303090e06040b1203030712091a04080c07080703120504030b15040f02030c0a0810082104091b0e0105131215020a0c0606080703021f03020705 80
    0x800c09c403090014080c414094031a490b2008105400b180040e420b03a8480d01004010669101c424403581c030428131031580c4428010310119903013010b140400c3d5a0b0a081819202ca6080042001019a0400b0444048010071070080008034116201c202c520200d00c00040c100810b0300020030248400c55083d155484800400c2d81c038130f643d540d400f285c0da5906a20003210524088040100b00900a405513000c481d04820800215510308109440c202c81e401340b401d03802503859103201c01d10501c0348040e43c8101442e00005590f0814688081c0094400030560031070003920b00c0f804e0100e02404100c520780d80c510311045004030002841c1c40d0f00c0c03030300075504410200d503d061601c000c3c1500007203407840c5000290310303810400e61140d00111164429141d117880c0c0e1080c0d21004002800c0410444c07030096000d100b21030300c0c1d400d0404220080e170340002e1071a000551181084000c1c4491403080800030401d14000380a03c0b031840e40450028005008100819045000d900d00341314000e40440340d038158400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 358364631 1250 358363381 358363409
    0xa0b0f030d030603050f010603050309150c0d08010302010e10050f070809100c020109060f091a070506040c050307050406141002160602011406041a040b1306090c021203150d020a 78
    0x510010000c080f02e200681300303407040744c4c0380a00700f0f00103202c2d043c1501d0300003020b036203801003401c10b12500380300d4240469800b400800440b2243d503000d004045000e1902d80d10385549516600004045401c084081881140c01180929806400008070348090503056142603c40103d0700b055444c07030050020b4076070022030758101e603071103241d1280c0840c0c0900c1c400d07281c0c2800c840c5c40c0c01d021554400c0f80e0340d003000428110101844060400d1a03102c0c1c8880e14135843c10303e000c0c0c42c0d40c0d4160402c1d409482c11101c1c0c103002d0300e0a104034541881460302411003030310200b2407180780c41d22207602071450401d4640100e0010196002d010f1090004081c0e00540c0034454000b04d0b40c2d000003e00070b01025140010030168803003c9180c5280c03600403000001040c2d0881844c1d031031254200001801000c6010703174040139070700e4007218403080740c010b2000400c012400018030b802c11240103420070015545160781107500300208240c14010011407841200d0a03900942144070610116440c00c4040e040741261400d40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 358365881 1250 358364631 358364653
    0x100c050a0816051216021501120b040f1e020f01050c060c13080615010f0311030a050c040f0303110d02061e06010e121c021606030506030a0c0e071b02090a0b0f03 71
    0x1607034821030b40a80c16801c03103085000b054140f940040f02800f034440c1c03002034030827031101140102034111340190280414060040040e03891146880b14600d0381310426141811040541c0b402108024103000f0031b090141c41e01c400369404548480f4002d0420340c2d03422002c00c030801c09101500030f12000c2c1c10f20100312011801d224222000800c00c40040d5400901520001000c035846409080e0a900c00702c4005810358560a80ea40054080203045071000002400b0004074031703a8000a0784000c600030344440c0304030128000810300704040300c4503813000e5501c001e0911034113404441350004550181c2499036001c0e01c0d4000100ca0038100001d0090b44060400446d80c008e4501040120302407000d00003402269014020170303a1210480040d0311100740d038070343e0300300940c0b8000d0b088164410401000c0e580c0190560b51001301201268121aa0100c0300301e08128041e82c1180240c080c0c006201c99400724070503258009408190000c1040c5c010648236180078005403142c000010403240002c0c00d8890f05018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 358367131 1250 358365881 358365901
    0xa170421080c0307051f0207080306060c0114190608010b0a03021306030501051510020609061303021e030301060807092420010510060c0f1202070905010602100c050a08160512 77
    0x14000f544000501c2240701c02c1c1d46c040c00d108a80c0a29804017805056568003030802080e50422600d0803110754841d51b105503240c84003105540b00e824800819900c0f030080744101012540c03e0380001c56103030306d00b0100904940e01c0803d04c1c5e08890f41140c108400306104001c40c006024940d00082040d030038071003442441c22405d02c103040d0b41c1c2e90507100c90045408811089990348070940b4608590f40001c00490b040001800018040320700a00443e107402c50080c041c1c0d407140c4090381441800340c02c08030041c0141d5a1000d910340d006029407070242e80d801d003001c1d842110318101e412012442c1145c884808040d034001c0703084004a4849940201440f81104d20326400780004a4800400840c0c50341c02081c403c2c001c61030354800c5900014840705104007a0344a84003004c000c0b81c25401c1d44280c440009140c805401020b002e092540e000e002e00040c440d000c2410356090141e10010b00c0420f00c14822034903800144994028035a81d804001110786c1c82e0165000d01c981c240c05024010315500f00184e4800d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 358368381 1250 358367131 358367143
    0x4020a050f420702011d0a08030d0504050d02160e0711061003020102160e220f03020a0215040b34050102030f0a0b031504080d020304050a170421080c030705 69
    0x62003028941c0c2d402001c0462000c5845100703c020301183c4098000c0c0c0902c40042150940d490000e849600d00b0382c0c40b225818655000140c941b01c006482e10100420070074280302c9000300c903640d40000c110310044e84115600c07640f18ad0164041c003450a0002810700d5124580001224891000340d8515007014102c8080c00400303030000742d01502c1003024000d034018440b40003204940c00d14541c000c40b03484009031449100c040d031442e0b152803c51404c642c0301107030021852080340e5100c4d8005200516803807062002e00000d0f043c141d1000c4009010800148003101308030340c1d91340ea0440c1c000240d080220288075045404030032086242c00403051043c01c11005500550164200081c8070400c5c0d03465010700d00503103046005194154010032004640511140500b5070458441c40c40070f030404141940c07210032a0000c413001c1c0e40780e1b4407401010051206400030085102540300381c40340742030f052200c0310503190764004d480550068084241ea051001100a555883c0c4080040e20b03942c08060038003980e201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 358369631 1250 358368381 358368469
    0x1203190626070b030702030702010c0204090b2805010e061201150807031110050403080307091e2408070c050309031501050306010b090d03030207030516030207090b060304020a050f 79
    0x1104010b4089a00c5048900384d81c401c80f19580210b290440da5070044540c1012440d080343c0241e110900e05000401180d40c1d24452303038031040e00c02c0380c2c48042800041a4070103c0707401b003042c0d031418005004a110002030281d0081094680c40b00300f42502035103900510211010201c0c0300700101008c5103140020840b4030460b40a050807005c00202481004071040c02e009601020070300800007000022020009141e000c03005040a1180700d555802c01a40d08455441102480c007007980f090015130018822400030b58590003184038441c1043c0405481090040c0116003882030391a0318904208040044a014010240507a0780881c0c03603200e02d441c4a4028040d041c032030700440780040341e420400403e580d44040700030300307444860344191415802540105005c1d400c100c41040300400d141c8106a2400713400b0720980c02806c01603e0141020204c610302c4042c42d2150f0303010400d00000d0b03900e1440800548400b280c1e020094039249001030103c3d61031344014000e05040403035041010741c0c02c01c11310f07100d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 358370881 1250 358369631 358369633
    0x1110309030f031c050c2a1c0f171807090e010e070b07050601030818060c07030c0501030204180203070318030f0e010302040b0a1d03120304060605031203190626 71
    0x341c02c80d0340304141910011240d001004501b030012003101e08680e401d447c4594294001925810110307803111741009142c5c44418110500c821400380e41e640d100c0d4110390391100c90301d0076134150040740c0c800b40c06c0644060075a0000c000e4500b0030082e800001c0c0700e90070091107244000c010114006218502070700e25041d03828114003480d6400211116100c0881d100d5950210140103607030b007948e64184080d00300f17841d012511211510700c6125500c50b44000c00d4101c3d1400010020300e8914601801111010f030406810580140800c201880d40b45d55100c5205045c1c040241e00c2c5c0c1d1304c60404030300400e88000c9180c1460030344100842410f801850b10040d0841315501d01d220704403484015826840b4511410300080c00c200a40151240300317101281c40f204191906000f170701450b00004e03241030001c00700d00034418400801d000800403244180d400810081e0090201209455991015400010200c41070701e103400b81c0c103038640c40c002d9100d0b2000d807031415080116601142c1e424006c490000c441c040d0a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 358372131 1250 358370881 358370917
    0xc0f06030e1c0804030503130209010b030f060411090f0607060623010305040b01031b0314011a040b011715040203070c0308060a050a1511010c050702100305070e01110309030f03 78
    0x801a0802c07150300c2d5400c1d6111085240c81c1e0395412141d9900003044681343c00c0760503252000507550120700a00074901000c00685a051072414001898000f416441c400d41c5400600c0f01c5421003201907401d40340f42251203c196151001c00f09255102c1c0d000000d054500e40300c000b04400130761206030b049018503510802c8495608400540842d141a10050244c0154000400014070320450b41c0d1002d0418201410300142c0d40e035034941402c00d90402c2c900309a51640c01c1d0b924840402481e600d94800308950034084806030000103000c05143e0503500c3c1414240b9800180111480c0001503101403014000710f640b403034403000003403002100100480004502602042451030680036840079144002d04000c0e9591501c070303071140d0502d0048400070032700180c00c803000b026141c01e105640000025440740b5540e5501d030310400210880641e001c50a1518040a20410591041800b15403400a08041500c0340d072101c851441c42c000c6501e1380e41e2502c554111007411440201c081d003c407668030b01041ca0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 358373381 1250 358372131 358372153
    0x10e0706091d1620060702010c1704060b060c0307150c031b05031b0304060b030d11071a2809091413060e06070f12020903190c0f06030e 60
    0x900300030b4809454030320903502004a4003207030450b0089104030519082c40303400402c02540b0000502e0950408040079000b60003082201c540a004070090701807a86030070301d03140c0c11000d42e50622140203400503000075940d2001001c55190b481c00c640600da0040220782d212001441d000c007481815030000900f036814001442410ba00a006060780c407480441d41d5071b6446241441100c040d000100700d14010400d8001c0805201c840c50b000f5030195005407808280c1c1c5250006144c0f91660544001c020040c0442010b48103103008291441921300c544140103a11220881400303690052500c04c60140203000e10f04881642800b9480000b00c84035203a10240f0fa03941d468000c102d0350281c4881024030401d000041b00505558100d80707104d0700c2044001a10710301030300540e00d0040c00701c0f10003021548016158030420340000031101204035001041d13241400c03000201e074458151300546c0b007181c1c815090040c2000031810070070000e04a02c01301d02450741d907100001805011210540c51441c066404649 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 358374631 1250 358373381 358373399
    0x7080607090f06020c1e12030405040b0d0b070e03030d0e010b0405011a1804090506071211181003090605130309050a060801210609030e030c042714010e070609 70
    0x45800c21340180005130b103000d041c40090401203e9074030402c3c56050305105a9511800548103858000c0000c580340d9081105001c00c545d094440540f14003803140d0698002608114902c0c5c1c1710000f840c0800301c26215202081c9103000d14085542008e0624803020302e03190055025080d242012034040c0300690703079040c842d2606c0d00030314803004010500f005003079404007400006d510b0014011b0000a16005151030722402c104090703c03040d0009407d03603d10007083c2e54074001e10b0194250300c3d480b50714190f01c004801000054042e8100d01a003400002140d14602039800714014541088061040740b6102c8410741c0f01c00040075084000c506010400f06d00c50038890003a1003600d010380c803000301c2ca0742090120306003100c01c0c0140515403503480d0403842c002440c6028164140380319854400f440e481902c200743c1851251045240503519100710500c441150020000d00e140d07850104e00651402070070030b80c100744801d1790441000d42c00c024400d05228000074007041200d1b010b42e14403500c140c44804c00313 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 358375881 1250 358374631 358374659
    0x114040b18071a1603030504023a050109062c032a07090204060f08010506120a0b0d06060b0912030307020a060f060e0708090f0106030f0b1003050708060709 69
    0x1494640d010306010b002c1c10040407829400c2d61060f8407124248480d00f10f1484d00f4804a01040f800283ca07141484214140708514510602e60a8002410005030000e40e6020010304550880668040038441052100c04e5101042c06500076a040c040607801c11814510311100c0c06d00d1004102c8854601002c1d52000300a56005c42c043d40c03030f203641c0104180c10702c51141102c0d024041e198081e030b103800071700900c0505c0104010521916003140492500d40090103400c4140d0040f40125401c02008094000801d041a48072588040000d001d0341c05501041d030b03111222100800c1140b502034041410810040640315458084604981411014650640341d020a81d4510050b0388040f16404c00210315801c640c0b01054800800181c00da55588000300072601a00c1031400301c4c0d074407824025904420300c944079502505200030300c461451540d078441300c000c07682d00c0901f04c111898080780b200010160701400031a0840300300d50140c0c2d03c4100071511100182e4855002c11441000015011442140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 358377131 1250 358375881 358375921
    0x3040f03081e04330b04050c0711010c170d05090609010603020102061513020a0507140f03090402071a04051c021f0c030b061813020f09060d0605030114040b 69
    0xb88124988a03507460110444203d52a0301816154521a21003c60144c02002101c0900040842c0090140b01408101e03080501242080c60381003011202181a56a865112100a180c1a03d003603000303081c041c0740d07866100d001d02000400040e5000240c041500024000d241142c00d940d2503480e803140c00c6080700c8052100a003d40c03c000009401d450548944400c500005402c000b84440c005103c501203910006040011420101c1d0030380c10700036120142680b05988100500c111000d4045080e564002d4040c0300d84520b800041c00400c010300003e03804003617018198900010704040c40d000740c50ba0b10512200c2103515000041e451418030024066080c07510781484c00806150b007028050243c401058900280760311540280d000d9152580107090744001d142c00710b082848500100030504602c1c3c4c00e621403990050001004654031a0100d5071844801c603500c0c0d544410708220040600466845168103528002d140e0381c0c040402d003403043c40b40e8820048400d040c0c3d40c00350b140c0303070800c81582 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 358378381 1250 358377131 358377181
    0x5010f12082101090515010c031d04020912340b030403110a030f03060b04050616021203070809040605010206071d01170c040303031d0c0d080f03040f0308 68
    0x1038103801003401d0070010704049640b012400205104041d0b04110242d00380d100c410504d98a504110035002a40803410700102c0c00d1030040d6040d2001d4a0007402e135aa603501030840c503100c0c507035030302c000b40c7e650307812592041d801620340d02442601d100c4603030316820f1001390b1041e01e5801d28070364503142d6086062692003e90700c0c05001441d5081c841c1841a0f500020011018441d24060002c1804010459500c0d0603200e07a03200304601c940c0032801410b41d0b40d41d92000310364007400d0100384000d0350751070152074520421200000620059000003001c031006421f084040d800000b8803001070100307001c000d18016105450030320120740e40c0c02c0126a00c03a4104d45950014007d00540c01408600b440511510b0328145031299007003120703d07034400c0340801c00e891845484100082c10400c058060085425001c4e4108000c154001243e030103a886130003a40c45144240311025200341041401000da61b811311202c50140d45910309480c000c00b04401c26a400d50124040380e0004e4a4401620403d00000358002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 358379631 1250 358378381 358378409
    0xb0a06060c2a030b040609050c19030809030726070b0405031e0c060a030525080f091c0f0305010506041a0306031c0f080609060907080a060510030902030105010f 71
    0x1e00c56a0a006810310b07621840d001c20b22000001c591481c1c0018011400741c080000d1220580c60401d03e01641103810304d00030345004070f00a4a98040000c104116138000030810b54600059001908040c8107030400ca06183c5915000060705144010941c41003d014080326103194845c41c42c07100303501481c42090740c154462001c00c01c1104600c4898503010241e80c0455402850030000900c0640045c1880c4001a0341c82080201d8001391000d40c03801d104160141103181e106040e0000c111602c01001c503a10b041c0c2d0350000c2440c0080400102e106038540c103946c1442c0d11102100240b2160b01c0a182c0d00000781800008119031500c40106c1d401c480c00605a0006102a510705016030381008100c035a2502410310340c0540c1600703000800e0002100d03940c0e02c23104822041c801808141c0040c2c54140141720250402c401c3d0b85484440035080b81071400c207007940e56104400d110160045030462038100d0396021030800c46640641001c86402d208034024000e503038903032051f410203030000d12851424003508 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 358380881 1250 358379631 358379663
    0x9080d03060e0610030b04020a0f1206050303070f291e010e0112031403010f0e0708040809010318050d030c17060f01030203040f0c080709060b0a0f080903090d0b0a06060c 75
    0x8107800104d00f10190034081480e001110014080360000c00029010400703a9100740a00d680c0308101e041c1001200d0010041182441c0120b42d5034014460018240300392403182205100d40403046140101094242119281694071501001203050f11001189914110ac0444940010206506032000060300c04203507844c000010251171400b10068061148240004040e14107600056003e01520800381da282880c10036032604843c001800c0a04101380c11040c000090010703401c54040690034603001c110b484088025513039040e10b444005006103d01c50b200ea0095805402c07194441080e83c45030b18a001c814145c001284008850713091340001009809055903020380d01a6400c140074540c5201490038581d1285211007140e002481da69010382801c2040640314000d4030058020301521b1420004c2c1080085c0403d10a042140c007030005c02d50009643c248104156401c1070802000407035646d159050584500c24107803142c9184c42c0c00e180d00400d69074010710503441102d0340a80400c42907104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 358382131 1250 358380881 358380889
    0xf03080c0706050c0711010f0e010e0d080d0917070803010603020d02281b02150706060b070c03020307060e0603040b04060e03072906090f06030111180910050f060318070609080d03060e06 82
    0x510602941c806490233005011070b400a0181a010350140e200084140b00c5041140b0081504008811010740410800300010020b00c2274a04407501800e0240c1c0300c16200c142140a40036003000e8044201140a00011503070440b9443d212010140c0c031000702508501c801140344000721036001c0d410082c142d280081c900c2c4034400401c80503000b00d40000355544c49840030441a44600d0003500d80c3c0d01d0080f428815454144810801003d40303007480c040004a603030100f40207010040024040c0e8110000003014004217821569200541f607050329943d400d185402d840c118900b40300c0c0e511030720004150700305000703078120b0560154000400044045d82c03440b10040420030000d103c6a055500ca09040221400d1000a040500800c4a801402021b410140b1940410041c0a200c2d00320704204100400d0300c49200f405030391314080d503155070f8a507241c80403c0d0440c003100c14406c0c001d214144c400502d032940300b1250340c260307160310301942d0b94507104c40c008809440c0d050203a4010200130300040f40307030741c070f8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 358383381 1250 358382131 358382147
    0x31d0f031e04171c0f0c151b030207140601030827060f0c010c0921020301020f1201030c09110313020321130603090f03080c0706050c0711010f0e01 65
    0x81c160355110324241c0c032aa42c2a03c1c1000040810346240e21800307040d11062081e0080701c0e880100b174600060350f001406401000b5000c0500003621802c81030855803980840b41c2c00802103950001c060500d074a80b0711000030300a512a24040c1c0b0011842924200b44c241b0108802d41201d8001e100c25051114001c0e06010480c1208110403600d41100c50000c8103485040c050049000310714107668071001d1070541e003401c0d500c0e04d00800040000a480c1030200b059041c0101e002c21721074407808801754141d8404a40244140010141c4154010a24170a00c1601d18002c60603240702e44040c1003e0b035660000907050f82d180041001e0190001c1c0002218003040f401000e00c5207000500300c8443c02641c2180082e122508904000142400640400000c1920a140c80100201d1070304122448481c0c035603a10501c4040c400408104100000c20140c9403900c0c00e0301c1425820641c100100c1c140006520619800130500700d409580d010744024043d806550405101c9200d0744408804240020045541d04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 358384631 1250 358383381 358383427
    0x30c0302030906010b0318010501090506010e030105040308190e01020403050a0c06020a080d1802060d0f0c09060207140303041e032612040201021f0b03060c0f0d0c03060b0703031d0f03 81
    0x440380e00391f0307800c240a02e0b070080880c1440043c0d60300304800018120405052000d000c0e03170509080c44006544650342e1584544180a44c86540148280c844098060001509425030010070b021007400404142ca0f407075240300701c500350340003907036118240c0c0c542d100034038080c004401c05c1c4a0b91107080e0440d000b00400c0d2907801c0f0380325410809540020b9aa400034110103095541d15802d60030301690a2241c05645000d9050080d40540f400c00003d6031074103140141440f10310100081401c40e201003080d10083d0a25001482927504508480100070400c0e100907200404030a0480d402c0c00c08610401d18800c000c80c100c14582100800d0564440001410890441c41103c00d00540c2da980340100700c0240380500f90100340b0812050405203424009000ac8a04460811406a030b44071800304446103800d00141c08a00390301c3e42c076026001000c0d00d5001e0043c2d540300007140b400301541030303100b4808044020381d40d6907a020343c0b840e0503a07039118091030300c50725600030014001d43c0c83c40000c0c801494 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 358385881 1250 358384631 358384651
    0x2007080d0c030e09010b07060e0304150302180a08100614060d15030821180a02010807120903080a0c141608041e08100203070903080706140c0a030c0302030906010b03 73
    0x1c4142840404c0c0d11440981c0024003508011601c0000c000050080c040445045c10041d41031a08014503070300c4e403051030001c131000d040e400181c1281207240109043d200c03c50080c910100710303079500340c2e0548900c02d400310740ea00c03903103418000308800395440b00d0180301e80c0001d0121410701c07841e040100700409088604040986513080300100042040006260388560401c000038040803800e101c09020802810300d54101103203554000d0450710004030829000d0302464004d24980b0307a14000d84040035046030404605080051902c141a00100014011224101d04120041c901f02e421280c2c82010b12030400c4040d410000c43c2644081780589030f18240c00340c151507290558507840c4202c04030204141c0c5c0d0750032080b02c108018a0005002100a62404080551a42c60b0501004208044c1808014154000440c02d0b40c2031040982c48003002c060091041012800c10701280c0c090343d081207400e400064140b26081102c2c510a00039240514941002020241d08081080b803207501300074104018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 358387131 1250 358385881 358385897
    0x1b2701030209070201020d09051b010206010e0a05130f1109060d23010f0f0506010305100311060711041505030c1008060d03020a08030a020d050c0906270a062007080d0c03 75
    0x65500b232089071501031003900100201c03441d403400344014800c1ca81c10b05e810754000340c0040103a0803501c52038960021004000040e00c1e5200b480492a81c0c0c1506805003a90500e8201c00040140741c5081c55180d010880703001d8143d40c0c0302403c21420f249521001001e81c2404510007061311240b1011517141c48190001146043d44415984100d8004001010040351900d052220950b05846000c3c0c00901c9070600a035070600f0b5803104a40e207100713503c3c03441c01150300040180500c014400d1400866000500600441d051030701281340b02c01260188511a016081e10864540741c0740a081e500c100003034481018136520b01341040302544144406031305501031070040c8000104030200461088418400040c0c030303525118204070440702e00502d82031044c2c0c3e00300300408045e900c1d0400c3d078501190150240c043c1e1041e005040844204048650350020401000440d1031a00900c0c41c002692054014010786940010b107d960f64031244148909a0003c600b0000018407401c00c114140e80203041c0840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 358388381 1250 358387131 358387147
    0x170c190e15070b16030b0a0b03060d08070f06060b09010e21060414010e0a020f0405040c1701020901030b030613030f0309051c0e010309020f01031d1b270103020907020102 75
    0x710ba44040821102451440300304082c1080c0c5281035030b0303101c0349807408100d030b42c5941d80850b060071902e0040000d2510080700141080d0f440d0394284600039800900c054450b0806d00e440c2c0a0307215030340b0046420500780040030400398288404d4411413407050707448241c402007a41c1400841d40b102451a03402070091009480032031020845540101d1107481007440b06da683e11445821100d15098021840e00210008805030751001d6072041c01d00710884000410340c4680ca0300203801b500e0f07503201460901d05600b40300600c0ca010360180801c09001c0c2c80c00d02c4030700079500402d526000c2c00c955032401404819042e42c0030910a000300c0a4854403801c0c0002e03010a5134072650301e8508001c091120075016000c01c1c800700c40d84103218009081003802d0038420010250f002a039443c8007040c403c1c0c1090341d28014800080305d944820034403a9000e03130580d0316a5504000151003910b40013103003030140707440d0103152610500e14040c16000f41402c8414049030303401c65003006278005020709880215034081c00344103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 358389631 1250 358388381 358388419
    0xf0f1503120f090118060504090c020a02040f1a010e0307060302211003030927050a0f020c01020a0e1807050a091d0405060c0a12020a1e170c190e 64
    0x1281a24280c0c1906489014070000100540c0180f4004d115051095104201b901e401c1825103040d9000407501207400c507244017040b403805100e020060b5000d0700345842c0000c1c0b0398080c1e01c40c80b001842d11000c001f402030740b0340054a5070413014403a540c0542c080007042001758400d50180c86840c500c058100c0700030001000c0c221525000781c0d440541d120128004108054010701c90314002e258200154280c0100c0300041d00001c1c0c00c00314150040c90325013000036030948240c1d0065030010721410f821511391501d00e0206d070003904484200b00c017054101041841c140707044017071f000010140c2407a40710385031b0b502902240c05402c0002d8010078000e84000c0882c400c01c1c0f42074545101c0da20046459114501424014580300011b0035400e03802004204444449034403c007410401c42c2e506001503078031880684111080c41071010b9500a14000340c2d480024240e002a0152261442c186200e240e502c400c05002d00904ca070407556143d0300100c01c1c00f03100040c0030b112401041e5000500c6220b0521940440c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 358390881 1250 358389631 358389637
    0x80304030203151e0c09131a0d030e031b040b010905031207020f1e13021806070c0e07050304060624030e2b03140106021e100207080a02060f0f150312 66
    0x1134448001c000c00c1e01031060410000c420030500071f100c41485680345a4440611460501c00f002c2e0282202c60899004c4c180a083c54038242c09010b001c6411100c002d40d025401c015041408a1096082984c615415807151007204141e460060161010088014181030154003501040340c01c10100b13050503183d0360342c607080c0300c105169100c4a882490b0315001040810b101240741c0d000d0151046c000c60348101d500154440400d0001d6589a03500e00c46d9090808030314026a0001c038070000a4010840865409400f441c020752059100740300003501d542c00d5003510403510183c441001201d402c07039508248a50408c4201d2a1203c043d41d010554414003030541801b0101c0809914840340264101c1d2a418441c1c0e00b44640070088603481541480402034440220364024603d080c010480020b51501c00e0000c415138107640c03402190b0341c00c914507241c81f8980041590304003500032400000c07414084506120300c6800d4184035030301d1940d43c260810f035811036044240c981522802d4401c0e10242401001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 358392131 1250 358390881 358390891
    0x91e01061b020a17160b0313050a02120a05060c0c1005181002091504050a06110304150807140306010e0103020f0f180a080d080601030b010c0210080709080304030203151e 75
    0x304c1c400d100c20491461402c00c02d5041d10340301c120740000c2041180031081c2900e4000131031185045c04081181892860310b110342e030001e541f00084030b18442001600050303035605540700b0f0080e0381d00d613520310031615601d00804500a05680010003030011901c040c0d0b01c42580900c00180140000103882c0c051454880b240a90400e03003a80050983e101c2d01d00219000c0e01028001d80c206d182900f80030205003a03500c18414041409221030541c48822000c0c0b0581d03000e0008a1841ea80003800c042008244990030303200203000c1040c034503a6019a9003c902201d1103101c0c10385030040306140001c01100254050031098035401d00c20700c0340304030040045008141410a624402d00142958000c210356090964440d800303a500403000720714082e0708914520382c41f040909000400d12a800010385142000290080d0304c03002820145d071049804c40700c420300540591340e8080080b6142d0050380e42d284101c0c00080e5050348084181c2c8044801056580d610000e41d0190001000a5800744e6906d042c003551 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 358393381 1250 358392131 358392149
    0x6030f010530060f0c0403080f0915070b010519030f0f0201051e0306190819050a060603080c0d020c0102030d050907080303040f140601030c170705090a0605091e01061b020a 76
    0x50010901c0b4241219420a50305440d0620f400e1559488e85610711982034150210307a00418504c0007691000c11003801e65880340221f603910051450030f100c140c3d00900030244500e14400041c07820040c0494050141c95114003482008140b5403100210a54114400c0341086000c02405c3c1c2110510080454490600404140c6038108134003044190b6120f20355690711008011420404c01c240000c000042c1351254800c1070749150796040041c1801c1a030760000d40074a0500300c00008120080006021403004101036030f60262048a04a8881d0980d00c20f013070043e4018030440030528625071045400941c24401c48255a6482d0281c0303055410440c1d0030f80b078040a8030107103014000425807803e45411024003030041981541d8904842146d1805036034518414024585804641081103401800c030040c1461514505044014050300c014001c0e07030700031140040860740000c41d6a0380c00410702c0300d04140f001144e007406012a2400703440624400402c0101d070440d40581c0390742e038021001e446400c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 358394631 1250 358393381 358393393
    0x11041506110f0a030e0d1a0408040e10030803071407020907091a1c0209010309051e010b1c02040b150301030318121a09010f140103030e06030f010530 66
    0x200c281016181e10b01094990084605000040d03071045880c3d02032942110648500e43d0b09003130903107040807140307030350a2040c1088080c0300601c0056009001220080700d410303c1c0a83e1030a0700b18441400602c8002c1c040d81051000c40d00b600d002c0c1c01c6007600c0303a4015042d2400c241641d000600139000983d03c00c4042804104240301d60803c891019001d04a0701c5c011070b140c04903480140303001006001600c144542d0220307924010b0780c82a0402d100c0c0c3e1b038101c42262052403051200003034007501c0e00740b40000e0790300c0e0071010740ca641001c060b0b039040c81544100517020760000b40c0078170000d00690320340140c0c0800828040742000701c03400080c501960107075035406610941c3c030041114014864100c07803d4008258410380009200856407425607150400c1da40e47c50315a841c10501404004915500d6241805180000316a0305004035040b80c1c003030398442110385020750030710419200030345034807802511150040c042428288410f40280c0c0311a00c80b94043c03546e034600041000c5481c002c442d0103070061 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 358395881 1250 358394631 358394657
    0x120908371709040917220e0c0310090e010e0f071413110408010b03060709031e0809060406030f0b040209093111090108060c1209031b030d0f0b06030411041506 70
    0x95207050b044184038036100c06e154140a510807000c08010502c0c0c1080500000003484000400f030180020840790300284090032036080800d004c4c009594003440f1a01c98034038407544070900003485c00215890340e100d0208210700710b414020210f40c202e620510640c1c9aa0035804a07841010040004000030400042c010603c1c4003010f00b8114003810410401524038401e00200c0c0c840041d4448404906020900c1170306030b031a000342d05000e40c00c10140d0265001c00c001070101c1e05030b040003803d04020300c4200040340101041000720300461f54020b80002421000915810110404c12140300683c80e100f40388107110341900c5109003a01900f1950600001ca01220f10f007002004940034010007005000107103801d804141050080c410080143e6948402003222000180304440d82d84455074007004040c800113501543da40d12541c50940254508000801009100e108a0310103000c005d102502e1a10765460314130100411202865005e90780d2801d903030310401c0a16400c0300a0002c1e0311307074521581782 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 358397131 1250 358395881 358395907
    0x312090607090509010501171f0b2115010c0305040f140f01030e030322020a0312140906040308091c121b0b04120908371709040917 58
    0x1055103c0c6009004c000014069070b80c0111103488612050041c0c0140f690300c0c490541351415641e241a480500072040c08508400420001c02a054200d0b040e8100742d40d844609043c02c120494110310038401c41c00c020080340d88030f0444100d605000e0701d0144e05040d00c5154401d0b44640552006040b0b00040341402003034201020482c011040c2401c0412400c100251030b0b0742c4034071000340b80c01e4220a43e2420880219008030030008140d40140854080c40e840340b84c9049a0208811500003040800e01d260030106841f0013180c02d400400781480c1e06041c03455807a041c0f41e030441c0341400d50103000c0404080c10700385400c85035416030f80034507442c0b00481c1e200c0c0000340110108800502d50200c0741c07240140401d050308125904594055000ca0080c0130f08103044803282c000790001051030213801c03194111100e1940303031f11150402e254008040290300c950004842458903000a0803000d06a0f4102c012000590181c8aa03440140000c50074140300d60341d82400084801d621550600081888070301c40d21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 358398381 1250 358397131 358397147
    0xc030717180108040b041e06060b250f030815040906060e060f090f07030b1c0b0f1905060102070f08061e100909150f1b0302030c0f07050312090607 65
    0x10081c00c1082e51404c2c1901c401c0494500104060843e103460340ba81c20030004048018030049410481c20403540380c0b58092241c040d400303035600c101d0381001c0b903044c40c1040706800c50300e50103240d2010440c0704840440e5400d40e004c52000b41490f002800b0074201c07100301e1700ca0340181460188a80300002d030a5003041c50a0725032134405480c90340100c1c280c1c22040c843e6181c0b84111a00718200d65229a115595010120080c24036202c150b60864040c81100e00d22647c96080150f40c1d5201d5640010700c0c3c0d8459840d5400e29904035141c0c11070340c10800b00003108062a51000390000d1061050b56200c41d11040e5000100b90305610041250f480101002843e00c41d103003010303a261058426440d8281003c001e2341043c201c80703002c0c006010703035a1080309082000b0075208440f070101a80062288460380118480104450b0010102400c10f015003810014031030300c2100d01c01c0071104089401c00700c00750092041d0f50060102240c00d032104020048455001c201d410344120101001460b4520741003200070704444d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 358399631 1250 358398381 358398427
    0x1208070216050a0b0c010902030a081e030402060f0c01060509010f09050916050108090a0c030f03030b01030c1215050306010b130b0c0309090a1407080115021507050c030717 76
    0x2420701401441181e441c1c105400c00c95a1304043e15844076100404203004240c4408000e44c5803040255050400c03e41d80301510b03009034030314032034694240b1050b04041a84000c071002076108804020106100140c507026060070100c81000041c400d44a5001c584220402e82000d2140b49640d00c00300a00507141c05507a6004925001408a101c0801400c5820003a6801824188090003000410b040c00c01c00c2302814064000c1990024180d4071704050140e40d40601d4140c001909140302c440495000e0700666104103404d81c4da0188118481b44c140c401081c400400b0094a0600000041c40360707400c100045c042d2280e074a034560b4a080030f910040e0100c21b542d200c00c01403030301440b428248484c04010b80c1c5544000356084101c070b50b103400d1988014140c211068500c0d089070f0080c400110b0b0302c154040d06a65081261680851103020282d0360380403140e0075101c40020540025619a102e0030141280d120500d04480c02c20280c2d03070314140d1444251900c00390003500421030400c02420400103520700e07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 358400881 1250 358399631 358399663
    0xb03120903012403032607050a08060d02210a020409080901030605101e0509040e0703031b05060a02160b042603073002040815091515030a12080702 65
    0x101040410319a03c0301c0344800780620070210920310381001c1e541304148030344d11038034402042c92501d604040c1c2250404544800050110400600d07039080c8064184202034004000256071113244038071070034015002c40220b48601801509c400140c8550107828407051148250302d0700c0340d400704001801c40724198080c030720500d060f010840f0b03903e0308416140d600e1445c80100384042d00304014280d82da48200d140860f0400d160164220080d079020642c0c0d01a64032035030b20101e81c41e0340d130a04095003010f032000140550b0440e00100700c2c8288550300070321640c0d00c8021914923255654a80c80c011407400c50f420f451030000d580c030b41040500040c028501d607004200c0c01505500380000d0041000c5c1040c88405501090200710300000e07401d002e000c04101400407000e543e10ba8440b80e002e61284a140758054490655001150001c8404109000c0282c1503c0000b10b0541c2c0d5000082800c03e1606d81c2590180920345500001c20607c03602c084c0301c0043c54840d40c0050400c0d2030001d180c04a107050051803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 358402131 1250 358400881 358400921
    0x424111b03010b010219110d08040e0a0b060a020c010c05070504051e091b01111002031009270b04030908060a0606081e070528020f0f0c0112020d0b0312090301 70
    0x50310054926800400d5082a4547e44c181503c00104051601804001d80190b0010800007202c4000d1a81c0314860080010288907082c1c064061041c00c0c05541112000358100e1031000b507880d403050707425140c454012000c81e485280d0703550118046807026202e890090070711b0701c502603034640c01c420360704d420003000001402d60085d11540e0301424500790300803e04008101a071055055410058400c808802000455490800200745c0c15a000c00f03108a0303204508040000c411203d034141005002074110000c4420115a5911003d8000c8002c00132403c0c49031004000c5005282042582d202c0c01d050140002d407d414040003801c0c8001c01418104c02c9111405240461051602035a0300402e480c10701d0354886404500c080c0e41078112000c4030000c0c0008456242e11a540041c44140200580e8241c03014082ea40c50859103800b810b03070303c450200b450408900500c60a40c2d00034817403010070712000200303540d10b030000038284031220141780c840d1368000c903090540b40307420320443c56124200800d00c0f403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 358403381 1250 358402131 358402153
    0x60305070b07030507020411220503071d18120a0305061305060a030b13080325170c030613141f030b060d06021b030c0d050424111b03010b0102 63
    0x1199101d05c0c80002d01840c1c90320700c5031030025096020f13070300c01c0030600f100c0e40d80f0746440350040302da4580207101c4c55200340f0540500044c8261081002c2c145040d941c0082402c3d55114620001a001d43d100580018031441d000100108002e4016129818440d6030104050400c081006000740c0d84000d050101481c11061180c2503030b50f4002c0d241120307488407403c0c00d2652034008003056968250780c003030040ca2001040010b1000034642003090b691074801c0c160045c00b9803590895415210707400c5920610308820208244e89560070103140d001c01c0080c081c0c002d5507100007618040d105a0710b4401d450a0010085c00564074001d643e00080082c09131000d52881d1031501d80c40c1d90102d0141206004942d00c044032006d00203540c044508281240f022485140c610440e0507950b0b522613600c40e1064040c0191002c0214460021201201c501e00940541031001401e150f801041c0c1c03200c4407040c0f0507100b5980350780f01e00070301c02e0b1503509200010030f0754001e0b410320030306003034411202ca40390454110602e024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 358404631 1250 358403381 358403387
    0x609060c0f020a060507020c150301050418020d0609170c0c030615030c010305130b0702060a050a02030402010c030e010c0c0b04050a0b0f0f131a03160c0309090e15070201060305070b0703 82
    0x4036070341080c030200320b580f06c3e480c083c2e003462103038501e09401643c584c5d41c086140d45d01500860407280d050368100300190000204441400700d9100c0250b020008120500100312250040420781c0e004030a42c0081c9107003211b1a0120b5400082a8542604000c1108403140360500c0b80a41c01441854015441c0010b0400283c840069426081c1810b0743c410100b146403200508666a03143e2000d0343c4005402d0940000c3d550782c000700c444031500c2d810003000070001085c40c020b8078000c036410303141c4a460b5155540c0503280d2003603058a00b810040c16034205400b01d02d651040320024100c514500d903036103007084c0900182c41c5c2650406c400c0d070181007004112080308101290911002c1084094030f441e0a203c040150001d00d80c0801c00750300e10b10a414500000c43da00560141248801002400e01080400d40b4a030203e8800a0301007842c070541000302212541203994040140c0d0261412070080002200c1c1099041e00c0c070130010f0b91b40e0340d810300401c0000c1021902402c403105402e030401c0b80d10364000b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 358405881 1250 358404631 358404643
    0x240506030106030f0b1804050607090b0702010e040b131d030c0c010f02100f0507031a130b061b0601080105090f030d090c03020325170a0f020f0d0609060c0f02 70
    0x202d4101691216444900c1107641c0c0012001e12008100c4420501442d4000c41e00450a54043c0e80c1805a0360101e00710394050807a001c100d035003045101c2d0030304000d0f400544500c0781c000e03101a0080e40b101c1c64501035aa0f1003c05058815006a0020f5052080c0780f030005209000507042081c0d07403040020840e20000052800360700036003464048070003c0b020404a007003001c50b0641c016224106200308429480540002c6d201d82ea603503400b0810101e4034691461820544040d560300300d0003881214030500250703000184c11250141506192680340031031041c003002c0890441d95260440c400510079a9000c0c001c55400040c400010051000516000d589901c502840b44002e1543d5604030800c00440c00704100c01035400070251800c0350045042a807118514440b4484c14194035600452100c1e4401c45180740c9684035001011021150b5039100301c1070841000590b0f010300030741c81c1d0112944c2d66003c2485064442c007070100d002c00d118503082099440107000d0409004e1621541c14040b6800200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 358407131 1250 358405881 358405889
    0x609021c0c090536030702060f0a030b0612161115040209072a0218010e04022407060908040e0405100510060804080a18060c110603070c02150405060a032405060301 72
    0x7250038a519456413140b03940304000c0c0094001a0100d800d0b0407580b0190054011105c05031414000491000104104d81c03003440d5214481c803d0041c0442c003d00031039000d42c90342400c942084401c0d0440e010036241340070240c40e840030130701c03100d40d003040114102806404d401010318245801c3c0c58460203048102e4504003200f0703040d40d4803814240310542d030f500301c034402c0c0b01c590f0304140c008556140e1000022098007200c0590140449008100286032000c1c00d0b1800c00a4030642c40d424190541e4032540648103415040e142000c01f4003010072105a041c06440c0103074070400007042d103c007100d4408403d8800c0203215500c1c10408010421150383c002d41c0280d4890303404604540d517800020b20030b9480f0700d0400416540c04500000104d2101d405c44039004541b80544407081404401804008003071004075403440006020080070001410048074041d01e03c85002800ca0800d03442d140030030120b800c103412110009480340081205002d4040310344d0f407031600080142a500f8203000c046401d512040c42 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 358408381 1250 358407131 358407211
    0xc0703080708091c020117070905060d090602041d0a05070207060305091510050411190c1419140109110603100b04081c0504120609021c0c0905 63
    0x1403101c00b04a0282d08466100c0e0004000c521544030061103281d0503401040200c1c0840d102c00300e021400d065040f00980304078010340c1c03602d901720304003024808950085950300100030380310001c000c0010030b1343c00a03102a00070802ca035070748400d00032110b04001d90060301601030249000c040c400b100d03502045000641d45142800316240e00d030602c07554907211443c0340f641c480b41c205005102e040640f00300824110b072000c8605001030740d2426802c0c1214070800c50542c03007a1406500c03c082660040c00c01c1e040980c02441c10103251040e2152280c03d02003080c40a00c1c103083c600c4a52390820070304008590789000400001c0007442c0c000d41d10340c011480c44103103080c1320304000300c00200c413221060991000350001401d611b880d2503640b030609699442445035481c44201000b80351031400c0c410815141200c654414403001c00000f03443d088020400420182c0c0c03c56903d082e030300d0310505102c01c8011454400d049505100d45400d0440c0b0071108040c11000c01036520302c0c94281c9007144501c8440342c501c8018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 358409631 1250 358408381 358408387
    0x6240908070306020310030609030305040201120606090e2e05010f0302030f042a080a0210080f01031502040510050a17060d11030f1903090807030804140a0b0f07030909020c070308 79
    0x224011041c0c0025440184602e0901c00340d270007010f515800250007a4401c1e200c84444104203c10002590002d00841d400100c1d80034003000194041103049412022403110745800c4101090b070b42400f2504000448035036a0b0b1076100700003650b84010711000050051808500f035007405d501c407642030741c00030348054501c8230600789450040c4402801120b854840340800261255035068040d00c0d140503200c16803041d14030182142e40c190180f89424072444010480744041d03803c43c0e540e5024a409440b100a80c1c0707600340004a80b03600d800340006101003107901c400c0d0721007494030401000342402d00702d0018000100d0050280d42d403103000e100e05005600400302c801032129800401c1c94160655800501c81c4142a42d407825151161800b0a401c0d029540d1000d01d03684618101d0395030b85035480b0041001100700400c01491072030144e15120020010008031005980780004010742d046001e40d800309001c0080c1d90810540c12841a000a051400003903080050414890341c03107460920000e000340c9800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 358410881 1250 358409631 358409641
    0xb070807020c0a090902040f0e0d050f0405040c0504032003060a020a021903090806010603060b0304030806030c0909030310091109010807050409020408010605180f18070801062409080703060203 85
    0xd222000400e00042c059900480c0d131804076502801501d241a40200c0c80d018400204c255a8000d84420340c40701401090900240c4138103c4a69100f10200307802090203000201d41a55640194410b0641d80d680e0b1644481c150b0a10101c003c03120000d44410740d6040d042c3c825551004280c0980c000c00680c2c0061720351100a4007039080404074403c0455022907080c04008144d00701c00301a05461100303003201e41c66a2180c4050b811140b0324062000d10700c4080c8000b0740080d108604080d8440d0014041d00c2d0003400c0c0c18041140f0358801d0b50020000d81011007040183c010131b80007070300104103d1509012820042072107008034880c205c211030401502100250940d40101c0c125001056a0340085644030381d140560750080a10b4011644642e0b0111081240e031001c510300c07140200124003c00d4a19141c0c0d540740c0c00c0d0342e580c60741c41000f980038040b000134400b0800e2041c2c00c010700140d100f0b0008407051800030a160220074500c082403290349402409420000940c240130b50341d00440050360f035250303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 358412131 1250 358410881 358410883
    0x402150708040b040602241b09030303041109090d090b07060b09040f06060f0605091012020d020415090806190207020a1418011203080a1b0801030b0c03040b07080702 73
    0x103480c030060040040064005031504410000b0400c480082d03007941c45142c503207a01602904081494080b5401c500808030b2460340b007000051034a18903c01d52a4504000840420300b107401c101c80076108090984601380490511500080e80850a040500a042d0089070080c20300626401504145400410b10404100c066400500000001407041d8543e28142c030f4016011099543c04a4005090010000340060f424683c001507990320780b039142c20142000c0501440b02c1d80d442c4004100080c0309081c1d210006076100512080d03075005005a039941c00c2280019240d00b0381d596450410030915000c02140c032012070311a410070460b2201d02400850701013000060301401101941c4210407403000a003214282100d00d44c3e028064440c8100e0f00074000749520314610900c601000400406036440009224214052740b14808000000d112118612019284a086d00c2e40c840031581180c0140b060089100c01140c0c40290548a14036600c1c10ba039640c01041c2028081206220200001c6804d52780 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 358413381 1250 358412131 358412137
    0x14011d060a08010504080c12120109091a15040b0d02013c0906020d08010302130c03090c1d1302010203070609141006090b04020435010f270209040215 66
    0x705060090125043c281000c40481e40110041001407042d1a100414694030f0015101d0209c14089421103076840c18075000701401e24010201e031605450300300100c3c001d00c4000d070503000301d60982103c1d03040d80d5010700340011108d0340380401c0e01c513130003292016005070381c85109691440c0c1c06c410449000b14400410314000c0f00c03841d840000281d41a803180602c2540420701e001198919801c84001742c8503072005031060b4000303001c042d400a40070b104400e0f6084881c2c03c03581d02003840741303000145a0381e20744070066588202d400c10480c100c2e01102d01c00790610903840c2c8e140c001500b5403426101000d0ed50010b503072481001c40c020b1103e604e5500721014080c04c05181011000c001d4150784c20038030107003148001400c181c0610041246899404102c5060130320a5505841400c503240101d2821070005114018000e030340b4400703442c1c0860429611643c2805405030340708004402140091814864101070328030700818165402c50f84c0d01203405696400c40854205806403401c2c0280a142442210188 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 358414631 1250 358413381 358413389
    0xc070801020409231302100e040504060212070516020d170a0305101715060a15021b01031a0d02010201020f0a0903121404090507051201090f14011d060a 67
    0x151011500050300c02d00c68000205050b2580d604e01c00304143d61602e40c003080d43c240d54401c03414890900c2c5800504100008407020442070401c4040780c04043c0c00201a170703030100c0e81158007135004200d0700009040164800d41100040c10283c1c10809040c03207030040b0940000002c0d00c45c0707100101c2c07403090010340e6039000c01ca40b20310440103a4a84800e0006405400180c902950041c00c8140005012400700b030424682c00178400070303041c0080c0246030310001c204041d10540c1d018000407070006654a0002d46180b00e035115402030140c203994002190308900079005194181800c26941d90112000c10300c6502c600c900c02c42d80304194886031300040780240101d42c000c00c154000042c86041c0542c01418010480348110b240e0ba80c10f02c0899012941d03000600980e0171029814007007480f014010750400c66000800e450040e080c00711a240d8003480c84800c1e0710691800340d5560308841d400c441401031404050b5007110360301c03a65250810061a0400d11030001909100302d00220790301d03545103d0309800134 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 358415881 1250 358414631 358414633
    0x3090c03080f0310080102040506120603010b032508010203160507030903020910081b010206040b0405030906030103060c032a031a0402040305032101060c08070302030705100b01021902060f0c0708 86
    0x1d00002c0780b150225441903c1d5550600b403008800034440c0814000c40b03003030324400307088141011828480c042c0c84034009000f440d455525600034900300d8408020110302c2e80d9504034464000c07000c02c01058214101904a0440c2c0d9004204000042071103024400c80f46150b40b900301d80d80c04140c201200c44a00f82d0b00020750004049041c8284a150399500b03405941103c42600c0c80c420464840c4104061000041070268000a002402203141e41d8651644140594240d901d08034010002445641c03007600101d400c0c40d0340e00084680250f0602c2256034001418007541510700758611022400b040120030b035810540c907800034100680021410661114010300f00759159900c80c41c102c0d40704e130400c0c0491081c24034000c192560304c0124441c1da60480340d1640f1110040c2886454811040d40400d006078103500c0304014810004004003e804c40100b004000000d0f02034485000900340a41c0301e50349440c25100c00704480247e511441207a40c088800030b01c481e951411101e01038100101c941c440c40031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 358417131 1250 358415881 358415887
    0x12021215010602030c0111070f1b0801090516050108040b16050409060b070203190c29070f29160306050d050303010603050604020a0206040f020a0503011d070b090303070303090c0308 80
    0x112600000a0400d14600600031f0007108076102e17082c6014002c456025103003081c40c81a09010070902c0c543d003c1050a0b0302c1d487d8401c107030ac6e0921182520305210007100c0d29440b41260040c81440719540c40090402440c182c10f039400e1035224880700c0315016000c0414003891400407c200e5014900321002000500420b121841d922003000803540c11180d8168081d006000940342d60410458440618552084441030f0302424040e0400100c1c000030018450307801c0740409000d0752a0244040c2035110721881c1803602d8030b045132030006003e03c07940c0d12069125071000a00c0d401d003001c15810981c001c406504101101e043c8000032005002c0a038892034101c807034080d2000a104000c07000b1410380d06103403030a00c003980b01c00c4180300480c4600c81d2910010f0300704c003000c0f80018000a40e01c0300b21500040406130b031103843e0f00029084481e0100c0c0611101e03202d480611004605210030341c0181010076810f03041c100700781c01103a12803144400040030141e0328110030040200a10050380910307041a84151 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 358418381 1250 358417131 358417139
    0xb01180b040e0604180f030e12060901060501050a0225090e0f0c0307050f01030207150f0609050903040302010c0305030a0e060a0618060b0f07020a03080c0a0209101202121501 77
    0x200c660041c09400402c92220000503100d0416014080040c081d00c0c042d00b4454025441c0d0f07451081c3d4400046040181080000c0751658920881c1e07064800150098a60b0303043c80070101e42142c3c131942c40a41407050078040383d500c298010071070b00d2004210300052000e4001022010000c02850341103049140d140c4800750701703500b00010322040c1d040ea6001c100c41144051100305592180305100300c03980b0104900207403507194402d4014200c0d841c807076125600c61400c004150b0003510455004204a42c0c0e40f04030401c00110030b030140b1500524044e01441c641030558000034411a02d109016040c000d00202107001c3c03810f150300c41101d021220065841078144503034004040c02c03242c407403d40c44000c248022041050f05100d500d0482d1982e00d103c501e0b0131501c0003901c0281d04406400c0e81d21824010380003003c119580010300704403000c00c021304100e1810303104000500502070440c48a40c081c000c0306228408810701071540ca6601162440311418007440f540e440c0485201004c2c0181d600040001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 358419631 1250 358418381 358418399
    0x3061c0506130308070206010b03180f011a031203060a09023105090c1306030b040b030a06061703030403170a020405031531020f0f06030c13060c030c060b0118 70
    0x200459103c1d9882e01e0b096101c0d000d080703980d29400e025007019240100003003007603008008540940003681c41c0a840300aa50010751030308540014200041c041801d8000451a01d000d1008450035001c1810003410b60910001281c0c00154500440c80d16560000703880c04440c00010b10000060301181440c0e005151405032a04008014840c0d1400754030800042041c48141000740d50401c2d00d80111240510f1502400300c0140840d89407094010380d0b2040051181c0c1c03000e0000328901c50048034041b07641c0f482c2141c21903000181d05202c0c0e005800c00c0c828400000c2e4084071060483c449464901c12989074071110b00001d100e40d612503949032040310081040203200b460b406200700340e46581d030517130869071440700d6903c910302c148460981540964440018541400010020b05014024402d0150f00c50045481e81d8030a6682011143c4003043c450700000c003a0749103102420852034061060505503074040c2034114440c00c0141312a40b101c8120300135074411240403141b1268a00104142517a5031244 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 358420881 1250 358419631 358419661
    0x7050d1a060d02100c0201140f0903060a02070302071215020301121109010f12150e10060602030a0f1d04180b1b070212010605090114120a020603061c0506 68
    0x1a11591504002822514056001290b03a50f00039004441c20303840d981c000c07902d080c8281e400b24144019444503252110420021b070400081076980030342c0e03070504402014a0054001c0c00310780307400c2c0104420300001c0d9000c90382c141101d0f100e110302c40c90702d03421340741007540300100100608113244080000101c140140f1001c02102c3d000c3d6003501c80010500c0140703c028802401200c000d06003501040121041504801c1d030303e1405180545d03942d00b800329207881919903000103905142c0c0194085030b14502180304000060141d400214903010328135101600040301d03240c880d82444800a20200c01104c0441580c3e40c0c03901c000c000700105084084807100c0480c03203410a5440300d005200240c4218090500700ca03568a0005846042c1802c903402c000444146046003001c654070380c800056140c9446101c140a483e4500340c499282c030001307040c41091581115590140c6d4007900580003d0f071104030450f40c01c04429a030039869603481d5400740f9030300341820000810741c0c8540d10400040308040080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 358422131 1250 358420881 358420913
    0x2031203011508100b12010e34030e010f05010512012a120905060a0b06071a0606120f041505072a080f03010905010611151e07020a0b01080d12050907050d 68
    0x51541c00d84550700d15003201074240b440ca80012071400d100c0301458209c0c1d195080001d51300d140118109000034406400d40c0d6044000052441d101c02c010300c014900740403c074040100c114020010b006850607914a02c0c0302c0c00e1604031a20300d0b00108080a5441250452000c4500d000c040c810b914440c0340583c0d654201b00c0d40015070340e241813080c90607407510030308480400ba040914039a5810640c4130102025001402d010f510071010420008070401d000c440c184a09090300c401452884d01d400c00000b0504031400241010b4a8842000b4031241c00c52500c2e400c3c00a400000c0b96600009000303540d01080200018220000c0131854044910a860041d41a02c0a0650030301c11640e80307400542d001e10682c54401c11980240c440306218103403203080703a42d12840078804030340c0381d441424202c2c42ea840180c40303840058004840c0e590500105800c518014401c80d002441030b16107281d0010808640030b04401142e80e110303000315100450401c80d9801910000303017070001005080c80e1508103d41c10a00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 358423381 1250 358422131 358422149
    0x12060105100c0206070206220f06020d1e0e010201110d020702040c050f0307030e0a121205010e01050a0b0f0f0301080a0c05030105060607060b041b0c02031203011508100b1201 77
    0x84001c0c25500c00c0c1c01030038031580d000c0c14083c1452895820010550864803884005104003c80c038481416102c035a94010070119030120306440c20014001c4c00c3c045000503040a10810950741600302c2519800319660302070600d4010402c0d001500105d001d041c071048007035180762010842c1d4007035100380d900410103144210307010400c072588000f040c0e07030700d02541849402c1010203000040362503001e60890a510415101912003150441e0742d00d103110500d25180200040b40c0d14400404130741c4a104040c003402e8084c0f051039a544c500000900d8040a600035400d03090808511202c240d0303440425211b8600350800001d03125a16040d14641d50070064a05880240c04074400003010b00b0706102d02d901a90300a0081c914205460b250f0034098100f0001858206550705059861440030704400c10038405d082e80d4410a2a5840c0109072914105052464403c0010001004260b800101019440200d402c0ca40c12603600c200f164a0a4095903000c18040c4400040d020301d500b0490804605855000b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 358424631 1250 358423381 358423399
    0x612160609330207050303040f030b1005030c010c05030405030d0e10080606072004140915061324030510060801020a30110a03110a2a0212060105 64
    0x80c48080028024204407000c020003016120505849040b0030010350050b00451306405d658401003403440c1e0242d1722840c80441c0d620028010840400c038095040070070a198075600c01d060500103070302c0d00ca00c2000030b0305000e400d140e04820007909209a400a000040981c2e0542c00d03100009890405d001c942d05100c0c00805501c040f0a0740100100d60148101404403401c0001c1d582d01c202040c0c14080f410103d0078012107000304250b90350b0080107a003107040c8401030050306000d0703a258039125a0952480c00344000c00704100c00c0780c550710290b101d80c3d800c0e110042486441000244049903080d804110000c2040c41c000c810b003c00050340d1003890440c01c004206856075007110714200c0c014205a034000466012229200504c4100e1003040e02d4200c241600b04031000d400010201e642c00a90130820100104010158680610440d01e4000c484c0511510b0400c01040090a1341888401518849005055011056585d018050401ea03014001c040c0643c1324203410b5603110024402c03988148408 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 358425881 1250 358424631 358424639
    0x1060f02070303020d080703020c0d091e0305061b0910020f07140913050106050301180606050402130b0c15070c05010c0207050a0b0309030906070b0f100f0504050612160609 76
    0x2800070440303815601070000541d030488100ea12441c003074040c900701a02806200b10a060900c111140103140313803140041c0c58070301030300b9441d0500424038150340d103000118104041000407944951180084040005030b0054100044d45030080b1143e05401001000c800c0c038001e500042c15103105a2400100c1e08016520307501044855110100c032504143c18002140c021400440c0030782c4454894400072450301d46840c0424211494131150580213100c0c1101c10003481700c5840354402600c0250382c29460010000c0d081ca504c03042c148200c45807071000044440c2c1c440000c0c000405021081c40c070138022401d080d000240596241c60040c2c0f55035107400818180b590000410300105d500c0034111404141ca0320358070075070039080148002068001000075400e00e82d01e2000400c1070f00d1082400500a003000703202019100b1001b1b085a007100d800c044140180d04402d40010101c0e10100c4012407259240c01c040ba800c200c8143d40c4580500c69080e91602800c400d02c89041640e01a41c4c600040c1036071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 358427131 1250 358425881 358425883
    0x5100509031606050a140c0a110c060313050309210c010306240c02031005071701180f1e1b020613110102150403030b0906010e0f01030c0903020402070b01060f02 71
    0xe10504024459003411004001042134200662090b005440011003102260304840c41400442d000c1010820000d0800000c3e504215461455000a00200320b00b80b401d00104120f48005030191548001c180d400c0e40400604108566540d00003600400d0500700081c07444458460b00c03410311002d805200c040b148079501c2031048000b1190714000d8090051200d021001041500304080410043c003050034034007588042202c0d114001e01490000303813038a814a4011b15142551201e50140041e0794010040e036240034003441841001c1c5400014032050441c104c0c001060b07160740703240c0000711401e0261800c1d855540720000304840c80d0303800410340343c00350710890b1074003001c540f80783e0f4000704d000d64a40454003040300032241003418011585000305000e41005822400c5900700c0000b6242d03102812141400c80d2134035007013202030030443d0800103039400080d04180481002410075a842c051040003900c220a80c0e001550058070844d9188524181440360503400d00a1101051030400040032440c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 358428381 1250 358427131 358427137
    0x906050607051f110301150206090a03080106080c0415020f0105011409040f02030703081b0d1e08100909031805010c0206040b0901050f030108010c09050103021309051003050304030510050903 84
    0x5840b001919421540e106000d9200100f0f1100c030b00000d96580d01e08090500920084d406804181d000b020724001c0300c90000e2074548010030101643d00059451000a81c2046103103054a50743d08285400366944042040705000b030740c3c802c2c40c00d0825003085128254002c546404642c000c1d8000f408140e8807401c80101d9100403900c1141c11180700000100800e40000d410382043e44001e05581c4450360326141c1c0503687d00001c502060001d44480602804401006145191000d504214001410017035091103c1038941c0c803108280110781000980504038000c0c070030b000d000000b40410000089050041c20f051401d81040d000c1c0010031000702c0c4e698040c464400c546035005124a14260520002004c02d401039042c039070502005000c14031031015060087c50281c8903010001541e80d0403100024598855588001c0c141031040000320408041d04048000751201d410300410756480d164905076108489a00107002c41c00041000700410801040042c1002c1b0040800e21245d111618603c0c2c680c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 358429631 1250 358428381 358428383
    0x191203061719060f06030309090f2903011103090a17130b0d140f04060f0c051813021315050421030c0203120405040c230903030d11040906050607 64
    0x5405039002c1c035611800d2002c1c0c281454031810020848110164044080c1c80940d0800c4003c1800c0c4034050003000c41074403812040e02c040203c180241c040500d44010702030b00200c040c50304040e5070742c1c0008054070250004280841101c0c4565079a10b41483e0f11501c0e0104400100c840f20f040b251350100c040d0b0380360242c802c8025802e503101185450b001b0014610b5200d500c1411a00b91203074a1300c0100200b880324903120b01e1000001042501e41464040100c4454400f0720540c140f5241c0c5070800f03103900c2401e0765030b61802005181c7c0c50070494400501400400704941659a000107507603040b14082c108648200c40c0349411742403c14100b0607007940d25001e18001c84444030002504107100b8204458090203550003428001204280c94020905040c08135462082c0204005010071507070610307208403400c3e03908078500400a1a1446070f01c80c0021844002c03011881004941031135240d9090040728006068213104000003480f6054080081e00644144101c2c070f80360007000245410107004680c035039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 358430881 1250 358429631 358429633
    0x30209060108101208070b07020318060c0106080f030d0b1c060c0e040c08040b010605071e021f0306050f090c0d0c020708101e02040b040b0307021912030617 69
    0xa949030401150540c000800354410040040d9001603042001c3c9112607082d070007094910354130000d0303003000d40141401a0000c811035004000c2d00c08a03610401e01c080100304111610341d0b48815000c5401d014020581241d2454010924107081428001000380356035002c6000501200030304404001d44d03101c00d5080048000781180b1000b00090480d405034080101500706059001c60040220b01260000c0b11030034045007005042c00117221121b24080d00508003450140d2802c04e0310394601d0703696802c1810f502d030a0500c6940b2201195070304602d0070747c604468141e100d004034500100401a000034862540601c20081003e0022708080d8442031040c0110400e903450000800e08402c001c08010740031100314055040e0100c0c0450f4148003c82c0a140035a9002c1001c25400c41c02d0a010119108002000352040000b008103611001c00c1c1c40841d60140700480e2207036640c150aa050101241c604d0550582c00c995610400000c880f8850244505603002c2090782c1c6c84598409800461100c0100f076 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 358432131 1250 358430881 358430899
    0xf0f0305100b060d230403020d031d07050423040f030f020d0503180a0b0910051005090106080c04050a1d09010903090b0c1e0c1207030308061c0209010806100608010302 74
    0x221340c90a03003100f444a68102a603100700122003840c0003040900340d0b03044006800c180b00340120650716000e9882100e110501903200714400c2280e203965000944a224003503510b8146803550203000701030701040c440d030701030024440f85000e1500460800b034030001200407858054070510300b14400111840309080c0c0e41c6480b451510340c00f07074041c4404481c2c0c05e4032a492040b200c0c40c4000400c3c840d03405008250681c01440c0d400d01880400c8180c0d103000301034a0b861941d41e80108080c6c0d860044041c1140c00e1401c080c592520b031305c000d4200510030b6070085600070b0350608002448002c030141c1c40160145468111005460307044185085c1c49040c0c0c0090000b4528440900044803464001e00020b1461022101e111080003140340240114000280c0f15801c0003102110380d0411003118110195142d015100c514107590380982881d4001c0c0080d402501c000055003203c85a2030302d98421070b5001448417a0ba580d603900c04a03031b2010100c03240c0f503403c03e003458009000b41c040c1c0d1006050303030341c02041049 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 358433381 1250 358432131 358432147
    0x20f011112042109061706150a0507080a050a0906030b0a031518050f06070237020405041112030a0507060b06040f080607080f0708040201030905070f0f0305100b06 72
    0xc03031080080c0054410402c00300a5440000151441c10401c00c001d44512001916005c8054100c400302025240c1c110019801c00c00e243d5100d481140302c41d1010840503490300b0b40d102044a8034080c0c81e1004240801c000740001019170401c01a100a0036141c4d84c0001e601e0b2200000c0301602c00005500d0741080c5002c4061001401c68021a280c1c0091f041d0001070b41c00804109042d5080e5400d0240c40b00d4002d0318554003000c100780f00c910f900164031300080c149240b003104200b41000f158403000036400c004a1170100301143e002c82d05503003190008e00901803410039040c92880c81c0080c0740c015205060382d0040d480b0741900030058075135640c590b4540c6070425a42c6d4070750700e000e0302c91581d500c0d901180420000c1140e041c1401c0c5800034124800041840e031900c41c10241507800081c0010404c07002c000200301b440d0303501100d45944030398286008a5000c440d860801e2a02e00603405c00c1c0410901c5060210b009540358030f44008890069003150074400094100b60111045c10070400c1d0071040410240d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 358434631 1250 358433381 358433407
    0x91e1116150609151401020607141306020c03011d0d05070602090a260307020d02013c021b0603061909050a090b071e0c0303062301020f0111 62
    0x1100c010302500090303480540282440c011290b680e002551900c4e690960204548012443c0d000900303070911840708141c8030340002070350740c007001000c031010802032000d07820030b03600031809a400703c52500005100443d141c00b0060740b0380214008142c0298604000041440c1c1c6408603003219181c1e9001600200302c0702d5804a4aa0380f02e8030040c0d40300d5408114851050f1200d580301c0c0002c00b14021100b0740300c8810f035042003003003000f06c095500c294002d001440c050707a0f0b8405032a5400b9824201108868084080d2201e5564085802d08400c000c801c030082d100c600d4101c400345070750202c2d03099982c60308072000401420080c1000154000780188000703819420075400d601880c8080100c14002c00c1c0c4c2d1070007107109a078012151000303503d807035411400820203c1202035410403240d0415142500c540501c0a41444c02040c2c88010030071a05e1041003403600950202c2d001c0c1034000e0482c00c501d40781502c0c003d0b804082d0b0f0394079401445641004007003414107124403299900d13032031758043c45d00303290348181 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 358435881 1250 358434631 358434667
    0x80d09030b151903080319020c030a03052d060f04090b01090b0307030b160813020d06051306110c070b03090c040f0b03010c0e040c0302040806040210031104091e11 72
    0x2503040b002c42c0500c441e06052100d410002940b2550175642d603413500034024400d07204d41c0a614a003060041c03000404c1510b000c400e82c1d07000100b61a0000e09aa034520398580e4079040c5d03000c142800c9200460a10601070105541d03032113207000b91034106144e2070610500040710740c1141c000d03102c0035070040140141e031400d800c40922101c00800702c3d290117441e038560107030840094410012850000d4204110140c00c01c08440e80b14200403e90302c1a500650080f03078400344043d0006110541d940300203400302c00c2c01c41b454040d5582003a0b08000705040301503191b40c2c40c1d000c001021128803524034001090700c024000c0302e11071500d517000781003c10f410b14240b0001e001d1a0881c401d0300c9840e0305462107151070074070450803141225602d6611762209941840115913410203150209070042100303010445001903116080b96040c0d074400c100c40c0f80200110000d0003201c02d10002c003100010700103494203071038011031405480b01f03480020500d90700284004070b50340c0c144199240c7c1c2052050a801070080c000d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 358437131 1250 358435881 358435921
    0x3070905060303130b090405011508040b25030e30130306110304020111011b0c0507050a06020d17060d141c030e1009020a051009090213080d09030b 65
    0x407070303007091412100c43e41013066a42220340b0303105021820050a141c03a00030140100224440b00c0701e40710f6100b400030951080200098505204080429501d80c2c0714003a01a40013140c00c0580c00805101200401030072900d00c040c0240d00c00c50094142c8400121030700082d4092411022259414100b138030100c070b801c13805c1e450301074023240c100000201d005401030003911100450f0741035a85c40d00d0f100260483c0e0702020800510f80c0b620b41c00b41850030700095224141c12103410704640c84221450114901151034100541201e514240091000c0e000201801c3c00c55282c1c070350381e0031600c11600c1c16100000032240340f0f03440200c000312500800c44800e80f0402480e41c4806888031b4180e5101080702c0c0b06510408000060358a2030300c10092a010300c000c14601480b000144180034890300011200f0900b409403900ca040011051030304140145508001818040400e6456031007a07651a0b14206481c410040c0c44c2c01103880405109225092a50580381c4c80540c501d0140c0300c08491005441c00802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 358438381 1250 358437131 358437133
    0x50406022107030f0e0a030b04150e0c2e05040f0e1017010905070602060a0c030e0d1b0c0306050f0105101d0315010906090e030313060f0f0513050714030709050603 72
    0xc01788501d031503001d40c1102550050030b1012203802c007854110010501c104042d0010303807401021134054440803a111402c0b01088070240040850404c5062540002102d10740d60302090001c00d9114030303003110141089892070001407040903a1043c020701a010100c4503220341c003054640600ca08421003640c3c045185040740001031a082a90346d0900d032541e01e2700401d02681c85070f8108200620f02d40242141540146814425115400000b80d611701f11a0444410310140b400b8100c0080d141405c00408990005400b4031380c16500d0034064010242078580000300c034641000071904d42400000c1024103080c0380d0354640e401d0b00a0f02062403108034950410741c14054118240d25004600c10428086e0080d030400160b00c80c81c3c8074041088681613901004030380c10a0082190070791003201c8610445811850110307240003401c4c1e1190040061400c480c01d014540000d01c5440d01040420080e114841c0c2e040ba8140750f00c8404258900c90030008460381a84680c00500011607107400c401d81004001d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 358439631 1250 358438381 358438397
    0xc030519030f05070930051621030221090d0302010f05090c06120912030a0c0e04051005060f0903030a0c0506100b0409020901090b0a050406022107030f 67
    0x10404150359010030209100098803481d618003030101c9442600d41200e072900f00036408900c0d005060b0000000308030b00c0280d4004a40a00c5000c0122070441d608032035011050b50314105440c1c440041442081c09400b2206501c040840000f856540d0303d02c16842e055001032500d91840e9464441c007120340da1000c44a00c8050080c076403252a030317a054805542c842d80001c10a8203000c001c2c2802c490340104811096031064458504070f854407811242c05204012040403039513201c1d00020700d00503c4103024500481d00000704103240240d5801204081000c1d510712200c00744880070042540e070103072412600c011650300300300410300d8034900400d02840d92050746030420400c500000d09503004a40344102003030101c000038040200900c00d9517403044250380c0828080e81000031440d464000c4c0d00070301080507400504500c10703a0041e05401c0c0101142d10045546131913080c0f0080080d0000d1007903401502c546041425100340780b84a401428080081450809846403400c5451408a00d2145e0070b0090710 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 358440881 1250 358439631 358439647
    0xd0f1b02120d0201060e0f060d02100201060302090408070b150603010909020a08030a0809060a090302032a060103150b0105090f010f0504170c0a270506010e03070e07020601240c0305 80
    0x140200505a0b03082e0300000b8003d454800520708000008000c5514184070104100b450303510b200034032460940643c0c07000300c0c21a203031905900511176600080c0d4400050700400081102c01c000401110b4815000d2403039a448014400c81d40000c5030301d40c0d42d1320500034001482000500c4d80802c0c1094001001c00c3d1b517180e40d55180324110780c0070741044000180301e1030412400540130894290803440080040043e81d9190700d000f5241c3c0a6002014103546400c5980ca401100400c580703000343e8002001d17200c5959481c500000d40207140e41003010014280403412803190300070303400d43d082100081c0a072487c5482d003030011107000940790400028441c0502c8085444110400f51303d220011080051200858540400c5007203146603010500085040030b01112680070484041104101417078081590b842e0200142e6212181035021390f01407203100c0001405070f8502c02ca0501882094080c1c40291f603da0a00e071341000d1781c0480c103103401822000c000310350a108042c0110020300a2030218208148 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 358442131 1250 358440881 358440883
    0x171602070306060803030a11070807031d040f09030206070f090504021e040b0a17061c05070812030a060807060f1d15120601050301180e011103010e01080d0f1b0212 72
    0x1e9a0050601d81e8001b00800081021a00c1000c030040795030070f05181401e03180d40c3c45190601c580c5400404100d01401c013298001032500d00c205a004006000348511411803140800070099111b094005106110100756143e00501104410980030b07601c02014078205000c0c00007039030016000d10b04420310240b1052900402c00b0240c00901600303000c1d140d4403211210010318500080070403c0300e120442701440b00960f6010020441c0621858110035095458100a42400c42c0382d40025070600502d0003140b01d008200009500c143c00154042268035110380b0101d9440c0818080c90340410503c985500c10f00d40901d00d4049140748011842d842140a00701043c5101ca84a80e4400000f40120305500580200d490701c503440038007032901c5429589440c045403001281c21008040d402e80da5071500412210030341000e0010307000d84054990380d5a4480b0441d44a607001d01c2030f1907560045400b1b03100006e2041c0d4000f40c035407a9030342d00c03900c0403242d000a0030094104984d0403070b401551015026075160b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 358443381 1250 358442131 358442141
    0x801090c0e151203120108160e19150f060507051203070f0c0f1a04030806040903270b070b040b01090902060a0e061b06010609090b1c0f14011b171602070306 69
    0x10841015010740d80e0441c0d00c1203050301c85d60304270603110900c2d40100050100303c00c01903803280d00c4d0b40d00c01007142990820380f05007088032a0041c51507a4138019012600907000401024624403c1040300c0407480401d1140010f800140c44510000384850440012948500c000e20092405007130f1803100803a8550b00c40282d2441c611000d05800d05100c20031041c9908060020343c04031003910700380424401542c00400030000c0e02c00031450122400c00748540594065044c1000e02910b00e02242d80e20003d007404e40c0d22820481d030498a020030480003044440d018000c90f007520307a0103401181400403039038054a441d41d800c4078540d0000b009100e0003a92510224500302030000e4200038112650410310000e0034402c0540141008ae81041c9082c215525860300c8a4200c0303100d41c1c4604000390507890031050101c40940c001d80143e01940b18000d80c07102c1940400d44e5006411031014404000302c41c103442c00300d0000a20703283c030300070b1400017460400010040f480215440c41520645a281e80d12141102c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 358444631 1250 358443381 358443389
    0x315010905040c0509130b0702030d020315030c2209020112020a2d08010e1803130608010608090c0904081c090b070504180e03130801090c0e1512031201 67
    0x59203400070b10080c01011040e0501505080d9001801407030003500b2078080e0441000018402100000012440c0d032083c010303a0701c601a40507055649060041c41815007a580c02d18462080c011142600039503e80001d81356400d40702140304c4001ca108002d03504000b4240303204140d0501400ca42200d400c002c040c0300424803107a154446090b5110001000205403042809941030b505565420311002504a60818110340000e032800d0226600d000141d0300740e0b1101d02610340d0300e00c00800c4031a840d01d035043d90401603074287d0350369500c10780e6581401c132042e00d0255034a0445400181848140d0f00742070b00f04580c030030b02610310145414030400c90141c0f1081d0140c10f641c045030340c8a48020810884a0883e40c000c1e5841c9031590810741880307aa281200e0040f00302a511a5030f405641040a60034401c0c0c94400c205240d01c9901c10313684040450107006600342c01c03144942c07808000b2600022200145004800e044010380e4200c4e5800d040c0034010741a0041f03030400707100a0045445a01000c07103018060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 358445881 1250 358444631 358444649
    0x2030106080901052d04050106030212101103060607080a0c02130b0a050f0a1e030f03031b0918020f22080d020f0a0f031214011503050907050d02031501 67
    0x10701d003103035042d400c540380505014080c5101c10700140d100110203940030b1120704403903e6884251254508540145099400203410483c00c026171243c00c0d00c0801c0d03051100d2404201441041440e156020480c4001c84030161300038401d104e03c001260a00025024607440b508009507100440d400055501c0324604491451a444a4544050741409840e14004103400e407070300c11168149000107600c3c1e1415000f08908104942180350038090603003c200021500008030b0141c030300031400e0060103001038841000c1c407110700e500407151652003021500c0856440d072182c00e44010340900c200000c3c0d44960490085454203020340c569099072902821824020303100d011b0074080c034000c4640c0c10b00076885013180c2035411000c403054074400040b8844c0c3c5030941c03201411105815624040e1503c2d40c49092581c011450145006111000000756038141d40c0c0d08207540e2144412400100c0c15034004403800d600b1a00004010840d600f003060000c1da040e032000301500e0715400d0f854080e0b410610240e0000e214 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 358447131 1250 358445881 358445897
    0x906031a12030405030c0609130504210c060e0c0904060203091e01050604061703030604020f1213152d1e020a08060a060e0f060d1404020a0807050310020a02010207020402030106 78
    0x113615040000d4504000f003070310410b041c070f016039000903e00b0b081c01c03d403100076a4481d80010304000741842d83e2000d09e0804001140028195403008142072501c40b42210740c189030071410300400400003005188000010f00352001c3e582c503a924900a07403c054140c02c2d0f284100201c4009071030108000702044544500006142d01c2d100c1c0070001a50501c1d032142c42c0080708020b280500b24004411a580042d05480242e03442404000309821407003031000302c204010641043c0540c0d03031144030315110714900401304014400040a140c00407583c6d695400c00405d89155000c051a00740b00c40c01d8650611221400a169103842c0c120035120085020f61450546d40082e41040554001c55038540114042e0741140083e070400740b01a12542401030744a20612903154682c1c0f650781c92104440c0c00d185020414001610001c5100f4101081a20304038480e142443c0041441c17540025141c04540006005003070740040f9021440003035000441c1d81c8219502007010b20090780b03450005500070003580e40e915803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 358448381 1250 358447131 358447139
    0x1c2409051b0703090603020c1e030c010e01050c09040b0604050405040302101a09060904150f0207030e060c060705070c081506042004060e06070501090b040c080d0906031a120304 78
    0x660303025410707061990034410722103140841d504c1004401550400c1c18010307034481d000184d40340707840c80c11607104020503d40940740d070304848040f000c0c0c1005e4200b10700911a0100c1b080c1c403d420380ba000c451000241105100301e410a00d043d13081240d4203240900f02d9490161601c01007415030f0303811101600940e00805611000030094071603200c1c5103c0002100c0728082403000040c417000400b80417180f2903015400810140316441b50040a031640d800d8040299003900300c3c90030042e412408055001c104d61810112040c1000c400321015010f910010300665a00c030310050340d454006a405a412079a4000e001c908030340300300124101c1c05905048480780d40740c05d40800042c0c03030320000c4040e541809825101c016030348040039142601c2c01828404070a610302d50110355503005c0c03100c01810380e42c20079401c070003401b0b2001c800358000c601038000e441c86281c5400c00266210600726010001400b07841c030400c5014820303807045110410301100032001c040300d007000075200314089101c808503400001d8208 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 358449631 1250 358448381 358448401
    0x3060803030a06171617010e07060e030c09011a1b03031015110c1212030112060e0a03021015031a010501122708040803030c030a111c240905 62
    0x1100070000c3c100030540d14900e0105d00045100c14890f10594190380c60403010102429001a4000c0c10000115102d00b5503808004181180502055000b4003030b2010488180c207090100a0680c1d4010402140d0718442034844601c03580210b90460221700103c291614003c024801103014800d400b80d0081c109084c46000c65030b04500c20001028000c4001c20207200c1440401c41c0c500e100e404840001c13981c2051200d250034040d079002c04942c0d8001c00400450b0800c40208096640341c001d00d010001d03504c0c4004100c4c1d84501030003002e000350b0f100301c80c1148030309040e0300003003904e008012503032090307983c0e95513144510301596005540c241d40130700051080e56400301c2120104036142d0b806000b41914991041282170160013858251030b0100030034014044603c04660040c10202d0480e0b82d20314002d00d9886040d002030381c00c3c2202c241000000d003100c200305d0b0b054526880c948413448480c0061141c2c100001c1608500c003845c0d03c0d0b803035010110558007401c1e01038002d10103c41d002c40e0310301d4510460 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 358450881 1250 358449631 358449659
    0x3121803110f060a02150c0c030403030305090601050105120c2b0236010c0501152c1005010503060a03051207060b030a0f14030f0a030c02010510060e040b0103060803030a06 76
    0x2070b025140a005000c41c645e0b0025268840015041c90158191611400c185140c82090b910490611000400200701603040c0d11851040440c03005445503640c0b54001103d5a104401042001d4440c0d02c01141a00c00c1550007800c021040242102c00382d0020440810b0301d085003412418580d074003080030007403440d2030320801e0103801d0882c818843c0d2500040c0c0e8405894245d00e11241002240303001c00040007130035070003081103846c07040300748a2050ba03e2400d0150703d03041c2218800d20526940810300030125001c842409070016040440b2803500340401103910350070042030154043c1c0c2e590b0001010032402c0c002c07807180c002c4a0010315a5010349040c50001d6074848501d45000313510000c040030205640541030042e1a50081400300c0d4001c0f400040c502c3c40c06015680c0d2400000065495011070f0103a002c0d1043c94070940003401203540c0c070004144529207a2041c0008129036100c40130507841c187e0b000c00001501410009541515160303043e1554008803030a0810030b0b900c40d82030001103200129 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 358452131 1250 358450881 358450909
    0x40302011d03100209010c0501020309010605100206010303055707031505130b0c0307111501031209120f0c0503030406021504020f03030a02070306050106020c01090312180311 77
    0x10010120072001107030365031101007200340c103996002c00d07140031581c81055003495aa4102001350b4590405606460090203544100751040740401001e80c80c19002260a03812a5010346905083c00480c41540d41652490a6000d4040030104081e15407613a00c040c1c1e01c030000201000a80c403a02418000350141000d030940e140140c2d01880d0200005941d80343c2c9900c440d0014940818103860303100740e4048038200544002c1c1807010320f404000c4450210005140b2400341d0340c3d2100419420100c000d40c4030a043d10000885110f0317031006002150094010091016040c40c0c1070b405a0307a240c81c4446012114413049846c441ca5a207000140120890082c014060440181d13281034a0000007039500c80d00190810346401385500094155603d000c42c2022054001e0180d0707584503135003400207440340300a01085410305d1a040002c1425807001414221484c81038441d0100c460440c0c4964605684a130300301c9080000032020300300c0884901c030010004500c200940c94155415808008540d011020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 358453237 1106 358452131 358452167
    0xd0c2303041a0103020d02010807050f0c030d0605040501050d06051003061b0906022811061605060109091703180303090309180103020306190605031204030201 70
    0x80254440c0384560200d168412030400c034120b00344403c2c000a0b412040300042c08006500500700305030495402d06140e4100717035004810702015030101e081880580c10110700810791503003d0041d18003030803040700d0a000940c1858041845846e144402504003510740b4040b40c900d1202080d03100255802031424090303c10081d503610030811740c850351800044d40501c0c0c00210039101050f66100095440300980103040d441c42c1290708a6081d0a050324219400101052182d50f48070080c0b169000d600d5514001e0011424494241b503016800784004034103213035401e8002a4409814511075003c084015141c0d15500a8000421404c00e030050203880004103210703002c2000009450a6035080718200480c4803a4194004804020711000b03400d0341c8940003080b008072211080c3d861841e451000007031210307131300c50002e882d00152491b080c1d0b503244006000e000350b590100e601c1c040c00010318 = true := by decide +kernel

theorem cover : BRFrame.Cov 358273381 358453237 := by
  have h0 := BRFrame.cov_init 358273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 358273381 ≤ n) (h2 : n < 358453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
