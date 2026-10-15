-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4134
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:40:10.440429+00:00
-- url     : https://prove2.me/submissions/7dbe31d6-801b-4313-94d7-5fd2db1e3f58

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 743345323 ≤ n < 743525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 743346573 1250 743345323 743345327
    0xc0503060306132d02040501030302070e10031101140d1a130219081807030f03120b030a030e03010603080d020d05131502031b0a0c0b0106110712020a0f03080d060b19 73
    0x111804d800410342c140c203c0c8000068031180f050314001d6021b42c0c041c0a8050416400030a25a005090111880d17030002050000c205001041c5220344d0b0242440181c00d501120020f039203015103010009034524290503034460205219000c00d0b80d94044500101c00d01d4158029800c038080c0c000c03c402c010301107421403103880303014030380c525085005204120008406202024a003141942040752440110f0107050304140d0010f0203006100d89a12051002c00d80c8c0c0404213566902000001d00ac011800c5022180c5440a42c0700d28051500403066559130003544070820301a50168807030700d950718605800030301e0001c80106201102c580c0712902e82210740f40b030b460706d2000e9000038100740d41803805608100c0c030b8150072034002d2400c15041c2e100c105451042d410548444101680601d05010001402c45030100c0081807200642c3c0d00009020180111030022410417080d5810490a0f201030000c04418003400d4002b43c8009580303841d013807000075229454480c02b802100ea0200900650b00c0440785194 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 743347823 1250 743346573 743346623
    0x7030516020d02090705070611030103050a0f031103130f0501050f0f030a1e0c030606020c03070e04081204140c0d0c05041802130c0806030c0d0318090c050306030613 73
    0x60009161280c145220f0b00003d61040040d102440400d000244000c10050180607800028102c03141036400c6614503107615803036000c021001044140515161410180206c031751241c108000d8040341c1e2030b0754150801442e000300d64055411ba1100d11340340020307030398400d80454801104005d051410107544012280300782c0c1014140c10803071394480300f03040c40d44030040d03031410728000e081d0300049407444841301301600322051500418215003140140881d152000651301f0301b142d40e41c8031b032341e0b410b69118101f5031854042c04051a10b800b16030b00521040c448854010740036a0244401e07102c120078641c08011400300050030040140c0f0500c042000107240a0340041c0041d8200485801562000c0d0700040350000d50b80d03408a0110707a92001c44404645c000305542d4002da043e0020040e4240060000b1030030304200800070304200c0341429901044101e009054010260200180104c0700440d10240c8282c01c11518207009201c1c040008100d6011080358070080c540041017404080d1810341e080700c40ea = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 743349073 1250 743347823 743347867
    0x503070504050d0602120f01050f061309052706090a030f3f02040b07060507090b030c0403150b130c020313080c030606010215130213090b070305060402070305 70
    0x1100303081c080020140c88041c0c1088290f40301380700060356a8a0320a0521505901419146102c03180900600a64480c801c0720f4604940c1190550744400c02e822100b00400002c2d04511280fa0500c0d00340300e20040d1210a410354165804902c00104581100d101c0e507e5800702c500c142c440d444440500c0210f4010080e00402021910700300103c04403403c1520300140510541c11340d4811050b2164024258441a13400351105003241545818a4601241691300070408080c111542c1c1e034000c503440900174a0010001c180710b08066482e03151216113080d00740c100e1f02c02581d0303130300d0034024459010348203100e4856210002015200508050200907005000210350300003544400c001180d80d1052070102900205142401003c0c030203403450525003401c1c00901b00c02e05544c071100200c2441c901d043c02c1c903940702e884441310303601d841c0c06400001e489080600040955501d070501050501c03502e44072a83c03050030180c80c140559220b59081c4802c9206030f40c80500056420721601c1c0c50030303111300005021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 743350323 1250 743349073 743349077
    0x604030e21030a0e1e030a06110702030f0303041a36010e01020403050d0206071e0c02040f0c02010c11120f0f0f030f0606070c0b0901030e03130e1006090501050307 72
    0x340041c9030181e40c91603000704069004500340c070444400310720300040f0056114100324210140d00003444046a9940c0c0518002084152607020700807200b40d908040d61b0056400508035010800302c420003c1c2c03282c0c0191030942d107120490300743c404440800c103e418081e80500d0381c0c4104810001e0b4249051009e09001c010b0008001300942c510903c09000d14019000031100040c0d4807443c616056240c040300703410744001c0d07402c40000c00080641155584c020380c0000c1c0c41642c213040c0300e0001101c0c13243c40c0e110020341c000d280c001c0600343c07a040c070b0340000d1b130800b9590002c0004114540c029034124051886104071741c3e026000d030415071424071000d0b00301e42c20303003441c403030308260006409040c2d5800034081518014004000c1100541d038556025070400da003614103920340050780d00c851034144814011180700703001c009090500d0340d20a501038410b90b101c0f4000d0380e4550201c401c40c0654028944030b98031030301c080900070542c1e000002c4010021035950307490f001100c0c1e241c0380064500d50002000401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 743351573 1250 743350323 743350369
    0x71215061b3809300d020d0e0105131e020d050a1202120913020304031209110111032a152701091518240c020604030e 52
    0x9440d0010744007804828682d66910312803084040d500c1400114028155410342d80f0050820000b012502d5524045010003070030a9690390b08000013401c02d115020f4001c100c07500c00201d0301d50183d0554040304c040941c540080c0301e5600e46844010b1140c0e100e03040a801d8100740304483e603820031074100401c406403000d0900c0070303102001d44442d410130b00444006c0d0b0b01450300c4101c4403540d83e07050168010b0704107104030050400130550003080c0c400007a0441c01c00640d500002044c107060003120020140c5a07042c0c1c0070f02403400c042c40c0010b000310070341a40034042161096401c10751a008001c1d01d21014032010170302100000200d06200094000b031074048640500712140d03900984102d141d85c4204081e032428110301c01801c21b002160a01030740310550b240d1512004500043c081d003a00c56041008010114005a0012241d06900314900e402401c0320001d40c07000c1d00c0085000040b0255001c032180401018084000c00c0e81c540704115002070005000d080e00084034506007c13079500340201640712035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 743352823 1250 743351573 743351603
    0x14070f060c1a3121020a2d05010e0106150507020603060d0506040c05010216051e01122d02251b090e070512191109071215061b 56
    0x4866802c15003c41e40da1182c1500018090051a40611044800c0c0b007003450040000814003c4d116900c160000b01480701c541404102101c1070417070104080b82c051241c0401200e00c0c81c085008010210004203103508283c0c0000701c0ba24010000c0c25100071648943c3d00d07000391582000b0160780000c099a512034000122080403420811945106502c00c91018804600300000649049540300f4018109a0358a209000d65201c1c9124182c010146159541ea1034400d4030042c2c0d403d00d190142a00c03414640031032400c0d005c2621541607003100b4041050144180c0010504040c4e115051713000c0041290580c50180e80ca02c180d100481c02c90051b101c2c81155004a02c458a004a50358010400c0d06d4850541c0900020184942c3c0c000381000c65440485148900f150750b15003d92030030406940045103110000e0105121284039a14401400100301c0d1800000140210074003d010411403468000078000c0070007190700040a0f5180c81d2103840c0c61078505540740f4440710242d0401c4407a0940d0030780c49 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 743354073 1250 743352823 743352871
    0xe0a09091e0f0b01050a05060a0e040b10090e060a08150c0d06091e1b0f020304050301060b1c020a02030f0306010c050604030e1e1c0c0314070f060c1a 66
    0x460000e0302c181d0050015020a0408948010041e00114811804503008200c2c60740d0344012100314003424207290f6900101d64000900901c0c0000b99182c001014601d904103496000000748250b50880f48450749548400c0300b840809202c5010f0582c0960000480302188481ea07840f440c2c0c8201ca0042c4580381180026a0300269490b13503200403001911481c50b8415440581c2c408001140990300030030145816150040c680c0142070308000920101450441e8a07503c24401c0350050072010f0000c0c4840c59a0b05c003180010b034000201079020210089510071039080764002c482044100e540210709203484100781c9660f13940041c19090502080da941c100c0002c2003402074a22aa0094550b0ac0030914039000b401007001c420141c0b074031030b246070906022065480e039400614841a0415030b0010440a1030080350340d01c7d4980014240d10460001008c18110000d01c0d4030645002c4103515054035581d0005456810804000805400d507080960704c2d030012a011403940b04942205145640308039a0354 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 743355323 1250 743354073 743354123
    0x519080c030a050c0454020c0c120a0303200a030f020912251d090f060901050118020f0306040509070f0902120108030a091703120f10060e0a0909 64
    0x7031504080e10b101c3c903080d0001002d080d017441061150342c00c0c1d480c4250b051412218074008803041c01120307400720303c018100c5020000009e4821000c0c201c0e0072441d48404005a07039000610044000034100804803c41c1800c3e403135621000304184031203038184240f4140c25400361482c04140c114243e8280301886082d0750300041b5140c01c0001401130807138400042400c2415103401200c400034009003c8003007103500c03900500d8a01c480d65a0001c4900c0d919064503007030034041d1a214808891040c003080c411000b4040d4000c80c100c03010555019040114820413800707078040d1070526800040180000b83c6142029008554010b80b1803054605a81e1a012010103100d003507007060f190f10764045020702c100c01e040d40041d400341c03151900030b60030028494402090704000340582603002d107109051004114080041e40c402200000c0e4400b45032410003c203d21035201200d0500a00c01c0410b000940a4003d80240f83c42440142107031208500b040318040180080400480d4002d03004a480d030203141550700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 743356573 1250 743355323 743355359
    0x5012003090c0f06040611010908070c0609080109020a051c0206040906260c130609020a030b010f18140d140c03100513240603030519080c030a050c04 66
    0x4201a100c0c100508400d26000e41d007010740b406180108003484040c1d82c3c1c90281c2e000c403203083c0307001c05283c1c1701310035020702601e80d42600401c24000810240100a02e1001840a9500c26541c402a90b03550b100394609840c111100070b5003100039140144103c9c28510b03070f10001c4110b2024030303000d0b29025901207000c030b500a5016a6a182e5106014080c0f030440045144003d524504102121541051616100e03240482e0040c42100103003a84402c584a98001d14010300702420115150203040d28050b01901402414600180700e04612101c61400313240003144600080c800d0303000190405052001951044502687c4a07641030f8041000444562514110be0141c1025019010081e01070601e081c1050500c0460380e400e0204014544d5a5140b101861582051941003039121800c3c1000d07010403190059010581000d20210a00d43c102c8010424a103070303e15010003043c01c401c006c50b81c1f514151070f005001102040441c0040d074150b0086130304403031005ca0103480c140d40c95004110400d4029 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 743357823 1250 743356573 743356631
    0x209030d080108010b121213031502070312150611011d0c0a06020d1e05070803070906111b040f0e0a0b012c07140c010c08041101090612090501 63
    0x5005020f07100082c024645d0031441a24010001120f603803002e900e4068200700c03488080000329a007890002001c140a0003141c204010a65228840100030080e50001d0703415800700d11501c001c01c20180d440d1060740f100c0c4038054510400f4038100041120410b200320201c1001d9034803101c29603001900320011010000c080801891072992003010f0100e1b01841da44508159080f110794522442c1c2c0010304c00040e600710080e4628a00c0c21a10191480d0090740b0018082c10b1001c01048403998120070035170182c550544808000402941e6110b5031801d10010340c031106003100006103124185a001008800f500002c04a45c41d02d9001c0c00d6450120721007c180c60b806a0203004003c1c90006580c0d500302d00b52030141908618801e60300c02400e00c10081c0c42c2c030017013210204411170021585070075a180700c0d0800e0000e020050f481c8070000d10351034040e101921540c8a10a603510340f5801141c42c0001c850081d10340c00b1010038804a800020241000107030303815501c40364083d01c8440c9802c0795000b820403407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 743359073 1250 743357823 743357837
    0x8030703030c0c330e1e0d091a04030b0103120e06250f1a18071a0d0609020309101407091206140403081f320d081b03030c030f0405010209030d 63
    0x400700c464100d8400b41b0703400098020501c020015541f026004094400c0182c2c91381c020b800044100d603251190350f0000d01200c035103000100030411085a80d5604050319542e881c4a0002c030300400c02d90f84248032440341c041811070071079008045940c3c0510030b114041c10350303030011a1241d26850350441c8106410034428120704204540d5007034102c3c00036188224500100b00c0745040804040400649107038055124402040d030b03940c8410715030040c10107844090800d54403030421624183e50382c48408907201800703080403c080421070564000034880d10b62035036902c0c5c00390f00c0e11280d00d03000300c2c001006480c00c0352142c0410701c2c02c000565040c0d006034440e540d07a07003841c40e140f100c480324041074040c950000600848208588242e15041041c82c241c01c0c08440207000b03002c00080903864021030a103400c280990301c104180001e1030054046c0c02040c18403141003a2109103010f85901c8110380001d0000421320103d5a881c200c640c01983c010310510006150010a40c0000c2c07524040f0040342c3c0008400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 743360323 1250 743359073 743359093
    0x11040f080d02060c030c092803060e0c01180e060a2318040b070e0111010509161a1603090e0f090d034208030703030c0c330e 55
    0x1040180651100d250414036096080c0303800a0006c43c8541c42c2036500c665402c0c0c0884a22545640c00d1030100d03204080c1410405683e40f0f0500050507281065948034003403c1e032020000e50282d81c00c00318041c010f4920030f5285040c2403410a00b0380001e4480c41e0068800000401c0800303110300003000304d00086031881c90108071324081210188095095813403102001081c000051150003010b03402080505104480500740c0b00101c4020807a1038180c021503081800f0320404002c08030b000f000e078101400c4101c81c21911181d14030342080c2c0c00004840d02036801c000d00c1032000e0001c0351148650b0b01c01d18100219960714031820010607816a684503001c591881440980740e420881007074650940d06050004481c41d407180c0c0d5a10601c0c81064116520f16080da400100c4c030844280a0f064403c01107200b100e46591055590390001401100031900c1c150381541550f00888070410480d92100d144000c55620704d00742c10001c6290b1989001c51a001c0360003000e4640c90780544180340708400024800c91107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 743361573 1250 743360323 743360327
    0x1813021207090c0f0c110f0a0e0a1a0d03080c0d050117010b01020c010c02010e0a0807150e010c120c060b100c1511030609040c031a010302041b0f0311040f080d 70
    0x4075100f5800510540409488070a90000c40141c440f43d005401401d04150050100e4005900c0a00259004d10000d4020a850040e0403115000d503013005070404c4011040e2115192060040c50025440004038058100091094100d0341d4040c82008206041041c203548105c03c1c0c2c1c200380c000d000380d984a200810480c01c0240720301408113009100509a0902070300c0068640c050b5100302034100300c1005035502c440c0d1940f800c0c020050100204540a00e5901d285074809c2070429614603000820000700c084840d0301c900460108203400c041c0205480c01c07154010ba07080c40072103100700c421948030b1000c401c00d44c0e42c0c188204488801d507100c00d10784d6951072900790b207503000382c3d11440302003468041030403d00d01420703056070b46c00f4105540c81030150300c91b41070004100c001540003c00e070159551a407119074503513288080c101c901c29202403090041c3d8410340704075801b510201c0e000150202036030703001140c80386d04145070515204801a20706030302c0d660302c0c140c0d9242d5a0000d030115804210f050000075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 743362823 1250 743361573 743361581
    0x1c060902090f06130c050d020904020c06010609030c08010e03030105040f09051204060f110c3106050906030c0f10030b060412030219080412020109180e0d0e181302120709 75
    0x560940300c20480c0c5c084000000e070417402500c500d25485a0b0100d41801141c40f0360741100c0710b82c207480b03040350229079444e1b40c020161219800200c4194914410000e0060742c140070744918644031030301850031a0700788024800140381e01950002e00c1601c440410000c036078240006800401c00c1055039a40700e00308030010700010a0329140348200601c004a0400010001c1743e070100443c0c0c116002c0004400020218404c08480580319007081c010300d0700c281403124558030040c01c8a90603a09041c00369a00d07002c1584908046541623044a9031005900c0146824140e0140400450500043c000070350030100e00c1356000340e001460070070351481046041c560108004803016900d1151621300501c6956208014000da2242c01000d400c2c3c0d0500c00c0071607000c4c04980c0042c0080c044108034030700180e200d4401800c1980b100074000d02491001445252240c480c95601040140400003400c40d880f4240300c0311070006080c2c016400c1404164401030b643d0380e901d110060b5070b140c0100300301c50802c1d200c10111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 743364073 1250 743362823 743362849
    0x105040e0a0c0e0403021f0c0e0d08030403030902061303050f0c03010c02100c02071205011b0f0507020d020f1005070c0605400f0f090b1c060902090f06 67
    0xd5002803050381c00941c2408a940a49080410a400d25180d5107000d80c03601c0050031040c8891104940f5160950030568010042c105483d40ea0000700b9562100b072000780f070740e006009040410700b0400500824025040041058400f030601884d04a00101c41a001c1101d900101c42d075421082d41c4403d265401c01180110f00d00c101d0080020081e82ca2010f9a1102820b0300e00d68003036194000ba2075054000d10011300144507405000d01c40c8101458218000d04140125405160215104007039484c410a903402c05d40069869091070040d040e0204142400503800880e07200f21000c80140d0745441d00403656480c5a42c6d92035050701c0701000d01e0300301d9000169030031110400c00c2c1440324680b002d0310311140a40d403006000000c28540700b8103c9206a03818501ca544000e080c85140000d06010b4419641003141c1d5186615000a5220701054064504501015a0000b018aa03010407400071040100c2050b01c00e090000d01c034507450340411002141111a044074a0f04001004858181802e038505c0c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 743365323 1250 743364073 743364101
    0x20d06090e07051306090603120206100506030a02071407060c0b0f0402010f0c02030f060f1009050108031803070e0c1801050a020a0303051b3c0f030a061508010504 72
    0x2000040450303902e00a0384203943c8103c88500031141d6010090f0302c0f40c4041c0000c034509214241e00e0307060291100745180175080c0103100703400004280601d0001c042c0d058070001490309281d501c60400c202c010f50800c1c0e105a4a0703103200c2003458840f6400704152030082c9404d84078647e015030203007001c040820303006020300341c009122410480140c0c1d002a075844204914204403903401c08500100b4a808410703c0994a90b1081c0360a108405289440040c850b000c0b4074032107074800d61180065020b4900038800d10195510a1110b802d40070546101000310b034001804558145a4680042012600503504004044c80004888084945080c120354240200307003815841c3c82c0030701c88020358a40444402800301070743c40c1e02040c1e03d82d800a843c40d03601040d03642001d842e14401c2101a107240030201e0710000d41d081c18000d691000503801884a1803040d1601502c0c10982010940503213a030000b068060020742c2e590002c109024881c1c0080c02c520643d5841100960600d000d10044601b40109070343c0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 743366573 1250 743365323 743365331
    0x6090f070504170c030706170423031c050603011e2004030c03020a0909230c0d0804080105130b041113020408032101180e1203070f090e010b1207020f10020d0609 71
    0x20952500c83d845d005075001ca01d800300c016131103004100c2b0800900d64101e050100041c080d01590249600003525541180c2c00c00c0291504020103003200c224003101c40338027041282286200701070b68414203070841040c01c0e00c0e08807131f200a21080d190f80319400c1254551102d0400380107605044c90000003400385510304200d8140551211410711641e070200d2a05059031088288150005002e01040d00e6000740006640c00c03680c0ca0149565049401440829841d00000a1100c094601c070a103505030052090030280e103d03500c4009201c2e03000310606420401403154aa031040161005100800100c009592106000540c0c03008916800d280488010001c000501ca1311000c284440031806040310009518226105602d003481c0500c003600a00c1403011041040664201040d5503401d4101c0d519042580c1c2c451001c3d49142c0401c0c018112404400c0c03190740c02c01c0032602813464100c1d196004880a008a242e00f040c0b07041070f010a180c1183c2e07000b10328891b000d4550b00450020f8043e03040180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 743367823 1250 743366573 743366597
    0x50a0914010903080702010207090c05040e06240c070f06050703030c0305060303040504150506030405060702070611280b0411010216050f1504030f03021c050306090f070504170c030706 81
    0x20542d03041c034040136029603800200d40c0116802008801c3c0240790201c41441544031414001e456900b10344038034091807a01d1000544c0d6032524204541c03025400c03664100e0603894401d1241001e4100360040c180034403d031400890381c00d034601c00204c01040389544107030b07a894451500030251109507101d407003454206002d000daa0b07603020059809071001980c000806004c01206401c24807480d500503504220004244000d100c1e01250082c13040c10b180c1c007100c1c4519994034040751822034401e2440c2d8030341c00032606103100c00c4801000200741561248105d110410039200d069010605440c00c403402071072141003031140d58040c000000110909011400030a04c0c0c507010500c0101c0070100e4034421182c01d03081e00ca252000c0020344018507001488442d2100c21854046e40d0303507800101e40380307050043d080b0790803800d1f10880403070f0720641c4043c000c0c4869031210f0080d1060920050024420300100380000718840310380740c90407200111a18028607010300c2600a05003403415070b0300b04a040080200b103030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 743369073 1250 743367823 743367827
    0x30a0507083409050a021b071d010b04030204020f1c09020301200f0d09050d0c060b0405060310050612250503121629070306080609070b0f09030a03050a091401 70
    0x2000c81c1c3e00c0c114046915034480701d20b40000e120703200285c0e90800d080d440703510401c000000d1200585103620a02a001a07004220301c0d40e0500911509110780d504010510040c10301d6005000d0010030701160504000e28407242c91003440407210200c852075603c8115100350324003408be50010120120b400c0552428440014140e4030a07108420791101001910402c07852450b441925019000015100114810000106080c1c0070795000c1d0707401420a0040162882c107482054040c0100400816a01010040c0d490103090300400003075100c1401640c04082800920403600c03046080c40034540300c40c65550300001411850b401450080d8406141c0d5051854844205d90b44d00400009070700030100645070110040640c812480c1c5600c601d9440055018690b0524a0054100351024810b064852107060342d80c2800303c43c1c408103588080001c002d000070b4080180b40304007003664824940031142000c6442c00b1050407040740019000120480d005500601d920054031588034500b140405000c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 743370323 1250 743369073 743369173
    0x9060b09070e1c0f03080f09033f011d0c0f071e05031801030b100e1014040303020705120715080601020f01110301140103020301030f11030a050708 65
    0x40030302881e50104140080c02d0340b4020441420b502070610219404e01d4900182440015a454820054501e02007201e0020110a40e9102c484042010f050004828030100f00500c1d240500c801e4042c0d15040c2c050407408042900317019084100c08000d00501813020003c8c1c3c501d0041200742100b80c203003b11400c0740400341c210707a203881c0c02c10903481051038030098040c0d0111404600400303521000400040b48402c0340251141d66800740c03410070100c0d4500d42130203d00b6407409a2800020382a1500002c02e00d0b01e4800c14046840c141f8002d24400403204201c10554400d40098016a0114104006901d003c0b41c2e0003403604041d402604200d0311304407409c018154025030000910005200050643c0d02c20000b0050b034541440082c422028004a009010b900038040d0300c072a501d500340100d5031035001e4000c49040b680d102c03a81000042c0390343c0300c02901d8000c01c0ca103030743d16009401106011031302c2000f03150302601050380030389031141d007602105141017141c03905030940b074410b92a5034000c840d040078 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 743371573 1250 743370323 743370347
    0x70506130b0705100513030806061603120e010e010509160812071e2a061d0418052b1d13111908010b04090f090807030309060b0907 58
    0x442641c03030b12041c0c5410760401d1342c041e0360090f030507103440b0400c0300702100f901108090310b00a860780c5c40103482d41000c2c01124031422041c869401100c00720b02000a2090100c192281154000000c4500c0074070055070940f10003c1c1c28a40d40d80d16074061121040c401c1c0000703000b039640352050080c800c0c54050621340398280c4581c04041610040303964028400c110b00591104400c90240401c0003c551030b00c01407003007060000f11034175142041b900e0065082101803a0507a42c00c1d4441000341441140d0840e5000750380000540c200d6214000244604411a001c2c1c156074429000b42407840300000007117503882c40d441c0c4442688065030004902690300a172640d61000300300b407070040202041e540400c1c1c1d081403130741f52403c5441c40c000806829880070300250100040301102004a540700c007a00301c61041e0280544c00c24000c00704800c206032601c80d8800ca601c02000b030004544110740c1d840d08290398118810a4010030f03141d80c011801c02800b80700341c0c580b0400440c3d640c0322900306068000d107c695045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 743372823 1250 743371573 743371589
    0x18030304060f030c170a020703020d181205070506030405061603060e0c090a0312020309010e0f0121060b120106030c020d020705010c050102090a030f0212010603051504081c02040807050613 83
    0x2440c84c0080f440703422026405400300c0c048a000d410407949400007507000450650042c0900c901c00800240b244100c40304084aa0007004c80042c00c03e1b041c6d035412105580103c540e8421508000b9490711010081c1d446103000d070001d01003600c3d020752003401d2090719190100070985408000c0c85628410f086e400c0d00504440c418a4943c058107010800b10b03c0300d900050b02c0c1828000220b00c006900000400c00903002780c0e1060107460070801407080d143e221090540c04244458007042d0105201d402c44030b407800c011040442c40b20b0f600c12a000c0f01ea8400c0320f0000d1f04c00c180740014091540c160040041902c8184000c1c511114075540003074950400d4001c0d581001985420700c1c007400025019160b04003c01403c03400a03c3e640e15218a2000b10200124040c00e0011548041144103125610403a41c01101901901035040502d5001041c01001100d00e400c040c041c04c8000a8140e0083c20344940300e41c401a5160b0811007020318040042d4041481010b0810040a402400e440110112a048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 743374073 1250 743372823 743372831
    0xa06020c1f0204080709050f070f120509060708070804050606010e19090203040b13080711010302070f050601030203070801020405060f0c0a0222180b15041e0218030304060f03 77
    0x10803200c0c0c00c101041c0741d081200d02002003003010611040d03005108031481c6a0840300207558407103030042590740131a07140c0f20080540c0c00240c503840c061400f044482c1240d01e40b151070b0180d8001da0108442c000e41d00b420309c6601072030400c460300303400000b00344e0094100c0c18a49034500d016520315584420080001e070400070135170030b4940c040c0c8072410709450064085401c0040c4640b5180548001e40040f5800d54401c020040440c0801540c00303810041c0f030380c03c441d00a28124503074a1720010b605028130958101030b420003100c0301040380c0100f0707071442c18403410240c03e15514500405282c10600d800114869104000c10001580c1d07043c00c9500c400070940c140b5071904403c2903120705054016030301039080070030400c56583c040341030845072690072075080f42082101c59103034044000c7c04009074010001c00c1a01301044081d00c0748400c001c1c05000090011400050001189009184030800044403a4000c110041c107000071041c1c5a2412a040d0f00035802e041c50640010013003440c54030000c05050340c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 743375323 1250 743374073 743374087
    0x501061103180604080a050c10090f0605030408070f050a030305161d040906061e0603150e090f10021803150103030507210e010210060609051003021c02040e13050a0602 74
    0xb03d07801e0b01c0051144100f1750b00303282c410342065a02e901e8100005442201a801154001402440d254041c0d41c06005406200380c1800c905452951014000b529900801d2000c80c000407550320800f0300892103a400f40164402a02c0c0203420340344081c0480c4039400050050f580115480a0700700040c0920082c00364055410101260041002100c06810141001750105400311550810000490b092681000d125076489003101207512080109144e45103d070700800c004458004002d4109200c1d8081c3e80019602c0e400d6175141643c01000d92801503004108507071440704c204085030000200b0f901030440080050360010908105000040502c08042104001d01c0781c13410101d020100e0310903201069040701c1d0350241800c40783d01d03410b90061080c0d40400d0b021580c1e5000e05030840c0c0c5640c58203107119041c5000c00c034807100c078502034104043d42071040310f2903040d090200c1c4141049074900165940c0c1805000781051100920100e001054001d6160000d540000c40c072840c503410407401078840c91 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 743376573 1250 743375323 743375329
    0x5010f140d1806021602100801060504060e013605030a0b04020409051e060105040c031a040e0309090406020d0b0a1203050a09081f1802010504090c140409060603050106110318 77
    0x100b02c500c050159840071406108129500c0c2200c08010300844900503d050341d54022500707403d02340038880c0011002e00040012030302a4820b5090000b0504003960806040c6080700d485031261158914040d0701524120b87c40c801e0440c1c418040d0605401a015912141e20399440420001e08001d0199589140340c40074454144101d00b148012846410001022901001c0e5a28420300801c0e01c241d1500141d007141034001d01c18010645400e4503081c40c481840010400140440c101b020140e00080080d000e50340c2d9100250f6108034420040180c4940d0981480300442d42084c20060140c80307100002d000120341034a080075070342d03490701d402a92035030700c0302c070850303104116520400051080380788525420480c060040c10344815941c040040410360301d04135221401004000e0301094041205104060031030f000310216541905150710030f4030024001d0b650b0356005a0018003615504d40341400010740c18084c00b401400c89243c14100c0560b003070069903c81c42440c070201c064941039500002561 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 743377823 1250 743376573 743376611
    0x8070f1e080d050403020f100e01111609060816061706180a140a060506070b0a2d0e0703032703062405060a08180307061505010f140d 59
    0x120094034800d020401c400f030020781180c08202d10031130004404009070308202a000788901031603510200c42034480001520340c04c444104502203400740c440d4840d040c0c2da080704200028501110000f0b990740c0b401d4412414104a0b00e41180c0e60004110104922075016010014440400100c80500d4945000141000b62584044a061281c40f0700300b0142d041aa070040c4100080a440c41c94581d841c81110740c2154114006e041e4072000030301029020840e0b08140d0303a444a600740740050341325801c1003030364083300150400d1040c0901243d103e01d200360b558060003c00c860741f40001c03c41c483c110707540640780440f600b01c0c0703403041d04a10780141a00180c0346030b408001d581010701049001c864149407d16240c14504c0051410082440001e0604013441100c6501403180e4440425403140310354240b03c040c0c2c0401581c0a0301c410300a070004680e0912500e80316000c0c0c440c008040314035000000d8480703411580204140400001c49400100c807441c2141c3c07414020748000260101c034604074480304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 743379073 1250 743377823 743377829
    0x31305090718030b2a180111070e060a06020d0c0f030210090602091203040e2a0f04090e0105090c040c02190c0e06091009321008070f1e 60
    0x440800c2e00004107201850103020300034800120b40c081151401c440c1800729080ba03400c1a8030000040141500b410b940c03803002c2c0703c004814940f207985607115501c1a403400d406604520504100041809a1031411011070401410240003900d6102c144200143c42e400c00301d07001034142918100018101842030004e803610320201101080748a4246c00d08034001d4000490240c001c0001c0074512005240010542e4210350907200412459a5074884001070f1955a00c0c07046652015160340d29060f00000b40a4685607440c5440346844510749005d40042c4e0b0310346ca000001692514003445024000402c8c0b503400710100340c4010501c418900c00c100d241a841081c3c4081031442c00c0c5a003401c025041c41d07248201c890b0041f00480c1c6032200c2d010489070450641e014a04548a10010400400250004d4281d52801d60303400c4101c180b6542c1078203101b2030a02d5003d0210720100100040c2c50541e4054501800c0160000d0003100c0c02c150034a0f9440e41140145201c8002180c2c90031142d070414039150010f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 743380323 1250 743379073 743379107
    0x705030403200601080c0616080d06051e18070c06110409110705060c030f0f2802130b0313150204050a15022b0e1216050307080313050907 61
    0x1500e07102d440e1504020b010b1141c980c080c0450700c0341603140c03901c15070324450940b007246074841e00c45541d146c0013076000e14070340d40d55a81ca980c4000350956904e1100d0442d642c66101d0410085500300400c83d48944040070200c824030f80b5400d101031280c1c40103c0c50341e0390f540800c0010301c4e0242c0d0040e01e40c0341c0c083e503800f91401c1801c00328004030030070202d0080c100c40e070b01c1502122295158010110b810f03010071141071210400c2440003850b015081a005034001e4030070100e2001e6458600c806d59444c81400c03580c41c50f503075000112020500301103010000203001300e41d41d40341181030405100303048040010001c0c0008090341482c5d80b42000d00d42c1110020100100b0340030030207a0f036060007424040b401d58820003600030b0341843c010f841032210320380500d0040050780981549210906035000d00e03040001540082032100719004484e410031900b48040030300c480076012289400201351500a8603000300c41d00e82c009108034848240500c2955051380c80840344040c0f01d50329203204840184880d805048 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 743381573 1250 743380323 743380367
    0x110a0b03041b0f14090a020a0c08130807030303240501020c01050a1b1a0a0c020312090c220c1107030f02190315060501030b010206040615080102030907050f0a0602060705030403 78
    0x405480020300115032603016208200d45d5900e480d0103000301c1c068180e070240411140c8034031800081c221801010208902000c511940d0b480d04103c1c0d2511a0680044001c030342c0e2410804080762032101690a030038482c0200048071420040000c1d01c40d908403083c141406000300b01d02a1050003482e41d842e1100d1000c0700000c005549041c01a0b80d1040030842050030030450b00810900c50940c01940d41420a0f50011480c00c5010b018242c9071442c028501515070081c42c4a10f40039640702501d103200340c0b103410380d0301c11b021617100e004a00301c03401040c100003880340080750401b401c0000b0614400700c981104101a0742603032400402c4c5442c64074200311b0640f0394840b40c04020012011020700d02d00100d52000c0001c10f80300d80040d4116620703010a2400342c1d00600000e000203005421191302d460185103021401956140b80301d00b6600195110800b682103800140301509080011407400c0e00c0c12074200f5219440c185010751102000fa01c140c041060010019050502403506e0f20403070403000103c50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 743382823 1250 743381573 743381579
    0x61912140412030b030a0305030106120e0a030c020114070c1205030f030c0409140f18010209220f0b090c070302010209060a02060601080901150e09070e13110a0b03041b0f 75
    0x840442c2c0944a0300021914050501c500c070300300082d40c07201c0c940e4940c1300e803403460342480380c1a10641c3c3c050301c480001548401640100100502c940400140309403070301d401d07421070b0b0f01c0098603411044480d1000588140600e0300807403c181034410441c1d413580c500c1c040d09211070070020701f03510036124820540c690010600c24002d00c0d500050044600c071682c10083d40040c0f81d25a4403040c0c040e9001007000110a01040640c141e0481d21680a921040014505500400401c0c0c040d40c4220031202a0300091030440c1d1a2440360040500781d8641031000c0004800020000c1ea2111002e88074612030940031644104150003541101d200000040880d5203e0f031100800079600c070002c407001800500d01c00c0115884440c140683c520784480050540c1c0564107200422a140200800700360103481503200c00100725044c202420b00030303a14242030040442580c24a01824a0b142c01d590f070145050303150130403160403072000b50b0b500306070706c42118110a0109481440f140580d90091310303050281e01000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 743384073 1250 743382823 743382833
    0x412060b03010c1d010914090a0e0706050c0712020d030c1b090902120a0203100903020c0a080d090605070b0402010804080c1204050315061804020a030506010906140619121404 77
    0x4c00703029143c414544015102040c0110ba2820561140250000b034401075503903146031100384980d0010a402000442c0400d80d841e4602d080d916a001c80040742002400710600d81c810300912004d45036845204243c1d0b240759020580319400d004001e0100642d030704545082028042a0560103840031072080341c003607102c0840c10300901e2100d0080384128a00310300042d072542c2c0485d0981f0815002405062007006018800000e04004001201140034440f04103846035908a88075014050550042004c0c0241c52805007080d5800c0c2c202005102040c02504000b5100c292aa644960b080c038000000c2c3e1200d240405c40c502546801c0359140c007a1001d250002d500940182c400c03a0700403001c5542120a9042742d8101d100300b903c065411441c2c07000125a85240e402446e6080340c40982404074484d500d450341e500305602a0440101c05880d51001c204901b071051401031180000c40c4c05034a0500c0100c11044102002d0017044d05011400e00d4014042d100744d40121295642d2500340f4020381b6142c500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 743385323 1250 743384073 743384087
    0x30c010606050d0b0904020d060506180a06080c15042646060b01051c05060a050603010b030a0902150a171501081906030f050a0501110306060412060b03010c 69
    0x3d0f0110380380c64040704c50442c3c60201800c0e80034a4011300100c0540c1e6581d2210f4002c1c0c0001040c5a41007209004140c2e02d02022507404c6202c1e116040340007954508200849081801402100384645a42c0030354840c89012a070480d801c0b61150300c6e640c10402d4070b800d103c641001124804040d1030168050000014281c104120f04003000b0708005003415180c00d01c629401e23210401c52031582140000e184002444980c0181e40c2c1580505000d4200b081030f0202c8004000c0d0140d02c034a1080d240c00500c4500e00f01120f0700000f401c0115411410741d03041a403144520b00000b4840c10343c1b40e80b5030780c0c1e00b4150346510a5480d02100c2c01d0341d07e2039a40f61900406012281103211034a64109000c001629581042c006038801241c142d6031075030075480324891103101503507410503400c0c225174a903400400258101a500602e134440c030058150000c160404500f111411b842d0404140401c1040140c2c41e51600121402d44400340b13004241141c45040c075000402070000010340541c42c0000400f90f454121031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 743386573 1250 743385323 743385337
    0x618050604090c0b13060f020d030e15011e1a030a23070f0813120507030504051009031109060901060f0201150e0405210702012a060507030609051302010809030c01060605 75
    0x6000100e0941d114405c41d07e1003040b0711001d0044e0891404480114800d402504540d800c0f41300711500403201d0295410b50420aa012082c00c0c103d0555160b055074200c51688010f0204000603442c2c0e09050701004c1a334032000741421045542d401200c42148640042101858441644a210303032400f08400350144101035400030105e008640000c5010340b8680341c191000da4032106420703000046880c2601d41c0d4000100440900105002c0410644ca4910000d283c440d01c42c0d440504203031a42c2408050006081100c1f0300411000080103495114041e07094112440e52070548070050710070604900521402005a01001d54880c00040f00805403e0b4240200e000701c09640c0702c441d15210300100680c0c090311143c4200c4062000c0c90256000f010300743c900110440c1015180f480341520410803d44c104000c0f40c074140c0d11414001c5081c0e15104100c00f900c0046820820390501e220340382405d056070540281084524800246510000d10603298083e400400034041152503003406002500520707 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 743387823 1250 743386573 743386597
    0x1e13090818030303090a0803130615030201171005120115120c0503030c100f0b0d05010603060e030a0509060c07050901080a032d030903030b0d030302030f0a0618050604090c0b 77
    0x1000c1c0e1000b403901104890085041c0700081400d00c00555035441e15802c014003003407a6011700d52000d808140e6a00901e1a920950304442000c0e905510003d4002d1030380b11485600b0400d40c004001030003402c0c83c0c0c0d19040e5001250b9030340400b0034254006024001c044a03164550b8850b12002484a2009440118803441400c004e84501d894000b416924051030500c2002540111040c0c0c001400552085020380180b00f00410124056404901c07030200603d0300722410380d500d90040040c40740c188140804421000003070f47c6130203480c503001071090107050a920701c07441d40040c000349a6502000300c4001440c02514402c1d880d039541000540f907040aa40580210b442d80140e0403100d80040140b038404583c107010702086401040c81100281003400d011030905a0301c0e651007919981d028580c0078010f22030350b400350b40d0340b400700d00c8143d0000000d06001e0240f070422034140411080d20130851040f0080c210005080d680b02d20005010b0311041354090310310780608e0400304001c0f29050040070b034040d40e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 743389073 1250 743387823 743387857
    0x60305060a0c03050907090930031d030702042c0a200d11010c1b03020a3807060603032a02030309040e0f0d0201020a1b021e130908 58
    0x2004003035040e071300b0850307990800b90840311081c4069141944440c400e1402602e428020b0702040104405811610468103c2d400c01e5100760a2200d0781405002c100442c04080080211544043da40d56800340b000b00030303c50750712a481408082502d03c4405200c00d080b50381910700c2c04c1922082c0307445103401c0e04196520103610a00c84154915281440502034025003007141c1d400042d101c80d00480c144200032410400200f014101107204081c44084001800d0b0607800001c0c5544108500011142d002032505c0c05811503480b41d182741441822140352806541c6a1b05001c450750346d9280c0d105500009128034545130300407086c5035100c4414405082e180400281752503440e010710130200040c03d13009525070b0040202c2d02184c10290800000311a4590849410341207000880d0700309944002c0c1d030300040c0e50204406002d542d01607400201c88240c000c241c5018401c54001c116802141c0e070350f003081094014100c0c651500e03030910206501c000c1510030041000981b0701500b66500411522130540d211b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 743390323 1250 743389073 743389091
    0x90b070c02180a0213031b1d0106050307050712030902010e1c03030e0c0301051603061a09060729090132040201180303230328060504060305060a 64
    0x4003009455990000d0030203005002c107070042000440010014094941c0910403d0f05400d04034101c0c8000e103105590b5640c004082c0440c521062200d82d2000701741d4201c040742116205603d40049041d5180380ca4641e549646141046d149403184200080801c2e850340d0a5204295140d800514140e100343da0711462009040d00300000741560715041440b00840c29201400640641d201c540c0c01c18403001540c020318070981c00070342111001c5440382000301c0c0c50590120f41e00c0e418854100a002001c40b490383c000130900000207180501c9202038041d040001c0c1e0a014450001c107410401850301e803080b581090142164140c020041d00c0c04c04441d0f0230028071000240d00241c2c43c4044082510704160600401e01544051a0015009034140303c0c0684c0c524203d00032142070100998040d03180e400d010300c4c60343d280050450b490050b0201c000d0f014014445000d10000007c3e0b05d102d8504003401c0340c8a444a00c003002048070342d000e240e105d4640007001040040104c0c6003882405818000c20040348 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 743391573 1250 743390323 743390327
    0x7020706080c042301030f0f020c0c0603071704060204030b0c0702150a1b1502040e0f0a09080a050a090e1501030b030c0916021c17070c05060106030f090213090b07 72
    0xc1c500444141540000c0e181130910321403004000000414940800c9600740b4640302401c41d6079445040d22807030b40004151002c28404c0014240c00c0d0340c20f56406145140c4440020107803036001d004141040100c001103004d10800e030701a1030146400045c0c0350218241807850700c3c00c95026840482c01240180320301e15800c0720ba0b0342a01c0c1b0141e1a5100c44d555500d80c00c2d0030a0803030300006d03000c440200070001c1c50a520036491001c0c1000e8044c608010155045c00c1c0400c0340b030500300400c045049810300704000f00041551041e100951000c0c1052510740c541340006403006045a004010400040030030020312102840010a201900782c808101009441040c9034440c8121039405810001d000c000c60f000040800501510244c107205885c0b01071400324070000e07011840414440080d038075032141015040140e02c6a6001070960030f126002c3c12141e07a03488e0310b8850510485d0140341c0d07521150004507100e9005a0420360380200401c0200407082c405000401080784151448403500f00001c000303034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 743392823 1250 743391573 743391577
    0x4020d03110a0c0e012405030c070206040b0408010902180919030c05010e03091e100e1314060a060512040813030507080303070806100903022704060501081b010503040b1e07020706080c 81
    0x1600c1d60b07501807949d40d401100c46001e074042c081c22600b0070310030800001c114244c1d0f4041c00c05030071880c001140f0400e0a00401a007a40c00000791403090040e41c0501c400c0c00400110100c2d00702c80c03100e824076030504a003070954000c60000e43c0035055500b8051005d11070040070000b8004803a040b182d5072030034246d8408226882c101502000d80280c440c040e48601c0c0c0d1300070041199804402824132a84070710888050741552069100c40014403000414800c0a1a00c2d2150304040c16252030b12500304100d15001189030403018002401c040e00c0023820b00d40342c204800f4504084c40d082030448011355625a070240d502d82c0b0464454000074290000b00b102454404007108020006940e4605d8040c15a000c00248110404140801030384210404003640000c85000c0d00c00e5015090014132585801c890701d0400d20031004801700c0d00301602095006a0700328094030b8115401480c225600e0341c03403a540315065040c1403c801d06c07a98086003040b448550006220b0141e825a6440140a86940307031060054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 743394073 1250 743392823 743392889
    0x3063301020c1c05030a0503010f12021e060408030406120509071a130e0702150603012906070618050c09010b0f030712023004020d03110a0c0e01 64
    0x41c0c00042440c0040d140000f44003401000e2105002c80c401180d684a51440e0b0180700740c40702050011004210a0080412000041405071555a00061554002054400381d8601d90600c0c0a590b4410302507a00e03000300b954050050602204d41c1c650b00d0302c002031304408035180f4a00d00036003030500050080701d000c2008400c079102c1c00305820301003440c80c05503c516001034a45900d903000348500040d21070425801c40340541c000787c018003007076889120725a00b0880c004140d1802030f070601c2c0701d65294070040050551a030b641421407941030031045000820f82d206513031024100c03505010782a55140c100742000001c2c1842841100d5010500100303001d00c50300d0134407450003144011310209000ca28000000c550011f004c0c80e040a40c4100d000c00002240c00501110070140603840e848403001303415110084001c1403c2c0000716a034900745e4001000303150039040c000d0030090030440113494003801b042000031040d486406064965210103200302c1d000d90900c21500002c1c0702c5000381b80d001694210349044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 743395323 1250 743394073 743394077
    0x9010f031713061202130b0318060108070b090a03050312180705010206060607060b0907030f0c05090f0d2f10030513061104090504081801050a021908070203063301 72
    0x1036240c40c00c241c59407000021306103156174007000004011184160b660001c5c1511040817030700c0e4244840900810051b100c91040355a2003040144421100015048204c410f40c0d90b81c00d07601c2c03600380041f600081450303100030000d11020400c807601c50301c0d80810740e1041c0c00a0701158004524260761b03030768500d90340c403413a4096001440801d00d5410890300070302460f4040c0350f0110b90708c6003a44c08118000d130201d0380030000030341c3d5504451a808050103030201075105460325904051070800000c807d0018448540d1080c6078001110042011019025000d1100c0d01040f0702005c052403203200d034080c507600d0500e00c030f41c01040d0b680f1004c5000e40b1a01c0c1c0240c0a1010304469640203a8650004085c21000740e8a056424400007d24240c6405803d110f05c0c4a03505864a805215242540b1401c0c1400558148042031104003241a800200d42c0303210380700840c031601d02c0c0b4160304010b6603d00c0f6801029406014000030031400c600d81400c02130008200404188100012008902c4c49100412190340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 743396573 1250 743395323 743395357
    0x10170618150f2503090b0123060c070b1602040b0105030103080306090705360901030506040305030604110403030e03070504021606050c190f080f040c05011d09010f0317 74
    0x1801585902c4a5030f020780034030703414040200f5004000006030100600e10002913150400c074000c001c000c6800754014200b920114200b010040000100e111400480902400b40400c804003141010030a090007050740e00c1c04c881d50748200a070046242100441e09070701880c2050b202c00c800d544240c1c102e80c100c0703402100441c110b45504080018201014205c0400c0040c01e10031034080004001041c203070480b0640070210314803102d645a840401410540c1c5201d10740d2040100040350000c40d40355030156151174050381e03a5442070001002051b114200100801c0701040100806420501c03c507081e5500710110f40da2070382e580c000c0005031300c1083d0300c6205c84400f080401c400101d035500441d400c20504e03410181003200e0101d0b500840c081c10780385900000c0e0410088101140c000d4080380c0c0010b02d09460310490f243c251500106122144500c9040240c003015100500000c060404903100d001841074240d035a4030303104412149588d000940e00180c1881d1547c088114034801c40300d00c051003608441c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 743397823 1250 743396573 743396581
    0xc0e010b091002011512050c040c020a1b0329060d0c050d1e050705090a05270312010e180f060703020f040b0316030c0e0f091017061815 60
    0x22800800da10b64040541d9203822080c54040342c0c034185c1074060609012051089911030800601e0800f0045040340960b25110708018182d5000c50040c1c01c1541002c100c010085404000301c10070059070784050b00f042c6081c0d6481058202a040300314a569892454071625140d140c01c102d4180c00841008000c80b200400c10046070400341c0d9201c0b4201c1c020801c2081042c609240c182034040000000c0b00c254110030800c1c001443c0c0010420f80002841c8010406880c25803030501076010690b21542c2a803180c100c8a0304805000c0048904031460320422030302c5560355142c1d21501e82000d03141c8030b680c08504042204a00800212071802042034401040a912070101c150020f50000480042c0382004200214200b0030400081d40107c40202c0c20350048183d109000f003c586c60880810100040707800040d10320b5036410900d401e12401100c00c44c0f09503d450320421343d1603d80798020952070380d141648941e03441021031701522aa0400ba0f03456111040200d03403e40343c07400d10310101c100420010110b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 743399073 1250 743397823 743397829
    0xc01020715020f060c0d05070f090e180a060b0306070e09011707080304170d1b06111c0e0d0206090d030504060b0406030b0a0605040605060901050d14130c0e010b09 72
    0x181100c0029030054071a000b410f02906030800d04102c4041d01c0c12900003507030060700080f52282c2503002540d4602260407208554000341048140c0c851f001c0c506000201150240d0034059000f20a980b10b28115045a40c1d60300c1c1c52006007601d000c01c24031038007407040055116800392125500d00c5400600607a503580c2031411906985828101640700d40c130400401166400080009001810b101c4a00c0c180350900c0440300761810312850555010401e000d10105052202c0030b419800403940503202085030b04503008586810b0040c43d41841e0002c2c203010b4410481c5141d0750011000c00c0c9441d09849000d44035801c1030780c2d110010348000b285e9034424240341c0d6001c0d00c664007403508944100c80200300034030000005001e641890300190340d405441014000b03801c910b4840c0d41c004020503581032100c1031402002801c503024103040c15041c041c1c0040c01c4582d80f0040d82c0321034a080c424880b04015410003541114450281c5c40382240d100d40200030209007502800e405a040b602070700318691601c0440818 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 743400323 1250 743399073 743399099
    0x18010c09060f0309060e0f100b010c030e060702030a0204110a02010b0402071109130204060605190306030503030a0b010c05011805120c0601050111010f05070509011b08040330080709080c010207 85
    0x2007030b80c01c4c1b0359502042e107405800380000303040500000010300c10945000c0110b130444418006e036034184a00d140d10000029044030707003040300140884000d512010343d80046070401c244104001d41c1309280100031035a928113103008d4010040540e000b00000e800d240144401c900c0355540180042c520703603d001d5028545010802c4d1b004d11781e4070a0445908580c3d0101c0d080c2e41540e000300c408502c0204d15801003a02103042d120b18039000380f4050003101d05d551199078032440054107600c1c00e162a4408241341e43d010314010001c1c1c81d4000002c02c0b22085002c807680b80411080c40480e158052811985640000c8500ba0743c5c641041401030f08090340380c0070040d0384900e0160882001d5541710180300110042d28411148103072607030346406039203466a0000501420f600040c81175030170315207035a40000c0b031000401c0e00c00707480e404600880000e0034503001c08901d551141704a049200180d881800c01035000d100640909200d07200e0324426030301c0351001a00c030b120418002d0b00682c00000c08200003200040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 743401573 1250 743400323 743400341
    0x20d12091509030c0b0405030901260414010902031005090105060a0f0603052e03050f01060308030115020109050303070201060603110c03271207030c091b05070c05060318010c09060f03 81
    0x205404d50000c81e0741d480c82440c0d8115400d4509400100300b84015507041410245c402c0210810f0381c000d510741c4800742415400140025020709a0b0034241d0880c10b509501600e4543e4000341114080741c0185020005004112800310055080c540440d8050601125410540c2c00c28419000c1d5a401c0020490040000070082c28a0803081307500088000c45581e420142c00c03c0c0a030b04544001e0542c00c18900d4000350307000740e0030103a26180017040401c0401d000c0d20305499522500c249151068075040b03001d04544440602940000002c1c00310341e60701580840100c0e46551800d0002e4040486440418041c040c0d0b18542d94004102c514104582503846140641c00c2a108040d00ca1a58011a06032001b82010164a07403003000140144a90711200c135000f0070110805000781c40310018a007800017045030010082c040c01003110000c000b0b60303820140c09400040c003042d881b850003080c0c0030240780066110300e410354038141c07582d1001d900c1400b0304c00c00d5440c940c5501e416070302014011401080094 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 743402823 1250 743401573 743401577
    0x6010302070f0602071208070c020d021306061e090b03010506070c08030318010e010e07150210020a2f03091e06040b0a0f03060e06060a1e020d1209150903 68
    0x8001c20008820300c4621080c1e9018440c01600c4199a25180d4410a1643c0c51001400151810404480d17448920030a5040c0e040d20101481981c910104c1c0c102d1101e02c8421110302c1c1005404a082a400307242c90350142c02e0750318a089030a096603800c0d943c3c44138a003d03100d002c1c1d000308011711450801ca4001c210340d620460025403226030b40c0381d200d0306503001a58203000c01d8540f40c904101002090150b00b000c002d1040c020000c0b0070090740d1603940d808035489071001c0c010148107200302d980c4c0244a0464011110b00302559078041200c002854250049107416803440030b0b142c003020344076104144245100c070b507500451a0040702420000603540010a40c1141920381140440c1c0b0340b80e2a010304001c00c202a8200e880b0070740840080c0400c0f1b88840c0003c02c0500e400c20401046e0104001190403c0068a00c10754507460380d5000c444140f1001d01819240c002c000e07801c0000c0d540000e0b0358041205503560200a01d0100c5081c40503210f03a500090419a4448012402580340307074040e40d0554070034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 743404073 1250 743402823 743402827
    0xd0b01020a0203070902031603020c07090e19060605012d05031b0c01020901080112110d11030a030237290109050105030d030507050319200c0f0d090e06010302 70
    0xc0e9001901d840b40980204100740c6e0084103005004400c01e070440b5030001d1506065003011610808195903001611540c0312032600c4840c4501060130902000c4190f4064801000e40c2485a0034140d000e483c0364070070f4a0001c2e42400790f11380380100891049445c2c4904249601d40030782c01d2501140c8540014107141c03c0c110b4a24142085041010700801d0f030f8640308000035803540650300003d8400f0300143c0c003a552890800724240002409140e002c1110071003158610440c15050030120011541294103a42510030a4507500070b15800143c910180140282000744200420005080d801403924900c030300c43c2d00003001034000520596000341e00f02007080344522200d078410000f80d11038400781d0025440317980d244018445420f050003100c44403512420244440d0900980c001c00a11009001d107082084100c4036450003600b0380c00c244243c4400c110b4030385441400d0342c80c40341c00e60f0062150004c544195681415188800b20b68821448210b44a004100d8607017540d07407a0024009180504055003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 743405323 1250 743404073 743404093
    0x80c0904210917070503010b030d0507034a100906210c09030302150402100309050f1c020f0609060c1803031305040f060e011202040207080309061b0901050d0b0102 72
    0x7000d5010040342000f0002840c880d031030304091501b141d45402d0703024001c0e0000c510b61002203070000200c949941d858034121010f0305022080e001c000808041d030103100490745842c02c80300710303040c2540c0b0f103100000031440b0709103e1000200700c849240c000004012503241001005031a00400c000041055100e0b011903086c040c0c0e031299030072180403104031404607407180000d0083c1641000030b11108400040ca60300e182c1015000a028520414034a070209030312200f11408010081c0110111400c13408200d9000c0405000031034031058101c1008001446a8110011001d00000d400760003181100c0280c045919030030555034056104e070468100140118003204130b00c0d1030401c014012826172260403030070b090074007080100303480c2030005040c1a203003011401d0280130340248415044800d15583c03a028060039201040180c06210710280400ca804007c0040c01100032840d14400c0c21459408018009060010790b924080d40c101d20740010001e0020300310031103507907000c00060395050044410113a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 743406573 1250 743405323 743405339
    0xc05010c1118040c08010e073302011d0a0f060b062b060e070e060c2112070521040c0b0a110c01030e031206042004080c09042109 57
    0x4282e030140400c80d154a4200010300078650403442c0070f4040f05000313003c03c400d0780d0b142c01e03503030130980c01100400710703413401e05540c92803480010590a1002c1038142544041d4508041d00a224440640304440c0c1c010b18500203000b000b159800d1681c2d8021410005410151607490007041c1c215032164202c42d08202c405180c44400004080d55503100074065911010f61100c081610700a40c004864406041c052051158200d04c5e0404034042c29104242c440c0c1ca00a001890500c0340c0388031000130901c0c072412580c0054500001c000d904200f40e1080c02986480508446920820b183d5180d80c3c03d407420036003c49a80190380c9904240200c10703081c20581c541ca035150440d800701c00920081408500d02c04042c00c001e00c242505d08038242000c01101103d0003985d0b48a20440c4a21101c002901c40000e120303030344030307030048404031100c142c00304030703540c19060101403580540654842031240380d5440002d171901c0c002c850302c66039100001524614a81002409894000c500310341441408500462406 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 743407823 1250 743406573 743406589
    0x309020d0b07020c010f0f0c02060d060b07050f03130603090510060902030a05160905091905040f061103060a120507170c04050907031a091c030e06130c05010c11 71
    0xd801803004a90509020781d02030f10703100ca41080c2038140002821101d05031074020000d500d000d074443c14000c030740018900c0020354500c6800200c1001c18a05070740490304d00041001340c0b040700d2080c01107550f203412940c40316139280150300c6200752200e0200c01c00d0060324401d8010002d414032842c01c442c1c0d0814250080001c1d01d21a40040007015404010013291001c02d0149640011443c64800d8281c202042d00401890860081a00030340c03120001c40c4c104c038024980401a400d004104000d00c0c207081c603110300714180c2004240e501904041c9040d0181c04c40c241200d0242d03500910040d0060f14040c01d1040d070512042c0140d07000d00602c400061030021103880100c9840700c40010700a10011401000704545000d803807280c45078800c00090002500500244020800b080b408107066610325803074500d00103944454103c8419120345410010b40c264025440003800300c000d940541d516284014a41c002107003002d021000340170710411065000e8854014038a024182c0e6803a91002d442c0426800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 743409073 1250 743407823 743407849
    0x80703051221070c06180308010b0a11160807081c0e0d0204050406051f050d020d0212100911010f0c031b0b0c03010303140705031e0903100f050a020901080109020a030902 75
    0x106140000c507408000311403040d044007241440d040e200c6d10f02c00351402405030f0780500481070003c1c00018000c0701d640c040c0003004100440380c1d0403201c8842510500c1d41100f0228400c20501e88550f0070f002c42c2040c800319208408000c50301c1d100c45504100300086a012040448031a000b0410f41c10b0b00340940c071640151071040d4005c4102007400e040c06480d241c8403183c0e1500c648551152100107004940e6086000052142c04403524420a90340d4000208404004c241e01802c910036000c000045020903003102100d98000d005a01003803042c5801900c4a285404015000402c41800d076070010b0702171380080c2c400140d108803c18010031150f80d1414000020f81c1c80402c9140084010004c065011002006820744d802509040c41d155907280c650341c0c021014096150f007400014a40b015582d0b0382a5600000e0003001c8520140c0b6800442000b07040c020300e9240102e0070100000d0700f2008500807100d8104040c1e50300300e0b0fa071380f030022650b00a4000000321002c260300c4200c41d80169aa4001e820a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 743410323 1250 743409073 743409077
    0x1c031b0f0b070c02130209180603030909040f0b01050418170c0d02070509060a03080f071a0f040218132004060605040602280305090f03030408011508070305122107 72
    0x1d80c1064010405c51009928045030828010031041540c0d032103100ca02c018110101307805030b410b510350344002402c5002c1c1065054100a0030010842800079410050704224012a05003a140e42c0b20403d00050300c0f00c3c418011051a481d4000c01c00107140309064550b986803140d10a400c0855403040241014001880d0400507403160b41e01b4030441c41e01010280c2c003c4003c8ad00c54840c649950307074000c0c4500410014908cc5030010a82d181440403409074025134207080e208208451034079610700d419582064400b6401868940401a0481d80c44c2035820300500c0021403c502d20506a9038a0402c0f481c56003140d51400009100f005607500c039401903001406441d121030707440e01d0400500034504100c00030b40125641c1440306040310103101820074104a600751511946d5040c4401c0442c049842d905c40311a0944400140007810510650080854034401540c0c0400540e4840a103991405640000780550300550f40180f043c480560040c50081d4010344020b5100407a2103000c1c0120380c0403504100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 743411573 1250 743410323 743410337
    0x705120c0414092a0310050115030506090a0b180709180b1305151203040501021212060f0121021b01181b05030304030c03021c031b0f0b07 61
    0x11910303090092152814024096040e6480c00076007003541c1d404c0e10786a068940c0d0340032800c1007500380d010f0025461098080c0464120002075010f220003000240318011000c8511580d44055502c030380200c5001e6080288440d00344c2d241d00c3d041d07100810000540c281d219035148202401c943c0c2c0d01000d07900c08c2299455090000b407810004004510200084004051521290f010550b9607489041c2010842e0840091240e80703440c0c03c131142400e505039686d4482a22643c1c03041c1d03040300000a000303581c400c1e03007561000c0882da516424140180354000004604103800201141800f04d00c1104a5405140000f0900d80d10240da91603580c0c040c9001411a40007e170076001040103140012070a05500003c00c0312011715076041846021050000300801c0781a0615245114164986800b0708402010703a581e41d56a86485117010300c030b500c003c82c066542164403010003000501d00003d555003640303407050051030f102c03100d5800c1c81c0321a000300c4cc1114404402d1000c20041494584601e100340c9a0300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 743412823 1250 743411573 743411593
    0x50a02030411010c0b0406050a0605060711040c0f12020a020715020a060506121b04020408190c050402030103080f07030519030c1101020c07380301090e070e070809070512 75
    0x458041500c0418605002c04140c1060008001c51704082e48190003820014a54640103600c001400c103641c07004c1d07409180400d92105200d03030200608080301d42100c00b02308a00d00500305403020803101040d900030031400b00074070b031150107640c0003007411055501c196260f068642a0541207540b03c281b8101c01a401512240d00f0000b00e0304c10640c11840032a02c1c40c4444c1d2a085102d0358070241c50030018000030980c6041d51a0f0340700ca1701602c0151200c07200340c0d100e030b0f02e05070f292a007046503804054400e00078003d00040c4605245c17080341d040c6c940010b2503914052011135201c5407a070100504808112040020000c003114805c00a03070030b03480c15500032800700c1a0369401400b05c0300b00c034100c0503180d1040100b50800a0009841d40c22114000d4040c0024a080c10640380b400b0307250121316000703600404a10301d0b060b440600442c180c40140c102004440407550300185d4600c02e41c007802c0714000421002c01e501c0d6008100303c9500070403640031a015541c88001040742507100ea4100e00391030380050b601c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 743414073 1250 743412823 743412833
    0x13030c0905130b13050a02100201020d050f130206130302060d02040305010506030d080703111605010203010503070f030c030807061b02060105030c01052a0312190e0c090613060306050a020304 84
    0x180da00301c040b10411548460007520f4119040001070462000c11040c1a40101044018008100642c0e0000c000140045140700007034040e50000c40c400c07035050703d01000038000391a0320910358003d04d1105000c082850079603003442071540c40008000310f4080c19040000c01a80d40d1401000441c0032810050b0300c2d61310f50314000782941c02c060803882c4070b80c20024817443d211754404206544000d85140110383c3d6852507885840922992028408000a8204001c103000054005504a84095045074540c55550b0302060031241a40001050000313580c07800c00104008402500702c00340140c2000510700c6031018070a8070f1015000d02c3c4405604054010003d03881c1c148001e10101b002828601d142c0130101e045001c0c02c5140030503040303629104aa0f10360141900f0010303198200b1400e02e1036a003500b84414103901ca0040060002203440c106801446c0b2004041540e4000d181d000c1d2414801d501d47c1c0d410081910040307110074101e01c0e580d40300080404c109008641c01423808e0b490041c0e503414a4145 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 743415323 1250 743414073 743414081
    0xe03130902030f04060f020408060a060302030d050c0307060c03023601031112070c0203070e09191104050a15061d0603070f1b0b0115020f0615010e040213030c09 71
    0x30560144184100402645040f41d00c90340329903c11000244425040d000c030000740074a42041e1024450340701044040300d00b80c4d129100786c074000c0f01104e0722040c24480460b02481004003015154105000c1c110000c4c0054002d81c544114a080140c1420344041580d1601c4601c0d0540fa0f0941d0381c40754048080b621902e0740200000c1080c6814441e02100d402d60150601c81d03200c1c0300c2081002c0b40c00140d8030724843c020300140070394000c0079540c01965450b50f0164030310090b1144022806031501901c0b4910040c1d0390300b046103034008a561051540c1508010003440014110043d143d101c0500c03603036a00c000d065210140c040f0761a4002d42c0085076005988081c0240b80700c90242c2c004205014003c4e2708007400e915000441d15103242e5002e504482d030b5800c0002417800800e003507d00e50003c60780128494a4458403881c646c00c131011164140007132a580d81c000e0354000510384211005040f43d5120340c0310300002d0a005400035141ca00e00140d528489101d0341d20035145525510418008200a402 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 743416573 1250 743415323 743415329
    0x150406021e0310050d0501180506040605070323040c0905180120040b160503040b190305060108060f04230709060c03020d200708061008070e04030c150e0313 69
    0x12450b086150031181032107560818095148903118010b50101040025006090b19400841014007400ea072480c01039914241620100c44141c185800124858440d02c15111680b07854415201d0b45410031220150400020700103a681003191440419070800e21b0041902075408002400700d00c00d80d0030b192900710782058035103000001101c00a6007035403c00000751000d480306d0000d00b03036842c64440842e0721200e014800081c4103000c00300d40011650307400d50141080c0c16040101d14110040158214102c0350210f907198049241d80b8081600c5080c00d00b92090038480c06400011001d005190203400c1d007082ca0b91100e8003503200400c000da096408038a0034000d04150034004100303c0b00e40c2c0c000c0c0d213401034407001d4020803a08a183c4c071500c0440540000b00d20107030105585070607440d2210552501011104111940c0f215440040e407143c000400b41d044440b441000d05a584559800720f80c01c442080c0140c1d40303900260f80d020308442491080104034190103004681d240c1e02030a80c0c0004070b601b54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 743417823 1250 743416573 743416627
    0xd0207061d0918030705010f0c0f08090d050306010c0f0c081608070b030618090114090c0117060d0c080d080a0b0102032b14010e010b250515040602 65
    0x201280c4095112040e10b641c200303407007010070300c0c1d90028440360703e00d1070203640c601811030340c00e1a40203030000c03515500c95183c44070680c1c2d0360700c0b91540002e0151a000c00507940100e1a03403001524070102c601c240702031600410b0500d842e68031141541c48005504805070f40659400d141d03c0740410801d0804c2194010072032713905038042a01894100c06d82e03100d003550700c200003610000100060b2159116140112426040e0015811a0800e6070020b8002c7c40302c0702000707110703841d18400320310304400004004c0801d48050b99003840b07000d01500c210b110650003404080c1c2147c540080200042c2892145101600e500300c01400005284500181000301c080c20317041845103454150030303051742e000c01199941d10600000032800c402001050038801400c0ba0071510701c17840c1800640503041006101b504881c07030040024111f9880e5804546540705403042c410000820740340d0b50000104011900f000c1c18040c20a0b0b90030450036074441d4844820885040b80c00035030005181080030190011484654080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 743419073 1250 743417823 743417867
    0x50a0e1012051c0207030213050f150a050d0606050a0b21010608040807030c121d03010e070e040501060902072102061659010804080a0309050d020706 66
    0x81c0c03a82a2101010540c00c03074101030a55150f80d82e68003c1020800941c2d001d89070004404191103600001c0c4015109807070000042e0010821241040e40180ca110100806d010b090300c2ca4142040f0318201403010071030390740340c40310000a0b040d0b03070784904000101404104540c1e50b8400181794503401058154018114100d4401805460350101819034001d502c411066940c51503400c09807409a06900014000883c0079a202c0b05e866000820040305140000d8a015050740078040600f0384038240550080d070f61000b00f0412104020079007564000c0c2c001d40000402c152201c080720280e07070201506a68228900301801d00d070310485080f4644414407480600b142e81004c00c084040c02c01c0c40c1c2c5600081204503080c40b8056a00c4900d8044030300d514112103c01407010b0070500d031781940001c902c034411890000300040500455805410038290594808080b40d40d10341d81c0c00341580240c00350000b05070303039003204c00b00217034040004140381201170b0000c04456251070401400d04030144500f222000c42 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 743420323 1250 743419073 743419109
    0x5030a0c0e040f0203010806011d042406032607110f120d05090f060315060307050c01152409090c122d020705030f0717030a0912030e0d03090606050a0e10 68
    0x2020600b24bc0140d446103841c070408055060045c0b40e000c6420002a580345894000001c10180f06820104000c24015a03241c500300485140d41a0003103d001a05000d90a000c1007618500740e14002900b80300104000445207140f0981841c10603510005004140c0020b111303031132460203582d540c07890401107400da45186040d007604822035179400c0301540181400300128008501407410ba508180c42600204801c80018007110303500310f0a071280b0703402001001002e0800c04000310340410120b8480d1148080545403012200c004c141800301c0004008281130144440c0c40d4500802207044070003100003460210090382c490650520b280346004003481005624001200130081e285081c00c1081840d4507a495400c164109604018000401c8000002000140c503e04c1e4041903415004480c041200740c46000144c00312815402100000d0f4440c103400c41041e4400d800066490344181c0001c58034035030b10f601040051501e074204054860303502c0200003c5035441c510181c01040840341150841030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 743421573 1250 743420323 743420369
    0xc1c020f12130f0311010f050d1e180c0b0307021f09061506022107061416030b090c030a0b040c0908011506090302120109080a091508010605030a0c0e040f020301080601 74
    0x2441c03a9255050002102282020600440a580c0d42d00027014051000341041900c0290001e80402c5801c4401d140611102490544c0d10351400802d43c40350004207001d06001ca142e0086c1c200800d4002148610800b030103c0303180100c00c271680b00c500310381c020901f007446143c41c1043d100b8000d03d140c0c0c12a10050b04120041e80000c5118141c4901c0c404008881156074518000b440b4048011f440141060100e0790000f0100c00d00038400e00520f24071842100350240104c054405900502e60300440c244041a1444802c10081d034200b00391400c00100e00d840c50001c02e040d030300c4034a002c4010a41d103a0082000c580c086c080d18049101d1300f043c21425a0410401a20201082c04007034040c40c0302440c0c0e09208d01007503101c4050640c1240d02d00742c40d0342440c4002000c2428600900b040c841c0c5d84080c418a8a0203100301a05944543d250903013540d0307070b809036080100300341500b11040003c0329039100101d4955201e185013000c00a030f8003503a258100b0185918000c01030380711000c2c401c500400007025131 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 743422823 1250 743421573 743421593
    0x60209130603020f010309031e120c020a0b090d0c0605060f1504050315091002090a08070906031205090108070f0c0803010f0e070503090c040c0e06160b0a020c1c020f12130f03 77
    0x8841c4030b410220303004600c03080361880d2b03454141040d294a0300c00c40e030a2040e000a85105440d10810f0501e03020380e11030046e240c07904110108200422200100e4000180307440c0c000d9548040d000c2d150003800020100011409040a040814200000501401030382410b02c4651281e840000b902c40b800d0a2041750150b98400030458151038039404107140c0d07110399800c000100209002c0c401c480245841e280c5950003030103680300c100d41030119134142000403070061003550007509058540d408075a49102069405c04e122003240790420060029180000e920700b0099070281c0a0114081074050424844200792400540401c040c400b05208006192500007800380803143c06079004039040403656015118141c40e171a5582d40b1110108652001031003412440e44803601a1140c241c0382e444062206c02240308116952515810188080680410302042e81d403540c0414812a25201c480d80c00107414070b888202c0e0518030040014051026220351008000941000c00d60281c0700c070310315600c40d9401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 743424073 1250 743422823 743422847
    0x10e090c0a0b13030804060201020903070e0f040308060303090a14100801030c15020705060408011a0406060e04151205070f081203010e2a0a14030c16060209130603020f01030903 78
    0x2d540c00040054000d003428007a0001103078404019901d458840740042d010307410000c0da083c003d104034800042c0c5400c404a03000e000b0707240c88100c402e20307031125102141c10200041441c0e0f01072004200200113503c0d0b466a500040c000a5041d6035006c0710b01c001c00290b048400f040c2410041a40e0052001c9518500e40c07000300c8805d40e2181c2ea1002c40c0c0d01c8280d041c4105031340724940c44000414001940b48064000103c44242c0341554002981140700708001c448903402007200283c010103540c58a401e059008919204a441001407001c0c2d41e0850380c0345481a2000c00c440c0d503005004100301002e84048920060f04d01d12016240c1d000905016003440d000c144501c42c240f21507900419444c03031603815040403c0c008442d071140050705605204002d0f43c0981c2d000b600050001600d01003c940d040c003a41c0c082c0381407001c0c59141461500c03003004044100c96080d101d42e90300300560052581da244252601c40302824000c03940510314010002540400da1b112418141030004190009501503200940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 743425323 1250 743424073 743424089
    0x20315060a02150f090f39090a060302030f0303060603040b0a0b1003051819060507052521270909080309010b0a2412020a08010e090c0a 60
    0x224050703003000b2460400c5031001e48075083d4000c030521481007901a803581c460f82c4000b0403103405520342c0c1c42076607860b44485403803460b030908990030b0a00b0070b65112501450007440c1003001071034400140015003494080e40c0c941c1c1c1c5107556030410803c504052241e0b003101c0f0250005181145405000309003644000ac0004280102150004003060651f0748403000c1042c0c05444250480341c3d020000c0d0003030805039243e486440c609030441003007140c000f8a1064001002c0d01820700b080182d078444000d000c0c090000c2c41803182c10f00040300241120701c110045003e550030281448022420010701c1501c8241c2040002440c16108901c542c0d008084000400a4070000b024030102d140c0e60707544500350a40100e8481400c0081c00c0043c0486c0d04007450240401304001c12106800d58200030003003e8a00c505010384040034494401299454500525440035041030100350043c0354815049900a2402c00003050740d00e0014018082c3c0b03c00300701d52016592000302008140c0c5000294514000d12070220 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 743426573 1250 743425323 743425327
    0x30c030403030f1e090209180703140f1006030309090c1e02100f021b0703021003021e071208060a0506120a0908190e0306040305030c13031e1502031506 67
    0x400f0000350b0f000c1e03034044000036090105030320400035010144c040d801c0d003640703d188404041088102d0580052541e40710400044c03083e00d02c0c650b161000c44401c10380417500c0307010b07102c510003c0e00d0092003030030102058144000384060851401030294481a00845030384c0b4070300000081c149412041221500c90800c800b01040c4408103012807410003021044100070303003080d00d040b00e8142c19030060002481008124420f0068050b40386543d40389d1480080e51080c10f0400c01a1054025070080c01c16164510341c0e0740b115034041c004548030347d01060045682c0210060386844090b03011203400d8100c48101d500c150707458034010002e24a0701803642401c10200e41e0350003103082d000076a0b000382203041d403050050f5110300c110000d800c04403806003190004102a40619005460049081440b07654591101804d58540d41490350b032507003200b01003501c66001c0e00c0000c000314410542120010002c424000d86042d411f10303100910041706001c0c410320b140140148801c81100c000c0b500c80311541958216 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 743427823 1250 743426573 743426591
    0x60501080619030503160507290307090506120a0f0b01020d0509030c0a030b10060c05070324060b0c010c02031303020907090905090106050f06070308010b0d060e090a020f010203030c03040303 84
    0x140c0482c0070741c0010a1484006650750350005030211403091319018001b1340f4903965403642590890403006170400d100040c810126900d07032801001441d00280a841c1000086071114045542d40c0e00c601c83d0015500c4124003001002c3e1982d004420302d10b034400328240030046d12400081d540b16042c48641051010224082040751400c000c40190604000c0c200780110b40e82e400d003128000030a80b03000381ca10b00003d0004c6602e501985503190070396840300c0104485480c644902da8400f505000e07107068540345410301c54030106980180303000b51914030301c10340d80d400c3c603100d41500310b440310342d80e410554005200c98a1100b4240c00c645044903015104410541d0b120041150b00740c0c0b90b81c120311191840c2509103d03c101d815031212043e204140c400c9a04030800f41c04000300c03030051510050005178280e0060050b401104081c2480c03422000d0080f5003284c59164602c40003404491031044c55002c400810b00398600019480d007580c80a002940c0b65090401c48100c0324400204042d043c161200100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 743429073 1250 743427823 743427859
    0x20139030f0b1c03140a0c080901120905150709050a0905060d08040f090b0a0b0a0e0f0429010801062a0f051005101206090203030910050408100605010806 68
    0x502d1010320010035641081200d800000854000d4040580c0011080030728428074554840490303413442d9807915a8160040c0c030b03945a001c07943c884d1000d5810410410350031510b01c9140e00030308110620039800f50010320700d1f500c0001c0c2c5910000301b40d03808000340d100007003100d92181c0410001b500c81c800c1010803540e840e070000c2114450001c4d0b00074100a4001000070302d1940c1182020142c030b44501e0140142c484140030000103400c24068030046071400c115540c003950003942c05604114000e001000310001d40c1000400300c034528040020703c1c0c40a000c4542c6103103807440326216828000d00708081d403541000c00080000c1c004034000c064010507641c0c1c0c20548881c1090200d18190300030828500581c1130310f0500d4890011409103210181000302142aa24080c0c000c1002d59000426410410355144c88100291001000680e01400100322490704c9444941d04150050040d0700e03104d5849107000c6085d80350102c100e0720813140d03501e0003400744a260380c8051040e030024412900301c0c20311080c44400d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 743430323 1250 743429073 743429081
    0x30818122103040515070c0c080703021804051005090d110f0721150c02010513120e01050408010e0309012006131b08101d15130c06020139030f 63
    0x2d8440e06020100f0001e0041d1f03c200c0b010200c51181e00900318080c1e6a80109985412901000307501c040c2c159602c94407510b4100c07055900c1402001107404840d000c03266101103c10070741d05140ca40d0007040c45985415000b4600703d085116030001880004604080b00c0d49640340360180c0001403800301c1c00c820100c0c401425801e1b5030b64001450603010b050810000c1c008007103e030002c03400b550070702c00011160500d80b9a4621059081000282490315154044a440809242007030502c0780070310000c14038840c24415118803911160095035114a003800242283c3c0a2240d08151140300b00614604084045503041d0802015414440440070078030b0a0b051801498000c4003050503640c0001985100001b43c00016888500c030412045400f194074048920749c054540d14158064450307081c2c0c0813944801141e020040c6000840a41c085980383d1144200d250300590060391501302142a00c603002d1000f081601e000da54625004201140b8080a04002d101c200d00b4181c1d208216540e010700c3c1c0e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 743431573 1250 743430323 743430343
    0xf09030415020d03061e03061d01020414090f150d08070f0b040c0f08060610050f040312350402030f0717060a1e0c05040308181221030405 61
    0x80364058508034001e60f607100101c900c2d0000b80c00c20000285826036a0365051601c904058116045802d50701e4643c06403403510611410012203544200c00ba000a1015001502c4440034210880d03000c2b40c100407010001400e2503034a8014102803292501803107084040c1030000b540c11078407540e00c40c10b00d000d540c09042405003441c45101340150800100301d90c01ca10461050700a90300f40e40d15039404001294082c05010016403110011070a00e16001c070011110186030300d03250b490040c48148040143e0020362044410000400b603c142d10ba80111000c000a20343d000d600c000300505007483c4a034030340f0002003466410700c203d01040564506109584405008000301d4070700d242c0c2c3e1250110700011a5004002c580100c80200b0350440a85c01503c940311410103444110401c0f80c1e2030306004102d016206404d0104c100000400110401d010b4200c20103003940015030044160180480d480b1802052201d541003210f50000d40340c41001a50201d81004a02035207030394480ca0f1003443c00c0c2646c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 743432823 1250 743431573 743431589
    0xf03050c030607020a15020906070605040501051b090d020a09020a050c011b09051e03160306110403020f12150c090103141b070204021b0309011803050d050a0203090904031e020a02090f090304 84
    0x902b4a040c031155800850041c0c0c8954001c0086941d0002c40d1009034041c050071080781042004548294070f821400c81400c0d0340010080340340300c0c0d502c24203001268407014252012030004980b94403030310000c0c80b42054070100c0000104c142d020300840248241128054588106513000d07031000c075042002034048405d41c0103000c84140b1000710750715030075041c001e11049418500f00406186059100070a8804496010741101411190001006005050b000040910b4800c112403001c4003010b00c05524040c14400c40d4040e5a00103030800101030f80c080c08642c9807003048c40400e100300c2c0300c1000c0c5280001111300384c0060300d854040c40005e000e0703c1020441341c0c540c18119012440510044001e00c040300c8240c8031401d01d07110840f41401c140308144005807180d0001401500c84901400c01021131010a1041c1e920380700000c070000d130503a14251410b400040700703600a10f114a40c144030200b0364429900040c103a000b11540060654a1300400707922031000c0304000700d0700403c1e0401c15100509618 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 743434073 1250 743432823 743432827
    0x4020108280f02031f0503060105010809030c0a030801030b07020105190c0c06060e070305090d12150518100b0c03030103020d05070b070f0209070c05250803040f03050c030607020a15020906 83
    0x1006000c029400179140c80d1822040c6588110100044110010440780c0241c007070040c0e03a181000540303005000504155160104200300c00c0d40c03e105001e4400303a40d200b9100c0000550460404920b0b101009203d101968500f4051200b03281d54600517080308044101d02042080d1905406c880a1080d50401403c035400c10b00045103618002c10114419081658200b100d650b40707100960744e035008001c08101041c100d01d8a00b01d0013025801000c3e0001e003400405280903035480115458010b034131008406580070506211140c21030360f003500d00510f10000950706040610f0021b644910061000034801c3d504000310780708201052015070010b1052865440e00e5100380e042030035030300c0b0742984101e116140d85000107840c140118541d80e01c030341c1c0040003000041c82c042080030003200024803070524042004170000b0042d0f010002840602068042414400e195203802c51400045202c0c00748250450410080c901c3d50004404e4140c0d0780106100142070400c0100c90b00070f03c1064002d940101d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 743435323 1250 743434073 743434091
    0x170c0f0a080d0206010e0622090219030f02090c1318060306020c06040507081c030513051b03160605070803040303023a0b09012c04050c090903030402010828 69
    0x31801504842c6c1300a030b0000b03e981c8030410402110283e00c0d86a800e03032351101624180391450341c000c034510352016150341c184444680c008001550298421501401c05c000c00340c0460400392400764200da003074420340741024826109607100c010319000b00c1e0710a54183c02880800411608118000c1da08100215030721110300020f103403105c608030b4090300e0328410504001031a410004600700310005c0c50b810303142050070a00048000d000094107450485d12841c1c01040854020701c81c0041d41905108540481d050300824181030102110700124580c601c4881003084907044422034007500e40c0700d186180c1d299514036060b00280902e180a00c034503494641084507054441d511032410300903101b2400240030741071141c042a208040400c580041c080001003044a011140c0410001c1c0921016608400e074800417170f1501d06c04841c1955143d01600034042103040ca0001c03280c01031240c40107945185060340004c0c1040c030001c0c0c00e0070000d810f4828108a034183c407050320490505541018425012 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 743436573 1250 743435323 743435327
    0x1806030a0603170a050a0c020d02100f09120206070605040510090f02010809210c0106080a0c09110c0d0e150307120b030c150a0203070c1d01170c0f0a080d 68
    0x10060000702c4211107107111105a40704100c013030321075a1103290399071880c149018104807100c850614040b40c04c484e40d03001240040c0c0e24888003511076081603403440d042284c0c00d1030007402a40c9550018140100c40700030340c130140c2c4407041101d100c03640140c40400c56031104d25215140c4440101880030481c83c01c0500341c01c112030000d0062041d4001da0300c140342030700e40f04056078551003a02402d004c070f008148a05101c8200345d201402c00340d403d4074000a021a030301c5c620541804025003049411000140782800b804c00795109460342c1d850414003090a15078808c010542d5441010700700702c01d0104140f940752940c0c0e281c600d01c22071035002e0503000d42c8030309200b440a00402071186419591504002c4400810304001a407900308070002002c9103007a1040795011802e41d80300030301090850004103d0000440c24407a005002030024100e000766000e000300c0c601001c0322042c3c109142500e0448991301030180c0004658010301812a0703c03404505e50280007542103426540200d034907000e042d0402071159 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 743437823 1250 743436573 743436581
    0x160915140c010f1514102f0f0c060307050309010f022b0e030714010b0405040c150e0a05100e130911030d0504210807080304051603171806030a 63
    0x502c0b401d00f44450b00c11400c0d68440d6922502800d0980c0400342071410040c60100700f150b0480031a41050b520031005001c082a1380c7c8042e140d8440184c024009801103500100841c0700d08560075000b5001c0b83d0b45520000e24148409030048040210206c0428010103003980000c40407800341c41700f196500c244500840110014105500d1004400172009503443d5084c09030580000e00d084c0594030f000700590f43da09504004000d82085c0750b50701c16020039030303850720b2144500481c002c0108002d13452400c20743c50300c0b8402001b040402c0210296999000c0e4440c0c035050826100216854010809070703010440703048400c80040c3d644800503151070788013014a81e2110301d0140c020300824601e030808a0a143c0c0e5008141003e0b00051030801042040300c1d00e07000c6000701014201d5030200c5509298462000d9604602001e503210000001032000b002410002d011141403040d440440580c42d688443e855004441202c141d2440005900d030f901d480601ca080141c04801003101d0380f23900301581c0d101c00070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 743439073 1250 743437823 743437841
    0x7080a140a120f0e060406260108030904020f040305010e0304080f071401120906050c030a0e0307080d051e0a0213060305060a050108092802030c011e030b06120906070305160915140c01 81
    0x2e101c0c00b501c588c0f00501c60240c24181c50600e0300840ca0201a401400300035070101145040c441c10901c40071001a82c2805500442c8031074030021a200e90034180a641000249a5000041d038800001000b0030702c0561902101c12809003000d00d0f00c20340060002c130103072070300708030082680b49001c00700729150341c2c08030185005030300a900c00c000d92006c820545030b8034424110080d000c0e60052061031052100ba8000c41d9214003108280740c5082095001d0000b1460305031000820180c010440c10703d814560311f5000024096442c00740424181800461703004102d900a442c10031443c4130004c1c3d2646010810024146001d000081c104030302054208174a1600c0e001c124400e02034000d011119600c9601da0b4203e81540072042d41d0000041d090981c01441100603140c0c002d1004e100c458a00352101d030403070f48600c0d85080500b6171880c100348010212079000703244030000504100341918a0341d000005406507502c007003038854014107102080d41c01d41d034201c850740402e074800200c6928100040d00a407400f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 743440323 1250 743439073 743439107
    0x303081305011401080c010e091b0f0c1b01080c070f08040b0a030605120a2112050a020c0d0207080304090e0f07060f03050c0702090c0a1107080a140a120f0e060406 72
    0x74443e284011504070b01c3c01800940c0c0800e01402243c01d40311042e0040b07620300703401c60312b640c41e2103e514510055034008a40104294004400856098403003201c5126040d10074030345082c0c02e1400c4000d110181c00350b880060b203854100c5813681c04001601040300e000d0400c000e04d0341d0b01c5101040009003e400c281c0503080c010700302c1e20f0542c0300d41400040c41b45c01d40c941c13000c03440e0320071189c2580d07080503c403440b240b090800c05100070903902c2c0140d500c41c0e40e000390481e100141c2e448010160b41032510002c20324510856001c00700030000b008001c015281580c1c2c1450011400c0704181e403880345420a04102c0d20241d0068a600040d42900007404202c0038020351803d00030ba40d110740c111800c0c1c1c003030603801a421000003000210320a071000006c1400202c0360400d000c041180340b0840c0d00d0400c4c1500804041d1740b01c802000d06100704070350a00961800c440042041000d10303603540c41c840d41600710603010701c00051104d41010f8010340340343c014014058283da468950302d14004040c1e450290007444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 743441573 1250 743440323 743440333
    0x41401032d060e010b03060d0c030b0414010510061b060605120102040314011a010f05070b04050606040e03032a0c0102030f070f110c1005070203060a02030412110601030308130501140108 82
    0xd415558040d0310f50485403202241e9080d59a82420301090b400c4c00481115200e030f4110001c40001d800307000c024000c03401240c101d5103800d4032020382c0c0e084440240c0308a4020b00340d010200109070340b242002d0003030a0409000403503485503192010181c031050700010fa102d440c01410fa000384034150b0260046038003580c43e170140c0010b900c0d102c82c202d41d009100d801141450803480071295018418048404c40d4614100307181c1052510b441443c076509941c2183c064000608ac448146858002c48030b0380401440030b149181403400c0f941180700038009000002140080b454840c003420101690309091683d0000d641d24a000d41c4803400e0000102e81d00c5c4049080390b1a40a561841800c03000c2c54826290300601581e1040c0d010018402074518141e01004010889600180c9060150714004d903050103000d622410546002d500c9002124003240130032610740808c4011000000380750703044903014100101591200c00ca01c604188030000081d08540c285510780e031003500401c4240c1d040318000001e80e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 743442823 1250 743441573 743441579
    0x4020306060d1214190e04051006052205180915010305151906030f02030601090b0907030c021018030e150a120204050d1505060411041401032d06 64
    0x1103030890300002403c1c1c0da0948168402450285540c0e20494903460750a508280301c50303019010718200c1c007030749174000743d220524540142031034065175400800081c50001624107004c0002d01c1c40c05801c000021440c020b9020222214488980602500001e070465014a06130a03840c00c04582c141d6158245206280c80b0281c0409400e01c0c49041e254401c02a01040d140301804120050010341403074035030100301c0745100c0074960b5407081c0002544501360407102615140109070800b40d0590040500fa0705180030241f40343d4034030440301d50006d000d080011f4040d00c5040100d10f011040000440818035241500d8843d000c01995a0403543c820394485105159000501034189244072000d042c030300d820b1102083c1240a095003002d044007140d001030410341d0b9a0000f0381c802440c28009d403540a000328440072041d400f40111540103005407810b119244a144401000384a541f080c0451240d01d840b101d0b9490780329402070400d40d00c204034508440524414111980c2d81e0085001c0082c2d86019400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 743444073 1250 743442823 743442829
    0x5160b0c071103010605010c0f020f100f121b08130204292d06120406052403071208130306050105031b030a030f120e01050103060621060b1302030f0402030606 70
    0x40c0580c6c0f41a51a0421404696a020354102d21a00300300c3c0d0003a002c641100f025264846842141d082c10703a6034610601d0006e10203071075003054140000250f8100107010162079101411135884c0030003841d000e0800e0b41c840c004081d0420031410001d5119007006500c100b510321070720b001c400048445000e002c0c1c40080504000300d403450116910708651300d004604a40030706282c1011420380c0b000e00714600d4203804500d00d001b00740c4103d030100c0360f041c2e43d00e05101e040c5014401410703a40261140400001c00d01c100069600c0d56184104c824000321301e003802c01008110410380e0000b0340d070040607144843e103d02d00b0201526003401158000d1040b480456080403c0e05099201d03841d01501a00d400c4029490843c1c2001e21041040281300b407541c084480080300b0310510311645800ca00000346035040d89006d000340c038070503400416594108009000f12800041681c140e46a00c0382c2c0000700340020801040103180d920098403003851020041100c601011515144030360b02c21001c1e22000e585003020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 743445323 1250 743444073 743444081
    0x309100c0c1502120402060310030203032208060c122508040611040f0e060f1206100509070e0405092505040e070602060c1c050903070b101505160b0c07110301 70
    0x14412030100710202141c0542811f40055030031040d034660000e01c40d6160340100f072031980721401600d00540c101c1c1030300017200d41c06800e0801925050740546202e0426104c544c43c2c1d80205441c13000320084410120781c03d04440500110814940010410b9408201002030000c020403641035522604284490b40200d4031501207800f900c021151098282d801c004920704035503c02000f031074000c00c20f00c000294503910b2150400f422000800101001d14146043c02c0d040c0e10581d10807406050354406008104d604900b8000050105540c00170f4070340e031000c02103450b004031a03c1d80d07020001c04071010003041280c07a6619003a11400d8600348407000d009a01d05940301c610384620360058012070040b4200380190002441e01406000d5400d400c090308074108021140199284403580d44005483c2c41000040c0e00304a5010603c000350350861403034080041c041c2400c0c4030640c002c105002418110400c2d608402e0780c656900254a40c401e45045000c5a01d1503010740030981d240c142400d6003000c90f00d01401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 743446573 1250 743445323 743445337
    0x10050906060d0303050604090f05160902070305070609170d0b1f0906200d03020406110706080105131508030714010b0a03080c030c01290102060c0306060309100c0c1502 74
    0x401c80315640b609890440c010719001c6c11603903115480d55860070120740364494440078203009070060650041000b03a003418104a81e8040c08110740103022143c0030035080070550300b000ba04450003058180261a0403400030080302c402007201c00000c140d0f01980f01881d880107280402c282e03540010f480c0002041504401d54140200003c0c0b07040e441071211078410056940040307529100e1134451070443c60040d007480c01003441900000d602103800c01c14590f00c010000700b075047c1c15011f4041c40c1d04124001384031007414051b0034060406140c0e400d40c518820707131008074200b040604462503242c0b122102c5449600c980700680d803014401018160707561046c840c0f0250844014180d0000070700d0366171041015004400f9050b080c0c00180245a881c01c000e025600c0c445440031003017150107070200c0d40594100843d264441c1103600c02c000704031440614408481d007041c030403682c00d500c1e6036600c2e0149103405030401c180e04105042130301e0303103a0054110301012104d034402c0d803208408050a40210b8103e0003000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 743447823 1250 743446573 743446579
    0x120d0e06040c1509030c1d01050103052a070506040506011d0c0405101709010603060509010c09140d050f0d1418100207081501080601090b03030a0509030705121005090606 75
    0x200812002c80c05005a490004013400c0040e021a501e44030400c0a01d031540c000d040e00404401e070490500d029146981c00b420302400c4c02c10290504540821200c61b4a0050450703c9810048040300348000c0c000f541d07400f540c401c04035841407078a4604203454003030038802d15100c148800782095208a00002480c0300e806181255030406150004000710904110f01c80c50a200c454083da05011001d620654412110744002160440c5103181401c100c40b030050196000d41d1402c00c82c48503841c3e00c540124103c40b1981c0c40303168110103d0000078034800b220000101213200da48190344401c03c0200e04050845460f403181551441c0d50883d1030200d00c201b028082c0c548081003181251890b1a8031030003c03445551044030307485512815035514003c4444070303a6407980c01d01030040101a804201240c0500100801440301d05002004650369005010b0030b80e0501c18046080d401685081081d64001c1500604500e42c440300000103e440f0110700c101d02c40311504000000300c06620000b41c3c180645405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 743449073 1250 743447823 743447843
    0x150509030d050c190e1e03030406051c140106030e060f04082d0c010b03030901080f0406090b0a0207031d150a020129120111070602030c0705120d0e0604 67
    0x19070000080c00c00800040040c1020700c00c1c0e4506401c0004401c100301e6042d1603400e02c10240c178080010080c00180030180ca01103a080584581d05d011054604844132070400079110b00c042d00129400c40b128640c00c0c03c90f1440c102d0380c035019144600d0114101d40d243d840401c601c00d60488090746480007260031a0345191070001150009070500002c0a1065204001380d000290641c0e00003001118001590342110000c59100a10b4800b885481c2444404500071840c09503040c0000c0e20010f40100107c02c030044a1000500740003585d0481e0901d1a8405011401c2e40340440b1910003d4012020aa0000301c0c41d407506012095481c60344400604028070301010162100d09100481c1c2c00504940e00315526000700d0b030f0040d0340400760000070f4110b5501444c0002c40003800e0103480c07904601c0d80059a070420080707016540d03c100840d90021382041005d641c0b03030344241e860070440c49107000c024058800d00c000c5c90016070000b00035007008100c3c41c0c8180035010030002c810703503201010344000e490000c01e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 743450323 1250 743449073 743449087
    0xa170309060702130903091a0c0d0c14030301230306070c1202030721170f0a2a0e090a060803160203010605090702060703060b04080c1306120f15050903 67
    0x411800b03050850320084c200b403850543c0200d10301c103550034000100c0c003054040e10180050380d459a83c0b8107542c00c482468030708011a51443c44c1c7c4d41d03414106064107000300010684140400b0f6500d0808540c086400c036980c0c0c0d40d40f51031101d1401c046000141c0d011006480d5a2220310740802d945000d000c4039540d4401c2000300e0346030300c00e0505480c0003810540c071080128000152100e841002414078201d0400e681c4034040e0009441c3d2145003120700034807a0744e0400c0040c44071500700425000b85c4160300000b0003e44145041160b0315022001d8102d5a980240c5100300580c40900d03041038407401d5910f40794075140d005994050322a10f01400b1a00d40081c8101c2c441c0c10080700e240f90700d45000400111792a55644003050101d9015100080160014400c0101e0700e03800d402007600502d6a689801e15152411100a8540640b003010603c1070408001d0b00818500316001040500350b440c04020905000e4500b2181036145000111070b80a07039100b5000401d0024451584074000000c00346181c030364 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 743451573 1250 743450323 743450329
    0x1503050705041d010e09010e0d11120d020a110d09060806040605060a080f130804060c05010e01020f0903060a060f17030c241315020f09031204050a170309 68
    0x100a00c4a410840d0610000640702d000e025031a01e000d100c0140710007994180241c1390881100201400e8486e81449190300d2a00b400240c031501d04d007000c1c0343c06142e14000311042e50034044001c01001d42890040340c2d2141040351a40101071038402600c9290540171190701290b211000e0207603660110f45210400c00c4110300071032002d07601000c0203200007601c40d1558001100b680016044200103000402003026803100b034594950400030a51001e81201210707650a0402e126a0046404000c0c0710003800003088403d4000458030201d10000307546608000000f03e005030040c0c10403502c24450340700481c44404641c410356050700c05002c018040d00c3c0c140f0141241c10240d2111200007440308005042524038103000c080daa0200454020142414a480c0c482403104040c1c0300070101d60100c00f82e100011001d01c640740554840c1c08015848001c503005000a038000c0207401909405031140c0786c0c20716601302009100340c503001c4404080c43e589178408102c4811610440403c41e13401000003054a00d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 743452823 1250 743451573 743451581
    0x131506030c1407080703090f030c05010e0103020702090405030324030606040b010c0602130510030e0a020f01021921140d020f07020d060e071710150503030f04050f0a1503 75
    0x200715030600d5030300c034040c6408100c0943d1040c441a01d0007540403c485081580c88500c0000030020340284101040c11516804901f020328420303d81400030a819120f141d90098041d2072480d0740041640d103107460b060134002e0310780e8401c44804000518407481002540365080c402103007008090f0003481c0325501c01040c000104070655031241840302a00a010020301e40d0300007003024107a030030f02d0984082c1c03400c42406603240b15801400181810b2420407480c4010001d160041c107070301180c1082c10342031402c0040c0c1c00c010b40c200c0c1462058407440c1c210020700c5414043c240311280810340120341c2c0744490388110f40109000e01b1f40b0407040800c004c84800e4544c290090a441d0303400d920543c5c601206035000034034985016400322041600d400090039000c406010800040c10030f8140804003200c210110390700c4a62900e8002d0190b0340e1425115628200e44078604040c00025080325918800c11b813608009802a1042c14401c0c14180b41da0106070800b049480116517005115502f00045690107078064 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 743454073 1250 743452823 743452841
    0x10c03210213060905100806060d27030512090606090f150a06030902090f0105060f0313120c05190b0705180310021e0702030c011110020406090513150603 68
    0x40c64080c000ea004240e5924100d07002440d00d0b403213402c2501c2c908018400e00c500e54a1001e8240180c90082005a46600088800707200b24114005918030045058091260081d00032622113200c0300000c070b041582050080c0402c1500359807030115a900d141c0c210341d8912048462540150301040405c4140707c0b1001d001d0b070041d00c0300c031807280c0d007038651030108540d50941d030300110020384c441c0c0308031083d070a01080aa8000c1d20100f01c0d010550b05050209100d4803070380c6908101d4100000c0000c03101c041c540c910014440d400409200c02c04401c413801002d1410303030201a100c03402892455040a002d86182031079540c0e00c802c0d03202242d41d503840251156041000c804a40208000409059540a105d0042e00540312a00140c541c0d851507454055002104850307481800d080041c4009681d0000b12503003911401d1030900215020303418031908040c000807955024500204000c40d82581201903927054440680303820383d040c0c040c920b12100b601c02080e0f903803c11000207502440114400c1d0400c1c041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 743455323 1250 743454073 743454137
    0xf030b0a0302060412140607170a0507020c130e0318130e190f2102070503011a0f0105210610051201050f010c0b041110110303011404090519020f010c03 67
    0x2142d241b601149003071000803a10306002070180c440a01c0040c141a00c1d40c0d800c800c0b0300204000750301d4201c0029541d040c0c40c3e00c030709109400c00d8008180c0030300e40e900031012501820043c0c03a201c10b0684020809100090900c0e0f200b151908015031040c0d075144948064007100c13078028446898201c2e02c0140100e0070030000d6891003070310b0514101141c00c400161544840c4911411001801800024189031380e60708418403990400306d0140c102c481c09900c032aa0140100c030148a80e014020041e1401e00c0382c0c83c00d94220301c003c1c0324040a40701081c03261500c1104140c0d48200342c101c0400086802e4030410403d0080e041d82800140841d0501d45440c43c4002c00c181008030610071203459031819001c0468044600044004c6a6401070500300e0380c80d0342d06c62280c02c0140e80b45841d07072202d989900050151140030248200034008a94481d0850654241c101d015605002c0a080341501c00a0180c04241c4c0200b0b0400f819a030254805c1841400c542e41696541c04002104001f20300c280d00c80c0340700808 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 743456573 1250 743455323 743455343
    0x120c041107020d03080a0b0a050904151407020a1118040f030201110c101802150a0306031205310302120f010203160e10080c03100b04060f030b0a0302060412 69
    0x8016201d800c10300b90303014000d4131780729154070780803000740c041c0d03250360402a00820051008100644070905046d420580c00401c14614803000003500d8024511040d0002c0c14083c890305020f10144c0101da0301588a0007480c44514440740c42013407092101541c0c1442c0c1d1010b980c1c4001501081d100182c1c408a607102c1d200109018a0485200c8000e0304880c08040c0f164110960341402e04419114800310711502040b0710314083c1850300012184000d0454198032000009220400d1030711a03030004018661004c01d40c804817208c080028202c1e040440d00282d07400f42d03081d9401a2009d48556070110548600c4201451f42c1140c5c2408065030341304520190510484251402c1c500003030010b14402d00c0300300c085038088400c02e4030091010354541c41d0b26000d40c0311907215512580d4031002c0594000705009641d179803602c0d0b03c10000d0701a01141e1010100e50408a404500d050388054590303a200420fa90a01035140c46600700561245e031840300030b5002030700704400c000315a010200751101c203004040c01300f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 743457823 1250 743456573 743456587
    0x9070c030908101509091e170f03150306091207020118030809150310060f0e0d050105090c2205180f07031203050906060609060c010f0218120c0411 65
    0x903e002100d001a10f4201d440d00c2040c01070a0305001e40c44010321240006008200e169102d8039208184031044003000c1c1e00003400300e03040c002a5400358003011039118506954004e01850f41255400c00d41d6030060104640c031890900345400240b00717004001e00c0014200b00d65418401c02602e50003000101d042c0002d0705000c041d45011110501d00660056000d540c5d105400f004000c0034040c48841151303243c02c14030600414610074101c140c1030f40c80c00d040050101d5015841600c04d0071000c24103951010b0001d03045001c201064002500841e900360445817030035001c1c02040782040c910110440c40e141c0c04500d0702e0001d9100d030400c94200083c284c1d000040001744032080d04051404403010b500d5804084108100000003c0410083e0383d1841c0030441030510f003110035241c510103800c0610a001c040394160440d5031320030444051280388402080607000c2411494040c2d08200319260b00d0300400380550802d0f0401546080c0b110701c00d000500a4082c0f24010003009190003410001e500906203e54 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 743459073 1250 743457823 743457839
    0x32e09050a1103101505031b03130b041208070c150c05070203100b01080618070e03010b0415030c0605040e0f1e0a14010b09060d09021825020102030609070c0309 71
    0x1c5014150766070030b01ca00d07141030441c042c1003050794240130800c205c410810440c0410075003881c1c1a48c0c20b010060303141d803500c9a0840160342e005040d009044070000c4018041001064003440601118a0320303042003075903542c40300b900d100360000005414807540a55400686e002a4445a602200c1e800d10b075080c0700a98010a140003403d0b44c41d104035642d50841c280042d03810959040d48000210382100c02c100d84000e019100340d40240c8030405000290700c201000755000c0d0059281c48030f0203002007100141002c14051140218407082c0e5010078081004251688540101e405a41c500c45440b06261618990084036620084c408441b89001080700c440045110003d5401034581040118088500c0030003119800b006a000100c1e0b44010482d111007030f01ea400c140c580300c01400f9000200311300c41e40080f410800340c0b5003400d42161013503001c109410307200703404084058007401d02da8200c0c0603600009030700302c0c03000b0380b42e05a0210050001401031071007201c40c6600076100f4941030000c0390342d40401d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 743460323 1250 743459073 743459077
    0x120b0a0e0408250804090203062b06060503010b0108010e22060506010f030e06070c020a05060424050705071202131a130504080f0705070e010902032e09050a11 70
    0x41182c201d0300014000e0f5481c0ca1101c041d00c3d11103140c0382055a01c9503182c2e503804140c0700d40e00c504141d00d60048000b17508c541d00d08418614001c5501303548042030803084100d84010080311011505070346490360116190405200350301040e0f2040e150688140d007080b00824100d2001000012140084c01003030000281482c0c402d007045225440214150401d8030026118030400039800007050300e401d0442c101c81c44002605500901e0034201140700a005001081210669402498002c140000e00148201c2c644901c0340030b54040c008240c0070121500320465141c411110040c019500110081c014030850700e40c0030403030a100074240c00e03800c40d51210950a44200c0d281c40c250040c00005050518245850481c465440c0b4020400c16407800d9914800c2c1070041c07860703401038540007107510010041d0801100003d0b040520300c0040c0e40d0381d94501e2601960044072200743d40741001a001c074107450011000c0c40c0c0f01c400d4464458010f41003020490040500411002e04951200b0801105080c0000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 743461573 1250 743460323 743460331
    0x12016061e051503060703050709120c0504050105011409090a0230181b0103020c0303151f410c01050f1003110d0c0b0c01060b0307120b0a0e 62
    0x10a45200040c1d02009008450004107000c500101000344112196070214441d50b001c0340a0600150548681d1400c84402c5000d0308030281d0090704603501428042c1c030b18500000c641d401c840901084c0e2301c0d80011030720400f0721650162101014840c0c16404d20f40014560742c8001a500014189041c04508000031091031088641d0208000b880e030581c1c294484443e0350281d0b08018bc2c494a00384102525906c801c83c10001d50a050b40100c403094580c4a070701200c020391802c2c8226030f240d0070310300050180c181422a20707911610240000800c03442a5640c4001e109400351580e2003400f0040c0e840c604503860b0f04032000b105403500d2402c800102107040c4031120382503101421035205e5402c0b60000342160307805040c1d400d15401110420600c010544041d0b13040d0703584411540c0081c24200080b801700c171001c90000b401e0f074024080c0442e03569004070107007481d00b0b02d081c001d0081c0c51b42d8200984d0719210942d07030080082c401c0d81c0c41c001d0424181d00310340c6041d04081d20b190100c035a03442440040a809039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 743462823 1250 743461573 743461601
    0x90e12070f0203011418101e05060a030204060b19020c06041e17030c1504021c080c03033603040504090819020102030717070c0f032001061701201606 66
    0x1e21506d410703034200112040802c48040401941da42040603107030524106241407600303900c03200000c50307948a2401d040300455001e00700b4401140c54003940c2466402040002540428800c00504c0044c80003503030b8144401d010f0051842c250078105500710351704119150b10f01c0d2050303034000003881e20740c80c010340740180d1510781c091758407950849031060034442c50080541d941c580c40c000b4040940c0c1c42ca9050000304641d030040016031151881c0a10060117400014a114000401084940e040520303001c2d08400076051410601d440305584500030301d130044c04822055000384810302607402c05501c54040b00740034034540e50030510407140300740100d540641d00714010f0350013100b4401d08039080341c0540d0f0051056142c2412503d400d501c0200302041c04540581844119041203007810b002c0c1c17407000101c224648850342114008603545010308107501c22065054021142d140d1215010f00c0b9001010011411001d00550340c420310210b1900115025510290003c1510b00010782520442c90314078441 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 743464073 1250 743462823 743462851
    0xc160602010c11100b1c120f08071d030c060712080912031f150c0219060503060f031501060305010e0c12060d060e0313090e12070f02030114 62
    0x1200900b51009200c003242030028001c0710b40c034001c1011442142c1484038080010b001c0c0380440000700b4100d00c0d51030000c654245080e046c1e00740842a240039154800c0b079240d82a43d60a0707040f080301d400070212240c10000f000140c031200b0400e03801445038a048001412909007a0b041c0001502a90010784201d400c2c0580d60144806650810600d81c0e0258000d0094071b0b664000e00c0440354180f0008262200c0070507400903100c2c0c03d2980703d44c141c000c0e1810b200169060000c0c901d026003141c0d55064142c0c819000080c0301e01b1500d4481c2c0310002038030b5241e5226415a00d0310720030b01c214144619030b000e41c10f01507040f45000809008118a0081c091660046804d5140070f44103010303910064280c11042c0c10030465449890320f032440094210009980c2c0d80342c60212810000010000c1840d503c0da18040020071140c0b80c0d102244940c2038410450042103c0118120304c00e0303031104d074441102011403080c0950340c0450140760400310300340e0010300003040003c09003004e070703104500c01c50b0200d80341000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 743465323 1250 743464073 743464079
    0xe130c0314090a0c030308040201030609020708070b06090603071403030408030307020706030b0301180305090a0b0d09031701060f11010e06070c060b09060a2106091a1b18060c16 78
    0x4402156500000b02e14040c0c00d114070740b030320758142c602d40c1c502025040c00440d001003021a403003544242c008002c804000c6407031302e030700e440d25040c10b9001c481c0544001d0906070104809103000e0405500400c8014000e000c07a51504210040b000520840d00c0d0707040c041440000f801c00001c0c00214800c4007181d0141c02d0039410004050101c9800701442c0e4000c2e807404244040d6000d01c1d205444030a0740505100d84c5407c0c04500040803003801d03800c000a00c6201040a00311a1000d401c00701449100e501c4040c0944102042a00b105074244182800184907048648485005800c1802440400c4002080c003a41c0c41c400a860000300b41c0e0030400140031840d102040c0003903840781c1100c098088440080c542002000911250090b028005d080b02140c151031a81084c584000840742c0c0e0300600c2440210710b282001000040410111490070702e141000a80407081c420b6a000580080c1c40520700f1b00f45c120a00c03980740000040040d81001c010003202000e44001c01c9944100070070340100c0d0f60080c1c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 743466573 1250 743465323 743465351
    0x13090201030e15060a06260406180506060f0405060a120c080a0507240915020a020a0308030a0b0303030c0a0503040c032f0103020f19051c05040c150c030e130c03 71
    0x10380c420070411403c1c4207001f6100b070350250f039041213485241000318503440b01d09100004002400818101c070410810944c10080e000c20703440c1c8225000c035070303014400040703400b0701c800d90300d045403260780c00712803040c081c00a01041c6502c3c000440c0180403c5d4080c0e41c4a03c1440d246c150a5003042e104e40e4001d01c0108501407080c2e051041c1048810300c200403c8610500c0a00302403034501414641c0120740549003501c0d4400c122104c4200d400600784e030640f41d41c0303040000740e9034425210304d909607007411b0441025003000001c4a00840e0b000136254905070038204100d40701e40016100300c4a002480f00c0c000007045640282080c400002d0f900c401150986006041e91901c07100050b0341803500611550b00d1480380181942c10b5520781c04404000c8810f1725104a4803889401ca004280750f20540d0941c0e10064103900c101d102da0300c507060b0180d202d5103130f07034560200c0400010000c00060003140490002841508954000301000e00800300541038420484d00781c865007806080040d503900c0c00080d140c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 743467823 1250 743466573 743466589
    0x1050109051005010c0201081b040f030c0501080118021c06080c0102010b031b011419020d0e0103021804020a2f1b03060f070908070f03051b13090201030e1506 70
    0x540e14400b011041494000064002c04958001905015401d000104a41c00d20084196900b85045480c0d0380d6a45480901c04041c4640c0010740308202080d07004140e55000c1c821860588051270001c00c0d0401010010314081d50001304c046d001ea900c1007502c3d607900151750240b070003e443d4550140c070f01d91000e20002821120440b8010b48268440d03619844040700c1c0e03808007403211a0030f103000040c03081c025034200303641d11801e24030019991105094649040d40494403040ca80314035621005400180c40c01103091b4000c9003110000400103180000b084e20701580140880c061509001c000b41d18105088480103161401c101441e41c1e1042c43d105400c4002d001d601c4807180c1200030005a280c42001203940c03900000c0201e4460360300d91021940c814051034441005142c2082114400c603252101104031701d02030b00c021207952140c1c2d4803107140c1c030481d0400d16044420150658805044d41e0701c000780034003860703803099051607550b41040c81c41a1050002103c00310400b0054902410031400f440540c1d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 743469073 1250 743467823 743467831
    0x40e0f010609150c0b1602150c030a0209042d0c0813030e0d0b0106020136110d0209041a01050613060822050c030c03150c0d0207140105010905 63
    0x109581000501c94550420110400d5500d0305180c9000c074100044103032400360003050083c01804000042044400b01402d1030361303070212543d094030b9003d0422241c1300150343d0191801c800108080c00000c00c098071950203030403502c10003000420240708890329412549142c81c5c0e0b0014000944009001007032a50140c485922501d00d4452a245081501c1d80c440228000b0002c0401c10301450b242030030b65444008507141d0b90000b90302001540e40c0c0c0c801900030580f1801008940ca90046422200f00c1c030140c41160000131394022401d011002d64401c035551544c0c2c6072195000050020710b8000d070329440d490b41d1245101d0340a900307002e510403002d07040110059020fa4483e00d400c0002800414840002c081201da00b824042155118010a070300c02c0000c030015501000c1e00007140000344500005c00d201401015002ea441c120032643c18107807514000c0048035605000740000c80c007640400c00050015406c0c0030300c01400c100c400d54408100c17511112214105079143c100500920400780305003a00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 743470323 1250 743469073 743469091
    0x50f04020a060509060412020d0803090c01020610150807140a0c020a0b0301120b1012050309040b06131823010e010e01030210030c20011416020606060a0201061a040e 73
    0x14401d13480c0000741c3e40d01c03490180c00e0141900481030002c54603510004201298480710141d240d03d00b901c259640c4020b039041903801807147d02c0204070308610b058003000513070b0fa181c18164003a00282c503054500d810050919410054402040100c6580c054050526138090b951072520040b1700d40108402c0441f40d4015668403401040104110282c0601000c20f503940a011101c280e13489003280103001000f42d0101d00303a911490070300d40400c07070040b0081981c1c02c8121000c0120800e075009000c854007480c018141c2c000c03c094801e0010313028042400c0c000410070740d0302152900308151011401103940c904041180046401400020391848180d03006d03044620003094158035640000e240e04684d401041c042c55607072480c1c00751036403040782102c00003c941210a0400341c00400040d000340007240400100d071a4940c08602c07483c12005504030006c429500802c40368445404020a540c000c40011040d5941c4031000643c8065000c03214081c00207120010b030f125490001400c00d1204000c0070181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 743471573 1250 743470323 743470327
    0x8010518010e16170a05010203040308011707180e0c0a150f110307030f0e0a180c020109020901140d06092f0315100f2309010f1406040306050f04020a0605 68
    0x49507643d90000d44046480f0740200610f010410002c0c1c0341450680c050140043d40008100f005058003c0d10a5040710700c843c000940328040044515100c0e10366008080c5415040c42444400880c284c100e003d120300e4860945602d00000310001c4c907444829441103540b1090701000080441e0444269110004a0b007000e40c0d40790070014029851344a00c0c0d038000c0904c0700401c10760252920a0508481407000034101d8400b141e00c0e0038444044007907401903551500d05120301c54160302e00c107003d903416030380c1c0c00391182d02141d0030000c24840ca04c0c210312400d81c00000011940000c034405005501e901809481c0c408190744058481032140603002c807164076a0301d03000d800c0c1f00450324000303641e413100300704600d128a0326100e070741030b000d002d003d40e9100e01480c00395044c0110300580c6079200c4038420000c980e2103841490a20061040c180300c00d2180c80d2100e0008442007080c2e0001825092403a0302c0101a64030740b42c1c980d5940f0084a40554821b144040484100801c50500c100b4000244c805820858 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 743472823 1250 743471573 743471593
    0xc0a03272d081c031d0f0d0f0c0204050408071b050f0a05031507030b060c0309031b06120a090f0b0402010e01022107020604091125030e040b0a08010518010e 69
    0x155031055880d1414031510326000ca8003d80c58800d80c0061181c610041640c802c403e00d00e41d0b401d0703a9044181c021002da00414000c5030f6001d0050420f410004510780300c2401c04082a02004000e000003130054402c0300d4200818000038500c2e40f80b0002401b10030740900c56050504051008031700001c1d940c18000d0031202800e00103554001408e501c040030000010b15542c2c0c58080c210080d20b2412903007034001601080a0240010100180c1710b50101030b001c64400d010040d1042c10148914800550048010009044074500d6031015591200c452540450354481d15603911401810754241510007000b6141480115a484500b42928110910040c41c098001c400d4503e1035040c18081c94281c0c0340009488011519100d003135500600d0104010003802d80424a21100c2c0c0e44403210b500700c0300281c41a03a0414960a041e5100d5940c4c25a6811240c0000c92040c08000c0c140030030100e42c04a01c9000010399041c0900075203104610950305980c510041c04029801d40384040e80e04030850300849515 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 743474073 1250 743472823 743472839
    0x19061e05040c1508040308040618050304080a060b0603040f0308040606051906020d08090c0d050a06020a0e0307120f2004111b0a05121309020a020307170c0a03272d 72
    0x1f894000d6001500001c5004500d130789180c041d15001401407080c003020400140070304000c103280c032080d40203c101303001d854807440400c0039900c0b00725001803007507040d0009080420f2248003002e038400e219210004101c3e0b15000000d1510300004900040f8481075036091080c1c550500c03403810401c2039420012004d00302405141d0b110f44030f8210150090302854194418442b041041003002e641200003150f0740d45604d00018410004a4000380c060301c250240001c08030021900b01341002d801501e41800b030f00680d070310503030021a08c031110f041d56601d5600d101440d40e1107125a0303400040c07801c18a0faa5004d9003100403034161444030030400e0750b0842c0d2126404208003281301060100e2800206984d0310120561000207012a04019042480810b038112059000801040003501801c49081d00341c01801066884d4811031a05221507041000c5039000640101d90303003810319440003920340d569000540d0403074441c0d9241c0d00c0000d22600301c0c40000f400c2501a0315a04041c0071440580202508001c08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 743475323 1250 743474073 743474087
    0x211302040b04090f060c23040620060c16150903090911070b1f080610050a031e02060927061009140f0916020f19061e05040c15080403 59
    0x40500019180d0400000c1b4a10a920034180440189a180710303501c3c103020002615002801004041580c01d0301e504500030000352407003403a8219900802c1c00d030b80c0e100d0700711001d03420040041c0c0c407100c050f42c454000140d20001000c50008100c10003d804401428000c0c520303a02a4030208250b8a040701002004002c5412a0089900582068865280c10003007040721001e66004a681503038041c0e003c141404041915801038100785c2002c90380c151544200b199039a2180700003040300c0000300070a8905410a0301408006000402c2a800c2007441404a03204141c20204a1f0400c444001003560314001d11000d00d410050549401c1c05c00284100e000e001030b0704501500c2a4042c038407108104a82e201817540540c1d54000e00f261900e410300c1280c400340e403941314a5200140c02a04000400140d0005044030113481180100c00720691a440305030042022402c002c03074400d0b24100e8207030703c100f040c081e02d03005901c02d09005110074502a2150700300c030107805058081054140038172010946c0121 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 743476573 1250 743475323 743475353
    0xa121b0308061302031003170a0c06090c030b09010f05010b0c060402090c04080102160b061806060a0903062a02010209011706220e010b24211302040b0409 68
    0x205112540c0350341001943c0441003020319020a030001040201c1c0c003e408020328112482591500c0e070ba10304410903140b5501812042038006a40080644042141e982042a000e4081d44050020988070789400201e50000c1b01c0b2001c4a80d10f6502911200c0c002d0f01c22140140401d144440c24160600c0d4a60b07214007010744040d100d81005d00210300d80d800c03c07908540003440c8940c001c40d502c44021044000703000541c1c03401d0700c1c0e0003640340005605003065203003005a0501c82482c0e00540d0b40c1c0740100903643e003003a04080c042110022000c00050024403d041c41e2440104030140c1c65a20400501c0d0101d5004c00040700f10390060150040d141d820525070b10420034603100d5140319543d03800106200341c101d000e5403918000c001141c5e0f0503d440d20f034402031741600c5101c0207101d0714505109000c402c86c03240900f40c2d40d8031400c00c1012041030300309015000c0d1140c0207044503600cad10700d4150024a440250b4080c1248482c1424010031450184110b140c442815136092216040075241c03134441240c1c042c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 743477823 1250 743476573 743476577
    0x18050102150c0a05040b280813021c0204051503160612181212200304020f0315071206090b03030d0f06120b0103050c0a0b030c0a020c0d03020a121b03 66
    0x200d20103d6840c02901039134081c05550000e251102e512140345d029000700010038140001e0036403540d00d811481040014810b07030450f225640070a09a13800c0c0004000000300c221490301443d1400001a6a207000b0316000f648101c1205174000d410b10200740c14400c3c1090344403035140c00c182c8200710054000c01a17521400000c08000341000030800039008074004024000c00b03042400c0c0900b08099001803210106d0003130f0244c01c0040824110441c401ea009094450301c840e007051000900510300040034694806020341a292410480b194100200000381c5810020803003d902032552442e85206100040080340814400236035040c011030780701d01c1012a002e544584607031681030400c10b00d40092000740010071141c485481581410140403c00b80001c5410380100d84501056142c485e012170169220000c0302c0303281d030b100c2052103000c0b40e10a103081030960046500714140b540d600c00001c8001402600a070801d04d41501d841c0b181701c0e04106071081840300c0380f40500341034400041c0c0f25891030b17414 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 743479073 1250 743477823 743477827
    0x12060a23070f12050103030503100b0c10150e010b04090506010e15031e012709170c0c030304060806010806040e030d11090a03030302041703040302011704020d02040c18050102150c 79
    0x5503004444400854400c610f8044c20000000209607201004500c41c02c40307210744425654480002404521a0b03a82e0882613901174001d00c0d5901202c0d61100140e00030032020f0040c09070340c40b0907014400100741e1002ca00c03d00c001c642084004654003401e64440030910b011641c8181110010b030000640c4c41000035454030101c0000c541d0b08000100410044443c803040206607520002908025001c685546030410b0814541100c0b401901480041e0780e44401d09410906100740c04140d20b4204542960091045841042190300d082c8002c1018202966400c801351a001001401064000d400f86010310300d0401850515400030003503902001e49400c021884c5401d581d091a110700a50401d640c0c4034620341c20000400da0568001c200712001042d1008640c51322040c075940324011484003130b01040790b4000c10f107011a00d07800f010398031600c01800f90b2403c0019401003001c0701c1400e000100801c090320302da03c5a5064106a810050109100402c00f5a0b120703a40c8011421005d410a0f411143c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 743480323 1250 743479073 743479097
    0x30f0109051816051306140105070302100204140f06090a0b09010507061b080705160f0c030503120414011112040c1203030f0f0b01020307140c12060a2307 68
    0x208542c01550721103501219200f99105034901d006102500c1182d119200c0d00c14080c000d52007900802d402c450f10b45030710504d1a00c1e01001594a0780c031184080302140103503c00c0042d401160f102510280014000801c450341504051010340003221704864401c4001340034071401507451480e060180d51004840c240c80301b9121006803018000c1d058024000c504043d032041030074864150300024a031956403045d0494a0311107058840f481f42000c0e95004124031545440813540503a0740900f0648103c00700c0210564a0b281c3e1411134020500040c1d01d074071600140300500c2504080e03607040c140782a0007040b484d10044000c040c184502c0f0180d82441413814006000d100c5000383c1c2000415038900200d484000519004004140414440407170074074068511b10404070034801c0b525034031010380003140342c0501034940e684804550070204030188038480c01010f4a40fa0070480b0340c3c0c3c2d2003203040280b0310340c00c02020364800d90b0000314078410340740ca859407054a10503089400f1900081681810600503032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 743481573 1250 743480323 743480341
    0x1111009150f0509011d0d111606030e070504060b160f020a0308071a040c0905100f090b1e09040f0c080a03120b030c090115090503010606020303071202030f010905 72
    0x148001c1e508007092802c8200e054105841c0c200f24400c2c50100c0c0200084001c00c210f20303d80000304801550640d1041d000d044180707004011070007100444030300316500a40c6801c0d070301c41241c2c059040900080d44410207401e5880c01040500040c00084809001540c101105580c9c81d000c0d83c454008a906906600d40510403128000e40301c164014006c42291070b180d0611040710703409102c08850300704d0002c418000081c5400d18183c0917942c0811511052031134020701c0c1c0080c01c00544042907110560328002040090014504c0081c1340102010030741c035108004001800c0e86880c14201492102410f0041aa41b450b0400c0d50040d0f0059102c02502c1d4542000417240109801c021518454041c0703017010b050304010000b401c842440e40620407600e0078000e154550243d00b8900390001008070051100620b10740701101550200d28289890607901c1c1d0000742547c81782e03072008001da0030000a100345140c0c0a8004c240008144d40154510f04247e81031104501c01440fa02d0166562803005c9240c0403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 743482823 1250 743481573 743481593
    0x60a0b04060f031b09021c0b0616110a0f0515070804090501090b1e0108060405060f06130905060303030c16030c020d05010b0f2b05071a09040b01111009 67
    0x407500400d5585803688901e0060b08401c541c60704d001d080740c121400014500101c0c02118060f031101294081903003c084140c202030034551034001e52050f030900486034864584060012040d01070741c102c0d480c01c0704400c18042c1c4100300f500081c0c40522005070602a40e114883d0201170b0f041041082c650f11192800c0c004a140502d07002040083d01f000000a25030140741c104060080044400d80061203010710b900d40704074980f064041c0031840700300c000380713480c0b42540c000350b8000360140c0b01c28002107130080010203542c0011105440d095150310103010034409071044684c4580150002c4d4907608018800040030f000f1009094a03511540000c1000c062081503001e840a0340901104252105450000d01800108000c680030340c0d121000c40040f40741034803d0301d480c3d4220b1009401c2c51f080700010044920341048003502d007441100000240e840820b1000003003104a28101d90700e50304603a04010079241803410090421401b0b4140e0764503603401103105203000000000c0058010114a0810285 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 743484073 1250 743482823 743482829
    0xe06090a03020f040905330f0f0c040f030b1501080f0406020a09091b030c21020c030705030c03041406070305040621021c2304032007030606050112060602060a0b0406 73
    0xd4029a1441c007d650f018010310659a400c80802d12000d402ea24503200f000d1404440d00080e2000c400c0204008100c60504590400e45c00240700d49800c2c0c841d031a0b10391132003e59100720354090700c51003080b60702c260700b00c400a0350220910f008003042c10302c40032105035400b0142000c3c094581c0000c450800a00400c00c64005141140e024003a25041c0c20012020107038113450100800c0c20440c884461a101740801d00d42420341c90721801300d0b0b10901041100039040903918062a11080004802007130040014080058429004503525400e010100f51104506000107000e00020320680c0b000070b400400751806e135405403600d120341140e07691002c94009207001200180910016100704143d58045100c094040064028841096140448003001d40c4910310304680b0780d0400c0c00300d00041d00ca030181001c0582e5607062418080f41034145603040c50242e034000c81d002c940c1c4e88001c00140d60441a02840c1000c48041081814602030019443c1c00b8010454851959034102c400240e0350b4030b41c080005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 743485323 1250 743484073 743484083
    0xa06050307081e160215010b0a050f1e030405070902070f02040f090f03111e0309010806030a1a010e0606034005030a111204050105070317040b06010e06090a03020f0409 74
    0xe810103140301603076110704c1c031016001401500300080b418644162040d040b81c111692407413401102120407a12a00046072040ba031719010400c2c51043c0c4200c480d0f141601103c02c030f0035944d90030076107406441c1014550020003914010701010020803244a0741c1d03509903405590200703ca0726120b8440004185101c00200014881c1148030203140c0d1210002d4400914981200c203400301c030004e11012802c0c8401c1d040d1b030070381c000c02040025500c19504140c2011029040780c80c452031aa0350241c400b05042c50842404c442c010042200340c4440101c03941058054548516504114940e980d662060140d0051545101d4100c160480301c1050001c001c80071608196010b1043ea10b0000c0e200d6002c40c45d40800a40700030840840c8000221b4202007000c83c400355507280c145004019a101d402c003920550074003051740d48102e05218408205846540703d4004a5501d2400000240c0804400344e101805148148110400e5850b4000d80501307a980403100764604502c1b0704c002401410303e070900100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 743486573 1250 743485323 743485381
    0x510291803010c0e10020106050d080a05090618011205061804080f0a0c0b1b18150a02010902040c180302040e0f03041214060c0f0703020a240b0a0605030708 69
    0x103544e50140080d403010408a401c0840728041140c201c0c241c40060141e40d0388009602c5440d40014400790042c0500044ea040c10f1b07003004080d00029101c0c1d0000b240c1c020540c881c07041000d0040d0307031080481400070040c0380c08002c982022804a404110f602c5070300d2030f200c3c00010214050001000035100c40301c40c1e0080c2c041d030391a0320013002000a0701050089890085d0a0b005c02c261000c142607848440500011540c20441f14035000650300c1d40d010302503900a400060b40700402c16004004113004900c0350008580002c20b803062108481e804034081c1c00b00007152446040303441000d44003004403501110b005c6203003059002d400e820002ca086001009100004002500b06000c43c1441051801404040c07242e40034045195150001141e8100d4000010000340b807620640b9805007520034020b1040301d159081d40d50314580c03803115841000c680c0169020080358510250700501004103401e0301d0524142d0711f0414083c007036010240031007041c45441000503d058021020804c040055052005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 743487823 1250 743486573 743486591
    0x50f030c06041d061008040f060b0d060603110d03051b072402150f06040c11070803040f080111040b0f0c0106300b0610030609020d051029180301 64
    0x502480760310160307440c070207800303c000404924080003451800b203401c1e222803049507150799032400c3e10000001e041340c00503a40c500019490b154a04c40040c3c1c40d119040024410f425400c286142284c40c44003c1d2050040c0c8002c500083d6016056a00040d1007420405807822040e00440c10701c0c1ca6a0040f105054188c40544800c1e42e086560608009141c0c080c2c603006003106a01e036078082000c45824035401004400306010382000d500c5041b10a01c549010b50311281c2010619050142a500c151103035800810180030003142d01d08050000d207102c80017001b00f12140d08001005020320301c1a82c800361000b150790508402030104441e44608904001c0105a444807203130b0303403a1001900c05da01c0c08035488090b201d00d416283d207180003c9401421550041e9a17500070402c100012580000030103449800004030203607103001504030403100c0c120106251070880030709185050300e03070300c40c010002c5505042c00c1098001c000141820340e00c0200150788100d034800101018080004841d0076600e0300b1800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 743489073 1250 743487823 743487839
    0x40c17090f12040e0f070c110609040f060311191e05060c01020703021605060306041116051e0d080c3406050a050903040501120e0a03020d0215010f050f030c0604 71
    0x92007a50580405a01c1c59190b03003282183d041d07401c0300c0c12000301f40280000f4011506083c02c520f03417490300030800d42c64540c1050215003598140000142c400303489a4051040003041440040001425a14003034111461020031040d503034948035450040b540445078600ca500000d04510150201a081b0b580e10340070322194038000e600025055005000c0c1050881407004003c091404907a0000e1080e8110b0f181d140401c4018040c00101c0201a0010080d00c41c500015040ba8405a800345010f04107005030410010080030b0070320300e00b1042e50800114a10120740202c0c21641080d803004403540c40d040e401c150704086800c1460314000c2000c00300c100040f0f2500e882204030040c2d214200a224035154042d20800f504d506039503600040d00140810300607548120f0a904020581407808104c11000c8130781141890401d503000e40068002601c0380d26002c0d01000030f08075220036112444141e602d068401d01803007405001d464406c0348130500400840e5820800c803041e54030001d21450342e4035911449 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 743490323 1250 743489073 743489077
    0x120206040b0708060a090e0c150714010b0a12050f0a0b070e030a02060a05070c05101e02060103020f0d0501200a0215010e060622090f0506040c17090f12 67
    0xc070340070010301d07000408191242210b01d00848001d02200201414030356400050300716503140300b40d00c0c8102041e10100b503940d012514000c400300b0403c0c44e41c0b01300ea428407540d40c0007600d80358840c9070b06000f001c0b03060b074031402e070080c00f1281c020142460b612020316089081c80340038001d100c071a00c41c11004000380883c01102ea40240d6a9450b040e030314801d0103062689902d40c00901940c440c0080c0002e81045000b9402454505e119040070f1184545550015016807803207581c40c1c00041c408116040c068291868000a512450005010562440e070000d0149440010380c0c0e40901043c034184c208010003500910307d4103100001240340648151008000c0c0d420042901e4010f00c01d42021201d0003840014240c10303500201d1900d03455030f0b03070f40c01031003401c0d44404841e99400a035048401842e045400302c41000d400900800f0a0707070b168007a0000290768020304503500c550701e0041a0ba001c036800080d600f150554440700d012040d41e909400c1da0515000c2c020b503440c0d03070103141c044d0084000c0d0100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 743491573 1250 743490323 743490331
    0x80a090305060c030a05360a0f050a0204050c0705060604020f0c0109030e0a06030c02060609100f08061b04050d0204090501061e0512070803040b0f04090c0309050c150702040e0703120206 82
    0x90200000d41d19025014400004182c602003007064601001c08981d00640c104007400d147d48084801c000e090f5655a983c0c41d003c95416106600000e14400031032509002e2146c0240821086a050100c5521030507140c01d8003920f414131940d400186100b000c441030341660001c82e60380000b000a070880d401e000d4544104003c02d54801c80204030041043c0d4040d200e1260003003415402043c4580d142000d120300fa00014011050004070084002101a40e50b64144003070b00c00800980503074100b0748130840d902440e6031442c2914010901080c045070710303842d440d88a801d404803004145030805003820b90040c080c9401401610a40c00204001400041c2044c030440741d065400e0350384194003102c1d180d1540500c0c02382d51200d410801040040e4103220002d014940341c50f10545d49840c0c1d44038822412940c84020f90404030362a62030a0017032000034032103499068000c5d1402c10b00051544040764680c4a00100244140e6540b060003001580c10000b560103140d010302441200804804040c1d07503844211 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 743492823 1250 743491573 743491591
    0x1005190e1509030a05070b060a03050d170903070b04030f0e03191b06020607080429070e0a08060613020409090813060212070f030201020c0703080408070e040f080a090305060c03 78
    0x40c000c148a0b030000001c4482111055442900303212440d034500d03020240240c8955880b881c209008408a0000c0c00b910300b0002c070343d0300c2e043c07070318084010180b481320740c02481058240c0050000030045880305402d254040c1c5d0520b0194403210250f0029610703680102040790700340c401c1204403080031104244607460240141e054201e4111030b4840e100291025000319030040e08000c0115113880d001d00c2183d50064800c1010032281180201c50210328464001c0c00a03054070440706000320141c00c51211116140c0646039010b07600c0c14a0074695440d00e0240c44280204140380d0321200210055041d1005014004c0c4140000040e50524244640003070090f8151002e600200140c2c032400003800459040d107900b4441d003804c0842e2500008030441c0d00040c0d0555408024029482d81d06201d61000346110b05080b03511103081c00c604c607190401075081604800c6003182407101103101040044078003940b00841c1946d03404403074400c41d44140c1640c0002c2440c41000c05200c1c0b49621900610b101b07041360 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 743494073 1250 743492823 743492863
    0x10606030221130308090a05032d07050d110f0f0106050406081609230708091b09060409050a0803070e1801030f0b0703150806040c050a03051005190e 66
    0xc0e046060020000303503420880c0700f015078000c00c000b80c01502c06940c806c18010030358621442c035403209429070b440340c00d0030002c845a80020005515a02c41440200b4418081031810103480342c0d1450341e01c194600d9180d0a000304261111040c540800c1144403010380642a200e8050000c0c05660282400740200c62081d03040a401150400002820862110354030000c2c1104038a08956200100703100c60041501c090701c2a1081c0d4040f0040304101c0c05030106595500540c43d01d100d00328203000c01e506413001e11300030341d0404d1152903807058a00c603042007080381c0000e00041c0501d0802c6c500311094400601d10b00c401300421512036000031481c846120300340c2c0e040080c9000041e0081d12000c1c01d0000038000480d4000c00f50201c1c00ba07045580e400701003400d002038032028109407804032001d66444030b1010b0b4001410441080f0000d0800301c000c1c0300941e01e010034203080d0f56880c0d860795480e480c02d403a017650310340010303011020080303c490030000c7c001401c004a00883c04505c0c0c07622003013103107107800d543d11b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 743495323 1250 743494073 743494117
    0x303020423090412090902030f0a0f05070c410712030504140a0906090c0908010c0906050f04091d15150d03051c090309060503010b0a050f0c0106060302 67
    0x2208102000c40c000180b140100b80d0f900d0307641070320307504840540700104003c00310007141ca0102440214041c2c0c2c4c03070241e83e09072490a54501c10a552400e907901158505003070901c80031a4103c015070203100da00444040c60030000c1e00c210301541c84240c401c2010729011840650503049640403a804200b88c00044da0a0140c4800d001d41c0005400c030001000580100820040d00c46d004030441c00d0010004c0680c40c0b40d44d42c0c2c0f414a4140c40064211006480d911540185d1082e0880c0480d0020640407009001c044000b0308040c090002da8403c0606000c1e00180c0c220500d030084040342c001e4020000208003000884040c00311810310b400041c0441d102d00c0d0340813840e004500c0407e501c1031030a800e0ba46412018401840040c60f40c110741101800014407400d00200300e400c5401041e881a410006082207a50400420f001d400364881e406000003000144640304170768044a04100d042c3c1071050381c800545c040300e180e41c802c2420210f419403811001091070380d4503400a100302140d105000d2170101c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 743496573 1250 743495323 743495369
    0x6030506010611120a0309020d050d030b031b0105070213090b01050901092f0409060b030901140c0d023f22110402220602060112080d090512040303030204 68
    0x95000c10300440c0d0b00c01107801a403015030030010110769590f860003141d401042da020409c010086102164150003410b264054a0350603c21009001d50440083c8505007c07003900280d06150307600b895042240000c3c88805645500e2200b840c52249041c00b00080c0c5002c0c109450070003001e004403803045101d08000583d20400b801007100250142001b0030b080c1c0e1000d0f60008120f054522911003114060100068600311442a04000e01c540b04696940b841d148200c00e003158034015401c5e850542e002c0a00140034900001d507a05403400c11790059803501c240c288170080c901c0307407a007500c000c41907061452824403072044000d800348403421040d803480d1620000101c8003032001d40c0346066003000e04035800c080341c200b440500850700c010308014076041c44c115241428907041c0c80070100044a0140410001d64100801401000404034404203c6d2117580c0d210b40b540300310307900f1038030751510388251909001c0e05008020501c40e49141881c0e9541c0e1b20f01e0040c02a412a10403c1e0b07500b02c0b17003521181740070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 743497823 1250 743496573 743496587
    0x71110050a3e030304060c110304120206040306021b060a05130818060f071a0106080f07110f0f010506090601021507120f0e010b122a0310060305060106 67
    0x10903880310440c141011408402000b284003822901c00b8940a91240d5820152090035400c50500007540d40c900e010b0800784240c81c00c111044003000f00784075002d0076039280442900c050742c02d008203c1040818034000528140101c1d007014122620000360070955a08094500702c4801c854003e40d070455594040301780c02c1f6402114031100a11074900b0010009000300028421210348640c4281340c42c039541c01140301900071488800c1c134448001024018401c00d2203043c480310035a00303105d900075810460002c203a003102801d1889481c4c40300c00400d0a0a025140d13081100e40c159003240c041150315000140d41d11008074011905501e03002c0070440c01d0418800d6035110702010b03001001c410070b0305484c00d032402c80000d2200040102c8501422481031090041141c40021110301007992600f01800c10b085447d0303001c52522510f10750040c491341c3e0b0404559004481e40300c3c0c0300c03c1004c6103001c0002d01e42000d40211240e16008030300400f40c803000c0c541d00c036038181c81c080c0741102c0c4140e032034072000c0d6224 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 743499073 1250 743497823 743497837
    0x80c210a0b1201150b1b0a14060a05062d3a020315040c0815070f020a0c0509150607210f0206010e040f1b0608070201060e040f140307111005 62
    0x4151413500603c1400300306001031130300a0004082da000c0c40c44d180805418025400001c4850400001e40180e41d55020007140750880382002041055040110001d0003095040c04900314982864948190700241c115020080c0340000d0b140c0c000c103a500c0c1400e4216402c01c00007004c2d450340344011030303885890302c038024040269001e0700409281041d1003291040000c000c100300d591228003034003c07800d4081405007183d165072184000c407540c20448005030a5a00d8508000300310b41c44406400c1c0800e0030000c02200705c40c415104400c3c2920340046482403120002645a044080014620200112071001383d91000c81c08403012503544201e141240c00f00030090008006030b00000060010f184c4c1400c115420030b100c1c480004e0445001d80d61943c180091001400300d1700e03104c403070070041990050b0039254032140034402000281d06200c46e0410000c030140010b0135441c20a4414410404400601041c2040e0751342165101ea0745441c0180301102200340031401044204c88001c03000d4001c1c0140d60903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 743500323 1250 743499073 743499101
    0x1003020c0304090b0a080a0305030402040605010c031209061b090314030906190e0d031206150f0e0303070c0b0a0215010b0d18020907020703050616080c210a0b1201 72
    0xb800b80780c03220043c041c203c2c203440c981d800501010001140070b420055844d001d440713625415200c2c609401008115000e541c4090305000715881d4880c0020740c092502180160b20203000258581c5504080e00101000b5045111107503000141400740c035002103186c012030388916402c02c129150040000e480c0e0007010a42900700806001e0641c5801100046986035140d03450a1411002c900c0c000444401c1c17204425000710760941070308a01100035000c2c14002d4a00300c440c00301102c5030190020f120f03145c100401d4007040141450074190b640d003442268a1650004803c0410a481e40301c1c4079090380c403230b0b540e03d00940f103094040c208540c0d08012150484000581403400d0000c6c20705084060101182f01e824034085900c4402c0040e95403100d400e00518566004240343c50035450810301c0d08201810607002061078541c064031290f0721a861660040c1d200d50380036102c5c00d103000304402500140320087c50407000541008600b54140c0c6c0800c0c45402d0403110042403118541c2c0c050300300c031000a81c030a4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 743501573 1250 743500323 743500327
    0x11505060f0a020307021c11010f02060a0e01060b0a08091903022116110406060824120601080c0127030303112215080f07080a1e05061003020c03 64
    0x105488401501e0b0b1002540143c0c1d2030511141e0000f40705400034001c0c3d10107043d1031503002060001108040c030080000382040f14001406400180d507400c4e00805015440381c42d0421142110401c0d000417004210403d0300c661601c04282001e000c5100407603043c4114482c1040fa001d2000600c0b00384100e0303d806401418100002070000001000800e0201d07101c01c0c01005220440e0541c10301d0030703040c2d500030304d17007069288010340400055942e140d014404200911081c05421148a03500203d100b02c804203248030a4040004218420550b800c0340184d40601000050000d001084413281d400090340c0d10808a5400300c28285a1600000003295181c4070b03200034400a406035002c544103400c041500c2d810040343d044c8103a194031080702802100c3e400b084042281d142100c4000e40c81c1030044c200760000345006103d1001c203030030040c41a01000038680200e010b07217450f41c4c02500c010089808454071740e65404488006414161581c038003418040701d001020038428800c0d2a4803a6044001e54 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 743502823 1250 743501573 743501587
    0x10090b07080a0908030318060a0b0114090d020d110f0907200709062d05060322020a120b090102030709120204020909040c140a050114130e09030c01150506 68
    0x5040c2e00414100002e00c94612408254420100b0185110304a080074400560000a003403a041a102070120702e289030038580880007581c0c2001080d1454481ca8550ba9150440e41c000581c0c291944c80d4060b4100d0f514035004428007a041362803401c2e0740030507a10101c408040c05e00f8001d60401c2280d518001400d00101c4021918066540014031903000c000c079420ba548130040c0c1070868030140c0c01148075100c0d0049041502e01c10310048103035224100c20600e8680d2134000413800c7c0784001411845546002c02c400c0d4a4021b1008026040305e0f006401321020684644900c0e800e0f200460040c1c0c0c24001c4580002ca01c441c1c14001c0f603106441c03d40c2e0301c840031481c0c903585807900d800a0350f0880e8020340a020860503a15940d03031861060380a000b484c03540500c0c4c400950320f140742148403903000e135a800400748101e9812070b002d10700d40c05103662007079502d81f150008000031256503040307501003030000c0003071003601c0d02c0000c0030741500000b1600802049803007150751f0760105490300c20240c00903070a1000d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 743504073 1250 743502823 743502833
    0x60f0904050403020f12070c050d0503070f050304120b09190c090b0f030607090608100b1e09030106091e06030c030807140115091a090406200f070210090b07 69
    0x1464200f40720f40103d8502513485841c0a040407800010700010b0b203004155801400f20300209034000700030581d503d2501740c0454a0303894482c411200068007244102003202e040042c20400c8800500c1000003010700400b16180454581c20181c0c0c1d200c40ca0312480c90410340406018594400380d0768407603c07641d40316280c842104090001d0100c9240d1261108100b05d402e0b40301403001511403070055582c840c081e8100840a450b038500940242039210400d64248008900c8604880490400394840324040c005058107000c03074443c509001d5095402c004000803040301b20342066500000100e400b9400308500c980341802c0b90010700c400b5183c0002528208042840c010041c806a070182030604a00910100005d080d00c035441640040d038a41c5500c200602d0030b09211700d88940c6001403200070003204200000b1556140070308040d1103e940e03141d5443c0804c817440c051444a0b807040d031205031610701d00e0403200ca003604580000ea00505101002840440c82103000c50b05441e0369000709420050b8a8840c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 743505323 1250 743504073 743504081
    0x12c15040c0e150a02150903071b090905100f151502150f09100203010320030106080a03080a140112030305060f0405040f1403040b07030c050a08070b0411060f0904 72
    0xe50a2001c1c10307485610540350203e501c61100d840f4001c4030303942c0004040091070010b01d0000008280b4414050001e40f0b05c020040703810858101d0f1903001d8446403608480c4107554103500001c015072401c52071004100703010483d0112001c5040c000c1094042a4031050705452905c0808051a460780009000701810140c1d506800718403441250020034551031921308401c016616507030108406420061521420000d061403012001d40942c04c552450b81c880c101c200300300d40385000608440040c2402500c0c2580200d0082040d442260300f928114207010301090750545581800900f4010040c0c06015041714142c1281d4030030028042c44c5040f500c0403002000301070001a070101400107140760580e900d0045600560007100550810400e903e0708a600e40140068031146410a11080003600c02403420307102e245804d82001c1c3c0c4900c07004d2501d0f0342808901c00d001070080601007003210902c2a0b5151481c40b40c0d201b03800702402c0030704201c100050b600568031503402400042180146504007a08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 743506573 1250 743505323 743505341
    0xc010905011404090617010f140402090912040b04061107050d031d0301020301090209100828020f041e0914061e03101a0409021c0812012c1504 63
    0x782d0350304054450003d90141e4105a0159103804554060003c40c00020706c1400b02186921348204800c410b500d40108000400030006031044030b60500081c80c90506102c0c4070040c02000360306682e031340d88400304203095030024002c90000504442d6034030014034001408405480c0010704c011111580c0d91341c101c8607060301100324000c1d401d1209c21010582c5090004d54041c1c12058030160311940c0340740910850194070110241000340c100180103a01d407503170840c1c1140c207032403683c1840000000c0301800064030440112004141000400041c0c59483c600754000c204060181c6420711a44ca41130714043e030303a1200750350009508440110b211841c0500d41c9446182c04a074202c818040d103200040d060484d124103940005491b0404190884d14450900c001c840049030100006100f40c0c0103e2801081070030b41150700740440203e601485580006e80c1c410304107100710780d181e540e102c1c039020499590010040f0400100054000483c80740080c0d0760388100c1c0a20284841800c0781400c200c06081082 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 743507823 1250 743506573 743506607
    0x30b27070504173306090a0b0604170724200102070c0515041a0a0315170709050c0a0309080c0307110a0602030406120b0102070f09050412020c01090501 67
    0x4000f48542c00c000b40040703003603410400340c24030009080c0038568296200c0440400b001880e1a02d44101841a0f81c0681028080d40c104845940d4444504001d0035071074046c41d40464040790000346148400034251011800d503043e04d00d05070b03a5414001400a2030b41d1100a10b0000309640a095403180a19501104c0da050f40c001014800c2e6180a0899101000641d600d4070406014040c6040c003515202404008c0f05415107040e1038503c4c00b00080c003c5a8583d0400040050081c003030034825001080032031031006203104540c1c0c0d980b84c4c0d06124401a5101c9465002d0144d0025800459204d020f104400380b20000c2c1c82c1c003100c0b0008500900e412401105c0520080c004d00700449001c00c05090503600c54100420811920f02c20000011210360000e01154070030002403207402d5100d12011790741201d040c000305040344c440e00141c0c1041030329048007030283c2c0704076030005481c011904401e00640c021012a1104550410204d8440e01181038540c0401d0384004204141d511079000c0349100c1c1080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 743509073 1250 743507823 743507827
    0xc2d0a03080c010b03160510030f0e010e0d02010b1c03050304060e0f010c090b0703020309190b0a2105060906011206080f0c030d0302031311040e0609030a030b270705 73
    0x3640c03044501e0300001e80801c0c0c5695a80b22541e0603080803c051031a10700301d0705040c02074a00c7c010008a0266801c1c404008040d00d4100300c0c440c0000c3d2307401180042c0806402400001007800030b59581d8101806444015030920322408514244910403d400f820401c000139941c24440c3c80584455001034401c55900341c1e01c0d00211107805c1c05203da40320700c104450010a03010128200100f002489401c0708800320020020b480c0060f4000086540070b2005641d51241240040041ca100c3c4900c1d84c0681c48480c00024030781189503110180ca258a1440d188050340700740d1072402c5034119001160340f0740e084550500422201c1d80560782c450302e800001400456000e446000c130324203081d104448558264403695034481c0e245010302191010070031030303d42103041d4a09540340540d000b959140292803141c0079804020141c8890f00500501d4100004580150525030344450b41e80d44680d0071940080d117005441056440c04a1040890781102da0718040191414072030505084009800b02040c0181 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 743510323 1250 743509073 743509079
    0x30803130503070b040c060f08090c09090307120504030b010b070213180618030f140304060207031412060406060504030203151f090509060f2205100207050c030c2d0a 73
    0xc05003049100741d11039060900d00300e1400c21f02401407502c0e40c2c031210900c90307280c0070003603200000126205007603022174910f20301d51141c41e20103086114a040c040c03c000198a020362421390844001e00460b486500018981da82e16202c035041c5d0300601c20020350059501c035115814200540001c161061a0b00141c0d001002c19940c0c5030881380400c58101c441c0030b802c040380d82070680201007440030461034186440044c0032001d024080d4440100300501c000e07400700300d400c1810300c512a00c50380a80c007401c80c80c0d594007031526801b00340e201c00c461491040b408d21801140862045080d00c003241e038054000d1883c0e0b8184990100868802000c0b0040d404540407031826080c4140703182c3d0010421881c001403a810304035109030034010300520300e0007480344000900071107980401e402010840e619503e80c0c2400c03c0f615006090a070b107056035002e01d6001041580c00d020020800d4007046c02e040f0110368942d1100802e0224030140b1480750100341c2403650105454011452a11918460042880f00b60302d80f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 743511573 1250 743510323 743510333
    0x220305150a1e0f050a0b0a031205071a06030c120c0f04020f041205070915090c1e1701120b06060724020301170c0a140613090c081003080313050307 65
    0x1802958240c111521842216050070040c070601703411820911040c0203c00030440440d420441d41c0c0b00c02032000300704031070b660b1849102e001566091940b1a605171040070a042c007201c2c0b0b141c1d060307a42a108ac0a103500405e66490009000c4507422892006098201090f00800498044008446400076000c00020f034258000c0801000a000580300c1c8800130121810414900341103500300d070550b50b1400c1482810000c502e6840b008071208130201140b0451a60cc0450300107109a0040d21203150440c10a01c5071a0860301940c0c0e40c08042040803841d0703903110301c1400e0344803000001420754007540300844d166003041402000c16900503024881c070364034040042c000c4000000c0004c10142da020005011f00d034032640044c03604148076401000c40c08940d40000313114600310b11580d0401c8002c1c039100c0c3d5071510346406407940b001c403401c004900c59560b02074880140500004c00c00004643d000001c44e60032030408080280c0703030400c040350b003075a8441c60030100e07038111302c2c5055400d131006020b0a40094 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 743512823 1250 743511573 743511611
    0xf0102070801091a090102040302030a150e0f1c0216090e07030f080409060e1b0a02010b0904060203010f0e01080c0105090d350708030a090201110d0302220305150a 72
    0x3604c0b0302441c040680c0d1402d40000d80110107424103030380d039004010400c003580e800100c010354590400010581c8181540b8107000030500c3e058035107010701a5040b2143d14080102d0760380d858100140034944001c50a0b242240c450030201c030f14204000100e90140000306d00343d1303c000c400f140f1000c21101d07155183e8a070301000f503080c000c08480740300000400b48006c01d114020310000300600d0000c28075030304040b0310101c00981d110b01d520007045004125500010f10035048410010005440089182000d04008000e54002d0160030051714500e100043c007403054900003412102030340d014000e00154038004441591280708100e40c0840103c80100c00b16043c2002c00300c01c0da0700e04000b0034040d22108a01c0c044013503041b0038a60744817400d001801c041030804084076442001c004000800d80c816100603100d00855010018291041060320a0791682548c02482c0c0100c500609440f10102e07411700500e00d8130203001c0100b8540184028065030480b00b20000c0e045103c4200100307981641260100540f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 743514073 1250 743512823 743512841
    0x31204090207050d17061e040c0203181206010b0706110c010e06060420090301020d020a1706091b0a200a0b0618041709060a09150207140f0102070801 66
    0x10560002d078040421200308504000100710f41804c4030b00540c1e0b0038140710004402030019008040b0283c01854000310251181410f0000501c10002d0b13501d41c140007990790700b10f00391345481c3d60b04a04600710386140030710800f5000d0030b0060082405070b0a110380441c2c0c03a001103500b1a041038882d03007203a540d01181005003080c0c0c040c00c400020703d4980e440e020b40c90700002811582c000e510b0141d160301d00c00e00740400d10800d100b0100c0e02c659181c0301c460110340203100b02148000c86520101d1481f11061348042215404c40da44e0b4105541c948441d03041009914080d1818404484071000410300002d100c005001c8155043c182510340c03101d40c0110002001521800d10401d070014a0250100320b00000000d801841c10b8910f080d0009500c503504494900251016089d802c1d40b00c1d4511030006400300322808010b000d0180358541e80141005840100c09005426040000030a020784007171001a018041302c071a10134443c20383d101c2c44c09201642100004c0d160450080d0240460021424001c80043c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 743515323 1250 743514073 743514089
    0x120c030403080a0b03100b0307090c05370e010c1a07120e0a1e0c030c0302040f15050111030c1b010206070f0905090a02090d060e240411031204 63
    0x600e24040c0740090407000000d06844915150600c2900c3c0c80d180015214010354120900040204680e4002450071071680d01c03000190781404c40c0b1841c81d9074803901800081e070200740b0350680000c419072290f49805501d20064040d1071000150010207103d1103180704c0c03445042c1020410030a641e21010034119000e5160b00303110300101c040c8030407244c0c02424902000700349a010041000848111a20342e1603610300940600704103203200f882e042c5940c0101e07a40e80d42c081c400085040c0c1da40381c4a040f04c089071205a00c16840c00444071155051406900300c400070244024035003074100401500c6451030001103901d42d10080c456010b62060130080004d044040d540311000e1101502c00080c074103c8014000410880c1208400750703080d40102450091743c008450614a40d40d40c8601c0070004e00489066590041c88011048140300070b03a400050485110b44c182e800e04e48803600d5104038040780d0440b025140301841c2c00240030401d604c66581b41c140f801400e071504603001000407546138116401940d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 743516573 1250 743515323 743515327
    0x4090804030f1406010f0b03160306050904061506091223030a020303011a070308010918080403080c211b0a021906080a1a01030917031006090f050d0f08120c 69
    0x10f034a0200300405401404010b403450034650603c000d83c40396000207007800b03c0e2030b410b0303410707021405009401410190030040c15541c501c2c60030742012406000e07201a0b031450429a090041003a0b07201300b40d64800c3da00c1d114003620188526540d1000e100d0034070001c40d0780340e03103030503d41c0d01300c4240c140000c040540507540156125410500c8070400010300e10071213050100104640700000303402035038490444d18080710014942d90711100c0520301c041c0d02000280407060014010003040100806080c0032100d840c02c5030302c01c0352504100c0c00d400050700079003240500c0a111102c0504e0101c040302030308140c12401d85a4140807903002c144810f04002c2902c3e40343c041c401d01841425808814a580320800c0c0c03505100180642120390304550b4030402c11810182c907088110300f0f00c0366040b400b1039181000c2012941d0791030010b20300c5500329180c0c01180c0010744c21034000a031325840742c060342054440003003a114002d12542da40c801c80481d00300086450304400d2241c44030300d0090103a00e40c0f00d41c420181d0a5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 743517823 1250 743516573 743516603
    0xe010807060e120c15041403071a07050a050a08070636020d06050901090b130f030c11090108060613090c060e01172d101e080613020f0d030c0204090804030f 69
    0x1d00201c40d41507e403070095109501c00c22010070030502030491612022403260350f50000d4145a814400c880744050500c1c440c400f0758500700600030005110050041c2402c102c000481210704108130843c4080e90303541e4071255403104401589103041c0004a200038803130300301e4003120342e604000d544080321400c405035502d0392004280011600e4250380402c0030001c840b0f110070f40782c0c2e542200c96000030313005d010070905003840c90801481415000210300004c002c0e100c1581c3d00c581483e5507490880f501c03401243c200c41ea15440300c07864000d40200942c41045084078134140b2000312490100c1d0b10440c0e0411110b450380c0c940c5c15591032026805003a029407401c101180980d4440c41c030315100c2c00000081001441001022014400c07605d081c1c2d540c400c4103e0444944503a041c141d03400c10b4000e05814007422040c01400c82c2c4901d48905900d100752449010501640c0c10003011208004010b070225030544640401803902d03074050380c282441800c0c1c0d10300b4036441745c50340101c0c1c0d0b860000c00c890407442440e240d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 743519073 1250 743517823 743517839
    0x5120a2a0801060311060310150302040e040f1b0302060301030803060303040b0f0409200a030f23090c0312030109090201030f0c0324080c0105070c08160e010807060e120c1504 77
    0x1105c00140c15a015859401d1001d02028083e500344a083ca03d110312205c1d105449210790100c0b00109000c00d03003142142812b040000b6909640700048a40d0400b8030000c01000500322a240202d0760010078071400c580c85c580b120405a44000c0c07095605010030800401d5072207540303028020178180038030002d0f211380c10004641c0484d803c0008103410305002041d2907041582d424100c4001103550b141c04962030801c81c234004007400240034015907102000000740c55408450f800b46215502803021550103520000500d1b840301c03107212010b01d80751000c0006121001c00f54122420080c03062400103459032006034244120303441c801c40880000d458003181108a15030f4104100ca4280f1002e82c03040c000d1038003542e1039030b0f80c15001140b4140003000c01c80c2401d100c0407001420043ca182002e03a1182000880c800091501074003411a29114200000c0303560344002a42406480c0b00f40c69052804020600b08030b010001000c4100c442d00c14804146680c0c0c980a50b551204003140c0990b036241c9050410b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 743520323 1250 743519073 743519093
    0x109020607080c0c0f0a091e020c010c14030601080402013506010e040b01020318040906090803180d020d120213170f0f06070806030304120f02040605120a2a08010603 73
    0x54180318050b9880103844a65170055103200712034141a00140f4003080041e008c0031104814a0042c1091004c0f800c4081100190890114840c0e00d0b900c3c1c080301010002c400e000c07400140d03240350004000380d0000c1d00650042c080e24141c0c01c01078070440d200780c840620528810700c418468181c052205401d00140d07580003441059244401c03242881540943c0c00000c0d5a409101101402540d017011004040e484960062200740c0d0000d800340001c106a0400d001c0e50362007503a41d6020b03000c4e4911035840f0250082650003507255658040c1594280e2407408682c00341c103050f00403c10356400c200e11064641d1520402c1e005012003a26201240580442c3c1c85c20650300f15810012900480648800001e000ca0341d95400666801d04aa807500d81001080c03640c0110382010008a80100c814810700c00e406244054442c400c90302804095280c0040c4000000800301492440d446409918006154001410603411003422000c440190303000840b9440389a660155840da5035880e000d00504c048002c07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 743521573 1250 743520323 743520343
    0x50c0c030a0c06110c06150d06020408010b0a0e0f13060b13091211070b0a09050d05060a0b121b2805100f02070902090a0b0f03090c090702120c0109020607080c 70
    0xc095040c448117000c12600d64000410301813150100b080e21810580c2c5280c0034a2445030055021501c0719107445400c3d000b041d5802c041e602c0f034030201d40c0000d0318500c0c1d064040e110324a0700755081040c1d101c80303039000260001020101d82c0035441d209551034170389880c800d008178112002c901040359603103130a12a1451000034820703401c101c2d2120414490703003000100e000455810384c0c0140d030307030714040340b4101c0310b94034581c105a070700121a84a00041c03180001c0c0b0940642100340003001084400f01c10000d00a0b0580a03202203a00014070000040f550b18005001c030324400f8010368a10002030482c1180321042114840c50041c148109004500700207c80044040190601c0002d440da01140a0f5030340d0668414080d055800160210716910703196001002000b00e4000252144030b000a011102e40084461203c3c6205920f00d55000e4685030040134010815600685030610b0a2100550558000840046599224050300700103031201c1c001458540d000d88030070745d20b41c815034600d14200030b0750403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 743522823 1250 743521573 743521601
    0x111c02070212030c0714060403050f1b060703080f06130c03090501050c04030b010512101b02101b0c0c151e030b06031315061424040306050c0c030a0c06 67
    0x813007061100d18000030070b0015154071070481d0401414850001d2060311503504010414000c5a01480030403100040d10002d405107944140101c446070410700c0028018124080c0c006907840021507070640c50b080055410440141070342c00e094034080c96090540b400b01d400d000000303a40b0116a4140f0030300707115040d004440c540c4070624280c61600e03190760140042c055280306040c000b0040c03440e0181008030541c01c0107241404e01c41800d07a100d00d26008002c468161026000ea840c2902c403094240c410481c108442094000c130000104900300d42c02031f0890003c40b68807244003004100201d90000000083c02580d460f001035004118a00e4000400301392250185410140c07400c610796124801e5070341c44180c0d0110340c1002041030400d07400510341c0c4c0c015114607030316000f004210514a540d0244041c441505c80401c0140f00e0454500e0055000b010740c100d28001388018000602c10303812980c2c0000c1c401802d0750624028452890665001c0940c0002282d203400c481800c002c400c0c002e1200c0c1031039003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 743524073 1250 743522823 743522827
    0x180f030e1323091c3609050a1104140a0e15010c03030f050f070327061a09010b03041109010b0a0c061b05030108010f020a02030d111c0207021203 64
    0x40b1881081e040d800008049401c0b1071a4001100380c0003c2161074000307208540c20340e078130107071569010303012480c8810b8400180d020060750180c0c20550006028010310702044030f1501d00d141013018401440e001e82a042c0301c0742c6a40002146040b802c3c090000b8008250001500c004a81d04000b490f2901740e10150085d6401d00422484050020000d00818400c1c01c0c1001003c2d43c5290840003820103214220401c3e20302028000c0d4034001481c030902c00d6146480c10020f400103801609c10002460302031505180a0500f1000000c840343c00c02c0900c10200c244c031008070b5090708000788003820240c01a074501c8802100700014000c82024203032242c1c100717440c900007a505195203201184500e84a281c1807140180f818000c000e0320703500804001069221907016041884001441540300b0301c5445505d609112105180483c5842100c840100c260000c502e407142180308040a40030300040155050014400d01030400155040307000c0c000e00c11000180d5542d003a10400949034501095205181c2c42 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 743525179 1106 743524073 743524091
    0x6010311041409060a0f0b0f0f120a0f051009020c070801020406110609010c05030423071d0912160c0306090506101413180f030e13 58
    0x200c1c0d90038480e13121002080f81000490207480314480c03041d10100258000c55006110303903090102420f01b40302040300c6d8548503401112080107100c044204110014845102e280c0014294130410042400c0840000b11085c1c03075800b50003102580050000380c40001003021030300030130340c0344029036031030391284030003400358041e00c00fa400c0d9131040c40045548910306005d86566601c07195250b45c04c648d6076884945034604040c10b03040680a41801518441030288505030140100041325100480d402e401242d0440c5c00800b0b054168114500240401c1c20140c1140c0c0d6980e40711900c9095080d642c1001c4a208034541c4c0005c0c074140c0340a400c070040120100f4030a1140b4040407440280036551420700120000050595a01943c0c800100951783c80e203a0208031444400813800b43d2040344d0fa5102d2918052420041c0c0100d022400c4c910074034500900551800e20f0f07030340c10a11100f58 = true := by decide +kernel

theorem cover : BRFrame.Cov 743345323 743525179 := by
  have h0 := BRFrame.cov_init 743345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 743345323 ≤ n) (h2 : n < 743525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
