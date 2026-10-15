-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4390
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:27:58.418789+00:00
-- url     : https://prove2.me/submissions/46278cf3-6d66-4e6f-8ee3-f61818cbd22d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 789388489 ≤ n < 789568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 789389739 1250 789388489 789388499
    0x60f020f070206030a0b04050c04090b18071404030c0e09100b03060708041a0c04091a0a050f0a080624010507020f0f03100f0b04240e07051c0b09010609 67
    0x1040c041c445000344159008400a440000140d00c40c010001d0000c0c414025400e003101150301039400b900518500608000f0781c0d10003403c081d1040248410040175403203144d50350f941e040f9400c05624241c00d038406001c00000000c03c0c04494020082c1c040100c4961540c24145925032500c480504011500d0f414034a20600594010449980c07090306400e00b07034020754642ca0300c4040540320404034100003960078140a0042c4a00c1c0280081d01c0c5040e0041000a1269211300d07080007581072901d6009411140a00039401e10b1001125140c3c006001c045c10252104509414000e04541c01c4400c515901000e0000381e18428000034450002c2c240b140c50000d0940100b80f002058111031b9004a4035207011782100d0f01d003048511104500e071401001842c41075055031020300a1604028440c6040c2004d0075010303001c41603103d800e411054800b2240c10715141880282c110001c03c00030510074240075100000e0f55502c0f4402600c6040c800000c0c4070400b542c20011801411b0704003204204401d542440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 789390989 1250 789389739 789389767
    0xb04051003081215130516110604060207032a1101030207151a0315040b1005010503070e040b0405040f061b0203090d06090501020f0712032306030a140a060f02 70
    0x20411940d50034851807640c81c2d800c1c002d064244c1c400d0b4240c02203507070004450054a036503c0b850050441e480002003c00c014042190806082ca00381c80c950703040640460001146940240340d06031181c2007220b1110125454009150715a00d5403c0345904900405410030000101110703030210242011801e10000391501c4040c00c49105100048070782d14408441c1044105040d81c040140c0181143e258002c4075107089070154040c3c40c00c5400003031090214264070410f05215080c0d031810b9440c542140d58844084450070031101c00c0b150400d81e1081600103075280d170b002e002d220394056001c9020352905e61901d07900301d5030b0f031900d00540480b52076612406a9404412a510070034212031118400c0000e0815800900c05003d000745190701c0043c01d0100b1000010184c0320540c050200e01c2c1c82c20781c2807079054007a42c00340c11101c210f4064038040c0d00700065440318240e07040340000d001c8503031141056030345190542c204511f0070400d9001140903800c020481c05940c401c050b030000709504186802c40c1900c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 789392239 1250 789390989 789390997
    0xe16081b1305010b1b150a15080111120a0e030307081801090f020907020d321201061b0812190908090316140d141204030b010e0f0117010605060309010b0405100308 72
    0x10701b4030323403a107905603048074454844a02a01c0690000c008102050544403d00e03440400007030441440c610000310709000d24031440d407a00307010034091491984c41d40c0c011648900002c202060304041c500c0c4c101c500c09024410030b2560791180400c00401d483d2030040128540c0001d0500045501c200b000c6032449500c403064180c1e1044483e540d1040403481c0e05107440d9200c2d00d88000c0c500c2100451854482c4a84800482c103c40c40741c1c5400a8152038103440541504440d440541a40e00030000149040f880d81c6505910185100c11380461540c0b9030240300c00da420740e813400e889210020950706403034a01417003102410702c0c0030301c10403d5051400e10f003400c52504041d03105109220304290401070210700f0f180c005000d0b207100309407141d00e00f00100100e09a007042c0000d603200b0700c2c51000480d07480c001100b03641c0102034070560b29526038a400f141d0164a103101040c0c1100755201d0300e00050a4a483d005140904010800440c03000b5000c0e06200442e0001050041c045902410800100d00880219 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 789393489 1250 789392239 789392251
    0x91e050a0209070e040e1c140a080a0f090302010603021f0909050403091e0602060a020c190302192109061202070606180e16081b1305010b1b15 63
    0x20390b007036850001c1907070030fa10381e0804030f5081410400d48000090001c600c0c0400c2401d000152220381d2002142111030f861410305c0700a20480810940385a5070181d8034540d40078640c40340229410003109072103002d503100f440040380503030b440e00c01c28002c6140014000e4a20000d01c9400d0100001c20744004150440c1440703481280c0707580d0b40c081404c0c541f0030403124014185006542070130b00405114010840b00c0303442104014010980400c030411418000c54107041a00d0009119043c0d800b200c41c82039041da031804078194410f01c001c44e103074011410202085540034110310107134449020318450449000c4c52410042040000f024450aa001010011404114400107071540f4444c42d24500078403603900610074208285e0f840944c2040b458000c410541041802ea03070003900000440040d405450103203107042e4004e0010031b1666090b19010454501008250f13000703440043d900f04007194000c0e08005802c1301d0016401c59140c07520000d4050000448008045a80a01da40151503000203410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 789394739 1250 789393489 789393499
    0x303060a360e0303040b0703050a020403020d1b210302010e07080a0b10030602120a0b030f030418020f04060e100203180603070203091207090c0c0506010b160c0603091e050a02 77
    0xa0700850031050b80003100211464088030307a0b03030805007003510f03422100700c0c0ca100020b0700701400156941018001d403000c40c2e90190a41d41d10300941c0d650254118540b20090345d60114030070001402c04541e145014000c2911103c810049032281402800e40e901c46103000703102d40c40080204040d010000d081e41702c40303421845001c229110582e40c102498502c3c0c0c0098001030020034042305130001004868003442100004101c4201a04103068030341420300452079042c1c00c203100c100940d14201005d0344641e41d02d07901c0185031050f003220171a115006504804000703a404c034544001030030610b00a5a4414050005504000b88442c044940200501011340100008004a04550300030000e45200100040c511580d0b0700300010b080341c0d50308c040e1003640016400c11401e940c0302e601074030583c5451070b04040076011680c20510407130074660140240720f0701c0000b00c105d188085402101340030702500c0156400f142540707c5041001c0c03480d81103041417607014001010040096000078001d10303050740c140d503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 789395989 1250 789394739 789394829
    0x70b09060d020a02031c1811120a0803090d090b0906090f03012d0c1b020f0901150e010504060e1324150c0b0f22050303060a 55
    0x22906900640d4107400c025400800c03860b0700e550700400504648204000020941c520900031a000d5030b51008408540014125228001c510004034841800d1400303082c0086600380e0703007007180c58960318080039602a50080240062500d06008801c0e200550340750111525003007181084040c814403802d10311904002503a00144d84482054219949000b0000c110340061070200e0440102c1100b07003545141e2060341c00701c2091510744160340d40988140e90381d0040a000d03122610180074400c100380d07404001440c1421040e0341ea0540b16001e001e000d800b034914034030240c901802d82482111501e042c0a0300703010500c10203520106140e8400d100b180d90000d55240604030310300900c00d0072041120504422010b44c80108a03103458001c4510440011107210f18a040443e03034541c080c140102040c0d010401300c0d04142144001a41080c030340f1800012100646080c2c0c00c50300340d8900212043d0f0408070800c803042c030b452072580005118a0841450710011120a0311085030020156124058442 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 789397239 1250 789395989 789396007
    0x6060f091d03190e0a0b0f0c0c01051c09080408030304050a03030c08010e0a021b070801061d010e010b0d180308070e01080403140a020f0a0317010b090a0323070603060521070b 77
    0x1076040f4004c11200328016a1600c960442034019440344100078083c2c8981d827103200c0e09501c10b008031600000e44088641e1080d42081c0c40002a00b0210f5003540d12041c24040801c2da507a0910080d80224450310060103c40041d2801400359503107901e40320244485100108140c005c071030078cd242d01111600b8016a00c0d0480d403405040d2310041400010b180c4116440402c20b16130560009090f1100041308a651180305048420102c60901420300705050b5000100f2000c030003507002d0b02402e8440708010032282802480e807003142c04088001d03000500030405000700f242d007040d4003005110083c030384a6210b181507180600191a00d400c401034285000803d41d0610f8400e000091520701380c2c8081c2c5800c80c809080040288881c0860b80104410303540000075181e443c042103a541400283c07e00050503d5515058442c0070700960401c40d540000f140d00054100505c00c18002d054a45c81c00203415041c1014402c4200e01c2c61b505099082200d10740122800002a1a0046501c1045055640c0b4414 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 789398489 1250 789397239 789397249
    0xd03240b1801031506022a0d0201030207080d0f150e040b07110a1403190c032316050706030f14180322061d061606060f091d03190e 58
    0x325984024003040110017041c0d03580c1c0440c4055102c4d200740f814080d2148100c0040310049040c01d00d9645c02006000307800d005500a4001d1f10341c0602407030025082102c503074404000c1d42c04105501d00c20795070701c00c01a200420001d4138500132b8000d4800703040e003600e01651800038a80001d00000203000140f101030031400000c101007401d060703102c1c1e00c19000c840701c068800e03540c0c2c0000c030240141384410448000014400e50300501819050303550a40d548207865007200a5003502d014040601c0b5042018407500d034445451307214000d10403402490700901d40103004089407906070b0132005032810030015000d4404000941504070850045071207410102484443c03543c8201340b40500007031410101c602502c2c0249245c0001c4035040d441d202d20340b1800e1581e81000f80505407403964442018401d80c02c4a0075400810786c92144203c10000d9480e0b110601d07000a5006940110140b030f0b141c0c0000111080b1070880414000f0011000b9403e28012802401d503102c02a6650f400304880c1e400803c850f6130fa1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 789399739 1250 789398489 789398501
    0x120e0c04050c0f070f050607020a0203060c0a1701030516050301060b1e0d1d070e07050409022a0705040b060412031d0d0605061f050a0318050d03240b180103 69
    0x700c400d103135a8080c1854500c00302d5555801c16a000c0c010080050400c50022400e000f01b1070b0300038086c01c4e00d5500c0c28408410344d0001807840082003c011440c0c000f061343c02e01100d01a5010344018040051040340481040d0095044180640d0500348204102840c0c0400d6401d220403040b030030400107104241718120303802200300024031a800c007250110406003100b501000103810354103071420241c41e0511005644003d54604001030002c000800000000b68054070201c0e01003851003110205c1120410310f0180d0481e4034103082c1e04031000c100800d04c0c2c0344c410101c0903841558028141481e040700c0c21844141c141014040c41288000c0c01101404460710b004c41c0000140070704a88072541c00c11034020801282c0c468001e42005c00f0a0790651000780c08005510707020340d02c0919002203800203c01a002a1001400407901e4500a2001a4040c084445400c031f480c0e80008440041c0000d04804000e17106600b424024441818844a42ca1904881401500c02142600c0648a800490003006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 789400989 1250 789399739 789399757
    0x1020d06033c0212010b0307080d0e0307080c09070507060227011e0f02070512012a0504121106281706130905070f0501120e0c04050c 59
    0x3150150110030441c400340d660600040164040b2030903961950792218504504289610201d450b1101200601d044080b440a018140303002181e0801d0300d0020925003503040d0000d1580d0b4000304074203101140e1218008040751000c42c0241225071500c2c41240e1110508200315000700031b0200061803003401f5100b1074040c5a801001155a030040321411601000124204001240d50030404481503210b050b00c0300e4000e0030050070000300d5550070400d60300c02070101059402e40c01240c000240c240c2c2e645160756104207500f000461202840c0303210f11030f110300da000c6190480a8a006006582d980700003079406941000c00703019405155400c0544403003100301c1c030082d84210000390b0900c100700c00000b195641025540c3c41c108121090701c1c10b5480310b00c0f0240102d80d4810b2000000e600d464850154002c410440304006030551280d00c030142400900d410000d5406a502c10400103541d008100d0045004078440800c084800c100c80760381c13106c0312104964480c40c0c83d0000316411005078011192800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 789402239 1250 789400989 789400991
    0x2103040b0409061401031436060108071205030a14040902210c0301050d24090302150601050a051206040b1f031103280e060709180b010e04020c01020d 66
    0x81c2d990782000d000c2d0200d0b000d142c1040e03480b40400003682d40203005007000404032401c00291035640b80200c80b400d401c0d403c590340c4242e42e4580340c603094017800c0680030305007204880940025810b15520300d04e031240c00d60050303407164503510014000c69800300690301e180c101ca28100c207800a0301801a15030380125040102c1080c40001c051058050b4010600d1005181c000c08021590310b005890446010903c075854104d40451001000500c66002c001590310304803000b282c01e030709200314000c111001100d0880240c1d0010b81784404940130703040007580c003900c00d280041ca40400564000e004e80036072101c501d00e190840d8040384042d40c59401803011194041c1c20f442d8081b21000c101d42188603c5644440420310f4011004141d65201040300d12a08510445030001520400380740d96200c40c0c401070120881d6038844604500e07106004242c0900c089507070307000001e805c01c25001c40020044a00b44211341c9054000c81c03191341c02a0a544882c18112401600c1c0c06003240301c64064071494071041005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 789403489 1250 789402239 789402247
    0x13050a1203020a08070801140409030203040b0d020406020f06090a030305280b01090f0308040e0402061605010203040b0601020307030207050111030408060a060305120304080301180b04020c01090303050603010b2103040b 96
    0x7030341603000c0c105010156071042071980b00c040d030540316013000b8054103103094001c01a1038404c0c100360f0000c1c91624800d00c1103a14041c0c2d01c0b007141803c2c0c0c201d2015602e21a800240070000c450341000b42445400f101c0300035211500309001115910315040c100242450b4580000a00900c12004500948a51840c1034210704008080080042011610140c085510b0000106840d01c0c5008204140d80c0d01441141c07800d1b092103030f10381e900075006104a0340290200446008003641c2031407a000107124078009a12400e25140c9170798004c200410b803c1c1194410710802c00400d900080d910704452003801d240d0f07114031000542c14210301c21a01b20041a10030b040c01c0c441c09406990000c8100c03805102506e046151740104c009482c4800e40b00684406030901c01405031400403a4402003240301c0d01d1000500e00e8103030b0041802d0342c206220704161030b591028184141a0580642c0d584503000710002c011103010000013905c102c81c0303110708241d04100048030030004001002210040c0801d00c40385516 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 789404739 1250 789403489 789403523
    0x170f06150c0109050d1115041e2109050d0506042019031407060519020c0904050d08010519031e0209011e0b04060801090903090506031905090f0613050a 67
    0x1703a5440445440006030300000000480c250200c2d4041514420a10021041d2240d0f10740042c030311120080c4240ea901040480d0000900040312660121881400700c40282903050340076010700c0343d56100c9405102c1b54006040043c8001c24035903889584003c0c410080f280080b050201c0a1003180b030241c2080c440000c40d05603c9072a44a901280e01c00c084114409a602c502ca6845030070740d1240101149050006400c4c288000d0388a42c400e000a01c1120004107a89000504501d403c1d2000d903050342000d0301d518681544400081e01400d01601d8500d020210807507038000094151201a14141c0620640c00b8221412207050205c2500240080c8055864083c40c00094280451038005400c4a80340000d541c0c80c440309a07011214991216a1240e207801b0862000e800c2d420310450400c0550800030900b95251806107002e10306103a040a9880303000b02e055021200085c2009030a54410303180704800180000e074003031b4008080013404038010031503d840da00d0b04028482c010710706446900c00c442d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 789405989 1250 789404739 789404743
    0x606170a050723010f021005151f140a030615081608060d0209070c1a09010f05010e0705092d0405070e091605041a0901170f06150c010905 61
    0x251907014009035505980c0e608100f005410884007041d14041280020001d10342c0140c3c001c6545000742d006581c0c20501c9406200220340080b6012429480c42494903030300c074200b821040e5a42e000352109080d0002011402405030904808941c0100400140d0302003018807a4000c00002c0440f10f813408034100c407411002d008024202c5248141101004800e40d90324424908280202009091411110159000e100b004c00c3e00400d0141484140d40030b1a00050181100040000701c1c1e156800701070500024250a440d686904140081c0c2050b00502124024002181d00124642007681d6546c100b00f0220b065150045042c0aa551292012001c401c1600d001c0c1c00b40b051301190100100c0e9102c00069a00b00101d1140b250031040410010c0d0020181c0d2005805042090078058205999040c01c492602c502410200000c0c001090120301940c208a042c0c041c0b102440d0001382c14540307071074200301b800c000502140c4074902440e20b0b40d4001d1000800c0310b1030661118004d200800d07030b40c00c1182d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 789407239 1250 789405989 789406003
    0x6031527100b091b090d0f05100c02070f06051605010e0304030605040c0f030312050705090a0329010e1909080d0207141b06070c051819020421060617 66
    0x740c080d403c10b0000035042c00b5035521681041c9804102281055106024445000e00c9000c003250309600008282000c91410050541a4440b410b8040359008580b10028200991940304c03a140e81c02c140030a00c1034540100c01c0d00c40c1555001e21042142c41c50b424002d0141401005080b090300000902000380800740c0c021a118902410740f003100d0b035075160340d400c2c00c00c2041d1001600040c41011041d07102d243c0380e00310680240ba141381190500702050005114141260310440d40e000c107200d03080c0c01e0850000d0100c03104000741654138000b90300d4441800254280104503100d1000080d580000c92a0f013030f03021003602600004500e45034024a03043c1d00c02580002e80944030910817460340d800705000010010064030401c2a245001c0c05000c0c144103586d004040105c5404a840f0070110b015182c40c90040c0002003a106045440d040c00c11207561601c860303801d1007003407a004010510408200c4540d0741c032802440d550030a81c1e1a51803c125000700710782c2e00199509035503080400704800740003c201d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 789408489 1250 789407239 789407261
    0xb0f04230c04060906051c1508030c0c040e060115050d0f060b0a0e04051504020d020705010c0f080108060c07021011010f0b010906020a150c09090f090b0603152710 72
    0x280b84d03151514010760b07103802414a45400d4440519030043c030480346804c001c070850301c030101404186071900003240c00c54104400e400c8003035100b8200e06a6504d8103025a41003070816001a000550610b150046403107005041c150600a0000e01005000170301e900145441c01c41c00ea04000050315100c00081540c0b0603580480002e454030300384403003440c09114260040d03040440c0c6c021306111080505c800382d0415000c0e0300800e54240a1000814020302038084480c82c40e640b03c120a085c0401f0240920406800179201c1c1c0c1e21201c100f0031003000880c01c4901c99601162550490300341c405046034034680c0005075a00650910080300040145504498601002600d81710401c6031220400c998441c1d80807000b4015442085035481d00c11500e40c0552a801c056141000c0c2e22512000c4120554992030114a4801c1d5940c10940522502810640d00400100c000e4285012080d8001030000d0380504007440c880347c4000c1440c640d4070034409900750b0092004c165406c107819170103201c3c0180480800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 789409739 1250 789408489 789408497
    0xf0105101d09150a182a0f03030e04020409090c061e02070909060603080f040e0f09060f1f030302030301090608010209031b040617100b040b0f04230c0406 68
    0x8a5001a19881c50140b140d500040104140e91034a903540d0b0311010058007200c04a9034540c5101c3d40310000c040c4124603907018144201e02d05040030084031440040d860f14108000b1a1038052014440b41188002103035010b140c010810182800001d00a129a070302442050741f88c400c500c400c01c0903240000d82107a04c284c462114882c101070340e00540a08040c604070040e088841d040c04864250392200b541c01e401000d0002c1c001d603c076907601005a00c4803140c00c41c0f00c00041410881c194000314404c0d0301140c42c4d0022324880c100203408030743d1090040c0009640e60356450025041c000b50384065881d80007010440c0c00055540d00303029460381d20030302443d42c1d0345040000c0030800d08030500840750318100c050001c0480228444030030f12031003100031010303a0154551b0f50018040c07400351442d5412a44450151528001541800d0304413011034074450700035820207003400325527602c00111000030030301a44c01150440c0f0120030082e44054240391070010341d40d80018041e1152a90000d030041e0394150712 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 789410989 1250 789409739 789409769
    0x40f02010f0801060c39090c3b0a090902181605070303060e160807020622031704080c070b1603050a02030714010b031603051005090f010510 62
    0x860300b460090280d94041112078660000180c085001100c00642c0b0081034130100e15007100210010400a0950102242c5284140042c034403600c2020200c0807542408026810b080342d191509402d2071159107441499150381685071501d07910030b0811440d0007001000100c0c0c90703d00400051540c080164003c1c84500d1404645410182032540a00a980130807807041d8800c14048645a03c012012010142c550384001800c119254901d40589480481240002303034030340e0000d00c006001480c3c841158000424050703214000d50519403200201c000428441e08a400d0030b6824558207003039101030301c6158042209000d070312005440030040d000150380d0b90b00d588144124043c01041d1100e0080134909400c80002030054000341006002c41c01504e003016542e44a81c440d000032411344001d16515050301c480d0a240038420440d00182c1c501c1004515800c5071122941e440c50f10f10b00c0090f0355035500204e40e60710300030000c1c02c45820ba03030002405985801059902010124841d55a0342c00d0510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 789412239 1250 789410989 789411017
    0x3110a03031d150a0209121b010f021609020d02070b0c0706140903030f060f092406070c0b07031809020c060a090305161707061a0301090b010905150603040f0201 71
    0x40b42c003154a1203040f4960b41d40b900d450b006080258003031400194003514004004003c0c81d8144540308007189100441424400610005400c2e40d213210485007c5400001d800108048491022000d85001903001a1194603500858001744a00c540c0a408a040c3c0c000300045c01032007e000b441418424a020700045184005004c180942580ca00016410610001d030040003020606a40514001d0079090780003101004500443c0054a82c0e032920a04410700f10b2004040044486d2403140903240a407411100e23489100d510042030140020340c0b2400542c08082c580b00d0003400e0a0051009004c445145c0d42c0d4115030f000b58080402c1d40118014800000c2203510144502358249803d92074280c43d0403603c011242142244020898901e108800481d081c0801600134050075032280c0b030001405101c420500307205c613102500b00c0f80f090b81005514800250030705819411100042c0e4081520b8440f0480e07110a05c0100030030f941c019002108001c140304805418400250007130300e944400d403100d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 789413489 1250 789412239 789412243
    0x30e061b031902070e04060e071a0910021b010507051509032709041202011d03040303020610050102070b030703020f0f030105040b04091101232a06010f0b030403110a03031d 76
    0x148246002c0700381003030008000c510302d50410001c8914230016101a0b81d142d85007014940c206e5003050141440104a081150030050b44c040c0320208140010128150344c4900d66946040c02e829240c104074000c06c0040401108000d481b0002407143c10460b02490070903041a56500450030700c02c000582e00381c13220183c0c900c4030788020204501500c041c0840d641d03502c0e1182c1030010b015a0604665a403240008a556241c0d0714a03816a8640003542c3e445182d41402071a0420150003a039880112070001c101c182c4c1c001500707008480c0f103408403035140c0c1d507945c6003038000f80605801c490320700d030000a009250000c9000158103035002120100501010301052004031050010010665480100201119802010841d202d00f034001d41c1c1c02d01c003480c1d001c1102c48035008640c0b0003010f102c4040b102c80071200c90001c9410b03015500801080c080d0301d0000a58140080351140b02d810001c00004141854403540d00c000c0c801113a1307012030f450465103180050090183e41e170100b58000380110900c0c004280 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 789414739 1250 789413489 789413503
    0x402012304051c15021803010203060618030f160e1303210605060f030f010605030702030a08180607091a0721030b0307030506090606040207020904030e061b031902 72
    0x100d080682030a041c18103100078880d412899040c55511814502d00040d0840d005092604a00c000540c583c0b10450303c4610003210042c5140c42a401442004915140c1c0000d552000b110031910700700d03103013004022070708002d00150462200d002c3c00351162486a8649032950491315405c6a01c082541c5014480f00314402c8a40c00900003821442840d01194250748000804480c01000240f0141d071000015500c3e800030711081000f20000c070820403100380d9898420b0040040d42003040c0340d4580068003e48a209010583c000d0001040200d04100f01c200c1460a0381c040100880340386041c61034010b880506144160614401c0f05c40c2c03040c4078901404c0a0b00e030415402500264114030314450001a01c484a1806c400c042d500d11020303000d40d80030041c28000b580940007a100301d043c004a142d041040081c441405940100445e800507281c0760b003602d074800e8261401103030f00d038250340000c1d0080c846c40c4522141a09401403c413190380c00440117110800c01c0c0a110a0100d466580598807408 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 789415989 1250 789414739 789414797
    0x5031c05040803060108040c0b280e150703050409090501021b0d050a03051801060b12072d1827051006140403120f03181509050f0109050303040201 65
    0x300f440030450650141da8400e4020703114064804101d030b1911043e150b643c120001c90846020760700c2c0340c44002c0c0c0d241d001606410482e071a001d081c1070500c0b4081507007500620214000100c0014000c01418400d10584000c0d00f0300300340501c155000d60600a0107500207800c00f49890f00890301034045800d0000d000f0740400410303110b007030a02c1c5240909800070500145201c442d0303080d0001c41c422400081c45148003402011610f6910f0348180b807103501481000502646c14481c6030840b100b80585001d0f480c103040d0300e015441d1459403000a00880d00c050035128a00082c104c0510301203012000140140c0b2a582c99000c2c2d0300e01e01c0c40e01d0541c0c0d02a1207064905800700c414051091142030300c03940c1c11400024a9042d034034503091340d981d60050010446030358440011507a02400c0d2407541e15014070340700c00341610041d107041803680e141c3e8074404000c0c0000354800c940c1c4d8820f600811809000307110308060300b84000c024004203810b210b030f02e03544200d0b070807070000d2211000381d6079602144541507107502c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 789417239 1250 789415989 789416003
    0x6090b0f03070e06040903020a020d080c1005071d1c050f0f0a0f020d0215120a06050618041508150609060913032d0c0501200d0b040209030a05031c0504 67
    0x203204d04040c0310043ca00b1110035400c40c000c110344d00001d81c0300c04081400d4680304103020707551508010f401c0c5042c849880c40d8194082d061806010880d60302000703c10300480410600c1d1041c85501c00002c80040344105400c0032150400e41610a00c0000b0400c10040801d04003513800c4107100340ca0003034a901020703400600000304103282001604148456119191003d8a24082103889013040f07131468100d86180301030b0034202001c0040c0e002d01809005c00604050700e21038200001860300001c04c0034034000142c061a56080703213a040140a24001d00103100b00380c2a2251040980550708107201c044030f08178003a43c24007000c02c0c02401c0c5840824421401004a11040d02c0135650869140407400c103401d0410005c1300c80301107d072030845050840ea041c84d8a462252480074600305003940d40c02c50300d0b040d1060303c611507078603010300010441d104c01004050008034080c00e035000800901843d038400ea01445030709994003c00c94000002c2030030014003803100000d8188031018100340c1c2c80484000b0428 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 789418489 1250 789417239 789417241
    0x30e03041211151602100c05100507050d110910050f0301060c050a08030a09021014040b161a010e131505100e091e030301050d0f140106090b0f03070e 66
    0x71500803041c12011075401400104200c0d0341d010340e40e816411180d0603c4c0c1d51a010b414900451400c100100c41c92042c40c105078502441c151901c80d2034030100034a040c031340381d100c030005024079105804440c010122400200130b401da411000d501180c008062490040d922000c80140c418020420341e2200c0000c031030200d2031a800c1c8a400c4a4542428804445912512841c20005030b07602e406544911460940011400514010010054000340300c441c18822144840b03121040301804460580e03c140880e1070b0b4a00c8003000380801605094000340030801e000d0086801f9842d4034400700d040f100041c2080c0f030305440348843d429810b002400000c0c1340780e1014401e901e0540717980c0c000c941e0007a00180b04040310b55480d0f0b00640e041c1000c0f14500d00542046d8582d505906809141038151040400294155814400415207070380590f80c001e4022000c001c4064100b00800c0c107202c4800790600028011260b42d10820340c0900f00303200029114907c44601d40c42c40d4207002810000300c3c0c0450803070140b9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 789419739 1250 789418489 789418493
    0x905092a0f09100c0f0803220c050f2205060108010b040f090f09051501081b0a0b0c100606091d19050c0904091b05010207030b04151407020d030e030412 67
    0x14404260480a00b4071000742c0495011811206141c44200d020b1300d40e41d6900e20748894400030000d501023000060240c0c0c0029140480c5065880754140c0f2419590b24607803581c004002041000c00510342401d050b0410340c15420041030344c10445c05510b0a8942080c2c90341c0f6544e0003105d5008034020201c0b4011540707420403207403140d030708003d030402c95aa1001403000081d031103c0c1e040c42c045034031241108412000401c0201c9003007001c01c80d41c404290380c013600c1c2010f400014000900c1403080000014010400902c014406c0c0981c040c02103013120100186a96098080e20240c0c2c10301c528140380304c000f242b0110404003030070901d00c02d20701400c0250f0740b11403002003080101000b03009407810300301c04d00c2003c10507252880b50b00c100a00490368010010014000c2410002140c1c0040341113401c030810820004411500e82500f0a52190b441e2401488c200300084c02440d00c00c00f25504001e5900503c03005135000b0450f201807020580d4148240e9401e030003402e0b42c0703101e80c3c421002d401c4454004500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 789420989 1250 789419739 789419749
    0x905010f0305060c03131202150114090a050402150d050106080f04120c080d09030806040509010e07030809130c0c020102120903100b030313260a0f060c0905092a0f09 73
    0x25120301d1403041c1c4182c000d8607442e04062840c03287c9180c00582d1000f0b117040d0000c08010610340c0100b0941220120a050480c003180782040d01500500c6843d444d13031f01003070840d920b1207443c0700e400c0b003c00c00307403502c4810800c2000e01a210070302c5403030081540139001c03440040380d10307409500c2070741c20100141103030400401c100d454800304041234072285407c0c45280004081c900580c1107260080d0b6130040542400c108000464001607d51515685845922400c050012a07803c049a40000c0e00d65114030010020806550a452903a00e40c0c41c0f0b0450032a4201d0b41000c1e10075031043c001c4c5e0803a1107035407d140607014980700e0b001d036503541513100c4900c4100c5480c2540091440381009020340b82480c00b003401c81c50b55104c06800042c5c10b150810326180c3c0c4240f40490102c00741d1101c0c00200f400d1302564a440300e140b512490040e00c407588a00b40710083c10b01802e044001080050400b0702c861600d2422240380c41c132411101e0608e8140a03181081e07803080740003942e00755008100c5040c900009481005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 789422239 1250 789420989 789420991
    0x32b0b040b0108070c02130204080115050d0309050d0f02090f09061302151e13031719080a0b030d020f010c1e080717010603060f09150e07030e060903040905010f0305060c03 76
    0x783c2c80003111011000c2140c0c7d6001400081c80c0c80d000104050b0703440090701c42c10b4007035600100d01849203003003403c000c80c0e48458075004689040d184415004507a05018101040c0108065000b100d000244101e0003084142c15201e03000f600156144c5858002500d84c0c0c46690703140c007a6100c0c590103c408403a241c1440248a41d212902c924600e06003e040c96102d00c0d0859a4400c800750042c1c203040052084000310030f049076558a4155181409100d906500f18480220040c20005c50704d0002e4050146640541c1030b2a034010226410103043c2e00d0001d540e06a000c3c5162545c3d42482030034018140200030075001c011129480c4003240c5581c220444900900519540400c10314045201104441030012030190440b6500486c3c0b050415260b03441c03c05096000209161078a2070302411400c541404505803145e0481c84820380c1c0722940210050486401c8070200e0303015a40070700c89101c000000810803141104401d000e940c1c2c0c0c0301d140001c041c41500c0b000c5d10540159001441d0309800600079 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 789423489 1250 789422239 789422243
    0xf0409150c0e09040515100605030f04060b03010e061f0602070311040603020909150c09010804241503150207170309150403020312010e01080c01050c032b0b040b0108070c 75
    0x4849800b4a0000a0721046003a103084c3c5240e00802013500d4070141c00342200340d00246a2100410091400100400c20310005041103528100900030904120f10750b040801861001070080c4481c052402c0d6154071b91806441c01e5000e22800450044102d40704040517084500b40e4001d004103a02d180c0b610102100100642c0e40e0103550303148040010394a845406000741c0d04100205048080c940601710101409446601c1d0340000340425911a030b44182d2465106034402d14a030403032080d807142d18111010129800b4403890601d0203004056080c100e0f01c0d01280d0003480c0d41e0740c03131a10010309042244900da80c043c00c0690384010b5801c007510345200440d0021501002c682440c2c464405e88146c074641a20203d0041e040002e040200d5600d040d01240500a4607c0700e41065141913850f82e42e0320000404181403043c0407401c100565001d0003540c020780c0c000001d0078404141c060054800701c40c0308510404c00303458a0210314003401c15120b1711500304010303120b03444151100c0300196084d907404601 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 789424739 1250 789423489 789423497
    0x5060f01021b150406200604020a0605160501050a0209040b15161104140906090f06070c050c0405090106031a0403080a0b04021908010515090904081e0c0a020f0409150c 74
    0x40303c10386005200200001c001503983c1e4910814807a69440c10f4040c440c0c003045290b4041c20600c0056270701c00a00c50110303481030600c83c1c0e4541c000c5080069409004501601079441c1208001d064801900189182201100c040007585507070801c0103c521701900d40c20700001802d0141500101020440500250241c0d00c0072840250130000078050302c1c181465000da03021040d0078046200410031800d9008590304000d00106420080c1c6941d59100082c8280f081000130024030b0117014050001da003040348050410710841c07806001041c0603010504c4110b5003c031018a4800b0001031505450b4011649652050282d40302e0841d2200680041ca0300c1560040d0300704010740c5c1800b01ca00354000c060901d40c40d12a5158503002c20040304800072038a1b010414030811982d003103a070f01ca11503594055400100030b42c80700103403011202084d080300440407101100041d845d1604100040c0041128821911200d00c04021000c3c401034901000006118208001209102c2d02031600681012105490 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 789425989 1250 789424739 789424759
    0x117070f080d1b05060c1201081c0e01170f070206070206070e1504051003200403020f1c0f150c0f020a0f0201030b1c05070b0c03030109050903190e030105060f01021b 73
    0x48885c144001524141c1c02e090000a0744c072031b078003446050140181700b0305014040441d20145900505203038800c1e9441000042e0954144580c02045101c88510b524903014915203015529074500712010f442a101600c1404000740302d2910004140c2d101e410b2546c1c41d01d04001d1107401f8400c00401000f103940c000c45042c400820f180e01c400182200c41c0c1b0150b500820001141d921118541003007410701c440b200d10030001400540c40d1100c0c01c1c900d150095581c0da0303002c1c1d20711800c41460200300600502030751800390044107000881e448a800700114241c2003090481c01c01d0b040c0c8180c4034100354440943c1200c0480008a03440012180c41c031401810040354550b10782c000180001c91190701441c1201c1004641401d000c17080000f14003900360100f110303141c05894103800d55603000505c501030700f003a11a000109050400d00c259644480d94254121040042810251610b868417078414003a41c41c10001815614100481010408060b00607000039041a0034040352030f890f92003680c0d00040030310 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 789427239 1250 789425989 789425993
    0x2109030703080a02030306130b06120c04030c061206052b14030a050d11030f01030f030c0f06020c06070801030b01091109060c0309010906030b060313060b090117070f080d1b 76
    0x1100030002c43c100703a40919503e150501c100300030001110401080b0300e242046120640d10f800044074030742100c01c5040c021a40d908004078981b807045820080c41d01c1c5480400088540e0000c002c480c541001440a215050710fa40510825103240002d5a01e204c600f0040c04100d5015902808882401404981c058203400f0800a2555020107007903000108006502c0950002c18411428400d000880b03c0786142056527042e041d401c810700001c1d05680042440400300f40c0203550450003103920415901c0d03001120304041d0001e4209155030308580c080d03d000520340500c15610f140c1604d600c421055026400d005807207000345514401c071904502c00b0401030358195140310162140240040086664030a548001060700501e684940149810074028800c1031340c814094a41c406014051145140e040e4204034018084144d41c5903008034540c0004a02c454607120040c0d408481c203011154225541c2c0180081c1380c90174841c01c0c4464100c40c60381c03650030b88156945803a041d040038060302908029 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 789428489 1250 789427239 789427253
    0x10207050105070e0a06051e0912100902040b030c0102060a02220b040f08030f0403020f0d1b150f020a06051f0f23030c0103110d060b0903010e2109030703 68
    0x15608200818014501c21000e45801a4450064031262400c41e043c004465400d005240d02303141d45021031030001c640c03071040d0b464130b22440294041b5401203640c1f40a140740004010b140c1326500768012800c151080c90355083c001020040c40c1d1042c1e0003042e107a40c1d2500c0c6400290401c485d041070003a1110340024140083d41100c0000e4141503031002e40d114035007014000c006000742d200c1d00c00f070382080c40711200f80721004042d50126a0141c41440f201203042000980e900b0035001c00410101e548003684407001c001c0803081e82034411780704070160041540360f41900c103039a03200c130001c1c0180d105d0305d24400001e0144d00115081855a1440202d458410400c201243c55940005030035454280c4c0803c03003111780520310010451a000c6036014064a074000c03944669280216505040d1994003051106110208880940f00d1055041062585621849010f540440680d52003982003240c600c00c403da000c1130034104000e0740071100080d00b40e0a004514140c110180081c4d07d40183e0300000041910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 789429739 1250 789428489 789428491
    0x4181d0d081f030b190f09150c0e0604090b040f0e0609070b16030e120d02071d0f04020d06090602190807030608031b0717010b1c03080705070302010207050105 70
    0x5a2034403032aa1400410345420044080010504485805020000304001c1004c9030741014000034080e41018a0506140140030b40d241c41c200007901d01001c01c8103206030034a0780100d1144112040c00003184940d000c690700c6460043d060b40c8000204002c22801600754000c1183c241d0113040442e0109030412403000701e54010030500340d0382c0c100c82c08106203944140018005840411889810f000040700183c80c03000c07459070300505104040000080302d40c0d5080c000c41d00103481c2c1003260121321540364000c1d1602c015100e08519403061305078904880c200c504003288102c10703110222449598907001c01c1308003070b0304110a9400356603e00110020461500060200f070142d29038000040700840d00040034404002c0c0040300301071824005222010005c0b04072941003540d5440b0f42114120a8a030a0804c40c1a44c8079030510065038090f00c4a4400c190000c140c880d100712826040840b001c1c0882c5c040307039250740000700010744150020302d5031405400a05a0180a48001414440c141e40d5060850340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 789430989 1250 789429739 789429763
    0x518090d020f3a211109040e0a0f061505010903110405040c03080c0109020f010c12030c020c030f060601090f1a0304231005090a1a040812010605040503100204181d 72
    0x1141425030349070030a44c815140403d8002040002611a55502d43c06000e060b15942c41152180c03107002c41c143c0c00f0000d40d000d00c0e07000010003048481c0da1034030030300800c3e201d4084600040d40480c001403a40c041c0780b030305080300d401c60001042c2e8800c4004102c000c0000500807614415081c0012010450100c040c0c56000800c50001406020b43d00403c0b0841903882000703410804130340c5080c00090151101e5400c642d030181004100c54100c03d030241c0c00d102c0c0ca00241c03501881a0002c19201c2c000008400d40942820b803651241c560301e84006a8840900b4010030400e010b0015040703100c0d001d448000c603405801341e4442008104031402441c590f105500e0000441d07445081008074000c41c07403048903003080d0403400400d0175141e25510308000039610840c480016460320002414071075041c040b9024000085100e1120b980c589002034032a4119008950080c8910b00c0300e08032010b120303c00c0320182d0310300200c1201c1c07000251445030040c20281100c0c1c000c2084c1600c20030001c11041107000e441c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 789432239 1250 789430989 789430997
    0xc06020a1403091605060315130f3e1e190509030d0806030a030e0d0f0b01060e1005030c22080309041104030c03080a090518090d020f3a 60
    0x1c0130354032040d80c108005400540c0706440030000e204500c01d00c0c1c1c00c0507486400591f81c1e150784001d051031210003001c100000d2014582032448200e0b0251008004c0c078078000c160004545025062031500e81420a813040d0808030760390400c0100400c1c07840c8501203002d110080b08103881c1415038104425110f6a04d040003000c1240440c940c9414076081c40341120200e011301e8a41502e00d0301e00006036490300a0b0101a0078004501c10000309178441c00034121496810022002d440c105a21f03203804200c00034032a07440010505155103000f03207480142e1340e0700c14109644541c19511000c400c0c4004e5481070b80200b0034480c485400b0f881040d800b184c00c200401c1440055510f4122090600040e80c0e0031207040004e181c010081800000c1600190106aa4001050540302d054156040d02e00b046140c00c0107902844840c01c01d011082410000c0c0d1081d0001300c181c5940c01c404100984e40d404100b0384020396500158030315200202042e4002c0511f03218504c140d4400809294240b1a40000981e680001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 789433489 1250 789432239 789432253
    0x190b040f06020f0c0f1002070b07240b01020a0209190e160603060e0109150f0e0403110c010903020f0d17090102010b1210050402060702061606050a0c0c06020a140309 73
    0x30b405106650428448401615500004000150001d50f40b5034005e485403c0d0241243c110354820001076024111080410707945d02d805050918030a41c0c48103000c50718600003240c509469102c1d001c0c40a140606800178014860300e5420071801d00001020306d080c00440311115654001140a0820341e80090b50141c00c8540c161030007402802400d401403014941842c070200021030701c0720315640c1140c10300c50700002c1c142e25889030040940c07503990082d101c03c0c0c800340300403d0b128800d200c0ca0b8015803013911201610102011a0394561031141400d81c00725003012004c20250600740024041444020700d1000c6951141da210561641c11800703414070200003040341c0c2d80d40d503024031420746c2c665400c4501c1c26290103040d650b00e40e50054008030507850740d1100040b404540350700c400d80d014554000c080c0c1e0749580c101c0d051045000c4806074103171441070500010a14003641c0e8418019580c03182d03a03540400708201d860300d4000e5030107104c2032000c004190021140710014a40698081e0403600003170018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 789434739 1250 789433489 789433499
    0xb190c080114030307051011040510050d0b011b0204050a0e010f0506030c0109081c021207031d0604080c15040e04030909050907061e020a02091314010903020c190b040f 74
    0x50098a051890281c4e004100c40f1010500029850724a070020305c4022a10360041c0300200e21074042c6074440c90300180d00d1280481c4250b0014083c0c2501300107060304100754074501d4011692003c0c180c8298540555140318200981400e03041070342d001000000204004903544581421038114079498001590780b038091103900c0c036041c400c18903648400d01c9c28501403401c041c40180c8035511074614440c020352200720401c2d0341d8020300c0000740078040d40d421542c1b40c1c21a828041c040c100749032611034001c0303001c2d001095186403034800c0d28142ca402e00018450100f2072000e00c200c003400c0000c0c0c1c03901401c046c800010002c041180e0507124034426520840c81a01d07140c0002c044d00c0024100040540000006101ca560300180c040d403603050211004d049084420030607810f0144005001c0d402c581c4c60820450800001c05120700141c3c0704a0200400039174078048070303003224207042000780141c01c548410300d40d510b02a4600180800380000403a010b0342e0ba0000685c06038401da00c015800550700b442000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 789435989 1250 789434739 789434759
    0x10b130207060b09060907230a090509090a08040605090d020603013002010f080613050f070f051e07170d09020a0504051302090c040f03060b2b0b190c0801 68
    0x921250283d8100c04e0504250700010030a810040c03103003040102d1140c0c4c05130281d44190041c10401b00141880d581d460401d030004000b4005805054043e40300300d0086101d40400203030301c3e2026a000000c040c101810f1200c100d91542c0009100d0740d1001c040a60140940e81c0d44004500911019446c45401c45e442001d078001c0704140d43e141302d051441401c0420160760481c401c0240b017035a80c80c003850f8541d500000902603040101c0b54070b4201d40390504200d83d800b1000c410a01402058540301c20240e1280402c8806e44500f40070b0000310907180901180009800c0050708003240f00d030040c1a08900001400703449508100ba080c1c10781525034610006606000103008081c081c02e8805001d036282c400e8040170f00c0c01c02000000c1c014041e05000401007001030060f03501900b5609a1880070b581d80f820914080c0440c0800103100b4480107514242545081000d5215940f0150011494a810352100107407403400078120051041d900d203624034100680e1090b111a487e050301d038080ea55040100d404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 789437239 1250 789435989 789436001
    0x60604060e13120c0f1209050406030302150714030c0904050f0106020303040b0702073c060206041103010f05010611160b0d090f080c0d021504080901050705010b13020706 75
    0x2641c020704420900682155107042c10607403d4110200ca00c03c0807901000f10f4044801c64406404aa400c2560400308181070414030b6002c00b03a0780d120b5052035261020001143c07100e120080c00350788901000700100217922511940400c990608070551941c1c40910351140d4011107041801d44d80c0003400f5580c5142c0b611a90707810418203140c0e82c201d0f6040c0781010b5034a120184c03014060002a8001880c001e100700401e40103090742582c0385c183c1c04600d44a101168484a0030f0700130200212005005501d0300080100460f00c083c3d00400107511a0740300c114680d07040321000354043d52950f0016034424400e000b024000c01c0f19641d900c3e111000004206e0428101114201d2904501d003001c000d03c0c0e0f412001d444440ca10540c00150241c1d4034a030036400c2d0032070790400500c40c540110350380702c00210100f03a1072025040e0390290b03001000d001e40e4041c1c1800049800401d80749040c88240625403050b0050402103100343d00001c0e200060b2000603420305100c4070a142c0c415000510042080360364082c0c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 789438489 1250 789437239 789437249
    0x2313120210050a1109010507020d06060f0905130b0c03131a070e0409030f050d1407080907060201060303090303030536160f03120c080c010c030e06130b062106060406 73
    0x104139224044006201174490719900604201c2c01040c060155030f140609024950745c0003100300165030340d0321003030703280549107228100030540741c200050f403d010f2060b02d026442d5400300005001d551031a10760091900301900d0412103642049180740003074402c01c42c03c00b0b012112203501e0390340c1c548048010072442c0c002c030700f03d0300540c10900444002500880704c512070081905140f030b00e81c0c0c90203220b40000d08640d036410300800621070501100070b820851050250b0b03040026180d40d07a07201d500907420707200d20313210080c001010b26400f080400e2196000e40d4102d00e9000e01c02e03e03c08607030800e01c08803404005981d8030240700c1c241c2000040500f00100140703600072042040c071003840c0c12000041906e0520000c0c4c009254010101001807242a80502103584202c8590f100d10096903920300a0501c8a5681d01081c542099070340c0781d00f00000e015104444800c0410300d4140c041e903c0c4081441e000d0f110a400c13802c525641054000f40d0b0f100510000c6c040d000a1403a40b41000030401612010b07408 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 789439739 1250 789438489 789438491
    0x5030c07171f0e0f01060b090a0512061f05030f060a0501270b03030702090a0b03070e0405100e01060b0c0a06060b1c091502040905060109092313120210050a 69
    0x1922410304110100c802c07098205001510000310450307a82010302c003580c654819481d000003c2054175868021708401e10302a1a0460202d4889060041d0111441060b00080d03000c1c1e00010800c110900c0c807040c45415900e000c00303496a8036001301e40340655124100c01709802001c2044182d000c644240c40c01084610108034088800c40740036034004158108107580755403140d034490001d8a04000721940c1550142070340006203030540c4010001c0c069444424401c3c050740c10001031301d9680000c1540075030f81040180ca06400c2041000d4020110b0101170b4207135540f1400300044042c80c06014004502d58003000d014000c100b0310782582251096000313020392040512010304107051400d00b0081014481d840029044000e0401d40565100012841640c034000500410148180d03003126000d4242a01c440300116140c05004082d9a2911040e48501d00030500b000c409541010300c03190452021a404600110543c48041100110601c100090390100031030300800600703489010b52001c02418 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 789440989 1250 789439739 789439753
    0x270f01141612110c1605040209060f071103010e0c0f0307240e04150e090619020f0906070b0402190602070b0901030213060206010617090307030f050705030c0717 71
    0x4444640407900000300030410a080a1501c401c0580742d01c0001000e0480e0105600d4100c140a2156501960094648542c4035030a0000f224281350007601d00840c4018040c40c200003001c50f2440c0c413a04801c0d001c1d645501247e0300000325440c02c0c070a040d2101c114001a00000c07100e00c040c001d048141284d03440c000c1d4044002000340c4c07a43d4000c1050402810300f41002c04408010044500c003498181c0142c0c00b5240c0350b407120382d180000180c101218840c81401090761341301a115629000c1c216480101c042c0ea1540d2a00b840d1203560041c12a40440805141440100c03808541780f600080130440b25104502d05010662501c045408180c0e0490114a48080d04225009442e0300c214450b0b01545000400c0a0000368001e4041d2550003800f5031584e0011686e6010003540d4000a100c0c040100c1c60212408141d203002c440090720500c0d0100045141c01c0700c6603411558004644040c1003008400c0c880940091814002000380c02040f42c0103046050616090303540c00300050040b480c19901801c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 789442239 1250 789440989 789441001
    0x5040b03070e0718090e0c040606051305063a0e061303030506040b0603160e030c061206150c03041d070f030b21070810060f030b270f0114 61
    0x1080d119070007241464030400010380b2131401414116550004441e4a0801d4180340e1032000000708100041d40403034043c0300383d17603032104281c501e4400d04244145112001c03005028504042d4020302c410b00301185a10442e2100c034800f001c10344014420a01d04007144800074040c0c6940c1e0203070b102450140c1e0064256410008001020302c080510010141078807980001d00350380c0d85030700801040d00c01400090f603901c1c116514103100c041c0080101d011585084a0000900f400207508611000181c00c0e0b0349040c88000c49064146d900429495102551a0380507001c4130f03424001d0307d00201003000039a280d60600d14401c1a150a1484130380b1360081d02800c00810503400540c441d904029030500007480741030070021520342031542c02462400b038041c2c00ca20358049400152181290040d07806d4504142c001c0a00c1c1c81590410711601c00020007085003400030844640c40d5603000190404442c07183d0150040e0411075940b046628880d940000780300200b550028002d60a90900034035080c540741c03400c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 789443489 1250 789442239 789442259
    0xe0f07090e060703090c150c03020106080c0f011202040506040803070b160516054603050301150c0f0c05041808042c15210c010c11090106020705040b0307 68
    0x802c40f1003056141c44880d41400002c0c100031000e0114484001c1c500030b00400042e204da404204100c0040d803800c00b0001c1c0808003c20703102c610000050142d003c04d0080c0c0011103000e0262502c80700119403c200000e61943d40e200100000c02107000610f80340d00681c200031140356002070146c90200c02c440300401350242e20400f00c41084107615101000c2d0342d441d003415443c003456050301d840d040b13120f40781e40021038045500c4158011030b2490598900045c02110303404a401910000340810801e00c018400074511308180c27078605c0c600d842d20740b242c041651107e005440307440000341c0342c0203c002d80620460801c0e0080070004500d00215003407801f403641d90616140f04512038035064800c410740104003230004082150310701d0840c64141d00242051484501c0d40104855600e1043c0762070a10074441d100d0000c0c01115a0314030030090003010b000302c0300640703610340110022503001080540304a2196603e46409020740100d50040003414205010b00c8103d40d14409841e1081e03000c0102000035140d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 789444739 1250 789443489 789443491
    0xc26100b1303021e0301060f1809110607032604060b0319060c0e04050907061b05210409090b07090803120a091412071203090b280e0f07090e06 63
    0x2060340d04480300400d210390f410160308080984c592650802d480010104101c03040300701981c1c0032090340c885d20016006084200c40998000400b46161821045040d10f4640054500703030307001b07040a036689644905028150518544402c1750031096900b070200b07110030351080d9881c7c428160010440800000075554400380c0750503009044946400526070b01610405d04d8000c2400007820500407414052040780d100e8180c3c5c0141c3c8005070200b556030010a4420103851505900f0401420314421034060b44100c4030b801c42180015540104000903556042d8031a0021460080328031428904020780001d1001c8656800782c5400c3d0320900606e11070782c1c020444581c001c40c1051000800041d585001c2d48240d00e81003040040340900101d803e0901218802004054815110703d444161452000da00302d402042014052000b82c40009801903d402d00d243d0002c201d00011040030298040e000c010fa41a410551410b500301619240130720a041003034401a1072000818003084c020810450350b1040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 789445989 1250 789444739 789444743
    0x190e0703050708011413110f04051305040201050d18120815120d0509030f0d0519090e060103051302060408010b0102212215080411040b0307090c26100b1303 69
    0x1034141c40003450b004aa07201f00c0400f402086010703107402c1e07074144d051250b40203841454019100c0c0c102103403821103584a101c0c8550b5050311094202905121181c000300184e00b981c2c02014201060040810b81403c45585070010310350700c4040702c0c07401c003d03900341200c04018003901400300d403900b04c121607001207512030710101c2d0f0707192903515003c0301c00000f8035220111705120f055004911106109640c8907008002114100165030082c44194408469a0a00c0d10960400c0c50b20704011900030340c03085e044035400c5644882202c45003142c03030b0000b542c0c982c071035800a48039a5540b0041809543c0511070315902124060011513140351440202ca4180b007181900300c0440d002d8060200304001700d0048030090054486085903d800320500540035480075501174800380341a001c01c100c030386040d0240910b075060140c05403050915000c4540060103030010703088288045142c83c11900d015440002001c2040d043d0b15107681d0800708442d0340940099080303060780c4c4c0410000c0840c1c440d401c00d0035804a075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 789447239 1250 789445989 789445999
    0x605301b0d03021c02010203011a030c091c02041a011409061b211225080a0b03030d050115020a1110090b1902010b04090f020f190e07030507080114 65
    0x1580502d012801c040d081a5148400c4608180c010251170741540038605a44d20038200d504c6038841d032020b44c0c4035400115002d52842e0b804221400b00c5007030010458041a200c00d03801102240c46500040584d00c907030303070401d90407202c00075039554030740c1e1004402c2c0c1c3c42920f5017407aa141100d80c1000c20002e00c10050050700ea107404000c00442c0e842e00300106086580040790115214180143c64103a0341d0041402a8060303601401042010030104881091088503810b2000d10300c1c80034400362540100280354004c07099079000c1c03110564806000400c0d40d6016003400160301d42c184481c030368400790209503000455220342c000c1d40c00506c1c10b040e4103030039840441c0c00e900c0c411007681040b00d181c1020f4126524101000c118002c0c01194000e072081c803000d141d002485181c3d1b0324014070044414181002e407041c01c0b9144010003500380000c030701c0b640e22000ba1503c4922070ba103034200700c8005010391268110b503d080c410086e05c940d240c841ca07a0816040d140c104004c0d40740248405a54403284a9580b2074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 789448489 1250 789447239 789447259
    0xc0b07050f0d170601210509070f06030605210631030f1e02120f040f032303030408040510200a02040e010b100c03030605301b 56
    0x31040811107614034940c040c0450b03016801500000f040d040000c0d0140034140581400700c1e8956010320003421521103400645004945d9084c030b02e2001d440080d21610b800d0082d1000031566281e14604403002e880c2a031408503020303240c01c042c00303046500020072024042002e102c01c0b1843e4004140190001c410003003149081c801c003040340b042e83c0c040d811080c2c1030440c0302c0529820581c000880418800458962400d140080c1d00303400b4038040b5102a440040e0040b03010108100d1000740131304901409104180d00340303a02d0700130100d00004540c20598003542c44028038a05521202e030700001039503090014605604040e919010540604c1c002c5520880c0500d4281841c1446207601d40b00809a18807681020141d41403175a48849890030305030702a5080104000000704140600d441240c0064500c00b210362860a00300d4419400300785c12000c00d070303d86500061540d145155403600745d40350481c880f5012442c4540402c43c01e0343d103231003409540100742a2561103215200c1c01c04080b005640054203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 789449739 1250 789448489 789448493
    0x307050f03040b0717192c0105091c090501030c110a030f0e04020c06180a152a14210414010e070b0f1e0c16060c0c0b07 53
    0x40e024401465414840100410091000c0c160100713000302070540790a201c3c81d819100d0503e0b021002c40e01001100a8504003540c1d0324030b00d602585490711021840d070411000521107107082c11021851104070ba445800f44102d582c020b02131840460b40031007040e10050410b0a010b044109540710b680e0600d0790300c1400c8001c49000324103120000c07103190181d0308040250716025004900040403903002074030800702200309061620031655460f030004003c2c085913603100140c0e90341c4040c0000004590288019107800104450f8448980c00c04c0182c0100c0c3d402c002c1000014074003003507a0021406c11101107802c5100745c0200380084008001450981d9820a01c0e07200d540d000115510104454160010441400401119198040042002030040020000d080c541c1e5920750b0081ca41c21003030400055800040380340040240d4040c41d40400d41e5880d10a251000d290400798080c203c68000c05007440035001900040e06c058516420324040c151380d11f4494001405890045842d0580c1c005002c0d01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 789450989 1250 789449739 789449747
    0xf062206200c100c030e060604110c030c06010e06061914040b07050714060708030708060d0c120209011710020f090a03030908010606021c08040f08030a02040314030301050a0b0307 79
    0xc0c12080d004401d41e0745a400407200c542e0303442d803220000852031410030762038003040c0310b0b005003141e60078031130f00502c080d48403401044010314841c2c40c2602150003c000030081100c09001030110104400094142c9624bc142d01c6101c8040c010003652040b00d00b0005200ba1041c0541d0f0001c04510501d005c11918181c142582c00350320071500030300700002d00030488400b0000000307092002ea400000e03260400d00051014080d8501800700014518802440018641d9220703400d01e9610800003030041221046680302d5001c050f58036000085044c0503001c900040d0b00341515100e004110030007808460045000070f1075124400b038285c44070220740000b81c05003200e0040080d07581130354004101e1440240d5904e0007814a900511031120035508080c00081d800340007085050540c0d252416400300c0100c2030703004644186006004990062a03d00184081035060003e10321402e038413400103a0301c9040d410400701c401d10980c1182429801040140800d49039261404210340720242d80035201d03114050300791 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 789452239 1250 789450989 789451031
    0xd0507090b0f0406090830041e05031b0f010e01030f060b13080a02090c03041e0813140f210604060c0e06030f0c0309070302030109050f062206 63
    0xc40345001151410007141c20b0300c010403c4400310307121004416a01c444050325400701e07900300340207001032806480c4040741c0d1f502d44694406d51546000d00e860b445280240a64820411142c05003051000030b01142c28100305400500b02e202c286034035444225000100800d4111054a0400114854100140c0d0003500400d0041d43c40ca02c2c10f020340c585809070a000d54005c5403100712411075441d80003031940400b081c3d054400e50003420720b607440c1e0f0f01c24003d8105544050b004603044807001020407440c14007030050041d06407040e00490b50310000845401c40402c5503802031940040c2908940300300d41d681c10b03410346002c2c2050320b8a0080d04411145c21a03032448030305480c6424080c20082208108056020000546040d115020401c42e0b00003409114041280e41140d078201e1000818040c004220107903a01980e45001c035010701c0d1301d039400300342560142034084460b0380c40750521031320340c2d90300f441030380d51090429035420061201c900150790415607881000e880321740d0311040400c5c0c0b03260310a070314 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 789453489 1250 789452239 789452249
    0x3070803010e071806090b130504050702010614035a01060b03010b0304020f190e0a0c030c02060a0911210c03030a020a0318050a0b03040605010b0702060d050709 71
    0x4a0322580d4908000450800032510381000031091028403440e802c0b0200c0b034500340c07605a900c0100480c2480c48055140c0d01c5001c114843c0003042000061681e143d000380e40c07041410b540040f6207107182540d040c05150070380c22014803e4000c0c1d0403a01c00d9020764644900c684c02d107809440e8096910042d23070410b40d041742c8078820038000c180ba200404040da902514446440b040020400180e03648445030080c0002e00408480034410800300d4054500484500885400248000c04800518480b0701e0240d000d07900c86480c11826500f04801034055201e640c450300410b040600010140c010003d40b40c1c0002000043c0b00d9580340350000c180205c040c001590800040c1180942442419425203029480c0140c0a814841d4014201032030070040166840142241c00511501c3d084d95415a22142e6909000d170303402c0100200000c156990a8254000f06200c42150f41d503420581802429510305811107000900100711203401a224001160110004180000b41d02d40307d2580803076101c1c3c055489 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 789454739 1250 789453489 789453503
    0xc0516060905190312020304022227020a0b071e05030403050105010608150a06230906030c04030b130f14100e1006081204031e1b03120309050c040b01020307 69
    0xf02c2426400800d89101020380240c5a1004200001ca0f44074164801110025001200402d61f501e03003200d0310f94030141d07000000c41d000c1a542108404000e10101e0103405050350019030940405600301880030710090b0944418880c5040400e40354040030601c02080864505400200c84c030601c6000c2c000d5501440e88078000f40850759640b03900138881d84050701d80d1201984201c0880c01f0901c1c20811345421100d403601c42d8840c1e44032480340b0841c10041d50b882e4122a000420466800e07649982c02148181c08410245403104d00b5420301c61600c0d90000e10100528148298100103c0c5000c0c2c4804001913008910002c03501140e0b440034100b02c01e8140d41d902590608092094400002c11001310b4905400b508100c10703565100c60035070391003c220141c144158104003e101081c1809440310b030030080b104140e45900156950302c01d2142040580074a09111200c041c0304002c2103200c081030303c0d403491805200004280d1aa10349940740274905603c01e6a40e40f4072581c03107034020300c00e442c000d40d00101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 789455989 1250 789454739 789454753
    0x1203070201050114030d08010b0a030f090803011d0903030105060a030b1e1306060e1e030d120c0906051204020f060706051b0a020307240903120f0c0516060905 70
    0x9019029100a00072031540100c003a0741c03540d02c0e09000880720b09000032130303940ca40301d40d181400381101a80f00d28002000c143c3c8a942c0c2c414000a40c0c01103005c0f40384250840d580d258035004402c030100d004010720044049100c2c2c240a10800d0000503241035070740844005135500018501036000301401076070150041c81c9180d0031004502c0305140b401c1084800d45440c0c20080a410406044600c0e0f070081c100441c807405502211400c140c9010044c2070f0483e061102440344010000785450b6005400c20b000812411100b0362108560082050480150500800f11820b0201c041d2050007403091031502c081c41e0750300103000e564600000e400301d450060304244d0380f1941c1c2c0c01c1050180c00d00b2248290100d0043c4803498801c0c8143c0100e032000901c641c0610708194a5960344600c0c1c1016030101c1002c56100c0600154000980c49250440d520945540d03210702d00f0144c820080d5050005811141403410420f4405190420112800340d01609492030402d5458034243d00100142d820240c150301c00c0c14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 789457239 1250 789455989 789456001
    0x8060312280c02030c011119050c03030f190c020d0204090c1e030203060f0f0117030903011128120c02010906060314060c0319022808271e1203 63
    0x10b41000b181d98000e40a65210001d41801900c06141c0e000d0400019404034540c4010500c0250f0308144041c811f405451441b440240001c0c40e5401840c141d401810300060850801e401d40c15100d841700782c950401036003410464000400645212901a001c0c5031611088000c218544d90003c0c0078000301d40d0040f10f141d17181801c541300c52242d8041203010f8480c107804150610032540e95030303214049050a14610b60700380440c065102d220b451550b08680b1040c001e070845a5428000d5078046c400e207010a54072001500b070300d024401607040c1c3c0103600c0e90200322290941c1c1c0e40b0521004581d0344000000c140d04400309412401003031521805484640780132030200c00c1108035a50714a00b200000100c1381184c0340e400f0840c0180c48191035102c0c0e190b2a600201c541c2075203580140080c11030690440342003903072125180d5500700d0740320026000107c506003041440c1d49140340000301301441c00c40c00e1509607500500d031aa140d0700c856240500689031440420000030070891008030300804c03710345449003890 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 789458489 1250 789457239 789457247
    0x3020601260a031e030e120a1106011e0e07020c040b010207030b04060c180b1e1c090b13080702120c030a0614060f030c0f130903050c0d0806031228 65
    0x1014042401400d0b001013009502c80d010f9103104840240c050201007102849064603588442000ca0a200d40c402485030001d00034403035180200036802644809103200c20101001d1030158010500d42c410801c10b10400c0c40c1d002509094500342564006440030150005038a404241c1d4401030850400c0c0d001c200800c042d80e0000c200c448076545400d0301004c06100030000b8030165000d030b5100690103018074244228138032070903030910410250a5244c545000d10020a07000c0006894001c2622281c4030300400802c049400d50110002455021010300341d80c44656034400d0700c00191240c64092580d00c10308000348420b101701031004003101c000000314940b401c05003501e0040e44a01800d9003000820905007109810110754000740a400c03c181e000d010015940114054550812160410210801b6a900c548540e40d40603484464a607900d5154051825003074181c10010810744805000d2661000280e5544140507400c40310f4913210f812018015020412450049c0904500440381c05981c00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 789459739 1250 789458489 789458507
    0x636010209120d30022805180603100918050d02120301150e100314010504110a0c110901091b09080309010c110a091e0903020601260a03 60
    0x8203603500014150b082107800e444402c0d0400190100d40c030b4500a03400f414554915603100d813580c400d868041d91000741100100e0300a110400400c800110040c102d01000005c010062802c41c40c000380f178481241b084010114000a00074022000070010074602c0c00514482d0300600300498041088801903442c68454400e10703002a10540184071841025900c0030550b105240383d4949003c0c80c6900e441490300706200c07a02021000c11011405400f40d595581004181c15040b84d500400e94558801090b02444010390040e4881c1e85011444c001d840c81050503680040010b06040e20100340c01c4c10900140e040d4140c031680d000318000300116100809502016501c500ca031004103100303100b248180c541d60150302032078940350b0080c80a1012984101d1140b10410321900c0340c03480c12060368010446201c07031038201000e0710742c82d10726211203194510280105004e90070014440c040054a01079120b00041c024503615108140706031100690310b0701449454160081122048103050400818a143d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 789460989 1250 789459739 789459757
    0x19021302070c18021611040905060702061902160611160c06030506010e0a05040b0604121211030403170307300e010c1d12030c070504060e0906360102 66
    0x250001403403e9501a51095900d68094240c40400c0340310345403111070740340c03003c0e030402036020340c84010b80390014070144661400340e41c50703400a20907420a20f107651802581c1000b264001403061090726091282c1c02c01041c442600200c0c00514081102c104a40324807402e03100340d602c1076840e0000303c104500b4201c540b04540140c7e0b001c0045444071001103c03510300701c110b51a4049a1400240300d40d1505500100d044200181311500e03265490b0203024043c00c404005a90a000381c11822903010340164206420814040245243c28150b6980c10844404468a4603403000b0100000d15554003d03c048a08400e840f42d03281c1805032140710403e01640805010310a2505141e01c1e15030016050044030805d40c05902d0f030119803460709548603481039154050a07800104558070040042c002d01c010714111030050040c0040c1810042408199000e80e07011800107070100381042595180032030820740064a0318200c0308044502c030200b50280402c844080440c2e002c440304400c6800c815401024818 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 789462239 1250 789460989 789461009
    0xc02040606030612021306170f070e010f0b030a020405040e0c030d0306150e06090603040f030e011404050607020102010e07080106030624030308180a030c2319021302070c 75
    0x2a15600124191000c071321840030303080b00c882c42038001880d02c07114450344e007451110300150940e40d5982140c4030103940340042c04290400d0141003444a024003591025180f000c2601c0d03040e52601000111007549481905589003011010502c0412207404a5004142c01001400140246100c0035225108049994801e210b03002e80e40e030013180070b809400202c50444007540ca0b010070510064070304d041204c1100341c3c0b0150070040400f59030b80381000380d8000c6010340354400a556103440e018161440c0c0000d80d42c10f12150410006d00b43c030801007260306858003568030644031912480140c1c0900041d0506000d0f0340100c603004680c2c2081584040c003142d000b1074060040b44016450903a0250000305019102104d00000b400400d00070341820360009002900a2142180d41c8425130800c1e020110440c0002e910940080501109607581081c604802c5035070b03c0444070b41c9060355941c452140780340f61003032403407200d0310b0556840f00000c0300da160755180d00b5543c541151600d542d84411601420080d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 789463489 1250 789462239 789462251
    0xd060e0901020f0708130302131a0a0f0504020a1206030602030f0f040b01061407060501091a040219030510151d040c0f2015041a010e0f0c1902060601110f0a0b150a060c0204 76
    0x280c500802d81804533a003512103c4001c9003001e0500000c0e5102d240440180910b001c0780d10412123841c40350301d0042d070150b500180c89080041801c405a6070180c451744500541d0014000840c00c0f62409a044943c141083d000b281c5030700c1101705803406140d501625062030540001181c959540140480e22204518a004255040104401c074011074075440f504454040e814032100b8003a50201e230b041003031400c000030110740d10005111120000d0034102d0010345207040c01f21052182144060040c00112003e02c95103107006801800c40041e10b40034020007085003810b142c142e81c03d2076400c40b41c3d0700100548850030950200c4901005d400d5408440500f070200351240180c004860481c161400c18681900715210749902e603400800260070000500002c00c070848040030710942e15800007403ea00503002e5032904400140044010140c2030701070f03230046035444809000c0840c200e002140c2c0138400108503103071420005485002403813402d410031803540300840c4180e00110914156403003100c00f4845 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 789464739 1250 789463489 789463541
    0x1050105060f040b0c03221e0503063103031b050c031801020c0a150e03010510090f02160516081504030e0103110d060e0901020f070813030213 63
    0x7520400720703032900e01002404244529412103000f01405100103088078142034200344010b0020360400c0412211106145080088852500600146429408084d00c080e80703020302003501c5280041200b00d0131903903c0c0580c5512040406050b0005490f88440e1621085600d0060000d05004281c2c01ca00f4800c0c032500041544141d04484203480207901039800d150030302c55031940345001c80c6411419400b910250044a4662611010040c1203460300d01e42655010303080500601503c090440c000d90410342004a0441306002400443d03101c01000190032450906210081c0500150051b04040d100e884005000c070000e42d031042c0c07030515240c84103056918001d203aa985403114512521210200000340070074001c0811118040c01070401052440b0b245000c41d55543c04040500e50300d9a641308103118554018014960145000b402149461040c44e80b044240c05210001010058005018007200c0503440c00b000040d03901030315142c00c035910201110040d100a0151144203820540f20f108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 789465989 1250 789464739 789464749
    0x9050a23040f0209090c100827072102060409061502030a0806150d06080601080c09060d0803041a010b03040201030e0c0f04020d0608030d0c0807050a080a0b0a090e0601060201050105 80
    0xc0902d0307000c04240084640ca5083c4110440010960352043c0681c0030121a252903441c1d06c3c06110b00250b81d28102d900d0a5084182640d640c440040302c3d81d86516800b60700380f40300141d02c0301504d000d6540280b03005000c25880101e500b0140c4025000500403400052002c00344c0c0062098503c00000c40e071004541c0343c0226524060101040c00080500300420a1824005480c1143c141503c0300c1c039140054102032a002c1d07a0b41544554481e43c812030040180c42030a015040c40034204958440090414800258961165150261001d10000081030400c4040b5004650310320040350719100940c0d441c207507412545c200300c5c1c0990100341011448030b0b43d54000300308941c10070300040921420030b500c0d01c203010080d08035001440e4904d907181c60105551000b04054800b007481540c0100b0b04030140c080c0280050384c0503240740c00b4080b050050400054024003055804001c0281c0002c000e80000001014605d655004000c0315262155030400c07008003160700c6050710000d400a201d166a9601403003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 789467239 1250 789465989 789465991
    0x121605070e06150f0702060f070f0308091c121a090106020a03080c0705100b0427120905060301090c0207030b0a0914060c0d1a0a0602030d05010e0606120403020709050a23 75
    0x441034000b00017107001450100080d05101e4183e000140c1041245d03920703040d228003100741c00d44c0070403e01c03020014120810414510000e000c0603903000203440000000c1c0680ca0006100641143c45e002d10032400c0000480140c0481c600420007101540d40b910f001e500c941c500007081d00040d0400001400d000d04005c119010300340e0101c000c03c0755144018064008003400a02c81e944640c0300e401c1a00b00700d81810504461040a4840301413803a564580501c0f8810340c2c1c1c00b0700003800412041000136075550310640b03044510381000418120042c44040b4201040c603000140949410742c1440400c8505078810140a88900140707070030a4500303000141d80320b0040307079017090701a070402500e02039080c140c00200720180308000708203100d032514000409402c8160010340060b8004540070565282d980552401404045089007242c1000070105007244905051942c464a503440480c081610030040d900041c00380d40020005401d0100100c0060151021a0a60124183c08281030400c00d030300c40c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 789468489 1250 789467239 789467257
    0x302241c0612150519110c060a14040f140d0e0112110a050d0b030601080a0203100903050906031e0106050405010314100504090c1d180c03121605070e0615 68
    0x81074140003ea403071007018100080c0074083e0507200c941507011040300c0b40141d00d0b104100a602a48072201c18495910f0000000d082450141c14818600c2d50620690092030b080343d000700c06031481070340c10704088000e1200c081101405204a000d507203400381d8400c06040c2c400c0000daa07564051107481002c0d0381526004900140054030400c884070003103015000034030900c41c1c14000800c1a403460700000717040810036846a250364200c404a403085182c00d004c06582080103040800c0300c0b60454800402074025042c1c8036005010010108002e40822510403070b050100d00051580b039038440c0f4008005070030030322556011074205000a804502e100311910703c55107030709003800290b626050402c4081d01e45640c090301c00034032080e80422040035106000d02d4802700c0846210460902e0040c100f5001c5070400340d85845d41041c0840309280d0b50100b41448041032010f01191500100714905407200000d450040503441413500002c0d109480741040791260300100d6140300342c1c005a001c02c0609200306426 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 789469739 1250 789468489 789468503
    0x303020a1112120903070e1603140f13020a05091312020c010c060b04020c070e041109150108041e050a0c060503040510023004110312040302241c0612 66
    0x14880c1801e4007a1002890045c02c40e45001c2c0c0d04c5854001c0d06d001034a0030340c8490103a00c000031030744e03805016410103060b8140214000d85001c124440180501614002030074080c00c0380c45d010366881051a002500300140b5034101800c048540386201014040121242c0c3c0031032010301c0c02e075030020449451590b41030f100d031000446a583e1b4040281a0407106540c415400d000094403501c080050703101510170310a40c60454100713070401000304030010364400c1c80340e18680b08002d0980154045450079400c282030030a01a140c52070b00c40225004080091a0351200b034030402c043c03100004680000320b02448a030500c02c0c5e210101216513110440d030143c09076201d4108010302904e158020490640c1d0500344400350100c4582100c64000420346000307030f000c40d450603c400e010000100c0521441c0481c0145034a00359141220014015407002900c1020308000048084040c070032020955103070241d800341e403080a0040444100b20302d130702c0c42100034600b08011450401b02510a105960841c403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 789470989 1250 789469739 789469753
    0xb0606160f021207060903170406091202121209040b10020307020d05160320032a0f12030301031e0512030a1e060503160b041a0c070303020a1112 64
    0x140d08001c14a01042243c0200240502500c80c680c103129420290100d0313540c506c1480c5c0355041150f5400070340b0305500d00c1c0d91401c0100f0050142c0010151088449184500d020b0701802e000140091504000b00d1546025401120b440003031118010402c0d4042200c0401c0519004020300c4031704244107917282d0140e482081800054500304410b01c14003446071003101c2400c8010801c2d104480d5440d032084038566521201d504c441d190400410102030800e90082041d042c0940d64a69082558807c2c04003d20f02075507000340c1615a4560298030090180144040403444100745941c1d900903c0180d40c400600c3c281d9424208006580121840d041401408030645d2802061140d034406003500c0d422039565520b1200031543d0f01c05083d81700b002c83d00000360251070801450b04042c0407407154207019003a244240000300c0007405480565009003040710b129400302024051901c68101c16081c1131184036400400c15a00159640c281392241c03058071075640e00b03d801c0c00b80342d6054261003a4640c10103c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 789472239 1250 789470989 789470993
    0x50a03030e0a0c06080a0509030910180815010801060501051801081003050f1c0201230718030f05010f1e0903051e09041505060a08072105040b060616 66
    0x3400c80c00e001041c0e40709450118189a50301810b002c1c0d02d40c840c002050380402041791620241c415107034040d001501440c44e01c100c610024507141841801c0a0a01c01c540503031076510341d481c0e4200f101504440342190001481500380f0b0200d03880134070406a01f5800d101300480c155101e48195070a004d840d1541c0d00c40d80ca0480c1c01903035800c0c3c000f081805a03030310110000012690400c0780d24510881c01002d8900741c0d0340032181201d5622103100043c150380c100760301c8170100505c00310104849141c40301c081420761161402150030b401b0100d0441e80111250341c020003030003584000400708a110b28000c0100c00172140d0f20500b501d0403500d580300340310500800c4055103170080e08055010380c13191410303a150019070706a202d9180d6082e40030180718400402d000c0f031503042912801c100140340c000302601c0d2500e07181c001034251258440d02c0c0c3c108040c8501041507c0e00692083c03d0000d0803800102d0b4204481c91000028141240c1c10b60300c0c101074034046a8181040f408036100070070001c03090540c0403950303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 789473489 1250 789472239 789472241
    0xf040905030d2706091218030206031504021c0e0106060e100314070c1e020901031707050703030c02040b0f09181e0d020601152c031002030105041503050a0303 70
    0x90344503090302100f22030103d480c010140d010b42002d070b1040c2c80014101d030300b80c1400c00ba8a00803d07400b40134412500b07a440300a441c89041c00041700d0b07044607060364903682d02108a001040e4040b00c980c001d4004100b83c1501d001c903003003214030940c00c0d480801c4010000e1801c282612010310590010481d02c41801100b0304000180c12500c91150074040780079960109502c42811041328a17100140900d0886820888001031002e00b41c03070301640d52803106880c0c0d00060a040380600c030091221140c0c080c000c0c450880c40d01038074800c0781c0010036181e2072962030030043c2c030310b5610078822032181d0302c0c05001721140d14200100340003241014206500c00d5441e03800050540ea50001c0f1072442d881501801c00c40845034001040161894501400c1709610749803010386040c0041c2c00030030410100c2031000c1080c81d03014200405030f055405440840001c41c2100d9101e44a54082c800c0c2c042c0035010708088444940c1d00254102e98003900c003080701c85002d083c04003404056000003840c0ba00300314000340c0800c7c46 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 789474739 1250 789473489 789473501
    0x50607050f090f030f060a0b040c0507050c1011100504030e0316051009051f08072a03120905011e0c27150806130615120e1603020f040905030d 63
    0x503081742ca03920003021200c0c1c50f1400446810300006c0d1281c00e110300703908040c040e824012455040c01410b0085a64034541c540070380300c001a009941061101c1c035410310500c441078075034210f2029288901608040200031b000219020f8000c11040d2001740b21506001902c0f401c0b40040941d03060445e0300381410800c881c443e041c07001e82080201075000c90181e0f00c14030b6061008220040480415210000c00381c00c2e03500c0285620144041c9e0070036121000d0420b9580272660780d020f0400175688800d45000d44216280c8811912554900815441004415405880c1200001041d4517a0008400440c02138890705802c800004542c1480000c010040c610250608034401040030a11030303c074852851001c03407142c0004001000031080c40700c1c40c1884d40001000c904850000e1001c0d0303091808011040350210340c07480c1046002c541c44210b10380140d00c00545d90844105481005940e0102820480480e02042c0d202d0981c042400c1c0341c0740360520805a03803503807100c0030710304004140e1144001050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 789475989 1250 789474739 789474769
    0x3200a03090c1703120f06060d090f060e01020c210a230f0a0914060a0e1816020609060f07050703020307021009060e0904020f0d060213030807050607050f09 69
    0xa80400214a100c0d40d1000c03d03491070541001561141716020002d09001000341c0b01c034034989504003d120040c0c842d8000c5800b619000180810058403d181c090005001030f0405000c3e540b030150401203841064000f000c060011208442461042032615072405011a202d0300441404203c00c00449004410f464440c80c82c100e00c40b000d4071240c0c8040c00c025440115060803d030030028946a10940080d4204082c03c40d0720800500180664082400c62242c2c004907424086200c0c000d20495586501703100c211255810b0b8514a401e01000312510440854200380140c0125000104445400103440d403003001802124500c90302e485209540c00d5108000503021800100440d002507260607100b0110b240d456918108030500d003940060a01100ca04003e200d81800703400c1c00091798031510502418041210030f030100d90319034944100240b01d201c0d110b6403940c84043e400028440c20901a00d8514050b03001e89000741da454070211b541d0b200e00b015020348210140907100c2981030154651003100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 789477239 1250 789475989 789476003
    0x206071803050a05010c021b010e131d010213060e18040201021606090e1303080f060111100203060108060603010f031b0e0f01031e150509070b031603200a0309 70
    0x203440b51916820300c1c0e4161410740d0160b441e0310607100b00b10360400c28050100e40f000e12007007001c0302d2400000d10b0a642c1d0001d00e446900c4076005060301100c151b00035a82c4451414928255514110307025010350464401700040300700015001444a000d01d20815181900a082400f98944010b02100c240300207401a41140300700303603901805414504600f4041c181030b4456911252404950791a0500010507107940909a1054500017a8009040c07a41004084104403541c4daa04801220015003064214145110b503054042860000f17500850289800780c0c0d40031401d60b204e10034061548000e106011b0710f02d134925010070201d0390410142c500c5e0426001c400c4c980075a40c1d84078121003c1c003641c24481d26010305004004001026102c0080080c1d0010b60f50035041040d01d420580e802100d0a40d941c06071640000b4400400c1404a0000b4042c107444940c2c50781400e507250141c81c100c00360359002203072419400c102681726800718104000d40410b003203032406813050f00c1140a444a860100c13001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 789478489 1250 789477239 789477287
    0x2001201201051017040602180d020607060b0102030906042d05090a09021807020c0118060512100306060f030614010b04270516020114011202011b020901091406030c01020607 76
    0x40704c000500e035030040e8010000540c480350082e0030100c4000701c2e03041ca140300316502044440141c4a0b14256400541c11800001e007a0f14041c006038114440c40b0340d26507004800040100700f210205512101d03007150903000585001000b554820a0314940c00780c4c66102e007072280054021941500405206c61024008201c40e10522002041d072120903030b00030016801c42c848040c03007541e100c42c00c1d4100c2d0030202191018a45070040140007889808040c1c00060b2120380080c043c1c1d807021240c00000c5510071001c00c801d80d1744600b503806400c80d42c00221501390910b15880f04116552011038165801c002c2040d03d0507181281d2140d01c8020304d01c081d403184c101c4ca102c001400e0b65510505100e00120b076403141c0c9030205004000c2c00c5072011010f6003c9003030790b078005100701a44012801049a8282442081000d210500c1d4988000649000b5440500c1400106448199820600d4446150003070411192110402c142d03d030040d52602d240103030300620004030b2407807041041e840c00404154400c0c0034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 789479739 1250 789478489 789478517
    0x50607030e0402120702060a11030610020f0a050102040e090304050604120f020a06050316051810050408101e0b090f060d020d060c02150108030301060c0320012012010510 75
    0x60741c0000c4010496264035200b00440950144021a402204840c0412107250365020955907400092f141d02e0081d065454890115070080100301c00d20440101200c222044503c0c005010390b0243c000d05003040800c0f070100311203400002c15102610402081613051609248500311818134001099682006158047c0050f0b00c45a15420103003a05076541079a03840e1001d82950144408030346102006820002940008000b03250240d0f8150200c4642142c801c99420032655801075420104150081141d041c19a4060354045410000b8108903200950780d2002c2001c11076114580c51078202a6010000c2c034070761014900d295110070014910018000c55801103a004444a84221a819a04d02000481e560100101d900b900c0c0985444213240d810b1049151f200c1c001846420b0034420b00048000c1014011880644a43c5e80d010219480420804241d40a4105101c141100510403504003805840480c01c4690b03440c401e501d6880164a80014403040c041baa22003802086505801229 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 789480989 1250 789479739 789479741
    0x308060a031a0f0619030803090f060702070f05040c08062103120a14070906030b0102073c060c0305090a09061214010605132004080304031515050607030e04 69
    0x42c0d00d010384002c007003551425001c40822400d000e0310442c0300300000d40c9441810b420b200040da055903840541c191300c9442c1c14650f0361800c14540000103090280d01e007044040d55000540e9130880f288503080c2c1102968076024441152035202000c000284160300162035402c240b00c0c803a10320042e100e01296125080751049086800c40d42042589070310050074400100e80074051702c004162925030740400c50501e02c00242050080b4806c00007450703150342503041c00303a00a101107001003003000708403000700c1c4440c1d44002c1241a8103018003943e800d280302021081d5118041c07039050350781e40c0d01d030f5048201568a0a942d65009140c1c20766020b9044440464080c44501440c0d006051280702e40c1c0b031500d65031034142d110401605204005038508102000f117507039446a1041d0048070340d0400224891a508454283c0002c2909280031403c002130000e000180000107100f01c1c1d00440c4602d050b40c00480a55040e40c1c65498030b40a04038000c04e041c4000d10704900201942031013810200aa0602d0a020034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 789482239 1250 789480989 789481013
    0x513230a0807080106050315040f17040605071b031130010504050d0f020c0105090d140c0127030219080706030204140d03090b03190908030108010b0a060c0308060a03 73
    0x8500b070700301c100100100d440c24010100505400c90181c500750024010b03140103480014805042c8090030601d620521580d520300d0007203d0750207114a43e07a40e85564024080b1740c00002d080768020041000644401040341c2c0d01c8041e01e0b40100b540024404690401c00303446055801028400d1621070118214840ca00d481141070522000101d2940b13003906003903040c6064510401d042c40a15018045200d501140021642c40f0900b405038640c8501c40210b11014080c0da0300030070000c414003000070211f04c0001c40150004099a075030300f44075412220400e401460304200d00f0f408608010510052405c40603400109a000010000503039031030303943c01d00d80400b690020022950004044c00044421150703188a01d000795017a0595030b07032a95009042445510801641003c00b20107d1180c0c0c8030341401c03c21402c100d02d8140400306079810542c010f0ba00c20300c10300b40c0035807800460820a06111103000304650803070301c83c40054805910150340340d000003410550300c40e0305007102000140749000030b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 789483489 1250 789482239 789482249
    0x30105010e15100f0c0c210b010b090d0602070305121501080f010b031b09031006090c0c05100e011103070c030f0518061303080408030703020105070513230a 69
    0x140050500d502c08400b6900c180307580030700540c0030b9020915115000a512640c44050385080b80c00c1000310705028500c0880c540100c40c02e013114404100e01c3d0320440802c0400c03d40030303c52076030b05643e90301035088640c418180419001081c0400007800302d42c3c10350250076098024140149086581810b0040041c8112200102055840141d40c0a07592001c400743c0e0108600c0f405050550420300408418000100f500115004d41c00c552500c10900318280e4660700405000c440c1d40114030b2844d880036000d54010740c54620f00c0e00b58001034843c4500c41c429800e50b04072000c2e03d00d1400d24440c0e4800340c203102e041d1452641d25040c2c001d0302c05419000a521464035135486005203100c518004200d041c00c7d4a0803020040207110800c81c0f0503032190080e54541c01142c1c0e00742d0f02c0341c40304260402c0442e20750016221401c041000610560048020454148268001c011355a20380c001911039008441c00c028564030007010501c40301c0c141820244043e03801c02d50101080d8101400038403583e4040d081 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 789484739 1250 789483489 789483509
    0x20d0c060903030f021b09060d080a051e090d26041d06120d0c0c15030603151503080d0b09190606080402090c0a09031406160507050a15020903010501 66
    0x4005040d070044d4140300000c1341e407010b40500c280c0000c0c422401101910203600c1150500045407043e95002d03510409668400d803e5030702ca01420b44050895005040c41000d003c0d8a544141540c5a200f8200e8001c40303c0244240606078090312981c45908116400e600310460840ad444141c5000034007510061840081220030368015070081c000300d2101410042c041c5000d058025030404021541d504a10001d00d8800d602c21003a05200c0d9402030b1a0b030090107a40d00400f940030781e5a60540045050302d008640c0035941d213080e1100f400c200e4502045200580c1c0c28050140700007a043c070b000b02040341d1a15404100c0f41010000a50510350640704001221003071401046020319038007030103004003840c2c14003088502e0550045816100c00810a4100c0500040e64103052350013000108040c5030000c05044044004012055450205440c601036202c1078040b035146142c42003046580550313000015080028441e035650010b54207002411000c15024805c900c070b291030900c182c174004c083c0c80c11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 789485989 1250 789484739 789484757
    0x80705130807051201052503093503070c0204020a1101020a0c02030105090307030509040f06081203010e0f0115030e030d0f05060a0803030f0f071b080a020129010c020d0c06 76
    0x4004034400b0508842d0001e0741000c00301301c0780c0b140903c0030300e00182c0d0800c1c1c0070310120f0407410102d004001c1800c00074054000050191076070031050ae8481e004401021005030000402d000420450000302c5140c000509454011001418140c001d4804400c0c542864821555081070b1381d400da8001e6510f44002410388458101945403d00440da0085903880245280561607203005040c2e10407143c1d09400341e03403600d4440300da00016510034402050a00142c9100031442d4201203001e900c20311444030380c0c5940300f0200da48240c41125141c1200c01515016259183c0100c00b603004d41301d00c15102500b400140144810042a070082210180c4035500004880c44c2a4080240410041d084245103078028000c1005003e03401003100e030001f0243c5842505652041e0701110061458003655a1401180c00e000741044400030281408a002d0b130000e00020043c0010440d6451100491180e048405890203526501401404a0103400070703016203498000c54480382104040e90b8071100c00250020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 789487239 1250 789485989 789485999
    0x314071b0b090a26040b030402132a1707110f01020c0a020909010b0d0f0809060f0301030b130803011e0b161a1006081e0f0106090e0c0a080705130807 66
    0x8a4413103c007003101d00c054281407020307030034003641070060703003d04c4450704000008181995184818903001840b00c4c42d0170301c00c0100c5170185000028110007100160f14020b0400d2400c54054901d82002c084800084245030780d48000454003809101c440700c0c1940a0318448491030b12085c00103081c03040800c4014641c00120f80705000c00200000e15440c00c0d41d00d4404c0d4210325666002a445903507030045580a40d202180c14240320b00d12a4505131684103100007030b6041714a45040245040342d024400c042c650766500316841300656809240240440310400050046091100603500341155024211007181d854110030003003544845610703100491150350036001c000c623080500140401c010628070082c2407070302401c42c03144480d0080900b07010360706000442007039480744840c0d100344040c1481c4925051400c079280803031001380690400981c140328081052284003c5141c00307880c40c1c88a00b0710f4900c4003101121000000380000342005000c00074001c243c040d1024607800340c030b0b401d030140c0b80103490700d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 789488489 1250 789487239 789487253
    0x603050309012a02040b1912120c0201021218220510080a03050904020f03100302090105010c03080105090c0c07080708010c0f0e220e0303060306070314071b0b090a 72
    0x2030506400d0507100c40c2a420840340310800ca81003213074191000b181c030542c0003000450008400b400f00400c070400842c00185007a1071441003000a00410913800115140c0308122030b0100c1103000a400b681c410081705940768800b400600e1280b0500301d05610901c009800202c111104038160700c14100b11140c000039052580c811a40c01840548074401348a140080f681d0301c0b140c01a401805009001c51a41c1060312144c0499a81c02880396025a0f00c0c58007592450703041140740402d0340641340410000c03810b9402800d100e1220394054451038039076031800d0204542c2203001030415101d58404e014101c0440c0c401c102080140021002901c0303502e0401c41020b08550b103041c402420003443d0003040e80526000b04000038805410703a04184280f2070001c0c1c200d01160151006c6d0001858071100544101020010f18041c4200b202524030310388880e8000c400755060781c400040600c00c590b01180300740c1c0c0114492080b50381c561004200c828881e4842c04ca1850048480d120b2a1b000b0740c203a40f0400c008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 789489739 1250 789488489 789488507
    0x60f0f050f071e050d0b10110d0306121103070305030705340b0a020a120302180f060901110f010c03091a15060901020114040809090901021c0c03020d060305030901 72
    0x102d2030503102c500c4140c51119001d2183c5588071040c400001000b20f0106101e800046088001038140f1800002d29000201003142060110030720b405101041c00b4014030a005660494201c1d40300c0c6620040c450b11188400041442080e40c1403040c100d00100044c024030141210f5030140c2c0c05440103195020250b010340043c01c4800041c18481d40c40c940a10414408640642e2841c41c00c064460074115826032900081d540c0180c10400c0120358070030340543c19002000d203900e00000c02003001c040003091208003000b004026502c00400e00c0071040b40d5100d00c00d60742680c01b03104d00716525207600d0114142154088004500001d44441071034091107c03066910400728000f000c1c886e102c2c03400d128610a2900c81e41140c2c5c3c0308590000d008402a0701c00d40052010610407004000300341001c1ca0035403441d80c030074143c1714000e80c100c1c1300150752001c041c0b0a4945010b00103205c2c6c0521105280200001d089810520092550a0045000c60509407007010043c40c41913000f5a581c0c00c1c4c44002400d892a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 789490989 1250 789489739 789489751
    0x11e08010209030a0b1305120a020106050a03020609041808030108030a09171e0a081206010305060d08070b0a06270e07081207020312030708150108010b030f04060f0f050f 75
    0x7004215008050701d0002d90f415040e904404800811744503542c10003000846404041c01a10078043e4400390340d08400d000f401d060702c7c182c0013040b40716518030921400709074900c0302a505c8842408a4103803820140c0002d1310050403034900c050080c0c456550b03042e40740c2003038011011070382c004030b41540115041800040980060380b074038100d0340406040c1960701d01811f0250380040a50f2800045c05407000c00058402ca0f5100211545990007891012031705c060071119103001904100108100c3d080210b040804103401c440310928088050301d481c000c5d03503000b800590006655500001d87d4180034a220b500d12001052001000005070b01c4030000c1e6820098400741c1500125000c021040c030004a00c0c01c0c10a10428660321804680006800c00521410201b06030200008021b0460b910903e0188a102c1369500c1948a400c001c00441d01d00000340100d483c0700004101040303a9009503403c060b8014441e0b18003042c0d40642c80c030b6803025600000441e400c0940c641040c00015846108150f503c41 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 789492239 1250 789490989 789490991
    0x703031e0c03180f0615050301020706051005060a0804300f020c0f061206040b04050405161d0a1508100212090a0c05010c0305070c0b120a05060a06140d05011e0801 72
    0x180c103d4413495981c100c0550b0007030456603608100703200600204110390080100600071500e42c0010304244015150403aa00c0c4035103155020041038a2405030b00352411212075640e501e0196035a6500c0000d8165100c500301c0b20304000301030088882100c840d54280810643da00c04c02c41c030a400c040649400d280001d1648150004404900f0580320881a54500d540c040700315170064842c0303c0460000c10404103041d400600301401c01c4203000000072102c5840965503141040303182d8170b0070801500e5201040301d400b085040c001081e088a4203802400062000c05041250346544141031031074115040c41c0d03001025000306070100c0c0003400d005150343c4203400e800034001c0c000e4955160880d03020b0901400c2c0c10710108400301820f05100c1c40a036043c180d403004d07030030300c00c00d407504040c40303c0d40c20042c01c3c4160041800c001a80c074400c1c5001d2140070b0180035090814070707800d14100f40c55608580e006440c500f030080c0550a042001406514002d04400c1d119058590155100022456054100e0741090b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 789493489 1250 789492239 789492281
    0x6030b0409031d0409060e160e090304270c020f0c1f0305101203080a0b0d11092a040302010219082b020703030b03070807060909020703031e0c03 64
    0x1007500500e1481c6000d081c1c01a4980300c0ea1400009130082c103032a14054a00c40c50314040e4160a04001901c1088000c1203040007406999903050f584115021100864a60802d20007080050560106a2480085d0f54254061414032121150032203d44003030500c0164003d034408240503c0500c91082021019140d40c0c0c0100c00c4040e04407103946c4e02e046000304042d9901c00244c1f003013900c500b00318041c1c1904200001d010717200b030030014420b00341520100d03a001d19100c0310030010300d054400d40d030200e0b07800980c005110207410f003080b000b007200426030181801540c8000c5442c1d1008a8810721600b04540040e841c0c03403c50000900e051621700d01c5503a070012810808000c10381c41410346c2c0441c4400611102c819a81403004031040c1c07001c40c144c940c01b50020611600305034040c1c04c440304e042d90503401c4550844e61900100d64564541c42100086220385a051100c0b08080d00145145406410f0218104c850000c7c040190740c41142c007170142c907039250f0100780c0580d8180915202c00b4082a040480 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 789494739 1250 789493489 789493493
    0x90b090114070923041d010209150405030d271d09150a1a0a0608061801050117040c030218010303020d030c0f1d06040f090501080607020a032607030606030b0409 71
    0x600401550035200d490101c0442d02c13141d640c0b6080003440d076003e05c0603c42414041081c0702c0c040d4104d20a181c0c81418244a0308500f20780e12420398044078801401400400c40c120720589481c180a003440d0742c007209000340d400d103521045501d54000c0c1010408168801c440321901024100007400748080ea0304101c00c10041c03a841c85010a0f0044001c083c00650013422800380c001105080820f5a04510a0000020015004801d0038030410040e10b040d115094110ba120064010034005c0f54081500124000c400c1c0900d200030700d41c02845000c004200c543c480e00010705032020380200c140030140141c014003c00d0f9060295008204240c1070901800c440c2c041c014145440c0c00c0417403001c000c1040d01c198858010304106d02401900501500c0d078454482c0c0c52983c69280c1130054003081803c5c83c0000030303180310000d10b6070710910306540642802e01850b03400b256200103000724a00b18200b0006d500d00d481003a500c0007405007146071400560350b850075070054150b80d09100c1452295161010b5240 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 789495989 1250 789494739 789494759
    0x9100602011118100e180603010e16090f02160b061503090d05070312060b030916050a0603020705070306050a021804200f1e040501020f0604080702060706090b0901140709 75
    0x10403c001c4540301e00c0d420640100303c0741c0a0301100c800e6405446000006444454441801e0003417500354024020700c00082400c07540d80304190064a021290b0300001c00c40561140e000d22148044a40c0c003620b4070184040052444601140c00d81c0d0401d001c5003482071518241100889890700814102c0c1149040c074607564031203604041d01824030000217880340c20036119030000c42c0c600141c03500800c00030307840780d02c1140305400c11101d12005100d04008281000020740c20281143c1001702610040c5003030a50840c065000044100d456225030000400080c0050040621900c0310343c000503101c00c102a007620305400f1800e0010b00891408140032061003004074505203200d04031854550b180d00c0c88049034058480c4512901c00c0071080341c202505c022990006000700c50099007142c41782507115011644500059500412040381081340d800141000c20180000b540a0703072001460032140d0712040f0b003501048404003143d96562035820180d03001c1400321900700c0000c1c41c203203101c2424401101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 789497239 1250 789495989 789496027
    0x10c080405060a030f0e07140111100b03010b03100203100f0803070f080408070305240c030a0e01060b0a031d031c09210f0f14070308060f091006020111 67
    0x15009080005114282c9402070300178240301403003883e0800c050710905042070f454a515019140b1521698041541c00d988103107481c005640070300303024000200702041b04100400500f45041d030955254600c481e480c0d0740c248402000341801050160766460010b44036044007507940c10040c40303071440c56000d00c100c080001c1602c1400d944064661410481c0c2e0400036168003559114130080c6c4110100401040740203e50324014000c503440d641300329100d900e010508081e00301c0d48044202c9003400014140780583d001803244030514800001d09030f86444000c190703a40554070b40c002080d00d4508074441ca2168082404c804c11014015508181200c1c2c2034103180110711100144c0c0329150b0550000340440e846412030129040b9040c0060b803805120064250080ea50514010560040d8030300c400e2400340c81c0100d030000c0c0315042a850021690340135180d20002408454020345032070500c603065281c042c00f4030f010341105040e061145141c82c90080c291011642450191882031080301483e0205a00c61 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 789498489 1250 789497239 789497249
    0x301140403030f060506130504140115260705030117060c09011101060b1b30071112011a010203090a1a390f060f06030307021504060e010c0804 63
    0x400c41e000c8503c454005040150400380d400b10b00014803404800b660300170321044801c1540d06100002c1d4a0700e6030801e2903024840d00e24104000c800404240f84103182c50001c0807811164280d051011741e010396140401200c2110100d04000014030500c901055480306d80c802d0040100380a01d0401c011056500800114078103104a100a00e6144d032402e412240240043c0300a1544401151100716041d00703010f00c400700d540c020582c0c3c448c0018440c25580703424106548060000c0d240300203c186880c0c0c858602514039000306a80d18440d0360b905c204109840b00302c100003040c1c07245484070f62020680e195503030505560040000141c1c44c2c49903049003044440503095400c51008080300c0d03440c9485007a2a00d08040302e420340e643d2512100440c1001c40074103905100700d1020001d541d59079115502041084150b004c880000c0c08d02d81c060040315030010001e82034074101501d90340070807641121844074a05880d40482c1c04d01907030354850015105014240303420301c00b11229844001e080c0c41039006d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 789499739 1250 789498489 789498491
    0x3230a020706030f021e120c040609030b0414060f010e0c041a0904090c1d0604090f122f061003020d26040815010b0f0901200609060f06030114040303 66
    0x1340b10648000b90707066640c2d031a90640c810744e00b83c00b91400c44040d0761241c00e2000041080328082150106030409440549a0503110600034506546400c0350700703c4014030460b10b2a8800c0b0607000c1c00350f030900219000704e030310428600c1d055041c0038048244010007494008039034800d010821140c090803104412404881000542d10080341000c40c010b0120840d020309160164200010300d00b4501445004200e0200030100c002e4031030344200b1003540c2d510000600000380700c41c614000b0a010f4600d03416007120504010348602446400a14000d55800c0254001e4100030b500791500b04083c402a944102e000d01e81d5000b0604550010780a078a450740003420a01c4000d001090300040e00841c12110b05503841010384480e540c2036640e6446507400c0c0401d21410529000207041202d02c81aa40c1c50050490310606104d107a1004465144250b43d0114854808081002c1da460090192a0046103036201900340c81c940513480d00400f020250005000780e00d451800c40c904552060748507001a030500d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 789500989 1250 789499739 789499751
    0x50306011101330902121e010605030402011b0c060f030f061d070e030318130b0f0f0102011404030302040302090c09031b030f1608150603071202150703230a02070603 73
    0x3c60b45601c55140c0c0007914450310015041c115400340246217445107560341c10900248200c107415482041c030a104040101ea42440400c00640c01303912480c0c102e220a075490400d118154032a42d4615403a41c1c40309010940c148006c1c00b07926454000d1110b060301010701480800d01d403212004943e14000c10002d86658082d000c00d64103403040e010408090401012a07465003691358083e0441081d501c0f80c503204202c01c01d011021031145010b107103c1c445008120f8503129003e1400c0c0a00000000784540c1155a149181e503036400d01c00001c640a03e0107954010f0326030781944144100b030600601a10003c1c80c0522600b0900d42d00042c0f01c000038505410a02d0310200141e0110303103030142040440342103009100d07080100c16040704425046500724001c541111081c104030340d5903da801d03500d05425801001051007481d05d030703160080310288098820000f50b8044510313017140d90810342e02100001c0e01c4101049801c89440e21300c18680b01c031b044219140414540000e552a945441180d081c036441328 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 789502239 1250 789500989 789501071
    0x140609030307050f0706090603050736090902030105010501050414191d1009020708040b03061504141314060d03110a0b240a0902070819050306011101 66
    0x4002e590403658400122602d00c80c1d000900ea84400302805a60b002a0007001c0000d840c40c402c1c003480f40202a0b80e184e1400955500300840c0b900d0590030b6072041c10020000129500d03007809060b540c014405240c2c00540707404a0310405007520303010ba02c5070f070400038107100c00c2c0090040c0658200e44c0e0030301250f07005050313000d80b0955107000d20a41e0017220f52400a6801e140052a050307401c0348144ae5080c482419030351168490300803800380c04005080240107100034400010301c50f00650b04140010035456425504110001155000fa040b201f0240c28945149155007046400391000c81c00d6101c0500c14002070501016020200408003403040d64ac0303030107450505014000124924014200303489a2208905107000540c4007643c01b01085080015138a1120080c0380c6000344400004200c2d0f80d5051070000307101d010750001c08090390b2051041000c4924103883e006101c002d20b00640300c0b00d440f071920070000b40c40300f039000c1e0040149074101003400c5907800c008070544d11030038044100e02004e20051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 789503489 1250 789502239 789502243
    0x405030313111503090c1512040501020d0504030225061205070c02091e01050312030c0d0e0102130513110a0f0c0c030c050910062003072406080714060903 68
    0x88440c0c03900100b001d80c03400303106001074004620445820040b41c00b002060811f01c494141e8001700e4001d851010b103d850701e40e01718554029003150141c40058109007284140c0c10440303800781d40860140c4c2c0002d600108010600c1c4c2c1ca103142240c0030307407004003840ca4414007400034004400381021156032180040c071250b0255840d0fa11441d00035000c1a43c5151006107100c03441d03c1585000c09103005000009054a00000c0110301d800c10900101e046440f4109a02c68a4000c0c4015100d115241c5500c060a884244040c01e1640380d03001d4007241052801d8280314003034458a0781c400300f003400d20600040044e040411208411202d18041d009003003c06012504141110b200504080700e1580020a00c00900000c0f42030340d80485045515440301c50043c0d03d110b410340b003200c0100700d24a0030b8504645003502e0003441c00e40044152454015595200540517084070405907901d2240080389103450404c1c400c3e80301800701c41c0001d00d50a82405078118400540840300d500c14000040c2a40d415101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 789504739 1250 789503489 789503513
    0x50a030e0312071d04112524110a0905060c03040b040b04080c010f081b2803050903090d0f02040b0901030303061401050a08130602041706090709050405030313 70
    0x5542c40000c5505100c44000c00a00d10086030600e0203004510b00c01d510b03e014800c00c4000c034050f180991a1102c0f40300300420203904040c140d00160300c00303601900820a0f00b41c1502c0c54101510034500f0b402c1840c840042140ca804401d0303400c6030001d2080d245002e40015694054800072900345880b4081d03500c0052031445180c2003140140d801203000602a80b80c40c0c054000da400c01000c0e40d901181c05070046070900e04c0303d411500058000380c0801c40341921085000c5180e0802ea0f03c0c0f52070144480e4603079510801340c19440380c05a419601c5c1000c032942c18072540740c1010400f0051440c1c00d44560000380d91034945c540182c2007042c0340c80c906046503038983c0010001000641121995a52401d0140007002e0f244650030b10301c0c0300022180700c15889102140c40103443c03602c4100803071301c4c0c50a0b4080082c120590864150703908100118465502c00200304003446058014645480c01302e038198140480395000d041000d06000500000030404429a54442d20944802c1800c1d182802d140e208030078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 789505989 1250 789504739 789504757
    0x2091e0a15050d0f02090105010302072103020d0504050307110913060e07030501060611010507091208030702010e25080d020606060d0605040f0504021e01020c061602040c0207061e050a030e03 84
    0x7070f14080a42c00c100c1c0301c0002c00095402219494032682c0e07240b00641c184c0c071039114000c0c80500303080c04e0340d5058156801c00070003c40c2c152a00604040950f501e00003125000d8030142ca0590002c1607407010803499103107503074589809580e51425070074148101c8400300320300c803001000070391109002c03401060100007900045401c02c00034411150303502d034060146190810501c8065090800140005005804480803240814200002e004050b00c4900c42500080d100d00b00315502e1351150401d0840c20021010045010300d0f14500c0745043d02a041101d82907a03200582ca5080003e10a44007a0040351541c2e00010603a009640c0f403030807150a00c0100202e411155101c3e00c2d2440c110100103540e88114407651080e21f41803803c2014119056410084040040c010b80c0b15115034500da05041001e0011000544000946180c00341d0000f42950f155003c00340051b4401034041045c0c940c00701002d02e140c407055100ca458140c417420000d06511400e00c007a01450f8485009400903e001c00803240211 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 789507239 1250 789505989 789505999
    0x1202210c15041a0106030b0d0b0a090b04141015031403040909081e16030e12010e1b1813210c0c0906140405130c060203030402091e0a1505 61
    0x300e06450310f403603080101c2000e40c00144100001254150081c8034640c03100c180105001c006a100341e403030001c0d40c2c40090040d15602e0315141480700144e02d180e107a50080380700b60488408480e0036108030340352029061400c0c1c0c240e8209510801503514620b2604107a03a08140c400c515208144d818900d10701c15075005640142c60221003805102250015065200c4104503549031007505a58403181e0707014001c0011046555102013200190003071200c030000c220080c1801c56410b40b003840b81401c440342d2500c8180305400918241500755110003a041a101045038008002e00c4051984203110400510440c418840d0010603c10300c400b0060b102c2c904506400703440030340e2482d9000100400540d5034110b1303104d54020380c042500b0225008101c160740c40e0510a206051994007004080c150107006003900c1c42030b00da01400410b90319504400900802e40082d96207061602c14840c40301002450920500c018454103120381d8064424141c22810b10b06c40811201e07100c080c10890034116502c010750013 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 789508489 1250 789507239 789507241
    0x20d111f0302040503011d101a0406060c021302041d13061a0a0f081207060605040219111f0c1205090c01020f19021201060f0b04031202210c15 63
    0x4075819001081a948181c0090161807015002681c0514014207049016000080480000c0b002940032000840c0440c1c0c941d401c540849001c64212a8160808000203000340000b070198101400402d000e07900783c0c881140b07818901a1101403d400a0700d100384007510708008a042c804690116441e6075400c034000b00562040c00710b642d2024032048030341c14090707500e05400040f6412410903180c1101c20305005000081c002809038400380d80071040c22210f0740e658000114074ac0c0c83d184007400c1c084203080307074144081c01002c01c003402c031008000d580210360b0b0040d84000f201005c0107203600420314a03402d000c124211031074030030349030202c1640310b41c090b503480c102c03c1098500000410070040f02080e000e5440030a10305c0c0015448100303500d0b52050ac035000140c00401418040340d01c0c070300000d00c0070001030515224140180c06400d0b940c0040010305022a0500034040c40ea418110414000c0c0028442144074003510801c12400d4449580c40500100d005107081c0010300064030700c108102c5405142e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 789509739 1250 789508489 789508549
    0x50304081c050402040c32041d1801060612050c120702071403070806070f050c0f0304150302090d060519110a091a0730020f0c0409020d11 61
    0x30941101c044e40304d6070401c100801014004c400c4180a01c4c070247d90310034000c992400602c5100300c2c070700025030010810000011108440d1007060404d1458501181550270101c400002c5441105035031407159243c0700c82001000d070040501c500c00f42c000320010030580c2e59160007503500d0044400d5580c1035070b6280e00b00501030394045001e00680f4800d00780d05d00313184c00310000d05607180000d0156070f0084e80203c0c0403800550180d171000c040c440701031914500d401e181d01900c50402c4c801c4e24810364240c1c0040b40c140101c0c03513440050302641c131a9150071810300348600005006403800d4007018101c55600e0010036000b5100d240c010302e0b924014201800b44455103400f254280d4098507003c00091490b02d00805c9141d1250310107200c0301100b000d03c0c0d040c201e0503214480b0310040b5550700c030304403480311881033309500d01c1d00104481d003465034004d850800d42030382000e03080003084203019100ea03103031038091001070352400b22034020704e500b000390401800b07030010209240c0d5009102e59246550680d0706091 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 789510989 1250 789509739 789509741
    0xf0c02060712021612111507060618091101030e0c0402040e040c08030702031f18030c02100828090206040b0c0f0606060306060702012703031709070501050304081c 72
    0x10340e5456080300d0f01c0142e24030200e02c010313001e8080c2e1100440c0d24402040820000302100d9520300b07000f0143e00316440c000f0b05012a40c1c1c4120001c039556512404100710803141091560b40c02503451509000400c02a91441c81184d4442400d90506a0704e0341d0407031040100300071000c5003000160046540c0c81e01e81f841c0c0300444208039130841c0c0700a030417000070130f0030003002c401e681e1401c1c0d0240040011050056040c0e8945052001d2a00d0050303951707054503480c4005e00502c042e114081d441d0203100f0030b450300501039142c4440f032410081c0070b0365409214594903007900789180c019000349052a100d03000c00c240c1e00541006a00690b006102142c04201050b8020042c20107100c5c100c2250545a4000c20317494446400700c43c5103501080500c00251123040841c002c1030318074814545101a41b01e1403000c60b640154915110741c4906442d8000e104260b04031a002e49655009a25000c551916400030b81d40c586080c02154104000480490200312214040d1100501d002c0c0d0301002e80c3d0000d00e07041c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 789512239 1250 789510989 789511013
    0x31d04020a0e0f0a030b160e0a0b0a123b0609060610020a030806040b0d020307031b061704080703050f4915121506050306010e04030f0c020607 63
    0x6101e180d44240d1076000c4e10700881020300720b82d8001c00c121055500c0b01c403583c0c1c141698050380c505010b0355200b400c41654440e5500c50203003000c20071568071900c034044014941c40b10b00380d0180002d440e040d00729510b80c1d136844000c441c51501c91044640040740f003404a240420580408289103c1c107402e100c50380c5400324070188501d00c1602c140072107540c410012680c1304910b03080034022480200c040340c03841c18907070025241d1080150400e62081c200c1e40c040b03441d092241c0d0066411000000038035180c4240180544000d00d00d500d040300505d0420303210f2400168015000a03d00c2c0c400080030001c00d40102c0a89503401c000140c01500d4911a6480c00b01042804184c81c29100022102c8c8000303440900e0029002c02240710602e91441c03600020710000c018040000d9402e5081ca03100090010503440b244800320312a80880b0380e00b9800c1e03487d4a095850a41000344a07030080c20041c8170307040c4200d4066611030b42515208030310440301503082e0b40841c1b0105010390003180010b0700c0c0044c080160140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 789513489 1250 789512239 789512267
    0x7050318091308030a090c4109011202030a120c0501150e070e01030f0903050702210d0807090f0b070b010905070c060f02041205060f01060219031d04020a 68
    0xc441682e5820700d402ca500e0400d108020240341c0c0a102107460103546078007070781160b446103039038204a41c1c40f000340c41d002900c034520303206d21203242c200c0490702c0e24072011420352010702c64900c0100310286200040c513281c00501400744411608400301c0c095690030000718107100d1300100c1c2035000d007806d48402800010041c1c0251029800c0c00081044000c40641c00412140e061442c03041c03036101d117082210f009069411a604050b1030b002908290240b0b84140c60301d140c440d4481558030304492040c0683c100b845c40720707824809003d0030a003800742c9c0301144440114030720385001d0340741d42e41714403050300c039107511b5004500b100761948030120744d01c280c0c82c00a000d2240600f0f8205204c1c2e07a2002448192039003100c00d4030011700760b02006000140c0640000c4101480d984001d810261200b81c8a03069242090041d1000c0e0301c043e09001090f80100201400b4050500c003800d0102c1e0200d442007001c1d042108001c04000002c0e600042a92a112140c441e140005000390b665214010004050311090100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 789514739 1250 789513489 789513499
    0x50a181a0a020c0303040509010e093c070503070e1e0a140603120406050c030d11040e07020705060f03150904031d0910170307080a0503040b130c031707050318 70
    0x4204044c1c540042550100d0f03a00034803040c400ea082901c264035202010346105c00794440d90488525442c810b1813811100501108541c500144540070145002c06a4cc407038402500001c205010070b89000c110301c2c007605c81c0060312207070603240c004d074041c50058401074022000e9032020620000702d020341c000d040c0f020300344110f44545d911000c0800d602d8105245107403800d0b1900304420051703640110054000064000306036800c02c2071080c0038005036042c071901400800030001d0184412003030140c0040c0c02482c540b004280c420700301000b040c0316108408180003411408400608030101e540008140d146000d084100581040d24001d09000910000391211210140c500f8805091155000b4070900764400380d8410140750051341000e0901c140102044d50000b001410041940540105402004d43d0b83e604e035a032901c5e0070070040701a80504280130360f260209803070307010500314001c4034243d0b070b004401c1c05040c000c0d511500c2c446114040c40188180004520500d1803501d09920040e110300c1030714 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 789515989 1250 789514739 789514753
    0x606090b010801150801060f020c12060a1b051e0705100504051903120504050a080f2505030a080a06051305040c0b0910180504020309060702070803040501050a181a0a02 74
    0x4204d03802c2080030b1400c000025003c0300100000c92182e078400100f05a1030050750075128490010454180218000c43d800b030380403105008100e11a841803980703103a500d414820324420340d036034014242c1c400c0ca10f00c688001c4940503416001140075003141c21240d4804200c81100c042004c0b035a002d480200c074142e80e1805880804202c0d03404001020042e1130381652078100b62104441c5040007404094000d562912462031485c001804a9006040c00030909445a8807001d030040140304042c02012a107c501078030801d000c0001c1c00010645001030402e08200c0b03025503910324004001c10341035020300d604c44400c01d880f81c801421a80007901440c0034140c4003220341e44482c02e8882a100701324081d40c1000f241c86d0310600f128071030221402402c071031a000b030f00c0301c6d980e4400040903608150b600b0315154000d1401d0065068040010f90002c110040103941007234604030000c3d0090141c20851001e001007000007007101589061100c014005076a42c0e004818055005410380d500400b4000000d44036030b40c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 789517239 1250 789515989 789515999
    0xf13060f11071d0a0902041118041109040e0f060a090213060e0619270e12030c0913060e01051c0b04080a031e15090203040c060e0d0606090b010801 65
    0x800c2c49400d64155104114502e030260008034101e01000741141c1410350f80b004040016500d43c01525251410b001d05552a410258a0810018101d000035407182e407030302003a000c60020724401d98220090031030340007401c00601d105650400058262100c06400b0703110400c1107004207a07004000e118001c3d0b13007283c0c03882083c800b82021a000c40c0100060515080700158040c82d00c0e1901e00a4124986511003881d40c0d161501d45c0b40b5604506299500c0b4a540741603041d044440c415403a0100e5000010708950814080c004034510014100c105030000c005206441501e40da010070300d010b6400355040000d15520200a5002c44003070060380d100703c000385251080d005c500e00c1e1030304a079030300800401c1158450341c2e00c1003038660101c000c030410f05454070404800e0600d00d0740403c1130110328003404101800b02680c606002c41c100d801890034a0b10500520010070580c5c45c5280c10780e03d45080c20880c0c02c95440c0026030140140100030910350600401255410a541018520282c01c3c2c941c0b1025988230 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 789518489 1250 789517239 789517243
    0x1f02010e0d1206080708070909050f0a0605010315091a0a11040f0e181903140c0106031403120f0405070806100e011202180c09040905010501080c060405010c03050f13060f11 76
    0x510802c2e4447e030207840140610f400503806000940d1003282200c103091030510005042001889040c0c0e002c030340d508010002e1007804602d02c1d0894025407400c0241c80d4165860b100125641816081c210074032000041a00040da80240c00000f2200003694481e540e404901201c0004d500840114104c2000810055042252114a0709000e50701502c900220450740da09010341d41081541009030440b105003190040310014a58401c107500080340c05410750a203a20201c481418440e000e030710812032405c0c5814620030541e0050a0418402c2554883d400d0462500145400c80340a500480c0184044140306004d200d0844a0300518600260391b03510101e0441250031001a4101c440310303440081428858403c254410320022000342040c02590200d000c462004208a07200d030754a5005107c03401c1c04120701401890121031a9140c282030400080c00903128210050a00c100850b00300302c2c41c11500b09035000600c040841a00310727030b0748140040000c2002c01480020a41304140b0b440d1003100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 789519739 1250 789518489 789518503
    0x61214010f09050703080717030a1b05180609030f0619060501050f04090203070306150e0a051509100309050a11010807030e1207110607050114151f02010e0d120608 72
    0x10f001d805a140340d515000e0701580004802c0368414080b83c0310f86c0320a100d20000c0c50041090305000100c04070102d900e0601ca51203a04080d0038001c06110720300c030702c418484c0c031940b01100c00c0d03400c242c0307640b60700000c6403502d091044554524050002003100101c0b185210301c00071030305c80c034062010994800065030f15101d5108807202c040410403040c003669401c0d4000f507821250030300d0300003245969007034003c0c0c8003941551500005001044650361500e0040e45005c01b43c101103d00501c40f00b40b555600044c0e10618070751b035028003084030740125010300991004983e80c0e0441c0603030b0714208081ca044c595601450281d580801d61480114900714440e210310704248040400900141d04613008004040d00124003c5459070003076000910300380c6034140a03119a41c03041c00003140c0c11500c00741401d0080c80c010b1502c1044c04050365001810741d01d100322400d0f0074001c07204201e040310100307004074003410101a582c005449110290146940c0c09104c0822402e04082c0c1040719a440f03109103921281c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 789520989 1250 789519739 789519743
    0x5040602070c150f030e0c10020f01060e0105060a0f09030f05030a030c030203070c0b190e0714060a08010308030c09100c0201180e1f0e010609031e0b0415061214010f09 74
    0x460100d9600210301917441b0f807003000784140495a01c0c900c0c3d100004e0045a18480d44401a00040c0c80c000307129409008050250400c1210000705604210104105026024490301001030303c3d03480c500028041e040c90b501441d04030080d4415038005040040c1c0d2075020110440020346022034407a0303030510030310a030381c00b41c0016510108520303200d03160301d480d0300800382c80c503451460b05941c410290318040c4034081948503000702401e407041c50440b0f00398503100200855401181c04200c1603110552154205054079481003c01d612501c41300700140c407500032030481d88d0300009034580c0c1004445e0841e18400c50300380f00342e840d040940f40c1507100c00030a491601c28031a4030030203900400c141d140d070b00d1078260f02505004149a170303640d55050320420b0300c1d80a901c07070401700380a010140288240001b08120010030350248822409103a9150b00041e9002080542403201d0318a20039481d60381900700c1d0000706130840c190091884a0300303002400009084040010390f180c803180c11034003015400384c0207400f5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 789522239 1250 789520989 789520997
    0x504030e0319110f0d06090507080102161a1303080702030d0c0e0a0927020310020313050c0901230102010e03030709052103070206030703091704092016080d05040602070c15 76
    0x181c5d00342e540c04007810340300d401180e00f409540d0022500041c00d20242130b8840680d0a400414078003410710f003100e84056014442c10b9880c0ca0b0070030104030030200042a640794185844070051740d80c880d00703e0850041a101c64082e50804600052140e4030a460014200080f2101c0003410f0381e0325107660844880181d412560103585100d0b2088003600d4048003400c60010b400e4030b5000e4081c0e80e45008a83c02114088500100b50401f5014048208181c00038000c080e41c0003d00e81d41010442d82c0a05c5d8040d4240400d1140c0c450701c1186030b4400e400580d070841644045039220304110401500031040d5003e1540200329a07688030481503800c44e00300708004006400b440ca0032111b070f02170184541c0f008140303c0030b154688005200050070985001c640d5003e5440450b1214202401141a155440820202c2c05072580c0540040401a81103030156014141ea01015407036502c2c160780180507016500e12024582810041408501e4005121140c860200700504a446504043d0f008410211801c001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 789523489 1250 789522239 789522259
    0xe090d0c02031b04020706090b040c1d0a090f020a0306020a12020906090108060111190b0c0901093f05010e0a0c062003070f0209060f010c060504030e0319110f 70
    0x34411240e0500c240c3c1c058005417a10b04140c5802082d107103d684126640c1e0520f404000510040b0190300d0003501030142da90f0440070882003640c8019074080e0620010940d2011814204142400c140f40100e50140145181580c3c82c1000002500070f41c00e0000401c2d45000d0b136000740380d403078130844040b00002400e541c201500300d4011160040000d020f14148668083c50040c07002080009070194144081140041d600b50300d0b20442400c005000940d5584060041000c030f43c0c0c1040b51403081e0354103022a0000c0e140000c0d00650040000700d41030300d20441034401151460448140d01051b28001e500030b21924000c004059900e01c0414400f03020500c9118050008a100304a0034101c803c840142c080c8800c0d60040d103a06607405035104960343e0450070044c100314104485040d601c103004032a4110940d000350b0018211581000c2c00810480ea01c0001071704150060f4201d1041b03d07000b400301c4009000c40504899420a00807003560115403190103002c02c0c2ca001c021100d038001c0042e200c1260 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 789524739 1250 789523489 789523513
    0x315050d02210304231008040218091608011410060f0e04061a030a05160c0611040806092104050a0909020a0e101a2b11040e090d0c0203 60
    0x2000c91010080b5a240c00100000500c07580240d40910f40d0714142543c00c06001e440f6410000050401810002803007034a404102c0540d075001d114844940e4019000c00841d0340381c10081d402c245840b04e80503040c0f458a5004101020158050001c2d01600c5640e0f45080c0c680c2001c80501201d0303803143d000068000c0f00c1d415521441410344080c2c9400182010030465264003401440c280244414000c0c800040200825040c036800b03602e41290714140c0c90804c001e2001001021007a042501600d04c51300c0f803081102e42c102d101d048600405001050359440c1c2041d500d15030310b6105686202034a00080704000c400380e8800d03c110381c100c510040030090788074a40001d0300060201004240c0c0d0240032017100041d04080c89204922451014494000f10742c149018843c0091401203000d841c9401804880942c0401004849000030f84c02802121000488050400750881180654440c9408900010070300c0c0a0042d2901551500095800001811204a0f129005004081d601d41d1082100703000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 789525989 1250 789524739 789524779
    0xf040b06120a1a16031103060f060d060e09160501020a0b0903070b36120702060f070f0b06010e240f04030c031218052b030315050d02 59
    0x41c0c0000d401e03055400e02e00703050711240c550600d544061605690300c0c408001d0101d03e015203559080740e55040030400c00c43c103041c20540b9804018070b2507000e500342c4117104050382e45038000e680c0c0e040e088820031b00c15541c0b1031814200b1004180d951401d94400e100c10030000308000c01c40c08054a00680c02400e100d0b43c251120f0440140180c2240840d00003000460041035090321403a1281840320880c08031702d100071002a9070700300420504480d40302c6540400380c0c1201f000c20880003c041e1980c6031501c400e0140001030f4a442442421803240c040091902d04010202e0302210071207008402d883d08179510013006460b90580390340c445a0111104004d00c58461660031403050144103011010304250345035071122000e9200b86c0068403421b82c030714003c004004c401007452694842601d001c0c018a503200444104007000307405501e100701d4654822103e0864100c1032501e035074190718021000a052400c01400800500d42030714441c428020000ca09424074840044151703078050000e1515040001d680b207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 789527239 1250 789525989 789526009
    0x30c0303140f09040f021204050c1c0b0f0901021b010605190605071403040816180b030703151514040606080c071506030f03020d12090c120302100e070501080f040b06 73
    0x565130b406e1080c04000c1f68503001c580c0c4164843c030004c1c18029481020080e40e40090406c0c108200c01428402002030140342060b5002091642101c6150315840d102a0180c05013104020880c50b0081031086140815000170044440955000d1104402c41d0800051180907004150204000700041c2d00041d41d50b0650b120080740b040240c070b080646841000b030403c0759402d1000c3d0f00740440801800132001511a130401c0300d0040b82e00300640b400302c2000c40e4a80360248000f900c42c6034410001403074000c0301d030401101051801104003e10ba01d84028a08134038400d030034540078518002021039118051414039000f8140b99102500301002a9603d44001c22029004101183c0329000040020000b103410301105200b038001c6c0c41500c2000e08020104107110303094007100c60030020b203440441c1c801e841c08002d40b801111045124651414280e1074034000c0203460720f41901d000405403014202050034825620266900109502e401062044000301078801900d5485d1000200c0c0003468805244 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 789528489 1250 789527239 789527261
    0x201080c1b0d0f020c03011b0c150203010b0a0314041e111002030c060a0c050f0c010b130f0b042003041e050304050907050309070608150a030c0303140f0904 69
    0x18104400e40701e61401d00c0703842850500030562000003a003400d9018081d01c1420f070000d500800c00000c01202c1c40801c00c0303e40401d2410b000c004031128050041110000e180200303041e205540e02d583d12038040901e0f9100c100c000000030310f84210340c4924403902089030b00594004990b4038051144042090f00e5056100c0211004681c2100c003808545a4a0242000d103105030065500d41c2142d5540d2418040001d189440f490f00e0104194072198100d000e0320003181042807030644441c0c140c024113006013080c40322558400d01c2c00c1781064644040e81c102d88a103142e0201c09110071642c60081c803055401014070040c40a0111403c1c144103409000510782c05405210515002a15000810250303803e03500d050380c0d25040020b041c09103060440f11260000e48614002d499450001040d58586900e4003034002001013142c0441c5c001000b03640d82c405190301c01894401496035915003068141c0c040e100490201d44c5517680c1c03107242d010440940c1c0030003c0c6001e1b074038a8165000100002080f880740301d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 789529739 1250 789528489 789528517
    0xe0405040b1b040f030c140d05030703080c0904050f060420190e09010b071205030606070b07091809050f030310090b0301060b0d02070b010b1303060509070e10090e01090201080c 78
    0x4c1c41c82e15200c00507000f1806005076500c3e0504285091511b204c81e54030081c0a150b980c10904c000030300000440e82c0c01c0d03805203840c0015031184901504036100d42c0c0328140e4040c2c18a27043c8600c001200e002da60080b403044130200325407554480e44071a416014040311030201001e03c80702e085005e1440864001d080d8601d440e801803920350303000544241c0e003a081100c8008012800004110100c0200c9400c40d220f420100c1c11450300710300065645c401c8807401881060b884000ca0661070140380c84038003a0480700303172101446004e44604401003504420644152003003181c11010ba40010080301c0c0101e1246a281c01c00609203110103025059221000703406640e50200002c0040344803000c0c144030884202e001d039480030300781000740b444101a00141000b200c100103142c064400c08842004481c4d000102044560399092080c7c20300f451580b0440a03e904807040015a012229902c0190b40391403804204d0700c904420715074200e803a072281c0280407884500c08103a022400d035001c0d0102e417101d400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 789530989 1250 789529739 789529747
    0x10506210102071a01080f0714130e030414011701060503010320060708070219062309090702012007200f180901060504090512031b13060e0405040b1b 66
    0xd588070904c2d0a0341101c8442130b803420014007a0000900c041050790942100400d1032605200c043c83c4080351504125118000d020381c40950103640382c228904108900082c0c9484964602001280500342031f0320500040c2c020751032a103c4076200780703118142c1e0f401d607640b42d0450382182d40c0c04c00307072001d503020001030b000302850744039040d5440740300800b0b80520408000b03441d8140c5205005100361200c04000045240707001c1032055950164901c910002d001c600e070344028903408101c40749442400030350764001803400c1c1003080071501500300d00d8112003178882c109000710210309903610354040d03624010018041c1d0740420307018069001221000302001407a42e0300c11a06400000c1c4221808643d00d1881001c132010401c0760320080c41020001c10050b102030143d1600795440c0c4d40c07980303810042c1c14031682011000c02d8506031506501c569a020300c0500541c1c030307201003a00c02443ca0305442100c0014418807200d0b10f440c20b20b0b00549000700d5000d030246005444404001c40141c90100305481ca4a800b40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 789532239 1250 789530989 789530993
    0x403360506122e060c0201032a140f030a02370e12030a12050112050a0206030c070c14030712081b1218130c12020f070b070e040e01050621010207 64
    0x2010f04000f48055103640c0e520401920015041c0c031000031400411420355030381c1c2d141100380c08101c80d64201075460010001d106ea9404482d0601884a1240f0407400c080200240b0302007a5005010000c072003545420781c0c002c0da01e0380440788803406030140304640c10f140e403914400d030142c20140b0b440c150080245c0c00d2544035114842c03030f41c0c001c4d4203001b00003009000400d880c59800c0c032070741c0d0150641200085c00c08100352589681c4450b5498001d001e000000700240f41c0c0702ca400c05407544150f0042c14500301c0c903581c1e0000c401125410051078130900410a0006020701000a1002803990200e100c41c2004400d24402403111001140500d10b401307008244980c000303a0380c0c01040b200481278080c18035000040e0510415200c00e00b00f100c0305619040d000426079802c8400c0300c404000e0304001594441584484203410b01139140010180c914150034090229000000a418070700241d50400040510340140c50980710182e0728a03030440000b103400210202008426184140c02d10300142c5400c0142d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 789533489 1250 789532239 789532321
    0x708030a0b040c120e0d020c01080a0212010b07032a080307140c0706090b040501020304170a02040f0c02010c08190f020f0a090501080a23040336050612 67
    0x110800002d132010344a560210641c45502c0951081c1c0340105aa00d005401c041c1d919003050500b20306201f450030010f40700d00c180f81c0456401c40144400c20002c2d581d1010310485a4100d104103c1c00300340c0c0700018031030034000502c15484030507169660300c1034224240c503440c840d680003a20300810814a06240442e400d4254002e0201d40c1c4424014921281f800704002c0c490b1417142c1005101d000e04210400590780c0c00410356091b00e2000076a6100e400e44600c18a15240a618009404c2420300c2c070000c4c92041168422048012590000d10242c04114012681900c1c2201c103c00f000099a001c9440590a0fa101180707061b110701d001880e1912100c0c03100200d8010848000c00201d502078140714030350388001403581180300c8001c2480803064099480c000555058039030068001c40f480040c003410f114141007000b000e00c621800c0d2106100d14040c5003070074448500c01c0c1c410f031101c441c00542410248100d60700301c020600c02c1c00c05d5482e0512004001100c1507215030300229203084008082d818 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 789534739 1250 789533489 789533501
    0x20d12022821020405100e0d0f0507140303090135040f2f040504020d02040e0c190e0606032503021e04061b21120b03070b0708030a0b04 60
    0x125121034010800840c00c4290750324102070b2402d1401e0062004021580365418028030b207940710b05012000b407c41a010070803490f560000601040d42d640b030140c080c050042000e0381075841c00d8240d240e10407012003e0564a1141e50107650010790300b040c03c5001c030b001d03004190031422100300d003880d100001500c00e001c0c9040c2c185d0301520b0340c20500c0d034400104200480f0340300314004d42d8075030481081c1002e2540416400d60801060140c1d481d42c00181c115502d108000106550090041180d06001e4a07007565640007840000c1c0038103014a203409008008140406c100c0b40e450002d00360315a00c140a000007904003511002440620300800c21b4007210310000c21842c0d04450b6070041c0c03183c410035490480358149409074607144500f00703c140700241c0d00030300c583c1c150013290f0350801d2005090701c0e00d02e4500c3d0480b003a9100203002c0110051032940c2c410780d07004c16012071200a10902038240105903c034503ca100d000da0403501041284001207905015603401012060001038510081d00802d040e034413 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 789535989 1250 789534739 789534817
    0x23010213080715090b0a03020405090a090b07141c06030503040303080906014401051003020910062102090306040b060112050f011202030a0c03050705030d020d1202 72
    0x4000c100921007190108601c2c4010510090340141041100701e0280400c0c000b0f0003003260a840014030005840e000760111070007442d0142461a191821544100007804d1000003202d607441044080b0b440a80725122801aa09220182d1392412803146141401603200b4101020200d0b00ca0342c000000c0364003800034000450103a16040c1c214600f02c0012030070910141c100301c00c0c1c4445040300407003c12080343c04880d0300e01007601c5051907120f81c1e40c2c1d4034032000291440e43c01c190b0134981000de07129800c190b13100c2202d10949981045450300d070000c0340c1d804902d004080c0040c0e00c08070b0115132231910000c045500e505580c13005141c0b25801010908182c0704a4054552a880f101480800d59002d1211880018400003c001c9402c200042001018040c400c1a041d00e054000c11000d6550030703c4482ca20640c4828869112580d80c40c0164076200a44a810701c280280c0542c9207043d400070034000c015a80340da5500341107500d41083c10000350444084801051030b100203818400000c2d01400030006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 789537239 1250 789535989 789536017
    0x50d060b0f190807020715030f060b09012006130f0506070e0f040b0d170408031c0c0203250f0615080712350a051206040603020904230102 61
    0x402c94400c01c000e060740355800d003042204250800c210164042410010398000c3c4000403100020040103e020388000389914900c5860004c0000b40844c03036030010040175800307885418643c0100205a00214184000030030150020000140114441c00c2d00140d410310606582c1c8801d1542d4a41c070f49401000c07201c1e04042500f1040302d40c00c40c0f4145800a1a0150444062100c0c007046000b0410304100000c0050079250300d1007010103030481c000140c41c040c1480310222901d90013114006442c01a540031755681c22494049180c00c028070120840740b411342004d241100203002e0a00d550314800e4640e80c1900c01841c501f0140001400c070b8050030460a47c0700310f40d07010032801c0c40c1c1d045091040300e03407020b09117a405410010024401c001e940025035a0100616580c043d10a0044480e9a5601e40042c800070700045540341a03403c80702801c20a001c10005c0c080c10355030f080500045902d5800301941c05411000010b000a0908441494440b102d00030b81f80740340107800e0000d082e40c11100d04000c1d03074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 789538489 1250 789537239 789537247
    0x1209032506110c030a0f1e020604110a0308040614121305070f081005060d060e07031a07050702100908061005041512080a020313091e0605060307050d060b0f 69
    0x1000c5039000300020300c142c1c08151807400300c4200a282c1c3d80c3c410b80601c14180140001016074603030003500b200c003030301c40c000640303001400c0c51441c02074403100115421100310702030050724102c82c10b04103d003509503a40304d040c0368a06810b04100380c8240d6221000b911010001304407290100050454040c0070302840d41803407065110a1400c9410654a500706c12080c0000300c4d401c1000c44000160f03184500181c1000244c2d80c0c03120130214203510789162020341030714101003000d072602100085440442e4001c2e2299000020400710707a10105806580510000304180105e0005d0b161907011441d9689090070084105a43c4400003424803c0403100c0324007045400d001048a81014015075516101c4a0115034543d41044411a050f0b0521503005e05104c501243e0040303014020422030b4054556050300a214696568509003d826031542034000d200c009443c48240d11480d0144ca4142c0d0401881903045030303a840c40803200e503000f034403017402030b2500c668001440741d07080d200416100450115265132 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 789539739 1250 789538489 789538493
    0x10c06110d0225080405010e0105040e0103030e09070212040303080c1611010e0d21180b0a0e01030902130203060406090504320d0c15150602010f0b0612090325 70
    0x9280071204801e0142d0f10342c000c0d21000070346000c048800381c8809003001c044d80140100101c0b9980035907040712502600440000c000d0642100481940440440c1c0403031469135041d81c100d031200840c02c039801500809000030f00009004d200010b0f80281e411075800d080001c00580f02c403402d2a11001506d10714078500300803039035503401188c00384404003d80b19612021036a642e880503d54404603e07581402c6409a0303401524440c44008208240c0c4449210728103440b1031413150968481c40700c43e0040b4001421604655000380582c40c105a002001652060903c0c03a210380654001000164455030310032001ca4102401e203d01801035001e03150825490952490f1002501d9544d6024030080c40d05070040740004a00088485c1c0003091898149840d56841c54812803031050b1407110300d0f050381800004010a218169868103c4046a000303202e41a65042104c08580f01e081c8220b42145041140f2040d5660024216800170315210071a85004e001c420008408640d4603202c2c2c1841e41906d0450b41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 789540989 1250 789539739 789539767
    0x605071404080a0f020102011e050f10140907050d020703020304141504180f090305032401020c0111030702040513060b0405010b03150109210b1008070302010c06110d02 74
    0x6114402011803916041c10031071020b50b20815260010054842102c49004592003900284049909002c40c0b03201d4064444591001e07002c03c81c0c40e2042c28402343e00003244211300c0b10702e80c1c0803901002d4094130002a02300500c010004010260f80a1001c20403858543e240148020300f5002d02a501843c0c590381441503100050041034000b9103d140094101e98001c0490750490307040301d955000ea1003140086220b588040c0c029003120505040c03410510005050f00b00c0000c51082d00840e41c60003501d1005000380300003a14518100b40180d200800844065008441c15440b40c4501e104aa04150341c0c1d50001c0d00b601c004580301840d903071010808004020703240c020400f425904540606c265814075000540d00d001c002d2104070f03602c1e420365841d61241d0080300c042c0058503070a10029206040c0520000d0024221081107030070007001c10000d0381c6e12000c4941f0303805030b81e0448050540d40b46143c0044400c4403024005070f9106a9502030500550701003c0109000e0204240160b120030b24010110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 789542239 1250 789540989 789541007
    0x30c0c05060c13081b1c1707030e090108120a021501090204080d02030309060403050315090903190219030302031e040303091a10030b09100e0f190321090f060507 71
    0x13150b0348005a11a00410011000342e50804282c41201450440e0010454982c4400c0805061511064590003503880240000c1c5203980c003e44802000a826400b80a2400340074807482545410426841865401b5100100b070305119500c112400c114190300810380600b07003a8480d5494990001d07040140d204180050002c960981c0061800c43c40c00f410b1030350f03c400c40200010b08101c400000070f584d50007035003070003003008001070101604d514118803010b990350302034206483c69031445111580c0132440000c4948910302200d41421040c0026582540a0340018000c0c880504000000548461041214034850f41c0070b6074020600700f0440c1044810b01008140741e24400100604005041500e400080101d0354405000c41d19541c514030a41e00b00b014546014142500301200324030282c500060710311540c01c0000c1135414034000392041540f10b00318403500030040380507e1110302c0401c1a06240448021186101044085050b900d620303500c14120380440d015a0760300240321070568089055 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 789543489 1250 789542239 789542249
    0x70f02070803040e060a1d01090e0313050904080405030d0c151b111606030911060703021e0a0b0403110606030609100f0212040b01060f180501030c0c05060c13 70
    0x903084003420400038545a1045009494030400c0e20804035440f81c07501c0c650100102000c3c0300c2c0306242c550060b20800c00407003e104203564181007089400e400003011041b156806100595508040e152070140403d5600061040e90b11407001c1c040000d09071014040c14110200c1643c40c982109581e140188030040c9404451613441e107000100260324172000341c0e028604000b4100f01000420202e08540342c58003502401040b007407030902c001039064068005440c050300c52201d24950103852070a00a0b540502400540164000f09031104081c080b5202201c40071001404d0710720380ba01e60744518190020645045000503c000c8008041c107400348002130308030170114050142411301e01c222560312035840ca0f40b02141da079121080c0e0b1181100d60304480300c031141c4048c5410145081e06118044803002d00c1003101040c800080c00c0d004520652140019142051400151508140c0110f0040088003c40d600380040042c1800114004120031132140c004206516900d0302002d60421140c8610384c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 789544739 1250 789543489 789543493
    0x1110307080103080913060f06121103061306030804030308190c02210408100e100b130c2607111504030e011404030b0f0601110606041d070905070f02 66
    0x148000d60354400345942c1181d0308001d100361589415800200b4101500b88802c400510781200001c4584001c1035507070885131035403900d2001c0ba81981401060310f030311000c220281c0307004200258071032401300f44500002641d510000f40c80e41d01c0fa0355400741c650154205602181010017080f10603081000d80c3c4520f0714814105100d14556014042d644607201e00d401c0c002d100c0d02e2903800b45c0c0c03128544290381c01400741001f1601ea43c00b034060004010904110741c90740074010038105c00314002040c0600b60054402604441410580d03100e150020842c0e546180e04115004070070654180c10320074617400b10b603009000c03280345040114001e4a8060a10040075503070300450300705400c0700c41c9400215070198050415040700f14500380125240522903428000008021802205001094148901c14805034000c1c140d035440710300054901d1949940c40c502185d2202000a01a04107600941d20f0038403500320282c1000c0651400d1400d1a019401106d06603a54100b048115a40b040c1c60751480c4143e800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 789545989 1250 789544739 789544741
    0x1012060b12060f030c1005090a0b0703260606070212010c1805040c05070b180a032c130b0406050a080f1b06070308071407080a0f0905030304091805011d011103 70
    0x10100e92101030f03c0a010b4030811a04403406c220707d0082d012a15405401072080083c6600c0c2e21900c0ea040d00008003d0b00004c5900e4030507100c00c540c54100e0051010180a202c001d951202d040104550040200300d8000e40e031a480940c510000f40940b03400c1243c16114610a10ba040038888090038056022070300c201d00f0140045100c0c2d82280480c0c000b41c0d000740e2500440d541e60820700180324400c0b04800803501c03450039008241903000c080d40541c01515446031032031848442500203110554031040390f1000810448a10002550707010311040b180140c030100d15241d940000501410a96010504a8000781081303c2c444005100c80190b080300322890340a03207900c200201d41280250140102404041c001294a03140141d05a5038802d100030300f040c0d950800c510b002e03074007500182582d10105100f4080010301d140200e43d2182503c0c805030045080c1840c1a01001c0035201c481001003160710300501c5207020820a0250882d17445841c2c00144030358010107203180c01c6804103890f40111040500c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 789547239 1250 789545989 789546019
    0x60a0e0a0218040b012003121e01080a020906041a04050709030219030f081b031303030806221a0307030302010605091311120f10060f051e1012060b1206 67
    0xd10074001b20f07a018100085042c0341c8600d10f40c614851700a03109803c05019040160001007100380b0b40b1a5000c144a00e4085e03660b4046241d0744030a41e4000941c440040345c001071242c20f0650002020820340f401c20300c4030809200218003100c0b0203176440000264418420702c150300701000c140c5241a5520081c103002469a01e0311a181d51401000402d01000003500d070740719103e01d13060b005801529406880d0795030300d0010450000310503444200e010a814030001500c80c9440d508440019194054000091142e449002e004104060906100780585450318140d0b840c100319841c0510b109400018845050404020724894000e242c0250b0344031001059000481c400c1c411352042005803191001103882d0000c5504100704035030a400b0902c0785003096184001943c018400312805100d401c00c051b51100140000000209000d038017519401602900342c0c1065034108650a945142140005104190200541c0c4c2035501c0502071a2000c1030100d00203000c40b01e0140c0100040741c0111000b444a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 789548489 1250 789547239 789547247
    0x8070224040f0c0b0a0305190e0a080a03060803041503111e160609060c0e0411031b09090a060602191212022b150617060a0e0a0218040b01 61
    0x800090411103040001c2c820403940001c0f50025003076030311849885080c902c400900801d421101c80041c00e0300380300d0409030701a15100700019040e0b038038042c04401c2c60366154520150b0028140d0b03820182e580c100041c0c855401d10250014019a0021504400702c00c2002410394040f0341240a8052003081442080320201c550000383c0180c88032000d46420310004c0808180785005400340940303091020b01000c026295101400411781c0d610340c1002e180807001480106c0f200c003019100c840307004001281124428442d4804000e0440c01040c0c500801180801c80002040d2882e0322460b4a44600744070041d018441c20441d800c90000d01e107000e5600351210921140d44400a5082c8618400203014840694048030306d94422000c3d46011000c449590130050840c00303070030049152078094103441070106d00c0210340455005540d8560154482c005440c039412002d428243e00c030210b544005200303130364041c02d584176036464040140c48200c100381e00c100d90713000c80c00130520551900a51142c140c0e08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 789549739 1250 789548489 789548491
    0xc0a03150e190f0c09020c030c01060803090a05130912110606060a1403060d080a050a03150803030714070203070e0727090f0b09100609150f050c010212010608070224 73
    0x208440781102c0710305003407060135103c144d00100e0400340000346100010380c0000050400f02c0d0404020407070269160841c03a128012410f0b00d982c00840d00804001600c0c00890b007141603001d6060014080b0040d40c2e621034000c6006200c0d60100d41e0900040341c01040602400d075001000f0b940329460200a04401498403003008200d144808000c00880c3c030310b4aa164440140c41d0740a0501c070390340c800043d4050859046101c01c040003074106071301c8521480862814400b2a80c11100a50642c0ca980805617007600d041c00340241070250034002800075070b500f000590000e09140b002c4854074180000c00414034286000549030301c01d0703081040711601050b484d401003110500000080e9000d007803400000030303040c0c1300d080a0340300d44a0f4051150f13095100d01520111003540e1568503295503500900e6000c10341c034110060205209451900d80540254010403c208440c80018580386000082c0500b0b490280c0208000074003d4040003c015010864407000c4465400a005200c0ea107010700c80384030310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 789550989 1250 789549739 789549743
    0x603050f0c0c0a0c030b10081603030e060f160b06060310030b09030c1507030b0109080304030b0403050c0307050d1d0306190204031a07120506060901030504050c0a03150e19 76
    0x100056002c1003003070502c01d040781168400d0851107220342d01d09103140b00743c02c1902c80000c130714101200003e0701c55002032191004901c4000340b24400d840c54900355480c00a0785040303604020104a034003902d60f003500042246460490005981c0103446c1040c0080900080100307016010400900141d401c5424900302225030004035400c0540e0f660300c01034114020300300842e140384034050181a40c2c8400c00c2d0014450580380d130301000011460b500440707142d1260310413905641c004010a10100c1c44841203154001d001c0c2c28190f1500700028855442d43e4030128003680d240d00030350050000a9840107065441c0d198952959903a104a000000c1c0c40e010050040600011f00c9011a1020009034065a0007990040e40314148105007500b410780d1608100c4000d0b00107614218010702c0000070303101e12801807034090002400d00500c8001500200702c082d20944442c0308108510016540304841400590305c5100c51487c08011030100c0401c1d600d0700d403c0c10056802407204102103850b0801c5601d9155 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 789552239 1250 789550989 789551011
    0x1031404020f030f0d051b0606090a050c1b0a02090a0203090705010507020f041b02250e060409050d03090b0a060b120a0905120a020d1e050d060815040c0603050f 71
    0xb00c100380c0081c0c54003941c2805030140340507280c10200110340000240c0211006108040c0d054212a0311840d100d0380100c0303002e0342c03004e003039804600c08000980c44254050a22102c3c41d2070181218000020342000c6440b1181c0e035400b5124000c01c5088c40001a6000750b60b10105505600340040280d4403108a801058100038020803903600b507541c1c80c20900300380e40c0050700c02c200b42c00e15402c1080c4102082c3c41c80f1400b511607621101c041e450880041d04080c9000208000d8541c1840305a1000b41409041c60350300075100d0b541c007004514103016800d90b50290f601e00091001a84c54040100c05005200c08121131410300204846840d1004450b50105200f08000746566000c000b03000511403a107014180e845030498440004141d4401070001031000d0b0221411414548070403541c064002c035900000c041c01c4914202182d0080e005810341c00314440c00400d540c1d484000301c1c2c0c0781106000c240c0e8603255011041c8000d218011400d403020f010285024800d45c80d0100404e010090040e0940c1100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 789553489 1250 789552239 789552259
    0x71713050c0f060d1a0607061d0307030905040902060d0f0203010f080c090103020424081f05073e010f06051c2405040b161803060906061703180103140402 68
    0x108007a030100f45e0b001c0c40184046c2d1214414105400145146c40103030021007858507060341940000416030340c80030b0740b59488100301401c00c0b090101419404030103d07000b010900c040701c0114042e00540c00200e1502e0001626503140040900e41c0c40100e9021030020f0308440003800b126103800701a5415690199004600c2e102034840001300074481060500003509904800302d81c0c80310104000036042d03040940d40113480504a409812181c007950007001040700c2d540c50072030303880090502e10a4500f5020742c00800d41481c0310801000f041482d0f580318242d40d5038034420209000d0348a00409894103481001c4061034031300107043d000156010142200900c4030f0105141c03408801000040d4514403010320042c146494200c2c0303e000240c8072180002581010100c0113845440c4d40d28000e0b02400307000a03a00d1440d10380f1001412b9a41c07090b10480e454080c0031465a01100c1320f07186a0b0305890003169142c1210001130b1400c071032040d000b4105418500c403040540102c55100b508690100c40301410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 789554739 1250 789553489 789553511
    0x105060a1a04090e16030309030507061427060c0c13050405060106110102040b040b0a0e040e0309090a140907030605090606060304031115131518030503071713050c0f060d 75
    0x18010050b01034217150b9a50080220400d035004042c4811a48501c0c01c6403992074541c00c0035110442c00d10f0701b810880310288220048803035001c03071040441c05041c00c1298003203e2207020412560000030300e000142d02103424400541081030030b0400030034000c80d01b00a18102071b0b032969243c2c10184160000c0100006d4000981d00085d412940245013a00489a13180d5503100f182c18143c0001030b52a0100d107400784601a0750500b405124100c4c500c50019605d4540714000304500c07810064018000907a80d80560710201072130301d42581c001e85081c4020558a803444c41c0110a41d80c0090a101c880c0e084201072000503120b001c03ea075041540340c00c00080c41d0003541a03031854a9203005000e042020702e88144400381540f00311400e9418003c2ea500da4034904001491404d0b5422990a0101040b840f040c04010034400c034042e54110500f8900482c0000c5c0b094005501768105884c40110800c12141c0941008010440940c00f014141e551040031210000003828500442c0350b1082d1858a0740e400880c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 789555989 1250 789554739 789554743
    0x21030417100207030801170718020d0e01050a330b0304030c0506070908120702030a030c050a0b01080102030a0f0902101d0307080a12080c0904090218090105060a1a04090e 75
    0xc40c49051004540700d0075070b41402084104203105034100141f014900810511022030180c05031080407005010007003000400100030b51001e42c0c50002e01e543c4881c0058641e00a0080b1401000c080d030000c00d080000501c4000c410100c0c090201c00b100b25880b0790705501211a540c003084401d05c0025036280c0d5200d0900341d69100c0c2100d00142036000340e078100034400350006088010b079045081282c0240c2868081d4210342e00c902e481c041d600d644000d2881c0002481060030441c02c910400036104c02c4d9600e03580e01c001c100c0c001e810105099402004000c1c2d01c240070f00c1803041505d402c0c00203001e140e0443c0c010031400e4a03034000c900108001610100c0b109150129200e2400801508480d881565034070b20a444400c0c10400302c2d4002a00144076003541d11454a4a000700320743c10800385846840c0003000002c0a58a4049030003008803d280d0f01110f420420f00f80c802c0c20920008146071074590704202441400e5049160b6920f610b80c00f00c1019012003044e54181c498000c0001220508818014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 789557239 1250 789555989 789556003
    0xf0b030406020f0c07060e1503130606031a010315050705120405071203020f1203012117041205011b170a090212100b040c0e043821030417 61
    0x210f8209000240429120b0740007881130101d801a941d05060029540c0070807002c00f1903242075040140c014008241483c41400011030030a08c5120001340c4a0703583d07525500c024180340e0012400e204184010030074062007200c0b072a4880c3e000d11042006141c520740c00b821500805955090105003500060b00700402000004040d20700c8100004c1215903d1400035a2107101f40d83e210bd4034050811086085411102035034140da020680010747c80c246105154115025448182d0300745400100090000701644000c0c0054610201800000081400c040342901c0184440d00407100b4465218402e245d4488404843c00819803043c2d00c1d141c546035000340162441d10000713980100c08050745c0c1031108001600e1481451022000e10102941d1070812080b500d00004000c003103040042e504070729150962100c06680c020740c1c0c2d8101d04a680c103c1d0b50442c07601170341e1f02e00d08504a030714210301d151419000c03004102140312030200c401c00281c00f003d40c0f28007d6101341500000e900180700301441c4180442 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 789558489 1250 789557239 789557257
    0x8190f02030a060914040309120309031b08010b0f09130203031b0109031b0312020a03020d0e0f163f081b0303130803061903111503010f0b03040602 65
    0x5548a0034000c0210300102510721600e013103246400d040064610012005501c03c50705a110140034528025140e841d03069168012410400342c01c2010000aa0341041800703181c02401d17041049505100515084510440c120ac2c441e038010024102240c0d00c1020281d80f00c80c810075040c4412000b880841e1442c060820180c078034a07000d4000420600056020300001d07402a0340300100702c00c1c42c20b105410380320134074400303400a00000401e8202c035404e6002040710381e10624006160001c41d6982d0340441d101d14081c0101c0d0b03000941c0c80c90ba514003c0180c980701500c50f00494210510384a6a0f21b40751840c1078940c40f5107218070031a01c1401d41080c1e030710100c40c1c03030380001101024200d207041001988002510714100703100b01e140444079840001070303030710421742c0b4608148140303038544440302c440d04000c101e05d5100030f0898151060342000ea00783d6006511448807200729288160030403216040203030b042190410f05000420a10106502d03210450344420340a5640c0c1d103071030034a407010348500c90032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 789559739 1250 789558489 789558491
    0x29031605181f1407030e010309020a0504050708060108010602033f0a05040b070309050309010e030c0a090203190213120206070804031101080108010e030406080618070215150108190f 80
    0x202c10701d61903200c0d040750304403905540e0300f050780b91048400c8180c1c1c020301d100613001035900a1300e90503d5000750701002400380001c0142c0407807580e0b000080e080c0c400440c0d0b000001084541400560350b0480100c60140055002650a0a240ca1202c1141800501320500480c078180c8503503d18002c410158500f115464114004070319088142c00041d22064a040300e0003140b550003d0201480307803081c80c6501c1d0707011024500e0081c4050045a5103c0d0401c50598980a03852149113140e03680f110402c0101100d0002503120320b03180d5002c00c0740d03422880c0c861614900410891319645501c2d0f071844260741054041140074903150000c21040c0c05180801414123000190100c1070041040110206110076a81c060b81681c036042880d003610b80e6040c1d010130a0340244000e0181c24001c03a14180c2c0407001500010403106e007181d02d202d1000301980d02c02d0250704443e640201201485404c03540c40a84961440501c0130317440e0009080b80c4004000d40080c001c50301c680d400c10004d641000c41d03420030720b0360 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 789560989 1250 789559739 789559759
    0x35060603220218070c140106050a060305100e070e2d0d050114040c03050610061e02030d150602121c0b030307020d0303021c05010b0708031f2903160518 67
    0xe40750342a1328001b41c5003042e014117030f480441014044d0100b41c1c1c0c0003611031500c8034907050007070703020300000703080b9070941032150401245040c0c4200210f80f080055070b440c5030009c80c002c418000d400d01c1100b603d01e403643c02d25108241e0b80400307125200b01100e094940046005041c108a130041c01c1d22040c0740c1201069000b44400d0180c03513461281524050030a498035a1a03985503410700042a205100214809020205080548c0a0b4a003101038150040c6c0e49000401e4a07070004480000603081c2107441048002e000f9660304002452103205201c200c0c910300f030b20340e40314617400300e030842d03021442c0984943c0020207588003070081e16840e6901500d0100300001625000c0d019410220044020300e00400500640300641c0c000d5a0488204000b801c3c80c0c41441c1c0c0714505107610007080b141e0f40d26030080350281d9009041ea05040100591001c0e41621429000c0d00c1194031454040c038041078000307100340070081c40c01456104030040c982c140b642e40c594000f80404801c60b0380315102540b00c04602c2c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 789562239 1250 789560989 789561001
    0x10c111c18170d081513150801110c190b130c1d0403030506010504120b040512181c0201021c0905040c02011407020d0c0b060135060603220218 63
    0x30f1040c81c401c00c95107a0512036955040305110a045030080700e6407102c0311001454010b9503c1c1d00c4400810409035028280a40390040030f402e6584e82242046903203000140c1c00b454010910a400101c003820f280200286861303102c58405110261801503c8010803a2010402c4040032181e0000c12a9078006800703580c038000800102681181c09902107818480000d44940c070a000b114103840d2800c0d5014121251030700c80881150700140116102c2c4200c0102d2a00c0c1181c2e8405012500740b011008104204c6900070b11002ca00040c00c140500d1500400090050f078020800180c1c10720300200700c007000310303001804943d64603c40c2c2c802c1c1d401605e046000d030242070713045d0008030240501e410300942c940c850781400c84e0355040c0c4150000015040303102e1500003a01c2000000d0300100305142550300755560001441000e0006c401903051300301c0d4544107075040c100a00c2921760003138007258098103603d4108a0b07180b10050341c9000c104e11140c020035040440d690401100041e0400703843d1109607107030407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 789563489 1250 789562239 789562243
    0x2120a021602040f0e10110714070503120c0d0507080931090203070f06050a11010908130501120917070f050304060201090c09111e07060c02010c111c1817 68
    0x218484100d10302406100106c0003030140034030982020040c0c5405c1c681705594480002c40c0d90701400881e52400b42c19030001d000c1d41c08000c141c0003500c4840a095566558000007403404901e01c40b00002c1c028280310320004a0f1546c3d09580c104d01d016505d8034011044912203003201c80c580f405034010100041070744a510700065002c606014801e9080390809522084855078500403481a4400a20b040014201051046400b1703882c403807007000040b42640301076803a182660411445002d102d00800800c100c2c075a0b21220041171008003d404000080c1c081d02d400c10728000c80c2201460004001071448208041805d03154070440d004401da0342c40d5516184003e0203805646000d94110480900c0400c5c03060380340c420320b0704403007091030b641d4a010501e48004046c0444101220240b00c8140f00301070100d8024062500440e003a40e00001c0d41b2014020094003035441e1001c0a4165070055203060100700d1202d813084994445030074484079030f20114a0070460360219421100344500c034580100c11240c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 789564739 1250 789563489 789563501
    0xb0d0b0f1f05030d110f0a0f0611031306021e0c07060201060e0f01091a1915050f0d02070c12080403030323041101030f0c02100b0402120a021602040f 66
    0x2044184a84085580504145070078071401010750541103c40701c240c549024200502d140f4030340700c0544013100d4032190400d0410401040590f84081d059850741c00f0080e0601c2880c0002d10001c10702800c3d0300b0080c543c0c4e035201004640081000e81e0000b484c00310000d11200342c42c10191080c0d2120313038642c1c0b5028a162607403014130504001d9800d24030003245054500400a00c521003034180e1a2060f071a01755007038060200c0d40c070360884008102211888a44602d00da444541d05c1c0f803141c4015641c40c01035285540c08151149100304201808620060b4810300d086a02c2c0d0a1010800f40e00c031221428260320f403502d980d11200b9030041c00c5814100300030064000d4800c80780261000c02107616105800d1b590600107039444502280d2940009000525070240740200300c006150000710401d140038a00e040341c001255201c0940d00144903030400c105180a420402601a20190304050300c901d88140d412001418001003d40c021480070989020350b4034402c80c2d00d40040061128400e2031001b6401444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 789565989 1250 789564739 789564751
    0x2d0209030601120812060a05061603080105010906022508031617040b09131512050f0a030e2b0605010618031203020702010203040906060503010f080106050d060b0d0b0f 74
    0x4110000400e0300f00c40707064010725034019440d1840c1c01c0384007203540d10380403000f4981c1313030b000c1c124803004140da8842002500e850f4515840b014010820313801c0180209a0580c0014101301c14100140980da41c0480c103141c40003040c5205411600e41e45001c000c143d9490f41040407244400314508180d58200100070380304500403848201800d0158140418910481c0110590110100803200442c00d041050384045001d1410009800b003e10449602801c05a03200c404515454282c141c20312900b48020550101140002d1401f02c10710394005d80018482d20714103110382a5a22041d42106801e6003000109580c0105050083c009250203030092800780100000512126420803000e40c40c0ca10450980341c0140040c4003078600c4003000c80c060b5018440882c1180020300c00068860014000c402c0a00501c0e12126180c0d0b06082400c215060703160b00c0b02c80c0c0c070382c10b040081004d5140c2070141007220380c001d0f40129007a11014013150040c3c0f00448001c098203d003008014820003600340b80b40c0212 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 789567239 1250 789565989 789565993
    0x90102070309090b0f0d0503070204110904062c0415090501021c02161b03020904060606020d020304030b010303080601031b090302011e02070b0711030619050105011e032d020903 78
    0x6500d5444603000c0310714400b407490300550f50311718a540340d1501204901056119404980c42c1a500703a012a068074a107003503e0100c0322002c5856260761034180190b00c00340681a40c04011240c407510039000181c0180700c170740628222400880d09010700820740d90610108945c0911140e102850191300075448541d9a0b881400402082d461482c000e00072a89a40c101c1002c1c00c40400c45034480a42d6000c03038044c04801030542e5000000180c548451040c8101c0c0260340c0054841e14080c1e010f8105120f0107140c40443d002080103000290300c980c04281540d416285c0100d041e038900005034020400804004905d580703401c0741881081c1d00c40c0306201680d100b03a84840c000100080507406030a2021400c60241e0000300e000d00000d0401000b41103058042d03034111910082240220b410b02d0019506c6000807060440406a0510a401200d0040c8402c0c603110400c108507502030440740713030421001000c0503250300e40405a02585030488071884100684035990804500071940254080c6140502034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 789568345 1106 789567239 789567257
    0x109080d0206091501050904120c0b1302030f06091504050304030b01060c03031406090c07060b0a0f09050f130210170406050a14070e0d1a0901020703 66
    0x44030503401414103410145145400e20b5802006058225840d10040040307032200b2802c3c0d584a600032003c7c940482c1204d03c1106e070318000c0704001d04170072410f8051100a841d20701c01c201040d84201c0446009400c02040e154a800045a8803640c40d045a03113030308440008030090541c094440e0341500c2ca426165511045070324801e81140000444400b150300070107405109081259000000c04031007468140d000802c114402081032004d8140030a51104000164000b8130032028018955980c807034460703c0c1100c0c80144ca07c1a81006e60801003c14210502c1c6200c080c00380c3c50588181e2443c40a039002d0011181134150800c040100301d11030028050405440c0340c0c0138611811020900e0f0501001d260141c80500185202e51039014081c40f07a802d41241400641e280b00703813400290546541000141c0c900c015501c511850400400c001c0810010f45c028580b0b10302c88d849020072 = true := by decide +kernel

theorem cover : BRFrame.Cov 789388489 789568345 := by
  have h0 := BRFrame.cov_init 789388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 789388489 ≤ n) (h2 : n < 789568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
