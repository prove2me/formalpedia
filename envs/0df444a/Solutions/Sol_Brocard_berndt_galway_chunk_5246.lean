-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5246
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:13:43.679855+00:00
-- url     : https://prove2.me/submissions/e7c1df92-ed22-470a-b6f7-843788cb4412

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 943345323 ≤ n < 943525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 943346573 1250 943345323 943345331
    0x10061707051902120415030f060b0901030f0e0304060818010219030b04021912181703092503291807030203071e060215060d0201031b0c0302070b0c0c04 67
    0x80401d00a100166202261030000b1760386503207408401404001c2080c0800c0040d207081a840344540e05c0b48280c50503035012440d06454004207200450240c4800b81c290064941e5403800401071706010030050006000319194820796113001d02c410b91668a45a000981d0307a401003065240d600789004400c0180d03855403c0c001641601d410101d0028014650003000c4440c5140c003002d50103410130804081d8440c144014415815041100d008160360107000611540107002002c10010a40000d5507102c00c000081750460b035507000044405204040c40e079513042012080510030701ca60f0000c01c1c3c070b5403401441064100c03c1c54000c100901c0a00412808540c0780d00c041100c0c000006002d2100150340040032102110f8691500c03e203600c10200301c10216440050f00001e22078004191002c01d0501820321605c695901d00600c151200d003101c049040540d5130501041d0300703081040b600003800301669040c180c0c3c030480c034005e403501c007444c0c0140702c03244820f0120041c801000a900d240144068070003003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 943347823 1250 943346573 943346617
    0xb06161b080a1b06020f07051c020a090b19080d111c020c03070e04020306010e0901110316020607032708091018090b0f060a0c020301051006170705 65
    0x810503240354010356042e0281480b8001401203e650182d125606100104511a581c000503a5034401c804000040c03a002640d08102900d0b25003404200c1042d00303e014481070742e460740010b13840703991343e08091002c43d0750325800c442c81d0074098102500380c44004035100b003d605005807540e995203426101010000e070000413443c2e07001e083c0200706881c01c10140d6280ca20302841d00c040c6d111819075101c9030017441703a00310000b220f00070304007103034000c1d5000b401500c050303402c0c0001d95089240003080c244007592980041d8000d41001d40040d8401c45548510f407a15900c4000028104180074103001c08150030240c81e0902c0c06800444000b4803120086075054900c000c0c03909400500030f65042c0f541c4051b0718090400c2d0f80c3d40000300300e102c0003a5025100c100c242c840c2c01440031942c8884055070008810300034030202d0300b0000020914540385003041d90600d082d0358002400e4400c2114240a10490890200030f900c0d00003086152400324111808502d00c2e110700002c0c618026000c4805c2c04104c035a081c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 943349073 1250 943347823 943347863
    0xf042004020a0e09090a0c05060d0b03060c09090f01080d0c06150b09032a04020d02070f03090906080a05030712090e070801170c180a0b120f010b0616 66
    0x181186000900195251621510041c100d00c40d00808140101c002c100069a140d10101d2010302d21980000c428441e141807030144401c981041480d0f511042c0d4851505841c0d5408011040c40748290801141d981d04da801d060103080c2c7c03005800c40e0340705c01408006120038a00400c8017443d41c031481ca018120b5105608140020342044d00c0304c41140c6404100200e04041480c0c0200540d40c820340413240e03c040c01200c1c420300800301c0c0d141c503e507030010400040d0013440c00344c000307120f080c003010000340c148205929130840e54851244110089400e4410800c00d030200c42c0240002401900c1c0544440046034440030b880384a00c08005000540e0140c14903646030040150f403018041d014039581c05880c191402804101c4280a00f100507034813214140c0d400d5000090082c1014405080300884120350440c0c04070085026215a500544400800c1216140c604100b00c1c01d0305041c0082030b0f40788401c0c1c8181d00b1180039130326590043c40100074000707400c82c02039194504150301c41c401928200280007a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 943350323 1250 943349073 943349123
    0x7091509061d0612010503060c070f020112111204031b0f02060c0102040e0a020a02161809030201020c1b040e01062106090b0a09020a05010203040609030303020f13080f12030f04 78
    0xc50340048040785500100f9980804141071b224290708685d15901c5030794101c4c1007030142440040c00d40c002008a02c0040d4420341e0000c00c010205100400c2905041e6080a4160801082202592005404c2209241d8018140c003482c0315881e490000c5021141ca03100081302c46154064000e210000d220182d840d825412074005000390076410505050180b404006544401d04050061040c01d03182c86210740d1200f42101101c000d15410f10031814a038410300060034541c0c03000e4081d558240304103040d502003444640c3d11044038100e40c01103181c1d01010442200c1ca01c012510007070380b400d402408520340c04d00c8045072260180850000c9000e040c50200081d00c01e238400100100d10401c00d1080810803a04084a140d10031680d00581607204c2c1d00490b5240201c0c8a1100021481032080000c240244e000340410003004481500d01380c40340a4911000e021540002016408200c61118801d000d01040f02d0265400d07002602e141845903410025040140028180fa001d0a641d001e501d07060000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 943351573 1250 943350323 943350377
    0x114210141060a03061b0e1807110703050d090602070e0114121009080405040c0e01020303150d02100f08240132031501020a08070f021212030709150906 67
    0x9020302c40b0740c80142c2e584094a41105113100880c4510030100354629100400900230001c0c2c001401e0b4a980c1c09904448104248904c00101e000e0503001102181050040c0060303441d144c2c5030540c039107280160007450b104941d40700c0030404600e9401846071a401c0340b5800c0310100d08441e1400c001010994041c18100000710b540646403920410f4070030008001c015104803042220100600c0c1c00060090f940318015440e110300580040002407207801a80782d1421103044058a08008108640e01050022800c09804404030360302003440c03009a070b40003d07080d601ca03000c000050305140406000810a400005290341840710070a480714010034580049070404001c028064000b40b4800c40c40346c4a98801d5481600149410041e4825540000740c020310f00c1e80e200260501d08207035500d84102c6100984130407a07000d89091500c0b001c4200c2041060300c01c100080c80540c1c4c81c14a2a000380100030310b43c1c4131a4074680299417001226810410101c110340300c50920384c0740340b1081000d525180d02c042d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 943352823 1250 943351573 943351583
    0x1180b040302030c19060b010503090705190801180c05100e04050c0d05041a0603071410020f03030915060f061b0705060a090312050f030114210141060a03 68
    0x2081524885d24055980c001c140c0c0180810042c0c0c03608100111482d00c41169401199449a030040000c2c5c1421a124140b4000348485c440703000b40c40c1c2c442103007175800e80480d12120070a038880c1d89041c8101107403610000d0400321064048000c5024000c0c3c01841c55100d030350301c0346607100000b40300c2840040481c0c1a060401034200b04c10b02c1c151401000303881c0c401510200b020341d10710000781e06040024492050b2000c14402034100900e40c1c0c2000581241707030540c1c60440c01500c1050010b2481000954006c0c00800c01a01d8180d8403640645208280241030be8030400381215040815107800d005c03242904a80408a410300c01c40c0d100c3d2900d456519401281c100d0000506010596031009540d4164ad02c58a244480c2c0c40238480d0469207409039a1821b490313034004100411080e9400400e0001c00c86003e4050a51048205900c0100c0444001c4110a030f94440a00a80140300c00205188650404902000f02100f03885d00c120200d41c140c4560314521200d901160955442c5c0c0b4503a0002d503400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 943354073 1250 943352823 943352833
    0x150b0d0f0c0608010602190f020a030f150c05030c03040609170d0605030610060c0f150c1209030509041503080f0a090807030807060f0e1c0e0301180b040302030c 71
    0x545046400044100380c1501c0303540e00028082501e500c110304440c100d45143d8003d01c0f121004030038040354640030050850361030310043c2c2c640d00140c90b008504401140205401c441c40072850070200d15461424100b203040515015100c4000c907000003d407a0081c41c00c408003616a0307210f180490040803a144003501005541103a02210b4407484020010b401e140407040c4180350343c80080c19640c00b4191000c0d00752548550083c04221b226504070030445020303403a00c13940e40c41d03a0b8a440d80030b0058988003230181c5071650600411513420802d211685c1030303080010080400c107504d0060050188401c401c1c480d540392841d455500304603182620103950400420341c3d4400041011000310f60140708170101003036080600088604020032401c04072508107910b24944003099541c10010a411080060f8003a034407868610802010001010350320014681242511842c5030301038020000849828480d0703042c00f1f06d82c000e44406462042c2d01d113501c4059051182c5992030241d0841c010360a01c3d001c580b00e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 943355323 1250 943354073 943354099
    0xc030411041437020309150709030c050d11040506040e030d06080613030906030f09051509060a15090b15131a03250210020403261303150b 61
    0x22844480c0101c070f02520f200100e0401044007800c02d440d0060300d045801c40611030b240602500d0700150780c00103600d4180d4458400c0c403030a4a0012400b035411900041d00301c030003801008511000900500011504400628560303540c482407401c114410760b01868070758011414541351600201081c140d0801960707280c80b114000c06e40117010301c3c4200c121610444000c1080300d00140600e084041d01541c80004403410500150040c00e2819000101e0319503c2d00c00c2c1c00814824411040d03e000c0070310001300e040c1444000549802005012030307050501c0c01d21000040035010003007008407030316080c002c074191000100007681e02c0a815482800558002510310a000a411802d0141d60a0020040c0555002401c9080c07034042240c00b444503075141c512120247c4007910000d00c040b1214411582071100711061041640c01652044440d61004000c0510081c1da014050611902504409080c583da141410801490707910019000c83d030103c001541c2440b09401041c4252806070101406e085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 943356573 1250 943355323 943355351
    0x18151b0c02030d08070c03030b1c050607120c09030b04080403022206080c0d020f0a08011a0f12070e040f050d09060305092109040e01140615030106080c03041104 71
    0x80c12000300e200340200841d85a049025090007805420955034400c1050040e54054000b44041001c540d8401800e17090801c2d40101d50400b290018802c1d030103015241450f140c00381207004919075000120341000c00ca954402d038020559000c89800c10141d002607140c81c20003a01b80d00c50782d04080e42110000c1040c00e0001404800e10788000d940b003804004d915034801102d0349804003042829072040940d490385002d40b901d5511640e001030020109640b680d035880301e107400c4030829003440030040d1a90002c5040c5107040d04070744041c1241915200c08004502800c59155582c6009500c40c000003400403400b80070400c4c2c41d1481c42c90307100c2d0071208642144100608109018407c610001e42010005109034002141c1d20a051881c401790074a000c140140c4401d054001ca405550010b82c0d58607440246a002d00400c18040111180d4bd805401c048083c840c6603944503502c0c3c10301c15820801001410f62000109a00c401d14054098480c2c031246400180c141030200f1311a806030070980c0c00c024000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 943357823 1250 943356573 943356587
    0x501080f070920030a020c0d0e0321041707030609050604120507171b0102032409070503061507020301050f1503010c08310c0503060a18151b 62
    0x1031618100c424550740c40c0800710a0390400403248450950b102140c00c2c40310309441c05541c00242d02034001d8244251540011314240b5882c0c0c4d440c0000c2c0503401800b060781030a119a4028020070608441c0b50b440603001c95810340f05900c69118103c03a201e40b2004000c20901c100805181c0c012001e205851070b904245540f00d10688080d5907045070f0844001e132460044003281c1b8601d81c402d42200205403450011b01e0b854200e08204258480c5601441c00da10754284010342c452141031030800b280001c1900e0720304000001025140c090004d01d000e001c1d0403500301003540e50090302124030240b2000107015400040c068a18021740640c20300c803d00c100d50610500c1241f145034000c000c24080407860041600b0780d241a503401011940e03880204450350307008603900164203d10403844000b00101120450900c55200080d140c01c0701b0440c00744443c0c039061003203e0b007240200105101e0420741843c2200c0721207003410010b100e8449091000c642c064103810180f850700b08480301912400b603a04015245c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 943359073 1250 943357823 943357843
    0x30708031909150c020705130509060f040c14030a080301030303020a021b0a0603020f040b211006140c01150801060f1505030708130512120f0106020c01051804050108 73
    0x4081c0401078045008684a8040d90540010f0491101d4004182e0840103000d0045000214010030102266545405d00600060102500009258a004007240d030806402030100034011f44500240008902551140002d480078001d00c100d0740b00700c10300002d103009208400186042c2d0003000000626030554098446020303d07400743c9500024a00b1401001407014000030385c020a20307081071044a10070742c0903009001c0541242840c1039110543c9014941080b25860005001400048100e01200c01040e410800080f4860082420301d8406450503040e5140003035208004a900c40c99254250000c4604440f030f9455048501c0e07c0f006a0303400f80c0303d14021034102901110700000d10382a94144d00d800074400751380d61400c40d100c0c0141150f00b2080505411904030014100201180040c03008c09041045510f0441d900d150842041d40c604074003c0c8800302d5440608010010b0580202c2c0c500c040c1c003000d281c015030303070001400760001c4040340104c0707036400528010003c5400c13680041d480c41d032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 943360323 1250 943359073 943359091
    0x1807021c0509012d0509060403150209031e1b03010b180612060408040b03072a110d020d0b0910050405030a17090c010c060f020304060f050a0204050108130201020f03070803 76
    0x800c1044d018209074014480c4448058103808482400198420700c003501d0f4411004001c0e0349090369a891302c01403a0090310300341d400541e000070345406034602008180e41921a12000310314049111111035191750207000402c0c044190400c0e50b010b02d0f903082d030000c5c54480d4000c00252202c45180741a00e2402403c8411a0050701807001051084000041d014031480d0310100740d0346800e007005101000b5400103001c0100b4401c0c2440300301004c59a0107405000102140002600d0300a242407600399102d000700c0c1039010346c81c40c2c0c0c0e500d030240e1944005500d43c250000d00d00350260b120300304140d00e4000380c800544d00541c0313043c0610081140c0400201490156030751801408130440d9800034065800381d030f4000b4254440c0301540c4403940a402201062401442e0004180480002901c142d078004c5070125600d40d83e40c0c180d06411030b01f61160540008a07150214101401e000000c2c0c180003001c0c1254092030318003c0902e04583c801c0003404035030304000c0152502d401c00b0745010b07203480e0000d03199400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 943361573 1250 943360323 943360337
    0x40b0c190c091505130f0c052703070e01082d0a110a05060f040302120105010f0e070201140127020405061231030905150307050703030f061e0e061807021c050901 71
    0x30203481002070b076010141d29585100c01003007105270300c50111440340704260140605c42001a5240072000b806008000b5840605000030012a10405c21038120150818034902030442050403c8009681c5a00f03690040181c0308a804507000a0410081c60703101d00e5200c000014180090149a40a40200c070b2007512a541c1c0c0001c01e04c40213098070802d0003400b447c040b860b8010014400680402e6410403454000001c440400309140000a40241c00202c096001c0050300501001e424880542c6004880d004508003414140062064803492003010000103084011455004c4201103002141815403031400103094850155070141e424144240c0115070300640c002118140852008140842048011301e5a654075400703903003d40020f04254109a0b6484801e28030440c0c510645001d40b2080c1c1801c0000500d034a005051050541c02c20030105000009020b15500c808941301500300e08092410155030715070004a14013040c0310f9032802c02d0307400c1042c41c1102907003100082800c01020b030ba07003070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 943362823 1250 943361573 943361591
    0x60b010309171c02160b070c050d090501080708040507090c1b0309030308090106050f01032711120c030304030602091203041d07021b09070e06040b0c190c091505130f 73
    0x2030103c5c0203c1e4142190b00703c4450764440002e4610511691058060428902c007107101d4540c81e240c25a1140b00c01702240190505001e150381001a0540c440d60600d00b02da500c1c42c1903900d00740c80712441d00c107560869886044924407a4060342d90f9040840074008001c10850990500802d8401140b00590110b81c40e140400c401d40010f00442c03003a0307100600401104522400114014000d0394400103c00c1c6021500c2d07112140111080d0505600135030f40500303040c1d1040c00700502c0205401a00080e54040070b03a821807510080b054508407904400700503154030705400402c66420751500d220328540000940880d8240001240381103c03540101d0302441595000c40036652801c0302c18614181c0340c00c40c4903191b498038103a612160f012006103000e07003400c1407010109140d90050b4208030300b2142c02044064540344104000020fa41c0850760280c2c088840740c80d05c40c4141014010064819100d05000c10201c610000c1200100700c050032192402034441c2c0c0100080c030491184040440c104034100c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 943364073 1250 943362823 943362877
    0x14100e0f0d02060f1b2a061614060603030c1e011401170c0f0d0f020f06040303020606041b09060c1109041101080a0606050405130e0d0207060305010e01060c060b01030917 75
    0xc05e11458450485c003961b01d45c104a41c0000c07540700c469980102e041004088074607420700414030040c07080720003c2055400010050511174010310250080c0e005000b88159514001402c0f102d50726810303603120801d4107039464140502500556000a00d00785400054510005400d02d1600c00790340003682d080c19528001c0059004d01e2004c2254440e40d80c036017000105402c4054007d000c0e100800707800030504250302094898200740c0c410340241c0c11140400c00035041070b0141d010f1114284002480c4144001009880c01d0307868010301c0100840c20390000208049a24440700044c0700400a0503140303414640141925402c00482d03001407410b001194200810340644030944465482d0503003086d05100501042484c100e8010100a464800703c0811140500000e81000c456a01070891070b030030800041d090b035106a001c0d0380c41800140040000d07941c000d421411140c0c1c001408902182c0181c0120301801004102600000102c8041c3c20301c4410310300148011100448103c030303070b240b82c4801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 943365323 1250 943364073 943364083
    0x30c051903090603150e15011707081314150a0c0311040519180501050a0e010e070507060902030f060108190f030f0203040b1314100e0f0d02060f1b 65
    0x200802c004000600000380a600020764040e80224101083c5540e41440d0442c1481998034040060440904401c5075078400b0715810802442c1220001a003400b110003003004000400014406504601c14003c00030590503240c4040c05500071655490700304505d0201d00341003510000e0718640780c0589070800500130b025000500c0e03800202c50381042d14000c18071040d160000048858034603015804250140030008a4070f1310340c011754001a0560400051003241011504010742c603440c0c5000400980c1c3c0789941c1d403a40500c551074800c4e190380c85440c0c0a4090a1400b2000f90f15005401005410316800540141200e2401084132001160302031071000000c4500f90140401010300f00c0200442e000328a921440b000380c1c41280c1c90f180e41d52481d241c59400505204c102c1d5841880f04000084030304004403814582251110b0b43c020054102601280c00e44030020300440b0301c900b5059190703a03080d000707403041c035006070406680e240d00661030201c40e400302d0200c00d0900310b9294908c5a07c140018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 943366573 1250 943365323 943365373
    0x10e06090919080c030c010203150114122a0d0f1b0503010506030c0c191a011d04050c0402070807120e090106271202010210050c04031e0c03030c05 65
    0x24091030200610f03254043c0d582d20010076400c40c3d100810010301c44080910007148250103221040c103161883c140010305140441e045026805418070034083e555001c000f4158000304a14020700c8141c849000c0c0c209141030240c10346000f0140881e000303991000d80d800208007243d1001040008001007406100c0481c03002504030300050701880140501e0130840000c40d0012410b0b0447c074100416402d03d189131828103080e1060041d02c0748200d0003000f82141044428044d5844070300c040c2e606040c1e440326024801c0403103a00300c01442000c1001e101c410b0206006481c0040d00c190364403141070500744d4041d03212070340c2265000b11110702a0462403180d0804c8540c40e800410803807099280000840718001c0d28909440d01103244441040444024040c0c100280112811a491010706d0300019040c50501842c088a42c1e04103410052002584000c550590303a00145039664207020300761075450080004401083c0140303400300070041c15004103a40060910660450307000e900c175090f210600c045651 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 943367823 1250 943366573 943366603
    0x2250906080105041b1406090307082d15061027081509030a1107050918250b0c03161a070201020a020a0b0705190e03010b0a05030c0d08040905010e060909 68
    0x21b80d0500701c0d1800381300400321040010215004540c440030754608101c1011545c41c0c1503542c0b40c0c14044a80e00f02040800d0f0410182e0103049070b0101c0e248072840c0030b14000d240d00c0c4190341c050030f00ca41c140c0c000c600d0803200201840f04107501380caa10b21001c2201c20607009007459032149074444001445030098a52080c0c144202850600c00b00c00c0c01680c82c468142c0c0818403501076110040360a03101c80e80351307a12a241049109401c0500102001d050116481a5040701c101c1d10b1f44c00302100c000803a030301d8200d9000100d03269445c051003581905600661034084800340402c1010014490782400f80c5806041b10600e1b4201a216008140d08030b1003801811030240c3c0100b031900000c105041c40503a03010301c0c2410401d140203000600c84100124560406022031048684641c4d50b0400344680d00f001d21040d81d10654550074000000c3c3c0d80d0f800743c10500c1c82041103400701420410030304140c4004000d10702051080d942c41e0b0001c3d15422000320782c054041c41ca881c0c0003a4400c600013540120700c00740d00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 943369073 1250 943367823 943367849
    0x10f0303030e0f060a050f061008180c0307030503041e0f03110d021f0806030c062514010e2a0d031404170c0d0302250906080105041b 59
    0x15502a03000d4400c090b564019802100c0c9022841d0005206884c401c51014800107030b6031a02c00400400c01c08050314890140b11a19a009501c03500264500e03089004c41102036082c010110025107080503c450729501030040f02d1000042083c00805481502c000d5014903181c0400050412103a102e0352050b05c1c0040e074200002c101080d4a1800c1d01d010b0403020748181d90a030000c0e000b291020366090500b5501050b00c40158988540c4000c9058118008901900d5104090070008019018540100450100c0c00a0440ca003000021140301c403a64001021120026160300517030007090800260240707402142c46103030300880300a00030342c05c61b0004202c0c00c2e113040c890001d00582542d81c1000310180038942d485005000c16110181c0300078150000014400c0d00503441440c280107480100034090b01000d80854006900450403608484a01d1a10303000c0c1c501c220040181c6a80c0c0e507020003009840c00d9400310340703104190021032080340229896041d1402a00f0440e0030304a061050014281e00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 943370323 1250 943369073 943369079
    0x80111132106020f041d04021011101d0a050307050f030a050409050702070b0c010f0e0d200c0d06020306010e100e1e150a0f0905010c0816060c0323010f 67
    0x1180d016203600400c0728066801e10b0f4442d298554404039000309150a08046c4040000318649407804200c041854607184e02c3d484d1500c1501980c0d4840e41d41140c12460b1038281c0c0003a00350405103800161300380319007200c0b14405181060350f10395019080a403454007658100c1c4541c507c0000c102d4041002c01e50f03883e80781c980f4001405000f0500078140f5011401744900020343d03c03601c0c3c4040c000304e405003000080d4403040500024101c4281250060f81508860240d07044650407007284140308540804450013140500e101da8200481001e002c4c0e03112111850700c0f010300a0603030140d845610300380c9604c442c090301103081081041070b50707164a00103100c06030741100364103040c034606d0300c00c4180300392251b8181d40c9680000c0e03101d00d072086000529407020411081448d40b01c0f54440c4d8130b01403070804500303480c03c06000922000070400c0180c100000000d0040116406080e00200300380c100c2400c21542c05101c1004010305035590702c82141c451b9040542c407100d200085418129041c10683c0b91103180b07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 943371573 1250 943370323 943370333
    0x8010e0103020f010507060209030a050d030b19030204090c0b03070807030606112e020f0a0905120604020603182506020d0210050901110d0c120203040224040801111321 74
    0x10021b0011100e03280c007400703154002d0301e080200c81c039418440d40240c01e0707500381d820004086541041c9160f01c580c504444488504003140c6c80041640e4050350b0128103648507003819024800f45600c1000c6e82d8200101f000300c0954801c000502500311503406001d0143e80e110101d480c1d900040d03500c0e0b80c0b904400c48080d006800010605030025098110405402c103842000d4100d8002d182252a5541c2c00030b08012150303030002182024090840e1030362144910011003540d0b41c01c1c000d2009000d69400070124450600c620300d4060003d410070304861707043c25a182502d8940c4440380e56080344000c00c200c00b1541600216031071280e07116990044c03423185052445400941300140001a0956841008211940b040c900410800c0102000842d800c100301c1c5005080d080500c0500e07040a10503c00d200041e960390301440c10034007c811141309811110003030803840c2d1190b0307404036200f90318120003000001803a1001d005406200600019902ea80b5102501d0003e40d1500350050b00d42c023013071042c000034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 943372823 1250 943371573 943371577
    0x20f09040c1b050f07050306250203070b0a1a0405060f09191b021c090e07110106121a01050f2715120a23010b0a03080a08010e0103020f0105 62
    0x41c0d42c03034600075400c00034010000c03811910342c05540030f4000031500a201c0500b0480300d4003c100580060040d440c2c50342521080e030311402166000351410191445034140708100780e40072107410000000395414002804002000d04045002840090b52000d08080c945889042d120b000c001d0412401410000100842c11000a200490034407402c041003680301401c4c403c04114a50002c4140c00700042801c0c0a8a843c1a0144090131030b220103446a41d42d44d400384025080b5210041900e046803107200d000d03200c070764000002c03024942c40d003c80000d550700c0c0c01290000440c06040c0080310240400c0440d140c89009009884e00001c5140c0c40c4100d6051142d41e5800140203006081c2e088100000c00b080b05100c140c0b990030858804001322280351a0800c40c606800c0340203c024441004203a640039901007024021f58035400c03100301100c01d0300c0000c1d00201545180140206509500d0f8900f48185400c81040440003030541d000201d44010840725140c1669001800403100e10b200c2401180d5036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 943374073 1250 943372823 943372841
    0x19051b2407060f020a0924050c190c0609050604080607140c01050112020f0d0c0608061201022205060f030406183005040509041502071502070209060103020f0904 71
    0x20030400081010070710b03a01c61510083c040075030141c1d4840c046140101111150341201007a40150b140d0540c4042201c40c1c003014410342401c105840e03402c0104180c2c00e1820492200000720300c0901b1040400c1400180d0300182c40f200e8031100034130380e1a0824071005020f60b02801c4076039400b40000c107040501407424000c010440d40d00d0203203410150203106003941d001380e03c1aa080083c5c041c0344021807421940307001036110103480d488407840d40c80c0c44040c002803c034890b10050145a501044d083e8454248407054030350000b00943d618004100468581c84400c0d60490054044080c04260b030319090040320302d100a4090034030304648980e00c0d0b030001001e0081401030b1031314140403044005046101d44024076045440110b80c0741407c08400008402112204010800d00304401d0029584880740c2c2c07504240c0040d255004688074424980080c4078200d80a000b0b00f00a403890308902030550007c20840380b00b5107a003649902da00d00190140e020b032801d08440c8080c2849000203d00300380e4030040b80d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 943375323 1250 943374073 943374139
    0xc0c0b16140a17131704030302010506060304050606010f1101020c03130503030c03033724050109031407032a06020c100e030703060e03070201090f0503030703050706020c19051b 78
    0x1e030b90138a684034002c5610b030214904001e01c2c042010418140c080c460035274080320a403101e0703165140565031552074001c014480380c1030000c0302e03104400b500d2154069602d5400300600841d91419520302071652030b00301d4007066090300c4250700d002c0b42a05000c010340d03102051500065080d40c03940c043c0c54080402120320b00c20f801610482914000c1e41c0f1a00039400e039001c82100040001b403103499a480c0380c81703500405807441c0080604200d240d07442140c050469420446079034402241a03141802c00e01c5952000e00603040f12a40c0d0381115000c4074005280c1e1212040c040070382a03881e10b060340c0350070950304d041c1d07070106e04150300081081c000c1090550644005056615140c0c59645680c111100503850000652021414104550704420800041d2072984c1c2c40c01100c1d8500307800a5520320030706000804100c4003003103170820041140c043d01d02c00c00c820001d680800403008588104803403440342c00d81d028820818035030340841160080c0d14500c0f00c081d00e00f590b0b0340380c68080c0c59602a1038400842d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 943376573 1250 943375323 943375351
    0x1a0a080307080f0d0c0e040f0b0303031909120f1815080c0d06030602040504111806091804260c07150c05121b030a0c060c0c0b16140a17 60
    0x44c14245482034504103816a114881070456210501c002c4030004503a80d0080e84c5050f0f0302c018682c0c3c001095a41c403402038028035003150403108404000d8050010f004166161100c50701004540246401070304444c0390f52100d07c600450101550480c125100b64180480c41e00501e010161003202d000f54001010f0702c20500c0c18a040e10342c042111029031064035480d42c003190900c228505130248841c002000816182003c440f10442c50034480c2c0c890300140718000c0026007210039151150581201030400207030000d546003a041c01840702e402015401040e81c0890120b8168a01d043c003a41c41506c207401c000e0066900b031212000240c2150983d43c0180b01d6078494413000218100520240b090854548540301c5550900031008180305502e0104160400d000c5000003940c0800070788822500460b020607100510902560100f08842024101007001402c011242c4521240d02280403055502c0710411010505101410b000d480322000c0021300f206101d484030300c104801c80d501b18220024900d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 943377823 1250 943376573 943376587
    0x120930120a1a1801121a01060c05010b0402042402030d020f04051207230d02060706090507270e010e0313030c051804290a1a0a080307080f 61
    0xa066020100c03101100c841e2110015412031160b2072103100e000c5000e4542ca20110841c01c10b0100040b41400b41c504008016001041800903000d40302540030512504000d995071039100c01004c20b00c0c200c40644142d030904d0441442401c1c40c2c400c032801c40c1e422215108040030044080600c0c0c2030846540c104610003445589000443c5100501c101c50f801802507507180d29220500c0b181464146541030940c01c030340e03410400041c1090302c07040c00d00000714044186100c803034001801c0c07044d0814042c2d0400c4001c40e08008010950b405242158021070840311119030303d8450203441c0c980d00f080c061220b221180103940b2140e02e600301346010440403001190344071905805510351b8112400c412801c81651104100f88030484120701c01800c802e41b1041c43d0885451198075201002400c0200b074250000c3c00c07081503801c07041d91002c21a610070034907451821301089401c09007074081c01041c042080000f00794258501640e4000440e1110307400f8504000340c0d5166a01c03a80c001842d03100024a00300004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 943379073 1250 943377823 943377847
    0xf010315060c05070f140919060e0106031d0d03180515010513020f070f03170f1009050f060d05070e161706030a0215040515120930 58
    0x14400307461265148003801d070050914a1030041250b01100c1c80d001c0c01e44042c4420b0b181080d13074240e140e1041d1500c0300b0a888211070607600c01e2015285801c15403420030701042038100d007201f280c105e40442e0b6003070003004510303072440d01041c03602c6482280c264808400c0e198042d01941010700c00c06040c2071301111021450f12043e00389840c80900042804d68440140414507000c010000c55040000085040203800c80c1c0c4004a48a4120b01828581c002142d070010148281c00c041c0da00f10300518651110309003000750100500701900c0712504c01c0101c62000c148204a44a014421540303c104410152100000d01401c01d1b20700d102a03a00e8010201c2c003080100d641d207a06070084004c084028444010800018080e0445540600d000c1494505000c0d00d5a03001801221980e0121040b0040c1d5142c83e245a00d80c1c841e59010607001407510780d84181c0c07190818041d1035251a0410003410701c3d03513203009282d25001440242c141c084003074800030350101d800380110510240101c90b05454034100701c1c61 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 943380323 1250 943379073 943379111
    0x60907090f0b07020319030207050d0f120201060f05010f02120313080a021b0919050c09100201020c061e04140a02180601090e0c0a080603120a0c0b10050d020f0103 72
    0x121440e1404001520f104505042081c1c07a480180b5140040c1c048455a800075141c8003984946840780702e40309045402d0010b41101448400d6103d000c8003100e0f107403004068042d0000b0300c0394055a0580190015855010354030810120003107501401248400035480705203a00042c101c00c1000601e2000c010014490f00b008100498040d001040310141c03250003540300c91441c041260191247c403050040400f044062800440c135400b07400708055440c241e0302e003058003424242d20380c0702002d0b00311034000039010341c014900d1202910076203210b50396148100e601e40d8244d40e407401c50030034110002004961030030b00c0900c035648d4031001d8800346200e540000300c080200d005009500170f58442445229038008010320010000740c0d210f1403c41c80c01c100140c099019451144003032101d06800100070755803d00c03002c07640f1844505826114030011034000c02ea00f46d0301c10121441c04854000c1542c8030982041941103030b41c02040382400803026400d200e82d054020300c3c1c0c5030500d612010054400d0a071004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 943381573 1250 943380323 943380329
    0x70612021b1b0a060f030507031418070815040201111f021801030902030d0e0f0a03120906020307020d060c0e0d050d120219230c0d0305070215060907090f 68
    0x1061072810388001c040542e0303461050280300d098901000c00030160403200548500305c240c2400140765803039441c02d03005001c0b0803149500551181c4204041082c410a961260200f1a002c0703851550b1100703411070f0b840c0c000345a0b4043c4070f0f003d40300081c0190710512215200c1e640c000d0075144c01c0b200ca201e500504c9a07104240c0c0c40c1040d00410306044440500491031403d242c01d207002d009400c01034002c2503e5a4120780f60703504214100780008940d407519000206040d0000d401c4110040d6281032407185600084210800551040400112603200006841481c0d400030000e0305503624669510740186820400103041c0000c00703141c3c03412030f1b072000841c14200f8040d101604a40501d0b80c002018182000415085603205214034480c4501e11400090140180e08004644c0341c0c40b40314545c0701081020704444030309000590000607075000b141c0d034034a842036a00c0030700464807028030598803180d13549d11030340350000c20300c0000c1c07110301c2c01940050b00b00300c4034101b5040a98590625181060140d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 943382823 1250 943381573 943381627
    0x2103040605190201021c0506040902090f090d11072603070f03030608031c0b060f0d020d1404120e01030e070e040c0617041412161403040807061202 65
    0x2c601c040d940da1034200320b1491002c0742c0c4001c61801001103882c2d04110301ca010100d0300260303520001001c60700c3c0e6500c00d401030ba4004000a10906c1c0040344c41e0700c803203421204210726004402030480c0e0980030f01e01c0c0201e030a810a0190501e00d0910441e100c2045140e42c1c0e601483d4100380101181c0a020320081144e00c1c01741042c032403280d40604014003030300e40c00d80c40444168003c100c4001030300050342c0c214128078a600404180941c400000a0303550040109100b0095800a859441101c540c3c0c0148403074951414141b0a00da50903202034480341084401410b040980700381d451019101d807078030340f10840d0f05050000f4000449510685400400d410800222101d9410320080c000a107000b00002c0c085490414003a0700d104082a8030703030201410040007201c580307400020701d5034244841c001015032184016203c801d2074410b0100f14440a000351015080c5660426074501c000c41150262600a8014002180b4100c4110390b07035440803200c00045c50b03081c000702403c09014101200c4c0c00b840c034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 943384073 1250 943382823 943382827
    0xb13030609140120040b0c0f01140109050606030127110f070507050613030803131707150b030c0d0c030605040305190e0d020d081201152c2103040605 66
    0x2140c001c0c02c440c64621094018800c080c8850b400c4c0c1c940034112000c0c1c4039042080d9071506c45400300d06141c43d654006540c0c1035400c11104407401540a00f00741d040761500700081c061074440505014143c4028010b88000c62950707920401c08a80103a0701040f040040100040c1d6a4112552040260021160012607110005040d018054108015400380108445540c0390000302c840443e0445003a1200130700200010000940e422012610410f12503048140c0f14040d0a00c950803580ca54890f850440e290070011405001c501d209104015500001030010040440101e00300182c07005480400c40700f8041015011001030698080c1500840c404d40301c00391182c06043d011004568a00860782c03c100c030b1000c50080c40d03603031030b144540c14a40650301e0804518090910ba50184100d10401c0c4411500000004103040051604804000c569841601100e05000071100900c401d03034682c2e45283c0d20b001a0f09031460405910160350010044190402481440381400c58110364000300c0881e0300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 943385323 1250 943384073 943384103
    0x1103090306091e01140103230f01090201033213020d0b0105120604030c060c0905061c06050109050609150c15010303023c120c07030204140408040b13030609 69
    0x210f0908180301c400800a001408026085040452051102800c0d00802500031803103054043e01c400509462030094400c000c0c48140103901800300c800d0308074001781c43c03c41c80a00520610000c2c0c032140c0c80d8105c96110311070401e506a02da02c40050428004024181252801a44e903100d45845507842441c0c0107015600d00010442c401c40003200c8440d140d0000c10410000030350005881d021a40d015000050800807480111000300440d008282c101600081d03031b02d2181d034455003e8040b00c071508030500039140c540004640d82031803807140c90b400c8407045c0a40380c247d2404102007002c45180c00c09150802c6d000210040c64000e5201c4184200e800f114014400d055041c8000c0244c401d4403840a0181080c22a2007698030742c02c0983c141020820a40035401d00c8020b120129043d0101a9215160058580c105888059600c0200d101d1407402100964403001c0802c1c6901c103a07004a0014245407429481c0c60a0ba44060b240c0310000c03008030740210015406100e041f00060182000c0300340d03491 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 943386573 1250 943385323 943385353
    0xb0a050106020105010501171b03010810050c0903030f18041113090506011b030903020901081005100510050f07150203180f0d120204080607020109050d03050105010c03110309030609 80
    0x506070090001c42e41040c0043c0180c0e41c20940c0710926481220200e103071b40c1e030348901600c2c0011040098060381d000000000408480008882c140c6c0241814201b1180e00d030605040d004e84100341c80d458064000340149440c0e10b000201501c15031a55030002e070120856040010121002d4056022038403501050701d81302d4030b059000c101c0c00307040702080410103810144c1c0041e06226001c1603182107090350305141000c1510500e2180c1c011070b80a044c40d221543c580020940f100d03000310741000700510b4400010b0703410400316100d808030f4a028050100c00081c0150884195100104890148004010040009407040c4d003485050015201c0182c80f4142000c401c0c0d00f42107100b03081c04041d84058440005010003241801c40b4040900701001c5c1550501c8203940a4051a40a42001d001e1002040441038064024180891040098948801607242c040e0101e65081c0102400120711aa208000034041d20b07648001c0240d07003007285c1c106503d003400a8a040402c80d000e04d659007003000c1040c0c03584 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 943387823 1250 943386573 943386581
    0x1d030a050d170709030b07050c0f0319050301030b04030e030313030302060411180114030a021314101401120207060e1f0b0f101116151d1203040f030b0a 67
    0x8940c925400c0340c1410070004107280805d000140840c1c00410100e075600380a002110418041a000c1d10310000703500c46015103e030030101c0030709101c02c10750b416942950b01c10011a03050365441480441c031511680c50845a5102080c2480d4052004100c0030b12000c040c10402d000451096000f07061502d001c0c5858040c4080480e0700a00032a51400702d540c1032180c011500381035035014001c1c080300c0007003e000640780152820010707401a500c003c00c002502c065030440b80c0350501440d544202515400c54100c8180c2c00c43c450200d00000d000c4642c400c1d58481c03241c400c2d0789240600098200351450b150b040850320160300c0158540c1c0039069803a1404a04500040c1c03404414204000003520000401d1842c61003660031803184001e114924000c6029000c4084d81e09940f0007140c0c0703a58508010f000a10000e4000c140c48000c3ca0811104110320030104200080c41c0c001440c4c150f14608000d0101d0480310a00072050350000303100104003120000388500055020740027021050a10341c110904031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 943389073 1250 943387823 943387847
    0x3030b01080106020a1401020d020f0403120c0807141203070e090604180303020d1103070f0e030a110613240e03010501030812100b0406031a0f101d030a050d 69
    0x80821940104605074001c181e540303c0d1904800248032881c03441c00c6d402e0082c8280e40c0b0303214202c0d01c00304a0720710b030300c0e15500034000b620f11038150f800650120368000d0311081d0403ca07005000a201300401000690101c2141d1440442c00f011144030701304041580704290421a01c550004010808000e02d5181c98031915030801d9080c1c504100300c00f020b400501500014180240a02d500040d8540f42d49980c5e50042a1000c08226000d80300d0600a1005000004075410301000814030200200c01c1e14010681012180d4031429080004841c5000c0c06601d4021211068480401e408001000c86030803000681c1c40200b02102c040e824040b64011b40a802003c18580c001e0b0303d0400144009020102111a1841d5804100c031440d0b42e210048a680e25442d04100c0e0814000f080008081360141c01080d400c0880301c4624204010000900440c03480c9030f01c0081d803040480c81600c4100340a016101ca0322956865142034005169022031b240c00444070702240d00386c2c0542e030944195179002c100703030001f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 943390323 1250 943389073 943389077
    0xc090105030303010b09030319020c0306010e090d0c0303090204050124080f151c06091502191d04060815010807060507030311090315060a05062a1e070303030b01 71
    0x4554180380200303549000c140038240d2181000a228503141d5400c0003030f11080b099500c20070a140200b00002511031b0000c0d0506070081c40f424001064985c1784520542c0300301d820000410401001c00c0c03007200c90002201041c1d080c10b541d03d080001613103990180c240039240c15074902e44010765921a0301c2c000c400901005080094400901406000d40f02482e40c024481d0034000701540006000100d0b0059400d14150308003601581610411010760840f43c00d282c0104000055a0485d0740403000303a00c61003403840520303404402403824007401003c41e4103030550b5450ba07a11b40d1400c0d11010404480b00f503041244554810352401c1c14144040a8040c090604100900401460850040c00601034030400406241c0c5480e100001140000305590810350014100d8078030641800c6200c0d40f4580c02d4a0650190703144140114441c1440e0044921802c02010f02004481701d031a022403440d68064809401c5000341c080d0000e41081500c0c1443e00108040c014059007440c51502800f211045070171141 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 943391573 1250 943390323 943390339
    0x20d0b0405131712010e0718150915120504110d030c051e0607211e0b0306010506070f062a030b04090c060302210c07020112060e011715180c 62
    0xc01580941e50a0450710340c5c6d2054280b546070784809441800f4075050206000584000c001204452095852002c00243d2242c40c04140c58142040070944001c0c030700000300d89400000b0300d500d616070344056402409500c2c0c801c003801a1000084072511010010340000d00d0406040003885010b20424040a100300d10384008496a14003841d186d481c01041038052001701c1d001c00500813031001a02d402c454142100700011101e84074440b10807110520360105040c40d08a160945041c001500360613124014100d5090864650301c40b901054a0101110820b07151200014940402040100c005500d0300300e01c0218003403035030018200c680040c0a544200d043c0402c14004c15199240c0c40b003035500314500583d8a1900c08000400d03190201c41a40c40560740604000031000010064400c8500c01d0743c070320a003510001c2001d401c2d10f01c0d600901c004070450340e004100e205042c4440c90000d1074800709641010007450914012141c08441e42810000f40c901c03c011005400d2040407482c60040759206 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 943392823 1250 943391573 943391587
    0x1a04050127090b131406040804090906060b0a05040509280b03030712020708150c1902160e010504061203020a06180c12110108070c06020d0b04051317 66
    0x1206080e01044120140c0c01508045100201075030004210260007500c1c8040508200400007030901c4a82d40980354070080780498500c4400c00710360310b4000da0300005c03100d0400e428561410000e0100541c01c4405950328040000c2900c8001702400000341291248c40d240ca1418007404074a00005106c03a044582c047d11000e040f404400740d1109900202600150f18551000802d00d1803160350f5025002c5030110f201142d0f159400201042a24100d40a5030100110020017284594013694042090030f000e00c110107509880460094003618644115200c040490000030703400c00749908007001c0f051040c4c0061246040c140604002050b00000c8288040b0b659200251101d44814004141d15240d101c0140d00045c5081c061407003603003214901d00503544e60b0b58040000c000411040301c0c0200c254001400c150701400c44181300d815161941420b82509984103002540400004e482c01c0b541d42000b905292101d1003924071802851007039007070070341160410700c1283c3c40644568550070030411001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 943394073 1250 943392823 943392839
    0x1403190804060e100f050d0605030114011a040602060c030705070c0825080c01080a0f1107291603020f040603021e0307050f03091504030903060b101709011d011a040501 74
    0x8034240d0803171362030b103991601c05040d003000c05456182e2025600d90b080400180c4480300d141c0e400350480d00340e005d261910980080f003194550040303200b4040960043e82c00580742c01800d00096610034810301e070091030300000390745101113104517801103002e903030080300c081c0300c4010165a2000c030917008001c54903065182038031280e559800007000d00c1c100440d41c00843d020b00010b4000c400170b0a115002032000c802c0c0310040590b03a0700146815243e001ca032403042e13451f8254400b8900f60381d420320141200c803542d401134013011040d6640e614504159003009031618400c4984041c3c006005079039000360f41d0b00340000700031204141c3c84464040c1c5e07500400a022401c0c0e0040300f25031500760b1030b0642ca07880350703a180390b03260a00b1901038440700900818400c00007050360092084c42624826030b0200301c84c030350070010300200000c042414404600918210290220621011580501e5240010595201c0680c0110318480389006040c01603442e600c81c40a8405103a9401041c5c4900780c030100b0043d8544200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 943395323 1250 943394073 943394087
    0x80d050414040207150c030c18150503040f0507030f0515101205010b040f050610080708070509031f06091a1003091a131401090209011403190804060e10 67
    0x1442d10495000034402d08122080c580310040b448003030403c000c1d400c05c0030300150241c0a02d401520010742102183c031050070001d0120001c1c1c6a45811003021700500c86010341c1c3d55072024009075028200701c0300d00e00009208000907000f03076103e05d40600071141c0a1410320320344801c0c0c02c102c03c1c09c2104001003140c140d541800c91303011501261902c000c502c1c228200300b4010440e650800ea04141800c4522a24040f1604140d0003140e080d22403c054981e1208222860001525400b001855a80100300d03454410809088a20001810790381418401d00080010700c40e0310b410003140741d48a500800c69040288612404641d80d0711304803c01f03851040001e050001d04003031032418076036191005014094420f00004000c0d003282d440b5801424005441101c026200008480e62901402d240c060380c00180183c000081d8007030200703926a42401014201b9007102603500e81c0601c9003000d08802000c0e1040103045180c05051210707a20360500c480200400030030703016103003d07118030700f00b001c03078251301807071f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 943396573 1250 943395323 943395359
    0x30c0c032a0309030a2901090501060906080c07030e0a0b0a02011401050301151217030c0904050705070809130b040f0e010509190303020904110a08090717030f16080310080d0504 78
    0x20f204191101000c3c01007442001c6c10045c059001d5070030700210b0107030800c0d4011416142035490b10203010703640d918115480c0c50102d4401e20403100900030200083e0140d40c400350aa00c005020081641d128a0b15403119003103080c03540010303034417005282400c040c04080c0602510042d0001d0041f06494104110321040703034480c0007100303070014108509025424020490362064007503519075034109080c20b1045a00728007003062050340307800d0120f44424002d0301215045031f4890303220341c00c20103030908101c005d01454104800322921140840c900340d4491142803106140b220001400c10b58440c0b0041c02c482c00100456901e6100d081c401040000500008440d560b0600c4c0150341c61000d032002c00c01800154440b044103100100c0d0002ca21230704060002d104842490448244903a1030750f0b230092207a0502d4501600b90002c01034501c0030b50040c002080b00129086001070743c0045a0399105042c6d00443d1500803910852805100e240d01c1800020300104080c913201d030a1500340020003100c0f60807070b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 943397823 1250 943396573 943396583
    0x20409020d0b1f0509280f08060a1a01051612030e010f02030705030f040309150809061605090f040908030c0a021e030412020d020d0602030114061905030c0c032a0309030a 75
    0x85100c6d01c2e59480c2d8101403e0780601030460908855840818801c021158001d0411601031040000d0740100c8601c1501218130341c10b424288480d10b03800040d00d10380d00c000086107008001c03841d51030204242d24640c50b014240d07554001907043c2000070321402c46403100b0b40080014010814403403025070007801c5c0c80e04249000d80440003a251842c1c10b5903042c03000e078041d510b949000480319174083e40040500340300c1c8410105a0314113603502050002004109040d1002181d81072060035031500303111960503035558000d000001c030010310f629030b11259002110552010000061081c00391607042c4510701440914000442e002c480401d1b5140d102e010320b000b0000c00c00e440c242490300755a90480650070a5401402504480020341440c41c0a9402401600c0011148403007075622802c000d000c17640200300720410b101d110307205580215229030000c1e06a18220f501070204402c540810f100400d4265403585c1504880d0340d6414160084c9103201d0303281c031380c1d07a003013030004004d0794401140751118590b0203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 943399073 1250 943397823 943397839
    0x3030e060403120c0c05030607140a02030904060b040603060f06080103060504033b0d021305060127060201050a0501080a141c020f120a020706080a020409020d0b1f0509 74
    0x4200414401e0141d684064080f0a004075030180094018001190b4940645c80000600e41c946017070595440d410340d00240010f5100503204084007100d4090224103000784180ca28010090001a041d10101d4000410203140050100090f50700340c400c0d840200721a05249140604d040d01c00303803490741c4c1403201401a81d2240c000030201032251162000d1003886d186171003404090540408419100054180301c02d06171030944c9012450902d00b0005e826900405102d00d004841015002070800a0680b41c14031558042c000c902c40b0b407818903245951400c01144000342d00d4020001c2c2900d101400c052203039807a290040c44640004078520552a41100d10481102c0841015529002110449480c1c4032040344140604980c007152a040c0303441c007130044405504a500000700706101321045180540d01c180e60411200380101102c40d80014191001820981c0e12503005042e40c0c02070b12111035203961a0701d00c0040346400450401c444401070110364800c902000080e20511400345850f2080b405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 943400323 1250 943399073 943399097
    0x405120601051f051c15030b1501020609031b01140f0a06120f080c0703020a170c0603060306070f091203110f070b030601031a062b0c1b020d1406061809070303 70
    0x203907401846c0103110b1148800010350b624100300041d40300507100c10804051a08224403150701c0014110301805604014514107000e04064081c10b000c4110b2000c40e9548600c941003101c07144070b0340d02c2d211f190011015003403880c215410704100c0d512500030018101606031450b0120303242c074204520b02d580c00150360380c0c0d841c40f04103814589034440d031000390300c84140200030031016980da054040111aa104030b941c800030000070051640001c481c5a60182d11040000e24124858083e0300e0030010301e4180b1035030064803400550b800020020f03040e00883c408407891048000700f0418032200801c114044c0030500d0030141e4246241c4805002181010f032601000381ea08007400d18004840000140120b9440140c0348540658540f058103d0105a40c0c1c0740d115020300700903010301400c004080e03031501036880080250584040c006d010a036001007550342c1210005440000c80710351002d000004084c2403926000f003141b0030040824041e49101110180110392000044880a49a05050210743d105c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 943401573 1250 943400323 943400377
    0x605061207031112030d05070e0316050d110120010605010e0f030d030b03010b060d1a01091202010804080d0f050f070c1e03020a050d080f01050604140d0204020405120601051f05 78
    0x10341b031501045203113403006105a003a045504166100c41c00d9068075a01400325200c0130848501c1d1180c0354100b6000d12032040021619010050a0403050408161446104c8000d551110144107000c1040c0c0d0b540100f48025a007000746000d05180440f111722800700d0010110340c0381c810540c0f038141410b464602200c141d903001c1d00809a0007002030000394442401006140203404021000d10141b221b6059092055101e40319220a0f100b000d8880f00d80704070349a00440381c3ca02d0082c41030315040000c1c01070007203c0001d4040c1340040104000e0100d8030b401c0803c43c0020800d4050001401c2c44150840c00c1d0002d030480e80001151458006d0b01e0b0b5071030340ca030305007a818500c20950052a0b1f014400712080d403650001000c038002ca24000000c02141e81720800d01c02140700e0350045000c040c01ca002c805042d4030708130b155054420703c0603201506240c3c0e540c000c5429024114a40b1803d030b0021030041c0714a0501400620081801d800c61220301480d0765005005445a01c65108007245481c0d242d022800d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 943402823 1250 943401573 943401577
    0x40506031b1c0b0114030c10390303061e061d09010806011a160210031103161101090c05191a091309110d140a060506120703111203 58
    0xb000c80000015402490301e814000b5007801d00031040700000340000c60ba220f081c005803006c5840e102400d4908070000d1807400350303994000c0200f0503a4012280e200760451104607030241c001d010912070454205889450043e080c0c1d1256040160f0011079106404682210702080c1070450f181420510215401c1242032410700a90800c1240c20000c40d030000590950001a214100c458140400b001e00030690307018203130f9104641d225005101d0000884015290001c81c66460711200c0c2000900341c860883e00b540c50b50021540d440c00d540c074602c041c0030000c3e04810044c89000c03001000b044502495030301d90401845c10f0041d00d01452122074203018560842600d10007500750002e04d85415100c081e08081250310059002d40105840300d020b800c0501c49020b04201300780e12424030540c1202031310911920310f065400c142e441411182030180541401c1c0060604603001d441e01141c9480c00e10280010069071910349039690b88801010001300b001c1554290b914942202c0100072200d440c01d94502d0b40c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 943404073 1250 943402823 943402849
    0x804030e150d0203040b0124120c110f0d0216030f032001050103050a0c1d011e03020901291908100302120c0102100209030703080d020403121d040506031b 68
    0x1648000144010b006c82945d00c18100c039401503a244094440340300441081400e80307960400301c0d04d1291000f41c0700001c1d0f0000e031005615498203156a017500490b0928105543e011556142c02801c08036900c9a0f040c02103a008900103103440407403501c0d5035580c0d03080004000d03000d001c002c002d406080402e8a5440d401342c1d1201d07000000c1c050f40d6102e0528075252040d1210442c3c03426926800024008501d00005011020007080101c86a280210f05900c004071300ba154066038103000000720060740c1d88030b00d01c1d0203420f036101d40c4000c1041070041c2036600c21842114bc52913403002e012000003442201d5414204050f145000225911203800c41031250b102900b0003588410003500600340d0a00024203d030a11009900b21101a10800603050491090641081d01908414010b0001c00c598030024194010728810041c07810b44d480c0c032801c507515031020321300c0006007000c124034600e000b50390074516220b04111400c00403030501d0340c0000c1c0d4407030303040352101d400851564100c075041c3d4600e100900c0c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 943405323 1250 943404073 943404097
    0x1106220305010b03060a14040219150e1203040e070e0d0606030605060108070f09170708030a050717041503050402040b12030c07080708030a18050a180c0804030e15 72
    0x216140d15240d80a04406103115000c1d219040c0010b08041450064003101c2003140b408280035201e54080c030007410100504211483c04410000454a0940302c10991407001581c0e10300880d0b080d9020056900500542000e196000340070034840d00600780c1a141d005150303420310ba0356800761031011a1031031484100c00380840b80380560000a102c13030f50700072070703c0b6100907038400b2640c2e80d444005661210001c0100800121032201c02e005506128401400b880300341001c56800c1681e03041c00b54503680c0300441d1040082d1011950a0030400500c458400600e5a0746035681081d050046024840d0601039403081015140c0380418150740b03407640802482c117000f40c4526000c1505007040e50b60307a8000e242024070b80c803a4034800502c511021440720180c1e88203e000d94a08a19210101c03003001c042e08401540b20b400520020b03159581d0700490004002c00e501d040c0308940b0425115085078200a10802402540030401c00003c3c1d10089100c100102241c2c4d488913820f9550700040580502001000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 943406573 1250 943405323 943405387
    0x1503011104061808070605071e11011b080927010312120b100f3501061106040201050a0c08030a060906050d031d010c15050901181106 59
    0x100c05008400800075200030b9100c0d440c00c0785000050400e0344106104c2d40195410000044c41014030600060560a0280146105080c600c850f1910480803c0303000f00c41d10242261401740650308600085808110400d0385a81707000c1c141c0394200148105034016104188003800c9246c4441381418606020202481e003074210343e128604010440341c404a0075002c01c0f91400748184101030350007940d01c20100548803000b140140c3c501585ca039101c00c0f2030303401480040742d8000041070382810010000302403124041440030301125500941d0906800100401031540300204016000207180b6400c15828681b0300d50f50721031003c0840d41d0051030703000280021400028003945040c250007070340c142c035128041000082da84804006d4103002001001f0049000c40300601e0340e0011855038400c06030418141002441015510041c1c001e5140f2242030340160345a080c012030324807d110301c903c1500d2542600824030b145e034482a90307a40c0e92000251140200181490007502e080e04014000320220241c11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 943407823 1250 943406573 943406591
    0xa030510052505040317191e080106080f07030e030408060a0b01030b0306041115030408190f021e1005070921200f030f070603060b070b01060503150301 67
    0xd0041c0c0000d440d02000030201680d11941c84111801549400304651079680c41d00c1c1c42d5503900082c2d20a000c0301013100c40030030301c15107124a0000e0400018603555595450004050803024400000039450260820902d540188803058104910396003115490081208540d51500100c0c0500100b204266050001040000e8030700b0000031114041c00c03880c5018020081054011401c80355000e512540c076500c62008940425180c00496030b0360503020701041a409070405038000d440d031083d02c00701da807180001441c0501e031484240c110b40c1a455842c0c40c0820208646009554120080d4401450650302c2c4101807181c0b401c03c0100000c1a50312002e0040313162045014106898a204030700c0303e0316120004080c81c100740410412115400081c00c400c1d00342d4022003042d05481c2004e9940c0000600c114202d00303540822111184101a00062280301d0520500406540c01c81d0302180e05402c061102c1c8002034007103e4a00d05580052610644035580c01d10b200c412140c0c2c003034011381c155180c64442 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 943409073 1250 943407823 943407853
    0x1060804110613080c09090c0915030d120b0a05010e1c0b0906100602011503080f0d150f0603090503070206072a09110a021c12020301090525090e060a0305 68
    0x41c10451341030b141a00d480318a0f070418440900b008940c2032940f40c0000b0340b00005443e0001c00682c2082041c052030925054400c0400d11b03041c40c6c110f262011810500031070b41002c0f258021542a210280c2e080c24842d1302c1c0c08000b902d0700d005501ea05120380140e0296030b5007034000c43f0401c0c01c0c00b90448c1c856601801c006603100e46600d4241d8410100c0c003000940424450700500810313000b21071405021446601d1070301c0b9240b040d00845021a615482000048102e40c80d41c090a9241c8011006640d00715280101c400080368440d440403050606020340d200100c0d40200c280c40d4119010380d9519960b41c0070b0b01d0410780070402c00c200c03000c40d02c041c11280d142c02c1c2740b10200d2200780c4c0c07900b940400c040c6089075120302c1d00780610044880140d00c800b074442100010401045e140e801d00f810415042134200400200307030b0300260403000d40d0994441c20041d070005601805440c0c01c111180b44200c3c80301d0090010881000d60149204100405002c20200e40741d9440d48030095070801d0640da0905106044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 943410323 1250 943409073 943409107
    0x21306081503060a142203050714011a04061706010308091203160501140f0a0e010b03030d090209151e030c100309021503060a3807170f03010608041106 67
    0x2a00580b491000c0000c007013605180e011110942d031602202c6401d4847e81d4103d40da0361180e002221500895501c003100c100c024040d10519400d0020520341541202c01404116141580001008006110000c60f805404104981580d030000001e564071748400004c20080002e010114100384030006e51402c050005010340490507100b14001d20002207010a901540d00040d00d00b000d08030701c200041844d662540d88030101511000c000495140c1c40100002e003542c01510703280e54492740302c070414011031800f882460b51010704407501d040e26402e00408074507007002c06000c01c1443c044001100c2103a680401041ca003d500c011b0810300529808000180a000c2140003280116007842400203040c481c40d0513648500405402c20a0580c540f1300c4041e0313007a00012401c000e50403c601d1706100381220802d50400e40c04110301c0c15075a100c49281056100c2100d200300c1e80001c0080c00880d000c0100f1034100c0c1e044413860b1504129640387c601b0421180c19800e14031540c4028001051482d407060494 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 943411573 1250 943410323 943410341
    0xb09030109050a05030d11030615071103120c0f03030c09190510091d041203020d3b07080a060207050c04150918020a090c050d0c1205010504021306081503060a 70
    0x201400113a10047c1d043c081030109a581d1544502c610031b43c41d0110a061003d461214098124090044808030101c0d08040e007281d00b0240044d400590580c00307080c108140506034654500031460f51815002856040c082c110100344941e0000e07030240341040050180f200030b040018148170381c10017052400f400f102c1c0341384918008d56903101800c589581404c0701071449a60072111501c095075a03010102d000350300a403241c0461640d51052103a441d405070f070f01842c0e001c070004030310001d14400b94098405001e07a04105c0302150f10070303141400884004113040500c030398006000b50316507600340b4280b8105424041c04036040b034980320000d002d03410582180c804641d41004d01308150303100c000000c000340e0b280a001941000b12800100700075013440e84540c42c04000351070010308204600020b201621100030344100041d21004048040c8145445007034010300c0300b1507045152014440341482c421a903441040d0a100860380080c15429494480200904008055951a2800c410003400520601c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 943412823 1250 943411573 943411597
    0x201170c03060f030a02090c03130c03060b01091a0904050c0415021005070e0d11030c060a0306050406050a150809010e0304080f0706030504020a150c020d050a1a010f0b09030109050a0503 82
    0x34000c000070b081c0030680e1034103550058034420248d510000011101c0d03102505000320345001f0444000454405c42150026522030f080101e20313100601c00051549240e80c2054100e40000715a00010f0400f4004495401400340c80124855440780381441c0903004591080140c0c51001500d05540d990200c0c0c124420f1034500b20030040f94443da10100c03039810302c0186864012100105e10702c0030860b40c45080f080144000c0c1287d5240e0014030100b5590303040081040e0110b921407005008614040c0643c03800781000741c8a44464500d028808008801003a20580901c42c0c05000315080000130740050684149080c110303a0b40e6651355001c85c2d13890103400e08100b072a024041000c51418400d0041e54011500200010711036810030407044004480703400a6014010003911000040e110144541090303401203001d84420142820281b10f0036945140c0709011113503170401444140792800150084e0340007210681c0c1c030745d4075500209005207a1040060074a2180202100801000000a1807454011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 943414073 1250 943412823 943412839
    0xc032609010c140406200111040f0e0606090126010f0602300c03131508071821050102030f0601021b0f09190608030a0f110a0b040201170c0306 63
    0x3022a0410311096400400030401c0004114541c425038070303503221008401040f246c0020540b01e0307a08403200d00c0711800d00c00b4404201000710001c0082088c008004092030740b0041d140c8900011410701c15005010706002c00d0401c07042e04080541c10103811480111130340d00444d615045880d610f20b0882c468135005104140d200c2440c00c1c503443d11a607031110201914440e40f0440509041d0640041206548902c800d010507800c0980c0c0e0045500104182c460442d24000072030300050081900400c1c1e0001d2010758204200302d6040d081e0b821089a401140b0b5200310030034010504080480b40501922543c004405d002c400d8010000303403030250074241c00300ca81402c2d00c03000052500e1000c00240b64451081d210003030703060418010071a4003840841459041d030000714407140440d24140c02000e120707840481c9003034030560084a101000e00c07441c1000207540e560f0410f06551040c040c20001d10030010f1002040c03c5900071075a40944001500c041e40e540c1c03030301300b051070b18640003119200d1140c083c2e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 943415323 1250 943414073 943414091
    0x180618070515040308070312020712080112020d020613080609030c1c05070b0a0e01020705012702152511010806011e031512060501170c100c03260901 66
    0x100326400320302c03840c0030414207152468495140c2e58115000540c188100e04480d040c00e8449480184100ea2040303081950080c01c5240007840400140c1224042c4910b5400090140c3d50701e4000c002c0e403c1d030486056643e00d0f101140d01c40900900d91204805100e188240130100ca030200150203480b042d00c081700c41240400701021032a0707580316005004a003082160f000815591080c071580301030301c001c02040750800003514608a91048100b500c4995507040c1004d1004201c0c07500f10041300e440240ca41c4065901e030000fa000c041a440c000c0c4041c6c0300018900009101103c01c0c004410b048103045004d43c0090800041201040303000c40d0000d118000022903660081c00c0d44020340c2c0c0c80c110354442c12442d01c04c0540c001c1805600400103000c0c44880040e09004039041e103071209214490104d40d80d4506002d400741008858001815500b041d0131040e0f02e5110054528400b905510307049d030301070b442c03402c0c1515601c21801c0d9201c8100d80040016035400300090003a40a0340e9408002c210081d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 943416573 1250 943415323 943415329
    0x10b0d0602190903021807020c150a02070503070b0a0507051006080304030b07020a03171e190f020a05250803070c020f0a291306020706170402030a0204051806180705 73
    0x140318000294006c05d005845804000e0034020a1f600145038011180c1440c4004009105982d4212401036201030000b14041c0d030a50510041c40108400e900900b815810304840d0b445c1c1d03015a860103003c1200100b109802d116041098004504c5108402c00c0207644910075603489034094007043d1080200c0d200416141440014080421901070780c3e03150100001c441d86101e1030340d001e00072152281e0b20041c031071606900780312468090040000031070220700d40d00d010a020b80d060004c01c200307001d10602494122036049400c54101180c5107090022144d903030003000c600b108803614040e0087c5008002c00c25a01d4001081c2d60925002321040280e030b520319000c200401d1103900036020002c040041140c0f448941940901c400071101d1380d00344c280340342d00004000b04c010036842a001030380300c00020010590084561f86881104070403501c003925140d00801d1740da0035407507402030003103644400041c0c40308103460f4014410640d003400e6940034208898151005011111001a10700079900d00107030510b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 943417823 1250 943416573 943416587
    0x61e080309010e0f0303070516080c3304031205134401090f12171b04030f1b09021201121a01030b010e01090e030d0e010b0d060219 58
    0xd10160f50b01c0d02c40012a2003441240c000088515803d8032003070140b00f0005509200041004004071602c1120610380710440e4541184011090302a00040e08142c00c0710803080d00801e14031108014204120101c0d107102e9003140b14551000d407441e40201e907890042c6074400010101c29a00b94035100000d901c5036072800d000030000c03503604490400c640100786a02d000e032081496580111390341c001ca42e40c60045080c01e54113564802c458942105000c0410070007040016444400c81c0e14001a2080c00c00d0320402c0600009051100130b220410380550804540c082150099544100304418a004516101c403440f20b40c240000b9646007040808600c0c00500d20a0f180e001c0e483c10911421a460254201e20381c00e100d150545c0c4c034903440741c0b20b128140504821b040c000e510840c2401385547c54003a5404c69400c2c1a0400d404042c2050103500001c1400415187d1406000500055551210060500400554500c00c0c0c0000d03034400c00c0e90030300a00b079014200c1005c004100051140310714008607400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 943419073 1250 943417823 943417837
    0x80f090307030e0a0b0f030f0c07030c0605040c03120203090901081c0e04090609081c020a090b0a11010606050405030106090e0706120209030102070807030e01030504080d150504061e0803 82
    0x16520038414007021030700c075542007001d050020744034000050300c030700905809038450718503030400a00c00028001144241c064041e400246882c007036007403941c182c0d00140704405818003e070515407038002240070300c6507443c4424010340c0c1c40000042c5c400201c1d1360103516500300000243c8118548400001c14100109814101030310100052900030300461098500454003035416030003d942e41e01780c6c1e0020701d0398442c0440c200d000d6812991a09850102c8040e00b0080f80710400c0350a0040c8032640f00603400014040039a680307500ca0715103c4100c5ca004680390945a51840700643c24420b000500031b8200c4000d0040ea001a40240651515450301409441c89d005080c1d1499103d48004c1201d18454002441c10000d410b001501e00482500040e099030864042661140c00c0040c0100030542c008408034040036003800c081c49203150585911000b0702442041d8114291122401c0404540049801001c1d0200400400983e03071603489060a0442c1c070100c58022030300b5803d010bc1d90386c074000262442 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 943420323 1250 943419073 943419091
    0x30f01081c0f050a020102090a060e0a21120201020c010501060305060a1e051c0f0b180609061609031a0109050f011a0906070812040219081c09081507080f 68
    0x2c541c041050403143c42e403050340c05004555090007503440945d9107600820003000e107681c948030498110001c0044a65241d44580c5540107022402011405031081e658001070700000c26103c0b11001800c1030f03002e0f106040c4044500d5180c0303000841c0403601a401130b8001e11042e12141929921010762102d0080340040081000c0e0001008020a2900280c0c0b144803c540902c0403614240d507a45104e08100d41c914100d401c801c1c00c404101225070300341c003207060b0120f00c0c000030240ea04015420685480f405021042c01c180328003081c00541d4045c0150074002c5507c02400c41120712040c203220040a028052000014144404141210a4042c6450607500781031040c07541c840d01360405d507070079031f010a004039000742c3e0600003000407c0c80440604651464009100704500d480d00c104550441d041d4085880c2110031328051090550000351801c6a20085101010400c00d030041551100380702d0740451014807a51a440040c44000e40000c1e0103060704c0d07220301406448581c0d682c8001c2c43c0c1143c8480d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 943421573 1250 943420323 943420337
    0x504050a05010b1e040c05130326040e150a1a1206011119052d01060503030c0a0b1f241407080a170901140903091507060b030102030f01081c 62
    0x2c003403405e42d10054550030142441c500d081c44014100e800496150300964040744100c03c40b000c003824400410900e06090b440c401d14080c1000c3c3c0300c4c003078844050403042900d415185402420b032274000814000d4203c40404108080d01402828059405245103c2d80c3c8058903010851950080414020081e4480c0107001c8540a400c09000c020f00100b00503591032092450f10960103900d00c16480008081c0c1010842c001d003076001c503500f562095400240250b008200000c40b20f0000b04920010b590f01c5650442591115104446140f1025880380803050307010000003805c0d41c144900241420919600007881800d590701554098410302c21010814420040c3d0400504500010a075241c11130611a1080c00702c03500042c0c10000460708420240c0d035036214801c1c0d141c40e0141c26a403010350718004626040c1c0d21800702d1121000041d401280e00404207180040024503000071405003805002191a8900703c0c820340070610081c45002000c0c0100080c811484d207000d000500d4008068840c80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 943422823 1250 943421573 943421629
    0x703050c1e09040f1e0612020f10050706021b0607020f0c04180803102102010203070b0402030a050a0b010801060801020309190212061f0602030a0e1309080409020c0d1e1409040504050a05010b 84
    0x200840700ac004c1441c04118040002d0400030f081e51002d03108440808140a18030120401030b03d03c2e041000e8104010b540c05a11008809880080d807007185000039600418084e105003a4481a2030450710001e169450200400442c42e40204451040f6511142c1d40b0403a0300c9468401201c2500081019005800800034800420503484805400c244054100d45060059864103410084206403c4a01001d40001007042c55401d00401c40640759440c021491b5040c01c0742c01340e58610700c0060b0000c41200c0b2403001030640d6140388900000314080b030141e80d001d1502e80c00110b078109808109030014022074070b01240c130903c0007003610b500080584410440440d0746040100056078980d904003899111907040e03001940b8007011301300801c040301d00982c48010511000303040950300c400f00020040454211001040c0318040031503954620309202e208144180c0d0141007038850b48503100d40150408042c001040400101d0004450007400200494100041000804540c1c01c5414851400d40d048031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 943424073 1250 943422823 943422829
    0x406050a050706090c1703040609030b0615030f010503010c0809190501230a06120c0312031b1d010306180b0307030b0c030703050c1e09040f1e0612020f 67
    0x208030a11a07401d00c1414038071143d469205840248504440c4074001107002c108103c00e00f1802018004001c1c0554245424010b000b468241c19100145c0044110310126241d42c944052050400c40c0f00e02a4680d40c0c94401400c11000f9400c0c41018040c0d0710f083c07000c1c404503210348071483c01040c00c41e0113420b000c109100d41c0040c044410005990555840b0340d6102221905141000c0c880d030b0080c0c16a50038948006c0500469001d40c3c003180d0b0140e01c00300c0f2030780001c40500c101800e0381e5100c4d0980810326807444048004026124880e00fa42c1101c018150704550040120001c42c000d5480c101801d500c80001101034517111b100f408a41542c150408a0541240d04001e9054201408850415541c2e0700e52400004041d110341c000c0402c00000c1c08001036050044603800b40e106070f00240b414100c24000001c10f0100003d80050b1940411811602e9881d90807840102044110600034404c0c01040d070044070030789000b503100c1949046e000243c008109540b020555800030b2008900b080c0700014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 943425323 1250 943424073 943424077
    0x408040b07060e030307020c180402090f04050f0a0c0302040c030605061605030c01050f010e10030515040f020d0303020d181203020a091802070c05040b0306043f090b070305040605 79
    0x10440760760343c0b030360480710000400300081d500c01e80f42c0d0b900138078502c46082c0501181c01c0d892421120100712110812001d6140d0850058120030005400e408030ba80d681040c608001448144090500821045034288407075940481c080e01d000f1141040038403d010001d4044810728070075036402030700600820034001500600d0344032190050b001d41b0f00d4581d100c007981d421924203e450010300711342d400050114000c08101c4543c400803103400440c90301e0442d01c2e0590f40da44511000d0300001c501c40002001c01c200b0b003074208403441c0d0107406102126400d16006d40a5042500e0111400b4030300200110f030404004a4921020340007074401c0b882c11100740e0120080e500085a20040c450400c500052001c404a104503591007100401605e480c02c5203401807005100e640070303d00c15800c01c00300903240d40d4049621070704a40d2040f14001240e114001413080a400b500e00c40a010100c4c101110103007048010912510207107543c0c0c002e0380d40c2c588901c11443d000c0c0071400790006000340700c1402a2401840 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 943426573 1250 943425323 943425337
    0x3903030809010f110c0c0a0b03010306051015020615040c05030604020a03060f0f0f12020612040c090911030601060207061d0418050f060601051c0513020406080d1202030408040b 78
    0x100102c0d058042110f940c00352012124a0301c0096030000c1c0607181c0240a000a002c4113070200c81d90b07000caa2a1070009040d500041c04060000e40d5a10041200030b03141d15480da000340010078201010441115019444242c101c40c24082c54040b9a0622a1031600b84603031021035000340c444d00d045846030f1040c4002034200344803960606a07128808035800381c00c042c1c2000141a2405140006400c011040d11306510950003111000c0c0c2d54040240103903076004c03d0362951024141c40080c076680e80c4c100540c441415601c500409442c0c000c1182c2448503900d801300d120602501269016641d40c44d080341e644905101c0c00000071055105d108205081d4041e01030f0394031000b40041549a0003c0c0701d0500400700c068115603c2c0c5c03004507035501c04841403021320350101090074034030308200018107085c2c0311640102044444c0d90742c5400040f10700a100e086201c03265005001040003c0e1234500382562420504080070100300342003002e019402c100d00071203104a1307006131518145803401441ea5115040302d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 943427823 1250 943426573 943426591
    0xb070509131e0b03030408062a03060109050d020a0e0a06080f07050319060b060a030515030c0a060c0510021b100c0c030c141c0f05040e010e2239030308 67
    0x12001802e0b600408c100e5002d52503045e0200c04480e41680c558058120b0300c8003400c0c0918090040060685c1c01c0f06410040b41c2050320070760007c10281c0700051f10880f40d03401a4250300126014000c0d04030035039100b442501c2c6100c080702d040c803080000320366a45202d0310400e681588508a68541b64410205000b01da600c14080410344102e21000601c440d00200703c0e0400080d950720400862020501010803501000e40c05407a10b040c040001c01c0c1900414091082800b14600f41d100c20850100304071200d41442c0842151560070541c000210107582e031a42c207805100300a148890301c8614480e0380100303103181c1c48600c0b10140560341900c1101140030184c3c1c0c035042c450211004400280940812110400c110998015260001811200c940202401005000c2c4403d20488641e408118103503498890402240da079074441210a00e0100360001a488a411820004214a40d078884460b4600ba84090b0714241d09050890b100c2c80000c1240712840c049041c0400219000d2200e49801c00304035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 943429073 1250 943427823 943427827
    0xa020d03020c21040e01151209032f01090f0b1b161a0f0103020103150e04170408030d06090c1407150f230109060803030f130b070509131e0b0303 64
    0x80d5005c2000301c413099100e040200d0381c4a440840c000d07804981d100050b040504200140581a200101000c08039012400c00070018004090600145001201e04011580c0203001c80740d81da241c02e03003000d98119021203000d1006c034003207212401040342220246d0604550344e81013851044001d03800d401c20300400c3c0c03101c1c4140c0c1c0014604035100440035210300201115011554550701c001402c0b900c00703e009181d20540050148000b50902c00101d41147c0c101e202c180400c0c41c920b103516414031940d40210340c00d120000d080000f44600750048401c55030f0781c4404224000d8012000d035900300d0707003002820710104208004130001e10050900b030b03640717001101c00040314440c0e014281c04a075045c0d00381c0190fa4041c08415100088440d850074058084c445003485554a80002503a5a00000e01b41340b400c0640302002412100c160f104040b216900000c1488290500c0c0380c000c1c05070390140303d0280c000c4843c0d02d105611014280100301540d00c0e880e42d11403001c10244806d800406c06403518550501003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 943430323 1250 943429073 943429079
    0x114041b15051e0301080a030c0c17060709050d0c09200f070b0123011d030102041805130201020601060e0103020903060705190c0f030804060f0e01020a020d03020c2104 74
    0x8240c88052001c1d41c1600d40d2076507000c040016a0303809249400c404600402000140142580482c0d01914990f0505201420058a203030085070545c0316045560f030510303030041011210030001040b80c0a0111912628030403a1510148a2102c0010038003504440072807408000e11480d580c00481d00c0f003021047d840c0d900180800b0040c0303d5004c042c0e1046031803404500c4000f8405440a8907006000f20503102c071103c41d542c1080401800113030500c84c1800701508403107269008080c050070500c403004000315604c0744c49a880c0d11180c0001128500d4440c80c010014080080024182d01032a4051700144100c1c0c0ca01075086a17694866140d550401d9000d12482d600354408100030f074003820807512590b444030200c3d40040e400ca102407491408000c02c00100c980494020a104160359030145800f81240d9242e08129014151000564016a10307200b8501415441907024080b5000c0075402d036448003840d03260440a81c0103c0004035156080001011010b507560003010079040b00c0401800d040c980d17 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 943431573 1250 943430323 943430339
    0x90b34110a03020304060201151a0a0207150206160806090f0a200304060c0c0f1104233709020f031f0f0203070e0f03160b0909090114041b 61
    0x10700c03050860150340b000c01c0c1802613540a00a00c0204001c0303021141285281180c081c00c039910301c82c1000b881200001d2199080e0740b0a10444014203410021107100d00c1c51848002d40d628012141040003401e12282c00d80458803e03207515000340401402c44042d03413242c2d259160408030151043d102d5030780d00e00b040c0601d1440703040c80b182c0204085004d21303168030b064104a4151061405000c040041c241e5000c400201d500442583d61904085003d4001403100c7c0428020a140f211040901c80d25000310026200c0c036800c6544a100e948040480d20110318030254480c1440b2031021100c840a04440c1190706d070142c1c0680100c0f40010001c0d130105040c017011a080902c40002004803c0d03a000030b52201c0b1003a805848444a49100c0031032039031519600040c00c550104d10030301e1041c102c035004010150f40402c90b8903145581000b1030020540d40e01c00f5500d1661040400301c1c091107041001a004800611800d9a46403044481801603511035444501405051045000000d08006c01050101d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 943432823 1250 943431573 943431583
    0x80708091c18050d02220902090109090309140a09180204050f100f030b1f0918060e0601030302071203090807090203041109101403010207060e01090b3411 68
    0x5660344031401031111202c4489004038160f0070440c0100809684c850068444444900750401c13407042586480b145510440040d00d4102d07070207540099090000b0408941a50103282c10313603c20746075212956503078404064680c01a000e8035034402107111080000c50140e81000e410303076404000c22403010010780d00103012540c0903212448901c44da002041751100c800c0c08030b8409003034101d8205084503d15501d1910307098004056060310301809010031480500ca0901001800308400e00b40084040310112600d401803c0790250b40741070904810040e42000443d446040e40d41540c0903010090408822840b03104003c1c80031400c0108640c0c00180000d41400283e01626807514056620f00b0203061454042c83d10170802c0c0d21a41401082c010a01c4003c249a02107608481c0c02014900518001a009005412001d046181031140c0c140b00000306620071042284203503183c4070103441c0c00c10000320240309250707004444044020035042507027030307607009100b107241518107d0340120030000c15500304 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 943434073 1250 943432823 943432873
    0x30309040e0a0521071101051e0c012414060d050a060e06031c0810080114071106011a0d1d0601031709030a2006070c0f0f0608070809 59
    0x140c00c8040d075042002411302c11044184050002ca01c20245020385907502c611520400500c0079101c503662900c1a40920300342c9568003a00141c05036030020580300000c0a80c0301d40c0c881e8110754642081284603040020000c10400902c9015010035030515118501280e8040b12481e400242486008903290050064a1080384103080214403249403680741d21118a014100078400d810a181141845064028031300140d000340c0b42c6909030351074a01c5551101a00354102b00740650070310031000c90244103082c8190040e0460b549254034807410508a5480300e60a008bc040420346401c0149600e503001005084c5010210b1320005400c0007810640d103110790188902d022540240c001001840002d0080c0d00540e5034074011030746003050020000e47c5816142000034007495035054160b00400e40c490103107004080c090b003c9075482445003003242c0456110702c542180c8113105080401c9104040e40c00c603044410b02c1c3c41d03081d60754640e0030f020b50b24a1402400d00e1018801e003d41a00d2503800790b1410800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 943435323 1250 943434073 943434101
    0x140d0207170306060304030e0f0301020c0705090a02090105180427060b0105031003080309010f0617070501020a0f02130f11090934021606050a1107051e03030904 71
    0x980c1946182004a1024185034815140824000c101503516181d04507503020f54146442c551403181d60002400906040842740d4042d80301149914804000042c007500707940742150b601130b607661072203190030a902c500c0c09031600044042c080c10416054031034003018180c00041000c50481410480e603852200c041d1201c0039040318001d50041404014810a11500007e180c682e20390320b027290099502c03881c01c0c84018031a143c0040021510902903001c220103108840052050310303aa1620000c0e07031151541114224014030200103000d40c00001c03100801544101440d00c0311205400700b2100e84858003080352450346500c1d1a40102c3c00510a04243d102100030f100d4903101d4000a000d405c03900102441222080001d144445514174600101c07000b4401e40c1c15025480c071414200d0038005403030041c15410400d48401320b2120b40110240c000b09201c1d5658007030007005007403070325601c002c10720445400020781000c00d03800182d2107000040c1c4402c080d0032a07281c00088004507040301c0307100451880c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 943436573 1250 943435323 943435327
    0x60c1213030f060c0f09050a0501050c0c031e0618190f0b07120f1109091909301409010c0b040609141b041a27010605250201140d02 58
    0x201141e00040000492170b06454208401400c1c9404100c05030818002c82e0b043c0803000c645420000410021000e12039000760994102c1040380080c0d43c016420700142c0700840c0614400034030000e541030b15007003081240030010540000d9400810707200d40c51014080d1490281c44961001003400340e10124041d00903035681c01f847d19403c42c0350001300c500300c100411269041088a900e51424942610302c00340084603040015250300c80d1035035440c003181c00020880307420b00c071041040c0b26401c64220000000c0d02c401c01e40c21440f00007002c038040d440b800550f010498080d41d5110840d440409820143c0c010b04141c034801c9125111010340c420101c9003102d240c0d4840d002002082903042503131141074000d4000308a11602071540003686500040c0003805941c0c1c4203194251f0121701e0b2841d02204e2005050b09880d101c100b080004084884011100c562a645000150042c800c01c125541451900d58070407408542c1c00c4149190b6499041c240d0402c061020b0040c0318519420080440c0c20614100503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 943437823 1250 943436573 943436591
    0x10c0b09060a06080d08010515130b071b1511031c02091206060d06020306060f04030305072006090105030903040f06090e0a09020109090903110316060605060c1213030f06 75
    0x1400fa12103541210045070880c038074026000340c0008059040d66022108000991000507030b41070b250140180400c07040030f100c0000170318000e14000038205d082c024190002024611132080c0c1081e802e6116415907005408003035290075204a030303107000190f90300042e81d24007a03820807502400180701310703908101c940c0000c2e6150180b500c03894000507901c184000d85410301d0410000380382c160200c0030290200340c000001904959802c4200c0700785888071400152a0b68580c2001042034011076812620004500c141852492100e410700250340340040c140d910380203d00b001102c80b80c1001d0503a445900c02440041074034801000e005000c1c02d416920540c42d80d15000c03440040101c0903008450303803440c208542000d41d0707014499a00b40c6174410004900c680d0710740703411909030100e002d02c201c1c1381c080030807092001002820703020565400341e00244012502d6508100041c800d05000390041d5000803c00700524403d103018140611a0101151585c0c1e6207446a044400030703180101c8086039a041c0700 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 943439073 1250 943437823 943437841
    0x30a02040c030e0c090903090108040c1d041406010b031303030b030a050d02060a0c0c060902010c051510093e0310030605180d03021e0d09020406120b0103060b010c0b0906 75
    0xa50784d80508071180c0c00e40e810b0040b406901ca200d1810014104000c0a0004007842a0501408000c0400b910b04060700000e1301804030b00d000c5d0643c0e0444010029185ca0380d8400d5001410f18165421071510501d961560320b003910031101d203032408074241600c50410040b10b60f42406808151406280602349081c543c0c10b009080810041c10b400d6000c0ca0034070078000455100c200000740c158440c0c40043d50614500050b550b0001200008140340f04400032454102c0f0940701c0c00d03000b8041038101d40f200f00e03114a41403040d2040001200c6100407503020300c14115000d0400010a482c07066880d04440071234140c100c1495004640325050910030303240400401c40c0714407410f54004089038880c15141c136440065500ca04009859030101078000c542e0b07801d2030752136859240306d20140d00d8403982d6410401e200d1034058801c41800303a1090749000070000b45504003080080f0216802048900b440c0c0c250b030394010090000c0c1d88441e04100c5040300a600090750716140318000d1010074000c05561401a0b41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 943440323 1250 943439073 943439083
    0x8030c011407020d0c0609080318160303021f0b0d140c010801082a06070302070302040e010c1709031e12101a03180a0807030e0609060a0e030a02040c030e 68
    0x1090807064444420840001d9000c1000d051200b0b4900e041441c1d0107140c03c0c65009001d00d00390240c4011000020300a115940124000516105c0010365407080701030304401120340320754400900580c01c02c50182c0b03035440800003448162086014001141d020070b0010490040d420a0100ea001c851403a01c004172640802800381284402d181140d01581060905619818214090100d0f104051205615400c1000c10340d58422009010661108100c3c140296034400d17510090740202c1c6440070340c0400c0d0406001c0c0040000c100d0325440d61420400d800210440401011386540b03000074000850100d640c130795a1040c1d41c21b00d404080d111100c291b590360a144029010b40000c48094a080201c01151000201110b280e040310399140c0d545c2c005404650702c6075030140c0045000381e141d1441040150400340c039800d4003981c1d5142002042c04148456481122280350b0301c41814840d00400c0c911581c0031010b13183c406000c0d240c1d52401a404241a0b072002440d5001080d01e03008030080c4e11108001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 943441573 1250 943440323 943440341
    0xc030308090a02310e0a06050a020301060903030f0e311e0b0a0302030d030e0f03070503180d0c0b0307030c170621030a08011403011406090a06050a08030c01 69
    0xb5212840b026400076003944003035100c40c0c2125008028181001000c032903810441007124100748901107011070040c0e150030070b031641181c41525000102d500c2d140e4174401d0b64140c03034290722080441400d64038252000b040d41500c0340200321500b1041081078940d140ca41620080a8050071150032529020301c0c042c55500c0d50341000c4d6440e20b40045810701c4002c035103991140d04480002840c041001c0450802c1030340d034101030340500c22107003d280703e254590f2041425294510035101000f0391203401c241c81e807040b0300c009407041c0d00074030441408505500c070b00c503050a4001e00e0100f100f02207a50b500c02103c56640214210b04001c020410301e56010300030005441d00c41e1402c50782e1040306a410b0a04040d001e458240124443c0201c0e5000c0705907178000720304044081d407c99480d03800b146001040e0f40c0782401b0710544000320014171041d500301401032402c20340c00c605080c485a0b41d4a410701c240010001d1410b001551034010020720340d2a0710b070705180a801c0b0303440074517030741c80c6040681402d56915407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 943442823 1250 943441573 943441591
    0x60305040507050616080c060a050105181f091d0c1504090e0a02030f032805030403180f0602010603050601060e15070602070b0a05062409190807030c030308 69
    0x204000038101159400540d40102c1d40304d51181490a10f00c441081906001041800001001c481001c1e00107070300b6100b00d2036800c05100603030325681406880303a10400440b42441e1801c1c0841d0000307003001c0c2c903074036104a425602c80c2100e0f03a03000d0a030103548051460641401c1c4041150081445c18070414000e50400d4421014071070441721000304910403440350110b003940d115503102800030b0600c4000c0700c0b00d40080031590300c080311424403a100d511020446030031140620065144040781c00c2c1350045c140b8030ba240d02c2d056688540303043d220f01c00165810b4210400c00301000c41d1f00501c610840c2c0140004c0c2d0700001d8418218503003d85065010b0700000148120003484040c0c1d5a501c48810011500000e500307503da061500d04140640184074005152114030000c11910070b00e560300807845600211603d40c8001e14482103c14442100d44840e07103040010800c144a03801c10072100d00641c40846c80c24072055555104d1203041c604c0c19002201c0e4044482010424503910178860b980140c014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 943444073 1250 943442823 943442831
    0x130201181406090411031f05010306050f040e0a14070602012a110c040501031406150a0504200d1506020d020c13090f05251d0c040b220603 61
    0x840d0004000e01c0000364400c0000050721a030580381c5411441429800c2c204003600da003010709041d02041086418a2420707145002e0000b00d56220307000c0c3e1001c403140a08610b144c9102c400c140320103882d414003400f407d0b1280844030000148a8801c06812081c50006420764509182000742500c90000e02e1003001c0d0f00a070114441c20240010321040d0f0748240c1002188140c901e9942c1e402d000c2d410002a520a01e44070000092040189040300c1481441d0103443ca6507994410a0001407021046181c200d200c8030814080790810b0340c07048485c0103074412200201c40c8250703d104069071182c480c09a00a41781d400c16201d06006400f170350050480d0f4000303440b5407200440002e540e87c0320880c00d20b200e070f0302c0303100600c00000580d03100d081e9082d0401860f194594150074200d91b5204041105181030f0b00b5054050009421303003042e103042da0b08240380483c150480c002c4448856201804a010b4908200000120003015000803d0303000302e030b125480c49441040e003840200038510381c0078405241c18 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 943445323 1250 943444073 943444079
    0xb0315150a031101050703111c091e18140405010b04060e1e0c0f13060e0a0810021b060f07021218090c2502120f0d0f1713020118 57
    0x2d40829603c004028a02907407510300500341103403400c01c09803040c540341c002d064090740e04080b01c3c503020600b108141c9500100c00d40c1c0f04150120404c4144458140242c2c5050610001e041c60040345d00314002032a020480c010120b12400750500c05940480d8160b558486440c07050900c6d004000c010134102e00d0803461031a003e01c03035014003d01040e010282606c100d00003029500f0a4081d9080704081003c03c40c0c07106000415108014401c1c000d0b1008104400c0741d8041c10f140420344503082e11149405442c02141c0c1d885241c02a42000300c1c031003459070b808030b031750b081c1200704211591003100b00748520703c9241410f80010342889240112014540c000f003201640c0f0349040e403d4080e4242c802e8580035100d40c1c0360079500545018140322003041320715004003210480064400083d6160007210103603d580c800101c0241d48900d503420b141c5560b0040705444040b0342c00b80c0411042c800c0c05043c02112068440041c894404c02103d1781240c45440411210955038004000b40980c406201c88044482c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 943446573 1250 943445323 943445333
    0x50307090216140a1a040308010504020a2309150a09122a0503061905132414010f0e090609060c0a02150a050106110a0b01060809010b0315150a03 64
    0x18003400f007402250f010014084200403031130384150801c02410481803a14028410321805441c15000280610004540b5107000d1007115119001d50303c03041f4010125014440d0007030181d0031507500081c0c0034810f1a155440c0c09559060316180c5d500300e5a0b540100f5a4003a20040c0325412088010000e5680040000e02000341c4036154409690704070b01d90403950411150000c0a40c0015070180030b490148136050107546004142c0c0d5074284018403150791030003070700d19000001c5140070b00040446030815150007003d0b800111a891107c40101c1c0b480440720401c0b2540800fa80309030344103901c4100400040440c0010380f40c00c6241540a0001c070b040070111503994081c0a403c1d003604010000b48114010700801c00d4940c041065901c50701c942c5030058000b401010b0902ca10400b04000060005141c0b40100c0c00c02e1200380d01207034440c81d507400d1880841d82042c004080300030359980c0b24500212903504004d281d1010701c20343c1416426182070740c1940c560f86020030310076004802803642440095 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 943447823 1250 943446573 943446607
    0x1512060b070c051f210f0903021b0108040b040318031b0f06050315060f3c03090304231c060b0f01120207020120030301060f1419020304050402040e010503070902 71
    0x10307003180540c04220b141101d51170f0043c82c8200144104130324215032042010b4001c10400081c21100400ba03482c6983c910040d1480d0b2411a00240716580d840001000240030b007040300d2407003180001c41d1850079282e81e41c000c895019040301c0c94032461114020018074001d407904001409a41ca0024150305002d12002452440c032410742e8030074403020804a00380301403402900c40c00c041c010425400140548520100c4101c01da0401084500804030f003052422600c0440c0c0c019940d040045203050301c0d2000780c04c3c00e61141000b0f002c00380a445020710a41c0d4442e020f503114007000f04080410b601040c41e05c102124240464103010b00c10b0140d005c0b0060780c00c0200d050740d421120741c000d6030340c01c118401244c441409850228080400781c81c09000100008081c50503550941c8658501c61088007007550b0711030046440120024080100c0080c09520b040c1440c180007046c012281007944910005d010390b000303904840000e07980c160040116190805c9400010107031034038110700e05080800000c07149 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 943449073 1250 943447823 943447847
    0x80c010e0321091e040b0906010f0e2101150602210d0905161805040222090602040603020d0b0a03051510051c030f091512060b070c051f 60
    0xd44642c1c61644442c5801200c4070382c03000405100101940524665003440d42c044a1030040e841d05001d00a541803910241d4050702d016111040382003001c903000c40d00d01520f40e444035040205050448480d50741d0141003984031070303c01e00110b080595064008200030341ca6020a00311b5000c40c1004400e18a100c0e000144200c410f05803e80e1000c2890b4090040c0c035042c54000c000f4820b280000c50f990090030120000d0310241310407030990040c1014818103a031010381b0081d40c0103030a00728a030442e03101151081007044015a000c2800801e41d1244800c0340c10030b52024001c40e4001400021510340c52182d844945402c40300612003030704640304c0c1561150940c0c124100821418086403501c2071545160f070041c10003d06a90346002a121241c40e03480c0100c404502141c0322912500546010b42c6101c03060300d410401c5031840e003802001c11170714440001e80307044003590740302800305030320411740e0040c0100c6009807020445145040e041c03051400c00348003400d5181003c1400302c405564026400030306 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 943450323 1250 943449073 943449103
    0x15100906140a0c020a0b090312070b151801030c05270606090d0b0907170a02130f0221040b09070f05011d3102040b030c03040609050610080c010e03 65
    0x45441c10b00094886504141c3c000c3d40c0844403400000700c0b14501001009168010340580740070030084500d421060003801401454413550304005440525540d24807241004000c04030740c82c010050f0303030344084000207070000d4410a607072a50920440c00c0c28a41c68218003820003c80c1c0305c070a64420f00d4209004050030480c8030301d80008054041c0d65403605143d40c05030300401030001504080c40344956610b4076200d00c51000c50904500b1040b000040340c05040140c000c0d0046420400f01c83d513810007010a040003545c003075401c0c0301c0c000d5900c00419121100352001c518141442c18203090110759850000c01051256010b10f1040c024950100c0301c0000312003081c24034403044103060300606464210190b000382c118902c0c60f00091222080310428414142c000102c00800d00c2c96a50501a071199004608944d007003080400c0d035568140005580c400e005000014070444565242800c0045c06e642e0b000105074424070a01c0310720300600280c125650242480c1500304d0640700845d07145d40d0305200e8550 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 943451573 1250 943450323 943450327
    0xb180c0111060f040807080a0305270303070315150c0213060f0e062202181c0b130506010312020f07030b040f0312020a051c0209010c08160206031510090614 69
    0xc200805801550f00c06c65012420036140c8d094400000e004110494200b40707503100100719850100012065040301c250329001842c6186c4c0d03461015000b60110f078410552450b01448002074034000070150303004030340c40c55444c084591014010070010f07500000d90740080500c1d0040401008007411010012034500110020a40d503d140000e241c803c0d16403980c000800000b03003158241c1c1216802020170401c050342003001003001406100c1c1c9580f144420650220040350040b000c1501c07641a00d0380103d66410500c3d40307090a585d501c0c180542030780100e51050910b0fa8400d4015014030011901d1940701008080355465916600c00564000d0400740011041840200c01d00d403007011180f5400300440419556400e40080041c40c0364011611001141c192000c5039001d4152402200c2e0084e505a544500304203258803040c0c9594072034480e04003400010620000143c58450165100b06c0005480a5002c60700c1c5080c000d000142c40c0d090020000405000e014094101c4849420000d41d40d944907 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 943452823 1250 943451573 943451581
    0xb04290a0c051203040f14010504240b0612040c080f0c212d071a090303070b0103060906050a05240a0506040f03110d1a0c070b180c0111060f 62
    0x10342040710380f68005007000c10010800041c4141d600c0390f60700c40342c800c4140e10030500c04c04591600b00c41040c2d84c01410102c903030050180a0000303d000b1824018680c0380000c01c0e441b83e600040440d84a00258103241c0346200401003407203094007c0e40018818500980403900080440e039480300c2012269500c24400e060019921a50086812410a0102c011074014501000620a042e0028895049801c0d82601226611140400d400c402c0700c00000041c601d070124a607035480c842d001003100c1034051005000c200045680340d52064000d40c000d0380005021010f505040307003540c00081c55480c29a080405020040e011400744034100080d0b56000014101e078000044c0c0d0b01c0525034001d5602ca240031402161480c2407070048012a881664045228546403042c001e1001040d9400b074001c42184101c91140800c0d250410b501c040a03081081c90110503660308150190103888050100f920300c0c061b007904043c01c20104401280c2400c100e007030300c42d8168044d039850800030204800640084041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 943454073 1250 943452823 943452833
    0xd08091003060815190c09050d06090b0705070c06090506070201030f02041d0604061406040611010f0e010e0f0c0a03020409050c0312210105090103061d070b04290a0c 73
    0x41005030140768140d82c51001580015514050241c403a01711036031300190941c42000e514411240424080c0e120546828540b000b04071500b80000001ea03442510f07007114800080303802c17030954410b1101d82c60301904c078449414203440f598020b4010809001550005010660312001603844103035092902003001d0300c015035028042c1c041c0380c0c400e5a14846008100b103128041c00116440303080c00303840070000c40d503440001b82600a1381300c11158008400300b200380305240c82030010b081c00600c0c8030008994081c12100341001c5a144000c0c0011a940d40c404490580f8424441005a81c01c400020010115a0700001d0f811622900c4000c3c861655001803408000c0f0901c5441c030440c1004068410500c04682c8588899102048034030131507a00e00264041d595407401128166040644804c0d5103030b080d65198001010308000e03c020132800f1500384c1078400c00402a0901800f4046a5580c6076494190184058625060f504021146900c0003c0401038901d050f1a4107070881d2910685c204414145 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 943455323 1250 943454073 943454081
    0x8070818070e0702010b01030b09060109050603132003010f0b01090902130e010b0304020307060206010e0c07020409141f0204080a02040c050f040b040e0702010527160806060a050d08091003 83
    0x590841c2c600080001080c0c040d0302c40280301e0800c0c7c9043c820001d4590401c4400032003107803880d0200b04030000074801400d00002440c0d00c48122204c4001018403130f19444401d020740d000c09400070455040000c410308082c0100c4412101e410400c0c404602a8800640810720b5030040005190340490b0007003200c100814204001c0204014900306940c41c0c5040c01c400390705c12503081e4000c2c0308104001660520000d2554101d072000d440c112200c0d1905030803000c3c103500c0403900740d13401512940000007040c9103000f082c0303c1000c880c0040c1038861440c2000380c5048404043c1c0c000052060000b0001d140e404120000c1e01d542c12607002518200b104001d0719580241c82d00410392180214010411061040090043d81d41f5054421010742c0da0200403820b841088078540441c3c03404070140703501240f0810902c950705ca951004c2d1884989014500c0113980c03203075802407041d07030312200502042d42030000d031090217444113445c00b8100f43e02c81d4a502e0b5652040500725401141248000042c26100f688 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 943456573 1250 943455323 943455329
    0x501080903040308040f0807060801210f05030d05060907020d12110f07060b150f19020708011103041209030512030a020d020415030506041803110f030c0d09060807081807 75
    0x100c1399283d60311500b00c041d20281c140505111841144c4001c1030803802404418101c0341425900c0c840b00343d0740340c440b26403c130480c00c007112684014400c001c0011014005000b02c00100040041e90b031034000200040301802070551801c0d5088403003503000c03442c1e0000e0200c400c50820030000c66401d407450780a40c007a1094040c191003030300c1d010a0010800000360041482d42c80100c6000c14004045400103040d807003010301e14091420104004040c11a450300040082a140c0c0140c0d184290342b041203a0954031260301d2001940000010041001000a125003450049113482d4103200d0460703036107a642d050204141040c010000c0009040d120a5404a07910712852190954540d542e5411340800b200b008051f45011038107241c001045410107100c3c1c6050846540c082e1559514540c03402c0e5156000107a0310845401110b0112049250410040c40744040d02c8006115400c0e4280b8010040c500c2e64100f007080040510502198551003101d142d0082d4600541100d0301002c0449186841c00c50381c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 943457823 1250 943456573 943456583
    0x70e040f02030d0807030c090f03060c09050312070203100b0108060118030f0b090f01050412050705101109120c09040618050d051b0f0d0305060111100b04230105010809030403 77
    0x1c444600100d078008284d1340a2a1180c030300f8024002108401c0e00e5006072400741c9482000a0700342000400c0141d088064020118145030140e0358584000c0380c1418103410b52420340c000c00140e000c0841c18100081e21144006071000c02000248800081c5101c60241c2054104900f003401e80c000f503000780c2d41c07134001035512119449902140d0f242c40c0a07000400c581c202054010719808002000c1c040c0a014801c40e80480f1108024541c1281503603941c04c241d605443d2849207511184201c5258880e5004c101c005200c3c0d00c0d100c02c0100d04210294410400074441074000d0f0304884001e0b01c8040c40359400542c48030020a01e4917144003011000d40d405000507003144541d070f480c81d641d540c000004249186c2c607408c807012344842c050012a6250107591240c60f46d80e01c082c6a450f0030360f01c2640320710b0700110145042d901c010801d018052401446294410055944804e1908680b81c20311446412881170804100d4000c046107426075001c0c0c0c140b00382818484d003180014203418007401164080c50b801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 943459073 1250 943457823 943457833
    0x3190318150c02010e101707120e0721030806040b2205101409041104023f27100905010b0a0b1c020a120207080306130c02070e040f0203 60
    0x510300600d00030341c04100f680460021a029603d50510000000c9050302c07a4603405e03021842140c00c0f070181c1078000d104000300000c81041c004c007010035000792610b11301504010300c1c130a81000040b80c0c0f03584614012202e80d00c21604400c1c002034002200b079a12000440340000d40741d2082e4042000802180c145048111900a0000881030581c1c000390203003814264003824961030b985540f012001c0611020750000001c00001c00181c0181d41c0d15102c2400900058285403c00507450385940d00f0001d15101521090049000004007522110740d0181071020075255003814414408141c4074405901c0c94480818004004000c04104202003003540c038404005800c081d00703000e030080000b4a1140c0c41034074895400182c164000e016128a10b00209500d0061425442039100039403280917880284114802440003504452001d05030780350080c2c89540d81ea10340581008201c000d00d042c0e4041051400020b842130325400140403060362001c00d1100f4907030320b1398208088000000d0200075454811 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 943460323 1250 943459073 943459109
    0x18080f03040c050306091504050a12110105060103020a09060e01031e09050f06070509010807090e0a0506030118030e040c050c072409030201080609040f1202160503190318 75
    0x15000218400c038050440c1040310b9888204040d244d61080d41e03101308992100c40c801c003003c4c0005148139081841101124401c0704247c3c1c0794201000d001d10f00201095106103400843c150a015240d8070580c01d103001c42c60007140443c003a1100308140034070780400490018003821a40130790700ca03540622000310140381c204c1c0b088414202510303100600702c5540c028071210310035240000440c1c43c081c80040d200c09041074401c5004654000300103004104000e0900130008194440039105030140e200c0361000701d050316155050509643c00c4000d03001d041c22401c001d003004242c0c07110240c0c825580c111008070340f100e01040e044480c3c1c0a00081e0312814007501e90f0015000b001400c0900d41c43c4540070002d428100402800c0d10403001e144000703404551201c00080c8140b802d12080396200788190000040c5203d291100b00e5283c240c04600c03009a40000601c0880d00300c1c0c5400781c401040c3c12001450000076040c902c1100e24401103005042c402076080d10301a4050100b043c40181030f1032040c80d00e00201f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 943461573 1250 943460323 943460347
    0x106170703110d050a0e061005040e031e0c0a060c0c02090106020a02130b0112110903120c0d120e010c110705060a1b050a020303070b1e060303032410090f0b040807091808 75
    0xe681d2141b1403142f860b045034505003000100580ea90182d5010124080260756400c03070090f54800610741c0c0c054001c0c440d12400160440c400c1e181400c4141d07031174844500346031042c450201c0041e000344081d5400000d0307840c0107070303640145909801030b440404100d8001c01001a01c0f00c040d03d1a030824810706084d8840304940c00c03180a0b250a1001f00c0403299090b0000103a0b052511a05011130324a4002104049200780074031009803040d001d200001031956400501c50b8219203145a0010001c0e03550505441d040c0010400c0c1405488100d030f000e0710300204000701400c90081400303625500709154a030704050082c1403050401194016040c1e0307640b054580f40030041100112558140410303e900c8100d02101c0c00310700184120742c0a0004c4d850764440d020b43c0b440c4403820959581009541c00c002c074500b91540300708a103000c4a940c1b00e0300c1000b8140066244e00900d541c000d291508824041009140d2002900c60b00b100d14a80c1c0026400d01c40c05900d446900d0b0042d4003411481c00000c1d1011892 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 943462823 1250 943461573 943461601
    0x4050901051c142d0c0f0a0b130512030901030506030d090e04050c0d0c061e0503040b04150e0d0806040e0a081309020f04031416051e090106170703110d050a0e06 71
    0x150000300b0703180c14a0b01ca0042281d007003281c50301c080e0400c1f01c0d6402407003920f010200600d4410102d280246901d80d8400c0080c1d00b07071070b800c02e410400707400216100c010b65805020741608208100c0280854165114008124211502c102149020000c0125090000502c81100c0528005e003c42048040c1030a107641110864460030300040d071420213501042034515074056880409503542e92841e00d55441c0c5158003040680141d1f4041c0b26a40c01d910541d6107031280200c604000c801500300c480c605100984009001000075001d1401c0c80b00f0261603581c080b58040c03909e40d002c44035944482701c0c0d094150348a802504030320340c0180700280055200e8035910140088901c640b091101d02c540b4110781d15240c003141070321445503002a140c1440b561520011001d0395050060700e414214219100003600d0400030303840385d00400d035106000d004545d01e6609181d071247d03140c1001d115400060040703805034851802092040c6995002144074150a0380114204081120494406042c5140b20710060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 943464073 1250 943462823 943462903
    0xc020411070c080303071e1215050f0108010b0d051e0702011b03020a080f0612061627030201050f160c050102010608010e120a090b0f04050901051c14 66
    0x300c0c4000000080784440001184d100b501c0c240c0c1c4400c40021b9588156019141e8041f0250512016000384070303843c100b522031160718032800d80e02010302c249071800b0311010064001070141040341c00d000504c103903c1641c00311107400c40c03241c40004d030991b01e4500b04103544183c2e02c45000d80388020f20611032401d03030540210f508103a0910300700e0141c1c1c01d020001c0d0700300d1164103401c0c030111750003200040d654020480c2140e40800060841c03918003007642002030a040e0b04551000d401100e940d44080102d900003c0f006002551002030544074081d0710300e40c101801c0b9440000e04001c00050050fa800040e003098800285a00c00d201507000e5051a00c50209070036401001c4c01517103000780c005800030f0140501a595800003006d0500d24100044801e00c0340d2140191358180103951324001806012200105105000d245440343c855082004101c0c0007481a40814420030303a190b83d400b10b48400310758282001e07030710011024016400d54441e5007483c84244040105081101c0c4d00701149411100c40510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 943465323 1250 943464073 943464083
    0x4030c030b04051c080a0b1f0203250c140415060c02030c1e0f0d0c0605041403030301050609011d060301141912021009210308340c02041107 62
    0x4c1e11600070742d0401c00310840c50780b00307001030041c201103032942d451644105c002c041c001c1c051444251030000360001c0d0880306420000143cac000100c0c01412110344581541e1718900314610b0090005580340c40e035240c3c203603008070300745a40d25490310b10050f0340310b5228111510428001030000b030707545c0c4c501402c03c5811000c207900031b01a000054003149801c1992600b042d0440641030071f0f014011007800b080c000d44030344464001842001d0324002c11180c0b4007600c000c080039941c090750f560609501d84130360703a41d0040d0300e4040d90050005000c5541d0390002c0e111000402e1030510800031548151321081050404a15002a000000810b00103280e45420719071480c260707100d08003a00c0301c2c0c1d0f90140030400391160012588040c01d0503001494014800c5d0704443d000d180103103010741c40390311142120100d002e01050b90880b2400070020903800154440d4811455030350111a4540d040004801c04e0000760101c03060121440116103403401036154224441c0c028104020301c42e82c014164a00c1c1c0d00030402669 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 943466573 1250 943465323 943465333
    0x4080d08011d01180c0c02061b12030121050a0f11040e0303090a03180806091e010c0f03020d09170403061116063306110703020a0e0a0204030c030b0405 67
    0x41d00b03090242d090b4101c1d0f09441d1030880c442a080610750040c407044000320704204c40c060841015035a80301c090918824540f100054007450320f0765040c80c081c4d500c3c903002c1d040d02060004204001c910300307a2420001c010405001c100030589001400c285c11004001d04000000404c881803240c01078523900074000c1030b03404200d0a0741e0012199904d0100b211641e11a42c040c00f01480000e1240a4406911001c80700700d00c20140c55124140c2003a0307045550f40c0840d03018580d00441101c3c100088004862414001c103e502d810090003030484030240550418140c000604201140d060b0744032000442c1c00000900c4204000c9601201550041c40250760290402c0044040b1124140c00c03a2a90300ca031000c3c0c070b54a0b40b001e65545000c0e02e4083c4442034450058940440918881039981003507210251040d41d005043c1640078019a2907080740c05529440102c0c18130060720f45006200070380e500e06065904036564030204001034403031500700615082d8080e000000300f20074802401e000d144900c058070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 943467823 1250 943466573 943466609
    0x2151302010c1a0f182a0105040302100804060c050702091f0b0a03020c010b0a0b0a11010f050109090311010c02030a031d16080d080f0402040b040e030a1d0a12150204080d0801 77
    0x1ea45409149503c3d18801e142201b10314001860401d00c401a481814158140740d6641c000900d00001c1007204c40c04190403608110401103540b14826000c0707101e061a0f401e0000607000316909040c02461500306038628085a840030410302103520040441454003999030324404402030294104035910301c1d2660820301450881c5c03031300050810a03a04d186200509003005880115880c020858040c1e10365541e480c0f0410040005001d441d01804400b00007084007070141c6801003c8403010840c1c10f0450340743c4440c01202e01c3e0b002c01100d2201c4801e18001c220f02011070a00c60705004000702010151113144c2542030008002003010007100d10002c1580c200c800d030305405895044080b80c0d80b01102170700c2800900146805d9020751302110000e0310009503102e03d0071703585281d640410000804104080705400032107000301e0302040c0d001307803d44410003401c0c64400c07a01c0402d40141e5000f031662900c003a0b140d0300c03080c45d40d0669000305091411104001020f503809008806c0a0241e40c0c0aa0018251a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 943469073 1250 943467823 943467871
    0xf05130c0e0f0622060902180a0305031b03090a030b07230921060a0516030908070b041407060f0906030506030d030e161502151302010c1a0f 62
    0x8910902c10b1110541865980070104110308615002c800402184102001c035031503c41d1140c03001906079501d005036036410038540b01454207942c4038560b1168400580a01c0028004020380d041c00ca000c0914040005480d01100c1c190b002c0c1882d00c0740c00102e0480300100384403514115500404241d2508004e212000400440d4444d0024426070811003c1185131540d0421560342c082d1030360324008050041c110140c020382445c20603201003c0f001d0729402840000e9200d180c501641c40d2090808121055050b6510040380c007642c04003800034010f080008050040c0e289561812000340b13400c1d100d0103620b461024209480003540c50300002d198a0340826480d01902c0303030078003c00e4010002c28440c61002d10440207046943c219101c0d502440e006089851000e5031801c02400c0d80545050064107100c174000e140c00042c1251101400c08a0244800e01c849641a829800d03020304c1c0010078041300e41400f00c0b9030301d14895031040c14070a2204100460300c4804c146400b4801e180d501d008000401010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 943470323 1250 943469073 943469099
    0x510090906090b16020d0c03051c0b0a0803070f0f02040212011d060f1c08090d03020703020315011208090a03021f0f020304062a020a0b07050d0903080f0d0f05130c 72
    0x1309030090b0b07125101e4040601d00850110090500c03070f140c4246404000d00981c8948009005812000c544459050321940342c005401360250001400840c20b100d156241c0554000c044540a04110300d4141800d06640b940d80442e907074105030810310909541d40d5501650340d0340c1c2080700d4200c0f400102d0f001c0b84da90718000e004105610720003040d04251040f000c101000d8508a01e600300d40052040040110b140c40d00f14065101034040d402801c1d94502d140141800d092b800401c000c1e2048560006020380146141c503103021a13048803082e604d075000da0020520074005604043d5000c248150719015180045858103042c00c4e10303030303201002c140060905030303034a0055025031004a0400c604400448800c090340e04d84451107080803640c10401500444c0108003150045c0845402c0020341800b4402c0030044200341c061949000341e22145591a00742d403c1c000c41003114884100002c42086c01207003070b080741c0c1140070100800c10050408000a040c403004889084035540d0048a00054460303003641 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 943471573 1250 943470323 943470361
    0x305060a180f1421040e09120301060507050a0501050a0f1a33031806010e010b0a030903020a0c140a0503030f19020a050a05070515090a06030510090906090b 69
    0x1680d18180c0c1082e40e02d0b000020040140b0fa95070348142d000810004c1c0c0c1c030210904a5481c3c003402a6603a03818078145903070200e001031a601190b40182d060103480c84014049a04480851408d941c840a040c50454103013481200050459800d00080c0b10040850b503200f107502c0d1100c41010080c2c0984049005024500c03074503403d6000104011030001c2c061250701034603c603640c48801c5001403509840114850304241c1e2607020210364000c0d04040944100642070243c503010540b8103e5615060041c0741d0b51150746941000c05849102180405008101401501741e111100740c83c0a900e55150122440c610805035106465a01c00052281008411580007000c0709181a00d084039644540300100c1210345a43c04520403881c464000c5076003446a403003524480c0c070280c48410300c0d000c01c2080184052540c50401ca404212814241e80d90205c0013045400310b08002c034040c2d072000c2d10490742240c00d80c4030900e8241070840e09020800d040c4d10158606120300c411101d25100e811052108180d00c603 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 943472823 1250 943471573 943471583
    0x30902030c01081306090b100e09032205091305010507050403020f0402130b0a020f0d0f0c1203060b0c150c12040f060908040909020a0e151203130305060a18 69
    0x100c0507140c1540710304015035100b02c003114081c42c2500580d80700b00072138900c0342050b20300c54013107010b104211401c0b900b40c900a0444a5808400d0300b400c0720b40d29143d10034070f030b81e031100440070101c222003260707125400c100141070040840300c0a01d4243c041e24441715165508407015468040020380240c0110181c0782038270b80190200c003d0000c40c1d81400001e5015492032100b00120401c0042c4083c07841004003000f4800b40d001d8034000b82e000f41d459141402c2c895415013404003404204000c10f5009044207607998004040202c00c0c098100242c00800045d001001006000100f408120b04c00240240b0226400329603402240d582203580459070055030b50441400032014049404508802c00b0280031500980c8009002400d50351140c41540c4075502815295450300951070642c42d2880c000380003420b12054003000340c60b2801351085143d11880546104641c000301461030910200b0030f070f0354180304407003651200e1030321f1303040081e0b07200300450700c110501d428034200742c4c4994072401e501310f0016402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 943474073 1250 943472823 943472833
    0x806041b020d1d0603070c05010501060219260f13080703020f010522090608010e0d080610020a0f053702010e130603030e0f01020a051510030804061e03090203 70
    0x1481088030740442c03450f01d00d00703491007180b42d12803d03542d6000214003420458481d0f8817a55074910f45682500c005070b000c40159004100301368081e0003001152021158800388000d62540000f030300798004d103001040c41c41910000700d2183c08450350240184100c000d2402004201c42d41c842e00b0300e99841803404000d40100b26076034000c1f0b4075401040581200d0010800107a191510f10108610000155200d02e1900c1e841d0300b000c1104030821311a03010244d903a000907050840c45440d000c2c028042c082e080358091400c4020725040e0030300c00d001d046842644040078101356081c50508a42d507c1041080e09100c00195103104211404451505285540012008000b075465001503071002c032008044c1d50400140340c601125004035114800c00f40d80700e5118421200f20000c180300740c800e4011501c41c155070000411070086500000e070b40ca2811050310010003196030350260703890001c1c4d85034401070a554002c0303000700703006401000301807803c4002c8000501881c84054218152405100041e4040e040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 943475323 1250 943474073 943474093
    0x101808040e09070b0703020c181311012105100b04080a031b051f23150f100e09070521040201050c10060e1b040608250806041b02 57
    0xc0e80d6511a032150b4030800381c4540c0760b42d5883c0b800496000d07480440c0140c1202d00c2d5801d0a18055810151021119680041c2440c1031500c034100d400680402500c000d158a031300d19810b80c807824280c44032940200076800078610611256010300002d88d003514ad02c480e04100883c014059030700340c03801c0791305010081286132025281038a02800301311000d81621018072501c004150300304220802200d100405c01040c1d030740601c4000407901100b000e2003900b034122130322040c1034400c81003071600802030306441122204e81000099410010b0342103190440e202d4800021841d42004200710002e10941b1944640d40e541c0740d040b903442c410100700054031400408030a08600c0909040790b405031040c1000ca01d40b44071190150700e06000c0c00d0f03580040310307100c00d01401a10400c940c3c0a402c08ac90f030700039040c61007080c1518a403c1c0130f640030b01c004004080000a440920b140125043d0f8100400900d001c001042002058040d08451441c003440c28081049980105000c640b01d14800d5603019000c2000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 943476573 1250 943475323 943475339
    0x5120a03170405010902090c031b1303030305060607061118180f070c020a0f051302120f04060605040903120e0c10120908030702010c020d0815090a1d10180804 70
    0x6400b410544582d0b45c0c480441006031a1680744500403c8081012a26813500980700c01c005424049901d980e1030341030048024007942c103070081c415217905040208542e510500401e42601980c0b00c00b0340140c0c28500030514403d80303580104814880b440c02d40e00300700030210500114114040100c1084251040011295004a54880c0e00510b19141c26100000f107a000144c5240040e008102c41000c644420002490200c01d20484481d14280960030040b4002454200800c001c0000c842d51070203800180401c040c031351101d800b501e0002c00400500c0c1d035030f06000b070004101d5201840d40c10310b4144c9070a0400b0000404099000d00201403000d030001004040b2400401c900480046c60b499460400c002061000594451601c69000060000780c019000b86000d002c20300e04010b20841c1024800c0800c8501840100d241302918851881d89880a000004102c5100a22003602d002c01c2e110380004004030b84003410600420080c054010910718440414111180003005035604000c01c100b499 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 943477823 1250 943476573 943476617
    0x6031b120414070b0f1204141c030608060c0a082d221104020d230402010206070c030801060509011101050f040b010812160203031306050c100c081506130f05120a03 72
    0x18400c0b51002c59186230650028a06104004002d105c001c1602d81201d8895151240303600404c0c2100080c801820168040e0728184229408131081200080c00195007500040c2c000345e00600c032984c1c004034040350540f000030b50300091381e415080c41010080c840724000407044844005810030005022280c103001007000a502c02c0600c8a4021307106c00e6104800d940c04050a5140c60390290b24841500d8248002402c04034002d0068041c00140745000740800d030f000b0310700350644003141000d0366030b039109000503500381c044c1e040052140e60038030040049a081107214130707014500c580300500715a42c907800c4440d100c0c44040d003a195030b0b040c107001461b4140d1020221010290000d81a207281204203801c003000400b8981044000c207100243c3c2450303181007040001210380e8102c80c1001884104500100310000103002090b0300784071702112684135510f80c000c817000510421641408245d403403c6c0051608003070710030a41f04140341845c208220f80045081094a94190307903070700d203280c0d115450502132 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 943479073 1250 943477823 943477831
    0x309020a09021e181e15030402040609050403200304030c080d030c030618020306060409141603060e060607020102010e012c070503030a0810080102030f09100b06031b120414070b0f12 80
    0x3500c080c1c0030301714417500d818415861504a0078102136032841c16005000c241c500560180d074283c0c0c0303070100b00408264001c003d41d00705260341d56034803152400000d56900c2e600a40d040502034042e2040300045804000034448002c01058400703002400c0c0040040d01212020f100f040c50f6003e07144000342c481790055004683c0400024002c0341040d0715981500b0803690165002000c4240c601c061101382e1f01e040c0707002d81b82a04245824040181040c0035a04400d402501840c0200d00100e84001168001c4d001040036890b10340007000300308030302c0c5000c1c404504814441e81002c8186082d06413000c0012030500180c8601800951030300000000889944400034210a040940070340049000c5800380029406000f044110000038144002554100482e05c40c800d49520300d400001016604c0380740549a1280d03844450080000e880c41e1112884d01c2030060007003d000c0078074100400c105030703e18121140b817101070899170510740301d041001903031140d05620180c1120911034500b205807514102e03a80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 943480323 1250 943479073 943479109
    0x8120a0c060f090201170103050c2707030c0908071a0307050f0d020405130506031f0f05190c09140f061912110702010518010309020a09021e18 63
    0x340041034031900215500707020b9280d009901c801c1a2401d66a00080e41d04012445030241c0307640b13514680d00d0380d6481d0080b040e0240154070502c5000380760840d100303925181e0b1244d0300749840685440c100c02001048164a0100882e0b000d40010a400c90000341c20419079101e0b500710046025010a48403554100816140400408003c00e14101c2480c802030603041d0b980d44030241c0c41f00d08002c2040780c60712503a84081c2091f807603d004c11503996030028a6046101c99547c2041c2007000b0341a40b2005003503442c1c40602c015080030140188800d600c80c0181d06240302445c10420081600c7d402c0300c54600300e100720148a006400b1186080c0b4090108000d10f01d8002d02661420941011921070b507480140340e60081403000d46850b1201020340954910b0032400f1104d0740c039019617580040c01c240515011030b81b141000c180c0e4501a0f90080c0d02500c2c42d02d80060000501b1a0344400500207580a1070360600010701c041c1c3c0042c0c40e501c0c09802e4480da031003030201240344089890240107d242c038061075158 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 943481573 1250 943480323 943480337
    0x10807050726040321090501051c0908040521010e0606100e0109090507050a0e010f02071412060103051c0207060c020915270c0a0c1b03051b0f090108120a 68
    0xa6850422000b01060920307220f030110360f00c1d685c00303429002e890307000740d0500c80c0412044505003c040f11900e683ca404000000c0c60071101e06201c00c050180c3e412850308080c2040401c000c24902101c40b1170f02c04400c2c40280240c0ca0540070075070719400d01340c5100d1f810030309500078004414040c1d81e0700d0003010410314144c0f0246544456001c182c0300103a03070300030124000040361040c0300c1d8041c0e03104002e12020300f03140241003a42c800007541c4914612921030049080303d454022035580201140b46074000700c0407555196120300b4890344811491700c003110300b10513102c041d2026500220f903ca00710388440d1105a0524055024400104c500414862542590300f02201d580e5490b901078245d014001c91040c1c0a110080da05080c008401902c40d401b404002d001002c1c181c3e600906c2128515071004440c0c0d808084101d51950460b11500000c1030340c00303051154a48a1140c8142c12000101218000c117610240d605103d2040400e01912509804c50070700c0b002c8104400e001004840319900d4000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 943482823 1250 943481573 943481579
    0xf140f0108042d0201021c0801051315090527060a022104080301050315010509040311030c0102211303020d0f200a0c0b0c0c010318060509060601080705072604 70
    0x901041a40c0d00542144440c000143c1c0541d6410000c02120240031988501c1c815050800540240700c14840c0901c512a518120034186c80d4a130032100100107040000081181c4860400010b0401281e100c020034864140e0380a2400180359003004000da540d024045035216802c004020b544080c0020081710070b40f8035920301e00700d403044645204902a4229070b8603541400b04040c20001500c000040c0a45000010700080d500d0750074090f0010351608140c801540d009a48a0031030040b941001095480403854042140b0f01001109118040143c400c032250345003411610300441d07000c80540160310120f28081054061540200b02c8402820070562504100301c0b104104902c1d20358805031500202000c00c02c11840001d49006000e040f40780d60b0605a02d42100380d51800407012007810903442e01e00e940a01009400c404640301e03000003041c011441c00345006a65680240e6556002581c40e000268a13203102c0c0c003d64186a0340005502c41c440d50311082d8404481000b0f070590704c0303060100400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 943484073 1250 943482823 943482863
    0xb070311040b160204110711090601021501080304030515041a0907090207031106070e060f0307090e01060201020a090e1504050a0605191409010e0c0c0a02060d02040f140f010804 78
    0xa0070681d60030f00790240d80c655051040c40140c07850b0110300501103506000540c00034001441412008805940c5040241d130354900407460065119200c3d0401c0c0d1011001003850a004001402507034004d000315100030f05452070845001000300c2d006040c0e008022100100850300180d880d4100c52a407084982954482502c0002c9034403160086000c1282910b01c2644081c040c007079160b02c030a441c00c04544502d008004a0800d2190000ca101c0d5610004002004240908000d2010f0200c050b519155581c403504040d0007913002c21102400700309100400182c0d084c0b08054240715801c411031141e03000d140350051101400001c1c0c00100719a444000114440e1501102280e41000003848800e0607840d02000005840c0a2400c4034003407070300d860050151085080c103c6400100b5104515a100d06081d0003034108034006000940c05000004d8100310030904c1d401130001d44642050a40c005562040100e10301c0b1094006c25402a540401001c11980038641c4140c0c801d00900081090006940741 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 943485323 1250 943484073 943484077
    0xe0102281e0806012f031e030f010302100909060311190b0d0908090d03032708030f281d060613050c121303080c160b0712060b040e0907030b070311040b 67
    0x44980c21780e2002c035619003910400b20301200d203812129003035403231402c0c64408588000e80500011b8001c520300c0101b50380c15442807904100800710340d0010000c40392246401411710b840c0c615144e1103041c9041070b030400c2c84403181c0140100c0352403a03511460184052907000c042c1003100410b40310420140142c07983e6443c0c0d0300000101610903a000265400b0460a1286403803050b402c0313011040c0c2d050004e02c005410042241d4010440089403051952495500e048c540045001c034011220b0f00b440c8071880ca640303900403640035042c0d00000190340e1071089403da9031318011140d241e030160590040001140465000642141d08005040d15111102c00b500f5502c0c071060321880f0400c821544108245540104d03c02d070403e007403e0503146800ca40c030a1182c10000c40c110050402c21541001c1107145d401564002d055980840301482403598641004555401903c92a03420306015130000b0045040450742c041580d62014041009840b400400c5005115071622080744030010440440e94141d9080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 943486573 1250 943485323 943485407
    0x1203060810050a150608010506030411030d0305060424121e03090302030715050d0c0207050d0b180a2d062a0e0f01030e0102281e080601 60
    0xe00030885080494440d000c95a40d01d081a2030348100510504c00e03240d00942d20347c11540211030f01e0f40c4035241e038101132940c1e0004500003940351280c05480403003103801d40c01c29445002c0c1107404000d0030810042030301040183c1d01d0340003800e1f8116807040c17046829000ad800340060080074112849165080c5800405490346004d41c0404d0404208004501d030401c000300140c01040900c200c4131380c50180240007030054980b046005070329281d003510703050310801841c4002c26004200c440b80c1c0f02c235414140d0310340302c0c255144046c0c904480e480c020081000601d41200c280d01504050350002091a050800c0e00c2034180c072650b15482443d1440803c00e1400f8050502c4130920303443c1044020340c2c1e8582040c009140d22a02070200701c6204220395034840e000201c0d0450f0078200410b5402c02080c803a8028800c0780d03201041e00750300f02071409082c40c00501c1b500440e40c480e03c8810104d500690040b07610b014603500b282c000361299000810f10b5104080c040840c6c4202c1c1000040307034180301c1403170303801c601416 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 943487823 1250 943486573 943486603
    0x7060606090e0108010c0c1202100f091e050a080304051501030c1e0308160215040b0a300c1134030804050d02011205012403150312030608 61
    0x60802d10001480030746040c01000c1100c02084140d014100c081c0041e8101c8402515290040342c01881440c02485030391022080800100b0010081240510090a030480192503041410001c0d0300c680c844003ca41c128180c000b401003085000e5a65560010303031004004846601600c9109052061034600884c080c52040c10814040d0341000c50503601c080103600c2042445c000d1030010408140301078111081507a4400405000148500101d101c1c040c1c880300c00d520035440001d00080d080310100c050001030920781c0d80c500f03034000d0fa2020781500700540722188a036196007203000e00300e400099208045010444c00d0880307107120b0a0300d0300c03801d000400a07490703c141d4465001080706681c61503120401810f07442030212203821511002c0c0c050180703000f19030203114400c1c003c9041d6801a00394400f510040c1106004543e1508101c012040302c000e0105031103210903c01100c0719020307000c0c4a01003643c80c0c3c03054502c0c40c61030301d51100701d0001c50039001c03c2c19a11000856215010300205440c460b540c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 943489073 1250 943487823 943487837
    0x1c02030411010314010512010b060f0c010b182212090302100203040605041815060f0e04050903030720031b060109110f030402060405040203040b071701120b09010207060606 76
    0x90038801c102529208440341014986003000c0380844450004606640060300d11030031042c00c568040c0d0040c814480e200d07a1000000c141c031200942550001c003a412004070003800701050803801e01440300c041d9a12896040700600004d04107003010611400ca00d042101d600d040300402d52238180310400641010000541e0340c00051066091848861070700103560302c029840c8c2444e15000918600072030144d00070082d045050b000c0509100c1e0080c441403801c0441842030039543d042c01900198251005c00302050b4202140b910351700d858031583d4410f907003400185103941c0c2e40c0e02d000c5526660080800380030520704418190103c40c04c0016150b90030841079030300c8040a10445580c9070000507800003001a04290ba42906040e10006551303980244101f55600c0f0784442c400642c080c0640d4004d95002072002c000c100601029910540c001d01d00c0d40c545403000118400000d03a05542405009483c0c80c2d60350800c0001803043c009154040305010005040400d9a5074080035507200354040000a049 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 943490323 1250 943489073 943489081
    0x151802070c0605040b0f0304020a03080c0d14041a070203161e050f0a1a07020607080316030603030203030c070309030203120c1c0e10030905060a051005090f18031c0203 74
    0x1c03020030806014a400c0842c1414508084e51440c0c0c401c0e020034840ea500c0205c041002c43d203a20140001031640403440b83d4a03500e80407041c681c2c400c1c011803088005207003250142c0d44c00341040203c90607031310501004401c401400207010000c4d070080200300d030107100d40030800c08030400d143c2c0032001500411032200683c540740410203088800c150012442450250f000c1180350f607071058510200c1e00c0e42000e2803000032a02100c6801e500070840065040003000480f902040f030f03141e0095100d903221001102482110340c504400301e030301c03d00006000d6030040001c500100c01f1080a042203510030314000c10360923140c0d80401d0070100314240031115080045506141c0001c1441000ca0701c0000501c0c0d0381001d0000180100840b503a100594020718031034195494851103030704104952a000402c8441d24204a58680018141282d40c0310466064000204680c0f80840700d06004600310001540103850b80807030f10380c0440300c8035000d9004e40320070031442c88070002c0e0a103003611030b40c0c003818016203910b4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 943491573 1250 943490323 943490333
    0xf0f0106060e030c09040f02150706020406031812030203060f0d08030915160305131a01060206060d0b0c091f0c02040f0612060b0123030907061106070315180207 71
    0x90440340948640c01c0902c0134403954480004459009422000c0c071905880540045020130030400003100c003807580080c00c60306000c000e030028000c0320016641040640390815403041d102580c8080104460006554141d40c0c9100e90040c580003c0002c0c040000f1a01c1980080d41084484004490014001c010001411828020b032810b10000c01c0043c4240c0c07a1000b441d001c1c020111000300281070b524070100c0c1c041c03154004000c140720342c0300300b0107103050544216400070031400b40b041c0c0c4018407a010026110342031959051400b80c1e4021081040c0da100d0001014041e00610511a00325803010380030040c841291201e040e050310540c8804035071642a005000a4a540610401d1098202030042108004492440f0040c3e508400000b0700802a2001214011011580894551a400c00c1c0d80c04040020740118003451744401100d0066985031003da880138038403030b41c2c03a5031504844000b4000038081c1c0c01c400184160300d000244119201d507000c903800c8200704071820300f941d40803c02d181008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 943492823 1250 943491573 943491587
    0x10522080304180c0c030c1502070b13120f0c02091b190f0309080d0203040204062301020606090112030c05030421060b010c05070b07020307050603010902120a0b130e0f0f010606 78
    0x280740d5103003900c0034031946e450141030040340c03100040c4580c060450112295003664107982038180c0c4851441c2940c20320350000d00006d22003420a07101c60007950106260540510074030210701c4480d0303d500120612030780030460702e200021302c40c1c1541c114402c0307045d00c0030784044024507081d02843d28003440c0c4000f41000170101001c03004d26000341494081c0c4040400c02c80b8042d6205008070383c5000d03a89030740d0f03031000c90050180383c1d000c815005036203c0116040010290590075003902070b8211036481d0740345820880140340c20720030300e040d5003112400c2e90080781c440c61400300400e009070120f07441e1954440c160300036121001e89070040703858100480420000745005580030b54200b4038100131030101944615480700110720440c205104001110411920306001040007000b000306803e45940e59081c0c850043d41c01086034042c0d500c48807000484550440c8a5540400c01c00b4240b105603040303100301c180003030101254605891180000728015003c04000450510a080300045690362600f0b101901034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 943494073 1250 943492823 943492841
    0x127020c0109051501060903060b04020c07090f180c050904020613080d14070b071206030506090d030b030a050316031218030f020d140a03021e0306100503010501052208030418 77
    0xc0d113103c40100310043e030203844002601c0d08090000380442c10900010000d11510000c44064010b0700780001e4000315039400241c603040104400d001c4000441c07180030702e04102c140000e080c0c070405d150034881410000602644184082e01851600e0b80721945540368603003507402408a9400b0402894100f54071101010110103040740190074444141e482005a140080a400401010307400d900c060325499041017004540000c16103040d41800d03501282c8485d00c189412010070306107800100e0908000070480c50745a0004080e45c10300d07289070040d0416040c246010740420030304140c0c6045607040c601c250b00310300c080b107042110601b4640c6006050039415000307101c155048003000e0200c2c0b540201506000e04184150180d8130402c07440290b00a00612034914220307018a030b80b80d160141208020b5000f4182260345007400c0c01110000c881c03a10003401818000b403000d1044080f1000c0c080b140031810408500000794031a240c1d030300c82d45960443e5000289014140c02501d59100e9148100902 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 943495323 1250 943494073 943494103
    0x1713050d05030d09030e040f0204050f0109060206070f0e12010e010b2710080d02030409060f06050f16060e10050f010303021515090a060806060d03080127020c010905 73
    0x20240380303a2039007a01ca0040e100001122900e56954004151003030403000d5240300000c108001741c40f6109400f500a4200340603030b070b000f020000381c0742e0015030081800307504882840d4000c2c507096075250030481d130340d18416014100b4403070030030b6240b89a5624182d501d440d407410300c40001070410700810250300303492203420640e000351003001001c3c600016014125603080d4a562000c0d2864840d0b510300c403900711050303121900d075010f2040c20503143d07603010000b0011141100300601445440b01307900c0f19844014450040030030b900b00312115071160f5543c0500b90020000d103460041c4030b45900c074401500c1d03000c01c49a0094002d0901c18100d002c0b10b1140c01d8010b0b84406030b0303401da92304564000e03550b81d40c2030807441c00141001d000550250185404020800c501810390502810000481c1001d0305036400b83e42070700d001b20340c0001c03900d0a040510001c0d140c2c156031000c050340d1070110084140c08450302c41440320390743d40c91180c060b00828002071400180c840000103510f0b01c41e013012070034000f6078445c0042c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 943496573 1250 943495323 943495339
    0x30b010801031101030c020a0b13020909011a0114091f031a0f04051009110706060b030f28020f0417120f180910030b06010203090d080d09171305 64
    0x115101c4158030210030000e00f40050b40c010409020380c640004a880100401c2e0791808000950b403050504024103031033503070b550301180c83c0d405080303003070b50b800d5013522150b02c1800e400d002c2c02c0c0d80f2a07428400100d0b8019405403070211075401050500d40d1980c0c180d141800b08599071400300d9070520400302504040c10058800803907020010350203117070301c8250900c1240c80d440401e11194001c0e40c14001007880c031311304101d00c0c925118012050b801002c002d80700d962401c400020381910b52800c0368864040c2d4822500e1640d12035a11444000440c40d0501c0b4100c038808040040c1c0045100411445010300750043c0c60b2451311850f1500b10032411211601c076004200c600900072400300c255060080c0c246009a10365420b80e040164181110b11425800241c003014007070032034602c0070050241d90141d96001110307521400160b81d0f80c0f05084901e13410482c0000d0381400700b0900c0c405480d83c4010401e020449250940301c1b00d400201c1c2e118500814500000d0b00c00146c550180001c0c0140b0741600c040b4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 943497823 1250 943496573 943496579
    0x20d080d05040b24010e190e040309080d0314071425060b18150607020d1505160e061309060305031207030501030b040204021602060d06060e1818010902060a050307030b010801 77
    0x20010a002041381d0701605640d00701404180d87e071006d84025010441d1418003515242c20001c140c84000c0c4034401c0c1d01c1c000c1c0382e107171080031f44203028401c02c2203400d034001300c070030780301c01c14129400064010420150141400407220344032011003289070744092044024a044a507050840454070856244e5103c2d009051640d003950f0160300d640c40d48003c00107824840514150080703005882120402507010b000c0e07842c00c40400c458990494810a40b80c40104429910854141c1c42c00300e5640240002c2440e48841d8082d514000c8010100c0c3c40ba000400106550381c1c400e001c0c00e8403402d400c202c5e01900042040d0750241b0360007148641c0f00d0010300c0c0601c038552568491124007440500007902031074000030070296910502d10748400156001c1c00283d40c0b44465000d00d00104407600035180041c4955059039218500248485405c01c00e00481d0210b07500d80748020b0b42c1200755106055070750754031140d840b4096540c240c040c1c81c040499403182544c1e4900148002c00301e0381802d0115041c007403404014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 943499073 1250 943497823 943497827
    0x31101050f010b0a0c08070f030e0a1a071a010e090d0216120305070221120711090603070803120106030c030e0709050907180b012a020d080d05040b2401 67
    0xa40d0443d002e446609980703512810003241c00000303461000e414407400080403010880c411180109640c06560340d800401c81c08820824901c186204d213112007002000c07070b9441d2802600c010900e03103214908821a05000038a10a40101d003603215956850390078042007803440c000c1c480304000c40c10340c3c8003401d0340d9810940c1e0f250680c0028000c550181344550150402c06000307208541200b80c005103006005d8042114113614214203101020b1140502a50004c0f0780c0c60705820b40300401d91141820000c4c013000c50520050f0071008203490b03850b11a81c100054a418203000420b002c200c00711030201d0030341c10310001406540e00700d4078100c200b504c3c01005042c202008241582500c402c64804903503603d0300408075103812099008070020650000c242c404118460f40b280400440c283c80700c0303410400000c800b003031050b402141d400f156003440c261103006203805050307601c2952083c80d08e5820311000b1507110b011664100d81c200c800a40b403400303102001d150450304500c40348144c02c114020100350000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 943500323 1250 943499073 943499101
    0x1011060f0c0409021603090911070b10030b160318080714120c01020d0e060c1b150411120303060607060e0109020402071a06190e13021c03110105 64
    0x314140060800104681c1030010003180c0080c5800c020940d1039800b2040f19020802da8807400703e000c0348407801c0c0000c08201328061501c0c03078041d14040504080c000d0301d40803290389004054000d5001c00c0d2501100103106100e60324080c1201090b030415280e00074102804540d46124104200001c3c1800d00c40007584e1003080f5200c803584060340740851410503030090301c0c001e038055524010804c0801d000059180540c00b0301a03542c0028414881401c4200300d480d00c1341c5080e110303110002000c01c0039003e131420080074030071006040000c032454002c41d010b00c03811252090300c08541100000c040c050309854200441003407900c031b090286141d400c02100003441d6204010b0018001510383c41010701c01c030320030360102c030b401a00503009550b181120302d0b0620300c00010107001401c0080150105103642000452001c01001d482d10520005081c281d0039510124003c0c035800710100004040030050b00c0c0c00c5049030721040c0307850480502856030714000c2e084100c12114080503a00d0002004041e40e02c80305 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 943501573 1250 943500323 943500331
    0x103080417010f110d0501170601060521010627050f0d050109050706020a0507060f090306050a0f0e0c0102070803120105101101051f080309150d140a0506101106 71
    0x1041c4960000c105074140500707000c500400041e0318001c03800e00f0300c2c000c000080c410b40e0910b4a00708404c0e0303201d0882005c0d4254040802c82d460340302e9030050001d1801840101550901d0340c0f00e42501c0c980e4003010501e409004d804c0304002600c1200035205420f0041a21408140c14035075424280d0b0901d0041140401451a42403251100244610501000f1751101035016045010307604034607254a0081e58a00c0a0a0111064400c0359400540548601c030040d86900c0103940d018401445e60b2036503405000040d0441040300d030b841080b9501100944550040910b18001404069802c80c001900303042241d4400c14480d0801c00c0302c20008950340341c10605540049819081c44101904201d0355102280c4d0880e0b401d61030401802000b003503546030f40041d0180c0080c464003980e116004a0303224050002d8440d04039410091501c1c00e001450007810106104c032030300045070380307040d004041c14400548210441d1562481440b03101d003000c2e11800113070406030600486020034100003e5442d54020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 943502823 1250 943501573 943501589
    0x20a15090c06171b12091e150a05070905041b081f0e1e0a15450606081e010e0103081c14070e01030c050a030b0f0d0305041d01030804 59
    0x2011080c0a54a2000c0d146208000342d82c1c41854508401c4083d44c0d00480305903614042403140000010703007c0041d40c990b0001c0d2002e11481e064039074880f804003400300900344009201041101064a40b00c0b4420761010101c0800449440c95981c5005081c82c0c501510030002888045008901e200d00c541011040f00c84690320781916564514046890401800c04015541042414406240c4c007036003200d1045030341001c0040449944104c20341c030406102c84040d01480052458501c0c81d090142c0094004074441da912891011045410088070749980007000442c00110034841000d40420210040522801108109505080350f210210300c05100040c801400050008a000c80c0d080e50401405502030081c011002d01e407a850042e040200e50703400000d480d4040c0407200c0d40c401e02079444428103a81f5880e02d001e044480880180281440154005140036080411516070352851400c0310300079038071652282e0400030502c610501140d00540b20741c032070300d00503c08216a00110750031503100e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 943504073 1250 943502823 943502851
    0x912031518330f061e04080f0714010810050316080106090c140a03090c140f03060601091502070e014509060b210c04050f0103030f020a15090c0617 65
    0x2900284051151103561108211700c85011540009980041c0003030320051130560720f20314008082e0503a600c01c24404d034003c2120b00d015400301940503042158021441e1000924503544580100f45064441848018803541109040008881c00c1c40349102400d11804240000110250010480d100c20701c0010886c481c001002c070801c40c040d074013030358995a10003a2092107541c1c80081c1681c00000c030b16050b0188108000666040c5400b1680382e1040005031202040282400541804484450000c0b001e51144105c081043c40e68981094024a10306500300c1d070038881c5114992582080c4406402c1002403100360f220340c5403c070304c0448201d418035040054250900c0c00e2290203400f07200b0106400800300b036400710301480d20440c000e14400c0b021341110402c8a8041c144007c030347d41202d0001c10020304100500c002482102117018100c0c180c03044420f440c4041e02c3d501d4503070032600d2100d040b5075a280150070030040319080d03940c018007190800c204a081c1c002c8030307810865070050050f4144002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 943505323 1250 943504073 943504099
    0x10504050c04080a0302031206040c121e0f0903021903080415021611010e0a1805070201270b06060705030a120e0703080d14091203151833 61
    0x1c0402d0328002e0484400310b812140503401e000e51660310203504001000802000240c2604090084d514014510f41e5480900f110034072a41c40204510001d1160401c140b400d1031105101900a03120b4400f1940d5000445550615010b45802c1901000507807039041d2201344404a5044651503522079005291540b8882542024500a1190311a2000c080d80015068400c0c4a8164410300b2100001e0304c40d20004221041040707680d0b811882101c1c0c00c50814802030354509202d0304181c2d080780d441d00000c945044915110b1442820f0094a04011203841c5504001e00c80c040100542041d82607510318584206620381c16200e20651500c07109001600c4c10a45021078207600c03440100c1101e030240c0304419180c1c584010b0903446403160703804c140d041000b20400405455050b50041d0660070050003900c96078905409180c10013440c0300344a040d001d00b841e01544410500300c12844852001e000240f40024100c000058066600c0b090380500558000c07aa0760100c90700705044e00c0c101d803c0350304282c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 943506573 1250 943505323 943505341
    0x5121e13020a0f06030c03060b091c050c09161209120305070c0c0f0810020a0e0d060b100804030305071727100b011407030909020714011a010219080301050405 70
    0xd003e5122a0881064460000344a41d042c0d200b902103540c5503800303124065032801550224021514101d51003d41c020300700042c015000c000808451041c41515007070700354900052150801140c00b00c081c2140401070300006540148c2044190b03550000404c100ca603a030b2103000d01f001d884420f104c2810303540e0022520090090284490b09580000075008180c0c4030a1120100c0c06a44074403503441c81a5140400114403038020b455003a115682c0e0076519030003079020002c50740013840c029039005554a501d003803e901d030b1142016066800d6250010071f424546002412108018514000c000a40c0f81e0201030341215040f460b0404a102c0040d030001c5200c4681c000f0040c0d11041a46491084403421401814103030041071848900340c80380f1450900d5480d810245104580300180003c00b00c0c50144940c55441c0d000d42446801820b40c2407400c4807012940d402c42c2c100a003036540c04816105e4113200303980d0401090020001d00c01400504a88580c0c0e448100e01041c0182440369840e140012180f01c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 943507823 1250 943506573 943506589
    0x90312180c030a06020c070b0c280f060b10170604021c02031e06010f02191103030705070f050a0b040506071a1008011104120f0c08010c05121e1302 65
    0x1a20081c16107031862030f203284c241c0080d40040c1c00180c1e240140413000500342d4405094402240f90480500008110901d9848103640300007058030003042d0781038075400803078480c1000011080c03003044002400c03180002089008001086190b04001e400c840d4074401d0100d14100c20381052098030003507140c04401d05103502d281c02100300a5440303803010003003182e0000c51142c09101748549540030304081e169a001120091105228a8090f030f00200d100c8162881d42038480138000d018480c807160a2610000007401c40d031214406803a03170b40c0007d1003401a00403090040c80103181c2107407694409440c1803003494440c02107215039441600081494828801c3c9401104446440321440d0001d600d0218280040c0c1c03c05030183c2d07196076203404a111b104400241c2200d0a4503070301001e206a80c1400da48070008a44a00021a8480c02c00d00f400031310000c0034020003d040c14162a81078039051408a10311410f100101032034050101900d2290302d88a0303151003d900306220a80c3c9119102c80c0c2e002140c2a8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 943509073 1250 943507823 943507843
    0x6072a090e01090212030309210d0e010212061002070302010c06090821130b010312090b03090c0310051b0f1e0304060c1706010c061506050a0809031218 67
    0x31418900d20803804107040d401090050320132603a01100c2d80c0480c44583c1e0b40e0200f113a030b010701580000724400507004c00c2d0004180b000c1d99540c00d035150240b0312242e02d05607180d018810b2050b030b402060740e500341500078841691120080c2c6001c0504048110700940d5122070b448003905020301e02d2040028008250006188150008010b03a91481258000580722540c961075015400e41c84012031001d03c030511400d038440c1c1d0410707140c00040e4219280d014024a0702070040080c0110450300189940d00440079501c1020004041d0005501090505040c84c140018a907241c40c9850100110101150001010b0801e48060252101d4040180340601e104a00c00e4900c04050500c041018464600c01180300b0741c80b07800148031000005c1e6040d5119601000c410320710f030340c5103000034129504c01d44c0380718141d0b80140400b10360788070f9035611080702c1c52880d04403000144c00025030b4900315810049141e086441600110f181c40740c10307041d00320f00100240c0246452001c2c61031892903030300200b1240e040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 943510323 1250 943509073 943509089
    0x1e0622170d0e0c102106120305070209010609030827100e0f1801060f020718050402010905120703080906090d0b041b060c11121b0f12120304021903081806072a 70
    0x490307c40340c10098980d800043d0224411542c400001c541d051044a070b040c12280d000c0c1980b070a0010582040103218605825100c030b01c01d1603100781156640c0c0c080a403064510f543c80e64400701110200340b083c005800141d0078082c201a00d4004007820f01c50302894111019842c0490103883c900d40100c0c01c2c9003c0e903001c00c1c0d06084034860716014680580c082c901892003620340e0030070650b844080c0998896403004048039a0040c010410105201000604884030020b000d90702d007038191780012704520303900d403030988585202400308030401588038007040d00f40907101c080301031003440c001c0c001700140711102005069040000e01e541e010388581c15061141c1c00002c2c15100000c0001000360046848204c13107a00ca011348100903211410411801c0c00101c094001401e0403180507552403600f980060300880e003004140c034001d480c000c0c80040301e402540c03145001941d0344000c20008030b50503200517000e80c454002009480005605008103610303005559020b02c0100e40051110014030803681d2201c0c2c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 943511573 1250 943510323 943510349
    0x50705160210025502010e1c082101030b0103080a260a150b0f1c020703050310050103052206060801020c1e0622170d0e0c102106 57
    0x1461400140000786104006000362100c0096102604401c0c0311400031480038010890b010f10155200780c981c070354250390142980444d0b5441440c4100c0c0230450300d01c1955080c101188035801c0c1500500c0001542039000e810f040c16504545415801e81c006100060004500003400c050311030142c2d11115005511850090001d00140118090f041c001c650178803c2c14075109648030740102c1500e8000540c0c6145408a04180f04030642130f186500460759100e03240343d248024070b6030405900042031040c2c440d81d1135a48906014181d86092905504982c0c1403504020400a050105141010410008000c110400606800c20200600d01034000d00c0c07903540009190641d90740c000032111300071000c012403141c420004481050b207502d019240d1a519187c203d24001842451540ca4006c042c0a03455800c0e411b0f0384040350107440d600a212500d5000c0c1c880d5060026110140300702800708506907801c04403e824040d000741b00d02c81200402520340d090031401c8810b00f003103901c484040c101541e0011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 943512823 1250 943511573 943511623
    0xd09050105041202060a060303120c022a09010b07050604060504030e09091c03060806010b09130609060e061230040f141e060717030a0605030105070516021002 70
    0x1802c004111040f0b02502c240c901042c072540580c85034104598050303413205207042c520b0242c040646070003451002144108980d50000c0041d041803100c01d40c1311018101030050201c030034031040410590129603500000e005450210701c001c1800d981c001d6000d840012107540b03030329040e038548081c0c42d40700d40c01810f0f05040024290002443c40c00f10550200c0e010f105c4013070100210b042e513642c1d006800941d008000100709105c10207005e03040b070400040600d10070b090b20400f48000c44007154070001c54aa00d0302c9041000500200400d50040c1003130300e8039041c0f8075070301076410390f40d00d100c5086400403ca009000c009880c0c00102e801404d018003403e241d0380d00e0355404e10b00b402c000315000c0ea540c03014404c0c0d0119120b01c0c0054104950750780303a160b545003046200e41001059000400142c0d41204150059a00104074500451186403d03071000940d15050400b4142100c100600b2142400f4003045954091103848000b903100c2e070341c100d0303840d100c801404100701d0410349141915900782c500c012080e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 943514073 1250 943512823 943512833
    0xf0b060a0504140a080f0a150e0c0d02031c050d06140d02010c020f06161a070c03080423100606051c05180109080a02060c0304020109030308070918020a0801121101050d0905010504 79
    0x590021380a07480440780423010003010b001f212040601251203030300000001c10705040541040b030f00c0c0b0340020180e0b8480d00da50601c000c10403400c0aa81e0340015000140030a42d2495845484060000e443c02200800403400209202040f0914040c1c144913180d510380c03046541d00c03006980c10140241c01c2c0380c1c503441100034005480c4d40071442200c44284c0c4101161000d0000320107184a544075a4807220018a5602c1c140d5806501410039641c101100d60001c0103141a0b50746c070420b108141d0010302542001e00c0d00501101c43c01c0d0000740030440208000d405480310300c0f0303941c420112440c00000b86521100201d54080c000090140e144d5420804800140b145060180034001400d800395212507583d2003181d8a00d1100300d50003400b080d0230f10001d1001c02d1080e00d849d41c0c03222117421301b030800e1074031469000700c0740440702d000c5280c290b00081c1e0110520b038031032003c0340181510000040008801d9079a2403070340e08812682410410701181b854010041600b0000102360810000c202c141424200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 943515323 1250 943514073 943514083
    0x7030c120c0b070201170a020403060903090501121406130603060f14180a0f02040e060405071502160b2a0303070825032d0f0b060a0504140a080f 64
    0x20746180911900c00a03181a20750201d910f0340750305a442e8040440000784446403110007070f014081d0707954203000210000e0b007503105100d4031b14003940707135503c04e2031030b00780018000785d01280c0c0079000304c0c10714128062209440300240d4021804947c840d203041d2104220300006c081ca9840508072030b0610300022003114040c0d20107600310100015420300780da1007105148900889486420b0103611210420010564291646441c40d100810200e00c110840c0060341c075040056505072202d070400282003110005c0020a80d0030b80d8820f0018000500045403208a6210f0034030030f02c020765000190f4410449444078690f404000c0e900c0400500282100d0142c0c4d8035081211058081840b02001c43d1004690f804164042002c203018001d00f4515544100d000d84018500c49001da418056551000300001041c858110208500001c91400c2594880d060b80c02042d500e50040c81c0401c918110564050201e400307403950340940220b42a00ca4020508480203980314041d030b4040d079081d512583c14040340c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 943516573 1250 943515323 943515359
    0xf040f0f09031e0f1211191805090103080d020f0c0d1206141e10030e0105160801210606030506100f080a0b090316121e05030c090307030c 61
    0x1e541c8a00d61141980101a500e40764201c10101d40080d00013801c00b88200311415911009030f1000c0b40c140400b03210840300790000c00240707441002c09012000c105510040c80380c203103080e002090f8880c6280c0008981a04010701002d8054200001c5200c40d0f00100d40440700c0c10303841d500d0200e03540c40c8000c103040c0c0c860381c8a5120100040b0010107614950724903000798070030b96429038418424208120200280d800c2c0429812001c2118a91034809075940c85000e032443c100b0300e80713010840c40c8410071b03900d003101c00091200301c66500c91070301d400b50b15500072003440c1990a80041e08110500b03181001911486100000303107642e040c15030100800c40c021a9960140004040c1c40b18031030303112410301e8005001d60140b21125409a0744902c0031480b09034030180c2219999080e04c5c034000003004580408000100c0688070015070b141c9a501841c0d2120001d07243c0da00507000c54269054010004080c1d20000c3e001051a400100780c00c607285d80c05020030f00003154800c00d240300441d6521680301c3c59401d188 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 943517823 1250 943516573 943516577
    0x30a0506071d1f031b0513080102040e06240d0204150306050f1c0b04080a1202090a09091a040308311e0b070e1c0c050f040f0f0903 58
    0x2026040d0b584000714000340031004020700c12055610701140d940421518085000101900d903412450500910007803034840204a03910030359100b00e904420303088038000b50f1002e40260310412080080031510750103941c00400468684c0502c48029084a0303a0328000001c0001e040c000194001c4401b0181d0b005008560811900c542c041d807000c0030950840b400b43c800ca51304080040100300e0185441c440040d03440ba2210945410a80320b41c40e0b00c40c4042d4103c1d8211206c81c800504d15043c1c1c0c2c1c02480c0c4000e0341c18403010951a0030840d0022618108291103290203031030300c0b80544010894004490038108400740080d108a24082c00d00800784001611883e900250b859031070110826042102487e5590a000e1b2481c9400c50741c1e122900032402e2060206c00110b14003078440050080c0920300d005802d540e507001c4589001c030007040320741041c00c443c000c40b0704d6412004034000703409c640c048030859004890007940862a40041000b52851194a01d0b0040c0303002202c803007007071407980050241d500035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 943519073 1250 943517823 943517837
    0x6020f07120c020a08010e120a0917010f060b0301230409050105151207081509012913090b24181503010603051510171f060b070303020c010b030a050607 67
    0xb501c801741c22500042958070050300100f80f05206c05820000610424a2602c2d101c2c981e10303503500701d10f51900003200e65400c03140d4503002c100200c0509401000040c2c04403a4207203166516141089018200c0c12112544001c00140b171968242e40c0d076407140e00110381107002030005142c5414500e52081c100d06410f0710402c02500701d80c0749840000741c41800d46800ea80200034035405c040003241c0d0a140105200c4066480b080151070b200342d0096007100803103046501900e0001804104202c58410b00c1c03403141e00341d00e8141407502142c001c070500b94201d60707600c860842c0c5142c1c002402c140664403c0c6604e811600c0b500c6005401d84440280f80c0c800d288180003130b000b5100d180105426606a07100140050b8081c008581d0036441c80001103400c100078a1203501d41c01c0d60340c4280d024980920054040c240c004a03140001d445a001960450f180c0826040041c02d040481d08029400340000250401d5070100b200c4100d0682588140d02000c0020110f42e1a0b0699150282d51903408441c0c5100050302 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 943520323 1250 943519073 943519079
    0x18141906020d050a0218010804230609010b030c100302031905010f09140c04051e0d0804080c040e0304150507060e07150804170702060d1b0e06070b010306020f07120c020a 75
    0x645e100ba03031004907014545c0c0c41c80c284c3c86401142d0660019206540708850320049955a402c6e580c2c0281401c000701028108905d0550410742c2160b50030301e26503020381c014000307200075590f5010700071060038024100140c99440300c0e404c0303554040010040c0d0728254a00342c0081643c0841400c0541110355010f0305101e01c5801e600d103890520800e441c03c0700f00c280140300a000c2d0340f07080c49010340c0c11100503801d8050960701c0000510421101d40041e100200d000400f803000307110601107000b040c1000e55040c00204220800c0903a207104a1007484544071f0003064800600c1e2060741101c40241d0004024084107007504402515540103209103010b94050012500226000301d0050344200d811601e8250030010358a46550141d02001c022070b4080010042511102c01ca40f149800d004035004081d0548001c1c2403014091440c0440074031b10034001031141c01c001980c040341007415203074012000b51700e60300345640d030754030034026040010010184000c4a00c9240e85c4030403444a89402152a458000d503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 943521573 1250 943520323 943520341
    0x1510090f090209060d020304050f010f14010b07150e010b1f08060d0b1302040f09051608030c0c0f0a0803070303140c032505160b01090501060318141906020d05 70
    0x3c29210741540080701800300c0c2c600d89200f640a59400307070051003a40d00650104001c1402c503045074603056403140ea01c01000e074010b02c4400c0c98034098154945c9031072a241e01616502c02c420710180c000810a900d9040115160070702390000419480d0141800c0301805121070710054002840c1c4d050030000c2c04d90000600c951400d4841010381d42d411810801c50307600c07210300e0f42ca88102203034001d80c0c1164131a490500159260701c201d40e00d11b400b0310050002e410558221b4442403101e0f030700c80402c5034000e000005004401083c8960041d0040f61000110082900495140d80095010008074080440e4110a05070150006880b60b81b17000c0e00d80117141d8990798441120b00090300c40342200140901c910000c0d144540e240d024000b4103040c40b03410000c0f00e009400b01c1c113418400c21a840301c0f90344010404103016014950140c8014281800319003a4940c400e0120030782141e0240400c0c51190f1a81007080040c010400100c0e440001c1800d40c100b9410200045d43c40107900c81020351806000a80da11 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 943522823 1250 943521573 943521577
    0x60e07030b010903030305060303040308070516410a0308280c030305040204090209010f05012d051b010f0e0c09070503060613080601060c1509050c091510090f0902 72
    0x81c00507141c8002240c1035841c00c030006d01005000541502c03042002001240481c00500702151148009141302d250080580000c145140d020032a60009030061131a141e0008002181c5000c0c4060076092a4645c01010321b40c00503c0d41d6060b40050b01c1d510302200340403200c00180400b810a401c12500c0f41d12084140c0080c860038074800d40041c42625039140020310039000a50070500041006c622400c240d000110100c0c070030f031300918104c0e1580724100700650b00304e6101e100300520920b200c6005908241d403040001c1702d0410150400200041902c001c42c0354042c285c11003041440200b2805510b506440018840e00102c3c90392403046420028980c40c20701d400501c00d64050751542c0c210344400c410f000d21500540c0403a00c03141c08010000c140031104225a0b4001c1000e03a580e800228032604140850480c600d8a00d103200c0e003805013540104000040104881c40199605409659411400b202800503019000d5100c01c806240e0100790364400c00704015180a0310220011a9550103810124 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 943524073 1250 943522823 943522841
    0x1118040203071d0c0325031e150501080403410c1f2a17040b010b0304020604050315010303030c050a021b1801030b0411090127060b0d060e0703 63
    0x80f4050303c000407010820f030000b41d90400e280c0388041400480f04001c45201c2c880281111000981d9081f000b200c3c0000200405812a20180b00300208080c201666000c0700c1907014103410b20500c1c02c08074003010f01c00e0034200e0f89003c200300381e03420350002e0208929101c0100d003400d80d400d1181c0510a00071031110000c81c1d120881040051060b51508100301200c0f61400c6200217901daa44c200c1806a04880c8048611120207072600002c858469503001c1c049609081e06010b0303408414080000049008417840d065074144401c0c00e0303c1c3d46d2280300250140c440ea4100390741600900075842c890b181810170241c180c9110340c07000c3c8480e030104001181d850141604510040c0d000074161a5078101c1c1c0803400c058841c01900b011185506405000d0083e54281e00c2250300080da001040103001d82503841c0301c00c80e0002c0f02c4101c0304e549400b0f803031000da602100c100380c1c89011007203120b88004242c2d4860401403031904042a10340d1a8a10094000c0c4610b11035200c6140040c000508114420b03c110100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 943525179 1106 943524073 943524119
    0x3010e0f010509010b0d06051302041a150903071206020708030106020304060f020303070c140a06180c080c0913050c130903030c0e1507111804020307 66
    0x841c2c10081c0426000e0b450801188029910b2282c5484920780103003001c41c3c41c0e15a500c01e52904950180000e43c4280b8200b84051144000460110400030883d580c03050010030401307500d02c1d0704c01c03141d000b6459081400c0c20300c00d0b500401d8241d20054040c080042c14050a40c2d118030255100303800c02c9016900200e0104841c1d40d10103114000c04103244055030171030602c41e1000d440002c00b1280100341002090081c11210003c000302003186810074000d02481c0e0200c400c2003c02088004d0a0302d03c1030560101003010b0310000342d110102000548000c51b0f80d44c420880e640b894120b440304607540d01511352040d0300d030380d90001500801e0020110008075191a40f901604503101d1040080601100840c500307480d695512581040b160654101e030341d148181c0c07900000b202000d0f190140c1c0503e0342051000c200b40902441803049200350b0849913100d0310303005150208641d040080c81 = true := by decide +kernel

theorem cover : BRFrame.Cov 943345323 943525179 := by
  have h0 := BRFrame.cov_init 943345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 943345323 ≤ n) (h2 : n < 943525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
