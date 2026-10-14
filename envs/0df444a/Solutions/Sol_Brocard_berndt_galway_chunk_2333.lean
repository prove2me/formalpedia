-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2333
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:23:42.657019+00:00
-- url     : https://prove2.me/submissions/fe64ae12-6ce8-43d3-9009-d41dd53530da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 419424460 ≤ n < 419604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 419425710 1250 419424460 419424463
    0xb0f040c17030a170105060a030e01020d15050a0801020f0415140304110f03010e120906040b0a0206040615121e1b0f0e0105150705070305010501090c02010b01020105090c040f0b03 79
    0x101c200081500654032408000b0000d00f9244c00e480083c24000c0005004201940d82c580883e0344c000d03a03500c0c011501c000d03003a81a5000e80140001d01c0d1800341404034000c4002d000c05049400c442049170720b010f04e580e440203244c1c200c1c421030003890320400c000c120600184c444c0c081c0f00141a4654642000c180510075211207060300143c41c00c071400d4030329400000c0c03507107000990210350200842c020000082d48010156950925924414400c407020515440b02c3da40d10741a14000d0407180c0c84665034414130386000b9141c507402c81d4222030036440d041064250300e04c1c4c52940419610404024035241b0740769200d804040c42c03810740044005229034062000500c07503400c4161080050600001d134503040c40d00c00c5559403280c1d0494041300081e8401005171355600480c0519003a15180e0b21681c1e4021400c01e40e0500d411500050220760a040000582031110b604c03481c1e441600b0350003041101c1d00701004900340c2d03d0990f2001c0c1c150703003d00c0e080d00031450141d21404185249010000f030041d112008203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 419426960 1250 419425710 419425739
    0x9050607080408010b010f0801060e0f0a03050f06010b0708090d06021c0e0c09090c0d08040b03070903020a0e060a0320030f0d09210312060335070b0f040c 68
    0x100c80c5080d01103003c00c5202c109000d81c845a100909200c0f02c60b10554000034104001481200200304100407500700b40d0301c685075415921140503200400041d1682009a50b4050000402c80184910000020480c44107400d5031040c550100c03650346081c0202d01001008407120200f0f864081c0d00300154440c00044400c1085d0104920700302140b01800c0d904000d050851094905000c0e0200c2002c00200000100b403100e0a00f0381140c5840542c2c1c45802e0034680d5001d260000d1001081c00814480c2062300070203003c049034800c80310180e1150b00d0341282048024183d414540007017203e80c0501c0003036076408000821120300586917200b01001c000107445c090a8040b048040d401415910001c0e560002e0440e0140c0301d1514000e518038559140f00c0030000400348043c08100f2901c1c0c00641e1210140c12848c0203681001c40c09108588903440001c40702e002030112007161609140c2d1040204204080d02c2445070881c00050003503651080c002011400103204035894220301c0c10100d010750440296 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 419428210 1250 419426960 419426963
    0x6020d1b0f0c17061602010b0609040c050403050d02100f02090108060907050c030a0801030203010b18220602191e0f051305150c0709090c03030c0c08060c070204060e040b01051009050607 82
    0x3850a420302c150144001700c1c0c0b4969000859042c0030000b0300c59100e00c03044034130f400d1090318001403905403c4e070211800d00850308010b04e54080c01d505100d010340c1c000741c3c43d000c1c400f011b00100070301ca00c4034010000301c0c82508641d50220f08041c00023a62490180441e40e8802080c1c20f0540c0b03040b9640d00395030704542c041a000c8000c20025801402541001d100d480c00c040e20540d06002043d004818032200d681005040038041f0500280010041e141414200d9003da0322640641d11501c0d034162911000b5103116a00c03001030011101c0b5000d109542c80074205861594030b4420902e18001011181580804142d120306141c03c04000b42944460407403201c3e0452040706952506480f074441401c01592f0fa10440305e503800d203481c107004210401c0403502121b80c18104000a5901c41ca040040404d00d9400043c10f1f000303d1342002125078651000309610b5208840c20401c0c80d468840000090500f0b07607026002568040c0140510704010010301c4016225061040f80c159440d00096141c2d40072820 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 419429460 1250 419428210 419428213
    0xb040f060305060117030909090312010e1504051501051602090a0b090a1506030c02011506111e10020705030705120d0606030507080a0221040c06020d1b0f0c17 70
    0x20000d0040520100e80545420032407504c07031740311500c41c2c16980c0c020365030403d11a0081d840416610710f020803ca07001058085a1000c0701d6a690100035000c00045540660300d0102c92000001480c062040c030b84100701070560498020320007001105c65407c4001e481092400121103040540e8807134541c030f807241c09000070204100e0910003e11107100e03c01341030b450300107082c00180c025141c441466082920300c1854001554000303014220302402c1540d00c0c1480c0f000d54000c02041150b4002a200f81400d0580d007100d151084810b03d0fa10440309851005044e60008a2102d003251055001070601c14010011079081c00e2554a9440c20310a02c0300054125880c0064201d100c80c0050003100001c001604080041d841c1c03d040c06081200d00804511000342d00117100c0118410213401a0301c841251036007802945090300d0700500e5510280151009231140015140640340300384403d02d2026000b5800b004403105c0c0c4c3ea120200407241d8042221100e41420002c51510690244850108030010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 419430710 1250 419429460 419429471
    0x1305180f010b03072c13060516020d020c0a121406150f010806011209020310060603150f0f09020310240807081b071109070c050f0705130c030b040f 65
    0x10b04061800a0302d80c0074508241400c101d104d1489070700340c111107103084611540e950070750b02c080000b01d401807000c00c0104420300d450144426080d58540000b90308019400303c1b0301d980c0480100341c7e030740c55110030b0381a4081780a1303500f402550418600042c00c80d02c070f0200c00b9440d01008e0352003401c001d0102c50400c00041145960101850030003108402880c2c2800c0048650404100080070340b0a5000b1032000d01c0d8403411a60119107081107411014502c0d20802c20640d911108010050302c1c550707500e0082032001c0c91000c07031460700c80d038075020448240a06880c42c0c00c0c606862540650030050444082007030030b01d400500c2900d1241d455100c00108071300606035155044020782820800f80209040180d80810841c81d104078510341d02050200d00d09240d2203684a00d003c60803542404100d5400054003c180f00840c0d80160310500350342d100d003040c0c0d06010108645603644030180e00c5059132209101e00001091000c03a0303c0140307034901781d18001c20300c145080040b4060b29403408072002190f0303550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 419431960 1250 419430710 419430731
    0x111b0109120839070f0606090f1103070203040e0c0c120903010f060503060604150503030a050310120302060f06010c1407180b0a0314240a0c020c1305180f01 69
    0x40d0f14070501800224204041051040110074010b01d990314240d81501d00000e465040c40181002010201d82c0a44188945034440d0f00800180010381c409025450800c6003240c06480c514040c2c0744100d03e0340d8000c508081c079202022603020405041d90844c084100101d4003280303014050722168213002000503544100c840281403c40e61200c50020700c6a00d0b0400c10702c03041e0b40101d6907540110044401143ca444919240e000b41903c40d4060b507810b100018080300c000d60808040c2d44a884890400e0b9500c954842c0d0002c6901c510074030040040e0407482c00a04029603440382140c00c6403040c5488005002e00d0ba981000f80700c070110103a207807580300070010000c4100540b20000c156021460034407843c00500041040000c5a010050040d25545c26000e8004810441c0d03d0142000f138050b624800b0b8110078038080900c080c0c58001b03200e4100f81028003454000100b941405602409403400c00458108810003890041c044050110010240c80001132041207103441440602d0700009488a02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 419433210 1250 419431960 419431981
    0xc030301060302030f0a020702011d04022104020f01050304030807210c0c060e0f060105090406180f06111216020106150201060f0f05060301090b010507171804111b01091208 76
    0x3400d06201b0380c01004400b00507648405a80d8591601c1044e600c2450fa003100042c0c00f80c0994000c10b0320090550000d00781c41c80701551101c0c00b0b14001d0740e4030942055a400111900d2000b114080c0105d46004085000c00707208444c44a840c00050b400c00154141e802c6040054a604c0b41aa500042c000c11145040c481e25205850901d86005c005005000380141c80a03141d00c3c0c1440b5861146000c0d0b80001c081c0026a00258103840c0c50b00e20b088070b00701080c0b516003103070000c401d01500d04600c0c0c070102c0b046021400017202e40819104c141500659144140000c1000142ca5908115500c0703c90004002c00244098130a20050f81c001088041c00d0040c007104595803503101d101c2e9104048410815a01c0d054112419030708900d002140d10208640103840d0b6104100d8002c041c003410074403040c41010030002900c02c1700b403d56a1146904c0400c0100025100c88a111000c1c1d84001c11114540042009c0d1140c0542c0c1c1080c0082010901611821020502c950012000c942e0803001c1281c000032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 419434460 1250 419433210 419433241
    0x1e12061203080c1602091806160207080705060301090b03120f0909060301061a07060902030a0b0a0507020f070918080f0c06070f0c0201030c0216090209010201110c0a030c080c03030106030203 84
    0x1c0410f424244602d21900c554400c1d00280c1c0a0f01070141600410b295a0781654000284a640821101141006821030f07501503404480a40103005151010503603400101c1c01d13404aa41c0103142c2e50450b405d11107010028542c0810442d0b1500c900717240c00f4200d0307004d1070140807003060011405444081040a00410090052855103c0e91410710140544207061801c00c04004009250035103c642e00e05d04140100000755000c0c1d414441c80000c501000016a1300d07a201d00d1040409000544506405a80d507203026440b01640d50030100041c00926010b03485021904001c2041b0410b4240c01e484901a640c040400c00e0500d00e800241d00224840400001c0d400c41160b24151841c1551104c000704803620b80c031030090415445810114039280300b0016804208038150f5980c0219030f8845c0800000d40c804141103025500707003020a041082e0090070b45a20384282c1025000c60091130340c0444591204500031102150240300d20901c2442c2000990b001e46100d440060f541d09243c500002020f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 419435710 1250 419434460 419434471
    0xc06050309101b0302070203070801060902090406142d0604080a031704080301091e0c120e12040e0907170f060109090809040906020d09110f060a1e1206120308 70
    0x3401c08203452010803e0340300106070b032900c1e403a0040c0c0b03504407440000d0425049500c110b0b940e40c02d02002298800c40f960050a0300e4a0071141040010f40d40c01c2a42c441c0c1c140071088942c07100404103001e140072218964862044881c54240120020010000b040f03500150825821a80076440440400d5042414800c140000d2143c0c28814035050307030303a034089110501600100c103450ba40b003c0320f006c00000c1803e1104d030313820005001c03404030b0341c03401803a42d010b203018005450f05000c43d5801d07201e004918111860601100c8504d09400c1440c03c540c1960b001d0020a607911a8076000220171000c03c84500c91aa50040900300c101c2100003020302e40401a0026480d892a00c00000e0005061500700c03001502c003a42c011450500c02d0420384020300840032a56007440c1440c14030810000c1070300c0414030b500000c90f43c2e45001e540f00800d00200d400b65643c3e600119000b0040c00c00c2211390600601c5072141c3c0e038500801c0460448160f074042d20b00c2940804802c001c1220140308064002c400c0c10f030b100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 419436960 1250 419435710 419435743
    0x12180c051e0d080d1e0f060e070c0206090a0b0705030a090602190209041a100501080c0c0607141303030f020105071106010902160f080406020d091215090c06050309 72
    0x4407010800540c1030421401d0043c041d4100151034480210140c0200020802c500c6200c0d1001c41d028003080f01070600c4c1d182411700c6528103c1d000c5586d0030301c00360381030042c42c1d141d80c1c1e000902c500f40c1c244662075204440d1564000000600020702c4098030000b02141c92181018540360400c51102605416031038102d10217641003195103040a00f482000c201001d07030120f13007105454445042095100101c1142600440c0310380041000381c40200300c2c0d500480e03c083e07036641200e5a602c0c103401d21b01c1c050010140b8a039000342d00403503600781c441c1d0f10320b884007034030300006c1071812145441050090100750b00032400300c0c0a070242c00380308540a00c602c42e070210160910000b1000c501030300070b4039000140554500c2c0da44c0498000205151091007580441d44142ca203440460242840c0a0a8025100721310051090540e41c80781113102d0341e40c54003100c42c9040483c2100d000760703035290401c12594072103041e0b5507503551400f004a807400310414014140b030b89a0035564280406c445050214010100c2c115 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 419438210 1250 419436960 419437009
    0x18060301320102030712051c0c14090d02101e0207140d02031c05090a1e1a070b06010302070f03080403110307050304140402090603100e010504060303050a12180c05 72
    0x7941d0300403088130790f015840003844c40210202e05080d9241d00420070720010703e401c00b100f01141b200d00c41d4400030003200b00d038840105813000340000c0c00c0584100f0034625004501414020018109040ca4040b40d150505080e10f51204042c0030a45440c8006080001039101190400001c8030941440c054400b0584580a4041030754000c21b03034603440340510580312050f1084110b181e030b01c120150340e4010001491032003c070340e46a8000301d0746001ca8a37410340890445500103003ca90800700041000402e00b0810b00703180c080c1c2c40d1007030001c00c003c006505142d002c0140c40000303280d10307480504d8284070f515130250300e0600f0f040092240d000054103840d280d20400812011900000680c0d003200c6010311600c1f1811824804600a4040c2071080c94000b42c0100c00d00c12803008002491040e1220300d164034107641c2c0e0700d20400c41980d48900c4003501180c002c01c4401c3d07000d88182c8206400850118001c5007000e20680355104183d9642c400780d96501702c1030028030443c80d01e550f06006030440038038110075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 419439460 1250 419438210 419438309
    0xa0602041e0803070f02010e0a0602150f0403120c0c060608010c0f0e032d1e0606030703020f0607030e03061503010b030304060f080901090812160c0305090618060301 73
    0x5aa01c1340c843c0150070b0982030788450f01168400c0d013505882400152685154954a81010303583e86540c8c10b8205007204024009420395880e40d00b820300c16505580c51446440540400500402444040d0010068652412408150580101402480e854000041d0b0f41d43d0544000c0c800402d0882038802c004540b94060210b130383c001414254107024910305000095500c005114044010502459a01403031200d41c001003640b000c00d4411542400a4070816514a400c0549600081c00025484007a102c0300a01c941030103805040403500c2403c02c0c0c403080d84003030002407030704104480d21110542d000c6c100030801e00302030040004110b0123030000d41c245820070700080d0414401041200c100a4114001000300328250000d840345030b0070600d05940c6001001c0b890702c03590b208640d1080c0c050060f4010307a2040d0f22840142c144182c05540311802c0401801c10800503a00c82d07840280c0305044646c15013101c0e075503200114000c1c4030016035000d484046000100032840700c8925100c80d400d20501500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 419440710 1250 419439460 419439463
    0x50f0405041503140a15020901020c1203030603070f0e0a0519150807050d080403060b060d020c06070e120616091a0306010314090a020d0204020412030c1502040b07140a050a0602041e08 81
    0x106c0c0c007070311040140e03c07140f01e0030041b490000c0009415a1008100030700344000354020008500410095055801240c0c4402e0442c406202e18851850b09580c01c000042003001c050740600c0c1c005080401954180600481032000e803410b8a100725000700b4406410020450204141c0d4002d100c1502c07a10780e000d480751540090380c090751201400942d00c90031404503603600d117011110500c442c000110f489617584c00c1d0066550348220b82000200b24451481e416070700e08140442810f0000000a00d03c0303964500002901e14000c0c1c8000003440b40c00200461410054546403201c24001d031040c50f01c91618500040c1036480e0011800c15142c109000d02043c580d0120780310f48403540640d141c40072a421480824000d01c02c0e580b000c01c0c4882011210f0040561104000b004a401401c0543c1d401001c000240206d11441c4281c01c0403c0c010800f010010303a080240640c001070a03420b42d90300880036140e1900b0701001300e1040350610307400034003401122500303410740d5083d4001c540440407407070a220b00c03103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 419441960 1250 419440710 419440733
    0x150c0908190f080c01050402040515030a1101020708011e0f110a03110f0703080a05070206150118031205130e06011725021b090603060403050f0405041503140a 70
    0x4039070407003400a90105102c2c1d4554281c21255119054559442c0001c0181d4000c080030b480803403199041c4004240e44c03d43d4241c03800001d00c03000300509103071402e9907515401005c1c13119455065006120000891100a02c01c0f44403d10304804008850b50030240603404540a481d010ad4400c0d00d444d203104114000c031410741c0c501100ca810009628000a642c2440d64000e8400442701c040300010701c6c004042c0c3c0400254011166000244403a8031560310607030700c40008403910340400102d641a4030f07503503100e040b2901c6d00a060303200d800522500c903200d510780001001041c2000c2200045e02c0e5100101d040c200c2d20003059800a049600d05119000074002020025120780c0c900b40040070600c2c4151203030548000620160000081100020b00070b52540707000c5814903070b1154002e25900c4035040c00c2c3e185510610340140501030301c1d6038981c0c064559402903500010f28040c00e02011520303844600c190032602d1406404040c949142d850324418082c021013820340a034101d41c054100155208101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 419443210 1250 419441960 419441983
    0x30c030f050415030b01081029070209040515070906200309041410090225210507140d090302210a080706060506030403050322050a150c0908 62
    0x105035035000e0000212681c2c0125002142c4001d54504120b2040c0e4050780b1800a040d800c1e00d90f061560344021110035814071501c00c078100c140d0411503001070552416400c10310741c0c504100160410342c031a00030658110003110300712000d03482503070f0740c01e106103452881c1640564945000c4a1a5050420003092125400d401c440b031031500c0c10000c2c40030702d024800c0d0f8603082c802410400061030f092100180c5501c0695043c4080180c1340c1010076485090b000312800740d006903c5c00524030002ca0604c442c40c0b01400020307900d228007003c80c091501c1b0748007070180008040f03075111a00ca08440c1007040c0040750710516440641e0060f010107142c241c1000c44882180d030115040c3e40000110f007031109000114002c0d4004500034078550104201004024002640c0208001c100c95603c3d0410710040344015540030b004250280001074059084003e0440c00408101e111212000143e44507403400340c008001300d602680e000d0310181006802d00c210b680401246c542800b02d20300e07003100940c070380112421 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 419444460 1250 419443210 419443217
    0x1060b031e04030c050102130e0105151204031e080106030c050703021f1104081f0902091302150a080f070206011503051005210f0c090112051203090d02010605030a030c03 75
    0xc05150044040c8404d41d90090000d558500090102c0200c40c1d00901582c2e0281840c200003040500380344807400c001000c900b08a51400b8440030501e5035000b0018400c400300030b000c07080c060710b070f06404242200000d0741303445162981d418064003406544e040c015090820806004510100e42e001480c07128094100204613246100e0440110140074540303031341004010b00050000c0d016500140c100420741001d60f00d0200c10b110140d895041e1601c00e4000303580101008046148058608010a0b00601c01000c030b030b101d01102448010640c0006461501003a000c000700039440203000c081e41e90141c02c500c0581255810b01d40d4010001c00c18140c0e40d8105681d90000803ca4078841002c1e0014000007040c6030580b50758540c0f141540891001d1040f098045c03100746202d003441c00900081c3c403900080c500000350782400500074400007c008143e07543e2041c25007200d40142000c006600907210749029040d540003041c030280c20340344c050748001d001394090301c003c00220b50b1100680c10f070642d0624 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 419445710 1250 419444460 419444521
    0x809090718080f06090f03030609071206030c031a1014060c0111070507060f09030326070e191508060102122a0f070303030b030102041d060301060b03 66
    0x104540d9080e054407200780400c1e500074003084025000072898012040c802c101d0704555140040c45840300c001d0320504050764014170228000740b821100c290390101c142d14103170048201c9012840c0998849e07900541e0500e10603081401030002c41c8007001107a9240100c0c1d81101e06045540b001d0403540f40c8154461120b0211081c40c41d0f0703440d0401c0f20202c0b02c0e21402801000801107070a0341c00d6000312421629841900350000d00e540c020350482d580e41c66161541c6a00c1c0e4a141c81c144c0301c000b1089860000c907195100760542c902c81111201e409040141e8611540d0003018083c46820311b440340402c3c01300041c00404210704851004620314146d11032a02810030b440e40b0300180d1030058615072281c01018041407054600a081102c1a0000d21200403d103095080207041034880c0d60f41c20307450b9046d4011450510109000750007002154002400051403e580d55562150307902c24503803e6601d20420303009100c1285001d014210203404295001d40c694100400380340c0d00721145840002c101d10425 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 419446960 1250 419445710 419445721
    0x6040b04110309010b0118080601150306080f0c1c0206090609060405060d02070507120809150f04090608010609020f120703090602071a01150504030b1503120c19080909 74
    0x941004111000d103003807103500c1e070a200c0c810300c3c040c00b00d64881170700044d000c088203030000150316042000c465140d0050310040e400c001a0519030282d184002051607100e040014080d0030410400900161400290ac0d042c14010200030740702017007240001015148009040140e51800e0841e1031520707044848070fa071120080e02140340c0c1e000b190300495001c03101003005d4598040d26001820402d01c04c0d0305803200e15856145080c0101020744018101040031720030100c4604140d14800e0201181c41281c60800c1a043d50341c943c10360003500078049864640d4002c01c0702440074010900030b070030742807001d5040044202004419000c0c810340a0083c00c4150082000980298010540c0c3c0f6000401555a05a031f03042202c0030001c040c05044004c24600c0c00000c0b01d6140016000c54150195502407600c3c1c41d5840d880806213010f004110403451018555019560401c40b40044c0003854525948418982220500b08580000507880c805a0701003d2000140c0610441d11f00800440d0038030030340e0301c45 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 419448210 1250 419446960 419446969
    0x504150b0702120a0c0e0c0a12020309490e1003060506040608060f0d0209180f070f030b0108010c05070f110d0606080f0f03160f0b070918090201020606040b 69
    0x7051169041401100114030a00c1703001802082500c0011014155a4035000081c44140c0302e00c10031080000c1d060300740007483c980240c001b590400030600803507031500c02030681982c07104d110403a82070140d00d06048840740440e45c083d150101c0098450841445000400040c15100148144500c80c001c0c2504030b000d1315000750303c01005094040c150684a544680020707040b0041071307900f0352003441c101304003000038900f202248a000d0760240515000f0b8071003035104003a00f59150320344000c40c02485560201803d01300031500042154800f09512189103007004a04010103802c80c117202e03414030380b94800041d04182100c00c0550b000321000c520b00501e0070180f180b0752a8084059004018410100602000e604280103031464401500c1c0b412000102d402d9899008282c00c0249400c180245c22501c1d2844003505002030282c209600304040b9590f8a8803061802c80381c2201180c14110284400d82001310001d1200640c060104280040358001035620400148035910441e101c0d030415546449 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 419449460 1250 419448210 419448229
    0x3070f031422140105040c09051b0f040302040e150108060c0906031503100605041107030e1e0315150a0302130b030705060d020c0c01030204120602030603120d090506010504150b0702 80
    0x810034001c141d03c0100f811441e01070070055a0949480c03160040101d07294065200b85405103000e8468544440d014044c008802d070020039035884904014003001026848900910014400d01e1000c2d00c40b5a11024406c1c00001e010380000070f040c3d114408010f2400c00c800200da0702c8a4040301d07225181c2d6240c40d00c848440500aa445805025060b400c116590741074000c60300b5190115424041103032036103400d1074180203960000d00001c6100442c4256414121002c1040e190b010850703d150044042c0030038038040880004d40e90b03c0c8052030070048403580c441d070001c41d00b000c12210040b1a51540d00050030340c20400c034413164003559991010300d8030b070750400c1071000910b03025280a40b00c4240004043c0290040c0703016a04500803070840b801c0940c46031088509460703010010080544180d1a07400094100a100a425209005201440c02c11003c060a201d04124101194aa5040c500b450904106a0250b03004600f091004202415142c0084065801600e10381d52120094000a2003009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 419450710 1250 419449460 419449463
    0xd0506031c0e010201050c09010e061c060b0c1c0c3302040e010510021903030b0406090203011404091e0f0803040c0806010605040e0609070c050607020303070f031422 73
    0x300d500303403402030141d00036642c2e28034064260000c1085a464036130304410351003408951400200707030700a074020700d1400401900d0841c12140d0b0034a850825501d1000c11640a80c001c0c001c112004110a2a00c4800700040c100908007180031401c1c602d800702015001a1000c5030081a48a081001c1c4800c00c05003604900500207080490f0401003180003581e0096001d4003a414156810000218150500110080d8021600ea00401c401c010088072110607501c4600100e04140c3c4404440d886583c1e0707800b41c2400380a55100060356540362040c4d51580c0b0b480c9004250040f410121a440030910141c2840c500c010034001920081106140145500402070380c003c5c81c05902106120500c103401e152401510300c0c076011100d060345c803545c054480e03020b944140d07007000306039a0003d507407030814903465034000b80350341042410f400440c4c1e0b429081c1441226824010b0740301100f00720319643d01a411603000201820304002503d00100301c0000548000c00010640080b078441c42c12022141000580c4503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 419451960 1250 419450710 419450743
    0x1203040c0f05090105042f270a0b0708040b0316030e0a0b010e07050409110a080105090c0414130c0f08070513260d02161a271819110d050603 62
    0x1010b80b00394100c0c7c2030300403c60020200c41e07811881210f540010f00904c1c901c00005000c07402d1540b41440782400340d4420503086034140010b00000803080300c0b11000e0350080003100c0500b50104050840182101c81d2000030540d150b000d500fa0b900482c405009103419144002c03480c903010b642e1100165081d110300da1080171003903e071111a81c3c1484407900a05920384844c0d482d1003d90340d807071080014041007034400c0c2902d084104000c0081c48680a040048424040d00e03070711076a000c105c807078130480342101c8040000c18510344e41c0001107a481000d09601004905241c0c0c00c00c2440d00c0e10707444020007809041000c0d00b454443e00d084461100040700419a0307103007180c0d400b900e1403000039214600010005000800454081000b4104101920041c2840d41c509810101040740e00317210964101d01d91855105404244406503c810010004080c03e502400f110350802e80c80b144030100341d10b0903030701009107408902c01c0117051220031251b03038040440001c9070b03035199440003030f042440c0d4402c030b000d59 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 419453210 1250 419451960 419452031
    0x1b06022425090b0a120c020609100b011403071e0305090c0405090a0803041b0b03160f180b2208060105061c1506030c0806030c120a051203040c0f0509010504 69
    0x3451751100f0f0400c0c0107196920140003c3c426078505907500d40301a20000c1c8550400d00300d464598a05600120003080140350040700102048142503031940161140c50008060303045000341e071840d5006400c6d4201b007501d0200024a05840590741381d04000b503089110720745940c040b42c0a036004021181040380c0140d8120707602e003000d00c0c11840d452414480c0340e09070300000030001503100014099030301c101001e40c8c103840d0564602104aa02c0321107a8510320070b00800d03034601c1c920080f1103521500509a01c14a942d41c0b40308600705c2202c21048154000070740ca801c800305000110b00820041e0444500f80d464540392003a07040c5410042c1d174848100424103142032803900c0040a00c40343c0c90b0446029450030008400b1100048410000031124543c141d4451464901e06c1c0c20855070f042d078404406400d032202241c00f65241070500b071002d1003407440b50f28084240402d208910140b400148901034400f01c20300d141c40c2c0407a00580052260071f210360344d14503402c258111a41d004030f40980004030b19204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 419454460 1250 419453210 419453227
    0x1d0604060c0317070909021b01110c0c0306060637020a02040506040b030703021201021312020a240f03060302090907140406030305090d1b06022425090b 67
    0x304011403405400042d000383c140c00003403030342d040e905000b441030343d0311700504038203100416000c2c1d400800040e21446440844441c2e0947c00e00c1001010340c01c04030300965400040203813614000d00701d6040f91003038006c0c10900c10700c1d540d1001180e01c250140c040305441070440e40f84106000101400c10103a40ca02c10082c08445640814400300b583d00c203da0802803519414203100440e00f00203049501a444030740107001514186001c0d68441444000162900c1d810290740740740c14499902a05d400e54411400e0021880c2264814006d00800c42011000c00c6900300c05118810000c0001c506212502c02d20400e154400c2d04140041e40e000f51203a00340e410160921562410540304000341034039034907a45030003071900d030180a046a802d030f0b44050070400e4840822255520046003110fc640910400c000e40d8100c881c243c0f8014000c1d0f4024141c01d1701100001d910000c0741e04903556600010780e0820440499440603000346e00e1010030072102c88000c2c09025100a01190082500c044020818a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 419455710 1250 419454460 419454467
    0x106050303031008010c0e030a030e03071e0504050f091e33070519050310080a150e032b060e092b020d1d0a0905090c0d0308071d060406 60
    0x1404c80f08040000c201c0e59942060884100806584003a495041440f807072010a03c50044004261002001c0d15145566440450441c84100c4003c04105181000c01c2159260610806510030320401448210b450288142d03502c5010840900303070f14051403008842160010060309030184201c28011004003260907d0b22808a0b000f080419080c0d091000a00740c1031054056903144110810702c00c0c40c00001140944e880e070001003181d0411001540c00013954042000380c05840350080146a06c0c02458811010076210040402d02d45513004000d40c01c07610384081088046000d52035011440620101548000303080d45601021185240e0414890603000c00704420004e900c04034400c210110580383c80001c550070a06071400560041200404c407540149003829080f5482c000000c43c0900c1e80c40050320101c0710b80c203c04149aa101c040140542d81002145020001181c0f00c8014425a42d0001c0200f4001003030101048030025080310800c00d1594060784201009124540703950700c600c40107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 419456960 1250 419455710 419455741
    0xa0305010e07090b0417010e070e07080c0715020f070506091e010e060a05330f12062205011107170a08010b0a0e130608010c2d02010605030303 63
    0x1c00841ca65804529103601400d096422140e400d030625007810302d80854402c0308001120702c84415501c42d8045c80801d4070070301c80c450280c000f20240c0b45603814003600042c1441c5d0010180071081c0d40400c00800400c4044c00705503441500c030703000583c0d506d540348649056400b61550043c064890a000e2180d08140410350031a5a1148220666900000b01940e03082c0e5501d004000d54a4010601255039080141c02441c2e20400c1100300a00f03411044c0c00d403540c5408039050380c40c9000d100c02c183c000603140a0b00c8420752140c0c120b90880c80f414200100907101c1c0c00242550300e40649111098080c1d0000b0134201c0786164100c0e00810503814a582104040d070301c090030031521580541d02408440c00164140c0300c01c2441640d5100301a824814042c403140e0001c4100d00c00d0002d0050031034280c0d0344240c510600e1000203240401c445103040d2045080d5503e101043c1705010140c0e10341c5500e10101003a45400a5042141c0301549400c2d181c10703401000107400080c9c05000000811100c1504a00712 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 419458210 1250 419456960 419456969
    0x910030302010b06132303030d020405010f09060e1e030f01020702040c03061211031c031d07060c08030a06030f050a0b011a03040807031206080a02030105160c08030901060b0a030501 80
    0x3488680c0303c120802c1560310131018018a00318089506004400000c2040e5100440b4000201808071229000a00d96003242400480c1e20303400140c00c0c002541d02040c105180c0d207940c101036410a0400b54050008580380b08890301401081091800025481c03501481503d001f41c00e803100000c6a039201800b0703600c524800c0c4d0040c0e00348003d25280038420701c5444200c1c1d00e9007400041c4c541e00390756a070400590342d0b0340c8903526104131a40031044207280382510f480d03480076807400550302d0010480c00c82401c4200404480d1030b041040208401c903007040700d80262907484501c3c96a00e6458208a000411054201400c4501e800322200200a000200440400d000300034102c60303683d8a40400282c1d401c21303c3c0200031380d641800458005010388001d00090703482800c0840042481c00d5418040302c14551141d42c1030f0344003007204401c0d42000c0c810aa0864205c82c0207844107101000050715442d42c40c3d0700140742100000014034800c1003075200c007010f0b00703c03124090b83d11441f891009002e40703028001d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 419459460 1250 419458210 419458213
    0x6030c34030818030306131103070c0506060108040503040501180308040801141f210506040c0513020f040b07050a05060708040b010909020f09061503010f030506180a08090f0910030302 81
    0xc580c003402c680203458032403e40580114915900c0c1414401000c1c0e0035071151080903183c40c03206040000c8100503611404103940d9081905000c2d0621a03c1d00001421081c14001c85005110101ea03020080790241c807020b080c40003481d9980603841802c40c03c02e500c05041584003180210700c00d50107400070424020011503c000a44914030107000c00400395201440e1018003940420184200081015085145001c500300300e0030300761100b0f401c004085400300d5907018425024440f52038441d001e00c0e5444c00c0802c0441c24a50356083d1595184150702540020340d40128800040000c1000300c0c00b1305036400400c1d5a0a801c200c00041c00503070007507d045484081c80400420384050358450b0416441d00200900d5507001407900b03201001c580642240d40003a1644402c5900000c0000214001c200d40225046064514144141070010150040b80554070101c44085100b5001450015032600310014680e00c00c3d2243c0080c24903080c0e040c8050b00001003200700003220745000d4103241142d000b0340 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 419460710 1250 419459460 419459477
    0xb0a0b1815060c010e1216120507061505040f02160b100b0c0c041112040209040219030809031b01360602030a02280609111503010914040206030c3403 66
    0x20000c485500602c0c0e0650482a1102640000b048d603044050100141900701146031078030390345840044e40c0d04814130348204081701808002905003482207201501421504604081090450b01d5100c2c0b41c0c1c0d10060240f211041c04a141d801c64508540020304100480a0f940e04260030710603120444248054031481c0380410075403010302c059045810916410451a0455442e5800c1140b8403502900c1030341c1080c0d9580400f407074031020100c0c2c00b018501480c642600e440c00352080514003c2995000b10b02c00d400d0503032400080e6040400038952001c1c040c0340c1e074110303038900810010080ca47d0300c0e144038411042c1070004603030350040002c01c0009003960903107400c0d1000074045244c0003200450048028a0340c440480464196480101e045228000821100302e88200290305060910b20840900b40000f004101c00f03c01481003680d8071000c10003c000e42d10f400d80024115000090480c0c4c071800303001035058001d035940031685100340d802000401e014800700c01107152411208204070080317190304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 419461960 1250 419460710 419460733
    0x3060b13141b04030c05040509011b09140f0a06050f07061406040c110622060f05060306070c050618010b0a0e16030638030f040b0a0b1815060c010e 65
    0x54080f9400c0d07a801100e901a0189004203100090600401c100340f1956128540f510180b60442d01064900040d0b03140d05030141004c202c18420f0700304001561003002000b4048109803030360b060800031142c05007032458844078001500d22182c410030000415940c54907080b00b07501130045095600410081d98100540b41000d00261085c4109500440341c07980301c98006007c1c1e0580300000c0303c0c4036555088100e100c2285035200401c3e50416030002c0000c2d0703181c0d42000325505040042d04d600c110a8070b0034048828490316801e854100260801d82c200400ea9000b40407010700750415103801401800f40f0000642d5a1031424001c04142c40d030000d03103460303000003c0c9020f2180c098402a941c2d50805444081c08082ca800826005171101030724080c0c0f00301000c038030420160041d61141c4403294a1500c3c1e49414603003c060740200070300c0b244500d4500b0301c88609a84071241c0c0c40c0030010b0800000200350701d56040388100d00342d1980000b6480000098417144050064000203c5030321071000322500340107203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 419463210 1250 419461960 419462011
    0x2030a050f0c09010c081b0303010b071a0f0703150b0d05040507120b0a0507020c090901020705010f1103040b0604270c06170f0c070204020a030c02070f0f03060b1314 73
    0x4079505180000d00c0c004c6a80049880d81e4010701d0981710762001c0711f015124180c0c4203070450704241d20900b0850070200e0820140182c411004110032284400c03903800380303400400c032140b0341c0019110307404050b80e44200003c000001c401407005000342c0d07040280c540d080e520744c48002c0d000c1260126114014040c001171004028103013100352587c08810080180e4540310f0220050400424900451083d442400040d4031030845481c0030317800503000543d454105040c62802c1d1002c0c000518000352800c40101039801e028070940c0d030001c0c1e05c0f10414455032510f80004011345000c0d107010303501c03429058082a66000c41c40706c003403065105000c02e5840c0c55880307606480040d000511860300c02d21410015a0310070041507019400028049414200b02041c1c002c10101d0700b01042400c04030750380b440302528040e01000b102c4000c0c5500560011175a003000d40c80c08003850b082c40300800c81515a55088070980d122060f548d418100741c40100302070400404d03242020b00341650602400881c80300e828890742c0c132 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 419464460 1250 419463210 419463217
    0x90c08061f060c02010c051e210a09050f0112050106050c0f030906031611070e3702070204110d0915020304050d0f020307020301091202101e1e02030a050f0c 69
    0x390b44a14032403d0342a00103540d0040702c0c1e10111b50350b0080380c99000206000395240c1c85200710007001042c002d416941c9260071107100903c2096007540c14040d030352a040c0d1146d02e0605584041e101c200c80400ca000058900c6c20404407603440607410000085450303030b400005007030301d003d2040440c3d86840034584040c1c2c40c0d114011169422000400002d04a14200b80009461416a2401d0f000ca00901c0c00c800d824001160480240482a00140f00880004942228004da0031105121000c4103082c1013079080d91001c0400b48045401240d21019951030342d005801c80c100e000c0005540d616031400150040080c407404903245080c2440342031203000c0a100f9a40b15a512074020070203d011910181c5210050109020462004011110041c0c03428001d1201d403a200381c0300415950150705003e800c0410b43e40141e01c1c498a40041d14030150100381f042400440c0031300000400c5c112408848084030050400c00401b80d0002060058400c0254080c44c841e100f880360003840c03501c0f058602040c511 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 419465710 1250 419464460 419464469
    0x8060103060b070c03020603040203070b03010602010510171c0302282c0f0f0607060605041116110a0807080604110f0334060206040b0106260a090c08061f 68
    0x1c00604c418801420b0800081d03802c180014200c58503181c0c0c5207007800e40d83e8001d8100f140181d45403014020126038140b41e07140a0031804040390650302d51121920b5448003c003006501411141141400c418083d03030444403040c19021510140b5101d003501c0780e54900001c88003a00140b8600080080080d1030020055017100800d0000c803041407490800240d6180204000d901c002c040300d084000350b98007001840b00901c0703102c000c944c843c5440308102c11a40400c05d4119025410881c800484105818100b0301907800030002c0c42048210003c00c0812041383c001d0340c8148a80e8001040445001031107910842c8541118040010a00c3c1807045000e401c40c0020b80580c0840c010b5220407122054155001e40341440100344140c504400300c611a849500c0355001da0131076000c0c0030901c007889003800c3c05024241030003100c181c01d02e00c8001503403010391020b07080e503101e00c00031400c0304105400c405000c0d5007000d101810705032145c007000d41703550782901c01c0a960035140d9100c4450307e034106402802c54 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 419466960 1250 419465710 419465723
    0xc0801020c0d050c0106120b060406140f190f120b01080c010c0f030309170702010909050c0327011a01030b0a05010f1409060309151e130602130608060103060b07 71
    0xd02409002e860070f4000c13016036005035481d200c005c5441501ca050122146006020a00c0c02d4140002440f046900c241c20103800c071080c001480501d2346800c018007101c55021750b84030701400148002e1645050450300b210342d2480c003c08002800201c80380e01004405e014686030030450366103035a110750300c01c00003d980b40407401064130100481c0b01c440d0403050184c080d083c08113201c0420f41d03c000c01c010b07001c08450712102011a40400f03559000340148054178907000200220b043c0701c0050050344c0030040110106907170503034101d4442c0f400d08100c9400101c50400030b12403800000c850ba200490341e0000345001a2600c0060b894601c1c05403401812942c06031500740760f000000100b2118a0722191010001c2038042204102e50744035000158856100180540345200402034007001c8608060a40e07401c2c0780c031007040100c8050303200303d0158003c0350942000744450500e2811002901440002030180343c052800002c0c080e42091009100303103403d0303a04000080c1c1351030382c55005004416010701603 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 419468210 1250 419466960 419466973
    0xc032702010f030c050c061f05010e0a0302040b0d1505060f06070c0b18060d0e01240b0304031707030b010207171207060e0604030504050a0e060315150d03020a0c0801020c 75
    0x76003ea44000c000c000c2c58513001740b814407001700b0b240ca0500d05070740d040094002600d06071021004a84d0040181009117050f1455103d00400158800003070700020340b1443d030711184400c15688030540d07041c4c103a42c0401010590345203038030396200400080718060300401802011481520740b61040301da6150340a051542e441e410880881c10581081d04100114080c1c90700101c155a6100050400f00301c81d45004902c1404000455080d602c6402810a845100c41e00c00061104240c280400b50340070030201d1a10fa0b915401c0c1200d403840a03c42d0b100e0002c00c6032044c440b02030b40c1508210380701c400c00c0e02101c440310fa9424501d88006070a2102040d81d4108024005040c100c03000204182400f819011130f0740241d121240c1c0c01d160042d941140030071350000f01040305003003602500b401852014a8402240340c1078011a4499020b045403009110340040050319148810007600700190300075007034411844503031a01070f40d02d80c0450810303280742542d600000750180050088447c074510a6000d06070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 419469460 1250 419468210 419468237
    0x50403020307120212120406180f1b0b030a050a0c0f0c0201110307050f070905090109030909090212070609031a010815070507050d031a03210711040c03270201 70
    0x2010f40c2240d00c0320860181c80d07408010440f04801500c0025082c00c2076914030b00342450305130202d035404004a0300000c542e45071007010903900003c0740c15454007c4024075030300c52a68015000d1205030b030420b2424503030210034000d0801c0350f40c0c0460703c641600030040041ca5401c85e01910401c612520a900040c0d21984280041d48205001051710300d0190490f4146075459940608019017450740c04915400404100210300c030328080d0301c2d080000340d0000c0020340000c2c0c0300140a00d0340f60041c200b125441e429001e08544800b2074910b0304d03422a9003500c404a4684000406490a0b80f0003a204074294030301c2e1410060f484111ba60403212040b0085c640034920b0001c0003d0480001c2406051110520040d00421014000c040009466aa00044210a03095840b40039030f00c00d40118041c5e0b10140c2c441500d440b4400f4020102a00c521403203489494074540f409041c040180b44a4200b402c0400e580a141e8054100c0814107185081c02d650340c4202c0710310600c02c1c4000103c082e000a140071603c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 419470710 1250 419469460 419469473
    0x60f0908030c0d0204080105070c1e0b27100227030d0e120d09030311010c0906120908130302120a0803060d030509190f060e132d050405060a050403020307 68
    0x20304208907510250400780c1d51b4024508640e812520a80480d04403409a420040c4840c0e0200030842d904510340740d080c40300d071034550016000030700503040c0f41d0351030f8820780b80360309001c14a90420b00300b4422500a0380503410420043d4020310400100384039a460a80c0c4000440c2204901041c40070f03004002201d440c00c000c0300c00c00d8880c050160040c14034040080800000d11804040e505217881e64040300b0328514006210b200e00300e5041386036034508044003030f02c070350b004011804468071840c04005500003104644020b042c1c0200c001c04d0070300c000801400c120540b0305048200c0b80201c0c2d42a000c00e411510721f680345c86000b00020303c0882c041000403c50b02e807000d11141401d0080c500607050500900201d0f0911100090300d00c00701601e600108030680d4411101d1010340001e00d00f585a111545002c111005816000030581e21303103920307030141c036148245840c04071180591001450f072040700410380c00400e0250760585090140c0f600141c40d42d58640252405581e0560056213030030001d86502 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 419471960 1250 419470710 419470717
    0x6180c13020f0d060536060316030605060901080d1202031b04060203091f140721111c0921050d050d050f0c1c020f0d0207060f0908030c 60
    0xe0039100e0342070103000c169081100150204008110300041c81d2400d0004005154006000108160f2141c0744200c00341c45a8800754481e0300d6040c0d182c02c0f510b48801001900b030035011103034000309800c1d45500200380411600300b18016130701034640c4c0c5800c0c0d0301c0c0c82d111070311040326090520106580462014160000c1da001b150f0010841e80b4401c5800d4038800034022680c840e502c1000164030100780c1c0d07061403a140d0080550304140039100d03149100f55500c050103003d0488224200c64502040754400e20003280f60b03280007007030300800360b0010038070004c0049e014482d4442a12050300c01e013040090055107e00d400c59200015842e2000d1680c80e00d071110304444040105070140080c44074681e800075804108580c81c2c28900e49032035880315002c40d4000c00302c0304000d000d104940340003803c4c00328032903104c0c00b100c550078440f803540c800304424004420301a218841034801110b100149549907000180e01500810f803003007509110030007150740a401901c02821015220f62010004039441440c690300a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 419473210 1250 419471960 419471989
    0x20f0603101e030f060e3a0c05060a090b070201020f090d02010e04050a020d0b060909010308030c0c0a0f031710050f030f150901110c0c10090e13030206180c 69
    0x1007103146407039590f0000003000c0e00703104490345603c60342e08611354142802011740034255520b4510400802c1e010904800e24010049503206d0781d107147c4040c00034803030031500d1100c40e00981100c07032509100c2d0349440182030740201600c8410061011a00652060003140c4000701840701c01ca090600100400c012918050022814004101c0c41f21050b91918058144250514900140c03160f1181c0080b0341980d40300035205228032810005121980c1e07035101d50505581d00181e40540781d6807255181c4200b88982500c4c1200741c485c03038041100700400e01c4c01c490340c220320a83c2d441c07a068684150341d0101103410b0b82c400c0f104980b404c9003441582000d0b282c071032986800074121031520561011860402c0c0ca50024034048000c60700c10001386000034080c03240a0280410024a800d060800590b10365001c0302700a0b106c0c10403110040c07101449960380c0c501408070075011100b5800d110000401c1105201c40841c058000c0400050401803c414000d000342c045001a00f1400607182c200001d1411b030911 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 419474460 1250 419473210 419473259
    0x709090c0504031407210503160609050304030c08100c0804020d0510150510020f1e0c18040302070e09150a1d0304030b0a3c0203070c020f060310 64
    0x2c0000401c5542004041c1c102855000e424170508060209220320b0028091000400100d00400c00243c1c1c000100c50004c0211b03250b02a0400461811a020300303d141006840c5110111380032040c850310000480490300e43c3e00440380b100503a03a0140c4140c600e11044880856a410001009030400b00d014000040c440c000350340c040e90f615032101d011a40a140d03070b0200580602014046170410842460b00c440c0300d80000d051405442c1500c035598108800c0080c0b003404480703611541034404020100f0036442c014107900481890001030036007590211020f90052090807000500903034100103e03800380d010b0300c028041e42c8842082e603001d0440007519950040759125107219000842500d4030042e29464400755540d1861420184514800a8082d40e94603240084044220b40c0e010316100119a40b180d240c03450f412820030703420300103a020700910035641c000001c000703015502070600404c05100b1100a100d9640c614140f102a0101b01c0702941001c103840000e004441580028040c01d030f0481d031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 419475710 1250 419474460 419474467
    0x1050a0c05070906080c0a0b0301120f02060304080909130302030a1809090317070206090303060d0f0605190c17060d330f0b01092102040603110301050105090709090c05 74
    0x140d0380c03840c007201540410701141c4c2d41d070070500402d501404a01e240c0142215074503090782c20003c00e2400c07480184105d0750082c0310072150100700410351940007000d9030011706c06a06c91525080c100d00a500081040d442540380e00000740f242014440c1c104a0660154015030400400103000cbd41c4041061340701071501d040c000c5000400000340d0084025031071081d940e104815a50220003c0480400b07072910055400c200108000d0b21800006d40307521403400c07128001c81c1c1e00c8030304003810b1001c070807080030f040f040c00c1000300507041103200c1c000e00b4101e04000c2d0070031550b0000382c021a901c10107040c1009203521303c5004111a0300c3d010f40003040d40e600800e91720281541005036103001c20070b90300780005c0070400b0346e48401c00c215091180c410603240100040c001002a6000289620064081c0500c900c01e008100300138890351078441c07a40143e020b030003084056260708143d000e0320000103440707201f50b080c40300201e0316046c051300d007174024489501c5118078641071078001c10241c2256501e00c3d041010a1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 419476960 1250 419475710 419475713
    0x18060506160b060603010e0f060a0314010603050f0d1b020a0f03030c050c04050903120a062c01060e01080a0e01090816140705060d0209030304080d020303010602010b010c1101050a0c 80
    0x30340c01480c010014032400810420149045070440c1001401c83d0720801c4140010003584034451482540840644001805659400000340d5011219000508442030141c0c01000e2040154805002e9a00800032a0070554800722501e54808031a010380f0000760440c0320450010402c20703991040320384000c1c1020f60b80e50f00c400d00d01090646a50040e00001d4140304001d00380034041c40480c084081c203640922803483c03d0040c042d601c0c443c091180b414005103000107810003909a2011025009071400720030754060400e80079004040f0740f0684450011254000120103004984200303010206840320102541c40e041c00ca00105448826480389549848940b400105410010071014440c5a0a41c694038120f0074a401ca411080780341010795804260180515558141950322800c074000300544c0c1c454a00010a0a5020384c1e409403442d48a140300e45262640c000c40654143e40341e641c002c110300c1001500440f101c442580b000b0f484038540328003114195210b10300400b00703482941443d240e4600306 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 419478210 1250 419476960 419476969
    0x506071e0807060f050c16060e071202040e07062304080304120b1302060d0903020708060a060e0a0b010e043b01060b0c0c010f1101050c130618180605 66
    0x29614200c07451840012000d040201c036100b05902d000c1040c00410007450005054030f0184240201100b14504500f11039041014582081ca0342901200542e9240766880c005111240b81c0034800324452400c0c01041e844005000078648225040c0360340e900308402c0b0740545103151000b407456540d0000c80400002c250244104014001040848034514a10f402400c0080d050711014164400070074600c404100542e5409060300d18000ca01c1c0400504003041d46010b91078154150b014441c580030340000c200700c40030507134043c00c00c44d03207944a0500c41740d0b20303041d44004a40100c3c2145021604950888616003026844404002c241c0c09828100114019024960044220100400c0c100600e20f01d800090203001c3d01300240318101010342408240d054040d12440c229030600e04200350840c4e031452252244403601080d200c1440200518185100c143c00c165103c036003c0d0110500203403002420501c184200c89644520800740c41d030f61804c042c03181c818640103440d6014415200c8601095503030300c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 419479460 1250 419478210 419478263
    0xf09040807051c050d06080a03141c1406013504060204050d060c110d0c02060f0f2101050d1a0702010e0106090b0a060e091303140408010b2107050607 66
    0x1d61303c3d0244c8880c0c0d2164180c003540c1c1d880c3c01198454000c01004400a50042c11003140102901702c0c0c01d440794070821740c003010561803c180603407242c14644840621021101024060202a0780c2c1c0c80d881c1a0a0002103207d4071124091214a9584401203c04e24418030582c0d41281c412000540351641d5000010503054413880141d8515580d410910b0036550400018442408281e0191040c107020090143c000351aa4001a024850004c1c49044070703642c903c102d445015209030402d49684c0f44c146902d405d030708215000514030884800200325860106180c02d241c0d40d101e141c2c1c10052601c03404a05040201a10b61015507496000c1c0c2040b0003401c1c020013018012039080000d0b003d114004000740d050342a802882404420f00800d56030380c40342c0c50380550010104900e49000c40040ca27040780e010f035082e000d0480240003c903011a802e0030642040d11001800c4841c0c1b80c0c01d0070020040c482400c9040c9081c221031f800440d0822140c01e10704040c001e01409540142e00411500d01e1046a080c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 419480710 1250 419479460 419479513
    0x20310110c0f06011a090d08070804081506090403030e0f0d030c09090e030f031e1602210904090302030913150807060c0b0a090f030905010e0f0904080705 68
    0x100c0226090400c03580030010112103207810350061265516150300440b000e039101c06451480303e800500815241ca80d071004600c5c880d44400180d548021906004c142d80c4c1250007900080e0280e122500300d07040c0d0b9507840d0f5000303081c000c0801c055910b4950b4180c00401d4001301290b070601554201415101061250300c01e040c03919207000c203506440d0100101101c00075000707041500c0c40d003582881040300c00810b4680c80401c030384403540d80ea11176000880c0b500030401c06c5041d001e200b1108003c0ca46482080c500da250803a60222000c0020381040f0501c4001e52030180111040d041c0315a002070300e40358011040407400703801500e24000c04400450800c1b94141405842d080e00c2c4d103020a000c13018070084c40014111100940030807400c00300c0080412a00c41000751480c1510800310704084801e9000a20056108031851141d4100e4a0b011300a8a078501c01c0c203001ca41080b50a11941c00c0604001044540091072520035a680380e450301100e400c480801d0390b030b40c80b07001075540840614000c60b03020381 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 419481960 1250 419480710 419480741
    0x1e030c010e031005010e10090e0d050a140406050d1a1810031b0617010b0f0a050d0e1510030f0206070302031c0b1003020711010f1404180e0c01020601060309020310 72
    0x510345007111000302e1420350b002843c00c501d446042d1009c8480450404101500b51400303c0ea00d51380a0400c48400089030642a9000030020307000601d80d8104000308968440381c0002e2000c0c50814481a21020883c0001c0d41c112045542075514280720003d0309600c050484a901074850f140d407600d400f01c1508001c00c0c0c4401e040032000784481500301810440d07442c50410040034640c140b00100510740141c090341000190046640b0380c003e400307601a181d40e4440c40c54200000f10038100d64903996910981c80d14051640040410195400355010320f047d05c7d0881c43e100d00301201c642c00c1c000e2950000e0025005c5000500c005161450100300950311102c40b007030040f400b450044100220310000e41e1109042c035104001600000e400e04840d0b1034401801d0a1080f0b288820010585098440200d1080c00745400940801e400d02003000f2100020a070700000c00501c0f80d40210140d07241c4047c107004dc00340c0e009000400020b44660052080039201806036614039280140400680c1c0d41c420400c1ca01703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 419483210 1250 419481960 419481989
    0x10f030f0f15081209010f0e010903120309120807140903030d150e090a02091810050c0d0b060414150c0a0f0302060a05010303090b07061103090106051e030c010e03100501 75
    0x680c0404c02070401e01c510070614403031a00c404480060800003000310380c6014070480203000c0c119070703010342c403200000c60308140c842900021904009000b000000d070100d40c9090300130180b03008903219001e03242c0315201039102c0c60050343c02d440b20510590814100107500d48010001e52400d0340311030061400c10303000e80c1414803a642c01c0418042e0700d900c0041500c0303620f03448215028050380c0c40035202030304900d200c2c0c0810751080c400e00549007081d40000c0c50201403400c01c070500504d404020000e14014400d042d003041004249820000c1038816885004800807040c2050b500c146400b00704200300300c6101038130503c0c11140d0050142400850002030717440c440448910703002d06405105c0581c0c402c406d50700030850303581540c0d000340c20b0340090f000c2c188940c440407451700c04010b8594007201580100350a00d94603407802e00303039842c041d09041c01458051452400050710140f40d1041d011030644008029002802c0642d00440d02c0441641d1065814412460f1101610504c3e202d894043c05452202041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 419484460 1250 419483210 419483219
    0x1d0d03021e0306060d050a0f0509060114010e10200d0c0308070320090d0206180f01050c060c160602070303060603180312021b061005180105010f030f0f15 68
    0x100724405000c00454140400400015030740756000c8521540940000160301e86907400044001c000d910503240504c3d00d0001841000c20300003840b581244c9540080490900069004550819007100d0700c80c0c001f80c01d2a950044c081c0200048c01403944004460481d0002d240390b01c6103441081100000822903a03543d0200341940105c145500414074101031200e044007049041145815a00c03504071880046118000342d034624030690f600396002040d40d51110880812040d51000c0100f10502c660a40e09509445500400c1030781e002c014030101520042ea242041084a0313030003809a1414002d40c4030140b000504144003502e07030f203402a0340002d056400d0440144c21117541d0315484013080e195000c41000240e101401820b00e07004440b016032145030240003881c2075400040b00c00c03040d016200801c008170349014030010481d24101c6402000449640c61106002c0e0b082c06000e00080300c04007180080c5009401c400f0880b614070b0390001c0c281071590f29000440c1c11400c1c02e60240b40c61482c0410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 419485710 1250 419484460 419484487
    0x120c12030e0709050c09100201060f0e010f080f030a081306020307170703061208090d0501020a110c010801030210080709080105011203030b030102090d0f0602070501020316030509120406031d0d0302 87
    0xa094003c0d800c0040c3d04060b101403482d401440d001c98882c03046882800324151003904480000c00801c0040700b8107540b00c3d41c03400132483c0e00b40541d010b00c0016140000341c444001400f02802100480030710b1410f1003080c401c4440103402422030312080000da0070900080c01074402140300e000a540c41207508007504140d1041c03010050b26120402d81440c5007071106903480c101280042d40d204025a58a01c0401e011460714102124040c0807940b0200d4911803154000700e0356100b9145c120305480103041440c0054403a00c4003800301a402c5080391441c982c2d0f45004590031a000405810550405551a06801d080d07813000d8010500c0e0242a00c034040416801d030181d45003504c011802582040c00c1d0b2404203c00054540c001707090803070061481410312505d9070485602c240c002c0b00940d40ca2601c1103c05460b100c0d07520024000919280019a1075900880e8510104212030010341c9010318001d403c802802400e580504100c1c20245030900a2000300558081440c0e01e440143e1140410310915 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 419486960 1250 419485710 419485723
    0x1a220303020408150906150d020a080a0314190806011e110f1f09020a03050109050304050f03030304020d02010302130504090f0320030d0f0e01020313020a15020307120c12030e 77
    0x44c594043c1c01000e1254070310000c101c4503481040e45041094105004000805001900710043c3d00704028a03008650008007180c0b202800703021b925840f072001500e0681c441d2910450803d01c000900981c15809264443c4c130710b007500110145440103421000d0310720030a13807800c04a0000c020401c40204c8400c00b40050141d8010b07864410f000d00040424211042e041000d49640c81d00c1107690ba120003011540c1e40c01081c03000e90703041002000980d88500d0700382e40d01c4d8481e000b494810b00c00f00b100701800c0d14000088070b11856025140844829003940150040c0d00132400c140c582e4510b91102003000d480d140f29070585180501c0c008400c0d52072508000e4100340e880d031000c86106c403c400060300070b540000115070000c0d010b15000150000c02121080003050400d019203983c0d400002408140c80281d540314003814001c0714060b5800c3d5845451045400901981b0800340e0014801c81000c134042080d20400045030707040005400281c2d50b0392031f80c031560120710b40c0c2c00300c1e82c2c0fa07044140f50041004074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 419488210 1250 419486960 419486983
    0xe061c0501091a0d03140307090603051003031b0c051518010c050601170106090c0e010905030304060207030b040f08210912040909060e03160611071a220303020408 72
    0x700f0090030209008142d41c10320070b5445000e52288884401014425840100c2200600c1d590980700d09052500800e91110341c880c1303a0021307051501103181d80000203805001c4030391580360030440d1250321030480c4040c0068481a0b40e00c00c1011400941c0b601e03400880340244064105080e1340f11484c0000c2d80c40c1c4000d11503654100580c00c1c1e81c0703100290001503041c0c1034402c6d20070500034202078203800c42e01501941c6c00c01300123182003e00c500c0109400c98104004028262148030005480da4285a524052071045800507400a04100045042c06034181d4006005441c2240301213065261881a54071005c29200b0400c1004040c5484685460b00a5048400200908540120710030300e50101d004500802405503a2200d900081065030f61040044000f20001c2e03d44071589000500b060001c00002030726454100b0445c005121115000c640349150300008419408000c2295800722410050800240804001100560401783e030528903881d482035802581d13490034940d01030f00b042c040c1480c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 419489460 1250 419488210 419488229
    0x801020a021b0d140a0c03140c01030903090b0711033003060d0b07030e0616020d05032e0b0301090204140d23071a0714060c0d0b010e061c0501 63
    0x80401c15a03501909008000c0e00701e05130514001411400d1802c0000f007000082c05411914000020400310007109030641c0301c101c082d9400e0744a0300005406807960100020002211854107102c00781605000d080080d000d111003014204000b004a40380040c03001c04038210843c1c01c05141c041403042250007800c20100c0401600358101040490141c41203542c00130301070605800000c01e04e61103548145001ca101c0702c1140c040e4102480403056020340f82c540c460060040d1420208000c3c09801140d00540300d402221050500c001000510f2600744100f00311310601d22607000031100b071a24051806400c030f10500581c0e45d49802c2d410300a207200b42104500a40c40e5840d0000441c254211800340380b00085000446010074a0300e490a0a075650059206a020708041910300f44041d4041c0000c20310541c80e400038050400300280d41c1d034004482c2401c096400304080c1165900300d8000d1007240c40d060400000d92400140001d1140d08440040040740180b01a101050085409614010040740d02c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 419490710 1250 419489460 419489503
    0x110c0106080f030a0807030e1b09060604030c0b1b12031005102c0a0801020d060828111201090b0c0a050f0304050c19030b0105010e130b0301060803040801020a02 71
    0x300750b940c032405200d1040b41840a0b170800a010300d8081c2e008440215042015078494505080d451400494004107150099686100041007814990f0894007541d4000c80010021441d10105d2451588040a1043c0b4400700740d50001d0342c82d0007008850340a1710805030a548030726100741c24604610041e030006100758084588c000b000c6422507821800300885141c4440d100300c070b00602c1c0c0c00491084403c2c0d6006107105100240b00403041d4081c10203032420300c00501103e6520b00c14103998007501d880440707541c1001c010700c00075010341c2900c2d81d43c1c140c4101454034038400c10340006112483c1d0000c0030607030750351210034640800001d00d80305540701c00d1400000d824241e030340c2c4000301507020304041000c0d4400000b0200d014004100658011004010201c2020038600910500644035910044500c2c030b0004001046a600a40b41c4200b0098041c010306040c4030f40e601c164001d010030202c00d94140d565180085070440e0306100a0024244403400980e039410121130003850301c1d4a0000194090001b039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 419491960 1250 419490710 419490733
    0x20d020f01091109040c03170d1812050a090302030607050403060c0807050406031805010515030f0c101d09010b19020115121a04060902040c0809060610050d110c010608 74
    0xb0054903000340190703061358841d611494040a81005070b04090500314500d8085410103003480e00400e6010780041c4180701808514100d50340b8018034950050050450700b40c0d205010344200c01808c440e40c2c40b45844003407a5039903004282003100c203882c02800214001018020b00c0414011900e141101d0700d00b02c1c20501e040b070302c01040d5000714060702d0308150301c0d1040b06001d441c1ca101c80c281e01d140c1040017000f407400c20002801880c030b60382802d03500902402d203c6003240c5401184070386070a88080c2c500c0107a0b924901080b035101e480710002c1c1c074040c02c10310401046503c400910501030310100d083c01e650751814007490914030300202182d008580c1490030000d124503171a80040301700c0e03845400040c2c520155150011070000b01401d11a07030841400d0400040c00403541040c841203000f564104549c0b0200b0000301c820310b4084643c1c0c0c01c60740c4400041076560904185a120719091403401505000034100d00c201900d55500746603007080808141116092070a220310300003000e020004001d0707680784 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 419493210 1250 419491960 419491973
    0x1602030a08060f0d060608010e0f06010f09022104030e0405061207030b0a3e04030803180f030c01020310141e01030b1002030304060c0905061b01020d0903020d020f0109 74
    0x62015005807080f80001c4000c0d1148480546103950007442808040d4580742010300130610900b084d8014030a243c030098101d0400b0034480d050701d100f0019101e0043c14030b1501c2c40650301108032011512a0442000e040c0601c0c602e40300d000350300c2070b5100110b0403000000c000507240003800c0203103d002c1082c4031801d903010001d003141c1143d078041410001c5a82c1c00000f500103040710002c0360580319411401202c1910004041110000c1c1a003180300307154803031180300c44a07002e0340c0002031005034200041660109a6100d0414a0700c07240d04a504114104c4c800038203641241c1c2014100d030390003005005031104020059000f80c0000300b4011481d060590000391680003a0084c0e1482400d03044141c0c045912a80024000e0301010304007184111507150300940d00e038403c5400f0f9a059141600c8034825500c212980800c48a00410490514002003504004003021005075a5599400c01c844080d4443c0c40c024280c407035000307070041e111042c0c0811000e810000c1401e000d62840c0d243c2040800040d02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 419494460 1250 419493210 419493227
    0x6010512060a0306090b01030c0906050112020c010e100f180f02010f0c050d09090e0c150a0905120c0928050705070b0f090d031b2706020102031602030a 67
    0x3038240c00300c4103450304008034403400c6035600043c1c49141011088801d01141d410000c0c1241e1040e15283c58265845030407401320741c454003a16002a0740701c07a030240c00307a110350050f1007420404000050fa0304400390086c0d10b40410b070f0101c048020307101d6a1000e01d800e6544982648158221844006891956582c50250950300c00090600c0403601d240d041c50740c400c2c00b81150313056008048510400003410043d200c00e841d40700345824503050203101901d0207008202c461506034082c0414507240c5003903460b40c102d0b402038501c81080040103a000a40c2c2d50b00c9a00c5d4440c40d01c000c00c080c00401d0300708024081400e40040107070020030b2166001c072803100c500c034261210304400c22000180c651035900b01140d0710310426102030f00c469040418031043c1c1c0c0303411188a000714030706c900b00d9440c15141c16003a2305881000a8942811040c091030500c0a8001c0444000d906205d1680c0f0f180d1811380e1040030080d0f1940c0d005035005039408400c018032109040c5024034064040d0009504100c05030b034000b0710f10f09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 419495710 1250 419494460 419494477
    0xb0d0506070507140102040b030609090118080309190807020114040608010b0702040b1201050906070c42060603060b0418090212010e010e060c040f060c110d030e0f0603060105 77
    0x80002203c40511550310003030307220101100029955542d49a0010050b50010f0f607030248550540d101240c25418144181c90242480040c0414201002e80380d0f04000e400c0140700015900131b25085964039071400302c0c006204c51141e1603103902e0304c40500004051070b202c0c4d100840201c3c0c0801c81070180c030390404201411180c080e84101e0f5500054808100a00320480b0402c0e0082c021520300442460103410080c8035000d558201c8459039a14481100d458860000c090f280041c1c2c0c0e000030088500326007464040e04210700705043d0015244244e10b00f442110051080101e56525007800f4455141c09001d000307107400241d0b10304003070400400d0030b0115038918030a009699503a0b800400c41d1100d9411041600442008000341617968003054041c0c41ca041c004150ba01403200060200151007090750705035841182407242c07980c20020159041500124182c8070780414504c0024507545481450768140c3c031a40d100100c0d044c5490030f0120211591100d60300c640302c00e108110450f64000107550812 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 419496960 1250 419495710 419495717
    0xd02030a0504170a060617010b03010c0e0105130b0a0804031704030e0907030605090c09130513020d11030a0627050d200a11090a02030907260715030b0d050607 70
    0x1d400380d0940b0fa2418050950081202d07040440014002c0e515105065402004500902c0107403049000c06089400b080c50590105a86c089882c0995101d80c0c0a050707484060140040d80d180c580d00039030450b400800f801d00008203800100020503921401703121800c0c003402d40c101c02d46d00709642c0c0903120b00507048078980245129800a4151482900154020b00b0090002d58817424940c41c0c02d01c203170f403010200500034550300d00301038110034051061a1041d101000c031020b1500c425400c100c2d95840c02442968800c0010f0110681c0342d4040c058100d249210f12070008220405042c04080a0b82c0d4aa000104c0e18004004001140c0046050f0a1032036231413400340c024440d00b00000c80c104a840d503c02e0124460081c0c007008101d44146208820070080760521540d643d105900d200360f120848010061b500305410402a207803504035000d042c80802d1480b1b05c00e03101ca10b001705103000401e611240c4800d001683c0c4621154161061203130405040ea06110724104a8840e256941005040342080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 419498210 1250 419496960 419496989
    0x6120803090328020118081803030d02030c0d0b030303091005090f03070602040e0c040305070e040204020f030a0b19030b0f0606040f06020a060f06030f030c1b030309080d02030a0504 80
    0xc10109200310f403c4582d90703040c0340d00000401184103043e440c1c03042000002d5072030001c610401008031403007030609561001c1160301c1e04000342407400d0300030784011031660103110a004100b414091400038501c07e4042009071600e560768002071805a03801d4510b5580030fa0400c00500c02000b801266405458880d00e201056607201c0104807860400c4010303400346140804218031040006a03001030041b998901c4850210b920b4180d000302041c400c52000408035404603c0400070390140c03045041e44907000410040c01c02c00d00d0710f4910083c2c2c0c41102c0314149541e036845140b00a2400f240304901c010081500b03484040d045542d180780e007182c0a03108215130501040026038554606c8200d80140200c80600e0544c00e581347d00107555241d05400c200c4101d800e000e15503c441c98103100f0803045079001881c0c3c1031810201d4030309560b16510740c4401d951101070000d1040c040c07200c541c4940c0003107120307036035506c445803800c014281406000300440d0119001040f4221485603c1801e48058440d0300d40244035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 419499460 1250 419498210 419498221
    0xe090d030e19140316060f020406050d0f111b1b030a031d1924050403061a1906080c0403261e09010f0c080307030b0f030303090a02011206120803 64
    0x111598124041520f91000103500c500f0241001014840e540c0300351414010300070300907400000c5c1d00650254800242d024400381801c60340c1ca810600710b101441000203060054407045800740c0e80120702420010080b0b07405c00030442000c011211040c216009042d18441c0c0d03c20009844600400d4082c0404c100d00308200c10300301c40700c1d500b0508544014250310320340c0781001d441120f040c0030348544829040e00072203040c000d4148401480f1112101d035101481c150131542c5400080c07140f84101e5100550106456445880ea420700e8008100001160740005240040c01895000010450050100140070801c001026207891403805158084030103100491521204503600502080610b504180c401c80308034017038910002d10032100c082c4c0e240e080c05603030200140c03039107a074050b8020300c080010030005220512079032103001c01d550010142c240301ca141400092454105031001015030304003828090466801c1291b0a824200d80082400034030b181620103105410b40c200043c201c000300000191 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 419500710 1250 419499460 419499473
    0x3100819140a0b0a0b1c0302010c110a021003020c010f06140411040806070e1c0b0f06190501110a0507140f090712050402011e080603011d0c060a030b0a0e090d030e19 73
    0x10301b540b80c1c403041500404e1860174002c0c081e04440749000042003000104c40b600d4000414100c101c0354024001882190306402d04400943c428401819507560340d0410103130289403409200f000700041c9641c0d88038064510304001c11074100700951907403104d080008010504010840b40d50161490030103400000100300402c5032551030941036032441c9080b0500004001c03403004460700920b01c40a1802490380d03070800303005008660701407429402d607100c00e042000b0741c03180d00c070010034031b08100a0303851564842d62000d140c0100f503001003003114032a800e5095030341000803c1260010084803244210f00b480f01019020030b568100c003051642c0c840f40042c0559000d02002d8803c050404510844e07075000e00e000808144c2d050790958131030750a2908003c1913141d22288900500001c0f40030740030a40d840c0f070400500d90b0000c0c40e40010f05131942c404542598071403034688002c0c400c44140440c0ca240c40d810f0f481c1041103009070b500515140c0861481c0301c40001400024403000c0760300b40380107000d0314200403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 419501960 1250 419500710 419500729
    0x6050c150702120408013c0e07050d03020708010b010e090a0903170f040302011a010e061c0e06150117012102040204091d061302010503100819140a0b0a0b 68
    0x20020640f001500203259081544a402d42c0c203004030819501c2d00311081d06210240da03014200d01c0840d403101c2d1148559884c1d60140010061010444140e295150049041c165801c14103501580201e0020842e010003800754040c000c1c42442c2c60001c8480010014010980c041e1040c8059070b80c0e080d400d01058052251511480340352501201d8600c0d040c28540000003044074218015402d003103040703600c1d00c6017488005844405071100a120351030541813104c0c4d1b40210b19408000002601201c000304118841d01c0f25440200c405090703180f500306041c0411070a44040281003044c84104280300f00000314245042d00d050328111420142010541100b811010740080e600c50320008000035100c0312030b4450343d00178095403d001804040c01020546980c0101c070341800041d0300114041c01903100304c00070b5070b00000303140c0c041100b0364a424115140080044070305d8260241c030703080707a42441503209240b07071007620240003040403900c2c3c1d5481000da64000351908607001d8586420300b0309544c03003240300c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 419503210 1250 419501960 419501983
    0xc120f140f1b0f03040e061e150f1611012705130b180601030b060418020a18030f0b090606010f0f05071506140a060203070f06110c0a030906050c150702 67
    0x480703480e03686800040040740d06c203031600c6104840fa82e8102220a100d41d810860017440201008440d40106000000c039078000c00300342c1e102ca2801c106c4003e041c259213840c500751a00901100400c80803240000d4070160440d007580c18a40305040116800d15003e10100701a6141035440c40b800e8842900c01c0070241000c259040d610480c803c58070740c1c1d00031407124401e126807003d9130180070001801d0700344000d5110318002d094600d502080c050031a01065001442061403a00d0300000042007815200d090b40e203540c2040300c0d414030309a41c041c1171282001d4415041011900a44a141003910028004d81c050000b41c1c4140301d03414035881001f5000707009903800c0c0d5402280c11403d500c1c2c03001489004011074014060281c02802903140641008102d210075541c0c1a0010361505042c3d445800a611900c00111407070354482c002690040200703130240074554030201c000c000c0c102c0c0500d006003285416030003e104100050002c0418807800080a01003c2d6240b44064400e495092089003010500e416 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 419504460 1250 419503210 419503213
    0xc060315040c0908030703020d030b18060402070c03050d1e0306060e0f0303040b0c0601090c09030b010306020f1b0d020f1603020103051905010b070b01090c051206010c120f140f1b0f 80
    0x48000c00d00d88c0101c3c40303c40340400e03903900700304944107002040600c86003003d2800407607804034000b076542d04090380203000f801d008290814155550f40d440c14581030054000c403002541a0295030386000007602c0c20300000505040902a141c01c008006180e110240740e040d12540105a013854141c8050040724090324071076014564500d100d007482951814284030b44101c9503e0000c0112400e07115071002c005880d4440c1c6502650791940d2504400394209000040004a0411100102d26201540e40030710304c24080290030303181c0c0350000c00703810031386504102c0341d55800c8400014800034021301180e0030390780d0900740042c1640b15254803042010b0350500c070303c21040c940800803440e914404064100c0e0740c03003029050306c241e0300d840da003000f9120080d9494010072414802101c1c044110080d8543c08041890010036020b8162100007000c5100d4400c05c0119100309003034250507030300130130001c444880314603018988100752061081038829182c240c020b40c103900d103001a10307580c14000e10b024969021f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 419505710 1250 419504460 419504467
    0x20409031e0e03070906082a10030f0e01050702061801021603020703020901170a030f030b0907050301090e010216020108271516140903100905010c020c060315040c090803 75
    0x39019201010040b481c40c030030310402c41c0024400c805030203140251680507028103281c0742e0300c2103041101130444031010340392034041d0960764580e2118200d00307c5070070051f90041007000352012038400300c03185410054540e0f410030040000c0070b80c000550a811003040c030205602d264401040d035009000f00c59010311034241040062040c99070004a040541c4d0080790313051440c0c0d03a1030100c00d014032844c0c100038000d41c00c542d0348031780030174001c01c820041c0860501300403810140440001c0e0911000b101c504022420120050141d26994880c200d15407411000851400c07040400040700f001c05010004d040062413400200100d0400790500045034601a80705400b146d503203102a21001c490f45048004100100081d0207480d40382028035105110351525880c22081d0900c1e9000e0740c0c02902066050b1103000700315121142c02e4070541206c28060300000030240e083c848001c0c1020b1049100034818101030050001d50399860b20703081403403002190000b41c0c14001d03003010341d030101455001070224080070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 419506960 1250 419505710 419505767
    0x40305030d050610020303070207030b10261908040e060a0e180d090302011b0303060b0a0c20090c03060a0302121b09192f0d0605060405060702040903 66
    0x64024602034a000c8403c1d00e03583d01c1c40c8134101e0343ca0108580d641c0041e8408102040441c07a607007406500a40e201e001c002c0e5075500d692800805803e03040c410400380d1052035590100060a0003511000f000e40342e40640b44801e1a140c421140c06030307000740d1240024103408103595a4903509108007c000e2411040c1484c13501620825001400044201081c000c045001c04a60b01c0b4040c0c1c0c405580e4140c4904006121040c00c0060303940341c910044091542c1e48402240f811303c840080d200d01c080d00d070784040c2810024a8020442c007454604ca846038800740030441060740d80d040040b980080c41e1035450362070303940d00d1000520725001a0700c040e4010b200070908000c0420040b550708007070340c079200010022a039150b06202c0b01083c00c840b0301c00c440c1005100e0300d6100066401c481c000540112000c0c40341840008400c0c11217800b40d0076015505400a040b03947c0b070000b4040c11000301300c116085d5003000d1411010400354030950000074400d9949542c03a030200350040304000b040b01110b019614880014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 419508210 1250 419506960 419506987
    0xa050d0207030c0504060501050a11012408071703034b060d120302070507031704030c0f030503040306110d0501090507120e071703042c070f08040209060604030503 72
    0xa03400182c0300700c3d11a50780480d107401c050003103208494040c1c3d140c034030b081070a480c01c13584251a480100c1e041d54803049007040100c40101d11028000f210741c01644500e00d05980d2500d800c4855000300a07061030350702c07400d400e07450210540f5032000c2c1e1004032800c000700342c00142188003030305007016204454440b0352064030020700d038083d482c0e890034204000317094a9090070807400c04060480203140c803c240c10180032440c0b02c1d4010345502485402240c144070313100da5842c5c40c1c44d10401c0c2d0303207108400003150400a1048800817a80100008901c1982050442c0c580f0340e2688a940406000383c1e4854401d014000016011210900d00b242820051540c4440703000e03000d49026100c0e04002007030a15501c003069050711034401550144002444540d141c07076612561529410604c0d6018041844005064845a2200b55041e910500c00b090321001284103500ca4034005801c070f40400098403590101e854000303461303a40041c1c04582908650b540c660004d00c0700e100d140c00040503400b000c6500c0c0d0f505401e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 419509460 1250 419508210 419508223
    0x3070309050d0b1b09040f0b10110a121103130810150e090304030503030f09120306062b020f03010330030902010509181506040602070b09030a050d02 66
    0x10968805648554841c10003900140c6120094000c5102d0700200d070010a0001c18010003219604145007480405400141112050210820794030b44807449071900349003580503a02e448000d0300301700c031000d0414a030306030350b41c0c0169200400c41200c402403a003c4a02403011101a0b010705800c480da184d07201c05410381c00005502c41c0c2c421070b03c600c20007005070030041e00584801d940300c88050450246014042100c41101030141940c41c00108008070104030103000461040c28010f501c40c3c003e052000100e440d2911007001c2601c000010300a012281d5612400c4542d0b4010010000340c2c900e1441c0c5180003d443c000e01d8820b2000d00c0090558004059500690b048a00070002500303202415503006c0d644404901040440300180080321400300d000364405c03402540185401428810498080348046c420028800c526400034802c11040010003002c081c4d51003825a00c0030b05040c0360030720103580ca01d29402a5814828046001106910b0400c8000d1803560000101d8441488052029440303d2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 419510710 1250 419509460 419509463
    0x52214010507091401140c15091009020f010e040615110c0d050304030b0a1e0912031104060c0302120403030906090801020a050d1a0a080102091309020d1103030712020307 75
    0x1401e0800081e52103000b0800107044030b0300301c01a604c0e081600f8004480c0c0c00010b1b4130360358030090103009030090740500300f240004442d090400348000e0b042ca40012440c21101d040d021404505104c40e040c01a2215036100d40c2c100340a0810030560f40400740020094841078104564421000b4080445950300001503a4480b04480540c0c4d41c000c000380510804035200d500c050010f41c000c000c01c00c0084d10340d01501e80c0c040b40407100001c5001300008400404510788054100c156100c0950b00b060002c00031084107120240e080030408031064022030982401144175000a000307001c8500d00c1858001d0140d820030032065002e00b55a15240e10b005803484015009500002e8981017010030040300510850340f107440607454007820203041d0170744180501840c000000103900501301c1000749445010800c0044d0240c04005170701c45103448140300d4001c1030034110350809030801c4241c2c40540c817504100c040060304058100390b0034208401003031451250000041641049080b40c3e010355a000c4003604103070303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 419511960 1250 419510710 419510713
    0x150c090103150302092a070c1701020319150513050a05010501080702031213050f0705030c0f0d140c0a03030305101505030a0b0111030f040302240706052214 69
    0x40e180d0082c4040e10005400001e41000c01c0c0008603001d0080342614014600d102e500244503001c10a01d804090303000f5040c11685135003c810140100c80c1c0002c082c821b0080c5402c000c42c00c0d407810b0181a0344d0904140b00c46680c4558501e4221782000600c20020043e10f000f41c0f00f041c0301b4800180010003000200c135064000ba141600201d560361141ca0041d01420103a4000d60030201610a01c1846c4000500303001c00b00060000040c000500c240410344d1040518400303480c180e0710302410300d0f00f4008010f9549118000d503a00601041c0e542e02030f420072007500031041c2c1f03051140c195449490006205d03486a0301445031000041050340c10780220742f060007240d222401c0039650304078000c11102400b5444020400a100040b03658216900492a54070145040b40006024246440c00d55020900c0301a00010000e03090040d4100300000301c86015500d00c0204101403c0305d1901c607507009a100061800e601e82010482800014504128140d80400c48060840107490034104035082e601c04802113 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 419513210 1250 419511960 419511971
    0x1e0e1804110411070828051201050103111c02070f05071401021f0e0c09090708070b040b0f0304061b09030201030e0c010f050903100f0903090e040c0b0903150c090103 73
    0x1e810a8040c1403402e00100d01d4080c1001400c0c0e984031a6900030004c558114000403002d00403c104001840d00c540c05180c03a25a60707216644440c8000070b405800c15030505046c540c0408001949030704aa0032548040b951100c08411180070b40007a00c211200609072a45881d03280c414060080743c0d040840d13840740c222001514100700107a0310f0744c18102c800301c2d40940030000d036100c0002680101e66002c0303000081e509801c40f01c0000800740ea90544d450205907200703d80078001c51a0803c01c510103800c003500d410342000e15040144500e4451001c001c1d01c40c410210229081010075041800d0820324001420110341c90314000070f143d400c5502c0280d00003801c1c100c02e000780d910040740c1c680d05054181e450200a00440d80c090350180d0040031501c0e014850200644150f516034443c04102203508800407030440201d040c004c00c401d005030003070301c000b0700c214080c44009800102180122080e1100207900c56101ca00041d003460709215185c0841ca80200811405c814264010040300c0343c00d032001c100c0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 419514460 1250 419513210 419513243
    0x5060a03150c110604050d0906020a02210c0301140114061c0b060f0f1905070c0302010e010e0307120c0f181508030a020607141c02070503070c18050a0506011e0e1804 73
    0x28be9188401020f9040410451448101260808071908810001e0100c6000b400603d000c01e0031600c080c0c0451045c158104010300c01d0007002400c2c1d070f03840c00c2e003120303d00d0510a1203503d00791042c41c42c20300d0031030070381c0e1740c461140098403450706a403090a01403940396100c0c00032042084440c0d000411618541541e540075445041c0560240d9100507048070301c20142604507401502d0340e07600a480720381800443d85000b0781d00c1c0d07420040f07440138100b90401452007514529024803002e80ea5001800d1002c0d01e51802c6c889403103101500641290b50407400708803010001d490145050040e00480424040020003482080e0005009805000f0319680c0c40b94812075005202154010a40e0301d60407250782001411340c107034064000c0c02c002c41c001e80c180da1a020f080c0d91142407030f40090740400b04d8800c0700c81814400583d6845905c1c1c0c8006a00003d11803890500002060002004500340b120381f42c100e03c2c500705911451619100000c0a00100d103806162200b406d0502c4089404460500c0c28485084 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 419515710 1250 419514460 419514463
    0x201060506190309020a0f090f112107140a0e01020c0a1202061e040e0a050717060108101a04180902030d0503040f080403120305060a03150c110604050d090602 70
    0x80c4a007495400d2420340158030b0340100d0150020759004d9901c070001600210750700c0e26200307600004080c1000c00243c0400340c00d0804c2d05460070041b428160304014480603038040440308030002c1c200089481c41e20b956486034030030744000d000d0400038140414045031158030f050700704c1039400c0c00c44426003c07113840c40103000400c25000e01c9801602071040d041c03050308005040000203407284424032035603044c81a4403100442c041c1c1d0440d902000e54141c0d90740500c02140860700c80c0a8005040c0d14040c140c101d00800e00c0300e60240041c110904001c10400007514550701c4482c0031026001f01100c007200700340358a00c2c0f4600741d000f60040780d0340180ca0041464036a41c9500c10002c100d6030103009002885a1400251030a4100800692f404032581d0040302c0002ca40c41d00800103144115103054030701c410424004d0450b10010081402240401c40900224400009107262001c0c40100030030700c0395a000044860b0320b0480a0320b2000c3c40381d81c0030b000c100709011404524002d0b507a0303a0080b8099076214102e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 419516960 1250 419515710 419515717
    0xc05040509180d050f0c030c06190501030206071415160207060c050714060c03070309091109090f0a0906230f0c0d0906110a08060906040221041e120201060506 70
    0x80b0721660242d107203d80102d00500141031006141140e460400500c034080a003154010908000c0b02c1c0c0019041061038800346800b0020184030000402031581160302003005440b400f50044c00034103100300d8841410004201c621611170b544054201241030803212400c8640790206a2805030040c690081401881034900c0141e440e0070000a111461400e500c0d00c0400030038274500d0b50000410061244a03170010401031820034030994822070564030b00f0f02c5030f204a640c2070a02c180511410051403d256880b20030058010383c3d141c00e00700c40380d101e848841e401081503d800402c1c0509013840032800c80980c0801c48091400381e02c03c010141e44c1c8106074510b425044031114000e11081c0500098402035034440c402e80d034410311001607880c5100d4100c8000d5040300b046500010031600411545013407100c2c007150041402d45066042564009904160212280c0c3d06c0c3c00f00360300c01c000182032144605641c4ac680422425001000d00c442c2082c003c1c42c112410f990015600380180010a42030107005c0703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 419518210 1250 419516960 419517001
    0x90207061d0109050627060405030c190809010827010f05060a150503040c0f08030a020f0105010b040302060903010b091e0603060402130f06090615090b07110904150c05040509 77
    0x1a001540e2101c04144030132010101c121740030155049800f8900101f040b01c80c0c012801100250b1310764030311059103444e008521002d0b24082024034007040001e000b0206071858040242031955607581d82c81c081ca80c0140c60400030102c1100c00100324042204194480040401c40d5907003030142d65500c0b0306000c0030510500c80c0c144540c1002070304a9240c0d01c1203000e5500248150040d844141d641c1d11614a0f511345500170001d10303000003500c0344280380c04010702d001020580e0b0003440558274200b0307a40c03510700940c03201034011000000d014215a80a520242c60584010080407150400b0652000c00b886005001221800f512002c500c0034500000c0031480f032070740144204000d50310109004040c03c1700d44503084e4020f0721030700045000441f0b4018032025102c070841c81101001d00e020018408104d40e4803d601040b410440e00011900b0b0542d43c1020810030744807030041d41c403240340210040d081400b50307404a501d44801c1c071403099070000080c0111802114600641d80b030714200003290340000d81c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 419519460 1250 419518210 419518213
    0x1409010b0a1404030605152b060b0904030c021e0f010c0311010507020c130b06040303030e160b1315020d0f090e09030c0609060c0405040213090207061d010905 70
    0x1084445900c000a200850356460b02985640d00c24448980030782254100b214441c4d1144200800800c203803a402a2029040b52110140013502080500030b03c4500e0b004145000a6048201480704c0ca0708080b0035800e0151100d64a4030702414020b02c0d586c61407000302d102c0c88020400c200301e00e1121b0b801081c031450007030290760507000100040d1040101d81c00c048090160180c1122003d040a1003640c1c0b184100e50064500b080d009410410840103401620481a150800b40b20554039043d06880c152589801e0000c4c0f9081070180309460491080304088841d545030f10041500c0d16500080c00a01c002c405610340700c1501d6032440b540c2d1072444a16400140d000d030301054038051040c000101c07103100a04001e080281c0b6044984d8483ca42116201101c0c0d10008910070001410080e03264802c002002034641e07803c040c420412103101d2807080d41c0c440c58000c41c4a90450b09615042c00c001d0030540c1045681d00306501d040340c00f82911b080e80028a444540203804041c4044c0945200194000d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 419520710 1250 419519460 419519479
    0x3090715141603090e13030e060a0806121e0304090b012c0a15030e06060405040308281a030106090204050a0e040f080f120c0a09090507020f03130e0114 67
    0xe0740320310800420070081c1d0800c80f2590300020440d0307407174002d00d00a80e41201070400078265820043e01400070340307030030301c0c000c1008000004010b40c5c091002500620115020030080081031481c600c1d02c0ba142152007030400f0072071b001000b18180000104122070021906100800102005651070b0051245004000c042904911381c0900042c403401c180000003042071988a03241c580080880d45501450400700b03a40d4942598500004c102003588600d0441d024081860140d80052014602400010302608c00454510104e62050944003a501034018200506d980940051460b001c0c0c0c0034000d8040c0d4a840070200d100c81d014003c0302c060b00d10151a0024161a000b102d06003010000c0c000c1d00c0d0085c0c40c0d0040000662803400030b105038003100c14a82e8845003e85a8149040d00150000a400c1400c000000d041340c6c100c2051000c0720900b03c0009225584c4250503400d00901c0b000a111a01001962040b070244605040060b80c1c100b0241d80416a250402d45c1038003ca0340405662124500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 419521960 1250 419520710 419520727
    0x309060309050a0602031501030612242703080a15050f010507080a03050405070603051909020301140906010f0614191701080c040f020a1e050702060309071514 70
    0xa8101420081c400c404030f8210020644805003281c000780c618548803c0c040007107410942c1e060054102502c00340b07550003049c0d03d040d61504816080b460f81f80c059175800403001c01940708294409028280c51b40345503d40716080044610908605000803400f00380040c02040302149244600c0038129607070405004e0035404d001c2049406210b0a81c000c0c1004000c002100001d10000c0c040d014007251a20003043d1410b1624200382014801d41018082620b0b050400640207041410300001c04d902e408009604056400071a0140000005c01601c0c0100d060034007541c4100058202d0480d00c040651010443d128602100c9001403849103a030070900900c8400004414200351505421140c10103170340c4060452103043d0080c00136888546507400050f8640d00f903041a006041c3c01c0e40c5512011450034a248001030140c070103010195988600070341020204600880848011580041500341c4030303e0003042041d0380f60340030700400d02e4074000100060003140c010b060360302030035001640a60900c0c82c00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 419523210 1250 419521960 419521967
    0x170f070e120f06010501021504151a03010504150c03090809150408120403021e1c02120109050a1b0b12070903140c010206010f12021507020301061203020d0507030906 73
    0x4280c0d1081d4080900c624891094000700b280d210442841c1c006011150314007400a41041c0c0c4015104001400c40030030030000a89002c01c2a07281d038203000d0f002031100c4000f407081d2400d410f408840d076010362825060100703104d412514100d00b41c0b83d07030f58140074901d12002c0072401d80750100c200078035007101030007207400f14a02910800d162503503007411542016680d0307000a1401300801c111000580001905105500f0800444946850708449164052200e00d010501242c0e861079007200b50030b0900c2407082155103520000310400300c04002409030b400b40d2f0a08030b0b1180c42c903110854040c0c15041079a88002c41201e0310800701d40d4419500c604007001145d4025546030014401070412895000110000d08000460854000c02d0700051000f202d0000000e8500328042e00518200d541c0907004100300c9a0010030061541d0341501c442c08000c003004c01460f00f0b0701030034100039031550034544049540400030344074850fa00d02990844852803254102a10603226407039000c0c00007410410140009800f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 419524460 1250 419523210 419523227
    0x70308030a02090a1553190b0d0206070201112e180c050609012d08010b03040221030d09110f01030204050a09150305060108030703170f07 61
    0x1504401500d00035406000400d0746400f600580c0c400f5192074550805540d200020b801c28841160807000f80c081da080315904000060b40401543c0848011441c2000944a840a2003030560031000350060500100985d044407c40d000d41001525010b120011450444009001c080e0040c025038a800e24035001124000345042007a200303489203101c9920308891421550501c400c4200091140400c1100c01c01e041d1204500141da8520318564801c02244220340441e0882c2da0440c0c0c030b80c5d690000400141c682007246446044008000c12403680512082480029800c0701540c0e0941d1030303030300d5690004e1703580801d60740a900448480303102c00100c4040b80319003102c90324140899062554061040b801e072a18544115100b40c4800241c4540342001a50074190309001d0905500b8a030070000031074580045440340168060b201d20b1103076a4150344851003005150028241c1e1040c1d070311416102c4d0760f40d004180441c00501d124282c41002d8000a10b018001c141007280348032507071107881c03048a5109 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 419525710 1250 419524460 419524471
    0x90f060118032f0111070501051e1606050105150f09060d050a0c0801060f080f130507030c1401080103020627030a23030301080303070f030f060801021b0f07030803 72
    0x282440c022001c2208a9108031084061806201140e0f0501035100101c400544046041c0300300703d4036458180c503021480d0b5007610780a1070a00e0320b0300402d0111041410700b05c5a0b122010200041c004801305080020400c40c03400380005000503680c40c82070100c81c01d407030401089c11b00014407460400003101030041a094100601c0182010111408007048410950b101901250b990001944040c4c205a110740109506e0810104499821001502d050310042060900040300c8002845441207501484420340e002011901c40c0f50b280d1814034510006e5015100c4114000400c500c5c040d0b10604a86040c5ea90241003207061003c50201c40d4480c18001909220b07100030041005440c0d02c041141c1c10489000d04550700329203140142400d11000340e40e0317040c0c00641080006100c1caa2000045a800a500d0310f08040d851000030011030062812510400507182002c6c00069403a105401801e01d01402050000a40680340c604a0341c80c2a110040107840c3c00440040002c1912a0051030307111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 419526960 1250 419525710 419525747
    0x70911120714040605160204060b3408030a1805060f0112030509040e070509160e04090c2309010608060319031218060903030e1501050901050d02060705010e1b090f0601 74
    0x1016980003905a036140d8000703040100300440d100000c4400be0b817441c070003281040c001c0d88410010010304100340c80c110b00083c042e0303540000420610072250f40072640110010148000010042c6000c9448a03029100040c0003003c038000801c890301480b10303601c0a40d50bd0303112145041c9a060a02c0090f1508000c00c61060113000e00004040c4c8800c0e480c0e9103c1c04500e5040d00001d43c04940140804540b01c804500507458030310344100103501a2080c00070b44100c1e408895029004c81c1213516203a09011340c00f40c012042c01c0c00068201c1e00041002d0152504a003a918080740c541c2c40446000c880d15800740c001201c1ca081c40c4001c4240b81c0c008008a803035030100001c000f0180e181d0381c1c140c4a0610040b0002a030358440e82c038282d5401c0c0500d140d40150800c480071254584000520170b640180215032040c06100100e00843d50f800d401c91340c41a41c01070003848a96407003542d4907260880041009400c503024400c03001645000101144903100074000b02281d91144401182c800243c14080c2401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 419528210 1250 419526960 419526997
    0x90a090c020f0118140f060411040612080d0504080f0c0303040c0602030a021507090506040b0a0219050a031409032b0201020c060a020a090308030a0501090f050108190302070911120714040605 84
    0xd28014407089202d83d025503275002108481c0c0c03081c44200c40079940312072a14000043c11782c001030241c200300c0e030301e101307200401151075103071418082c40170b10a80c0c42e8914000c0c000140b8150401c000f10155110710300400d03e120314169640d80680e01ea2007204103200050300507803000e05000c1c03076485000d40c01500d00c1c07405002054403140030038110360054001030140600422082d0615504000c0900d20029596130391401e860b10f0b6440c55510941504001d06000c0d0b8011171051081e81c131010f8030b004c2c5000900312603080c01c082a400d1000000305880802e1944000b160302c0c402c0380140201c4503490001d200800c491780d59183c0c550025040407030000d040088000000012848290141d805040001000541549094460b40c103c1d1140c49800020508000041040040224405204001702401594081140d1804074141403130f5400c00c1e181c203032a1040c088a400001c0000d8640c8503802104450a40c45200043d941408410025100c4038800c0205001c80c0b480751025000c0c011032500006034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 419529460 1250 419528210 419528233
    0x507110706033e0307180e0910050c1209030d050915010501030606120b0409060c02010b030c030f0a0206071401021606180b060f06090a090c020f011814 67
    0xc2440a40c003020000c2d44418921520b844983c00040e070406080c001a030428211003100e4803401010f82d004890000003000013144540510305030b852199802011524064440c2e00c040894142504d00040500c9404400c00e1540c1da0f40c03080c140100b0010040c20700b0990034004030b0704113140c001c2003102140000e0201616052072401340501480000000d084000c40901411002c144c05038829070406040400800090303070030029010314075151480205814400b24003090192803004030060006140601400c40c00b82e041d4854103150100b01c2c00d44840c03000c3c00003015030700c412200c0c0b0220a50001403203440103107800c4009102d410700c0b031105083d002d03c2078020320f82203801180d00209100b0710400d403070041280c640304145800c5442c096141c41c400c85900e0380207040a00030b210030b01509240c0b111410980d03880c015107800c43d50003010740790310301d49485c0c00c4030180885801110240c800c030744a210f40748070180103640c0382c6400070b03d905400400710b44860050301e4006a0007801802000302c00721 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 419530710 1250 419529460 419529463
    0xc0b030f090d02120301141f0302090f060f0d0b0117091608030703090513020408071e081906050606190c031d090402040e010e0a030c022e03050711 65
    0x612489403140300403414a4001c80071414000250a4407007190080c611008211400c6400d59055403038405400010400c4040403034196080c900018081c0c6178043d00b21706400d40d06400801c2040302c140d400340c1c0285064001e01c005406100582000e155090045103c2481d182d03111140101c2e05142c1801c0f503c440402c40010004141d171000c00ca50013450003610702c1d00c040e203c510005d00c1c1d01d80003545010401d46004061000e18080c1c00d1041d00642d1135103909121540545d4090b107205000c0d20401036031902028650008403400081d2210034420020b25018003042c580d0384081a4640201d5595007a910341e00242002820780b58088010b0001d03940c10200d0704404880c6070b04035200d4208401075418040c1c1020340700c142c0c001103090104d10700c0c2080d480b480305030760b0000e9044e60f012941e0344140c13030614050320742c946406140307204110400c0103050380007104c495068002c0d1040050240000e0b400d607008a0b402d212030803000580c04140348007512943c4132a40c4031900f40703080d00100143c001802e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 419531960 1250 419530710 419530717
    0x604180c0c0c0b090901140603150118080303240312030a15090b030c40020a020d031406010c020d14120a090e0f1311271609120c0b 58
    0x3e160020001c6203200107410410002405040b0304c0010050910301840003c040c0d02c001024003800550482d4541c1c6281d000b8211140d10350307002240380c983e0700d171561503043c1e4035002240c100c850184420b0b00c200a00014041c041c56081c4007401801000c002005003038500d0b80040c0107045540e80d1101c0d5480c0592910441002819041d00f010034810100030400d480d00070008842071065005044d00c004c55078124810400b150101107181c096107005019a030040d06c00704ca46d504500e4000200030400e65808107101101c0c101c140c404001904800001c541080422a40a4041031012500c0005480d0a41e00390301c0c420321400c070400310302c0404200e8504054000207020721104010440090040c1c01c191610003a002040d110103151504031085525103c01400391340d48820118103000c00d01040300800b8203100ca0180041c090183c24120414018401d1b00026102408030000b2466020700c3c0007000703403804001c1d541e40a42a0a09402c030308880751071041256100c280e00710010b211032003030307015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 419533210 1250 419531960 419531969
    0x130b1608161803030e0102010b1e0d110406060207050a060309080d020c030910030c230d0207080d050106021e0c13020a02010603201002060903030a020a1b0b01080c0604180c0c0c 78
    0x4029030390181170006400d440031074080034032075541500c400c5210701840c10000b4803ea002c03600c0440742000341c2003d2804d0018620519046410a607001c5446500050300c00c04540d4180c0307102d400c582d5188001c50450b100e03424000d00f00c000400c80d6105482e503940181c040c102070301003903a140088140000c2c0720164070504500110751100c1140008581000c11f07440761a4030184407021003005502845410311920039200700a42e800702e801000d1020007002e442248414900802c8656110100030707642c0c450995078401004c0c1e03200280712103810042285102d405c4c0c0a400b0b0b80d0301e120b100700194065041403003650110741d03031181e001001c20004001242d50006401d200380341d4a01c01401d100e07141410300040c6042d0340c840001d0003590140002100c2e2300c00e4010070b005842d55482c2c24111502000b040340c48000386001c900300024400c0083d1664103c400c2c000803203400c402c8200c14812540203e100d280c210700d047c2c01721301e45c11350155005103542c15032510384800e00c00316668a002601409400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 419534460 1250 419533210 419533217
    0x7060c1a090105070e060909220b0a0b0312042105120412020f010e0303040608090a02220b040b03030f03090f0703140708120f1b06130b160816180303 66
    0x504c81c465030810f2000c08014003d03a1164944080000400c0c1d041c074000d00700c210709213100d00c5040c000403600c406000d90164058078101d4a404c0000c01e0300c029001010310b2604c81c4c001c242240e0030301260102114201e5442c1001c1000c100f0007200801002c4107030f0802942c00e8000c004401405400040c01000604030740b800c00d03403000e02d00307006124035400c070098410b0500400781d649404540d00041502d007150900d26218465039100c880312400e01520810003034103c502809101e008410b21050058204946a420000798030a04200000c0c0c58100b9041c94064104000340d2398555a4800110740c0581d03140216035950441000301490304465a1064502e082c0e1b8083e0120160b07001d0255000070100707000101900340c84c0c0b451801003446541c1442c51151320001b580c90600750758081c590a803070ba807181911441d1406c0b181081c2c0c024418032041ba80c40089000040910301c1200740d04600560b15910b044407542c2e544100002144031011031014041c40079445404460401c2070380001d07510070758 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 419535710 1250 419534460 419534471
    0x601030906061e09020304030206010e0408040e010303090e0901060308040b180d03020a02010215010e0114010e041a0f03011a04180807050706110c010c03211406010905030f07060c1a0901 82
    0x40d00300ba0560f515080042440c0c01007050102281c0d0003e0b060b070660306480e0f08922251142e10f0014100d1003150f03c4050b44c017546c0340001041c50b800c60b802c3c20481e5820301d284083d40c3d440203001803c8854a000040114000f800240704aa55600c09400c2050017085081d03105075401703000902c1d1010008085006030302c488688411968140280e29503200c07058120a042d50401540c281c3c1030005010b203281400719a645030400f07a21030704c00c4100070b40c4041d004200e42b0940902a1600302a04002c903400b07905400b031b03c400e26040506c02e907030004e01400c02144c005201c075070411020705110800000c00c840c2044040010640f060001e09000d48610002e0440310302c2c1c4000a024a090407000004070340050200c040300b07036003007181c8070130995041c5044c08100304800303d40340300c82100040e03a0140794036000f030081e15600381c080041c3c007504c0300f40c0366203800b280c1e100f00301583c0d90303004600314401d900200c2c0c0800815000c1e4a4500100384070300884000c42d02d403a449001c2c142021103008103660f4450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 419536960 1250 419535710 419535749
    0xa0e0a1506020a2616060204082a0609150c070603110f0d09020a0b0a05030a1803020d0f2c1503060607110f0618101107030b06030102070503120103030e0117060603060103090606 78
    0x1c011503641194105540c0030660042c07000c40cac030500d50000081e801040c0010f601426961200150140080d010582c0e517115a2501070080c3d07600120300a080100b440c1c400740c204a110f268081c0c902101c001e40c0d44a2a1612003e2810050134200c0e10498200c6000500880d42140d114050b00400c3d4059035400d880340742c000e420074240c924101000c00301d0f89405680c0d0011075400f1450010902841c20a490f02240380c050498440019802d0b40c0c1d1500000303003540c401e03c41c861814214102044903842e0f00303103480c110304440d50b200c04d40d10958000005c100d22400100401040d040f079220051404407200041b00208207260b02c000c210b8181d9070301c4002d000300c8902d802884054003099510b030032000c00c2c4202080710364a00c1103000241141a1400014440e90f40075011100c00d00ea0240a407030700c2d00c032034104070380711001c080c007003100860511109403955500c1000d03940e00c50012905000e0301c54580c40f0500c556030b80043c14050405848900075400b01d4ac0500410001b01000c440030503030010403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 419538210 1250 419536960 419536963
    0x10917070c0e01060905010507050a05060108030c010f151203031b03020d050f010302060a1805060c070305060108060910050a230915040f110a0e0a1506020a261606020408 75
    0x180c2d000314404035540001800100d6028900b00d040d03a00a0a15950795086410800c0c40c0110403800140300380304040010808070f0f4044040d0075a4010b00c0024400048149001000c0d14010310050b003120340f103583c2c100a0202241710070b22680f4000e0400040190400c01180c11a0324203000d00d0000c01c0d000144d0b410400d045106441d841016000d1402c2d02d5411a030008240303104180d004000c014070000103c1c2d10307200c10307440d2a0083c900140003079551454040c040740c44600512080da9503008100000601c5074003c01e016104000c1c0d60041e0402c1c000b081c40b404003c11003d07002045080c1d4601c1c5d11080030040d100c44076803490940203140100d182c0504070910701008846196049003819040c840080d0700400d5441040d030f0710041641c070107060140860b01440603540f00f440b034090001e00748400c0d10322560069401c40700c03101c41c008441c3d4a4a2003a42e903251001e06c01040c004069140c4017a03800d00000402c51155100303509894403c0ca020760113240c103020701094031210743c00102003000800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 419539460 1250 419538210 419538233
    0x100207110603070c051c200706110c0306040f06150b0d022a07050a1406090d060902030d0c03030c050a080f2d10060929090405040b040302151b090301091707 69
    0x311101d1030200400e03400f04954407070300b0f60310071502030050f882b0b0400d0400c2018040d000ca4400c0141c103c640707510b4507003130040c4501107003001a204589440c1c00c44607600a014000021b8541c692101841c11444c1001d840c0258040c81d111040300521452680280841142c6074801c0c16100005042c1a400c01c0200f080c1010181d20424131030300c0c1c07a200c503480b50300ca010965001d00012910889003c08900301071010b0854468002d40c58010b0b103640001040d001055601e00c107010340c2e010441524660000e84861041116440104607450f001820302800c40e0045640300c3c141d081c041e0419503000201d41c00c90b0400300700b2180c1c1410004104600001060400e400130507691a000103590310b41007001e190389045d44078000082080941c40521a811001180d03602080500200701a01d414108040030190503501100140076010b0011444d03140c521002c1e0003030254200080d80c0f10a509104401d6078410b0719610f130135548602c1d0410100c0ca040c420701e0070a0b08400704c1c441d40d5680c246000c810444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 419540710 1250 419539460 419539487
    0x201231906230a1a0706060b0405090a020318340b070b09190f03020105060d030503060f0321040810110906072f03100207110603070c051c 61
    0xa1501c401000906001c1e90324800d486004040800552489404103070260001e400c91440d8a902030030140380d0b4410200181070340350280c1002c00c5020b840c1c584100300c81c0f00d2407090b15401040301000c650041d0581d80150b40010701c00e030700c01080a8843c200035050144200d052000c1d2030640812032001264610003c1c0190b1480c0c003403400ca64207201c00418a0300a00c00e025040e804040006510540c041140c030300c0340745034403864805101e800d00e001c508401562800301d0042d400c0002190740760410306003565031140d040d1150360440d5100b0b01407003084502900d045d03500d0b1040601c545800e1400d20381c0300c901d805010405950321400c05a0750751400d40c000741c0440c0f8042c58030201c5010180d502080d10490002101c1c0503507200314909000d04403013a046891403a20307030300d84500751440c0841c001d00c8120b4002034091300c100040c03103e814002c90003a202c000d0160200c02c0b0900541d0300d007410041d9442030150600312503648441d200c00346070500450441e044000d1040c803c0b501c164100a02c440201d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 419541960 1250 419540710 419540761
    0xe090a12022808030708190219030f050f0a0f3b1603120c05030c0c0103050114090a0e15090c0f060301150e01090b0c070512010506010906050307020123 67
    0xd030b030503515000c692100a011004001d80c0d840401d859007030b03a054150600ea002401591107403100d001c981444414284c0c54070110f4541444500844443c0c0101440703504107851080f0f0035912804848003a04034603896500d4145d581100f144611040c3c2c038072082940c2c40103c00d102d8050100c484908d04461003401c81c07000e5000540640e150345c6584114002d4940c002c030100d13001c2c0798084041e580c0d6065a54010543d000c0441c1014054100041905088000b44d074280b2042e6a42d03420000702c4068030b081d45402c0901d003000207032522100c1d004180e41008000c11664801c0c82e0414082d010b0105480c81e151a402007100c207515840c00340d00c2c00400200c2102c00c3e62455142003ea411103001403200b400501020049060881e03004186140c001c245680085980340500980c090725401c8074003a09100700e501602e48071b0380701d03014484c0074460700c13041c0c44402d982e500304034050b1803d4100404000440d901c1d08041503500070413401b000c5045e21000c6c404402d5050140b2181c180341d40ca4050354106 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 419543210 1250 419541960 419542033
    0x40c050604240315080f07060f0504030201030b061e0d0c1403061c060f020a03060f030203070605030a150b030906090a020a0b090114040608090d030e03040e090a1202 73
    0x2c14000c68454259001401602600400d82141900904183d841c05994034940f5800010840008503c0c03842c0c0360001825982c0c1540c9914081c2c3d00b6032528410040010b006100a0005500941c024140010014a603e092003450f00401880182c400c850486151000c02e01e2440c01032a03000f000b03007190080c1005c8400c1258112131464600005082610641c030701404100c610b44860a01001306411071000d02ca200140500b240195014401c0000060314050000824a13003405034541920340c01030241010070300e4a402251540c20140a954050f9502c5a0080c410905070446900038240c0050240c0c5038075003041071500702100140718500c5508080c8900005036543d0000c207080d103280f44c5c4499260a603a00040720011751001c80900c0c0c5450010b00400e2280e00084501c1c49405e000080303521f0b221400104070155521125950100d90060006100310360888a02d5540008030100b01c858061140c1c88100003440300d5441580540c0201d042c1341c001c54482981b5a2510000c100c40b41407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 419544460 1250 419543210 419543219
    0x60106031d0c1f0323061824010207121b0e04170d020d02070b040b060d08090906040207050a121803030c020f010504050a1d0a0e06070309050c06040b03040c050604 72
    0x30030745020380e089540c0a08a0780f101c0380c0c18000d0740901183c0b14108104542403081c8001c80e1002c5409548642c40342c00781e1500301c4444800c001c1c03110b1080c00c005104030720100c0e100200d240507008103d02241035001d103003408214035030701c2c2d5002c040403800f0362441040d0740381c4080c0340b0502ea0301940003807051107518010040824068401b1072100e05480e03c0d026075684401e40254000d0141c6046c5104050002030b0500502901c0c4c0225805a4011030f5400c0068075143c080281c103031141ca02c0104184014400c14556140558850b50722290207800540f401380299101d90404009483c1100c0c000a800c851220590b401044240814018200303034032514210b4401425503c078210000f445844540903501e2643d1240058800500000d4500c0c14001c1d02c40f1100c8580d03d00e1041500300e0540240000740c0e51011a0041418021039440070740166100e100085000d00030224040e6954424080010f03100c1d11040f00910050226001084c3c403800c0c40d181110b203a07840d95000d94841c2009100500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 419545710 1250 419544460 419544469
    0xc03050606090907052101090b041e0b010905060f0d0b0123071121100c080402010e0a0305100b0f090903040501110a0b18061b1b0f060106031d0c 64
    0xd442a0b0201d42c0361019a032039960840b91842003601004100a0f0a00e24a01c007000c1c00c0300490680c0c02d05041401100c0d84907040c08229658161400d03481039100b070107044940d1455026501031181854400b43c420303212404107901f0360082c607c000000c0c83c00640c0d081c0c0c483c1c0300e20956000e08400d1800d5030350a4030703090305000c4036520225140c00e001c2000401c0010080e8030b000e1014004405004101c074101c03120020b015000b0501003564140c01900044031081c12503200300740e5800e031f240d16050b0403502d079600111060358488600076000902d02c43e001c008108200001081d0300d0070003102052180a41c03013880140b00d00740c4101400380900b4014007030b25132004000d80702624402c0c60400141c0d240803884034a002001c10003d0810030504007407001b03c000c0d0780c4ea074088100f0410708442003a1130707d11900815001c10748000805207000e01016846a41140e8845508002c2100329013103a4012880581400700a900c090082945d410a062070442d414490002c1070001d84042c2010340d003540e000c40e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 419546960 1250 419545710 419545717
    0xd03090501200304090b0a030c030b010305070605040302030601060806030114012d1a0f04030b090a0605060904020d150e1b030d020d0225080118020901090b01050d0c11060703020304060c03050606 86
    0xd100345e60b2502084101e40e150b24941d40000d68001980502d000d56a00342410b1081c0280410b555601503d4004180395010b0800c076405c8940c050300600090f0329003a002c40e41410051314555155486848a20f009201c980d4070134040d09418441c0444020300291054000d006c0000025039250a0141008104408104c0b815001c80128120796120028140c880d103510903608020101e59100090110010002900c0c1440a01c602020030594540e4410015104801c5600950004404240100089034131440706004140c044001c02c98000203254103047c034520805107902d584441d0003081c102e140c100000c03210880180081c03c0100541c0c18020b4551400d20b03602c0d00c000d05100c044080303000040302c0d003200502108008200c100e0020441e216900c4c00c0c1e4105a01c41d0100800100d0020800e09c28102c2d43d43c416110300303160482c0d1114500261041303100034418004003402c50210381d0401c0c01280c0c8030f60100d90340180d40340b43c076185c5881261103404101c0d00309884d01042010a48845049 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 419548210 1250 419546960 419546969
    0x60905070f1d0109090311030c06010501120908030403030b062b180201090b0c0313080313061812020d0f03080a05131220070b04061211270d03090501200304 69
    0x300d503c0e4000e080075a02004c8011f10000300d440001142da656074004184281690740980e00c1d101c0740c80007103a1707503415241a803002606001080020400007800f1750700050140b80c001d4082e03070400c1c41c0d641840ca0b604100100e120419600e0100b4803040d40d119201e009100c00a0808c03480e00e1049940000705059850b0085500308100010b00c211000d81c20000d8500c0c08a00040080e05551103844650316900080344624130f002403500041103c40c040c10704800e454131004031a21005152929204011198007021390300440c0d0031074908007042e0083c80e140e940030b0003615001da160070309007620822194000c1206107030041040d091000209041e094500071115880c0c140100300c9400449500d4010fa040e240903035100740302000980002010241c01202c18580340c000b046880c0f000010191141810302c0350550204024992242c0031200c20145203048440c0040c01c1451000c0c003107000d49440b40e5096000c03172a07072101040150b920401c5040e10000d07065284c410680030941d03880d03417402680503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 419549460 1250 419548210 419548229
    0x110c0a0b06061204120e1009051816230309031c02030106021f0e0115233015180a02130507020c1504030605061c02010516060905070f1d01 61
    0x10280e0b0588641c1c52124000c00c0102602e80000d241f880c0903120254512032a809400c449405d44d2005544036020b903c00c0683c41d090b140345603854241124510b640c110301400b01400e08078041a0301c0192005907100301460401142c0d504e4442c0c00b1100c00018501c0107142c101d00400c018810a540452100c400200c4203d004c25031055004695002d4820003040204079840e00c2c000d800c40562544040707046500010550451040e204440b2806941d481407540d00901e11440c02c0404041d18210403144469004c52629a40c20042e18a424000300f803101c1c2c001c035001c0d0070511003000350441e000084815048014a0030f55003981c0424400812840d68001055480300082e098900030b005010400074010300c04141401400d8843c42c140d080381c081501c4242c0f401000070303410704110424215000b208038401c2d80c0310480390b004454950000c01c00418008107402e4a0700040d8a90040c1d60103184540094603a0030f003002c90044140405500240040168031001040d4801900705941580c42000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 419550710 1250 419549460 419549483
    0x3041805060f0d050d030b0607031b0507031a0a0b0117040212241609060215150607140c01030203190506040e060708011703030403081801110c0a0b06061204 69
    0x400140c241c0b0420302080e03400140c010030035001c101011800568204a03901c2c1000025041000c1c032051b401500c2d00100460022100454443d083c3d20300c007a00ca5105000f111030580e144c0d074984d120b10f014080801e5200072264144050a81d00c0c0c0540d01e82d4000a2800b0200c030310003001c0f6072006d80700c040d1001e0301503108043d4400c2d0081c010300c140c0c00e42d100b01c801c1d0700d10080d241c040b00d40c900c8042100c00401c60280c200040340950311410200c0d044a034998010700420111400c0215400c00245c120780c1e130061000740c0413106446400152940c41e0107001c0300b600f0008080c000760309243c3c81b14001d604051040081101c41c45a6030a0b65680c6043e541c1c2c00030380c80e5142004900209503c042e200501c0c8124810407015560151105068685050700c440c061030b8002c0e40c8554034001518014085440000040d081c62a46a52031008401100010070f4120340c0381c0ca03001195002d03d034414082e030045800e50b420702c4112008603030400302c00e644d054a0003211104a20101c04050001081c080091 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 419551960 1250 419550710 419550721
    0x90603041401020a090609050402040812162003011a03190f06022b0203250e10030c020c09041e240203060103060803094203090f03041805 61
    0x225000303820641d070305008554620150101030240d1441d80300c2e407000503070840000b06080c2840d00030341d0304841503078000300544600600d416803560450703608980c41c0c50010002d040407400c11502a600380c0d901c0320003004c4400c039407010f250030b5401880b181d021400010304051030545001445000790b5800a1b030588045640d4501005144c2818802034402400454851030421041c1c0c00448100544803902032021030209400040c0e010440701d03944000300c090700082c0295059490403210709110314244440d0004007000890010781070f40031000080d130300e11007000402e404100c41400e00408032007080b141d2915a580d41e0103000c1181c071041065030008081c1c000c0000c2c5c1c548014005201102c0c03130a1240d50711013860000e400413900540013a0400c0710001d407000d4080100c03404800c01038500d00304400344d2640d00280c802c40001c42d4154046480b05000c0c00600d03620301c01a80c610514085c1c0d664201403810310b2074040d20400c84003c0e60402c000400003026003400020418a030910003107403942c1e41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 419553210 1250 419551960 419551973
    0x61205091f09200f030d02060615070203011404050c0102012d0b06070f060b0a05091308040503120414030607080106030c0504090608031c06051003090f05030c06040312050c09060304 80
    0xa0300ca0003401e030a501d005003120082d03e00c40140818205903858503815a0001c01c00d9900c000b01104480543c000001181c8541405200c580a04241004075850100c80d540400c0c01c40700b403c900b000b02c2c1182d0700f040c0004c1000910840c190008244020f000e02c4100822901402c9070801d0388050400882e034981d03141c078100d074001030801c1400405054840109081032480c40b881d40000b01c1e803a80ca41a194400d5203000c042200603540050700f07560840c0d58000041c0119078a648090f250803909000005955030104002e860380134451b2801901d90f4035041140da18118030501e660704c03030f40100c020043c0d5260702500c1c080c11903040f8540403d60f1002d558041d00e5501c219005051910305081010820100002c01880d19528003861100d241c00c00e940404200e421310b01171541c2c00100c8502052440c0d06c01e4001144c1c460081180316240e0666a8500d0310710351207411818044c0c1c001108000c00d25400c00c80e44242d55081c03243c00d008518000c1024000b03481424415482020007001180502a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 419554460 1250 419553210 419553221
    0xf0e0415060611070605030f040206071419051b060703080a0b060d020a020c0109052115041b080a0308012606070201020d0f0905030a05210a0204061205091f 69
    0xd0040042160300d4907400010180b050140e440d841900c100040056513a02c01c0003103911454800095000310380340c0350308014255001c20000e4481d010030642c104a5103d00740940c2501d070000c9210b80960103c10328005043c10700c00802d03c0c07180391913800c004106880e80021260381503814507000c10560390b07802c82a4018901c115a280e001800810a24000006540200100c004c103408444543e0312441c011980f1090740d00810340c01010612800d5020a9078501c010189091030060f9055100d83e0203805605050480d001d4030041050200101b850b0103602101010701000c8001d02582c010513200501011410300ca9018602504441d4400c0030640c441300b000344007140010740f900b600f0410002400707500066082094146001d49406009a8521904007610741c000084d60a00044883c00d84158002072030a502890070244440250550076111520801c4000b00050712281800b000604821111404000c403d00d06000d00180aa000075403902202d48880c1c039450180c42c90145c5009041c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 419555710 1250 419554460 419554493
    0x308160c030f0503030a05060306060d0b070201020903100605120706090b0313081c06120323090a0b07060c08090c040c030e030a080105150406091205120f0306011103040f0e04 77
    0x11442c010034000c000012000b94082c50001e01c06000c2c0c1d4641c8410175403294400d9500d030f0341c008001d11140000031604070200d58448018000103040c040b030140440e052040001c3d0310b40c03403285d850301c2c203201514001c45600c514803c0c440040ca83c150a00341c0c0038110852030b01616400d0b1001000283c412950300800c494130507401b802a0391514801d00107615007014000030b0350402c50820001044821007007040008841d050b980311f403031004030769058528440c0c02010700200d006040010806584500e00f00e00010070300a1426951110203003080021034888581c54010003810b14103204884078009250034000c4000c4a001401804c3e101c0182c1c010102040d00c6d2610b40404a10040d0480d003041010b4101d0300e0581c0c00030300340c031000000c00c0703030300d20035800b902000c0741e0202c50510000c0c1c541c8a00c1104240708604a4a4030302e000d1000b200e040d000107114800d1010000200510365074011805200745011000031810a4105000d581d103070041b0317010340ca00c0351b04407000107010300030b03084000010310b07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 419556960 1250 419555710 419555723
    0xa030c030803060406060806030c0909070305030301030b070201050c031018060302150711121c0203040f0b03150f010e0103020d110705010203011a040302010801180f1d01060f0308160c03 82
    0x45590703141110a68004940043c803a9180120000d00c050042c0021845011300030058540c03c0d000f5000c000281c0c40c041e00c03802d86486481804000504d0030002140a54083c0d21661110328003580001e003500c3d0000c1200d0f01c1158140f05109001003521400021703281050810b08448103194521001410b455002130350106940c4100041d0b182d454008007280e030702a042e070b580c034203a84009004581c140d1028180c9981c0c000c0300702285200d5800d40c1d0182c03a03501c80c410303030340391982d41c11a541b030f0f660302c03a0410380c030010300001400324098060030380000200e01a50b0b400c4408a500700043c040b81c0940c1c6845041c075400150903460708126512040710070300c0750b01a1645800081c20103034000d4109000707072106074801561010b024044103003074a007141d6050f034409400fa801d01d160109080001c00958005036181c03680d00405003018050300c0321900040041075801d0b4210410207094401a03030203041c0ca017813041c80900100d20792900b26281c850701c02913401a54070243c50f0403900040580e1015111 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 419558210 1250 419556960 419556983
    0x2180406030602130b0306060d092103020901080115120b01020a060608010b1008010e0a0f0b0d0b0403020c060f1b0a1202030a1d0105030f07031d030706050c03010f0b090a03 76
    0x8100d003640c042e004c48840109140c010036145c03108500244800d403055640484180300c420307c0c000143d00034100161040b12201d055001002c24024129108000c00b40801c0e004280ea8070380d540c1c02000107004002c0fa04080f400b80381003d1011b008101150340340040c441d2244110380030769000b000a01c603880e91201d82080b25130798070b121090081044041a611441c0b5442d17110005520a014a905840e0501c000000c0d5407180c02c40b03800281440407030010026100c490440c1ba076900c0c104903e4059002c0c1c10040c0143c81d041c50300a0074112880c0b400d03441000140309100d040304400c0280c502e0712122080703140810307030400f030420320344209210b00a1000003440d0000e50f102c0d6022001c0c000c030440e5500c0e85803152140e44c0703008040c04415002c0320b0000d44103000095041c3c815004598124240e13040000e0101d4011a400250113800b840501155000280031000c000e0948950b0f40d00c0905d01e8051400e40d41008540621403481d403007404120640420386460070b0390382d001d007803004552103015401c0b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 419559460 1250 419558210 419558213
    0x161d0102011b09140f1806210a03020c030303090703031d030616020106060f0c030807140c010e060901090c2d1202040e010b1003020d02041203020303041b05090a0218040603 76
    0xc07090990054404d0030455168290441c2444042c0b000341100003054400410780a404041180340d00a0116921441c40300c0708005207090b00d081c0041196140001e0044141e031410082d00d4000c1c0b44c0f00aa002e90700c10001c00c26071900c0890b20805903070303241c6000402c4100350400f0200b554602144290705002e14814042900020581084400d000c1c0d0000d00402d65108000c0e02c802e140c052015002c1110100e20300002441803040981c0003c0c21708000100000003010740c0241d400c8440300100980d920528411011400c111496004038400028480100036955040920340720748200d80e810742540420007200085600c590102801c01340b000460305641c0c0d801f144c20400031001c2640100c1c43c10700030300595081130103501800d15000e41500e07070400141c1da0480c0254095441411165030910000c2203030f80c0140c604002042c0280c0c0115100e043c24109003500f420300ca480306441401660b0100300d6a2900020960b01443e40c0d01d0041c0c6800690019002d8110300215080c1d01500d403039070200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 419560710 1250 419559460 419559467
    0x20622030213060839030115030311070f030c030f030c080d0c0f050c0c060a0c0b1603110427090f030207030501050c091c060204050312040509161d0102011b 69
    0x1070071a01102c0466045d1360310080003484282c0854414010340b800108407071014803081708100e80c0300202074000920301442e50303200d809002c0c250704100c0c002200e4441c451011300d0200300180140c0800040214040d2541d9180aa10780d11448020441082c0f40180d4040c58003400c0d40d080e80c42e8205090f980da0342c412110034401821204020b0010903c445106620140b1130000c1d1005080004020b013100e4418800308642c0340c00c0a0706990810040c0100e04000814400d5a1409801c0c150f0b6800c4080040440180549a0f607070b25012200c2c42c18041040184091051199104040300070007050340201e4811001a09044401038031020741107080c20704241d030003e545000c071303402900200000c0d190404024528400d51808961044180c5101c14411741605c1d0812906481088018605035072100401e0515800b04001075400754003040400503410001ea03944c2c1d00c00c45516600c3c5c11420140000340040d9005080c2d401c10b5400e00c00b111b074159000350310841004a0f0503134680202c2111400c0103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 419561960 1250 419560710 419560721
    0x1a0f030c0a030819052d0f0706020904050112030503010e0c13030f11060310031403043c05060f2b09021903080405220c090509090a020622030213 64
    0x1844d02c14402d00540c00e84503c20006d880240c2000c01e0f01c091424140103410891000a40a408243c6410400c2503003072800c490083c00300501c07440c00581c48400180820044803016071084410112141608000a600204072030565801c11440700346500c460b111419980507071146110300b40c041c824080103001c070400500001d64030802050340b458441d007040c0041808107581d981c0c80480030070700c00c1c80001c00519031042c04054440840c0d090070398510100b440c880052445555801e07072000c0c120740c030350440300e40b890010781c0d10303440411000e00e01070100d8018810984004000da00c046480c2c1072a888403400e8038420003074480c04460310740c08481e28600600c00604201e100c2e0441f038803480e00c0c0704601c42d04401120b030441e0005081614082c20700c0301601a00c5007400700010304505020504043e0b21400381c603078107981c0c1c0d441005410b00c41801144400130300781d01c00a901202c0d140006965410407111885108034080000050551604107aa000364000951000164201241d405c5065000c0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 419563210 1250 419561960 419561977
    0x7050a0b04150b21030d02031812180f0609030a1b320105120411040507050913020f09090f060922020415150315091a0f030c0a0308 58
    0x40001c1c0600c444415001c43d80303a085100d0f00036801c14240740300b41c0e152120f40040446000150380c40c00b012045170000307da004a4282d00d141800201042c0782c22400c000020030f9012403442d09107032130040c1e500c990007240c00b212228411400842c40e140a500c030f0030196040340303401604580c1011003038a403080c01c10020b404244a800107030640060703a84048900940c481d03907000c51041070a056000c419a6004001c81c06c1414018204500c441411007640d400784a0381c000c0d582a10170b81c0307034001000705031140900210204141481401420f075580a60b000740788640140050743d510450854407801d01030410340390303842190202003100e68514152030070700c10f5004179088a1079640d100820049454900d641a01d0b0104001c04880182030a078007842058a5920f8a1744001da42d0380c8801000d184214141c00002ea11403103c135950255910000d8003a1008541c00d1016280c2c440035404465000c00c5441d01c58802c507400f0340300a0b14280f05041d82c0c024080c26881e481c40d00c90500000940c0510368 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 419564460 1250 419563210 419563223
    0x50c0a05060f280b0d0206070c030203100c020c12070b0d020316170c250f050106081b060d020c030f0c0d05031e1009050709090501050a06022107050a0b04 68
    0x1600002444803c80c442da85070110074404050041c00c06004021400615800c0b80f10400d401016a5404010f8164103203c0c5280c0c41c011411403052605181074583c5821085050006c3c94400c9a00400d07a034014a000b560034000c0f02c11908030462910070194041c0c01301c1140001c44001000680d00198826403664148070502001204c044460012944041090460590109001009000041145203003a440c81d406558640110801c3d61054980440e10026111801e00c2002001c1c01060002c2c070200c00544040301c265101c03100080841300040b486080d000075900915031696056a429507420b0048a44070000100c40516940c06281100110f12890146550441c4544116442a0305504203034400106000889002c150060002010540031040114030b1040c103114141c8502c00c82da0316200c0c41131419071b00e4011140181c002c1c41c01102d0146040c410705800148400c8803200c810b040c0c1050100c090038000d4140a000c80040c2503003c2d5007a2641802050b032000c0780194080c0c076 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 419565710 1250 419564460 419564491
    0x100815040614010809060403140a020106051504140306010323010e1c090807060f0311091806040b041b05030405070f030507091802030c30060901051f050f01050c0a0506 74
    0x600c0180d9490003161f000300082c5483c8610317104000008090022200b01e0b000204030503480301c2c0001c88040d00519021500c404c0810701700140b29803c0e4020b41c1100080c1e010380b5455055032904841e070102146072002800343c18898200c2010709500040c03c511041040d142c0d806010310410141c0d00d122100c840020740510008205c0c1e94000c251b1400301d40741501d50f4424940c1c1404141e02808918800c0000c40c2c1c0184100300040c0c403040751a2804039080700a109440c64124100001c070b61480a40034066407904a9240c0b40b0100b41c1842443e46045060140e103d035164a02203141000396041280003102008002003005030001e41d4805803217603c1c03c140174540400c021000240c0b00c3c0c5c1000b030350691122108103814100781e009071100d80300080000a9140e80c1c031781c082d20100031040d030344502d540c8810104644840c081c450300350015504910706c3e218005000c4c2900d1022000c2c010700d841040d08076000703089607000c3c1003101c1b80d2107c40803e60300510381600380035450f00702c2103070740a84100065 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 419566960 1250 419565710 419565721
    0x31080d0b10022509021206100c02150f040503151501030c0f0f030b150d0606020a020607061109090a020a090e010501050a031802030a0c060201060b0304021008150406140108 76
    0xc02012118070141e030041c00c04840c003070302e084421050074124161200101c040851402d40300c3c0000d002c0b04040d442c130303000d040c1458000e2104050320404000200900c0c00e000f140140d139181340080001c00803907070041d02d40d41c2c16024000b0b00e204030341c0a15803500c83c1c640c0305c41360740024154592140b00c000b01080d00c144030080054003a0b6206840c00381c00a52000b44125400f4000d849040503401c881c5800104010800c01203156083c040300e000c2142c940109049240c14040e02810340541080d00c040c0071004084e50106906020740b0f60001c2100d5294401d0946001512045c0d41c01c2105c010540a8242410602d02d00254855008039002500d00040401c10340f140d00c00c031134101d48041c2d4510745843c403800803c0b0010105c200e0796a202a00415030701c0b002d039a042140d4180d40d0301540e6400004d0b803034481c01900319038444d4040f040a1000303008020250742c0f000b1030211240c807207041c42840c99540b40103d651145492000c01da01c50b2802d50049981c640d220b100008481081e00d8036a02d03915803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 419568210 1250 419566960 419566969
    0xc10090303030f2c0a0b0c044203090b01030b06030d09081f09140f161401121e0b031509031e040b070b0604060909030831080d0b 57
    0x522011580110300824401a156010340c41900c800f40c100240ea4413440c00b542c4401c9403260685d1000c54040c0046010b0104176946146141564020400f8201c035420700c81074aa10b50900e14042c003510300c141140c0740e0392700b4000d410031054175a10007000b1a00f1360316460f040c48070603401d0301c080d402403003060541740b1500c0c040d00b180c10981c1d8682c0c00500254003021090044d1490741e00b09400c1032034440b1401c400146030765511190641c44000609520704d0035034061860712014002141d01201d0249040040354410601c048240c802840c04081d46c45aa0361581c001e41515185000e04aa4442e403101100c49a9031001c000c10000300c081da0000750800700000013a1000340c035511990382007004581d6001c00180c0e11040c03002e03186501c25041642e12a851480c54100070b00c04d03140e03a910402004500d00d060320030400a07003040d5004000e98581500c004010b000010960316000b02c050b8000c060f01e0030440c5010030702c00303c004811070288101d49032540791074212518050b402400c120000945180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 419569460 1250 419568210 419568221
    0xc070803190609200c0304030206040b0711030715050304080418140c0a140d0e0f0307020405281e021321050a0b0601120606170606190806030c10090303030f 69
    0x1203484d5000300c44100d50b443d41c2903030703030108188000138403080000200580356280580002c00e80c00c100c131900d80b8013a003410240100d0f03111005120b900090b50030303c8841c1da94075010324020b06d2850590703100c1d61030b860400c69600c510b030000c400c004103207071808100c0d01d09500440d52800c048054035026841d12028684680980280e546c041030100e890740d094141610b019041c0025141c2002c25100c0720345d8445420001d030810340908640002803000c047d81001c0c0a60340c1c02401c0812100e144900c116800541c03082d13503001418989032a0800243d450307518039460700920b4040e813811035032407034505031510081049209491002c1c503550b1031041017005c20b056590240b85c0007400784c80380d10b100d60f8503410301c40c0300200650f042c80407a010484064511b4070415000e0f103d035403194800c1c61160313890021172500082a1921551007008000c0104400c130004003080307540c1e4200004103444d0000000d00300a44e9111880d00801d07a1030b05041da05034800d122201b200d0094408101040800c00000f05444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 419570710 1250 419569460 419569481
    0x70c170a03090e070e1e060f030412020703120f02071a0a08130804060f14040e0117010c09090902120607050901081b030103021c061506030b04050603150c070803190609 74
    0x11742c0940d01007450300708104404051141c5214140c4d00d020b00310009156500480081103600708041300300320070006020381000402c40140000c0002c2c6285954048002c00040490001c10142c0b1000e440b89600801c10720000d001c81e1400c03c240a0408082c0341c206402500c0440e000803c8030f404a070101d04003030404a81180c205503207130b14007400d00005403203445002d6103240030480a0301d848611004800094409014515081030480d40b4208a410380d84078107599a400c03917413611002e072000c16000000c03502111829440458913042c50300000d08002d010f960490315501650080181031907005009242e04042601c4585050711071b200307004181c0a142c600b000c14850200300501c00351801400c0c0c03030b90301190708058486100c100e0b80e4503800d80340c88401001e050844e0fa101448400c0c4c050207106482d04054500300114944400008d81d101d540801d072140c00414180410b400b07491000441d452130340c1002d80c1940d242000b030107142c589481c403030300340792003915140e00840c2070f1840740284802076 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 419571960 1250 419570710 419570717
    0x102010f0509032b0903020c01080c0a1e09090e01020306030f070f300b0412050c03070f031403070f1814010e0319060f05010b0c0a08070c170a03090e07 67
    0x9184001020045407850141940301c100480300070305240c2902035500d4086c400d13406008400e15007000035245100c003801445080c0401c0c0703c01940143d01c0842c44034441d4218103100708061050200341c440d4160358004030229414685c150021035415002140600e2040c3d08507400d10961aa02540300d45041c01902801e420401003080340d101621707005111040420314248002410050071511003010b1142220000d004008000c1401005112441046500d00b822850071103c049500d032a40704441d0300500013100750381030509040c0305047d005460940c1c0e0356019904e0428070b070090600071400c294400001d910860707000710115a595080d0407984003001c1d04d0b45415006005440307140d03010500c41d400d8411402d0080140340c9050013000800c0c0281c0c000507000a0450300d203010346205800c20100390300c0070041c0e190150000649183c82a81140002d81c480780140f41241d441034a03a8008100d0b18640c1d01480c141e0600401c56490140c444d88808200c0313540d50841c40a02d2801302c0c1c030800071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 419573210 1250 419571960 419571967
    0x303030a05070905060409230c12100906030b010e0601051314031204060e1c0308010e1518090c0901050a060c05011e090201120513060b031e010b0102010f050903 71
    0x4869941c101c01d800c40d415080820752151a8804206250443d0780100c80042d2a807000300700d0070429404070610683c566a07562390510308440b0f040d14503c01c20480b50101510000043c0001e18040003050150590320020b001083d030345d041c02000d40740280100036500004c0030200e281903002da022a5480c041c44402104e60504d40001c07080c01306031485000d80c0502072610b500484080e1500103001a00780362300d130719000c40000c900380a1a1601a000090b110302c54030000d4006c03e402900c2103044456048511b031047e6a00c0a09020141011054a81100c0034107401041e107243c0070b000c40d20079410721040314030401c1118200a6003179420300c03a4a0f0080c3c42010b041c001c591080400741c60140c000d01c00801d1809021880813400c0441d0681c0d120556500d8407400d003150ba02030000c104001941806000034200042c24401100a00070000d0205e652076682c0c0b850350306c09103d8200d644142e14101007a008040131940e02070003842d00158010b518089010344821014841c480c016403200303004609 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 419574460 1250 419573210 419573221
    0x7030906170604020912012a02150a0231050907031e020903030702090907061107030309120f0206030a050118061415041a040302090c03060306040201030f060503010204140f030c030303 81
    0x2980f200d0751840c1c104001030011b41544900340190703420342d601d154107500301603c4851500c40301c1052403040070031904100c0c0300705070490302185465089030048200503511003442101c000c250240e14001010000c00b01e40c0580c4156800101c01d080761010f80d0056019525154100c0886440301c8150f402081e1101541c1d1840103981c2c0900840c8802a003101d00d0a26903400007058100112001e41c00e40c1d01090f810710400d944881614001c050309401015482d003540da000d0802c41b418000c607032541c00d044280005200c0552262425243c01804265403824000b070303050040c01702400b5440605500e0141800f013215244903400842e1510502d404488506604000d003c01900c01c1c18803a10304288030200d400d42080a5200c001000c48200c0c2c0c0d0784503d1407060001254000b404003010f1034007441001800d40740480c2c640c0d8450380c2460001a840714100c0c042004103402e41000760550305c04100480c2ea40c0e040100d0060014007128034280510100082542e2080d5003d99250140c0040c4003192 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 419575710 1250 419574460 419574469
    0x3030f090b12100915090f0b0310090c1a031807050607110604170601140d030f05091305071812020d02130204090207081b1506060a091a070309061706 66
    0x54100003549401c000c441e0744c2d15010415105215401005607807000401c02141d000e07441000c4018203200e00030b001112012000a803520481c094000301c0544500700401001010101300020700524440040d801001c0c6803450b45a13001140c104107140c50040b080c1003c1d40700040d011013119030040186141c81c1a0395078400c4c1c01903107102125001542030101059014503195800790700410000203040320f45c509040b02d082240c000107050302944d15403094102003907101912250202103820034680d61114180400c40410000421001c51854042406540c41d44140c441001c15000300d01442c820b926054051314484114030025402000386800300300608044080039000341c2d13090001420300d84d0b00c0728800e003a0b0703000c1c0004075007801001403001040412030400e00c014166400040160880408051804c2c0740090500ba10416000c030b030444d91107110b8122a00501510810800845000740714010719410101d001c0780440c2c95030201050061050400000406a410907011b090702c9850510 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 419576960 1250 419575710 419575747
    0x301060f09180e10020408150606090d0302010e0d021b040504050708010501060504030b010b07111207050a0308030709080f060604180803070c05060c0f030c03071808060103030f090b 80
    0x24000e100c8a4200002c4020080301c503550b07485034604003c50740700010030b201420608402e0404094900c144400d1000c00800034a003040d250043c2c510207942c2d2103001c00200c0700d0183d00301e116803000c2c844144004042d0f040d0000000b18650350120f81e100303e0340d00c5069864403120b06500d680185100441d004038034050300006c0d0018058400e44090b03d407541031840c00d45900340c00c028081030740058204208480100f00c1c80c0144070001005003440c080d83d03215034400d4202d0200922030b82007207802c1e2800103004d00000004143c0180f000c44100e94929183d00709410407224000418501700d00001c80c41004100c0048100f84500900460351344c510400c0000c2c14032001ea001546208001c0000041c1c100c00114000e12054881650300e42c0c0600c0e0161920100070500e0725289070034040c0440242e802819260090b111054032501c0303a41b035176801c650b18042c04010030005400c0030f40000d29010080758003070680b1700070b54030b0411416540d001076450346024441c40d16609820001d15001103071030003c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 419578210 1250 419576960 419576987
    0xb011e0e100908060f1005010f05070b04020604270f0902091306140124110309120307081204060f110306060a0e1f080a0903211b120b0a0803030106 65
    0x803009103a183c1080a203810b80440d01c508a04103001c2c1801480480002c0ca100104002d00e41030040c60b18400004009000d288001406d000883c004101103550309000d840c06444004d09040044e10750108a180e400b50000040c8089850003603500491450b90080060f0f854020b8540d68450301c881d00c42c0b800c114082141540c00c00e55614080b0703004c41c03511554500801e4110350000001d00403c0c80d00401e26044040d21051101440300d8225041c004410f42d011031100f19051401b669034503407200c0c00e500c5003a03401850300a001034046481168061094000d03801340200f00419a0400e20503000ca8000b8080e104080d24107000052041c50034a0040241104520300080480b10780408a110501c1304035941d18140b0480a030064810380c01600713141c0c00003940c10140702d28400b68901030056103580340e411446c92000c40702400300c0c00d03440e044940c61300c2840843e030000d009580c100a08002204140040c0d090511441f0a801d24212100340c080c0c9124001440c60350b440c0c44000e8500b0000f4298 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 419579460 1250 419578210 419578217
    0x436060209032b020601030b0a0e07030606031a0c03040b0103020409060f06320d03180b0f070b13030f0809120d0203040b060105270105070f060b011e0e10 68
    0x128a242d4405100d614200b0b0705000f6070403010500700d60b8655030000c2c0c2c40c01840c210350164004002060ba41c04880740c004907482c80000348082007034040c5041502d15000500f40301c0c1041e000004210201c0e10402890800301072305840c6450300c03541c1d030b00390303100030745018240e003a5440040c80980341c00e6220b80304040c411000001c1c6c5425501d500d0083e907003140c0c0890742003021101c3e103921141140d400d92100803c00c00c80880610802c4000508110380d410707002d400c010000e080c1c038001c00f02680b004006460b02000068580007000d000c005c0c242c4c481e060894100003040082005110001d046003561903250b254080c0b40107109604586002e40107045140f10703c41c0e00c4810110b040850024885100b0781100903036240341070704040b460b50f1809800d450400004100d144105c405061020351603400c04402e0700100414400120b4030350247c01c60281000ca040c12030202042415405240201400e0b00c0342e440e00000b05441c580d6180c0e101e031145000c10540c09202c001d5103003d88002038000f4071400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 419580710 1250 419579460 419579467
    0x405060a051207090c050c120a0507051006060212030702030d0e03041d060301061d070503070212031608060919050c040801050405060907050d0c090b121b04360602 72
    0x100244045552089000483e0440442401428218028a0217800d85814940d01c0c2c4504081e007140d03074101e0b004241590b0000821104040c9101d1404c03900b4494101c000c030b030003082801c60203000400ca184900805482052544041c2125a0050742e01c2284103802441c11b04030300400e00e030302812042c03024840900080002180805105100c041500040301d81d484207443c0440a0500710341194000c522220380141c0881903002071040c07015407040061074503a84a45610307500307034030304220303410952015a004801c000504a012401100c1042c1c140e0b1131000390303150401030000c2c1d00c0301511a0141c5400b02160440c0b00803182e08902c0d00700b0803d40020b860160b40d86c1d05242103c00c2624102d69541281c0d091050540c001c1044034042c0c1412a5402003548013503032020100071441c402c0c0340203e43c50f0046404555904803080040f403800005885d19403000389405e003803418404155074030803132030310764424050b0303c0c1c4070766500150440213210326070b102e42102601e422180240c82159256001c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 419581960 1250 419580710 419580719
    0x31008030307050405040e060903090d05010e011b08070e0114071e0b0117010b031513020a0f0609060c02030312060a0902180f030a0c051002030d022719050405060a 72
    0x100300840c850040e0743d44107601d0303608140400c000d0b40d00c0d208080c2a1940b0241c18403265035404011141d08203021a44042c40450350b250485c05003500b5040803801d546041c11803080000d50038070b00c4000b02c0031b9581e04000e40c0e4840d5801c5d143c05009100390313800600c24500450100d084c80d001801c040d4025000e021507410b00d00d50001418220704400c44010043d240104025a400e4040c0c20100030305200034001c01d0307103407408643c0d01d14010740404200082c0c0e01c04142c050041921156401e90040c007902440754071000c0d070314980e1803180304c1c20300081c0c0c2c00b2200080861103980320141c483d40c02030103185040000042c0c0c00114070b010f0000c03a8020101e01d000150020310344010084254100188001c070f8691000300889902c1e2030355a140a600704c42c000800143c2042c8460090743c07c11200f80741090344207581280b85000349000341014920000d04840203c0925224254448004d01103d10941d1300409010141148800f0840c0c4e0300700c030700018042860280c000302d0b40020041d0800814a40d207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 419583210 1250 419581960 419581963
    0x60a02150618010f06180b09190b07140c12030304020607031803051c030204030b040f061d0309031903050f090613030f12081b0702061308060f0f1902031008 69
    0x3e80c011315114001c083e04103c000c0c1c11a0200b0030001451086440e01d03464020b84403001c2c403c030000644070f4280c10107568404e5844a9110001d040d1440810391640c0c40740c6841400e000aa800030050b80c4104080740380d4905c0c2c900082c05000d45070714040c5007162120390a0100b103800c480b104030140040e03003a01c21002c01c44001e040005500520003000c5801045610885c841145e04042d070400d030041006001040f180c002e1035802a61100300d21014550030308194006001d602c2c60301003043c2001584a07006038000001e4506000e0441c26031380114604203407071460700c0030705800a000c500b0a0103000c1e864000c02018112806014219915009042c440c100c401062a0001c603132001c11410200244054810000f00c05c40440c20040604d003455a40307540c40070004a8045c05812000904100715191034040e21b00f4941c00c0051403041980321103207551100b9044803040c48102c14080020005040002554001d0107212039489486036001550000380d032004059109000f86400c000460010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 419584460 1250 419583210 419583259
    0xa15110307020319060c0207061b02010306090f0608010b18160306050d0c090f0c05040b0702061b0d0206070311040e04030c020d0803090d0903120f09080303070c11060a021506 77
    0x620181358440341540c51700f03200321008114120115848001c080c420103410032081040801c040440da501c08085200403009020640c024a8055003040d41e0400349481c2c540052064884410007400424000700c14050303400886220286114070b000049240074282030701620003142189808146141c441d000708402c0c05188100b102c1d0b1201d401420000c032489032003900d5a220620800b0311503107002446c000c04d0f42c0298000c1101880740080c0d50070440d03407203d08071004140192400c0300c20074048200103483d1081d10500340d015009500010300500c2c4284500c0030300d500480002d40c1040c1c02c0103204414003800920072403d2003000764030f40780542d481144040195104401d060342c0d87c58604002418901c9907004103061114283d4240f0004002001c0040c0861540ca8032045400d4502c07421554060303144d215000c1340c0400410300c19510360200c0c00311221400392451400e44c454080501510380310f50200c01d401a00280c1182808042c00c2d0074941e00041c00401030100d01010307481c03000c0c4055 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 419585710 1250 419584460 419584483
    0x6042303070b191a0a0314070f080706080c040b12130816021903030543050111030c270a06020a0c0504020403081207021006140f0a151103070203 64
    0x5070605002c01c90304046004e5519810140a100c81d010004030020840a0301c0d1400300516500036080422901401000100000c021a482a1130042e40c0d403d501030700d60a99000320b10010b5043d80004403221543c804850032600103142d500e1034290403d8200101c444c015110007403d10340580d82c0d0000c988004040d05407511400842c1111034194030410002c103464514038140d031035221004002098010066500d01c40909480c01010a400e0030001c64a03903070032002422a07944500541120b191809420960901c90700003000044070505011500e40800c8400c00c10703030101000400007210f0117145184400c019920f02d031040200032000900010400e030401c1c0e006901140c0c8030001d002c10905100018078003a0350840c074003421501c0300c44503481040c81204940000c0750100312010700c2089a2a0500c28404003008029111104c591104480b00d20b524030445510040460300d24001605e0400c071142c1429070b10040120b18802c2e2a250500c0e2000f40d59408140030355000b42e2030600c01c0700c1c001c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 419586960 1250 419585710 419585731
    0x60a0806030607020d020a030c06090819081506071509150c08011707170307020a031421030a0b0402070605071e0509010e0f030a060f1d06042303070b 66
    0x2840c060081c185809001420b074011540a42c030044021034001c20518a001d40501c0c007590f8280030750402030050003601c031004010001c005161179000129519404440c4030b550f0b62006252a2142c00d5208690200812644010100880800a039081d5400101d9054035180030955a105449401c1416482d016080740507031645910158180d00c080d0850140004c04000c03070018140d003074000d07034030070b441c0c0a001220300003001500c15601e001c005940d6100c2e030040c8042e40564891403c04498013410b08007036110306c80c031480200701d200140315004d020608464103900b142d9505494a014142d500c803110742055080204401042150103401e104440350348030304641c484501c005c0a5000300100c5050304019082c0b01040c25680d02003000d00c1ca502044a9201c111080305000070700300041c0c0c1c0401029145820124002c010b0150441c01010215008100745000007880d200c0d1182001c9400505c2e0b891005540301028500aa1401201e0b400408030f90034034807a5914008076120907250075249 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 419588210 1250 419586960 419586977
    0xf06080c01030e010216080a12020d0603120c0203100b010c05010e1c1706060d110c0114010b040e0c0f040e130204060909021305041407060e040e030c030403140c060a 73
    0x507540c041c065840e004111000851500142070200c00b022411510010401c200001d00d0090442c811240009840350000d021035642511200040040c0941d1000701c0c1c01a5a5403405500640580550402c06401402400d640901d61500304000c1440900d13050603c8811002c85004c50780900c180004000c411000f030250340350890f80c02c01100c4645500b1002c0040001035080c14403402c03031031103030020000e4441503110440c03d50010040d00c130161500c24604008078040c0e404041c150807a103407980f000c0c403880a0503621110360040f03500c940c0c000c0c0074003400b042000c2611342d2207440040c055045e215a030039090940310850014621025141030403403c5418044000754602407140c54000c096520040040308981e0340401c600080002020071703040c0c2d40700002001d22600e4040c41030b41170100000e68100c2900d808001c0c00c0307442c401c04018040c0e4a010903030703a004880007003142c444c0c1c552a0021030906145035140214040d00c10702000302401001c0003c07100e9110400a002c25018684645070b4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 419589460 1250 419588210 419588233
    0x60f110a022a030718140901051e06030307170403020603040c080d0201140c070c050301020406050c0f19123e010903050a1b08040b03222102010f0608 66
    0xc41c02e10102540b402c03004401d8900076150340c0081d0314001c407200c407850b02121201d000b00d202c00034824840c2c80c40305810110f040094004066110900c1380035030b044c401d0705000b805040c900d040c52084400c10342580c0104048400f08041c0c0c070090030011040700305185840d451354040344e540d400c103440c00c5840681c540c000740051001480340c0100d85050344000c01100320f0007940300590030801b50440040100c0002c2900070305c507001070760b80040c001c083c00965889641da0402001c0f81d219280d0308180c1c1c0150711701d42c06241d030085080402420854215034085c400d030b803501c0b0320041468040d40244a02c1d1524070028441004414040c41c0603600d8468107040002e0400d000748c0c614442d01000c0ba450030b0640301c00250050140c4905120174a4003230030942c0b50642c40c2841c00701d0103002402c844004200001c000140000840c418084031a15005040b00000c000032901d01802d002014202c2600304001c60038800107848208070300d244004079502d90b6a40c01e0780100c401d16045078230550880514202c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 419590710 1250 419589460 419589493
    0x607060f0f020301060206010605030c0d0b010e0d08041e140411070f060507090e040c060818010908090111152d100503010507021605041109130501031101090b07060f110a02 76
    0x303004060f52b0034603a1451500c0406160b0500c160f0790310710704886d5102c04001c07969115409441400301c0160000040ca68641040c4c0400d0b00144500e00d20b0320382d0b48804240d011a0000c80c002220f190540c0f80d02c0724062201007201410303032200300138008a428820381c404505594100e40180c2d002d020002842c0c01c1883d0001c0241410b90400c0e46284008000e101c00240c4030242c41e41214a5440d240a10f502c4000d840084101911560100c641c01d2140c24402e0040480c003c20048609880b103405055015511548076610f00c1d4401807041c071120006403036898940d48840070500b035041481d1605200e03641c0c001201364241c0341c822550310390000600c02800d0900c41c1eaa04600389000808050034051503200c598219400342500641d1503515601c0c00092900542d14010b034012b014800e80d034400702e2880010042480309948501e01402843c1b07007035008035500420303544507000701c038a49100b03515098003401300414400b41c8540d940784d413565007010381005406500c000394040c00c80c2600040c00300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 419591960 1250 419590710 419590723
    0x803070905010e0f0f1c0803060907020a02011d0402130801140901020405221b11070902041203050903100612020103061502031b030c0604060b1014090607060f0f0203010602 76
    0xe05210fa07400004a0761340c2c80ba00c1c4041d0880d02228022500691100413800010341110b04c0a4255043c103540c0e0b081114000c0a14031652041e5942072843d95061800c998030405c03e9406400b06207141d8002c044c64800b035114864207200a00094900320304419031054642003544030403d2650b40320720044041c28078545140d040808080250b08050400c1c000070078a1000750f4107034990050003000031048810a03001548141c00103000e804000c0054440079000c40c01244001000740289500400c0100991081d035007500d44145145a0388000f503a4180c0740c030703804011800d516214091610250000d1801107502038902440032544a2a8034070000d4151005600142619501004542801e0358000140ca248543c0c02c2c640942c8000c902e46024110b209115803090345010b041c00300824001e881d001000503090907107031201140241c403400c50300400210b100c01c214400c200860303400d41c60102c01810401e070082e8000503c460106060404032006120104500384c2c01000420030990144540d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 419593210 1250 419591960 419591969
    0x3060102010b150906220609060f020f0705090717240607020d0201030519142d0c090a090501030f0507060507081204030c0203062a09030705090a0b090408030709 71
    0x4a52101e1151982003035602035014480d00030705022030f086036801030701c030400128885000f9610764056190380c4008c03c6103601c0d000780c1000c111600303e000241403000500c42c5010301190003401100307003000100b00c4450009408a410401300105410030380c11000440ba00901d00380b0303000e84032080c0030f07961446288a0407444510856042c007030030025071541480603805690900e00001c0d02c0d40c82c161500d01207444848005916882e044844860b00b0780c0300101401142d030a00d10300c0c46512070102615014108008e64154441c44001182c400c692040190645200040c10905502c0e10b8010020444038240d2080d608001c1d10790002c41440703024880d12002d840b4030314002c1c0c580805a111034071307548076000141019006042c00101407610482036006500e03401404c2d24828203044280d40030122801d00d40c0c1035005041021143c0014142044070019903010b40074100541c40c02c42001100940288003400941d204c1c4040710b400c1e55030111291040344616500e6481e420011401400c205440c1c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 419594460 1250 419593210 419593219
    0x30a1407030905121b1009031202033601020a0503150a030f0b090a0803041a0f01050a060809011503030c06050c0307080117070302130f0e030403020907080c07080f03060102010b 78
    0x2c040042100402d070100c1041d0b0022130030b41c1d194034101c440c2c00c038a904106070f440e190065080e04503182d0810740103590380074007039070300c484c1e000c00040000c0c41203110903078856244c230b03101d446001041c15141e000c0040d8050303540f00c000e15910440c03c900382680c0c0404e064200281c00041007003600050000c0d003048000040e155902c1c02da0039545c400d259803000078400f0348000c085000080c0c0d004820441244031640c03080710a900ca062500e0311550081403035691986c030910110014182d000310780d0005048820080201c0c2c16103142840039a840a40549002c2185d521180200201064007100000441c070a580e12034861300142000011540090007428520200b0406e20102660112501d07055403c00f600380302d80710f0702d00743c0d1b40b51a1549582c00207412204030300000c00203030031503880035481e004d00c15070600940720641282500e0707109030b01009502001c1a80443d231481e10036500c5660040380d00da01c161074007006486059880d0070248c8039103042c800001c1000084c2d40d0a00541500900c01d48 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 419595710 1250 419594460 419594471
    0x3010605030117010f1a210606060d091a071205010b071e050111031e09030703030903110f030d06080a02030c0f0a0b04090c0801060f050a0c030c0206030a140703 71
    0xd00da032106204000b8107405840100788011002c0d803000c0841d6640b140100711240054002020307070b0104407141c80c0f18006858a0301840001601c103511060141c4000d00303d0740c0c0d10780f401c00042d508004c0c3c1048040303558012550019013503500c54289100340782b20703030011442d0607180101490f104160303040c0000d00703000c010051340c00d481e801d6809181d404004105a0310340c1104801400700103403400341c070960822888002c5200c50100441c001c1d54030181c3c035048035201180e2080b070300c0030036501c00c81c61303900400000340881e109600c8898410b00c04d03c0e108840041c601496858000ca00d281201903800004d03048c12070002512039080200140406402c28400980001e600d0341025013005004601607001c0c12159a40c444007000035100c1012682d4955444000340350062000b144e503100418185400131440c1402800c0c0004c0520341c0307944076854448179071303012200d11046d90812414000a12200c0b0010782c1d84001a51040c2d009007000640130b081c4120301c400c003a002611640c10f051400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 419596960 1250 419595710 419595719
    0x9060613050d06020f0a0804140705010909051803030103052d06040f0503041503021e04030f1716060c180602070b032a0a03050618062101050709050a09020301 70
    0x1801000c4400440e9408103940b01801e03c0400307842049505140290b00040b0a100c89401100e2980900d0240c6900c100103681111260303500c405502070039001c110401c8080105034000d4020641c442400d41113140100b030314220075403a540082e042114640c220382858040b419488940c1c040800c0700a159044420203101c5041d03c0d0b120181014000024407034002c02849401c0084070010000c008031101c0030451100028003c1d0010740d424208442030001440c000860207007601c0070380b41c215100d00d07400e4460359a4161400d8a008004090003070a20071010031116250300844001e0041d00b000c5404400400000d01e0030704501070b4180c240d0348940c07003400030716800140d180581c2c404009660ba01e07201c901a5200d600d8202101c8074030714405520200e0090b007113502030310b5400e4040c3c031300b4490381e02c480301080203409a0101d40e1612002040014016103014031802c21000b4510110036805e0340d01c40d0509d401d40d8021a02d0f8000300341e440d03600300600d0600104013001002c3c86c16003141154100b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 419598210 1250 419596960 419596987
    0x40c0801060e04060509010f051503161116090605031006061e2a0b07090303021005070513080607020f030711100917060a0b01111c0903020d0b0105090606 68
    0x600804041152001c02c1140d80d071640d922850140030000d121303403010742c1e441000f11040011401550f006079180721a1711105074a01d004d89005070841940f514804503401011582980e41e8000e40e4035a10801483e01c8409200b0038004010b840c0c440e00c080780590900303081c14a84100c40d40d2a10f4560314005007046030710b520107051318900d0072440c08407440803130b20541125019800e0a81e0000c040e80825030184164110042061881c8034081100e00c0d81d560800950311b04d10a0720018016070055819400e41c401540d011552101040c00c3c4103060082c003168010284c00b0a80144000344c0c0100e040c44410750b01048501040b424203801140380840b40d83e540b41b40b0402d403c400601801155108070001ca00906908000e844c0c40150311800c0c403d0f80c480b20303650b5542075a1010840e403514101d071a05512031203081c440010b800000b0440144681b0444208071200c0031030030704101494002000603600c030b0040002c1070703025520ba0300042d41418100000448094034903841a40308110040131041c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 419599460 1250 419598210 419598227
    0x30307020714060c03041202040b010216060c0c08010914010e0a031b020a050d080406030605060f1e0c1f050c04030b071409130c0801090e1203100f030f11040c 70
    0x14080b0800d50b0b002c40c0b58000c107915000340b89082003d4007002c94041245204410305101440c0210f80901c038a101c070100691b1501d030b4800d035402550b681c01405011640c029013404041c0c030710032019884a0381d9030f4007450b421070b00c4042e4101c407074803451102c6807481082402040d01e03001f40702e805016800b43c01e980180c880d2005044407514503401402c1c200035942c2d40401d0708010107000e03041e16200301162a0000c55648980210004203140800c0826203081c00c0301510b030011114240340e89007840c447d01c0100d48072610052824401d90422080000c41c038240103900743c40d450fa607215500040007501c3c135419540001d154120800c4d080c41700300003141003400aa90420b41078201000f1904603c00441c17898812000c0e02900602c2e4074400d4034811115a06c80b00d005a6141e4602c3d0f072598807a0700c0c11040d04d03000c0c1e44851031584580445820304048100868100c1040625a59030340d40c3c0300b40340c880f0745406078001c3d950801441c00c5882809104911581c140748201cac0c1c00c101d1200c00342006000401d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 419600710 1250 419599460 419599469
    0x70c0321090b0d0b0a0503010507081f12020d0c0f1d090c0105040b030907030606030f140d05090f18070519140f070807050f06160207030c0b2b020316020303070207 72
    0x344c40e150101c21580b1240e02000107007801400174080751a0165001e0507503103090f05d800a044d58914440e003040140c1e46035200a030780104400004010013502044503a498029064444e613421503000543c0c0784041c081c0600400a9030701505485042c24803004200790300500c00001034021420780400c903a4440b04030b07015280c4081e002a10b0340c4690501d903203032006a8000030000740c5400c4c0040117000b45d103c0c01540b001d2184640504054080244a4865138201e00900220700280500320003407600580640312404080d0008030001c1160b0400c17141c0e150300340d9018010410000304465500c6c107003480801e00011a0910311104030a507111040c0910130307140310303502000c008200e03039003008a13100071100d915400808503403115002200f0325445810540c0c0e154070303400042c02040a000c2c0041a03620440341c1141c3e4500d000d80c64440e0b1100c1e0b41e0300110079003000c801620841c80315202401d2481210b10001c040050702c0e4030300845080191a00d02001c002554814820482d030541d00041041c180e8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 419601960 1250 419600710 419600737
    0x31c0207080604051504150c1e020313090518060406050a0b0102061e0c220f06030b03101121060a05010c1101030905100e01140105060412030e0303070c0321090b 71
    0x2955142081d87c443d1150450840e500790a000064001d80d500084c1001074940c0d0300f203608404668014240c0c0d51b80314161040360f0580081c941084040c03c582d008540c024a01303400b0700c003541100010755041500845007241c0c2555100c0502c0140300e130383c5c030030300e4500d010a00041078181409003031001c1c4042c0240407400d50302c40000010b03814110a100356040c00c0c1000319030340e0b920080680590704103110750041c1503134203021400000350340744203015841f522007028014019081900f45900c0240500011580007694100650401003001c140c0b0040580c4c014841c030401402c0c4041002102809540041d0400c44604109004510f5140b60005d07014000d0800042c00a4649005401c0510016100910518100f5051075080040d0060910340440301d03402ca40303a80c1c84e00204a2540250f0094010b000210820500003a00038051002c0c02e0200a081342c1c104090350752018900c9520760021140641d5880d4944ad112140d5a420038440c038482c1484600c45042ca4080e55450103900d2010110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 419603210 1250 419601960 419602003
    0x1141e030a08030a0203040b09030a09030f1a100609080c01050306270702210a080c070c05190510031a0609061b1e0a08040303030f0209031c020708060405 68
    0x650341003010072142039116034030540301d242001404e4001d40040303070151464800500083c0d0400c1000c41240e83c1d842c40fa441d9028501e046459091042080c2d00d0308071400c8030b0b10385020956001c040766140c880d00c1d11030f010984040c02d141c4014415180d0780c0c031100c484d5011120400250b81c0143c1506d40c01074095421a8441d1203201c940d0180070203090901615080301c07002c0c400c1c03040e0b01283c0da030b0740c00305a200c81010a110400041d0000e20844444600040241010640d48071054004095aa005008101e24240c44034000b40410303107590344400c5540c0c0f801c81d04200c641880e02d02d2491001c400e090400490301c0300d0485016090f0102a014480c0c04001040b0b00d03283e031440181c42e20b0100801c0c1000d102e12402e0402e0b696201e01190346079100d41103004140754030400081e040300440d4480481030415103180d03800d80161032072510f0051003c1c0c0074040505252420002d890301044415946144001062030203420003410b03420504907a004901000082840091200c0b0740101d000d030f55049 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 419604316 1106 419603210 419603269
    0x90605090c030406151a09100314010603020c1905060718060e060a090915181103010509090102091801081b1e1c1a0114 53
    0x1290740040000800241d029048204204a1007080e82d0b03046440d1603010100b03190319140074110b01c0e00810000c0c2d00b8507100c0e20300c40311102607042c2004044c2e03286d01221403891050103000145900080d000d803030503404100141c5101080038610000310b08a1a01d180c8a407001c6e1400c40c0003d07050a00c106c0d01c512582c44803c100c40003920741503c241c02400c00d0129035000318180303005211020f40001036074900c0e0301410b003414100b1450f80b07880c00d04114140c03414110545202c1c103101d1500d01222884c001c16000c40f419503000f04c1d04040c81d607a4503038102c0d029204aa0065400002c41c80c0c2c05c000440030211f40030306030b070034010a4031201d90300030481440940184851542c050461005203c030b514082030110324885004e000ca01408003401501a09030f0085042121031006000f050071500300f50385551800740030028842c50700c100c41d4100007009a44400312070321503031400000f5481c = true := by decide +kernel

theorem cover : BRFrame.Cov 419424460 419604316 := by
  have h0 := BRFrame.cov_init 419424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 419424460 ≤ n) (h2 : n < 419604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
