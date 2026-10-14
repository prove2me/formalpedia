-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1136
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:23:55.786423+00:00
-- url     : https://prove2.me/submissions/4ae40a8c-bd67-47c1-8b23-e1aeff9cf6c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 204136690 ≤ n < 204316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 204137940 1250 204136690 204136693
    0x1b020406030c090f06080d0c1502070b131103031c0e070e100923010e0703090b0705070516030b0c0d150b13080d02060103020d05160311030118020f01050c 68
    0x1c400030380001c070154042d04010000040c4241444c00c40000d55915034004d8103543c0155896250007a40011210200b075001100c64226140c02c0307203030784001d11032200054602c6504030309004201d002010100310032402608042c11500004e002c141d04c1e4480d401079800c11a8066410380303040f49864000d8420025260192014155074811404580d4001c58180c0b43d40818140180314003001d51003542050446040d504040300403144120002104c180250b101500c60b03040002c1540d41b003030700700c8c44007240e202d13410244a00b0680f00140c480e810901003100d842c000e0520783d003e400500c001c040102d9030008044035054440c4000d19a8651111032031502581c0c5410742c0302c403000b80440e0a040207000c504600d540e550000311401d8801c0120360401d95850700b01109079035203154005005410b498045440e40d41c0300304580f40080c40d124440790540b2242144034400401e120403102d088808400075002409080850071059518075442c0c0c80c02503102c251000c2d14401948144050712581c01000d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 204139190 1250 204137940 204137951
    0xa090201110109030503010603060b09090106200f0c0f010813030e06270913030e040b0639010b06030a0903020304030f05030d141302040c18260606011b0204 69
    0x700c00d402d448072080b00f5008a01d00000400c149070341032044100403e90303514140c4c2001c0b003150005282c07a0040c07003903404100016a195510035000c030a0030211002c0c000840e041010398901840e11002002c2e0b11900c581000310135803800b94002c00d005441944460f1207080e004d0501d540c103848140c07a440c80305401c04000d0040c110020710f4000c0581c8191320081e40a59031a00c10ba040145036a40100007203403001c0c03041441d100180d04441e060b528450115400715004a0030b03404110a4040d1810143d11a240749441901c5c84071003000c1c80c00e4600c9071005409800c0f80c0c0200079070030394483c08100c9400990810004441600d1079100ca03404034880d1055a14042e540e844080f100600e1090030366090b00f0004c4c6907011a4501d02c500c1d003528072648400316103403502c5c9501c40030310120040040d000d60740740c0005110552181c000300921300e00d103012404405440d0004c05403a42503410101c2c400c500450b0b000303d2009800240544140d00507926910000040315502d80400c14201c022604161a032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 204140440 1250 204139190 204139217
    0x307050702150d0632010c11060d0906050a1a030a03031d0303100e060109030209041112030f070218040c1a0d06060e041404030e010f1b080903060108010b0105030a090201 75
    0x20b000b000d00030000d800c00ca09150608011800c080390701c9180304100501c0d00a10740c5c1c02642c000d03540282d16600594841c1b020340501000c1380c0d0b148241c1030000142440e14001c2410040258885030081071104c42c20041c1c521001c00b10708000710f210520540c558004260325000903c80d42080c029061040140b20052606550880c956081500c40d900d00a05c001d1041c04081d01584c040c1da4810000d107410b0b0743d141c1c51070300825161000503201412103106030b06a0b03600f82e00c0c0c4401ea40c240e010b0702d2040360354804900c02c003d03041e0b4020040403482029042c107605c0d00259800f54160060b40c11001c10001e00340341000d0200b050801c021f0301044000d09110743c00d1480b4440c42000c005021640301c0e410010481020401114012303404480f0f10702039202031102095110414080f5980c086c240300c640c0308d103802000d85074040c091721031001032000111000100105040984020201a0100c0c0d60300d9888018880c00c0c5c80c0c80c0c0c80454001181800080c0d14000d0b160402207440340181096072026084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 204141690 1250 204140440 204140467
    0x14041b02010605011404180207050309030d030606020d080408040509040c08030d0c09091802040e010605040e070815150f060d0515130b0d12110d0f030c0302030705070215 75
    0x82080540540d5480c00108959600054000100b510301c84100c3c5c6014100200013a01d04014141d5201c0c1b69804a03000342002000c2049999030f1100904807542c0f01d10480d8014090f2040340500d1005018102900a4044c01402014010765100004908250400083c0880124020701c00e50b140d18240c1000190180700348002c004c1103d40440128050800c3d83c006030003070906601889600345010715850540b14000c00142d1a40d5041b036000c5042c082c2d0107000ba016080d540c210a0f4802c3c50000884c00d008000a2032204503000101503a0f0050040b4490907401141102c004226004203401100c00c0d203010350b50380c985048000c1c0b4442c1455100c440e1401140c40488125007510424009612945060300a42c0c626201a880900c43c5603501c2021800c4020b982074010204880102622411400394038030005a80264044800d500003903800102084502482800441e14140010102910030f0013141e10400f901e89407185131424a60030700444180910b02d03d003c0c03020900c00035090024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 204142940 1250 204141690 204141731
    0xe060307050a0e0f090406110903030408070305010e0c03060106051c050c0c0c0f0102100203090106091b08010e06101107050319140601030c120f0f030504080f070f1404 74
    0x8603a90760a07202c00814101910480000103524031800224004040541d1980304060b40541d2204021407800104600c0007242c1c015850f08991500011401003505080050454102d138010030007440f0400880354100e4a82e03488107001505a000480103121007401200104225070820004003000c40c81c20801504461080d90801d100b48400650011508410010054800b07404c4400345092044200081d540e034070b003406803803ea290044001080704a0a40c0144000e1800b00014040d18140310011506622185c4120011a82d00380000ca4800481c142d018400c141c080c010754181c07500c02d1026502c0302c08080d95580c0c1382c801d168010405071814402203801141d48040341c980340000e840c2c4140200443e44916550b40e00c00b4004201244690f4051003c0780c0140650680d407000ba818500c001c50158107025102c101e10f40e081008159100c0020400c80300c409042e5840e1003608820583c48120303c6c032030102d50b8030f000d0b801480f9010703150008800c008001070000038095403801407450b4200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 204144190 1250 204142940 204142951
    0xe0c03070c05030a0906180b04120f0f2f1003051911091215010b0c030706150509010501080708040305030901140a14010e010807030b0c0906030f0a0f0903050304120e0603 75
    0x5420f0041001b070303241c000300c140301c0414000380720200741824503045035294003651241da00394501c08082d0f0070034094402d50703c181c0c061300484c87c100d540000b0304100705402c0c1482107041e2440c0792401040128002c0e0010075001000041c4450b03030580007484200d000e131078040c1036a8500c081010b0888031a041d01c2c8615004081284c0302a51214800001c100659982e01011071083c1c015000c041e5403024400ba405041d07803549181c0c16220f2950114952846c000d40d02c009200d6850405482c08442d072448841c0119001110340060981c1c8503801101c2c00e42040d20700030049141d400c00305002174098400b856021200400000302c002400f044800f00101c10344244d03184582d90000007201c003c40210040c0580740342c00c0051000c4d45411840c40c1c0d1224544406007031140c0c0030000c500e005d140c0c01c00b2100031040080c4019107078140507200070152042650312386038a528200d005001341c10b0600035814141d4042d1206815607880307489e01c140c44546039100004001d20400022010307640e000c091405007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 204145440 1250 204144190 204144197
    0x403140706090623010e0406060b040b0405030d0e030613082b0c020109120f020102092116060e040b030c06191106060a0b0901020f340e0c03070c05030a 67
    0x62071503040043c1111400b9420b11641c2941d6064400303004281c14100e8111014991002c01555a41c00c20301c006280b60b8100d190803a00000340081e4852032940580b0075200118250b800c0410008400c1e81c0c41e00380d450a003038054108500061107101e011810305050b41c02060a145003901e10400c04124040d44100c0c400b461542e0909981c0d011410302c41e440030105c80b070000700030003621511044a0b000080b03040c08200409024040038880c801c0d01076549002c1d014008105036511105d0322000130710301c0303064082e8910902d001810340c0c071151800da000b02e400035207901d03201d0040e04090101801c2032a07940c0d9018401c0a003000c6007922064001c000c4843c0d0364507000712250742d14100810721601200054825400f8800b4805213940705400201181c0c140b49803655101c80c1000140d00300079020a12131014083e601084040c03511100740f036010342000381e0a0f12403821050040c4201c90010b3700982e03108081d050002144200608011500030b405401c0a41c0058010b50324607246038813464080001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 204146690 1250 204145440 204145451
    0x406030b010f0f120b010509130c0b07051006051c081c0b0a06031b030c02011d1c030603080a0806031501030501090b070203070f060c1106090715020d0e090403140706 73
    0x200d080f0401a20113801da101d0240c01e540c0d11a101c5100900781801054801c41050002c5800c0c00300c1c002406074159030041201000c03954468100003e070300640020f403444e006841403241101034521840c000e580c40108800c4515140c0580c00c518200c4002c004c4440050400410840d850040461040c0f44400a00403035a16090410700000500e01d0340400141410080100c45c803002c0c140c1310190070760091400094020010300c00b24090201d501c400c084e0b1421240700800b0000000ca4403d490f405003d482c42c01203210804110100d4509100c0a4a43c035002d20602907003503c244400c903000b1000600f111201300a01d400740b00c003135800b80e00803283c581d580c1c00740404010809490651201041c0059420b0400a4607102007140302ea0000030f002650310b54000304401e00940b20703c0c000b0000c800460b5070900d000b00c9070683d2198940188450001040d00000e1070750b200143d00030801c1804e55411105e0601c0009002005801070011014007803080c1c28440400303626000f414240340500400300f135 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 204147940 1250 204146690 204146699
    0x9200414040309050f040216030e0a0501090b030109090c08100605040b01030902090f0402041e02041406090307060f1202070609033902030c0603180607052104020406030b010f 77
    0xc0316190240840c00d060650204008a030f045089503040351000c0c1c4032a104a0005000074009200e2610400c2e140340d4180200ca0515901502c48043c9050a80340010f2058941c030054410603800d224803000c20b40200014031105030203400004a1038031440711403200507225410142010702002d040d0350015a18441085146002d02544502000c20b080400c4459a0b540203d503030040b00400350640c0c00005404281152216884116881c0d41d040b01d035002c2d41401411080658480e2043c09011800010785010500e8610211140428004c008200c201d00e858000e854070440d0302114002d00c42d84400740d07001000386000030424a480b0703140002d9980d41d5840c002e0205101d0404c00210f503803c4019003808210045001c401ea071401c015403242c0514a4130000e86081841ca10080d08500080705014010758001d12000701889483c05451079580c030710320211a1401407298644d44524054a0600401c506001c42d53f041070010b000401c2da035480713807100884108282e02422110007030070390800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 204149190 1250 204147940 204147949
    0x21e040b07021519020f060714070201030e0a0618020a09061d090a1e12081b0f1626090616050a0b0c03011401021b091015020c1002030a0903110102010920 68
    0x1079114082c1c2c2007a584d180c1c020039040403a2b01805600078140340d504c004400848004005a000c0c0301d510180138412040d480b1b0800315400507600003207009180d1302c1e0010a011020340601019a1303500310050306628070034a10041444006481344ca030502a261218000c44d44c00d2445400501680425001031040346c6440100098105168410004400103122040c0c4003a0902c070402e00c1910582511554800d066075490702c15486c0010101412031107882c02c21540841c40e600c1c0a010340081c0c4201184c4241349081d41c8a40c1007995031101c1e0402a2454090040e400341e04400d0050045034502021550342c03015400080c0d41c80b0700412000301c010800315800d1004070681d60000c0c40900350203c00208000030000d1401400c510078003c0320009190a010061128010503102030224020590b80701c001c2e403203003500103000d03000703608000c91483c80c58000403c407520381a0035034880750030714034686860f41d4414030341d80118115500d40c1ba5027804201c00c2c103510380b40900d0805039003042007080c60810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 204150440 1250 204149190 204149203
    0x50303040c06030e0705150d05041a010b040f0b1305090f0612120d110702030a0305070c0506030f0a09060b100206060f0306040302030f0307021e01021e040b07021519020f 75
    0x7810181003042c1c0506038040805c0c0b40e0100c0c5d005070707515048040074601004c240c1c0034078021108010700c0d050400c82400690001408048003041260200b80d0b2604503401052103a8045d42201d84201d0204011084100c8000c0c0710b0300300b4900d021244181c84100180c44407200307441400102000c6814003206240c0000d00b100d90300d983c070004081c071103480c1e444070b440707809207400003114036540b14104600d0300c12071000c4402c1e0316401015544010f03145e00d03014001d600000c3c0c0907569078040e00b001080a00f0048100e03402800d10009e00381d155a900c004a402400c1c003010304488080c4c41d01002c20031034440301141258114103401510342c43c0340000a203c02000c0088031603201741d120400340004070f0380120464447d020b120b18019600e5503a60003da00e0902c2c0c84081c20b408001011420740110010350103031080d0404401c0d01d802e0300c3e031780c05019045401280522611220100400d03c0180381c4941064081c10180b4455410203110414010f0040c00f1190528051303040083d00c0703100382800b405030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 204151690 1250 204150440 204150449
    0x6040b071406060a12060203060d0f1505010b1c0507020109020a090605040b06120711070806041103010506030d09290406050903241909061d0f0705030c01050f16050303040c 76
    0x10810249085074085404178104070180486a00001087c401d032a5160902c0318160040c0e81c134103090078146446c98002d550348101040c410b103441e001260754441c171012075010342180441304d4031995004a00c0c400421010b040513040d990713a80080e60042c0c40e4501c400c001401c1c0900b001820310315003c2400f0603182c4000722944240b03000c01078a1006026001d800d40c1100c4c039440c00320a09401141903501c1d2200b580c0014019100b00c008000401c024900c000495103801d500902c00c9403a420249541d175108900c070000030901407a01445030340c0b0000304443d040e451143c1205040381908111012a0740a078115400040700010302090b075007401c100003010608140300c10000311407091711800007a40090003003400440d5480040c50002a1900728141140d0410304c20004004110340d0b524200401002401e298003a001000c01d40b0900810b42d10201c800284c09800c407183c0e0000111860361041d2594002200203000c451300a642030301d4402d011a00c104000d580d2801c007420118001d0029511 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 204152940 1250 204151690 204151699
    0x302092e0305040b15010903060f0906181203050604020706021201140d0b0f0a020702031009030807050c070e0a020c0a12090e130f060605030114040b100b07080906040b07140606 78
    0x5110001c1e004131801341d0f2120800c42e000e44441008801241c0d48852544013904050501c2040d08480c0c0040d40401c1036184138030001c000c1d8400f80a40741c145081e44150180000d01600800300f0741d0703030203904101c0d07221200400046c54003241b40d5801c030880e040248070a104100c0d83c401442207040d540700012052404550303040d80a0b4980e500c6040d8540000c05580d0080d4214021074081840350b019110010b0f030080c00d9909041e40d40c0400e1000b8201d0341003d0b80010980c20211722014061000c0380c829076850405490b005003482042d0f804144040d2552a07040d41c20001038403a0072040c8681c404040c403485442903480720310180141112025001101c5040014080c0a2490400c00e54611f1040d400100c8646074141e5090006c000c02480d44074030340650074980901d4100b0b030741d1041d5920440c442e00501005440d48242d12170740c3c110fa801a41c0c9001d004000c08808680c000020701100c5100404240c40c0584603580907140b0382260740c1c02c4400b800c8408028100010034016550700150644 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 204154190 1250 204152940 204152951
    0x617060a1203020f1908040b13030209040b0405070e070c021519050d05070207060c0201201b120c0f063105040c0804050c220203010e0906010807061403070302092e03 73
    0x2261b5002611851144036400900020409482005600e1140013181c00410601c030514080c24529184202220201c1d81401500c2e4046580448804082e00420340f95580300300030001c82d801c0c8002c031511580103208007202800450314103c12070354159032198003650380c507444909481410040e504041c0100056401040060000c982e000c050401820b40910340328030042900c0915403203104402070420040e000d50382c0299500d01509070071010300d60f019107460302e8118800b01e1003504e508034a40020f03440907424010314054034020002d40001401c44c100f029001b108001c00304210018100284d40400e10981c041103c4c2c98648640b000104407400c108885103460f56401da05c60310321140540c45242c4c0075131500003606107244443c0b0080c03040304045549584031503581d1402c03402220780b200f2501c202c3c00003180075000400d2034022a501c940b00c00e0983d044104400d001c1da04003d0003107080550900440c80242d660690111680200b1030445141c0c8624295110384a40e040321000c05150411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 204155440 1250 204154190 204154193
    0xe0d050304021f110703030306080c06040f09050711030304060902011419050a051b1617030f033103020d03020c030405120102040b0d06080709060617060a1203020f19 73
    0x80c4550401a00080c2440f281803000040c00c3d030380e540c45004c6003c00761056600100c10035401d82e00a40c03d0f00c0740102103814403030301030b800c00c8224400d601070001e206010344001c100c40080758001c5a004400350406000782c1200004461039500103c2d0151043c1c0d0f1030f6602c000039940c02c00e50105110072008000c515001810485a04200b1032002410400c200001e2070414070344184240d50082c02011200c06034030f00e2504019965801c011800c0107a0801400001950180350080880d04280880510704220910381c0c1c0180c41d4100420ba05000050100064480303401c2030080e4402076443e0384040409a4107040003450001c0d1800c01d81c2c01e041c4100a003a005e80e5002003035908403801100d410010384001c404103800b80c040d507400b003030300480046954208050706400c04030a072601002211007071070703544240600782c031040d03c40ca40201d05c0c0d0080f01c403800c0b804800d401340d2100300a0b102c411aa0b82d2403604000c0d0446440003a0010382201540509000c1e06120754642403108120f4043c645086 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 204156690 1250 204155440 204155449
    0x50909040c1a16020f1903061b020109020d030e0d06020a050304030e0603070215040204060b030c0307110606090c070c08031b1b1807090f060905042003150f10030e0d05030402 77
    0x10304002c0d100301140420200380c0d030b0b12410f01d51401006d281a9641d669500d2030710701d010780101e080c0704014480324500a11518030510500015503001404605040340039101541c00418082e040c0350400107905900d004900d130341c0010325001c403c681d0380590f82e181c1410010a09010410100d04c195420014440f041d0b13400680e58032444001d1001d00b03660340b12440002c00401259200e6200f0b040301100300421852101d000c6d5208202c16201d035103d1426000040d40c5401c011030701aa4080300710000325800c0c180100140c00214402c19485901c0368852910600d182c000100c8400c191410300d10050000b0014481c580340d2003100a80340030883d160030001098004403103002446410210b0000343d0f0300344200010701c01003140040c126420b64541000419041003402a18011800d110031b220503189006100440808114000c1e400c6d600c0e2000118401042c03641d115a10403014459585141e440c050a014144500d4400003100c0c510040d80a042c2000a0070000030b1210030310420026894 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 204157940 1250 204156690 204156727
    0x6080709080c041e15150201050c0307030f0213090b190e07030c0c1a07081510050d0905070e090f060405030d09020409081c0b190b030403050909040c1a 67
    0x904a6011840d1102825010106284c2e008400d840c03030700700500b1000043c0b6901c9a04141c4881807140200310003441d00c10303800c0c1c40003580c619400510410001d42464420380c804420284083d5000d481c1200000d901000141c19401842003255100319403001c038a07041502e650f1a00100f004090450716000c02c2c1c0d220103034000d1a1009060b00c0c1c0d024000d00307174801c044080566600c1510b00da0021300030100070410783d800300e9010011a0301100030070001940c07007400c0c0f000b148005151a03000e0a5030541101c01d07401c2004c06038a20394a076941d5a00268050140c4400341248064172411031900c40400d13443d08018542203070440e0801010311000c01da001c0308813264100c40d0310011880000520100b00101080d0101511199004c108400400341e0002c400110a039002814481c0c03040784020041c0907040c00d914207030b002007245010015001594041c40d80940203052042c141b001440100d4200c0c00120740464060000140a0080030031002086040d450031000712400c060055098110808 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 204159190 1250 204157940 204157963
    0x3090c2c010611072102090103030801030203060a0605030a23030a1112130905150a030302060a1413030c11040e1608010c080a1805100b010e0607080f0f070c0b040608070908 76
    0x646003007603a005c0c2c02e40798980004541c0e000e80840704c99070b500e08004020070003c0c00102d210b4001d10700802d04102043c010340e0192500207011b00341c618032030342c6c1c0c2001c1c50407a03408840075081034410100400750144050110a20940c94a2400040c018a1681003180380000704103043c0082c0007400c400940d800701142550140c80b00040c1070789441c0c4004110409100149070302004a9401000301907020415a0041c640c84100303014403400c0f02c00e071842d03401c0701f1541441d0f01c42c0f503980d810021a104200c14603825000d10b6681c1c100400b004081410380317101c910262002c0d4004140c0000109001401c54001c01d00d030f1000f002004d044200040050f100030348403042c51034a400c501c4003052400d6900741070300c640c04401c03203522921088480001c1c0404a001a002c0350080c031148041d070030030b90219928603501c10001c40c41e0803000307015034003a43c00124410708001e03014804800000c1400507140080c2035941c40c41c43d102c2e898144001c16110f0000c14610802004040400c0244000518070f400c08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 204160440 1250 204159190 204159209
    0x40e1203070302070609030c060b12190602070b01080304030c06020d0e101106070801090605040e0303040b090a120206040b01050f03280c030c090b01050a080703090c2c01061107 78
    0x1d498281049029006450014000d241b500050313404040d040700c101c00e013091182c1024012044480204481015100f02402241d0840541001903900485007a0199841500010704000c841c0e00d5400c0000c3c0d00760040d03003036580001010b109002000d201c0d28000e110510003800500f0004800420025042d81180e000f4095003190712034140c080e001403070603007041c102225094980a007008003011002c0c42810f1401e803409034003180d0307424180103281107488000c00441ca1503c45035907900140e50001c2503841c3d2405031030400000911300e000c4540009105a00600c83d40c1440c0c1081c11400d881a404a442440ea10b4004201c0d520046041034040d400030482c1017803410780801d41c40c1c44010320320f8001d180c4030b200203010041065403270b800b8003522500c1c2800c00101c0301800c01511148140321803a4046140b400024050b43d00c2030b00310040382807103503040c0c0e203043d07a031451a1508102404d0f2842208100c90000042e031808011032140101804d19140c550b0341000e00307005440300b50600a14188 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 204161690 1250 204160440 204160447
    0xc02010e040f1401050f060702210a0b0a021309060503060720070602030c010b0d03080a0e07090f020901020d090b07030518030307150501090504081c090c060c02010e040e12 76
    0x70754507030b4059400b03070071440030034011886440a800d810400902a01d40300b4042500a6000e5084c10340c155143c00364007a10318041481d105071088810f030707140781c0c2d07842c0d142c40381e0341c1c1c03400001d0b1030340c82041d00803954001c003d42c88130a103d485100000b65500b01c1c1c0025840c0c0a010071040d5030020701c181d00305610741403040c0300440012020215400f16100d0558038425484002000c541c000300410810358404020030a02002004014054042f1500075000070b50003c04a062440e141c2d108083c0024400202d80c4c1c16a43c440082096039034014034165015030200303900c103c0307507018010f03441401200e14002507001d040011185150042c814007408001c0040355208480c0700c1c400303100d41d070440020102c5c1d449264924248180da116501d588000038140000090043d89500610340a140e100d013800d401c1c5095203040f4520000825040a03c05846001c000007246405c1c3c00300010b00708650351000e040c0580c0c0009040c0b440603501c00c42c061840c01070031445200000c40c4100114441d025025079 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 204162940 1250 204161690 204161717
    0x610030f031707020c010201050f07090302010f210b040f0b01050d151706010303110327190e06040e120a030902120d02030406090602030a0e010e0a031e0203060c03070c0201 76
    0x300046403203061100c0c0200b000c1800541034001410350b08140c0264001d1049503503614010501c2d40c8143ca00f800402c001d16400c1c801580544107005981110307161880204881c400300c807000803124903030000c805584000050623810203004c1c61806801040c0e052180844c201c00080442c4240340c0039040030b0b075903401c500c401141c008481000030b00089038046000c9070b4400003103498280c203103c200d0119400050f8102d50b032030040309640d14803900440c5140096110079402c0403d1407420901e0783c1c058034110482d1609001c00e08188040c1c43e082d00d0020051414034240422608011810384c81a8440254003200b10030303800841d510441c8915000c10302c9002031010a0192080ba40c00401f2402600c407003154250317001000d0001c075015941c031140010b80c0d52005a840344240350580d0000359840443c03540c594018240745501d4031001d0030960b0115500e0319540c1c141040006420b44070600d0039080819458208240380c0c1140c3c0c0b03d81c10a2550a2202d409882c44040c040000d0620515449001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 204164190 1250 204162940 204162947
    0x121a070c080d0627140114040c120e0703020f010c0209130204200304120c020108161e0503010e010618030b13060507030e0706021f020318070b18030610030f03 70
    0x3001200b80310006181c44d070718a00c801d021800030921415250000700100c0c090030010b83c0d81201c48080340101c9951407034040c0b202070801042000280710038080e68482c0b0914501c101d82181c0070312400307045050f04520402400d096055407050400021310b4076480540e480e44003068007d1500c07210b55500729100c0c4003241c0900701c40099885800381e08a80c411660030300381e004500c81d5124549120b0201e50103141500e611280c11006400035401c00001a0104070400c1040078061041c10040304000810b52004034440c2c62203142c13030020310044010010720a51a400d00e001d0303c032a0400c416802c5144440c1c02c070020a62001811030041680881c02c1800003d01e8684801d401640034007880c43c0544014016001180c5126120f00c940c2c0380000304c0a2000c6019802d2102980005500350025130382d40010750805001c059001d0044400f030308a03030701c0800011006000d00c00702d41e03445116030082d4120b0081c1c0e040070300d80207070011020019140c40550402c001d50780e00201800ca0188a41000ca = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 204165440 1250 204164190 204164201
    0xb10080f01060246081207030203040b04020d0203010b060313110a03031403130606091a0915150c0f061906060f080c0904050403081f0f050108041407121a070c080d 72
    0x42011040c01013100041c07014030001071803895040c88031410542c845003000c4040b48422100503080b4071401d03000c1401480e1440e208950540006d0001c20040d00002c0000d0301c50f44291480c4989000c01d10202d410029440c010220641007200c5854950b89107440160840c0742c29255102600c01c00000031303203840c8405600092060300004c041001c1038a884c445070040c0000000d40c0099130b0005255102894522185c500c15103400e640c2038400707662101800503505181c0080f00b940041404481031602d000c028445950960500505044c203149511028100308107441c25000c0d8240f8205100494128801040c070020901d0000341c141e660792280591402960300c0c0a0b4464100000e10040c16485210240200d9042e204d0381500c031140c0910004002d41031240d01e03078212103c5010031041d0702400d10158454040c06520441c1c6641500c118205002030b0810304024190a910700184805c82c070311151070101240700d200090070820005410710649807c001c203005800141c0019002854009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 204166690 1250 204165440 204165553
    0x40e0c03071a120a091401050709090b0a031b0306110c030a0e0a080d03090606140d0f061d0a1e05061305010213060905090604050610030b040b10080f010602 69
    0x14541401080900030f40003640060fa0f51b00f050803503030101c201040c45110300402e4a070f02c0308001c40b0b1500c0e0700c5502a0a00100050b4460300180700000480c3c441d61003040050310000c5480f0700d2504618288080300d01c01a001c000d680c0003403184101c0c2190000c02c0310200107075800c01c1a401060000080c11541541c1c003d02e071180a0f040d020520300f5019006103042c02d01c1400140b200640701c1c801552190b141d00812544030112603000004102d00f11803059406008100c0030a2a40001040d80459031058084110a61001c202107080c00b2200188645007842503203071202d070401d40c3d111941e455a01074220482030260b400440b080200960480b4041d210344244002a0350fa215809414100f182c8982805801d200c00001d10070b01d0700340f01d1248100801400b0b03180401e0350310011802070442401858005584031211070385545d41894600124502e59600c070440e00e03104900e0304011006034440c2d8150352040d0040c88180341c60441c80d01d03200c6c042b01c1748031940108c2404402e4101909650 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 204167940 1250 204166690 204166717
    0x304050a140105040314180d020d0f08030907060201020f091c0203011109010201050a02040501140a0e0307030b040201030b1801060c02031606082502031b030c0615040e0c03071a 78
    0x9511207529041d040036118034029295542d0310801001c3c9403901d40f08011206c950b002c90b05a204102e4038009030001185c60000e4170202e01400e03d9540c8004101101009481100c00402003005040f410882000501641e2000754100004090505010b004400716a846a840381c070442c1c0385120856001441190028000d120b0030040c01c01e414030b00d0b40015942c0e801942404001524000c05000710360890710103a464842c078400280381c403143c1d0f4011101f10300070051000411001aa02044100c01450190b140c4007401e0402d48000360494072107204442c0982e0040c050140c1c407400e0039240c20304540755802c1c41400003809200003404e0051811142c0c800c030110280104a02c1d0f4401d2a613480b884013044d43c01c1480002c5035511500c0c0c0d0002d24036030010ba008000d1000c0c03200003440c2c5c85071001d09100c22242860001c00340f20381854002c444408038000c00e81104890f91406014907014001f0800190690310075020100342c85400c07901071070000701002550415500b00100440318041003103071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 204169190 1250 204167940 204167963
    0x70f0609060e150a141603020306011206060203120a150b0309030d23061207090c09080a1124030c090a030b0c130e010506031801200408010608011803050304050a 71
    0x2000422240c0d07003035425100003842c00741128030001c421600180101b1010f0701040700d109001004a010b58001002d86041058502041c0d540405a0194201521603074000d103459040c8608012000c0e10020540012903003440e1144990900f242c0b150b0b800c0e0740400ca901076617580c3d111200351951160001ca1040d00c0d242585000864049442024088032560049442900c442c1c2c2013004006142900313601179040810100000c401c1035000240c030100b5070500400a03580c80c003046090055040060398551001d0006103042e2030134201418000c468a14900029841000048183d00001303004162100303001808040300e942e15004100210b6012641d04510300d050700101c01c03141c00140ca00141d1100950b00456a040400d06013030582d8009011107080d030342c41415400c02002c0c2659508110b5589160010b03012040310440e41c1c81040c5210003955071440c05e9150b80c2100e100c1c0d0711028090749050444e0714100d140030040d031080d036054038015490752500e05045041c0351904000501d50003201c0e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 204170440 1250 204169190 204169213
    0x8220809130506090a1b0e010207030c03140f120a0c08040503031303050609060f1306060305070f0501091a16060b040c0305060f0904050709020c031e1b0102070f0609060e 75
    0x740c108510400e0300f65a0469540c0f111100201506d03000402c8250030140c07400e40011282c0700e1803441d02980814412211180e03130f01c0d190b1188025058009445035410855607012401c420445480a8850000107101000101e4012a840e005031318100040207003842c812414040c940056801a120040640e5035a0000111410f058001440112034600403140010010580403030b200e031081a021070700084c13076501c02a00030007040c000e0310100c0e00c030f5030340d218044045242008844080e14510803000303032036810f2600250007841c00341e100504030f1450003190208031121809441078108544000a030400d407920303100300500410080c150b0005e10b00312400d40580c0e8550041c5028202c01e8401c5507000280c2c0d0300303008418000b10340190203640210810802803440c3c3d402006108581e00039203061100848500503040803401503070401c8880402c00c13100c0380514406544019402c0740007140707009482e0b682c55100c2d038103008010788002d0359403a81c001031026076000310882411103816100c0f1541f40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 204171690 1250 204170440 204170479
    0x18010c060e071809050c0d0f050a0506070207081605060a1e0507020120070608070e04050408040603050c0a080604110d02030a05010e0114060304080714060109061508220809 76
    0x2a119051400001d0120700b070004025201c2c1c401324a4000001d000701280e1071080c42200c14120908541d1448000c042c100444c0c02801240c10084c4902e0180c4040d00780000b0003413405d902e507002200d190b045030304868001c04121704581e00300d403001e07503405444808641b0300341e5a680629414407541c104080c048018598030000910481c2d100742c85440e407203940228851510003042e100c14a40d54810703c418850306029982c0180d00c01680c1c9003e03608268000c0101d0103454094070206c0d2190f40100c1c4c10b00031282c06018007640100f540c0103460400484020007009902c0150800b402669100c103800d00c40c1c1d40704c60440c0e03600421003030295903030304000600c80001c1c0400d1103080c2080760f18100101e100888140c50315469400149041e01750740f199100e8007919486060122a039490340303009600d02034018810280200540580014964585031100c80324104908001e420080075004101c2010b12000001007424840780892040e4209860000d50b81e220f01c0881e580e01440d404650103e8070b85 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 204172940 1250 204171690 204171703
    0x70213020a031b0e09063006160221070b07080a1515030e030d06031407050a06050a030c030e0708010606090e1314011b030207020405100303020318010c060e 69
    0x907a6001c02c5200f400019510740c840c5105a40d0340002c0b122004680786182c810840394021500404491040504014a003114203111848000004101030103000c2210140701090303100141c071301800a0852858802516256640f00e00380e030011a04540620001c40c000640700311039480380140a803402c1c42d05010340304d40d50494080c1002811718403900c02c2000140300c89000c030350380e03941e41c0003400381080c0058001d07004150174200580700a001d54410300f0310074010304008502a903113031201101c0c404161070621b000381e0856802800300d84802c2007001d80c04030403600303042c00a1038000340400c50320408501908030001c000c1d149100d50400804c211006511660031075529485400c242d40d41c0781480c0078103c100301d5440c0d03159407400c000301c0d01146041c100044540c0d596000040c060901212681c0ca84000da034a90300026401b0403141d04504007032040360780110444a80c86aa5840d50790021340d2442000c071a19030488a86a108035180d0050044d20111f5074032280070b0080c403100801d000c1e990305 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 204174190 1250 204172940 204172957
    0x201140a1b14090f0f060d090201270501051c050103050309100305090a06110c0d0c02090105010305060906061b060a1b0903120305100b0c010b0a06110c1507021302 72
    0x3416044a0384041c02502c1d401a00718041d105541420040401c0021014620520541250160500d06002d5580c0c40041818124450b0001100300f424000106402c1c50101d080307840f581050020460300c02d4115000048070b0007481c0160340c82c0c10382c032182c0700b0440d99580c00d80c41e0707141000004010810040040e201d07510003a03070080b034030b4005140d0880c15035400340c030640010303009154140c1c08a0351075001000c02c11040c1a07075500c0c1440c410f040034030307010483d401362000901e00304201007149408205280102800d19091000d4184080080e03c8104d000d000b03248540c0000506840074908400c010001c483c04e0010b9840c0c51822103a104080d1401e41800c07015400b044041004640c01580410150382d081141e4080102c507040040d0010072001d0032810308a0000100010311074085001410302d10f071507200125100e41c165050080d03c5020f07401c4501406000e880036201890009054610b81008030b03140300071225100c10300256803003a0040650001e0850039000c00900a075001416002d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 204175440 1250 204174190 204174221
    0x2070b090c010c0b1305030c03180307060801030206030f090c0301060b13090905031c020412030e040f02031902130503010207030203070b01080304050112020d0f020c0106050f0a030507150201140a 86
    0x1082601c004485001c442d110080070303290b00002203070744c0100d80019a04010710640481e490207009400045c9141c0045901002811129a012045080c10b0103100000d00f202e0a000a00d0350446e030010b512400010b1001199022034000201e9010003000f05940c4540064001c00c00341d500d501442940e0b41c0040c540c4070700e03000340340d000161001076441940c011036000009141045d600041903555903400000c401740090f001c0c000490300c50800050a498188070303031180c60341d00d1f6000b4240001d075042e030940004404e01c14010851149490309020018150000d001a914114005030300c01203252604180d40640c408180c0c1c90801d9000002032843c01d006940705600d0303a03600c08039130b83c0c8c91040c0d00810f400a03220040c5a40c000d556900074190f44004680f0104140250090070412070b00009100485c3d84e444000400950420581500342480d064401001250460700c58558628140c899100c50b14000d0803003c03503451003940480c0500c0e2115a4010650401e40c80007401380640c5601c05020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 204176690 1250 204175440 204175453
    0x1002030d0b06040302010215090f162d0506070503070512070c1502030910110a0302031806041a1317030a140712080601120203010b1201080d0915050c0102070b09 71
    0x1180b411000351030489905900501154209580c1290b40340005000d8002c2d07031080c5040944003000501441d211000c060348400c07080c80c03820842013410140c40f48003004504101d45480701a000c40c0340c0020941d0000d0ba40c50f030383c591841c03409a01c0d511a29201030018090050000d001d01c039580000d2217014041e43d0201c0c00c4544800c2c0e107124071101360426202603031003004410030701d040407066051458124200300e0030f407141e000798490070140b0344841100141c000041400c80c80c204017000703100d0300b9415204203040505100c546019404609c103001c0320350304041904440c0c00c917210b47c1c1030082d0603255050f00c29004c0a0f040580e99070003800042010440250820901c90008420380e11025000031841c9820300c81060152290700c1c1c0500114100314544141401c81800e0340003e40c020b100c204001c030768075403444044907284501038114004d82d03004002c031401c030a503000f900d1406846200d400c1c00580d000414080c4c440b0b219290205006500104075107052080c0ca198140c440d202d01d4040e90030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 204177940 1250 204176690 204176711
    0x9071103070b1528140d140d030e0a0206041206020903030a0e040b010305130b07142214090103060c031b02060906012108031e01030b0403090906061407020102010b1002030d 76
    0x140e403012000e0b403010394600785038101301141154507210085040541b040200d09141d8954000c58081d450412031640d100c20b00035414035502d44544101d032011b4134050210414141d00241c01071096204850200703c500201c28140f107102d074122a11900024101d0799100043c40e806800d12220080c450720803882c0022800140d4000d00030b16114807044401011080c02c980d844085c0d010001d05514204549035440d03646000521000304420b9141036800c201104000c000aa03442c035003038002c203940101e03550105015440d03022500d03040d00d500c2030f00414852810f90003240148030f0142d0b0343c240c019a03481e021000d6900860014095074100c81074070f0881c2e880d1600c03428030003140800000440f041a41d00c4011400c038401454000c1c0054030466815548405102c41040c420b810a860510f0100e0a2004164002d100e080080195050900c030051620401078a011415040024400304c00a90642160f00c00e40c80003102c03d0004000d6041100382a80007903a0360080d02070300c0c600c545041160903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 204179190 1250 204177940 204177979
    0x40b0103120f050a030221010f030b0a060302030307021201141006020f06061f120603050c01021504080702040b060c0604060b031b0f10110a030f03140609071103070b15 74
    0x301070002602c0306450080c15074801c0b4001c7d442211101001e8001040e6400c459044c210b040b4003c0c001403c08007060f0f81141045080240094002c071551880d101c810030040c0c50200035580440e4040310754124054803007180700e01401089100d615248124010840406584100102500e580c0ea00300c0e00141034019485503554400c3d10b450341e0042c560319030700c81c80304d41c8441480c1d0807041d140742000482440d0b003010026200a41c2049030366411201c0c0540740780d41d04104000c000e0303101c804007142508294660180501c00e0010181c0955210100300c40e0300e0701c0d8001102c100c2d400110844400d49818107240300100360705078400d44203024006041035944070515003110b00090050041c45c3d2041c12074100001c3d0701500d1030b0401170100d51020340c14110300c00d01a031500f080c006e813114009146c81b40001070440d200c041c50001131007004410f1000989541940d240e1008590405000051003408100d00c3c40c01034140043c0900b81010401242d00d18013052400d040d0011b0302d80c04141503481001c003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 204180440 1250 204179190 204179207
    0xf0c1b0201090306020a121d0c010207030c0902160f05010515180f0a09021c0507060801080607080c130f030b0603010e060c070c030f03020606120304050f060306060c0105040b010312 80
    0x181c0041c0407824188003150360f60b4028003244002e07080103140c1c46d203c2503d0005071460800d00341ca02c100c5110003020003880c180540c13405104248007906200c0e0030744d0382d4507040311101e01400100c1640862500d49030070141c00c1441c1030079000030603030951050614086000c0c000c03c540c1c9141220207031500801c0d5041c06424003060020000011916580324128601d400714014240308080da220ba00c0c42005d03840304005502c10001202c0b40e560142254203015250401d42d901501c1004401e00c0104480800400c4441e0840410700c1d001243e51a0800108014010500142032a150041000804070541c0092900302d0307114450003104c1c4d079241e90425088840130701c1600c0c41d680214001540c03240081000f407070194031810140d10709a80301d4032016207a5000d5541180964024400e0068514203500303080c0401c804c501c019860941440c0c0418030240081d041140130f0040800403c81685e5140140c5821100300402005146001d042804a0350028401507138120f4100200c1442c0c0c9200b101e64 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 204181690 1250 204180440 204180443
    0x160c050c0d29070e0409061103010b1e1c09060b150a03050609161b06021c051b0d0903050405090703021b01061d04020d0c090b03011116061107060f0c1b 67
    0xc04d040200e4038400d21002c0c140c1c484007121244e17540e03e030015040e40c01c5406140078190042d800b64644840c00402000790505000d14100c030384083c000e0a18881940080d1081c0341441c1201141004081c64201d0143c4803180c032099000f40b5041c840c00124081a003d488030f00308a42c0c1c2481903843d00c4081c000820320645a200050703c91504c1403034140d0003403601d0385000445080348200d20040e5143d007400ca070410500d100800c4d0599400301d01c2e081480c01010380001809401481804a89040180c244140c0c041d01041644030380d901d505042c000c030b05443c010400a09504842e182c8100002c0082d8080e0f250399420700050f0b240d08a01e240c0510460b81910302c1d00e240c68511800b903501220340444020300490b40003071095000c10000e1300c0008183d000b40325003407010444130900c408041c04c1d2440c60000311124401404500188070302e425140c85000c1c0c101a001407110104c5481c0703141c522a009001d052141416101200c0c1403155100400c05001951070402c0f01040c404c590080001c00b060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 204182940 1250 204181690 204181697
    0x6111b0609060f04150507030905120718090c080105040c0f03080a05071514060a06181202011701080604060506040209010c0b060418030503011706160c050c0d2907 72
    0x10720321050a0076402000107110500040341419074612507294601d541c0304050000842c0840c1d61400c15800c01e50000103440215120001000c907001955a10202c5103c0c174820f85410521f03050b0304580c00d900070003a07950400014541a62101c080501030842950101c03451180c1d94400140c3e0b5074540d0151003942da000421074030b05403410404179599040008142e03215510301021403443e54072407042e1a00b491905100c1e004030701d0b002d800c00c00100d6042d0700c20070902005280300b500c4000b0075400141528000800000c00000030700048031901005410171440c900860300105d48040d00103403061180e44204c0d810301c203d90fa01c900f88410ba006030152540454000383d41200000d540240c0203a00010243c40042e1000501010408801c15014190082080080184075000208464903000c085d41710050509081590405100d841c8001301c410800074841da4440811105014620b0f01180051540000828074140940701c3d4654501079010030102e160008003021204080a104011545 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 204184190 1250 204182940 204182947
    0xe070503100b0315130e0c04050c0d1d0a050f010c0e0a06031d12041802070201080f0702030415080105010318050c0111070503060a0c1b0210050f090a06111b06 70
    0x4a032820b0540003d0b0400d840c052081280407a10b8071400c880303207460132041a0200d004442c0944880c10489808003550140e810b00e01041401115001103a44000481d01d001071540255903014114080b49003141d00240a8802c01d4001e000c400180140040e41d08170080012410342c0c0005c0d50400301082080750400c0000f0020000c0303600a44c0880142440d20000700a810001d000711810000c0c04100b44180040101d01840881d040070007410b000c455075182185403c50310f0b00003070b0442d40024449110400002d00090599100303100380c0e4000d00c56020281500c54498001412009007405807030700091803c1d00e090100030681c000c00c1e00b6641c1080240207026021401180d42c0640710500802e00c3c80381c0e500004290700c003089110b00c1b9079031000001409403031031400103100c0e413865051591015a070000d49805a03503103072807074040864142805551401246040c2555009640001e40c3c050380050000440e02d810402407000125402c1c140e40c4a000c02c9214042200c1801c20074a80140003030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 204185440 1250 204184190 204184199
    0x714130608070513030302030406030b010804023001020d050f070206071d0630010e010b04052e1e1404032009040c08100605061206011e090e07050310 66
    0x100255600044140351044c607020705203881c980c280d41e641e4021801a807000070304018060389482800e418403c2440c0c28002c41c10680c001850010409414100d1484248522411403400c58020300d0745c1c41c8460001e544030342400c0b107043c000308002c0355086a00881d0b200060281d51011401c54031884c081d8442c1600004000c107800da10545181144d9044401080070b030210250709142046510480c0ba8485940d03040c020100c0c01c0d40d00103a000b8070b4003040000050248a003120242c1d402d0340c40c292101600700001e5011000f00f4121a481c05005140108130700c144d140c3e00807420003060039848884507003422034450071200c00c940051002e1940006000501c0024004007403101d0b841c981070202201141c0c0da5000a414950035142103030210a400010003078400203000640b0a00b0728580d0410541b0302d00f03130100c0c046100311800d0580b0610480c0004d2001c0c1e000e40700e00b02a9040c40c070700e0b80303c2141503100050401d83c418042e41282521180c0082e5090344103104a82c42117201c4100d82c826140b40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 204186690 1250 204185440 204185447
    0x80601050925210e01020903070b070203060403050a120f0207050c0324060d050631080406080402030106090c0201020a180302101101110a0509100c030503190e060f07141306 76
    0x8810002c6036901500d0a00405400f240121001a850381000680c2d41c00301604040c500101a4040703102044240b00032000f698010907442c0e8007a805050240d82c0700e44041040b1640100003820094091a2030310040080c01c450b4094090141301f0800c94904070f44600415640b03102c000d81b00900c0d981c0c0c0084840c8001e442c0540f440c2c110f040500441480009540d4140c14000d048901a030444488104814480080c46080700c079505500031440d0000440d4555007150304c100e016a1051051810204003103403004d5102c8002040c078110200b050514440c1e00074080d43c451008034001408419410250558401104003220782c018180100c4a15055041d80c85503030f6040780069555940c0e504d42c4808a6040c01440c240f2800e07900e0958580c0140304000d4024017000440c03007003000601c041c0c40044d030400d0890350031940c0c881d4022401c80c60303007a4030006400e10035640080350060005100c501401c80b4580e40c0221700a4a40f000303c48280000381d61300d80542c003c045070860390100c003004050f01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 204187940 1250 204186690 204186707
    0x60c1104060b0f18060703020610170606010c08070b1014030102040803090d030513060f17060d03030b040b030a081305100507060b0a03050f0d030e01020f220f080601050925 76
    0x2400c1350407988006180c400241542c001d1074058026030000010480000c2c4201d84440185c4103085103150003503c0070040b140d54103802480d40b41803164074010b035000d00000f80c055410440d0710107881074440c680058010100c0340a4482c0103406a080c100d8401503107018000d4400f9900f0342001903007481e2000c0c0402c0945039071072000742d0500030308203c9071541d901060081c0010300f086441e842c032003004140004141c1d000d51200c215a0032141c206102a55452103a1101c82036014035010864502c000e000900509800500e158903200301c4a107001001100c1c0054100158400041d8807620b50305e800b07000000c5801e124410000b1800c01013103000540780d138404070076a10058408104a5241d9803550b14010b65034460445540c800a1410141645806040746902c1070000940c2051213000090f20346000d5412003141c45114802032003030782d85032220150300624003103115401082ea14001c1d03036219a400e015030b80c0503c8180b00041d45444c10b60602e442018008031140c000141e10a10441cbc0c5e246 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 204189190 1250 204187940 204187957
    0x30a020405150405011209120f03060b040816060203070302151302060c01021305030c0d14012d0e03030103020109030b040302120a0207080609060c190201020c0106060c1104060b0f 79
    0x590038400858161292890100200602c255a9030303035604150014181c13611070300d00c043d140350030a0900000100c986c020200400990f040c10110f504004070240c2c040c01c00c58003e603035000e60220b00082e40410001e0b000001500c240c007008051600d820049032284a030f10000340151307108421038040071762500140c0381c0c000c500c03200f0980c802610f40e0006800f54007220700b41d01d944c1c0d00410f01e958090407840700940141000c6000304260707003400020400c400c000b08805461050541a401c084180c290041d0301303925025000c5140c108505d14071000c400401c540c04a1382d0501c3c0c041400400c002c00011030b8180d0790141c407020f0340d103403640d5241c490109004008400710701600d15000301c80f02c8054043c0000e0b5601d50042c0c01410305015150b4074250b03004088007440c0d403015041c8030a01c80248220740c0b40495000400005c00c40079002a80a0b1255401c50b0040f580f030083d00085095006101e004d0301481940d40e2030060703504900f00429240c2d5400398014840f0200283c0384c005180e000102a41d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 204190440 1250 204189190 204189211
    0x61b011a0a080a0c050120150a0f06141504030c030f0507080102040614090111060109020c0d0c0b0402040b150703210213170a0204020304080d0c050304050c0126040614060a030f0803 80
    0x442d01807112309014074680a4095200c600b4103010341e417111400741a1780350340c5005040195a191940f12280c003411059000d00a064481c142d82d120103402e0202c8001c0e54002c2c0a1b500000e907649020b29001d807c6801c266050f000721200410101010300880b82161443c1c0d6440030328100f4250040b50540c03040808a06200e0720044546441c0028080d40303008042899006888210324145281004484400b05041088060b8070100041501800c0350b08180c0603580042c07281c01c55004524001300410a1010180001c25404101a40181d0307c3d8940d00c039018031010140c9c4d000e814003041e402051840002d07141a24814001d40000c0704c4d1000d000c42c4600100c482d200101d402142c100e81c01620b06417401e81e0005400c0b04500101e00a40851100a2038034a286240646909460300d825104803410008042160154498407091903000c00754142000840d0b820140b401c080180552996420325840c2d03a400550645040c5456004803074106400011219065966034130300d80c402081e58844 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 204191690 1250 204190440 204190487
    0x2503020105091206090a05010606030b06030117010b0604080127050c04050c040b040603020904060803030c04140102100c0309020a1401140f0c031204151109061b011a0a080a0c0501 79
    0x108000300941406408800080c0221b41a242080c40c251056900701e00c09060419507140d4280c0c8032402100d044402d58501e050381503011a40c043d0140000e140b9a59004102180118032942c041d4000c5c4188200c2c8581c5023426440918403a441440c0f201c0c000e0520b405c00b040c0d042031820300d074100300c0c0d2014a0074501d07880d164803500d070110190003580242c1d000a9000c030b009101402c1c0b0340718013070161503480011400e61801040c029024491805450010580134034080d101d6402040f951390000c000d84014000300300f84410050062002a100368402e14125030001100b02c480b05805203842c00c1a0354441d004044007104110030f03803220f015218101c4c42005000c0f400d0000780068607401465100c41c0760b250410f810f001110010100c0b2040d125031503c00103510110103e4100c1e94808002d03145541c40305000c40152100c2000a041c2144170350900680040700462160715030008101222810312442c0c0300c894495075600041c0780100f02c1580160141702e19801821030450100c1d40f001003030344 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 204192940 1250 204191690 204191719
    0x4030c0209130201030f020c19150501140439110a050d17130609050a0f0b011706040b13080409111305120604021c061404020102250302010509 63
    0x521400c01c8490401d400002c031201e908560703160081c184c205480310025800c00070038800c5c00383c0740c0c0018040301ca019000180742d03004100507441203400241e500e00d020040340d80d5818003007100e40b09208483c0c0c41a03240c103220304420815603000000c840d440000501302080c030103c8003110394003024a590140301080c0010300c1d10342c000b080000002d5100e60b02900c51300c02da200001d468000d030410b06200c1003810604205204010314050b8200641100c000b04540086043c402e003040000200540504e014882803c00c0c40306102e4294101c3c0c101c04e541d48000c0c0644121181c80711000e0b2070007070003070524402080078108200c5060780c00a02400c48646403a07610348440c0101d40f80d140c0451401d4030081608a02503151042d0320000342415105c81c55107082d92610503440f81d0b0005d100078819080c00d421260403154900070a940d6562141041080140e0740800d01003a01c41250202d00520400c8800540203501069911019460138209000b1506545c01035503242c02c0f0091440e048210284144c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 204194190 1250 204192940 204192949
    0xc080109051f080d08090d050f032206060512070515030603011107151107030206070f030e0d02060613060803030f0403021216020a0e150402030402030a060e07090510050108070804030c02 82
    0x4000c100c1c82c401400c4c0451049406003801e0802001c22400d40c00103100b66038459044800c0314040001d400f2074030b9481c0d480070400925502410703100b00182d50702548400c10000140d110000b07456080701c50100c01d242c4c13001d01710b60362880c44c02015004081040c010070840203110143d504204018000324450b50030141d000c00907000b0312400d8031841c0c1c00480027104100c00344145490704c5106005940b40100a48010303603222000313401503041144245444160a2003a4061010290900f0940d81c03a0740907224025920a816038425110b001041020b01e00b81000744154030032100c0000144d415a50f881c1a600356004009009038254044c0001d054541116070700140b84141c2c4011007003040a1590040c424450301c190086441d4401c240300b840424060b11840d0ba81d990030459015036a50384510101c0c0c184080404000d16403410021207903041d07003010650409031515000f040046990300400c5580c0d1546d10310403e4049285240420f5410340b0a0f900c1340e42c01030182c1850420410181e001c00d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 204195440 1250 204194190 204194251
    0x5090f120a08030f0108011a010f18060f030605040605031207080702130903020c030a03080a0b0117040309060219080d022101150215251214041103010c08010905 71
    0x1142d4042d00001084000005808007602502c040320080084146e00182100d04440503001c003410b028a00322010845c0307200d80d002e0140c885800c0030386072080d5644c001c082c018002615202c004a401e00d4008100e070304051066004507a0003c0040c90581203c004000003a401000b013641c0c0c0c030404014440250311840c016590503042d120001a041a0605000342001c0b09015840d02c00d8000a5180000c0781e400218290800d040803c00600000e07e0750051382c40182d0000c00030400c0311854108418582c1140011040b90100d4003620080600305981c00468082494010407680c0c05100c2d48505103282d602500841c045036034100b03d030b01e208a456450b019801d0b4002008603ca10500a041c10380c14071101441045003900e81010b410b0100141e10a003256000032510140d0075000c91072800c0c880c1140100f448074008041280382c9030703032040c28211070707080b0b5041d600c0e03008511010a4600f8140300f80d9415000b05c0d5186856642490510f80c058a409408006030308a10844036401b8076110080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 204196690 1250 204195440 204195443
    0xa1115010303021e0109020f09180a0b15030d0507080d09080d061e030203070b07030e0604150237030e1e04050105090402090c0a1205011e0e01050105090f120a 70
    0xd00342c051001c141c46468031300d00100c1030400d9042401440c0140c84c1d80d4070801f800b0004613110303e1207581c1e1494a10314240c84000280c0c080c403034000700c1c60911141d12030366405800f11001d207c52226082e41410707901c000e10081100011070400013003000c02c3c3d034503001e4590303030409107408160001709803034140c0c9a8120005540031a40d9448003004900301c1d480d042a55082c0e00740411045600d5074001a071901d006220703041d02c0000024000041501c103d01c0e10b550000000e101c651501e803a00d804495034600301c026440540b280b04242c21105998200309416204e1041e1521607580e54410b046865480700b440450610444a91847c00e41d615004051112104022281d0710004244204070540e241030380903500aa8007042840091789544140b507078800ca035407240994888402104840c0c0c000c0c2c440c0b10303910080c0780000100306515080403540b40b040340d0401d5400110385800704050344110078460b9a000c03500c2001244520f0030305100c00f115040c6c00a0840e4580c0e80418891814020303a881c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 204197940 1250 204196690 204196693
    0xc0e09010303170a0c090902030c0f161106070809010f0c020a140f040b03030304021c020d03080718080715090b0c0303010f1401080a0f0207020a03050303091509030a111501030302 79
    0x14064004100c03c0e40e0140d002e03c0e0303194140818081c001002c0c006042601451500c0b0743c0010004000112500c2103484900c94188039954070540c0c1e0285042c62040d003501201e00b5220080381081c0348c5085070a6584450304000c6451604441c0c40040d0360a070072410b06107052248000c0300c070700560340f880305040090840e003044800342400c00040120403805400958484c0b40351140a03e801c2c3c40010942c0c1c0d2041d03068541502441c58841c11300144030f00b00e4002540800c0c00251b4000b0540d00000d03040c02440107444102e008070036400540340320482c80c010301085030700400c01000744e4410100100241d03002c1e41800c3c0107080d00e500140c03007941c2c0929070702c042c5a88000010807591110102500040c080041680720a50300c01000800302c1c034002e48240c0c000c3d62500d100342c0ca02c6442c3d03030407594260790007410600b800e0740e2072512036102e8100703d500038000c1c0580341d40d04920000103101d0701c0c82515620065460000102000c3e02d003640b0f0072901c2c2144e840b80c1e640b0394040030a9081554023840c001e80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 204199190 1250 204197940 204197957
    0x5060a0c05120406090512030a03050c1b03181f210501080f0f030f12040606051c15020901050304060c090f12020a06110c01110c040f0b03060c03190c0e09010303 71
    0x4201505a010a82c4014021f00002c400d8044d901c2c400b0050310308103100780c5400f20303068031040041c44050081941d8007840701d00c400d462214406000000300f082003900380d004035600b2240010010400a81c40010101c50f00024200312514810090003126042c2d0544010b41261114568002c0303801c00d0b08440410351040c0c4003030814200c2004100141c5101d000110701d0910081c0e66021035004801003912101c00100c003143c2000b41c0e0ba04202c000c0d00d4064040c55031011f0071307210310f01c9058541c281036a207524202100e181c10b565900846102e590706840e80b92460300c0d983e0340d50004080c050360f082c0800600c01c00c080b640c0002038250800a143c14007198800d982180108480c1025a13801407060050124802c800c410012600021403075003403c28035406200d4410041c101018203a00342c1d80503151142c2d9482c41d007042e03480745030080d805174101e813425034401c0c07151200703484151100c158a03150300740a038401040d2a0001100c0c0640c9140c4030000004e0140070908050080c2c01c00c6000c60710a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 204200440 1250 204199190 204199199
    0x40b070b22031209030c120503070305070f0207061d0409030c060b01080f012c070207090b06030c1b030d020f0c0607030c140a031d0705010f030203040b0105060a0c051204 75
    0x11075903000761207020715034030710340c03040d5601418041c0f1a0016114107500c6603d10005c2c5406180c0f0f45a2090f045204c43c00c4144020300b005201d5401141c004000c00e25001c0410440b601c10304403111100c41c0381d0002c02c1d1040c18100103481003c1c1c0c4840ca250040b00d00484000e4540300d9025000c080391280d25403c8014540e46440000e45024180c000c0c1088900d004004501c00014007950440d0303d4007810075031004522031030300a80c101041240c80c401c1c41da5014080301950001d41001241c48020007000305001c50002c02003148000d80c0c40c205d04040070b000d20001030400355042a48804400201c0303240200040381c003c10b980200f00f20822202001c0303409003004900b4402c450784008203103810400103c01180180908c1c00e000c0390780030070030030114100410340d00a03444050100f0610801e81d60300000400c6469541c072a07401903e00090f030364076101c01b505d4042c3c0283c038083e0768040c109001503802c20051150715088882c105040268114410020910070311004c0082d60210b4000d96071b0f035040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 204201690 1250 204200440 204200461
    0x8070e07110a03080408070605091e030f39030a09080105040b040b0903090301060f031419020d0213020318070609140609040e070806100f0303050a0e0303040b070b 72
    0x510303030400c0c8558084a00e010010110b102520140d250904a5a544590400e90b400303015070280100820b24141c00e001c510040041c2c0c049008114241035100003c810415548901500303400ca2004d41c03003405403030041c90142001003950756050326804c5900480b85440340a0049400300b42c01c45400002d450100e1a030300a5000000e0b016110003031040c0e0a0554403151403a10040c4043c10f645801e6002c0740308050148103c860703808006009025154903494038445010452100f181e0480c40042899068540882d400d032140c418900c1d00300300c528450302807000d00c1140700c2d01264482a43e0007050407440403840598082e400d1214126540c1c40400451031034600e03190401c10034030040c2d00c410800780107203070812000c000701078030b206482e044040d022034042c1c54041c1c115155400b840502113041900000c0e41c0b4881c0f040a00c144a411781c0c0c071454080881114040640024810448100010301a02aa8039104800b80890f8901995070000c0111500480380440e903082c104010320205602c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 204202940 1250 204201690 204201719
    0x1c0e030c0a080406230a030902010e10030203160804021c0606031e14010b06041806030501020403120806010e060d2c0a020a150e19051806181b1e040807 67
    0x4551000d2040f40e010880c80d038400380541b49401040580f185000d404592007451040f1314510041c01d9040c00e50200e440180203904206c40003608010802000702a0358841c00d08607000320703005802e03030303980074414000856100d509441c15201c041d21100700000261030651680da001965943e6010040300b60315000318180c05066119006a042240c2d5003030b1075584104841c221002c500c0f01d1811142080b048a024010070303400035001e54030204000051003003644001507005040e6840c000d840d0b8407a0015a5501034942605820202c02e10074000c03001e074550f102002c84620380c0400c0c0c4072a405900440d000300407515081c2650b400140701d410440c2071260303944000d05280d00c402490350703049520007401001c0c0610030601c601c20360011154021b50141041002d0000902004c3c0c054103403404040d107079481641e09900441405540401c50881001c07024052000f02c0f65407a440b4814405035243d070340160380c1d4100c103425000708040824031910300800040a00d41c0140030700514042103000b0020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 204204190 1250 204202940 204202967
    0xc0608090708030a030207030201060509010e19020307020606060306031e0f100b030a08070f050a03051207082509050303070c1505040614030714071113021c0e030c0a080406 76
    0x344107010500000b40e01000f51207601419240c0140c4401140c20300701d0140c0816840f0300d401c501c400001007904000c480c0e0851040d0811540c0000d0001340a000c1c40407884200c40c541c00503003055000ca6803e150840045800105c003e04669441800f2021429000447e9048100941c02521791b4402c0c1c220034030102002c4043c01c0400c008003001e4601094844034000c00042400000103030304410449401102c0350001e400c88115901d00c0c4281c074011340b450b400000000d081c441e89071300240c8803521a000e01da10800148034003007230000103280c002c5030980b0f0610060041c40014040440c440e1400c2002c0d0960a00404011aa0700d14000c5180d2038903150b451090100081000b0502155811005416140d4801a0800d5480e5a0f45404881c000d500360078090201c0d2001490405208441c041c0c40b5034040c080b20281c41100700ea800c00c0d0101d01c144000817070000c52131030854035016515031050f41070280082c103603850f00f030003416058102100148200c4800303034041000d02c142584801d0402e03285 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 204205440 1250 204204190 204204193
    0x15030204031a0406020c1522020d0308150301020f030406180803070c060204170c280b18030a0b150a06090306020d290405150607021018030c060809 65
    0x9400d585900c80320a0002c040c8450301e10a9401042c1004019812200083d4041e4190781c3e28070741074617092000c8481030768041c225401c02840c40560040207510484080d0380203020040e01034136542c080d209000300810005503080300748101c0d8203c5c2ca0a0004207012048111416a01d1600f46440d104607204180e002c9004038400201c80c0010b6118800c90703401601c1814403c10090903460528064411f40d00103405c685041c00701c1540340e007800100c5412001080740d03080b031100c00e5100c020b00300c90103040d0503290754183d001040180d04074444c01442e500c02104100d059000300310700464130340f0403a154103c688145000030010300d6401092885030510303040f6410a8210b282c00c0005210607440e0002800780c03540000e40c560780700d8042d80605085500448070001c6640001d0344610340e4080114030b240901e013020300182b01200708048807202c0060051a0a04020f4150203008421400c00c121300c00b84136400034408980c0800100800007584540300e0b11415506040008042400103062403595 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 204206690 1250 204205440 204205447
    0x4120b090a0b072001090b180c0307060c03050c011d12040e18010b181b0f070f020303070803091605010503071211041e0501140c0601060c1a070306150302 68
    0x50318942019001801864000340354030100000c1c14452014000c1d401c1258a0071b584c0078200400005a031384035510004070044c10714070003103010b900c1d900200e88159060304040c2c400c1c0b01c00b500620502000c54000e2400e24102902803414900311380000b60100100702c20004d06d110140340401c0008403100c0c03003450700b50801d803038400026004080078250301d4140044462140705100300358440d000300d200007004140c1e141381442d04551421019100b004042449181020f0310707000c2c1c10229000b24038243c00303181c46c2c0100381d1240b42002c1040c1600703d030305000410001012649007000345008141c02c2c00600003000e440480c0400383ca81c02d50000341840010f20402ca0a581c1108910380c4240c6016404248000b50b07161091480c465500700c400400c0c201e1702d00e942c2409003030b1040001d81e04280c807003101000d0b1900d52081c09005089104900ea0304c03400061111904c40d000e00c0e03051500c60304040c404900015441030220004031380080002c0e6950004210405004840a44c2914030381411450b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 204207940 1250 204206690 204206693
    0x615020d09030303053103020c04090201020606090403140705030c1b061c0605060d0e0105091c0f1202040605070303150503190813031b050405010e070c061104120b090a 74
    0xc1d010082c4005028107658200241400e0035044100d02c08210402d400358000400003910380300c0c54805034007030b00148154100042a4109031203080e00040d0140c0050005580d140100076000c2c000410440412024010069111021101500d1000d1064029507103031005025000d2400300300301c15442050400000503080d0f0303144c1408440c0001002400a007100c9007a104030302c040e145991043c1d810190016010002c0c03442e60340912101c400c0703030b4001d000580703601e06001d5581651084051101555810005501b4000c1010304841c002c0c2d070030a090b803c010440060100d07001940801d001c00c1c40018100109a03142c41002c0202410001c407100550414000c42d5803a040c900081801d032211051500c140318007001911800e01c00c0304003500c4169200d2800702d0040f8000f403c00c203c0041d10f0140850580b0341401454141e0f04013480320200b03540d81983c202c03103c4d0048481035890310f0303a49100d040301e1210344004201901103001501d0031b00e80075152204150380002e0440c030071a0880f00b580d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 204209190 1250 204207940 204207947
    0x180c05030c0a0e030106181413021815060d020a0e010903030f050d0917040302090903090d021e10031b02070b0a05031e09010f05070f020717070b030a0615020d 70
    0x101c0c1d030402d610f4008801c5084901080c0100415084000c0d15050301801030201d06164004400c54014541a8502078031001702203108240200703c029840004840d9000001400141084e07001c13000c899011000204040840c10302c3d4400c440300242035800003680c10300d40d40c10141099503a02c007031920344511491510300410405101104108100f800280d1b91680101504200000c42d003040c419225008040c0b040d034a00d50080c40220f008010740000204010f001005440320910094808406403800c0c0e8208980e00c00c0840421f03c80310381c0100a06119101d0070000c44581d0f082d510006020790001c0020b00f110400181e078001158072414050246049020580e401c04995081c000d45a0b10350b400c000b050741460214109a071146c013020000f1184054115900c2901040030402c41030b1510801203c0e031541c0080d107800540c0c44080c0811101c1c0c014980e40d2102d0318540c00b580d152a89400452103503a01c140c03541c542c1c1c2515100c0c02c0c02042040c0c0c40501c40420907000070308209403c0351019 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 204210440 1250 204209190 204209197
    0x120201080c0a0207050a080c0321030a0903090810050f010503070501120e03040b0f0316090b12150d0501093e01020c0d0f060617070902071a01180c05030c 68
    0xa01008200340d002c65000300010310103884018407261110307032035040c02c3e0394640034168001c1c860f104039014040b820036600151046414502c010710b140d6960680d980c4080d011444003201003104420000400c5030060042d03100f50052030401250398201400f02458003a0107030840341c820380180000300304603078004148061840342d030b94000c189010504407450450185501042003802d000070f00f0100680032800071032044400161172503010314080c40c00c9030300d82c3c0ca83c0240d44107000c0800c802d8481c4521004c8003a4000010205122809a1600801d102501402046039030769100e04030301040002070f00c0081004d80041c18544490010018418000412858000d8241c00990381c8412140d2080c0440c854049000c0c6c408150417049151984007009102803c1d03441c5482c05a010880203113044a03107a11b03604020080c4006070818400c0c00c025030025070101c903646140302041c62101240132005009108002c0c052180c42106100c40c4291483e20f8149d0301001800c000701321090b81001c00b036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 204211690 1250 204210440 204210451
    0x5060405010503192a030b09010c0c0209060415080706020606030d020d0c0312020a12050a0c1215050d11090f040203060112022101052202030303060420030406090c12020108 76
    0x46507142100c03414841ca14a03c0d40c02200545c09266031518018414500407600301d9100d07114042071a0788403440942212051401500010010900d08001d0700d07052042d04d03000781004000190b00b10000300d1002e4014070b940d100f41c1e00303a008140200800c6030180252540440d00303070041c169084a5250003922038203582e0b010406e10148204003410b161150a02200401d000780c42156580f03240c0c08040c12251044c3c6025117502d0070600080c0100b5207034002d050504c038031901e45500c41c0190041c0100546400c210031302c03041c802c1c40c0b40044c0c140c0d2203403401c11800d4001c0071040d80342d0307040d5424042503210043c03500e014064224180700043e00c000400c141180c00c0300d5a001088a514800207000782c4182403810280381c0c0840c52103840002c103500403400342d501c0b040310b48100ea00c6111044070000160b0b00203580358000340009001c03070030560444d030301c003e084410b0300351380381030741200c0805642050b00d0980d03282d55075003520400c01c1060300b87c0c2000b03040301c546828002e00d41503000a2040400508 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 204212940 1250 204211690 204211723
    0x1a010206061f090e0a0f0501080307051e010e011e0b0105030108030906030c09040c030b030d2d031404060c0e1c06090201020c0301090b06030717030a03022113050105060405010503 79
    0x14002c0003144908042e1001d408185640e5a1900701074a18401038005c0800c2c10070400d1804000113140300000040b1100c2d00c0d8002c000e0101c0502c102c018018200e0040000742e119507c5928400b039880342845030412044000c107080b03010001070f80c0075404a5907107407201414003d0800c014084400008140c03070345042e01711859030703803585c40d403684600c6030143e441165040b07810407100c80c0c0c2158046d001030701c04003c15404c95404a004090403103032208440304000000c4400040c00c0f040310450020b8405041e027a003404104c06070014552510544202c5050312020740d02d50020084030f5204541d04481c0d41c084075135401d06600400c1180038080703607800007450350303588444040c00c690003408103032840c5100030000c20903a42d80b030a010b9290707041180c0d424824014040b0110721148204403103000c2480100040d4209504074109400031f500c040d1021414400c641c0c5800b51003d21520b24501c1103442c203401955138600761510700c0c00d498001c2c00007813143c0c1c10940107010b162400a0070800e50b4036810b5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 204214190 1250 204212940 204212989
    0x18031801050d09080a1d1c0c0506120108070f05100c020a050306090a140106080a12020102130f210b0a1508060a050f010e01050d0f030201020903101a01020606 70
    0x8006884921074000384a45140c2071000d01d0082c40101c0d000b51550150300d80318130701b020380503c1c0c55032200c1208000d00e541c08040240d0703151002c40d03c902a02e44052140e0b907040b9803a40c540c4c0004032190022411001030485240050025a030140300c401c009200041310710200a08010004d0403401558090b0004c00803144080f0040d580c9580c2400020a03011303090740d0041c03d1000a941d15161040c0080d0b9414001341410791001b08144140e000303c0e042d0b100a80460503445d81e0368001ca0704806144011990240003800b4414041c1e1080002451b0384080c40703807181d241c1000c0607110b81c10110070f0b00302e520804042e08080341c26102c040354000010800007070301310226100341c4010f42e010b800070340b654440c19041004110a030707842140124005145000a43e0762103140e0341c98140e0902419800080302c40518001032403144a81d56151300c00c0c00058145000f03140400d280c0a81c2150412141d80c9564006005241581d10040204420710190181c5d141c00e10100c4c04206002907200082815203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 204215440 1250 204214190 204214237
    0x17010b0c030d090b090d080115030b0613060f08061002100e0708010614011112090f0f100825051602060405030303010303030f0606090608060d050c06070b040501051803 74
    0xc1c800c0b101480416641044005460705048407a520102e0345081144a905083c0811901070000300c1e040329549002c22a8001503404200d0142c1002940d0b10b0704030409001412542c4408070301300028149540d075003041030b0003815005241147c06014a40901d054079008140c051340441c0c2100070300407049022503018041904c281c900000c07944422529407030300c42c000c52143c42c0e032404400b160409985a20700b401000c4019502d0303c00b514051403a84008001584584c140f40300c454500b64001080892011403400204440035070000b007200008810301d00300205089401144180d0038400065001c080c003080c1d60103040b9200c0e11040700c140c5016600b42d2411955900c0880b8043c10f0050140e035203a5079a03240280151000c1c0d0145000300d410b108000c9405840703000804201c074000da0320503001d40c88070340c03c1c400c0c41e14441c14240c3c6c1a008010b406000c80e1207001c0202506481036041041c0713407825041007404c5070310240c906003850300140d44480e2a08400020380e2500d419901d08142407403c0b1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 204216690 1250 204215440 204215443
    0x4050318030f030c07050a06020309030703030f1b0b0403030f150315020708040b0a0f02061509060a08030c1b100c082d040e0a0b06040902090102030408121917010b0c 73
    0x61406940b040e01c0000f0b05400c0000b4041502011141d00b81d0340504010f464900580e142e004d8040425015844003000f040420300c290007041155a642c02d2880000d4600240304070f042c0c4887d0b8046c2e07000300e80042813204040d4184180c1e0f400c14690700041241400102804a400702140b00140c240d100c000c1a003030745120310b80d0403103404517030000c0342598459440950078220b8100004040c04264400d410510309400452182e1164140d5045030014502c4401048000d6401800706074002c4074080010580b81d004100401516034000010180c1da140341c180f24103080160001513000f1034100c041d0000c0c0c10342202c50928034544c4800d1207921400120092681070401c041c00c02c00b9900008106048910010002c00540314201c008514556402c003424054070507988080303420110801c0b003044101c04d194080c0c00f0006052054a02d8607580b40d403140c2c0b50104106400040900018154213502d484147c29103000040c1d003010b20200220240c50b083c1041c0510070281e101c0b10024011440500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 204217940 1250 204216690 204216703
    0xf141503010806071205100e13020909031c1b03051306051009050109051302100e0a2309190b1f02010623030a12031d0f0d080405031803 60
    0x142451603912980e40d8035615940e504103840250101d40c02200c04200852203000f0284240301c82c0e000310005c6440c0c500d0700d207a0300400601d00517801040b2421140141d449092443c047c800d62002940c0303030b44500c1c0e492031410180124100703241e460072040074150444100160009131181c00c00040a503180340741c1e2820b140940c000140312510380300820840740d9940d0203000c240d45140790200041e03038031102524200c45040d10354040c99400381c0c81d8000140f80c8106e003c0340d810628074041802420740004207801c078460380c0002c01d043c0036045007160040b030032211010b00d00c1c00481c0c201019045c00d8100c08400d00c0c001840104490301ca109240312511081e103100503202e4a14407114810742ca11030028028a07003070050854211140f12504030909400b00714461403100100600302d400ca940d40e0340e0802c10010781c2c60001f456201c1030740340300385200014600d100300c280b2006000c0704001500c6490801051110610500c08018103010210300d0010984814600712510b1012202c1048000703440c240 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 204219190 1250 204217940 204217969
    0x1080703032f10090b060907170613061413060b07030c060b0d0809090601020d0f1809020c0a0b0a0c0512041505090313151403130f0812100f14 63
    0x10543e4015200b031001030b40102c9840b0302400c11240341c0c1c0c503520100482e040c1d00785c07203008c0040e07a240224010319000c50702c0c00d0f42010005240520440240d08004103403241a80074280c1074039000d465a5850038000444581c00c1450141040010704001c0050310901401d070001d810000f0b442241700070803c05500c01d00044400826a10024180385095140341d030100ca000c60140c0030131380101c1c905500001f0500007103400c41d01d903203c400c440b00c00c00b15581000700e8000000d0106001000138a8001031000b07203c2c240c00c0c60060030015610381000c1d0000310740540400c21b03041c9000c00da10b4800340e018094454003000442c2c4400745403a03d040134080b1204600c00b44040f180340905102000100000400700c404680c807040d141c10b56941403011505000c08012001725100ca9003026804143d80c0046034406541e102c42c44500540d42c07242c4194030701c0144200c402450001718207180b4051907a680d980482c1110a1f02c0b401030600c005000e4220703061040c8402c1c0112040b9580d42692510309100c0c010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 204220440 1250 204219190 204219193
    0x309031905071a010512010b0306010b0a020106050a0f030308010e06010c031d09010608090c090903030a0b150703091404050403020c04111204051506011d0d1118060901080703032f 79
    0x1d0f0710b841d0b202c110b030842c00e204103481010f12681002103080e040c042e0821014000340a13040d16860015003403c554800d00b1034200710755070740b0b1022400b0341e51004000c0140942042448003282145405051801c1c1a0014502040e800b410007080341e910078003048000f6414900384904504803000d4904005028440780d900240b04070004c925250304ca580c01d84036140e400c0031a01c1aa40520921215400a5415070310940041001500c4c50313203942c000c02101540075100ea6100101c5403800341107600880d00480004a0161080012241000c01d140000d1000c0f01e04000354101990f01942e107100300010640540c0d207030071448031240d02d42000c0e039140c1c84003100050b4aa2810380b0b08a5101e0105401c0c64080f1118540810702c154810003a9080f00400c1627207010001d04042e0411845850049003103401c200c01c848248425250b00740341001e80348203140d10b454a410080c04010a0b01d805820500c8da66005940410220b0b51201101026415841d00e2054100c04080c2c01c10900f190054400040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 204221690 1250 204220440 204220463
    0x3010e04030c210f03150b030112021f05120a0c0c12030b13202b0b100e0f01080c0a05091c0f0b06011d120c03190c0803030903190507 59
    0xb0f042d042040360044e840c25950802140c00144822140394980d03001c0c1110100c800d100610951244205a0700f038180010822f003144e50045d4a50171038894801040c9000070f8021500103154100020703131581101040b02c06210050300084024108070980e60080c087c4107800c4d0143c000b0502030351183d200e0f0900641042d104000c1059410040e00140c03408091154114101c00d80c00e200d540e05841560003103845d503260141103070610b04181b06800e204858003d0740d4917039072881c903036400a80c0d15011209031910034007202c5902c100310711048022401810b110508003080a907255076022580417aa481c00c00a13140c0140c2c001040391f4820455004c18040a9101290140b20340c90200032100c521070f15101207140d03107280044030303042c203100300d103c0c1c4005a00c20002164030b0b1040e0007500e1201a03030100e403040c11079440003e190600c0210707581036800e03900d018102400803c00c4190060001a001035243d401c041c20955a01d20529031600d2161010544241500740f0540880310000d40060072260b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 204222940 1250 204221690 204221753
    0x1803170307120513051b01140c0304050d0c030209060d0512160f0b09190203070902070503121603060501020c0a0e0c0706090515010503011407050f0903030d051b03010e04030c 77
    0x1c0c04607110170340e954401d81d0312411480500440c1500480f01c1a56640d115266001c141e024607008100140180e0109000200d820b89802c400041c041d400381130f84154861031801401003800002c0d0a5a010f07200040744280420800620001c41c0c84c407100d906503030340800000e03030010b04901040c000c0942000e04d5981c4203101c1c5960a0500441c004000d0300c44030030300c00e0814aa5034012560094040d000000c040154414a9002d440d17882d000e0001d4038502808032400e04803590003121403c0300d0140019a00c4030203540f512504000d045c00f03000a01200300d0f16400200f5035040c40c4a83c0340000c81031800180001c540304d098a01240e440f41040c480c5410901d4481c0c3c803406540102c40d400d000c404000240c03483c0500403a441c204000340da200b4240c64240080b9826400000030003c5032504104420454500708018207040c040614001001d040940321107440d01070300d0541c4000040240b005100a150710304900e40c20a5142c24014902001803400000d40f144201c5045c11442500e00c00b001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 204224190 1250 204222940 204222961
    0x90310020408060a0b0a0e0610050405030616030e010b0a0902030402153105010c03080c1306120f0b130207020d0f0605060315070f05070206220618031703071205 71
    0x5005070361400c811701440702407a0522001d07808034800d003242004400c0200d00641817403400000e10300120300d0410315050310740001c24600382060ba803046000c0c07a0321051205045d070610440a191039032100a02410002000154840e00640928207070240c3c000041411541c03a40c6d101c0c558004090082900c400310304511039200c80312440e196680310b071052000241c501140c801c5a054440584501070721001c583c03002c40702900014a4100e2a4004100c0240400284c2103514020810355561075031183c1c2c422500f005441c00d030b080000f8041e01b042e007a44019035070862a0001e0901d105401070309c0d1180c070300020780c031000700d8a006425040740032060b2092000d00e4215520640c81541141c2c040c103408500d51040100842d0b2403000600e000c0380c0b128100344200000c0510038001894030381400c0d4480c807052000e070202e1040d039102d010703550b80400c0320030340000d00414519000c11500541d9403a50300c0c0c00c1c0c0410b00c00c45940d1100080000050000781c02040101889034800c0790410403450219541d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 204225440 1250 204224190 204224203
    0x12090f0b0a060e0606070615080304080120070812040f0204111902060402060d1509060905090709090314160f11041103010828060f060501030c0804030c020105090310020408 76
    0x81c100c0380c144003011421602944082d40140c102608007850a80182c99900050036001102c8004030501c1d44000f840c02e0003000500060a840380000a15468003640c080b00f101c1c0c6a055202d0210080c81000081070103103040d10b00c0b55148100300c01840d0341d103150603d110020044002e44c868600f00030014a149002e002d0046031401c03001c0000b44041800c4c050b0703910170084400070f40c840340070400c101081050b42c01288045003142c0f140d1040355194402602a100c00340c01800d0b20075135410800c958400200010401400da1100810401c05a81c074000c005044a481c1e5000c41e500014285030b060700320020304000f4035081402c0698240c450300e0144d828110b00c292040c412414828400c0d50400d4880499040b245944020b20005503030302018011150100c0541603c020105100c2005c10624040c25501140101000603468144000034040700c2404000508216a280c10440045d40102d4020066902420030603114189240000c1c50f0410804070804154004500095052000940c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 204226690 1250 204225440 204225451
    0x70f0603051e01180b06070809011e09150e0d120906171302030c0904110312040e06040902030304050409030306030b0c0c060703052a090109060801060507020112090f0b 74
    0x148041e03212004100c1c010760300b0007804450300919900412140540d0074202c3c828141040001c1801d6402500261454018200030713520354500185000ca10342e4860000b9209031111190703411100010800200b210030740b80604114a446807001e41f900341d024100640c2c0b038403070062042c50102c0d400d00d8054069a03107000c2074400300e182d050380030034940d01805109005c10f2600211212030f654806007100f440282340e0050742c1501405004080c541c03540b14515201e28091103081410548140500d850040c901c101c11480380010320041c0076402050034802d0700030104407404030b07410720b40e400001d09512895100c1ca92091400071110100740d010b030040c1e421680a09001c80290303071b55036494440391003903854071900341c1c22860019417064040d5002c181c12900039035455000c018501210380c0d400c883e101c4252142e50f0081640c04141da481040f11001d401d2500c0d01ca94a03501d0120098668020840000e05000c0b070380e044186013160360780c4600e031034039003000274000609074909000c81c246505540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 204227940 1250 204226690 204226697
    0x40801090311030f09040915110307020d08060a120309082a0307050f0d0c09020d021803010b370e010602070e070804060203090a020d03050d0609150501110f070f06 72
    0xb012201400200075108121001140355240180c0c20040100a00c4801c00880782c551a0075020508000548141d42ca110a000802035490030f010342c020f8603000c4404581010015850304200080e00c40714a1001100c111a200f0070340101c2500d400e44941c4100e4022001030f1080e80a540c0c0f0b80c88603101c24403100d1000300c00110003c3e42400516860740928000d07550080b503081d052013035500308070340c11600d4940500c00745a1a00c3d1201c421406a9120820201c40d40d900415000d40c0c9407040e80c4280740c1c4103000c8008016100da09008100075141ca0305000f0b1070000900032000d1b60800905120401c2710010000e1081c5940b14030101c00185028011f2000501c281c0f00082400c00d0f482d50340314060501034849105d259900d80c2c44038041c0d0700007481d042c01e501410b6040801600d4403046028428881c0c0c8900e07031a01c1100804804440c4940e001c42c05060801c0c40342c0c0c07490180041b9640c2903407020301c0c0c92110665000b260500c0e00500400ca12020300c00c501000070000c4040c0e02c400c0c181c418564 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 204229190 1250 204227940 204227957
    0x7050d051b0a1a09210304020a0504290301110408060f0903030903040e040c050907080415060315051038040b09010c060f06030b0f010f06020d050a020703080408010903 74
    0x2401596204580d0750020400030103070941e0100c20003643c028036400749640c0100e904d21281011200c820f030300c414502800c4000c0c084144003c40c500700c000c00015103c00e4404104840000d404810080c02031a00300444491001c0d071404c0c5502c0030342040c94a000b802c004555102e940f526002e5640c03a007203032600035500721800030822245010085070701030000f1100841c2490b04181c1c0b04074508002400486461040000014041d260903040310300c0742505454202c89490181030406c03004102c1041c103000d581c5080c0c2e0910024111001780300803c0c0d6094400038696a501120104c85080c5400416510ba680c00302800c4a40e00018045101c15001304880703021408500301016601035402991400b00d824048803525500c501c0000900c180501070101e010075110342144100d600e19082503819407406020000d14600c0542c0460042140e00b006008103880c1c914000d4480991841101c00c005000907202240b40c820003425018540120071255101c2c0d88000403070003002c03c560110003041001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 204230440 1250 204229190 204229237
    0x4080601080a02031e071802030a0b030f07210204060e09010e01050609060d1b1202011404082a030d0f170603070501260901020a090906050607060e0307050d05 70
    0x1146811042d640640104001c010000200d110702056a12000d81482410300005041802d01c0b41c0340c0e647c0304418801603890604d03040900a87d0300722981c850207584411080408580e0004510b4100c5081181c9180003101d40004543c800154a001035401814402d0128118404001241c090a00540204500f440620f06507091300e8080340c405600015400006280d801c02c104201d003064803800100d1000f980740c1d0b8a5101c10b90301074205192103404c40a034401156040303103003141e4003e084540382e8181890032039590303030722a81b5454501c0c4020b913000c030b2810015807014540b41c44c008000c0540c0d503410401d010040204140c9150940054010710340b81550905221906008030400303805083d00301c0c28600155030303000c0607000c96202d50044030540352000c40c84036150390041d0096000540d41d40f040010003013441c036254001c2e0801ca071421000300060b6559500311031341941d000c10041405c0020343c0b031080c2140a40c4501903c07502805003040a0554000c004140010519040c0d091040c00e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 204231690 1250 204230440 204230443
    0x130317190c02060a0507080c07030b060f03010911040903051e130504020304020a1a0403061a090702060f04030c170a03090221120c010e0a06061505070807060f110f0408060108 77
    0x4800c006900903c04000403407115114000070001307513020b80511440c000000c07601600d0a2281d901c15a880881c00c0c00b48009c615016012510b01e400850080c00300c1800c40d1100581401c1c4641c4052049585802c03a0080500030802d1301e10080c03000c0b4810519030030034484201c032036128800a4441e000342d08008907076451700e4070a070303402280c000d01404e8900d4104541e08a07a8246400800d141140501c0004006201e900400d00f000c1c05080c45103607000720700800e0011044000c0d00401c02c1d50040b804110043e0007403407004e5032240d01481d050080b441c49040094600203021000c0d461420f002a822000c3d54160b000311020310301c256403081091141e884465050040300f84041c034960040300203401c1200030503000d4060303030701c051000042c01c0c1494401b8518101d0b50b4031045560304d032549800c0003c2100d0344458200304a4904107281350500c61f986201c1940300700500149081c5e42d0701015200e240c281d600c030161070042c0c44d55050399200c41900780401608648540c1e001849102c0002c20060300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 204232940 1250 204231690 204231707
    0xe0610030920151809060306092104150e100f0c03270602060a0e0604121116080f12070c270c091401090b03070513031719 54
    0x10450210190102c915182c010104400d0384043d9000c034856000e6921034107240020402001c0946100324000a41c03400e1295506000346914070a030062001c10150910119005c0320005003c01d80b009802c030703801110300d41405180c018001481107090048041c58004800104000c000c98644d190f0141034032003200c0070901c03c3c01000000740c0015040c00000c0c0248420030306801040e20040d092403500d030f030300d1000f41200c0d400710005a00600078040000154840da030102c101810192403285080e84840300740307225588285041110f40360000a550b00284100083c0b21071444140317044558402800c0d60310038402c5003000032402462007910303840e41c900003100d84241e404400c5001da40d00e845102c4080003400d0081030344281401c440c003541404c080c401d005400816446249040b8104a811000115918100da06000300e041080c0441d085070010f0726800f032a540f5200da510902a01d41503400690f031b9200804072103209600360140090308001d04204625580b940340c0841107120100c85400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 204234190 1250 204232940 204232943
    0x609020a0c031710060804031404350318040912080f090304050609010f020f160510180b0903190821061e010c0f0b0a051b040306050c1b0a060e0f031815040e06100309 73
    0x10b104106181c2990032020340c0c503401c0030003b080026040c4d0151284101c18800d61807030000509200104804800c1e000f9a0f0381e00622800021030801e41410003081643c490581454188841c1e405004a0b80744204034104404200000781d400d8011600e00c1d40d10607000902a0510a140062418002604c00c2081d87d521131100701c580030815251504003c0035500c940c0038150180140b40804000e10803d80c1e002c40311f40d1003070341d56503980c203c0751000e2341c02c1141c40b0050041c08078094003800b00641c2d80c545504004a003240072603d000d800c00b80180c5400036401801003241110705c42c040240420f800383c051103225000c0c024070031a5640c500700b500400540b50f41041d1000144801c0c40820600d40c80681d00503000c2c403a10b80b0b407152180c803070240a001100e0044040c0e102102a004101c058000c0c8840c0c0c0381c5005c000c040060301c1203a0280c403030042901c094809510706014102d1a44c0c3d804d100e011005c803524042d0b681c0c82d1254202614100e0490f1418023402c00c80001d0341c0c04501c80c1c4202c50559 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 204235440 1250 204234190 204234193
    0xa111801030e030a14030907030c080303070906050a021b0a05151908040206040303030207051609150b03010f03110303120907060801060c12120609020a0c03171006080403140435 78
    0x4640178080c002c580c1e08040c0081c080c03031048007000b1000449046160b0060103c0800442c0c60f8034040c000103141d240241c01480c1001030500c501042c40340c00062881c00d115800c905802c500d90303034002252580d44260b00c05540949001406e4010741d090000a11000400d219900f0340380e001050155070310b000684000790840c03820001040800e11a0380a494980e10581c10744000c40032006240b1441d0b04c1c00e400c405003042d03650250314040607081144030010222001402c2c1550724061403c141c1070a1440f02074201a6000c1c00d940c4c50359401c1c022102000c0c2d101d002c848060822203c482d942d040c60340100c2001c5a41c0c0000031174403038058110402c845134019000c40d00003410170401c58003000c3c01403090200c03544402c408100010704d4005440341c82e80a5465200c07103005810000d1408400c014024400c1c1200b00a00003507015940c200b5050f20307a2820414941c0d2100d2608580340003a9454404071241c0110340800e41d280480742e0840f0079040040c200f504a0103e83c0c2e40103c54004030b0806406 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 204236690 1250 204235440 204235457
    0x615060e0402160318050a0303120510052407120804020306070801030f15231f0510110a0804081014060f1c02090411040c09030506040b0a111801030e030a 68
    0x29104400c0c501c0b440c5c4504525110456860f804146480c5950700124041048550388207001702c600e104640e4401013020a40100c1413620011030954100304618501002800f6006116500860201e5070880e9008400b10740c0005c140400415941058400702d11034090039010a41103480b0301d000300e06a82d003014040991880b980d84410030b4809603900c6080d4580c40351641c90204840c48a038001d0300c0e600302c0b140c003206d00d00380c0c0b10000d083d080d044401c070040d503440c1014003054480e618659000711581c104104655040080c0038500b5401c201d00030030001d0001408181030001280190b031a0744504401c7c400d040a0032840041c1460031600d050b000314140c802d11003a450040405480011400c0f407604810309660045034000300122010f48943c406400510303007600301441030910200943c640b0700411030540c0c3d00c05441d032002a102600842c010004100b5048860744510a000c4c84058081c0c2d44001580c9080d00c600400c1f20744070702207450001110060070010003110040500399071001381 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 204237940 1250 204236690 204236693
    0x20c01200f030a09050303090c0f010f0509150f070c090506010306030201051206011e0215070509010f03021806070501090c09020f040603020309160e1603110315030a0615060e040216 80
    0xc071504018402400162260319100c0800c10601c002c60050000c500500212031640742030000c5100349229042c10820b41c1006801041e40c418269600310004403502d10009a60810116440c00340002d00401c0000004820f020404a0400d04c0103d400d40c0c1ca0600c102d540c0c101c0154112200c80c032000c0e0101e61704002ca1420030241c04d503401c0e07129805040140b824200f80781c440158598030403405000d40c1c0501c08442d003c5c1400300000d681301c2e1051521610344118000000e00e42c2c9208040c050038103402103880d80e040c0480523845115860040d280711b444507c1810814080c00e6140c2058500b2101c040e80400d40d0365032070003111801d030342040c03445180c18a4010214000e41c40205180030900900d5600007060400740507000003069510403500481c2403900003d10084109040f100515103446a040340c1165540306480e403240e8020508034107041d0407804a81060b0303950780d00400c680c0c82c20b0a819181005003246400366182a6524400468210140000c0344103401900d007032030950400100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 204239190 1250 204237940 204237967
    0x6091503021c0506070504140307031e14120a030b0301050408090d02040b06070503040302010807110d0e06120106031b1107030605100b0c0c0405060126060102150901020c0120 77
    0x4081d0b01c035078002d4a00111050b2101e07403d03c00c05984500c00110300190070008100c2c41d80200c00907a8080f40030b400e44504d103039555440008640f0300c2e80b140d5206500039000303202500f81c0b0b0303c48590042c0e00307803099410812200c02981c1d1043c0303080804a0700e00f950b004450700b0b0503ca19031103075500000061402250204008501c54a510b00300d90040c1c540c101801c203502c584001e000864030560056803110700f0b600c009055044024400d504020802c02c1104c1d001c18000340b43c0c020540207003000e250740d02003880890f103548124a0840c0345030034210000209554103910140751031303180410781401e00e91421003c6504200700f010755015076202d51020302c0031940d1640001c1e040400d40350303c0541240e44080c0c0300d0a64204000440c1540c201007804001400d01e40202c0d98011000d180400c217030442031181c440c01e042216180300c41840610001a0981d008008a02d20410700723410b554a240740c04d0b613885000c4d40c03001054070b40550134460440040340070800b514411401441210303040030500041136 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 204240440 1250 204239190 204239209
    0x30c060501080a11120f0f010911011b150f0510090b03030406080a050c13090509101431050c18070206010b0a031107080918060303070209190608060a0609150302 71
    0x500b424091b2460145010608001c0ba070b400590030b01c004207044c4a182402131800c0c5030303a80403e043c420b41110400700766203520100461a0750107e400480c2e03503841d40f0309100510fa000c40c0340d9034031403402c1d09000a000300c0d410b0308012a41c9224080c4058a4440c0500d92070b170255104010218800101043c880101c6030461648070012210190901c51780044443c100314140d400282c241c0d651300140582080c2c203108a0a0b0780060440074000b143c4001c1405e200d50b1401400050765110300c001e00b0800c09024543d401c104c084c1e02039401d5800c00c0314100780e80c0312880070169034807924070744520000504420403040d01c02c24454020749416884c0420b150510b80c071500140007010741d00c5165075814001007020348a02400350180ca03440312910003d0000304040781201c41514201e0804100c541d035800000c503080a5810b03244c54602d81c81c2c5140c05403942c03401520100d881e03030400c08041351030b400c000b42c003a21452450701c041c010a59030b4100e6008039054800707080404810b00b070007440907003024840b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 204241690 1250 204240440 204240469
    0x3030408120304020d0f030504031401020f1b12180406080604050601030f1e0b0a0b0102010e030409020d020d05070201090302060708040201020a02060f1201090c022103010608090f0703030c060501080a11 89
    0x43d00b100c0d50150303075411004840b03000840122384042014410f00c00c010307140e9000601e80c0002140b9104003c248416540110709031140c1051100d0440f0341c64400130b1003c03440d20071555a50340d8aa0300820211a10700b2000000540903900d402da0000c0c10100000305180140e40090240841d642540c464055034604001d0036148884070845c210141d00b0410340c6803042310300510031310100d13080a00001c400c0d19140030490b411a0b040035440c15480310040102d03012505504001070ba10b10035104090040d01032202c41402c2c0c40d203007404105400c4c1d01900405581e501c65401c0e942c00e0b030340741c0c2000e450490302590080d005074421038a20005040c039200500c8030441e081503040c10502903648c001c400302401d802003100c15031500110b107121a0104080480ca140c05403e03400340181c00200d007074850105128840030403c00002180d9204001d21040d4410340111b01500c4240f03489040190100310b2241c800c4034903910307000001520703020100d00b40b10380b80c0c0e01000e030090960b0008108821403022020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 204242940 1250 204241690 204241699
    0x10207031505040204051305061614040e01060311030c1912021315030e0606040b0f03030c0105010501090512100c02010b031e010606020304061e020705040f0504110303040812030402 80
    0x1202240320550300e200c441c070a040e07010401d4034007881400203582000d0003c540781e10405220400090000c10340540c002c241c003038040014000803004548040c146096030b030042e01c0000b00861086c00000c0c6d01410380e015500d052140c0f100113000c0c407280c1c4c40704a030030041d20341050142c0032503000860118007040065182440300084a0b5401400f241d00100300c0d20448a8814420000d00d4480160748854400d50f04081041e0910190b00c0d646850340148241c0c8107a903130b40c0e0300c820251b460f8007555151078406021203845506905130f1500070b120a0083c03d021a000410000382c914007801c410090309070040180ca0001112030422000c3c0c04024100c03000d40d501d44000a2440c0c03010001c0d014100d4980c10313000d6180080c4c0822074219075494002c01d0454000b0082840120b0700002840d1201d80c1034102800300b401103c00403030401c1e0782070f040075030301c18240f200c0c541c0d44123681d401160240c0d029040800000c1010f0040584d0b81c421807244600d290841d2001565140181c0042c40e03100e4006070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 204244190 1250 204242940 204242953
    0xa150e06041203020d05190305060a0e2a090f060d1d01090204050c2803090501020406081801060302220905030705030316030504030e060a030209040504061b140412020102 75
    0x10009812500190000030300180c2c581d02031003e00d6410082c404040040e030826600d0324807900702055142c001c079103015090584a80c00301e1040d440d4402840010f0a0500000d4114181a2094040307169008503440c2c0c568205480e03c5010f08041d0215148250020101c00007203c0d01000c0c0302c21500411a45060710307580d4402c40c0c07694040305541040510b034100c00000e54082a2040000304c0358041e0050031008000e020326800c4d40342420500781780c10040c11000000c141141411009050303a03d40c000c003554000b141c005026a000f42029000e6000f112030351000c43c4403110707a14220b503014030010390301c0078107039040c0030035000c1c0b62002050182140c20701103a14500f5489080c42c541c80383c0c004541641c0000100b00759440c41d48900000500b040c5021f11a5050944004060070b0740803c0c141d10460b800a03008a034503000e0b904403034030080301520a2201303141604007140188981180e101400310911006d07000c0d6485216114103080201070f0481c10503003440856158500342c00307800c0f4154071401c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 204245440 1250 204244190 204244217
    0xd0b0609030d08060a090608070e041410090c06051207050d060503150709080a0b0f15100906020d050a09120204020c1603060b0901060c02040b041d0703051204050a15 73
    0x42c00120340c042e51607110590581012410b004207000c03154008140300e4a0f06009012100002c10004104c80502c0c103804502e440d80c0c18400014003d04132401001e100d81401000c8000c066040420001d00605410705c416070f5030801500c0510030461080b0440b007014002a5a50713000d407000d006064001200042c41684030b030b011030b00e0841c2c50005419211040001c0111403580310121001410350b420143c50364840300d50700c1201060000d031002034401108000118030310540004d03401140310080500301800400c00c1d0103040106d807409803074010300403c8050034405002d4403c83e01641000c0c0d0381c103100c00b443c00d02c00c0800d2140780c0031b040b43d1154007040a85482582009003040c50103410310751002403071561034558211001c0c110880d014100d120010085d8503004412030810f15015900840c40540c0440060001d016625003011500224480c074405117000003185001d403803041e81121540591035010103c02d004038443d242e0320200345401448007180302c1c2250348028080341800d03030140042 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 204246690 1250 204245440 204245443
    0x3090507090e0708011d06040308070e0607080901020d090f1e0803040e09070503120a080405071a0901110a08070212010e0105011d07080118020f0d021303120203040b0d0b060903 78
    0x18403042d4841d03010040c14404207000384a02c440f908003840007810014101c10780c080e1510b0004001406001d103007400a0482070081c001c0030710146004094550f1107490346840721481d041102041c1c0148281c4000700c0e5944c0c020907100050f070f045003121141a81c602011010943d1075100049607201d420100081c1d40d880800c040c2001c0c001c0c000414820303182c4110413514040c2e0560080d8800e5100140114860103007078112509000c0512b05290a95203500381103180245941c04455110210070301d03800304d0303024400949540c01e000da0b1046840116031840560713403608114050a0000208061401860480c4c900d00c0c64200c1000081091545811501e00f16203090b4004800c490044a0642c40300742e032905559400441810503a01d40d5040006c11103440b014401c0902140c1c0d4005416030b0032000b61000c0e607090b8500c0b54019540e501d603000700c0d04e4181c4054401100d92140c1404d1a0b00003e0000c029074058030300400e04581000390318038042c006843c1400c022a0011410041890700d600c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 204247940 1250 204246690 204246701
    0x10e011401050111060f16030914060106090b03090d030203071209080306010f020303070c06150504020d0b030d020712060506010c150509060a06030c0e061903050109060f09080a0309050709 83
    0x1481645000d80d036140030b0014020b00700ca0070307030701c1819000f0400700b06140c060f07040400d4000c0503d03046c1c903103581901c0708150014242d102014101420304e8070b0b400d6541100040c918161011a600c074503050b562400c00300c06901080e03030b4100d45904054040d82000e88690701440d44107040d85484810000184034050880b000d51900340c45484000041200950300444424503044003440158914a400340000303040c460010700c02813825443c0c050003080d11540b010103101504008004651b21070f000ca40140c01030001d049464040d00445128000705400800e080b4200c0c1c00c200841002862541d0f11800101001064207046c0911320007000c001c103210000840380040e001c2c5000444d414101d04481c54003d00130943c0002e540bd0140520002e22000110b4088600006201030151500c800094251a42c550281503160010300c0000c180310054002103103c0e402241d08000c558116500d030004c4d5802c104010780400c2d41003140d004054443c2d400b0002003130285013a1120300d40c4078014202a00c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 204249190 1250 204247940 204247961
    0x21020906030a050f0c04030f030807030608150610081308030a0603080414120d0c0305130b13090b0114121302060307030b0906030606031c0e0310090302010b0d051905010e01 76
    0x90f80c0e0350400086822256100360000c0503c1103003030074540340d030b9034605104068000c01400c000102020034400e5000e81c1000c1c0203000c2c0b10050314044800711100c00420001201d41030700c100d80c500040f100481c01160720b5400381207103590a8140d440d17607469403813042c0d0004c1c140410340c80c0e80ea60000082850b0001030400b40c0281c0c0c0b5000e01b005d0194003000809400607000d07005a8002021014200707410050300c0081a606050850700c1e90098030264281c15101c1c0e02c18441c002001816a2034100d80400400564040e07840410240c1000e9004640c21403650303281d000c10103003c02010f980c2150400e07040340d101000100c038400e143c8803039000c00c0c1181c0090381c080c404a81c03280d14070725062038080d141ca6070041081d0000c0440e490501d0002c1e80c0c44165400515030501d0760358040c6c0744540f09034942e800341c20028081319a0480443d000704000d002405098006520301604207449140c00c03451020495003090040c4242140030110030821000d211080300d1a6580c1c404e03d1a400304280118402e0a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 204250440 1250 204249190 204249211
    0xe030a08030402091b0a0f0e03070321090b0301170a05011a1203030618100803030f010f05010e210a0c03120e01022404020622060f02010209012102090603 68
    0x3800c0510500c000da010142117524004000704010420380c440d031050320741e41005490109011901c80c04141e540d110300602580e010300801401000f84000c1024444c1c450500f0307002024001d42960048404004a01441c558400704100401895100d484504507c058a0090700c29884440c0d8030a82110180c000094a5010060f100740079464989060310340f80b205080614954a85100007880064508440da04523008035404140d400c0803100e640e1014190303600c00c0703030303900e041116150601034001d104000c10080d041d0004100355125404c07081d55100054414516611071185030081d05185043c004010321a0712055004240c014041c00011401a0002e00c2c9500415034001c0440300380b0034005043d544400c050058030714030001d80720001d00001e00064143d80300c44c4000344c894450800e001290902840700c0c0c5e0300400d0760f60352450850b01940c554100010785088240d01781c1c0a0841207a0108506803400900708481d80112441021481c01c014600080b5100082054109488401e0344 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 204251690 1250 204250440 204250447
    0x130e07020a02100513030f050a050a0803060901050a030f141906060f080102270a090903030f0c0207180e0307060e030414180c0901030f02030717060405250e030a08 72
    0x1d40c244803e07101144251850820700d0503029020383e040034081c1d480011302d00480c50210905005051103000261341c0d100081d554454154101800d82c0d41041e00c4151040b035850300001080e18000da2540200c80c2d210302e558403404219101e0001000b05036100d42d01d503002d802258a2100c01540142940520880b4009a600e09180040f10000000c1e04801810b0b8810411243c40341480c80040c4400004041b24402c21030008010460041807a070046c6801380c1402941c80401d50503421174121840c444500300301c1d402e8944070803642d1314001d10409040009010780c400e64aa00c039080505605800d008482c0351201540c0d50368100e625030406c0700b0369904003080520182c000e0034205810782c441125071000000e0340042c201504800a44003900d0840005a215507590190300881c0340703680c1c101001c44d1203290980c0c0c05024402d0740c00340e20b11b1103c90100041c030580703003a201c1d2500502c9400414819011080046804a03068054a60a000034400c0c0711005940811048000500c146045a00d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 204252940 1250 204251690 204251693
    0x11010b0901150315080c120304051c0b0a0c0824130203040b09012003090a060504051b01110a12110a060f05090a15050a020f120610020d0c08130e07020a 67
    0xc54940c040040c1404c440e00c0b10030001c090000501000d030900844010002040e0003611910710310031540f140c0d4225451528001022200c8503900c11400d0085000d5401030b030718885c401040300d00c1d00402c42d01152480003c05c01003203001e0710100e0007000ca001281501a0a000042c92803610002c01c56040e5400104000402894072141038100c54148024410260350900c0c402d21964140d181e04d14807040400050350030f5404100c854000c54002208000700d061a017400354135144005000c12644d45c115060003029441804e00004802d810005400c01d0b1b003140d074030401c600682d414950204171041c3c00301201200140b210f410306912400c400260b803186890003409880008000365419044220301d0400720b42e02c02c00345d0000b1011400c0c00101540c80301c01c0140207011748061052100b001040604082c0e038894641c6004180454150300034180c185012070303691800c005604009100618040300044011014200402e01c071007400c81046c0e00e81c150301c4803211080351000016030044c2407540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 204254190 1250 204252940 204252947
    0x70606031202190302030409050a0f090f050105130209060607030c080a02030c06010f030822080706020102180f1e0607060e0d0f030c0f0c061b020601140a0e040311010b090115 77
    0x1483c4501c0700c000c0355801c01c043d200030703407240102c2c444d820b00183c641d070000d01c08031240e51000180328611070003000616401c0c144080765080c2100101c40039031900011404061a040700e507000254020b00c3e9030ba082da91441403080c2c3d500508411421700c13840a140c000010601e001409400c007580d402181c480503611009854440c0607840007030000050312083c03021030114011911001100001c01d151001c954003018880400c99000f61130900503401c0114040b9410b40051840c1f040403a00f00341604c0d0364804102d4103c00541c0c480780c1c0b001c00103048080003285070f1251185620000d1086003803071015117035081941d00c8600280490740001e1540980c039900301e010201101d0952508110307980400801030722104a070740c07030702d400c1c4411702c00c409040190a4000c00488103c2c03800121005403186000b035507071a401e00420880f0381c4d040c0317040e100c41d0400310110707400c881e0280310449054a59841c21b031807580201540d0840341d505d800c10484e036903c1e007004143c02000a5401482101e400c4103008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 204255440 1250 204254190 204254203
    0x103f0c06080103080708030403020c100f11160501080c07080f0c0f0d05180310020406020c09011509050103110d05010803030114032a0d06050a02030403110d140c03070606031202 78
    0x8109114800e070050010030310800c29540410390040f5499500c3d19503003420f81c50101c06810441d4000c05400c0c00d001070300d60092070a0000302154543d04001c00707030000604d4891182562a00120105980030441988500000e41e0400007401d0301c03610f4504152111445030748000902e80104600045881c1c20345410060a400b80c20701c00040c1c4034002c4101c90050051294440362007a081c0c000080c45050794090020b00121150078804542da0356440c2006515000c0c0703401020310640c0031400008400b5042410042000d0283d960300001ca0704080c015001003400c0700c603c04804100b4800301c403a400305441a2070180008100564880d07140940101d50072503d000400d00070f4000c0c000da06240c0051000e4a00314014038031084146201000114024500003040940003504000c14440480e82a900070b6005600950340c503002c0c091011a520303941c15646021200007090480030945d41448a0b003e000508241c40540380303408070a407900400c0e00d00c182c1040c0c1d4038200420321f000d041d54040010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 204256690 1250 204255440 204255449
    0x906090501020a0317100b0c10180804031e02040c090e1308030a0e0a0b0709080c010801080d0804080903010903030605040b0405010503100c032c060f103f0c 69
    0x51040d0f00c803d9800070043c05940955242c0100074030046085003040d030014501408030500c09940b1840c01802c007555910711480710b0401d440c035000c1503289690304909461400340c1c00000f014078040c65552419140880e512452605d20004464200140c3d1a07004020b0a00307040c2e03581c2350180d0304040350091002c402900b2940107070215522140000e910009480d03000341c8400001925401c282030f001d0500d03a1440006140d0030b0b44a0400c0700858110100c0c1095039000c000700c552445a000041d901c400d0203018680391503100c00c00d0070540d80c0c4160a01c4d51302c2031080c47c0a07410f000d031400100b803d4a0741071004030007098450005000600b000e1081410031a0111400d000c20f514040100f0f0b00c44003d6000102c010391940000c1c141c06010b900325101c4070134407403a00801b04006864007000d007902020a108a40503280c041100070701034844040c000d03910f05400c02d1010b480d00d040c082070b07954844244031040300c0c030600141d140e00030020860b840d2012036030510400c00c9645002418018242c12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 204257940 1250 204256690 204256693
    0x50303040501090302150708130e06030c1305060d050706030b030c10080105010f1404030809100809280b0115020f06010f0e04020d0c06030b0a17030d0903050d050106090609050102 79
    0x8200590ba0348030380d4400c110707034040d24513100058180001c0c1c0301c288a44000640941000204a03081d60a00794076070b421141083e5007200b0740d4550108241c1c4603058100c01c00d41c081d41032010310440c54116032000390400ca009260110104660b9200d50030a1b401d5401b9501095950610443c942814445c01c41640c008542802c040d0300ca122000c0c0c008001806035074100802d1034901e8011502a80c0012102c09400e041c15445566a29040c0d405900c01040306004140084541c9070a50050f0701c1c0900804480d00a820610400d41381500045140007d103c18010801c03c00320200301500c0c05203020344007a1000401c00b800000010b803522000c040c2a41c801c7e0b2220300104010803480c042002a50038490140342140c4a9000180d200f44420802418104d0b40c0140020310a4040d803200701524421340306480055613881c0d072101102d41070401c1407035642040210004e0071090340e0103140000c0c40307814441d0a1910801c11603040324426003054010030311200c1c1c140800c503007040030613004080c01d20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 204259190 1250 204257940 204257947
    0x2208120304020a060f09090204091a061303081809100e010803070c050409021201020d0c1d0a0902091f08070215132411180a1a03040218010902030a06050303 69
    0x18081003e00200c1c2c0300380003c008110b480d0840c0d0b40d1040b02e4603801001806015034489440300d083c00d004041404d44529000d000c0d0384e0614680c00c106042d00d544222a0f0b0600031400d1854459040550000c0480c0c02000700d802c0848155070b55200740180510340d610441ca80483c01c1c00c01c540e03c100742c10b03040341c00d50b98020b10008002a0302440301c20243c4c1d0741034501240315069440481c0e5000c1480d070f154200e079400030419408105056004007204460b50351803114485050b000414150890503003070341c00410340d000510200c012034000303041146020b0720000c0c030414140802c1d00311081c04034100c0c4c00940301c0c1c018840e2255040090318201561034003400c0d903500b00345100d409083c1c003640000f070617043c0317101e0050407400f44107003500c06a000c903610504c9040c07144400f5000541c0301d012500e600042c0b00c08000c0d01d40c00c0201900051f41c48048600c100031a4211440c0c00c1c980000700120382c0941100d0514240340b2403840050700910804d2000358032828002440c5c42960805c1c3c01c0140284e1003071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 204260440 1250 204259190 204259193
    0xc0706020102193b090c190509120105040c030b09160302010c1a070c0302071a031819060c030c031b0309061107030c03020f1504110102032208120304 66
    0x10f00b4400385103285080c940c0528501a2001898060070080c0c100070002611082002d05405a50108070ba0b0045607400c181d40c0d07400c071032170389070340600c02c6110f00d4001800f00c0044600c0c0034800400001c6c20051240d03035401f00e090092801d41c2da048404031265003621004000f0880800c644640103524a0050221440c0e540e91940446469110213810041405280070a2207280004e81820f0074542814991518000f10042c100680d4032100301c00521031440d000424003003101d035450386140310341021440c0d41c613868100243c03803031074001c4008640111410100d5080808041201c028800c00006c900724420010280807a91080480d80c113150a14403000110102010364400c590305070304001800721039500b040e10040110102e0740c1d00d0340d40001030341d0341031503006505a0080c1e48a41d0844115442601c040d545038508018489890110440802d00160030304114180942041c1f048a04102c130505024905c4400e8141e044a0311a030548144210a03050104131039804015007c00d1071420f25 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 204261690 1250 204260440 204260467
    0x302030d0e0904020609180a1b05180405060102120a03090c170c04150518090106170709021804021c0c0e030307080306010309020909030c0607080106021b0103021e0c0706020102 78
    0x3e200034030860703000450801603900c018070b8580e006a0310740f40070283c1c43c090480a00811b110170808907409136a02180802511540031a0035600e559601c4a000b280036006110150801074001d6055005a8410124a40381c0d140507241a04076540d022542c6111820681c1c140d02d003940008110301d003290f00c0c007034214900241510701e061058400060700c0070720500b512491340c515007140d5408a103c05107040c190100c2c0c80243d006080390340081180b00e541d1100f840f99101c030341c504018543c000020400c080b1105a001d407404411403065880c20b41907040c0043c0032603110b00c1a00c0301104035850a4846050f41d407248140b400d02c03e00700342c110305a501e40001e949000720b140c0201005800400500a039100350400205039502a00f07640c0d42d81001c502d855101d8015a000c0c28451094500003184140300c6c000160482d032441e000341450070080f40d040f098400b02c100003d4180741d0204001181d80f00c54003d0522184221095a07480329240290b590a00d4015840300045a00502410207541035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 204262940 1250 204261690 204261709
    0x20d0c090507141602010e030703050a0209060301092414011205010c08070e06090411070b07110601051f0201140108011d0102040608271e01050610050415090312090302030d0e 77
    0x45844c046800080326200403030b112500c1b070071825014000c608001042090004004103094800c40e01108195600000e05080b07400d11803024054031180f91281e1066180e007540400304480ba102c003c00c008011100b10082e950080c1e200052020b022524036050000070322030005a8800c0e458200d508bc24100e00042a00307550140240c441d80000940c0c071015906e0b503201c414000c1d90f5a04690721240700d1305007259100021154a400b09480b41da0355031050402050f464142c44000300a0800c5030503102001900b6060710304c8810a40d941d0300b0740100c03820f0804101c2802444540004100b03200300320107100705c001c40080180450b030300500040c8103442e0000e8405920421004080103138012a058285e004240080100018000c2c44419060500149984a2050b15a00080c1300d103480b14818401c2d4041d81c00400380c0020801c0c0400e2115010105108810903e58904003903501e03181c0d140e04492080c14600980851460101002103040078880000200a20b007409905459800c0c04998801d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 204264190 1250 204262940 204262957
    0x31d0a060f080601030c120b060706050901200310060f020a0501060b09030d0509060a2303040c090624030b04060308031609081b090402130e011a0d022b020d0c09050714 74
    0x544620640d100e9850350720641e0ac3c0180c02640500c52400c1c04110b4a000b030a89000f824801c011400002042400f48002c40b0f02411843c0c400c091400d10300754046640c0d0728084191401c6000b91550880483c6090084802a0a42c110000e9032603801204140c070b49119103803060107200c814400035078950b84160540710050a50b0411580c2144428a16049081c0c42400c43e1010031012090006000e4905d0320082a0b1780c07070a004000c895141c0402c00e2800c0d030401c00c141602c0044020501501c0c0c0b02e40c0180e0b402441c060001b040d501c0e12951005000c3e00112a195450040560880c200c00e503c4200c4c88000d084040281059850100840c0345600064000d180920b01001c003041c2103445550021032503104480d420132084030146940c4d4040c10a900c1708014110800da0001840c2ca0030015111545500821004216401803039200c040051650192041c1c04c7e260020005603e0303681030071201d03500c551400c980c26030030300c103084003202c40180010b000c01103451410300c0c4a41ba801c04484200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 204265440 1250 204264190 204264227
    0xe0103020f03151312030203151e060c0c040612020d0303110d02040b0c070609180509030d02030708041209030308010605030a0b041a0a090e0a031d0a060f080601030c 73
    0xc0d06040220749000707605500b03a104003510700200201c4c0440c0c1008a1080340c0704000030104c002ca850402c60a0380000e6680000800d00d030300c4075410700d1601440b0715000990b02d801c244604150100000c036507421600d80c808458100300e07071040700e0740381c00c0c800e14010300500000c006002d541600451452444408010141a602d002e0f900d8103e641006640030b50000345425540d03540c07a100e10202c142c03c042c48844003845402404a0168000c0f0348090981301551210821141d004045001030640030f040640140005c10403040c01c0c48560004512481c0c05845224040c1071510740b20b0520700740004071404000384030005000003a03010441604581091402c3c54903a191041d441000300302c1095400e521920b4401c032840d040852990894030403008503100c01c8890f0b0344203100010b0ba050701d001440c494000c0100c00d40024010400d5075103103602c8800454404240d003000c105c000101c2e41240d000f050000801d21000d035804800c16901000a190510a14040e003501401c141800381e641080c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 204266690 1250 204265440 204265459
    0x3040308040315151410020d0f0e0609090a09150509100b1c23070302100c081e0304021f1d06130b22060503060418121d04060e010302 59
    0x1040303103130700015142410800103c40042d038484040c00c41c00074200300640141e11101c1140c0310303d0b0020810310100441c90311501d038a031074410000c42e00140c1440c80c030340d8410018441240141c0320801072521444480c900000c450380141000480c2019070003a10a4040c00d06040000301500840c040141240102c0c0204a1b0003440d800034090081c042e05851005403050f00308402e00c41001c500d54030060881d44e058000c1101c1650103600d4060030700000c0d4112410111200382c0c0c61060350310002c2c10380581c50090030440c17100400c02060003003902c5500c00c00c0d00072040c0401e40c98414041000c241c65603142c0741c00045486409001003041903201c40da8007015010700c0c0e900380c46000803030303102240c01d000743d4410540700e407440151504101d940e0500b0024101c510013101303400001400540c2c80343d4440d5421640c038074040101500448a108100c40000b100640c00514000c800301400d1302d540d103803803405080700c1c0494544800b60902c03070392180d4140314042044440301006581500e0301034565000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 204267940 1250 204266690 204266723
    0x703080a0e01050a0506010e03210307140f490e120304060c0203030606031b1b010c0f03061802070f0218041103060421020c04050901020d0608030403080403 69
    0x7000080e026020710350906007084144401c0364415440361000340c032042c00c032501c0003052681e0b43d04c201c90002803200002006004085040300a164400d0162a01d0a41032018101c1251036800c1036124186003140485d810300c409804401c070b010340d8451751246405c040100031085000140c442502c480b42070352104900c500040e80d4000c9203080403684d08481c0f02c00010f140011103a4401c403026140030b8138000b0b424601c9031002c8100c90050300000d18950070364035034044450600c807140035003140c0c18604101c030742090400054206000c100c030308000210072000c1440600100449030b881410146003010520800400ca0807003071001c4c101540068441c801403402c45840408014083d40c042d006035002c000d202211000e4921891281c8a612a020104014199501401c0d5802410402d1600f041c0100001d54416104040e1403407040381c50902409000c142215015180542e540e500000c02c2c2d1100740c101c2c06060000c00915000f1413500d45035440e02115400380e0b0000a05402050807400c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 204269190 1250 204267940 204267961
    0x1305060c070f060c0b13080306013203010305060f0103021c020312040b09010f030218010807050706050103050105010f050d0c060f051308100b060a020d0810180f0608070605070308 79
    0x2414007100344820b42d58461101404001009400300c3d8000c1444001640b001c04140c024070f01c4580c400d40c1981540c0340c4100544a2400700c00d4003440c64924040c101d4200710301401a95284201c419940d0764135411270800700e080081c000c1c94030300d1081000d80100016115500d40c1a449000403c50491101d0640b000900300b02c00c4400072a0450400300d004101e1040d00780041404102c01d03210864a4400b4920070703070981c003072102904603051852400104c2940101100e99101025240c1a45040305d90381d01c420803241d080c5c0054039180e554800500c00325942070029400742104030b0300408038a03c6680c1c0c680304002680101070810100002100a642c000d000380ca81502c00a0100045c40346c81d014415a03410f210900c3d041c45605200d04480030342003080454400c0d1880b80d0103440b1b6600f001005417291003026009a10308034607218009941098150b010b0220203a840010841615440254044e10100e4104c0c056a800c50781d41048001e4100d021a103595615007070043d01d55544c1d24000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 204270440 1250 204269190 204269203
    0x3170907030336090e12040302060a110303100306060501090807090e0a020a0305010506010201050601030218010c020102120a1815090614091f09150c060e0f0d020a171305060c 77
    0x3c40d500c0461a280c0d0411402c4462450a030303656918104040526481542e64641d240e4850b02d08601d001c220600150070310000500c41414141002202e400d440d460f42c61559000f19018401100c0501e0309008010f0140907140c0100024030b00400d40031f0410754001c0c1c0b03d0505200d00c1c2d40300e580e03c50503040400b900307004c0340441e69001003403800000e9990502c0c90190504460b80d45c010b506c1c220008910390b000303100795618038503283c00c0024a144c03080f0042d641c0100e4031030164154450800080f407a81c02c900d0003400719000503680c40d100510704840d54810b8440741d4124450030709001c0c0d0540c910316400f50308041241c545203801025181004411402c9205070358001d0380120400c2c00416078141607015100120001c0c0e035880f01050394520074072160420f5a025180040e0400900c400481c60307a4100c80303404404401502e1101650014641c80c0c032031103c10490160b0050300003102841450071203200c032641380d00300e81441d1201c4446c1120080c822405042c2c8101c402080f0880071103010001c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 204271690 1250 204270440 204270497
    0xe0109050313080106121703040236130302032203150605130b031c18060908100204030201020a08031e0c0d06210303021b030301060309031709070303 66
    0x280d965802c1d8421226100c50420700943c2043c2d030078403000040100d21075401030308464000119aa84000f00c411080340340d03002400c1682d0003003d500e00b8650359081101c940c1480040c2225200c49820202540840403000a00000c17520710003250070b0340846e0300803003111751032981d0308810340710b4481d46840303520032400c40c0d000030f41901c80c2c40384c0c1d60725103c10301d40c407100503a281110344500e020584035110041d654172901c82a00340e00010400880d03400c0c0600c00e00c0c00c100c0c00382060b04019641036040210111543d10541c00101082e4003001151001e00c02103204c5c1903500340951038030b4210340010b590b071b0f041c1c07000050080c00c000002410042c0f071511030066444201507174240c80d0501000300c40d056088100b0301e20100c1d03d0040c0000351003403d55615840c05904110001c090001502d042e4006d40040349520403041810749202407600c01440218082c1146840009010740b84d400e000300044551280c400c1e090310000c0c140b0801a0000554200303da905150100113403501d4074204511801003c003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 204272940 1250 204271690 204271693
    0x207050f060a02090a080604030f0302030603012702040c0503132909010b1002071a03090c090708070e180a0506040f090f141204090902010e0d030519050901120e010905 74
    0x82c810001900e400a002540f0111007a00115440c0d605080e1101c4042d00e008002c601603003c3d8450b018000d401456000200070000541200d1103a003240c45081a125004d10042014036218218505403003050108016450818103525203414900e01c8028198000790601000c5283c111610340c502c00742000550410310b6101c00b0b4105a05070701d001c2c01c2d00001603845010180000e0055a100050b0700044540c1604900b0220310039a00d44803140c1d00150014403540601c102400003912260f011502030601c6540f504901d240140340200b0240744241181e10443c00d0540003521040120a040c1c1c001c0c54030703000014541ca600000800a0090295000d03480d030034900d000c008d20402c410104d01c2c0a008001010922a40c02c40f240e40701d410000c00e00031481d01c00d00050150320b00c03a07400f0410340c52060601890400ca42c0c40005d480481c1a03a00300c000401c00548000c000c0c06803a2001e42c1c0580c1070600ca8240a141d0002170144104400c0c11240695102002d5011400075045038003460342280 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 204274190 1250 204272940 204272953
    0x602030d0b0a0b0d0c02070b0c0c0405040c0905070503090c060708090907200706080a050601020604030809070803041202100806030601090905010213060305180d050f03042604060306140906040207050f 88
    0x1005800031748141080390026006240300041c01c07411040131245076820a0007e0607501a000d01004001c06001d841664100300000703000c125004240f0600d80110340300d4807129140d1130715107a003910300b000f9590960301609040c05014001842c0000380c8002080441e0300394801c1e03541e0002203400007820410150800c1c82030f102114030000114a06051301d805507500301d410307600c0c0894103065039400e88400c3d005901950002d40400e10403201c00307410040f00c8081d54101079480f80c1280c076641080e00440b80c03e42403020f9040451911000c00b65000d88079050009440c682500025110700051051100b103503100c12030041001001e504072050b5032341754000860803d0325114020000c0200300e41143c2c004402c0e08110300325000c00990700603603002c03941d100c0d86010a0180070744c18a409c058400c81d030100e00b6202121341d540e802c1500c0441c200c0c40031000760b00c03949003e40050aa407001d0f4401400d008580c866502d250b154100805c0e8044020f83d00541c0c0d80340796140080c50700c801080100490700400c1d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 204275440 1250 204274190 204274207
    0xe010e220803061017010504020c16060206060901090e070b0a030e0a0605040611071e0c170f011d06011a0f0a08040507090c170604150b040e0a0203010602030d0b0a0b 73
    0x210107540960000c4d6140c56003061840390a031030495442c034100302c2044505004014034501038004080600050040d241032014202e1011410300843d000040560130050402909007090030180d4010524800300340110400f80c4000358841a01e400b1b00d104c607080005210b00d18030b00a030015030000f00e046003281c5420065040602c0140342c141c0b4100c03441401c103e541c6840595139402e842485400031381c01c0c4841c0142c940602d1080361035000c00c603914241504001051074011041450304804c010161011403010b09140c1e0840b28201040088050080f2000e0031001e00020402d06594030003c0045051030360950040282c00307441350079282c850b000900c03003400b02c0d4071080d51805640f0400071604040e0f02e61a4041c00d484070701c2c80c810005001100881c031840d8840700aa60003010180c80020203001e40601e800314006250000407104030005410000401c800c601568031444040e011030540d41401c0c00251a8881e5000a000c255281d00460042d5510700b00e6000003800c610000a9948120b13 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 204276690 1250 204275440 204275453
    0x51608160c080106080708190215040b0c0609011a0909010207121d09010e0c18030607200c01090e0c0d0525090e0604271109100e010e22 60
    0x9000b803006950a0040c00903c0b0174000561606449222003d4004000680015083e0250b200380982c0d004911035403001c000c000d028000c2000e8080360b08000d81d42d4944481d2940b4229020f0950030f00d030ba14103030a4800550040300e1600c000501141c201c00d59448001c140c40c06400b5504d8058141280401491241500440a4000e54904a04034009110490f041080115092117010b2041715020001b0714240d13584070080100700c0c440013a440300f0000700d40200c1c2c541103080751583c01285000c55035061003541320301d0716185400c242000340350b2454003000003004143d20f849465649070442c0081018801003800740c41401504480412641c9405005a102071080c405482c6030f520025110224a42c0f0440c00141503d810303001e0001e080d101c1805000090101b920000c916031610b03150002200c2ca404014002c10f80035401251019185100b000310310300018100d03140503034a1031400c010080380180c406044a410b8488498551b40700d91109100401c03100303403810303071002d0030000c041000003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 204277940 1250 204276690 204276713
    0x121509050601080109050106081b1b07140607020609011b140a020406080c0f10020307080313060501050102030c0a0b070c15060e01060e030a08030903071a0f150105160816 75
    0xda0342d83c8810390741c80b407044c011100c00780139103030005070110300007004100c5241d50280301c0c06140ea44a880d190080001c0160403134020a500802d4000090410240140420451440008848640c505080d95001480c1c0c0d01c51007008034140040e4140980b0342c50405804c1108550304484500c0c01842c00800c0142c680800b004204d01c0356241c80c4002c121080c0024517046144000361124a84486c1501003010b100c0c003d503213030411488104000c80004040d032020790300540c00e8001d8080020a0361905000303035101608107030304550052050480d080710009841039481c2c1c009000300d405450342075044034000314211000c5c0080007160408a40c840c4140d006204691000c04240030307503600d828040f150001304411080d40340d840070b5071010211382443c005581081405040f40c0c42c180c0c56690b111006034041c002011648092001c100000c140354910907804030800f102c01003280c070303908006081c03801041401c615a07101440c1050400500c0022a0f4a450302e080510045140c0b038038080ca00f07481c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 204279190 1250 204277940 204277951
    0xc0e0105100c1a0402061c020c01060501051c1a040c0f030e010b01020a080c100c02030a020706020102070b010905041406090a0507150807120b060708032202030d12150905 75
    0x104810350406840390001c0c200d6075a00010981e00a10b60a0241200c90f1014006903417081c01003150a49072080c510070200101c0d4003000250711402030041540c02c5800c030760300003814840100811401c80300c0000e0702c0480324010000001301501e101ca03815584141103001d640e0400d1a0560792041243c01c881e051010090551741842845100d4002c1070aa0700c8a41c074190250f03001002c003074002918100036007003600050046501f1070515000701019107060121140150b000000e42e007050542c180403440140c44180000d520742602c60703450f580039400c14400d500110741d0342c20100382013000e40c455140230001c5c20000c440340b41c140a04183d44501c207584086602e81310300b1900041c1f5050700c11001030f10302060b8890745e2150740e8511091315151312650202c12826035903d0382d05116a581000b074040d49000d034544039200e1520106060801600c2c0d183c0a07080903003e995480181d40002c0c40d4824001240b400100c1080d90600c038401400c03041c0e05640c02c00310100c202090707100341d95002c00c0c03251 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 204280440 1250 204279190 204279199
    0x7120f09060b1f0e132a0f080f01050409020d0614100f03021020030c030406111606260a020306011704030c030305040807060905060108070614040311010306030c0e0105 74
    0x1128840c680c1ea0000e43c00e002c80020459409204e0403a00c4c200004144501c0c054a000c00c050454900039581b01d1001011304802c4c0c2400710b000d56145a11401c140790149403400d1005860911582c088512401441030510a075100c004c86011500d4040400b045603600200500c0f5403203507181c140c240264101d0301240d50440d001800515580052130310f8045a0700640b4100640701103540c11642b40c803405c41c0000f140441000c0820300c65108000400d541e1000c82e01660301d8a0810070300411483d00700c0c0c9807202680c0207061007440401c0c04c00350b54080f00c4541c00c000d85a5049002032a43e642c5120324881810510f0a04100040c00f00d500254401d090036a40e400310a1003a40c1078805030441030700c0140000e0042e030900350000e8000d5101580107801a0581400d0141ca541e8030019204a207104a8070354010600401030a04100010405041a8248009003c0e403034001e40000b4003c1e440080c141559490700001181d00a51110003d1a080b02011001c1611001d0200d2103170310a1040321b004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 204281690 1250 204280440 204280459
    0x20721121107080d061a0a120b03030306010f031b020a0c06020610030f0f080a0f180810050a0204030804080f160e07051810033207120f09060b 63
    0x18008148946599940105015070426582d6215403030503401a111120035a0f903201e5010900c004241220702c0141c507001d5185e0380c1e0b095050b1000f0003020b50002e0784440c00382881d5503120b29540100a43e03a11403003c1c40d085186400c5a08101c0181141703060140c0224900e074041a1080c0d33002c41c0042c8603c2c054420341500b00c0c4c0d1103000303d1b5180021603801501c0c21aa030001c0c00082d855150f0070000e1801020909442ca20f1901c960b1901da000004075400316000c100a1082242c12500703e81d080740207442e000c1c1032580b03400c0b9000c0c0c03030b2500551f20030340642e030320700c00200809010360565001e9600040850384860308c0d040410380e0741c0d14080da00c501c140b040c107010f0880d00d1281800042620703d216402c4115444e808005d56180d040020a85126083e0461781011501ca10a41c1c90901200344d07030201d20017090300e160100ca0400f00192a25114001c80207601d4000000714480d001742c0c0764609901481342c0c02141e0f100a01d0b154080801c041e080c0040c40f01170110a800103540200100c948404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 204282940 1250 204281690 204281717
    0x5100302091603060b0c0340030212010b1f14040b030405190c0e0403030f090c06090902030609061014030a05190903090b03060d02150307020c180c0a03020721 70
    0x207240500040303400c19074010450f00462104003a88e9030b49105502e200b207e0a4540107041e001504c00700306c51105010000d1000b001507260540022228a5106d0020084400c85502080001010400625445001103410541b4600c0340c070310385165a0000c00f9081c0c4490f1540442c401d03c1c0d1003035909540c24405c5c0110f4214600c034504120340d510f54040480a2110b140c08403c4a1482e8014010b41c103240d5140c41d42103000e20903024480149100d41c50072011181804c0c0003130140802500301d445400e20510030483d190710380e6034007150031500481e05258150007d030421610502400801000082d0200134845018440c2d00b00758020341d0840310100c007140d81003e00c6021602c0e05000030340058070120080003c1c40c41140103542020740507040030445800c030340114140c2c500c400c0c94010443c0c0c0c00001c0214080c1d0511050b000780b07500711a1248140c0344481c01c15802c0c81c0c0074151f92582c0c0c100091031844a030003035040728035080d840703541c03040303400340402c1144284828659030401040e064035000343d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 204284190 1250 204282940 204282959
    0x3115120218180603060f07020304062a03090816030f0233040503010605010e01020a03030b1203070b04020a0b0f0703050a02010906060303020f06060307082d01060b04060315050907030510030209160306 88
    0xd1090145230b00440c00c0508d01182102e9944c0b128140382d481a680c0d0744289001079815048010385c0e0b0080d00c84072881450039102615041070450208009010b0305820f00014809040640a5036011519900c08000d29056450400194090318003070101001542d2150501c9801510450341f049000b0001c46549200545200c2036000581e801600080d4003140000c0c041e900c01180d106018208507002e1054000c074034959441a4800d4a0200b9a082040304601d4020b100c0c00107460701204042c2090364841d0039050b240900403008050120108024407168401d40c809030030141c03ca00c2c10300400d0307580d08001e07480384880c406905041c00b46400150b0f16060025040040b80c1a02000b0803040c401c0013074504482c909035404602085642d0804901c80381c0901030017000e0089150782aa59528002d0040c086440c400032020364818860005c020301d41c0ea004645500001a080214290ba150840c1c0c00200d2a1500b000354040c0e018401d000e050781c4902c00703d5a4081090703c04101054540e8401d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 204285440 1250 204284190 204284221
    0xc1d010501080f070c05061f05030a021503090c1503060f0d11040e07030803010602030a08091911010c0609060c02012702060f311512021818060306 65
    0x11030100b000240410b1002c180e10b501e150b44a4020715200c40101d580d655804c0c1801000c2d1452410310034490325001550200071403400003031000300c009107180f0b01d01d40c3c081085c1056012020305059004400035485202c244503010108100801180400006040581301a0401d90302c56000f1045c0348a500418208000e05480030340d007007580340c16800c4d558402c000107001c543c2c0c0712072270390b0185860000c00149048003450290400e6006035407030790b030006d0700102604402403440c000c0340c0c07181c2c20182c030301c03900700303c221340f80503000140e007c4e0383c403944001030303a031040d5030b01c03008043c1e03441c2481d18414000258469106140d49a009001140f85005000001e82c0e19200780030f44d820135980000010318050780101604215000c90a00b0f00700d51066003403986600d03014100002052080c07032880004442000d5000d0070207a40e0f40480d43d480082d0040000d05201c80d0b44c01140d60000301d0a902d6000000c06560f80d803401062061610b40564107003a0045095845500a10803070020441180d48140513 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 204286690 1250 204285440 204285449
    0x90c090f060c030e100815030705060c03030403020c180a0b010903081210062a03030b0a140312040b0d0c0504080f0c0a0e061507021f0e03120913021309090c1d01 71
    0x10f90600341c070381403035003081c5114200b041941031042780c81c0011a80c940c0e038090030410f441030015580b2483d2904001e0b044c42030807507580d03101e042110552088003a4564500b40c010440034000200403101c400181c4201d02d070b94002400340d0001243d00c0b5044021184551301c540c120400f840080c507a10704040d03400000c0381d24171010f03040c6d24540e81008000395100083c40540a841d020072620044c60100b203050a06400c403000880d0500355035141410100716012100d124403006500d041e2601d0f40014113030044440130324903542c4800e03086480501c1802030702d004e0041a425105c09040800110f07a441882c41c4015015003a83c040000b0411640a101445050094488440c03441c1d01c03ca264620340c400305040b42e000400c41500402c40d075060341103c20b130034081e80721040b90300c051004042c1351041d035207010302c81c250040021480079102c003c603200030a6820280540c030b484400b540324012100d42c2d04400c01079868240e416050102c2203142d01c04442e818424140c5000c00e480704104038002c00d028 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 204287940 1250 204286690 204286697
    0x105070605060612010e0a0b091e1b130e01090e030f070c0b030103030903050105060f0f12011b0503010f0b07020f0603040510060303080a060e01080601090c090f060c030e10 76
    0x8501051490300810741c803840c01083d003403401138401d2100340c0308a000e8001d224030710044070402200340340d213210310000304500315801103151500010040c80840d0000000c0134007a001ca006c00c09803580750181142c0c481e200c0042989030a0022143c0890ba44c25101e02d48079030854400020304c9155511405460240b0407005c2d5181c85001280c1200c260311400040320305210410300080c0302c10070300c0c0203140650702c00c0c1e40308030509180d41002400e450b00502060322401301d002c90b04030702d13603521002340c030151030140c3d0481030100b602c6003114010502885801d040800b085042400360380e02c0401581a2600c00c038200c201940c458143c40036070300907900000c0d000702d840c128180d020303d0184040e40e0311620803c02c83c0c5070700144007113010640c2c01d65441100410b402006002a000417030143c08050045000c40c43c06940c5080321182d598241880b44200c4240d889807203114440c491210b19001d0460b4214000965683c3c01c001000b0030709105082c0d00080c078820528170b551616800d910200c0300c3d1680c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 204289190 1250 204287940 204287947
    0xa050f06070e06040f0b0307090807120210030e0715020c030105090703020924010513030204141008011512050f0f031c0b030c010e01050c0d031d010b03030d0903021f0e1b0105 77
    0x20b591b100d0580c4050003001c140602c40364009810081003104602405160498071001c80302481030089601b4000c91010a00d030400011140380b0400281c440122101401040040c420707038441681801d170207180031078065003054200701d26800002408000c03a8800e07181e20f1402e503175404e8941d66542011aaa501e0301610b40e1651000b588075101403c4100b9821000112060340c1e82d00050844134941c0303010349526251781c1001a6540e0383d1700480000c040080003444107911034102e4095024160058202251030701d0000c5050060421020a00c80c00c0c01c0c00704c45140451803181e0f42c1d20f130800b079050340f50411341841c0234039001c000d4020206c2c02400603000b408006004030044d41e0141081c80703003174100f010500403192031007410010180020031540b00040c14400884000781c8080c5802c11503000350307051411000c40c6490000440700c103034020100016010b80309280880c200b1030750f0020491003c10130301d00b0b1000030303499510016010401710200c640c11a1058001122403d030300001601196052 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 204290440 1250 204289190 204289199
    0x4030903030e060909041505090d02030703030f0b04050c0c0d09030c05092505090a12030f12060801050103030815010e0609011101110304050d020d020a080403140a050f06070e06040f 80
    0x156030240140b54018021800c1080304000701d984201c040302c05039001901c804540c200071145105594001040c000601702e0f96840000180da070f4451103100074201540c803840310240001c180c1c8607a00c0c0c0c0d01c0052080c45241085d0340c8500d6250410404030505004800303d808131580501c4019003202d40c040f0380050307001d107440100048100700426140640f003c81484010002c54122165841c10742c50b140c0c3c6460b00002000c0c000711120a0700220040c4121702c28400110b5003249414021115074603110080500f58916500079154550200a10350700b0980040304040c0c204c01118419084420580342c18201d4900444a00f9a03540d030581c2c01081c00c024034085c03075116151404202c044c50001154000c4562080d0040303501c100c8081e245500b100d0303510303070718680e06107c1c2601e440080c0c0700400140d4106e440d641100d20441c40014180d0400d8100110201003c3c0400000031b40c100c001e50300c1c1c00500f1443c0e03644175042200d814000407514030801c0740e103252600c25102a00c6007481c24031802e500700b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 204291690 1250 204290440 204290447
    0x101506080603011b030e0c060f030a090f05030a0206010e0603061311030309180907290703300e071a180d03180b0a2304090e0c09010602060403090303 66
    0x1400c1141c0554075102942061044e500d5060310a50041d60300185c030014050500b03040c00340268074070348111420040b0711181c0380c1c0ca89c1a207412440c01c40d40014100c10905d0408416804003500a01034000030546080060b0041010b6049a85c1c4c0e15401c00e1a80d501c0d020540c98510450754440070041c010b18a80110b0942104405140d00180481e0700c0c0c01a1100007841c81c0749000c0d180c83c901d6440e00200b0810308818080a0024183c2d5002610024500c3c142d80782c8891204811a42c180310100300303c01818800c551003c26044460400300d51581c500c6242c40c3c01440d1000c510541d64240150001d0628002a520301240c00c4601d8400000ba0050341e00c45880d0b001032000c0c031700400c803d51a5059aaa00300d107a90000b48251204049185440c403940c1c58101d00360f120f0a1a840305101082105030800d2181c5052aa08091160005c016120a0740e1a005079003100c0744041c80d10765001d552100000c0d43c1190340c2012119198540e80c0d900017241d45010071280180000c945400400010f0300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 204292940 1250 204291690 204291707
    0x18170615030d1239030c080c090105070c06020a1208011401080c0705010c110105060301090f032708010b0f0a050f0d050309041107060e0d02030307140903030a020c03101506 76
    0x40324041800413946640c14020181c0002084401000f51000740d49015040040555609142400d02104400d50300203403807040000e00825040b1000034424080b68410350454030441c2e0300400e680d000d01e4407028029903441642070112414013521001d418054051002281203481468440c0045ca519400440703161201801902d4012014020741c00029400c1c080e515003084161740703001d1084070040d1154255440504424040d034074240190000c02e0220400000c0c0540506200b0488003c0c000900300d0b200307004107945141031041c00d0200c0d1035001900800304162088980300700074103200c0c0403c107850440c0d02c2500d500c254441c20b44007035410920114446280200203690808079054082001c4c1d411204440e2065a40098808108441803169003c01d5840400500c40c15a0350200030303580b031001501b5078090151903d1907841407070701c3c001100e00c442e0028064a444080e106006035940341c21030036581c440c1c0100611036041c103425208402121040c2e00c0f02c8040145441800e40d02c00c1d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 204294190 1250 204292940 204292967
    0x105150103090204330f0605030105010804030507170306040c0207050609040905211e07051015120606140904050705130b0d050c041b09090c18170615030d 68
    0x949905c050102010102d0480580c0a9034840c0d400441401141c0b811042500d40c124100400782d45109104003948002a01c1c1940c1c001e00745000c07607466a003000d40e80380c09061002095050120103800e018080103000d0360195a05690034024150018030580c3c8a443c58040c0c80c0c2c10800600520103646840d40000c06200c5c002e4081d03c81000d65910080c2004001c803c0d07410075040c002a40c03026800008000c0d000d2812084505400c000c00359070b90a45407101130503101e5170b07161143c01c01001010b8003407444000b44942482c0c15584036507031030034002803c1c0500c05d0a41c48102c10500c444c0c5410305040c6548120742c09000f0700256400c0904111004100040030701c0000d5590004541517101e042da03020004c0d00440c014500030b42e000c001c000956140d191021950120740700c1050400e500080050255110400d011960350309200301110001001102c200d07800000020001d01640300c0d007008101d15117030074103540244d0349070550300b0381580c1c04000040c0c0541c032095840304007903c203040e4021500d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 204295440 1250 204294190 204294199
    0x9050a02190e09030a090506070506130809030714091f0b0304061509140604020a050711131409010501050a050a09150902040b040501080105090906070c11030312071101051501030902 80
    0xd0b502c8001c0544494801c8948180907803000906102550304640b800c4003c0a0486000b480d0280640c2c03a9070301d4030b60140c60609003042c22400d0404000300c00e81614201c9001508641c4420751f20b41120065500c0d20b40c1241c050700002c0c0108800035140038014804c03c41c09061003132560b240440902c0c0c958001002070340c1c029547e142d0344158243c2c656080d402400c0122010440c0c20b140c00380d440c2592400f8042c1e81c402c0b40304018403820356403c04107450050740c12000c0342000c0c4658201160544040e40b2105410754502100c2d020144807604c0260b000306102c070000c200980e01c4000b403140416071405029407003111034408009480700380c0c000c0380c04418510710802d04951348480303440c160b80054008601513007001c2000e0026581c89a040703030044c41c040b0383c401d006080c054003558885201500c0700f810001d80c2d054030707418800c66104144003084040d00302d0307559681d0f030105004000c50544104001507200c0d1000c1295100500802d40610040d1007103085c45500031300154024428094100d030003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 204296690 1250 204295440 204295489
    0x52203020a0f030f030e01050106080112021201050f0f0f01081c180305060a0f0b1320120106030b061c0c110a0c06091505250210020d030f09050a02 65
    0x6200000c039a8200b5100c0d403980000c1100000c800342c00c0d00c0c1d07682d0001d60213a1404004107c1250701590302811251080340e606000c4042c0c1c00418883c50188900c4040740d802c2c84148110000300e0141244110b0784040f201000d43c4541c03000250101d003e00c40c641c100d50142801e50140d08000b0141c03001e804040c28100821020316200d070181c9540d980c01964603821440030071041c99480d003d16422804000c2081261218034400507a291100d4003812030907039560503901c0c0d0400016095020010004603003140c48061501280f0031440d024014140028204080442c103828800d094030243c040c280303840b819000c6400300c0800100700c9007000340100710100d69040c000031400d001040115000f0001d20900c1801c02201031310040311030b441981c1c40140100e05815042c1d0080c203550140810f0454209003080c0741341c0c010341c00c0306459000b0758030541d540c50300b0741c009400090402407494203880c00d101351281d17011014101c4a11300409003c0350448060540103107080c604d0070103080e01d0000595503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 204297940 1250 204296690 204296693
    0x70b06131d01050402032e020d1d031e160b25020f0d0504082e0f0902090705040b0901050d1d07060e0306040c0509060d1203020715052203020a 63
    0xe050104258041c002e9640d5000d01c0254201480305141e01c1d10101d20381f18180000300315492100300741c0541c0b40342a65020944590700f150942290000e10201c400810001404146182d281c0e0311941e01c030030348a15001c02c00440c0c005070006070741000e040d42c54205411000e6488800610000801941004a802d07213070450712105a42c01c45950782c169402403010590009819141c2580c02c0000381c00d000341440200150500043c80c43c14580f10b418910811403d03440b00d289000d54007449807503e040c20650200201e040c2a030090010900860b4a860142c43d064400e40d0548660f000c0c0c01420b2000300550b004550250005103029142c0700000070b4a07402e050a041c40d503c04d80145198290000344007040080c0c0d01034641001c05800f00d01a2015040030b0b5206e0f403590480b84502c601452420780041c00365520400500410390704001045410780c40000006c009520108045a00c0310b980040040c14012510440384508114038144807554a40f40681e1100c2961620480c2188901ca030100c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 204299190 1250 204297940 204297971
    0x90b07020a0801110c1203010e1f05030a0b070e0d12030218090a0c0908010506060a0e0f030703060e0d0e0a06030b06040b0f0304020111010207030c0201050d020d0212040c060203070b0613 82
    0x45440a0080c203607440d01d00303170003102d41441d8088407645440e00081c8014801c104840244035007000c001d000d0800280110750706500c0e200e0039036108550501860003d0b00900201031545031148440e980c540f440321042c3d804000c1c20802005014082000713011060305001d02a90007016090410708400b80510008000107800103c211500c00d01d50341c44044034040c803070b00400c40d0b50103013007000300a00c00391901401080a601a0031420801c1200441c02c8880c1522098281c1544440180a035440591282041d40c080d025040130700006104002e48296110300c07914441e170455030001c1804414500d4542c04401030b20340c1403200760384403600304000203486441388000c05241e81283c0e8401e4403490140009885a1522003c00c1c3c00350340108103c10009602c0140c5950301a42400d0950300c64548450600082c0a2484013140440c40080c84441d0000540b001c144140e00c40c0b20751202968480340100d84174002d9880051084000c10045031881c41d20584ca090050308504000401d20509118003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 204300440 1250 204299190 204299201
    0xf2a030a0e030d06050405060105030c19090302130c021908042607090f0605090f0f0c16200604060f05070303090204140f180307110d0c08031201060f090b07020a0801 73
    0x482c3c0d1a5a4840801c06030406000f4650f1159007400c05605514102482d9107a5214030689085102c1801844104081c0a0124400690707000740a851014041105010043c0a4030000101612400d52482d0a285000071440b600a90003401c142c00c16141a840940190681c0440a4503900300c02180c1d58002017041010f0040040d401c021035440071920103207040315000d41140d40500c01d00010401c4160b620400590014118010360401e40e490b503882d003846008242149209078603040c401818095507110707209020419100030240e80d01042c0030007002d81700ea48111400304115607555401c05000e0006403c00368024100460701301003aa0029088810004240c2c00d003480301414410398001818106030f0252010907045d41e078003882d2007466641d000d2020000d203080840c016019507901c0703d50420039a1580050283d100301c0e15803d0845e00c0c0d0300151003600c0c00d10340100c0002540c500c110b0241c50402c0c0c2e41e88030040e00c10305180d003100302c540c4603a01c1642c002c4241c402c00030382101c0034441d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 204301690 1250 204300440 204300457
    0x5030d050906071a040b07090f0515030a0b04020d020403050f010207020d030c0312020703051c140c071103060f04140109020a060c05150a02030604150e0606160b0406050f2a030a0e03 80
    0x19a1010301d000c7c031340a002c0034800c0c1c03c200408048050140701e15115070200034104020556025100e0350f640d01c06001500c41400550f42244c00030a030002c11f01c94507009801030b28460340c01c1d039030b011000c020107500300e00812002035032095501d5040d8001c41d0043c2c3c03034905000d001345054156641800c01c850185d82c01200704a0000e040051840783c00301c110402080202100241440b00c0c001d034121400700c2990142c42e0080b0900001800400c101322400c0410310280301405a80c403915000d001c1c4c040303815085405031006004040a1494820180701d11040f1650040600c480345080c010204c03650581d8441c1240c05103d41c40340040c041c0144444180b1602d901040540c0d27900d800e03014001076520141c5200003842e2150010301c1003180b2480c240b98040b00984601c1d45a00d102c04941441c504081c3c0042e203c640048248400d07c201500038030b102d189451002c03078030b6844400c440101700d00c183e0b070342c850848a0007802421450828000350380200074260042404560003064500707581c40a01c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 204302940 1250 204301690 204301703
    0xb130506122206111e070b1506070507080706170c0406030c0e0306090a0201090801290103020f030a020d2d0e1e070f090209030316020310050103030c020a05030d050906071a04 77
    0x4401800180960503001010800d010180c200046e5a0304c5247e80c502c00b074112420800750850b04203064039010290391031250088100c4841769992651680c99101c14003941000408142800c4010301041d18600e0080b8100084a49042d1800030103c0060040d5048034040100e07960007422255010402d03140601c1a40014080c0d02d81c1c40d10014090900c035a0000b240c0703034108101840c2151008000005004c40400301840421070540120002d00c034103242015000e801006204500304680d0142040c0b11501400308220005405440071440d1070003680918441440750310100344244c0c2e00508007000d04101100c021286015900da041c2e1981307080c001995009000801604664851600082101480861034203410348086501c900c00e80340352442034030510140f03004540b020860010704000408081244e56128030f801483e80c6132505040e441441a0240070401d4580803814484180242d110f103031030004a582845603980064000356000002010051a4880042841ca10aa200d503c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 204304190 1250 204302940 204302947
    0xb03030f21091207020108100b2d040b0306040f09021302091302040e3702031e0106091208040305120702030d180504020c160b13050612220611 63
    0x180c03901c010400400c0448160f02c042220040c00f08900116126290217103070a000e541c1e20304003c9803c0700440d5010020482d0005401041c2c00340f4950000001c41ea00302070500d01200c0401081c0c031500503801902c13003200c020000f0030060300e482d5101403103070140c1e42804201c0b00700c2e0740c00041c40942d0401c1000012900010008418a00000f400d00b0000c035080d801c509050400b03c40098480c801012040c003c420402c8e07440c080503020f045400300b84003503500d400c0c5c40580d0380c0e1010040c1d00300755401d0128658203a014000200f0480885040c1e940c81d58515141034500644003d00a4218006590003c010807001c0089601030194081c80da0f20552000c2c1d42c3c460f907206051800402c1103110b42002134042c120510392154031013a41c1110b0080b2000350b190428020028102112410411990300300d9543c001000c0c0102c00180055048000b0104042560f030070a100ca1841425041012080f044d40010000c01c3d455415400e0480d168a0b0456a0202039131000100ca1107440c3d141e1503a200031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 204305440 1250 204304190 204304237
    0x703060209030d0801030c060c02060c010c0207060e090f06010f180806010e06032e0204090c0809061602060604020a17010303030501080606010c0b0f04020312040603090506060613090b03030f 84
    0x42203168082c103d145400080d9605d141c0700c2202c42d59060141104108a101da11802d540d149000c3d140001c0c0210000c018900e0004d10196881e095442035002084480180226625091541e40d00c12544c5080b180b0b1a913503046c00460300b84034520030030070a0080094607000341d464980700c050301a0035028010001941440903024403040010f100b10306ca82e118885411502c0086100c1600c00400741820b00881911301030326070f020380641c0c0c1041805a10309080321075010740c040c030214050090b0700c5c2030321a180c0340d1600c852002d034110410440980e108001007001400e0a9008040041c428604100c11751002040c51745214820780c41980080d40300c40040c01455001d000745a0459001d080030303a0301a03642e81c0e8800038440000c001641c4502d4001c00503095440034840f8614040c0307000301d41d0780d0310341c0c41e40e47c00350007004901001e0701c0a10810002030040d04108003101c031884e444027940703180c1c1b5190034016005030042d00b400d0b40c0c250206020420301c100480000e420a6400081d800a01c072441 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 204306690 1250 204305440 204305443
    0x803010b0304030207171005191d0f071203050d062c0609070c030e06040f0f031515140d150906050a0e0601051302040f0b0703030b0306310b09010b0a0b0f1b0c03070306020903 77
    0x50ba1844a035980201d00304025886a0030b10801c600369040c101280c59000e2010326000030104717944800d90ba010384001404000940d00e803100140414803100e030007140c0705c2e4820700107100003c44019000c56420700540700400d0141400408640c0b00400840c94251642e0b100b101107141c40d401004000881c000900c00c101a041e2051103401280c1d0080001c40c943c982d0440d0541040d2064141c480701028840100c3d46840d0100c48211f600619004841d0380030a031968010001e225040c0c40c6180307080d0128075010341d40e00074400d5446a40000300318507401d040801007032801c0248100035199080200007405400c8540d4800100540003140b41c44100c1810041c05a83c0282e03480c51180e0441c1080080001e5080c8420403030034640200041c0e90f051a224081e06482c5910016005503100420840c071118150090055001e0940d60360000a80d10074103000c5501651165600c1e90170f090003034102c400b8020842100c130120110881b108264014042420030120390000d9519507000102703141035040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 204307940 1250 204306690 204306703
    0x231b10030b030109121e0f0504060f0201020d14011e080304090518010509070312050910141204111903050c090a110a0f030b0f0319020d0803010b0304030207171005191d 74
    0x500d4107180200400e01f04000b0120f201f0b9000d41c2060281107818610035500c00d5040d104980c3c2c002004000e21103091540b2524482c091103201d862292240403040c00003001076450f030844807080011800d05080416000151000811030071010060042c4140e01050902800e4007800780800a080079500703504185d01e8840b4041008005d005041188001a448031020106100b0283c90181819075000044030440c0c4601951107a641941d10180414818400b81c006406102101c50048412041881040301c8600e4400900260084e03140320b481400c103009400d07031085111100142c2d20358080048078282d0000440c0300c6c00502d942008880c0c082d0541f0804402010032200503249444800000e80e072514030308c43d885140d1289400203821900d50301c8444480e03641c403504c0503072a0368582001011940045400341c005100f4650009015001c85180c1e4010070300c0d000150800088115400c000f801c0054096088200e142415a0888034030344a0188540781460035660b10104101c0c0d16031a18a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 204309190 1250 204307940 204307997
    0xb010c0813031e020f10031113170109150f0f05010905040b0708190218060307020a0303060f03170912010f1505090c071202030403231b10030b03010912 67
    0x3a1260b5100250341c0710f6410410484080f10454140b0b21b003803004502401d101404441031001c0820a2807da541d507110b45000c1e00c9000203a03c40e004140c100240c2a941034100140c02c1203910346903072240100c1034005005c6074168010204015000d088210100d5100760b1000725083c0d80c0d94240803c10085081c926001007052404100c1800c040c1c070000d42c40e0700c0076012000390544c00600a04001d10a654a580d8407100610b03158032841c050001135100c51100c141100001e140890205041e1504d070a486e060b01e8202c644e11f901039000c4d114120069000000c0f09600103d41d404020200b8030034007428942d00e000100201d20a607003507544400c0408160000b5100b414000e08214000840c042985e4001d50002492030003101d02e6041a0304600c02c603000070302080c0c1101102c41c400c5506c0088404040d10150446011424082c00c4850054250b070006070b105420704048107210348681c0050860040042c00051714000ca0ba03280e06680d0720702002c08021480c9040c14001e2044500d40d000c0c1d000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 204310440 1250 204309190 204309233
    0x90a140f0d0c21060608030306010f030e0a0f020414280204080d0c021f0203070b13031d01090e100305190c0504150b03040302100b100207090b010c081303 68
    0x1801d05544203191000c45005481d14110182e660990440c02c000d00411000d0300450b04010094036805419207c1d4400c0345d505000c1480c41060b9a80240f0038401e100c0c0c0494104040d1500301c0450340d0b2140d42c91010001a030344113448616a00403140340c904424003441054400d001c6012007203010702c141e407504442240c59248140810402c0180110340851400200e00c0c10134042e44062000a04a0821840d040d401060111400710890b400200500c550381c080c4d90b20318215903c641c483d4a101400010040006000500003940b10420300c407444003801050414140458407034480108600003140c1628024070803080070414800c0c1401064842410041c26103610b01c8951a04c028040041c03281e2401180d0318903c181c4a0003d10340c00c0c20140844a08140d503030b0400b07080003596107064200500c03026180a4154803980b41c405005081000c054014000329481e00b03032080005c00030340214038103000186030882d0014140c1c900501c0c0c403454802c0d03101441425801c2400c102c41030851003000c1c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 204311690 1250 204310440 204310459
    0x302160807061409010207023607050c0f03040e01090b01090b0c010b060a1707110a11030708010c0f030c0c081801020f06090c090c030705040515090a140f 68
    0x16a4010042241015005022240d4440162501c20000d0281c40d1210007a800c680080c4a4600d0040d00200401c80c000c8488885900031940c07951a00c250031101400b030341c1404020300c0e42002100705055400703034082c02c150741843e060312019814082c01d09002714940d0400141071211546890041d400b402da00300c010840c10ba903400c006803001c0c0081c050300c5031450f40441d41c400100b200350086070b0791000141c14503485140072400039141a005801021540740c0c8840040ca04030310603201c5800100c1010000c103c80d09454642d00c22030303a016400940c0500400d040891024000d020380c1e0160051075135440c90b0701340b4544000342140c0b4841120810480d19803082004500e01c141551440c1c2000c07541c0e540303c3c170450b0340180d203084003070040c40c101402610104055410701007802507810704240c64036040c96503030014551151008541000110b8401e010601080c00d20070790b03048103c507010204600d00044080005c24242c2e440c2d1102000780d41d221314a0659060241e80b4a2103030350300b40c1e80c08a5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 204312940 1250 204311690 204311707
    0x40302181b070807150608010506010809030f070201020c06070308071e0f050c24060a080604020d11030307080414130b0a030204111b07080607080405070b030403211a010302 76
    0x1c0380703000c81d1040609071401084003400e00032054216010326500517213505170b03d070340816100301510603446810225440d00d40011455406002002c2c42184a400503501d803a2101100341695017090720305904620070144040b98030b4445000514000e030280d1640503840c0b40108004082812030102c088128803000c1101c943d4a070400e800200324501ca040c900d46800f0b000c12281c4c6014500c00d20b0384031442c8501034104a01d4665680740380a107100382c5071030207995122030002ea42c8a030140c1e4025001404d44161001250001049034000d113801010750380b501069072980c0c001c41c0c00c150441f840450142140018918003244c220f0000401d0301000d00904444400107104110303244000380c02661207a00755060454070208940c0441c499000b0805c140d040660226035a01c81405140c40c644500d00110b07001034003654400f0308c6190300ca40203100840c2000c185000170380002d80300300d050041c030443e188030411642030030550700b18a02600040c10100884254410700741c804105062503c100003611 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 204314190 1250 204312940 204312961
    0x40c0f0203030402060a0512040f0215070b0c03040309050d0305090f0d0b0a0e120d0204050f0a0806040f170409090302060c0a1704020f060c0304090b060909060907020c0306070504030218 82
    0xc3d84550111001c03600c03912510401d0f1490b11840300c001c10038525403803c101c00c0101d0011110b076030a000303035038000b05c00025983d400500d1290410290514120030000781d50380c116040150b9004e80302e4a080100b4603502d9010907071103810004102e000c0390010403041c020381072800d0b900c0e14202c0308880010900c4425122110308000c050f2a505805407100d45180f0400010485034010395800c92100d5030340c10801c0c1c8410002c3d049030140030b12805044190780040d1502a0400c0280c0d90720001a2102d900e455a51072290b50041d0811a4401e405100d00d007061141240038000408541c1c2011411241c03501c3c0007405d1600040802803090707001d0050f00b0346903038081e07a46852821004510a01c54640d4000074040041c07040f500c0b40e100303000180d2040b01d4107010018100b00d031a0417500740220780109040001d41d005c0c0b0951a90080c00e4180014400d00c1d20840c0303103400400780d00550b003405002e680802d050403c2206e500c030119400160400850603c43c038401c40c581c504076001c0401c0e040106062 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 204315440 1250 204314190 204314197
    0x30103170327030c0f0304030c1701090f062c060114010203130902090a090e03032806090e0c0406030c060509010908030a0201050601030f1401180b03100b040c0f0203 73
    0xe005410010000034010800d8034601500da000d05007000a00c89003240502e0341d07070f60022160241d140249041590998400420348042d40ea0100711741d26120308041085124540801031000e0b5992900240130200d0544514002000e00440300030465443d100b40c06c4a81d141140703a04802d0107100c09064086507408142541034808180c648081200c1883c0100d00d940608840f07840c8450780000c0024442006034001c2c44040001e48c0c50160080da1844000c0803070300140314121031600308100181210129003102c6000f02e00d0100c1501122032170384400d4080710102d40007840e0442d540e080b00d44510004100013000c201e0111000d0001034215503941030136411a2041ca41070040204111419a018101140c00352409808807500c40b0210b520090207480c091380c12902080c5001c4000c0001c181501440b030406500c2c4071440202e03441d1800f1502c2404043c1c5880f585983d1312845803007aa039090108014524100c000030800503188002c020440703442203541010700500300a040070030785c0c020094 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 204316546 1106 204315440 204315473
    0x90509030901020c1c080306040e03070f061808040302041d06040b060907110312090304090e0106030c12020d030f030b100c0302070e0621010f020f0d0c0302030103 72
    0x2c0c0007918000c3c058104444000000790b1010649180040d40c1043d00540f00090000210192b40c1c01c0d42c10000d82120222800c0e4160814050781d8061031100c4010070980c6010880641c0c0c85170154821444002c0c015a16524921051101c260100300e028204500b600d04a103403524103003203440c204071001d074407030600b01d0082641c3e42d114283c8030410050030720017140392800176025031101d00801000d031b00719407200300710116084285000703101c0c0c12115403002050690841c54516601c0103150006c010015040c004a0301607030b51001004500341c2c050510080504c010349007180038000c04902e507600f03c0c3c00720000482403588400500d002ca4007941c241c4441c691075076428961900250b46040c2d0001402c080304a02c0000d4203460465058541c0000074130001c3c0304040c9060780c2050b201d0303490003030380402c4440464100707004d180c00340021468114510740c1140d544259012207c000e = true := by decide +kernel

theorem cover : BRFrame.Cov 204136690 204316546 := by
  have h0 := BRFrame.cov_init 204136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 204136690 ≤ n) (h2 : n < 204316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
