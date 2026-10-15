-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5541
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:12:25.787982+00:00
-- url     : https://prove2.me/submissions/f48b2e2b-6205-4a2a-b532-c56b1d3b8573

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 996402877 ≤ n < 996582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 996404127 1250 996402877 996402881
    0xa030e1507141e091804050a0602030411030f060601090b0c1e030910020307060f0608060406050c040510050405040e06100312020a0204050a09110109080a110f0a080607020c0306070c020103 83
    0x186100300c40b00b4100030308465101e001c0161030300b0719854032440d84d03608001d000744904085081c41484485074100c045c0f03c002000814001180364002a0150f12500d544c104440d44000c0c0007400ca0b8184240c1248030b44051020800d035114a00136202d01190030303076030700310300203c0e2148071407040c125040704ca4004a42442424042904241c3c001141d041550320f80104032305450b4600f00074050b0380041503010070820140210fa03a6400030f840244a0540313441c140683d514006000200702c907071903d00041140e1880c80a6400401004040320302c4040c0c04003002e041644503000303040c01039040000d01c0b000c1c0d510004085000b0305444c0d490f8860300d89141c903204d0908210340584811400742941d224056981d50080c1d138084d24460320300181d00b003124a801d8151080408495041c000c84044c20424000702241111156030005000c0c2070071815600095144241c0384180d03076201c42c1d8400302040d131035000074182d84500f0040c0c00716600c44181204140c1e9900c030072514100040c0217440301600651180d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 996405377 1250 996404127 996404147
    0x220609050c04020c0f072423041508180a0f08130b181509011b0506070810090605060306131803020d02070e06130b0a0306020a050a030e1507 62
    0x1450903151900141d500140983e4801401420594080541103d451000380541e0004160400590703100350100d1421882006901039020107011f40c280200491038070040c016501a403403c03110036592a15260b414000000d00064680007036405000a442c1032881400034600c220444020a011100b564500d0803400d00c1d882c084940700001e10643c240001149036103000f8084580500d40c031103148880c001102c200c0b501686200f101d03030000a800c0b0b814004200c4550b04820320b0b04c11010200b2124101d080320381d07004001c125100e44000c00c5000c544c40070354180180d01944000700352075515000b610036100d0f01d014480e03108c401080860014a420102e201190560040c046006102680c10440305040c9400982c00b40c0c1141010959155040c0400d03400303080c1c400000c42c80360510b4004105400800015101c0c00c80e511807540703126640c4c0d103541c0070044d40d00070815961102e03001401802d0707401c000344003400710342060002c804100c0c020542103010418031261030040d5a032a00c0c112402c0c004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 996406627 1250 996405377 996405383
    0x10b22050402010c0803011229010e09070515031b1e13120506010317040e060402070201110d0905040f0501061704060b300a1203020307090527220609 66
    0x60b24044d00d0000c2c600070042c1d8020241130181030700212950030089540007084c2c040342d1000303c2c072243d0f60651b01e200c404c5440c1503441d181c0c03005c940340d9242c0c031905290400d00d0f08110f40c4803400c01d050110788110000210701c00ca41401f1a03c00418080003043ea550040032690410226040c20392140030b10320101600a101500b03c0340c011080e6220803400107440106801c2c0e1b50354010100500a101140307911910310120710030000d1405181405804803180040d243d5403003241c00113541c10940e8450000c4800000200055446c00080c152000c2e0a0126612802d8004e41c1800402400002c90380300f490f040311540d4850003284000e52841440f21080204100c0e80341d60380d00308012898480c6042c40760344822a0541440d401000308804c0001900f0305180341a07540805a9a40000c456002d01c0702030414070f040c056104d03103440c842903803040340d203410054004480060020b94400601e040d108050900920000b10761642e142c04010504c1828240c01c80180f00842c120001da415800640c0d4280 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 996407877 1250 996406627 996406637
    0x4260403110a120c231e040e07050a060c08070c0f060329010507020d0c0909030909180f0302030c01020307091503050606190c0b16020f0f0a0b06010e0301060611010b2205040201 78
    0x16a100054a505806d0201000107195034210400504162003000d5403c0020801012218a4240061032215440c00340340c04000004244c0300400c090f4005540b68181d018882e900340750380f103801d101c1c45118688202d1001a042088801e1a500302898802450007200010344c14070308000d00545542e8404401203030491482c140c2e44000c0760a410f170490140580003000f240700c854506006250718903a4002c0910340f454000c200e22683e0040000301015540b141c1400425400c5040c281d040d4001c076140f000f00342d4000820400f10135408031448095900c0c007044510464064130048044a808603007180e000241044126655280d210500c2600060342c80c00154114180d510b041d20f0b9501512081026020302c020081d1035a01480204605000c0b82c0040042c01c814120300b56a4000d00e41c806000160240301207120750348250803840340a20301a0080c00480d5449a00602c0c1052041d4281c0c041c1d443c08083d4281841c160346144503e890f0005240c6101e0034080075003009041c0500101c0c1842 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 996409127 1250 996407877 996407939
    0x21804050c0d0c02060612011109040506190f030b01140102250815060a0821090a080303040b161103040b0c070e0a02040503060f0403020604260403110a120c 69
    0x14101d4007860960307070644c1e800303031005060a4040c4254410204c150340c40316410000e031000d82145003810340300309003401c59000c50140c45800c0802d130020745c0340d02000d00d004000800424220b1002d400d600c1124811070409015a80c2c80607583c41c41c0b15520041801600a044541841e8180701d10740310020244503008880da070369032444103103041e000103190000c11a0303000801c1094500008000f0092003000b01520342d007aa225213543c0312a6a81482141e00c80c40032840d425940c56070361030040580280004c507656404c15041051001a0480d1800482601c000c22640340612a010303170a4495802001541407506050621010340c0141751111050b11482c900020f8207d11310201d58002c108038040180c0d901e0804d820f150a0100042015110380d00007824440066400200c00d030f880350f006226120f0b0801224a174124840c030780d05000b03101030300200b00407085c0720540711843e014000c00c549400b0001e5480300115030347c1c150a03202603c1d90350411800c100d13004000711982216185d648262101c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 996410377 1250 996409127 996409147
    0xa380f061f110717060414010603141b0312040315020f071202010b060a1704052d0105010e04020a21051204030224030a020901021906050f0a021804050c 67
    0x4084406100030005480c01d41c0c02d4a820014081500588185800120344940c0c40303403000d5684001500062800c00c1c1ca030444070b0101c00a40c8000b0255601036410364906010385c03002c0d940c500880040c0c0c00580c10b40104003c03989000142a8400d061581880f418189552185030b110070180790900b01c4290208425110307803500000034041d00b4410003441d80c90742402c480003030850b191809000d010301c004014025240c2d422840d018003152140415900903522440c085d410041c6000b00700030b1034030020324400307101403030702601301a0803444030002c0200741c0c3d03507081c007640490041d5006900036041181c14002d0724641c0d50050888400b418040150041c207503561850090585141d40501c4804030781402107140004210845103051000050410640080d0300c44522001e0083c1440d2540021403d00f16402400b0002104441b90400c4c1d808940340d01b13012010704000c80b814450101080c0c006011105148282c03001840910b1080c0d0140400c01c0c1880002c0001410b0454070400030f1100d5404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 996411627 1250 996410377 996410419
    0x152d06010f26040507060207120f0303020910090510023c070b0d0c020a050c060a0c1b1502030c0d1b0b0a15050d05060a0504060b030a380f06 62
    0x4000d200502418500350604ea420441550411000c5400c060010008089403034514242d254100c2403480c2820081c3c50158024030520420b207811080300c408802c84190010307070300e5003255400c2e9000750300c02807400001c07a06c0b00c4081801060980c6e080703c0c07a4001140d001c804032584c1061200b00b82e00c5003180c1d0482c034a08105580000741000000034100c610b43c505008180700c6400a000509028005544107601c1d5030050a505009840102d2140701d20380c030a0f219400504d130090000d041c25005c050002050403103902030600c5929002e00c50a000030302c0001110780b04504c14014040c94100e07650110b45140c0c004c03202605465814601c0004140e0210303020380070b030410b01c500294a180f00c003240940070401c0d5204130312400d080c010003404240e000c58050740c0801c9103100082c05955500c0d1204c020b05044078181c0c0c01d44100e408400800008800c1490b50306105844800c4126603400001442d0209a054451680c4150007003461104c2e00c1e02c0468118070002c02c28030081614215043c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 996412877 1250 996411627 996411677
    0x313020a090507030c2111130306021e0f0d09050304030602160b101208030a24080613080702010309021f180f0602030901050f0903152d06010f 63
    0x740340e520414440070700c3e0103205a200001040c244140b0843e040013100c14129000041c1140e415150945030465031004000c80d078091000c1c030307405032082e03440e424140000d402880441c0b1300400952011038600031401c0545030001035042019144c028003c1c0350344080d060600d4101c55903c01444040001101c9001600c415284c41c41d14034030103405400d200c41c4564000d48111039551100074280400700311402410030943d04000c00c1a500d03120070546400038803c498044102e00b4228042044150012034a02e003100e45100c2102c00315110228082000e90192100822407142040203000550007a0418030b08640001e1074200d008045036441d52107902510b01d4800040c814401d08000c10340d800300044060211140c55100302410180701030740c0c81c03061442d06414040d005c03a040802041560444a01d1180582605c0c00348000c064880d820303007000d40e000c0707001049210b044c2142145000c2c810010080c2c0e2100705c0d5240d21004015121345c040307001c400c401c225000d400740d140340c040d2070030240c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 996414127 1250 996412877 996412889
    0xc05210a0c140a030c023c0a0816150e180c220504111314060c0318010305010b0c0a03030b0103140c04050405180c0907030207061b02011505090406020313020a 70
    0x841403242620422818040300c10130b2147c400880003071005030610080c01400d9400c0d107450000003000482c000500001000c1d88528070394818070070420440b54281c100341080f1100e240740e1080300045030805840c0c6841c84212a070300a040c816404007805483e410682d0000d0082c81554070b0414030b580340b19500600a07403200d04206524100b0005800e003440785440303001c1e410b10703c181000e01e0324054010300c031414440d035103126000d441d4801459560000b161080e600000071240e840f1101007255400094818840380864900740002900003020412a1451004580540303846d00704d07a50240c0040491680e058101582e81041200100d80240c2c000c0c0285080c0500b55101ca25110400c4181c8000610344903006159058640d000e490004121040c03044c1152841910341d5001c00480084c010b400029143c10304082840810100303c5401a07012601580280204441c5411840b428016445119040214030340020003051060340610782003080244401d103810a02e40014410302c049411030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 996415377 1250 996414127 996414137
    0x17060f0705091318061b0c0c05060c0c180402041506022d150a0b06120a0c1e110d11030d020d020d020301271b0c030e100c05210a0c140a03 61
    0x50701c819046c008260145891601d0b0000f0301001c5603550726076926182c458a4020b000c0400c140c82e0311a02400b6400c1d4555000c0c203050420400d001c0c122485501c01c1e14141c3c0580d16104401c9003145611203200c05807411a0002c115410001c0424114038414a0114000c89884000c480c0350000901060011042094450f1400d0615103081c07800c0345d60b4a0803485c0704903410803580f00ca2045a140450703000900980c0007403004040351055949441c04c0440c2864504140e04080c90150860304500a006504003112a4021102002e0b41c021034556108170300c650080c4107401c0d400382c09800030305020340020400340c10080c2c00340b03419090b60005c0c1c1141c1e90000c8945111144050705030301d6440305150003c0103105c1d051200130441811100c0440b803d0403c54800325030f4007414098483e045815001400110008400a00045c440484200c044405001e1098550600340030380c40046c10120320403400ba0f1510454113002e5400340130034401124603a051070720b18010041c040c80300d003011901a40320 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 996416627 1250 996415377 996415391
    0x20030d0b030303280f0603060c0e0102010504110d11030d03021b011a010806062206030c022d0a0b010906030210031e11040e0117060f070509131806 65
    0x104054804403124240280d1082c0200811010075075002d040c1e00100c140c180c4408109505044041c00c08600d1005003035040c00c82c00010484958014140241070341d890f00600f0040800490980b40103503006401d88003624402021450301e00b050008a0348207180002c551940400441c2c00c02c0c5126004001203680820b00361102480c0440824038001135070001c00440350341c9007481040954016800d4108400c00c0b0009102e42c0343d2004a071801040100c50824104043c6401040d00002d40200c000107420310b885034000342c7c00010014200c66514042500e80f11048841000b41104c4851000551150407002804241401003450290002100114a16046005000003450f001244d1000c040c542040c10a20a00075005207003801140100815614120300340c14403a03000e150040d00b00a1295000003880c0c076542c0d800310f0000f131b50b28019201d59a980b00e040c01c00000c4221410004175900300020203440c40e1482181d111415544000581e0100c0c7ca003a00344101001101110601c0d80c600c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 996417877 1250 996416627 996416647
    0x31d010608070f0609030b191b1b08030a09031407030c1703090318041e0b041b050d09061404110306150604050d02060c1212010b0717030402012003 65
    0x120b280041c00c109070040e01200c0c0b0309007006050382a184005804402c803400403074840400b00960b0344140341450b07402e000100305507805007010f020461204000c100c080300c003241d4101022400d0248503401011481c2155113101980c4058250301404400700032001001e034502c201c070384015201c5c840c00395640c1c0e0702d8a40c1c5450700d241100700300d03900f0010528003442040b070303004400400c5075800500007844124078444140898003824081a414041a4013080c22128030340d500d50014230300880071070b03007030241d0224401009040c03040d000a60380099002c1000080950305500000652441810000345c1703919552481307a5100001c0e1400c942d04d05404081c11220b1804100700c42c7c1258503080c50703403109032029002a81502c200d21540e0f006044c4580d0001c19550b8400a03507040c01290002d807640e0f00c40103a1043e0701c5501086800103504480c80002c204c1d40003503400c0ea000554065084102811106405505600028002c904024100d503071426189440c034403040e24008060000d50b11a0b00500c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 996419127 1250 996417877 996417883
    0x90f0f060402090d0615030507060327020303030f070c02030109200108013c0f06020706021c031d010905030a17060d02010809150108030a080901050f0610031d010608 73
    0x3608240c452401480002c80c6641c406008640c0c143e44200c000031100d41c0302006420b10b00c0ca982c80505140a40b00c000070b40ca41d099080740d00c6903089403000c40000d506094581e80b1148050201a401d5882400003403006d03101c1190044d00600300d42003014040c042540041c0c259000c2410840c0c085201c07004104502c3d01840581c20301d1102400d1008656060203201814043c048861300404c5a038000d03030464120590b40328a07042c001103c2c0c4903010701d031502c20112010b5447d00c80c420041c480c00b400003406510100e503191580c000900d42101e0046110030480c0944400f521400c801c2042100d845400d680922031050958801c1e4003a544941980d40c0140203440040c100072810a24081044101d5941032284190b0944c2428158800d44605802078500191520001c12211aa400104406070000003a0225640c0341d5503142580d40c42400c1075081c0c4078261070800801080d480071540a00d00728080c0c1151784000d280000da00003503280e07903501580060201850741d035510081400542014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 996420377 1250 996419127 996419131
    0x2070b01060806091b12040f17042102040b100c110a0f1211030f0303040611090618060f0f040e0a090b040308100b0a11060109150b0315090f0f 63
    0x5410b0201107850038102040940800404210031256080086221a5000c030b0654403519420341d1058035901d49403030001315103e00c044013601ca0101250700160349180c02011981a1420f02c1020500c412a4841c10900c0b81c5199100f00d900075118495070940d616040da410545540503500c1e4100300346203017800030700340e001e81c03030100c0c010040240305004012140c03158404444900300d13402d81d42003141c02e00c504030f2500ca409581e4140540c0b0043d00c0a95000409140103d000d200100f0000c1000290142580f05103a81d058001c1c03002e110580017012096003a0010407000342c01149081e04d00c06607118540d02c031040070f2003d01c0700440c041c4501d040d03a4050640c48002890108101d460b1a00c0d803061480d8020801000c01181a00150882000c10354450081180715422a20780c84404809441d00c5106056004075101e06000000c285156014010034440040388201000e41410000d040c03039880107000c41003800400641980507294142034611440f20100080254102170703006081000d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 996421627 1250 996420377 996420389
    0xb0f070203042d08120d1104050f131d010c091703090904110301110c06361203010f081b0906090402010c02030a062313080c0708030c0102070b01 64
    0x4140000c0c0301030301c0f5000100c0301c0002e41e0260410381800031000740c0c46041060300301d90000e0252644442559410401810301ca5402450034003803010150b400c4001d50055204035036100d0f18810250069007403104a141c01c01541c00780c0420908440a24041110010501c0e061142c1d50b030300e00d8806c0705900c0703202a03000d8185410401905c03882140c11701d91324020011400c3c8212880740106d410080082e42505000308094000e20460350300f64011000d50300b0a00070080d00340640800100d1b241c04a4060060300d070480d000c50340c241d1075150385a04075a500c1d04c100f118144242000300180c000e105c00554005c0400c0c0c0e21034004d030382c10210705a00b0070b01c1c10354840080001001c0d01c80c4042d40c0b02d00500ba8801e0095503208441c2d503a50004070707407503c00e07030402035014051071002344184580d54202c0c82c40b9900484030024a11040781042e841e41004680703100040000740d0640000407202001440141c500904617100390391228405400c2d5402249003080d281c1d400580d2a040024000042d801001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 996422877 1250 996421627 996421633
    0x313030302071404050f010603110c060403030f0b0d03080103120903050f030a0f11030a050d0f0c11011a0d0f0201090e07020a06060b04054b130e0a032a0b0f0702 71
    0x1e000100c440c01b0301040c0030300c205160b152184002c1150030705040d100c541d68000200d580e5030500b8240075005000410a090655007003464402e01c0d410034800001400340e243d0368416940c0e1031505c815180441320310201e0100450401e0000100b9030402c074200103034a1031030103103549400300d0601400d0500180748031800e00c110034110f041d9050380401070742c0a50480b42089951046401414801080380801c500da01928103001002180c0d40300310304400c10390389030000b0003011000c04c400da0ac0e0040192034113a4040801ca2520000070b19008580b680140706040c2040301c681c46054a03c1c0200c01116034400507400048140700f03004590184000409000508070301c2e0500b004c0c081100f5034544150100c0c1c00c020300418034004055a00300c440048851340c0c441400c0c1c400c2c091001d899665003100244a2485281c3c0f034043c02c90070344509407640c81e41c440200700f4116280e80503210449880750303203690309100d40d6a0180440d204444191083d00c54201003c140c501030b5150345031550041d0103101158 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 996424127 1250 996422877 996422881
    0x6080d0c0201230f0a0201020703034a030403080c1603150203190609020c150c0910020703021003020307020d1715030c2806030209061b031303030207140405 69
    0x40d07001040003425410542580160b5401d001c40b20201303105040760100d29a40006454082c1907042d8041c00750300d44241c0e81400904c2c420f82c0346803010429140c450020320228900c515812007205000e18451900c0143c80c004041b41d1030f400c43c19074000b64802d507002c1c0800260150b00d10f10600c002c5490047d201c1d91080031f04d09680b9a0391070524a00707010303003140f0341c0000130541d822407121076a00034044900701480015210720940001c0d4202030b552107500d209801c0010049a0313014031282c0714114000c506810000034201300300c8004160018003087d409441c3d80800583ca0b01d280e480508800c1d030700c01695a00380308200920f0154406c01c09020030040b500030300103d8840100c541c0e04190032005020110101c0c80009041c24144084036900c504240384518920a983e004d5000d40d150b6500c0400c120780c2c0d42c020030b4050b0b01c0f400e1303100ea52015041209440d00d15034600105e000700001c204581c10f04401446111743c41d03980f90001d40142e0302c410f01c100940020300320042a541000c3d50180014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 996425377 1250 996424127 996424129
    0x150112090803061003201b01051918062307020d080406231f06050c07120c210c060203091c0807020901090506012a021e040603030306080d0c02 63
    0x19002c0070340541e1181003015a143c100d1882a04400c440da00040c84071154600345e45010380196100d50102188034031402c802205590042c0700d10740c885d6022003003c9480c0440340b5451401054096a0080009209040748003c1780e154810175030356a6003964104190340200303005007440d0740018016030465020300b001301c02c401e50007a506a04542d000b440407460b10520959880c0349400b51640f84a510100d10410540016004444010140000450030f05584984046400b032050b101c051090340d1110380b04012910046e10003a401e40c0c02980900720254440326041101d8180001e1a02150b1346400030710240401c0c1c1c1070310320003400310f8002149008074030004244442d2082c07040400c0016103032562000e001814048468843d4010300341400c940e11303100c58500610064404a0018552170415030b406611001600c80d01020b607413503840b4400c103a50030007000c0e024203000181d0266500c40100107645a81c054400030354400c1d20003207459402c20030a64900707110110404204404e4100b04005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 996426627 1250 996425377 996425393
    0x207050f0d0c42080a060902070803041109070504150905091e010608071b170307020f160521010605041e181e29061f090603090f080315011209 63
    0x3004181c03c4c5008036607903c0a9130001002241d00050f1807900003c3c0310020800d6034070003144202d104000b035240380840c110501010b54011541030002c035104100a00c0903481070b0241c41c01014003460030782c584c0d903200c40c04100f1130b1205442c060b49030000c6121881a40c0c40520f000c501400d194501041c0ca071601c14401061000000781c064030141c0c004030000709108040f00c01c1603003021240e2040307650b41007540c4d0080d654003141000850500036103070300d0007d0340a400601d00888100404044e004001e4001048003040b0240c031182c804c1d03507200400502030300d941c040d403100c801800f00c20071004003580000c0b10903241195200300080c2c52840702240019140f480c0100110300342c1c4034059855442e8588030a8407a00c20781001314001c420b41001c2d54007400c6c00109442040c041d50050000300c03842c81801805003a0b8031078a00400c603c1c407014012a8800d9100e10a420b010742d05801a031880342e1903c0456034400d4901450f00704040c801ca420550b080000000c04c2115003100f08403140313140d02c841c28 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 996427877 1250 996426627 996426749
    0x30919031a101203090f0611120c03070312140a0e28110d060504050109020f040510061407061a032a04020f0415020106090e0d0207050f0d0c 62
    0x1004150442410301890702c80e170300000141c0907600302814460380b00c4d0030280000c001100503e00500c40c010150344001030395016a0305012100b0011410071002c3d40c8c1c00d032a1401c100414840c2a5543c2c40c03240451041d00f1910341c000e040311200000c49a81e8101c0945c1007170b03407801520a030380000c03040d10441c80710484100081540c0009886100c0c900040000e2590082a20702800c1c03d400c107028802070000c10b5000610300c5108546482140f1846414041a030303801711200d0801c0d2040a1040003045e0190340403542143c42040f81915005940d5100012a8850304010081c841c11402c041507a0030308000e0300003440c2d010a00c80d8441d580b040b507821282031148000c075026903008110503107140700e01340603100a4140d40c008800042c0920b10028002c0c50b05210340c0c04100c1c01c10304010f0032404045000401c400306580035016490070b00003404503d03000460002d0704007141071a00c50214614060003030281058150794800725007201d1801c008003008044034001c0d200380c1a05c00103001c4210b00454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 996429127 1250 996427877 996427889
    0x5010e06040513140c04081501030b06040b010918090b090313150302280e0a0f12080f030708010303020c010513060806151306030501090b21030919031a10 68
    0x244403c282c90324a1406405400744011621000a06200e00d4580441c064815503e0703135001c0b6042c0c40d80c4050f00b092100001e11018058280700c2000c42c5403824150042d5401000604244c240103a85e80480007105250f0705101c001d131556014108200000401e07c141c000300100010360816401400c0541c1e0041c2c244038424208403a000d44540c011700a07015104e40449526440c41e041e80b44400710613034501c500703031030030001540320300403001a24100c00070300302f0b603004802403403038803401c2c204103a4a511076003c040c2c801d034005101d4100840201d41c004c501c184810342c1d45070040d51662901030b1400b41d460407114140202031101002e044a08076070038040391164030f4041c035580c84900101d911440603030a8030320806000104001801c2601014104803642a0703403c01240e0781e504000740846054071242071303018485010320301c0c1400107041001025a8060243c030b14110340580003910120140c4000c0312507506c1084200144807240c00a01c1542c40d045000f4151480d043c0d43d240c442e100c1c01d000b45 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 996430377 1250 996429127 996429139
    0x1142b1502040503031c110a09062d180306151829010e0a0e1605120606090105040b0a1707020115060807090315020d0e030a1b020f0d14010605010e060405 68
    0x2510903c5943e00689002040c514581d5034842180034000e02c01c03c0c440c02004085a444010411600be9820000e601444210050040030641110803101c00300d00307408001c034265003070740017102140c081c0c41584100791a900004800b1031030401145a860b6a900c10b1200c55072904100f4140c184014005010344c4100b003001ca000d4503580b100581b0001c1420320240d801510354500852290241c00e1518000c52803503603851900c0642c21130440383c0e4800d13102034019012440c001f140044c14408007800c0d160005051081c100340d2643c0302903105801c00751401000603801c0c2c1c610340d07900c041301340704c50b40100d028402400741c002814207141e03448486114000400140d040044d003000e00c07076502e031809141d006100c40f5050300030011840280d04090221810f940c40c10429852000f000400c907041034005403100d003228080c0c54a1030000384880d050a0341c0000c4c01c4220ba4407290764031685195034520460404510a060200c040d0031070305550880360610020000c2c04480d5502d090569044803030032112 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 996431627 1250 996430377 996430417
    0x90605090f01211a180c0f030307120903080708130b160b0603030903100b1002061605030a1826040506040311030106210506160801142b150204050303 66
    0x1801d134540007580032400000d04010b0215a0000c001d00140c082d003e04222114840902c0802c2174009010494541c107034001c0112100040040307008e0f200d140f41508154801c2d642d00e4480e400680c0c0301c030600702d40030800002c00c0038502104205031009400d0260b000d074103104507100f0800c1030801c21000030344144a8a07000410703566081007220503481025041c0d54643c2c0c603112a14002c1c09403021600d2107255030304606840588002030003846220721b000c820700c203400c41c110b0548056101400c180103c80c0c503401e4010b0317030103082d100c240442031085918880c0c5003500e81c204900c215800c408800501002c220400c0342d552503405440540b900084002c00c0f0340915800230b8014440f5900c50100310504031424603154000c400350341d09650080b429584280e50300d400c44051340104044500210b44542d00500454040303011001c0c1038030019040725600c5c00010760329003200c0e801c10b213816686880e145c0c554003000704c1c10b80300c1c0c0c01c00f01d0080300070360070b290510700000e8a034020108402007850110320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 996432877 1250 996431627 996431633
    0xf0213050906190801020a120b0303040509150a150f0915050a050403020a0308031b0703020714031516030f021c1112040506072a080a1404090605090f0121 68
    0x3c1c0841c24080da943c43e01d03000e0b95030030750340d4040c0d00843c000c2c40c04070302030701c0111074480541c0c00350003840b1070020061031805007084200515114040c10100010510311034184260302e030818103c0c05404040c2d4071011080200d040280301600d03004100c810407030440d001700611003020310700d026100000c0c14440d071500c203060310071600d900841d48060340c40410707040000140f2000d080158002c139000158522101094810761100d48108940200168007040007000100c2083d8001400c1040040c103840490000c40742c0502c00b0141520031b010032510482d0080d808540500c544200c038604e0050560034900c040103140b5942070807800c644000c0c2c0e1101c1d80d00703440c125030400700c908070004440c550388942000c3c2012640d4040031a0890f0129444a1042c01086520420342d468100f070301030410030a407121365030f40c502900700404403414407540041800405184a000d44060581d00500007903280c900000c1002034807002d01988407840141006100103028080000013018102800f40c4030320860385 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 996434127 1250 996432877 996432889
    0x71103070c121208011a0d0902041d0705030d08160c050307081c09050d0e01020c2112030c042c0411100807020a020918070b0d0f0213050906 62
    0x403000901c410500385020603946520859a40858080c04003a284140100030549062000380105000705440038208190681d80c1d100421034041c05060201e000e0105901050a6804610241300200c43e038451410840390300300180c50080c40118000c01c0702400b40b00020303090040181c1068551189203912500d010300525200d00902c0c0c0c80700071070340d8446180c100201c0d1500184039482044030741122401c2d000e00a80500c42404e508403020348084070841c00c0a07140413001e00b44c540e041d4040d60407005050740e616103d44142c0d507000718125440c40325800b4403c0c00d20500311a0250f680340103006002c0d40c1c000307401c2560f047c0d40040303d0906c50324410301641284108140360400118072084104010848000280e4071802015501c842040080f20015036414608940354001a0711030800300015141a9900317a0700001560496210310039003055090800b03a1340e0701b000c00e81400014241e001d2403141d109105580c1c0082c3c004504114003041840d80044041c41100c1c826480e10b400314100395144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 996435377 1250 996434127 996434137
    0xc020f15040e0610080114041401080114060607050a120504030602032424090a090606020f150702212703070e0c07020d14030c06061c0b071103 63
    0x52850440c141a100500d00c00d5101d801448001440000414001e0400c0d078085024901117031659003e50b0308009074a20400c504019159200d074455992403ea0b031403146c0b80501808078600007150f020708060903007260f10406404a40504010415480031030b5001c1441d51003564030107580d5510710b842c5e1900301da980c0910b420140c0401d10020511140c00203000c3c0d403e9490184141080441203e80200714030b141424003003000004006060014032544400180309502c0300030030104049844001c12000c455490f0001000744e42301002403081090204101e15110818000c034010301e1030030749402500c030241103141d000c0d010201500c05160001d04001d448204041c900c201201c0c15800d400c4200c03141342103003918028003801c40041040c4138a0400c0078800d0260001c403903d450304030340c00d00036003842c0c1d59010307162001241e00d103002d40d4209000501c2d1b510600c500401250038000201b1503000c2000710380c008143d02807840b0030b002400704c62840d64812a541025195034004503502030640c0700f4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 996436627 1250 996435377 996435379
    0x111507110906011205010905041202011e0b150d0b0f03061504021804150603050901020a1b0f0f060204030b01050607031e090506041d06010224040807080c030a030b040513030c020f 79
    0x400c00003041140c901c0e40a68820380c050604c42b4425110040300343c0c203e5800400300f88003950b0300e50122590b03010355000003182c410302410304030350180040c0700e402144c4c10601c1c0c0e90801e251100d0745031240c0c0c900540b66510151081b07010708050305000000e1000603c0c10740d13045c2d006039004101c1401c0b65160810680b03025401070028032802c050803402d18043c924501600011900c1e00c03000c124504814400d40301b22158544941070140c040c1035408901c0f00348011f0403030b580b48420322800b0000c2c102c00c07909800284039a2000d80c4544c02c0d4580402c034248140c10480c02030800b0b0040c01c011030f034800452018041700300d032581580248000100c403009410781000d074028800140000d0f50a00c418440704a59010102d50100c1d5140e0300012a241c080d614003222103890800b028a01080080000d5608244504591482c111155480d03000300e0300404c8203041c0d01c0e000461620141c94150280e142420b10446041000749003680087c2a140c1c0c103e9030280400c1041e044400031920740a0101c0d50f0080c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 996437877 1250 996436627 996436631
    0x1f1b0f020a080303071403070e060f07120c1101030209010909020733050604090b06060a03150314100b060316050417010509120405062b091115071109060112 69
    0x340314040707199a44e0080c2d403a80c00094070003005802d0042c0c0d900c10341e4001d5016550b03940701807191a00700091500480711000420408000203400100c2c10120303014080f90360788a142c4d0b65078460a01d14458049244042d050500401c000d0050707a0b03024007603000381c82d1005001616151181007024404040603012640721301501145219001100101e034411601c1c043c2c00e2001c0d5440c001440242c030043d4000070f04158161000c0391f010324107440a0001d00420b460005180d42c640040141c3c8072a440d801920924100540300680030001c4c0041907220060b1102800350400400102da242e11008100e0f170b202010706424611b5291040301160020081003030030030300404071888668000c00c41540ca8940da8030551000d4540310040106540440d0300040441c1e04014450001d44100014500100e01e58400c3c003c00455001c4244521071800b801891002e402400180a100b4205524105c201200105108030000120300780c40980007498140ea055001d03413030300350044e582c0c08180c1d00c0b01441d00d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 996439127 1250 996437877 996437879
    0x1c02071709040b1512130b0412030c020c01120c050f220501020604030e0607030c0b0403090627030615170109030e010c02130e160806061f1b0f020a 65
    0x80c04800241004020488003040f2104002c020800d0300403a0721030443c81d00000340481c404522400041e2640800e04503030001000241d691038056503042202c0c01c890a400d0041040000d40d4980f08075203450259000030071001060200103445907459026aa582907101c01d4505461441401505c5080b4400218580c0741c13083d850704289103409038891007502e20600d0500103120340c40083ea182c0600e03050740301c102111040703406106080d4801541030b014485008a002c0004140c00140d81c0b24501913901d00503038500f4044020081060b4000a25218180d0400c41483d0360740600c03e14102d9521900001d1848014841d4051500e0a0b901c100450320004842c1d6000c0034064200c0d1050500c40e40d0b40c0c010740006040155176846200c4006034100c0c0007044519520820740e88506818000c010132501246114200c00c00030802035080984e19400c61424081036003000b030a10304400034102204100203440d074400a2580740c42c5010441d04000c411048010700036030a41103000c0c907401810f248009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 996440377 1250 996439127 996439163
    0x62202040e01150509011d0a030f08071208060f0423090a03031104031a04050708031b01150503030712111b1c021f02100204120507120302031c0207 65
    0x305400d1140b03411000d0402c503c5092140304000700c40485105071100344200000b0041541c06840e80c46403aa0055035080000c070218003403a0007072104900c81c00e0319664548a80ca4801202e451801c43c40d000e10405030184003440d51550541d6000d92016203000400900c1d007180200718183c0e5051124a8061840034051404408224950707130b01e00984080c0480e0b200d003841d54296101d030307100c0680740407c0c40c40080407108001610380d80184c09a400c4400c0b16442d000041e0850303005500769014004039441c42d00e42d5040c203000b8001c0f02c28002c90051078091030400486d80b20f104250000300742950310494800c3c414040c50201000614001c02c480d08224440000b229491071004150f20030b0803103d46048059141080445095074050003030240d60041c01e40d04003980114440350002e5002d1602d00400340340051000c0e00041c400011002e01c03506d4030f070504a090401a40281c640c42400009030030204e500041115800f52800e603a942c140c12802c440e56009001c3c4010081405141c0040000c031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 996441627 1250 996440377 996440399
    0x310b0405100609080d0c0f050c0a090e0705090c0a0507021c0501020304170703230d0e010207060e0f2d1509060a0c0801090902120607051c0203040b06220204 69
    0xe40702c05880d070004058403500101e0341d82221400c1d810019118036810800030b240c4149403405680f044044448400c0880001041045150404115660b407240800808842000b1001c01890240c80b00c1d04c590074011a2101d440c0702c0e9418003010b1180014500b401c64507a0510310641c02e586110100010b0098544203010350305c1030b10190f0301482d0454207514013401c0e56040b200c402d540f40d141d0202c902c40355401c0b056403156094003030380b040c0e6042c000c1b44202800c6005003203003c1d0403a400140c0d00c481c24540036040780c60f0041c0c118a180e11030304102e0580034000489000c0304414481c0e041d44525844101030b000885003d013018980a00407000c400143c018a03418000c10600c4240c5280382d0301c80312118120f52030b85804800081c200d40040200d200c550b403007283c81074005070005000038403029030f05191010503140c000018600090b6040701c1030301d4240030003501080150a501d14100341c0c441101061015000034801c92010f01c5034400c00c1c004040800360400951029500d660341c890a00302 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 996442877 1250 996441627 996441629
    0x1021b0f030f1b04051501030c0306051306030605090c0a0308070602090d08070303060501140703200d110606010c0804031118100602070506042d1d0114310b040510 72
    0x45814071600f01c1c0d80794941030013010300c10b02c010360707040c15030f003c902c001140505140c11080d07050564590b008262902d440000008405400001042040c650326044c800c45000600f80d140a41183c000d1100c1503481c0b10b01310044031780020082e6225090340c01c11030004e1149929070356201403170344032031002c021101000d81a440e0007603c01b08881540d41c1b00640b06009050184041c840c0100040c0c2c0000740299400f0081240403504000c40e031900d400010302e000720a400500208110803100401d200e0200140c03030f4084402c0c80c2104545102d6610740c5000e00071400014810b007005146c0d4080340d100c03d15450400d03005a1a00d2290341031040100c520705505025aa0060081c40004541345c208503040310100e030300a965a500000a40a040b40143c040c140d10b8401c09412003030004804000500c201134140e1125400402d5500d0192501e04a1200c0c401281c00b41c0301101d0700d20007900654082d1181c0602c1500030003200055091500024480036034242d40c8180b400040c400c191002003680c01c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 996444127 1250 996442877 996442903
    0xa020f1b0105180607150c08060f010c060e0304031b06020a05281a06150f090409080f030a1d0109020f10090911090301140417070305042106180201021b0f030f 70
    0x260f007c01c1008860134503080b2016034010940c04945102c1d540304204402e50356002e0100014606610300440382075910541c02620007422000b03100c611100d00b4140e0030002c19150005000304401c0b03070317501d03502d07050241045d4103003107800b0001a0700041c4098191610940c40040701c0002d6501d64020101090b0070340310580659041308514180d4410801181d10380d403001c00c07029080c550036004000c09001020012140101d0622801c070741c030b010034005140141c201c0b00002c20034500b07540c0c80d020041c0c0d06001540711603042552502c05a01c0f000b19002c090360082c1c0388801710500e1010160380159550f4000d040240c9040000703104550050013414440c2c00c01c600a00440c00289000c1910000650b4003424200702402c43c0001194080001d0007514884e04106060039034690800382008051880c0d00018030345081203104011403803041c0d188100a038240d00110b0b131038580000750395100440116030780380307241c5081c12004e940b600302c40081c2480003000c644805c200c12031401e0315980d0150b051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 996445377 1250 996444127 996444131
    0x709090203131b271b030605090f07081902370504080d0507020f1f0807030c210b2206051e1908070b0a020f1b010518060715 55
    0x405008449400d110484208500424000e01000c48280c0744c02c4110300b15098031552221000000c50210240740d0010358141c8000a29a203407805002c203070b200c000c3c0a80d48004031841002a0036030888506a0410203428266090907402461000203228503c44c107040d50f44a060303002e050f03003000041454040200c0c41c5c861750340d0100b000255082d0017540296a001d42201d030007807000c5442000503010043c0020580e0181d068100041440c80200c2d00741107650194071301500c01c0190b080b070245500708845290800c1101c5a541008081c88111343c3c2407200403c1703920381e0111442c081d80001150340402805030384207074071000745c4101070040b040381301149600b890b000140d907141901100940c00c1901646100240d001c000300007039949292a6035a03502d00f124004145110704010900141842069075950f44502c14004cc0ca003800004c042010b0f944441282290007402d840707000030035071082c00d016850b5082c0078a4a03424907035007801141c01500c00310b500e1081c000100c81d100a07805641c941 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 996446627 1250 996445377 996445403
    0x6030c07110f01140a02030f1303050c0108090705010c03022103090712020307060309230d12060503070e07020715120c030209010c080f09040204030b04021810060305070909020313 79
    0x24001000c03200c5000301d01045141d202c0f150308002c4d00d0001d28560000703105980c82d015030b52030200301542068000c1c201d0060400418010070000300810040384201742050202c9240010000740c0d00c480702d000c2d441c10050480510700400d8001c01007a200010194441d102110354425981960b0304116070300f9071644904140003529207130054010702071175000f45c00340040030b00701201900a41500b039800c40c1d03600e45041440711058081b403126a00302407002e01402e0a40c030990f500901140d0380340082640b807803802c0e90801040d0750010b2110112450303c0300100c00d43d502c1200c203034200001035211208860310403481845841e40201702449071219940200840700740b0402c118124010f103491280403134501e04c1c040e00440c41040141c00307800d0486601510381200781c0c1c0410b050303070400c0c0c2c005c0ba031180100c401c7c03004514210b000001c116190162048092424080d0700151607407030302c6448141030740c2d03101041c104c911a03141c4c81d02a180d548000d650300d080200c6602002206090306031034189a0f111 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 996447877 1250 996446627 996446629
    0x3150a0b04031e0515060f06120412050c0f0106050a0609140f03190b180303100b0d09060e030309010614240403060c1106090d0f05030907030206030c0711 68
    0x1502810380e0000d449103400c01d400e50352200b080d0710760120a05120310345001503400282007001250a0384410741050000360600605220381e040745020300700c1c4245400d214210045440098050380135070130103409414400c485e9015581d80c8206180450036010b03003144081c20702c0c01504110304840003030701c0c81d82480c0d59880c0c0407104580d29001d1110b203c10301c1d20b0300d19264074000b0143c0d145a0f0f001010385450000784201105131030100380c401c0300c0b030780030307000812203217170694813040f460031170301070b003d14910300e84204a910100e0082c0a04402c041c00441d01e020040d00300d62020311f0703d690212040103907494000e1420b580350000c0b1003006c115800c01401050301c11501c2d03200031b03802002408100e04c452910b5905100120000e142e404034080c14000040410301c2c0d4011510005042c0d1070306581d6040f0f5850060034500002e1800d40590b01c141c0c400b62010ba880204498070003050710b8100e44035104d031071a40e814103031a41d01c0a075010b4408006d020301c1205910003850350b2481180408c16812400b8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 996449127 1250 996447877 996447889
    0xc010201090c030f021207080d0813020a0b0f07020604030c090f060e06010c0201031e090c081b04051306110912070b070b19060807060806062d07060906020315 70
    0x81c00411180082c4030403c0054180000e0543c540e10040540c07408242030078000346044143d902118695002507201341d903458002c1071a98000e00856075400c00040e45801051098625114131501c0840c000b4070784101d8030075142580d149036130050000342d4866803410140c8040e4450700510390420700d0140c4511004090f4400c030030498400c10090542e5540d10b0005440e0f001181c441a414540c441c0b42c585600401c044500101243c1d01c4c600280d41211406d19252403091504561116401404a0b440c00b04903001c034011212421100801c41e5940e18551001e00f0314899002005a401d01d01c2e41d80d10500303003201420b000382c4184e80e1020f08d0045040160740c0e4040038401e02540c40d00800c0f0741400b00c0c002103742d581c80050300d6940c2c00c82d1460b00b1440c0007150758650185050f038010710020320080380d011506d0380e001001107d11505000f8408c0c0380f680502011480211034041c1000d4a10440003000b058030b03002c41d0400001c1000c00700d00d0034400080d500484000c0b00f2081d80e4082c030b00c40c5103800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 996450377 1250 996449127 996449141
    0x30c061706120c1f09050d0305030a020a200703060e01060518060301200c010501300201020c030109141006080a03050c1c0f02010b031b01031e05010f06020c010201 72
    0x40c51040c8107500d40d50203121100090b200452040d000d0030580038007039107a0720340e11485540070b09028403a04400f050700910048803034202c6440384402d07032858800b00380d11070141c9070021201200181d94955160381038902c0b992641c032101301182d026000c0c940492001c55800d0480740120410302c2203080c1840f800342261380d94001c03241c1c0b1200c840e030100403501502da1400e034440302c09400020343c0030848401c1100b010a0901c24800640300040d15000600280600d40c0107003030410707280864400c0386142038110003486c070011450250101507101568804c100d01020000060000c108145e22814040141081280030b01c4151041c0340c112980305926216250440c0c090304090400d00e44140d508441d55400305040002903c210312a462103d11844c140d80361620b11501c0f50b44103035000b140c0c040d080d103800804940c8a0340110b007619600007102c03400c2b8081c84100b40380c00584110341a14806c0e02c40b000130b50071400700341b5090000c02c6500000c04240e00b075070040e4003125080c4903120012801d070380700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 996451627 1250 996450377 996450407
    0x50601050f07081c181a04021f02070308040b1e04081906020c010c081e04110105130b04031a160e09041a0a0606110616140c0313030c06 60
    0x10030842030010460000c041d0003108400000e00c1800c04000d0580c1c4199650040041d07174100555000034108044102c03d90a0380864008600c1c0c3d6251940001700e40c1c11802840c5210b00c842000050700581c07091202c0e60245510000250300c1e540c40f0074560106412190b040030301e03002040610068400c2d0b071400d0382c2c11075001500800b02440c18046c540b10000c0222402c6844a4007400b00d002680780a004d0402c03019115500c4071403902c3c050702064003c0c185840302c000940e60074401d00022624551844020010a0a00300c1d501d0b404036800c180e80d101c0f642c0c4040e419960116000c0f0030030070310030080c0d600e52403000c210840b1ba80b50314541c2000d01412a42860114041060051041c00c244440f55070150145000d0720b030304103010b428800046070403580032100e240c0d180414044903400100b1030410006a1000740928a442d144114006000306507034400c0c030502902c40b091802d0380b1f40480301e26001450980e5160000d004000a2881d52800110780701d048400c0b01182c101d100710580418608 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 996452877 1250 996451627 996451657
    0x50706110706050c0c0103091a040602090f061305040c20061e01060804031b020405040f14071809052104090c0804152f0702090c0f0318160801050a05060105 69
    0x245e054010740080c41144812507907083c80c10804010303402c040007100d12441c0641400f50355803d00d001000314418490320038901c00c04052112020880c0400f00e81015288141c4000501440e2132800b41c0340e5205e00110029000b2a006000224500c0450542d0041000402c820580765070800c3c0d5000d5030b4424050440010b40200000d0040fa01c5024403d9001e0f020984a100c1b280450700410b0607128200c3c0c0584242a80c20f43c502c0c108143c4824032100f461003031014120b0b5500f004c3da0307002d9411080c0000d02c051500c2c1c441348000d11006220328070280021404a07211000c8101d03180030160020710601600515009045200750300038070500b4403c0390712010031440e00615100303582c02007000c00c240703159028400e036801c1003c0c400e4000c0e1242d0001e150582544440d664410000a0b81c0001c100d2569100113005c1400302d01800d10980b50071040708413090034500c9900c21418940340305c0c0e440359401e1405401c40003416a10651005002d00071462062040b95039010046d24544074203984506219 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 996454127 1250 996452877 996452893
    0xd020409110717072d110907140702040b0402190f1b03120e03040605120a0c0507230d08011403070810020912010f0b031b130f09050706110706050c 65
    0x2d184400134208288519000c1a01d54088121049018518014600c02451a95140090016032071042103403032811111501035140c10500200111080884041480da0100d8845d0466031540c00100318404068411529000104070300c87e500c01e00b0b5201d00010445c22240c03c09890b00c84d018500342c007000b03001c0c3c862048846a80407121a222420210340c4c0356a902800041c0010900041c4020206a5151520340f44151528500548068482c2c040c440c98961b85562094016050301c2c0826045889600b14607040100b848506158140e102d0740b42c0500011004d1082c3c0280959040e01c0c40400c403c64200041418580da84d042400381a0582c0e0154000c001e5101c03560300289101d81c0f002e040080c5004142d1880d50940e18070011344140144c0782d2404003080d0500b0040c40800000e1410809000156880418140703c0c803080c000c85c6080e1a0703040b001f401282504411a0550302c0812103001c41e0340c1c4c0900618040846902c110180101000010118403900c01d41c0d82060000001d05040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 996455377 1250 996454127 996454163
    0x1101060e0f04294507090903051908040f1211030706050103051c050706150e191802012703020a06081603020a050d0b040e030d0204091107 61
    0x7951000b082180d40590b241e41040060b00d05595201c0701c000c058140a09900700644540644001e0400f910102e48484600c07058a4241140600c00b140718284c2c00c0c2003504401074494100210b50f00a5984a0f083c408110101a071000c020000513042403840b98462160b486e089900344007c0d6000b80c2100304840901000c144c2e4100801d6070400340342005003010050414084c110f420103882600e0680d0340c1d00040090010500c91a1220100f041840d540f5801c00360000c0d01318000c544014100c13517038070b010035902d0b45006004403016204501884020385032030355140c3c217500c094588a10400381410002408441000c4ca40c8101660585440c500c0103060300301c503a40700c1d5803507a0030a01004071f0080080962503500c4020b000d0410356a80b99298a442107249100251010101013010703c1003000e40243c50380182916000b1083d680e010940501090001e00905043d84c008209404001844503511300190f000b84101c4203034441c1400003000e49a0710384040d0141100c003404803140c914440540e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 996456627 1250 996455377 996455401
    0xc130f060f0e040b0a03031119021c11060d090201110313140a1203260f0103120201090c120b060603061008040314210a0e07090b01170a09031101060e 66
    0x10960003c0e000040c58440701001500c001c2095006802040440c91207480c0400c00b4807640c0a8030307550001004070826540e012542d00071800100d4610b18100da035846040094801c9050105c0301c1c001c00071501c1724646911617004000e452030407408620072005800c1d058201000b500c051002901000313030000c0c80c010150b90940d032003d85995202d046640046941e6000c042920002400b0760313a04400c1d45000300103e00c0c080f004695042c1c54035024170412102c0c403503070410141981d50111420b207052103446400d9001d028104001400005103210109103a0000148103680038060b02428040392650f8003031216521050300e20907001090491021445c42c0100e0b601a001807091810f09403107800052403802c0c58010000403047e807030004070b508248010803200c1940040b80c0d0b500c02c00c40060103100c4255161041c0c03040682480c1c89000a0403141c0c0207641307078004002448400e040710328103141800000c11405104030f02040b4520510800000705102e041d081e110403c5054800351034490210103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 996457877 1250 996456627 996456647
    0x2a0e060d11070c0e1b0702090a02070f0f12090b0c191a01030515010503060f041412030915180a0b1b0703030b030f010902031903050705060c130f060f 66
    0x9401c80c02044403400140381404540020450f800d202c3d80d1034144034503080100c031580310501203c242c003402250056603901e2082074100c442c4a10050f6a100c0519090301c8007010349502034010140d07074040700c090040f03120346800c103c40380395501542036455040c100b002c2d02070307811418125481600f10b03950640803c080481030030700840e0302d41d8000a07d0310003c130306003409030000c56090f000046c80e040218000c418040c09007100700e025001c14a0110304001d02860b0040015041c140b50701c054000411041c010b100c0201c0c00032900640d83d1820b01030f00c6664402c80c54407445828800c00000c0c0c641d122400403086e080307070000c003d00003010040e1280701c0903a0b0068581140342250040e03107460314164070001e000c7c0178403d4a0120389105050101800c11000341d04040642c0d060190f00e5006a5000c0f071482c1420f500c00c9110022502182812106406058401402031240401707102d40452414083d1410001c0b080703050342020b0700e62044981452251040e100850f02c411081d0f2415130041d140c400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 996459127 1250 996457877 996457901
    0x912040e07050903070609050f0108041a06062205281502100e1c1103070201110102071e12090e0a09030309051b010305011403061303122a0e060d 64
    0x3410f20b06600000b07410440316074000c2d000703d41c02c80d00402190405a155030141c041c00d00b013001d4103180c0f6803280c01d0a07001d0070748880400a016400100b0641d1124161211441c1201d1259251011414803076004029801000e10480078001020107506a010b04588019011010034810038039020b05200c6110310f0350000c8040d80151402c1103420441481000c508500c0103000304958900041551415202421139104100d185030b408001d5000020403120783d15820701e003110300000401803190090158507001030840d0001d11410030006249a48078200074051080510146021601614000498460500c0c8003400c41d0028501c500c02e544205480f601074280032800d10000d56440703042640c681345403030424121003180480382d40d061144030b01600f0b11004001c800740007640082d54514009141c0c0c40007214040704201094410f40d41a8051000c0601c28801090380c02d070514140c4244000758030765000341d20850401507211f0456000d0000b0060f105500e00f114100d00040134040c00d010f44 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 996460377 1250 996459127 996459137
    0x70201061503020403110312041802040302090124050c0c0d03051306080106030e0309030309060307140406021005070804021f03021b030a020f0d1d1f0210050912040e07 74
    0x1071000081e10101c00a28410b541c0107079620b00303518140151800d04e0090f280258450409010040481b1084074282c41c0c5204000d51041e82012616001c1d02c00da0304025005443c80c0e00004120000d0200460400178150a1020340380c03100c00e08650f00d020b1055812102d9020982017a900d040030010b00c40000e021389451454803101c1c1d0031041040a195011100140c5248010016a0703030610803507000441144c05545048841e4001070368034042c010525200d00740c0000030400300740c0940031200411149041060711281e03940c502075201c01c5404da5912401c0d0800e00044d45841c411942d2900c9254028220030580504621114040d45070512040a05034200b001d0f1400070140c6103600c8611940e20300070341d55070381c41a000a007054a44410f00c00e880c1d010081488115412003840401961b070807004100e100703a0f180001d5248000b82145441000e00c0a0341840d0481c6c4c040385a00c00b255400307905004544912001b9541c41d0b444855803081c12906000900c144e0101c5140250001d000c0d20340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 996461627 1250 996460377 996460379
    0x6090a0b01180920010912030503240a08060105040b0906090a0c05090301021204020a12030f0804020402040e0f061e0319020321030f010602010c08060d02010207090f09021305040206090907020106 86
    0x20b14555204041320601281d11108401300650391200c1094060b0500701e585080c00405580d016026000152980c2c2c8042800e41d40e2102c41051844c15030720344c1d10010f0841e03003540da45030052500c1d03043c28015540100e090411501c00c60030074010b010b002c2c04c4060032403042070f600c40108100402074074540a04100c0100321701031640d6403d00140008407607526078081103060520402580f01640d5000b45607106000420901107030b0003254429000700036090240035640e0320300c000f6009110316005003c450301c0c8076080c00070500b4030602e0140308070010b40f4006a02c0d15101179041500245440c017590582c0020702d0b00c5025000301039103001c1c1d00c2c03010b800c4813800c1d1020002090300824542407610713a140003000300a00e42d00c0c21403006004007103034002001404c0c41c60600600080c3e00801083c001d4554803946421a40308010000003482140c070b042101c28410000480a040d0039441a0310401c0c046a0020610245108941c003540d401880782d4076040d804001d03c1131001c80100504203555882c40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 996462877 1250 996461627 996461633
    0x610031209051f1b0b070c0c050301050406020c010c02070308090f040b0d050c01021002120103140f060f060a0f0e010603201c060e070c0b09100e0f06090a0b011809 72
    0x3012182c0d4201403400030382d01c3c0e400980203043d0303048004082c10000c07400c5944000300341d11109042d0000c1d60340ca02844101100d0070603e81010055000582541c60329081006100d180d0707029080c500c01140081c814040c03051002c0f69144d12030700010700a01d401b08412a00d9203000103001031308400151000c11400c80c6100028100c084841c0b0541c1d03181c00518882d0102d43c2c1c14040c070142c071285840210b003080401e00703000d806010140001098005003810003a8510010898180e40101c00700494109240041031500d404000b030300d40302e01501c00c0c020085104800c201900c002c0c3c1d00070700d284014681c0307030450403805030800c1d00b03510f440701c095200700c0f01c0c0070055440180901d810140f102d4103480c80c4052008100d410b140d10aa000010040a2020b203d80c4286a07000c1103401c400c48404949030045943d0900c21f164100e00506032428141240d83c503008910002503d0160082d25207640c1c50194968594048074002025106410010b01c005000703a504120100100140020780110303a503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 996464127 1250 996462877 996462889
    0x5100504020f0c0c06070507030303051801020c0115080d050d0c0c0507090606200a060e01020c1e011a01020d0309030504090204031a070504060f050306151b0f061003120905 76
    0x4103840d10808002508a040c1c01c01300014041460241c595914214054540c25101c2c2d0250000904241e11034001c500d440c13a0000d5804164407048000319950007d605025000b170005d0628407403ca281c50b000014294000b20ba0780c0e80001c259215140740142c60380000f40103001c0071482c1000d00c014129000082141048201c014000040c0c0018800d41071140180a402d00c1c4401002512049039501406107000314000c410107601c40408990340d1071500485000e07000e040d040404a00c07035041d844442c074400d4800c80018601c5200208006c010140c40c1000e01c11001200901507480300c003c0398581886940040071b05802441c19608141d11481c5c401c0580c0e04caa40140e84195580c0240010300264100840d0002640e0924900d020701d4004040c01d00e4880d0a500014042c010000a49503155501101cac0001214041995101001c1c03003d003012404120301c03130250348240c03082c40c810b80d0400100113026141c110902d0300840d1441e56041c1000800c14180810001d400380c00084a0310b5070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 996465377 1250 996464127 996464137
    0x5040e040f0b16020609010b01051801031409100b060702010804081c0507050c1005040314130e091501090b06035703010f030204020c0307140303010311030a020102060a0510050402 79
    0x45a943d804040590009180c03850191500030359925100365051039a0b086811a12203a05010864103040306040040e0020320000d281392072010480800c0001c481c40200d14109401040407040002c001d00606019441c010140001c0c046240100400d01140d03101000d00b49050b071503280501004194000c0400f50b40003550110041280415101f1018209122107070811540070420000362510342c80c02844015000d0f0b92a26414000690014152022920101801191018602d41c0c10310181080d036a8105060501401c12040000b2540b0031342c80c010701d20a90402485141551601c501000c5811001141a0b540c114200308a099480707400103289003d640502034062401656180c042c41d449844010500014081005122404044c1d51348803c0c1c9805450068951440700ba201d4994410740e1405005002140701404810600000840c1640d1060404d1074022181c44103141c0c1e07400c281f440090240e0405c400042c5212a1039003d180d000070310710111a42c1d07903940d02c0070030b00b242c1c80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 996466627 1250 996465377 996465391
    0x11130c020106030c0e1005060d090203010608160503160303031503050d090521060103080d020f03100812040815061c052401060912080405090f090105060405060105040e040f0b 77
    0x403200100305120a0304e960400500070340c14800002d140c02d10151240081e03600450b4810200450001034140e0240d001216440d80a0000c00404e512050080c0e96048601c0c5880d0104000d40c1d0045075608000ca000c03c000710003079902a1400e03003150f80170380103002d8400d13110228503c800740000c041074041281e1011440c05e500c80c850313414200418009049c07400415420000366156284800074000507180e41125001000d103900e424541c0101e03006071080e0760f10084140408030601c84600d40b006103203001c0b034400001701d035801c1001c2400003000e8001c038881c1e0051030304800c10104101c252030310040d0703100c2001404010352207407541094210003844207003a42d455010b284903044100b44108009507905d5011450003156240100043c0b50500c6e0740105035440b00c00c0d00103401082a00000e0754091312008100308a80e26010b0030700e8000010480d40261150f0074140441e2003401c261040350b00980040c0e481501d01428090381c5040301c4d00260040301d0750488003c040e8003050600c411f1a00403c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 996467877 1250 996466627 996466631
    0x10050d09110402041d0603030c0706110f030a050301081902180405070905130c0503060c19092402100c050301050613030803151801060207091a10020d14041211130c0201 74
    0x442130b070407560542c0000d01b42406940100200c1c01000e50004000d01115081d2a04030701450005c2e4000d070a010060395101e48500c0041100d900d4990404d0243d4107840a0a0488014002d00480c0c00c03030165480801035042204201040d41e480300d892107035903002d801602200d288540da10f0110317040711801c6861000c2240c07076511144c1004030070034002d0028036007140100181d041004060081c1c3c805c0c94110f50a03d1641980c0c8200b8600401c0807a00800c564038600e4114403c401d001107000300b100110344014018601c18118100c0c1e50300c0bc01c225481c50f80d40e8a81145c1c00c080900c01aa40036404145500c2a03000000001410b03150096119040038902c690519100e40305000c4240302d03500008034480d05000040c0040f990000d031640858a5003980400e440000c5e005804203660300e040c3c1290000d005c1000e0541054000034002d0603a03080e680c901000708590a025080d500560047d0031040e10035240083c0850700038001c0300c0c0c141e000140240341c1d040f41c20046408440c088039100c40036035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 996469127 1250 996467877 996467909
    0xb03160902030604180c050613080706081e07080402010518090a0b030d020f120306120a0f050f12040b070512030108060f0703050426090d0c050f10050d0911040204 72
    0x4181070080350601e0350105d41d03202e00c0781c200359a07200c003031503880c02018002c96010400e03880724886808800e0003880c084e0241e0f81100e4035002d008145000449203030020160706802c0101c0440c1da001010b2003040c0b259600c0800742c0380e030790045405500c541c0b218086c00c608108120241e0380ca035001360f4001d000058000882d115442c05050030010804d0340302d03066410011500c2e48400d07002ca00600c1c00180e490515a50765a25000070303840d0903803180400101d03c5005440e50800020b80d0b10300c1031050180086031580c40260004603030700c035024100d803480135009000400240d1044009480340a1264045c0c03646050508500641604240e0001100c0e9016100740035500302e00c200c0b0143c11082c145000e2044d171515032543c0741080400c40220041212041d9440c60016500c1c0c01e031080301034000d04404010000b410064181c24490051502c151048140c518103482c040d440d008821489071925400d0440c07810302d0000400b06070505a5400c00e1071020010a5611440100083c00114007a55222 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 996470377 1250 996469127 996469129
    0x200405030706020705010206010b09031e0109030207051c03030504210210060f0e040b0601022d01111e0c0a080a080a0c09050619050f18090f10090b031609020306 71
    0x1c0780c040e5100009542200c4414455641e02003442415680500405036880d501c540100e460410f02444c049001d50100c244401c0051064100840b0a4041d60896040c951200108814040c1c4280b880c0d212003120011180001c1c06038200c1ea0380280602d200d1803441c260300680c266944105070407500103030407010310592021054401c45000d003c2035481900d419041c44e00c0341d00502e00150010b08030440c90707400108580e1003001000100d003485940015245103002e82d040c40025200d11014440d42050740200c410b15012080d02c40444115040d0340c10b007040050007100790f40c01401128014020024001c001c20707180001403000c4811581d40710303600c3c9041d445203421142c01400f110b04000303038002c0070003c9640300000e4640e03480c624009c60700d101c003030700308265550321588800000140e00801d8500d01482840c004000880040d102e0610075540d5640300c4d800300d00100c0345118104400d8809100132401c1e54000884504060202c40078005801d40002c0c040301581c1c0012161038001003000b0701 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 996471627 1250 996470377 996470383
    0xe06040f0b100b0f0904020d0c09083309120310090b09090a0219120507140111030a08060105070813090f0b06070b0604060312050406080f151320040503 67
    0x1c848a100424940c160a203d129501c5100f1500f6031020074401291580785551140d040304c103030b03003c080010032562000301005844080e00344544c4101d4050304010070f0900a0b1440c1d510203040c08006031042c100d0340c0041546103684058560422072048940c404c0e00d1070324102c002c600807221900ca540c401854070003400b00ba1402c60740c2c0c0c24007403070980b014070403445000031340526503070340c104c510307074034801ca0b03500003005070794044c3d1104dd0181007400000c001c0c001d0214812090b03c081c02000c1551401c1c010040d50340400300c03002480103500400020824034410944150000350502d0a2460603125488103001d81d003110204e0900078050100c1001034180a03c1203a009400e0001d0601c50280d039031001518600440801802c0b101302000014140d40d12076100c10091980014201e0f0300f840b05d004001d085802c1405503501042c0c1a2000c00e18a8100026051155003054844e214910030b107010711007005501e03550040c0e442e86030714078982c6010000c0b1940104510b060041a102e03842c02040602d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 996472877 1250 996471627 996471631
    0x2270906040213110703030c050d0f0e0d0507021f0c020d060509010c021606050306040f0e1c0503010b0403081e160213091a070210020403151419090302010e06040f0b 73
    0xd1107184c01d1322905551034940c140d0700400c2c0c05080020341c00c41080d505440c030348540c4001d41b00d41850150080c924007001c0d403242030b904d84041c049520a00c01148295034a204880000c1d41c040c003103c0200324410f450f0300600090740400d140500040c2415404100300c5d4080ca4421120035841d00304000300708000f480b0340740b2404151b100501d4034103111030603130300b110440b809034000b04040000000e86640380c85c3c22999401e80d81d800b041258425000b00303e41c640080b0070804010300e42440410a00c41c1c860000c1e40c1c1660742c0c1422051405140d5526101030741e00c21060386c0f45820011105085410080e00640003424000f40e0602c0101c019104100606081c020b00422140c80c0c00c0c00e02c00401c075110381d4404421000219a602900c1d150303010380c42e040d8600c0318100780f00d000040100811001c1c8000204040100006103e0150308842c241100141120b10705002400300c803101c3d05004251300003079106070107400000740b40f200d411021030520008483c2039450b40201c00c2290100007022000079 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 996474127 1250 996472877 996472909
    0x20d031205060f01050901030e120f040806070206010f050f04090c030602300a0c090801020d1d0a15050c040815012c060d0614360a022709060402 64
    0x1540702060f500018149010f4154120b04042c0d40d141d040c0d82e181020040d4403540f01d44821510b85070040407818040c00d60160040385064050500800d03034007400021510b041e40c0600b0814101542400300307002c020000102d860741c0c4591103c40050108007411000b5015500841c4003507991a070640300c840c43c2e00588a0352000c400200b40022010800703280019800c07013220780002c900a511044221411806504554025440040c60082603c4241d101c4a45070102c19a006046940c2c10415510742d191018040c00d98200400c109071504d0540d4000707607003c100b58115909194482e1803251509a10700707002510301c0c2d00940140003c80d0980c00c500300c03105031860000300101c1540c2c540080da6030080c080a005a400f0700c8208108542d80e0000c103581da121580358074041c0f8100d840d40100d000e502002180031100d0650201d01181d90410090381402000020503001101c0d6080c407040c00034264808981d110b80a90b2100e15000242d000382c0070301540d200030665418030b070042000016040c1c445ca = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 996475377 1250 996474127 996474139
    0xd08360c010c0f0206090102010204170d0e3007080d02060a0f02130306050c0d050708041202060c1b0a020904230c0d08090f0333060d08070f020d03120506 68
    0x20b50005035100c0400250340d9040c3d40315a102c40740000142d0281c0030b80c0d000703000d030b0b0303045106408a0400300044584850320151f440b10744001c03159040c4030200116202019005098a461403085880211074108400c03064086551042c1d0b100000d9060040041c1c0100040c0c2060080c0148005c4a000e41000c446074100c0451800050011081d40800c0a00c0014019600c500c0003070320f1007802400381c0b525524100c0091081d4a8034400007848600700b11011a0802005410005910310005000340b06001000c00c1620b0100c11601341c10501d64101c41954181c03007490510710040c0c5860a140b8051031141c441101c0d110b030380310007000380c81c600b011491205034400003c840b2039a07036011090406a820507813090b81c814031440401d04079000c081b0000d4051242110803205000b08281109403400a81c501aa200c09040d250791400702041c1c407040e5110100e0803040001c40c8941008024a074818540c0648070482540032480003c041d00094000c500d4820001c54207078601d0007504c0d40440100c4078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 996476627 1250 996475377 996475397
    0x12030c041802131509030c0306021917070e0f130b090c0c0304052106010f09140f0402013c09080606010c23060a051e01080d08360c01 59
    0x32190f954050340c400c201c40145032816062015025820b280061600702448446454803424180c011307510481c0340c1d07680c4100f050800c00000c1c2c1700d140d02d41c0038a8005011850b8030b881e07000381100d02903003414540e07034410084000b2101503911907941040f10b2994a90220701d200801c810020700c0b400040600001500030001d4119804020007240c096510440b803600c0d403151466943c080800e400f41d5511b10031b00c5008004241c40036800084400c40300309032000d020442d403480b542031071900b05450380e030000481c6002040c010341c0030f00260001c511502015261210840c00e842e101a08603403021080c002c20400c1d0380c02d4450727024504001400107000104030a0920740c0000b850303020303003001c00382c00290801c0d204c170715455140750310300c06a5080b0030407116182050002540200340a4170343e04207000307141c401303075084803800442c07603040780c00c040041c10a1101902d41521610001019110740c1e0082c060a2102d180320043c40821407060807000c41c800132200c894162030a6002c40005043c030440c024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 996477877 1250 996476627 996476647
    0x1e050711370308010306020a1b030e0a050a0515030703110a0809070b0712031a04060801020301050f09060616082a010606033605010518010c0c0b1812030c041802 71
    0x115241121b520040050395130802640486404000d11312a024102816801c032051560148860801d120200c8119001c00d54910030060203101c3c034413a172900220040e440075004100280039590040260402007001c140b10f02140c0a0350b80445880000314009406003c0d203000c0030418003010746484a40c8500e07040c1e59031248441142c0740698034003055200c81100003101e12540c00c0402e80b82000d04144040740d128080280030b5007090151038010b824482c1b5000091074264070990040c140902014a031003008050220100e00450b8240c1d03098004004092801040c061007200711408043c02c40a0740c51494042030941b60f1551103081054284409280e94800b00701c2010f1441081071500300d1100969582a506401c1030b401c00307040c0d9468203082180c5c58012040c0383e080482140020040c0f20000c01081c0c0b9146802c91020307041540c0400000c3c803c461594403803885c042c021048400400c1c80181d4040380303500841e9038800c003241c0440c0812410088125000120000200541c18003e00c95 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 996479127 1250 996477877 996477887
    0xa060609270c081222030812070302070c18050609040302060705070c1508040302150c1b0109060e0c032a0108041401050a140105041e0507113703 64
    0x16800c038000000000810412426450742c0c4000d002e00780c10340b102500c060340d41842ca0b401c03020300030141151808280b504500750300c05035400c4c0e90b0701a11090500b60280107520321200c0090440042c190708000280108111925040090030302c42c0d1108840d485010100069940150180b4000c15092007131100003500810150790181e410318009441d00e02a040441c00e07040aa4030820400007848109600141c0c0145620310640c001d808550140c01d650f22428240e000441344010300d284140034600c203000c5107108008840c9042000460640f00d60384880084070601d140110450344550607a104900f401d02100110881401200610f40c940d003140c551607012075038140e070400c02c40000103020425012070700d2100d0307030046000300014542840700d08024180620184900c54620000241d2480c1c24051801c1c1c90703c2403006c0030294218215940041c08000e4114000d108142c3d5100e40c82100c10002810b00d4008a6800e0030300d0414242c13090200309a0f6032811201540704048007000c69000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 996480377 1250 996479127 996479171
    0xf010501030b040b0414010f0f030b01050f040621140d02100e01021605150a0507050a0c0c080a08030105090c030103021008040203070302060408010203040507090b01170411060304050a060609 84
    0x3800c002c2001c030007200001c0c008240b5038440603805840c1181c181d80c3c42000d0b90005050704c091040c0040550345501032444441c0d0140b00007071003001240e00500503410062040824100c014001041007516149240e04445030340007403901380400c0341200814014543c040f400c0e02202100907200110140c032000303440d41c968400b052065500d0703044859008c9000d41c111404139200c03c48030240d8202c50310b02103455034440c001c00c0ca52401700c04c022420103941c4c6d1056500400554070b07800c0c640800c07054140d03000c4020789070690307903a84c8904c0c00040c0309109000000c402ca1080b0301a41c0e480d81024100716610401614a0030100000e000600c0141c0301d01814829050a41c00c10245617915440002c0ca4000a074000035007000011030300003041481500a180114418015640c00545801860017260f0111106a000440303101c1e5020f0041c204612080d0424040c40c909449011903101040d06640107a030112410ba01501603107050003658414080504200d40c000d2000506004c8010340340c00341 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 996481627 1250 996480377 996480379
    0xd061508011514160b0106090e150d110102210702010318030c02010507060b060708030a0c0c170d0b060a05041d0621010b120105060301060803070b0c0c0304030f060b0112050f0105 79
    0x31504101084c00c281c5444080e44900140403640e15804010800d0501d0f224942c1d1391a0000003003400201c2240808032040f10143c00c0168140183d1500002882901e0305241503010f40c61003141c45041c0c07401c801e014610802da00e5a91049544001000c07030795100d480c154030078040003030100040d611003440c0203826024a4981e0302d071012420b220000702405000301e64404c1000030740104000303041c00618030070320085904201d50904403a040c1d600740605c5000034803418810380044030801e82e54020300555000c811000808001c00004a903a0740d1003114000049000840c08004901c0c0c00e09200500b1480301c00c0340c0b4103d0030207002103152100c0710000c01d0481807400101c92218582540300d0416100002c200a0400c8021461a402024180d40c1c40b8029402c048012818000000480300c1c1d16510070f025290a42d1743e020503a042d0b8215056030505070100304000000f03c0c0d8072440c492402030107000002051700c10032001500e0200c0140301d07401d07079a003800f040014101e4144036503811210 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 996482877 1250 996481627 996481667
    0x1f08340b030c0409022a0f070b0c0a020a03080c01051b160609023003120610020a140f100501081b1c0f050111070206030103060e030d0615080115 64
    0x407040740020702c5006603007049040f80c0c0701003a040030500c0000d124448100391030011850080124608544035540307030480000c1540a44800c1081d1801e180007032840c007894400b0740e0b815140990024076a29419442078800c0740c40800d000124960070320919400c11750041d800d00100622641c642c0d0399000c0c0c0d17200c1141c1100c405221806200c02504010a200e6000b02005003d102403003541c1200c1c6505000d50100130f04c01c8901c0c218007040041140c1d200b0009103140c40ca6596400c042081c0011590403040031401042c1700040010000600c581a240990015001245031a03051307502d41403d1865140859090800400003a18081001c0c5100d002d10018022004804000305640b042c44c01e581010061070015403605124041001250561040000340240400003003041454015000060360002d800c100410002c1c10940c080f076281c0c4808000e807030620703000308000401c482c0030b80d07c6041286550500c103003005500c450320318094440e46d10020b01c3c928200000400d01a003d40c103142e01d01c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 996484127 1250 996482877 996482881
    0x5150927040803061f020f010f020a0c0204050c0714060712060f06030f060806010f0e1b0f360f010903050d110106051003020a200c01081f08340b03 65
    0x1d1110308051010141e1030708112601e041209000707680324500f00307e102281d46004105444032403107000300c0d01d900e80d41e40e54040c2c40f11050340030131004001c05001e0003038402003004060005030b40d400000080001c104090143c0d4500404c001e060600c1c41b5210301d0600b480c081d010f00c00ea261240c400341c00d031505841d000039012005c010303500060005130010709452059800008500d072140c00c1003c1030f81c140030740058107a150080e480204c0c981c01c1c031008280403400d2003800c00301c80d0300c100174000c8070350b82040c42011107042010660280181001320700c001000b29080b005142080c0500a82c6480c007031a0184c00786281d5264a51509145250310003000140407000c01502c10940210300a04030090800851126021000c1c0080d481105130401281d46040442c3d0b4800d110f410b03003410080c4078406082c00c03e40703c90046074400030041064805010310840c814564000c0010341002d89000c00c01020b860b0705180c80c845a07442c500000c002d0140714110384031000d160070400d0308211400090219200c1d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 996485377 1250 996484127 996484129
    0xd03030207030513031103100209130b19120c0b030f0718030215070309080d0210090611030a050106021b031507020a02030d05120c041d04020402040515092704080306 73
    0xd4498004c5030491000440700c0481802490380007400005000c0301203c0ca01a44000c16000744d00519007410341c8840703010b009051903401e5030031018840c100140b01000c1d26404440245100149401c01072400320710140c0c0c141044640212140500350704e8031058114940607000f07000d04080101034004104200c1c80240110f03101e03100140240d0390080c0300ca04042034691607081e41307410811080e0001514503000140c401800b16910074002c140d50b015008010008510b034001d80b49028040343e81caa030301c0b0010501d2202e403101560203010b9140e4041915450044000d1901c140904d80300700e40301110300304166540c1c0015103240541c00c85000d0403210743d2100340607402c10440c6035000e501402007070500840c071580300c401449011130050f0740d5205900e0341180c0700550b004138085d20801206400c03000e010441052121580144018030140c82c103500ea41c0400c40d00125084054114180800c03024601d140001d160317014048030b102001401003401d40c2e40d0166a4001e0009081e16800001007041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 996486627 1250 996485377 996485387
    0x1008091902040b10121a01080408130e0103120f031a1908030a050408070e040b07051b160504050612060615070c0f081509100b01021f0902130b0d0303020703 69
    0x2600050409000199981c00a0031024a0386545400641b03002c441c02030309141054404080308069650035903542c0c560342c0320941030340414100708490303000c1400026451190014503000e503104036484101510010700247c4440580300c801028141001034480c00c0390021980c40880c29030480308070042040d15401050001400c0d044681c041c00005041e10300d2640020040c422100c8240480c2c28482d0b54000c85d44155400741d80c000d010014240114a24501c150060005480d41c0540c2c0e030325109080c448541750940c40d0002d6401e481041c102008145018412142e001c08203440072000d400c1d0540c030b035680340d44008280601c2080b507450700306018450007040c0d5103d80c5d88807070030315006030b00c501da00c4184801510031a0400c4c420603100d844181c11351a90103003d1800c2a006104004a4802c0540038140201c0c045045224591110304190701c06040703002c18002d42180003511450174018032aa81800041da02220390030000179030226200d0040c00492180c00d4030300180c481d541c502c1d04a030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 996487877 1250 996486627 996486641
    0xd15211401150302130e0c0108070e0a06080712020c0309090c1b01060e09010e0a141f02180a140d0602070b0f150a30050f0c100809190204 61
    0x9901e601e802404035944481409a4003a207008450b264001d18105403590305464280007034141a802801c60045154011480e0942140d000e04003031103c408894042000e00c1c000c0d40c807540c0002c01c1c210601080c1d98014040780001440e0002c15032071b1203c1500850307524855458064090b064040020307030681c9035036003654002601c0b40e80c840e160140b80c50407180680814060307646820030040c0480d607103200501c0388200500240000e4854194030382c0300c0700411000005442e4440c01242c014260080801d4164804841d10b880b0043e201d40e0000401038001c4240d03c480340c02903a1850f000e03c5807918510204078a410120362881c400c040300c1c549480a03000c0d0780e0000f04074008000c1030182c001004440716114580740000c01030110701c004204480580c0d00d01c04d000000d040c0704121615411016880400d001c100040203400c0306640d81d6040ca880499580503845030030494400b0158a0008510a0000c3e0300303140240030f60a08000c1141c88202d0107044000d030340c1601442c0411501d50b0f0f0007d030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 996489127 1250 996487877 996487913
    0x61532091003030801140f0f0a0506070c0306060e0c19051621140f0d0212011d07020703080a08151003090b0606040e27060106050d1521 60
    0xc0c074142000003072907800070340c001200030903030309000490150301d184510182d91100074417211004c92a5014003006a9802d030a6680001c07090501088589526001301549803154528540ca10300e54145081100e6503a005202c0891030f46091211038248403080d610070b03015a412284446040107030540303140c4076032400c00c1a203001201d1000c042c8884010380c20f010303041a0001c04041003003000e08942481a208050b92201800c0c080c4040b082108800307000c2402603000c0052508000c0703080046200026400594955103039015072100440c0241c0c8240c00020600080c40303118110f83e5180b48502508202400b0081c404000070f1007481d00300c1d841d031001c0a000e000701101b4041098000e001c0e00d4956406c0e902d41c0f4200d804203241d41840c2e4116021184011603481c0b55469001908040101c4003624400320030482c40c04420841d02404068000c00090301d400341d81c0c0464041e40001d03078000808503d00c12940c0301041004c00d104400d80c8078551410440740d078412080e45040103e45903242008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 996490377 1250 996489127 996489139
    0x3020d121b081806091b010e04091407090209030307021005070615060f0c0206251b1a21060607050303010f090b0d0305040b181c061532 60
    0xc252090704210003e00541c00050210340d80f1600350a482d90f50310041d01c4004803544004107948050340720725044404224145420000350458100250960346030031003d4642030710009128080d0030040024000420031110150304103071142000035100e01402901034004d04d0601c0003140745078803032001c9400466204000700403040f42c1c1643c105000301c60707015030400318000481036845ea80c0680c20b681c444550041040f813801d456030404020940700013815150300320360a402100001c030201d0111050003500b030840c103c22031502c6a050300f4185040d01d2050f19020810091078401d5590450131b40100004011002a44031400480c400b4402c40038040c009002c044004207a2081f801c1802c011504220300c148003020911040041560034607a00a000c140c0070402080b4442c60310010340001c1e01400800ca1040340703003001140100350b03807501c0c0340400503146607160100000b42c45580e100c0006111107150050918400d4802941511020351540c450b4000b880000041d810b001009008040c1c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 996491627 1250 996490377 996490421
    0x3020c03070302060f0603150103060b01050403021f020d09082a120f0d020319080a020d2315150c19050a0b070806061c2409110703020d12 61
    0x82d11000141c8840810701c40b5031006c0b41c032500d00000c04141c00101c044113030b0a164655910301000300031407a009410f00101340800405a86c42e0040340190700d810800008440009620090800e2581e5031080140301c14500280700f82800004c4208000c2080c1c04107181a15442d581009010003002c0b0040c5d002c4803200c1d154803040000318503050380d400500c0450300c2001502d030050f43c5900540c00341000ad0022400700b188010300ca042c0254002c080503c0c01480c4c500c6009080302501c5000020324102c880e5030401d246288003105406501203040c1010f000c0c081c01c140009004442e0f11a20202c21395070201d1089200710061002c1280c050f010104500032540514180352501c0031540250342014540c0c001035a598003030820b01e480345600405641c9400e00b450400600300103130aa03e01e54841d0b8800c01c002030070042100814058041506002105107050720300005d950141b81100c0070044248840c80c006500004c22103080300759420300c3e0f0007160107813403107a00608039101581101c1c0c82e0344203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 996492877 1250 996491627 996491633
    0xc1205010807030521030420041409061003020a061d0a17120a0f0c08220f050f09150d080a030906050a0e0c12010e06150406060207030f1203020c0307 66
    0x142e4030b01228840c0303040d02e83c8050000e080e031441100540340100768450800c00180041c1140ea14030700e44498618030003021001004c040390456400030840010724454505115282d9000c021040d0f0144100e1004009142960301003440c40950f0f20a9100340152006a003071424030009031080311034000360000c11004d0762010685800c0180004020b42402404080740c902070004c01140d86111850300e0300e03000044101c00454034261039040035504070030103104010705010703440d9030596032800109402c40e01c030f4103040005590400c1940301510800e6141c2d40021203841c0d440c000c03036104000c002c0068000c903283c004100e2340441450000d21030000081d901039010b42607800080e03a10701400040100381e44d018003010448000b80c902c0512035005078110b2445280c82d484400310280200008100119180340091800340182c1c0d502002d60000c07180144282020b1241a0003401140300503d0818510744908a4601c0d0030781016104080f034460f090459406601216002c0120f00104c80d80c0300c172141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 996494127 1250 996492877 996492883
    0xa080702040c0912020f0d06050f2d060d030c02030f0607081006021b0a090603030e100806130c091a070209010b04140d0515131208100501030c12050108 67
    0x441240710700c0c40c0803480031440e8440c000600a40e401d07190b080c800a0420340070400b40f41c00f13000c80c0580c01440c88000c0d100241c15406854050180c0c0400d600903030038240140e180d98084d00200d03030310001403245198842040d0410840c2c100303a0603200128a401c0c20f00381103c0250030248042c2d0944681d088070082041d0004401d44907404c60317541e400031a180c060031120942010b104120051b031050303c0380300182540025800c031841c0300405040407255956618826248075a1040e80030542d00d00388042c1d039045c6802c1c0c0e07050400ea1890301c000c591401c000040c02480c1d4600641b411142c1e10b80b640003685010b00181006440110107400c4d4100c1c0c170007a01101e07540010400c0340070304004000000e107030000d0003c0e5025180085000307211401000c05024003051001d605488511900780102261064000c046000c0d043c800c9446401b1111820801381003c66074042204001040c0c042288568854981d20103803802440d020500640194040710b011141030940808075180500010704cc1c8400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 996495377 1250 996494127 996494137
    0x6021212191506110d0e28060e0f04020a09030803090a0c0902031608010308040611030d0c02150708010806010306020d1e0230150a150c0c0806090a03050a0903050a08 73
    0x2e81c0e240304950b9132064100741c0790784181291030302162504104c04c00d149003003200440301850b04c51881090000742d1b142401400c01c0d0b80c0c07211001ca02600c0c1c8640c060b04000c0d4454400c1d04003541e0039454001070f100300a005d42190712010704495804008215207200900c1135904598000c1044110382ea180c0b02088029070050f0341c45094034484400d01c004070340c007891416040fa0f403c030051034141803502c0e1301a0f91100e1407200d103181d01d000400c07a0b21904041c40c4101710304000c81d540107004c08411000000084400072b446e078404d11580d8001000b1000c4002006415a5440304015840c0d19007403111801900c0070142408641d03040301c880b188503c045034042e280c00300d66144510805030361001050740c0400300c0c0344110f0300b6504000024594102000307060351582c0020340880502a551798030b01481c0e43d0700030110340004d6100c0440700706100b50110008054034000b80a0700450400c40c500036901d151116005080c0840842c881c60800d008500e494020740d044010781360700002c00c1c544000d440c1c1c06 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 996496627 1250 996495377 996495389
    0x60c1e0d06140d15020a030914031b120d1a1e030d11120c0a0209010b070c090b010206040b0a0b0a180608010c050d020c0133060212121915 61
    0x140d420b0b01120314140341242c1c403580c1c000341110040b09140740c001d0041c0d0302c8a440d8109041d220010800002d2007402001c038030211400146443c0e202e0113813403250b8a158007e400181e43e010f256031400e80c082c82c00444074441da940100203098504100c0c151400c5101080003079204507844440c0c8102e003209405018802001c400303480904040860035941c15001410460b0141d000c80310503140c1200e000000c202000c00e14084074140705a9900040c65503409811005c0d0041b400309412040101c020001c101905101c0c0007400450340c1900001e5540400900252543e1144d4001c522109142d50244003900c030042c002c5000e464079014510868441e1031500480185001000210310106101d15000036006a030f40c02d24025a0030855400394100301c0c010500703035580d0040a203040c42d0014000f002c000c40d80088101441c0408402461800241c0c094010340d004020540000048041210240c4900341900581a100c00a0102c8180c3e4203001380c0c2031452410030010300c080c181051800407104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 996497877 1250 996496627 996496649
    0x90e07020a0b060a1d0a110a05041806120204051003060f141602070e10050a03151b091511010e0604021c0302060118150e01150908060c1e0d06 63
    0x1122014048000b08601c43c0b40c0d008076105d42c0b0260300001180760b403504001d4251000c0b1340c0c0036100402020f81d901417000b19003c614002001c01c101744500f40310712800107070303040c1c1000001d2610b101070280f81c860751002440750703a40740e0028030080c42ca0940c42010b10740000b4100807218145070240000c05042150b00b10b144500000a180414581103100116030079901a00700c05181c80c1c0c00400c1f4041c041c110f600300840c000b4010595407100c5402c0f038006d500407240c540c00c1903070886007041101c0c100c070403408189135003155030441c0079005031041c0201e0380c98107255a18603400e18011606941440586a025420903180c4064a13100086c402d02682c02200c0759005154500c1c2c07500c5000f1007000e4000d000d070708000010040701920a02c0c0c050043c10101d00407030292007000b09560100e003283c211000000e00240180f00a841d1503640740c0c2e000c4404d06044103040d0030511030790741d285001460484600b00011b00307001c441000340c851410480c1c6201c6001d40f80c0403508c1010010707007080e01401803c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 996499127 1250 996497877 996497881
    0x60919090c05131a0d140607080103020a14010c02120102070203030318240601050306010c021903170705030405060f21191406240a08010e060609010203030f07090e07020a0b 76
    0x80c005100340c50300c404502e00c0700040011450301713114080712030000682c1d04c410011807050700030b08240700c5a442141e5a03600c00b840784d8150300c100701d40d01000b50440c2002c01450090030ba59646c1000011111a40440300700c040581c03140304a03400ba10032800025014000807040c031011003803000840075499140030030354100c4400303c240350402c000b5250b0601c00440010b004202a540107000460700000103240001c07e003250b54001c00c404270703e043c4140c003019100720801c005100c1d8202180001c194040300c0c1078580a0561551696800789000f01032003550006030072410050444110f0300c3d80c41d21848010f01c00c4e0448078081406c0201120038501e40c032400c604800900c4034600c190190340314103068241840d150401404041c05c04c2183c140b1044600c8050840050034180140215682d076945031200ea6050841c104000b0102034900ca0046100307001700c00b810703a00401a40e50000981d021003080d540c0356481110a000503a001e083d1641c80c500278481d02c164045580da120900485c1d07280f03001e07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 996500377 1250 996499127 996499159
    0x6030106090c05030a0506060f0f03180f030d020d06150c050f070b040312170a1d0307020d17090d0f060515030d0c02041b0207050a120803060919090c05 67
    0x3940551040c080001c0f010400155410110350149802400250910342400030014500c10076500004a0011a1901208119640000f41c012204200c4004060402009016016980ca02820302c511424039004240020b0074052039000c01c006103203070314190841d01180c41010b0900003809a060340e407409608070120040100061000c200c0e80d844014501e05440e5440d40d41026400402800401a080c0255402c842c034a1160600400b145800000c174006505461070001513003509802885e0410700c50359000d60780c0c124980c04c00e80c2d00a403542c1940d1610100303c081300d20031403d002d503004030700800e0f001c07d02480c10684250948210301c20000d80d01c0b001c08406180390070108040d416404000042d032031300e104206d02d03442c0d944060710125030700e00c0400300d00d01000b80310712042006070300855007004a85070401c3c5030070090068503551840303440e5940b41c3e42010b1200405c407a001d40010008140c0004280d05002c00d509800d04041210130f0b03e501d4210f0022800784641c41c814500b1445407005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 996501627 1250 996500377 996500381
    0x80a0906110d050903030705060c0c070f12060c090305060f040b010e090d0e03030904060305060f071403071d041e050702070b0414040b0307080604060c0906080f2d0603010609 77
    0xc0e824002465103540300b2100f1103107903004007011034040c0014007041001603401c000c5540200001c141c800e441e4205203d950345040d84a5001c0344000c8041c500400c40200d410401d0381c0e0717440d0840400b143c100d400e40c20644001201d0f601c01403042c40b4040420209840301f400c01c5014501c14654540c10b6603954510b404440e8065800489a4224a64624000703000e8400200c4402d0098141c0e420000e00c480094200ea44680c4281c4268006204210341005403901040d40800c45007002c0c02c80b00280d01081c601408010011001d000094442d0395074458020800c48a1060081c001c0c480403070b80343c01100840d545202013140711420607010170070701e034004940b00f41602c240c6105103090a01d42481c980d000481142040e4001e5900c80d400c40141d1828000000a02141c000512540c00d02e441e02d641210620405a010040340034001d000159110040c11b81241d80303169021a10b44622001082c0001548001c420718100c25520b111070860b1801340318410313001180200314580d516000001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 996502877 1250 996501627 996501647
    0xf3f0515060f0910080307111203070f08030601144e0c251106120106030c020c120106030312050405120a180b040302041503020a1719080a0906 63
    0x15009229405280c0c41e801c18110060b844942141056403140d902c041c450300b140d01081c0b0944035400c4683c00d8241c10304100701882550300640c2700a41c0350591640f1440c4035083c00020041c910400040850341982c86200480e110b0246903900c0c0303959503d4801c0541103107840700c8402903824042e012540340010121140c11540440c0c605011444540b03e140000c0c4101c028000030001400f8040707074090703c8a042800e4003c00003083d5075010f038451802c241c1403007907048000902c109002c121500340301d001050b0907030444416081c0418403901040083c0d04060300501c00c0c0340c00814080030041007050540103101103074026110180850f04805900e000d99070f0445000e00540e200068035000c4424500085c80c0802943ca001c1c504038508084241f8540b0460340000c1c203007000420188154541445400c1d03500f88107070144041c503403566010501c00c913420300c182001d101901d404150302c410148140403ca48004c0000c589541d110320740b06196801000d80c0030001000707110042a502d024410030701e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 996504127 1250 996502877 996502879
    0x50c0909060c0c16080a05100501120b04110415060e0402030c0702190807260a0b0105090606092d010206010305060c0306130c02010e0111040f3f051506 67
    0x1565607125124055298020300c241d100c144510312664074001c01d1084200d01a10259024010f010b4547c20014603040c0101c079010b00300c5140400400030000e4004002d1700203603000c644d820050b038560a24030148200140a603030058104682c0c500d44100c010f84140945165032500c0140365084810300c4104d01044641c1e00813030030200301c610b015240400900c9804045103070001101610fa080c064117202c015031080d03d080d0304852a040012208801544100b0400c8004000344c6482e602e4503e406401803241138041c806100100d00103480d000c0446a5581c006007034050704494003241d00a070508d83d903046070851950003042a01c3c1750b1001c0f0b81d15041380d40107001003030309407228081a04036038000f401150b03002001d115101d0241e03034140500c44100d0040d8000194025540b0070590a50fa13540c5042103500c60b08100501840c00c2c10141081600c50502c13180d42e000202441e040758800c450310164501c0d01040c598807244040f84488000c04901c24806e94070303500403906101102520954020b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 996505377 1250 996504127 996504133
    0xc192c040f0b070e01081f0302060a020709110c06151c03180504051303050d0f1a131b050f0d09050304180b090f090a020907020a0c0b1612032007050c0909 68
    0x820301c4226000e409090030804c0c501e0305821f456607940010210f0380b0411204000d40c11250042004040078441d0301e0780c2c20381070940c1f0340c0750003032407080103881d0900200083c46464903074601c0c082988072026042409810452221800c181707a0034054041c40240084810384101840c01041c141400c0c003420780070743c1c0410400c0d2608040e03981c00340c41c0f5800559403c104180c0e282c5c0001e40f202c03030f5400744020b1456013410766103031641d08c40f0500102510100e9004e049504000a1500310554002c00840d0341e0b00528180791074103403030410604944a0304821b15286400c21203079a0902c0000b00c010800c56849005c0d07441d550700c9406840041e640307525516a48180108005540e0020120003213a20481c3d00095840b60b805540c00140084003c3e80c1480040c2e000d04c5441082104140a10003d4a10340c000d440c02e24030010801846941c1e0410010700010b0800520346c0b07158001e03000440340210281c4da210f200300d032021644101e9002981b060f41d0300d106405000d941800d00f0046903000d6070440d000b0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 996506627 1250 996505377 996505381
    0x106021e030a0212070302011814060609070e0409030c060615020f0106080a0f0312050a1b080108070302060903030c071203031404151806020d0209030c192c040f0b070e0108 76
    0xc4c413a036607007201da029000c0d952a450940702d034904403502d01d80c40714400c0101c0c0c04880c4442064030301c1c01400903c1503000345203050a00568075040100c2d0248190105d8000c10311030903d240481e08141c484030010103040c2000d8011480400c03c40130195081426070803180e80480c0b0540413400d80d50184615a01a00003011020110f14140c601805d611301a040c003aa140d4100c030118030451302c0441c0c08000241ea600344848007a0f00400c81c1145c1c0501e00c0c03400070540d50400c58443d8503a0b503503101c024800c41002072045910b031814405c1d6500c80716408140c0d00055a0f8138103d411442d5928011400249040403ca1402c2500300f5058003441d003040300d4030f18001d4021940002841c110402d212519011040f503000603015000902d85a4038200025841c1c10160044c14500040c103803c0a110f00009807103142000f4050354424221003004a14184c002006000d44580c002c0c01c5e00022100140b013003c20003401140c4070300b100c04501c19407601016540304001250040d4000c11014005265880 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 996507877 1250 996506627 996506653
    0x1a2113110f040e0a0204110a0507111f09051011120304031e0e010210020712030b030309120c040b04091e0206190f18120f0c05091f08010216080a0e090106021e030a02 73
    0x4543c07100513078080e2140c94330b990301054031400d002d50300002000089007103600b4005c5003400410240360716141c3c10301201902941120540b00c00c1e54040e030348003605000c8001018103211320650355040e4501050308510f0180000000c02e03480075420660301520034a4440d4002d01854402c4030002500181000d140401020b030460184c03201d82002c0741d041c40184038148031a85e40310030035403840f030092006202d8000000c0a00054484060001c1d120f186042461404607a000c100200003103804100b800d040354052000030b000703001e0302144241340c502d00d50f510074041d0742051052001a010713031a00c200800502500110b202240c0c05501034801d400c5d11040c0006140d05e04000d0700510909140f10020340b18404685208011110403400c4012610b418840c403800d10b00a001424100c4c0003076160420540000d03628104820004080301c10010355034030031510400c2e1410861a005100d00c0065a4642c002540e0b4507258225403120442101d0740503003180004101d40e0840c0040d000f0784012520b4003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 996509127 1250 996507877 996507893
    0xb1e0411012d0813030207030f08070c18050a0c0e2403250c080a120e1e072403090305041a2113110f040e0a0204110a0507 54
    0x10110906108542c00c512001035214503208106103848040c100128089003801451140003520780421143d25110b4480403960210303048050700d810038240d01c1001c0c0c0c030b4a000201c0781308550026040c03071003d07640801e00041201103101d011840c200c0611103502d880764200222106660603a000ca00d601c5600d40749401e164034620035008403007141c048800c00d440215940c96004840e154089241300b00c02c01c80c01c0c012900f00c241c5180311841c2a4009120356610326020b80324116011050025190280024070103d400242226003090705a50b01c5644094a21005242a850b181d9071801a008041009000d02ca034200d182003416142c070642001400d004d60041c031920001340d0811000f00300c040b1b0101c00e2104440011814452074650b41c80404130820700800c501c070b04804e5461084024070102d0303045282d080d080c01ea0014241440642004c002030707001c4208192150f0000d042004000d01c8001c00305400c200d45000b40c0e000d00c1034560311480c040c414418465000c01060b02402040c01040ca12 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 996510377 1250 996509127 996509153
    0x501061d040b010c020301050a150602060108100513020d060c140a02030909061212030403081024091a04050a0803091c1e0f05070f05060a0503100f080303040b1e04 72
    0x103040aa044c104c40e500800d003034903011280308002c6500c0d43c41d800c0c600140083c82000801d042d1000d8400c550401c01113603110040d0050703802001e501c07078000c03034040c113400c0115040345d07540205148081c158901e0306801600403100c003800440c0555803103c14001d512012a400350325250f01541c6880d4085081000e00c42003d0308141e0007800702140b00c107038080304005041c0340601030303041d0b01d40344e18081c0b038000c206200090160403410400e40c810464403040f800d00c001c20400a070a40c00c0c0c00620300c00c0484100785550311070b001e980000c09500200744014801070041d1407041d14211411520b901e21a07540b40308520b4010380007001d030f808540840748c101c140010401c0c40b40640b0120700c1500b800c03040c03840324010000c0e40d0700c00c0f100310b602c0100101001040020041000e0f40c0940c0c0c4c1c0b41c000042d6840c06413010300401e0040000c000381c0751160445403800078040800034900c640e51242200e0342d69400840f0100ca461035040041500e64501c07a810513601180d0300070301d14541d69140d0364030070341c8206 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 996511627 1250 996510377 996510379
    0x1509030f1e0302030316020a17033304060510050f0f0706020414120a0b060118050a090212070207050d060c0201020d290d0c0312300501061d040b 64
    0x107001c01c01c0c84003045801040c0c000600075402180c49040011a4520203400d10000e882554000c00ba4000000c824469000c80c100c1d1000041351a40e0318241441e001c510404100505c28003e65840c00c2c030000b40c40c5501552031025076080240540341d805101009112a00c0940807030410700011001d41000e40080a00c0105469454100000f0780d90b40380aa8001d17400c82e008030031a010f80c10b5680d0030301071401030141c01c00070003c0c500380646484041c032100c0d024100d241000a2601e801101020240c842d0b801080060710071003c003652030003454000e40101910b58580d11440020425192001901e10242d60004145040f51401e03030f6281c05c02800080041404d65400340b02030103280800f032103400d4503051491421040c000d4802c04c031b43e49894078008601c6c41040c4441164002c80c8484d03500c1400c0d2584200b6140504c908c041080e00c41c05001d0303241403140b80880f010160180600302983c3d40c1c11000d020144a681d80700c03442070b180c004a0300d1203046807004d0318540c0e61051070181c100c0a0306940c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 996512877 1250 996511627 996511643
    0x20f18130905030306091f06030b01020a0f0b040302010c021b041a0d0f12050f03041e080307020312070e031b060d0207050309030c04020c10091e050d0305011509030f 73
    0x40a60914030580300c401d103060b40c4a800110030420203040c80e032a000d5001058842030344a41e01c00c85203c86059005000b0340e0105541c610070350030264020410412659001149140d0301c07081e5180080c0c4d0400f04482c101c0055003403e0030369103210300000380c1c00c00f070710400e40805602400210500000300b071031103040842c89102031660a10350321841e51200d04240258007142e5a900d0605010410090001d0b40f003003000700400170305d025411080241d94015a110005c0c0000881c03c034a0799205601c0c1c01d0007d054510000240007400340c000000b0130891a0b090021561541d805005440000202440c580c140e04003402448144950603c12001c802c80200300a0500e06909101d00803a044100100c86551000a4590b1107113001c1180c0404580c0490b010361a10051941d03a40d19404402d2403400b400f51150003407000c10000c441c941c40c4c114020340e051100f040482c10301c15a039601103810880464900400030031084002c5500312900c2c10315172680e0440b1455a500c04600100c01942a60084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 996514127 1250 996512877 996512899
    0x13030810030b0703150b1603081902030c0d060e0106120c030615030c030f0c1403070e031005152409060904060801150e010302030a021e0a0621020f18 66
    0xa20b00700c1d240e40c02603089550000d0b281034024242244421581c1206900f850280034688100002801110034582c1c1881c0c42480754589127616113000f0f0862100c1080c140c000320800801014070030103018500030000040c001d203aa607000d11000e801003801100002000340c4107003c2810103a4003c00c00c2d10485203000514544d9030480640c03034960002d10140060b40b01c108601e111a854000c1008402c2c0701c0404100d002500d0344050203950b50780308481882c55010001403000f0740929462150303004042c0036a20700e11500491030300181411100012043c00d001c0001c280c0d410301c5000403100d940b10380700c0c411094024a071503e4581d0466000564401c100300000000c58645004080090800b0000490300040d04021025040420b8100c0d1105080c0f510040025942c00070b0401c40b0b03180c0594182a4081e840700401141110620710a80c228034901d0f000a0042c0d0300c111000e100c001c01582d5104411040c444240591007460305d5420140e90510039030204560810f810030b02c10f400113240c00460 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 996515377 1250 996514127 996514133
    0x20607120206071709031603020a0602030703091202061e0a27050c01020f0c0103020d0b1807020f150f0c12010b0a0306060e0d030c020604080118140102031303081003 73
    0x415440d500e080c0060300701400b0b205555800c00800a0a00a212030b00c54a62400601c0d455907405028080300310010100c0d620001c1c580240600102c0e075802c480290741e68501590f0250141c0b08544040300d60020601803180c406101147d114001d412146601a0441c0c200e881d44c03611b044047d00f21a60070380d540d0600088201010290381c40c820032900460300540d80341c100941042c5142141238195007002c141036041c16804070300c010030f0070b0302424016200c071030001d030305001040c4100e01c4903040702e9440c01d070004d48412035400038411035040c3e080b079081842c040c800c642c0b01c2c141c0c0317810460705070204808200c81500d40042e443d8002d107144c070442e007040c2d00c94031030030030b090020ba0148545000004440508130ba05000d508090485400e241101c8020703640441c16400c0082000f504010161002c4000c41d5a81c01c12107005001c0d000007440007107586c031106030b0700380d00a000482d608003911501200c0464107000b580d20452002c2c0001c5802c0c205610141c0355142d00500c0c190507051014404800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 996516627 1250 996515377 996515393
    0x2090f180f010e06010503150c0a031b03090203060703020a050f07050316080c0c03070b2d04080102040609050d0c030201081305030d06030231020c0309060a020a0b100e04030507020607 81
    0x19920200042400041000f5250a01c40306030009406034201c070302c03072101000701e070b841598005041c448119070b1006800f0044000700400480584601000c030449000700e903250f00400c1c54680200c05440103603d030090290101d10801c64810301160303040c00402580010b0034007030104d140c0243c1c2035926140030901c2114943d1120442100c07442000703c1c00000002040181e681600c40c1640102101d505001040e0140d0003030741410242c40e28540300050146c441c03c00134242004440c0011a100c41d2580e00303290103904030b4001c040c001510300f0400101c61030130407181c50100c1d8002c0d152000c2d00d07007150011602000c009003042942c0d42d18000000000340100000c0050020000c1e000800390308510400c182c80914403103500302541040240340c0b6544800d90156441c6900b410010703512852010044d0a500454188580c000d41c040f50b054040c54002c501c00003642d01c01d030504020381d07880741c480c0e505940b020b025603814809600c0020380001d000300c00600c4031500003040203080204580e11800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 996517877 1250 996516627 996516643
    0xf16030b060c1e061501170a09050d02030406030b0d020d0b062e03110a1e0c0506040b0603071703030402131b030b091503151b12010f0f0302090f18 65
    0x4202c0958600486448105029140d08103050402401081c500310300000e2155480c40d0006071400d049031f0104000c00956801030720323101e6202c01aa44201010003019459810a11400000c282080000b0005113001012940c00310350080100d007a6015a42b00c0e20580d001c014038454000c040b62240000a021a82045c00311440c0c1401002c101d1b00700c1d40004007a10040002818028030610011448903009030080d078459600c100e5034600c02d80000021260100f240354013800b00e000344018882407010001a05224050541c101c0d20901d50316600c10040c00b440c10303000c02440e0414030101c0c00500d054801040c00102010012580a5445081c2c001c882a40503c1c1ca01017030365130340840c0302d0b410003241c8290311a405a110075503031940354010a4071001d0001d000500c11580340001003c00500d6034840c01102c0c424155103450700707c1c189403821795010030302a42207126440788000608004400d143d41c00e0f030740d000e0300c00082510b40840007000810040c0688801002617101164174690800c6140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 996519127 1250 996517877 996517903
    0x803070f11061b011401030b06090403020705060d1416140904060504061401030b0405060d0215070501180302070f14040c03110a0903061a090408310306050f16030b060c 74
    0x3d0182e02820206030031603403040c4400908140e2000104081b940140c43c1590104c800d03140e07110320381d5503032a00300d0030140660001c60f402200030401c081c800da800c0d8401e0345424043c40410074117488004580040b01c0c0403a20642c000b420384540c0684100b50701c00030307040340507020748046801621240090141c4040380c103c40070085046580c1881507078103002d030b070f040098140e400b08000d04024011401164054401034094942440e59224079543c050407210a00d4103c0002c00c04c00e0a650b41081c03090a034640c040e0014443c103040410580308012031503003200c2c03040382020490f007003105c00d0101411400210b44141603444180f4045403480d9401001c1c100c0c010b541e02c4c0c610f58254500703c421106c85904084403180100d402d03203500e8560300704482d001504442e8264440051910442001032142109d8000000c1c1c081c40a0220383c9903402401074070300c65101030110750780d111040e03941c3c681d084807103519001e01c44030014010f50183d84210003d540203800180b904000c00100f91402000039862 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 996520377 1250 996519127 996519157
    0x1a0403030912080709060f1b08031812030417090a17070807120237180911133e040b0702012d0c030e03070803070f1106 53
    0x12402c110003419494504142ca060082450801d5840100000380e41d0003280d00b0b1003072140030310396242d02460304800030700350111010351001d04514010703601ea042552403899054400c4a03000006002054a40d52644980d817264119540c54890b0034080c05601c0801140e035104002120164a8440300c0c28042c11600b14440c0b46a00710003001072a004003544500b1903900407400a0115100b0180302c4518550110340808074135800c0011a020b2070309104148a0903088003011090b1071601e80c5564080700c05e469040c4854085a03980d400980c1e41c00a070083c041401040104154603144004d0043c481c004c000002d41110400103004a041c610a03400076401a04100c00710701d0030110110b41c0c101c1c1001e90b030140c14189060b80c4c0e010389000e8824001d040c49010304403d00200f002200c0051040d212082003601144141009001501c441d141980000c2041c0c00313260250800140503421100040002d61402c81079440342c1c00e80d11204241151110010340d022a020703030f1030302d0140104802107248 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 996521627 1250 996520377 996520391
    0x30702150f39061501020703020901090c02010e1c090f031a070210090308090c06040812071a0112150507020a03030b04060e0f090f0d080a020c0109050102130503100917071a040303 79
    0x4c2e607000015801040c50440d80100e00900050312184c0c00039045650480c0d01040c0b0017110502a40507040411414445208428148001c1c2840c0d01a4000e0742940313450b440c14040d10b80c140b0445001490202a0503462031901c82645941c4c2c151840d81d000c5410304c1542d00034031502c1d601c4400c0e5005081d080d80092290818400e44010038410002100000c0300c030540740901d42a1103544882c0100300f49031514001180002c14040000209004000c121085010325031b110100c20071545100c00065507480c85100d10540001e03040d00c641d90103a03089400500c3c0680031660b044000d8030320445041e030029141c403400154241b9029156010f000400b0042c005460510720301c0d85840c800003080040c541c44071a01c0c6000c6038001d1400703900103841c0305002d0b03582c01d0019400c41c090210f03000010110340c400900304101c1458841140d090f0b07001102510030f000440035034a4142c40e501d0a02420a44c4800001103107000400002e000f01e5100c3c1102c40c182c5d0140312840c0c048454200c0f820f030b0200b034880350703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 996522877 1250 996521627 996521641
    0x309010f062c060a060f020304030c061d0103141906090906020a08090d0e090601110718060506040503101d010c030b0a2c10090509030702150f3906 65
    0x620b086880c48003414522903481c1010002d541c000451040c4c1052100481104e0300326031081c02102c003d5034001000700d00c09507070360b08000d044c651002d5000104000041039036225611a014000c050a5500c2243e4001e031a10001c1d41201e500010703500c403c5503690320001600b00007078081d50801d1400b41c2d10041e116550018090905040107001046a4220f2603002d0701580d0840c0010140c2035050303490820641d201c40050700d1403d030003007070f000040c454400c00041100380c001001c094040d5681c0d040c40010b6580c0188021400749018541d41600024010b80b41500c440d44207000450905500c20034400e0340f120342c1400c5503d0500a1070009880760f1030718005d801c1821549000b4030700212000d12441c0042316a56544c40b6109810111168002c041100303c0c00244540002e000c600720104064140b5072304555480e40414812401011a0342408016410360f00584802011071101d01d07107000e8414030341d1950351000183d1b1000808d2041c202101e086014058808007901d240d005140509006d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 996524127 1250 996522877 996522929
    0x1103011401140d0f020c03030a15120c09050403030219090302010305150d150209100503010302091b0301120201090e01060804020906030d020a1115070506040c050a15050309010f06 79
    0x96a15814005104030070b04480d000d00c0c0407600c0210200000040d240c030300c00c00b0400684210b4203018260b100200500040d000642e201c450b41c150106000d400c8656036480304428001d80341d4000c3d24501d502c1d0b00c1003018040a40050758498424503005240c4040094110899219000b6040001d510040e040c411560944a5180c01207a41001214201460310000e49103014010300180405001e450648038800d150301500c4030a44000c020261010b0003640042c00760b0030074030003a486001c040000c240400c00340065101084809140c143c550307070070000042000e100d9003000b00d040004103000041c0a030840151680038000607500e04806082500400450305405800984203400501ca0008541d40024031100519445245490001070702000140003011041341007840081c000b448030100900440d045128610403000d840300c0c6030b100c90034800c1d480003d0080e481e0304032006060035032190080c009140d02c000c0c0d000c008500c880c8041c2142c41924100d40c8000110001500c010321220440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 996525377 1250 996524127 996524159
    0x606050301090e030f160c0e09011a0603040201081305070e07032f030a0b0409080f13090e0a0b2a0903010f0b0a090b01020708061e090316110607020301110301 70
    0x202c0300445c1010101102e08400741300c0c0b0030710940c0c81540f016082c0100114810510010031944a0031040351071b00d0402c0d24041c0980140c08501244640c803c0402c9242610949000f0350f010394034400240e81d804e4180c01482400d0005840c0d40c03048040000722540c0302c3d40d0f554800c07482c0b42d03000719180d0b140c17942260504404050404480308202d0306044107180e81e81c1984e0784500c90000100d42c021000e4080741c02802045000780a12034009030422820384148000c04141c0c00000c5905840c96035055100c0444443c00c15034040c5070041c2d2041e1010030001d11659801124141445201504242d5218a40400c0da180600d90100c00302e00107865140a1260b007050000e0b40034180302d46422540004c0704044d90340501070641d941e488076408c06901c00c02606000e0541030007142c82c40c1c204801074960070034404a040842c40c200c07c1c00190746c0720b030120034ad550384d01c03000c050600100030310b83d20300401d03403800b00e9900d801000a101040159400f40120140102e501c0d1081355203504010000c2e402a05e4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 996526627 1250 996525377 996525401
    0x501060510052704090b090105070e03070608010303080a0612030e0a090b06030a0c0e151201090207020d26070b0a06061119020a0b07120e120705010c050709060605030109 75
    0x2d001032012410082c6000c03c4000c09101c02500401c64200001c000381018600a80500400307070400000e408158440c4c1d020b01c1c000e8031801c880f44200402c140d0b030741c900b03801104006080040100006802050540e8010242c00000b05a00e603d460f185440b400342c0714070540c00200c40e03030100c503050b040034840031000d058000c500740081b03903030350000c55024840034007003d038100d58a800c0301207218423402440700000c10040401e010035008030b1004110781c020110501c515800e4000020b4900014422152165406803c510812142c1c3d2150022102c8220304020a107800070380784541c100c1400c00500c500380c4a40f80c940c40500301550000d04440390740d0400000d1015409207a0141140041c143d40c1000003450005954039592010072004507003688001c2d0303441408039520701004085041101041c0b00c0c0e03500e180e40f640c000020840c0c00c4c0c101c40c0c0c07508080d400014090006511600400781402c0c022421210100e5484072018121907040e800400000c202000601c0034454a01407c400410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 996527877 1250 996526627 996526637
    0x6171612111c12020f0a0209060301140f01140301180f0507080f01020a030501080606030604140f010f0c031b0503180c06070614070207030308070518040c05041503090c0504270501060510 82
    0x2880081c960b0742007851b0019204041c000300090b195942500201040c5142481305405414a040f566405c0d00d03003070140300d80e2580f01c880403503954181441420500c0228041a80c04c00302c45440381000e21441407002d40c2c885c000c898000c10050000c0200ba10100c60304000141e840c405008014211001a004401d07903420072800c0c4401540c00181c516040b42d089503292014102c042100c80ca4010070b00e800b80c0c9103500304144000402e03d41d600241403a003958500f40440c1351a014200383c00c503411642c500c041981400841c1211064a611610f00d0740b81804440d4030203180f2001510326040028121215a141c40040f09800400007109400100b1030004021140c103680d8040c1c4480c00081c07000080001c0841d004007121200500801c001c00094000c0060a025040003005d81e401030055410380141c81040c0716115120780718141c1807541000c81c03c90142d00300320400024003c8508509580396000044030500c0244085c0282814420b4000096061400b4280300750600c01c00b0000301401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 996529127 1250 996527877 996527893
    0x2030a170402280f0e0403030f050f070509010302070c0308030103062a030b0103060e0906090d0903110f041e02070303050f04080a140d0c0306171612111c1202 70
    0x41c0350f404010031401103490798410405801c460707254200320b280d4002c00741d040d00d809000807940300354100540214041e64080c011840d403958520103880059490103664103401c1d00166100b0b20481c06450308603070501d005850a0a1a211034074141c204d81c106a0782c101000004004000f0b01e88200d51003004a050f0210b00542421271001e01552000707840781c203140d154803c4801030b80c0309500031005040d040002c54941c0c100042100e680f03490885180c2c10307038400e50740c0b4900351a0240392614101d0b0740c040c002c5030310862480c0900659640c000000c2d600143c0720b09001480420707003507a100d040da130920001a110750907810020295203014002c482010921800d01020521020440740e00005504100030381003100c00101c04a440741039065901c0c03c0ca050008000c07143c1c16008001164140d129000d10305c441d20a4860f210703c0c440e152441b41283d9101d0411800e018100c450300c3d00d500509040c0068000d00b40401c014107030302e9040b0f00ca140c90110200d41040b5103074030340340850301d002d100800d480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 996530377 1250 996529127 996529129
    0x10c0801080d05030405030d0603050309030c01030e03040323191b1d040212030f1e030f011e0f06030605031e060c0d0b0a170f0328120c02030a170402 66
    0x7407104003401200f00301e0000001418444204121000c1c080c3c000c1003000515035904200341c0fa0382205013a2440b034014050b05031075661180c0604100908404090742c607051445d69078020180314484c04200501002401d401c283e4024458011078000082202c07144506074070f403020300c1d2514090403001031481d404060112015201c0a81d1030074000d03c3d0710012544a80c000204041c110000c048101d1000280e058804c102c03c001070111050300303195050304078501300e509031441e0004540d803100c41091a001089800940c001d482e460030b0410300c070400b40c543c58036035444020036140c010402280d00c84008002c1406d00b0060000c122440d400410f680c5818040603640390203002c1d00c00b8000c040302150500149406521410b0704032001410a91501c0d070310414040202405104240a805540801301078510080101c440c0c0c58040039413010341910010841e81e0100443c1011400c0000403c41d0786240d0980e40b00d0038030002ca45400668aa5202960080440030f0914110031401044000e02c001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 996531627 1250 996530377 996530383
    0x303010308070305090d0606150503090307021c080301091a010e13020a18030b090106050d1a36011505010c1e050703030903020f0901121202030d06090e010c080108 72
    0x1500d0788580720076a11001420304803102d0081210b480e0307000038018140001c110203588130004481a400413040668000307c0287c7d4140011541c181e03032a0010002c400052400c1424840c40c030080018003580000c40e52601ea103c2e401c243c0003024465500e00c03d0f5540019000c150b503684040c01d107440c2a582a500001c42c2c22604030118011840d500450313a080481d0080141440b01c031506200c181e4030543e40e003000f451070038058924280651030010081340a0030150300c4460015080419880c1e071448003042c000f1181c0b0010102c0180503181c030000480655408001ca02206005a0f500c10065011104070308441e00741540712488000b14104101d5071360020052841f043d040b190170380c440382944e0801c95042200740d40007001400341c0c0d013010040640290000301524000c0d5010200342c055241031042801c400c3c000c186d8110030a00d11311000840054003050340c001907105490904501a5214003555800d42004040b203403500c9060307202d0102445441d843d12441d1800103040e51618201a413 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 996532877 1250 996531627 996531629
    0x1a0c120f030420010c12030b060a09090608032802010212040809030607211d0a05060708011e0902210a06080f01050c09120f1f1409030a030b2805010f030e030301 71
    0xb01140e86c2c5065090541e000b41c0c4442c83e6008042c00301941d40c404d080c2c2c001d110b2111030040ca0350b1a46021300100707000000000340c0f280e490001c0c1a90392640c44000074000c41c3c4400c00165421507408200d464040c0c0045588a4010341c481c110468690045208041c20300c480240620b04210f40011a01c2884800010448580b01110800a04440c0c14041003c082242180d6510f952180162941c104140090f209100d90b400d80d541d807034180d8940340c030400e0905040d000b240c45410110800d011140090b8010301791245501007001c0d0081a405041703402082c1290340d5082c05a6030441001a00c2d0188041c50030181050002c0245140003a0812100e005841d0310324011b40f020182c015a0150820850402100074800c446882c05a9882101001111986602d400e41800c128070311a82c004003900d03004208400c00b440c140848403200701c000703207512a020340d80114040c03840c22010303550703076183d030f2400c0301c00305000320264107280002d80744d62040400750041500e00700056201d5100070056034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 996534127 1250 996532877 996532883
    0x20a03201e06090d02181e01030201020a0b190e07060914061806040902040e01050a090b0a0b160c0f05030d0804050a0321020a02010b04151a0c120f030420010c 70
    0x164403010f000010070020a01140e000f034210480154075841c807601c41028610420111040404008005240c501242c00a2000901503030081c0d84c07080006984030b0380d0a034005080060700c0303024030307002000805503007001c1800b8400350480b08040c80301d564400d400340050074554503040f0203540c0b2800841c0391446844440032062840f4074050089070746140841d80200360032002552036a03281c1d13076030b00e003045001e20585200e00150000002d0300922406501c200c0724009006110742441d241081c4456400100503000285e081c168100c005502d56510102510001a1b641320703680c108000c0c07602c1c100129040c03900f440302c10020400015000521410b02e1039040c90415803006590444110713010384140c90180c0d0b40c0c00401c1210036564154042e40b00403030111000c1c019030854940c0702000907000e0145110110703001204080e40d6820800802004d042c4e00300b1100004682944a48240c01065421815400000500007404060a4050071001c8032502c02c03c8036108001c0060410f0008500003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 996535377 1250 996534127 996534139
    0x50103021c09020d080307030204050301050f0108100b010e0d0c050f01050705120c100f050405100e2d0319080f1e07030e0610080708060115140403020a03201e 70
    0xa4401c41d03e400c184030340c421707500c680c0301c039102d01300050054085d400a0088030300961925000606110544031114100c40f1000094642c84010032514000742142440d014180b0222001e91055074403170307100104a040c003540340505201d0809041100070443c51a8250400c0401d0141c80003017040422240094003000d02c141e81d9075070b15400c491342403440a802079803015280100c680e040482d41d03080030344a288501c0035506117002c00b17940070084038016011103800c3e502036041a4001107040a40030306568500070806008502004040c0c6180d004040d80040440281d02c0040e00b90f4012180603005689001414500d1801407001d40541c036190752141c0b9001c035114046000b19002768851000607203620244e824610380040c2036110190540700703000c241d1003064000600700c100851154166640246c0c80018101c45000c22140022950201350080100b00400070050350340c00b124000851140b90001026aa12914074042a005000b6180a2902d26004d105002007030400c00c88584411030b40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 996536627 1250 996535377 996535391
    0x907050931030305070f0203041511010507022503121b02042903070806070804141920010f031d071d0105030706020d0c03141303020a050103021c 64
    0x1200d0010001c00607452109510300440d002140040d018065050b0007500d084c001c1e502e907503004580d80542c4e0307880900140c10904c014000c40e09001c5042c2d8010010780f40101002d401c1c0032005003141e2007500c41102590001110702424800508400c1c503101c000400e00481500e141c8880300c07181c021034016400c008070807021071001581c014a4505094029000300050308000406000800c000c03040c0c0445c5a0400d034085140b444d00048103400d90320b1042c040d2540b070311001070540b503015004c3c108070ba0401140500e90402d40041105e040d8803514050406655925070a01c0800143da4060708510820b00b80d13000c08050740c0012040900e008107280004030580310030710114a0240d141103e4501c0d008000d40090380500001829a005000c02c1440003141d81c2c03a010103035a17a003035201d00b6000d0b80003013440c1103035070b070160300c0081c00c06002e4141901038505040f0503d1a039844040420b46001350b849090081d800c081300c040300941420b09045241c02005000d00100402c41a0003043c800d80700c4107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 996537877 1250 996536627 996536641
    0x110f24190506040227010305130f0b040f02101d0d0506130618060603020a0f05030709180b041209080706120b1804080c060a270212100e010e0609070509 67
    0x4101e80400c0c0d940e0b030b0800900d0480785c0c64485070180000940780080e0401003c540500c5800c90701d080c10680c8408106c40020b0140d440100081c0001c2054403402042d080034000750315000100c0544000300d0ba42c1e01520250110045e400e9042c0c480c14074080c08001e411070b0000b0300001603494100712804900582840c10f0315082000d4000a14a002c01124030300102c020400380390070041c20340b0310031a03002e0b0030307a82ca0300019401ea5829102e150341c10b07400404204103000b019031101a1260080070030004681e010340360101a444140e9080301c80d8410464030b848802d030f00178140d00c041e008072000f410702136141510041001c0c50f4008400183e41e92809c0f240c00c1c40e0346010541d00c00030050b10f2140f91900e0720b13003006282c2d5040050020b10a0241e480041d0b10080c10f440388000c0c8600c81d0340e070264600c0030040c402ca00c0801c0400200e8101280c3c101108078003c04102003901803510039030101e840da201003203031420b40b025801804150f0744110240171700c2c00c0c07011482d50184d4009030b403910440d2396840 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 996539127 1250 996537877 996537881
    0x3080708090703021509090606120705031b03150f2e0c1a091c020601030b06060d0f020c0717030409150f030809010311120610110f2419050604 63
    0x9803000317620030410080c00b030748206444058890100100c81c41c040c01d507500014026544a107102003004003000030300041605000e000074580220b215087c210500c258001d504440364000e07101c01d00c2c03580c44000c3c101c0309884c1c5811940d00d0402c0580d0301c0841c0400c0c0c000102c400490885221020744600d0340c41c000840c2c460700035011b40541201d806c0711303040c44003c50a190f15506540c3c900d03050260880070f00030a0440300c0009800700319940200026840c60710b40b01c141c1c1e00c001e04607039480b0500700800d028010a0303019081c134001b41e0f41c000582d20404000c0c1c1514006565001c090034a13401c6e9445420302c2c60120a42e41203403e0fa00c008901e0019807180b1021109980c2c001c0d460000c0081404014811030320043c0034891341c2a02c0421018040310383c4c0381004e0141e01381a402c0e2405890001d40d103410a40c07201910340940d424403c080c510311441850920141d48200b0301c05d40d2081041100d0041c0303903600341400313541551068038070307092504030909480460040c1780d1840f03403520081041a183c503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 996540377 1250 996539127 996539129
    0x90218040509240702070806040b0c0318030304053007020d02180405240115030c03020c150a0b09090a03030c0e27070809030a0c0501020d0e030304051504030807080907 74
    0x40f00764031600601882100c070030140f09588242c01407064510204984100240d59400745401941c0400f00c1e5a88484842d9035500003480d80e054442c1c1800b515070000707002c1000e140601d12510250052151035502c08200c000c904000700d00f582c035207480914500c3d4040341192803c580581d01da100002440c00419402c02c903a151112210f039070701e402c10007401404140aa083c0302c04d0707006a0b0010102d004c500005c2102802901e50b0360025604810140d4001d1388080c1342c00f00b00d0f040241c18816500a01410202c10340041405038108000304101004075211303644070f0840c100d0741481d090070080802c41e941c0c010300700e0040500d980c80c45403c1c41c5a006454102e00c804000301000401c03540800d40d6502810840d080e2a500a0300d000031484503401420401e100d070190000030b40c00d100e40f000b0b0441d0304001c006026125954200610384589000340503185603103500700011580c9003480c1c50001e01d040114503514050031004000d01000a61040074039411604500c1c0812054540c040c54500700901 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 996541627 1250 996540377 996540403
    0x902070611040b0301080c0f09010618031e0c05061e1303020a0320180a020f09040501091b0e0d080a05160b0106090f0b030a020307020f01091a01090218040509 70
    0x101242c0051080d20030001075050300c202d074060703620399040541070050100096191a620624070030060181a101340e1091428000d0b031a040b07003409507241c4030121401c00d841c1d40c4550003610301080800f8040e001c4c01d40d0b0010001078468030303d8824007213200c4003020784030340001f00703040300004020751022100c2d00360801550f002005c1d408102d903245024140418080300402d1030713140400c5011954608404000c00150070021100f0a5956604a180081d80200d21101036403400b8090308440740c4652090b540689060709000441043c0c400200c1d404903007100c500000c12080c440250527545030300304030600302c55118403140d0b11200c0a007815152030288516110110210309604801d00160080b0079040314003a86821144640310304070304100700c04a0081442446007003001c101514443c1d40210360184e500d01c10b0768200c164104615082d01c6032084c090310350040d8514442d4000ca050f00407030b03004040082e000c502c0d00d681c000148404035078404a16200d0703550340b0002070308400e091000b01464a1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 996542877 1250 996541627 996541661
    0x60f0f030f0a0e010b030a1b0e09070306150f060c0c0305101d070501020330070914040c020a02120c1801030b0a05070c06091b0315051f09020706 64
    0x16054a00307014111003140e00391511810980c01215a410602c11800100400f401806812117a5120b006216451054004c0d516455800010780716024031011405090349801400f0510b1942c00c104054509000d10304202042d00d0b401044080c8000c0b4104085881c81d00b0302d101e00ca001c5007009518403226510140540c040c0081c107008400c2d850b40078030811150f2180e80960350325451030641e52508a030040384d015034020000c003500b180b21a43c2d0b08103403c0c2e00701d01c50400c13103801600d41c110164080da20701d00481c080301c0080c0a03c0032000040350515906031410410144503400003590b4080810020303005503500f1541161542c003d11541c800000003409400020040c6240d017400ca00d001d01c400d84040c007642d0085070760b000c40d81c0642070041c0070941e102d40d14035500c5d40f101c0008045d0b50000b11050b80d04403042604004010088500450158101e110315104105481003a114000c1102d44184500d54860380350000f010b610205031000c0150058481442d440c0c0b0500802010021143c410303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 996544127 1250 996542877 996542881
    0xc0f0317151003020a020304030212030d02070516080a08071203200d05060901030b01051e18061810231c030f0c0209040201050c01020706050f100f0b0405060f0f03 72
    0x2400c1656055044005581500e10b4840c14081241240600c0101c00011380007000b0400152a0205541d2400d16142090743d2600d40c4064038a0b00726406290f00f21b83d2600200c800d01405d9000d241180c005042c0d240c0030301404192580c40881a101c0c6c14802044c40d2040c0ca4000003181c8a5401612101c180039003810b444c0e01c1c81101065960000804c05424608100000740d0a0501c2d0307c030f00c0e048030b41c0001411901e908100070843c0f62000901d6601c90036045e04a0b2014507031b43c00e0502c04140e5000c03140c4800900f082c00c1441031745440211000303481ca041106202d19001011510301c2180d4961100c1100f4080c1c40740900e08040c0c00140e900c1c0e1040340d664180c5952803c840d602c014081c42034540c03000848440d10306881d00e0441c8079001e54480a0300000502650044000b000345c0d11510300010725103d0244c0e5a80202d45082d0741504055aa130700030070452a00b1041c403030f40541140100c4124040c50b280003c2c03054803480c019a40181404110340040783c42080a45201d4000240c081d9142c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 996545377 1250 996544127 996544141
    0x181201140c040510050c06070c020d1506030212030304170a02010e0f0708061602030409051012050a1218120c12060c0201180201050327100209090a0c0c0f0317 70
    0xc2d002402030a21881c0c940303c00798800c60050f801c58104465081c041c0c0482d655005c42640d030f01401e10400c0e41c000ca1a820b120f00000c560000c04504a0210f0000256450031401880312901901c0d1045030203510800074007003c982008400c4c4160b0385214800d980c1c9040820040780581a03000f0410b03a0b510620300341074123510f00410103c040d200a90221000383c2e8a0b00199003140d0148080c94000d0b070410001400b00d400300c2d400c025807010030859500c48856071000d00250000380c48405948541010b40040104a00002c2010031962549000090540c180121080a00240c80b8071a20250418850300400a5440d0860020041ca402e864500c0c603c03414400050105c80380307100015440d004010240907520080b17074082540607900c0a086031340d1083c103030010654100c83c0301d480a000e40760349440c06400300104402d51011000260320b4412190030b102c107080c0060044070040d81459050f2107030940c800a040e00140d00083d176100a025141801d1380c8403500000324440c100c1c2c5032420401c2c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 996546627 1250 996545377 996545401
    0xb060a02100f1d0a06050732130605120601021212091002030414070b190302030603280620030705030705070c060905030f0a03124a0318120114 63
    0x10982c0a56018840b5a503107681c03c580103034030b820300300902c0d01c1507148c01552503554040400f01071401c071207174a10700274810401e051059110b52004000800000711207910f1250a860580c00050a00013000789003e6495421244e014003d2404c9031201084000342d90f5480030840d54103214440b00c802c55aa0030b043c1007201015003004811002489202d1000845440360b01c100c40040504441c00300e42c0b240d12040c01c4010758405080c05038507120f4140c1200740002c1030b81c0c1010140c0b00300e920046c1d0703030302907460407a064030488414408500b91311581030016a0f4100d0480742c0c402c0c01071030300c0c130b0741c942c1e901e5130954807800341c080064180c8002410108072103400003001410b850081342142d0014035040403407644c8148040c00200041d96a090810450100d41c211403029000f032031b0842d1072045846050703080300e8103036019042504101d00d4270814500440790000071074500e5001462401d001150103410440b00c00c020140901e03000d841ea011030410a50182d85040c00340340c400000b60030103029400ca = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 996547877 1250 996546627 996546643
    0x1c030608070602060c030a05060f100519080c0405010302250b060411090a05121e0c010f0f0219020f040f050a0b010924020f07180b060a02100f1d 64
    0x9801d100d0460085106400040c6242c4a00c2c20020003a14565078a141200540b03005032803980c000c402d00102c03505a584045800d03d0710031159442e0780c0c6030854081040741082c040104c06041c4242401401022801c05046805840003801d0160342d41001c103600d807270100c590340940200ba040d0301c840c031410804d00344030440c02000c0440b0144030f03d5188074000700281c480c900000d603010303555100070000d50074840074582860b60f0700070a17141000145641d0bc0411005071404d1000c0d60005440444190703089803540d88802c0300340c42e1050340c01c9610000a035950902214010f43c0c0342101040a04541d81e804460402c200043d200f4000405d2881044024202c15a250705640f42031540c130f03a9083d445001c0d6607040b00d103040102c0840b1420810201d55600314001c0550031030146181264840004000200060003c0703024080c0741c001145161003110034010f4400d1090a040183c0d010b900d50019507214182c4c001c010016606c081c15203d00d00401120306100340440305050000102d00012800720 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 996549127 1250 996547877 996547889
    0xd0807080c190209150d06090203030f0a050405031905060a02091519031103060d0201030e0a0602071202101118030f06070201090b101208160f0b0612150a0e1c0306 72
    0x140c5c483c0882d80d12a81031007505e050b08440028100d0010440c20740250451078000b40c00d8910303103c603c01c40300d4110f500c40034496000c108000350420090a082102141c0201d0f40425841d901c00c8640d03030035840b07200190005a0742c0d50049031800d225038940e80c02a540b42203622800c0d0303413105c01012400c4410941c241c5100442c1c41c00d00ca5507665102e0a04a82c440c4000428511060a1550040d001407416038a0181e0f079124140350140060b595200400103d0f003e19036101c0885218031000340707082d400014203034829082984011001c450707401613842c3d588044903904880c20746540460726210304001103034a54441c171414003070050b80660110030154091002c20480b0790351300c02021034245d200d218100c580010126090003103481d8001a1600b81844060903c1c032880e00d4503000741c40c100d4000e06440c1520707400103010302413500c4c1440340242445580a020581d0082e0000000020002c202420081d250311040c03103030680a200c1e00c0300c0c80c031140351110008824000e004000b0300c031600602c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 996550377 1250 996549127 996549139
    0x80c07140d17060a05010210330510050c0304060309030e1305011503060b0406080601050717090103050601020a05070302060f07060f0b010314010e13060204050d0b0604050112020d0807080c1902 85
    0x400d2443c02c040d400c04c0e0581d80182c000306010082071a0f00c0004011000e0700d110100045400004290034110221040041801400d8000e07400e002c2000502c4840004032000c0c0041005442003811021040d501101d90078200011031a141d4181907820b010500f042c56440955450344103800da0482e032046068a407144004400404a58000d400b110118041c0e41e4011f0010702080210030310403c840c6505c0107040c9005810309803543e852130b00c007800d211801e600f0b0f0360010030035810559240c8601a4000d1091004140340270094980c1c0f600e41d03045000c00b900410000031000c00001111080b0ba403050b07804103040140f880c1c03c800240090180b03512442c00a410248150055044000c4140c1600c00144c0020540e03140d503070b178603c0000b00104c42114103503001d010005403a555150b9840659005400d204a90700d00b4404103c201c0d0301c141c018000c10481e0096090241c0c880c0f003440207440d0350045246a0350046400d1041040c005d110540e03156124100300708400d2000c0704c8403100c200b4401d03204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 996551627 1250 996550377 996550381
    0x60c020604060c0906020307061d0a05060f060103050112060f110d1509140c0c1507020102130905070905060c011b05120c090d2004060f080c060a080c07140d17 70
    0x10448513103800d841030a0040e4420705c001000300f81b46070300c0710055050300d98046103941055141e040c01c20805610556490f00240100150800d041d945940d02034070919003000550b040c00007500c803a0038913072030190000707940d06001080c08915a1011078070701c0003045590340345c3c00d0700038440d030180c140480c58104a0900c07030b20000c1c1400041c0a0100c0044141d2480c0140c0c0c0c0d41c500d103880303041e0042c00310008c1078400c4961295024071142102409241030b58000350f0344001940c0d405000710001d601c40010180340100700301d0030700d901004103c1076a00498101e90754000c81c0320842d000d86250b241d250540444400101d091641080040803881060080415070799190ba1b000c40e8030b0b0003455129500036103602d010034001804120b517000c0906040d41c48030b07036040d04c0c40042000c07550320381c2021141d400024014481d21404002082103407200302c8103646442d070000c400628180001e40416050000400c2010400111600702800c0e20341100c1280c052041c0d030170300180b0314a202046460302d1408500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 996552877 1250 996551627 996551651
    0x20306181c05040924080c0a2301140d090c210302100b040b040e03040312020328030e0105010b03060103111303030c080409090b0402091f0303180812040e0c04061b0f060c02060406 79
    0x509c281981010000702d000785031004010b4031080715082c9500101141042401101d003541c0c410000c40c18082e002c0701e0019801c0260500020800c1248040d004000c500c01c400002d50026070416101d100040c040352a900c184003050140854541490b03116042280d5040704003c004058003c4a00400010342034030b00c101c0007039031a0320440103651020f40e807420100740c01d5a0344400242c0036088610740042c10103441660740b03085800030381004155901c00424442c8a6900d0b0003a008490605807510f17180001040d0b20003008159031200400340000c1040a1040c1306503202a107005048a56084c0040c48003894241e40340b07101124100e104101c000041203103900048000ca003007200b15040e00e480281141c40030355038101031350014400c1c01c0402c400441e00940070b000d014240e040d00d0342c0302034940d4103140c00a000544018188039000c0d00a0104214042e400090040070511100e03aa00c500c078041e081ca0740911445540240010303040610b282c080c40d90000d4550320440c0103850400c01640445 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 996554127 1250 996552877 996552899
    0xa0620030c030105010318080732061503070305121e0306060706110c0706080907080309090103110d061107060c09120809030a020306181c05040924080c0a 68
    0x240c1d421030809401c1c0014001540294400c0168441c2907429520400c095503e0550550081c041152083d03644034501c0040390000e10548142116030303515070411000c403906580d50b03103030061002d80000d800c4440090941c8041c004000699008802d8070b0140c8052500e44190b540002e100306a05580d44042d08072800701041503071b0041074000c0c0711911f444d0b272613100c9402a02c000700210031079002c2080112400101000420020503c58580a40070f2501000c01820f128640d8441b000a4004019242107076880c01e48282c156a07100d42c0c65541d6484640114200e07201c80b1000400d0a850481c06601c0b150903900a404034501c203020030301150386034030302c1150300400603c166454140e6403206680082c100c50060107102801808071342c444d1a070740d00004c0c6820820780d1402c20b00205a25200a065414003020308490b40f145106408509500340040c020700c1184108901649d80d41001c111011003c810800750b120301034140003105441e04105900d581c51210309501c118400100003482c1ca00380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 996555377 1250 996554127 996554131
    0x3011e1d1e2a04050402040b100906021c0e01050f07060f050108160e19020c030a05030906010f050a030204050a0b0a30020604030807050f0a0807030806030c092202030a062003 77
    0x1082c1d40039030482850140b01c040d1201410032a405600e4081854051712512100707821102c2e20754900200307625014019040c5503e00310503c043c002c144c082c4034095900074800c103000c0c200c286405e070f9807004590701481040c0640c4000925080c21300903071440244041c1c000074142c0b011042606c3ca0750300005280d22a5081a22031036600210368000582035503190700c0e01558090410a01510f40a81f1100860940c0c0c080703035207070000c0350000c024047c15610400889001d040b2005010364424108400918141624030000b40b045442d13900060619070541c04c800716480d0083e0807a00d440d603c88172549210018450070345400c100c0004425540c00e55072501c070000c584c000d8041490942035417a051010b43c809001035445202c0c40000c407d052900b04540b9100340d004001054440d00c047c50000c11003403010b850640b00f0740c0719622101c1c0d281d07103c181e4140c01c04480c601e1502281d502c41c0482c0301c5202c1c030740f50203075060207501141424081560000c440c05c0b0034000424031078820344c0c08004210300003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 996556627 1250 996555377 996555433
    0xf0201120e100b01050903060406050711030c0c040c1b11010f02010b0f100306050303040608040c0b0403021c2109031506180c02010207020d0f030e03011e1d1e 70
    0xc20b41c2c1190955003994440c4900c4007040c5002c610b000c04030008030340b070507005031000c5440c141d49104009900703900440098004103100040d40c5002c03042c8101540d100d014001d9144604e5a800271102240c0c040d41a400030f20b0381c4003855240d140c001d41052080e0140461001e800706d02910580305150740f042c0705003210340b2070090802107051202003d01402c3d042d00c1d41e050f0241a6141801328030b03a44c0400140004200682d40e0201c0d924061600c1a850a841d5003d5000c4034005d200520050f614480240d01c0e86091800e91116a005814607260907a01c28250030845400d01220960540d84221040c007528080d245280703c07078105c180d000d01220322500c1100c034140040543c0440d00c5ca03064210b1202e1003070301c0c4005810a221500011029031a0311800c0f92243c0b10310340c018080680010039440c080208400070400c564200804e44000d0801042807180c50f5522000040c2324074524031480d80c1981c84404031003011945001c801c02036441c0164009180c45102040c00300780203462052000104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 996557877 1250 996556627 996556633
    0x915110d0908151801050f0709050105031b0d061737080a05090a0b180d150b13050c12181b120d0e040c03020f040e1905040f0201120e 59
    0x2d6803c0c0c040c01c920020304080c400100380200703401c1030072090281600072400310800d402c2c142080d050150003803c0355803203036045c845e050007000440c810500030b4518401d040d4500540e200e0160104400511454009210003010849132980d240c8001848084c4140b05a12894244090350340b4010f10403504004045010301c0d40341100c0018115070041d00301c0100c80d00340541021441d40004a600e22160414101d492012821035034203541c2c9000203620351800da484421007050303515030400c00d000e100600300c65651a440403c40b20344a0111184c29200104810005410507400360364407a03103d41d002c40304603522180461a0f2101813035002c04140500002008030481200400c5070010000c83c00c02d40c40160071102401e50700c800d0100401034581a80c41d02c4085032502d0800c0b0848095440900c00c06105100c000340f00b6022008860079a1038090101e50b4555842d80391041c8402152034480b141401d01040c402001703180a04007a04034800d8982c0705880d03960403000d100310782440c0c20002c1154 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 996559127 1250 996557877 996557893
    0x30b040204111306020319110606240f0904110c030d0c03090f0515150f060d060b1b0105010e0403021903020c031e0f010605011e0915110d0908 63
    0x86000d510103070b00041481c24640c1040481185081003e805600040160f000090521000c0740d4103001c1078280340303e9003001c5501240c1f40074030f5903841c80003d141e02d004140d40d45404480b82d40d03090398844064454044541c1d900e0000000d403d4a0304410401d90155050811085500422100b034401050b00b070380042d41459600403000340602000705604041c5a62041c08101196030300350a2044a806200100740040b0b44100250780344070010000312103e11580f44c8001c2a0f81c4c0c608070712031180c40864a40d5110400ca000c0440180b0142d48410003d4100251400350700003141d120070346450700c1100810040c3c0c1e03644138049074104100c90040c0141c001c0d0110000381d0191001c0408050300a2048920050040c000700b07281c60300d0030701086100c198612036101c103400100030903038030b03840d40d18002d100715450000081c005081c2c00c1040468080c070742c01c8401300c440c8912844401400020002c03003102880701c502500c00c10348140b1841c1980201195000a54082c1528030120303078040d03000709012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 996560377 1250 996559127 996559129
    0x30b0a0504060219170a0c12050405010216031706040c0e09090106030206030a0b09060d1212020c1002030105012618160f2d0504020c03131e080106030b0402 69
    0x401009000311880340d401d001490140384c0413851a28440880e44641c0b030601c0581d25821075542d40101070302206130600c2d14424481c0d03444820a80301031081400071030103894901e40180a80141c1d0f4405035003c004501100605610800e004000c80c6600c88946468031040b042c401076407219814003001c2032500200710810704006001552200000d0000a0071588070b90000d20640d00986000a0503625409d80040e685019050740b0340140e003c5800d108550b886a5902c8591242c3c854414140151103800045101150701240d000984c403205075208001c034222002c001390420301500340010742e0030700a120414010182c10740b60400c161356034a140c1e40c814249245060030140b03c10424012154000c200300b4004600700d018010402240c0d840074109007a040050980c0d00d07003000c800a070034184112800071900140143c88041e1409655003074030241d19031841c071031075030312140030b07078035800b0025010f0381c020504a80c05e00100d40da5440035aa40b0b10207400e0f950140806000c074007410002c1801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 996561627 1250 996560377 996560381
    0x714160e16140c0f15060301060501110c041d06071d010e1f050f0f09010206241908060f1501030c020303060d020a0f0803120a05041e021311041e030b0a 67
    0x84035001c3d4045841c0302008904203030501500780d12604483c4100014014146028010f9030b02601c021710304030758102202c40020365201c1c0700c501800e0045075503160a20070f000000400340218212041250741506181e81c0c01480901c0c00800d05180ca00c501c1d020f03100644c03042c4803c0f03103400300c0144500c07a03c08c0c0d500b02001501d01940c00800030720008002c10b001c0fa0311302e0400f401c01a04c4415003180c80b05405400a800c0c0100109220850388a00c2e00301008082d0880c89541060826110061014058264010703094603642107000d00c1d02c142c8003040000c1d04260f04040c40340424145c0d00c01d846045d600150180c505680e44c2c1c0340940c1092000408600b4a5401600c2e03d5000a0005c40d442d03513228100000c8200c05d400c010031a400c006020030102800c0d050310342d0410741c00d0804000f035240684130f03e154503903010703c03400003c40d480d11140c0540d981e041800d000d030f0885c048104024202d0f401b04403000d070702500c034882c0400e016080d0002e0a00740c0042e107204072500010581e54640d030340c00714800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 996562877 1250 996561627 996561637
    0x9090807030f030b0a0602100b09010308221d0a0c020d05041e03061e0c0e0d060e0115060c050c09160c03090306091a0a050105060a050714160e1614 65
    0xb04060340c940180c001a501d0b60b03407100007001150080c0c4a04030300124280180c0e80403a2165029404101c010030001d098042103d0713000121034403412500f214206901c22103d21540400c0c0704e9841c0305580141032003903040f02d901800f802d6000300301fa40c107094003d0303880320142d48900300407a0081c082080240c0000c25042c040070040c041603074890381c80c0c1c2e03100d5003200c6c400b604402a5500001a0003031007405480b0f400481001820000c890201e124001042c1145034500141510740f56582140303002c10035040500c9601851400141c010745800004241c441c00e0101650036108602030710b2010304212000d1790040ca480030940f2600501c101e82696a03030b851000460412400310800008621548110950b0300d03c21800d454507a00c0d00d0041102641b00500021041c1d454640100103d0b0b40c1c01088590f20011800c2154580c0c4181c280713505142d011b2f20385900031f40600b980c4900110803190f50001a64444440c1c0b0a440d225026140e542240e20707c41c80c804501c2024281085900d40e0014007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 996564127 1250 996562877 996562907
    0xf070f0503061207051c140109080412050c040603060b031e071403030c03070605060f0316090510030503280c110105070206191206141309050a0f12090909080703 71
    0x203040c4d2030f034071400310b0914510b004010182c04442d584074001c1050240920300c610b1050b000a11400c0c0d01912022410300c00d600c54040f841411448000c05c009003840300000f040c60080040052642d00c4c18101c015140c2001240d20a008034085d0159541d03500c40d08481545c4540010481c1034100101808202000038031a681403005009520941d8000c00050100d54401c540220b01c50601c0401d1298896a1030307201803082c0c100c580780c1120601301c0e0710034904650800d00081504c0d25090820515500140c1015009020000f0600c4014a0911035000d600700c1c003404000080408140031658483c0c0400d0007000b2013180d250800003036110303d01624040340002d14052070520b0344009001c0d040300783e40d8104049803091264113100f80380c500c684070040400c542c1e0780144210305800034459850f40e411015070180c3d140c2c140014044100700c510b60f49940506078101d41070480c1083d040c010401c2482e80c002900d00d174400301d0305941f240244001c2c0c5030310003c81810324041d40e9069032046106035640d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 996565377 1250 996564127 996564133
    0x50a0e01050607081207030225030c030e300c090124170a09030e010f2102040308120f0c090904020d26040302010809030c030912030405180f070f05030612 68
    0x440c810003545c15803d0040800d610010b94035558130705070f20342d6400740e40c0c107421a48045242850100303800091800e822036041c43c085000d80f020800040c01c0004c2108141d09450303500d11445800001c4050b4a40c3d240b01c030702c01329040c40d0200301c200030b08142d0900440301c00d503411131101032440d40e80001c0210415424200310010b10b684615110381c0880c1203c0b480c00c05920f0306041070502d42c000c3d0140c1c141920a290907013080d420854040c20480c00c4079a1505401d142584890940e19547d0655014580c003104541d59080c2c5c1040c2070000c1c0d031042e0313281c10314100c191340403c1410562104641c00d40b000071b40103589543d03030360302040410f205c0c404058400c0d56030100303464041040c01c0c3c46d50b00c8a908000200b03442c0c50440c0001040c01b1002010154176174810050905409030000658132001021119601d02441d203000140c15070280f0350003540c000450b01c6000301c01400b0800d10900c40c0c0350a1040880c1d0b5522404200c1d8002c2c118400c1d000442c1c402c03c04038005003050012080f03201481021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 996566627 1250 996565377 996565387
    0xf02010f1b0f060b030a0c2912013f1103100219090e0c070c03201c030806010e0319051b01020706080c032e0807050a0e0105060708 58
    0x241d0310034110401011076080c51001200c10412000b48544146500141e00501c0306400e03c1d0f135408802030860040400b031101c1190502a9845a800340b000740362002c7c10388a46441601c0482c0c0184c1e6400e010ba4083c1e40c0940029550390701082c102c1c00741d00c01409156150018242811800d8100a0704082d100e0700070003076078151075131410401207103000480c2d00d0050b0358021701014958000e1a44004a007000030754034042000a074010303101500504109440d40d80c0d03504618244030202d800d83c0c4001c0c000e0140c0310108241c4640e1408010003d00d095803404207141d480c07111590700c4801daa100030041280762011801035440340745a046680005001c0b02d0703609890042c600c500d00c85040702121079034041c2d0f00008200450410030881d60000b8001407031628103141c0c0162403454000c00704090038001000080d0b4031600c02030075009400007911034200311705100c1b04010b180310950051484a100380c1c0000030b9242002079038003044503e15032084480707900b04420818541d0250100340c2e01d000f400d000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 996567877 1250 996566627 996566657
    0xf0705160602010609060302030c0906030109050607030506100c08120a0209030f0a020a050a0b03070c050a0c26190f02030111040b070b070924030e24130f02010f 71
    0x204280035005880d004424541c035010000342940c0098200848260520404200603200001c0402d070303600c42113449180d02c0c1e40300d00100780140031641025020707200c0c5600b84160705d07425034442070140c401035500107014144004c0a071500c042c081e0005082c004104a46025000b51807403c54000001450140c9030a05043c0000e160541c00c080e42c40d00d60308401c5032401145081b0301070000030300003911509016840e20000034500d0000422000c240a130f040500c1003084400d20407007001a503c00b00303c0004c949ca0303002c0b140d41c844680c0301001b00281c1c1030840080d8403500040031a40c0f02101d030f01501000c0015500e8444100c40150104c0e010742d2a00005294072440c3c1002d0b00242120b4121681c40e1195414084550803000c0e0001041c4a1214000c0c40030b51011289604400c901d00fa00302e0346040070104c101c2c001d010075001403c0c00e0290003401c40e6282420a00803c2200c01250301403225140e50304107601d00c0c00224001020f00c01407804510055000d1080c20300349054508110200d484101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 996569127 1250 996567877 996567883
    0x30a0510080d0302090a0906030c05061c020708030f150913020111010c030b031002030601021b0d0f080901030f0605030706141201180f0b0f1207030602070605062110020f0705 77
    0x2c2c403001080d00400c000300e05003450242c52008000c00001441070382e143da11228000001401958083d11000425902c0d075921412059072078040c4103001c40d45c0e8420f40c10190030903082a103518026141c61004100405000f1a03018000003009000c500145c66041c1920640d030348100049040c013101030b100c45680c503c04e2107100310103015600c012800003c2d10040506040d19200403101c5544103000b8000266400540c252034407001169000c028490380001644948540000400e00c1e40200700440c2001000d03406803010000c01c0e20203101c12110000854161241c5008035500f65000791420094236100301542e803039135200080d04c43d01d0030008050020005c0001d812580800c0e01e40c03070640076240c44d141300d00000391214040030058a600c031400107503000c0075003c3c1648100b16100390018a401c050100e0070086030312000455903100726240075005000102c0c0c14500c554182c181c5051800104000300c00010800005000080c0d0420031240003034000c1c0340c80d086810300070b001c8207000072070030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 996570377 1250 996569127 996569143
    0x1020c120d020c0613120609060f0c0e030705150322030507050d080106020a120504090c0804060c03180609170f0309060106031803270b04150206040206030a051008 72
    0xd0054039400d4600080689080c6410308a50f0107201c0070084103c07440300401d5440103440c036816818203503500301e04116010706a0801c0c0a440f90b86028410b515444159119014140d0b8a446402101203e1410141c07190203910031140c125000b507554030595410100115030101168081ca4400c0401e09001c02d03400045c040201c1c041000010301009001e000c0245480d20390041c40c00740c01a40c1040d10094407216001001010003d140d10046040d9010f0300075140507180100701009044800e000c000c000481c00c4d14107441c11480c1040d45d0005902c00e010303803070b54200c804041ca0207100840c0d55900080c1200e050a43e01e0288051f82c2c6512041541c0081680b540c1c0428920380b0303410b00d080041c0c02c260701a400b103010f00d4038185030681089a00600d54146035090304010b80580c6840c1c0740041503001340c04c00c0c1c100c104035070303400030525001c084094000e669004410303400800303003e2016070faa01d00903280030b94001c009000080d0b4407405900015885040e40a0500105030342d0705245203444d5030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 996571627 1250 996570377 996570409
    0x130203041a0c041a070c030b0901020711040510170102041a032409060d110a060c050f030a0c0b04050a051506030c06160b06060c101b0e1e01020c 64
    0x4800900385040600000c0030307000110b4141c240d01d02450304001c03c02ca9903102401001d283e802040b41c5040c080c54502c0040259040702e01c0d81914500100440e0013503000b600c0890300320102c60864103050500e40b0459100c0c0001c541040c03031450070000c298003617034290101e84120b50b40802010401000c0135500c180140b8803400110380302c1c101032001201000c00010781400901078034500004d07a98a114059400c51800d03504042145210b0074504800c1e5081c80001e50000780b280710004002da8400d820940d028001c0059441c1c141c031400655450707214680d201d1000424181003000400d04800304030790070520500454200d80d2590343e44074100440700d54040501c0580004119084c282400b1a8400e80d40423240e0601d070030700f941643d01c0442c03030305a4003038584400f0307a0008540c0c7d100e000c00c540259401c0b20440d04140c07070f111a5000585242d0b503403000c14802030460a4007003030242c41c3c00341c1641c0000b0010402c2d6401c143c00212440385812a4a0443c8039054918210781c0300d038425100f859170 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 996572877 1250 996571627 996571643
    0x6051e0c060720070b030c0d0501172104031b030b190507091d0a0e0a0b0406061a09040f0605040f2003060112180804080c0310020c0c0d0213020304 65
    0x81c06101c090810360755128401102d1102510403440482e000c540501620714050005c0c0d1240c4490710b0501c010700511442145462400001044207902c038098a010384e0022012101d01707a99140044540007001049007044060511040c000a000c039a000c25444502c4880c3d4403c40350380303444140031000309480d140e480e250844003110fa010194051039501226604200079658980050703005640b200700c0740a4128030003403000c035081c0703499500b01c00421507105084514000550400c0c81d4480000e4504842c030070310700794000400c658950001d29803844c00340d6119080c100140288404ac0210b9042d00000d1541c0384400316a994452003185503113981c90760000b40c4c240c0060f00d420000d440c80e400c0826648403e0040103216a8011211006d800041401090481c002064840740d02440300c1c00401005001c01c011400c00000540c15100c0c1504070304030381c5069042c9401108910030044020700b190403a10b00c2c4142030410b680700360030007403024143d4240400c0d0708404038101c3c1c01c251800c8906030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 996574127 1250 996572877 996572881
    0xc0a0e0421030f0c1d130b09090d1e080711011407020a0314090604030813051302120f090d0f020c04090605040b0f0c03130f0b04030e031002040f06051e0c06 69
    0xc0c00352103126252101c41c148840c51140b200400340c205c1c14805000c0707201e1030000c11400b9840d0381a800846608102426810b607609004c2c805940b114010480da400040709151816900c540000c0390440004c0241c07113180f416140d0003021150005c5135410f40100350b490704404a000700c10500c840340300359000e5016154000b200d140081c495071340110b403181c801406101c144010340d0703035600302d401316070380304c10034603075540d4000c901050000d9103501c541d40c0520700692040c20010a41c0083c0300e200c0390444010802d80d2000b2a9140399802a04e80e0205581301c12290501d0a0107203e5600d076080f414011219040281c0d400107060f9200800704482e1750342c551040c0000c204200c510319400c0403030492154800e2034611a40385141c00014001c4c0790301d101800455080c131513410605400c041d04030018000c40e107413500380036180d10380c10000f00c0d00901c0b0301d10010b40305102c203100352401e0341c00c289004c4a507585851001c890030b0b0001ca010b0702d840303e0295070030b8000c1030a080040103513000b040701504180c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 996575377 1250 996574127 996574151
    0x23060f03150a08070f0902120a1503060513020f030a0b040201120605210118080a08100509180712150c02190501240509040303090311030d0504050f0c0a0e042103 71
    0x185006c0e80964280c500511600a00d9009000040c1c1c0c4696040f800180311014074000c94254041d0b03a0015010764500f80c180840200000c0005041d280252441c0e0003250940f0b0a00d0f43d91458100c02903c11a540c0c000700d0b0041d84500c05660150140c054089200c0ba00c4000040b13058003204859401d040505c841074640034801c1c042d086043c060407441d207032a117540d500d528405100300d884000400525400040d0300700c5012444030058600500309484034070b094004c9a4400740d1018000c42e49200703240c0b001940258200c20305180642c0880a24186d0900700d071000003900801c444441540620410842c43c000d03207094040406c2c0c01800045030520068818603094003c1c0c0041c0301c4c001240302020b11460315090225504103a0615000406640500b01154910080249000300e40030004905071462502e401090096000b40b060380c82074900340e03428641d600400000f440d0000d5020a0811006c082000000e5005000d44030207030089070280da0040c0003440341e814040200c1c0d580c1103c0d40c41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 996576627 1250 996575377 996575399
    0x21c1416020601150210020313020307050f060423040905031801081612090c080d08180d080901111b060709032609060f0423060f03150a0807 62
    0x800c030180140d006010030000791551414050340b44506981101d0780800c41c800c012111410030300c10011512814a01004044894400302c103034801d10036200c012480380340641902d8200080184041d20b05441c2c0040c0500301c20300c9450034002d0000350300c054075240d213590060312245031241015658856444c0208030405040c42a9581041a131b00100102c01203408200700c031510090070441d420442c41d40e000409065201401001e407101c050001504000000781307500c525000c1d1b21007904941e1080985004204a04945100c51b80b00c0910b0036862800f42c0c854503000407104001081510443c40c80445590242d04141c045840c40780c00030600c09014009650810000d01d000c0030154170f940c070f80d400e00b00c241201d034841c1c0010707401c141030100d812482280c9130340102410158513008181082d00403600503100341440ca111100d80200da038200c65a1001c0c41200082c0074600704040880d00c4038164000a10302044da41c21801101065901c8160135401000048028042c00c2d00302440c4880c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 996577877 1250 996576627 996576631
    0x2105030a03060f0608042418150f05040206040905040309090230240609180f010510052203061508010b03010903020a020f0a15020706140913050a021c14 67
    0x1003005819428400080d28150011340119080d50b201f40e00008172080c00b80c01004948003000e146040020381100300702100803103c0700d00035068070812034900c02c03038424801d69008650095001c0c1040000344120102e640c48550024044c3c034160710655242c040741c0b0120b90100180c04141410361410f241000b144200102e140d8140701458071681c1003100c0012318074803004542d20741c0c0741d0141103654001d03126070f403d03160320000044c0006180c800c078610b20a406001611016548140c41c0d0001c07071141010501400d0b02e00301e65a0380f074505001107038105c52611051a10302400441d40341c2c0040440d0f2903000d0404444c07540401c41c2c1100d0319107001302d42144c102070303c0c41d0300903410000d4000c003003500400c0b00b182c0c098041d140104c001041100051a03100c254006810410300c0d0004180300b541c2c0001c6000c10ba036041e455503602c1141269101503c0d020340d000346540a43c69018560700305d91140c001c540c1010070948094204068682c1400904000c4032102c1085603465040400007100d400f8115 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 996579127 1250 996577877 996577889
    0x13170709060501050d0c1413051008090d1d060c030333240c07030b060306161b08030903070611130b03040828021507092105030a03060f 60
    0x40302a00e0500003928601a010341c00a400765940030981b00c0c0d900440022120304041c41c3e000ba40c8840b0032203910b00700d804e1400b0b014040e402d41074050307440900aa040500a41d202c5000300382152402d070b002c503440d4004443d54a940703e2450281049034450202600f03030500c11300b01464591901c61800c1002d030341d04070900054107034003000301900c41881800c9414124004d40f00e21091032403000300c8503044092052040139000002415200280c4041a101c040d04d200380d00c9805a0b840d40c4c02003540d200c0095404082c00180d190240c082c05020300ca00c14503d62003121003820b507080c1c07600d816070550022240c0c556075820020350882003201f18402c000c0001050fa0015050958070f04190004500b540030380440d0500000228090084c0704040e251041e01580c80e08451081d06100300c0d1400602407421390141c480d0710780c00080300650310b0003079128070515551124803600e00740604180e45804503109144100160060011600078402084503010644010034014504121214841120b600c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 996580377 1250 996579127 996579131
    0x3020306010f0806151005090402121305071e0509130501151403070e010e040812010b09040b0105180907051b1c020703030507020d0c210209100b031b13170709 70
    0x10304010b544040c11b500c00c41c0352a00d0080d496170807040110b8004d1044041d18a000d9880108106c1d041a80c0000d0000091060081c0d4025075901d0295003040102480c0c80300d41c4e1685a0414419400c1c0405000d9104141d49000c0301c00416540303440f821035500321840e1140402d1a081030080b0740a00404101154040d0300400005207025070107021041d060041082d41d440180201d828082d040041c0c030303041150406040c2095950313010f14241c540c003411440c1d0246040c40070002c90396006100ba40c00186104d040b04400020341c80800c0701c28a001441502031160511000a0104108080881002c07140c4014003420710f10721005c0f00d101e0900648102152b000580030700009600005a0340007607810350700044000501d1900c2c1d601600c0075008042854034411045c451000c3c400e0a0045540c02580e880320a41c036403981a0062203524050011034110400c04036580d8601000840449a0380d041803d04111440c00011820310340c50344010f07007504900d4001c2184140920522004220381745007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 996581627 1250 996580377 996580411
    0x111030406050409180203070602100c1106060f030f0a030305190509030406050304030e13020307201f021b2103160c0f0516030519080708070c03020306010f0806 71
    0x300405a2095015206a1940f05d01c405040c4003001e200010301180c0c014142d4690544a03c0000d41e640041c1240101803420f050300040181c9c01140a1a2416480d2020b00900d035036000c1800078010340b1801e0242c0502c02e900356000799810904c550395a00b4400c1d500494a820301c600302e000c22607006081d05420514100500c4481d2130008201d800b260618280f280d02c2e503403542010343d03440c00e201c1c00c0650040115164a071440d44540e0066200b681c0540f07512a03200b209003010800c09040d049840700c141e1085060b80c00e080846c04032681c800c1881c5901500c2d045240030902003240320000d0559059100743d0f0424400740001d032030248940f440066031412b40c070b0041e8910194452a5481b03905224410310042c0520165245c0c44c1c3d8600e070000103e41140c21400b004803032899843c4400d5442e4002e60240403030b02c40442845032a0181c120609604140d010780307500340c450f030203080c0440d8140d102c14030020060b217083c041a4000d1a080c0c0404403550710b4020058200b1000a10801c5a6034010398 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 996582733 1106 996581627 996581639
    0xf240130111c0503041a0408070602060601020d0203074116050a0308092707020a061d07030b070909090c03020f0105040e0402040c03060e10030201110304 68
    0x2004040c200c0381c2e44012038501c00e4407100070682e40007008100000c5081c0349000300801d40e140c44884c54255070f075815a1800915600800c09604403400f004059a018802c842407000382e400518a005000da854107100c4a4201c07c8010b0800b8807009942003840c03001e000d02100b1800c01c2d2a00403d140c400300b040d0b0b2603581d01c0c8002c00d4112113010104039800c1c50240790b01146c1e880b4007105d0508614408202c280c4071039603800b624402e5030304c05441d144d80c104c4044500580d09074020740740b0507080c0d080c00c0068401040904071000e2841070a2a400c1000040c00c0003201d802180da40313500c1d00d5884d001c40390404907a1180c619075050031041d07420710002d41c01260850b4800c035009688010300380d0044d40d0500451044180303908041c400900076003002d4001c41d1525400d0310300018550341b2603591488005058810b000030819810f070600031960020b03e000f5181c04d08100079800c00380b8280b = true := by decide +kernel

theorem cover : BRFrame.Cov 996402877 996582733 := by
  have h0 := BRFrame.cov_init 996402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 996402877 ≤ n) (h2 : n < 996582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
