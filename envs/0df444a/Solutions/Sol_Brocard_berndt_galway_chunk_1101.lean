-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1101
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:14:34.367715+00:00
-- url     : https://prove2.me/submissions/142e32dd-1328-4c8b-b74a-8028966f70fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 197841726 ≤ n < 198021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 197842976 1250 197841726 197841731
    0x2091602071715040c0305060f0708040212070b210c0703080718081912090f1205121216170105040e2103090f1603030507020112050a090b0c0a170a 65
    0xd030f40403076440310041d000b180a9040860380b68118140300703240410290040c268000f09034208544c65601c03808041e0060360440f01004a100e841f2142d1b4a80b5500360050f904102c80018000c2c02441481080c0c1c0340d029065500000341d41d038404032141c690145d054090040f5021f20001805240b040c0b401d9440361066424042909071104155071400e0b01d0a5442d00800d480509440d040c01601e46035544c1d108590700d082c0612a0410756201075801c070500c1030301c050f5403540010804100091044c50761050380409800d03251004400540301c000c0003903480000090000d5210f03581248540014540d400e080c1440d07040c00e900c0c1205001c010481b0a00342c14241c018006403005000421018481d280011030701c036074980c20100e58180c1481d0b504000341040f0f9001042030564884030b040401c0c21283c050400a4560302c1c02c0c00140c1310041012040920180382000300251030209612840b58103000304005121590b40741c049107801e10401740c809000c50f41d800841800c3c0c00c03400415941c06240010301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 197844226 1250 197842976 197842993
    0xe06030c030a0506180132211926120103120c051507030c0c020109031202030f0a0903030f0504050f2209141005040b180102040506070807020916020717 67
    0x1680c2070400b078012031300401d95201030562210b82032034081d1081c2031f0f40000304c007000d501c40001241d60780c040f0303000c82000e41140069070807d5014003192428603901004803035800b541c0c0c5451621441c4440d01d006410300c02043c0301d10310300621415620b0643c00c01e1001d0401b42d003107458038500c001070b40e00d00c0c81c2081046420140040c0b01840950180304078004480401d060207d8058141c4480440c41801c200107880320902503030b0700c02d040c041200d409c51891841c0e05516041242184501c8094080c9001700044480c24030750322400080c1203134043c4e5036000d9404c8203118104c400f441a40f1881d030b4440f00084400400780f405c1e500148000d141592007040704680c40e070103030040d41c4a88200740e41c0060355402e040c0200034240800308000c1000e04080240c0d2030261743c0e501081c2009403d2a803072a08082c0780c84d1021500b541114040c0c040201010340720f82d03951a000c941640f003108101d000b500e91002240040742c03440388100f21800c454014200c4035041c9940100b015400310000740d01403150010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 197845476 1250 197844226 197844259
    0x617010f05010828020403030c0b0106020105070210051e090a030905010e0a0b0c070e100504050a11120403090308070b0619140d020a0b030702010204230f090604020d0515010e06030c030a0506 84
    0x31b20003148030382c4801c0c17034150b400d003024221050305900c40400d590528040140003680481e030040e240900050021321a03d80121504810411055209041c648101800030b02c84000410280c160b11907030f101305215440754011116074814030001a0400d5004200344600304040003d409852211400c840e4483c1d511840f8004119042e10222418440001c0521040c1084c1c0145680030050600030f000c065600c0c50300f0041c0c0c0c800d40b000c148020a4940100d41090310440559006503000100c0c3c5445001c203040ca80c802c21000d481291191a1410708080014012a8a402101d1a4242e403140a49451040c054403004070403049a028030070704d1010401c0740e05040a140100c0e0310741e000503142c0c1d04058240407803c8241e00100102440440d10702106c0d1f076044840302032400181ca004100f40c4440020602030300070800c04200440c148020044440c40c042c070344086a00c82640e407502410244400d00080744010b407801004564104000750414109812468211001402c2034840d1041c540307 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 197846726 1250 197845476 197845481
    0x40611090d0602040612200313140105010608071106040314070618030305011e06050f0c0109060b0901050121090f0203060f040c1a1e090a0617010f05010828 69
    0x5404444030b50340450300340310f0250701204010414003250b401f00022001d003845030591180d540c4010144003c0000051f0951020101803044640d100c041d0305114198001030034060071090240c0800100c944000408081c81454500c040c0c0d1040c401a12154540d514121400902010100342c0d4110401c20080010098407681c0702541035140c490481d107002c1c1c90020143c880682c812031030341d142650b030500d5550504c0e50040c21940c0600b4216942ea01107886441c10707016820040740c407546403100300014400b05800c00d2242110456000b103440c0c1c1c90703400548810040030014103404480070841101c40202d60320100400d40903550850709104558000b915005080303800c29105a5042c003400100141181c140c00903042008481e02c041600c47e0b01042140691822a44500300c180d01c5845024050b10440c1c0080c900a860300c4066a2900307000b800e00b06800750140b04c0c00d41804000141000c6020968087d101d0594441d2015107070044907a24203150144214101031b20603003109036581452 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 197847976 1250 197846726 197846749
    0x70503030a0c231509011e02070501050a1b03230420010e0904020405060109030c060306050f03060105030c010807110601060c1a01180e0a0803010b09130603020904061109 75
    0x1c1ea01c482a450003480c1048022143d00d481034480c0c40c0714000b0b48041d02011881c03046503100d0304d400d21815620309420710301408075042c20422400c20420030b802c43c4800d40d0000e104a40c000c40080c0026107426001c1000c4414201581c1d010401007901e0514482c030a4200400407519010728140951000740d16000b54201960101e41600301014585070030200c080e0b00415610b42400c0c01504044c2810204a840b10b00510091066950758009001603000d044010091034001d44a82c06881c4c50303d00c045d009103180c0c001d8138880e02003500d040101d4940020880d043c1d407400f4001c0e1007103240d20f000540703100f400500680d081c0080c250b249032030028108a00c074020902d41d5038000e52a61642800c0700c04010501d502d20343c0d13603a00001401856246a84803000641004d00020407908440045090940c071000044c41c11400000008007100c0b94409000100d0382150382001d4150400ea82c030040340d40c00d11000303411901100006d408110154401180d14200c280a18a88218000000c1c040c6414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 197849226 1250 197847976 197847997
    0x1b03050c0f0c010f020a0506190f0e0105150a21030c0b0a1e09051c030b0405040b01090b09070e04050a0b04091a0703020a020a110406031a0a050601081501030902010207050303 77
    0x2d521002900c0d80c2c040001e200c1a4a1400549014031403510b03040d0321844011b0038110142e400100c07070701d00e044040d0721082c80c03d9886d1704c1c104410440d4030004c501826040c3c0f52a940d100e5036540111380d5140610010303003280c55051070106104400f600005901c8603820b03050701405228000040030918000800d442110fa500c0000360340100c0b1031402840e0003486107640011840c003501c6000082c00010b1040c10b020316040081070034071110300d003100500140031070660400d09003001d10040100d26001a03051750300c1703610203011000305107052200b006000c58900c0009988104290341500382517000c641c0100c200d802c04503d80304a44085015078488420490b0040502c084603a0088110205203410002900d829482d1450343d6000951380d4404c0030001d0302d5851020140d03141c6a9603a4080001590302c980708508001e0204812120f11000f103c00c207a440b03003408009801e43d882011240d10407192001d40326854000400114000d10111350124158810b2171408120780d50f0070400341018080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 197850476 1250 197849226 197849233
    0xa080303040209150108150a081f050601020a030207060c0206090406030f0317011203080a02040e0106051e120705030a1508031312080307080919030504031b061b03050c0f 75
    0x9040c8144143d0040050040501206055041c00c1e640e0b400914a90480f5070408140b414403c50000a1140310070b990080c0035912444504441550f100d24240f50300001c034020800203603a80b0f4005a0701d0f47c0b115800100140c00158003171040901407040e66041d00c0c00a400a4140080b00000c0790440b900764100780c2e02e445251fa8060101507011004245004408115040380c2d45440c2200741d01460301c8a005040c07220300700024084030041d0303040c1c1d8020700c0104583c41d0346503555a80580150300c5036640514003160700b01501c03500c0c25103404903030658024200d40c4c4003640c0d606401701c1d8560000b50035110202e4407101d079580c90644445401000d01071807405596928509058108091030503880307540c0010302814036501050b1040150fa07031044035410440c034181e03121a24507003402e000d00c8003010b18019100c160424554400041c0040d6445400744440d012002c801c008074484040c4241c00025500a00c24550000c2c3c7e01c08004e80544207052141c100320b141300c40c0b0f80c100030416005244550 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 197851726 1250 197850476 197850481
    0x3011e09020a030603050d09080303070c030c0b0403080f090a080d0209010302070f030509040e06010e15010504030c0e04060509010506030715051e030901200a0509010e06030a0609051f0e0a0207020a080303 90
    0x1b01c14010040c0108083c05d003046400c0c60403582a440b40001040c0d4024020886800b105141c041c80e20426030aa100d401410140f0702403030050710710001990704030441c400c0c000002d14100c0000542d2400690060442030514a42007040006940003520700c07810983c0900c1810002441c5400c19850729201e500c890352100480340510080f02e45c1ca14100d03c0580c0468010001c80c41050201d9400070502e101c05410224004010380d540d100d65400203055065507030300041d0500640340b401c0e000c1c1e1b200f06010b109076154100310134242c0c5c0080d210301d581030f000f20310108100c19400c00b02c60050005800c0c09420403000440c83e1000b010048000c0900c00000010040c03460400e00c501d807000c490078003554140b440d044007818014050009510203104002504200d41c0c0c0c026880010180c500405541d41c0b890801796200142540f807140d00c51072801c050202d0141d030044a5035001440400041d0807403240303840f400c0012401c000d0000380c0c4070380d402c1207041f000d42c80b4110010b002d807620f0030041d0b03500d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 197852976 1250 197851726 197851733
    0x109230a0f051b0d0903050721030c031406010c14100506040b01081b091903050c040f0e031c020c0106080307051b150304030917011a0f0603011e09020a030603 70
    0x1110b00412891080e4010954508004015000d80d148801c90b8880080c001111786002d81d602e2166050150290344500060f40028008180c07504408000350b8041c07042c801c0f28001542501c043d00c410301c4441a01000042d00341d4420b030050050507000d19210540264801d00c603030b00307201080c010004541e82341c00400030581018003910361424030078030f0980494500000784104149410420071640040029210070a940e28440c103045882c0308031a80c5001940e0f0b141166907040280c0e00d444c021400d1030b84044504241e07110310040041110003440c0f902d010820307410000c40010720a1000c60b6070a0001c0d01400009104803406000c00b18001c1d6a1545a810007510300b07450302c2c802071344103c20140305458684400b4190a000c42440c400f0b41c1d00c80e1210b24081e1034016071504800e201c81c10400c140c041700c640540005010b00d04000c1c006000c40400e0013400241c0444100d0150841d400b04010041519602d01d4012103040900500304010340760003042040c0d91005c684440081e86444060050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 197854226 1250 197852976 197852981
    0x10f0501080114011203230c0111071103010504080a0507022d010909051302040b061e041706090d111f140115090b0d06030b010314071d0109230a0f 65
    0x1740242800f010102e08140d940280901c403020702d40800009417030102809212447d090302d05111018009005c00615030500107103039048020700782c0300301c80f202c3c504030094201803207400c3c01590045240e80c902001440161003643c02140100c0c1c202500c071840c104612011182041044496040111005005c1c800140400c85030303003055050034500ba0920207660000001f03000b00e91782c107070340100b080459480095040d010f01d40151001801d43c2d0354101d40740c09064001d1081d10040d4910022042524840030b980381d404a81403070311503110310020445075005101035040f12075140c00310780e00446a0314910340314441036082d0010a5031a481643ca001d4448594a0302412081042d45c84000c121756001300000d00c14402c504030a640050700d11690815034020202450308880a43d0311541c0d00c1c6400c0070900c0424281e4102801041808030729046000c980001c44041186070101e26420000404020072419180303c080909540340d0310306c0c0810314802544107041410340005e00034190480b040c103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 197855476 1250 197854226 197854229
    0x1030509030c190309030501020d0e0d051303021201060b07030c021c020d061a04110d050a05010608041122050601090803031306180816030f0e0a0603090203010f050108011401 77
    0x1a0700203015404414038001810100d403801c103841c0c0040c0c40703a9400e0030307680d550094002030f0155000144083c02c42c01e0b150880090201030104503031040003180012611401040700b070f554000d2000004001515041d0710025101a0324800018100d9468248501c56449414102c01080c490b0301144154500799401c003402191140e42c0c4880c420843e40080c90040d6070f104000d290a640c3c0c540f1082410681d480302c0302e1486c0207841044804021404c03216641c120100c1c1c200c16600701000903031001c1003801114100c450715202d03003c00b511aaa101500004e80c0c2c0c00c240d400401c00b148854010100b071210204081d2071540015041c146030700010058a0690000c1110f0f0b8030800902864148805009420a07080310000501c146401108204508582000f505024011540d902284c02511515094031310903210301a111800da074065840501403400c01d03911031402c0c00e040001c507000e9000b004542c1d05c014000150f80000f25010350490300c0030b07041000143e40d9400c9220610b1500d010150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 197856726 1250 197855476 197855491
    0x21151d0105090106050906181c05010f020c030f0c010905150f0703050f06060a020c0303040b0a021b180604090b040b0702010c180510020703050d12110703080a0507050706020403050309010305 84
    0xd2081d8186134001d0301078030a43c040e081c0a124000341c8007001105150070b00b602284020004200e042519001e90400709010600ba00c107540b82c41400306035540c040c422a400b41c0000801355003000c0e807410004c0c407150448a8410600d54031a0740460000301c0c20700001c021001186079081e03186c10040b07208502c81d10000c100b0700030f01d40f8090920240c0001249030b280e021000b210f0722580d448038030f0f4089041a000284c1103800d444041030206901078500050f010b4080682d00320307003844000818514000da60401c026401c2210303038260100e4000c0c510b4050354801405400890102c4c2c0d19034849481c144212020390b007104a14043c859150f50a004c1d0f40c08800b410b2400604004849800101070107040c81001e1080000c00d900e095001e000344401c60041d900130054400000c1d01c600301401c2c8501c141d01c2c1040c1980b5081c03c1a00e40e081040c04e0354440341d0199280c3c011a03481d690b0000003414081c054006209040c0321010000320f941c0000c00c040c501c00c03006540c03103656427400901607a8000d8105e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 197857976 1250 197856726 197856739
    0x503160203091302090f040501140f09040b131109070c0201030608010b0a050d02040e03070c09061a0a0f1b0302010209090a0501030512090d02100e100201060621151d0105 75
    0x44401c1d0340e4580380c03c009200b00200041c0d64111207800035540001d250724182d0000d040c01c0002640c8040c860b500441c104082d0b442402d40000c4104000c040c401c00c0360001c1009140001007811321203c2001c95007100d20507555003000080c001300140640000f19036000c0040d085220311800c5591501500e40140300c003000074400c14403260b0020f841c903000c3e4002d090203190340082090540d503d5410a40190140c10240d9959184a04000816501c0d41c0548208542441c0000403040703100c000c04160846d000004a041c01c0c0c03004c200311000c1d1206807000d42002109076035140004221454421503c2c0310360001613581c07c8010a024070040002e1030100b100780340c03a0040001ca030012408400f81401090078554071010040016022100100065040010010040d03500c80d000360004000d028110343c016243c2c44034882c01c0782030340e00034002e040001d100c0305c4c031510308858924084c2160214151010840c0c401d0400c0c00101d59900e90710002d0254590241e80c0015050844882d014090a0302e14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 197859226 1250 197857976 197857987
    0x1020f0d0f05090a050a24020712030c020d1403040317030402060415030f05040c030308060d080a0e06070204090305040e0901020c060403081f0305010b040b1e060306010207080105070503160203 85
    0x30700000c034110101024408009080001c5603550120100503010040140e01c8407a140c2c8070f030074441c0001250b82c24030105240a001d01301780c000900c2d0300403070f51045460f0b038113a8135558003150548030100040f42c000311515001c1d00041d60082e00741d1460100b800041d034807180303142800c0d499003c2c41c00b8002c0100c4000c20500c80580c640000b110162041e0030220160340390a81000c90051015940410b407a924000c244000c0080041118040b240030381d45411aa0712003404020110407000700060032190300300158104107004220b0241000d2005140600313144150300820b055840040045001400002d030602080f01d0000c0036035000802c6400860500408060007aa1140701030b102a00384003d050011360212040729042146030190100c140c1e1241e56840c0c018080c00d90038001501c214106003580445040259401c07516807182c0501d0580041900d0070301500d54000b4001c42d0441c020700d400410241003d00030305c0d006500703e41d2070f0b60381c1e4a480180b41d222120040401070464008010b03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 197860476 1250 197859226 197859253
    0x608030903190203250902042408130b0c0702040504050708070f060203040311061b010b13020f032202091524030a0b01091a0d060b03040201021015091a01020f 70
    0x1500c045a645016030b9401c06620410170500c460419800490001e00008000ca2440e0550a0968400041131994141d58401d200150313039951049642100710018840f101020030300c004406038014090504591030f100e50760b008201603860481e02910729500007802000888010040b0310300806070b85c0040c0e01c80c00e080c640025242d201b1480301a02d8002d0ba05914009581c4810850380b020900403000750182083d210f542c1d0203441131440e0346220340d503c00613880c020400c41c002c40d21880c50a5580c907145a4501320500c50300440125031b114064203c04c01040140c8030610320702d00480c21111400c2c011414035041100802d0b44000e8030300c215540000c0754801c018402e007543c0d0400c08203d00890040e2602c00122001011a0311885240a42040c041c42c03907112038004002c81c4491a00911400f41c072103003107040520003a9002401a4810344030b52a0340650380e4080d00c07600c0001c590b2441c00985c1c40c151103003a20412264440c6803050703161000100c1d07070104415440120800042e2012515410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 197861726 1250 197860476 197860483
    0x40203030a08090c100c0605010501020304060c060f020d06030503182704050c1e010e04060b0304120c0204140105030d020f1e1606030c0f0201060e0105010507050a060608030903190203 81
    0x7680102400b56080220710002024080303103869a901030510b0560515004004190585402054541d81c2c5004004555540f001c0f0417102034480a48440910000301d036200001445540c0b0000030180d820300c001c00391249240108401140140000c68071400400b04841a14400680c820310030400b2007a105031400301d0142403c01c4100721096070710f0a0391b0b5410410f041c100708090b5030354000c1e00412403400d90703028100e051200c80c81c2030b680d03140081a102d00307001c00c83e02c050095200078181840050009601c401c84412540044c1c500b980308164268003040c1a65a03070940c2003440c428400041c46241820800701903a5019407004008460903031403400e89030070154007540c602c042101c0c8206109402000f210f01200c107100003522081d580c848004009100b2420504002064444102e84092050140a098400c230040455003a440c04005440d0b0740d1124004132041c0c0101007040010550902c28030b0010039440c0301850b07841c0f000e10700300b60403d2a2040001005007090f9228400350301d002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 197862976 1250 197861726 197861737
    0xd03140109020a02030c0f03040609120b28020708040501120911010e0609060c01050709060206040b22060509070519030c0509060105040302092d0c0a0f03021909030c090504020303 79
    0xa800594604019070100e0071845201b41180f0240300c0e4a541e1444140008010001c0b071790710380d64500c0310a450b007070602d2202d4000d100113050003603920b0115030080c10304100010301d03440400e802248540118100c01c140c0e080f0450075074281e400450200325558003e141d414640810340f00400c001c640c01e82e660103107080d00140c2c40781003000c034036090801610b601045440100c0001e014688501403001024042c020440b50440010303010300000070b00a00015405004552210000d221955200145c84030101042c211702d00c20b045440d03000c0d001c942c00c0e106075409018103401412000341810140021030b1002641e0602c074804071601040460036211b60681503c0c0c00b100c46130029100d41c00102c5050140c0e8001a5124500c0300900c043d440c0c0c1c40e0010342c01c4130b505605202441010140c049001d003401c0f20081c0300c940e420050350354601e1140009189481c800c0c1401400d0400e1034902d20158245003901c2400300720344078400d0090090b0051690020051791000b0300c040e2034141d010a07100c0c06103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 197864226 1250 197862976 197862989
    0x1806050d050405011503050610050f060403060507050d0207050616020c0105040902090d020405070903061128113a0207052202070308070e03011a21010c0c050d031401 73
    0x128000b00e8100706081d00310112046404108070b1096449007411070311005c0948105003060000d00000410381002c40904011040043c1102e0074546940c5681c0c010300700042040f42086410095003804425610146c80c00d2401803004000c24a020a84101d810904d0552003045d9840380c101500300381c2e481803c440950f194100e000da181c07158000420388a21580b40000d600c281804200840305900204203411207008413400d01010300410b03081076952040110768000c2d0303507000941d0b10880706000c01d6030510403514501900220003c800c20b070b0403c40b00803001104d203491070f101c3c0c244064401134202d0189180320004041850070050180d59090320340314641c0100d11500c4030140c80c1c40c9031031003c2010003a1860a542da084c451a0060001d80308172a840b01203400c003140038186003014826540407812101015540f900c9080400101c561806021109880243d004c2065500c0038010018103942548407000d400c1c10314904141030083c0b2540c8201014a007444005444c04461007580c11203c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 197865476 1250 197864226 197864231
    0x30e06161409030d0804020901140904120e0307090c11071d0402030f030a0201150e06090403030b040b1806121c180b12010f0b041419050a060f1806050d 67
    0x7016184005000300c100e142c3d418044d2103082022140c003c01c0c090700c20b030f01c202c4150500d80e8952011401450344580c01507080b00200d000680003448880c280605894982050312911007107400180c5444e507030380c1101c080c40e41c6606113080165040384044119441c810040d003100341c1081d000303445510f082440030481521000c00306040d501c05002031001000c81000703a95954aa014000e806000784006040301803620140c002044200350716510b01a035001045d10b03440340c4075514110043c3c0502c8608552090359403e254a041d0750742044000900120000b8520b107241400400c010090842d20151460b00180a451181c1c0300c0c0700252012414503090070320341202e90141d20030034480b298000c001c041c40001076207100c2d0541c800645040741c1404030040d40d015241d40b00c1a4140c040c1c0c0c0316070f003a0650f4040111541d840c1042c560740d6516090440000250303070341d074000303518108154010400b007004840d2503101e40703901c0203480c9900d260315910200c10601c0c2100060091003030b40211420350340e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 197866726 1250 197865476 197865497
    0x70203100908090a03061e0b0105030f04110a03030809060c040e07050a02011103090619060605160f0c06110d030507080103031d040e2503020906130605030a12030e0616 74
    0x1506010f4075003028000e0022200143c4910300b113070040c00f010071045040c89000c0c0e5916243c070128000c2c2001c480040e91a507040d51a00000702c00385070005032007220b800349981a080d00a131980288c180045009540e04031450905c202002e05001c809400d51411800400042c00307035007005c0c241c25400180524202e91f5a07040710600304d0050404000354001241c0000c240006070800041030350188807140a400081c4419a415004a5070710744500c401103041070044912130300c0c00f440701003003060040c4c0301d074601c0c0e19a603518000e0555175504076002080700718100141900e01001880440f24940c1420403003401e24040c06000180b05110003000c214844459504100501c0301c0c10075000300160041c0103040c00d241ca403075241d240c1405024004075640d1600494004590b40101c101c0f90051702c4007206444400a107c040303c0340d06030114041c3d45904000580707860400242c05410b010f20b041c6584030340319550003829140141003525260b1300803800d00c41e0103030259100d5800d44415050000c2401b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 197867976 1250 197866726 197866733
    0x3050313020a0e0916060f030e0a170703081501053001141305060a030f030908100212071e03051e0a02040905070c17090a0509130c0503030702031009 66
    0x10440c95200075007150070100c000481a56410707880d40280613440c1a00c03980300c0c5107070300701150403524421900050808000c40c0d84035802680450714903c100c2c41a22a00c03102512400d01a0014840f400c01d41c201c001110014164885010f58005148580b4055000010400200240a6040071020341f09083c903203004186218602500700440e042608540c541e5500d4000e004404401001402174585204a40c1e0441407482581c0c8581d00040c6041e40f01801c50b11498220340e0503410440c14410060800705180c44200207406003020544800f503a100714041c09260300c1c0d00d000d8403c0301444905c0c2000d021804141400003043c0c541450b0002d026550314040f22003000522600442059201050001c032441b02d400030004c0d14500c1c1401c0c4841c2d210b90104540e03140110b0700c00740c000802d41d2155908001c00c1c000a24954100421110300e164984000516401e4142c801d00305507041e40c41d102040020380500c650003804214086d60802505070003003915000c0042c49801203d80c1c03840c099080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 197869226 1250 197867976 197868001
    0x80406031a1c021e150d0e030c0607030c0c030f0c0c0909060e060105030a030f1409120f01050106081b0f070b07090e150d12121b03180b04030503 64
    0x198000509031014980220704414418290b0742040c0c1c0607181c0da40f01510100500f41100c100903c02608131480013110024164081c1c00041d0b02440c0340b501c0d1a80580260b0082019040c8001c1e007030050302030790402e218040c0c211030804e440142030081420982c00800d41044424994080314145114148041e190500d00c280b046c0c0c214810803131a00c1c403003030184030340c030350100312448541307030032240c19980340c0f020195540490b09004000607100704804400e00d03c5001d0582031040c10103c1942400316840004070304030609022300c4047d41c000d80c040541e003142402214010720850424003c0d41c1407209070301071151280c407000d0041c80790000b02ca410008a040c215040a0b07007142e400d040900740f0440082a20490b4840e1256402c46a408260710091030b46100710001d100134110044501d86966005040314a0003210003408031000c5042c3c6000348a0240801e80324044c3d01940217003a0421780079085802d0032401d003552400b61039070b40c4006000304d80c040e504180c06090003912944c070310b19003210 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 197870476 1250 197869226 197869271
    0x12080403110706021e0102121b091519030e03161407060c020a080601050607120c0506040b190501031130010204140111060708090a0b090c090702030708040603 70
    0x707489404400500f0a1340801c0a449401d403c11407100b2617140480030320b01382d000d80138844010700142e00110301c81500c0c042c0c6011900c0301e410099401c4c001204000b82c020444007c1d41708101d440043d01c040707060322a504071802c604603400d0400401400e8020a643c0e8025044d0300d221008940540e4810311554041e140f2541c1090b0342154451170311164010802ca40009003280108000640890604d00100d0240c0c16107002405c01d500304061515030042420220715a68144541d0250040104000388500f40c0b0072401401d10f104142000031341114200c500190501e04a880c1000602c00180e65040d00f04e4446004c8981d040d1080e101021202c20820042502d0b41c540b2441301d4130440c000041d0040c10071504140326410469082400665004403041c0d4801000d030400320004420707500582805070800344030401c40310300d206942d40303446072004156248881580700d000e004078103182000c2c000d58400030340d01c055070401007280c3d9403400502480c00b4400616455581d6141800010201c060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 197871726 1250 197870476 197870507
    0x10061107031b06090b0403050a06020702130912080a0902180a0605060406030b15040303080a0f0e030a090f080c060711060706020a2106050307120812040c06020706020a12080403 78
    0x41d4220001e0b1840c03031200c2c548615004216107007000141600c052080c3c2d41241c0e041005032100c2c40c8035a030780800a500881040340d01c1420101c84000315601b600c2000100c40c491282045600c0b00d040000d011220001d101002a03810301000701c006858181401c603003d0728001000b0300b9a12410a0384026040b203030402c5400203008500050342c6581038111000f03903d029100c00c2c4c0d084070b2102d04071509206030f02002d008200c500700850302c681c10719400300c5102c0030010313800195079503803600107800c40d4003000c20200002d41c422000e125100300a901d21006000890080054100b0100031503054000c02d60068003200d1260f0000200d43c40f854100d502407503000804554035165043c001d003000c0240d440100d01803d142481e10303a44880c510803001034800007001015402d1030402d8040807884410030031200968103000b8484140e001e0781c1864015072007000642c0f0814100300000780f41121075401481103510284182c13022555080205500c6031461a020355695503505040d11100030051110307 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 197872976 1250 197871726 197871743
    0x70512011419050a0626160f030b06030f0607081b1323030705040b04230402090a0510060c081209030a0e0a0f0603180606080c040b091006110703 64
    0x12907840600755002c03001240c8840108501d803a1800c00c50110303212801171020b1180b1085c1c006580c807030300003081d024140010084881034610306101c810000550f9110780000184034100380300700102d0072040c580c40b15040d40100000004080d01e55520031f40038040ca001d000b240c0d000f1490140c0404c0c0e0243e400d00324080050f0307462540c082c0f410040c1019104041c208542d203840c1c820504802c0c034400300d8800d1b004004201180c1820200001403106100403275015564004010f00542e8070210782c66070510f00306040f42c6514160062103d00b4000070702c0c1c101014507000412404840c440a500300351016883c0003801e00f1030908d040310517071051055034035194001004220781c400c0d0010013000340300800d55070024080030f040c0900288013460302850b0001c40590745c042c003801d40720350311029032210b00305081d03000c074906503c0300401c4450981000d66283c01c10102d020090410b401000a9400c007501d042840f8501014101c1c0c00c00014002c007020020740603c10b050454041101f03501860300a542c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 197874226 1250 197872976 197872981
    0x606160c140103050a0b0907050c010e06010909140d170604090212010b01090f0605030a020315061b070f0b07060b06090604080c12010603080a18030b0c0d0501090204080705120114 79
    0x4407003069500410060001303003400b0014400b03140d60f00a200c070f084c04c0030380104250703107030008c00faa456040340e60101515940e070781071480c1100301013103001c3c024141404005081c3c44079040081c110700c0500941d4403158003844d0307200e80f280d9004114105900380c540d032059150310b87c1c0c00080c015040c0b19030041e60000c1e00c1c03e03008e40f801da0107501246075000247c13990300d58540c0d904c40c84d900722480d520404011600a00002e1700710744040c1c0085d43e101043c00000f2007803d00c41800070f40d65810005905860101070298603a205004004040c0542202c07903149407600d00d04444181e1501c81d18900401d041c0d25464401c0c100d40b1100241c89504d50010000354a442e2602e003a10ba8403071480703030031a104409403450150012418800d01080d0394104040c1da213060610142074959410525409204c025012000004603080800c80c0f0301410032900400d40e1210712082400541d881030304941c662900c10002040b100200080c44802c8800a8843c0d01d002c003a201280c900400d5042000408148620304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 197875476 1250 197874226 197874239
    0xc080d020f0711191802090d02030708031210030c030206070c0302150901080606070b010e0c04030204060b0a02010f0b0603150109090507030219080f06010e1f05130e0405060606160c 80
    0x40711440030342a9825801000041c440d183e00034045c1c07084040c0e5131503001c58400c503100d4030380060445100203400e24110004641c042481c3c0b0800b039103d029250004141030707861702524401030750031180f840303101802f00e41903881e00360f0700b0320503413200034860a80001c0341d0b410000340840480c01141c00409103d8090072900e881035007071b8480101d0f41d00240828000503002d107403560603541919001030441c116a03003818640c0c0c02c02100902141c14a50307080c00000f0042c0d40328000c05004d03009001c2c003607441c3c01320b04401909450091102c4c42c8120b05001c58000c15403903000942c0d078408105528071040c906481c0050b034013a070391504004620f60520381001803041d010f070001d00106095426081d60b010504408a9801c0360a6401d03c000d929528040f4015601c141c0090485680c0201072941114103404e44240b9072250007091400b0800c0418808029014050000020520400100014500741d0b03102d980710700e0b004021074422600422410301c010302d442c645040039580222480703d5a81c8a00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 197876726 1250 197875476 197875493
    0x1b06140a030b0a24020114010e18011503022b11120106170d210b040209030d1e2d180303180b09010e130f0929070c080d020f07 56
    0x6030442d144c5400b400030140314814411490260030340a280c80c10b50f400d00410210003a030203802c0c0c400c1360b402444c1021044000388244038071118040b003620f450510310700c107002d01c08030b64a01041894409512680c0c041a0301415482c4a07035105625038032044c440e01c0001c049014452201c01a0742c40c1140c00b01d80c651414a05606204c070103001c40d0580fa0350010308a0702031802d1070404201d600700c0600611020000e8102e900600c40041015043c620440003080c074005500c1100000640f15074000b0002400690300c90614660714580502000903003410aa500706843c00e14900300d00c60a0703010002d1603c81c0d4613410201441000c18664190703207080040140303800022190390b64901d80c50008152112074101c92007002c041e12018602e4400904200c043ca4104402d88011a102c100c610b00780b80d417a102d000096880b801c03410501500310341d900c0f13020030003201440e00c039060760b0014800d901d42c1040b202c5165540c03207221385a945c0ca5103207000000c1c2c0520310002c16102c401240000400445c0c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 197877976 1250 197876726 197876759
    0x150310090302161205010b04111606023708060607020d020d05061801060f240e0604290403030e0d1a15011b1e0602090604121b06140a030b0a 62
    0x8174006c0c060355441e00100300844100c1d070000c1c11108806c001c40038004800d030003080722040c0034281c010300b09000140c0250810001c000c000d000304c50820340030100e0381c081c8099021042c840303182112607841d250303022035101d00c901c81e0007034440c003102d011103030856440421060b00a07521500341c5480e402c040095080b95200c5000720006035080c0b04c0003003000b50303035280720030300b240c002c01480d400d200040101091021080c0040381c040020b0340552038850b4907200010300081411150351010f00081101000200103074800c0d40307500344000c00040011a0384010f10ba03440310021510710f580c9000d14545840c000a40d0328205091f06084003c00c0740040711020725086584081c1c8403400701d80c09103045c00700021990780009100515a211000c4050003000207458024400c1c81e00500d4004500300181164205922074400c99410702b42200c1004102034142038038540b207800d102106400e120014161404195a00309880000301e519440c8078032940101e0400c0710003030503407200c3c0d588400f104c0000345200d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 197879226 1250 197877976 197877983
    0xb060d0f0203071704030c0305030711070303050405031227120a05071701020c0d031e14040227010603050c0409050403090807170604080a180906030b1503100903021612 74
    0x5801301303000c603901070300d07107003841213500d0b903201c0b02220b101d540d090b5030581000d4802d41c10802a07807941201d001d0104025009540261203e90319249441c0415180145c0300e54000a1000c083c42404082004240041c0c90385001c007100310505260706000c110500d01034490300319a8400c0040d21800c2c0301d0b003c81c0d803000f625801014180d2650a1102190903031064a21140c60f991240100070501c0303110380c0c040583e402244008407607a144103c52901541d0208441c02420003040040c0004c61412a40ba4590100b44090035200880c0ca10351000c41c81c0014454035040c107440340c1c0041c0d50022424101d501400c802e80c010415030502e0700340144404094004c002191248000100750b512442410402d55000381e0020041d030750340e0b5610041180c0015480e0401e025100700d120ba9007a006c02c1c3c1005c007420b0400400140903185003404103203104003420700314480c80f43d41c0501800742c8001c01c40c41c61003108514007141c030303180e1454100d107007440140d1520382c2c641d01190049000b030341c1f0020700d503a090301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 197880476 1250 197879226 197879237
    0x140d0c140a0b150f0603071d03070510080f0601030b09040f03090506070b0405010b0108090d1101060314030a02010b04020a0c0605280c080a15031205040e100302180402130b060d0f020307 82
    0x40c0c4e106005142c07105881510101d10008a030030b44542241c1c00c110703000c0344003030241e0f00209e81d0b0b40040303505d0048543d00318003c00c0803542000061142c840300654042c80034038040c0104400500070618a140181c80a4449400a60801d00307050061090a00805014040300d5881c3d140d81401c0d09150410b0311300319199420940d602110b90700c10310086014250010282100c0041100180c40011800003854401e54840d840000400c4200c0d4645c0d90720600d02000d90356030f0300d0282e0000d00311000584401c0c4a10300c18400344508a61108004658030703130140c800142c60b02c074080340a4120200040605a80002c036804d90440d80381604490040307aa940c449101940f5140305040943d04004500070b12180009410400311f0f40072140f507040110982402450242c0b10f00c0c5c2c1840c01482100c0e500c0c0e0791905c0c0c0f00108214280a0410042289000b00c6656141825400286400301c5000074181c1642c65455070250390307441070112624402d44c1281045844030f86018038010f500200c0d00039000c40c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 197881726 1250 197880476 197880499
    0x30114010311030105010e030109050102070c1d0702030405090601120e01020a110a021005071b1e08060906060f0402040914040c0f031109100506030f04140d0c140a0b15 74
    0x1402030052510028200d0324071410f503070a10340112070012101005943c50744d02e030310101c00802d03420320007464514007400e40c04000710306148489406001000350031850046260802070704c154080203072001d4650490310f01000b61507840040300c55260f1441e54945042c0b900080004130001540100a04e00307040d00c1c1c107401041c5408145441d0005a0b8000c0e40003504941c0c4402c200388920001c101c0d41d4403444400349240d940c6441107583d40500c0c0c001c1e00c042080728254156007040c80aa000080285100801491528540440e20342e48050041070080e81c10010410a40d9105c0c0c0554001c0d10030000d0402c030001791200d0700c0f440070300143c5041e10104041c01012440d08407100603c015690024200390b101070340e12092002c0300c140201151103070601c0000129403aa40c1d400118000e0011640040031410907003442c59600c10300f948044400d6202006000c821504141e400030095000b4032401d0350540e00602c61400e01c150100014140c1550394200141624110f522240d4178105403162804030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 197882976 1250 197881726 197881729
    0xb0f04030f0506010f1205100510032406050a08190201180305061b04080d120e030d1a0301050c0a050d110d021309150605070c0503060405100506030c010503060402071a130605060f012a050a030302030114 89
    0x2402c0d07801130b00301c16003000300b4740320f103d00d40030141d00000e51042c03501601d945007090300c0404041c404e40040b078403030f0001030920440c034890f06112001d1036a5030700302c3c603d0107181114550303484512580240a0021030f0040d03e908040f298000b004001c80031041d20380c2d81e01c10612400003402020301c105990400e60705d00074010300303051191600c01e0300c0d2640c0c2d03a4a01691007800703031902d400410365222480e40b18020160000088000b0b4580c05803400405a2151085009c0165240c1107411107103c845c40c11000d00100c2006a1105040b5110ba00b042d0f50b07116428100305600a05541000d42c02d84240000d0000308980040d40101c2e0b54030700d04041216446200c20192130703180c00b0f07030358030300007a0b060000c00c07001e21b016402801c141b4840d0f1480c01202901c40c030f95175140d0304100d41034084016070144c4281449068000e540d80520100e44045e81e00d00b0800c0081c050143e603840d0a4031191005c08911203501c00600b054a40c02c0c2c120007103518542245c68014081e500034041c0070003888214414040c903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 197884226 1250 197882976 197882989
    0x61202030f0d2f01060b070b060907080a020702120f03070311120306040b18040818150d0207020102120319060501020c0a0b0f04030f0506010f120510051003240605 72
    0x203030300741d0341d07484900f0344841e9510341c0186400c1e51944400720141009036030380f00c000d2269030010b00104268035101c1c1d09504001503280780c021b000600030b0720140d0030840105c0d880180141e1002400d0001612540107001280d25400d541c40c43c0c00c2075204100c010380300b102e0000007801080b4420b50b55070012980c0a403503d9165040d944042e0811a020f0000c01c0051030290840590703440054090080d6441c003010809484c002507070b054903545800280001c108020f03800800036050184c0c0c20400003c0c262403422850301c240d1000e4411582d022400c0d03403c42e8402d11800e001d40b0f01c02800d8036100c0c03c212442c2c5c5820030300d440a220006252000004d030315400414441c081500080c1101c0c2898035112b40766805500c0f08141500440040101100050034001419081805100184504e6040009911050030560800d000240c43d400d00500003a200203080c44803241c000c880481c2c0ca845150550030208400d8000500d0720b02003104454503284040d0005a040c04c20100c2445259aa035050200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 197885476 1250 197884226 197884243
    0xc0403030c032001021602010f0201060806060402031e0405060a0f1a010315090608030405030706080402090c09030a0204020c010c18080a2402040803041a030c12090c04061202030f 79
    0x2040d11444040003090083d42d007069a04000d001d0071498040d0200c48600326401409589000b10b00c6050704c1040d942d01492030782c0f0991160008021540c14800748540e01d070350003000544500d4001000400f80d00303400c45400600fa1191041204030b0901d0700e00700b41c6484089490520151608413460b091600c41e0080751082450020308905002c510700044000e45510400307185040e20448000581110302d102c1d0400916161024507190703400c0c241014205001075009004010f10301e030500c00586d0725074840e5904460401002030303a64204101081c1003941502001c0e51261010030000b040342d4064100000ca0442503075418501c90840003080121252030240200650106d1700c500005200303d4880e1100c145842100021005001415030981e40705404c03c50a44d040401c0401000390b1b519020b0034950b1090b91014154038103401f034075505004000c0d61a030f030704401d5030114001401c2031200001c6074030040d0060050701c0e220070125000400c0301c10100e0192060650500080502091024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 197886726 1250 197885476 197885483
    0x70b010608250f170c0405030f0d1e030f05070c120f0e010318080706060303080c0a0e011407060905030318060c1905040905240613030213060e0a140c0403 68
    0x31800314142400c50f0b00e0b40f10f000e120401e1102000040300303104c4100c0d5007180300e8800f5100542d61079042100f1305040081850000b0410b61080d0190003c0130b40204000324803203201030610704030030031140c0b0480c051700041480b1060b03607280600b0300a025620518000c100390040c1c0e0f103e40b004036190000c40300c100d90991803d0005169070a0100290b1003904565030000707000b41c0300011006152100c00890341302120480d10030755161010410180c20100140d4803075402340c1d00a0030200a0a00034142c01c4031104040d0400035550102400340500303005442c0600c2e04000100700c94402c61501a0703607a07001781c4019616850b1000c0d080f030340600000d1114880c10f500341d491420070403a076012015001807010104203001c1e083c4004200c0403941d202d01ca06c01d000581c0070400520100080c2d0075510b6100310214000c0300208824010411801e0003041280e60540d03135643c50a8500f0501c0001700f07a16006903200a549109100703500d41d4a403c12100c034a09100c81e0f11544e220301e1110809803080d0f20008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 197887976 1250 197886726 197886781
    0x1502031e04020102120c120f221401080711061924050f030114070203030709050f031c02030408030c010212070c0b070507170a170907060504090207080c03070b010608 73
    0x6152094170304043c0c40203401050458450303400003c4000f5a036009602a03d074280000f1520414290303100551128802010700c0c5200c5480c100010521402c1182c400030f410b010700840410145c81c815060300401d10061800c4d6035041c10304045807088000e91072100150300c1e007010714a050b14011010001320354014080c800e50200d18140500811444110510740e06540e40c2d40400b20708810408a1442181c455002d15560700d07003210003030301080c10703500b045006040092501d18581c4001843c01e49c4d68200b240e0350240d4070b0000d54102d1443c0b0641d0030000d11070002041d8070509480540140c13000d101c800d08949026070725080d00302d4807089214000780016038248049588a40154014034040f07005844410000008422101075644140c0391040050502c3c1e000f000b510603c1c0c0d05003900031605001a0a51130f1921200800500550082a60155000500301c0400481e4411524030a84d881d0035251a107071541003a108080b4244221000318044100240c1486010f001d071040981211206 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 197889226 1250 197887976 197887993
    0x1312031e0e0c100903140102090904080d15091a042703030b1504031208070807140415020105100605071208060d0212010b010e040e0606090c04031502031e04020102 72
    0x80406421100700300c011030300481d0b28891040e2100c040094241c1d0468603000206881c614000c6940d80012100111503481440301100700c1c1c3e0b505507020303045500f080005850302c03d18200d00d070040c03410901016800132001000109080660840c5aa40d0a50104130440030001828001542c001c184804250000702d5020b5101e5000c9507202d28081e4002c0c540000e20729208004100d41d164a08403007100440042010010000d410000c018080c0c2d80c0d03e0241d0341030920042c05045620301600890a000e14004414200e942c00c205980c01445c0000d2201c011342c01d03649001c1e0082c0010360f580094425a81000b1810f20701500885800686c40fa501580030741070750034119090a0040d101355449015180107801596840d468865040079440000805102980c000760650800d410078900403030425404e0100f250b03010501a6001006480c44883c90f91205501d00280c421b036000100b0b1100c00900028181009078003440c030a052040c07084824804120940c4149001114000d0040e4000e299 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 197890476 1250 197889226 197889281
    0x1e0501081b090c0a0f050423040c030b0901090506040902030102131403070b27041b0305060f0a0506090f1f022118030f0d1701091103010e04030c0b131203 68
    0x317902c03600011a10301242000c1d02c1d40c6041001c807003280103a001c00140c040c000c850601c2c140c800c02c85400b8aa080406c1038207240404180e500d00c05106412109680724006655611903810080d85030764014000c558030a50000107102d074502e070b0302480341064105003800e6104d080014014041e21549600c0c00d00701641440401c002d110040070004206515601081083c0c88130b018818400403e921445408094041c009086035401040300707110b520081d1b4200705540f103080f408003d450b000d8903556594158107000c2500a081c0f2940d82c1d402001c2181c424228401d03465003014545425400d035101c00440240d0b44030900c81041780c030102e00743c1c20490312221411442d07610103e03c0d400350031348491103914048241401c4a402c40c1001040e100010071400588254070103005d425130840405c24a00401e03143d007818001400f0321078020443d40086000d0500801290b030002ea4070140020301860805105115448528011907540009006141030b00d4004c0c0166042112036611704045a0110b24 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 197891726 1250 197890476 197890487
    0x910050702101505060c0303070f03020406050a0c06020403080f0a39141002090901290706091e050d0206040b071b050610050109120c06031e0501081b090c0a 69
    0x3ea060307400c1101c07400002031a0319460060510342003080301a40d1a45055000a0103a81e4003020f6441003600c10801405a55005019155500c0301403400b0044a02d40e40791500003840b450b04041c00c1c21402142d030004134203c08000301402840c999a041c101d030080c0c001d001c25090b1107400300300f020064440d01080300442010303000c0414082c5115110200b003d9040c1402c0c140141c420201d095000100724030760741071034422507005104c050108030b1000302109202068441030580c0400d2a032002a1240c180801a004801f1190b000b080c10342c048001c401e8480c0809102c15000c075401c1c082c182d20190000c2c00070541c148155080302d044580d80d9105401200c03c140252414007100c041c0c4400b01c0c0124008101151083c0f40201c0c408690b00d00b80000500361142c03960141c03048404071880d1000081401d00400e04030750450602040406194082d040300122003056682c48030300c2c000c0002120700c00011000a80d0302000918182c2c01080b00038042c114404580102541e00c1c104001301c0f0700780c880e6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 197892976 1250 197891726 197891741
    0xf03060d02040c050a02011d030d0b03100e03072d03050901020a050102070b100e09030405040b0105040306020703170a06030c0b030603010e0a05060f010e070f181a03091005070210 79
    0xc02400d2459281e60020341214401541c0301c1c0000c0340401c02c110a01d0302445141c054000d40b10030801039810074855a5a03902c249641b0705400c0d0303250704000c0b625481c01c1010160000700b051082c8500c0380d503068201c0d0780382c201c494250768501d241c0c40c04003600c62040c1c80310300c08000c04080420400300f69440c00d80d001d0380003c003064114410040316001040c0f080c4094101c03684150b0070b201840c144480010f000c840e0b6500024000e03202c1c0418070000c500000215401c503030741076034041f801480c03020040c0c44c0c0d4021940b02511490002860008161340883c0c020320120100700703e00103a03107846405104941d40c0e070100030981d104c0758009100081d07518001d0355014400400100310004070301541414001c0c04103088510342d00c80b42c1807280c0c21078460300c101d003d060000080740d114a0424001004c4205c0d82c403106d020b00070702e0504d40700c400c007032004c00302c0103092141c2e183c0b014000c04000d0b001690340200d800c81c1841c000ca080c0d4070b0303d00e100d03802800d000300c080d940184034803001c0f280b10100070f1004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 197894226 1250 197892976 197892979
    0x702010501170a1b0b0412020406140a2c0106020c330d02071703040314180603040510020f09031501050d14011407260408040b0f09060c07080d0201110f0306 69
    0x45440c000380071151704000f00040d201075815a00000150300c180400d85980c0e0700000405030710341001c003145445e2404410101d580c0a100e2401c3c4080212004800c04040b007240c00308046034000206429800041106402400303944403190b1411402c840600f811107106010307440826006200c082071030b41c00240c6103e0300e0400005182c000359030f0b14035107001052412441c60303013400703c01c002c00d240d048031040f00740061210b012072170300f15140b800e0411440110601849460040045824010304011004114002c41011580d80703880621501070758208400042c0b0030703c6041e0b4544401045440300c42d040b21070140c0a080040402e54401080090740c0402d105559619400c1e410362003042c600d43c2c0e00407001c41c0c031042200ca120318804141452600f0304044003083c01010310000403c00c42c110f40407503080d0307030010b901c8448044104a5910655000741da10060114116044007008a00d000840703034064221a02c000503000143e00340c03900600c4400c403120b01444003018120401c2c0003035602260 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 197895476 1250 197894226 197894273
    0x6061e030321110703022505032d010e010506030705040e060c030c070b01030305090a0506030609040602030c0706090c0e090f070308072103090606080a020303090f04060510080702010501170a 84
    0xf40480400303150f00403c10590040c0d002c1243e00280c1001d01d040d0071000903042c0b82d000441410040402d6440200404412080c00801500c3c141c078100384030720404031001e42e0000e0120b503012081e064040c02041e035070035100780607001001580b4501403050041601048001c3d02440ea50f03800e400a1980005107078130001c0d58200500c20010f9919003050740030310311070b44640d0b0715400110144450500c980e004140505002c1007445001c0d540e040c2da680d80164018805079030383e07480da4580e010a010352070008100b80d08001c2c140c010404494070071400da98440100a440342d80305404160f44d4049070100301c400d07400501c81400424502002841e440d40202d013403e003100c05850140c0180314640d02401d00196a9462007403c2150b607010b40c1c1d004017140002481800c40e60380000781c4034451202018414000008211060749440c2c00000c01400001c0001c19001e4400d000170307200752411220070005520740000401c48400348000c04007400c4d0408001d0a40410369a61011811200b0060814114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 197896726 1250 197895476 197895491
    0x280b13020607020d06021804090f020f120106180b0303040f030b0901020f0315030f0d0e21070b1207020a03050d020a12050a061802030c07080a03110706061e030321 72
    0xc0b100701001c141390b4445c500c010380c1e45148405035209094007014440c0300300d080c48000d10108810040f401112034044440c0c07840c034296507001940001507030800c22465400c008000030313860030444a10000d00712610702484406501d80806440748100d00034a182d540017404240045910090103a62004501000514003402c40039031418540088079103511040c100004004a4101840f070407001c4545c160007000005004200a0b0806240c102030324014040f2581c610409000d00f505001f6200080c010340d2607440c0c4402040c0c40640c4a0444170000d0300d030150202d450355100140082200d0303003690b03480d402c200121040b40c0c06540711843c440100440144900b80d000420300c01c083c0160b16600c0c0004182e03180c9903c00b451a8a8a409407403407604c107200b00b010381d4844500300c4203100c2e800f00815580e10107a090540050004107110f0480b6000801c0303440400030564065400d41d00140d800200c01c1030b5010440704003401d5408014009000d014007250b007001c05e110b1140c000d80038103802142c3d91 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 197897976 1250 197896726 197896729
    0x3070c050a06050a0b010e19060e0604050a0303050a08160c061802091501030c02030c030a0c050f03040308070b09010221090f0a0b010906060504080c0603040204110c280b1302060702 80
    0xc40040e10134914460780c07100039400e00e40c0c1100110b29005400c0c0c80000044259904003000d2565601c580c500340094404200080d650703580456024000060440c001e85860342070007132698000350080b402140320308001c00c8135030300c03c114445031040c903a81d50fa400c0020a2750364071010380419440440c20242e082e4900e00166070300c0c2c2c0b00a116441d1640f01c03810001c0c01d5030005050300c06010310b42003503401c01c004921050801000b02c40405400c0e08115840d4406d074a4014a020300c060500041400040780100410107000000d00c000c5d402140600002d484540c0000d00300e10403a556003000404800d25550582001d0001990203600c01c020b403000c1d1540740d904a400e0401d07034070b0200c031911800001803000001911540700900114030b021420705060a4010799900c14009105100ea40d01000107401c65607507402c22030400c80c1360039209031180a403003c042d41c1da48400c0102c40c600501640c10402c01c0345040b0001c010300340c004c0e8010b15561100c0084c51141c0350b54800c26600840c0070421200903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 197899226 1250 197897976 197897981
    0xc07140a0f0b0702040b04062601050a0606020c0f0d0506070825051602150d1e06210c12030f02100b010c0609110d0b1803030103030801060f0207050406090212011a03070c050a06 78
    0x5940d1039180f0740c272600c03568274a00d400c5410082c486907255141c03800c144001c0da400590b82400d41d400384c0c0c02e40e1240860400040301c0c2401580005e146105103000c024045521504c20f50141208420b440410700c40c4c001031a0600754007404c0300d80090003c6c00340810582a0740410301c00c407070000e0002d0b03108a1112058108551080740d00e10070301a1104000f070110b044110400300c0e10030128004020a0307041c41e007041e004101300c1e0205401401d4103586003007070043c4450458028404841c20200803072403840e000d0198450141600b000d0300800c80030090182c00c90180e5200d160050303580d402210b40c140c1c1d804000388850201900e1018049452038440e454001e10140440c0c0509982030792031805400300184003115040e6002150402e10040000a402c91000f5041d10100d04254400500c5100100d14108841c0d008a900c00e040203070024807803041f0360050540d5500c51010b6425a0b0700e131815200400035182100f01404000c20000e41001d00c101c040044080c415810f1b110410202c1d12610f09 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 197900476 1250 197899226 197899259
    0x71707022b15020307051b1c121409030405040c020708070603020318030906070303020c010b0a03060204090c020106050d120207170c01081509040201140c07140a0f0b0702040b0406 79
    0x7282000c0d01c1400344551048950002a5901c905628510700400010110f016030b00c02d025990b814855115400e038003d0181c4c80c1026035030100b4140d90a075140c0020140802200d075411241c1c5000c814680304580009594854413548000703503c3e1520b41010b01c07008055100c2808214045c0c800081071010341842010010481aa80540c4034140840c595980401c0b650400e5240d41c420450f000060301d680080e00c06441d0941801619041c8604016000d080c03010f4542d0b43c000d03080c01021081100300e034060015501c040c88204144e6421800070707800c95072240601c4e9404440c00840f400020f100c4841d2800000c280d10565101030354504a03100f58201c50800440a500b011090046179644a1001640f01016185c3c14003510040c1010441101c0d000e0700280c1040400c0480c5043d070021030003141c200140e0441100d21040e0348402400002901180051007100c80c4980062682194410b00e000d80d180541058501541982040020940c64052a402507100d02c0001450801c8500307010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 197901726 1250 197900476 197900539
    0x602040902180109080c040504020409050613111e1002010e030c0c0112180b040804051809060106050c07090c02070b1603030b010305010b0901110c09070f0f020307170702 75
    0x140c0b198000d9200c0400100300074806410042440720402020b200085d50b5400008251400503c1382c85500106d0081c101401c00508248500e03410301954195200c5c0740c6100c140540184801c2101d4001000040e4130b030760b81a40d065001c010184640e40c80c28003092800403040340000200490b46018081c210380003017000030040c1d00702c8040502e155801500c4c01800d040d16000030002c3d11925209030390000f82414001d0714000715080041d0400110100300c4001e007000500c2c1c680650840d00907404510b60450f03402c12240203031400041c8007401042940e1a85000e00d002c3c2954500344a07040b001080c203844144114801c001c0b001070303980526401003844001045040144d4245410013406482021100030304061601004201310314007481920030180307003440d0002c01c050f0310301d000918000180701520390040503002800074bc40d1300107100280c1d400300b94036407001d0345402c4041070307850380281d0002904100c800f180c44035440c030380800200b0381c00348010041c0343c104014070400c088030030001c03070801d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 197902976 1250 197901726 197901731
    0x105160c03082d070305130302040204171002030121030215010b030403030b2d01140408070501120504020604210c0803030912091509060c151801020a0f1b06020409 72
    0x12090b0031101e0060f507036100441103a02c41440301510302d051a8890200e005d4100301c00446c0f0f0300a5030358405541c01c02590010029915140c0b1949000a0160910342441c01e44c4100410303e81d03500707010b0080d00c2c120b407800965200112105400c1422551148000b10704600404241d9200c12801807200c41c003230010f54242540300d05c2c2901e409811200882c260341c0c45864108001d400710f1016400c00000320380d0310340412086541c1e200060302d100b00b82081903400030002060101d07183c00006a0b0400f100e9090340d0f941d0303103014000c0f00c0404945d001e58020b500244100814480000d00410400500013040ba0304030700080c0d2625900342048640e003008101d03400010602000f86001c101c029030114001d40c40d80e203000d421030300103030350400482c504841e40840421401c007255508810b91b41d8403002142981d103211002c55800d500c1460441d1825080c6090302c3d040840740e401403080c1c4050f05210b4469030400010001d05030342c451035120700302407510130f0715045000003007980c0003600041003100400b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 197904226 1250 197902976 197902987
    0x91a090601083d090e060c0304030e09040f080a0c0311150f06010219080405150c030304021302130311030c0607230102040b0a05090f0901050109050105160c0308 71
    0x4000844a000d0142030400103103000744849000d500340700da6900b41400121000c01444803400104280034011010030031a40101d0004012070716810141000e102d400c01c1c5e5900d651504082d62150105550160002c0c403c1a821080740c00c3c940107803900705009180d4103051404070340c1c0360007840d031080b54038000042c01841110708058000c0c04003120b40703429101401d400b000b00404031003503040050400f030702f0601b00750110361a41d00a0010010809a1409960b5032500908082d1a1940984140341c061040011640c2c2e2484400d0309071011842090081e45c82c6071503039000c01102115810303115400a50070448000301181e08410f440003580701c1c0095a10080da200c04050418030505151805000204494000100104031591003142c0d50040c007080996420040390081c022a000b100b0044c00000d2a070301c904c0c1c0c002c001f4182c0c00320112800e4101d0710030131082c004a03540a204607804a02400b5090045d58014400740421000e10b00c00030148a8241e1a440c010520507407041c1c03075a8200058 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 197905476 1250 197904226 197904229
    0x1d092404050105010203090d06090b09060708010f1409100e100801050c09101d09151f0f050d150e010810090308180a052a0108090a0813091a 62
    0x1020521100031601040a5858800043d4582c03240f0b00025110b241002e120100708003050b40820032268000e04440350a28010303a0050b03032500192508000300c0c426800000d2040c0c3ea01c0107890688031091921204034036250140640340e0030140c0004e490480640e400309040d03180d0300200d8800c03500d204482d50590700c0d09440e01d08584001c0c1c44240042c40400c5845c00e1510360030041c4581814614010340d060103450284040f001016100603408050702092003001c0500190700c8841003800c070745c10070f080442d04169000c031840903000100803941d280481ba4045000348090510f070b51401d040030501d20070303a01c50821070341440d40061440c1d015030700040c441101c0400142c03010242c000b90070041c000e12920080c0000100400b40d0030b560440e2040078095400602001c00c805070b04c2421a60a106501800143c60950004031401c405840406010542c8154440740c020f8444001514000406464440041d44003010400000b1405075002840d0300c1342e485019400c911b400d00221409281c0d10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 197906726 1250 197905476 197905531
    0xf0a0f0b071125230d080c0d02010f050f0708071d04110a03050f22030c051504110102070b0f0a03060503070b030a0f0b0f19080a05030403120201060b03071d09 70
    0x1041001002c0302440300384c0c00c44010100c040b541820455000c03101e009207160501c0940b00e400900c0b4100d0082c0c1001000054054111031503120078101c050207a566001c10701c010b036a4040b40c01c000002d003d940841c013128069480f1441d540105404140c2c96a000b0000c2800d4a8082000803401580010101003082c0d0500c1a81d401c4502003841030740c1400d05800d0100b100729001402e0049132841c07840c400405008506a180c07903917014040e5003040101e811001000881101d0680703005003686641d5a0359880821301c07505951a0311101030915116a80e020629008003d001c81456616080403515940c10010940180101e0800302d0752841c0c0141400140c1c3c22000071704840da400e00194041c25500e0b6400c64021001c1038a1a4024643c070310512580305450f0b0707108100c207020360100307801031010200003001580c0c040c40030310040c0c0780d40d070208900700d6003648941c1c50103140c2400803c0249204580c244642c81c3c00c2c466000c0000d103004000b90440c8001e8810313940c00481c00503915400c01200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 197907976 1250 197906726 197906729
    0xb03070314010506060a170a1d010e010b0609010c030305040212010e0f160b04050d03032403050f150402281401020c0108220807170304050f0a0f0b071125 68
    0x41c3d6172113007042c0c558180544840012070307141c500c95242000040c0c3c580050f6000c41d2803040165106060700c1c0c0303c0c2000c5402801e002302c00310320399400d009120340c16040000494808220607512003031015040d8030128020300010300200d80c410b544010044140720b09025040001c0c417900050300c0b002a10791959440e003404070420480cac0300f06070a000c02c50440803605403001c440090f10394000780d0125103011401484a0000d00b0181e08581410203c172080c3c050004080ea8404e904503406940b541440c0d0741d441040b0310002c000704102400060060502c09019480e60101042c800305560700e01002038480c0045400c84d407500281e0101010040da41003010341d200500c282442e00d540d0900702d44250584c4621a0b99080512031a9418007c110150040719042030b04172410178509814898680c1d0a070307000707031820707903407486083c06e0300d84164004030742540c00c2603002081a1190745203603111410100018402d605100d40c0b262001001c003410f001c500200d04200380900ca0000f43d01740314502c24480c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 197909226 1250 197907976 197907979
    0x30513060c020904120e03070306020d06060e031b0114161208090c04050601022b031d06010620012a0207050d1e050709090510020306010807030506040b03070314010506 74
    0x55008074015850b1801c0e69504503030000505070501c003004030295001c1880381d000d10b416104910b000001d0080c81d034050140251242800d121440ea039100403244040d0704110194550000d0750744007042c2043c1d0981e07124041042c1040c02e221122440e0208040e049554214145651204101e00f080403071000c000180c41036007004981800c007040820fa031112040d0b030142c0a56a20f802080d42d80c4c0c02081003844a06000516a0140c41000407074007842e03003030092110200c0d082c120f021450503841c0707440c0540c545c1020000e265580c81c00c4001c88812100b8004c012500e104030401d5017840c4e50a0007045209404100c46400c0140034400042101c4c080701119800c540120b107044c45a9503076410b419074420740151390010390f45412803201000c541d810200400f0b40c881c01390f000403040440c0d00010504e600072401d440e040d5400302030800680c48101d0700300e80015245400a00e4450280d4010f542105010704001454117031100442d02c0d0060540041d154801c03659490060000240505648505c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 197910476 1250 197909226 197909237
    0x80607031406040c12060305011d0705030a0b040f0f0503180604050a060e06040f0623030c0421050f150a060503030403230d090302040b090f1b090d03051306 69
    0x71000c0e075a4a19581c050030309489680c8503108024414031134040b2170118401d12008001042d500d151580c0242102444410010480012007000000210b40441140d00103409844a41c0301070392501620b0400800481c2c202820012003408240015180003030b02d845540219615100ba40701040d40c54050040303103104180c1004140310540302c0c1905031f4103c40305810400c0100c0d1004001070728074044c9410488207490710500c001403942d84820b2142c40604a01151250f145414400710300c184022501751310600e40170003040041801c000c441c10050305140e2840c2c0301c031001541d6080c2c00c010321366040714034176440401e01c1c081c83c0460000c60713504822201d9040003158503041c00b00c2c0d101d01442c0b0014140d0802450390f1584000c000010b030445c51101c01c1030b580e80c14492a0003a203480c640d80000c0c0d00951903d0310000c12030070203070801401028401e00300b035020354804074120300034074801440744044072003480040300b00d0722401022000761b4400e40b59140c440d01c50184681c540d0520f83c0c403480c204103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 197911726 1250 197910476 197910491
    0x110405160309030c1e0b130305090d06020c060405070906140306010510112e0203100306020c030c1f05070c120c0c120b151012091b0f08060703 63
    0x20140403180411600314140859458014101030302d11002e43c410190000c00e40d044a00b4410403520b130b004200702d01c0360000c903015848901d0324403181c11011f4801408202e08010340d0009103050700100713681c2d5210b54805841e01510b612064204201540d0454a980c41040140300301c7e0b6480c09140c01510b44c2000c42c0081088000009076201c10610a56008a01805501d03480c50b06c5244250b080d02504001c17a03503030440301c035404882d00442035500d24403c2440f0050701da005c80d5a008903801509008210081c2c90b046481c0c01d4002d50044901d1038042c4001c1000400e09002442907449040d0044a03000074200a0340b048030a80320001d10000401040300001c4000800e18007890621b40b1040c5070a164400d0b8524141d95401e0164000d03c2c83e86040000700010408010005031007000e4452040100009100c14082100840e5a00030041140080c2c0483c9190555000d20941805070111151202c41d1503998540c1c1c4c500da0f00a14148442c007403050010388030401c9510303000100e6142c10055103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 197912976 1250 197911726 197911741
    0x10311040b030a02040f060804150902370902030103060b180c1309020f07051c0210150b0c071d100909030207090c030606030b0906030d050c012403110405 68
    0xd1189000d001d0414002102003040c82403903506a0340a444030180560740715841d03910290104100f100c040316160850f054030054204940229414681c3c050086188104a0085900201c800d2240d240d0f6a0000401c40d11281b00407100940042c0100c0c42c0040c0d4039415801d10200b642d041280f00c502403031400c7e014006c40050a500c2031340c070a01e403a0100c0d46401d00b42410390f0401070107078801c0900740e001003115004400700e81d0043c25001e104004895241c904020800c004910018503000580c00015542e480d041194000802002a0403035624000342c40704507051498014848410031a40a0701c0140040d40ba42c1100d00e005408a1014040a1070110201e90071046240139852000351030b181c042c0c08150007002000b01810403c8000d011210412074018003d151a20981002a0503c80c14441e44c0c24500080c1d4003590015001d81b14240141c0b5042c0e405034010b05820000d50b50b156032000d000c00c42c6c14400b10a48038014403a440440c510700f8135503001516800420b00c500e02c2d00051010a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 197914226 1250 197912976 197913011
    0x100302030f03130506071a0a020405120f03030a0b010318031e080c0304080901020109050615030d0c021315080d021006080f0714010c08030c0a11030f03040f0c17010b03010b0103 78
    0x2200c1c41120f0b410346e02c1016142000d078044401c0744090b2910140403c4c00080d64407034009d0410341c0d03400c1d103103001001c0071800011b0790f807848010407040581040011a083c0300703490300141c44102040c140443c01028a1185182c510100030303044d00082e050684903041c0001c41c00340440008501e16060040d81040e0303140094600c03014000818103c00026280403e0b4000c2d001040c0300c42c0c0010581d955441e00c150303c240c3c501c01440d202c5202e80104400e034003180707008460410b00c2c603401828200e0101e407091041001445440514084058400d03000a10b2080c00c115000015100341d004c0d00c115a904014001940c43d6a0060042ca0304007100c0b080340385000142e444102c4854070441c3d842c581d18180140c0320f031411888060b1401d00008201704120a86000411850050360b64092001164080f035944070f00895003d4840a4010008907000c1408400000111405040c01d01410350f59010540b200b00740e20b070829040d0343d4480c0703940b0311246401c1c0f00d8000c0c00d079408e003824440c410024611190 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 197915476 1250 197914226 197914229
    0x11100206070f0908030c060405010b010f0903140f07060f030c110a02010309060b1518030601030c090218090f1506131a0f07030203040306050601031404020d1406100302030f0313 78
    0x402c100842074000341c81c4039014400050082c4815655191b2052101d15156181110705907010340c01c10201020780e51003080307041110511940c551001a040da0745000c00401c01c0a8510740601c5003118a0742a0359050006000a000c140c4460101d14804500941541d40440001c0180300884540d981c4001020416002c100c1d82440c001540701c026241501c001c00b502841d047e004161603443d091006e00c0300317000f0306001000d210100c04000c000e60800d941e841003400010002c03518207400704508080741d00500304050b41800d54500301041ca1020554081c4100d4414102c07007080c0c0300b8040c50404400c0d03c00303111a816a070741c5190001c8502c074210018682d02c1559200c0c00c4422842180d65104000d032178046074002107281e621586424021b50700e4206004c1900c2c8240351802042903980070340f2800700c2c5640d80101c80c118568403a001c110f82c4400151302920541c14001540e280c0b4001401150321454a8a0320480c1d03681c114010b044c94000340070a00c4100354410084101c2c4104100d09010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 197916726 1250 197915476 197915491
    0xf09020108041104140702030705010f1505061308060408030412020604030f110c0d0f1202010c020703020d030c020a0906080708030315090606070803040506160513030224070503040311100206 84
    0x40912040b2000c03400a150b90034080b445885d000050141e9543d012000b400d01c00c0c001c80081c81080c11112001c001c8900c803064062030040980402c10807410160080c195140e401800c65115994a0b001c5a0510004680c100d512220000030482048843d00c800755941546100626403803038544c2d030140c142440803260350b0602070410007151807080104071180074000060411407610000c0d1034030b12402c041d60101140d4401444401908103841441078004080c15507000781241d500e0360302400001040c1d440180d08100d100700c100c02c05602c0e062412001010360200001e4881d1405219505202054200c2d0501b07400410a01c03c0c1034801030b0346c888960100311190380a9444110010340030303101d40103000300344481c0401000148000802e91b548112010031042c9600700d43c4600c1100c452103032811013000f4201c5100184050308001a048113071106101c20302820250001000f803607500b10b000211010b50001805104110b40294113031002642904d40742c019590b810700294841c0002000d15 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 197917976 1250 197916726 197916743
    0x21203190311090d08030702062d0408040e100509070203071505090a0b040c0302010207060801081b01020c04090c03020a06050304080301030f1b0311010f052511090c0307030f0902010804 82
    0x1004802c0c1ca0004990350048018a501141903a520b4101070741d8204a82260250080c00f0000d0042c1d8010401c5004203201101004074003121030030f002d140c01d00702910540341c98006010114040d0b0308043d40314003403980d0b041c0d0300c0c0c0411300d403804201d07049800070110701c00c5402c2030007090002081c107203000440c9050094080341036031f50080750790f240440050018089401c110140000c0c010980a8841541c0c003e9003030b125015195007056444040030320910b00241d0049d540700004001007070303c00000c1c2005105031100441c040001800b1f0b180d61080603034150b01d03c2a020070451411040c624002d10550800340e065241039141c68046010501c4003411400420301c4140c00c00001d2103086100355946908030a10917103078100b103102d00d400060040d002c10004101c82561600032000c0c0c41d02010703040310403250004540f60201580c1d00300c41c011141814001c0d00c442460b41c510f080e41d4030400340760014603200c0c940307104000c0c160345244804a075820b203440d24600141c2d038000c039003a91058112221 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 197919226 1250 197917976 197917991
    0x60302040f03060e0a080a0504090f27020f032e0c0c080f04030b0109050603010509010b030309191203030c02190302061501170702030a1d1806030703060e0303040212031903 76
    0x45045c0030441d800100342c0800010750804a64202014005441c1100030070000d1070003c826110846107240d0110b292a100500c2184000c50050a103100803440a03040005800c05c290102e4078240444605040c0c104400c441d01d032a49904099840e045900440180006c11017136001411141d101840030707006100010383c0308421a11342d01290010b69106072008019a9143d1081c4010042a102d0f00d12079400c04011824856050140710a881e10040107140b41c02e00380410011291120728003440c0c6440d40178400103805000800101405000b0303100402c3d80c9408071802810003403030180481c04a0829030300c941c0401e174006112a4080e0f074081c82010031107035000043e2141240380259002d071030507072000c011241e0703808030180801c20740d5901c4109a121114210b03100d00e03607c110240750048060b9801c801c41c5803d03000c0140d0000c80250603120a65242d8850100340c64032003a0b103082070f030b1001041c003045050050800038284002d00146040030000082d0f01611407a00307850710101602d4110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 197920476 1250 197919226 197919251
    0x60304030908102310050616020603100503010e070305060f18010c120b01110c040203071103030406050601091d07120b04020d0f060f030f0b04080412050604020307060302040f0306 79
    0x200c007805494071008440646181c0c0740410003401110740200c034112611404e4101035580c464101d4041d54109840884103428101400010f07000a41c41440e04011202c0b80070160f181c240042d8024190340c11880401c3d410803044c113003903a10041081010394401c100c10004a000072a00503080000070240c990340303860706245606c074500200104200c1e0f503e0580344200c481d800014080311030151030001e0203d250108019505001004032020894015050141c0b0b1031038190b00031a4454424105014601c001c4401c440c9103400c212421130311181e6031014822190f82200d4040c0040900e09020300c0d100c0040c101195010401400c03000038007800d08030042c00680190041026944050000c544a060180e100c40160800040400800340b520001181000425600c0c1d015a504030106e190000d00315a00c04620400c000c0040d1940c5a05000209640148130034841105014130001c018508050040604080faa580030340141841040100004580303549020304880d00030000080b0300e0304802 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 197921726 1250 197920476 197920487
    0x190b04060f091a10020c0d02131e110f09041a040f0f1a0306010312180f150207080d0e060d0606020105011e060e0609030102122706011406030403 64
    0x801403030301c500102002040007a0958090000f1021801c05420010318039824000303400026202040142c216400d10400d82c10081b02c0b80031500d202403e2900f4864072503241e0411510314410316000c0e0550090550b20507400b60094628695102684615195080c60080d1880c816650800e000360313102c80c6818042c4042c1040c40c03540c9500500306001094044251070020000e0210403a0200e1500303440c0003900d4000186524445c0003c0d000300302c96400c2d900c50b10403c2c19805c0300c03201009680208504006c9030080c0460080c41b41d00c442400c424180329044114240042108003198441c40c0d0030010030000041350703007450055040c0003011407140d0000c1113240c464021841811828800c0004d0040c0c0d055105604a4020243c0d0b0405440d10000d2104803075054420400021415140c0301d1072483c00800808248100a00062420604003000344008804440d050306043e00c2d44072290803011001408044460036402403d1158186000c52041d500d040c079041d400b07424080000b1b000c250042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 197922976 1250 197921726 197921729
    0xb0705070506070e041505060403061508010903050406030501090506031b041d0a0b0601110c010302030a02040e040b0a0e010b032d250b18130b3303190b0406 69
    0x1400340c03002d900e45404040d10682403180e0240c01345282900f034601d511650769609050b074100524461629195031200006401c00440840c13400040a40006001c13100b4454050b800c3c0c465210b207501c4d00e25181000d0102c40f016401204003e0902c4100030381c0b0781c1e0102d80c40000700248980306201400340404a001000c01090a1042102d0301c9400354810000142d800a103030302c151342034501075031420011605440d103080941d050741e008003c031120541c0031b6006140d1044404a0041c2820749d603464403130486509031401c1d5901d20002d002e102450b14a0300409941c0c43c00c0400a00941c14641c010076030b41c483c080500401c0140a080d10810b040c80c094004c1b0411b4030784011070300c22000c4121004094070806088060080070843d0000d0b401e01c140041d180c4402c040c0c10241c00d42d158860622050700c0e402e0081d42c0010b0b9403510308426981e40c440810b943c0c82510901c4042031000c80a11002c808412059603850010034410060440c0c0c4500c000d041d05c10111001040062202003c00d0246c20b95 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 197924226 1250 197922976 197922983
    0x60f2c160f090c020a05030406081504050c0310050a0803090d02060c06010312030b01020c150304050129010306170309010c0c0306020319050714310f1701050708040b070507 76
    0xc000340000c0444400040e581540c05080382009000401c60302030f60b8400c592034004040e50410b000070418980556074907039016201581c94214504480006422038004449240d00c028000c13007805920001202100040c000c2603921160761402d101d5035035624010209107500c1810400011001c64540000380d402503007060301190300950b140c2c0340c500303103000001e080c0e280080c0c9410302c0000310b51b1002810110150300a850f404902c01d030192a040740e50703c021b00c1520651740b1100a8103004054000001c24101440510240c1000220005040d24540d500206010317900c507800b040c07a4540441250301308082401c210348010854505003810f000b041e4000350003540f011003000036000800484024040c0941c000708155aa0350105071003410203401c00c10300480301804040c4a016140aa200d14048000c0090168070486040008104032a400c00407480724001c00030030481d940d080300e82d1801d6401400030b010600c1c122000402c0700c0001040601000b10303803000300d004140107008580e1103d80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 197925476 1250 197924226 197924263
    0x230c06070501060810020708090909010207020a08061501050316050c150106080a0b04023a0e0d0f02151f03080a0c020f100c020f0a12060504060f2c 65
    0x35041c0140205030b14071410000d405500c0141c1284c2c43c1500c02c032a001a4410945420404000c0c180a5103100040c40f0805940d03003000110b02580d20160b6510041011000a201514203202228681d900e09c50010f41400002c2c82800480c9080003086600100c1a01e4020b0316400e640340218605030744100740540c415100c81c00425400e0b03020781203520030700e806003040c0f18080c050701c184012440340791a000d4100e60741c3c00d404102c280c10704c1c003aa80f15101c141c40d40c040c602c0241c01000c02311803506010030503940c031061000403141d4000382404a020002d001401a04001803012034001300b0040c000007001c41a40c4c0102d5039009500b450074042e43d0031500f60f903250000c500b000351a0340b0141a00340d216481d045001009441d1100319503000505c1e940d224000c80055900740035441c2819040030b944884941d0300400c100c00341c0845505500d0141d100402d4904140c14982d00701c49440d10f60521316801d003844100d000c40403840c01d0f88106107070324801c041002c46000341810701e075160070141101036 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 197926726 1250 197925476 197925487
    0x105090306150117010b0408011b02030304020103090606080f010203180606090705030a06030c33020d030504020f0303030916151704152c07140603040c180e0c0d230c06 74
    0x82c1d90038050002da80111000b0426140810018030505240ca0114ac0050f4810000140154801e800c0140041d1144d01c01140d0f09031902c200d1800c2046940031202d541e0760110410000c0d011444000803259410b00103483c440c10701a01086110034000c14090030f12800001140f4020282e501290007590025640f003a40d5860b003461790510140044103403c141405928035108204500030040301c03100b540c00525001040703071401e078007600c002801686c0c0442d60300b04890f0b540d1000d10040d0b100c0c18030072020b4100b0380103590780700400ca000340d00f10031140029501880405500720084c84100c8050340d0320510150303a1858402c1e424034040d030094184504000c91105070340c1039050202e0380900201071000340c010034045210703940d100381d1180b20464210401c0010307450510500464015004162290b03076540c4a42c2c3c4400303c1d0034415401d40e5142d6442d007031505590001d00c4404112001201c0c04680b0002c26151080e940080b4202c21401103103400d00c0790150401005001074544000d002c2c0307501c1d40e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 197927976 1250 197926726 197926739
    0x309061201080607090e010603090c090501030623070206060105070618030806011412060f01110111090f0d0203060c03070216080f0c12101a061306030b010509030615011701 76
    0x1030001c0c80364403414410200440d01d26800394210609a4404c1d211800960307180070011000740c4081101522820210701c00401c02d8030315401202d0282d03020380b0001c180b40750b202c0010040d10070340301000ca1111b00c805003440b034201da001c200903400c180d091070207984402460a04074010140d04d0080341e09180b031001030000305174000508509c101ca098032440d03510071991240201c2032203005401c01c10400041c0c000f5000f80740004858981010602d0280c2c80000c1c0401c0c118211040441000d00060f00424601c00525020880c4040c0102c1070302c4104000c0c010b079010942c1c3d160098280c161584010001403040c61007005101c0003044803c600302451991030f03544545841d001c1030600340c14000d01402c0c11403410302d40c00d80c0780c00b01e004000422000800d102c24400810828400140408100c04100d96503501d941c041c0884040c00f008031888c943c607101010b803c50307210003081e606104080c070107100303280d50208440d03502c40040d0b13080b02890301120300101c41480c0c94111b4103090962080011524 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 197929226 1250 197927976 197928007
    0x18130f0b011b02031207061d0703020307090902060306010e0301020d06170d020607050d0507053a050c160507050415031103070302061b10020c0d02100b0d0b09030906 73
    0x10303410030380b1614490544440c00141446030441c0180d095400942c0c07001c5461800c90003001c490780102e00011310302c40d294000e1508840b4603100c10580b64031400040c400d602e0180300f408014181d403c2e0400c02e21880c2e5002ca4054080101014107200c894030483c4016203003901200c015501b12a8100281512100c0320302c3c801009a01c030040d944030f440307a48155240001040ba00a146944500e4140340c2107044560140c00700800c80e008004042c0110301440c1e0516076149042c40c6158030078064101c0c8500d5850003810f1440700d40d60104e0420051284c100d1060701114621485c1c0c0d0050086440305040c4680741444a0340807a4006241441b9110a032000c000700d1420369201d10b412201c6680f00008040c0e66064500010303501000400c0443c28000804059240503007000c0190f43d01100d20212540403604a6803035841e007a0091240b500403da4148410450741035106002c0040500400216080700c203020402807081d0140004101440c9040007034030a1260020013081d50340c00182d105848 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 197930476 1250 197929226 197929241
    0x20a0801020f1c0c09151e05030403021005190f02070803040606051311030c03220602131e030305070206070c09060e07110607082a040f170318130f 65
    0x9445860815000342d04075001d1135202e00c9240c0d5943c0104d03410445042c2d41041082560014402100c0c0030514011102241d0348401d00d03240c0b101903c1c5d15181c28040d041c415810342030065140fa200400050061b140c001ca0b454100303983d0002a103001c1100400000e108409004d8000b41d00072003040204903581d01300c00c003514403e40f44c090921404007841d001387c0300d443c1030210705c4420903c00142200440800b865004015105040d071200001d25180016201c480c0d051320a1900000d502d4108a10301d01d00030001e00b002c2c5941a419018080e0308000046540030080c20001c1c00100c9100f90360311002910507103504000b0500042e541c1d403c43c5002454144984102080d8002c0020501b41c051441c0d80c2a504c1e9030406002c040e1348410046407031103801800d44000414103e0403107222750060700c10400340c0310740d02c0d076503980c80e03081000302c103001862a0b024103141c2031000c0011000c2030b008410341d0160201c81c000302103080c202500140e0f02d800358046585c0798a14052168015600300d8110b0340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 197931726 1250 197930476 197930497
    0x1090504020120030702010503130b040303090c050a031502030a1103010605040608011221031107080306040501050307180b0103091a1608091504080d06060c05070b0301140607020a0801020f 83
    0x1c8041210f03062500b29400c6041c12000680082c00810b0155010b6002540d101d58610841c0d07040c480c0a640b140c0011130103030750950010303036503020803000c00580c82070810240c001190968550707480c583c1c480c0b1004108518070000036402202003031005c00c1a4204000224600b101d0a8aa684500d00200550498800c042c0040d404000025004104a6510744059004201980c1c01e42c1c1f1312020010426080c031a800030551b6032410003003040c0142001d07001880c41410560354908102080100741c13441a04090b21030341040c4010440c010200f0907400782c10a6609010601110120050f002020100b00c09040003126594844811080050151080400408442409480d41000c84401c10101c03003c442a5100e1071001c00c0703074000b017001c659110780701c1d140c481c0c40c10904981c1d140681e9580d074008000308220020300d0f01000010301c0100068a0160041800d540c07415841da490340400e5480b44d030146c1400981d48044d0340710424070001600300c00009641d180714040161955912100c1e014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 197932976 1250 197931726 197931737
    0x17040f17120306130b030c0604090e0105060319020112150b1213030f18050a03050f0f01020703170603100504030908011503020d030e0607060c0201320f0709090203010905040201 78
    0x5101541c015054074000d0001400e41e0300f00351000720001008020b9a02c0d000c0d854803424080121503903813030000788040c00009801041040c41506800d0940718003610300c0d440303074024141040b004c040c00c0c9102100c03182c091070040188082907103698000c080c44d1a503c031041e03015840c081803c050303041c000c10901c023084403142d4903559540f0407212100040c01d4000d0024003166001c84030180302d007140303944400c01109041c80b4140e071503000480c11035242d07004543d1034001da0745030410504180801030a000054009500c0c1041a0750020440009096440c610700c620b2004940c0b01d0701c2c00c000000e040707074907144104803900302400c024080c1c1e611881811103540c24180c80259203071090550f0340807640e024040d40c2c002002c59401303840308040d680940d50085824003040021032540d019161205a20741c000050701c0ea0000007040c1c0d80e5111a540310301408524905040340e9580707454141e030060b090300101c000c540354500112059119035011521050000c030000c40d03101d000303070700860186100340c807507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 197934226 1250 197932976 197932993
    0xc0f03091507030507080a0203100509090106091104061b060e0d030e0606030307080403060b0301020f07060207050c0a0806060405060411040323070e0106030f02090a120b1b0717040f17 81
    0x11004d40fa03086071a4000980c41901050300034007039402550304212201c2c2d40c01d0343c0381e07111001709509003401c440c4140c4681d1100300400040c291840341260f450040c141c0c132890030342000c101410384510f0a03502c2c0e03903501d164070318002032114503440380d0324000180042e521001d0100c000100540341c0c00e0300c460043d001312004516035107000400c035507125a01c0007007507040c01c1c80c40d12480d004203030b0301d2030aa8065408003c0c09a14207089801004282d02c00c900040e203070701584c10f100e8a4001d0004980d405061081000e20400e040001c070203511003000c0701c001c00e2554402c408100906445100c5240188011802004020903c04001120000c071041e48981040c0c00c0450780d691002840740403801f040f00401408030354800d030000c0d5000701c0c00d40c0c405440d16826101040340c604903503000761031030709005050307104001b8010b0f0b1654000e00e00f003140b04035010040045151605c50030f40020320f080c034501c182580b1002480160390007092000d000003080396031140c1e03d85100303501c240c2000b058050b0500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 197935476 1250 197934226 197934241
    0x20307030203040204110c0d05090a03050703080403030f02061017251d060d0b0c0405030a0309060f0c03020d200102071112060103031b02041e061a0903030307080c0f030915 76
    0x4c7d2051000850002d100c0a68014015206507100d2801181c010f010040c001c4003140d030401c0010010b620524900703036a9465424010040d000340c0400d4000c41d0080402d001e50000030341610000d68020200c4a40c000075140c45152070030510842807a48041c011244c1d0203128094500e0804840e050070784814241c3c08265000c1d004501100d80941c003200f07105220010882d4686980c0d171000e40809c1c031500d0103031648006450203001400440001d04e88007424031003a0381c0502161080d0280341400e2801c41025030f00a51144108140641007045150090aa0f180030600244504c1c00c0c0100840d44c1e0801070401c80e4031220f42c0b02d2094009d03034403401e0070305081a0004034a4100d80d01595a00150040400d80d50340007400d5040aa80c410b031902e901014212002e11200f802002c1c1d10400544103107022802d034210b1350100d1900104900c18045032925840c0403007200c7e4003500514182c1415071310203a03080180d0080e03000f20b102c014000310410044690005e00d5201002c880e03842440150ba03040d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 197936726 1250 197935476 197935511
    0x31116180f05041a100909060c0f021903080604060513050103020f0901030515060105070b0702011409070e0613021306020304060e0d030c0605190c0e040c020708030a21020307030203040204 83
    0x50300101105202c41c1a07440b11000c684015800c02e41c5174510001ca5a5299122410b48040110944d442170b541d007182120780e5041480b000109813580041c0a600001c0303640c4d100c20a01ea0f001c090280800c880000d8082e554503404080a014000e0502c5003840000c00c0c01e00040600740412800740c0c0384d00f101061035140c4085034904a0754041c0042c525001085c0c00c40303024800190085040c070030300740f0103440001c841c1071803544901c2c3d281c4e00008940401c2c0480001c206409040d004544d08452014000c00c41c080398001c1c0e21110a032115070542c420110300c03070000c2c1700b04e8890344000203000602081944d40403000b00102c4500d952601d00480d07203a410812403e003845401404100b40e00041d10005400303410151b44264444201002d10b06182081c1064a03c082d45440c001611440c22103043e1a2074441c810100300a8802040d0050404104650324441c182d04c0005124000f6003200d0b00e0410300003001c17405529031a0640d22818800c1c0060080d41003a14124407481c1400300000480b001071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 197937976 1250 197936726 197936731
    0xa201308030c0709090f02120a0b01141c05070308040f0609050f09040f061d0708100513030809012702010e0d0c09020f040803071407090e060103031116180f05 70
    0x400141a9040c50444c0d10401030541d24001c84856038021100e1026a45c1c143c414407625030300802411000881c6e02d00070440340d80507006510003050010268020352030381c40070241c0e003200203040c0302c000448034182280342104503800148040c03400034001c141c004050945074100c41054407950181c0351030b24100b2055840407245550090502d90005010481c0d0802a0056038006c43d0b002036003038444001960f003030005c102808130541c89050308120000707041058020209215034200310605210001421a60111402408214551012442c20002940a80301d49040f824a58545400d01d4041d0303c0301c6101410b0582c08907a0601d1803414a0901b010040c1010b0b07400849100039a081544540c000d421080f1a080c100b90144804102200100010441140603402c01e03103074021103002c801c0c034000280e08443c07034041c20154180f0b022100015990305403640740c02d0071400c225a81c404e1a141484094010079140190710000940042490309811440e1002d202407018204020713900c025150203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 197939226 1250 197937976 197937997
    0xe040f02150307120b0621060f010c0210031e02070f0b1e010b0a02030c100501032d020f06210612010b06030c090f0a06080f07110a0b0a20130803 64
    0x10124132008644d100d82c004060b010740107080f5800d202004103400c0d00484040448103281c3ca41105105240c13510303100d0145180024a0034292002003940480e0f2124600d4034103209040e01c86d00c958103d42880941840c1e00462000f00319140c1f021810103400c84245d01805480301c014a8010407004100c41c9248070359070070012078881c4581d10f002d00c14007065011016002c00c500060000648842d401e1203581c462458034480030440d175040d410203012558088031034205007041c07046100e80c410070705c0802007401c540440b14001c0542141021030042d2252101d0901c150500240801003100b070782402c940074540c290740030b204450a422002e401c80356046842544000140001850240d40f28000d2011503000b8003125081d400313a20104002d10707031b103405c0040030440b0b010411040c8061900055803210040c80d01c103803030855030221562118105503010744071070314400000d1030100d0030342c0051540300480d090070440b81c20400744140154118003001c482c518a403001c002907100000081e40c140701740 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 197940476 1250 197939226 197939237
    0xc02090a0606030f1b0c020f0604030515011203140a050f07240203010503120906041a0403120206040209040201110109050d0c030201140709050603070201061208041e06091703040e040f02150307 85
    0x40c0040c4c03c0c0e8108803145404c2360f20854204950403140c81d508041c100842c411001001482030451030701e40760716816085232101d816411542c2002c25800014000400b140c9032107181d0315400c00790212046c6c41060f07088401031000180c7c0c4010054003c0c03c4000c4070804144890304803040884034410380c4000e2180360790551102110580c041920801001c5003000140400e06c1c0c940d07203600c0c410814511500c64808207802180030400c1c4244a406582e070320299202030003107403030160b00040c002c18000d071000c1c0c10403200c1e00c04184e040a096006103a0180c00c5030403544942d0300802c0003000d400380e42004900550910303241b88489200b5084032405400e49483e8400e01c1070402003440069003000f41120110f649032100010b4000215040a45441c080d101507030343c90342000400c40a004840343d96110070755902030f0400c00581d2000c00751040c0e80c2081c0e070802011280800da07610b507001d1034100c44580390310541400204551341d005501914400c2e20000318420150110203081d02003100c084000c43e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 197941726 1250 197940476 197940521
    0x1e06040f020702030106090605100302030c1e13081014040b0403030c1b0f06051602070504180206031e06010518040f091a01030302012007020f010c02090a0606030f 72
    0x150035081980148081200107040448540004e800c0d52013a90110100710b40e030b06820302082c201110603e038600090b041c2907265041051500c00d0620a08000142048840303c040c5010342c442d004442ca8900c3c8080e147c17004540f11402503864100340700448a402e458906054521840701103154410758100300b05c0141035803161003d03000342803440c80c5807080200c0303d60300354540c480300c1040c101c0b158001d03a55054903083c140341c0b0b8411900003031b2501c19140c01c20140c0511803a80000c1c0c9030252041694003094516171002d4124801c12541d400039404400401013284200c0080d0b103002e0f10313240003141407003981c54000040d11144a00c042c40044481911082005030a250700300500007450071b10f0004408031151a00c48900703940c01c0511617103480d0a00100f0501d64240501441018804500c201c50395440140c000203100d00000280560040d07a026a4940e000e5075031103034800c2e0042c2c048030080c6400700071300c0018809405103002082c03512158414411940c40756628071b8400c02d140f0300112 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 197942976 1250 197941726 197941729
    0x40612050601050402030408040e010e060405130f11061b010203040516050a06031e14060f0108070c0201031505090405030705150c090909010b060f040f0816170c04110309061e06 78
    0xc6d07000510617100d0840130400060702486552030140244271a080d0089c09080c424104000d5510181c0100c04540000c003403080420702c102c0824030790740e5008802001e03000d260000b080c0a4050050040e1400960100844103c02c040d00298455407103002074904c2c042c02e400c8110109c848900030503070000080d110500203c0d00036800424804038101403004030205071140c0c08181e80e0580442d440d0905a0418800c1c1c07410f060300180c4001d0800d0801c0d200c01c2c82d0442c1c0003031030b034048900003a0402d0b480d0355001080302c11446444c000341a000d480444146003a04103142d0307aa06c445412a801d21a03001c0304c10320381c1001400c16015443c1800007900d801d203404100680f50102138090202950780e40690209581c4880041c000000a10001500c55107080c01084c0b130741269034445001c8c2e41025104207580b020230001401038641d1800c2c161000c40074172043d103142c0304180c1c8000e90440e1409140e44460541034028620416035442180ca0b555079140d20320300781d007981c0d015802e4140c1222003c21442e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 197944226 1250 197942976 197942981
    0x170105030a051f060302040207030309061523040b210f030a090512010b130f0605040218091b0304060203100b090d1115041706092b0507020607030e0406120506010504 73
    0x7240a14072000c07070042c0e11781e000a0304070392051504a0100361794110310002c03c9528004e8460518074406500d02d0a442e0400e0301016100354521040801e058a14541c841c1c0d0380c42e4011500300602403c400c0c002e00e9901c56071007c40c42040c1c40920184907030040720840444c0002103840d060400e94940c07010510300010f201640c0c1c040c20a50846540750396043e55651203112424110700b10442d0301092501c1288a40f4040740c1c1c2c65081140114010400840c00717501807a040400410b003a540884030b44e980c3d00949510344030401280c0f59087d000002e02043c0403403a000365001e01408802c881042d983c90300300300719520503010416040382c0c01070440c101180001084001c07c1d0b502800e006401180c550042e03045500a412a00c2200c1061401228007a420000c1c1603200c12620024121a080c0304080f5075008000c07411281c1c064442000480b03035a03c070724141c0700d10036070181c2402c5c0c50b52401d1801501d400741285290303005a00d012070019541902910040105401c80040c0400e46d0030304081c00003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 197945476 1250 197944226 197944273
    0x150503151b13270e0102040605070f0f0b07020318040b1804060209030a03050c070e01030206030412031424010206131b210c0504022109120307170105030a05 69
    0x6040030480b0002e60403001d48215441804100d40d03100c110640444040129100c01326191a540c0c4188002e028164011080ba0700c0715401c6130780d5452000b00b6107046c2101685000c0e000700b050a604050003410f40d00080a0140440f41c080328001c000c0740001840200c400d4403020590000d40b480f02070b0140c12080d014190401d010301005440c001c003400120307150001c200e60890006100040750440041c0520a40014004e03007800310495514540008441b404040c10141c0b046003003545482d0014002c0d0301c603070072103006800e01d020b040c0342c5500c400020605484490001134825120799203150300c0445e5051082e00f800d40c440004102075220911101e080d1400001c01007000a00402d1714107411204030f404440800d04065441e100746070005840382d403640b03c40d0085005014035000d110034540c05500040e03c41c00104e195a0310940d6480ca84a00200e14840b00b4600009011615500c40301a05c0500401c08801303d040c2da0300c00a15642c0c1200b008081c01c00e07000300d0a54400c006080c8040368 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 197946726 1250 197945476 197945497
    0x9060d021c060b040306050f01080303160203090904060603050c0130061d0403020f07271410080c0d0206090405040f060c17010603090b01090f0f150503151b 69
    0x15070020039800076070101e55a54000f02192000400d003041040390602517141e00c03910030007da40941d4901040036689000161090198068440f5a1411140300b00240c0320340d80070061001d0f40300e0909003044401420b80d0300058500c3e00510110b84160350040150304400115030410382c90180d07214040c0da80e5000c51130000800c1350340b02c00000030301c4010b00c000d4031603410501010429904061030080d1514403051100d420b103410484081090a20101320702c0c0510041c44088001e203001d03481d601c401043e6501c003ca00103654002409603510100c02848180d90404040714082c202e64002c100304a20b0313200000750300600c208036007500740c00c7c90b40145da08180b00f060b01205d035002641d1840203030f40500c400740000078040708000109040e01d00c14a4014549400c0c00c02c80507482e80c0f00c0c0305103000140103800c0a29120450800004000d6008140740410a0020002e040300c2c0440400040490720500c0c0c401d124100030140c25561811105016140b03210052203880110402c841d081d0b0841c40420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 197947976 1250 197946726 197946757
    0xa0204091b02010608060405191110030c0f020312361605090403020a060507110109080705060a15140f06040602060702071e0b030a090618060f0209060d02 68
    0x144a5140d802600300500c1c00700403400306007504250003400c403440c644c049141c1c2e40c061014003011170400301c0c034117050001d9120003000c03450481c100360710a00b00d50b100c0c1d260004525800c0181c1664180e00582604000343e444002e098043c0c0012a92401911a291081150f02000c42c90100d141035080d688900382d903140b074400d0880142c14840124503034100c07429a810984150041d0350b16001840060b09040b1042070450601d9280207603580000d040043c0304607070364404035070120b010790325604142071068000d00419440b441d116600d80c0000b04203d5241c882c1601240010805024a02a4940b201003002e2121303e00441054070041102c3d4281d0825411948808941c071020024006090f15800508050404140003441c001c011b50008500540d4044032803a911064950b075800c8651407205a5265224012604001c0c01507140c0201980c2c40d01200300c02d03610b010000443e149001e000101300400b544102da0007a4844c1081c0c06520210401001c110400c03180c0c007800c5040e1856251 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 197949226 1250 197947976 197947979
    0xa171b0d080f040e0703020f0306010813020a0b070606050405040f0b0a020706021306022b0f0512090606090a1803120e0f030d0e1603080c1c08010612020702030d080a0204 75
    0x840000c2d51060010001050002400748a0212034145590704800280760451a001c0049200c05543c00060011410003d038540440d51080c0d80b1032000d01c42540040c00340454650b00e0031206030b90b500c00002158120b040c80c600244a02d41889118810703904200c0c12010980c1c0780d994503014400080070400115400e0020a004c83c00d140301a12201d00c0403201a810030f800c204001e49003103405255940e1242d4000380c4040034014040c40850008402e0030201c210452840007607445006510003110385085a200300460040f00203255030141c1d80640d401381c665203805010809440300510040e50072581d100000001910030100180442c00e03c420009101c050407040c00c1c20984180c0c0310580c140d20210301418448520720865124030500b80007081d500c021400003000c610f8072440081c0407080701091100580606004c803250400c461070550001c4401080e0243c0707404000e00904000568014010131441c00303138800c031501a80c00030020045d06001c010101e030310040042262607555000d000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 197950476 1250 197949226 197949233
    0x3030c170907060306050904030e0613090207050c040e06160e0d021207082406062104030201050403080c040e180f01020d1d0d0c0b060402070b04110a171b0d 69
    0x22464091051507024124180c40c140b070007000d5605681245128013020000d1000081d04915101002c02d026524162030716615928415502e00740c0d4400103030300c1c3c00000c0d66001c0090110b13225203051002c540c1040180c4111030190340c0c51030111900c120096040300c480a0640c051011400340e0b80300200300d440720030156408214041e01e100000a0326921034501407100b03010510400c07900000d541c00b68a1880303900c003500f05c40008098012070159200050085412403070405984980c0703012214071019080502d8000c0c006c040440e0203400140c03c41c00407036403184507041107038112503000060a6540d100c030b0800c803010f0400030008201a100e980e40384c460301130081c000740408414413080010010741c4a010103070004090011550700e6001440300601841d0050442a240d942014140e90b1503a210130100340240f15040000d090210040204410425a0b0441030b015601c141d602c0c42c1c40d26914905c14030550a5003040390501d0708501204105145507032074114401000400709040310702c0584 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 197951726 1250 197950476 197950517
    0x60f0705090a0b04080a110f030703021c06090503132103030510080706200c03030304080714100c110115140117070816090501021b1f120608070e0403030c 68
    0x30305c07160303503504416140003d020b0440c079600c5030103c054030501c8464000030f00103900ca0700a030100a1140c0d05056138259500303001c034114544160f12240420505400d810441e580e9006500c00f001c45c0090050045000c00d51035140c40402c502d0034000614450172030b50150080c21700204075500d81c0a0a0800081912040184000501a54880c5251007181080b52030b400f810000f20010716070b101d900300355101d850010480e648181c0254080f900d42c440307480e00100940ca403a0803502c5034441d0700014051340300c59904c0382c151114940c96107001c0307110402c985401e032030301c100c1944a08c0381070a2081004400340c6400ca82c60500502d450080419809010000c0c07400685480c00014200803c01009031002920a94041e005042c04003030a44bd12000070740e2941710356400070000b958031880120356210401030071803514420444c00304500a043c8001d0101c030721050414500d900740a0005000000030a180058803122100a03140360360f5070310181d01403f180b980714010030440c84540c910f201c1c00003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 197952976 1250 197951726 197951729
    0x5090c1e0c1905060708090a051b010906080f07080702101a090609101203090b0c160b040f0e090c18010312050c1009060e07030b0a0509060f0705090a0b04 68
    0x2042140c407101080d1101e45400c051070300007054500740c0b15803400480c4000038625440851450290005c0c1e41d0a90107500301500b1840c000c14501c60076004002d01640c400301a03003281c03c00c1e6070740307004d055403080c048410443c2941c81a00540d002000311f92070522032030f0501e50000355070045030301c2a01c03080e00034022681900482d1003c0364800e2502c0d40340d450b251245541111044800f04101e05100300c00c080040060b201d00c00110340f0b09448181014040c081c0c21000b07004c101c0f5139941383e45400c04001e44400345108003080507440e440011642ca50b4080595065801c1541a1709400d42041e031031182d06207000c0c0800f60f007403044e8000ca4a01d56204400781100e0b03500303042c0b003868a5145261000619000c008600c081c004140034038002d9150028a4181512140e83e020400c1c00903420700030014422192101c100340143c4202009005a806055003e044041c0d000c00055071501080c07901da1000f40c41e2100500007110110b99082d01c1540a0000000020102c000455440c2120526a4000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 197954226 1250 197952976 197953027
    0x1104050a0b031b0702010207120f02060f09040509032b02040302030109050307110d0f080901090e010b180307060801030201180905040f0b06300f010609060e15060405090c 75
    0x410080f4030f110701c408000005051003401130610250b0390020351615060300484240c0e1010751840403d0000d030803103103481c81e900170b0306550381c0d40a850755032400d17580042c80c0c41e806281414080703800468004204ca44910040400c1042000c88002c00c483c5e0008200300649155000e01c40800540d4082c401e002006110b0350096548458624000001c0c0c82100032051080100501120106034070b03507c0c400764280e2105106039622803c2d00180e03030401087c1c100842c01021035001080d8481c2d6040184409030707050881403a070842d00c10070150765035020300410340060264001000107500900c0c0341c00d403d5411102105400f51075035560821554112801d80e103c44101d014941404203100710107401640a840c041000c0750201015016488081040d95600b03c001c00c034201c24403000d100305203000d10200002d0003802d5035101084041c0544c0c1c010724000c2090000820380c85034041001c0380d01c05034054405801c107490601004a544001006200340359010860605030104005031440382402 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 197955476 1250 197954226 197954249
    0x190902030102121f0503030403020f06070633081507140d050109050906060a0e090709091101020106150c080708070f0f20030c060711060a03060914040201050d1104050a 74
    0x13407040c03090307200c4a6011800341d0118844034090200717880100c100c030305581e0160b503580481c5071100003094880c810148050301c0030b49400742f042d10540103165003e8ac030030540a00b0807560f0000b0101141006100d108019540c1d009540001f134000c0c440b0783d45688010340c1d007030480241408200e200c06541c03040894041c07a42e0358000610002d5046c3c400e894100d07110344001c008a190150100340b00c1407040c02415040340382000041c20f1841d0400c8041d010f442041024401c500b0217140145500020040070307400743d4203005c0b0100d800c2041c1041840e44510990f04d050034480c4035120058503620030710007550384c42020003100010174240c00400d1340c41c0340729170781d20784504400f800c0c905100f0480f81c60240d138203900401c4485143c0d90005005480070011a955542c1d86240e00d401c90b59a500380c2d402640004010070340707200c419010791203001111003800e0180041c0d2010411680319010446000307001c5001806184c032040060307400070061031176412040d0714082e110400613034580000e501041180302c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 197956726 1250 197955476 197955481
    0x4230d030605031e100b040f0905100506040905070605070f060e0606040c02010b030304030b060301060e070c050c030607080103080304061401121a0c0f0d0f0c050c0c03060f19090203010212 83
    0x1410000c0c40118090720402d204603500c4c2c803007640e440d6601282091801601c03025068a182c5d501e910400d42010215002c00c4504441d00c0c1090300d40c00c03542c02500d201854007001440e18100350090011103039220780070749a040c0c1025825207890f00918810790342e107207824030220000755140c4139044640b10118002e140e03900d41641004152188400800e04690416118060700d45001003640e043c0c0758000496104c0f031361000c0c04a40180306c580d03c085c0c1d5948014060004084c1c0000c0919544c9001303800340c5807854085003c1c55500e45050301e90b040040c0034880104081440c52004c0d50300144180d41c0442d14800d5210304548004083e04400058001d0074a0881003042e0404142d0490350251074211140c5480b0003c0d07001030050810910b0074000004001c2103080b06603125a00c0c50302c51810401a80c45200300091082d0082140a50b5501c9540038040f6540f4000400c2ca114100b80c80c0d61103807550b076840c6542e10303d25401d0040300c04152952002001680c0030f0014100c1000320200c42c04452 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 197957976 1250 197956726 197956729
    0x20301090b160c12050a030e07030f020a0815010303110c0909030c0f0601120f0c1503150e090c120c0d061407050c0a06180209040506010303031d0604230d030605 71
    0x40c030100002c600340620302c81040300081c0d42c0d8001d0358440825040c40ca03181c15440d40141c0c0540000c03040320400d402a5280841000941c80200d00c641b8000c1d50310031700d2035485081050769122604e49030300060131410300410000e48540c84c10401c0d05004030585100d458044086100480c080d10307410219080480e081c80e5200c4c00300b08070fc1604900f20010401d03545824030000205c1c20b0301c00080c20003081d0707480000c24090884604402030203080c0180310014403e5000034010304a6100000c80301041f80e800107070412014410301c2c0143d60407400b800313401c1c0f20701041140034140c3c2d042d010308a01405540009a42d202101c0d0940c49000328408118164211081040d40320010461001c0c89414061040d80480020301140f80d01ea01010000c1e00140c0c04000050030120110003d6001700c640d010042000740205410b4100c0b80300341c505000407a00740c04c2800282240a005c1c010781d600c6440050007240c00a000e503070700050003803503002c0076540c19442d0301e04154005211001103501c0c1d42007040503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 197959226 1250 197957976 197958001
    0x20403050d0f03050c04051806040905070801060510050901020c0d241506080c0304120509100201090302060604020306130f0209030102070c030b01060e060304060209150a02010b0a0e060f060a0c020301090b 90
    0x172807055072081d4506030030306001903222007645c81d455240b00550f000084040c0c03a10390088480a400c1012100c6813940c1d5450f46018181c5805000e00950300c000c1050b030740d640540207036125004160003400d000c0308000305114214002d55004d0350404001043d180791b2406210001d2501221540c000ca003200640c0b0741c030107200050398050020000708004000340b00f9410b03030540e40c1180d802f2100410814908504039914068400a140c0c0030311342440140095405502c1046854420380a9600036920502040100c1c04202c0d000303900b041c015101203903c2e02607030f0312400c4902c54020380141401010b4001c242260001070341100c08014000c01841802400c021140c0140441d1a18003412070403030380410300030301001d0402802260085070110051760354040c000d003001080980705449004c0c0900003406050705074030356801046488004590030441e42c038a280b007484007400800f01d03000700c401401030703a030f102c40c82503010055034400d101c00603982802001c6119001300f00c40380a9080c19401001c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 197960476 1250 197959226 197959231
    0x60b0409020a0306080a05070b130f0b09180702030f0904111b060f0103021c0201030b130f200403080901090e04080d060506030609010e0601110a0c15050f03011206020403050d0f0305 80
    0x2c05d40c0c0644121000a0780006450b01520100c010b070945480c18544443c110384090381143d8414442000003081c8c2a010710003034400c6100449252110080c40d00c0e1400319050143d412000503002004004110302d400c00c010210640003910000707c3c00c0d2085401c01c41900984549049228105560300703206004014864221a4002d43c45e1a41d51540e40003c0c0721105100d41811003503031400220083da030180e8800218400003520305002210301a0b0f01100900142c41000151498a20034a14103030460031070203440546e0810161074541151511180d50b04030580e0681006130845011658a110201040c0120b01c0303550b030a07032603e040c0c01301e076800d403909900a180185000e008200031503440741d451034119002c07086422070b961641c80048030301c0600200f804056114001d25481007015641c0c1400c1142d80e131070841e008540d085042106c0070312440c001414910002c0c0014030201c09000424501b15100d510010f152503560741c0c0d25030400021540ca28003280300202c45020941d0140921513 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 197961726 1250 197960476 197960489
    0x2040b03190204051905131e02030c131104090207200f0d05030d0c0504050406051012020a0203040f03060b03060601050412031b0c0e16140904020d060b0409020a0306 73
    0x41080040c0a007004000300803000640b0880e01c50300414180c0ea0151000c034121082030b0000d01181c82d2100c000000145801c00450b8134000c044200301c00004003220f0384107040d5000b400b034404020440c0411040c52892140041440d6542e10003162000b040c000410007014440000368948080c0d080250401c06591554546130000c401d080342c0c10707030740c0303050301d0351042411140c83c0c503002540c1c00c0442c0382d8060f0500c25044989441e50000304940c0100c00307041191411079051000310b8a030400d00ca803640d0108925000305450440b2500c0000641d009404500303c5841101d050540d1424200413100203035200782c64190759201a854141010b200ca03c1e0b02c01020300308a450586030080c0507044500c0d90402070200506010302e1040f0040c20414032441540003480004120707110002280181001e4801408071000d0b914401d603036500581085010380114034040d400c0160020501000e5404200d0f4554000c0da502c01c0841c030810000003400c0038080d0000700580304c402281001d0203c48094001c003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 197962976 1250 197961726 197961733
    0x40f1503051c031505010f0e040c09050406080d050f22030804060809060c040909030201020d020f1b0d02070e04080c0105090609010c0512010b0918041a0601170711070305060f0402040b03 82
    0x41315000c0054545400c0310028030340784486035021941141c1154070045020b40c0207003460f02510815521035001c078142c54081705d0030043d140d44c800500b540c44160740b006402146090080006020120000d045803600048215a840c1440e65001301302440c9030b08119020840814140320907507000e26595404000720b00244110304050010b007009000e5449030708685038444481d13274200340c030070740551f0200d041c107107405c0d51908540003070942103800584040280c2560980c96981d402000500000a00c172250003401401d8100f0401c0e42e01d00800800903034054008000300f5100c04000d1003814403031040c0101402e003074145402c1380303400d59084d0701420081010900c107400b00076990800c9141181d01e4081c0e0170359100120b0300440d4012200c14201103540d020401000144078811071106454181f50407541816a20305005445090113a2110080e0018510001c0d10b00c5018592050f106010001110269a902e950f2a0318204048907014103c0752004140421402c20f4090604040000c80c0034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 197964226 1250 197962976 197962991
    0x203180d0e13020f0c0703020103050c0f0304062a1d0a0e1602010e070303051e040806060409031e031e09080f0901180803121b0405040f1503051c03 65
    0x1040000000d07000d61040005001c18580c006050b0704940c1040da03112030381c50f22009000324144c1c496046100a83c0844d0804000070309402e074003001c90f81c0001c1e05942450464a50f520740e8402840b0800010360f0070410300e00c0603a6915040e900100401c140ca5442c4a0301c0003000321024218007500220602130a03c900c1e09004a420400da000e9000c004503001443d08609610100e02402c5d5003040c224803802001d0012041c0741c0c0c000014509a07040500d0345150094003481c45007244a42e11031202c1d1900100c001c5482482d06400805040b03002c0e00d010740101e1f50f03500080411560140d140c0700802e17034421818100d1408150380802481191408001c1401d103500c5d21005441380802c0d4070708162000985269681c05130320a023200b5074240b418103540d03a440380b082e150307a0307444030404055401e114000507100740607411030100c88441150701c643c00c01c0d15100c180f1014003512103606034281e40721882030499210390300e044c4000b903016100030080e8980d070103003000c00d00044419590405040200c0d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 197965476 1250 197964226 197964253
    0x60501020a06151511010501120309140102010b0405010b040609090e03120903040e0a05010501020c0a142205070801030b09010b0d0212100f06060306080102031501050c03120901020318 81
    0x50a075501c9400c5000030900044508280340181101d400c1105021020318408080700d902540065185240750020005a601d80c041c01c01c1444000c40d000313002608030340d004e00007004041000d03c141c560600003c101d8540b0500000d0035030b1000d03009507000c0280032900304a429440500b40004100b484402c002c98000c14204a449100386054050540400740109000113130410441d0018601d80eaa00e41311810845800c0000d85005e10816005109411244d1312030311f01080c01030100c40d0583c00c5484080d0190050042506201e01c60034001102e2101a8403415154007440384211207031740d1100300c55819880d21030300c0d042c0054044a100d0380b4260001d50b403603e945480941140c2c0407188600d40c034152062151502002d501c145800600300a440307114220b564000300162451510140503054807040d07110300701d000484000719900302000304080107500450080c51603206241c240c3c0e18002c041c81c0300c4420440d040d6140c4c0305c0daa500004008125405007a140c240844281c040d0407840c00068 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 197966726 1250 197965476 197965483
    0x90e0c0f18040c0b07030c06140f0115030e0708030301060f0507050d0c08092e050c1c020102120f0103030e0409050d030b0604050423151003020d09020d0f050c0406050102 75
    0x444984500c515000c030b800c0c45407240c1c00078003c209052180f582d80c589440c00404120f02c56904032605800c10b40d11107103203441c00101c54410001c10342c050f0640d81c640f400b0043d03107400d00d070241c0080c90340d500d1100c100202c0521150024080c0310303000710f41d01e515000e0300a01410012490741c00b04031061280000049002c1001440100e040c40c0030854040ca90a08011502c246140603034082c005244020751a40055143e900d400b1a00303010812110b0718010035221845420100400e50b001141e00d0900305480d031420b4000d0342094800141400701c100f2001d00c0c0090b040e564403408600c4080100f040540c00211005000302c1034a051011925550f00c1c035a03103a400f61f40250a046e00c44c50b031302d480c41d2220b005940040000410030311201107512081c0703518804000b08111045001c0000817040c0c1d16407112841130900c0503080d451150003400c2c045000303411890f40c0f64816034603414481c01680d02c400c10040b456003d4200501552410315000f8907100c090b2100d03c1c003e5061100030442680c020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 197967976 1250 197966726 197966749
    0x11b0b011d0907090c090f0305010e0111030603100e070b07030210060b041212030906150806061921050d050c010b010804022809020a0519030513081c0501090e0c0f 72
    0x80000c25402005c4000307460103211a0000b01c2c51414160000040c044150411444403818500801000e640c958a6012034801103a21713a030141c0c04084820302d2006564062038411160341c4c1a950700640310180042c0d036600c1804107400503801aa60602e0700010351140d00000d102d2220700340d24240c47c2855500c0b8000cad0524015164514881150120724040e4000b004065071283d030820007029a501038070042d070810f0041d1641881000005640c40c00c04d5031204002c03809665003d101103140102d07803224582e00703840140e41124600c1c80c0c03400103001004000e001000c1611207030740300e0b1180e005d0b050856030851b840c241000091400c1c0000740e1644110000b202c0d60309250003d0415564011155850040d800703007440501c0010342d68115580000a00070f07044007002a1002100b4042c2c04900340e03032080e54040354038542d9184110000c2e0364800105450400d225aa1802882e40c0c0e803030030101d420980c05004447c1d141c4210b100b0044044c0880480d41d0011100201940701d030801080d11000340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 197969226 1250 197967976 197967989
    0x4051320090114031312110706031509050f0f1b12040b0a021201060e1207090f050610020c09060117040506090d0f21090503030a0f0b060301051806011b0b011d0907 72
    0x55101d004401b52003281c44465603203041044421240e0740703d100500606000818122090004402243c0e00034180143c6001d0703c0d01c0c508500f4203031034032100c50000940113041040220f041d5500c4100401c0141c2c09005009402140c1d46c07000d00e4103003072643d11010f004000e03c60013032041000902a40140400505440c440d19028201c8010341e808941040c201500b5401c10344200c820000c0c00139001c0c0c010000c04007000c2010320058845106000e994840540c100d00581c00c0b8900445290034080c034281d40c44241490040e0700c02d003080c8950400020141e40a41d1660004000c00544a5082191142440580c40c04035030540000100510010717082480601400343d10552600703542e2143c202815044e044400c1d01d81d85d080911004005111f0740045082c0c1d103007003580101a502e03001e41035074100c03103003d0700c403554090742034404020404004001905000d01102444030a9000c50040302c1c0151280100c1074055040c9140c8194488051100240f0440c02e001008000c81c40407035802c04660b40d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 197970476 1250 197969226 197969243
    0x70911180a0f0b0c0c010302090a03110f06040303050901110c0a0605072d140309010503070305040c0801060816091104050d080d0c1d04060605040513200901140313 72
    0x24480066050040781d80300c40c012001812020079110300f00c0e030091100c1030305074007250076040044005506a01400100c03035800540a40304002254166080900144004000c00e181c0c0744072070005a225013050708190b0005201260701a483d5070000c45071030501d41c0c240020200345510100050440c1380c5801048100900824070301d08104148503a00d0043e4440c5a20944900c08a03042880402107680e0503110340c01030840c1381c80c14020100407210300050680d2141e2030360340c842c00d0940107450f0240040720295a00200055903030000c4c070680018050030300251075404003501840280e50b855401a01400340b5110340c10b0700582804084904640013583c49100d1511b043c10b190100c5d01844c805403040034180011082000da121801400010140400d000c0c01c4144906120481b80c1d1800340a0114500300f209100da482d10070840d02d00d401400e80003103420000e034284d60b8110041d201e10103d00250206404800e5078118412911100d034000880b825894840094001e41540b000d001d006001d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 197971726 1250 197970476 197970517
    0x30209061b060915091005061c0501020a300509070f0e0402130b010e04110c010204030b10080f060a0c0e0d031106070e0a0312180305060702070911 65
    0x115408161110280d05901c00064440301100094490304200e91034101c0780242604203034400807041e4500e0246420500419854019a81c1c0d500241005084250700c0840088003100707090b0340484000c1c1c001d1180001607103545281c80081e085041c400c02c0500d440a29080403170300100b8000c5480ca00c91103205010901c0d8840140307841c280800b6420004100380f0030036000c00c0390903c2c0080140150300c25203215100da9504680203040740ca0450050740001d00c0314080404601c1c003600211902c1200c1c20241d494090140704650881e84154800c80d50a81464100640c45280300ea200c8001c1c01c400000d020b00c1802089105d45500b40180078036281503450040241c8584900340341076200801518242442c8000e0502500071450b40b54030304200d21440e40000c00c0c10388602002481517401404602d400c80c2155901107180c883d109100c03040001c0385440300400307110f0904c40c00040d400340b00a04442d040c00c0c030000f42001d02c25080f07803250300c1c204032002d01066140001c85034032a896000041052 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 197972976 1250 197971726 197971729
    0x40617040609080c03090306102411010606030b0f04060503060c03100b0309012f07150b100c1407030809090711010e0c041802010c030f020c0607030c050115050f01030209 75
    0xb00800c0d01c0192100e00042844560303400008000c1107003a03000c0b822940c503982c071031800c98088130040c002c01c821303042c3c8448a20615442240c0030740070200c550410082c050000c0c1021030842e46c550303004c00000b80d110341843c1140e08042c485080d00040544045c0041030505000c40d075101000740c1540c2410900000265284040088400c081c00001401940e41c0c02e210300c040340a0060300c042164850044d4107071801c480f550400790011f082200e46414100b90180c1c565034050703108494035688598032084070440c6541c0341c000b41000000c40ea00d6500c50109241441480d205a001d00c00c0350300d610200c02407003c03c4118058581000003101d0442090340c40c0b81007201c82071940c1c01401010340c203010300030a8a240105444404030003c4c1e6007000146800c02c0651420f6988003c082d01194401d02c0100204e4442e004c5030010203524011a103007201e20801041555000380ea0540000781007072443c608000b400e003d03080c00d002c04509002641802c05000541c2001041042410b0540c0040c2c41c0500317 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 197974226 1250 197972976 197972981
    0x21c05060c1309050f0f0f010503190507050a0e09070b04061b020126061306050f10020a050303070215250318080f0a031404030801030609030507120909050106050406170406 76
    0x50300c2c01c40000c4c01181400c0d28a407100d2a01038981c0307440f82101c030300051006220306800c64102c8000070010300d0120b001610394864240e5a1900b91094020340c8000b081c59125800c110004100707080030b4003a145031854078a41485025041055089001c0104002c51a803013804502c4c01d04e454660b0403030503041c03880140c07102c1c01c103031400c022188012400b4080600d60781134081d10035041942d400d048041d001d90300f4002c54119024669000804c02140d04903401c000d400740540e02d5650040700d0007511152619807031500210303010001a40503410000d6065000d018240e0406907803201c12400d01c3c10b054012041134050140c1a00301036640100c42c0030150300c40001013900d07401524039551f4a450781e000698503803040500002180c00c00c1c50395214249401c5110b4070a13509641d41c961941d09542d40d80025110800060382081424041c92010519070b521022240a1941f90a81c0c02460100100203840d016409103080c4803052000b00409a00001d405686119100c5d0741401c507919494540b00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 197975476 1250 197974226 197974229
    0x308060120010c02161809060e1203090106050409081e040f080c040b06040e15030304030204050703020334050f0f0a020303040312060302060901051e0a0c021c05060c13 74
    0x100551995400c84480c1c106501494258119a007a5030382481c08401d89a882c4006106040640f221810341c0341c04059940c0c0017681c02c83c4512000301e0041c4c49001c00b070f0b24040882030712001d01d040c00801d03c1030f00402440340a000b80380c01e0710b040c00100d0090301d0780311082c0030b181040001c0245e01c00c480d04a1a060000b10f40280c1042d1041155880d00c401065a07110120680c6d540100c2c40c0040032015842c208040d00e048a212106000043d5901009210444450103120342c25110501c1301000503070310350190f5481429150b800680f00d2802d01019500104000302c40c54480c44040c0300510105140400180c2000315418265a103a41c801f6880680b840340d64110314510760b001c2112020950b02000450050b8007030750301c034401040c104040c1c2049642ca844020750040d020402c1a80b194001c20190455031924007080b04071a1318030b101014641e00045407100040c0521070500110b28200c118034281400900140b0200750180d990343d555218050507050903143c1c041600c190000c0702004200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 197976726 1250 197975476 197975507
    0xf090801060b04090f05160c030306090908030402091e2e06020102070b0c040807181e0e1e15060a0f0303030f0c180e070302090a080706022803080601 66
    0x100c9a549142c9003036034209018a9103594109405500010800d0007040e0041300b01030031142540c8421070341601c0508007110210285511080000380c5030405110f0b50041c07030300070b40790980d80345024410010341340b000415100038400900004070321014409001c5510206401100000010760048400940c40c00100600707120110075011440f15410f40261415034880ca000407231585980f003402c8600c1c059402034201e5a03202d0b950400005508049140300160b003501c00068581c088d00f00e20012135400990108102d07202e1b4200c01030080304111140b00c07603030300c142c0c020840c3e00344070002070b1580c098244152540c17010340c1c00f283c1160740b1161100000d01c44c11001016203660307854046c01829401132000e060600d4500c16403000c6004271a00d043c407828040002d001c0c00c1c20a2410300311303200d019202204242c0c5c00e00501e041c540b20030a20101500100c0010034416240030750080c640f54001c0c50000021032900140810145000340d1620715940c94108543e440d50b0310001240d501000d5003120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 197977976 1250 197976726 197976731
    0xd0801181d030c0d0c1104020a09050409050c0a12020108010e040c12060504030f14032a04080708120405060307030c05090a03030c0c08010515010c0602130b03071106010b0a0f090801 80
    0x84058090000040210f4800361003036445070451500c042c2c070382d9030035050003600c00e480c0a010300100f8581790380102520704140c108414043d4692000c0350482c1e034910b0003110f0540c0010070f0a0001c0c42c0c44e1004100030000c51091000307403d00c81d0b0000f440701f0418841c00c3d80100510300072404010042001c0405040c00180494441d44a03051075005008103444c00d0300403c0010340182c015034840d8540b46c10000000403114a0342d1500701940d000980e900e20b212040c0f03401001c40c0120600742200520007000d0800050148a00341039045040c44000c1241c914640d40c1003004008d152100d006890b80803850341000100f45120300c00c261000e02c5404441c95100720911008000c168000c8841c02c8054050405c6192a0f515a4003043c22920252141c1901201c100c03038800c039661052a824511512403200035082c0200034980e140064255041820340d14070110400139425404050702d1105004135004001d25403418044200350700c2480c400c0f10800001c0e0f810540b2450285284c0401050a20000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 197979226 1250 197977976 197978021
    0xb0304030903120206070e0904060b0a080f120310180216060c0816051603050702031002030f0a060b0307031a150901020d1125030b0106050403140d080118 68
    0x340901007500080b00c400c032504100c2d0252500c00280188622403d0302d6121004103018100f10b82c6113002031003200c440d6250340001c1101d4540040d140001c3c0300742001004a01c8180e101c0d141003c0c08a02401140641072040008072111080c002c07040724000c030f491000312488070403504007038800c00c80a03138030903240c60200c0010003280798000c041a0b5500e941d005415140c03444506180d4180f0087c880000e0404c0c00f6019910003c581108074142c82814142d1400b2415030101e0b06160303815031404801036012040042d400380032a1040d0344102c14103001c0000c03a05013407964940e804090400d4007010781d41c0102c49030841542e48400d40b035000040081c1098100d007102c00e07905034042c0400a0040c003600c944e82401c28018401481e00e2841800179246010400c4a0184509031280d00b00204007600e42c00040411181d190540c060001595090b540350f081d41008075450005d6901244581d011503468104030382d01040303150541d00030f203110a400e00e4040003142c0c05405003200c1c00e012981c41051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 197980476 1250 197979226 197979233
    0x2518090b0f040e1203280c0806062a01060312090810050c0d02070c0503010b040e0606040203040303090b13030f050c100509010b10080114090603060c03060d060c08040308010f05010507080d060b0304 87
    0x104040111924110380300c050034108a40d4140c41044070440d000c50014004110240340c071001410007451680c7c088110b50bc07081c5405180780c50152078000f01655110801e0060100c101038400140341c50341440700300c0e2482c0805c0c4076030b203218441c11240416500c00105450402d07030402c0765049204d416055403500c4850810001120700d501c10b0622035840d203240c06a581c00c09000708540044000301401c2c2c40c1d0f944405000c060b40c00204124201a940d400c524002000d00c1c45040c040e540010451048111916014080b450007022010903c4024811042c0d042c4000600706c40310900d9420104c2c1c640c070345c803840c0d50250280b0941181d00c59003289002c0c04241e40322941c24101e8030701524000d19901703000300744298003205071481a0543c00201c0094088450003000b590401000752110782c0b00c92460702c514044541a01000c070000380404240001d240e803046045024018198031040d002e0b1618001078400d12030034000400800001c07401c00011110b5078015001080c020380860303601c1ca86440d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 197981726 1250 197980476 197980501
    0x30c091a0c0705090c070f06020f03040c181505040e0a0213020c0120040302010f170c07060509070f1a07140705120304030b0f2518090b0f040e1203 65
    0x45031021070b07108107840000d407032a225030f12a01079416075224518209480e1540000380c48500c00c152130060f0200a096100500340e00154804c4d4018401010314904250000307181200e056004055a802c03c07081d0302c41400444014011036a0403240000c01c81402c0c40c481e42000420000a54400d40300e05c0b07140c5a4407038980060080c580c40340020408104488106000c1c8c4008051806041c0401c1c0700c1880154041c009592048071305042c1001103100f40f0701c1110112400307c400d044802000b0603002c04100f010f002d55900121b04001070300f20396081101e07901031070040f4850a00394a104401070740000541208a40b8402e40080d2400d5448569800d016070300e004c02d01c00d0600620300b0b1560076034054804015102034a82c450361003c081d88070604605680c90014213001c00c440043e9844c00698010100ca90a2440c560388468200641c1300d0300740340555005a000c40e4000303040c84400802980d50000700300c140300f400c031000200400055421860308400ea0046040c00d1400002d00c0855001d08 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 197982976 1250 197981726 197981737
    0x50405010e03071a03060307080a080a08010e0f04031d06031509010b030c0405060a03020c0a05010504020f030120031005031902101106040312150e0a0c0519030c091a 73
    0x307032508a01100c0010925550315024804ca103250074100c1c0c0708464000d545001950403803c02011195105d4407240c0440c204800e405d01103500d0400011101801500020300c1401080c4070300c2201c0303171407400040359541910000c02c028204803002210520f10b030824002c01c840f1a5028001030744910704103140c503a51461034115507214418200000a40c290301c0c030100d9110340074590101c0c0c10149130905000c080d4103c59648030506800744141031008500304500c00d04140654008a52424070b401803060782c100c1d0341341d2180070364107110380d680c12410010b40448140310240510b03540c0703599465032151600e01350741000d0741c0f45c054694090ba03046e440d40f80780d2185d24001c59080d81c00245600c0d05031102010140c1c60b121a401800014000c02c0c05492040150700c214032011403030004d00050f031040300c200d03600040c02c00c61460b400d0101a5215104200107a441e604106140034850541d00345440c04402140d4105600c6403850820240319400c0380c4c000b01f510062001c5e00400c1400d40c0d40880c1c001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 197984226 1250 197982976 197982979
    0x1b2904020a0512030703110a0209040506071d030a0807080706020c07031a0708130201090e100f08060906040b13060903050a020d0e09072d021e0607051606090203010903050405 77
    0x9022002c215490540ca20404204002004518021469900303490301d000300c0c2c980124030b00520301440c01580342d110415103e07502c20f801521907440c201e18040c0c0f0b12410641340c3c1d1210189500c030030280b501c00040000c045608440d50645030b00c21403604030703d41c1c07103160802000b403400861022131200001400601b0f5902c035240548002d101c0d80340420009408469000024034820040b4000080c0e12022442450044c50a05200744d01c4203403811000f0001c2d5100116240303002030800006170000042009411a140608100e003042050150740e114041d02c081c051110410200340c00e02188072203021003036405881813080700b850341000381480c0c002c2c0000d600036001c0e440701041000d10401c0d034803804060050042c10315480d0803504607200710200140d05205442401c000340018905242d0744110a4254000d1410003520810b10b4441e0344078141410103035000c4001d10040b550800c09503200c110742c2c40d035500078081460038010041c08040708040d405510b4070782c0500034541d1182c02031059800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 197985476 1250 197984226 197984239
    0x301060212130902030a020c0a031d09010815190c120f0203070f050a030605030601080c01020d17040f03090302130b04051b0f180a06020f01060605030103031b290402 73
    0x4400c04810010311602c008160201d000c44414031262480303901030754000075816401410044c90b01d2041c0c0c9440700103401503001c100311161154410360b60003a54800803e00f43c0340c4d506c0315458a26100d0350340c043d41d6110810701c401030002407659003d41d040102c2015024000f0f12000c0d400000151840286d10001e058003401c000242a6440c05402140c3c01051541c2c0d07694141c1c5468001145e840c0c0140109004143c0c0f280300002d0207940c00c12589029200c8807028220b92101d41d0000b903c1c00403080c41010602c04505041c0c146001204c07002076005401c42c0c20f0820341e20a901d411102c8030820340000350b004022a5006102008a52004000740000c0e202080703580c4550b2402d0603110a40f0546100c43e400c10401d094908814074003a140000459065a0b000e421071800151028410340140b40140e0050503040030044007401007200420342410103915650568500a0150106654185407502031480e040101b000345007000036050181119050b1103041070381380d070b142840113440a178031600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 197986726 1250 197985476 197985493
    0x1080d03020a0503040605070e060706060503151b0705120c0c011d1012090f0b10140109121103030c03070203010f02041d2a030403020607090506040b0f0415030203010602 75
    0x10300900c2120340400003500c03000d045a45503501c2202511009021070100400f0707140141c141d4071004046c002e003d1280a01152050820080c1440d1002e404c41d011003030002403040c4015445400703004c811206444401c1c560380d00041c10300038505241240d1055034840005000306040e5000300e11006029401d13070761480e0941c255075500780e80c2c030a9001034a9200400b541000165409500c4644c1002c800038008207240b9002e8483d9001505003050503503210a2080822103040000480c0b1402323814a110041f5510381c20070002414040c1394080c41500d4102c80342c100c4c0078001e080b0424042001c0050807171350749060ba402520f40700e8101e407030124040e60800d401440c049980b40243d6064a800d032801c94864881c012000700d41640103810300c940a60358a0409882c45180e4020000c0170501502c81e60f41c81c1410300e002440c280340104910104410804180306d183d4526003141c04917001000000d440303a1168036091500d12070b580c051080d03541c0c01d040508150360944c02941c100c52054081c0e82303001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 197987976 1250 197986726 197986753
    0x80313050c0108041e060b0a0e01032607150e0a080904150e070f1e030623010e0f1512040b0105090c04090f02070609050c1003230601020a0503070303050108 69
    0x1c80f050350003c015a814103810006200f00d035400c044000c2c040c45011600d42c80034808a100040745402084180c80c0c1040140203001c0a9007040c0d1030790b407004458035110084590780c52000d0040030300c0207000c0c80b03100100149008141d000702d4403414030300c01903580407021454160925400341452a016501301000000e054181002ca40d0403109061341341c20301c0c2da440da102140c3c3d00026504400c1800600f42d500c82411160030144a0b44031000c0c6c40c0050f403542440c44c5111400041405003140d40c00d501808002030341c1c0290b06102c610400c3d01c00d210001c0310100020078111404206001c0d445020445242c2c0c804220040381c042c500034141041c40c0e90f00ca5051105012040b00c0c0101001d40410041049100950040c060310206440041c288103080da00d690a6900ca130500751030540c003510a0001500d46040074030b0704414241410031045858074031105048900b1850320050340400c9002400590081c0900c403191941304042d6995001c0d00d1134003070000d00c000e006031000c92042e01f0185c8184e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 197989226 1250 197987976 197987987
    0x17070306051e01030b040206190e13020403023003070b16020105040c0b0c010b060301080a02130b0d0206090d1a07020d05030705041403120c010902150313120309080313050c01 77
    0x810200d0340c42c0c03010b07800c54840c1c0c0204d907000f4004a0300b241301040410300103402d17004c880e80000c91a6445621803c8804104101d2801d0742e8050911144100030070401623483c22904515061820700c0840c12407200061419990001d03d030041c0240000200842000705d00b46409110f6035038011079002d502e0045400700c1c00c80301e0864001300490150a001e001840482d0068008030f0680d80000c181205444040740e0303981c0003030303200d000282e12400360141146002d1170300602d980700a2408001403000e0b00d001610042e12404007900989000450110720b840d007800c000c83c02500030989203611070340f802c0e9100164004a48000050044031640403295102c3c40440b0701032551903981e5410541809101e460036815265410b515100e140c8d010f0754044a0300001d41a020340a1000150784600c600520176501d403005002507101d00c0400030800c41d100c940100391480e0340c00c0030748030a600112520541c010703d01400082d0041c0004010000d00c158400000307160644544140c030140340284006452 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 197990476 1250 197989226 197989261
    0x60801050c0f0f0405031b0414060105040b0a11010908070b13020102151f0e01081905070b030618040b04060f0207021e0a090f0c08070c0b06060708041707030605 71
    0xc19041040b03200c0310750765450081c000644500c2e181601d4680d5860001c0d16040034507924410003559214401c880749418880d180f8190360705480841c15240240c00244544901d0051882c8502c0105110003014420726050082030307520b2000308404001c50070080204e405c600e0702152010b408000064502d5041d180a880d50303503060300104003100c3d00381c5005040034001498507590f4075906010f001503041003913260004200704581400d2070350522240c54203000310a000002c9501d0310003036810004500096540c1120220104143c480d20340200040c0309403080c001e1003200076004000d100c140320a0141e0940a02d00c070300c00030842c41420201c280140d00880310701951111007601d2004041104400e1644000d20051a20080a88a91400b0110303080740c1c4035452001e981d40700c5800c0061b0041079480d0406003c0c10f200640a80d1a901c0e840d43c4600103014a00491000c9840e4007002000800d0720050080005c0b12005030b283c6d115090b90314103c81c40b0546025080c40041507020596503070040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 197991726 1250 197990476 197990491
    0xc07080f0703060518011e0e150a20071101030c030c0c021201021b03090405060904050703060e010207020a0803030702010f1a0405060312070c0e07031b180807150306080105 76
    0x1e0790b203907482d0301c801054001c0c11000b004880d5103c0130809902032080c0071154199144e8659040200255001204c0391141030030030303984c40b10417101464903003001455400b07259000042001ea0b00c00c0c0100400180c050701511107080c0101e040e50401c0f20780c50004140800a0307a04118901009004505503600150b803000460030100c240009414400d9500d0209c0400c1400907160903107110401e0a525154860800c0c0740c2c001060101c95441c01c0e0080300d4009500301c0d0000114145502c8403901c40000384070040603903607659454810f907982901600c0307080b40c00800840042c2d03540c0160f41d469500844e103110055103042c080051703a000e0391181c845030800c80200c040600d9249400c1c4401008050401c2e41d02d40700707423503e030146056404010039609104d44d804820480c034048214410321f401406c28410b040c10908501c030103d0001901145c2d052103031500b4480f41d0b81d904a00b141c814419085180c0c1400348450114101149440c0b098082200c1c0da02084031a50b03c1144a080311010b13190310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 197992976 1250 197991726 197991733
    0x16060801090e012a020f120c0c060705060c03100e0f0403030c032f04030606080c120f210c011409070504090c0510050f0703080a05090312010510021609020c07080f 72
    0x40d02d0155644100c02d1044c4150044411400301910301610b480e5101e040c45105c030000061500c200507061003217440c0709405441d01403d00c451507807850740342c2c10018481c1d0120800803001543d92090810850000e20180ca1000000e003089003012a0080c4211401c3d40406e00301041ca0800d54400e10407907102e2450781c901d02d1120f0102e0021061000304e19440d49000310070910003c008249a84584070042c2240d500a100546107602800f4112451001980842d040320032064044d84001c24040c009000701c0490849810400c0702c1c4c10420300800040c26403540c038240c42850b104100d800321034000c0842d0001c032460b60ba84c078410081580c00e0340303200800c40300303184500b0002802c00e1251130103a6415401c00500b802d404010448242e084140c0550005440c1307410700045c402a84509900086907034045c500c0c04c2500b9030a035401003410712403107001c0c0600c002d1002c100c40c402d0080b00501e52505052565444e9103010071000b0b9013280c00c0c00d281070301881c3c0000405003000070b0707078100510204015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 197994226 1250 197992976 197993021
    0x120c0b070515014401020c010e0105160c0b06150309010e0105090309011d0319060c030605060412020904060b0a08060f0c070309181d0d030f0510030b0916060801090e01 74
    0x103640e0500e424540d040201303030148050380c142080c0058030300c00c544600002501c0510340d2140b400d540c0701402200a0800200351803541d55408200c0300c0225070880f0400d0925103d24001c6103079003215240b00340d42148003005100c0e86010642148149000100003840162104408280c903840ba082d4410b0106040d60300d580070f48004410588142500102524035540d061180036046110715502218500e60b40e440012113540c02d0f02c1103d000c0e06082c1c810b1800c207402c0081030540a0450316000e8030400c0a40c00040411a0a41000100700350282c42c05650b150b441c1d2445a4070842654164070341034107400090045000706094604403a0566544d1070b000e031911040b14810407100c4e140c404555199514a09500405400d108e40b8140c1d02005005c2c20b0b04070b440c0242183c4c074002030b440a06041c40c003402410303113800e04540c069a401114405e91501c07211402407030b0181c007000d100f415a56500c000100240c002121a0480b400100103022001c10303050302d282225003442076080d040003110348 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 197995476 1250 197994226 197994299
    0x1e0c120402030a020d030c060c03060302010903241803020f060c121306110306040c0306030201020d050a050d090c05091006140f390303010e01120c0b07051501 70
    0x211908140003905a580341000e5801040007070000d004182d012620346400d2208009241c41072800e480410b01e4104041c5080d03a00003060700c412444003400390111800c0b000c648500e458102007583d021604200048201104142071074403040e001031700980610b40400031090f9021402510034101c110440303107010601c1c020300d0300350349000e440d4800e4080c202d0141c10000c0c0c83ca2007032101d21802011041e4491600200f08003d8a5000071200109410b00c001000181d0300010642140301d020f0400503203400c1c0840c0211818001d0038105a442070400340c41405000703110030000c0658500703030381805d25984e49030b41003520000703103115000000300d0100c603442404039200090105039610245403441c050b906540400800c85810b4011286015246810140c032802944400d20060140c06142075614050300c21031554414880e020303003280030108850800800c0640c141c0a0600e00d8040f81d195121410800d5542c00034100801c03581040e9400440c20200d0a41c1014034a258402d003d00481002e11 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 197996726 1250 197995476 197995507
    0xc060e0f090406110f0c0a1e15021602040609140714030c09041b030e0f07060e040209150c0703150b03100f1b12110301080307110303040f0308031e0c 66
    0x8102407000a000340722111740001e0003411409860401001890214245200504144880c92402591401d8003000240140c0f14403084401089801625a4001a00d020a201008000072340c01443d1040c08a02c1c1402c40d171000301c20b42c0304411401407641c2d0f40f81d001da070075904115034048089824000244894610401408041e00180000c03035214503006001e00c040d181001148007003511002004030203017007048003024584501006141c050314041002c0d100c104000403030790085400050a01258584006040c44500c4205101c0e5440252220f59500c40c0720741e000480b012810071407901014281806034920b000c00043c0545010101030a12400400c500080341d100151666010203816980100c5124284010788070750204480c41462241244c0d0100b495150001d024030042c81003107000800e441c0021343c05600044071242d01300029186002d150700c0118040d031101d0000c030400c00d049000c1c40c0509005003100141d000e00c3e0886040d46001110380d0322250005120f10101c090048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 197997976 1250 197996726 197996741
    0xa05070b07090515030f0a110d09021f1d040c1e11030a0c1406130206030408040b16030314071d121902011107060e010f0509030a0c060e0f090406 64
    0x1070030b20ba8402c550340c0e00440d001c0d032582c401440d404100032081240038400c04801c503601080c400001c00032444000e140908030301070800e01d01110340d40c600c110011911100c1e900c903003a80414402000459422500030b100d800b5145202880c69110b00d8061881c0c14540500c0901001e90703111008080180302081c003a6001e004010700c10040d2a8014504101c018001041070094665a075140d0420506141280d859202a001c80c0743c1d0048080103c80c090314180302208981c110795080c1d991300c4500b40554140100e03045511321007000655a1a440050720005104034071035103043c44004501030118003400000c80c1c1c0003006c10080f258440030b4a02000c82c14070101c00082c80c491201100c011300c40d20740a880d10004a0b034a40419200d810340d0380143c8c0050403c81c41c0e20003407048070b0400750020140803160304000d050061034204450a40d01800c16160402009002c44040302d40a04180f08011064400c0d00301142042c450344050742498090100c2109003e40142c07001e80712540d03401d000b032005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 197999226 1250 197997976 197997991
    0x1203030203070203160804080d0e1e030f0124080a05071401030905010207060f110301080d0c0305090909070f080c030309060a090810050103020a0b12070e041d150106050a05070b 78
    0x108100145441c200d4140001203015801141c1c41f41e00384005140307000b05440200707092041e0154807420580c1e41054107000b402c6d003a0030f01c0031901d010134040380c45d010241080d004503500308420ba514910114003401c2106280500c1084165a40c550080c0c48480c03c5201810307a80000303d00744000303000128960350490044c94000781c0c101003622090300720b0b003007030400700d070707895101c94001c01c110340c25000c0d00e0f156641044c015403855250070002c50f81c0d01854030100c0248186180d054052600600c00e803008988090300f04100d914082e000d131925000b42c3c3c050000508402c9102003440100040d50014880380680154a4014158108412500704c8081c0c803040009046000ca205142404a12803130030a00b600401c3c1c2d035040d841000b401200e550004294010705010100c050071800c00c841d80c21403514103000b08070781c082c170000c02d0103003c10507180c0101404030800b0362002d200000c2c010b200038080c9104000c040e6201d81040768184a40400074002942c14803980001c10081d080d0290000003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 198000476 1250 197999226 197999233
    0x260609071b081209160e040c03020d030302070204050a02030907170304031a0108010e0d080f040203121902160311060309070906090b12070b04090c03060e040c1a0412030302030702 79
    0x108008100704850601021200c0050101d03003000204442e24109030041d1950300a44400449024884450422441026045101c0b44089030912221b8008034028540141c21003114940b14240900654400c4804900075031904000030141320951098a010750000405403030701d68034000042c0c01c002941d90005400340020040000003503211003101c5407011280035181a258949809a82142d0042078003161075002440d0f942d07445030b4045512035002022800103403c2c2d4449002281c90100340b581c00741d00f00300c80050301030310034282c440c603072690000507908544200180030443d0706d503c042440018003000d5488400c81103071038864082c0d079004003075030102d42c407051741c03260b40c0c4054030987e0f0f000c9400269144901d001d00d050034000034000d804a8001803148030310708081d0702454800e074800c0081c12556140c09070030300da10a80180c0014500350b07101100311704280c00c00000c00200c071b100304803802c0103441c1c00419140c4800242c07411a0303441c0b9014512a0007030344080d0041d51000300140e08500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 198001726 1250 198000476 198000497
    0x30606060a021606030c02210307080c07020d0b100b040e040f050a0c06051309020a2109050a3c150b0d030804110406030f0611270126060907 62
    0x10314443c190300180040d5030702180606280001906111044451050090114a0100c58040503e00700c81e0456410700d01600c45943d80da4040e43c0701d0040440c001c1d84691401e00c003105001420304200d000b41d00050007c451350b81d4403140da0300381c0d20440c420300c80c3c1d4051100006010601701c2004d464054011301c06c6d40c2e003482c280d90725455600d52680085000c2040812115601d880403400d46000c0c1a212800318603000c1d00c80303006441c03801101904403110250080e01c115490700d41d00300e4410705511408070b40300d15071076181410b40d08203080c5a48030307019059540d0005150340c0725060750441c442003030905012101c0d0b40310224801d5081400b0060b0f207071910001c180d01c0c0ca80b03001840000d40079580300b201701d050501e4654541c00041c0809842241407500503c046156100c0c40c1180d01d81c80040015803403140c40d034070041402049403030400700c180c681c070611074000b0b088010602e921099891003410707106200d41c801c0f40d041c0390700d061011820781c4000078010b040102996030400e115040452111 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 198002976 1250 198001726 198001753
    0xe011403060a32010e0705030f181c0905030d020601030b010b0c0705130c08090c01050d1e021b010b0301020a0e0d11040e070509010e06010c080a050702030304230103060302030606060a02 82
    0x48aa00f00039200e168441401000741415200e2002d400800d42e10b08240f03107003019103005c0d014400207000c0d0b1540418090003650540c108000003c0700e0780400040813100903220002030803a0616114650080c0604900742e464503201240180c142d99002c0b050304407690824907500e00c035402081000320a40704101020070599618a11003c43c40d503603060101e010b860130040209180005083c0650700d520210000003247e030083c080c4c8104501c0580c2c0000c4214078644001101003440c0100c80790548001111010810498016808102410002e201c21070b00c42051600b01d1107824000300008102c901e02603544e05d0214003200c11180100c04602018041c20005000c60307400200305c81c820380c00301008102901b440282c803801000d07141c0c1c02001c030303291890020308001c6c103a02d001040c0e10000206a0485402202507501458014040301d480e1381e103d600c00c0d198047c0c5082c00e2404031451003282d592030740c442d001d65000d5a5028000d410f8a07201c003824004035400410144066014650060100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 198004226 1250 198002976 198003041
    0xa080406020c0118110d2001270518070e31020c0c01110c0405040c0f0b0a110f1b0a030204140109050615070201081806040c0e011403060a 61
    0x1a11400c038407003401c4d01c50345804d0100c6401a030030f650003696035011050125020400b072071440c800044030000d4201080300104c41c10700d00e80c4c010f084030152510510003140402c0052000707480080e2110316400c04000000081d0840880f1604002115a07203c211541014a0041182c1c140c00700e65103048000d900e4040000f880c054032042c2e049501081146070400c04021b24500b40400b820028504049005420f413030b982c540d80014090b60300c4001040030010100e224500419284900020447d05d0b602d86680560100b45108000703110103030260300306034000c6100c00c1c1d0200390b2002040742d00f80c40c1c621410400c42e20303010300b940180c3c90700000000d601d1b01d0190644e4042c1c400c51618256041c511542e0031110050130b00740c041d403006818404d11084400c102c071070140d02403c01e032000c1e64481d20b83c40d4840341c402c80003100a002e400240410421110400e20680740300c20b4400c043c503070721144120070b407002030200142d16a00c03941c00300306c51800c1c076442041300d00042c10808011101e403505030b409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 198005476 1250 198004226 198004241
    0x204080f0105040c0f0b1b07050603090d030f0605220209040222090908070f0519110307060206090a0308060a0329150f040e011e0b030c06030108030a080406020c01 72
    0x20a40d4440d0100010804d1200d144409040e0402000d0340305400c0022400c2c0130700038103010890201601103034031031010f0200000c0c401031900605407582c0e464100034640d111007801c1c001c0c0c8042810103104803d152158029101550310103003107400803041802c40d022801d5003040c9440d105a07130822036240303030b511940010f001341c0c0c14014076a24002030324014403081d006154040784036107103040550070010310342100320b40f04147c11105009a000d9181002810110680b40800e40d4243d013401d20300c1002807450344128a06801c409031044607079142e805a0301c0381c01c01c0b10203480c00d40200c0e03000e500007030281c0e41e6a5008800601440740ca152a0355800c11100c4003c040712104260101d48050702000b182101d55104400c545155818a46034006c61001050792411510035615001e1101e150740003540014107a50603095054100758000074010300400c0005e07034142c000c0c0900c0030100110706124045034103d40c0d003040114a08401c980e030440f190a005441107070169000c01c400700740e80209004842c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 198006726 1250 198005476 198005503
    0x901092019120b010e0105210c0301060306060305011a13200c070812070c14010c150c0f0e09010312110708010b011b120302210c070308060321070204020408 69
    0x100740121418070185441c0141d108411740d03618030005100030f840c0d40004031001455800b10703520b4407001d8404a42840c5074070726016007540ca002000030500c0b0881d08007038205c030b009c4c0000b0010104042d6640e18841c1d404040103401000c40c2613650700c115600c0c1c0c014419071511324481d80c08919992200c00d041d40c02280036414551240f4020710954005000038065555034040880c6401d1070799480410500c140e12030001c1401c002c5610044603401400e05030f41e0700b94480c01444020181044050041900300314010001d040305480044590265602141048c1c00800740c942c20303841c0d035407959044948001240b040201c0300a00c1428043d040103c000541140b0f40007054001c440400140524030010f032059030045081c10702008100304060f000b00c19200d40c0340159031441d506021408450f80e220f00091010900c40030010800e00c01005823910602c80d959295084c2c4400e41015074800c0ca00030a0018000c0f80301c9000f001c0b1076a14000c040c080e2015002505090f41c1c0c040503401e00704101d4000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 198007976 1250 198006726 198006749
    0x1c02030a0f03080907030c05060f040e040f0b060109050112050601050c030310080111030f07030f0b100e0906061903090203101814030a140f09040908120901092019 72
    0x280c0806411051965020882c1303402010311500d561038841242405205550041c0b00014410b200c0b1400300382103c0c040c02140c5400341143c01c0c41c0c9008414ac0e86040b03030950340501d1603004500e6540c0b1940c0c1160846405a48007110fa02241c5003140c005c1002801150502600b0850700854803410700c06180f08490f02001c900210340ba0000700b509441d5400b030082c02000080081081e0204101002030304007589140010b84484030303904400082c030f024480140c4c840343d92440d81c1c1e030141d40070f03504440c01c0c60709450542164555106101c05800ba5030107140b03190940128100300342d4400e900010300b0702e00040c11035403d5000058180125000d5107502c18010b0352010401d000d10007000d012055611011008610f081c0c1c408000800455211491464030320000501240c2c1540c040f098402e4118020300400c009000344c5000300c000d610034100045021070501c0002c0306404103208401e500340d0402d07980300b851080e02c0190008000003000391680304a0542c0e030842488205a6020068030520f2540c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 198009226 1250 198007976 198008003
    0x30213032405011d041e0206220e010f03080c03040b0409020406031815090c0b03150109063009060c03020a030b030303130809451003021c02030a 64
    0x10400b6030314140c02281c0e8510a06071801079510550036142d41c402c1c0c02003801d82d005410f403540c1c005011074401021b907000c41c3c08640554104414080600d40140c000744042049039a01241a9051401d108280100104440070004a50000000c1400e00c1c083c6040d42d00c1c007a10740400405581058001b0000c8540c080740620507283c04d80314454152803081e4540c00148140d42d6581031b808100a01650510f403030307000003010482c000400c50060041d40c07610686903e054000b001c910b074000a10107000030000040012945c1c042c0d52622042079003048003144000400c02c4101c00c0b51200108402503c0e500d0810001003000c500c13175810041400d80c0d000d40c0d1340c0c0405000400742c407030302e11800303120741c104105000c1c0c940601c0251800b41c5078061003a0313031a034441307200190554200c041040361900c080602d18200d500c25010410001c8083c1c0484507038950400013050b40400304a440d1540c3c0395402e9030901c0949411403480c06001c401e1554442d0412065000c04d042120300720003201c04200000c00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 198010476 1250 198009226 198009293
    0x4050d0801050f13020c03120c0315010c030210020f040302041410141c0f05030301090506032a090402030f0a060b04050603010c0804080904021201080c12030c0d03021303 75
    0x60031801840c00f12109800515450002615070b80203041030101c00350700090507507246000b40251915140da601c84080d003460041940b010603801215070600c82011170003000c149600440c4001242c54141d802003400400382d000400003035020b21800c80b4460b109010000040c0e51318065580140440c8010800e542083c0f004003825500c2a0030000700f20000002d0b50407a03440300e20144400313040966030300b601050381e400e000b4080300302c00d0400b8016000000c000b0900c4c000b01c2d00035600925080e01280d458103041c0d41102e081110094030b21705490400c0b40d5441c07081c40c0c00075070290000d00007010740348020301804000340382240300101241c000b0740f2a034181c80c480c50503200350b980c031090a900030303c039984665900820180008000904010300070880011503203c3e030381900c2c440c42d0341c90386402c03030341d40c41e10400740e030710716524030300034400c801450001d000f41001006032484030880c1d00050045005005c1e00340c0182d00041e82c2d00584541d81d801c000081081000d1416100500058840c0071020940 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 198011726 1250 198010476 198010487
    0x2010f0509060c091315030f03020709150303030e1002030a0e12070b0105010503040f1205030a0f0b0f150705010c031508062202060702090f0618010b070b040503040b0304050d 77
    0x140a40070079040700040020790b9006030f0440f249582c00b140d800040034004281d0300e00810020900d4240e03032280481c00310400200e1016807828a0081e000c5440c9580d41c1c40c900400d41d403000c2280351084074051020130002e402a0480131010744200190f80a0b0300c40000800c080760402c8410b407038515111200700398504002d00101c0958902c1c6607a90745401101e032290415050180304d43d5040060000c0003070140f140102d003c01d050745d403111004058000000c0d008040d40c20581c0e0000a16280281c200380c001990b1080708402400640418140c952003400c100c41041c58604c00c80c80700104000741c0001030820301c81c40404c07140c5614002000c1c10000c90701d01c101401d075001f40301c0030b030b11a40c00d10960715842d00030742070075103807003101c2c118586038520108400c0d0051b210029040040304041c45100c80813621545d100d18410380300360b01824140780c0c0d011b0100c40300384940c0140c42010001400403410044600d40c0c0240036500f101c1c5030903502c0400d68000e910880d01503940ba00482c5030001c038150b010323 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 198012976 1250 198011726 198011731
    0x2306040615081c20070605030601140315060a0c05030c1b01080405031903060302180f060d080301150c02030f070806070305090d110c0316030b0601030c14030907051002010f05 77
    0x442c0108070030301d031540d01d19040c207000c0700d502d070140940d030768407101003440d100400032290007080240c90320203070b5031440070b4820340007a140140852000481940b4411103281035a03c140601132241c0c0e42561401e080c00841c1c0d128001c007100704a440340359680491000c0000306107181803600201803460016409480419004801c6030401003600c06010104000205642910f52494840303034481400e14070036401442c480d0300003074010014082c207100521042450074840d01004400340215a990000c1169259651200401001080c0018012a0941e03a0380e81030402d400c0c1842816900c160300081d1400f140c046840b504c641c00702e00c05024201013030160365004240c030b0405000e0b5040c1000e8141e10b840c40c01c180700b42002080f1071400074500e001c110f0305020100241c25501d004901e41c407040d10340c82c41c41c002a1241c1900801142d2507501c244a0210030700103641d11a484000c0c140c0c440d0020340c0c4003501c42640c80c0300c0d05902103034550300c03d06041078020b601d0b00002810703062411040f0585000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 198014226 1250 198012976 198012989
    0x6080a170c03040603051f0815010605211306050f340e040f0e010207020a0e0106050a080910050f0f100e06060d1409010c090f0f032306040615 63
    0x288603070706021000000380d034255007082c140843d441e0380700d01428000448894080c580b04034601800101c0110102d0741e400248813441700344d10180c0e02c030030060b500344c40382c40d0340380480d0640d0b1008802d03203590034080560031585150541c80150786503181d84041d2081a980020803041070814041006290100a11080401d90000d417109125460011012a441e0300600c01e100c000c844800c402d0380c1b0343d800701281c409501e030708002c0410070070711441c001d4022400885c0240703407120340800e0440c00c40c40214100c0d0345c1640d800303162002c02d42084500d600c011307000100a120780c0b040c2d11401c11039400383e58480c0400380b07405c103090f02d0300c1106c44010540143c07005040303045440060096400760788405034004d000340c07042da990f000ca05480100414100d807640440350030b058140400b4020640100e02c9292241d0348034042162910302c07409a11220744166150701c00071100420019030345c1045081303621500c5800801e1030140660841c00c10302c1c1120119080380d5684180380b041440c2c8180d10019011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 198015476 1250 198014226 198014273
    0x4150905041d1b030307060e010e0a0c1401110c011404031707030e0405070e060906040f080303070206070206150d030e1e090c09091807150203040f0b07120c0206040906080a 76
    0x6441010984034801d51b000a84115203810544640c0d020940000c4241d5280c18225002501141041c012144080c0100c64141071390b542c60410940c4180301555459003040080c0159092000c01074a58000c0540100000c1c5400e02000001c1810003683d0103030300b007540400c2c0e50340d0303401880d006002d886440d0341680b28501c0e08050145460781300203030101200d4255422665402d540e4006142800782d58005240f05c03128680c0401c2203c40440a14064941c54003107400c3c030f4603010400d980311141103070051807189400c86e03803240d1890b003035000a10140c06070408030050300002000c01c0c0c070740000d0035020100d00140c520010b001d050034244a03a00a100074000303405d004403007000980f0013001405210000145030010042e51009100030310080026246541c0141812000030351690450b11401034011250701c00003540807400c04c2243c049685c008440c1c0c43e0800800005e0300c80310300c0000309a030000014880494800354034803550010300809402404a5132140c507003001c403021070101c2600b40d02c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 198016726 1250 198015476 198015523
    0x10b010813112404080304150c0314070f0b0702030c071a0a0c0206092205060405060d03030c0e062a0712260a0c0b100b04150905041d 59
    0x640341040031128160485020f11905907141800241800f10102040c040380c002400180c1c002000000780200c40900f0505210000400800d44244039600790140119041c1d40b0650720040140005040c0ca51080e05503245080d2180c070b481ca40c0c000112030401c00741e0310001d076107807003184204101802080480c07100e4205070814804c1c1d00003130250703c0e0803805100d6007205681c215030345c1c041900d00d200c101800405000324841248040716140e030301c070044401c1c40c0401040ea01c9c00d2034015130340300d030030054542d0174044001e9174110000e10b04108032208001c2c0080030041e890341c90307000420741020100c400c1c11510b00c19803500c01a004821800490a600050f802c1006c0c5038001c0c12400c8081c0c000300121050210502c084801d03400031044c80c220444005409034540e600128414100b43c01205407048950391407240360882c00d402e00070302415200910040014120704822800400d02c41d15204101c0e81c1c1d540c011505a602c035824010f000800c030140e416003820b040081052600042e50500c0018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 198017976 1250 198016726 198016733
    0x606110601180207080c1005041b0b09131b121a0a031209030510052202030606060903010b030f0f010b0118030b150d0c0509070201091a0714040305010b010813 70
    0x4000b60300c8551182e80d00418181d0a0242000c2560300c00701041c001d841078080440c0c007210041004179004ca4494441b04a03000b0804107580c130240650f90000351040c5020380d08000c2044034a418a990205c09440300c0c080c0000d4444d010120b60004100c0d111003042c00c2c43d5501140549942c2010080f080418901d603d01c0740d51181d250300202c03070b0002c401c00c0184d00b01d031104442d0400d0315000a04a44a841001d003900c01699005901c1081ca2240490081e441794004c21516000781102940c59440301012035840c1c036080008007280d0400900000300382ca4501e010a04004000c0054600d54102c42c19044040c0c17428010040b0004c42481c14044220800148004203003580c0006403e41d9209000580c0900000c1c5110720262300c01002c051059499180c48201200d850040a01510048000c10f4400340140203a810655100c803860f0001100040c50300344a250041031401049180040c03950031484a000400256000b18004030f007800501c40054032003c005010b61105010081020011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 198019226 1250 198017976 198017999
    0xb0319050604021005040b03010b090102010c030509031b0304180f0e0f0d030903020c0603150f0901050a12050c04020a020f0105011d0c0901020f030c0f01050c120c0a03020c07090606110601 83
    0x1941112201040460204e0480e414040c135041107544450000000c60302d039010001602c01c4683c00d074001c0c0001d0540d0b48048054030720594405081d540180702e80c00003000800c03489400280f01100b241e007000d613610001c03040d900c0021401084280d50b000c03840da04402e503029100c0d5440307141000308680c06c0f01a4411740d4401044060b05c04155540301000c2c01c25109204004015200138040764076800c159619102007144a002948030303003500001001e450405034030781c40c100d840050007440c3c16440e00c008001d070380c2c186075000c5886024156140c2c0050388d8504c050b0a4502d5590b00905260b00640219402c449060b0015540c5204c0720000381385d95054a401540d0000a003910b1689645008005034600340b00066403007542d02010400c4042000005404008103080d140240840c0d00c0300c2c044841c4501ca118510b040700905100040e807a219a0030003401c50088a140052800704520040c0303040504640021455036155101040250b9000101c800da03451150f016041551409800341070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 198020476 1250 198019226 198019231
    0x237080d0c0213090b0103080a200304050f0121050103050708010908091201150806190b0609040510030b01090f050601020606091f05190f08120a0c060605060c010b03190506 76
    0x2141c5400400b00310f8151168100301c060691000f201d00541d61203150180407038011100300800102c089078030010481c503002e0004c4540100d03002035072401e03040030305001241001d144090706000c070f88140346005403c4011012061550380800290715415450001e0412940381d1060301c96030f04101c7d0080c04035100720200c0d60010011030321341e8501942c440a16014182411707100c1641100c07000001003400c0041101481791041c1c4011200070078510441204581d580c1d03080c01d406c640240050303e160300389580800d4101680660100b400d1307549903115405006e0980060080b02d80760021181c5203a07140c058039030001005d0001d0800c600c0e1850200700c078400002c00300000594880341240d542c0000d0010b0101030315001e4000300b0002c08188803c06105624400d5007c546496000020305d10008a8103504101a241d405460014400800c89800ea024541580c0042e5228030020322945e41305c005100d031114080003c01d03105003550405080c0080b801d403289800c401603103094001500030403481d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 198021582 1106 198020476 198020479
    0x2040c02060a0c09060c20090721050403080f06060415020703170c06070e03160303020604021018060503040f12090e0c070c120237080d0c02 62
    0x104c00d07000501c190030000d00461000e6000958040c4040c1051000d8005150340322084000900c1102c020b5a101000c2031640e035075000144100340c1c01c94202200c4a60800c52480c060310050070000b0010580c0300003400c0c42d4001451075941c40252400f4140300014500485038007070703010355108010702003501c00c02000038207104041e000710111070018042001424441d1101181510909480000e4039031501030340b43c2c0d500210007070030303400002540039900400a60405006202d400801d0601c02410000c1e9042d00c5e40741140315201d2034086402c02d10345281e0380c5c1d40c0c50421001656502000500c0b82a0b4200705d00103559102a0354400d5500c582c2d8600c550351a288001d5030148a00c1a00500410440c00201310801100151030700d03490024000400350321018011581030000400c09802e95a0300351440c541110242504001a05102004100402110401403c0c172000180001d = true := by decide +kernel

theorem cover : BRFrame.Cov 197841726 198021582 := by
  have h0 := BRFrame.cov_init 197841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 197841726 ≤ n) (h2 : n < 198021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
