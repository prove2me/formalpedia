-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5006
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:26:17.987982+00:00
-- url     : https://prove2.me/submissions/d5e84c21-b7d9-4b1a-b89e-de5ce7c4ad65

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 900179856 ≤ n < 900359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 900181106 1250 900179856 900179873
    0x2120105040c050909041a01051f0c0206090303031302010f0e2407081305030d030e0c120712050307050d090312080c090d031706041526030f03070f020604 68
    0x103499040c0c41c001500b01010900b50f982e4041c0c604e0480d0302c01110b02c03c210400800c03161100c2c4a400c441c507454040d90721101004009041c100b4040d01e5208505020a035040c419001c0c13030102030000d00380324540394015000c01d040d90f008031100b22403d1081e030b507460111f50b0311000031550a0030320b140100c0036544034800a000c1d60101e9281d00402404005800507401d102c200b1160314035800040707184c1c0c8000410f402c09840c0180d04c140ba109001d4142e050240500a00401c3c800b0f981c040c0145c001c81074002d0801c40c0d888020300e0394054a00c9400c4021072060141040c0c2440d49004034010358445250b80b5095180c130980030500020040343c40c3e020000a504046802a10318130740c01c14003140e560b0351481c00b420303005108802c3d0340804102080000d150f0003022220415040e18078403401941c2c2e40d024801552600b1910300082d02004508108454101c2c80e5032011048828140c440088580001d5146400070090640d440341d000040c0550f42d900710344200c4202100e030010300030920306511007240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 900182356 1250 900181106 900181109
    0xf030f121b200a030806040b270903031504050a0e160306060f06200a1a0703050a110f0c030706150e0708060906060c013c02090607060902220b04050604021201 70
    0x17440800300118502d07560f240c0000c49280f00281c007000040c0c0b03030800c2c04160300804140c401850098240411400b500c0801101d10072207409009440302402c100c180300080500610004100e0780e0703010382c0c56041c1010721101c60781285028038140c0840c04e504100088894640c440d961840c0344d50f5040000c2c07900038140c800040058810410110f8030f00d4001410f100542c032005144101c0100b0004400d066227920500502c059a0204115620006100f0858540c07400c0900c100c041800025a0000c0000007410160301e14000c0d42d0401c101c41d074800090310030440650b0303040383c01c42c1c0c400d0040c50f2200c6425a8016a40e04e00782009007844d1002c50f401c00340140216016038400583d11000300002d400518030007a84004250201c1c513428840c401016a04040d400116241e04d0b5102090010b4001d4841e00b0b0801003059103880c1d003903540c040c01030090381012038102821680c08080441030b100c5c803c0003662407910205184440c43c0c20407003116402000070b032181e072060103212450100c2d41080ca0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 900183606 1250 900182356 900182363
    0xd030c0905042a090801020705030403120804200d240b0303030f1b0720040b0f010207090f0e06040305070b31151805010b06070f030f121b200a 63
    0x141018405208a401134001c0d0000ca455600019540d0100000000103108490050380c2e4801c03c0c1c542c14404580c21a4180c83c05010540c800c652517140740480f1580c04d50203680100b0504110346540c0c1e48100303001c1440090407000400b81a15030361040c0c0341c020195802c0c0214040d42c950b00d80115011824800174000f403c0c804d084003400c582010b5560100c2e070189030001a681d40411020001d00d83c1000c401f0380407030081d420486c940d80f1a04104a030b60780705081c160040e00340182001c20070001400300d56a00c883c1241c0782d5806c40020b00c000e00c0303101c1c082c9000f0b42d5800d9031800a410800c40b5004080d20301e0285052181d170108090048200001032846590b003c04a69031031401d04680880c03418440d1030401d4541880c00c810203003001c0010000324841c60090104c030b03410074200a158090488080c120204040740200028801d14214040321140d080a46010540092100803a840c0c61084400308040b00001c0842031b801010360b00f101042181e0034402241601205902c0d400c8120008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 900184856 1250 900183606 900183671
    0xf1d0a0506010504030204051609080c030a02090a0f05130309081204140102070f060306050a0503010207080f1b0313061b080a0f200d0801150c020f120d030c090504 72
    0x8415a01c1441210001c46e0028000e01040c20445443e541244001500e103005ca503525000081480c00420700401502d801009007084559a40900030720100c014084080190740ba40702c4940e101007440b03010300602d14002d0f9698a0241450090501c20b556085090203a01401c0d001408241c85002c840503a90602c00c0c85001005200060345424800d4101030039030b10002d03c0c00325007160301d0703407100301100c0c02202c040c6a2030340d46005040c201d100d440400b0308442000c21140c0c4542c21003100034410508042040c01e54240002541821500903111080c00700c4403031703030080144e60752000c0440041d0726000641000c002450740da0310114499504a0001e01504000c0704040502039421304500420300290000c200c03507040b005a803a40c124800580115244400100c3c56804000015440c98015299410b00102507003c002e40046110052036000c3c100001c0650b8200090045040d14401c54034081014a031502015141c1c01241d0491406146851998030103150038419680c1042c6412603034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 900186106 1250 900184856 900184861
    0xe060c09030f07081006120507271806060602010b010801180f06030507030249060903020d020c030d0206150609060f040f0b03191a0a0e010f1d0a05 65
    0x3007400e140740410b040c103450144140000700c1407004030320b10328500b00d0300d00200200c648410410709815a6174001900a51090a05000b0480c05040784c1190279103c1d840007000c141400c00300d00a64401d14004040d48031418002d00030450740b0700407a40030308038030b000a201c000030380000201681814881e50400d00302c10711503220108059070000151402d003031000d10081e0f8890500941d60850347c401240075100755105100709082c43c00300780100c1c20b4a0b0400001502010800204003007000c4030210350081e42142850010f80e90740f01d4214482c2c400d0300070302003460841c6800381c24084407000003400f0782c1040d4581213a10b07a010a00d19070203c1407620140c001526180442c1c03150152202d07184d040140091119006c4551070040c0c4201d81048202c4140c0c181c07118055a42400242c403254044941c904402d41500c001780c2051000190014140354407500a9001070400300b1154808030007584804010310001904c92100c001420300e0b08640c4a0304e00e50f10b880301c94039001c0100503c7ca119a607901 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 900187356 1250 900186106 900186109
    0xb041505012102270a080304050a090c051323010f0f051303051e0c030a0201050409020918160305220210021006090204050906010c05030f13120b190e060c09 69
    0x1035400c070b54103200404d21a000703054078000d051400044681d110380d0300c020000075800c800100312820303140c001e03000b80115450543c0318130141522505c62018400305200584094800000c1c030801405000c4100302a216031002411000b500c95003600e0400c9410700c0300c514025001001711108080740d00c4c01c6655060300300180f24410069800c02070141c01404c1300007400e0030355a066284c140134000f055a643c05400010140c0d5910a808003c0c00324a052004025410403039000d05101e410240080c16007a84100c0d9102851804603075840e8580d05002541036019411320451f07610040303203604a540807540010f01d5442c1d01045900178850ba0003a000086810300c2030094100122401034280801038940445801a401c140107860040602c076001816562003011fa905c6803a42210181d0301d050080d240c45945984044940340c50002c041c8400030740305140031a800c00382405011400003500306000002118a04024400701c46400c21140603100d407030114000350130005803511240d4900b070400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 900188606 1250 900187356 900187361
    0x11809121809020c030705060f0f1311030604051b010302040b0909060a0b0c0d11030a1205060319050f0d05031005010c02301e03090d03030e060a0b0415050121 70
    0x7045103451500100d04c011009100002038070038a440f800030781c6d416940d0f1307e900001d40c1d03004840c1c02060300306a00101e1185280340c0c20300d009250040e90740c0311642e01500003181c81c1260590301198642e1000390300314182e407903407120b20408180c01d04c1d0540c40c140c40c00c1006504c0e40100310980303114031400c0b0003007400c079642c07880308000900740d195241c0d8540d8410350302182c86024407241000070030f01c00b050140103404048220f446042154940c80620b01c1603038450401840018a0107030036200e2040310000b440c1c024803800000c1c0b032140e00100110340e80792560b503050400e18114403040c0542403041c400308034004250041560420b02c4e00044034105400000d001e15090031540c2116030f2107109903070b1001ca0421714150000030745802c84041e541202d040682c88205e40b051500107407c140040312a074900b10343c1682070305000c3c0c90007055806030900c08a0401a084d140650640d039a024410302c0740c20f290191901e038409610f40115280e00e400c0020300482178149001c2c40c0c1107801c0c0000c03e140512075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 900189856 1250 900188606 900188609
    0x160609171612020f010c0201120e19081e0304050304060e030a060204081006050108090c09040f05030309160f0b030613090803091b06030103050c0909011e02030118091218 75
    0x4031690124030b6848540c001c1030000c010090b401800d404603001c159500400e03803400a103506a43e601d42c1c12820f64100001458815005042c901443c1c10345403000c2500c408000398240030f03940d4036650b90512085500e84100c81c100211509105004200201d9400b00654044400500b00b07001140f0f00346c00040d00380002154002d10051000c64041a40a800154020449100d401c1004410344030b4006451880c41180c50060b00d6100039054901410040c66240e0818815a134000e599111a501d06013035400441d43d180b40d0382d100c000880500007c40742860010004070854010307841c10040880c2e040e10008000d07074016290202c085000342c01c145e01200d500780e00022659140e040821029440b000392600c845050b03142c0d07040f1004103143c80412603040702c3d8040010064800b0400605c0756a40f0003e10100e000d541e01c040d011600c280341c11807140190000b4100581da503040498010080400d0951444104e182c22504800030b50040c0c1001002285400c0c8851041c80a112502e00c04846 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 900191106 1250 900189856 900189883
    0xb151302042c190e01020f031b04121709040e010509121c0c0215090105191e0506060f0706092307060503061305090f16060917 56
    0x190026012011040d80540191004850400140800e816550040040c14084441c8080d400004502c440750340740c42101d048011680b011909158019100e4220b030000380100e10500000001c0103117210184000504800b40304900070700b0300e81041500002c0343ca01e0031004011180d1480341c0c22841e00460705071664010300900512200361010940bc0c00b90201b90781e40b6a0521403111040d00f1480343d82c09550082210042c0644030755921010440039100310002c41081d409880c409103100b01d58440304911941005001046604000c10140c00c0c0ca4080704210021501e0800314180b420314904a803220080029004165512842c000a00601c00c4115840f5055400260001000804c0d04102811030003940c0703181c0e0444a1054082e5000c1c141c2024083c030790030004092104a005401554000d030003d45140c543d0074052441c0c0c001c4035000d032040303000c82c0e10032005254800810031000c0c0c200c00d4169503200d021840c0000181038403649000c1c0b441051424116061420b500700000c2c001c1d1040f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 900192356 1250 900191106 900191119
    0x50901140c011b0e0d1101140301080714040504020609040b12030703031506020a020a09022107030f1116030c14031306030c180303050904060803030c13050406050a030b15 75
    0x20240c981c03402400e450294042d403003e4a0784980c42240101022a00510081c20b1700444500030f070b80e01c240700056101154140704400c800381039910240009180a03050401c001e01d103160900c516030b24040c4004418500c1181400b0070000180c5038041a607107400c0042e5808160175090900040c10b41d40129240b58a81c40f0104600050541c075411a10700d641d9442d10030072040352682c2c03089846010740301d0060b400141c2034404020303008003540103100120b840c50240c0040c40c08114440503400302540c82d070000944074442c01c44080d13014030032185203103045500c46150442800340c0e8601004c014201605001c1c281762560f0031b0010711075400000003903a406907582d03640d04035007070141d0340344da0301a440000e03240c109059281d5000700c4041c09486c90a260140880f4075542e01211950300200c080d541003a03d9000024034201c081010314010380880001d2910340310130030051001140c888e403186101740d0915804010b01e4940c0d6400754152500a400002c1d255103190701041c819840a158540094 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 900193606 1250 900192356 900192367
    0x1b0c30011503020901050d050d11100f1a0103060f140609030303041b0603051b210c03070e0f150901110601080703060e0f1018081206041401031205090114 68
    0x5280c20001800c2d244211205099a62100240019111341c200010b01e55801a49003003c0d0901840280501103400002c0b28410400084240b0585a002200b02421500d40d12444040310b03110780e035155808820329040100501d0f02c0c14400b0720001034842c003018181c080b003c0e0003040c0c54a00c1160301682005c2c044076903a040c180b4058908540c2a01400309030740c241d81012481d940300740105030003007560600210104000000128172540010309011032120109510101c0c000e10350099880703110840c04480e184d02e0000c2001d4024404105114030611103001481e14a984100c03209140f6203112400b151100001c00041e22000d107a043c403c0050b1243c90000100150700090801c1507910032802480720780725901983e03560340d075000d0100c0d05a401c501d4203141c1a0039168007004001c1d020940c1c004070031200380c440390042c0d03001d1400815800034103000c02c406400c00b402542500c00d20b4500d82059580340d52606000c0498030160031041080002e0044001d0b031150340ca484988071314a0b000f03651030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 900194856 1250 900193606 900193631
    0x5010b03060901080a0302030720041506020606100903150b03031305030c0d02090f0705040911040503070f0e04030809030904050108010504120e180a1503081b0c3001 73
    0xd81046654a119601d441c00200321282c000c601c501d43d1940c5500210700b0b140d42e940c0d030000184d03c03101c109841d4a03005903611015a072940655040c40e0720840100e0381d182d0804400a00b00b42c0d004010a00030100c9146114803c0d40c0301c0383c80800c82e82c1010407005600c1540a5420291480413035181e411300c00414a02e20704203030441c2d0003084075002c07030071035549019603c2840252080202302075440541d1000045c0404503030117a00350303c0145464180e191607180d295180486400e80d07114510b5800104092019003070400c100c101078100d40c40c04860342440e101c0c0d441c005a40c000c00080400c070060006c1503501400304251600d801e0024814801581c541420314000c01c01102d00362106900d14042080950040c50088a030510140a0055140202d915180003050140c22826590f9903680201003014031524418043c520604900350740314100c0d88041c5030403d07924242e40d5240c00035001c124850343c0c0c10111420118550441e420200f041c0c40c070600340c17802c88036819000340d420722401e001032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 900196106 1250 900194856 900194879
    0x621101407030c0e090c031305101505060f09130902090705181002190309080f03030108070b030c09150705070f05030d1412090a0f0501140a05060a140d060501 70
    0x10781038603a401c02010b11400404c881e2614016015500015180007140064803800002d6600c030980c6022580b10700c1c02640e81c64034226101c040e01e18410341d2201c1050000c03074505102c4008003011500d99080504196900e002ca1081380090f510450319058801120900c5400121015400801050142ca400302c0e01528650003004440d000f00076490031380f80c6600c1c09003281141080541c0c002c0c26401c00c20160b03000780a20042056007400304892001031b12240c108a031840724051000a562254504400d03d440d10455400c90549a802030040082da02e2500c0d0a56580c03840c111100720040104c0b403406415841603202c09001405000008035a517503600000508032a000d504440384070943ca4011960600c49000150215408001400c8000b00c08901c0340d410503040d0040e120710078210342e219461001c2599040b100769444207003110010004054890303004171105001e0210703103000c00010382012410301035038418541d1200812441e407290204816440d03440030003000103586800310040d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 900197356 1250 900196106 900196111
    0x203010311090109020a020d0e060c100603030e03150714040b030a1a0406120204050411060d0b09131101080405010b0a080c0f2407030c1707050706050306211014 71
    0x10920b40b800040d411042c0c0c822950040d209501138002c0c1c0704404003c880103100e0380480c6030f00c800b05010710b2282c2142408030351840e68540f01c00080c51851403030040c15001488280700c1c070075040001c1668805201e1000d0300d601810340c0c5840340d46030369200000c07003c0380241d4010900c08072002c001c01404038980d03403045a64115184110300701d612401b007080156000c60141000341c105c001800401410140c0002c2d402a00c900130003081001a0400704000b9004010b8005019454050414080c20064149500504460086214080c4c0e0f611102180c40b4175900d094100a15000010306111081d40010003141c401800b1170090381d43c401c90280d507038802c452032070320540440000307401c240b900000000011024500f00c00302540a90141041600300309010780601014410840008165910304081c1400c0d40d0342e141e403941200c1c24401c2c60201181c01100030700c4010000c0c050f0079500c03136106c240c01c02104042601c080e5084412182401c0040c0350418180d07013041d80d907100307019203240e00c0307807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 900198606 1250 900197356 900197359
    0x60e070503040201180e2e060507080c0105130606090902010c0f030320070218090c150c0303011716050603130c03050d0203031806100506090117010306020406170402030c0f0a03060203010311 84
    0x5808164841040b401c200c1901f204565552481100b0000c1034090805080c0f141e000d080d480c1c1c100b5407400c0a0b2405c0d22000c40c0c083d050040e0000f109400c22402d44140c80181c60b080e44200580034480c0d0001e420512030900140c00d002e5100009000c0500c2a00a60303440310820404c42c0450880d840b11810030380107968120300c600901090302550310300700100d483c440c042c80001402003220700e100340621020502400c60b08a1000c01c0140c00490b81003000b98005c203944c0781954009240c040c3e29504000210a904070441d010080402039a600e64003030341c0c1c01c45400b03200d0b240c10030424905154074900340da000600a000f04095040344580100203184103208420900b1001e803101440c0617104c000c1222140d2072105401014802410a500079091246060404c07031029031403c80403441e851800d80c02290200e40004c4c090107002c6e40101c10f416400180d28007004035092580c0040c1e107840601d14200d000e0701078020400c0140e40c50102c0f40e07000710340140045541e941c49061540104059150a0b03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 900199856 1250 900198606 900198631
    0x933270106061716140d0e06011d130209090a0b0c090a0f270212100810060e01090c140d0506040b0f130b120102130305010f060e070503040201180e 65
    0x30824040c42c4624034440c00a41c11161308101030184180e4004c080d41a4480407602c3c10720206030b2503252449092076003100100200f042d50700d000c0202003c0c940d461010001503400c0c0e81445075041509861441e01036048035050307099921402032602c0d001c1001e00140481c8110414045e41d0041e010080c500c3d0704c0f059503110071481e150308038560081d6440c0f1030101e08d8025000200440f14898403000c8800d80f0004001d46003005090110b6201c3d070007603c50080815040e8800c1010040400094807103045130300003441503c1c0349c000f41d606060414842e01502c0c4da22030144a031f40520414034480c003031407000c000b291585070261400c8000c110490340319015a191503800780c0355250522aa40400500603c110560040c3c90005405400d90300c491701d0304441c0c0c4071005902c900d0203001600b04141c4030b100030031090b4a141041030960303142e06810984107180910030b00c400c1d0911414654000b9550900968a48030742c40121116965010301059040c0c0310a03001c0b8100096030015402450440b01030f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 900201106 1250 900199856 900199877
    0x42103021c032004060f050c0c0d03110d02010b030307110a0905071d0d02060f0a02010915020c010f09170309031215040f1a0f1f0206093327010606 65
    0x4051003031044c0c1c090350020480162001111911501c02841d91101c5034040d61414625400400c4100c10540400c901050203284080403800041060070403613081c2c0c0c80280a40405a00481c3d00da106032200a0302c81c2d018800c1c0340000e503c1c0c90000030000e11003e00c04020514102100415140d498007140c038140380407180c440b001c1c0c41c103420301800281c0c000780090f02e081d400054200c15940f001c503900701075540340c1c2943c4010030320200e02403000080445026a4131401d61408908403103811100442081c230700300080b004170305c0c03036480c0d0351a07100408801070f5240c8458030150725501404081c54010313442c080030441c002034183c0b00c0b48810f010a94092281480c1c0e0b18044050710070b0b070341c210303018501301c0c4e41d55410518110024840320000a010b4030701da08503400e001d82089001187c0840075034000401d000407001c3c00c00045250b081e103030310001650608e00d1f44460018510b01300c2e4075494a4a000425421141002c1c1560000c13040c100b40c3c00344154001003507011f03010902c100d101040e0305124 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 900202356 1250 900201106 900201161
    0x11013b0303061309020f0307031209060c050c040903020304120804030c292d1905040303080c0a030f0f0506031908070803040f0c1d0c042103021c03 65
    0x1a203020788002050b2101d40510f026076034000b4104620241c1c4d0208255a411217262400e004d184041c50281d841e4140c00c1c2c00e05a005441d11a25078040010042c10401d2100410f401082da2a01c08004660100d207503601c6080480c41c50246800505120540d200f510b0b041041940040084a100700901c6022544e2100003500c0e10300c903403e1f07001c2a048200610030038610440000c2404501c1052010400103030800c076070f4003100d08612600341c880d10024100b544000c8075103c408003001941b070302c0c9180038119600104080005002d04840d83d2000c40c90120183c000e801160b0312850880f4104203000440035003401402c400d40c0d51a000740680441541d140480d911503005103904104924606022662120010f0740018015a182c0c400c45c00c0500002c1e440c0780c01d50000b40f4180100a81181802c1c2c0704001100300900300303000318a41000200321100c1100d17415003064154464150f1b0000c10341c24107034144a0300788008400c841911010002064241e0301081142c07038050078901d0074800055 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 900203606 1250 900202356 900202363
    0x6070c021306081009031e05030603011104030512071a040515010509070e06030603011508060a06050108223206130525050d06140a140711013b 63
    0xfa00c2258100001448411404c0e80120350a40d00c40d151807100540851840035040800c44505070000710700006111442c130303007401a90082809000b0052405186070345069407507081e10110048140045050700c1401908617030250841d50482400c000c902e420300d00135031140d04c1d40c9210702202c0c0b20f220004c200784c10100115880748215445103012140302408104c4030341c100810459040d074840c43c000500030140500000108801c0c401048981041c42029040d10b8030758004604000311503040000c0090042d103030703d030368911180305400072102d507040c1100e11040145455000c084000006540354541c125030848800c101e1040e00c04580f00c07944c0c07214041c0308110000c7c02681c043d12224140000c0e90340840c48101a170f600641c2c00980d5031000c03031030705d06502d0f00c00d54800f0342c0e1b40014407012820100c03c0b41c1c000410704040020f240c40c0d90f00c2308800036024120b1410000d03802113042c00c1103001d60040d001a000c80c1c04061a44801031250320400104440f85050b5012440305411543c0b40007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 900204856 1250 900203606 900203609
    0x20415120b09271c0f11121c1506120c0c0206030a021e0a09062309010507050d0207230a030305090607140606030c0105040605040501050307030b04090605010611030c03030c0c0a0506070c021306 85
    0x100180c14480ca000c030b0454601d03001482400c0d40e0441140701450310304014450801c50004144c0c0e051801450000003801d080c1844031241014cc8c24199580c040030f43c09509010301541c1181da654036a1079092001009005080e1040b4840249621281c9405082006420083c604c1d03a62010002d07162281220112119400c4001e090a1b403d20482922411400352660b2001854218203001c580d480b210303d807090024401000d40c2043d1000e020700745064010845026500030798001c04001e07280407400c1c4801078403003c0c08019003c124101241d40c3e24048441060708007500080b200811050f05840b1101a00c00d144284619680307640301d54020415581162101e4940d14285803400d401580c00f50f20040c039a40030565070748480350300c555035407295594141c003e1000241e40e6041490150215502041c01d0311298014403151100380b400004a80d07112240542c1c039a258a032101c03145281281c1264010f0031030191108008400d54403003400d003007140c02201c056800844a080b40021031786203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 900206106 1250 900204856 900204887
    0x305041e0206072006070813050619032706050609090a03090603090309090c0e0307081603030302210c120f060901140d06020415120b09271c0f 63
    0x3e014140c041051220140c418220300600800908021000900c0c00da000312411981707a030700440c0c2a041002d0900b540400341100380d07506460030b0044440c000c1c0c00c3c5804120f80081541b03900340c032540c82c501e03180202c91002c400a82881c81266610b80100035100407107009014030303490030006861a200040c54913200b50591242c41d809414420300b03e015009941701074043c45081c2e00e000850500c2c5204920380324100713544000951602108150030030381558403c0c06a54021042406121201218030007200d0b07060a0050383d0391a80501c0111800c0949203040c0d42d201e000c010031090b0710381c000041c0610117607580f02900c50742d60b41c501c0404458003030f00c03041c1c1c1108200c0018001c08011f11007002c90224024040e0a4079883c56a914080c1d90054000c0c6455011540e9041d0040750440c042100d11440d40310240204003a00c0082241100020064501045001c01c007529100740a030000589403101001d50380d0500b00c59640306c1d80400328400c04000641c0d0341e02c004540070b00c5020303d44031401c07c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 900207356 1250 900206106 900206119
    0x30030f02120103080c12031801050f072c0d08030907090905190618120207090207051b0d0b150a090b030a02060c010621030f050a020303060d030e0607030305041e02 72
    0x3d645a000c801d0300020340c0070680340b00d5030030410440100c22001d14801c0b103c0510402c01d68070107011700707400e4034409050b880003151010240031000384c2002c4400d504c04155030200341c6008007004c0c41003440701200c0d10319410034030034070300f010a00c41c244004504c9121404116040e01d903469918104440a002001d0901c0e000281601000c2c03d0102d90406000c0c054000440c80c1c03002940f8480000c014000d0494060030540717180400e190b0140135820003001d000c1000c40c104056500c13825251081c1c0e0440e4254100000740803251a81c44844a54000e13401a01c810038510b0b044801c0380c0c0041041504500c20071106100082d01c418902413032411410103406040c0b280c250b035007800001d030029400d241d81035489600108844114847c1840044071031008150320400c90700700070340060041c096005c1000742c2080003c403903c0c0c002040f81d80086064a41d0383c21030500d0b04007124181941c0003a2507100c0f10020303100003896899041280124041c0522041c03809440280140041c80c0ea01c00a40021 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 900208606 1250 900207356 900207359
    0x82d18070308180109090e0706030606050f16031b0302030c1006030807020f040f022b0e0a141203090d0e01021b060306040f02031906090606080105040930030f021201 73
    0x42034050344884001041c1030041c406a101d1b6030304d8040d200b0703d0030707104e00552144d9000c004c0c00c0e0f410300594004081340d04000d440d24510107440c8007203110300c140d140c02c1803e0000341c1c4420107200b013141000d00b0611034484000101203140003902c9078402c0441c2a950312443d043c00500c14024030900007120381c40460107151a05035400e00443c0b0110400f4242d0181d03039503028442071020340c0014081441c0304012240042e004110700c3d48281c01c561600455180740990a02d40400000f590100e000d030051800d004c0500c056007194900018012094424400070007880384800000428440d8805a6203c6030039110705800126916101d40c0c11107420040440d15031410f82c00c0010040d0780012028001150a000709882c3c0e8040e170f807082e0350002c1e04400a08004807204004d1054078040d10303c00e2000c1c48800e18040d002400088107004c0d81d4481d5541e101d02c0310401141e0202e200c81003405003443d10342c0c08150441e08034861410f0030079002080c00c1481d0405100707003e200b154881205980352000b181d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 900209856 1250 900208606 900208627
    0x10219020d050f18030c1f1b020904141006031101020c090709090902040b03070303020a29070305090a05070b1e040510030917041e06050306090601082d18070308 71
    0x601806030f281d8250081d44201c81003511200b084d03207c1e0199100c4000407007000c20760700920082071b048140710380140e01d900d4000103980f8000344030b810a0b08901c1090008280d0a103450408562039031311860b4601d090000000c0220480d40d0f100915002d0702907441c0c0842d070505024280c00221880000584071000c10f00c8401441d92180740c1c05800644001038640d1031401080c500305161700b007540564032404420003000051140c03000b10324821000c2034810810b40c44000704502001c1c007005c0a142d10742001500302c0300c0c00c00205011542240454070226a5640700c2c0303025a100302080c04801c0c0054440254810b1a01c04072800c031034000d01080741c008680b110440040103200000c0722139100c001c1100e000c10100c4400740c03020349041c0b03040a1710041103100034650101294003842c14000700f81b04121541d511100f101e9880402800c10001a58441030501c01501c040480e034036900103224400e59810f1400a55140715081d040014020031480700749641c1da0380502c3c403008000c0203040250f651a03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 900211106 1250 900209856 900209887
    0xe0114040c1e020709020403232107031103031302040b0406120b040804030b0c0a0219030e12071a1309050c0324060c0d080705090f0f12010219020d050f 67
    0x982c006031042c0c1c2c42c01a20b42580c034059034042d5006551040c035080b54280802ca42c07a6030841c150942ca40180b040e105180002800c3e401d000d4071400707807484013140a10606008105d00e207070380e001d103105917035a0303107080140a0040c681020741680602d2500d020480282450b110710815150400351020119180b40d9503601d00c0a4020b01c2110201d40c184800000180030100303681c050304016010f680c442840c200020302c1c0c0000454500c8000000d8418000429005100b16161640584103a083e001030b5007011452701005602c059000c08510200a08000c00300014150642078800d589480660310f41c002815580e046d100b840c03c101c1d081021a900b407040000110f902100d02e240203455920003c00103260f81c108124842c01c64121082c01c00c041ca0b4096900f6a0189450804c141000c00c1134010500c0160660056409240d030070709444c1441d600c001404521545c4040255940d545c0d054012800850308003280d4090321400c0d50801756980100140d41002d007000c02032070300b49801001ca8005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 900212356 1250 900211106 900211157
    0x618030b040609020d0c0e0a020711010e0f0a090b13020309151003021f020d11031c0b0a060c0c06020102040e04020103230405030a02070e01030804050402090a0e010e0114040c 77
    0x5406035100004001038841d4060b05c940e440c05141400c00592074800c9102e0b00c2d4800074800c441140c030401c401c1e07000598000708101e80c51001e18107142c24003114030111321045081c4031165030000040c840011004a1030300300c0d005580301510240c0402d4280c529040c03c1e070006568084040e00304480102c4100c132124000d5134010402000c20301e02982d2034000c40d0f1400c01d020000c42002072402d1340c03c00d944c0d804102c145801701c014a040300b040036807d10200d03140d0090b035512215016032082a40000c18a60b0001030545400034030f4400b68030f5039410080c00c628501a0b04031040c501c0c4100014119006100395402c0303030005540099a642c81d030b030044000b000300302c000e0941511070584c0001c401c80c0e4151800c2c482d0b88544002e507521559060003925200c1e1542c4003100c2d29074200010300c0040c0c060015a022104151000f58031403500400082c1100a5a0030000348076010000026000020100540c100c80021103010b0f0500501c9061106845144a40c0c8010503002e000134403403c54507180050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 900213606 1250 900212356 900212363
    0xb01032319121701080d140901020c0f04021c060302100206040c12150e16050f130203150306070306030b011a18030c040f020c0f060412030b130908130618030b04 71
    0xf51499035a00036180c1000070f8001241540c4242541010681c200c03c0300902d1311b12440d5218100640d03500000e40c0d5a0310441c8603030080c50b0682c030900700d0381c03502d406803180c0f040036421542060700c01003050380081246100503485020a0f803000710b2007600126000b4046c0b908a0800a102c504107140103041109104044030700c0002c61420500b101440d1091501c00c1d034480c030203403011242101840310103402c5600326a10518510b201c0c00b06a40e10710110740c4441202040158580c3c0c2e40346041d44012004180c556094000c0074200007880342c3c035a0060b82038038854403034800c26980f2003030060104040b02031848a082c20800541c1401c204c0d00b046000b49107070080498008501d03107000706050380c0c0034040c9440e407650080f6072244056001d002046003d02144010b003414685a214009601c40049400080c1552001d80820307680310781c00c0210400ca0705110030310082d086890703c0c40c0281d110761158592075501460104400e44a603a05a089003602c0352110203842c01c41d02c42e40d0f038400001e4402c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 900214856 1250 900213606 900213617
    0x6060a1d04110432010609030b090304031a0f0c04050a0302310b0a0806060306160908030403030f1b03120c0c020a3503030f0403020a0b0103231912 65
    0x40c00183d8860060361680b560246440030303540b6111104542d000c444509541002c01120014401d0b2030b484942481101d420954030b0350192a0341405c641507100f0f680010b4403030381c0704030390840b039088044900a002c1c080d0b0846c2600d540c0c0e22080c40b241c543c011401255481ba4000c0400c00c05440d20f41c0300c038841e60040880301445080c3c0048c040710000508c03d42030f02200d8840100c101c0700d140002001c1c3c001c0c802180903203506d2910800094840900521080351015803c04da120400d05c6044501d020300501d1040b41c1c1e40c3d544900300a0542e50500b03030781d070000032a601c00d003e0169103907208010300c0d0b680c143c503440c003840c94403400800941515103a10b030400c418200100301680d0703024000c10090440344080305002855500742d8002e020500b2000380328440d46245403806450000480e0361250042458944580381d03840c08a04151252a000d010a8020000441880071092581d500e420249811602108104400548505045090000c0c1d10503181003c0041000340c902c4414142c3d0341e1030003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 900216106 1250 900214856 900214883
    0x50102120c03130e16050315150c103606021c1113061d040203190905300d020f071406010303022a0f21010e06060a1d04 53
    0x1411007241440e4400c0b000003d82e0380505c035444440240515002c606403038010725510304070f5111010000005869402155411028a120074420040d03607280b80343c102c20b648030b9041400e0050060101c2d030140001d03001c3d00e01d041c1840d1918568503058481c860f8100c1e10003001441d2039001c02500640701508800e5850750a04294604904c20881c100c00c03500900740d2a40c05000c0040c0c85841c00303400000c284810303d010030141d20300b0b10303070310110700c0f102200c015a480e13492001240c1c03400180b1880100b1b03030b41012050010883c5c0860100c62000715014000c07202c56014141c10411642111040c40b1600c2c208070640038581d0300d400078104100c0b85c42401d40780040b680d030b50282c4030304a40c18401c0aa00114018810103605200501e002d4026040c10300042c104104003c9145212911184c451b2030b80344008183c0e520b0303081c1c0d66401584800c2e80400146100c40c0a180a80404600e101e294029040040e5280c98000c50010507140d000c01c840041284002c40c82d0400d080c0500280e40c00000a1032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 900217356 1250 900216106 900216127
    0xf150307271103060a090915060b180a050616060b03060408030103030f020606060a120f15092a36051c0b060f0d020604060305160801050102120c03 65
    0x6075404003501071070a111154800c10040d41180c5401641c220180c5042062219640d561031940064555081700002d85007036514111039003901c071103402100182000070004128034000098059200680c1d184d0454032014020403060980502418ce800402070101ca0840620600781c844810310512000861410350b00029161900855003150f84a07400030052082681c0045401c000c0c0d10207000400740c5082c200001001405501003607410001c004030420602140d41e0400300396181c11301c2042006e11075103503059020400c1070203078444060801103800d42d860300c60700310005540d01d07100f40c12400c0c0b4000b00c4102e905c001e10100d140000310120505003000e01800c0f1152441c526442e0b00b20702e044d4540400c6c400b003010200480580c2c00001075801001c00c03060031509601180071100840303031803040400119928031030540a504103002040c00300c0d8194040d48111701030b1011054450042808400031680d150b801d0107030b940142c2141040f030302a040080003030480030a050095038200400806d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 900218606 1250 900217356 900217379
    0x515040603120e1206090a022110020d020d0f0b151303080702180a0c031a0a0e18030409051f08070504050726070e041103190207020a0803070c050402030f150307 71
    0x1141821030381c11181d140f100714500b0b20903041404c06949150042275042c1c50500f5103900c18140b441d080c031500020401e11558249c0c0c102c1d031030321020500401c550034111000c0702c01403890303000b01e03405190f0203128180350341000f1055481645002c4800814503045540b02001d940018504070381005041c1200702c0c045060302095840b403504800000f80300e10400342d001b8155000c8a0f04a02141e007000300e004503a803a107080d648103070780d0402046030f141d80b0703140360741501c1710204401c004035070001080100709408540c11007401041103206019190420000942da030124034804d518031688056800c20042c1400d03081a0740c03101c10350070140000080c00792003813189040c4c1045540500c03440d500b001515504038517807140c0038406079800c109135403072010f1000c6948400740c54100e05031b224800040174082030750101c0324070b84d6018018118060f40c03218259560380202c00112030400d6144404200c2d07041ca0302c2030b41d21640c82c41507408402c0e10360245480c07250710340341f2a003605030041040c08038803c404070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 900219856 1250 900218606 900218611
    0xa020c01060b04120c053f0d020304090c0e030a03081e0a090501061401170619080303010806010b0f07300e12030910080a06180515040603120e1206 65
    0x4113800d030070102a403a004a60030540d40005204030081108034500c1a00010720300648862140c810081d0603144c0440138030140c820180650b50700c120403018403401d038044090001c89091f030380e0030b108070a20900305407495243c0307061040c1c0552201c4840d002107440786002e150811400d00301941010781801400c443c030002164a16841d944031003420f01000801d22a400041c62006010701d09207114600080032000b01c3d04009802003001c40114003a50399070558011809003460006960301d66420f03803107403280c00034410108103005c0e103c000a0a105000d00b2260502c0110402c14070344501c5030b0300d940f03200820000d054510002858108084c80307502c09a49000c06c2c541e1180019501d441041059541080303050000940082c400141d440e150400b02900c440c0145c10b02c1c01a030398651207402c008040d60b46c4042c0b05500e20541d0108000466400240904070505400d5603000d690b41c21301095440030306c40140780200340c540c09484c0700e1150b103020303645440c001c14105220301c61203013142c6011000e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 900221106 1250 900219856 900219869
    0xb0f090717040f032303160504080609060417040308190c0c18181e21030c12020309070b0901030f090501150e01080d032c060603011a06030a020c01060b04 68
    0x20f007415001859081062902140c12070b40c80550140c0c21004490028000548940d140304000001c0c880c4990060055502410403107040318098540117424940d0307404203075400c2d141c45003002000b03107040c64010100c5054981014030146400c011446040b11035000400c910100b00024030540300050740014014010b01d01100300000881c1031024103400c8410100482040b904140000e80c0040d42c01c100c081403501800c1c0e0f00810700c1b0554180322050f40c030904042d400c901d8465400b6001c1c01c0d0103621a000c00501c40d90350600014242000008901c019101e03002542e10104080020400c0c000042130008010325000ca41840340d0140c20054903000203044580b82d4640440259140b03041e0760200080425140d446180e505d071094142c0c640381c3d46181401010b4480c00f003c0340d00303880301c502103038000c420744c0c0c0e0341c4101004002c5e282d458030426180310303109500f031100b243d521074120180000200c0d0002c0107103140d42c41e91030496000394402007203403010b9525000001401810040600001c254 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 900222356 1250 900221106 900221123
    0x1d06031303020c010e1e01050f03100e0717150a0b0f0405040c030b010f080705070c08030306101e0804020d0b070503150105040b0435030d0b03010b0f09071704 70
    0x1058500681000119100f107410440e2032828002196902d00c0349400c0c031110314409032413441c413480040b03405102d003108180da03440c1d00000b030040602640b2a114201c6099041010240c0c0701d5078812141c1040e220060300f000541000420319510f082c0780342daa98140001c060b00a46980c695542455402c003140088018401003820400380c10103002e0030300646884e20b000c000d0308039210006481250070a95100421644500282149001e00f044a010710f402643c0c5c05181541c40702c000b5a01d82c0304a8619019070380b0a5000d120980c00380480c0b210b2180607000001c5503d003501c50403103a070400288141c0e4084206504240410702c45450b15004d0452030390f9080c5c0e40e00e0b050807801d6101c4803e401d140e0401408020030480d407290b040176141030710b944c00700000d501d007000d042e40001c0e24408058045218080c03030a01500740710010007001c03406400c1c3e0060104a010004140c01c0758a02400c0a03007200005208209600c0d101043da83c1c009080e00709180350140c0f00e1009a00590126401c039407040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 900223606 1250 900222356 900222391
    0x902091f020a031e05030103140708011b0f141803030d02190f0207080601050906131b11160302010302090d0c2c070f0f020312040c0323030304031d0603 67
    0x6502844901100c019200440c131040c0d000000104144814440901040034104d0709011000041c40400b00820b80314000340b09544be1260500c4414186442407004101c28003500601203004044014000d03000041d06414240d0760803c00031240b0070701c04920750600042008c06034106451014280c00400c0c00828400350030050000742c2501070601f0841c0031743d8425a0100410b40c6d000803514192541610300e0f25154032600b0106092041d50043d201e007090500c088540a85544181c09440b10440c0c0d4983c60840b10b15609a9101c011451012608040071003043c400340d400fa4005010a003405428242e02c900140c440030502c0341e45130040c10420815103440707681e010351806055492142028048690b05000341d01900126010b001441442007030f00601000724005c2c01900c422404001700c1e41090b0cd0285004500300200380001c499603071382085060b500f1107202e00d001c1181d460340801103103103848a40742602e1450400c408201d0683d4030031000e07801c94890b60081c6014499100400c170005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 900224856 1250 900223606 900223613
    0x50301060b0310060f090902030727030201171b040e040209240f0406091107050d02060610080a022512031802040207060f020c0a03270902091f020a 65
    0x15803507a4400d48418009009011552100d01803500c126001404c114000c003100210540d01840b06030b210240c2c1ca88003000304842a504059403480f00280310b000342000040c42c0c070002c44440741900001c6e00145240d68030307509a1102d0000950400c1500d86405414240c1e80c541c180c140c1d0194001c0d4503c1c038002d4040c08118248000080c3d001600169010000052180856030b50301151010310702c50300307607195004030940369035020300c000d011402018032142002011050043d0f120032030842d168070452145401c010700c0495054000c003030052100001040c40c0c001218009805000c00c0481d5500300961a4071402e103241031710a40122128104180c0c0b56410000011090800b80c401458185035113100000203086200c3c041036030486005855090702d0500710000c20b621911003014510000740010343e0350000403880d80c0d4034403903601d0b103c8032000021110340c3c0c6400c0111080b100b0082c0c2c00c2c14402801182c001c4c00e40440c000e021803041884001c02d0048034181c9902c00c0015030840500013050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 900226106 1250 900224856 900224861
    0xc02010516122712030c0c020f0d020f0604080703151103010e0a02190c140111030a1e0501060e2403070c0204020903010c1e08130308131202011d010e0703120903081201050301 77
    0x102d08590a00c1ca16060880c0c0100d1509c44062900c00e1003095501c080c04115078681c0070076002c4e0b45015110948807615800c1c42681e499090105a884569050040310b141410340140e4642c9032040000700c1c2182d2070500800e10080c0c000d49810680c1c1d07001e009020314102400f0601e80071101656032101d00032a24205100758088041d101d03d2181d0402060060a000302e00880307400104000c00060342031440c11042900700d142056424a00b410040001031060303009000300366001c403c4881031810311440d075900344006d102e200e030346801400030310008031058028480b40303081074001751000d4600000500002c1c21968800b01c0701c804100c0080d0b0800144e002442040c071000002d04003c1c0c0c480c100140580308c0c020080b20000c0070171804200181c9440070804584000f140e0040311101048088200a4080c1c41c20b044031024660f40748040185450050107604084040d00300644145800d64451643c0207001d10b021000b03004812200000194001008100e0040d02e00d55003001c03941008209400d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 900227356 1250 900226106 900226121
    0xe0304090b060a14030a06031a0103020102190c0315110a0324060e04020c0705030a06050609070c0b4c0503010227150d0c0201051612271203 62
    0xb0b104107114403480f07650030014907601c11807100c8181d0746030b603a882c8659016010a800080040d0441210034051040306010181039a200340c0a81d6501688401911002810114040c2a140c0c1c8140200041b6041e1010f5040005059002065484081c07101841ca94000303003001001030399a800c0361040c8401d0074590700402c03d50907621903000c0d00c0c042c0c00900441d00384641e988502e80c0000e480c04420000c00030714006101c00703820fa441640150420707d0013080112103541c001c0d00c0040001d04000d1142d81c941014603841003250240361101d04240c041c00c800311034001c00342c0b00b099010040c5151200c0c20550700e41205170145007068800000d4034400c07441a840540240c0c014444904024010204001001d04511100c0d043c1c118246c00100408419a001d802c01c801c0050604001d039602d4000c142d4081054009000d03a80b962000640d001003d40c1c50742c8005400000c0c1e41404084680203000c0c011140310b1b05240b0800c6c258109040c407015400210b0300524118060b000c1d50341c141c050000e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 900228606 1250 900227356 900227359
    0x8060f060901061d130908042d0605030a0e0f0c1509061c0f0204180e06150409140d0519050306030705010f0c0b041506090e0c0f03100e0304090b 64
    0x8072a5150881c064480c0c1d1150080c2e81c0c0107040e01801d03100540728610441c0c900e403014107050226940c80e041400c101d0703201e40030342c40d403569510406040c4001d0822681d940709017240e018940c2c4031b25001003186c1641025120b00600e54603007103041d04002040100741702001031500500324846040c41001481e084083c0140380101044c8241d08035566400c003540d10700e0035130040c0c40c1145511420004000c050150704005110720114000c01c4c80800f003240700c265003c042000701f203c0b05003200c0f0180d449000716020014130b06820030754902070034035030040c628031752003061041060390b01d95100608205e041c0b1440c600150002c211452078411450001868410504000d8550305004008c292120703000c2c01010305204d00311602000310b9200314035940300c507900300c0c241ca422400e0a150095140080d681c0741400c550500401180041d01c2340719080d10001d0400041c101040c51170140000a90381d10502c81d81409010540c0f400860710f4010510440b00d15005127959604210304103045855199019 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 900229856 1250 900228606 900228619
    0x4020f120105092a06070305040806090303070e011b0314042606060a06050706150918020307210212010915091e12030f150801020c07090902030d1209020a08060f06 72
    0x72681c1c00191302940580385810340346180c1e5000c44e420251010b00c1035500282442c40b40d1004c02c43c049101101850007260f035941e031112100145401115440c6039540414024080440e00c00002800381d59038501c0c117100c1408a81c00c15649030f140c0d954281240c0400304449203840c94092510900788600342d80580201d540c41106801e1080c02442801800360007400a69a81c01120855500070b00040043c900341905000c80b4400d000001d02c030310702c079600032030081c401d00c2030101d82d0445d403c40701e11344005601c8012540114640030400500c040040b2284076568030031010010948140850300c02e48418940802c0c80202490a00c000c00c0500103560850b400602c04040003c00f810340d2000c00c407485160115001e000c6445840041034002c00c40000104100400035040ca01074014115082c0200d0030354685503036031038981c0107445580c01d000358182c000c490340c1e1003ca401051400d140000c2750600180302d8145901040c2d001c07c1680050506138402c00400c4010a5082c0142c0c2c3d00550641e0027 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 900231106 1250 900229856 900229903
    0x3061d1e04150506030304050a0611010c020c0312160f0309030c050f010f05070201020f03040603060303120507051c0f0204182412110a090605010206010b070206030106030504020f12010509 83
    0x41c0611420490825002c40380c45802145035560204107682c06020014070b684200e564640707010740311a100e504026015420704c2d43e90300e2018000306400c000320700080d010309030550500d4041c2c662030740701e40c03110400340c45c0e551014400b059114040c420001c5c4070b13403600e0109900f181004404c4402c00e42c00603104803c1ca103228407050b40d02071a07038001c0500d1030410640b5005d4030310060b03082021000d0502e03c035120225001801e140c3c141c100300701300e0303020352280c4004064080d5003000f59082125900c02040080000014000108100e09011001c402c00040c14001110402d826680141e01210340c5401d020b000c130031100001e2054607140103124440482400e0200c40100407000544564503020079050210300904c0802026020111402400440c0e0349844500e800e00412250250600520408001041f0440d00b0011100c90341c0d0018176007030840c0c0c80d00004602402008200700d07048003003503030511981e4880011030311421040c5000840d441ca08800301c5460040840865100d2074103003140c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 900232356 1250 900231106 900231113
    0x1e0515040305030a0806122b020c03070e100902040f0306180b010b0309010906050f0103031b0503030f0c0705100c030c1403041e12091d091b0103061d1e04 68
    0x702c0f00e5184c00d0f410300da60140e0310840090545994481c48107031902419801111407200e8020385400780c41c0b0280202210b402d058012643da5080c0034030780382c041d40070721803d00107418502c2d103035a030144a6002e0046695160013404043e60460b5021014020500310280100f0000e0f004243d44103440120421448125899400d07685006102d01d8511050010100d0300e030840070f402616846410480903c801d0170801b0142200800920013900003540d8580c41c0700804400d200082c102540000065003582c80c0e411520829940140c40000031a0080000f840050350600404003980c20340f550001d00030100030700190a65410780f2082041000c50010380c090041e260301074a81180c2c01c05820020410482481251155004070180040c070349004c1b444000351740403420030107589200c0c21445c0e050f0a82001000525810b4410804681040c614038074001c078030400b0044480307014034000c20390960358002d0044840b0000c0004c019070b5448420000101c2c241e0341c4144502c0342d031004178000c80c540740c1c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 900233606 1250 900232356 900232363
    0x9100f0909291b12041401020903030708040812030c070602090f0909100f060501170c091c11011704020108090a153204030c0606051e03100603051b0103061e0515040305 74
    0x43c0000c00c0d04549104031401606c095045d25540403024088030340e2900d480c03c00c5945a0050722500d890b5214080d1310b421444004002d40f80555064101c442c00c010700ea40d24407020b90001c0650340d4003c4803d1005040315a91a80098001c1a8000c0645204207540418000391206002c1c6002090b041800c10451750740e02081c0324081010b05290820a43c50341c40f0f00e480288a004107281c0c0c0500505c41c03100c400300301180a00c2d080c5200720042030b15900881c00645089400055034660004c1500010300594050200241d0020a4009540c02c28601e0b1303370f410958400009900d01d44564035490003000c07982101111049d8120b61021400c04100c2d4550340c07400d03107030042c002810400b4140080c0100412030300010007811000b000003540c0103105100f500014642c0e0303040f85c401c1c443d40c0301104a281c414410942500d0b040380240c1040c060302454180040200d814040c10075039112000100c0e65981001400b54015400300c01d540717286040200810321580d0a034080c840c04040004000061002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 900234856 1250 900233606 900233611
    0x3030207050d0614100f06080c030a090212060a0b15030105030d140c07080a1e0f08220f0e090303071710050301020304050a0209100f0909291b12 64
    0x1111030748060b00b118904440506980c20130080004010070500208011a0104809030303003d103c01c1d1060380303070b43d81c00031112240d007600c402104400801c04101284801c2d0480c004040c00a4400b44039845004640e038646542103d000400300d6031900454040e00e06811610401443c030300700e01e406c550501c000a619800381c0d0404005102495020300547c1c003860003991901c40501c03003540c8070b655454600540311040980100c4426101c03201c010055000400d1050100d0740250303004280405640d2000b1b9664807413400342ca00c012640941003541c048680842e000b0305280f0a00b0300c041d514118140320654401703014091280c1050042000841d44404000800080d41401c04066120f03044408203805142d0070540e019400081000184480003c1120340184280e4011009903202e481c601c42800b840e0041c0c1b203907400700201c2008149100d800c0a11a180a0303594914020300e68078640c00140c000804c120204100341040283e8102c01c483c00c4180c082c2280210b52a040c80c20011460701c0a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 900236106 1250 900234856 900234859
    0x5011203050910090e010305010e010c0306082a060403140712030512040c1503020a090501020705060d02070618030f020606011d090712180213020403052d032a070303020705 76
    0x10082c80d0b039840f0b80326055140041208481114840d6104c1c18043d0183c681c5c482500c1d0558280040c10055900c00d00c40c4c03034121140407000d0b18078007240032030025a440e00c240903130402044842810a0650b2244000e00c000d502c102d811181c1002152221410800c0fa54072402000329503001c0c03c07010079080300485118030303203182c401c038840d5a130380c6449000250650410380d400c000c06110307d01e0180d0158000e01500449444d041e21035a40c902c0120f9071592035000d925001801401200450700f40c54000d455084e2107101d011550009420008014045c06076003a40020542062025081e805020081d0481e400f868044a80e0382c10680454030541c00c4100940030302820400070f09868441c1c20a40c06890801d1030901ca070505207800280240c2103441c05a01c9200075580100c2e1440092003110100c4c0d6000001d8a51403025802c0003038810003c035071002d03002c420000d10b074040035000e0005150400c0e6240328402000303104002c5a1401c0040070481b2000d600c54007040c0f000c80d0b0005108401c4890 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 900237356 1250 900236106 900236119
    0x10509030406091d1b0f190e030619110c030a020105010510030608060f090f06151305090c220e0a0b06040c020606060c1018050d09120213060806130501050112030509 73
    0x4046801295512070381802d000040008030300107207c00c41d004602c3c502c4e40429a0346201c0b2810200030182ca070b0105540321403a10814a40c03c049030310094004210000724490034038101000200343c1030542e80b1251548005035503402c0107011518066514030403564003480c04200090420000d540d03a000098000c0e804004080d0010310741e4001042410520110300040c0c800c0c2d8140b120110001110319114a4400c3d0010110307400203400354030560340300703039002c0004240400084041c482c00b40600045840000c11031001c0980d400c0e9140140d5040415010040002185505044510305001743c1641d11030350400801c94007003503001844540004c0c04442188e0f5491140c03401300e28016002e000c009000d0f003040c9285075002a034055540005000c2c20903200ba92440030f104030f44a00ca5030141629115090340240701505290b00ca0407a14150850300089441c1c5a82513130349880001c890003560f82800d410800100a401c0c0900750040c6840042c510010790247d5000d040345c05203480700c0f4007a60 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 900238606 1250 900237356 900237391
    0x70305010b0c10021309020d05010f050609090a0b0f03160603050c093109060b04050f071409180a050420100305040203030909250804030905120708010509030406091d 73
    0x3940c42d05c290000b81061a0115070720500c03d5004e2025150074800c5005060541800048500b0020704482c0b01c00d0b0014510140340d0364500502c1c0040c80090516a0422000ba07000c81c460f481c10040d95030701c2c2c03400b240e1054180f480c140d03006083c0c410050054103421010301254202d40c0311191128120040b05608072120380281900940e0700d95040f035030300c8500d0300b0140782c1000e00010754040c6184000588041c025662189000c0a0482095640e0030010f915000c2d03d0083c0384d80f0300040c1c91808401410081115031898200300d81110545a001d0410b54800501c01003000640f03e000325030010208409000005100007220f50f1101e1401205060b01c0b200000c00315601402107811003280100040501c0c200303a03901030f4a1128104c00e1980318542d02156100340390240110038410750b49035488600c3c00f030501043c03050003440d80b00b40e82c1a91207091400300e40000c0a00850340b203810500c000355116450250001c2454955501200e480010412012645c4a9441c1d0241e80030008542200208 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 900239856 1250 900238606 900238627
    0x801150e1012150f08120f1b0c04020d0618050f060d0609120e0a0905061e010302070501050106050307090603200a0c0614061002010b0102151f0e070305010b0c1002 72
    0x500b458225081000f052420114071034550341800e100303695008044400803e005201940d0511405c2c8619680c220180241d004501008590081444c0c2c48001c0e2118114800080741c182d03040301d60103411290f142c01040c480c44c0340380300360524074254008040c00304d0b007854045d20181000190035203014401402c2c6000c10f11030650420700e50b4540c4001a18414594400c1c001d03e400b0007200107500c240c0c1c0044000844d900305005190160300020109d1b094141141c407442040c1e04030107601410704d6001d0150002140081c42100c3c000d15690722074aa41e4540070000505601031600700b001031601e00782c501c81c03400d903405020450388038601c10510740c0c608a041c000c0e0343e6209900802403040303081c080d01e81460140b038a4050b01800c8182c4001c07556440c140810781c280c13100c402859005070302607440e103205400880ba119800150b1860300a018849104d180543c0d50141e80160303810450300401e10604c1a8584aa1401480c1f111812401c0084d1075141c5502d42d40c1000d00c00e000c11385c0208085150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 900241106 1250 900239856 900239861
    0x9050f031203040b0a0c02210d090506040302010519060e010506132402011422020a090903030506120f031605010b130f0c0f090902030a020408030a0801150e1012 71
    0x201410540700076181d24040c40c001503503a104030380a4130218181b85107a0003031400011045102618040300c40801d5685c070000703c2854020800c1402c2480d1900c008c0d8000c154240802401640241d0010419103420155090300b41501e2074540125840c3c000c082190403e05072819064131412291a660f8140c03017400410007181c19004110300e010400d81d80140c0030201d40303444044203090340090100d5900c540341102d00180448030100f5901100010560b800350240c10168003a2000305007001007610385610504407030b0001c1c41107011a90340c80900c4410710b04581140c40101041c0b0040100303140c40c8010548074040c1e1ba03241d0b58a020801440d004001c0290010400804003801c2250420f02c03030003241c03000e40604041100100c1c0b901c1941040300c0c1c0304190b1038010540a4a8021183c0d14120b4150002c5d0b20042000000315400e00001c500501c040c00141102d0f0450303a2181095410701b44071100c803078128689201070180c0e00105052544401000c0e203d8042d1905040d240b42000d9100d0102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 900242356 1250 900241106 900241123
    0xb070201120213080607090501081b0d0e0f151302011704052104151716021507050702090c0a21180501050907050f031203041b0308040306050601020d09050f03 70
    0x10070944200012403801c900080d170b58850001652151011640c4000544083c40705840c100f18001e00080d14002120101c0014004440034000010b0003d030072464150812911025004054200e0f4005510300d18014141542010780d1610440c000d0740c09600281150300105c000710075040040001030280101801812039000c8188211145800c1ea9600304040340d11500802e0040c0c3d00f22200d8191480c416498202941d0810a5000040d103ca203000ca60320801d6907207100c00c44c4100301c1d200d041d260f405842c1c58050232480d01c0310341c5c40d400c44e0310402100c0c4070002c0c1016003949050200c11142948051206c11500b0f600101000315840c0e4001c04014001c038070b120740d8441010010601c1040740560210340f00c2c0c021282a509003949820070080d98052042d00107038582d00612081c40140110301c006c6030040e1181e5020040d0030301c0c0d4044031255912661058905810100c0e041041c45880d014041d804842440900f0340c89014400240c1311410314000c0030300038400000259402d0b24200000c07007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 900243606 1250 900242356 900242377
    0x90405131407170607020c010e0a081203060301061d0c0d110c0d02060901090201020c06030702011803020d0e013b041a030c0105040b03011e0f031401060e010b0702011202 75
    0x624400281c0461592001248a003240d01d9110a0324500200004910b440c0201400e0340074240f00840900115003000209101035440070304070b0b4000440c101c0801c00c41c5051001d0740d1311940c90346011810113007107580c00c0d446040b503140401608043c1c00e80d1143c080e507016001201890300c80b030150320048014034584010004107080050f007010581000201c40343c1000c201d07803c4035481e0742c8019429090f52a4044000d0150740700300c101178100d00c0d14502940d07100005100006480d8806207090030080030400303054001d03801100d080521242c0c4107400441d002020708115034001001d00d080301c0c10080d00c1d18001d402014030000d4441c0c425034820320184090008005204d44010015180160420050080e200b4460301134208045d50080c41544c0480c2c038400200740c1981c0c43e00c00a030030358000c20305a800c03592003074140101c0ea039112170100c0700184d800352020560400040b00c203d421520b541d00031030104e00c04500101f2616010703104441340301c3d50a01c0d1402c4003451880c1d4550190062403400d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 900244856 1250 900243606 900243623
    0x70302150702071a09040e0319080421080a0c08150f0d02041e0b030a12051e04030320070320010504030b01171e030d05090a0609080d0606110309040513 67
    0x54031084c003900090520701e002100e04010b80c041c1200295501d120f604081103508414002030020b00380101a0258418001c043c022041e1242c010380540148400300d0319404260814140455900140b00700009004903090242c501d00305029030132400e000142d062071040c0040c810b01d65545e1213600c0001c0e4107641c00b800520800111454070b0364000c1d080c01d081c040e41d078502200c80c0050b00d00007564079051a042031440c4c0443d03480090403a0300358800c9141036900c98101d01540c4c0360744400c80040000390300075514480721442d110035002e609050300301508003603407040340140b000c0b074056001d520440c00e1110b220b541040301d00f00140c44c5070186a2014042400000c00081ca94001c6a581c2c4030744402a0706841d01040c000302040c10301d0021380082d00031948140500c054070301443d88015003045072141200e50f20700c155036901c401d81303c60303e0084034605004215910584080d0040301c0c05080c0320708058207811000d1180607038a005184c0070901c030380d03180d070085200000600b2007441100e401c00a00b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 900246106 1250 900244856 900244889
    0x1805070801050d03170c0306010215060d020d17041d090f070b0d0609230601050a120f0902040f06081b1806060c1e0d0509090403080c210f01080307030215070207 71
    0x81b44e040c2d00206e40e1180076000c2c00503502c203400c0c01040303824032421008221114584207030b000d005100c04000070882d42c0c0240d212542040d06c008030050030007031a001c0c466610640010300910800540500104003d80c44040211071840000c40c600b420346120344641e0707440300c00c1c15044070050220390b132003100281c1c074100e4045c51030315007221b4000044440c509101d40c3e03030f15507100440d800c2c40b400e00700c1d5001078030380c1058040204042e0002c241040d03416030040303454a02600040d003150160b0361000c4603184d9841c01046411418880e030300141403e2071040041c20100c1c00881c0124002c0310201c040e12000764005001941c800042d40c0039003016030100c0c0c0d003500c0003c8203580541c81c094a85181c2c0d01c00c2c169004c00c8148640115401c0d034602402911440c1c80d0b070b56003502c180c28050700d156521306090103680144040c29010159a800b0221201701c18184000280c00038201a04500d407140c00070400c010200c0d40019050b000d0000075840c96485580e0440201d0802010343c02549440c0c626400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 900247356 1250 900246106 900246121
    0xf010c320c040c09050d081c02030c03060a0905010b070204050405010608070b0409050f060d0303051009150f080c01050406270b0307120e060a0902150c071805070801050d0317 77
    0x1d11455410041c0c0d4100a84059500140c94441d4644a12139014200060010006281001170101d2040840d12904407803206120300041e60400c94a2010500c0003100704165450900d40400091404840801c6207504010440740184a01307074020340140d89440100d0100300096001d00020b0008806890215840785846c4c02c09506c18411003200b54102000714000c01001802e450203040001c240c03090340301c110b0360b0a0f8050100148404000e1180c8140024894054090300c0704100d00604000a00da01300101846030b4010713a04080000d502080807542166001000c580603520281049a901c4401c02142070381d003403d50312011100341034030a000860034580c0010b98003640668036030525060128211400f04c0c0e0345080d908203a070780f000e8040348900060350310490a85002400741000da12000012901c01c1e4001550b00c0c13225400b4081c00c0180f8802c075601c00800d031102d207001b0f01090034680c00003008003506000b441d201d2480740043e5820140102c4000d5540350200004a50701d01d000c0d203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 900248606 1250 900247356 900247363
    0x60409050601020717030a030c1b030e2d090402060f0c0109060501051906050904090f0b040b1f050907111603170408071a1b010203150f010c32 63
    0x194054058031031550081021410503117446248010300c80118100201020114060700747c82080106001701428070b082604419281c101c20035000ea00c8140c01d40f06400240010300d541c2c181c0b003c094252800d152103d02d00e0020a41c0080b4030b0071107442d24541c58600000c2d25034802d00d102114200000115081851419001410098040c800800ca1a0380c0c400511156600510190390344680b070030014040d00c1d00032809046000d80140000550030420360345c82408441e00c0c1001e64404040030200010008070032855540100b00300403803449511250b03194019140e084c014a8803800240000500c3c00b4418180b841c40040c00108170741c00022904040d41c43c100d06070005855103150a040c030350000a019044404561709034000b055030701d01d000c48031150702e41c40c01d8101100380c50800001d040544000a083c0c800091040016aa41000030038161029048420b05000b00c2100000c11032a0303811040d11f600c103d8000c1e480740b01c0e001800740045d0340c0c2e0802d120000c1950b889101400d20114001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 900249856 1250 900248606 900248611
    0x1404060b030705060405130c09050a0815010f15050a0c0f2003030903030703110304090e0f060709063c0903020112020c07061b200102150105150f0906040905 69
    0x1070301669003803074840043c0000c42c4143e00800b80c1000070840110706148490b44001220302140ca01403640544402c002041801154000c2c1c403a94000b00720a80e03d40d1500f50081d0040c4503148455080c50b2410040d07080c030481ca140035106120012504144007405032191040c0b19900080c400c02c42078640c84d16401d100c480340f0b03400c000004e0101c021681414004119561988014001c0d41804072a60341103401091075403100241e0302052000286441c04c601581d140a2008000351200711001d41019140c194003c01c00d00420400001c10040c0c2e9401c6100090000c0ba13525200103521080b49001074080c03940750500c0ca0a82000d6440800c45510204850590380700b680c1e103250b07050030780c5c040105030300500741040d000303400c1184200041405000d00d548081020312508184046685a4a442c0521039075190140d06559440d02019a0706010446c5150740c5280b9405082d410900810082d4514a20701d0700804800917000f02c04003105410b0b114401001005a503071035484001382c1c0042d000a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 900251106 1250 900249856 900249859
    0x806011d0a050c0913020f0a2007050117070201092f010905130b031005090703110d0c050f03030405030a05070f0e040308060d0303090209150a09060806060409061404060b 75
    0x20045180c1c0400750088500403401640041e081100d641c080000840500c00d0a008940d800c00c038140c500b140f840003074817a003c05a1103240152006410047d600f81c2c8003541e849944c1c00914043c03120780c1e080f2745000e403d104031250880791f6503a403d50580c010640c0d920040d0110000e100909649008034a5060351070f00301d4204030000000c00c0006407104102c0340035159102603a41e007502d4450200b580301c5524141c00400700c4000d0f55107610100103c900940741c082c8160803c140510030700c0444004003900d11000d48001469007519103484503410707014022a40308102818003176090382d81c00c20a44d07025040090a446808039503107401503899840744a10b803800380d4100c9001270300703010b1901480d00c202e03059154031b1202e95542080013070702c0696003411014180d4902c0c1d1078000d070300c1d0a01e11510400d40901e42d40c0d40814082d013000708a030401e41c004c5040701e0070300034140501c09000c90007503040b29042c3c80100740c03c1c0c114640340c0081c0c81079642002d205008001004280603840e000303c601000d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 900252356 1250 900251106 900251159
    0x32a190905060a090b0d0b0d0c090c0509280803120f09070b0406050306180106050a1419080408190507170306060301030311010912050a2a0f0507080601 67
    0x5a903818050103002c3d0b4000d06020440c0c00c1010480c2c0070802c3c4c02070008880c903e000090f04011030b00029040c100f501c400740c941400c841e40c04d11040310b082c4110382040b02103050240c10800f9220010b808000c640000034850040301e0ba0554083c1070811040014000800999440c3c400031004030b580c040c170442e02182d2062004001c203101c2800440d4103030507a219002114901428140c00362019400640041e0700403d02400202c0800328955040d400b0f49500e95a4541d1150700c458000c040c0d6007800c845041030001041512909410402d04c20b05035001814151a1551a41040c48450203a4200c0031140301301481d0800580368448001d0921510a2519004818090240c1d60041c002294007541000c020401030010038007801c1504000c4041400210b2000019900c019101b524041407a0100e4008600700c0c1c2d11f1038000c06800c41d16540c0712410b408200050300c400c3c460740c1c0b0061010b047c7c00040560701c014418141300000140a144088943c03950f542c000c000203082114100c0240e564 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 900253606 1250 900252356 900252359
    0x1703070605100f032310061404111b030909130506100806240d0804090e030319230c1309020c06010618031b03020a0614032a1909 57
    0xc0d140b000c0800d0703800050140748028116030b124140d40900b5a90210681616120070b1a144010442489a1807641c0c401150b61480c00303006040341d09820701654440c07030800034002e0720354682c90181d411030020820009290041030840504510940c01d10b0382d0407104c10010000c40c566140c101c0e03c405403007503003103600e20340d03a4129000d00000b241c010320700d41d034001e100070601c441c9950106a0440c501d0900c01502c425541000840c46000303144100c0d2900008501001084028400c031103140741003001461944c500708014140d003010465516004659512003408588400c0c06000f800c000916650061401c269040e10fa048d00109942070b10650744150201c2c4000050003507406420080d0002d00300b47c0d0820409880e1090075a00b00c0040c0c5176440ea00002090b21420888903205036100101141e0b402d60050054030b85440d080f110a0001e0584010300d14101342003203d502140d115402c02030703141400c0d10060580448044a03140c07800105200407400600d0303051101c041c409450700650340703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 900254856 1250 900253606 900253621
    0x2a060d060f0812070b012c07080106030c03060308041e03080301141c020d260a0e1201180f08040302270f10030b180a0c08010c030b1e03071703070605 66
    0x130b100d003020007002102041e00401c1150390303644515040c0c41003900400030400140303181c0100c140c005c807018800074000d0b4004103d01a01842030080c041c40926003032203840d08640b0b800082c4d101d203104e1420144c00b40750490f080c0b2079286d0110030142d580032029559950790ba1844001124420b400d05104841e9104502e801c0b140b44000760003c60b030b001d48403941040d865212034140760f40d00d01e0010000b410342c2c00419160b03141c40c001001550b0079601c070343c00d10800003020300c04035503041c240d40317200c581c900303a200c0101c1c030083c10a95003450b5110300b00341340200c1545022203c0d4000d030f601c000d405c01c3d61441c3c582a01880314510a000b00340000030b0039801d50b00c0c0503200801401c255840c007007003c403901d410701c00f2407460840c06c0e40c000c6500c0c0b0751903000b900709e010291800b86400000d030303180303c641030040c03019440038050040f14500364030741800612800760000d10310b482c8041d10100c00b0780d440e101030f91440c0c90601c4064000d0461030820007500000071080d0346caa91003440d013180c00c5854040040c2d500c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 900256106 1250 900254856 900254893
    0x111210030c06120e070f17070b1b01090203161409060a12080c070f0303020f03040b161103100203090c060c0c09071e09172a060d060f08 60
    0x200c9400c80007803010103203030020030303600003140d260150402504d4081106548104000180080c6908a491941036203010312403000c2d881030860b040d5840e00f0880c420450008032500f903038120b40c0d0b8002000c0130300b80c19540b240c0c01010003c0c4001e4160140307042c42908100d503188080c0403654424811807403e081601000310210781201c199078001d2500714140301c062603030403529945074451104a4544801200c07064902401944000801d201010342401015810701021007042c40c883e00030360609091000c0c0b210203008a24101c0119000c40d840030741030000021000a06a2024003a00c50741d051a6030b880000e58400c8074564070a100c4c4081034605130900c80e0032518504080c401501c140007000041040e9028054103250810032907a0340405600c00d0380301d4550102010341c480b145003500c0c0800945082000c01d06860240e0001098804582d2000d68150b45c510090300b6010020054500065043d01903c003822546901e000c1c008183c08000400020a544080c0e040701d0030001c181034190790 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 900257356 1250 900256106 900256109
    0x1207020109030c1b0305060a0c030c1d15210114030a02030606060304060e07080303040201090e131212150905010f05010507120504031703041103030a0203040e06060d111210 76
    0x3003410207a200411345040d001030920403c402424051a40d0380c8a2602e00f070000c1e128001075941d0f82240344000c582604c54000d11091a092074903041000700722070520a0b14001a1a01584903000c40300314800c8000100d903c01c041580b0050555101d003020038403405424010120002220151680e0070700d800119284c0d0103600400070710712681c030502031100a4002800866290780c480401882c2e031003050203a40041c00d4000300558891a2500005005210603440203c92043c00d0003405004048401100c40c120f0300401c451030200c43c81c6d202103880b0040c8081c6100b500c1d280100d02c200c0c0c0d1000389001001c03122141001e1101d640c03a07000e682d0009061380329107070100c2e0080001d14000b40340000c810a030003030242401801c05a070307900c8008040184518150844000000300420840e0007000e001503080c059000310300b04000c41c080690380788960300070032001c06d51800002c0c8845e500c050031144076400c1c41c241402400020400300d80c45400c146040304240d41070500240c0e001c0001e088030320 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 900258606 1250 900257356 900257363
    0x130213051b25020303070c060210050618062707210b030a0f0f020402030703060801050702070b03191e090309080a050c04090201050912061b1305040b0604030b0c1207020109 76
    0x180d80701c0c80030745051a40c0b451480c101d81500050014502182d02c5001900040038650007410001c28030410510031104020881441815400343ca600c89400280605a014409554007000c980c052108842c5204103080c1011094004004218280358000c003800d506501249441a4000150108800703407264048504d815a0040c00000b0119010800c1e0b04011405440c82c520b03e482c541e004641a603004031800300200b500d440013040441002d00c5501d0740101c0f0741c409005000d08000e964503c4d0302c005071085e030341c1c12042003444410750702130350241a510390094072000c3e800e5505104100540300c401819030101d404140c0000d2241000328a140710b5681c44000b801f21042003800300300081000300000c0c1d04102050007071495030f44178840345012800a080050440c0c0c50300902c6028080b455218981d062a41400b07283c401341480c0114001f50b07041110082440d4482101083d2036000303c1c5d1000c0c0401d005501848910f23481c0c0b200418842541c80e86940c0d40e642e4800702a8242c801c0000b006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 900259856 1250 900258606 900258637
    0x51f110403050a300201090c0e0603100f15030f0201030b1002030d091a0709090c0e060d020703020307050a1208060f1806030106050a0b040509100f0608130213051b 72
    0x210006800c1c2501c8681601a8050b030b4101100c0a2400c1c10100700c000c09104c00b50f07642c1d511810030f109107000c0040c002c20540e0b101300ca00d0307e421000310b900e40c03800d00002081c0a4882d090320040ca00c03d60070107510611a010140c000d16602d042582c0809070991007071740400d01d4145142064100904e4405000c00305400640c80c00c59419078480062503c10f02c2542c207281041d188071100c0702401540c5022f1185940c82211990a00301e12808940041d403404080c00b0b00aa402c1025440700d80544003642d45044005894505178201a0b0030340c07207030300781c0200940507080941e02045955844555940c0541e942d0f000c5035a201001e0241000c07000410981c06100e40c081e801903030001d01c0a199001030b01400224025550741c001c200320a482e40c00024020b280410107000e1360a0505000fa48110054800f2034400c1c40c010303c141d0000d005006400801c9406800181034280e02141c00411300e0340034002400d184503000d5054002c000550f00f641340d03803070b8071900c40f85207240b6441519811211020315 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 900261106 1250 900259856 900259873
    0x1109030607080405150702060a05010e01150507170f1803060408270a090c12050c0a0c0305070c030f02030f12031501020708070306060e0a060b04090216051f11040305 73
    0x240c2d42e111008000f10f035184208010707001604400310105008148540061005051003030034513082e0349050700302d03030201001c0700c004004c04c0190700d1080d020400c0d1404e20750307034840084c2813031600c010841e020032455400029078030361001c421100904c81a40403041c04080080d00404142d160442a1070150181000340100100d40030345440d42c0350f520041100d0006440c45580229005940343d6021116071556040d41c0724010383c00024503001320710801c07010050703131405008400369406241c4600040000b1400d100341050302a1080b51074803a0090629004640e491504032943c50b103030745003240a4000c4410039505a10b00007030400200480c09540741c1107a13118940d4441d035039240203c081c118414102c0004c0c4144050101502540c00399101250b0141089200400540050301074040d19103004420412441e440c0d0688059611800015980d0034214603600c0b8000c0c030285001d821401000c507401d034400c0e0354802c0d051148070004000d022000c408103440c5002e020b40d00c4054501d8222205 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 900262356 1250 900261106 900261121
    0x30f04170a030824040c050a0e090606072a140a080318060903100905060906131a06040f1a0a0b070c090c0512040c06020709230402120f0109020411090306 68
    0x5520101c08101c5003500d500e501300000390503614030740c0c1e168000c40d90029100780615400a04058464000d44103000542404004164507108a8001811900300403401d900360405c2c8009203100c030702a01049440d401e458081c0120700405900f591485414101d10000b44c07441c0c003006035911381824060303601103040000309000540d803000d090654180500303040381700961028803071441800e020794010101441c111660501e003d601809010356090304c540d03030b140014411212540000c0000416405039102c2c0030109001d403203031511f5408001e0402d041d0701c1403120a0f803080500000100c801c1e80c1c1030307176840111149a203c3d45c0000741c2204500003091045100c0c0d504400c00410302894610301d40340040c07042005418040c0c808035505801c18504000003a41041004090184104104402040007031481050703190017541c01030400d08000001e0079951242d443d410003494560584111800c6084c0e10750007050b91030022407046142c07240390001c02003024103035203480034040c0040181ea12403d6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 900263606 1250 900262356 900262381
    0x1f0b131d13140106090614030c0904141509010c02070603020315090c1315030e0d09031101110304141336061802120604021f11030f04170a0308 63
    0x107055940120401140d0103018007441144028465450700040003070410359009003d20303110700268403a40c0000c001504980d503a000e642d800c075034042d41640036804c28034500f81c10401101000100089030904204c00c001c07041d004003001c0e00b0716600303841f0f41c10f45509050341240006e542e01c5084c6030350031070a4405030138441c0e010b58002042c00105400e10301258001e050515407500000c02484208094200c5e8035094040d603221403102c1c0740a05804000c180340200650000d10000e40074120741c01001003541d0250041070441300748442a640d550b616603409441c5114a80709590040b9988440c81d1660700c9070303110300110f00c610201880850b1145d400301d00c5d00c0100c071117280c1034003403811001c04000440c10b1240341428203034402118203c01050040005140200b040600244c010b00100001039072003120791454030b1507040c41450200d001d40011503080030758409550321444000b80365840b0140b500043c20481e85018000480e0205026055854004031030004000c95155000305e010074000303a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 900264856 1250 900263606 900263641
    0xe01110c0a08031201120b040609030c05120c0d020a02150c160810050609040b010b030c0904090501051f060e040203070c0803070c0b0907030206030c031f0b131d 71
    0x1004a45034205110002601c0001c41d60103592030f80d200242d00c4c010851509503e600620b403031480820000019110209010401031000f04816510980c500c1094040d0038080501c40d0000c0480e209440350740008503542c1c0c0006808061403094a042100e41c601c00a24492200e82c044d28540d2291007126a44107075030002842100707203025600d40406446d0721411620014800c550050200f005501030000407104040c001c3c50013a10140208030200d01301d944540d0446a01c1c50030390743d80b50390713448405943e8003c92a8081c0d1041c2015203820500005410050240c000545000300d1451500080c490122191086c0382c0480d0541400034810f01d031a5002e0750f849003e608100340711b014195160034056004940d0380700461202c1c2208014400041d01441d40a24a44000e1000904680010307085000003030012400d84800400a043d1803c00182c40e0101d4000e1401e00224603143c03450450560004500200300d400843d20015415840d8003205d01c8401101c90401002c3c1c481044086100e03841 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 900266106 1250 900264856 900264887
    0x5031204021219030813050a020d06110c01060503010f2a020705151c0c0e1509090709031103060402010e0609190902090a050303130e1e0403030902010f0306060e01 72
    0x3000007030410035043c0040c01c001807400342200b92450182c9030181c2480c801030310b03070345003400040a000d00080001400ca45926012581c54204810914110010b070014080403440748401050300600c0a205400c02816a1803c400070320a07000403030000401c48090501c85c0c960701090a09144c1c010000ca2450740540e84940705541c400c3e0744960204884011210750843e40540006903011601d8000c8095a031101e42d0400920100c9550034008050780031030607804d84108508110400c441118100b00d0b509003801420700009450801e002800f07050292000f51074505003203001a0b10b610300810480d00c120303416161003043c48410024080c881c0c000710340d11500300a00b4000500150340309150300d070040c0125040503a681520400f4809104800c0d4801c5009a1041c0f140d040d05a841810700015156004c1d03243c00310b81d5400b14500f80c05400095952418a044001d0000b8180c0c50b0700150420750007a01c0c0c44a501020800490490300a8821540090a81c05040010b90301c80c030700509102c4007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 900267356 1250 900266106 900266119
    0x60e041b08041e051504031d01081b0706180b070302041214100f0534030509120307050a03050f06011e11061e0c3c07031206120503120402 61
    0x49584c0c415151951000c4581110b100d0601007004040d03018440a10401c2164694042921084006400014050020002c069454603403460803480c48066506103900250180312442030006403400c0c9094500703003526041d44140006060601030700803101110481c03a8001c03080d245640301c07034050503a88d0300c046a0902500320f18024280c50780c0102440624255400290317800c0101c030104084120004c240d182014080281888405401613401c0c061f1003400c0105065035980d142c0c03030500030b5031100d0344d41d4040007109001c0f00660000c050310681a4a8504000980368407184c25426031081320341c9800140d00041c500c2c00c22010701e280060146881c10450300b40c103c0c107140c503420048200c4180c00076004c3c0b010300a1001e801000929004061052018984040f42c0340d00c4000804400b508940c41403018000480000503000c4001d50000c46031a0a07210481454020400d550b101010601a41410350104a004500c00365011aa51110003103180c83c134120340740526803c001784280d034402e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 900268606 1250 900267356 900267413
    0x3060209130509151e0a111e0d061a03130201030b060a030b100f02121315021c03111e0403060603080c15190e07080304060e041b0804 59
    0x162a4011070f0f00030004200034100c0b1802000b1540c140365401005081941450700e03108800c40c9640c00d0312600000040d6020401c1103811034200381c0c9102c1c150340c020f501d881440005071848456409056102d0802d07a0600010741d561950024a0600400d0042428410004600c001c80e03079190240841d40b045c1404070b6000705010004009400c041e0407000400d0b1560012080d5140c6860b01004d600d0302420500440c0301e00f410000d64400c01c240c01e81c3c01c10b0000041c80c24406c42d804484c0e400078000060301c0400c0118080c0002d44a0038804041d040c0060300035102c1c6465406400303180030284209000d542081562120464844080803000d40c01410411012012440170700a030b40185015240a990b9040740d034041c070b46450180503c200015081109002443d207803040185443c018100f00400c9444504030300d14200700c0c0950168256100c0040c1c005480ea820a003900500da80880e0100808103941035010f620b0310a0782a008005002c0f40e00107130009580c0d5408444080c5c01c2080d220416 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 900269856 1250 900268606 900268639
    0x20106050618010258110c0a0e150409080403050102070201090f060f050711040606090f0819060e0a0c0b09121518120d0f050705040f03060209 63
    0x7980080c80c2c5006981440d04441c4065030100040801140c1e1841806400c0342e101c402500882c4551610900070400041c244084202d505810a5055078148984070324000011020304115502000b95090340640418010381d0300e009006c2d00d0890b003000529a400303a0703034000000325950b8000960f950003940c511000d0f010034078200c080c0c4050b5204100041c0da5141d076000150401301154800c800e402d802c0f08061001992002c8100120030f0f090405607103801079440c280b14010140350001e030b08540f5084d00007808030b500600d04030440b01e0070050b60f06403d84480141703480364020700d80e10b00b802c0d03541c2d6031820005800340c0c000160314011400761015450705940d10342c81001580d01c418407020010a90b4642894408403541e00c0102c41c100800c1503030150100e80e2040e00b001001004084182d0340c80c004528018415801607034880c1024995501701511100000d0501980303146c04607181c000000e40c1e980c01002120181d412000a0201c0e03a8910741c0c034030380079507c80e04e0f21a40010201d001c404d01c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 900271106 1250 900269856 900269869
    0x504051003230106080d05090906061b010f110a0e150421060b010906020a0605040c08030a0c0501060522020705010204150c0b0c0a090308160209091501060804080d050702010605 78
    0x3501e2032a02c050040b5142102d56900791540d0b174100700c5041d00240b002204064021040311500300781601c80c00f8175507072040c000642c0ba0007020b0f082c07000b400091a1200c0c50305019480500c0140c0520810003900501a10300b020b103004c2c4000311070105106022a207114540b18524103d505141d00ca11440d150700d5114203102809860101340041d820001078004100103400340701e842d5402840c0861280c0c2c41c06030700950342e100d1210090801941c850104050200c12029080039180c080100d0340d640703201080c0107240e2407140d00185c4465280282c0030580340b038500540603981114040344042c000c0c403105101c00a40c0316141c211030940d800c000009280944016900710340010b83c5910340c41124038140150614002019070031000c00400101c8035503600405204182c0e0b421082d9240c4640c0050640c003800c482d80640030b0350108043c2e0800851400004284582d409800030301c9000e640c0c0d4900a80c0c1010302138800410a00080c4090750b0701032455401641c2c040705520011400641d9180807408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 900272356 1250 900271106 900271133
    0x61a4b12121201141009060f020a060203011d06040b031e03040807170d0f090603020d061d011707060219110d14072c1b0d020304060c03020c06010504051003 69
    0x1182d00340600401050850714104120954266a81a5000030080001340746034440d01071181880b00f2849481d03e040e100304051490141e107c0011540ca50b1202403c00040c1001c0450500c0858590000380280c10706000b510310005000c0e0041c1011602030419084180e00c155601d030301c911081c40000303036003281009410002c0820030101101e002c130318003480d030621001e05400d40074002d00540014805a00c4400501100c11034a001071706d130981c0d00c05440103070069602610002c10454525040c401000201c0e504079244100050750031100402055141c0d51248a10310241e00300d500989030341005c620121100920510326900704c60b030305d2030000d40070301c07461001900c2080b140d1010001c1a0740400185c0b016007114204c41c038031500340e2044404030030300071407252010004c001c1c007240500390300904e040c07034a5090b24042620381c0000c10070305000b504101d030143c4107181028010b440f014068070803130b02d0140003003000d480c890f800c100a220141c01d0107007044060507146103000010602c031444105 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 900273606 1250 900272356 900272377
    0x6010303030f0b042a020f0318012703080f0409020c0d02060919021003110708070605011a072d0b040209010605040b0304061a4b1212 59
    0x9942c0404401d4804603001c164440e40903504d805005003a0001e4007410354802c8218200b0030103024038800c8120300f04491030046c400184400b1503c03104481600350420b001c101d080ea280d40c0001c2c1c031514002040300241d801902c4d02003c400090010410f9400100b01d044050180b403454169168094012030740001c0409925400402d40c0200300c69041c406c803900040e4240041c11008095005145003407801c44c00284a03d454090b1822120700a40048041d6a10000038503100c4415040102c280e60050200b150b100785408004a1130440014041082c0358490803002d003071031507558602c10140701204011030030301e40c181d074000310022988600c0c1c48018401c221800060415105010b0300402c1a0090414032005003c1170103d00240010707290b00503046071002c6602c58101c81c41c0003070290b02c1c83c80303190401c4203d4108030341c2100841030241e00903100075408028000015030b00c600a101546a66400c80700c0300344a44407443e04401c006105d0b40340a0984500081c40c40d10f503041c43d88826040c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 900274856 1250 900273606 900273611
    0xc091018150303050a090b1312150903050d0501080d0c060e0a0c0f170309010e01050d0b0a0f080c0d0201050a211503020a0e0c0322051b040608010e15180601030303 72
    0x7611a030380c414202c1e001824950296820230b90004e003d0228005c96000c0d07001d04041c0c0c007004106005940c00820b41c41c1304244000c0004018a044c01080c0c5c0d8041c0b51410100f0b8108000010b80001c00500361202030b029076a44140540666260700107820040031031280d5125003400c00c070101d410b80c0d564000510710038052100c03071894400111640354101301003141c507400500c00d40d80982d810200b01c010000c02441e010384d03209072856181e40203029101005070840c1c0200c1c804a0f040002e84e004c80259840c42c07040f03c081c514a42d080100880b00508000d000910034419900d40300d000d440e0b0b4540c2031000710709180314651443d0154089031400819a084800300d55810810b50905120300740181c1025540c86c4007070301d07000101750464032000d000d034800400049507d048004802c0315030448164070001790780901328500420400d40200726280d511540c6030490025889405128400340300d02d005010f032841e1b02030082003151006004182c07601070001300300e0700c0c42c5d40d10f020b000a501071032103074400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 900276106 1250 900274856 900274867
    0x60a0519031e020f12060a0308031302040b0f10121113030b061008040f03030e01140115113703120501170307020909010e03070b06030c09101815030305 67
    0xa4004000c420b502c08184074410001032003245118422906001d0101c46140d1007502d503240819184486a400980000700100500184609280d8103580e010b000701c0b001d20840c41c002041284a42d0198603040c6c4c043e003084c5221003010300400002c44458010840040e44440a42d14404035503c050031500d030401e00124280104161201e20a4001c902540c50108041100d2405056000094805440f001c0106c00490400d482508a039122005503402031048020020800c003850600703001d5580d01a4107088031950b002e201c0e040038108140c00c403006007452100101e6aa16180500c03110451003805241e00743c4d03d40040d140d801005510a0707071003100903500e100000048401c182c102409400c85d000c8142c14445000040d0b80000ba01101c07000001e480d5003000500414501804612a0202203030010034858035140461044500f5020b403503105000700c04108030034104842c6800503084040051200c0c060185414071030b8100f081c0d00080c40102c404a07007085c5c442e10741c41200040c000140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 900277356 1250 900276106 900276131
    0x2b0b34082203090e0f1b0903011b0e030f01020f09010806040b060307080a05090d050d0f06051507020102070803071e0f050303010e01060e0f0f040915060608090d020a0b06060a051903 80
    0x2101a80000ba001c996011410000c440000303101000f5186c1401c80030210b010031840d542036021a940101001200528130b030080c0001e882c620713610b0510ba00c20f014400d200368101d83c041c021651036481314090140b5000c050f400540d8044070240c1500d4109695a00c2c81d81c490312501e0086004004917202e16440d0301e041d1030420b081d03a6005100000da80c102d8001540001d8104083d0b0b40e00d0f0501300350125041c03541000300801410164401a8094180c1d014116209825001025168001c1e42910003d54948680503900d208824004040d81e200d08090103642140c8106005401d00c0f80d060514a0310342034403602c1ca103400a07001580c111120500412940b50465480510b1803410b4413206000411040055203104140e01c5842c0103e454001440030440c0054502c0d10b20940310504000d140d898540041080c2401c850030b0306244560321114840600018940c0c580b140d0090791000c50707540f18000d001c00c0e0303001403800c601440014022038858201042c440301034808580d90008901c90381c1c45 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 900278606 1250 900277356 900277379
    0x3010b09030d020d020303130812160306050405060f060705100c08060f0f1e04061802220e070302070f080d0903080a060803092b0b3408220309 63
    0x101c2c109541c40030070f000101c6034000c02580d9028041c3c07a0320510381710703d50a00d941c06100f10650030540310007103000c101c0750b1101141c91003202040360341d0030841e0b6526442480100d88041c0c41246d40040064010003491610300d00901e22184601c080d05d00e01c0101805844c2a00c1d201802d90f00801e80303041c100602400d200c440c501d001e0074101d5135000030707100c104049400101055200c10640d800710100d100e998507036421000c02080100954040d400d000307078540b8000d4105680070000ba02c2280d8402d91100c0da08c004d00006c0d51000a881c0e515621502c00c00d80c0203501c03000c003ca80038404005508041014174003d040c03400c040b0240031811188603d00141901c0b001462411214988401070003205400810b0300d901400607240001c605c40100c1c0950322103c00c0011038005140402200d008015013003040b20b0041e00f200c60f02032910344e54681c0070300c4c0c04007030111001c183c103450000201029111300d80003600840d1072400030815107125407803034421013800321003500802c80030002081541040d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 900279856 1250 900278606 900278623
    0x180111101a0a0303120b0a0f0303050c0d0c020114070f021c03030b011e1803140d0e0a030f030f0c1b1a03010f0e100807060f11060106020d050c1203010b0903 69
    0x11100d50024900f1540c02030304646000010b1048903079a540000b55076221011840090541700c10540c003210360b00e01d0010001d601407440c00035180100380540083c2d074052005600780d90341c142c585800100c0c4c1e112983e0940e030468681503402c2810707102d541000d81c99443d5030419103190f1560303590f0506414100074042e80c8403401c40034100240101540c10101d01125070402050300e501c1c100071a424524900e00d91120740c0d802c00b40c1400700356043e6400c80c12000036850382000441c2c0343d40700c10145003000c002c4180c52610000d800c1d02c002c01035040010f80728903e80706501100d410070315841c502985a001c10300041c1c091100360501c00c91070038001024000200f5004404056442e40340d9810060440d107500c1d214459606429072000100710017041500142002c2e00030034049500c02561740300300600c4005400c0101000c203c0c2c2c02c036000081700c008038446041c2d802d10340050001505c6007500711980e5100c04281361290184800c8040d50030144001180240720316140c0399112a0094100341c2401102c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 900281106 1250 900279856 900279859
    0x7080d05150a180b1005090909030306060703050d0207051f0f020310031101052106120109050c01050d0b1e01090e0906070f0c1a1b0906180111101a 65
    0x12201140d906541d5942d410007074030380b0803002070484500c10340c800c0007070305921204550101c280e0006050195100e4084c00c00400215415191901c0301e280c2103840317220540b070898000904110800c08030340a4801451104486003005203030403020307111a41450300100006416148030062503071300505a0003540c00c4401210411891402c102102490307a88851100812100350396109542917801507060314088503004066100e07031500f400000f5070700d40303007122890b101d007a007041c0d00c40840c0310520860050303a50207001819034560b1f040064517590807002d40b0310541510341c1100b020f540c4070380561180104054a804014280f250000340005805400c11a520b024101c00c021900e240003449a4111000b0304040c61004400f1008669103200700074090210918881a8840e611190044038847e0861200080c40c8506e45203443d00c072803050150581e4058400c0c00950521241110200da907000c05042203110400300c4601142400400b1940000f030a541d04403154201042d00c42c0050040300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 900282356 1250 900281106 900281131
    0xb100608010801060b09270c090102060c07150515040603081902032d0405041a011e0e090603070806010825030f06090203010b09090d170103050c09090c0607080d05 72
    0x500f840b22040340203044200b881806000c248068071907247c0c1d101d5906900710909440d80e4645501c4468042c1c2c00301c803469005108100004100802140c1903441496100b0b20407071006040a1603100075100c0984002032908c0351808400c441d989610503500114800d5001d180c8418108a010300d1034100b0030041019900300f00810720740d00500c800a011107032007240c8403150000c080c4107450240d000e0b9810030303900b2510300051401c4640660341080003640c400d903510a0b03c100f4202001a01c4048001781501240b110403544c042850000f41d803951040380a011107800c1552650824600f82c42a0f01141d46904a0440400784514210a0201100413076001c2c4010f01d28590b42c110b0f0301000f00001034a075941e04d420301011503400b0340094080c0300e03004100410900381620a0764841d082803550b00080348540340444079000840203254103e0342c0100142ca4041e5148091004072400101044041d00464140d006180c0d00c0c08050b0150901556401e0b85401c807151081d0219075000c1d0803400707580c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 900283606 1250 900282356 900282359
    0x11a0a060f1808030f03010302040c031b05160f0f0203190c06050906071b0501091211040b011b0803100e13060b030c0303040b07020a0f0b030c070f0b10060801080106 73
    0x2500901244a4100c41d840c0c08200c5005020ba60b9220000c9a0000340440c000012554000781036440550706a90003180c0400081c110100c00f602200c0f1041100700c0d40c1c2c1e07504810240540d0040d4003621840301c103450174003075074070065840d214400304104040750104110b040010540c00c08000402003e480400e18107140c0140751030f80c0c01c0112047c0b18910800000059520711900c910003a20b00c007603481810045905208600812082850f00901e030024154a800084550300301403040d1886400c40804961401c5170000d000280451030030640c1808114109100400c0c070701d001e002401401050503640302d0900345984801e104656125001c0c1c4105a0244500918840080d500181d0300c4040090f105003200046070526200e804515410300000c200040c5a40c4610010140207100702e50520810b03803500d010001c604824014101e41d4a01400003c0c030f100d49120013031008034002da070690401d0f4500d5540b03a211403803c5401e8140028034400410500c0d401602c001c2c013501803040207003c00c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 900284856 1250 900283606 900283619
    0x15040e07020d09150c0b04050105090c0d0b010e070504050a060e0405060103140f0702070b040f030606060804241103070c0c08060c09011812050f15011d060301110c011a0a 75
    0x51140d008a04d000001c4003e211146800785901c00c04040e480380c01c41d40c01e403500381401d90007040100c0d62800940110382c0f201006152408207039401e43d51000f92000d159003082c0d40d102e12940001c1c880390a12104210201d01aa12600920010308003030b0703240c070303e90b0700c400c828801681e1028140c04d040c035003004041c640a2040100060384a000c400f0f50000b6581c681002702d1901c0e6095000c02484000082c01180300440c5007040000c1e240070312800e004265451004036484c103811100901915110880d1041c044d9500e5213a2140b52281c0e0408911404192201c502552058404401003000c1091420400c030221140303100402104001c0d054514110580200d03920440101074100408510821111480402400c014100b010707030b605c05c3c0003510f1038402e5403a0807001031030300c0500c5501c0500c0d170602103041000381078070102c400c66044a040020450b40e500c4d8080c050907490754032205c0da5011445d036600a080030480c4200003003a09044c403641c4000b0203541080090044040070028440d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 900286106 1250 900284856 900284867
    0x8031b1206060a18140a0b0a1403070201060503151915050d0c030f03110f06010b0f0c01020702032a0405060603060603040c030b090102040e0a0b0a150e15040e07020d 73
    0x7110094030001d90300c20100408546011010301c00d02d800c0c698403903000c507181511124032010303c0029220031042d583c440f00800c0340c60240310707481800504000d00000404003804003460b0080c03683d000225000d5140c00000c4e0034000c0710249180070404020401000c44483e0720040c3c1307800c101c0d080802192009880820395041c00b0701507580501d00140a1104000c0760600440046810410b50918400c640c51300900310300703445007808403034400c14550130400a404200e0070704035060407403258540780c40d042c441281030300014041c2e81955800c0c40083c01584042c41114106107071140303d040e90b86c210f510110042400d11104502451501007080b0258a4134411641c0200c1b0444d8030b60f40380d5032686090b115006007904010811041d00c018800003800c150041e10998110800301d100556801c041d0008640400460650041e100b840802c2035046102c00d14001401c0d03840d002c12815007100c0440c189141911200c200c103000014104103ca8100304d00503009117080c4003412120000c410002c0c207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 900287356 1250 900286106 900286111
    0x90a170d080714070605010602281209030515010f15020c091305070308090f011d120313260712061107061d070e01051e0301020c0a08031b12 62
    0x280440040821041c078042d01d0f00f0300b884004049200d0760391890f49440006170400f8403130075015110b081149140c1090000100e10118007d00d4001070f1110a62246158084914609810b05c01c8050020010400500c10000040a08142c81c81c0f1545840104401c00c60603920a00c0580c0702d520441c00d0803580070503815280d0b20116103441c1540c980760620880d42d0320b043c4008126100b20030002040015500181032013031000c503000f0380c480c00c44a00548030150401c0000c114404d44241c0c003245440d01141001032140c2c2481281c0c00c060304030009152000c000d400040001d50041c071600c070051782000d003545c0348170005400740610500d01114a18910711070000148020f03121181655490714040564004940104007840480328030b4076400d0705050304682c6110745000321034012840c41031400001e8120b035809001d40d85c181848204c0c0c500d02e06c85030505158555020094042e14500400903900c04134014190240d1720304240c640040c064490381300140b02400203111503a6060f4006684c643d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 900288606 1250 900287356 900287383
    0x3151e051516021503070206070305160806042a09030606080f03033d080105070809100e0a05070603060e0a090809060c0a0b0103080a2c040b01050f0f090a17 69
    0x41c482c034600c0042c0c0800001115054038110100030170a070380c0c2d0300044007400f83c0400c0e1820030044e240c2c44040c1c0d40c03070f51018044401080c0940c01150a9040c641e001c0805000c0c0180303203002c0c080ba440010410050105901d000160030f0764018414840c103031040b1002042007400408400c10b0301111070340c49010040050345290600200102c003413925400d5010f003050f03008100404e00380b030074800e01c50008042c0035240c01c0b0f62814002401150042d81c2e003d009805803c01000110650300c410000740c018030800003405d000b0402801d002a00c100903400c042c1034252004035000781801c3d00e0b14a040030050840004d0313070170155110b011510a00c21a0203500c820741c0c6040d0b03104003d5050b14984090080001d190130320f00800042445011405064030300060368420465161034049441d100c000d0700d034915841c0101c90b0052403a460079a01c1212024018106030782441c001200d0b4250300e0b049650009000000003030001c5480c54074000c00806007010360200d00d103020f490150241c1e01c10201100e003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 900289856 1250 900288606 900288637
    0x180f07060f02070b0c010207151401050f06070b042a030308131a0a091101021222050904050c031c080a0c0201180c031106040305060406090303151e0515 67
    0x241c05074420b10002002e400d503903142a13a40e0040c070b020345000b54841d03481643da560600784400c410312002d00901c0746211110542c103c09900304410441003400c02c010180d80480108a800700084107202050311990058801c002c07500308100000280c1a03514501c0707120030300741c01414000640c01c04622600700020261254160489140403001ea90540a2004412040204100b03807241140c0003600311170704c20380910144546410059a44d0b08a900e05401c030000180440f41294401000b004441c000d0010902c20041d41d550100d140e461090b601615103401c0140541110304040041c10148407031000151840b00503d040100080e5028110041c1161684800081103101b500040a504400340c0210480740b001c2c030302880180c50b54401180c003190a958030300030b07500d014415101141d41100c0070342426555075a85078002c1050200072010f0656400c008401c0c0142404c02001815144080c00404450202020401e00103030b0b10491103000318440350105402100151280000c0c0e8250301d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 900291106 1250 900289856 900289877
    0x2306040204051f1209080703020d020c0a1413020403031215030b0a020714030d060617070915020a0c0b090f030c0604120804090203070314011505030118020d0f05180f0706 75
    0x71603a000040c1209030045003445018024006000010314844d0b08c650211654980d05e8031080e41c5426442d20075603840310200c01d0401058545400c0e05001c2140140380002d0746140354462030498019410076800100f0303505039100034105038410303000461249140b05124610b56a07888402c00c20080440c0301c0d00b9004a80b40c02040310b042c40312103100b080001600e8507a2030360701d030b440000c140c00e104410000f03444450002004404408440c0103901982d64840c010f400d0031002079041d0380170703010341045104030741d0408046810b40d840d80b030141c003a143e0b0055545d0440c00802005105e040c1c51213200342c00c482c1c074042481e134603182154100d070302d0745468080d0703180e090400702c105014543c81460f65034000001c001580d80e05600c01a80141b1a841c41d02031a6212848007000354020340d4580c02280c030410060094441c080101c1203100c800020152600101702c2d082825601045280d400c030fa034030b540500810f003805200d88120013807482d00408400c02079a00c03041e5103141c10b01c103550500030718401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 900292356 1250 900291106 900291169
    0x150b04150c080304110f090103110103140f060d14030c03070b060418150b03030711090f040c0b030c0405041e110f120a0902190810020a02060f0603010609230604020405 74
    0xb46e008000c00002c002c0c0c00b19603502d040400c062104510080d0010f860207510903100110400114040c916600741003895075146401c1c4414030f2072401c01507035003004151400c51292002c10041000c0c1340c08c030026644480c140e1506820342400508240c0c4a14244480700d580301d40e10746500c91029401c00c03454405525034103007070801400b501c8890303500b60000080e00d0091024810000040c1501916000807550b074a242c14034141c001958020503820158008000078440b0780c0c0556041405081300a01c0e150b501c0d4001400c4440c0215154115100e070701212008a0080c440c02c03485000741c2c0d42c0e0500c2c00c050920b01d080c443c8524038144000001e00c101103210804203501100c2710580c050307c1405201c1180081010300b072118030542900307202e000102080c0308218000c0e141e190000c0d8000340003039100d40440d80d090500c01000702d0703099941c0d040002400303840c1f4007030001d02402c4040c15880141042d50700000707a1500a29190061b401080200901e4481c0800b042e501c800c0c822035460b50300e500340c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 900293606 1250 900292356 900292369
    0x31b0a0f03230105040201080406020a030b0604030f0b060111071701090b04050f0601060513050f0d0803070332190e0304060e030f0a020a0b0d150b04150c08030411 72
    0x1002a2040900048007000b0441902981081845812801884110540145402c0c0c400849000340003607640c401060001e85541c003d802600c20300d04010615407a14404500c1d80c1d0000d6000303a5030003848070486800e100ca030501081d040308080c41c0540148030f40c240704940e5201c5c00e1003601241c1d0004640c94106090070f510100805038031600d0110035080c10b007881a03941c0500001440349016100000455078040c904488070b441107840c8040300d40b46000b080044540150003125009440740c10582d0028441d100211700c12001074a00040e00e852504003030148408261064400f5601c2505001501652480d0a40e001c4a0011010614407441100740050300369000d1000c0584004100802c5aa030814849034031200f040d0104d905a00c46e021a09030703120124400a500034008000030700040c03851100a2030480c8200c840862401044010ba400d00520380d031000700d400c2000b24050080d9100b1381d443c5001030840745801200c0190640303a4940da2f20014100a0143d100300700c5030050b948410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 900294856 1250 900293606 900293609
    0x100203090d120219020d060506040209090f07020d021914120c07031505160f0201020f16021203030f011e03151d1b1309020d080405011d031b0a 63
    0x80c2900100c4005442d08840b0003080301161005030164070030b80c2c01d00300328620724880c0300b540042c003101c03038243c81d600d84000a200240100d50442c0d020000a2120344072440c255000c0c01c0e41e8003040449261074940203080515000e00502150401030407411042000d004008070203402c81c5242e9103c9140c2d41c82145000c10064090f000c00c1d1740441c0c400050300020070014100c0e030080348032074628425080e48100b158400c44e41d03648924003c591440309544110b0740b01340710b0440c0707000052038058801c039143c8280d0490310503a0b8014103038040203011410200900b1104a400030020360039814080c0d0400700003481402035034110810034218220711402c02d031448005540100700343e10315500c292400d070b0147ca181408190000000c100c064403040740000c00c0c107401142250b02e0145120754008014102d0010380450742d1290701d54414001580d9125070400c81d46e840342002ca40c4d03403440d2070009480410f0545441c0d04090041c0c01d181e0b10380c0c030041011642c0b012490504905014103c8c00103074803011030b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 900296106 1250 900294856 900294859
    0x61b080f071b050601030605060d08180f04090609060b0909030a1d09010605030a05070203190305060f060c030a120501230109180218040b2209120f0f08090c10020309 73
    0x29410440140038001c244e59060302c4c01084107211a60b40d05040c094502d440c1d1706c0041030b462041240c04e6079059021008003a0000c01400c00145240c0e81c000a4151011040252500da5072100c032141000214400c0c407100b900306646030200b92808640f2142c03a8000c82e1912030074815181a2003000c40455180e020845500a01143c1503584840b00208190004c8400c011458605008a100e19000109641407280490315280e00c40c42c0c01c9404601030800904003a030410350100e4044400d1752018080c0c608004040b000f55118090080000d0081c01200000f200181c5000010301110002094031451500c080e10380d1350104130014012142801564000c6c00700c20501030240310046016001420061105070007500c040d18014204400c541d142c9001c594000c4410380c14001c5820340c0701c4610f09018080000158190340e54a0341200d9000c800c8445000030f408a1070402560b401a403801c0320b092261409844910f400783c00c80741d41c0d80704204164420030b00310902c01c40c20f41c400c00480b00c10220 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 900297356 1250 900296106 900296147
    0x5030f0c0d0c0503070f0903150f061208070c1707051c05010c0305151f260403080a0e0f12180319060c111f0204030b1003061b080f07 59
    0x1000003810b9030004c0e581c410001b8a5805010301c294403c040040580e41c000d890b411851002201c0c400050100004a4180a44410f0001061100b16940740703140360003070030201e6a8039800c2c541000307000a80e410038922170b8a0035620006146000590b141a10403d8400307118407009120100040d0b440e10800414560030881c0340325000c0e40c1500214003601c0072206138507000c11003208102c01244d003102c11140c0c040500c880002198030807032507840c007170400c4166a03c5848a003050009542012103064010038446401e000521000303102d0030002c00e401c10040c0002c070b00c01e08161503c1d650220440d420101c00071920072180c03a0b21003031100300680024204d80c1e02c013060020054a1440c0300e04240d500ca4a4940844841030044030501d4428807508041d1400401d180740d03c41c80002030fa004030082503402d000100001e0b1201494074001d06d0f03031046040c90903207545424000da9901002c01000840640100d060003a004402c6c0c41d081240c9806a10311a0b0303840004858a40311101010007084 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 900298606 1250 900297356 900297371
    0x702070b0f460203030a11070b070e09060f01020d030f02090d142503080a1701270c093014010c020d0905040e0c040608010c030b04060605030f0c0d 65
    0x400754490403a50391460110304420b060441c91184040d1103200320240980c004100040e5405495800030801140d652045401c200158940c2080090110745c0c40b408192418050010ba1a000400c030351b2011040f110141c240362072800003902c2d86000121030f0705041d1900e8025034554202e40543e60038400260110584d90168203381c0c0403841d204e910300c400e0340a4100013211601c0707084181c248500c40f042e007026140745103558641459006091184c20040700c2210f50141b880307603481050080004084403400303d44c3c505096011440d02c003005180992910100703840094000e2100b0086078110804009504881103400e944104c0b0884581d50b00048054124100710303506000d807401c0c0940300c0003000019980303c0245d80da0102c2c00104000300b514100204803a06d482d4000c01c1440d00d48005883d010160300d4082000c0d60000e0b040100240d4481500c1c0300066410300c1206ca255100312014003181e0324103d80900144009002da8a0100d80200001c0c50100b9500c22600c25060f000c00401006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 900299856 1250 900298606 900298657
    0x90801020c0709110408031902030c030703080106020f06071b0201031515120c020601091d0115092d0e071a0723060a0506040b03070f0f08060702070b0f 67
    0xe401c1801000e0040b460725101d01360508403039085c0e80c01d4480b440015442c040804800d071107081486a0a40c2c118481004240c038000b03c180090803402c0e1094640c01c01e40c4d41030030000303810401b42411800340f41e80644c0c1009400381c1e2054000714908003982c010024a101c5000481c0907000c54180400e042d4682800000c0c12800881501c9019405541d421482400d00c080041610040446880140d0001d0014003a0080940c00000550700c080310f41040e03504074210341400d43c0d0250f440c07100710100c2c20100b007100d000c081c0228503218580354110754082010700b100c00d0310100720404000743c05541e15008910030720301300800310150801c409003002400e10300b04035011640c8225011034445000d03041c080000d80014280a500040000c007612081d583d0324a0b0300d00604000345078551003901c0380d0107071015880501c68113001e8400110809005424030952003071039801580a0a443d0740004104014694042a11825610b480a86940e1021210241b40c420700441c40e68140b1078a82c00c0031450b00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 900301106 1250 900299856 900299863
    0x201110c041a0306090f06070e06071406040b0a2f040e0907030c0e1e0a110f090906010c030c06050901020d0203011511160e0405070e0708090f03040b19090801020c 72
    0x600c0c5044007210140d80d19802000d446d100c0c0b0071701c00c5020f40e0121010488060280c08000e14416010304541d06042c9d198448250307400210b01e601c0c166401103021f200038040740710b1060340d00c803a032100144106a030303142401c4d0050100307490030030b0226841c01a2100c40460b0408941c0144130101908443d07040032078841e81c40710716602c801c0301c981a01c031900240c100c0d2500d041e41c1c841c071520140304410300b12092018030407410061003203082d55603078280794021281c40390190011a100f0307800c69440c1d4a6440c01c1c4200550080d040301e06000c440c04803c0c0000707a00c0b025041015500450203d201d0b01c60942503806809180200080035001000209000c1c00f019049158600d0994a92042c40c40002c020340c0c58001250069007d582c0543d4140912201d101784690454814411074840d1a1b0fa050811003440c010b44444001554030000e0028104040001444e40003007500590326007031400d40d00c401c031840b440041c200700020500003003a42c0350280000c0b80051010000941d520540c4d005455207 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 900302356 1250 900301106 900301151
    0xd0b010f1403060f13020a050603010923061507060906140a0f05010f170c0a090902090702030901020d0c140d020d090b0708090f060706020c0102040e0f040f0201110c04 74
    0x116448009081400b0700c0d00284440c0038600d4801c09066588031111101d41101d115002039802042c0c19000042c80d8032060010350007171500200c00941103880c80c4c2c42050a508401004074401407030420300c0f00c03564840e0b028840889009208503502c854510f07008018184120300585080c0c501202c0102d0741c0c030100d207030511600348803078208071105a807013041044480a006110509a100c02c05012030b43c00ca5140350304169190f8203c07503540715050005001c3c60705581000400a448141420331070401187d07080d0480410300145042a40c0c0800003075981c4c5460015000300000c0c1d46520701071040606640d030b121840c183c160384c0024003040d0080e40d26045000d84c0300000740075010000c2e10052410039540c4180c2d1044006203060504801c1003508094801c02c0c4d40e110358104920000101544001d100507004500056103551915181c6505860300902c10403c1c40550300c108030006103803040c005a095424208451086205440301d458014403a55241e045860704070021004040079001e0003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 900303606 1250 900302356 900302369
    0x31c050c070302060c030a091407080708030c0c01050304060b101710060c080307020106080615090c0a05071709060a0201020c1c0801141302120901060e0606040909020d0b010f 77
    0x406510388849810349485000c10140058210a0101d00140031103002541c00c03048403200422000d109440351054000780c274007030364801c1e0304c085000c0284640c28407446008001860146040180c0040020f44503511f500c2040e04000b400000a820062183d1002c440445c01610b41134002041c01c00140c4201c200d003041745181c1402c000011075480c4800c0c01441600e542d40d9852605051a540d4800944c1029080c00e055540310341d0302140c1e1000411180d446040c51051041241507501e0602c0800d4801404420034900100007040d4415000400c0b02d101c164042e1629000348000c1c035001100e805040c4003075900070400070b01540c3d0103905402078112040e098080d10321b010340203c2d450032440e40300d090910114000b02c004001d00f9102041d404a8410017410301041070300005104c9080fa401b040007003110100c4030041c803055150901c070701d002800c281c2d8410381041c103008000403014050341c03251480742070311901d043c8119150501a140e40c664042d078600f0582d6114104404480e03610301411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 900304856 1250 900303606 900303611
    0x50d050901061409150d231b0607050c0910090f0b18071716020606030a1707030c080301090506030d0f2a0f0b01090e0304030203030f1b031c 62
    0xc00300036040c440c0d00e08a421800203101c00e0395070a4284213888000800182c5501d0001640108640700d41102184580c0b20380404d00c0481707140420080a002c0a000300c08490380213542c0821022298108040e8190085850a444800f1890182e15000d80718503c2504450f5010a0040310440803950500351a0001018419900010038140c1180d12a110303855020002c0c450400c1411901c1d50840d0700000c407442c0125982180d5840c00c440f16205613103450000b04044695070040d5414444d01e60022011800341440328078a40302e40c02c1304103040c05145100311000402c00c04050013108801403807070380044429100e41c0d486409100904c001c69255009006034007004060901c51000744420b1406034541001000d422074032a681c140c1f642c0588140040025002400700d014048000510f9110b200301341c1c041d60404580d00165000f0894070303425640700323100c00d00051307502205030b1341e002041110007a1244c1241003003426848422001410038000040c01d00b035408001c54590403480d150407070a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 900306106 1250 900304856 900304861
    0x110303070f120f14010518040206040b0304020d0b0103050c01080a1806020a02070e010801060602060721050c070f0b060f0307031505101502060411011e14090301060f080c150a0305060301090c06050d05 88
    0x158260041c0c2110020b50000ac1003005104682d03545000e16013150000c1c0071404191004da56446031900c0c20303001501c80c4d0703005040b444600d603030014081e23900c5085403206110810503040780203410446100024515030300450807280b610700c20062a8000e04130318040c0004d5594501c6100e000300118016400140500d42c000342e65640030304dc410136080c16040031a81e0201d500010762008103405415403015560410004011070340c54906407810394000d98070203d55040c4031041003010f2034241038044c041c2c1c01c01e03401080400e17240c1c2d01c0d40c0387c140181407010482c1da4070510103c42100c3c07182c001d10075540900800d01403040c0c1c00a240c611691082041d030350480f0703078100195040c421101d04103580401c0740581404140c4900d2000012401111049080a60703140000f03007500c0a0380c21440550207440d40030030240e1030402c0403500038941a19000c0c101c61034201c1d11200303849107400010925850b03002080164a095002c05e4403607421988000c5404c4c4c464200801c15840b20600b40ca60a00303000c003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 900307356 1250 900306106 900306139
    0xb030703030e130e0307033506040605010f0c081e16060f05100b070c0b0c0f070504140f07050c07090b0f040b01020303150f060f0307110303070f120f140105 69
    0x4d1841c405107000002c4d41000c1460360201d41c1d01721612180d40314460307080c0c90003110381031001f00c01c21440c4140028920601d40041440120380046d40a03504002c0070004078000d0903000b0304403100d160341140c24103596280411405000b0f110004101d40d8540b0000744040d00f103400320000c090a140724100c01e0011068200d81e000a0328000d4540014030310385a60108034602000004040d00ca1003070b4410f10026640c0d504000481c2c01400500c5d440740c00c00401020711002c00d10004001c1c0404480030000740aa0418007a00808004c06210b03900c0d075500c000c502c20b5030182083d156081c00481c201c0b81982e4942407944050400a4203990041c01a80071510540c5440d002c3d0417640c18041e401141150b5071000894502c40000c00400e800ca0000c3c402c003540c584580c1c0041a60b03075858241d031070f503904005100810058094286040d44d400900c18025110ba002e085010200700e5803926054090b05001e03c94000d001c004100e4070a2445d0a9420801c0a0462421412120f0031071310403205661040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 900308606 1250 900307356 900307361
    0x3020c1903111b09010902030702210c0114011206021c090303021b0f0a0332070c05011b121418010e01020a0809041a030321130302060a050a0b030703030e13 69
    0x44991350218070748005016090040c2c1c05189e11480c24030440c0c554100240c504e0325001c22140420750b03440f40c001518003c1c481c0074006c80e42c0c00d00c030607070f22652158505a41e070302d00840c030020001c1c10503800180b20800050152800082242400000c20032031010b440c014009520900e01c8040345403004c0000001d0031404a409030340e030940c640141101149554085807501c1c001c0403500c881208503100d40100f81d00307040040030b07202e050010b0a030f620410b032700f842031014ad1f0903402603040200d40c1e025401101e44014400c80c515a00011041c060704c0384030000d80b0900c5100700c4407152020042050402055a9115a604040e080e00c1d41d400c5000740100481c0c44082c1d1000141a10074100a400711030305055200c45010038800f094284102158400030342507502c00703410b10b001c1082c01c03002088441c059040c01da820000b05510411031050030f0358040d4a0b505d000f002806040d607554000303022003425400000d4a080010155140c850f26403501070145c09c0700e024118000c2c000d40c803400320209004e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 900309856 1250 900308606 900308653
    0x9140108030307030e07121a0105060c030a0804030509040e011505040b10111501150905010e0901050d0255030f0302030f0d241503020c190311 63
    0x800c055495a5283d4005401900828001803814841c07220005504000d444483c030101780328000104446200b2a0141e01240044e00101d1050f00104034848281400004440c0b0650880c2032001d01955103050984180c0507218140e5006420060408002501076100c2e1048482e4081554000c2c0c1d194000d02080310b045420403508099a14140070943d03000700307035044110054008881d0300d4181107075000c1000300e0a038042a60200c0481c0040c400d160003001c0c03c0c0c06000c0030320f00b031740c4203c01000010b141c00c3c50600c04d20b80903140641d0322000f9034551100d101725141e0400e4030159801e101031032081c015903503081810840780c84903032030384000340001c42c04038149055271041c860300c0d07800e503290580603a1380f0700c108800707600c410070400e44001d10341c07030181075407040000700055540d4503128400e50b50190b900d010000e5500d50102030141821814042d0b034840d11a260068840564455141c0b8240008901d483c00310700b00e5046400b01680103290000c1e5901d404240c0f0400844000b0080109000d0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 900311106 1250 900309856 900309869
    0x5040c0815100b161b050111030307020604140c030706020d12020705060604020a05070b04030c12050c250504090b04030e030a0b0c130e0f06010807020c130902010903020306070801091401 82
    0x356040140b11100c4001e061310540011419240603240d540300c0c140c4491401600050194404d0300b00203641c0c215415a03490704010003d5403940c81c1841340252036100081c0014035460202003e0f54a4010400c170507042131f03002504403400e90b61038210195413040b501051030005409060309009040c418025552020b602c400240740030703240c5600300000b94011744d4402003044000d00c014004501144c01543c0194000c3d150718148600c0c50410b2207807103100349400710600c2010400600c80420014402039540105c21800d03000c03048a420700f880040d200c2e80070a070702a05100480c42403001d03000a4034001d52180c0c840090b542501c800341611812005405010008190005040701018000030089610100001140e05861300351240075100700303540c0c140c200c042007000c100386560040041500624207000501803402000000303220003042c480211590381e1100407420440e409810390501855004082d81c0e590f10f42180c1c01009004c0911070300c02d03420708101200307581044081080e41600c0340e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 900312356 1250 900311106 900311131
    0xf01050a1d061504030602040501140a170c0405030304180e07060903030305060f0901090902090f280914101a091f08030d020901200304030b100905040c0815 69
    0x1546514680850030051015401044050003d0640b00c12580100f01440c800c80d03005848a041c4400100944445106e11181030010001d008009070403401051140812044040d40c985d5030708a10354950185500103601131001003804101844200f200f4204003001110030000c2c01151a09185d68407000d10440000c28a800001d20119110fa040203501030009849601001c40c40d03c0800c444410036403108140c00ea845892004501d04000741e1130300308500d070103250381c80d0500a410344910b07100d4140c8000001d170844100c400d5403030107400c48009a50059108000031860313141f2035844100060304082c005d0702e0503903058a014540c90b61801d5801000c0c002000581c0c5002414202d00e14040741c89403129403110700050142c404000400d03800401c01c40160f1152043c1001412007070a06900300200004194101e10441002041d44e003103030742100361340c11951504102c4164140036a044241103e05180c10001032180100200c402c0750441001c845090001c400107a0b0100b4088d1181031440c207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 900313606 1250 900312356 900312389
    0x2a180106110304050310020d05060f060a0c0f05010203090a0c081c030b0d05070602100f050f070c1419170a08160e090f15030318010309111002060f01050a 68
    0x41c852880c00d2640d03030482089038a4582c4a90020340703840c01a6002c0703a001c0c0d40003d40058220600c2c0039040d081481a64208003098000c0000341c01c03030040a02480c108064440c4d01ea051081c0d00c2080000150000b008540d01c1c20000c0c50b0984070340d44802c1c00c2e40c2103481c6043c00900e1150001d4200c00401501403250030070442c0d50700890280c011045403e510110000c02c081c00709409000117001840e02d41c0060144070b420ba200b6a00b610026500700341240e2601e0100708090f5900c00b2300543c099600c4c9045200340d000351400501800006840190908c20b140c002d030700440e10320110f01c020a000762074000448080301a81d40b411b21902c040440040c1500c03010030390000038500b210882c41c1c0304d8105082c4080602020400920045511800c04242c400c00c3c400c01d2080050440c40340c050a402841c078002405102d59080260300404c2c1d41095507880e1004140301c1507404921a10000829190451070000d500a5441030700303803081110b07080a180001494a06001c060003259151201c161426 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 900314856 1250 900313606 900313619
    0xc0904081801050409021209071502060109050414100b031605031b030f0d030f0f0c1b020f0d03020a02040b270a0621150902180a09052a1801 62
    0xe07100c003105050210522000c81c01652500140510b42c000800f20565403500442280c5014070342e038030040091a0000007060110350105055042d07404400c13010030300d91100d1601d125461502c215030f428600801600e460802c129401151038268200c1c1115920440500d4800112050344515a40355000414a01103001d20211030206800c009003038455803900e100555090408088001001075078070550703550b42c078080c0e12941c0101120301c0c400b01310035095000d0241842d402d103ca40c004035401e605484c000c656401c0705032078882d44090198941d0031083c0c5806540c035944181c1c101c2c4214140656031115040444041d03050300e0a000d107420400c41040140c0b040d205014080701d429917110603022802d1085180b4442c1c2e10380828189884080c202d05150300c5210700a03000000050a00d80c2c444c015a5594034001054000075021120640300c01c81e04034024590000020202d028071000e1351014007c507100c22407001c1d62070201c200c0a042c0d140402681d4000e40510904d40240c1c2001840913 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 900316106 1250 900314856 900314887
    0x2010609270302100e0c03120a20010209030304030c0303030513030818070911040303200c1225050f0105030c0f031e241c02010305060415030b04050c090408 69
    0x1c0c180a40151050041440007001c19192860303151405944008610300c01c1d41410440b14070850314540b42c141c205200c0c060020107a40c900f4064019910340700c1c0d5030252403c829030440d904d070400101200e54855407450b1078507000007503200c15400b191500700080c0f050600e20030800fa04a5142d50354015a130b450b403007484c030124041c0c500a401d0b807150105c045070403000380c892101208041e00f130043e125445c6241c0145042c14580d0818954031241074040601e900000c1c419490f03d1003100c111002650b495800b03440d09a5656500b01c41c000c0040c912118a080b00c00100d0a964040e10713207181c0c00c80c048005540900c019a042c10b1000b504001505050000d50081c54000c17030001d21607a80454626201500c0c28030540c0c3c1c02d01c00c0c503801030207031007034012901050452140913600c0c004a04040c460200c0d0f5810f00040c0a414561903400140c0141d496a001209003034841c0c504a160b40e480b800d00f01c040703080c121022156417180120701841071030025025441558015212031600c01c400049004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 900317356 1250 900316106 900316181
    0xf0405070e0a030804260a1104020c030a1112390d03020a0f0c020f0904050715030605030601050f0a03061812030911090c0a0806030a02150a02010609 66
    0x2081010500e50505640301002d07900210700616800d80c5842c100b5440e2104401e0f454602281d21503940181d04080e4030104132400b80300e03082880401c03404482404540644a055540011030000289010419800000800383c1018003411030b4882c0c42ca4001c404000c2c407030400f08001041c1900651051071034007030325407030304008007004c0e01050025440c400361801e080b40c003040003ca0740200e5440d100c654040481034140c0b00b58a0503a00c18412074010800b802c1d0703004151401000d1110001d0103004d0301300180c800074205141d1060100402000c018020000c5000726446802560000101c903e45800d45100381c00000340407409007442c5130340c2c1100402e400741d802180d000403c8214404603003916008103061010380c43c08a40f070002071804044110301050b003584070f20728400c18001c4501480042d2481c6144c0c2e8103120140380c0b59036000900d4198081c000075880507130341164011032840c8001134600340025130020b200300350301c515221040d180000d025921003d03090800481c00d040d500c0c100720 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 900318606 1250 900317356 900317371
    0x90301060b0a09140306010e040609020a0f1d150603010b0c0f07030c0819170a0e130c0801091808070609330b0a1502190b0a050105010e0f0405 63
    0x21034550341c0e804a08141c00c000614800304103910400c012031441c00c3c1414920050403000742a407036041c02c16034201e8000203000501503d651b450005c0071525018940000b5000400811454981c6c0e07800884070070105500364441d803241d107008601c1c1102104070311100700500030410b90039a03003041e03c41d5100307401070b200340c104a20039000000e4072141c0900c40e083c040d50245410110440c18840306514081c00c4400380c80d1a119521034038004140040c10300c00910414404461340e4003140c1c02c046408269081c4207540c070880030b682c100203019136a031001411082c1a00e82c01c2140c0e81c1e03680d01c0821582c444d91640d04010149001c2d1001035080d00003003059a22507500010f0760004ca80f05c505a5810740740c15000984090a400d0340018114020243c004003084e8051222200200100c1d245074454031990784401c04140503000c15a000380140c112050018000501030203060404001c608410703900601c01a162500104007948564402a000240030f03000e030800b01c0f600800d01000b000001d1036503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 900319856 1250 900318606 900318611
    0xb040509120c25170c130e010608030301080a0b060d03080a1e02030403020a03020106151e0e031c080c0c0d0807022409100603020a03060b031e01150b040812090301 72
    0x10a04040c00f11800c0c0c04920b9070349080c4012038105000f001c054003507001025a80d9100040710b6480350b8500e407210b07601080804000c6501040700da855405880c060b003002100e0700012001003048080080da41e00326601030340014096131284024002c041100400103000500010000745c054400780d006824206801d4000222400000100b0001c9030415507044006030001e410840a0590900030b071800340c10400c0d55600080815040034050310074980d4070588c07110201941e040f0f460702440c50207442c80c0c0060103a03407404038108840c9030b02100e1180400c0118100c200460300740f00702101921700d40d1942c1c1e00140b090301100745080d5440600240090704610804041865003418120031000c2505000c400a9050034803e8465081030b41140318400e80c20f00d80141040540da80c0e89540c401c40360031a0b0000741200b0008007003402c213072505d412498907071340741101c4000ba15015882044001403a02601030196110303a42d20096102702e00c18642d441c0c2c48034070650f01002801c001000783c054000c000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 900321106 1250 900319856 900319873
    0x60c031306060323010c02030a0c0f17030109050a140c2b020403170310060804050307020613081b101d0d080a180e01030f021903150b040509120c 64
    0x111002d45809410444240c4020000000c055007010b400344854244c6400138031440d030403140c0095480c010b0030060410405803124a1042c06100b080141a854000310601500001d1091413070709035000703109841a940c81c14001844914080c4101c03042d8040980107101c7c1501d0303a80710300300503401030302e140c0803170443c4112044407a080c88840101c00c0310080c0310244e00d403451400d10481c1d9005501b2034803210582002000140c000b0406200241c0d101420801c6a5854604205246001d07821000390022070000b141c0c844014040780d0201115481c1040f1a5201600740030342c11390700000720410b070300120036800000450740a25811101c12550b81040c04000c4004000190790502c80300013641c1010002030700c2d0562551004171440f03032500c0c40803800c001c039141c064100040303041440060308800e2400582e0b0110340d5081040c0100581451100384c00c241c690a2481c0255440c1100311f4141d482d29010580600f41030142620401c0c0b0b010281c1880c951020040c02c05902415840b202c50048030314 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 900322356 1250 900321106 900321113
    0xf060305061c030f030e120403061d0105040318080c01080a05070e06220f06051e09040207350f28020d080c2b06050a060315090e060c0313 61
    0x6481210701907580d01e961855132600143c12035400441200c0e2942002695101c941d0980b8101d03800c0701d0348984006401c0c00e0305a8074030343c108000516141507500344014042407542c04201e103c04480c1c0f9010304220b050307a410440d41d40310f503181544c9011032480d1000604201e21580915800601410041a5401d644000488560000324011020302102034820003403242c0c40118409445a2031000c0081404c111029050b4002c21000d10000c03614440c0c90048140c2d00e44c25600707507620240040d9114040361601c071040341b0000c83d1003c402e02d81561030240c00034000010710031200c0080307030b03451504a11404000165001c14000c00480600d200103d0000e40214001140a90194003500000c4e1300e26030000d2404a0240c5804000c040a20000f692b4411300c0c0d20b10080c8990802016110204001420f0042c2c40c155011503440710610b14009011901a0040020010705146403203515417155504011920061030307170341d42a44100000340c14220203038000e50308250000414190840b6940c4c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 900323606 1250 900322356 900322399
    0x709061b1110030510060c17070203010902060318010f150302041a060f0406090b0310120311011d10090b010b0d090c15020d090311060702130507080415060f06030506 73
    0x104040000780c0c4c0d58003000401e407a5000e4041c041d0040d4076019500d44480e4030f034000200502d8950b80300d0720030f0001d0800215507095000c00801580503101584a03c0c155140122035140f25161b24210f50901c0c844440c244800d21402d110640307044101c1542c9030468007030000400461711600111041303182034185560398400900801e400380004070307a0301c50901000420400e043d42c880e803036009060040c8014801070f1001c0d8826141c450241180510700b50404881036595074600761100d510f4449000c4513003140424100f10000c800b02200c1c04050b40710208411544414000b41041c2d0034240140100602e85008010310300c84180003190150b2240c81e0710300b070440300780c1c000705060180012407600950144101c0352402440d00302001c2c80b600d1034650b80840c803070408001d407045200107451821541d50340728044805641501c10000e40c030742600c02800c1c070031040d202540d1303049212030b045042d803569028000584d84107407080000b00345400401d402404010388510f0b0312100b041420241d41030f004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 900324856 1250 900323606 900323629
    0xc03051e0a0f0f0218130603020f040c02190c05180103081e04091103010e01050904110103020a021024150504061d0d050a0c080313030b07020118050a02090709061b11 73
    0x8100112907100d10010001039000014001b506103042003010005603441301c4d045018280280d801003500401040100d0500c8140c080c40885210240b080d00141303c003403420350b010389100b03840b40d6030900901c0407903204262092100601e01042004604180002c0c40c00801d01d02071a10092400c0c075072101c0a0b4001d80741114031114203036201000400c200d401d000e91040c010300064400c006c16013000d440c0c1c00c041e00a0ac0175442e0501d41c0002e03903108030074400c20100b01415003021040261043c03042414818656484c900d104402e031480c0042403180c0d221450a509502d0342e01c0e030350f1505107482001ea844d41005100c04081c0c1041c4070310500d00e5208c808034400e10601c01c0014204d481014a802c0c3d488032542d8101d0001d0b0b40c018070070b44070140d910340d04400699421030b4100d441c030b83c2c8003070f0300302d01401868201c0c100200e0303140d2448003048000a024407416100b1a2641c105075180c01c4202c4031074003103100b0100045e8480c800c02c0c0458070751031010310945010340740c20540c0310b56207000b250b01800c6c01c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 900326106 1250 900324856 900324877
    0x402130f0603140f070c060506060d06030503040905010b0f031503070e0408091e010212070f1e1712070f120615021203040506180a05100c03051e0a0f0f02 68
    0x1200b00308243d10f80c9060395140c3c03003281c40480d13107224101440300401000d00208010025a510750203d00c40d942e40300c00b90360b44058003440074480c00da120302c3d2044d1240c00c00c0c0300e41c032011402d02c1c0011071722966020640c0c480709440e8403141e085941d009086000f941403002c041d0707090b0166110115200c07400004062040d400b5070107a541d00c19000c0140040d004210768070340c00300c0080900b1010140c5c1c0c04a400b01100305071140042d101e48060400c004150b9210400030022401d54400865402e020382046c01c1f82c43c01a280e072810740091241c00782d0280720300716034089e2695090001032034160094018001001d00340c9004001c0302002640d401c03c448441c0c0200c0071031b00c451030b03400190650405c83d074000d8103401079440382181011b5841d155581c40c060066004010308072019951038a04000300c200c91074005080761224a420f000c2000103080e081d041c0f0f00024240b000280074404070303480c5440c044070a5445281d499030744008150090203404080480152950b07401e08190311030740080d00f908c506 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 900327356 1250 900326106 900326111
    0x818090c071202070b18040608031201050102120f030c07050f1e0c0411040e070203190f080c120109230c04061710090c050c1501051c110402130f0603 66
    0x200b820000c1c01c042c0100802c200310f50003000700b840705c0205201980c009482203441e06004611800005000d4031742a00644814803000c03031105c01d540500c03034a080c12551f00382c080c0c410148184517080a80e226540020001110810110302c48034648002043c1250107402580c003818030b41100242440d07041005040307030480c446a6108400010301c824580610308a904014611111004079186c1c0124800c194200c0320030070010f8143c0b4020310403141c804001340c21400e107032034070640c028002040301010603002400920010720000f0211080361040800c4400502c11a8640590785000c2e02c14140fa80314061444d006c226004211404074502501e40d60581c0ca071282d0a200c4001c002600c0c20750111440c0800d5024030101c040906c00802c01d0701c1e41564003003012211168281d405c2e114402c11304240e40700b41007040302081c902c80000781c16a02c00719820740220303131030074054510215001c00c06442d03900f6150104040c0c0c41c1a50041203030032050104606519030b1852080d411030410340c842004681c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 900328606 1250 900327356 900327367
    0xe18060102010e0c330c010204060e0d080d0903140708030a0e010612080702030703081204140120090f0414040b07080115030515090a0903020f07030b040818090c 71
    0x40e0280150f45440f042d9500030300c0c940c60780d000001e41003102c001c0e01c00180e0201081da82203001003064020807024121090a541d00c40c0020020300039489441071000041e1980d203456410f04c1c00e207046542ca642c000b9071140c2810600e0040a0080c04070590460900002c3da00e149141461003014002c95409045080d49a1401814078419219a49009900d80e4980b02060002d10b5515111405098122640588030022440840c0c0741c0220703500083c003000c40100c0c0c0d084800141c10301a41c480d030f01c140d10326150310407240030581c2a910f0081d2000212400595041c0e11a00303000b028100c16400201044840d42c002c40124080312040300d404000d84812808100c107100f5000c0e07449421100c1c901d40f0585961500c8011510314000036600020151203a000c5400702401180510364100c009190400a04140b1401c600810403004102c0140c045c403e0404484072001c925802201d801004000d16582c49030398114469200ca20b10342c00c0100c04644116054540365003251003480300c9440d140c3c1c0d61 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 900329856 1250 900328606 900328609
    0xa090f15090e091c12090b042306060111030d0f0b0909030f0403030503073f0501080303060111031318180f0b0604180b0f1f060c030e1806 61
    0x81e0240d04030030880307181c04041c00886000081c0700c40f61002e032101c0d058035104204404a9410b11104044007000381805000418025081100b82c02203100d00641c802d01c4807010030f03141c3c000b11500f01ea81c80355081140003d0f9194080c960f480c000c031403c002500d141090904a00c0c045541d581d095041041e034403251503465041c03107060309170001d207008000c5013002c100c1d12110030b00c0e106500000b02005808008200c00700d010f94492030540711080074030b505150408082401c00c202d0384801d5028180c0c0f141c18050007500503c562410b880c1d50300040c52075a5100d50042d182c941451406030441d10041003003035a0700c0b0306d00920300003038240c0c240e0040d0f5081c030302000c0c0002d8800c41042100b9a480408544000800901c0c0c00070140380d001c0c0c103205003552136000060051011242141c0f509411202d208100150300e003141d1700c0340c1c0c00144007044945442a2825482800c50b40213003450100020034800d85001c1c15216034910f120b0310b0700002c16040729011941465100d40e410320680514424407016 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 900331106 1250 900329856 900329867
    0x1050703050601090e04020f060d0203090f0c1c0b130507152d08040606080706080402030d0c0c09021305280b09010909020f0f0705060106110a0c09020a090f15 70
    0x2c042440c100f000141803880010b01a44083d2000303110b102c5084e0f080076a070300c4903400c1d0352800300b20b80d008545928000456645030b8101011400490103181c81400407481c04540400b0281d81c1c4403000552140a030746c0c0c0100d4540050320300c80047c3d400b440d00200007130041000802418441d4240501201c0c1980050103101225001c0400d00e082008502c0d880040f42041194070007191030701c1043c544441c2403440007020a034012081c83d0041d0000410300c0d540042199001300c0c8250210b441d0302d4042c4800b1a01c0050009000f272010307010620800c400307641c0e50082c022111080e900503181c2d40d66000010340c40c40d48072441c9490715090003c00d416000403201182e00030511281300501e4641d1500001b0110001030260303000d44e42d0302080d070080301100700054890749001c02c40050b9544419060403540c82000b4421800010840048079607548004500040c40d00d600000c51540c003414201000d010303400565441e001c1202d0920f0006504886210920080110300324060010441000042c003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 900332356 1250 900331106 900331111
    0x2a0c030301080d18150c031715210a0209190504111018210203012a140d09050109150f06060518040c091d070f030e0a030305090f010e0105070305 64
    0xe24070b00303c4c40800c9181e9807000300d250700c0000340c40c1c03c903400341c040d18007900c0d401d0b01021901030030003d28040000040c4070a2041c40e4603207048a14014940e00e110001007010481c0745a5041d9410100c480c1005062003200250425251032054600a00d49412070084031001c450a0303518080030007942803039082c83d408032400c50029182a545050101403003940305c0540744120000760101c035a45800f416926031017000c400303034000e0091101d15803850150548441250b01d0b0f903c0d001080e03c24400f03144c0503020301d1080d0800d443c0320508006402481000a000c040ba0540d80d954030b0314100300000c2d0390070a81c074070401002500002c0740003094902500304c0f01181c00c030308140300c010010b9504031490706000c42e588000032180414501512030084465040341e50003806034080300900f6070505c0c420301100c00e00c101040c7c1d441d070031054107030082207040c0c03a4203803240a1103400084c140400300c0e200e504416400000300c0104d490010728403000c00d00f1a01c00d90050f10703460355104240300f002da07070601a554 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 900333606 1250 900332356 900332387
    0x5030417070803071b171c06150e0105070b060904020d021003050f0603010b060405121f060503240406051b16020f0306010614030a090c0b09030d082a0c030301080d 72
    0x1e0500c229a0394400c6e66040e040c011501d0701001150101091000f60144060140e4005c0c05000741952822914052400001c4280119101c1c0300784441e5544620240c1d0840746c0c02c086402c5007511544184042414050802d980007407200c000c403400b60f211180490b000307101960380000c047ca071080010310b120300c029140307501c42c0c1d04203852264103641d180d042d41d0075604211003540600011803085490081819409800d000500b0348a0303900c00724a03031150b0f0484000b40c0650b240341c18048000c150080c441c401114800080c4004030b0085074003540038a5024100c003000140342058a03401c0a51a00070781c20484031401e808030303504114240601e44809101094005204035410080f0103080d00525035055400c68102000241c403841143c0c00c1449044d0308000c54921032a210713010700107a5409141031900a00c215003480c0440c0340b10b10788040c414003145034500141503405080d03113aa614521040541d0410a011f1358001260500c000c5008100700340c0202601d0742a503502500b0100000540c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 900334856 1250 900333606 900333647
    0x801050105010c1709030109080301081203160f12020310050307080102040501082d101d090d050715050112050d020c03070501140d051515040f05010503041707080307 73
    0x400442e6000801407250943c40442d040c25406490310300c00c443c0c080c1540c1d1650540c2040000418852044000c0d0305131410301c800d07540000c2c0e85404010b2107200a0740c1000c2620311811070b803a64584070b405061310081d414a00100405000c401c004180d8000359441c40c01c001c1c1844081040349020402100249a030300000d60600d4600400a001c0310300080601c43c1004041960b103100140500c0301c600c850480c01e01d80c6403d400d043e90301c00300141e0340740500d000c00e0340008420304e4074a9000c1c100d20701c21030701d06c3c00421800184031f0003100d8607080014110f40c85d50125810b100c001515004250281a41c0c042c03042c0348604a081261420b8800301c0f54a055400c0140020300603140407ca507815076000b820615440040c3e1118260703e03100e520780344d0078864502000d0201c0071f25280c5100441900456072000c180c428100c03058014803540c400d0344c080c003d440303004000c1365025002560b0b10500945104072070701c504089621065100020884200b030b0b000040006064012000490114204018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 900336106 1250 900334856 900334859
    0x31506050c150f06010530060405220201110f07080f0c01170406020703051207020105100510091e050a0e0604140f06040b0f120a110d0b070e1f081008010501 69
    0x283c0e070144020b003006041100c005202070300e2400c015020020304402504905d14100203244441c049034041c0c40b10740c840c9081c00c0101d9100d500741c50b00c185d0110440c410b46400703111a54015070b0290b000e1101c44070b00303010b2600c85094030b000c1800a04020070034203014080914810380e615040c10f174010b4540d4140302c10001d07071844810070300f20480e511603402030005030703914050b0905031380b00d00412003182107606003003082081c05a41074110a008811284140509507112010041141003c14286002500850f020007180d91b400c941031508101c00412031103582d48480106405480903004000b45101043c1401814203140c4103800b030900d502e00c5403018034144120916542e030000382c00030303100d503848441c80c0020b9601e09a0320807907488014a0f5034203e2132030130350090300c0ba51502402c0d5840f09001fa91b030b4086007030030900c0340700c120340c010803021113651201c8040e6030402d82d07000c00e190040d03090355070071110314883d012448441d601e60b21004030342d250003c4500503c07502c1d5005080c00e81d042000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 900337356 1250 900336106 900336121
    0x4050c0a0c031b0213020c100b061c060312020318010201051302040c020c120a06050a02090a030b040c150314070903021e061e030f070309050604020f01031506050c15 73
    0xd070048a607051405504009038040d042c00d401001c024042e520111400000302c91800a9001f85410440b01081c1e964228031442c0d00400c41d050050320700c0e0040c20800808101a840703150007821044003800000d0b01686076120a644115444224005a400002c4005005075003d060702d1001000340b00900c000c0c544503140c000c8901050600038041c035100d044203c480d50080c0b03c100d0349641c01400b985200c10f064002284d4a8200c6d180981b8607515000c0410701d440f600f4022101821000341070708221500c4c40c0d0342c0c3d180301e0328010810344030800b80300e0012692100540207005002441c2c0c0c0e001c40c070b104050001d2900b4140240421003030001c00303c001c10040c0ca5041c800c2d48865403040b0300d00681109440811b104c0e20890300800c800c0d02e4107003030f000c20301024140514019481401c04541507620014190220303480e14a000d0b106520a400160040ca401461108050f0040c580801c101c5000c04d4040c0d820a21600031002048000c03c03000d0352040100f20442d0b100040c400e4451035402d0014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 900338606 1250 900337356 900337367
    0x6130504020312210c3f0726062b1b05040f200c030d0506150a080603060901090312090615090603021507030f030507021006080c04050c0a 61
    0x2c0000c4542c60081040030200004030b61510b00060b00e0036041d480307461701e8411100c403079000b01d81d01120881c0e1182d80c0101440d0650301008060384414100c002c20304048000d1407858002026542040005c1300850080405002142c0c0b5260146400340d9803414007004008102c44448203100b420314002402880311051200c18205050704490603040e00140302ea420030000c0604d820007600203042c100950200103007a03100c081c0c00f151048403220302d06c0340c04800074100d20850383e500951382e0041c0700b00c02200205034020340d0030801c0180081100300714800310141e00d420241014010440a90800c1503908060209a9000d0b00410080205480c130340e401401001055a1100a0569a602113801c0000a80c80031424411030120f095540c1e61340c1c0c84040140005000880c01500d800d010001c0036070418050310b1600b0b615488013101c001c14820210010310005100404622529110740d65210b02c41c481c540217020300324040c0000c061100140720641d03038047c00380c09111108116000d02140d004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 900339856 1250 900338606 900338623
    0x6030307120e10170f040215030c04090914010c02030f160f060527070b0f28090503010b0603010812130312080a0b100516020d060212061305040203 65
    0x84241c030402244031001c075204048480711580001c01000d00003145904000b078000025481e581e090b61503941c204802c80440020754009400c50600c50301041150300000c041c1d5484030a280030b00b800c6c103503101840019103403008800e42d1032009070150310088403420b01451505034254002945020140c01c010b062074450112a84a2145600406020404079602d00c0c400940c0002051080f802c05140e0710004640e405001d40a0b02c4900b5449105c180000c9640c600310782141016a00703018109101d03040f81c0d030288071020340c203041e40605044031041d404074105c1180d1259131811201b42c184402d060859000a0300980703d100305000411058400003440200401084000342d03c807018220324001601460300020203000640006a8101d0f6015041c4e500c01c0a045070b05001d0341030b103c0d09015045081e000485d000640401140c5d024105032140c58902500c0a07000012500050303c528049811008803060209050024001c0c5440e02800c2038100e561001802c1125007425400242c2d01c41d40d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 900341106 1250 900339856 900339863
    0x2060a1a040e030408060a0c180501090315021b01061a03060604030f230d090b120601030e03071e03110f0a11040209120a0506010603110f0d02040b040906030c060806030307 76
    0xe9181802d220441802903030700401c03144c0200c81c56828080e5800c0060025014a50300140400c0d03c126000510382158500b299410713148e14409070300b1516080790305031100e0240d441d2035400300a2900c5034031842c10460ba81c400c10100024640382898503c14003000310910403241c05005005000d1199184012101180c1d40a20042550100d07850000d80d464010b5040e1082400c4145410301420000325030340d40b44140594a019103503481c0e0110681a020386100090540107040000300c01354040c1c1d02103003280040c40c3c1200e0801c009540c50450b04046281808440030b80d5030f0311340040640008102140013a80409000d1141c0d01c141d0007030361907802c0700e0007800300203810f0340071100c5031a15411602458030103419140181d2030341d51801c1d07485003040b4080340e1a100b403500000d00141319100c0c5015254002c01068540b0682c0284000309800040c102c01100358200400202542c05600820080c80f04041c0441c40074030314106100c20030200d501800034014590204022070703074084100c40c0a40c0c0d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 900342356 1250 900341106 900341111
    0xf0b040f0501110a02121e22091109040e10061d0c070308040b04030c06050901020705060c25080f1c0b180a02070c0305191e02060316050906130602060a1a04 69
    0x71607452107551020304840b0300c41f51810000d52200000c8154140c00c80c10803262a40030246179840381c000d41201d01000000c0c000e40400c2c80715444618040c0c01c00780d0031000100032600c81c8000580d0344002c0302c481e507000d000741c00081810b000744003000000d585c1e4803160300b000007400c011030740e2409444520010402041581900c0010f020540541040d41d41e584d040101000146840c10b4070318000d503c1404160380724821403000404110003141100d07c0c000c0e4944400743e4402440842c6008031002e0307241213a070b011052111152844001e4054042c0142120480391225041440541111038405910380150304031100c0c1c90985418425141e040f40d100780300141c0e20103242c1000c008041141d0001030083c025001c00010003600300340320842060041459000000140c0840640d91034001c07002034106a052000840d0103c02854400030709082d0300b0418588070f00200040c88543c4140b03010710010f52003078010f000c07081c0d0400c15690f02c00c9258008001104040303a0316001029060000c40c0300c6c68 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 900343606 1250 900342356 900342367
    0x60306150303080c0d11070803220c150c0204020a0206100902130e07030e01090b34050c190302030a090e10090b04020c15060f0d030e0402070f0b040f0501110a0212 72
    0x11042e800410366462a4050f00e495140520300151981c1c4142c0340481602204ac600408103d0f44419038071300a6405603818081500d01020396182905041c103184c14007a0100346c84002d070b19180018010502e465010301414500a00c1c04902c140a0340c018811480c4140150809000714203441801d440711050040070030380e141e84080300641800c2c3d2030b42d0071a5003007a0f580010041c8084580c0c0c010a852a451103d06000180030900c0780c2820301d102040540210580f1100b0780030b80000c04100031880240e0740320b1030100c5440c034007800600000310300580c070008038582c0441e48038600e18040c0405220103002c5042c5100b48881c40c00040c00b514038003e0fa216014800e9585680c1140c801c0700c2c1e54002d0701c0440302e8984170000341810031501c2030b01800c00107581d4580380c581184006116a41600c40c0a2126910030030710009401c4640304a510300b03450420140840d030100d69144c0b1903885a05203c54490036442d040e42500d604058001c0d032801c2c00d204501d0056000304001d44661215800d154942 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 900344856 1250 900343606 900343627
    0x20a06050c0c03281803080a05040506161a0105090423070e01051c0b1f050d080703271a1201320d1b030b0901060306150303080c 57
    0x14803504001500b1071000041918007100510710f20080a850101c0001c00c030b1040c8a0140c0e4580702c2c030310800361800c5864006000285019015100189252404900b443e8a034000b00f880c2d54458501d0100c4140c84050baa010032100d0b01d0606001d03082d12180c200107524090200d02b8264001c0c03c010080d030072440c0d0044001c0000c900c2c25200201c014101c8076460b654500341c020240007030003040e0090440b80031201100078401e524001c02c591081241005035103031040d01c00d2040b011040403410441c107001c00200c0395520684070642d54081c0004950399481441c000c0d0a036580341d4410801348850301d80011682a09107074100031108800e608410240040c0725240c01c500c40d412800c00c42890b14400414140105030354034064140d100480d000106150300044140c1060b207a001d94401500e40003900002c0b040c04045020007001800103c4090701d0b584c8403402d00354110340b40c1c081a03640307078020000d02c03540e4000c0c600001c401100c0e0f007880d0703411a280148040001800034410210015001d07450 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 900346106 1250 900344856 900344881
    0x1b1213030311030114182a0708030c271e01020102040905091c09081b0f1e030c040501050607030f09080a1a01060509130f1401120303060b0307020a0605 67
    0x10500111545a0303e603118032514460111083d410750003040441b00c0f002d07042e20b00b0800903020346e6090b1000846450140740e130003410610480c0d610404c0405012403000242d01902450203a034801407940e80311b4000040d00c00e0481000c1e05948401c0014950640e55a1180d003106201040090440c10040d590b00b00180d003e8030840d400b481166141000f007280090300071a0006031140f60000450304001030000c01caa04d129180600c00b11038106032425500d08285601c20b40c1901409803808842006010000e02c0540c0b241c0b82903581c480c0354264100d00c0f40307002e010310b040b8110300f2101041603504050204603180515540103092005001410721801d0082480c200200110b00031900d06110b04d1815541100710403112070000040000042203c034004d40c1a18a0110060600d0f01c0d24607110550074084c00040c0f0407005000e640d2240100800c4244210740e0180205800102d4020140d184c0242201d10a0b481490498424020b0029450307005c40c0351701600d030300450f020500b51140c0000000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 900347356 1250 900346106 900346121
    0x6210c090d1101020c1806011b050607030e370204110a0507020906090601021f02090409050708060903070b011827021e280b040e1b12130303 62
    0x28401140300c0020708014024520707a8070a003084e429070342030207030300e03c02e2100406191000307001000101000a00b01c1d40b089100741c01c8804da51905e50714268094948906105040e00c1e44800613442e80407200c1101820000d1310020b403250b24116180d2600e00c032071180302628004a005041c0841c6c0071900c00d542da00c0c0c200910011141140a642d0081031201500642c4902002c074083c0300c42a00180b118601010407520855041e0040c19121003a0722100c0014a02c400351220342540c00e00c1032001c203880d184940c40d103c1c1c1c800d50080c43c540b810440258501800207120b90407a0b40208040d100041d0218041411104d0340030030f002031480c42c1115040a40007130406000c500300480c0204141d0900045d0a513500b900907115141d0184000070b2200043d44112100c1e13070803080520065000c03c24100780410811510038481e155140c0b034090584881d4040d60101ca40400b0140503c008071140c030035206407081c0e010022606e420002c0e8803240744031720002d02c003c1d451801c21100381e045c140a60040ba0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 900348606 1250 900347356 900347359
    0xa020405060301080d080a0207080a0e0301060905100e0108010b010c080c030d0c050702040e0622060b060d1d0a02010f1b0204321005100203040e070302120606210c09 73
    0x7078036580c68038131081c3c1e1141040f01250000c1c00394008284a02000e02c2116400d6401c0401185403818925065501034911001c0b56055941d415002400f0001c1d40b08c4e440c018a900c0b9204183d20385071501c0000c582c9070680007101540d250800140f126a0084080020950b001707130f001d0b4844542d2031a090550260035409980c69040650040382107a01c40000e10940340308441c10072807079005000090b6103410844848000c0d10030314010244040300081580901d0b8031a10f4041354030004600820483d801c0040d5046145445000e03410008144e42440e903281c5503030100501c43c09906800090103002103002c400d09120782c0303441070484d2404514020091580242c410f200301d26520040111031021681300200f80c00f007441c20402c50004c41e00c207440c096000c5040404401d03041030100a0312002c54075400b000c0d03200c100000680c410030100c1e1a0b1040105860040c2c4466201d0281506208020180382c030a46040014a00304805440707001100300655015621039614610312140324445c001001d0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 900349856 1250 900348606 900348619
    0xf0411180106030203070306080a12080903070203030c0a0309060f12090618151505060d0b0307180608120304020d03030e07260d0c08070f060f020301140907020d0909050a020405 78
    0x1090b46605030f001180200110381d002c024040c3e8481e40c003a10794008000c020500c0c01c07030700c1c0d07207504a520075000d0682004142041d2842e03d29180d0002c7c0c61988a8842d40100c3c1e0044280c100916400400c08002018581000c1e1009445010024030143c1c0307089a5070a190f5858003c8401e0150f20743c01001052030040c44180107a4803401c007181e108816410700705a01d03091040074030701c143c9000310b19012a030000e01014106034111801c0000f82c400104a15050300c01e0210004a604126030780740c60f00d9098580006005041c4802c250404a03002e1040c07481c0d4104105000060311000c0e00d42800580502e4001400085401e000e0701389403040d4000b041c601c02d540714100c0307102c24500c00c0760381901c842012642481e15007002664902c060990150507294140165800f00d500c50030384108440c8520000242003010780402800ca070000e07084841c19a0803070811464505240c08141d81108240c00180420f03000785000508150407802502401911000403400115181d01924081c02005142 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 900351106 1250 900349856 900349859
    0x50a060c0c120914040902060d0c120b0f0f060903010608070609140409120c0507050d080405040b0108061018050a141f0207050127090b12060f04111801 67
    0x6184460303905080d100d106520b500360710000c0c0244030110031039169165440c0741070070200c02c00004190180c0182d070016000c1241c0702d4061054894031104074916110921100100d00c903c5040341d000d8075141c3c0c0a00390402c2c0310440b0385d41c0c1088421710a08210b0f5100d558010140c0824090502a80021f140c0c1c803400e600440c9103500810144190f6035081015441c0b12100ea0410040d20002d46e001340200001844114500e417044140740d8102e40680102c41305142d40340049050305030803000035640828081000c0c81a803410380640510f00600b40f800c0c00072401c2000c0011502c1c80120703d004103200d2081d42512854800d0801c010041000a00e003107041c50740c401d440ca120a04501c01f65100307095504032840c3d0308008485200501d9000d600902c0140e08110041d43c202c540882c444c6411002702382c18800881280302858003a00181c40301281d4185c42800303002444c0c144880700600d58216104200f9a0b0780c40b0186140e102c0d4100b11000c4e070602c0c4003004104c003441c20300381c207000c00701c5403000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 900352356 1250 900351106 900351131
    0x603060904020f10020d1101051b130e0a09140a0b06060d0603020303030c0405030f1606080612011b08150f04050402120601081b06040312080606040b2a01060b16050a06 74
    0x160f416141b6803039102c805a410106041500300c41c0300301e82c0c0daa8010241454118500600d40241103540c8030390204c0c0301c6031742e1504000e1594940490756400d10940781c80e0508204000101741c0340f00740234028024002c0c021103554822000200074801401220041098098100c3e1600548021500a82607070b82da8180b020207842c0e1503025004060180c41583d101c0420b100f000281c1c03101038907100e554100710b18103009040320f120304003034030055001e2110003c0f4918104203121300414800c08605200c03503c14942e1000c0c00c1c0d69801070101131540c01e4041e40c051107840343c40c03840d030b40110100c42c00a5113913107d1000036140c2d20401c21103003440c4900000412030500018280c070f1840201140c503c0048040400c1007031a108a010080551690014011180e802480c0280c3c10000040462341002d1700d411018005d50003000d0869140d403c68103621039003072218441c51814298410091289600701040380361a881502c16088100c0c60341d1052806100081c04400c40565011005002040382c00300e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 900353606 1250 900352356 900352363
    0x114040b0309060105010507211e021006051906050c0102040f080f06010504090f1e0503030a0204140f0d15140c1c0c020718020c0613030f0503060603060904020f1002 73
    0xc800d14014883d02e400800c02c0d41c010ba00b918411039000c50003920741d003025544000409107901c01c51007801540680c02c2a404d00b0034408028840711a4000c1c603030644540301c03480540700c1c141e014070300a056560b0782c40072650818418005461aa0411640d01c066101c2c442e130081c851a0b001000c9201e40703080c0131030202008102840382001034811102c49907290400c100071948014002424100598500c00c0040e2400710100203010aa07000891940c00a403141415640100c0f11748841d41d42c0042c080c03155840c40c10903008010300c20b4402240030384800c004180c509800f03041c05802d850b441d0035061210f0b07840e80c0003007105170850b038600c400509005400c08400d40108400c4021019030302c003480c50602c494854103c545450754000c08102e490001029080a11003110703000c0700c0c0c0c0030040a19500010050035024807041149000c850710141070080040860141c0001001010024040d0f250788040943e900302400301ea219400e600c032440021418082d4595040d08800143d080d07003922500030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 900354856 1250 900353606 900353611
    0x11030f040501080f07091202061c05010611061e091c0804060f0e100507021204120201081b0306040b0f10080f06060703020601030813030b0f10060504080604110114040b03 75
    0x3030f2107546041d00c80034441120481e040303c240000500d801401c10007200e90100c16024035001800742460068903c58010050720702000b4600307001e440d14010070841da84410008480030314100a8111424114445803590080700040313803550009030080f481e500e074144a4000c41079800f10600703d480c05401d402034840042100d085d602c1c0c500d0310301c80d1044c181d464082c9c8240c0301c50f00d0001d40070034419401302d00001e0401070030340302c110710408000b540d1443c10310005002924403501c1c0315007441c009100041200c00010808605900d000380c810705d184011105a03500502c0c112004100c07481d141001c82d40012030011026403081080768080360894015288a0240841966050090b42e90340e00f8010303175214810004005a00500042002c0382414024000b640010070301d004141c1e60f0780d2540a40c01c14181c841424503090403083c40300101030350b00040700070241030a14500381490400c08a40392000104017070944074004401201d140e100c1c2400060341c0b07071503c1c812502d540e26021014102d4208 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 900356106 1250 900354856 900354859
    0x341b0b100608090d0c1e1b0501020328021501181d030a080402060d060b0a03140402181f1502070b090904031b050303070e27070f11030f0405 62
    0x5031808581684911242c034440d80850008040394040d0300c6003141c041c0200182500c01c90b04c03001900d0a90784410455188a41c0510030960040e030b80003066106501c072642c41241954401c0104401d00302c9041003202108210480e50000030b601d4101c283c1c20311840e40d0382c6d1001d61407502d0001c0b802c0d2540e00f404014828903c441086441200c9900d6032a40c1c10110740c00d01a42d00c24071699003c184980100765020740301402c0d40f414503c82105e40c00503500c50303402c9200340d0300f40424565603580d4103211f00810403201c41000b45450502c2c2d00401c1022000744201c0d44810001000500c0c034540940c02c51196011544c2ca5a4500340ea402c041c1240780600c022a80041c000d116000039200102800e95042405c000c00f07150307054843e60360aa0780c4107002d04456003141030403d45030001c1241403020b188584541e446165401182c0c0007040143e5148005110000740d07a100303035846845150038555800445800c00312241c13a81d01ca0709850032050500f4412076071000054266151100341c02a000300e030030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 900357356 1250 900356106 900356131
    0x90903030e0f0d050f1e040305060708150f0603060607121d030a15051825080d080601050f09030a0c0303031428020c01050f01030b341b0b 61
    0x1203042007140c64001e2209803c0003d80140080601048400000c0010100002c84590381d0880010086201c0e001684140c40741d030811170410020a40200b003030340d0700940303032a01000d9015100380042d0808000c642051301801001c0000341260b02c3d80d03011100349130341043d035000300d110392840000c001c4202a58452514603840032414054100000d01107012603010808896010403003c880004010040424142d6050351800000c85c01c0700b4001d03140350089554440c03942c1605c000c0e1080039450790303a014807860361000b40b03c0c0240c2039210480541025003443c0055a480d0702c41c4050a0714054450348513498003440c05a0000c10a94004640840f40f00b0b80b420f110700103d00b0321401008104031181d500d0445000c945143c1c50707604185c0242001c02c02c520040c105100c0b401603608542d01114141040c60b0024014010302298104250f130003000310044205128000200300c22000003001e07440d08113204a02ca03d016030f0b004410340161003400b03131b5909514108a00707082201100a42b03280300440d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 900358606 1250 900357356 900357373
    0xe0c0a090b3a02120a180b060d0f080414010801050604081b060910020705040b0607020a0324050108011508010b060904020d06030b091509011107140f0f011e06030308010b0c07090903030e 82
    0x20f03000d040b4441b5030b504108007204540d1103a042c0000403490034011508000c100701c2140000b0071040240001c0c000a070060a41d40d00c0e0365002504c1c1d05c0d17040e0031241c8075140601003048031650005085100301e040041d0f0b04203036406000460513a0040308222540b1090410b241d46000d60700040c20740417113600311024441b00c1a0081400a584a4110041d42003802030100380086544120401c069420111030840031403180c01c0402d00f02d031000c0c0c001c09066510380740040b007800940d0f1078480103811260000c01c501d0075400002642d03442200c0c1d9103400307585c000c11000502e01c4035034001001542c024101b03114a20308a02042c0e00c580108094882c60782d2080c0109561040510559031152081c2d041c2500d02201c580300e4986041104000d0101032050411100c0f403441e0a10540c0302d104078581c0041070443c2c4a0540c41442c07050031041c007129502d01001007001c81d910845d22811105c110140d140c0c4c1d4101c2d020307081d003401c41a82054241500380003004040507819804400004501c905960042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 900359712 1106 900358606 900358631
    0x1d030105070915023f0301080106031b05010917030c16080d031a061c18020f100c06150e0c0a090b3a02120a 48
    0x19070402c00802440741003c44500052006001801340060101584800038103510700070b441d440e014461201010801348411a03102e01104040d5950303603105c0102e14041e0400d488115041c0781a0703140300c03110909050b016815114160340b440412460103c460504c50b24004c4004041e0104200c2c0c202c1410b020003542d4244c0f0000f840c0c201800740b40c80d04031410480c000c1684014503091900300c02141100384c1030101c8803036003190010303203404402038030000015103c1c0c000c1c1c100502d02000d42100003003440c94851420b100700d80c20114540c1c050103021452104a5514002c903400c81d8100001900036040030716101507508000d200b60369a203441007500d0b001a00c00381003050f0009590070a560b4402c141d940600b688445003460804040d00b020a8119410549083c4101d119980055021282040d46030345200e40b07015500c400b2229009840312505840702d144c0c9615002c00001603 = true := by decide +kernel

theorem cover : BRFrame.Cov 900179856 900359712 := by
  have h0 := BRFrame.cov_init 900179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 900179856 ≤ n) (h2 : n < 900359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
